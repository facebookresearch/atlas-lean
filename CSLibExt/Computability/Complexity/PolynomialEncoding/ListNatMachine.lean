/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
public import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
public import CSLibExt.Computability.Complexity.FramedCNF.Block
import CSLibExt.Computability.CookLevin

/-!
# A finite List Nat canonicalizer

Each block is read by the shared delimiter kernel, normalized by the
shared Nat machine, and re-framed into a reverse accumulator. One final
reversal yields the canonical list encoding. No numeric-value loop occurs.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.ListNatMachine

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding FramedCNF

/-- External input, reverse accumulator, final output, and Nat workspace. -/
inductive K | input | acc | output | nat (k : NormalizeMachine.K)
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.input, .acc, .output, .nat .input, .nat .buffer,
    .nat .output], by decide⟩
  complete k := by cases k with
    | input | acc | output => decide
    | nat k => cases k <;> decide

/-- Only the Nat workspace is visible to the shared normalizer. -/
def emb : SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : K => Bool) where
  e := K.nat
  inj _ _ h := K.nat.inj h
  ι _ := Equiv.refl Bool

/-- The normalizer's halt resumes frame emission. -/
inductive Lab
  | loop | block | back | nat (l : NormalizeMachine.Lab) | emit | finish
  | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.loop, .block, .back, .nat (.read none),
    .nat (.read (some false)), .nat (.read (some true)), .nat .copy,
    .nat .done, .emit, .finish, .good, .bad], by decide⟩
  complete l := by
    rcases l with _ | _ | _ | l | _ | _ | _ | _ <;> try decide
    rcases l with (_ | (_ | _)) | _ | _ <;> decide

/-- Label embedding of the actual shared Nat normalizer. -/
def natLabel : NormalizeMachine.Lab → Lab
  | .done => .emit
  | l => .nat l

/-- The concrete canonicalizer program. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .loop => .peek .input (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .block) (.goto fun _ => .finish)
  | .block => Block.read .input (.nat .output) some id .block .back .bad
  | .back => moveB (.nat .output) (.nat .input) some id .back
      (.nat (.read none))
  | .nat l => mapS emb natLabel (NormalizeMachine.prog l)
  | .emit => emitFrame (.nat .output) .acc some id .emit .loop
  | .finish => moveB .acc .output some id .finish .good
  | .good | .bad => .halt

/-- Workspace layout for the composition invariant. -/
def st (x acc out : List Bool) (s : NormalizeMachine.K → List Bool) :
    K → List Bool
  | .input => x
  | .acc => acc
  | .output => out
  | .nat k => s k

private theorem embeds_nat :
    Embeds emb natLabel NormalizeMachine.prog prog := by
  intro l
  cases l with
  | read _ => exact Or.inl rfl
  | copy => exact Or.inl rfl
  | done => exact Or.inr rfl

private theorem normalize_run (p x acc out : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * p.length + 3)
      ⟨some (.nat (.read none)), v,
        st x acc out (NormalizeMachine.st p [] [])⟩
      ⟨some .emit, v',
        st x acc out (NormalizeMachine.st [] [] (normalizeNat p))⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame p [] v
  obtain ⟨T, run, agree, frame⟩ := runLe_embed natLabel embeds_nat hr
    (S' := st x acc out (NormalizeMachine.st p [] []))
    (by intro k; simp [emb, st])
  have he : T =
      st x acc out (NormalizeMachine.st [] [] (normalizeNat p)) := by
    funext k
    cases k with
    | input => exact frame K.input (by intro k; simp [emb])
    | acc => exact frame K.acc (by intro k; simp [emb])
    | output => exact frame K.output (by intro k; simp [emb])
    | nat k => simpa [emb, st] using agree k
  rw [he] at run
  exact ⟨v', run⟩

private theorem block_run (p x acc out : List Bool) (v : Bool) :
    Run prog (p.length + 1)
      ⟨some .block, v, st (delimit p ++ x) acc out
        (NormalizeMachine.st [] [] [])⟩
      ⟨some .back, false, st x acc out
        (NormalizeMachine.st [] [] p.reverse)⟩ := by
  obtain ⟨S, run, ha, hb, hk⟩ := Block.run_delimit
    (M := prog) (a := K.input) (b := K.nat .output)
    (d := some) (g := id) (self := Lab.block) (good := Lab.back)
    (bad := Lab.bad) rfl (by decide) id (fun _ => rfl) p x v
    (st (delimit p ++ x) acc out (NormalizeMachine.st [] [] []))
    (by simp [st])
  have he : S = st x acc out (NormalizeMachine.st [] [] p.reverse) := by
    funext k
    cases k with
    | input => exact ha
    | acc => exact hk K.acc (by decide) (by decide)
    | output => exact hk K.output (by decide) (by decide)
    | nat k =>
      cases k with
      | input => exact hk (K.nat .input) (by decide) (by decide)
      | buffer => exact hk (K.nat .buffer) (by decide) (by decide)
      | output => simpa [st, NormalizeMachine.st] using hb
  rwa [he] at run

private theorem back_run (p x acc out : List Bool) (v : Bool) :
    ∃ v', Run prog (p.length + 1)
      ⟨some .back, v, st x acc out
        (NormalizeMachine.st [] [] p.reverse)⟩
      ⟨some (.nat (.read none)), v', st x acc out
        (NormalizeMachine.st p [] [])⟩ := by
  obtain ⟨v', S, run, ha, hb, hk⟩ := moveB_run
    (M := prog) (a := K.nat .output) (b := K.nat .input)
    (d := some) (g := id) (self := Lab.back)
    (next := Lab.nat (.read none)) rfl (by decide)
    p.reverse p.reverse [] v
    (st x acc out (NormalizeMachine.st [] [] p.reverse))
    (by simp [st, NormalizeMachine.st]) rfl rfl
  have he : S = st x acc out (NormalizeMachine.st p [] []) := by
    funext k
    cases k with
    | input => exact hk K.input (by decide) (by decide)
    | acc => exact hk K.acc (by decide) (by decide)
    | output => exact hk K.output (by decide) (by decide)
    | nat k =>
      cases k with
      | input => simpa [st, NormalizeMachine.st] using hb
      | buffer => exact hk (K.nat .buffer) (by decide) (by decide)
      | output => exact ha
  refine ⟨v', ?_⟩
  simpa [he] using run

private theorem emit_run (p x acc out : List Bool) (v : Bool) :
    Run prog (p.length + 1)
      ⟨some .emit, v, st x acc out (NormalizeMachine.st [] [] p)⟩
      ⟨some .loop, false, st x ((delimit p).reverse ++ acc) out
        (NormalizeMachine.st [] [] [])⟩ := by
  obtain ⟨S, run, ha, hb, hk⟩ := emitFrame_run
    (M := prog) (a := K.nat .output) (b := K.acc)
    (d := some) (g := id) (self := Lab.emit) (next := Lab.loop)
    rfl (by decide) id (fun _ => rfl) p [] v
    (st x acc out (NormalizeMachine.st [] [] p)) rfl
    (by simp [st, NormalizeMachine.st])
  have he : S = st x ((delimit p).reverse ++ acc) out
      (NormalizeMachine.st [] [] []) := by
    funext k
    cases k with
    | input => exact hk K.input (by decide) (by decide)
    | acc => simpa [st] using hb
    | output => exact hk K.output (by decide) (by decide)
    | nat k =>
      cases k with
      | input => exact hk (K.nat .input) (by decide) (by decide)
      | buffer => exact hk (K.nat .buffer) (by decide) (by decide)
      | output => exact ha
  rwa [he] at run

/-- One list element is normalized and appended to the reverse
accumulator; every scratch stack is ready for the next call. -/
theorem element_run (p x acc out : List Bool) (v : Bool) :
    RunLe prog (8 * (delimit p).length)
      ⟨some .loop, v, st (delimit p ++ x) acc out
        (NormalizeMachine.st [] [] [])⟩
      ⟨some .loop, false, st x
        ((delimit (normalizeNat p)).reverse ++ acc) out
        (NormalizeMachine.st [] [] [])⟩ := by
  have first : Run prog 1
      ⟨some .loop, v, st (delimit p ++ x) acc out
        (NormalizeMachine.st [] [] [])⟩
      ⟨some .block, true, st (delimit p ++ x) acc out
        (NormalizeMachine.st [] [] [])⟩ := by
    apply Run.single
    cases p <;> simp [prog, TM2.stepAux, st, delimit]
  obtain ⟨v₁, back⟩ := back_run p x acc out false
  obtain ⟨v₂, norm⟩ := normalize_run p x acc out v₁
  have initialRun := first.trans (block_run p x acc out true) |>.trans back
  have all := (initialRun.le le_rfl).trans norm |>.trans
    ((emit_run (normalizeNat p) x acc out v₂).le le_rfl)
  apply all.mono
  have h := length_normalizeNat_le p
  rw [length_delimit]
  omega

/-- Normalize any finite sequence of framed Nat payloads. The payloads
need not be canonical, and previous accumulator/output suffixes survive. -/
theorem blocks_run (bs : List (List Bool)) :
    ∀ (acc out : List Bool) (v : Bool),
    RunLe prog (8 * ((bs.map delimit).flatten).length + 1)
      ⟨some .loop, v, st ((bs.map delimit).flatten) acc out
        (NormalizeMachine.st [] [] [])⟩
      ⟨some .finish, false, st []
        (((bs.map (fun p => delimit (normalizeNat p))).flatten).reverse ++ acc)
        out (NormalizeMachine.st [] [] [])⟩ := by
  induction bs with
  | nil =>
    intro acc out v
    apply Run.le (Run.single ?_) (by simp)
    simp [prog, TM2.stepAux, st]
  | cons p bs ih =>
    intro acc out v
    have r₁ := element_run p ((bs.map delimit).flatten) acc out v
    have r₂ := ih ((delimit (normalizeNat p)).reverse ++ acc) out false
    have r := r₁.trans r₂
    simp only [List.map_cons, List.flatten_cons, List.reverse_append,
      List.append_assoc, List.length_append]
    exact r.mono (by omega)

private theorem finish_run (acc out : List Bool) (v : Bool) :
    ∃ v', Run prog (acc.length + 1)
      ⟨some .finish, v, st [] acc out (NormalizeMachine.st [] [] [])⟩
      ⟨some .good, v', st [] [] (acc.reverse ++ out)
        (NormalizeMachine.st [] [] [])⟩ := by
  obtain ⟨v', S, run, ha, hb, hk⟩ := moveB_run
    (M := prog) (a := K.acc) (b := K.output) (d := some) (g := id)
    (self := Lab.finish) (next := Lab.good) rfl (by decide)
    acc acc [] v (st [] acc out (NormalizeMachine.st [] [] []))
    (by simp [st]) rfl rfl
  have he : S = st [] [] (acc.reverse ++ out)
      (NormalizeMachine.st [] [] []) := by
    funext k
    cases k with
    | input => exact hk K.input (by decide) (by decide)
    | acc => exact ha
    | output => simpa [st] using hb
    | nat k => exact hk (K.nat k) (by simp) (by simp)
  exact ⟨v', he ▸ run⟩

/-- Successful raw List Nat decoding is implemented in linear time,
with canonical output and all private scratch stacks empty. -/
theorem run_some {x : List Bool} {as : List Nat}
    (h : bitDecode x = some as) (out : List Bool) (v : Bool) :
    ∃ v', RunLe prog (11 * x.length + 2)
      ⟨some .loop, v, st x [] out (NormalizeMachine.st [] [] [])⟩
      ⟨some .good, v', st [] [] (bitEncode as ++ out)
        (NormalizeMachine.st [] [] [])⟩ := by
  rw [decode_list_nat] at h
  obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  have hx := blocks_decode_sound hb
  rw [hx]
  have r₁ := blocks_run bs [] out v
  simp only [List.append_nil] at r₁
  obtain ⟨v', r₂⟩ := finish_run
    (((bs.map (fun p => delimit (normalizeNat p))).flatten).reverse)
    out false
  have r := r₁.trans (r₂.le le_rfl)
  simp only [List.reverse_reverse] at r
  rw [encode_decoded_nat_blocks]
  refine ⟨v', r.mono ?_⟩
  have hl := normalized_nat_blocks_length_le bs
  simp only [List.length_reverse]
  omega

private theorem run_blocks_none (fuel : Nat) :
    ∀ (x acc out : List Bool) (v : Bool), x.length ≤ fuel →
    undelimitBlocksAux fuel x = none →
    ∃ v' S, RunLe prog (8 * x.length + 2)
      ⟨some .loop, v, st x acc out (NormalizeMachine.st [] [] [])⟩
      ⟨some .bad, v', S⟩ := by
  induction fuel with
  | zero =>
    intro x acc out v hx hn
    have he : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [he, undelimitBlocksAux] at hn
  | succ fuel ih =>
    intro x acc out v hx hn
    cases x with
    | nil => simp [undelimitBlocksAux] at hn
    | cons b xs =>
      cases hu : undelimit (b :: xs) with
      | none =>
        have first : Run prog 1
            ⟨some .loop, v, st (b :: xs) acc out
              (NormalizeMachine.st [] [] [])⟩
            ⟨some .block, true, st (b :: xs) acc out
              (NormalizeMachine.st [] [] [])⟩ :=
          Run.single (by simp [prog, TM2.stepAux, st])
        obtain ⟨v', S, hr⟩ := Block.run_none (M := prog)
          (a := K.input) (b := K.nat .output) (d := some) (g := id)
          (self := Lab.block) (good := Lab.back) (bad := Lab.bad)
          rfl (by decide) id (fun _ => rfl) (b :: xs) true
          (st (b :: xs) acc out (NormalizeMachine.st [] [] []))
          (by simp [st]) hu
        exact ⟨v', S, ((first.le le_rfl).trans hr).mono (by simp; omega)⟩
      | some pr =>
        obtain ⟨p, r⟩ := pr
        have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
        have hlen := congrArg List.length he
        simp only [List.length_cons, List.length_append,
          length_delimit] at hlen hx
        have hr : r.length ≤ fuel := by omega
        have hn' : undelimitBlocksAux fuel r = none := by
          simpa [undelimitBlocksAux, hu] using hn
        obtain ⟨v', S, rest⟩ := ih r
          ((delimit (normalizeNat p)).reverse ++ acc) out false hr hn'
        rw [he]
        exact ⟨v', S, ((element_run p r acc out v).trans rest).mono
          (by simp only [List.length_append]; omega)⟩

/-- Every malformed raw List Nat input reaches the failure endpoint.
The accumulator and Nat output may contain partial data; clear the
workspace before reuse. No output claim is made for a failed parse. -/
theorem run_none {x : List Bool} (h : bitDecode (α := List Nat) x = none)
    (acc out : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (8 * x.length + 2)
      ⟨some .loop, v, st x acc out (NormalizeMachine.st [] [] [])⟩
      ⟨some .bad, v', S⟩ := by
  rw [decode_list_nat, Option.map_eq_none_iff] at h
  exact run_blocks_none x.length x acc out v le_rfl h

/-- The List Nat canonicalizer uses the existing finite Host interface. -/
abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .acc, .output, .nat .input, .nat .buffer, .nat .output]
  ks_nodup := by decide
  mem_ks k := by
    cases k with
    | input | acc | output => decide
    | nat k => cases k <;> decide

/-- A total success/failure contract at the two actual halt labels.
Success has canonical output; failure exposes no partial-output promise. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (11 * x.length + 2)
      ⟨some .loop, v, st x [] [] (NormalizeMachine.st [] [] [])⟩
      ⟨some (if (bitDecode (α := List Nat) x).isSome then .good else .bad),
        v', S⟩ ∧
      ∀ as : List Nat, bitDecode x = some as →
        S = st [] [] (bitEncode as) (NormalizeMachine.st [] [] []) := by
  cases h : bitDecode (α := List Nat) x with
  | none =>
    obtain ⟨v', S, hr⟩ := run_none h [] [] v
    refine ⟨v', S, hr.mono (by omega), ?_⟩
    intro as ha
    simp at ha
  | some as =>
    obtain ⟨v', hr⟩ := run_some h [] v
    refine ⟨v', st [] [] (bitEncode as) (NormalizeMachine.st [] [] []),
      ?_, ?_⟩
    · simpa using hr
    · intro bs hb
      have he : as = bs := Option.some.inj hb
      subst bs
      rfl

/-- Embed the concrete normalizer in a caller, preserving every stack
outside its workspace on both success and failure. Entry requires clean
scratch and output stacks. After `bad`, clear partial workspace data
before another invocation. -/
theorem run_embedded {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : SEmb (fun _ : K => Bool) Γ) (φ : Lab → L)
    {M : L → TM2.Stmt Γ L Bool} (hm : Embeds E φ prog M)
    (x : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hs : Agree E (st x [] [] (NormalizeMachine.st [] [] [])) S) :
    ∃ v' T, RunLe M (11 * x.length + 2)
      ⟨some (φ .loop), v, S⟩
      ⟨some (φ (if (bitDecode (α := List Nat) x).isSome
        then .good else .bad)), v', T⟩ ∧ Frame E S T ∧
      ∀ as : List Nat, bitDecode x = some as →
        Agree E (st [] [] (bitEncode as) (NormalizeMachine.st [] [] [])) T := by
  obtain ⟨v', U, hr, hu⟩ := run x v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed φ hm hr hs
  refine ⟨v', T, ht, hf, ?_⟩
  intro as hx
  rw [hu as hx] at ha
  exact ha

end Cslib.Complexity.PolynomialEncoding.ListNatMachine
