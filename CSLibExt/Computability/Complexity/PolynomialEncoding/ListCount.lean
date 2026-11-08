/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
public import CSLibExt.Computability.Complexity.FramedCNF.Block
public import CSLibExt.Computability.Complexity.Host
import CSLibExt.Computability.CookLevin

/-!
# Counting frames of a concrete List Nat input

The counter has one unary bit per complete list element, so its numeric
value is bounded by raw input length. Payload contents are not enumerated.
This gives SET COVER's cardinality-versus-length guard its physical count.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.ListCount

open Turing Function MetaMathlibExt.TM2Program
open MetaMathlibExt.BitstringEncoding FramedCNF

/-- Input, one-block scratch, and a unary element counter. -/
inductive K | input | scratch | count
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.input, .scratch, .count], by decide⟩
  complete k := by cases k <;> decide

/-- Each complete frame increments the counter and clears its scratch. -/
inductive Lab | loop | block | bump | clear | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.loop, .block, .bump, .clear, .good, .bad], by decide⟩
  complete l := by cases l <;> decide

/-- Count by repeated shared block reading and shared scratch cleanup. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .loop => .peek .input (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .block) (.goto fun _ => .good)
  | .block => Block.read .input .scratch some id .block .bump .bad
  | .bump => .push .count (fun _ => true) (.goto fun _ => .clear)
  | .clear => cleanS [.scratch] .clear .loop
  | .good | .bad => .halt

/-- The three actual stack contents. -/
def st (input scratch count : List Bool) : K → List Bool
  | .input => input
  | .scratch => scratch
  | .count => count

private theorem clear_run (x scratch count : List Bool) (v : Bool) :
    RunLe prog (scratch.length + 1)
      ⟨some .clear, v, st x scratch count⟩
      ⟨some .loop, false, st x [] count⟩ := by
  have hr := clean_run (M := prog) (ks := [K.scratch])
    (self := Lab.clear) (next := Lab.loop) rfl (by simp)
    scratch.length v (st x scratch count)
    (by intro k hk; simp only [List.mem_singleton] at hk; subst k; rfl)
  have he : (fun k => if k ∈ [K.scratch] then []
      else st x scratch count k) = st x [] count := by
    funext k
    cases k <;> simp [st]
  rwa [he] at hr

/-- One complete frame contributes exactly one unary count bit and
leaves no payload scratch, independently of the decoded Nat's value. -/
theorem element_run (p x count : List Bool) (v : Bool) :
    RunLe prog (4 * (delimit p).length)
      ⟨some .loop, v, st (delimit p ++ x) [] count⟩
      ⟨some .loop, false, st x [] (true :: count)⟩ := by
  have first : Run prog 1
      ⟨some .loop, v, st (delimit p ++ x) [] count⟩
      ⟨some .block, true, st (delimit p ++ x) [] count⟩ := by
    apply Run.single
    cases p <;> simp [prog, TM2.stepAux, st, delimit]
  obtain ⟨S, hr, hi, hs, hk⟩ := Block.run_delimit
    (M := prog) (a := K.input) (b := K.scratch)
    (d := some) (g := id) (self := Lab.block) (good := Lab.bump)
    (bad := Lab.bad) rfl (by decide) id (fun _ => rfl) p x true
    (st (delimit p ++ x) [] count) (by simp [st])
  have he : S = st x p.reverse count := by
    funext k
    cases k with
    | input => exact hi
    | scratch => simpa [st] using hs
    | count => exact hk K.count (by decide) (by decide)
  rw [he] at hr
  have bump : Run prog 1 ⟨some .bump, false, st x p.reverse count⟩
      ⟨some .clear, false, st x p.reverse (true :: count)⟩ := by
    apply Run.single
    simp only [prog, TM2.stepAux, st, TM2.Cfg.mk.injEq, true_and]
    funext k
    cases k <;> rfl
  have run := ((first.trans hr |>.trans bump).le le_rfl).trans
    (clear_run x p.reverse (true :: count) false)
  exact run.mono (by simp only [List.length_reverse, length_delimit]; omega)

/-- Counting a sequence of raw frames yields its length in unary,
with the caller's counter suffix preserved and scratch empty. -/
theorem blocks_run (bs : List (List Bool)) (count : List Bool) (v : Bool) :
    RunLe prog (4 * ((bs.map delimit).flatten).length + 1)
      ⟨some .loop, v, st (bs.map delimit).flatten [] count⟩
      ⟨some .good, false,
        st [] [] (List.replicate bs.length true ++ count)⟩ := by
  induction bs generalizing count v with
  | nil =>
    exact (Run.single (by simp [prog, TM2.stepAux, st])).le le_rfl
  | cons p bs ih =>
    have hr := (element_run p (bs.map delimit).flatten count v).trans
      (ih (true :: count) false)
    have he : List.replicate bs.length true ++ true :: count =
        List.replicate (bs.length + 1) true ++ count := by
      simp [List.replicate_add, List.append_assoc]
    rw [he] at hr
    exact hr.mono (by simp only [List.map_cons, List.flatten_cons,
      List.length_append]; omega)

/-- Count every successfully decoded List Nat, including noncanonical
Nat payloads; the count suffix is preserved exactly. -/
theorem run_some {x : List Bool} {as : List Nat}
    (h : bitDecode x = some as) (count : List Bool) (v : Bool) :
    RunLe prog (4 * x.length + 1)
      ⟨some .loop, v, st x [] count⟩
      ⟨some .good, false,
        st [] [] (List.replicate as.length true ++ count)⟩ := by
  rw [decode_list_nat] at h
  obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [List.length_map, blocks_decode_sound hb]
  exact blocks_run bs count v

private theorem run_blocks_none (fuel : Nat) :
    ∀ (x count : List Bool) (v : Bool), x.length ≤ fuel →
    undelimitBlocksAux fuel x = none →
    ∃ v' S, RunLe prog (4 * x.length + 2)
      ⟨some .loop, v, st x [] count⟩ ⟨some .bad, v', S⟩ := by
  induction fuel with
  | zero =>
    intro x count v hx hn
    have he : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [he, undelimitBlocksAux] at hn
  | succ fuel ih =>
    intro x count v hx hn
    cases x with
    | nil => simp [undelimitBlocksAux] at hn
    | cons b xs =>
      cases hu : undelimit (b :: xs) with
      | none =>
        have first : Run prog 1
            ⟨some .loop, v, st (b :: xs) [] count⟩
            ⟨some .block, true, st (b :: xs) [] count⟩ :=
          Run.single (by simp [prog, TM2.stepAux, st])
        obtain ⟨v', S, hr⟩ := Block.run_none (M := prog)
          (a := K.input) (b := K.scratch) (d := some) (g := id)
          (self := Lab.block) (good := Lab.bump) (bad := Lab.bad)
          rfl (by decide) id (fun _ => rfl) (b :: xs) true
          (st (b :: xs) [] count) (by simp [st]) hu
        exact ⟨v', S, ((first.le le_rfl).trans hr).mono (by simp; omega)⟩
      | some pr =>
        obtain ⟨p, r⟩ := pr
        have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
        have hl := congrArg List.length he
        simp only [List.length_cons, List.length_append, length_delimit]
          at hl hx
        have hn' : undelimitBlocksAux fuel r = none := by
          simpa [undelimitBlocksAux, hu] using hn
        obtain ⟨v', S, rest⟩ := ih r (true :: count) false (by omega) hn'
        rw [he]
        exact ⟨v', S, ((element_run p r count v).trans rest).mono
          (by simp only [List.length_append]; omega)⟩

/-- Malformed List Nat framing reaches the failure endpoint. The
counter and scratch may be partial and must be cleared before reuse. -/
theorem run_none {x : List Bool} (h : bitDecode (α := List Nat) x = none)
    (count : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (4 * x.length + 2)
      ⟨some .loop, v, st x [] count⟩ ⟨some .bad, v', S⟩ := by
  rw [decode_list_nat, Option.map_eq_none_iff] at h
  exact run_blocks_none x.length x count v le_rfl h

/-- The frame counter is a finite component of the existing Host. -/
abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .scratch, .count]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- Total List Nat decoding outcome and exact unary length on success. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (4 * x.length + 2)
      ⟨some .loop, v, st x [] []⟩
      ⟨some (if (bitDecode (α := List Nat) x).isSome then .good else .bad),
        v', S⟩ ∧
      ∀ as : List Nat, bitDecode x = some as →
        S = st [] [] (List.replicate as.length true) := by
  cases h : bitDecode (α := List Nat) x with
  | none =>
    obtain ⟨v', S, hr⟩ := run_none h [] v
    refine ⟨v', S, hr, ?_⟩
    intro as ha
    simp at ha
  | some as =>
    refine ⟨false, st [] [] (List.replicate as.length true), ?_, ?_⟩
    · simpa using (run_some h [] v).mono (by omega :
        4 * x.length + 1 ≤ 4 * x.length + 2)
    · intro bs hb
      obtain rfl := Option.some.inj hb
      rfl

/-- Embedded counting preserves every caller stack outside its
workspace on success and failure. Scratch is empty on success. -/
theorem run_embedded {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : MetaMathlibExt.TM2Embedding.SEmb (fun _ : K => Bool) Γ)
    (φ : Lab → L) {M : L → TM2.Stmt Γ L Bool}
    (hm : MetaMathlibExt.TM2Embedding.Embeds E φ prog M)
    (x : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hs : MetaMathlibExt.TM2Embedding.Agree E (st x [] []) S) :
    ∃ v' T, RunLe M (4 * x.length + 2)
      ⟨some (φ .loop), v, S⟩
      ⟨some (φ (if (bitDecode (α := List Nat) x).isSome
        then .good else .bad)), v', T⟩ ∧
      MetaMathlibExt.TM2Embedding.Frame E S T ∧
      ∀ as : List Nat, bitDecode x = some as →
        MetaMathlibExt.TM2Embedding.Agree E
          (st [] [] (List.replicate as.length true)) T := by
  obtain ⟨v', U, hr, hu⟩ := run x v
  obtain ⟨T, ht, ha, hf⟩ := MetaMathlibExt.TM2Embedding.runLe_embed φ hm hr hs
  refine ⟨v', T, ht, hf, ?_⟩
  intro as h
  rw [hu as h] at ha
  exact ha

end Cslib.Complexity.PolynomialEncoding.ListCount
