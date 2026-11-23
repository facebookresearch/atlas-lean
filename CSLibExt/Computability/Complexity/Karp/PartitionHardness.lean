/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionHardnessCore
public import
  CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatMachine
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy

/-!
# Polynomial-time SUBSET-SUM to PARTITION on all raw bitstrings

The source codec accepts only nonempty canonical List Nat strings. Preserve
the raw input, normalize it with the shared exact decoder, and compare before
running the canonical numeric core. Every rejection emits the fixed no-instance.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition.HardnessMachine

open Turing Function TM2Program TM2Embedding BitstringEncoding
open Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding

/-- Disjoint workspaces, a preserved input, and comparison scratch stacks. -/
inductive K
  | norm (k : ListNatMachine.K) | core (k : HardnessCore.K)
  | raw | buffer | left | right
  deriving DecidableEq

@[reducible] def Γ : K → Type
  | .core k => HardnessCore.Γ k
  | _ => Bool

/-- Copy, exact normalization, canonicality check, and numeric computation. -/
inductive Lab
  | copy1 | copy2 | norm (l : ListNatMachine.Lab) | nonempty | compare
  | restore | start | core (l : HardnessCore.Lab) | bad | done
  deriving DecidableEq

def normEmb : SEmb (fun _ : ListNatMachine.K => Bool) Γ where
  e := K.norm
  inj _ _ h := K.norm.inj h
  ι _ := Equiv.refl _

def coreEmb : SEmb HardnessCore.Γ Γ where
  e := K.core
  inj _ _ h := K.core.inj h
  ι _ := Equiv.refl _

def normLabel : ListNatMachine.Lab → Lab
  | .good => .nonempty
  | .bad => .bad
  | l => .norm l

def coreLabel : HardnessCore.Lab → Lab
  | .done => .done
  | l => .core l

/-- A total finite-stack transducer for the exact source codec. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .copy1 => moveB .raw .buffer some id .copy1 .copy2
  | .copy2 => splitB .buffer .raw (.norm .input) some id id .copy2 (.norm .loop)
  | .norm l => mapS normEmb normLabel (ListNatMachine.prog l)
  | .nonempty => .peek (.norm .output) (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .compare) (.goto fun _ => .bad)
  | .compare => cmpB .raw (.norm .output) .left .right some some id id
      .compare .restore .bad
  | .restore => moveB .left (.core .X) some id .restore .start
  | .start => .load (fun _ => false) <| .goto fun _ => .core .target
  | .core l => mapS coreEmb coreLabel (HardnessCore.prog l)
  | .bad => emitR (.core .O) (bitEncode ([1] : List ℕ)) .done
  | .done => .halt

private theorem embeds_norm :
    Embeds normEmb normLabel ListNatMachine.prog prog := by
  intro l
  cases l <;> simp [normLabel, prog, ListNatMachine.prog]

private theorem embeds_core :
    Embeds coreEmb coreLabel HardnessCore.prog prog := by
  intro l
  cases l <;> simp [coreLabel, prog, HardnessCore.prog]

private theorem encode_cons (as : List ℕ) (t : ℕ) :
    bitEncode (t :: as) = encodeSS as t := by
  change delimit (Computability.encodeNat t) ++
    ((as.map Computability.encodeNat).map delimit).flatten = _
  simp [encodeSS, List.flatMap_def, List.map_map, Function.comp_def]

private theorem decode_of_ss {x : List Bool} {as : List ℕ} {t : ℕ}
    (h : SSVerify.decodeSS x = some (as, t)) :
    bitDecode (α := List ℕ) x = some (t :: as) := by
  rw [← SSVerify.decodeSS_eq_some.mp h, ← encode_cons]
  exact bitDecode_bitEncode _

private theorem core_run (as : List ℕ) (t : ℕ) (v : Bool)
    (S : ∀ k, List (Γ k)) (hl : S .left = (encodeSS as t).reverse)
    (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (25 * ((encodeSS as t).length + 1) ^ 2)
      ⟨some .restore, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = bitEncode (fromSubsetSum as t) := by
  obtain ⟨v₁, S₁, h₁, _, hx, hk⟩ := moveB_run
    (M := prog) (self := Lab.restore) (next := .start)
    (a := K.left) (b := K.core .X) (d := some) (g := id)
    rfl (by decide) (encodeSS as t).reverse (encodeSS as t).reverse
    [] v S (by simpa using hl) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hstart : Run prog 1 ⟨some .start, v₁, S₁⟩
      ⟨some (.core .target), false, S₁⟩ := Run.single rfl
  obtain ⟨v₂, C₂, h₂, ho₂⟩ := HardnessCore.run as t
  obtain ⟨S₂, hrun, ha, _⟩ := runLe_embed coreLabel embeds_core h₂ (by
    intro k
    change S₁ (.core k) = (update
      (fun j : HardnessCore.K => ([] : List (HardnessCore.Γ j)))
      .X (encodeSS as t) k).map id
    rw [List.map_id]
    by_cases h : k = .X
    · subst k
      simpa [hc] using hx
    · rw [hk (.core k) (by simp) (by simpa), hc]
      simp [h])
  refine ⟨v₂, S₂, ((h₁.trans hstart).le le_rfl |>.trans hrun).mono ?_, ?_⟩
  · simp only [List.length_reverse]
    nlinarith
  · have h := ha HardnessCore.K.O
    change S₂ (.core .O) = (C₂ .O).map id at h
    simpa only [List.map_id, ho₂] using h

private theorem compare_equal (as : List ℕ) (t : ℕ) (v : Bool)
    (S : ∀ k, List (Γ k)) (ha : S .raw = encodeSS as t)
    (hb : S (.norm .output) = encodeSS as t) (hl : S .left = [])
    (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (30 * ((encodeSS as t).length + 1) ^ 2)
      ⟨some .compare, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = bitEncode (fromSubsetSum as t) := by
  have hp : prog .compare = cmpB .raw (.norm .output) .left .right
      some some id id .compare .restore .bad := rfl
  obtain ⟨v₁, S₁, h₁, hraw, hout, hleft, _, hk⟩ := cmpB_prefix hp
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (encodeSS as t) (encodeSS as t) [] (encodeSS as t) [] v S
    (by simpa using ha) (by simpa using hb)
    (by simp [IsBitBlock]) (by simp [IsBitBlock])
  obtain ⟨v₂, h₂⟩ := cmpB_last hp v₁ S₁ (by simp [hraw, hout])
  have h₂' : Run prog 1 ⟨some .compare, v₁, S₁⟩
      ⟨some .restore, v₂, S₁⟩ := by simpa [hraw, hout] using h₂
  obtain ⟨v₃, S₃, h₃, ho⟩ := core_run as t v₂ S₁
    (by simpa [hl] using hleft) (by
      intro k
      rw [hk (.core k) (by simp) (by simp) (by simp) (by simp), hc])
  exact ⟨v₃, S₃, ((h₁.trans h₂').le le_rfl |>.trans h₃).mono (by nlinarith), ho⟩

private theorem compare_unequal (x y : List Bool) (hne : x ≠ y)
    (v : Bool) (S : ∀ k, List (Γ k)) (ha : S .raw = x)
    (hb : S (.norm .output) = y) (ho : S (.core .O) = []) :
    ∃ v' S', RunLe prog (x.length + 2)
      ⟨some .compare, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = bitEncode ([1] : List ℕ) := by
  obtain ⟨c, v₁, S₁, hp, _, _, hr, _, _, _, _, hk⟩ := cmpB_run
    (M := prog) (self := Lab.compare) (eqL := .restore) (neL := .bad)
    (a := K.raw) (b := K.norm .output) (ta := K.left) (tb := K.right)
    (da := some) (db := some) (ea := id) (eb := id) rfl
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    x y x [] y [] v S (by simpa using ha) (by simpa using hb)
    (by simp [IsBitBlock]) (by simp [IsBitBlock])
    (by simp [EndsBitBlock]) (by simp [EndsBitBlock])
  simp only [hne, ↓reduceIte] at hr
  have he : S₁ (.core .O) = [] := by
    rw [hk (.core .O) (by simp) (by simp) (by simp) (by simp), ho]
  have hbad := emitR_run (M := prog) (self := Lab.bad) (next := .done)
    (k := K.core .O) (ys := bitEncode ([1] : List ℕ)) rfl v₁ S₁
  refine ⟨v₁, _, (hr.trans hbad).le (by have := hp.length_le; omega), ?_⟩
  simp [he]

private theorem decodeSS_reject {x : List Bool} {ns : List ℕ}
    (hd : bitDecode x = some ns) (h : ns = [] ∨ bitEncode ns ≠ x) :
    SSVerify.decodeSS x = none := by
  cases hs : SSVerify.decodeSS x with
  | none => rfl
  | some q =>
    obtain ⟨as, t⟩ := q
    have he : ns = t :: as := by
      simpa [hd] using decode_of_ss hs
    have hc : bitEncode ns = x := by
      rw [he, encode_cons]
      exact SSVerify.decodeSS_eq_some.mp hs
    rcases h with h | h
    · simp [h] at he
    · exact (h hc).elim

private theorem accepted_run (x : List Bool) (ns : List ℕ)
    (hd : bitDecode x = some ns) (v : Bool) (S : ∀ k, List (Γ k))
    (hraw : S .raw = x) (hout : S (.norm .output) = bitEncode ns)
    (hl : S .left = []) (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (35 * (x.length + 1) ^ 2)
      ⟨some .nonempty, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = reduceFromSubsetSum x := by
  have hpos : 0 < (x.length + 1) ^ 2 := by positivity
  cases ns with
  | nil =>
    change S (.norm .output) = [] at hout
    have hs : Run prog 1 ⟨some .nonempty, v, S⟩
        ⟨some .bad, false, S⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, hout]
    have hr := emitR_run (M := prog) (self := Lab.bad) (next := .done)
      (k := K.core .O) (ys := bitEncode ([1] : List ℕ)) rfl false S
    refine ⟨false, _, (hs.trans hr).le (by nlinarith), ?_⟩
    simp [reduceFromSubsetSum, decodeSS_reject hd (Or.inl rfl), hc]
  | cons t as =>
    have hs : Run prog 1 ⟨some .nonempty, v, S⟩
        ⟨some .compare, true, S⟩ := by
      apply Run.single
      simp only [prog, TM2.stepAux, hout, encode_cons, encodeSS]
      cases Computability.encodeNat t <;> rfl
    by_cases he : encodeSS as t = x
    · obtain ⟨v', S', hr, ho⟩ := compare_equal as t true S
        (by simpa [he] using hraw) (by simpa [encode_cons] using hout) hl hc
      rw [he] at hr
      refine ⟨v', S', (hs.le le_rfl |>.trans hr).mono (by nlinarith), ?_⟩
      simpa [reduceFromSubsetSum, SSVerify.decodeSS_eq_some.mpr he] using ho
    · have hne : bitEncode (t :: as) ≠ x := by simpa [encode_cons] using he
      obtain ⟨v', S', hr, ho⟩ := compare_unequal x (bitEncode (t :: as))
        hne.symm true S hraw hout (hc .O)
      refine ⟨v', S', (hs.le le_rfl |>.trans hr).mono (by nlinarith), ?_⟩
      simpa [reduceFromSubsetSum, decodeSS_reject hd (Or.inr hne)] using ho

private theorem normalized_run (x : List Bool) (v : Bool)
    (S : ∀ k, List (Γ k))
    (hn : Agree normEmb (ListNatMachine.st x [] []
      (Cslib.Complexity.FramedCNF.NormalizeMachine.st [] [] [])) S)
    (hraw : S .raw = x) (hl : S .left = []) (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (50 * (x.length + 1) ^ 2)
      ⟨some (.norm .loop), v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = reduceFromSubsetSum x := by
  obtain ⟨v₁, S₁, hr, hf, ha⟩ := ListNatMachine.run_embedded
    normEmb normLabel embeds_norm x v S hn
  have hc' : ∀ k, S₁ (.core k) = [] := by
    intro k
    rw [hf (.core k) (fun j => by simp [normEmb]), hc]
  cases hd : bitDecode (α := List ℕ) x with
  | none =>
    have hss : SSVerify.decodeSS x = none := by
      cases hs : SSVerify.decodeSS x with
      | none => rfl
      | some q =>
        obtain ⟨as, t⟩ := q
        have h := decode_of_ss hs
        simp [hd] at h
    simp only [hd, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, normLabel] at hr
    have hbad := emitR_run (M := prog) (self := Lab.bad) (next := .done)
      (k := K.core .O) (ys := bitEncode ([1] : List ℕ)) rfl v₁ S₁
    refine ⟨v₁, _, (hr.trans (hbad.le le_rfl)).mono (by nlinarith), ?_⟩
    simp [reduceFromSubsetSum, hss, hc']
  | some ns =>
    simp only [hd, Option.isSome_some, ↓reduceIte, normLabel] at hr
    have hout := ha ns hd ListNatMachine.K.output
    change S₁ (.norm .output) = (bitEncode ns).map id at hout
    rw [List.map_id] at hout
    obtain ⟨v₂, S₂, h₂, ho⟩ := accepted_run x ns hd v₁ S₁
      (by rw [hf .raw (fun j => by simp [normEmb]), hraw]) hout
      (by rw [hf .left (fun j => by simp [normEmb]), hl]) hc'
    exact ⟨v₂, S₂, (hr.trans h₂).mono (by nlinarith), ho⟩

/-- Total raw-input hardness reduction, with exact source rejection and
an explicit bound polynomial in encoded length, not numeric magnitude. -/
theorem run (x : List Bool) :
    ∃ v S, RunLe prog (60 * (x.length + 1) ^ 2)
      ⟨some .copy1, false, update (fun _ => []) .raw x⟩
      ⟨some .done, v, S⟩ ∧ S (.core .O) = reduceFromSubsetSum x := by
  obtain ⟨S₁, hr, hraw, _, hx, hk⟩ := copyB_run
    (M := prog) (a := K.raw) (b := K.norm .input) (t := K.buffer)
    (da := some) (dt := some) (ga := id) (gb := id) (gt := id)
    (first := .copy1) (second := .copy2) (next := .norm .loop)
    rfl rfl (by decide) (by decide) (by decide) (fun _ => rfl) (fun _ => rfl)
    x [] false (update (fun _ => []) .raw x) (by simp)
    (by simp [EndsBitBlock]) (by simp [EndsBitBlock])
  have hn : ∀ k, k ≠ ListNatMachine.K.input → S₁ (.norm k) = [] := by
    intro k h
    rw [hk (.norm k) (by simp) (by simpa) (by simp)]
    simp
  obtain ⟨v₂, S₂, h₂, ho⟩ := normalized_run x false S₁ (by
    intro k
    change S₁ (.norm k) = (ListNatMachine.st x [] []
      (Cslib.Complexity.FramedCNF.NormalizeMachine.st [] [] []) k).map id
    rw [List.map_id]
    cases k with
    | input => simpa [ListNatMachine.st] using hx
    | acc => simpa [ListNatMachine.st] using hn .acc (by decide)
    | output => simpa [ListNatMachine.st] using hn .output (by decide)
    | nat k =>
      rw [hn (.nat k) (by simp)]
      cases k <;> rfl)
    (by simpa using hraw)
    (by rw [hk .left (by simp) (by simp) (by simp)]; simp)
    (by intro k; rw [hk (.core k) (by simp) (by simp) (by simp)]; simp)
  exact ⟨v₂, S₂, (hr.le le_rfl |>.trans h₂).mono (by nlinarith), ho⟩

noncomputable instance : Fintype K := Fintype.ofList
  ([.raw, .buffer, .left, .right] ++ Finset.univ.toList.map K.norm ++
    Finset.univ.toList.map K.core) (by intro k; cases k <;> simp)

noncomputable instance : Fintype Lab := Fintype.ofList
  ([.copy1, .copy2, .nonempty, .compare, .restore, .start, .bad, .done] ++
    Finset.univ.toList.map Lab.norm ++ Finset.univ.toList.map Lab.core)
  (by intro l; cases l <;> simp)

/-- The all-string hardness reduction in the existing finite host. -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by
    cases k with
    | norm _ | raw | buffer | left | right => infer_instance
    | core k => exact HardnessCore.comp.finΓ k
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

/-- The total SUBSET-SUM-to-PARTITION map is polynomial-time. -/
theorem isPolyTime_reduceFromSubsetSum : ComplexityTheory.IsPolyTime
    reduceFromSubsetSum :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .raw) (cO := .core .O)
    (gX := id) (start := .copy1) (done := .done) (Equiv.refl Bool)
    reduceFromSubsetSum (Polynomial.C 60 * (Polynomial.X + 1) ^ 2)
    rfl fun x => by simpa using run x

end MetaMathlibExt.Complexity.NPComplete.Partition.HardnessMachine
