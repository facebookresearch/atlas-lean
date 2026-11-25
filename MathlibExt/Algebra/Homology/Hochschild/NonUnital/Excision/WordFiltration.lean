/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.Kernels
public import MathlibExt.Algebra.Algebra.NonUnitalIdeal.KSplit
public meta import Lean.Elab.Tactic.Omega

/-!
# Ideal-count and split-word coordinates of relative kernels

All spans are formed from original tensor words in the original algebra.
Their pullbacks use the quotient-kernel inclusions. Associated
quotients use the native module quotient projection. The arbitrary
coefficient V remains explicit in the bar model. Split-word typing, counts
and word-submodule images provide reusable coordinates for these quotients.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

open ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- The number of original word entries in the original ideal. -/
def idealEntryCount {n : ℕ} (a : Fin n → A) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i ∈ I.toSubmodule)).card

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Multiplying adjacent original entries loses at most one ideal entry. -/
theorem idealEntryCount_mulAdjacent {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) :
    idealEntryCount k A I a - 1 ≤ idealEntryCount k A I (hochschildMulAdjacent i a) := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => a j ∈ I.toSubmodule)
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun j => hochschildMulAdjacent i a j ∈ I.toSubmodule)
  have hRestore (j : Fin (n + 1)) (hj : j ≠ i.succ) :
      i.succ.succAbove (i.predAbove j) = j :=
    Fin.succ_succAbove_predAbove hj
  have hMap : Set.MapsTo i.predAbove (S.erase i.succ) T := by
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hne, hmem⟩
    have hjI : a j ∈ I.toSubmodule := (Finset.mem_filter.mp hmem).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hji : i.predAbove j = i
    · have hleft : i.castSucc = j := by
        simpa only [hji, Fin.succAbove_succ_self] using hRestore j hne
      rw [hochschildMulAdjacent, if_pos hji]
      apply (NonUnitalSubalgebra.mem_toSubmodule I).mpr
      exact NonUnitalSubalgebra.IsTwoSided.mul_mem_right
        ((NonUnitalSubalgebra.mem_toSubmodule I).mp
          (by simpa only [hleft] using hjI)) _
    · rw [hochschildMulAdjacent, if_neg hji, hRestore j hne]
      exact hjI
  have hInj : Set.InjOn i.predAbove (S.erase i.succ) := by
    intro j hj l hl hjl
    have h := congrArg (fun r : Fin n => i.succ.succAbove r) hjl
    exact (hRestore j (Finset.mem_erase.mp hj).1).symm.trans
      (h.trans (hRestore l (Finset.mem_erase.mp hl).1))
  change S.card - 1 ≤ T.card
  exact (Finset.pred_card_le_card_erase (s := S) (a := i.succ)).trans
    (Finset.card_le_card_of_injOn i.predAbove hMap hInj)

/-- The literal original ideal-count word span. -/
def idealWordSpan (n required : ℕ) : Submodule k (TensorPower k n A) :=
  Submodule.span k {x | ∃ a : Fin n → A,
    required ≤ idealEntryCount k A I a ∧ x = PiTensorProduct.tprod k a}

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Requiring fewer original ideal entries enlarges the span. -/
theorem idealWordSpan_antitone (n : ℕ) {r s : ℕ} (h : s ≤ r) :
    idealWordSpan k A I n r ≤ idealWordSpan k A I n s := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, h.trans ha, rfl⟩

/-- Actual native ideal-count coordinates of the original naive quotient kernel. -/
def relativeNaiveWordMap (n : ℕ) :
    (relativeNaiveComplex k A I).X n →ₗ[k] TensorPower k (n + 1) A :=
  (TensorPower.consEquiv k A n).toLinearMap.comp
    ((kernel.ι (cyclicBComplexHom I.quotientMap)).f n).hom

/-- Source F_p M_n, with n+1 original entries and the original quotient kernel. -/
def naiveWordFiltration (p n : ℕ) : Submodule k ((relativeNaiveComplex k A I).X n) :=
  (idealWordSpan k A I (n + 1) (n + 1 - p)).comap (relativeNaiveWordMap k A I n)

/-- The written count formula is monotone in p; its direction is not changed by an assumption. -/
theorem naiveWordFiltration_mono {p q : ℕ} (h : p ≤ q) (n : ℕ) :
    naiveWordFiltration k A I p n ≤ naiveWordFiltration k A I q n := by
  apply Submodule.comap_mono
  apply idealWordSpan_antitone
  omega

/-- The lower original filtration, with zero as the bottom predecessor. -/
def naiveLowerFiltration (p n : ℕ) : Submodule k ((relativeNaiveComplex k A I).X n) :=
  if p = 0 then ⊥ else naiveWordFiltration k A I (p - 1) n

/-- The associated graded module is the native quotient by the original lower inclusion. -/
abbrev naiveWordLayer (p n : ℕ) :=
  naiveWordFiltration k A I p n ⧸
    (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype

/-- The original associated-graded projection is the module quotient map. -/
def naiveWordLayerProjection (p n : ℕ) :
    naiveWordFiltration k A I p n →ₗ[k] naiveWordLayer k A I p n :=
  ((naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype).mkQ

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- Original coefficient words with the source number of ideal entries. -/
def coefficientIdealWordSpan (n required : ℕ) : Submodule k (V ⊗[k] TensorPower k n A) :=
  Submodule.span k {x | ∃ v : V, ∃ a : Fin n → A,
    required ≤ idealEntryCount k A I a ∧ x = v ⊗ₜ[k] PiTensorProduct.tprod k a}

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
theorem coefficientIdealWordSpan_antitone (n : ℕ) {r s : ℕ} (h : s ≤ r) :
    coefficientIdealWordSpan k A I V n r ≤ coefficientIdealWordSpan k A I V n s := by
  apply Submodule.span_mono
  rintro x ⟨v, a, ha, rfl⟩
  exact ⟨v, a, h.trans ha, rfl⟩

/-- Source F_p L_(n+1) in the positive word-length kernel, retaining arbitrary V. -/
def barWordFiltration (p n : ℕ) :
    Submodule k ((relativePositiveBarComplex k A I V).X (n + 1)) :=
  (coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p)).comap
    (relativePositiveBarWordMap k A I V n)

theorem barWordFiltration_mono {p q : ℕ} (h : p ≤ q) (n : ℕ) :
    barWordFiltration k A I V p n ≤ barWordFiltration k A I V q n := by
  apply Submodule.comap_mono
  apply coefficientIdealWordSpan_antitone
  omega

/-- The predecessor of the coefficient count stage, with bottom at filtration index zero. -/
def barLowerFiltration (p n : ℕ) :
    Submodule k ((relativePositiveBarComplex k A I V).X (n + 1)) :=
  if p = 0 then ⊥ else barWordFiltration k A I V (p - 1) n

/-- The source bar associated quotient retains both original filtration inclusions. -/
abbrev barWordLayer (p n : ℕ) :=
  barWordFiltration k A I V p n ⧸
    (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype

/-- The native projection of the coefficient count stage to its original layer quotient. -/
def barWordLayerProjection (p n : ℕ) :
    barWordFiltration k A I V p n →ₗ[k] barWordLayer k A I V p n :=
  ((barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype).mkQ

section SplitWordCoordinates

variable (splitting : I.KSplit)

/-- True positions are the original quotient-section entries; false positions are original ideal entries. -/
def splitWordTyped {n : ℕ} (color : Fin n → Bool) (a : Fin n → A) : Prop :=
  ∀ i, if color i then a i ∈ splitting.sectionMap.range else a i ∈ I.toSubmodule

/-- The quotient-position count of an original split word. -/
def quotientEntryCount {n : ℕ} (color : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => color i = true)).card

/-- Project an original word submodule to its associated quotient. -/
def naiveLayerImage (p n : ℕ) (S : Submodule k (TensorPower k (n + 1) A)) :
    Submodule k (naiveWordLayer k A I p n) :=
  ((S.comap (relativeNaiveWordMap k A I n)).comap
    (naiveWordFiltration k A I p n).subtype).map (naiveWordLayerProjection k A I p n)

end SplitWordCoordinates

end ModuleCat.Algebra.Hochschild.NonUnital
