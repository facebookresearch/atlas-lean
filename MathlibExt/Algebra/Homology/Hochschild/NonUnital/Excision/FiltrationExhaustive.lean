/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationComplex
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveBarAssociatedGraded

/-!
# Exhaustion of ideal-count filtrations

Ideal-count stages exhaust the quotient kernels
in every degree. Their associated quotients
vanish beyond the word-length bound. These
are degreewise properties of the count spans
and restricted quotient complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Requiring no ideal entries gives the entire original tensor power. -/
theorem idealWordSpan_zero (n : ℕ) :
    idealWordSpan k A I n 0 = ⊤ := by
  have hs : {x | ∃ a : Fin n → A,
      0 ≤ idealEntryCount k A I a ∧ x = PiTensorProduct.tprod k a} =
      Set.range (PiTensorProduct.tprod k : (Fin n → A) → TensorPower k n A) := by
    ext x
    constructor
    · rintro ⟨a, _ha, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, Nat.zero_le _, rfl⟩
  rw [idealWordSpan, hs, PiTensorProduct.span_tprod_eq_top]

/-- The naive stage is full once its index reaches the word length. -/
theorem naiveWordFiltration_eq_top {p n : ℕ} (h : n + 1 ≤ p) :
    naiveWordFiltration k A I p n = ⊤ := by
  rw [naiveWordFiltration, Nat.sub_eq_zero_of_le h, idealWordSpan_zero,
    Submodule.comap_top]

/-- The original increasing naive stages exhaust each original kernel term. -/
theorem naiveWordFiltration_iSup (n : ℕ) :
    (⨆ p : ℕ, naiveWordFiltration k A I p n) = ⊤ := by
  apply top_unique
  rw [← naiveWordFiltration_eq_top k A I (p := n + 1) (le_refl _)]
  exact le_iSup (fun p : ℕ => naiveWordFiltration k A I p n) (n + 1)

/-- The stage inclusion is bijective in each exhausted original degree. -/
theorem naiveFilteredWordInclusion_f_bijective {p n : ℕ} (h : n + 1 ≤ p) :
    Function.Bijective ((naiveFilteredWordInclusion k A I p).f n).hom := by
  change Function.Bijective (naiveWordFiltration k A I p n).subtype
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [naiveWordFiltration_eq_top k A I h]
  exact Submodule.mem_top

/-- Native component invertibility is from the count-stage inclusion. -/
theorem naiveFilteredWordInclusion_f_isIso {p n : ℕ} (h : n + 1 ≤ p) :
    IsIso ((naiveFilteredWordInclusion k A I p).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (naiveFilteredWordInclusion_f_bijective k A I h)

/-- The original lower stage is full above the original word length. -/
theorem naiveLowerFiltration_eq_top {p n : ℕ} (h : n + 1 < p) :
    naiveLowerFiltration k A I p n = ⊤ := by
  have hp : p ≠ 0 := by omega
  have hb : n + 1 ≤ p - 1 := by omega
  rw [naiveLowerFiltration, ite_eq_right hp, naiveWordFiltration_eq_top k A I hb]

/-- The associated quotient vanishes above its original word-length bound. -/
theorem naiveWordLayer_subsingleton {p n : ℕ} (h : n + 1 < p) :
    Subsingleton (naiveWordLayer k A I p n) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [naiveLowerFiltration_eq_top k A I h, Submodule.comap_top]

/-- The naive associated complex has no terms above this degreewise bound. -/
theorem naiveAssociatedWordComplex_isZero {p n : ℕ} (h : n + 1 < p) :
    IsZero ((naiveAssociatedWordComplex k A I p).X n) := by
  change IsZero (ModuleCat.of k (naiveWordLayer k A I p n))
  exact ModuleCat.isZero_iff_subsingleton.mpr (naiveWordLayer_subsingleton k A I h)

variable (V : Type w) [AddCommGroup V] [Module k V]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Requiring no ideal entries spans every original arbitrary-coefficient word. -/
theorem coefficientIdealWordSpan_zero (n : ℕ) :
    coefficientIdealWordSpan k A I V n 0 = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul v t =>
      refine PiTensorProduct.induction_on t (fun r a => ?_) (fun x y hx hy => ?_)
      · rw [TensorProduct.tmul_smul]
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨v, a, Nat.zero_le _, rfl⟩
      · rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- The positive original stage is full at its word-length bound. -/
theorem barWordFiltration_eq_top {p n : ℕ} (h : n + 1 ≤ p) :
    barWordFiltration k A I V p n = ⊤ := by
  rw [barWordFiltration, Nat.sub_eq_zero_of_le h, coefficientIdealWordSpan_zero,
    Submodule.comap_top]

/-- Every positive-degree kernel term is exhausted by the original bar stages. -/
theorem barWordFiltration_iSup (n : ℕ) :
    (⨆ p : ℕ, barWordFiltration k A I V p n) = ⊤ := by
  apply top_unique
  rw [← barWordFiltration_eq_top k A I V (p := n + 1) (le_refl _)]
  exact le_iSup (fun p : ℕ => barWordFiltration k A I V p n) (n + 1)

/-- The bottom augmentation stage is the entire zero augmentation object. -/
theorem barFullWordFiltration_zero_eq_top (p : ℕ) :
    barFullWordFiltration k A I V p 0 = ⊤ := by
  have : Subsingleton ((relativePositiveBarComplex k A I V).X 0) :=
    ModuleCat.isZero_iff_subsingleton.mp (relativePositiveBarComplex_isZero_zero k A I V)
  apply Submodule.eq_top_iff'.mpr
  intro x
  change x = 0
  exact Subsingleton.elim _ _

/-- The full original positive stage exhausts the original kernel in every degree. -/
theorem barFullWordFiltration_eq_top {p n : ℕ} (h : n ≤ p) :
    barFullWordFiltration k A I V p n = ⊤ := by
  cases n with
  | zero => exact barFullWordFiltration_zero_eq_top k A I V p
  | succ n => exact barWordFiltration_eq_top k A I V h

/-- The zero augmentation is retained in degreewise bar exhaustion. -/
theorem barFullWordFiltration_iSup (n : ℕ) :
    (⨆ p : ℕ, barFullWordFiltration k A I V p n) = ⊤ := by
  apply top_unique
  rw [← barFullWordFiltration_eq_top k A I V (p := n) (le_refl _)]
  exact le_iSup (fun p : ℕ => barFullWordFiltration k A I V p n) n

/-- The positive inclusion is bijective once the original stage exhausts the degree. -/
theorem barFilteredWordInclusion_f_bijective {p n : ℕ} (h : n ≤ p) :
    Function.Bijective ((barFilteredWordInclusion k A I V p).f n).hom := by
  change Function.Bijective (barFullWordFiltration k A I V p n).subtype
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [barFullWordFiltration_eq_top k A I V h]
  exact Submodule.mem_top

/-- Native component invertibility follows from the full positive inclusion. -/
theorem barFilteredWordInclusion_f_isIso {p n : ℕ} (h : n ≤ p) :
    IsIso ((barFilteredWordInclusion k A I V p).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (barFilteredWordInclusion_f_bijective k A I V h)

/-- The positive lower count stage is full above its original word length. -/
theorem barLowerFiltration_eq_top {p n : ℕ} (h : n + 1 < p) :
    barLowerFiltration k A I V p n = ⊤ := by
  have hp : p ≠ 0 := by omega
  have hb : n + 1 ≤ p - 1 := by omega
  rw [barLowerFiltration, ite_eq_right hp, barWordFiltration_eq_top k A I V hb]

/-- The native positive associated quotient vanishes above the word-length bound. -/
theorem barWordLayer_subsingleton {p n : ℕ} (h : n + 1 < p) :
    Subsingleton (barWordLayer k A I V p n) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [barLowerFiltration_eq_top k A I V h, Submodule.comap_top]

/-- The full positive lower stage includes the original zero augmentation correctly. -/
theorem barFullLowerWordFiltration_eq_top {p n : ℕ} (h : n < p) :
    barFullLowerWordFiltration k A I V p n = ⊤ := by
  have hp : p ≠ 0 := by omega
  have hb : n ≤ p - 1 := by omega
  rw [barFullLowerWordFiltration, ite_eq_right hp, barFullWordFiltration_eq_top k A I V hb]

/-- The full original associated quotient vanishes above its degree bound. -/
theorem barFullWordLayer_subsingleton {p n : ℕ} (h : n < p) :
    Subsingleton (barFullWordLayer k A I V p n) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [barFullLowerWordFiltration_eq_top k A I V h, Submodule.comap_top]

/-- The positive associated complex has no terms above this original bound. -/
theorem barAssociatedWordComplex_isZero {p n : ℕ} (h : n < p) :
    IsZero ((barAssociatedWordComplex k A I V p).X n) := by
  change IsZero (ModuleCat.of k (barFullWordLayer k A I V p n))
  exact ModuleCat.isZero_iff_subsingleton.mpr (barFullWordLayer_subsingleton k A I V h)

end ModuleCat.Algebra.Hochschild.NonUnital
