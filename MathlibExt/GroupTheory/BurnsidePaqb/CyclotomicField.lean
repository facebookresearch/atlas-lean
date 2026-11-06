/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Galois.Basic

/-!
Cyclotomic-field stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/GaloisField.lean`.
-/

namespace BurnsidePaqb

@[expose] public section

open Polynomial

open Classical in
/-- **Cyclotomic subfield of $\mathbb{C}$.** For a natural number $m$, the $m$-th cyclotomic
field is the intermediate field of $\mathbb{C}/\mathbb{Q}$ generated over $\mathbb{Q}$ by the
$m$-th roots of unity, that is, by the complex roots of $X^m - 1$.

For $m = 0$ the polynomial $X^0 - 1$ is zero and is taken to have no roots, so the field is
$\mathbb{Q}$. -/
noncomputable def cycSubfield (m : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ↑(Polynomial.nthRootsFinset m (1 : ℂ))

theorem mem_cycSubfield_of_pow_eq_one (m : ℕ) (hm : m ≠ 0) (ζ : ℂ)
    (h : ζ ^ m = 1) : ζ ∈ cycSubfield m :=
  IntermediateField.subset_adjoin ℚ _
    (Finset.mem_coe.mpr ((Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hm)
      (1 : ℂ)).mpr h))

/-- **$X^m - 1$ over $\mathbb{Q}$ and over $\mathbb{C}$.** For every natural number $m$, mapping
the coefficients of the rational polynomial $X^m - 1$ along the inclusion
$\mathbb{Q} \to \mathbb{C}$ gives the complex polynomial $X^m - 1$. -/
theorem map_X_pow_sub_C_rat (m : ℕ) :
    ((X ^ m - C 1 : ℚ[X]).map (algebraMap ℚ ℂ)) = (X ^ m - C 1 : ℂ[X]) := by
  classical
  simp

/-- **Complex roots of $X^m - 1$.** For every natural number $m \neq 0$, the set of complex roots
of the rational polynomial $X^m - 1$ is exactly the set of $m$-th roots of unity in $\mathbb{C}$. -/
theorem cyc_rootSet (m : ℕ) (hm : m ≠ 0) :
    (X ^ m - C 1 : ℚ[X]).rootSet ℂ =
      ↑(Polynomial.nthRootsFinset m (1 : ℂ)) := by
  classical
  have hCne : (X ^ m - C 1 : ℂ[X]) ≠ 0 := (monic_X_pow_sub_C 1 hm).ne_zero
  have haeval : ∀ ζ : ℂ, aeval ζ (X ^ m - C 1 : ℚ[X]) = 0 ↔ ζ ^ m = 1 := by
    intro ζ
    simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
  ext ζ
  rw [mem_rootSet', map_X_pow_sub_C_rat, Finset.mem_coe,
    Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hm) (1 : ℂ), haeval ζ]
  exact ⟨fun h => h.2, fun h => ⟨hCne, h⟩⟩

/-- **The $m$-th cyclotomic field is a splitting field of $X^m - 1$.** For every natural number
$m \neq 0$, the subfield of $\mathbb{C}$ generated over $\mathbb{Q}$ by the $m$-th roots of unity
is a splitting field over $\mathbb{Q}$ of the polynomial $X^m - 1 \in \mathbb{Q}[X]$. -/
theorem cyc_isSplitting (m : ℕ) (hm : m ≠ 0) :
    (X ^ m - C 1 : ℚ[X]).IsSplittingField ℚ (cycSubfield m) := by
  classical
  refine IntermediateField.isSplittingField_iff.mpr
    ⟨IntermediateField.splits_of_splits ?_ ?_, ?_⟩
  · rw [map_X_pow_sub_C_rat]
    exact IsAlgClosed.splits _
  · intro x hx
    rw [cyc_rootSet m hm, Finset.mem_coe,
      Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hm) (1 : ℂ)] at hx
    exact mem_cycSubfield_of_pow_eq_one m hm x hx
  · rw [cyc_rootSet m hm]
    rfl

/-- **The zeroth cyclotomic field is $\mathbb{Q}$.** For $m = 0$ the cyclotomic subfield of
$\mathbb{C}$ is the bottom intermediate field, that is $\mathbb{Q}$ itself: the polynomial
$X^0 - 1$ is zero and is taken to have no roots, so nothing is adjoined. -/
theorem cycSubfield_zero : cycSubfield 0 = ⊥ := by
  classical
  unfold cycSubfield
  rw [Polynomial.nthRootsFinset_zero, Finset.coe_empty]
  exact IntermediateField.adjoin_empty ℚ ℂ

instance cyc_finiteDimensional (m : ℕ) : FiniteDimensional ℚ (cycSubfield m) := by
  classical
  by_cases hm : m = 0
  · subst hm
    rw [cycSubfield_zero]
    infer_instance
  · have hsplit := cyc_isSplitting m hm
    exact @IsSplittingField.finiteDimensional ℚ _ _ _ _ (X ^ m - C 1 : ℚ[X]) hsplit

instance cyc_isGalois (m : ℕ) : IsGalois ℚ (cycSubfield m) := by
  classical
  by_cases hm : m = 0
  · subst hm
    rw [cycSubfield_zero]
    exact (IntermediateField.botEquiv ℚ ℂ).transfer_galois.mpr (IsGalois.self ℚ)
  · have hsplit := cyc_isSplitting m hm
    have hsep : (X ^ m - C 1 : ℚ[X]).Separable :=
      separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hm) one_ne_zero
    exact @IsGalois.of_separable_splitting_field ℚ _ _ _ _ (X ^ m - C 1 : ℚ[X])
      hsplit hsep

end

end BurnsidePaqb
