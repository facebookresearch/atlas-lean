/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.EulerianConnesHomology

/-!
# Restrictions of b and B to Eulerian weights

Ranges of normalized rational Eulerian projectors give
the weight spaces. The Hochschild boundary preserves
weight and regular Connes B raises weight by one.
Their restrictions satisfy the square-zero and mixed
identities on these weight columns.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]

/-- The original regular normalized degree space of Eulerian weight i. -/
def normalizedEulerianWeightSpace (n i : ℕ) :
    Submodule k (A ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  LinearMap.range (normalizedEulerianOperator k A A n i)

/-- The original complete Hochschild b restricted to its original unchanged weight. -/
def normalizedEulerianWeightBoundary (n i : ℕ) :
    normalizedEulerianWeightSpace k A (n + 1) i →ₗ[k] normalizedEulerianWeightSpace k A n i :=
  (((normalizedChainComplex k A A).d (n + 1) n).hom.comp
    (normalizedEulerianWeightSpace k A (n + 1) i).subtype).codRestrict _ (by
      intro x
      obtain ⟨y, hy⟩ := x.property
      refine ⟨((normalizedChainComplex k A A).d (n + 1) n).hom y, ?_⟩
      have h := DFunLike.congr_fun (normalizedEulerianOperator_boundary k A A n i) y
      exact h.symm.trans (congrArg ((normalizedChainComplex k A A).d (n + 1) n).hom hy))

/-- The original regular B restricted to its original next weight. -/
def normalizedEulerianWeightConnes (n i : ℕ) :
    normalizedEulerianWeightSpace k A n i →ₗ[k] normalizedEulerianWeightSpace k A (n + 1) (i + 1) :=
  ((regularNormalizedConnes k A n).hom.comp
    (normalizedEulerianWeightSpace k A n i).subtype).codRestrict _ (by
      intro x
      obtain ⟨y, hy⟩ := x.property
      refine ⟨(regularNormalizedConnes k A n).hom y, ?_⟩
      have h := DFunLike.congr_fun (normalizedEulerian_connes_shift k A n i) y
      exact h.symm.trans (congrArg (regularNormalizedConnes k A n).hom hy))

/-- The restricted b retains the literal original complete boundary value. -/
theorem normalizedEulerianWeightBoundary_val (n i : ℕ)
    (x : normalizedEulerianWeightSpace k A (n + 1) i) :
    (normalizedEulerianWeightBoundary k A n i x).val =
      ((normalizedChainComplex k A A).d (n + 1) n).hom x.val := rfl

/-- The restricted B retains the literal original descended Connes value. -/
theorem normalizedEulerianWeightConnes_val (n i : ℕ)
    (x : normalizedEulerianWeightSpace k A n i) :
    (normalizedEulerianWeightConnes k A n i x).val = (regularNormalizedConnes k A n).hom x.val := rfl

/-- The original b-square is inherited by its fixed-weight restriction. -/
theorem normalizedEulerianWeightBoundary_square (n i : ℕ) :
    (normalizedEulerianWeightBoundary k A n i).comp
      (normalizedEulerianWeightBoundary k A (n + 1) i) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, normalizedEulerianWeightBoundary_val,
    Submodule.coe_zero]
  change algebraNormalizedBoundary k A A n (algebraNormalizedBoundary k A A (n + 1) x.val) = 0
  exact congrArg (fun f :
    A ⊗[k] TensorPower k (n + 2) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[A]
    A ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x.val)
      (algebraNormalizedBoundary_comp k A A n)

/-- The original B-square is inherited by its two successive raised weights. -/
theorem normalizedEulerianWeightConnes_square (n i : ℕ) :
    (normalizedEulerianWeightConnes k A (n + 1) (i + 1)).comp
      (normalizedEulerianWeightConnes k A n i) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg ModuleCat.Hom.hom (regularNormalizedConnes_square k A n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, regularNormalizedConnes_hom] at h
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula] at h
  change (normalizedConnesFormula k A (n + 1)).comp (normalizedConnesFormula k A n) = 0 at h
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, normalizedEulerianWeightConnes_val,
    Submodule.coe_zero, regularNormalizedConnes_hom]
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula]
  change normalizedConnesFormula k A (n + 1) (normalizedConnesFormula k A n x.val) = 0
  exact congrArg (fun f :
    A ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[k]
    A ⊗[k] TensorPower k (n + 2) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x.val) h

/-- The bB+Bb equation holds on the literal original Hodge weight-column maps. -/
theorem normalizedEulerianWeight_mixed (n i : ℕ) :
    (normalizedEulerianWeightBoundary k A (n + 1) (i + 1)).comp
        (normalizedEulerianWeightConnes k A (n + 1) i) +
      (normalizedEulerianWeightConnes k A n i).comp (normalizedEulerianWeightBoundary k A n i) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg ModuleCat.Hom.hom (regularNormalizedConnes_mixed k A n)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_zero, regularNormalizedConnes_hom] at h
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula] at h
  change ((algebraNormalizedBoundary k A A (n + 1)).restrictScalars k).comp
      (normalizedConnesFormula k A (n + 1)) +
    (normalizedConnesFormula k A n).comp ((algebraNormalizedBoundary k A A n).restrictScalars k) = 0 at h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.zero_apply,
    normalizedEulerianWeightBoundary_val, normalizedEulerianWeightConnes_val,
    Submodule.coe_add, Submodule.coe_zero, regularNormalizedConnes_hom]
  rw [normalizedConnesBoundary_eq_formula, normalizedConnesBoundary_eq_formula]
  change algebraNormalizedBoundary k A A (n + 1) (normalizedConnesFormula k A (n + 1) x.val) +
    normalizedConnesFormula k A n (algebraNormalizedBoundary k A A n x.val) = 0
  exact congrArg (fun f :
    A ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[k]
    A ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x.val) h

end ModuleCat.Algebra.Hochschild.Symmetric
