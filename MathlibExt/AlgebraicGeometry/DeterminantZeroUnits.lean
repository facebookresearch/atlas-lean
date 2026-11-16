/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules
public import MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants

/-!
# Actual zero-term determinant units

The exterior augmentation evaluates every degree-zero scalar and kills
every original module vector. For a zero module it is an equivalence
from the literal exterior-annihilator determinant to R. These maps are
the zero-factor normalization needed when arbitrary scalar extension
removes some degrees from a bounded perfect presentation's support.

Source: Knudsen--Mumford, Sections 1--2; Stacks Project, Tag 0FJW.
No abstract trivialization of the determinant line is selected.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.DeterminantZeroUnits

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open ProjectiveDeterminantModules

variable (R : Type) [CommRing R] (M : ModuleCat.{0} R)

/-- The actual exterior augmentation, fixed on every original vector. -/
def augmentation : ExteriorAlgebra R M →ₐ[R] R :=
  ExteriorAlgebra.lift R ⟨(0 : M →ₗ[R] R), by intro m; simp⟩

/-- With a zero source module, the native scalar map is inverse to augmentation. -/
theorem scalar_augmentation (h : IsZero M) :
    (Algebra.ofId R (ExteriorAlgebra R M)).comp (augmentation R M) = AlgHom.id _ _ := by
  let := ModuleCat.subsingleton_of_isZero h
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro m
  have hm : m = 0 := Subsingleton.elim _ _
  subst hm
  simp [augmentation]

/-- The original scalar element belongs to the determinant of a zero module. -/
def scalarDeterminant (h : IsZero M) : R →ₗ[R] determinantModule R M :=
  (Algebra.linearMap R (ExteriorAlgebra R M)).codRestrict (determinantSubmodule R M) (by
    let := ModuleCat.subsingleton_of_isZero h
    intro a
    simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]
    intro m
    have hm : m = 0 := Subsingleton.elim _ _
    subst hm
    simp)

/-- The exact zero-module determinant unit, computed by exterior augmentation. -/
def zeroEquiv (h : IsZero M) : determinantModule R M ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap
    ((augmentation R M).toLinearMap.comp (determinantSubmodule R M).subtype)
    (scalarDeterminant R M h)
    (by
      apply LinearMap.ext
      intro a
      exact (augmentation R M).commutes a)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun f : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M ↦ f x.val)
        (scalar_augmentation R M h))

/-- Every scalar generator has its actual coefficient, without a rescaling. -/
theorem zeroEquiv_scalar (h : IsZero M) (a : R) :
    zeroEquiv R M h (scalarDeterminant R M h a) = a :=
  (zeroEquiv R M h).apply_symm_apply a

/-- The actual dual of the scalar module is evaluated on its unit. -/
def dualScalarEquiv : Module.Dual R R ≃ₗ[R] R where
  toFun f := f 1
  invFun a := a • LinearMap.id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    apply LinearMap.ext
    intro a
    change f 1 * a = f a
    rw [mul_comm]
    have h := f.map_smul a (1 : R)
    simpa using h.symm
  right_inv a := by simp

/-- Every zero cochain factor uses the actual exterior or inverse-dual unit map. -/
def termUnit (C : BoundedProjectiveDeterminants.Complex R) (i : ℤ)
    (h : IsZero (C.cochain.X i)) :
    BoundedProjectiveDeterminants.term R C i ≅ 𝟙_ (ModuleCat.{0} R) := by
  classical
  change BoundedProjectiveDeterminants.term R C i ≅ ModuleCat.of R R
  by_cases hi : Even i
  · simpa only [BoundedProjectiveDeterminants.term, hi, ite_true] using
      (zeroEquiv R (C.cochain.X i) h).toModuleIso
  · simpa only [BoundedProjectiveDeterminants.term, hi, ite_false] using
      ((zeroEquiv R (C.cochain.X i) h).symm.dualMap.trans (dualScalarEquiv R)).toModuleIso

/-- Remove precisely the actual zero terms of an ordered degree list. -/
def nonzeroDegrees (C : BoundedProjectiveDeterminants.Complex R) (is : List ℤ) : List ℤ := by
  classical
  exact is.filter (fun i ↦ ¬ IsZero (C.cochain.X i))

/-- The computed zero-factor removal uses native tensor and unit isomorphisms. -/
def removeZeroTerms (C : BoundedProjectiveDeterminants.Complex R) :
    (is : List ℤ) → BoundedProjectiveDeterminants.tensorTerms R C is ≅
      BoundedProjectiveDeterminants.tensorTerms R C (nonzeroDegrees R C is)
  | [] => Iso.refl _
  | i :: is => by
    classical
    by_cases h : IsZero (C.cochain.X i)
    · simpa [nonzeroDegrees, h, BoundedProjectiveDeterminants.tensorTerms] using
        (tensorIso (termUnit R C i h) (removeZeroTerms C is)) ≪≫
          (λ_ (BoundedProjectiveDeterminants.tensorTerms R C (nonzeroDegrees R C is)))
    · simpa [nonzeroDegrees, h, BoundedProjectiveDeterminants.tensorTerms] using
        tensorIso (Iso.refl (BoundedProjectiveDeterminants.term R C i)) (removeZeroTerms C is)

end MathlibExt.AlgebraicGeometry.DeterminantZeroUnits
