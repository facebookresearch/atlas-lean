/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraGrading
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.GradedObject.Monoidal

/-!
# Tensor degrees of the exterior grading

The degree `n` tensor object combines the pairs of exterior degrees whose sum
is `n`. Its realization maps into the ordinary tensor product of exterior
algebras. A finite sum of homogeneous projections gives a lift, and the
realization is injective. These maps realize the exterior coproduct as a
morphism of the native graded module objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M
local notation "P" => E ⊗[R] E
local notation "π" => exteriorPower.projection R M

/-- The original exterior grading in the canonical working module category. -/
def gradedExterior : GradedObject ℕ (ModuleCat.{max u v} R) := fun n => ModuleCat.of R (⋀[R]^n M)

/-- Degree `n` of the actual native tensor of the exterior grading. -/
def tensorDegree (n : ℕ) : (ModuleCat.{max u v} R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.tensorObj (gradedExterior R M) (gradedExterior R M) n

/-- The actual native antidiagonal summand inclusion, with its original tensor module. -/
def tensorDegreeι (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶ tensorDegree R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.ιTensorObj (gradedExterior R M) (gradedExterior R M) p q n h

/-- The actual native tensor descent, specialized to original exterior summands. -/
def tensorDegreeDesc (n : ℕ) {A : (ModuleCat.{max u v} R)}
    (f : ∀ p q (h : p + q = n), ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶ A) :
    tensorDegree R M n ⟶ A := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.tensorObjDesc f

@[reassoc]
theorem tensorDegreeι_desc (n : ℕ) {A : (ModuleCat.{max u v} R)}
    (f : ∀ p q (h : p + q = n), ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶ A)
    (p q : ℕ) (h : p + q = n) :
    tensorDegreeι R M p q n h ≫ tensorDegreeDesc R M n f = f p q h := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.ι_tensorObjDesc
    (X₁ := gradedExterior R M) (X₂ := gradedExterior R M) f p q h

theorem tensorDegree_hom_ext (n : ℕ) {A : (ModuleCat.{max u v} R)}
    {f g : tensorDegree R M n ⟶ A}
    (hfg : ∀ p q (h : p + q = n), tensorDegreeι R M p q n h ≫ f =
      tensorDegreeι R M p q n h ≫ g) : f = g := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.tensorObj_ext f g hfg

/-- Native realization includes each original homogeneous tensor summand in `E ⊗ E`. -/
def tensorDegreeRealize (n : ℕ) : tensorDegree R M n ⟶ ModuleCat.of R P :=
  tensorDegreeDesc R M n (fun p q _ =>
    ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype))

@[reassoc]
theorem tensorDegreeι_realize (p q n : ℕ) (h : p + q = n) :
    tensorDegreeι R M p q n h ≫ tensorDegreeRealize R M n =
      ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype) :=
  tensorDegreeι_desc R M n _ p q h

/-- The finite antidiagonal projection lift into the actual native tensor degree. -/
def tensorDegreeLift (n : ℕ) : ModuleCat.of R P ⟶ tensorDegree R M n :=
  ∑ p : Fin (n + 1), ModuleCat.ofHom (TensorProduct.map (π p.val) (π (n - p.val))) ≫
    tensorDegreeι R M p.val (n - p.val) n (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt))

/-- Realizing the native lift is the already constructed finite tensor reconstruction. -/
theorem tensorDegreeLift_realize (n : ℕ) :
    tensorDegreeLift R M n ≫ tensorDegreeRealize R M n =
      ModuleCat.ofHom (degreeTensorReconstruction R M n) := by
  apply ModuleCat.hom_ext
  simp only [tensorDegreeLift, Preadditive.sum_comp, Category.assoc,
    tensorDegreeι_realize, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  rfl

/-- Realization followed by the finite native lift is the identity in its actual degree. -/
theorem tensorDegreeRealize_lift (n : ℕ) :
    tensorDegreeRealize R M n ≫ tensorDegreeLift R M n = 𝟙 (tensorDegree R M n) := by
  apply tensorDegree_hom_ext R M n
  intro i j hij
  rw [tensorDegreeι_realize_assoc]
  unfold tensorDegreeLift
  rw [Preadditive.comp_sum]
  have hi : i < n + 1 := Nat.lt_succ_of_le (Nat.le.intro hij)
  let p : Fin (n + 1) := ⟨i, hi⟩
  have hni : n - p.val = j := by change n - i = j; rw [← hij, Nat.add_sub_cancel_left]
  rw [Finset.sum_eq_single p]
  · have hmaps : (TensorProduct.map (π i) (π j)).comp
        (TensorProduct.map (⋀[R]^i M).subtype (⋀[R]^j M).subtype) = LinearMap.id := by
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply,
        exteriorPower.projection_subtype_apply, LinearMap.id_apply]
    subst j
    have hc : ModuleCat.ofHom
        (TensorProduct.map (⋀[R]^i M).subtype (⋀[R]^(n - p.val) M).subtype) ≫
        ModuleCat.ofHom (TensorProduct.map (π i) (π (n - p.val))) =
        𝟙 (ModuleCat.of R ((⋀[R]^i M) ⊗[R] (⋀[R]^(n - p.val) M))) := by
      apply ModuleCat.hom_ext
      exact hmaps
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ tensorDegreeι R M i (n - p.val) n hij) hc).trans
        (Category.id_comp _))
  · intro q hq hqp
    have hiq : i ≠ q.val := fun hiq => hqp (Fin.ext hiq.symm)
    have hmaps : (TensorProduct.map (π q.val) (π (n - q.val))).comp
        (TensorProduct.map (⋀[R]^i M).subtype (⋀[R]^j M).subtype) = 0 := by
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply,
        exteriorPower.projection_eq_zero_of_mem R M q.val i hiq a a.property,
        TensorProduct.zero_tmul, LinearMap.zero_apply]
    rw [← Category.assoc, ← ModuleCat.ofHom_comp, hmaps, ModuleCat.ofHom_zero,
      zero_comp]
  · intro hp
    exact False.elim (hp (Finset.mem_univ p))

/-- The native tensor degree realizes as a split injection, requiring no flatness. -/
theorem tensorDegreeRealize_injective (n : ℕ) :
    Function.Injective (tensorDegreeRealize R M n).hom := by
  apply Function.LeftInverse.injective
  intro x
  exact congrArg (fun f => f.hom x) (tensorDegreeRealize_lift R M n)

/-- The native lift recovers every actual total-degree tensor. -/
theorem tensorDegreeRealize_lift_of_mem (n : ℕ) (t : P) (ht : t ∈ coproductDegree R M n) :
    (tensorDegreeRealize R M n).hom ((tensorDegreeLift R M n).hom t) = t := by
  have h := congrArg (fun f => f.hom t) (tensorDegreeLift_realize R M n)
  exact h.trans (degreeTensorReconstruction_of_mem R M n t ht)

/-- The actual native tensor-square grading, with its canonical fixed dictionaries. -/
def gradedTensorSquare : GradedObject ℕ (ModuleCat.{max u v} R) := tensorDegree R M

/-- The actual exterior coproduct assembled into the native graded tensor object. -/
def gradedCoproduct : gradedExterior R M ⟶ gradedTensorSquare R M := fun n =>
  ModuleCat.ofHom ((coproduct R M).comp (⋀[R]^n M).subtype) ≫ tensorDegreeLift R M n

/-- Its characteristic equation is the actual exterior coproduct in every degree. -/
theorem gradedCoproduct_realize (n : ℕ) :
    gradedCoproduct R M n ≫ tensorDegreeRealize R M n =
      ModuleCat.ofHom ((coproduct R M).comp (⋀[R]^n M).subtype) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let a₀ : ⋀[R]^n M := a
  exact tensorDegreeRealize_lift_of_mem R M n _
    (coproduct_mem_degree R M n (a₀ : E) a₀.property)

end ExteriorAlgebra
