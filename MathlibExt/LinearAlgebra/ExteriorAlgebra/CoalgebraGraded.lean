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

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraTensorTriple
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraDiagonal
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseUnitor
public import MathlibExt.Algebra.Category.ModuleCat.UniverseTensorExactness
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Graded exterior coalgebra, counit and coaugmentation

Let R be a commutative ring and M an R-module. Put Eₙ=∧ⁿ_RM and give ℕ-graded R-modules the
convolution tensor product, whose degree n is ⊕_{p+q=n}Eₚ⊗_RE_q. The exterior coproduct
preserves total degree and gives Δₙ:Eₙ → ⊕_{p+q=n}Eₚ⊗_RE_q. Its degree-zero scalar augmentation
supplies a counit, and both counit identities and coassociativity hold under the graded unitors
and associator.

If R,M lie in universes u,v, use the R-module category in max(u,v). The tensor unit is the
canonical lift of R concentrated in degree zero. Coaugmentation sends its scalar r to r·1, the
empty exterior word, and preserves both counit and coproduct.

On the homogeneous tensor component Eₚ⊗E_q, Koszul interchange is a⊗b ↦ (-1)^{pq}b⊗a. It is an
involution and fixes the exterior coproduct, giving graded cocommutativity. These statements
need no freeness, characteristic or factorial-invertibility hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M
local notation "P" => E ⊗[R] E
local notation "𝓔" => gradedExterior R M
local notation "π" => exteriorPower.projection R M
local notation "ε" => (ExteriorAlgebra.algebraMapInv : E →ₐ[R] R)

local instance : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)

open scoped ModuleCat.UniverseTensor

private theorem composeTensorIsoRight {C : Type*} [Category C] [MonoidalCategory C]
    {A B D : C} (f : A ⟶ B) (e : D ≅ B) (X : C) :
    ((f ≫ e.inv) ⊗ₘ 𝟙 X) ≫ e.hom ▷ X = f ⊗ₘ 𝟙 X := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem composeTensorIsoLeft {C : Type*} [Category C] [MonoidalCategory C]
    {A B D : C} (f : A ⟶ B) (e : D ≅ B) (X : C) :
    (𝟙 X ⊗ₘ (f ≫ e.inv)) ≫ X ◁ e.hom = 𝟙 X ⊗ₘ f := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For a commutative ring R in universe u, the category of R-modules in max(u,v) is monoidal closed
for tensor product over R and the internal R-linear Hom. This is the closed structure used for
the exterior graded module of M in universe v. -/
local instance gradedExteriorClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)

/-- For a commutative ring R in universe u, gradedUnit is the ℕ-graded R-module with the canonical
universe lift of R in degree zero and the zero module in every positive degree. Its module
category has universe max(u,v). -/
def gradedUnit : GradedObject ℕ (ModuleCat.{max u v} R) :=
  (GradedObject.single₀ ℕ).obj (ModuleCat.of R (ULift.{v} R))


/-- For a commutative ring R, the degree-zero component of gradedUnit is canonically isomorphic to
the lifted scalar R-module. The lift places the ring from universe u into max(u,v). -/
def gradedUnitZeroIso : (gradedUnit.{u,v} R) 0 ≅ ModuleCat.of R (ULift.{v} R) :=
  GradedObject.singleObjApplyIso 0 (ModuleCat.of R (ULift.{v} R))

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). The equivalence ∧⁰_RM ≃ R, followed by
the inverse projection from the lifted scalar module, gives an isomorphism E₀ ≅ R_lift in the
common module universe. If R and M lie in universes u,v, all categorical modules are placed in
max(u,v); the scalar unit is the canonical lift of R to that universe. -/
def zeroUnitIso : 𝓔 0 ≅ ModuleCat.of R (ULift.{v} R) :=
  ((exteriorPower.zeroEquiv R M).trans
    (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).symm).toModuleIso

theorem augmentation_degree_zero (a : ⋀[R]^0 M) :
    ε (a : E) = exteriorPower.zeroEquiv R M a := by
  have h : (ε).toLinearMap.comp (⋀[R]^0 M).subtype =
      (exteriorPower.zeroEquiv R M).toLinearMap := by
    apply exteriorPower.linearMap_ext (R := R) (n := 0) (M := M) (N := R)
    apply AlternatingMap.ext
    intro w
    change ε (ιMulti R 0 w) =
      exteriorPower.zeroEquiv R M (exteriorPower.ιMulti R 0 w)
    rw [ιMulti_zero_apply, map_one]
    exact (exteriorPower.zeroEquiv_ιMulti (R := R) (M := M) w).symm
  exact LinearMap.congr_fun h a

theorem augmentation_ιMulti_positive (n : ℕ) (w : Fin (n + 1) → M) :
    ε (ιMulti R (n + 1) w) = 0 := by
  rw [ιMulti_succ_apply, map_mul, augmentation_ι, zero_mul]

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For every a ∈ E,
ε(a)=zeroEquiv(π₀(a)), where ε is algebraMapInv, π₀ is the degree-zero exterior projection and
zeroEquiv identifies E₀ with R. -/
theorem augmentation_eq_projection (a : E) :
    ε a = exteriorPower.zeroEquiv R M (π 0 a) := by
  have h : (ε).toLinearMap =
      (exteriorPower.zeroEquiv R M).toLinearMap.comp (π 0) := by
    apply ExteriorAlgebra.lhom_ext
    intro n
    apply AlternatingMap.ext
    intro w
    cases n with
    | zero =>
        change ε (ιMulti R 0 w) = exteriorPower.zeroEquiv R M (π 0 (ιMulti R 0 w))
        rw [exteriorPower.projection_ιMulti_self]
        simp only [ιMulti_zero_apply, map_one, exteriorPower.zeroEquiv_ιMulti]
    | succ n =>
        change ε (ιMulti R (n + 1) w) =
          exteriorPower.zeroEquiv R M (π 0 (ιMulti R (n + 1) w))
        rw [augmentation_ιMulti_positive,
          exteriorPower.projection_ιMulti_ne R M 0 (n + 1) (Nat.succ_ne_zero n), map_zero]
  exact LinearMap.congr_fun h a

theorem augmentation_eq_zero_of_mem_positive (n : ℕ) (hn : n ≠ 0)
    (a : E) (ha : a ∈ ⋀[R]^n M) : ε a = 0 := by
  rw [augmentation_eq_projection, exteriorPower.projection_eq_zero_of_mem R M 0 n hn a ha,
    map_zero]

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). gradedCounit is the degree-preserving
map E• → R_lift[0]. In degree zero it is E₀ ≅ R_lift ≅ gradedUnit₀; in every positive degree it
is zero. If R and M lie in universes u,v, all categorical modules are placed in max(u,v); the
scalar unit is the canonical lift of R to that universe. -/
def gradedCounit : 𝓔 ⟶ (gradedUnit.{u,v} R) := fun n =>
  if hn : n = 0 then by
    subst n
    exact (zeroUnitIso R M).hom ≫ (gradedUnitZeroIso.{u,v} R).inv
  else 0

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). gradedCoaug is the map R_lift[0] → E•
taking a scalar r in degree zero to r·1, the scalar multiple of the empty exterior word. Its
positive-degree components are zero. If R and M lie in universes u,v, all categorical modules
are placed in max(u,v); the scalar unit is the canonical lift of R to that universe. -/
def gradedCoaug : (gradedUnit.{u,v} R) ⟶ 𝓔 := fun n =>
  if hn : n = 0 then by
    subst n
    exact (gradedUnitZeroIso.{u,v} R).hom ≫ (zeroUnitIso R M).inv
  else 0

@[simp]
theorem gradedCounit_zero : gradedCounit R M 0 =
    (zeroUnitIso R M).hom ≫ (gradedUnitZeroIso.{u,v} R).inv := by
  simp only [gradedCounit, dif_pos rfl, dite_true]

theorem gradedCounit_ne (n : ℕ) (hn : n ≠ 0) : gradedCounit R M n = 0 := by
  simp only [gradedCounit, dif_neg hn]

@[simp]
theorem gradedCoaug_zero : gradedCoaug R M 0 =
    (gradedUnitZeroIso.{u,v} R).hom ≫ (zeroUnitIso R M).inv := by
  simp only [gradedCoaug, dif_pos rfl, dite_true]

theorem gradedCoaug_ne (n : ℕ) (hn : n ≠ 0) : gradedCoaug R M n = 0 := by
  simp only [gradedCoaug, dif_neg hn]

theorem gradedCoaug_zero_value (r : (gradedUnit.{u,v} R) 0) :
    ((show ⋀[R]^0 M from (gradedCoaug R M 0).hom r) : E) =
      ((gradedUnitZeroIso.{u,v} R).hom r).down • (1 : E) := by
  change ((exteriorPower.zeroEquiv R M).symm
    (((gradedUnitZeroIso.{u,v} R).hom r).down) : E) = _
  simp only [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul,
    exteriorPower.ιMulti_apply_coe, ιMulti_zero_apply]

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). In total degree n,
gradedLeftCounitEvaluation is (ε⊗id) followed by the graded left unitor Tₙ → Eₙ. It kills every
(p,q)-summand with p>0; the (0,n)-summand is evaluated by the scalar coordinate E₀ ≅ R. -/
def gradedLeftCounitEvaluation (n : ℕ) : tensorDegree R M n ⟶ 𝓔 n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorHom (gradedCounit R M) (𝟙 𝓔) n ≫
    (GradedObject.Monoidal.leftUnitor 𝓔).hom n

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). In total degree n,
gradedRightCounitEvaluation is (id⊗ε) followed by the graded right unitor Tₙ → Eₙ. It kills
every (p,q)-summand with q>0; the (n,0)-summand is evaluated by E₀ ≅ R. -/
def gradedRightCounitEvaluation (n : ℕ) : tensorDegree R M n ⟶ 𝓔 n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorHom (𝟙 𝓔) (gradedCounit R M) n ≫
    (GradedObject.Monoidal.rightUnitor 𝓔).hom n

private theorem unitLeftι_unitor (n : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    GradedObject.Monoidal.ιTensorObj (gradedUnit.{u,v} R) 𝓔 0 n n (zero_add n) ≫
        (GradedObject.Monoidal.leftUnitor 𝓔).hom n =
      ((gradedUnitZeroIso.{u,v} R).hom ▷ 𝓔 n) ≫ (λ_ (𝓔 n)).hom := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.ι_mapBifunctorLeftUnitor_hom_apply (curriedTensor (ModuleCat.{max u v} R)) (𝟙_
    (ModuleCat.{max u
    v} R))
    (leftUnitorNatIso (ModuleCat.{max u v} R)) (fun x : ℕ × ℕ => x.1 + x.2) zero_add 𝓔 n

private theorem unitRightι_unitor (n : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    GradedObject.Monoidal.ιTensorObj 𝓔 (gradedUnit.{u,v} R) n 0 n (add_zero n) ≫
        (GradedObject.Monoidal.rightUnitor 𝓔).hom n =
      (𝓔 n ◁ (gradedUnitZeroIso.{u,v} R).hom) ≫ (ρ_ (𝓔 n)).hom := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.ι_mapBifunctorRightUnitor_hom_apply (curriedTensor (ModuleCat.{max u v} R)) (𝟙_
    (ModuleCat.{max u
    v} R))
    (rightUnitorNatIso (ModuleCat.{max u v} R)) (fun x : ℕ × ℕ => x.1 + x.2) add_zero 𝓔 n

theorem gradedLeftCounitEvaluation_realize (n : ℕ) :
    gradedLeftCounitEvaluation R M n = tensorDegreeRealize R M n ≫ ModuleCat.ofHom
      ((π n).comp ((TensorProduct.lid R E).toLinearMap.comp
        ((ε).toLinearMap.rTensor E))) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply tensorDegree_hom_ext R M n
  intro p q h
  let U : GradedObject ℕ (ModuleCat.{max u v} R) := fun k => ModuleCat.of R (⋀[R]^k M)
  let I : GradedObject ℕ (ModuleCat.{max u v} R) := GradedObject.Monoidal.tensorUnit
  let f : U ⟶ I := gradedCounit R M
  let s : ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶
      GradedObject.Monoidal.tensorObj U U n := tensorDegreeι R M p q n h
  let r : GradedObject.Monoidal.tensorObj U U n ⟶ ModuleCat.of R P := tensorDegreeRealize R M n
  have hTensor : s ≫ GradedObject.Monoidal.tensorHom f (𝟙 U) n =
      (f p ⊗ₘ 𝟙 (U q)) ≫
        GradedObject.Monoidal.ιTensorObj I U p q n h :=
    GradedObject.Monoidal.ι_tensorHom _ _ p q n h
  have hRealize : s ≫ r =
      ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype) :=
    tensorDegreeι_realize R M p q n h
  change s ≫ GradedObject.Monoidal.tensorHom f (𝟙 U) n ≫
    (GradedObject.Monoidal.leftUnitor U).hom n = s ≫ r ≫ _
  rw [← Category.assoc, hTensor]
  rw [reassoc_of% hRealize]
  simp only [Category.assoc]
  dsimp only [f, U, I]
  by_cases hp : p = 0
  · subst p
    have hq : q = n := (zero_add q).symm.trans h
    subst q
    rw [gradedCounit_zero]
    have hu := unitLeftι_unitor R M n
    let e : ModuleCat.of R (⋀[R]^0 M) ≅ ModuleCat.of R (ULift.{v} R) := zeroUnitIso R M
    let z : GradedObject.Monoidal.tensorUnit 0 ≅ ModuleCat.of R (ULift.{v} R) :=
      gradedUnitZeroIso.{u,v} R
    let d : ModuleCat.of R (⋀[R]^0 M) ⟶ GradedObject.Monoidal.tensorUnit 0 := e.hom ≫ z.inv
    have hu' := congrArg (fun x => (d ⊗ₘ 𝟙 (U n)) ≫ x) hu
    have hmap : (d ⊗ₘ 𝟙 (U n)) ≫ (z.hom ▷ U n) = e.hom ⊗ₘ 𝟙 (U n) :=
      composeTensorIsoRight e.hom z (U n)
    have hmap' := congrArg (fun x => x ≫ (λ_ (U n)).hom) hmap
    have hreduce := hu'.trans ((Category.assoc _ _ _).symm.trans hmap')
    exact hreduce.trans (by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      change exteriorPower.zeroEquiv R M a • b = π n (ε (a : E) • (b : E))
      rw [map_smul, exteriorPower.projection_subtype_apply, augmentation_degree_zero])
  · rw [gradedCounit_ne R M p hp]
    have hz : (0 : U p ⟶ I p) ⊗ₘ 𝟙 (U q) = 0 :=
      MonoidalPreadditive.zero_tensor (𝟙 (U q))
    have hzero := congrArg (fun z => z ≫ GradedObject.Monoidal.ιTensorObj I U p q n h ≫
      (GradedObject.Monoidal.leftUnitor U).hom n) hz
    simp only [zero_comp] at hzero
    exact hzero.trans (by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      change (0 : ⋀[R]^n M) = π n
        (ε (a : E) • (b : E))
      rw [augmentation_eq_zero_of_mem_positive R M p hp a a.property, zero_smul, map_zero])

theorem gradedRightCounitEvaluation_realize (n : ℕ) :
    gradedRightCounitEvaluation R M n = tensorDegreeRealize R M n ≫ ModuleCat.ofHom
      ((π n).comp ((TensorProduct.rid R E).toLinearMap.comp
        ((ε).toLinearMap.lTensor E))) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply tensorDegree_hom_ext R M n
  intro p q h
  let U : GradedObject ℕ (ModuleCat.{max u v} R) := fun k => ModuleCat.of R (⋀[R]^k M)
  let I : GradedObject ℕ (ModuleCat.{max u v} R) := GradedObject.Monoidal.tensorUnit
  let f : U ⟶ I := gradedCounit R M
  let s : ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶
      GradedObject.Monoidal.tensorObj U U n := tensorDegreeι R M p q n h
  let r : GradedObject.Monoidal.tensorObj U U n ⟶ ModuleCat.of R P := tensorDegreeRealize R M n
  have hTensor : s ≫ GradedObject.Monoidal.tensorHom (𝟙 U) f n =
      (𝟙 (U p) ⊗ₘ f q) ≫
        GradedObject.Monoidal.ιTensorObj U I p q n h :=
    GradedObject.Monoidal.ι_tensorHom _ _ p q n h
  have hRealize : s ≫ r =
      ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype) :=
    tensorDegreeι_realize R M p q n h
  change s ≫ GradedObject.Monoidal.tensorHom (𝟙 U) f n ≫
    (GradedObject.Monoidal.rightUnitor U).hom n = s ≫ r ≫ _
  rw [← Category.assoc, hTensor]
  rw [reassoc_of% hRealize]
  simp only [Category.assoc]
  dsimp only [f, U, I]
  by_cases hq : q = 0
  · subst q
    have hp : p = n := h
    subst p
    rw [gradedCounit_zero]
    have hu := unitRightι_unitor R M n
    let e : ModuleCat.of R (⋀[R]^0 M) ≅ ModuleCat.of R (ULift.{v} R) := zeroUnitIso R M
    let z : GradedObject.Monoidal.tensorUnit 0 ≅ ModuleCat.of R (ULift.{v} R) :=
      gradedUnitZeroIso.{u,v} R
    let d : ModuleCat.of R (⋀[R]^0 M) ⟶ GradedObject.Monoidal.tensorUnit 0 := e.hom ≫ z.inv
    have hu' := congrArg (fun x => (𝟙 (U n) ⊗ₘ d) ≫ x) hu
    have hmap : (𝟙 (U n) ⊗ₘ d) ≫ (U n ◁ z.hom) = 𝟙 (U n) ⊗ₘ e.hom :=
      composeTensorIsoLeft e.hom z (U n)
    have hmap' := congrArg (fun x => x ≫ (ρ_ (U n)).hom) hmap
    have hreduce := hu'.trans ((Category.assoc _ _ _).symm.trans hmap')
    exact hreduce.trans (by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      change exteriorPower.zeroEquiv R M b • a = π n (ε (b : E) • (a : E))
      rw [map_smul, exteriorPower.projection_subtype_apply, augmentation_degree_zero])
  · rw [gradedCounit_ne R M q hq]
    have hz : 𝟙 (U p) ⊗ₘ (0 : U q ⟶ I q) = 0 :=
      MonoidalPreadditive.tensor_zero (𝟙 (U p))
    have hzero := congrArg (fun z => z ≫ GradedObject.Monoidal.ιTensorObj U I p q n h ≫
      (GradedObject.Monoidal.rightUnitor U).hom n) hz
    simp only [zero_comp] at hzero
    exact hzero.trans (by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      change (0 : ⋀[R]^n M) = π n
        (ε (b : E) • (a : E))
      rw [augmentation_eq_zero_of_mem_positive R M q hq b b.property, zero_smul, map_zero])

theorem gradedCoproduct_leftCounit (n : ℕ) :
    gradedCoproduct R M n ≫ gradedLeftCounitEvaluation R M n = 𝟙 (𝓔 n) := by
  have hr := congrArg (fun z => z ≫ ModuleCat.ofHom ((π n).comp ((TensorProduct.lid R
    E).toLinearMap.comp
    ((ε).toLinearMap.rTensor E))))
    (gradedCoproduct_realize R M n)
  simp only [Category.assoc] at hr
  rw [gradedLeftCounitEvaluation_realize]
  exact hr.trans (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change π n (TensorProduct.lid R E ((ε).toLinearMap.rTensor E
      (coproduct R M ((show ⋀[R]^n M from a) : E)))) = a
    rw [augmentation_rTensor_coproduct, TensorProduct.lid_tmul, one_smul]
    exact exteriorPower.projection_subtype_apply R M n (show ⋀[R]^n M from a))

theorem gradedCoproduct_rightCounit (n : ℕ) :
    gradedCoproduct R M n ≫ gradedRightCounitEvaluation R M n = 𝟙 (𝓔 n) := by
  have hr := congrArg (fun z => z ≫ ModuleCat.ofHom ((π n).comp ((TensorProduct.rid R
    E).toLinearMap.comp
    ((ε).toLinearMap.lTensor E))))
    (gradedCoproduct_realize R M n)
  simp only [Category.assoc] at hr
  rw [gradedRightCounitEvaluation_realize]
  exact hr.trans (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change π n (TensorProduct.rid R E ((ε).toLinearMap.lTensor E
      (coproduct R M ((show ⋀[R]^n M from a) : E)))) = a
    rw [augmentation_lTensor_coproduct, TensorProduct.rid_tmul, one_smul]
    exact exteriorPower.projection_subtype_apply R M n (show ⋀[R]^n M from a))

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). The exterior grading E• is a comonoid
in ℕ-graded R-modules with the convolution tensor product. Its counit is gradedCounit and its
comultiplication is gradedCoproduct. Both counit identities and coassociativity hold with the
graded unitors and associator. If R and M lie in universes u,v, all categorical modules are
placed in max(u,v); the scalar unit is the canonical lift of R to that universe. -/
def gradedComonObj :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    ComonObj 𝓔 := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact
    { counit := gradedCounit R M
      comul := gradedCoproduct R M
      counit_comul := by
        apply (cancel_mono (λ_ 𝓔).hom).mp
        rw [Iso.inv_hom_id]
        apply funext
        intro n
        change (gradedCoproduct R M n ≫ _) ≫ (λ_ (gradedExterior R M)).hom n =
          𝟙 ((gradedExterior R M) n)
        exact (Category.assoc _ _ _).trans (gradedCoproduct_leftCounit R M n)
      comul_counit := by
        apply (cancel_mono (ρ_ 𝓔).hom).mp
        rw [Iso.inv_hom_id]
        apply funext
        intro n
        change (gradedCoproduct R M n ≫ _) ≫ (ρ_ (gradedExterior R M)).hom n =
          𝟙 ((gradedExterior R M) n)
        exact (Category.assoc _ _ _).trans (gradedCoproduct_rightCounit R M n)
      comul_assoc := by
        apply funext
        intro n
        exact gradedCoproduct_coassoc R M n }

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For n : ℕ, gradedKoszulSwap sends the
(p,q)-summand element a⊗b, p+q=n, to (-1)^{p·q}(b⊗a) in the (q,p)-summand. This defines an
R-linear endomorphism of Tₙ. -/
def gradedKoszulSwap (n : ℕ) : tensorDegree R M n ⟶ tensorDegree R M n :=
  tensorDegreeDesc R M n (fun p q h => (-1 : R) ^ (p * q) •
    (ModuleCat.ofHom (TensorProduct.comm R (⋀[R]^p M) (⋀[R]^q M)).toLinearMap ≫
      tensorDegreeι R M q p n (by rw [Nat.add_comm, h])))

@[reassoc]
theorem tensorDegreeι_koszulSwap (p q n : ℕ) (h : p + q = n) :
    tensorDegreeι R M p q n h ≫ gradedKoszulSwap R M n = (-1 : R) ^ (p * q) •
      (ModuleCat.ofHom (TensorProduct.comm R (⋀[R]^p M) (⋀[R]^q M)).toLinearMap ≫
        tensorDegreeι R M q p n (by rw [Nat.add_comm, h])) :=
  tensorDegreeι_desc R M n _ p q h

theorem gradedKoszulSwap_realize (n : ℕ) :
    gradedKoszulSwap R M n ≫ tensorDegreeRealize R M n =
      tensorDegreeRealize R M n ≫ ModuleCat.ofHom (koszulSwap R M).toLinearMap := by
  apply tensorDegree_hom_ext R M n
  intro p q h
  rw [← Category.assoc, tensorDegreeι_koszulSwap, ← Category.assoc, tensorDegreeι_realize]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (tensorDegreeRealize R M n).hom
      ((-1 : R) ^ (p * q) • (tensorDegreeι R M q p n (by omega)).hom (b ⊗ₜ[R] a)) =
    koszulSwap R M ((a : E) ⊗ₜ[R] (b : E))
  have hqp := congrArg (fun f => f.hom (b ⊗ₜ[R] a))
    (tensorDegreeι_realize R M q p n (by omega))
  change (tensorDegreeRealize R M n).hom
      ((tensorDegreeι R M q p n (by omega)).hom (b ⊗ₜ[R] a)) =
    (b : E) ⊗ₜ[R] (a : E) at hqp
  change (tensorDegreeRealize R M n).hom
      ((-1 : R) ^ (p * q) • (tensorDegreeι R M q p n (by omega)).hom (b ⊗ₜ[R] a)) = _
  rw [map_smul, hqp, koszulSwap_tmul]

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). In every n : ℕ, Δₙ followed by
gradedKoszulSwap equals Δₙ. Here Δₙ : Eₙ → Tₙ is the graded exterior coproduct and interchange
of degrees p,q has sign (-1)^{p·q}. -/
theorem gradedCoproduct_cocommutative (n : ℕ) :
    gradedCoproduct R M n ≫ gradedKoszulSwap R M n = gradedCoproduct R M n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply tensorDegreeRealize_injective R M n
  have hs := congrArg (fun f => f.hom ((gradedCoproduct R M n).hom a))
    (gradedKoszulSwap_realize R M n)
  have hd := congrArg (fun f => f.hom a) (gradedCoproduct_realize R M n)
  change (tensorDegreeRealize R M n).hom
      ((gradedKoszulSwap R M n).hom ((gradedCoproduct R M n).hom a)) =
    koszulSwap R M ((tensorDegreeRealize R M n).hom ((gradedCoproduct R M n).hom a)) at hs
  change (tensorDegreeRealize R M n).hom ((gradedCoproduct R M n).hom a) =
    coproduct R M ((show ⋀[R]^n M from a) : E) at hd
  change (tensorDegreeRealize R M n).hom
      ((gradedKoszulSwap R M n).hom ((gradedCoproduct R M n).hom a)) =
    (tensorDegreeRealize R M n).hom ((gradedCoproduct R M n).hom a)
  exact hs.trans ((congrArg (koszulSwap R M) hd).trans
    ((koszulSwap_coproduct R M ((show ⋀[R]^n M from a) : E)).trans hd.symm))

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For every n : ℕ, gradedKoszulSwap on
Tₙ composed with itself is the identity. Its two homogeneous signs multiply to (-1)^{p·q+q·p}=1. -/
theorem gradedKoszulSwap_comp_self (n : ℕ) :
    gradedKoszulSwap R M n ≫ gradedKoszulSwap R M n = 𝟙 (tensorDegree R M n) := by
  apply tensorDegree_hom_ext R M n
  intro p q h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  have hpq := congrArg (fun f => f.hom (a ⊗ₜ[R] b)) (tensorDegreeι_koszulSwap R M p q n h)
  have hqp := congrArg (fun f => f.hom (b ⊗ₜ[R] a))
    (tensorDegreeι_koszulSwap R M q p n (by rw [Nat.add_comm, h]))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_smul, LinearMap.comp_apply,
    LinearMap.smul_apply, ModuleCat.hom_ofHom, TensorProduct.comm_tmul] at hpq hqp
  change (gradedKoszulSwap R M n).hom ((gradedKoszulSwap R M n).hom
      ((tensorDegreeι R M p q n h).hom (a ⊗ₜ[R] b))) =
    (tensorDegreeι R M p q n h).hom (a ⊗ₜ[R] b)
  change (gradedKoszulSwap R M n).hom
      ((gradedKoszulSwap R M n).hom ((tensorDegreeι R M p q n h).hom (a ⊗ₜ[R] b))) = _
  change (gradedKoszulSwap R M n).hom ((tensorDegreeι R M p q n h).hom (a ⊗ₜ[R] b)) =
    (-1 : R) ^ (p * q) • (tensorDegreeι R M q p n (by omega)).hom (b ⊗ₜ[R] a) at hpq
  change (gradedKoszulSwap R M n).hom ((tensorDegreeι R M q p n (by omega)).hom (b ⊗ₜ[R] a)) =
    (-1 : R) ^ (q * p) • (tensorDegreeι R M p q n h).hom (a ⊗ₜ[R] b) at hqp
  rw [hpq, map_smul, hqp, smul_smul]
  have hsign : (-1 : R) ^ (p * q) * (-1 : R) ^ (q * p) = 1 := by
    rw [Nat.mul_comm q p, ← pow_two, ← pow_mul, Nat.mul_comm (p * q) 2, pow_mul]
    simp only [pow_two, neg_mul_neg, mul_one, one_pow]
  rw [hsign, one_smul]

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). The degreewise Koszul maps assemble to
an automorphism of gradedTensorSquare, the grading n ↦ Tₙ. Both its forward and inverse maps are
gradedKoszulSwap. -/
def gradedKoszulSwapIso : gradedTensorSquare R M ≅ gradedTensorSquare R M where
  hom := gradedKoszulSwap R M
  inv := gradedKoszulSwap R M
  hom_inv_id := by
    apply funext
    intro n
    exact gradedKoszulSwap_comp_self R M n
  inv_hom_id := by
    apply funext
    intro n
    exact gradedKoszulSwap_comp_self R M n

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). gradedCoaug followed by gradedCounit
is the identity of gradedUnit. In degree zero this is the pair of inverse scalar-coordinate
isomorphisms; positive-degree unit components are zero modules. -/
theorem gradedCoaug_counit : gradedCoaug R M ≫ gradedCounit R M = 𝟙 (gradedUnit.{u,v} R) := by
  apply funext
  intro n
  by_cases hn : n = 0
  · subst n
    change gradedCoaug R M 0 ≫ gradedCounit R M 0 = 𝟙 ((gradedUnit.{u,v} R) 0)
    rw [gradedCoaug_zero, gradedCounit_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · exact (GradedObject.isInitialSingleObjApply 0 (ModuleCat.of R (ULift.{v} R)) n hn).hom_ext _ _

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). If η is gradedCoaug, Δ is
gradedCoproduct and I=gradedUnit, then η ≫ Δ = λ_I⁻¹ ≫ (η⊗η). The scalar unit's comultiplication
is its inverse left unitor; η sends the scalar empty word to the exterior empty word. -/
theorem gradedCoaug_comul :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    gradedCoaug R M ≫ gradedCoproduct R M = (λ_ (gradedUnit.{u,v} R)).inv ≫
      GradedObject.Monoidal.tensorHom (gradedCoaug R M) (gradedCoaug R M) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply funext
  intro n
  by_cases hn : n = 0
  · subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    apply tensorDegreeRealize_injective R M 0
    have hd := congrArg (fun f => f.hom ((gradedCoaug R M 0).hom r))
      (gradedCoproduct_realize R M 0)
    have hι := congrArg (fun f => f.hom
        (((gradedUnitZeroIso.{u,v} R).inv.hom (ULift.up (1 : R))) ⊗ₜ[R] r))
      (GradedObject.Monoidal.ι_tensorHom (gradedCoaug R M) (gradedCoaug R M) 0 0 0 rfl)
    have hr := congrArg (fun f => f.hom
        (((gradedCoaug R M 0).hom ((gradedUnitZeroIso.{u,v} R).inv.hom (ULift.up (1 : R))))
          ⊗ₜ[R] (gradedCoaug R M 0).hom r))
      (tensorDegreeι_realize R M 0 0 0 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      ModuleCat.UniverseTensor.hom_tensorHom, TensorProduct.map_tmul] at hd hι hr
    have hright : (tensorDegreeRealize R M 0).hom
        ((GradedObject.Monoidal.tensorHom (gradedCoaug R M) (gradedCoaug R M) 0).hom
          (((GradedObject.Monoidal.leftUnitor (gradedUnit.{u,v} R)).inv 0).hom r)) =
        ((show ⋀[R]^0 M from ((gradedCoaug R M 0).hom ((gradedUnitZeroIso.{u,v} R).inv.hom (ULift.up
          (1 : R))))) : E)
          ⊗ₜ[R] ((show ⋀[R]^0 M from (gradedCoaug R M 0).hom r) : E) := by
      rw [GradedObject.Monoidal.leftUnitor_inv_apply]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.UniverseTensor.hom_whiskerRight]
      rw [ModuleCat.UniverseTensor.leftUnitor_inv_apply.{u,v} R ((gradedUnit.{u,v} R) 0) r,
        LinearMap.rTensor_tmul]
      change (tensorDegreeRealize R M 0).hom
          ((GradedObject.Monoidal.tensorHom (gradedCoaug R M) (gradedCoaug R M) 0).hom
            ((GradedObject.Monoidal.ιTensorObj (gradedUnit.{u,v} R) (gradedUnit.{u,v} R)
              0 0 0 rfl).hom
              ((gradedUnitZeroIso.{u,v} R).inv.hom (ULift.up (1 : R)) ⊗ₜ[R] r))) = _
      exact (congrArg (tensorDegreeRealize R M 0).hom hι).trans hr
    have hone : ((show ⋀[R]^0 M from (gradedCoaug R M 0).hom
        ((gradedUnitZeroIso.{u,v} R).inv.hom (ULift.up (1 : R)))) : E) = 1 := by
      rw [gradedCoaug_zero_value]
      have hi := congrArg (fun f => f.hom (ULift.up (1 : R))) (gradedUnitZeroIso.{u,v} R).inv_hom_id
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply, one_smul] using congrArg (fun z : ULift.{v} R => z.down • (1 : E)) hi
    change (tensorDegreeRealize R M 0).hom
        ((gradedCoproduct R M 0).hom ((gradedCoaug R M 0).hom r)) =
      (tensorDegreeRealize R M 0).hom
        ((GradedObject.Monoidal.tensorHom (gradedCoaug R M) (gradedCoaug R M) 0).hom
          (((GradedObject.Monoidal.leftUnitor (gradedUnit.{u,v} R)).inv 0).hom r))
    change (tensorDegreeRealize R M 0).hom
        ((gradedCoproduct R M 0).hom ((gradedCoaug R M 0).hom r)) =
      coproduct R M ((show ⋀[R]^0 M from (gradedCoaug R M 0).hom r) : E) at hd
    rw [hd, hright, hone, gradedCoaug_zero_value, map_smul, coproduct_one,
      TensorProduct.tmul_smul]
  · exact (GradedObject.isInitialSingleObjApply 0 (ModuleCat.of R (ULift.{v} R)) n hn).hom_ext _ _

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). With the scalar-unit comonoid on
gradedUnit and the exterior comonoid on E•, gradedCoaug preserves the counit and coproduct. Its
laws are η ≫ ε = id_I and η ≫ Δ = λ_I⁻¹ ≫ (η⊗η). -/
def gradedCoaugIsComonHom :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    letI : ComonObj (gradedUnit.{u,v} R) := ComonObj.instTensorUnit (GradedObject ℕ (ModuleCat.{max
      u v} R))
    letI : ComonObj 𝓔 := gradedComonObj R M
    IsComonHom (gradedCoaug R M) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  letI : ComonObj (gradedUnit.{u,v} R) := ComonObj.instTensorUnit (GradedObject ℕ (ModuleCat.{max u
    v} R))
  letI : ComonObj 𝓔 := gradedComonObj R M
  exact
    { hom_counit := by
        change gradedCoaug R M ≫ gradedCounit R M = 𝟙 (gradedUnit.{u,v} R)
        exact gradedCoaug_counit R M
      hom_comul := gradedCoaug_comul R M }

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). gradedCoalgebra is the comonoid whose
underlying ℕ-graded module is n ↦ Eₙ and whose structure is gradedComonObj: the exterior
coproduct and degree-zero scalar counit with their counit and coassociativity laws. If R and M
lie in universes u,v, all categorical modules are placed in max(u,v); the scalar unit is the
canonical lift of R to that universe. -/
def gradedCoalgebra :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    Comon (GradedObject ℕ (ModuleCat.{max u v} R)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact { X := 𝓔, comon := gradedComonObj R M }

end ExteriorAlgebra
