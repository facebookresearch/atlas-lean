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

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNative

/-!
# Lie maps preserve the exterior chain coalgebra

Let R:Type u be commutative and L,L′ R-Lie algebras in a common
carrier universe v. A Lie homomorphism f:L→L′ gives the chain map
F_n=Λ_R^n f on canonical Chevalley–Eilenberg chains.

For the primitive chain coproducts and counits,
Γ_{L′}F=(F⊗F)Γ_L and ε_{L′}F=ε_L.
The coaugmentations satisfy Fu_L=u_{L′}. Thus F is a comonoid
morphism in the signed tensor category of nonnegative R-module
complexes at height max{u,v}. The ground universe u is independent
of the common Lie-carrier universe v.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

open scoped ModuleCat.UniverseTensor

local instance coalgebraNaturalityFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)

/-- For R:Type u commutative and any universe v, the tensor product
on ModuleCat.{max u v}R is closed, with internal R-linear Hom
right adjoint to tensoring by a module. -/
local instance coalgebraNaturalityMonoidalClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)
variable {L' L'' : Type v} [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']

/-- Let R be commutative and L,L′ R-Lie algebras in the same
carrier universe v. Let f:L→L′ be a Lie homomorphism and
F_n=Λ_R^n f its exterior chain maps.
The exterior maps Λ_R^n f define a chain map between the
canonical Chevalley–Eilenberg complexes C_*(L) and C_*(L′). -/
def nativeComplexMap (f : L →ₗ⁅R⁆ L') : ((canonicalChainData R L).complex) ⟶ ((canonicalChainData R
  L').complex) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (exteriorPower.map n f.toLinearMap))
    (fun n => by
      rw [ChainData.complex_d_succ, ChainData.complex_d_succ]
      exact congrArg ModuleCat.ofHom (differential_naturality R L f n))

@[simp]
theorem nativeComplexMap_f (f : L →ₗ⁅R⁆ L') (n : ℕ) :
    (nativeComplexMap R L f).f n = ModuleCat.ofHom (exteriorPower.map n f.toLinearMap) := rfl

theorem nativeComplexMap_f_ιMulti (f : L →ₗ⁅R⁆ L') (n : ℕ) (w : Fin n → L) :
    ((nativeComplexMap R L f).f n).hom (exteriorPower.ιMulti R n w) =
      exteriorPower.ιMulti R n (f ∘ w) := exteriorPower.map_apply_ιMulti f.toLinearMap w

private theorem tensorMap_realize (f : L →ₗ⁅R⁆ L') (n : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    (HomologicalComplex.tensorHom (nativeComplexMap R L f) (nativeComplexMap R L f)).f n ≫
        ExteriorAlgebra.tensorDegreeRealize R L' n =
      ExteriorAlgebra.tensorDegreeRealize R L n ≫ ModuleCat.ofHom
        (TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap
          (ExteriorAlgebra.map f.toLinearMap).toLinearMap) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply ExteriorAlgebra.tensorDegree_hom_ext R L n
  intro p q h
  change HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
    ((canonicalChainData R L).complex) p q n h ≫ _ = _
  have hT := HomologicalComplex.ιTensorObj_tensorHom
    (nativeComplexMap R L f) (nativeComplexMap R L f) p q n h
  have hT' := congrArg (fun z => z ≫ ExteriorAlgebra.tensorDegreeRealize R L' n) hT
  exact (Category.assoc _ _ _).symm.trans (hT'.trans (by
    have hReal := ExteriorAlgebra.tensorDegreeι_realize R L' p q n h
    have hReal' := congrArg (fun z =>
      ((nativeComplexMap R L f).f p ⊗ₘ (nativeComplexMap R L f).f q) ≫ z) hReal
    have hSource := congrArg (fun z => z ≫ ModuleCat.ofHom
      (TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap
        (ExteriorAlgebra.map f.toLinearMap).toLinearMap))
      (ExteriorAlgebra.tensorDegreeι_realize R L p q n h)
    have hRaw :
        ((nativeComplexMap R L f).f p ⊗ₘ (nativeComplexMap R L f).f q) ≫
          ModuleCat.ofHom (TensorProduct.map (⋀[R]^p L').subtype (⋀[R]^q L').subtype) =
        ModuleCat.ofHom (TensorProduct.map (⋀[R]^p L).subtype (⋀[R]^q L).subtype) ≫
          ModuleCat.ofHom (TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap
            (ExteriorAlgebra.map f.toLinearMap).toLinearMap) := by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro (a : ⋀[R]^p L) (b : ⋀[R]^q L)
      change TensorProduct.map (⋀[R]^p L').subtype (⋀[R]^q L').subtype
          (TensorProduct.map (exteriorPower.map p f.toLinearMap) (exteriorPower.map q f.toLinearMap)
            (a ⊗ₜ[R] b)) =
        TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap
          (ExteriorAlgebra.map f.toLinearMap).toLinearMap
          (TensorProduct.map (⋀[R]^p L).subtype (⋀[R]^q L).subtype (a ⊗ₜ[R] b))
      simp only [TensorProduct.map_tmul, exteriorPower.coe_map, Submodule.subtype_apply,
        AlgHom.toLinearMap_apply]
    exact hReal'.trans (hRaw.trans hSource.symm)))

/-- Let R be commutative and L,L′ R-Lie algebras in the same
carrier universe v. Let f:L→L′ be a Lie homomorphism and
F_n=Λ_R^n f its exterior chain maps.
The primitive chain coproducts satisfy the square
Γ_{L′}F=(F⊗F)Γ_L. -/
theorem nativeComplexMap_comul (f : L →ₗ⁅R⁆ L') :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    nativeComplexMap R L f ≫ nativeComplexComul R L' = nativeComplexComul R L ≫
      HomologicalComplex.tensorHom (nativeComplexMap R L f) (nativeComplexMap R L f) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply ExteriorAlgebra.tensorDegreeRealize_injective R L' n
  have htarget := congrArg (fun m => m.hom (exteriorPower.map n f.toLinearMap a))
    (ExteriorAlgebra.gradedCoproduct_realize R L' n)
  have hsource := congrArg (fun m => m.hom a) (ExteriorAlgebra.gradedCoproduct_realize R L n)
  have htensor := congrArg (fun m => m.hom ((ExteriorAlgebra.gradedCoproduct R L n).hom a))
    (tensorMap_realize R L f n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply] at htarget hsource htensor
  change (ExteriorAlgebra.tensorDegreeRealize R L' n).hom
    ((ExteriorAlgebra.gradedCoproduct R L' n).hom (exteriorPower.map n f.toLinearMap a)) =
    ExteriorAlgebra.coproduct R L'
      (exteriorPower.map n f.toLinearMap a : ExteriorAlgebra R L') at htarget
  change (ExteriorAlgebra.tensorDegreeRealize R L n).hom
    ((ExteriorAlgebra.gradedCoproduct R L n).hom a) =
    ExteriorAlgebra.coproduct R L ((show ⋀[R]^n L from a) : ExteriorAlgebra R L) at hsource
  change (ExteriorAlgebra.tensorDegreeRealize R L' n).hom
      ((ExteriorAlgebra.gradedCoproduct R L' n).hom (exteriorPower.map n f.toLinearMap a)) =
    (ExteriorAlgebra.tensorDegreeRealize R L' n).hom
      (((HomologicalComplex.tensorHom (nativeComplexMap R L f) (nativeComplexMap R L f)).f n).hom
        ((ExteriorAlgebra.gradedCoproduct R L n).hom a))
  have hcoe : (exteriorPower.map n f.toLinearMap (show ⋀[R]^n L from a) : ExteriorAlgebra R L') =
      ExteriorAlgebra.map f.toLinearMap ((show ⋀[R]^n L from a) : ExteriorAlgebra R L) :=
    exteriorPower.coe_map f.toLinearMap (show ⋀[R]^n L from a)
  exact htarget.trans ((congrArg (ExteriorAlgebra.coproduct R L') hcoe).trans (by

    exact (ExteriorAlgebra.coproduct_naturality R L f.toLinearMap
      ((show ⋀[R]^n L from a) : ExteriorAlgebra R L)).symm.trans
      ((congrArg (TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap
        (ExteriorAlgebra.map f.toLinearMap).toLinearMap) hsource).symm.trans htensor.symm)))

/-- Let R be commutative and L,L′ R-Lie algebras in the same
carrier universe v. Let f:L→L′ be a Lie homomorphism and
F_n=Λ_R^n f its exterior chain maps.
The chain counits satisfy ε_{L′}F=ε_L. -/
theorem nativeComplexMap_counit (f : L →ₗ⁅R⁆ L') :
    nativeComplexMap R L f ≫ nativeComplexCounit R L' = nativeComplexCounit R L := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, nativeComplexMap_f, nativeComplexCounit_f, nativeComplexCounit_f]
  by_cases hn : n = 0
  · subst n
    rw [ExteriorAlgebra.gradedCounit_zero, ExteriorAlgebra.gradedCounit_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have h := LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality f.toLinearMap) a
    change (unitGradingIso.{u,v} R).hom 0
        ((ExteriorAlgebra.gradedUnitZeroIso.{u,v} R).inv
          (ULift.up (exteriorPower.zeroEquiv R L' (exteriorPower.map 0 f.toLinearMap a)))) =
      (unitGradingIso.{u,v} R).hom 0
        ((ExteriorAlgebra.gradedUnitZeroIso.{u,v} R).inv (ULift.up (exteriorPower.zeroEquiv R L a)))
    have hPoint := congrArg (fun r : R => (unitGradingIso.{u,v} R).hom 0
      ((ExteriorAlgebra.gradedUnitZeroIso.{u,v} R).inv (ULift.up r))) h
    exact hPoint
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R)) n hn).eq_of_tgt _ _

/-- Let R be commutative and L,L′ R-Lie algebras in the same
carrier universe v. Let f:L→L′ be a Lie homomorphism and
F_n=Λ_R^n f its exterior chain maps.
The chain coaugmentations satisfy Fu_L=u_{L′}. -/
theorem nativeComplexMap_coaug (f : L →ₗ⁅R⁆ L') :
    nativeComplexCoaug R L ≫ nativeComplexMap R L f = nativeComplexCoaug R L' := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    apply Subtype.ext
    have hComp := HomologicalComplex.comp_f (nativeComplexCoaug R L) (nativeComplexMap R L f) 0
    have hComp' := congrArg (fun g => g.hom r) hComp
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, nativeComplexMap_f,
      ModuleCat.hom_ofHom] at hComp'
    let a : ⋀[R]^0 L := (nativeComplexCoaug R L).f 0 r
    let b : ⋀[R]^0 L' := (nativeComplexCoaug R L').f 0 r
    have hValue : exteriorPower.map 0 f.toLinearMap a = b := by
      apply Subtype.ext
      have hcoe := exteriorPower.coe_map f.toLinearMap a
      have hA := nativeComplexCoaug_zero_value R L r
      have hB := nativeComplexCoaug_zero_value R L' r
      have hAmbient : ExteriorAlgebra.map f.toLinearMap (a : ExteriorAlgebra R L) =
          (b : ExteriorAlgebra R L') := by
        rw [hA, hB, map_smul, map_one]
      exact hcoe.trans hAmbient
    exact (congrArg Subtype.val hComp').trans (congrArg Subtype.val hValue)
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R)) n hn).eq_of_src _ _

/-- Let R be commutative and L,L′ R-Lie algebras in the same
carrier universe v. Let f:L→L′ be a Lie homomorphism and
F_n=Λ_R^n f its exterior chain maps.
The coproduct and counit squares make F:C_*(L)→C_*(L′)
a comonoid morphism in the signed tensor category of R-module chains. -/
def nativeComplexMapIsComonHom (f : L →ₗ⁅R⁆ L') :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
      (R := R)
    letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
    letI : ComonObj ((canonicalChainData R L').complex) := nativeComonObj R L'
    IsComonHom (nativeComplexMap R L f) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
  letI : ComonObj ((canonicalChainData R L').complex) := nativeComonObj R L'
  exact ⟨nativeComplexMap_counit R L f, nativeComplexMap_comul R L f⟩

@[simp]
theorem nativeComplexMap_id : nativeComplexMap R L (LieHom.id : L →ₗ⁅R⁆ L) = 𝟙 ((canonicalChainData
  R L).complex) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [nativeComplexMap_f]
  change ModuleCat.ofHom (exteriorPower.map n (LinearMap.id : L →ₗ[R] L)) = 𝟙 _
  rw [exteriorPower.map_id]
  rfl

theorem nativeComplexMap_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    nativeComplexMap R L f ≫ nativeComplexMap R L' g = nativeComplexMap R L (g.comp f) := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := congrArg ModuleCat.ofHom (exteriorPower.map_comp (n := n) f.toLinearMap g.toLinearMap)
  change ((nativeComplexMap R L f).f n ≫ (nativeComplexMap R L' g).f n) =
    (nativeComplexMap R L (g.comp f)).f n
  rw [nativeComplexMap_f, nativeComplexMap_f, nativeComplexMap_f]
  exact h.symm

end ChevalleyEilenberg
