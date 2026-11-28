/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNative
public import MathlibExt.Algebra.Category.LieModuleCat.Restriction
public import Mathlib.Algebra.Algebra.Opposite

/-!
# Adjoint actions on exterior CE degrees

The adjoint exterior derivation of an R-Lie algebra L restricts in each degree to a Lie
representation on ⋀[R]^n L. On a pure wedge it replaces one entry at a time by [x,v_i], with
all coefficients positive. These representations commute with the CE differential and
therefore define chain endomorphisms.

For a Lie map ι : S → L, negating the restricted action gives the right-adjoint operator, with
pure-wedge entries [v_i,ι(s)]. It is anti-Lie in the ordinary endomorphism ring and becomes a
Lie homomorphism into its opposite ring. Lie maps intertwine the left degree actions.

For the canonical tensor structure on the module category, the chain action is a coderivation
of the CE coproduct: Δ ∘ D_x = (D_x ⊗ 1 + 1 ⊗ D_x) ∘ Δ. Its composite with the counit is zero.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w v'

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

open scoped ModuleCat.UniverseTensor

local instance degreeAdjointFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)

/-- For a commutative ring R : Type u, the canonical tensor structure on ModuleCat.{max u v} R is
monoidal closed. Tensoring with a fixed R-module has the internal R-linear Hom module as a
right adjoint; the tensor unit is the lifted ring object. -/
local instance degreeAdjointMonoidalClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)


/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For n : ℕ,
degreeAdjointAction R L n : L →ₗ⁅R⁆ Module.End R (⋀[R]^n L) is the restriction of
adjointAction to exterior degree n. -/
def degreeAdjointAction (n : ℕ) : L →ₗ⁅R⁆ Module.End R (⋀[R]^n L) where
  toFun x := (adjointAction R L x).restrict
    (fun a ha => adjointAction_mem_exteriorPower R L x n a ha)
  map_add' x y := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change adjointAction R L (x + y) (a : (ExteriorAlgebra R L)) =
      adjointAction R L x (a : (ExteriorAlgebra R L)) + adjointAction R L y (a : (ExteriorAlgebra
        R L))
    simp only [map_add, LinearMap.add_apply]
  map_smul' r x := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change adjointAction R L (r • x) (a : (ExteriorAlgebra R L)) = r • adjointAction R L x (a :
      (ExteriorAlgebra R L))
    simp only [map_smul, LinearMap.smul_apply]
  map_lie' {x y} := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact adjointAction_commutator_apply R L x y a

@[simp]
theorem degreeAdjointAction_coe (n : ℕ) (x : L) (a : ⋀[R]^n L) :
    (degreeAdjointAction R L n x a : (ExteriorAlgebra R L)) = adjointAction R L x (a :
      (ExteriorAlgebra R L)) := rfl

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For n : ℕ, x
: L and v : Fin n → L, degreeAdjointAction n x (ιMulti v) = ∑ i : Fin n,
ιMulti(Function.update v i ⁅x,v_i⁆). All other entries keep their order. -/
theorem degreeAdjointAction_pure (n : ℕ) (x : L) (v : Fin n → L) :
    degreeAdjointAction R L n x (exteriorPower.ιMulti R n v) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅x, v i⁆) := by
  apply Subtype.ext
  simpa only [degreeAdjointAction_coe, Submodule.coe_sum, exteriorPower.ιMulti_apply_coe] using
    adjointAction_ιMulti R L x n v

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For every x
: L, degreeAdjointAction R L 0 x = 0 as an endomorphism of ⋀[R]^0 L. -/
theorem degreeAdjointAction_zero (x : L) : degreeAdjointAction R L 0 x = 0 := by
  apply exteriorPower.linearMap_ext (R := R) (n := 0) (M := L) (N := ⋀[R]^0 L)
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, degreeAdjointAction_pure,
    Finset.univ_eq_empty, Finset.sum_empty, LinearMap.zero_apply]

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For n : ℕ
and x : L, differential R L n ∘ degreeAdjointAction R L (n + 1) x = degreeAdjointAction R L n
x ∘ differential R L n. -/
theorem differential_degreeAdjointAction (n : ℕ) (x : L) :
    (differential R L n).comp (degreeAdjointAction R L (n + 1) x) =
      (degreeAdjointAction R L n x).comp (differential R L n) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp only [LinearMap.comp_apply, differential_coe, degreeAdjointAction_coe]
  exact boundary_adjointAction R L x a

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For n : ℕ,
degreeAdjointModule R L n is the object of LieModuleCat.{max u v} R L with carrier ⋀[R]^n L
and Lie action degreeAdjointAction n. -/
def degreeAdjointModule (n : ℕ) : LieModuleCat.{max u v} R L := by
  letI : LieRingModule L (⋀[R]^n L) :=
    LieRingModule.compLieHom (⋀[R]^n L) (degreeAdjointAction R L n)
  letI : LieModule R L (⋀[R]^n L) :=
    LieModule.compLieHom (⋀[R]^n L) (degreeAdjointAction R L n)
  exact LieModuleCat.of R L (⋀[R]^n L)

@[simp]
theorem degreeAdjointModule_lie (n : ℕ) (x : L) (a : degreeAdjointModule R L n) :
    (⁅x, a⁆ : degreeAdjointModule R L n) = degreeAdjointAction R L n x a := rfl

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L,
degreeAdjointChainMap R L x is an endomorphism of the canonical CE complex with degree-n
component degreeAdjointAction R L n x. The differential-equivariance equation supplies the
chain-map law. -/
def degreeAdjointChainMap (x : L) : ((canonicalChainData R L).complex) ⟶ ((canonicalChainData R
  L).complex) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (degreeAdjointAction R L n x))
    (fun n => by
      have hD : (((canonicalChainData R L).complex).d (n + 1) n) =
          ModuleCat.ofHom (differential R L n) := by
        rw [ChainData.complex_d_succ]
        rfl
      rw [hD]
      have h := congrArg (fun m => ModuleCat.ofHom m)
        (differential_degreeAdjointAction R L n x)
      exact h)

@[simp]
theorem degreeAdjointChainMap_f (x : L) (n : ℕ) :
    (degreeAdjointChainMap R L x).f n = ModuleCat.ofHom (degreeAdjointAction R L n x) := rfl

section Restricted

variable {S : Type w} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Let S be
another R-Lie algebra and ι : S →ₗ⁅R⁆ L. For n : ℕ, rightDegreeAdjointAction R L ι n : S →ₗ[R]
Module.End R (⋀[R]^n L) sends s to −degreeAdjointAction R L n (ι(s)). -/
def rightDegreeAdjointAction (n : ℕ) : S →ₗ[R] Module.End R (⋀[R]^n L) :=
  -((degreeAdjointAction R L n).comp ι).toLinearMap

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Let S be
another R-Lie algebra and ι : S →ₗ⁅R⁆ L. For n : ℕ, s : S and v : Fin n → L,
rightDegreeAdjointAction n s (ιMulti v) = ∑ i : Fin n, ιMulti(Function.update v i ⁅v_i,ι(s)⁆).
Every summand has coefficient +1. -/
theorem rightDegreeAdjointAction_pure (n : ℕ) (s : S) (v : Fin n → L) :
    rightDegreeAdjointAction R L ι n s (exteriorPower.ιMulti R n v) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅v i, ι s⁆) := by
  change -(degreeAdjointAction R L n (ι s) (exteriorPower.ιMulti R n v)) = _
  rw [degreeAdjointAction_pure, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← AlternatingMap.map_update_neg]
  have hLie : -⁅ι s, v i⁆ = ⁅v i, ι s⁆ := lie_skew (v i) (ι s)
  exact congrArg (fun z => exteriorPower.ιMulti R n (Function.update v i z)) hLie

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Let S be
another R-Lie algebra and ι : S →ₗ⁅R⁆ L. For n : ℕ and s, t : S, writing ρ =
rightDegreeAdjointAction n, one has ρ(⁅s,t⁆) = ρ(t) ∘ ρ(s) − ρ(s) ∘ ρ(t). -/
theorem rightDegreeAdjointAction_antiLie (n : ℕ) (s t : S) :
    rightDegreeAdjointAction R L ι n ⁅s, t⁆ =
      (rightDegreeAdjointAction R L ι n t).comp (rightDegreeAdjointAction R L ι n s) -
        (rightDegreeAdjointAction R L ι n s).comp (rightDegreeAdjointAction R L ι n t) := by
  let g := (degreeAdjointAction R L n).comp ι
  change -(g ⁅s, t⁆) = (-g t) * (-g s) - (-g s) * (-g t)
  rw [g.map_lie]
  change -(g s * g t - g t * g s) = (-g t) * (-g s) - (-g s) * (-g t)
  apply LinearMap.ext
  intro a
  change -(g s (g t a) - g t (g s a)) = (-g t) ((-g s) a) - (-g s) ((-g t) a)
  simp only [LinearMap.neg_apply, map_neg, neg_neg]
  exact neg_sub _ _

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Let S be
another R-Lie algebra and ι : S →ₗ⁅R⁆ L. For n : ℕ, rightDegreeAdjointLieHom : S →ₗ⁅R⁆
(Module.End R (⋀[R]^n L))ᵐᵒᵖ sends s to op(rightDegreeAdjointAction n s). Opposite
multiplication converts the reversed commutator law into the Lie-homomorphism law. -/
def rightDegreeAdjointLieHom (n : ℕ) :
    S →ₗ⁅R⁆ (Module.End R (⋀[R]^n L))ᵐᵒᵖ where
  toFun s := MulOpposite.op (rightDegreeAdjointAction R L ι n s)
  map_add' s t := by
    apply MulOpposite.unop_injective
    exact (rightDegreeAdjointAction R L ι n).map_add s t
  map_smul' r s := by
    apply MulOpposite.unop_injective
    exact (rightDegreeAdjointAction R L ι n).map_smul r s
  map_lie' {s t} := by
    apply MulOpposite.unop_injective
    exact rightDegreeAdjointAction_antiLie R L ι n s t

theorem rightDegreeAdjointLieHom_unop_pure (n : ℕ) (s : S) (v : Fin n → L) :
    MulOpposite.unop (rightDegreeAdjointLieHom R L ι n s) (exteriorPower.ιMulti R n v) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅v i, ι s⁆) :=
  rightDegreeAdjointAction_pure R L ι n s v

end Restricted

section Naturality

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For an R-Lie
homomorphism f : L →ₗ⁅R⁆ L', n : ℕ and x : L, ⋀^n f ∘ degreeAdjointAction_L(n,x) =
degreeAdjointAction_L'(n,f(x)) ∘ ⋀^n f. The Lie carriers may lie in different universes. -/
theorem degreeAdjointAction_naturality (f : L →ₗ⁅R⁆ L') (n : ℕ) (x : L) :
    (exteriorPower.map n f.toLinearMap).comp (degreeAdjointAction R L n x) =
      (degreeAdjointAction R L' n (f x)).comp (exteriorPower.map n f.toLinearMap) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp only [LinearMap.comp_apply, exteriorPower.coe_map, degreeAdjointAction_coe]
  exact LinearMap.congr_fun (adjointAction_naturality R L f x) a

end Naturality

private theorem composeAddPost {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (i : A ⟶ B) (f g : B ⟶ B) (r : B ⟶ D) :
    i ≫ (f + g) ≫ r = (i ≫ f) ≫ r + (i ≫ g) ≫ r := by
  have h := Preadditive.comp_add A B B i f g
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ r) h).trans (Preadditive.add_comp A B D (i ≫ f) (i ≫ g) r))

private theorem tensorDegreeAdjoint_realize (x : L) (n : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    (HomologicalComplex.tensorHom (degreeAdjointChainMap R L x) (𝟙 ((canonicalChainData R
      L).complex)) +
        HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex)) (degreeAdjointChainMap
          R L x)).f n ≫
        ExteriorAlgebra.tensorDegreeRealize R L n =
      ExteriorAlgebra.tensorDegreeRealize R L n ≫ ModuleCat.ofHom (tensorAdjointAction R L x) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply ExteriorAlgebra.tensorDegree_hom_ext R L n
  intro p q h
  have hLeft := HomologicalComplex.ιTensorObj_tensorHom
    (degreeAdjointChainMap R L x) (𝟙 ((canonicalChainData R L).complex)) p q n h
  have hRight := HomologicalComplex.ιTensorObj_tensorHom
    (𝟙 ((canonicalChainData R L).complex)) (degreeAdjointChainMap R L x) p q n h
  have hLeft' := congrArg (fun f => f ≫ ExteriorAlgebra.tensorDegreeRealize R L n) hLeft
  have hRight' := congrArg (fun f => f ≫ ExteriorAlgebra.tensorDegreeRealize R L n) hRight
  have hBoth := congrArg₂ (fun f g => f + g) hLeft' hRight'
  have hReal := ExteriorAlgebra.tensorDegreeι_realize R L p q n h
  have hRhs := congrArg (fun f => f ≫ ModuleCat.ofHom (tensorAdjointAction R L x)) hReal
  have hAdd : ExteriorAlgebra.tensorDegreeι R L p q n h ≫
      ((HomologicalComplex.tensorHom (degreeAdjointChainMap R L x)
        (𝟙 ((canonicalChainData R L).complex))).f n +
        (HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex))
          (degreeAdjointChainMap R L x)).f n) ≫ ExteriorAlgebra.tensorDegreeRealize R L n =
      (ExteriorAlgebra.tensorDegreeι R L p q n h ≫
        (HomologicalComplex.tensorHom (degreeAdjointChainMap R L x)
          (𝟙 ((canonicalChainData R L).complex))).f n) ≫ ExteriorAlgebra.tensorDegreeRealize R L n +
      (ExteriorAlgebra.tensorDegreeι R L p q n h ≫
        (HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex))
          (degreeAdjointChainMap R L x)).f n) ≫ ExteriorAlgebra.tensorDegreeRealize R L n := by
    exact composeAddPost
      (ExteriorAlgebra.tensorDegreeι R L p q n h)
      ((HomologicalComplex.tensorHom (degreeAdjointChainMap R L x)
        (𝟙 ((canonicalChainData R L).complex))).f n)
      ((HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex))
        (degreeAdjointChainMap R L x)).f n)
      (ExteriorAlgebra.tensorDegreeRealize R L n)
  exact hAdd.trans (hBoth.trans (by
    have hRealLeft := congrArg (fun f =>
      ((degreeAdjointChainMap R L x).f p ⊗ₘ 𝟙 (((canonicalChainData R L).complex).X q)) ≫ f) hReal
    have hRealRight := congrArg (fun f =>
      (𝟙 (((canonicalChainData R L).complex).X p) ⊗ₘ (degreeAdjointChainMap R L x).f q) ≫ f) hReal
    have hRaw := congrArg₂ (fun f g => f + g) hRealLeft hRealRight
    have hPoint :
        ((degreeAdjointChainMap R L x).f p ⊗ₘ 𝟙 (((canonicalChainData R L).complex).X q)) ≫
          ModuleCat.ofHom (TensorProduct.map (⋀[R]^p L).subtype (⋀[R]^q L).subtype) +
        (𝟙 (((canonicalChainData R L).complex).X p) ⊗ₘ (degreeAdjointChainMap R L x).f q) ≫
          ModuleCat.ofHom (TensorProduct.map (⋀[R]^p L).subtype (⋀[R]^q L).subtype) =
        ModuleCat.ofHom (TensorProduct.map (⋀[R]^p L).subtype (⋀[R]^q L).subtype) ≫
          ModuleCat.ofHom (tensorAdjointAction R L x) := by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro (a : ⋀[R]^p L) (b : ⋀[R]^q L)
      change (adjointAction R L x (a : ExteriorAlgebra R L)) ⊗ₜ[R] (b : ExteriorAlgebra R L) +
        (a : ExteriorAlgebra R L) ⊗ₜ[R] (adjointAction R L x (b : ExteriorAlgebra R L)) =
        tensorAdjointAction R L x ((a : ExteriorAlgebra R L) ⊗ₜ[R] (b : ExteriorAlgebra R L))
      exact (tensorAdjointAction_tmul R L x _ _).symm
    exact hRaw.trans (hPoint.trans hRhs.symm)))

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Use the
canonical tensor structure on ModuleCat.{max u v} R and let D_x be degreeAdjointChainMap R L
x. For the CE coproduct Δ = nativeComplexComul R L, D_x ≫ Δ = Δ ≫ (tensorHom D_x id +
tensorHom id D_x). -/
theorem degreeAdjointChainMap_comul (x : L) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    degreeAdjointChainMap R L x ≫ nativeComplexComul R L = nativeComplexComul R L ≫
      (HomologicalComplex.tensorHom (degreeAdjointChainMap R L x) (𝟙 ((canonicalChainData R
        L).complex)) +
        HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex)) (degreeAdjointChainMap
          R L x)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply HomologicalComplex.hom_ext
  intro n
  have ht := tensorDegreeAdjoint_realize R L x n
  have hd := congrArg (fun g => g.hom) (ExteriorAlgebra.gradedCoproduct_realize R L n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at hd
  have hd_value (b : ⋀[R]^n L) :
      (ExteriorAlgebra.tensorDegreeRealize R L n).hom (((nativeComplexComul R L).f n).hom b) =
        ExteriorAlgebra.coproduct R L (b : (ExteriorAlgebra R L)) := by
    rw [nativeComplexComul_f]
    exact LinearMap.congr_fun hd b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply ExteriorAlgebra.tensorDegreeRealize_injective R L n
  have hf := congrArg (fun g => g.hom) ht
  simp only [ModuleCat.hom_comp] at hf
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hTensor : (ExteriorAlgebra.tensorDegreeRealize R L n).hom
      (((HomologicalComplex.tensorHom (degreeAdjointChainMap R L x)
        (𝟙 ((canonicalChainData R L).complex)) +
        HomologicalComplex.tensorHom (𝟙 ((canonicalChainData R L).complex))
          (degreeAdjointChainMap R L x)).f n).hom
          (((nativeComplexComul R L).f n).hom a)) =
      tensorAdjointAction R L x
        ((ExteriorAlgebra.tensorDegreeRealize R L n).hom (((nativeComplexComul R L).f n).hom a)) :=
    LinearMap.congr_fun hf _
  have hLeft := hd_value (degreeAdjointAction R L n x (show ⋀[R]^n L from a))
  have hRight := hd_value (show ⋀[R]^n L from a)
  change _ = _
  exact hLeft.trans ((coproduct_adjointAction R L x
    ((show ⋀[R]^n L from a) : ExteriorAlgebra R L)).trans
      ((congrArg (tensorAdjointAction R L x) hRight).symm.trans hTensor.symm))

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L,
degreeAdjointChainMap R L x ≫ nativeComplexCounit R L = 0 as a chain map from the canonical CE
complex to its counit target. -/
theorem degreeAdjointChainMap_counit (x : L) :
    degreeAdjointChainMap R L x ≫ nativeComplexCounit R L = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    have hz : (degreeAdjointChainMap R L x).f 0 = 0 := by
      rw [degreeAdjointChainMap_f, degreeAdjointAction_zero, ModuleCat.ofHom_zero]
      rfl
    have hComp := HomologicalComplex.comp_f (degreeAdjointChainMap R L x) (nativeComplexCounit R
      L) 0
    change (degreeAdjointChainMap R L x ≫ nativeComplexCounit R L).f 0 = 0
    exact hComp.trans ((congrArg (fun f => f ≫ (nativeComplexCounit R L).f 0) hz).trans zero_comp)
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R)) n hn).eq_of_tgt _ _

end ChevalleyEilenberg
