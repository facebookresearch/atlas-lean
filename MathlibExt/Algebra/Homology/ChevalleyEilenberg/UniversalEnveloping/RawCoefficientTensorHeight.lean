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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RawCoefficientBoundary
public import MathlibExt.Algebra.Category.LieModuleCat.RightUniversalEnveloping.ULift
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.SquareCoherence
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism

/-!
# Balanced enveloping tensors under universe lifting

Fix a Lie coefficient module over a commutative ground ring and its right enveloping
representation. Balanced tensoring with left enveloping modules commutes with the coefficient,
input, and output universe lifts.

Projective-preserving input lifts and exact output lifts give the corresponding isomorphisms
for left derived functors. The enveloping and ground rings remain fixed.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z t a b c

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] HomologicalComplex.homologyFunctor coefficientComplex

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The input lift from a sufficient carrier universe to a larger one. -/
abbrev rawTensorHeightSourceLift : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z t} U :=
  ModuleCat.uliftFunctor.{max u v v' w w' z t, max u v v' w w' z} U

/-- The output lift, requiring only its exactness. -/
abbrev rawTensorHeightOutputLift : ModuleCat.{max u v v' w w' z} R ⥤ ModuleCat.{max u v v' w w' z t} R :=
  ModuleCat.uliftFunctor.{max u v v' w w' z t, max u v v' w w' z} R


local instance rawTensorHeight_source_preservesHomology {A : Type a} [Ring A] :
    (ModuleCat.uliftFunctor.{c, b} A).PreservesHomology := Functor.preservesHomologyOfExact _
local instance rawTensorHeight_source_preservesProjectives {A : Type a} [Ring A] [Small.{b} A] :
    (ModuleCat.uliftFunctor.{c, b} A).PreservesProjectiveObjects := inferInstance

variable (M : LieModuleCat.{w} R L)


local instance rawTensorHeight_low_additive {A : Type a} [Ring A] [Algebra R A]
    (N : ModuleCat.{b} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, a, b, c} R A N).Additive :=
  ModuleCat.BalancedTensor.additive R A N

/-- The coefficient universe-lift equivalence is linear for the right enveloping action. -/
def rawRightCoefficientHeightEquiv :
  (LieModuleCat.RightUniversalEnveloping.representObj R L
  (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) ≃ₗ[Uᵐᵒᵖ]
  (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
  (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w, max u v v' w w' z t} R L M).trans
    (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w, max u v v' w w' z} R L M).symm

@[simp]
theorem rawRightCoefficientHeightEquiv_up (m : M) :
    rawRightCoefficientHeightEquiv.{u, v, v', w, w', z, t} R L M (ULift.up m) = ULift.up m := rfl

/-- The same right-equivariant equivalence in the exact ground restriction dictionaries used by
the balanced tensor functor. -/
def rawRightCoefficientHeightGroundEquiv :
    (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
  (rawRightCoefficientHeightEquiv.{u, v, v', w, w', z, t} R L M).restrictScalars R

/-- Down on both balanced factors, followed by output up. -/
def rawTensorHeightEquiv (X : ModuleCat.{max u v v' w w' z} U) :
    (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R).obj ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj X) ≃ₗ[R]
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).obj
      ((ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
      : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R).obj X) :=
  (TensorProduct.Balanced.congr
    (rawRightCoefficientHeightGroundEquiv.{u, v, v', w, w', z, t} R L M)
    ((ULift.moduleEquiv : ULift.{max u v v' w w' z t} X ≃ₗ[U] X).restrictScalars R)
    (fun a m =>
      (rawRightCoefficientHeightEquiv.{u, v, v', w, w', z, t} R L M).map_smul (op a) m)
    (fun a x => (ULift.moduleEquiv : ULift.{max u v v' w w' z t} X ≃ₗ[U] X).map_smul a x)).trans
      (ULift.moduleEquiv : ULift.{max u v v' w w' z t}
        ((ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R).obj X) ≃ₗ[R]
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R).obj X).symm

@[simp]
theorem rawTensorHeightEquiv_mk_up (X : ModuleCat.{max u v v' w w' z} U) (m : M) (x : X) :
    rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M X
      (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj
          ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj X)) (ULift.up m) (ULift.up x)) =
      ULift.up
        (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj X) (ULift.up m) x) := by
  let N₀ := LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)
  let I := rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L
  letI : Module R X := Module.compHom X (algebraMap R U)
  letI : Module R (I.obj X) := Module.compHom (I.obj X) (algebraMap R U)
  let eN := rawRightCoefficientHeightGroundEquiv.{u, v, v', w, w', z, t} R L M
  let eX := (ULift.moduleEquiv : ULift.{max u v v' w w' z t} X ≃ₗ[U] X).restrictScalars R
  have hN : ∀ (u : U) (n : N₁), eN (op u • n) = op u • eN n :=
    fun u n => (rawRightCoefficientHeightEquiv.{u, v, v', w, w', z, t} R L M).map_smul (op u) n
  have hX : ∀ (u : U) (x : I.obj X), eX (u • x) = u • eX x :=
    fun u x => (ULift.moduleEquiv : ULift.{max u v v' w w' z t} X ≃ₗ[U] X).map_smul u x
  have h := TensorProduct.Balanced.congr_mk eN eX hN hX
    (show N₁ from ULift.up m) (show I.obj X from ULift.up x)
  exact congrArg (fun p : TensorProduct.Balanced R U N₀ X => ULift.up p) h

@[simp]
theorem rawTensorHeightEquiv_symm_mk_up (X : ModuleCat.{max u v v' w w' z} U) (m : M) (x : X) :
    (rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M X).symm
      (ULift.up
        (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj X) (ULift.up m) x)) =
      TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj
          ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj X)) (ULift.up m) (ULift.up x) := by
  let e := rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M X
  apply e.injective
  exact (e.apply_symm_apply _).trans
    (rawTensorHeightEquiv_mk_up.{u, v, v', w, w', z, t} R L M X m x).symm

/-- Input maps commute with the balanced height coordinates. -/
def rawTensorHeightNatIso : (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L) ⋙
  (ModuleCat.BalancedTensor.functor R U
  (LieModuleCat.RightUniversalEnveloping.representObj R L
  (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
  ModuleCat.{max u v v' w w' z t} R) ≅
  (ModuleCat.BalancedTensor.functor R U
  (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :
  ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R) ⋙
  (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) :=
  NatIso.ofComponents
    (fun X => (rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M X).toModuleIso) (by
      intro X Y h
      apply ModuleCat.hom_ext
      apply TensorProduct.Balanced.hom_ext
      intro m x
      cases m with
      | up m =>
          cases x with
          | up x =>
              change rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M Y
                ((ModuleCat.BalancedTensor.map R U
                  (LieModuleCat.RightUniversalEnveloping.representObj R L
                  (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
                  ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).map h)).hom
                  (TensorProduct.Balanced.mk R U
                    (LieModuleCat.RightUniversalEnveloping.representObj R L
                    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
                    ((ModuleCat.restrictScalars (algebraMap R U)).obj
                      ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj X))
                      (ULift.up m) (ULift.up x))) =
                ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
                  (ModuleCat.BalancedTensor.map R U
                  (LieModuleCat.RightUniversalEnveloping.representObj R L
                  (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) h)).hom
                  (rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M X
                    (TensorProduct.Balanced.mk R U
                      (LieModuleCat.RightUniversalEnveloping.representObj R L
                      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))
                      ((ModuleCat.restrictScalars (algebraMap R U)).obj
                        ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj X))
                        (ULift.up m) (ULift.up x)))
              let N₀ := LieModuleCat.RightUniversalEnveloping.representObj R L
                (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
              let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L
                (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)
              let I := rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L
              let V := rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R
              letI : Module R X := Module.compHom X (algebraMap R U)
              letI : Module R Y := Module.compHom Y (algebraMap R U)
              letI : Module R (I.obj X) := Module.compHom (I.obj X) (algebraMap R U)
              letI : Module R (I.obj Y) := Module.compHom (I.obj Y) (algebraMap R U)
              have hMap := ModuleCat.BalancedTensor.map_mk R U N₁ (I.map h)
                (show N₁ from ULift.up m) (show I.obj X from ULift.up x)
              have hLeft := (congrArg (rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M Y)
                hMap).trans (rawTensorHeightEquiv_mk_up.{u, v, v', w, w', z, t} R L M Y m (h.hom x))
              have hLow := ModuleCat.BalancedTensor.map_mk R U N₀ h
                (show N₀ from ULift.up m) x
              have hRight := congrArg (V.map (ModuleCat.BalancedTensor.map R U N₀ h)).hom
                (rawTensorHeightEquiv_mk_up.{u, v, v', w, w', z, t} R L M X m x)
              exact hLeft.trans (hRight.trans
                (congrArg (fun p : TensorProduct.Balanced R U N₀ Y => ULift.up p) hLow)).symm)

/-- Tor height comparison with the sufficient input universe. Only the input lift receives
projective preservation. -/
def rawCoefficientTorHeightFunctorIso (n : ℕ) :
    (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
      : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R).leftDerived n ⋙
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) ≅
      (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L) ⋙
      (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R).leftDerived n :=
  (ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :
    ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R).leftDerivedCompIsoOfPreservesHomology
    (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) n ≪≫
    NatIso.leftDerived (rawTensorHeightNatIso.{u, v, v', w, w', z, t} R L M).symm n ≪≫
      Functor.leftDerivedPrecompIso (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R) n

/-- The inverse height map is the canonical derived square of the tensor height map, independently
of CE homology. -/
theorem rawCoefficientTorHeightFunctorIso_inv_square (n : ℕ) :
    (rawCoefficientTorHeightFunctorIso.{u, v, v', w, w', z, t} R L M n).inv =
      Functor.leftDerivedSquareHom (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
        (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R)
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R)
        (rawTensorHeightNatIso.{u, v, v', w, w', z, t} R L M).hom n := by
  rw [Functor.leftDerivedSquareHom_of_preservesProjectives]
  unfold rawCoefficientTorHeightFunctorIso
  simp only [Iso.trans_inv, NatIso.leftDerived_inv, Iso.symm_inv, Category.assoc]

/-- The trivial module input is flattened after derivation. -/
def rawEnvelopingTrivialHeightIso :
    (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj
      (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) ≅
      liftedEnvelopingTrivial.{u, v, max u v v' w w' z t} R L :=
  (ModuleCat.uliftFunctorCompIso.{max u v v' w w' z, max u v v' w w' z t, max u v} U).app (envelopingTrivialObject R L)

/-- Tor of the raw coefficient at the two sufficient heights. -/
def rawLieCoefficientTorHeightIsoAt (n : ℕ) :
    (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).obj (rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n) ≅
      rawLieCoefficientTorAt.{u, v, v', w, w', max z t} R L M n :=
  (rawCoefficientTorHeightFunctorIso.{u, v, v', w, w', z, t} R L M n).app
    (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) ≪≫
      ((ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R).leftDerived n).mapIso
        (rawEnvelopingTrivialHeightIso.{u, v, v', w, w', z, t} R L)

/-- The facade inverse first inserts the nested input, then uses the independent canonical derived
height square. -/
theorem rawLieCoefficientTorHeightIsoAt_inv (n : ℕ) :
    (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv =
      ((ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R).leftDerived n).map
        (rawEnvelopingTrivialHeightIso.{u, v, v', w, w', z, t} R L).inv ≫
        (Functor.leftDerivedSquareHom (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
          (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
          (ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
          ModuleCat.{max u v v' w w' z t} R)
          (ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R)
          (rawTensorHeightNatIso.{u, v, v', w, w', z, t} R L M).hom n).app
            (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) := by
  change
    ((ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
    ModuleCat.{max u v v' w w' z t} R).leftDerived n).map _ ≫
    (rawCoefficientTorHeightFunctorIso.{u, v, v', w, w', z, t} R L M n).inv.app _ = _
  rw [rawCoefficientTorHeightFunctorIso_inv_square]

end ChevalleyEilenberg
