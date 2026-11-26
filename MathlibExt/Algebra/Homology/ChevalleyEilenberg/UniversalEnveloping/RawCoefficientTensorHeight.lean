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
# Raising coefficient and input heights in balanced tensor functors

Keep the ground ring and enveloping ring fixed. Raising H to H' lifts the right coefficient
representation and the left input module. The two coefficient representations are
right-equivariantly equivalent, and down on the balanced factors followed by output up gives
F_H'(I_U X) ≅ V_R(F_H X).

These coordinates are natural in X. The source lift preserves projective objects, and the
output lift preserves homology, so the underived tensor square gives (F_H.leftDerived n) ⋙ V_R
≅ I_U ⋙ (F_H'.leftDerived n). Evaluating at the lifted trivial module and flattening its
repeated input lift gives the Tor height comparison. Its inverse is the independently derived
tensor square after the trivial-input insertion.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z t a b c

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Let R be commutative and L an R-Lie algebra, with U its enveloping ring. For H = max u v v' w
w' z and H' = max H t, rawTensorHeightSourceLift is ModuleCat.{H} U ⥤ ModuleCat.{H'} U given
by the module ULift functor. -/
abbrev rawTensorHeightSourceLift : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z t} U :=
  ModuleCat.uliftFunctor.{max u v v' w w' z t, max u v v' w w' z} U

/-- For a commutative R, H = max u v v' w w' z and H' = max H t, rawTensorHeightOutputLift is the
module ULift functor ModuleCat.{H} R ⥤ ModuleCat.{H'} R, which preserves homology. -/
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

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. rawRightCoefficientHeightEquiv : N_H' ≃ₗ[Uᵐᵒᵖ] N_H
is the larger coefficient lift down to M followed by the smaller coefficient lift up. -/
def rawRightCoefficientHeightEquiv :
  (LieModuleCat.RightUniversalEnveloping.representObj R L
  (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) ≃ₗ[Uᵐᵒᵖ]
  (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
  (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w, max u v v' w w' z t} R L M).trans
    (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w, max u v v' w w' z} R L M).symm

@[simp]
theorem rawRightCoefficientHeightEquiv_up (m : M) :
    rawRightCoefficientHeightEquiv.{u, v, v', w, w', z, t} R L M (ULift.up m) = ULift.up m := rfl

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. Restricting rawRightCoefficientHeightEquiv to R
gives an R-linear equivalence between the two ground-restricted coefficient carriers used by
F_H' and F_H. -/
def rawRightCoefficientHeightGroundEquiv :
    (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
  (rawRightCoefficientHeightEquiv.{u, v, v', w, w', z, t} R L M).restrictScalars R

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. For X : ModuleCat.{H} U, rawTensorHeightEquiv
identifies F_H'(I_U X) with V_R(F_H X). It sends a balanced class [m',x'] to
ULift.up[θ(m'),x'.down], where θ : N_H' ≃ₗ[Uᵐᵒᵖ] N_H is the coefficient height equivalence. -/
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

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. The objectwise coordinates give
rawTensorHeightNatIso : I_U ⋙ F_H' ≅ F_H ⋙ V_R. -/
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

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. For n : ℕ, rawCoefficientTorHeightFunctorIso is
(F_H.leftDerived n) ⋙ V_R ≅ I_U ⋙ (F_H'.leftDerived n). It uses projective preservation for
I_U and homology preservation for V_R. -/
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

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. For n : ℕ, rawCoefficientTorHeightFunctorIso.inv
equals Functor.leftDerivedSquareHom for I_U, V_R and rawTensorHeightNatIso.hom. -/
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

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. rawEnvelopingTrivialHeightIso identifies I_U(T_H)
with T_H', the trivial enveloping module at the larger height, by
ModuleCat.uliftFunctorCompIso. -/
def rawEnvelopingTrivialHeightIso :
    (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj
      (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) ≅
      liftedEnvelopingTrivial.{u, v, max u v v' w w' z t} R L :=
  (ModuleCat.uliftFunctorCompIso.{max u v v' w w' z, max u v v' w w' z t, max u v} U).app (envelopingTrivialObject R L)

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. For n : ℕ, rawLieCoefficientTorHeightIsoAt
identifies V_R(Tor_H(M,n)) with Tor_H'(M,n), using the derived height functor isomorphism at
T_H followed by the map of the trivial-input flattening. -/
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

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra and M : LieModuleCat.{w} R L. Put H
= max u v v' w w' z and H' = max H t. Let I_U and V_R be the source and output ULift functors
from H to H', N_H,N_H' the right representations of the two coefficient lifts, and F_H,F_H'
their fixed-right balanced tensor functors. The inverse is (F_H'.leftDerived
n).map(rawEnvelopingTrivialHeightIso.inv) followed by the component at T_H of
leftDerivedSquareHom(I_U,V_R,rawTensorHeightNatIso.hom). -/
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
