/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RightCoefficients
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.GroundCoordinates
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Resolution
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Balanced right tensor and enveloping Lie chains

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `N` a right module over `U =
U_R(L)`. Apply the fixed-right balanced tensor functor `N ⊗[U] -` to the enveloping
Chevalley–Eilenberg complex.

Cancelling its regular enveloping factor gives the right-coefficient Lie chain complex. In
degree `n`, the comparison sends the balanced class of `m ⊗ (w ⊗ a)` to `w ⊗ (op(a) • m)`, and
the inverse inserts `1 ∈ U`. These maps commute with the full signed differential. If
`Module.Free R L`, the coefficient homology computes the left-derived balanced tensor functor
at the trivial left `U`-module, with `N` fixed. The coefficient universe is independent.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

variable (N : ModuleCat.{w} (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ)

/-- Commutation of ground scalars with the fixed right tensor action.

For a right `U_R(L)`-module `N`, the restricted `R`-action commutes with the opposite-
enveloping action used to form balanced tensors. -/
local instance rightTensor_smulComm : SMulCommClass R Uᵐᵒᵖ N :=
  rightCoefficients_smulComm R L N

/-- Additivity of the fixed-right enveloping tensor functor.

For a fixed right `U_R(L)`-module `N`, the functor `N ⊗[U_R(L)] -` preserves addition of left
enveloping-module morphisms. -/
local instance rightTensor_additive :
    (ModuleCat.BalancedTensor.functor R U N :
      ModuleCat.{max u v} U ⥤ ModuleCat.{max u v w} R).Additive :=
  ModuleCat.BalancedTensor.additive R U N

/-- The balanced tensor complex of enveloping chains.

Apply `N ⊗[U_R(L)] -` degreewise to the enveloping Chevalley–Eilenberg chain complex, with `N`
a fixed right module. -/
def rightTensorEnvelopingComplex : ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  ((ModuleCat.BalancedTensor.functor R U N).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (envelopingComplex R L)

/-- The cancellation coordinates for right-tensored enveloping chains.

In degree `n`, cancelling the regular `U_R(L)` factor gives an `R`-linear equivalence from the
balanced tensor term to `⋀ⁿ[R] L ⊗[R] N`. -/
def rightTensorCoordinates (n : ℕ) :
    (rightTensorEnvelopingComplex R L N).X n ≃ₗ[R]
      (rightEnvelopingCoefficientComplex R L N).X n :=
  (TensorProduct.Balanced.congr (LinearEquiv.refl R N) (envelopingGroundCoordinates R L n)
    (fun _ _ => rfl) (fun a z => (envelopingCoordinates R L n).map_smul a z)).trans
    ((TensorProduct.Balanced.cancelEquiv R U N (⋀[R]^n L)).trans
      (TensorProduct.comm R N (⋀[R]^n L)))

/-- The balanced representative formula for right tensor coordinates.

The class represented by `m ⊗ (w ⊗ a)` maps to `w ⊗ (op(a) • m)`, where `w ∈ ⋀ⁿ L` and `a ∈
U_R(L)`. -/
theorem rightTensorCoordinates_mk_tmul (n : ℕ) (m : N) (w : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    rightTensorCoordinates R L N n
      (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m (w ⊗ₜ[R] a)) =
        w ⊗ₜ[R] (op a • m) := by
  let e := TensorProduct.Balanced.congr (LinearEquiv.refl R N)
    (envelopingGroundCoordinates R L n)
    (fun _ _ => rfl) (fun a z => (envelopingCoordinates R L n).map_smul a z)
  let c := TensorProduct.Balanced.cancelEquiv R U N (⋀[R]^n L)
  let t := TensorProduct.comm R N (⋀[R]^n L)
  change t (c (e (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m
    (w ⊗ₜ[R] a)))) = _
  have he : e (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m
      (w ⊗ₜ[R] a)) = TensorProduct.Balanced.mk R U N (U ⊗[R] (⋀[R]^n L)) m (a ⊗ₜ[R] w) :=
    (TensorProduct.Balanced.congr_mk (LinearEquiv.refl R N) (envelopingGroundCoordinates R L n)
      (fun _ _ => rfl) (fun a z => (envelopingCoordinates R L n).map_smul a z) m
      (w ⊗ₜ[R] a)).trans
      (congrArg (fun z => TensorProduct.Balanced.mk R U N (U ⊗[R] (⋀[R]^n L)) m z)
        (envelopingGroundCoordinates_tmul R L n w a))
  exact (congrArg (fun z => t (c z)) he).trans
    ((congrArg t (TensorProduct.Balanced.cancelEquiv_mk_tmul R U N (⋀[R]^n L) m a w)).trans
      (TensorProduct.comm_tmul R N (⋀[R]^n L) (MulOpposite.op a • m) w))

/-- The inverse right tensor coordinates on a pure coefficient tensor.

The inverse sends `w ⊗ m` to the balanced class represented by `m ⊗ (w ⊗ 1)`. -/
theorem rightTensorCoordinates_symm_tmul (n : ℕ) (m : N) (w : ⋀[R]^n L) :
    (rightTensorCoordinates R L N n).symm (w ⊗ₜ[R] m) =
      TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m
        (w ⊗ₜ[R] (1 : regularCoefficients R L)) := by
  apply (rightTensorCoordinates R L N n).injective
  have h := rightTensorCoordinates_mk_tmul R L N n m w (1 : regularCoefficients R L)
  have hOne : MulOpposite.op (1 : U) • m = m := by rw [MulOpposite.op_one, one_smul]
  exact ((rightTensorCoordinates R L N n).apply_symm_apply (w ⊗ₜ[R] m)).trans
    (h.trans (congrArg (fun y : rightCoefficients R L N => w ⊗ₜ[R] y) hOne)).symm

/-- The differential on a balanced enveloping tensor class.

The mapped differential sends the class of `m ⊗ z` to the class of `m ⊗ d(z)`, with the
ground-restricted enveloping differential acting on the left module term. -/
theorem rightTensorEnvelopingComplex_d_mk (n : ℕ) (m : N)
    (z : envelopingGroundObject R L (n + 1)) :
    ((rightTensorEnvelopingComplex R L N).d (n + 1) n).hom
      (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m z) =
        TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m
          (envelopingGroundDifferential R L n z) := by
  change (ModuleCat.BalancedTensor.map R U N ((envelopingComplex R L).d (n + 1) n)).hom
    (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m z) = _
  let X := (envelopingComplex R L).X (n + 1)
  let Y := (envelopingComplex R L).X n
  let g : X ⟶ Y := (envelopingComplex R L).d (n + 1) n
  let zX : X := z
  letI : Module R X := Module.compHom X (algebraMap R U)
  letI : Module R Y := Module.compHom Y (algebraMap R U)
  have hMap := ModuleCat.BalancedTensor.map_mk R U N g m zX
  exact hMap.trans
    (congrArg (fun y : Y => TensorProduct.Balanced.mk R U N Y m y)
      (envelopingGroundDifferential_apply R L n z).symm)

/-- Differential compatibility of right tensor cancellation.

For every `n`, the degreewise cancellation equivalences intertwine the balanced tensor
differential and the full right-coefficient Chevalley–Eilenberg differential. -/
theorem rightTensorCoordinates_d (n : ℕ) :
    (rightTensorCoordinates R L N n).toLinearMap.comp
      ((rightTensorEnvelopingComplex R L N).d (n + 1) n).hom =
      (coefficientDifferential R L (rightCoefficients R L N) n).comp
        (rightTensorCoordinates R L N (n + 1)).toLinearMap := by
  letI : Module R ((envelopingComplex R L).X (n + 1)) :=
    Module.compHom ((envelopingComplex R L).X (n + 1)) (algebraMap R U)
  let f : TensorProduct.Balanced R U N ((envelopingComplex R L).X (n + 1)) →ₗ[R]
      (rightEnvelopingCoefficientComplex R L N).X n :=
    (rightTensorCoordinates R L N n).toLinearMap.comp
      ((rightTensorEnvelopingComplex R L N).d (n + 1) n).hom
  let g : TensorProduct.Balanced R U N ((envelopingComplex R L).X (n + 1)) →ₗ[R]
      (rightEnvelopingCoefficientComplex R L N).X n :=
    (coefficientDifferential R L (rightCoefficients R L N) n).comp
      (rightTensorCoordinates R L N (n + 1)).toLinearMap
  change f = g
  apply TensorProduct.Balanced.hom_ext (k := R) (R := U) (M := N)
    (N := (envelopingComplex R L).X (n + 1))
    (P := (rightEnvelopingCoefficientComplex R L N).X n) (f := f) (g := g)
  intro m z
  let zGround : envelopingGroundObject R L (n + 1) := z
  change rightTensorCoordinates R L N n
    (((rightTensorEnvelopingComplex R L N).d (n + 1) n).hom
      (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m zGround)) =
        coefficientDifferential R L (rightCoefficients R L N) n
          (rightTensorCoordinates R L N (n + 1)
            (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m zGround))
  refine (congrArg (rightTensorCoordinates R L N n)
    (rightTensorEnvelopingComplex_d_mk R L N n m zGround)).trans ?_
  let A : envelopingGroundObject R L (n + 1) →ₗ[R]
      (rightEnvelopingCoefficientComplex R L N).X n :=
    (rightTensorCoordinates R L N n).toLinearMap.comp
      ((TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m).comp
        (envelopingGroundDifferential R L n))
  let B : envelopingGroundObject R L (n + 1) →ₗ[R]
      (rightEnvelopingCoefficientComplex R L N).X n :=
    (coefficientDifferential R L (rightCoefficients R L N) n).comp
      ((rightTensorCoordinates R L N (n + 1)).toLinearMap.comp
        (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m))
  change A zGround = B zGround
  induction zGround using TensorProduct.induction_on with
  | zero => exact A.map_zero.trans B.map_zero.symm
  | add z z' hz hz' =>
      exact (A.map_add z z').trans
        ((congrArg₂ (fun x y => x + y) hz hz').trans (B.map_add z z').symm)
  | tmul w a =>
      let F : (⋀[R]^(n + 1) L) →ₗ[R] (rightEnvelopingCoefficientComplex R L N).X n :=
        (rightTensorCoordinates R L N n).toLinearMap.comp
          ((TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m).comp
            ((envelopingGroundDifferential R L n).comp
              (envelopingGroundTmul R L (n + 1) a)))
      let G : (⋀[R]^(n + 1) L) →ₗ[R] (rightEnvelopingCoefficientComplex R L N).X n :=
        (coefficientDifferential R L (rightCoefficients R L N) n).comp
          ((rightTensorCoordinates R L N (n + 1)).toLinearMap.comp
            ((TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m).comp
              (envelopingGroundTmul R L (n + 1) a)))
      have hFG : F = G := by
        apply LinearMap.ext_on_range (exteriorPower.ιMulti_span R (n + 1) L)
        intro v
        change rightTensorCoordinates R L N n
          (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m
            (envelopingGroundDifferential R L n
              (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] a))) =
          coefficientDifferential R L (rightCoefficients R L N) n
            (rightTensorCoordinates R L N (n + 1)
              (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L (n + 1)) m
                (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] a)))
        rw [envelopingGroundDifferential_apply_ιMulti_tmul, rightTensorCoordinates_mk_tmul,
          rightEnvelopingCoefficientDifferential_apply_ιMulti_tmul]
        let H : envelopingGroundObject R L n →ₗ[R]
            (rightEnvelopingCoefficientComplex R L N).X n :=
          (rightTensorCoordinates R L N n).toLinearMap.comp
            (TensorProduct.Balanced.mk R U N (envelopingGroundObject R L n) m)
        change H (_ + _) = _
        rw [H.map_add, map_sum]
        simp only [map_smul]
        have hWord (x : ⋀[R]^n L) (u : regularCoefficients R L) :
            H (x ⊗ₜ[R] u) = x ⊗ₜ[R] (MulOpposite.op u • m) :=
          rightTensorCoordinates_mk_tmul R L N n m x u
        apply congrArg₂ (fun x y : (rightEnvelopingCoefficientComplex R L N).X n => x + y)
        · exact hWord _ _
        · apply Finset.sum_congr rfl
          intro i hi
          change (-1 : R) ^ i.val • H
            (exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R]
              (a * UniversalEnvelopingAlgebra.ι R (v i))) = _
          have hAct : MulOpposite.op (a * UniversalEnvelopingAlgebra.ι R (v i)) • m =
              MulOpposite.op (UniversalEnvelopingAlgebra.ι R (v i)) • (MulOpposite.op a • m) := by
            rw [MulOpposite.op_mul, mul_smul]
          exact congrArg (fun y => (-1 : R) ^ i.val • y)
            ((hWord _ _).trans (congrArg (fun y : rightCoefficients R L N =>
              exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R] y) hAct))
      exact LinearMap.congr_fun hFG w

/-- The chain isomorphism from balanced tensor to right Lie coefficients.

Cancellation of the regular enveloping factor gives an isomorphism from `N ⊗[U_R(L)] C_•` to
the Chevalley–Eilenberg complex of the right enveloping coefficient module. -/
def rightTensorCoefficientIso :
    rightTensorEnvelopingComplex R L N ≅ rightEnvelopingCoefficientComplex R L N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (rightTensorCoordinates R L N n).toModuleIso) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      rw [coefficientComplex_d_succ]
      exact (rightTensorCoordinates_d R L N j).symm)

/-- The fixed-right balanced Tor value for a trivial left module.

For `n ∈ ℕ`, this is the `n`th left-derived value of `N ⊗[U_R(L)] -` on the trivial left
enveloping module, retaining the fixed right coefficient module `N`. -/
abbrev rightEnvelopingTor (n : ℕ) : ModuleCat.{max u v w} R :=
  ((ModuleCat.BalancedTensor.functor R U N).leftDerived n).obj (envelopingTrivialObject R L)

/-- The Tor comparison for right-coefficient Lie homology.

If `Module.Free R L`, degree-`n` homology of the right-coefficient Chevalley–Eilenberg complex
is isomorphic to the `n`th left-derived balanced tensor value at the trivial left
`U_R(L)`-module. -/
def rightCoefficientHomologyIsoTor [Module.Free R L] (n : ℕ) :
    (rightEnvelopingCoefficientComplex R L N).homology n ≅ rightEnvelopingTor R L N n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) n).mapIso
    (rightTensorCoefficientIso R L N).symm ≪≫
      envelopingHomologyIsoLeftDerived R L (ModuleCat.BalancedTensor.functor R U N) n

end ChevalleyEilenberg
