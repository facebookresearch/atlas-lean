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

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.NormalizedFrame
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Finite matrix invariance of Hochschild chains

Matrix units form a normalized finite frame. Its coefficient and algebra
sandwiches identify the frame endomorphism with the corner after the finite
trace. The resulting homotopy gives a homotopy equivalence whose maps are
the trace and the chosen corner, for arbitrary compatible bimodules and
independent scalar, algebra, coefficient, index and common lift universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped BigOperators TensorProduct

universe t u v w z

namespace ModuleCat.Algebra.Hochschild.Matrix.Morita

attribute [local instance] Coefficients.leftModule Coefficients.rightModule
  Coefficients.commute Coefficients.leftTower Coefficients.rightTower
  ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k]
  (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

/-- Matrix units at a fixed corner form a normalized frame. -/
theorem matrixUnitNormalization (b : ι) :
    (∑ i : ι, Matrix.single i b (1 : A) * Matrix.single b i (1 : A)) = 1 := by
  simp only [Matrix.single_mul_single_same, one_mul]
  exact Matrix.sum_single_one

private theorem cornerLinear_eq_single {N : Type*} [AddCommGroup N] [Module k N]
    (b : ι) (x : N) : cornerLinear k ι b x = Matrix.single b b x := by
  ext p q
  simp only [cornerLinear_apply, Matrix.single_apply,
    (eq_comm : b = p ↔ p = b), (eq_comm : b = q ↔ q = b), ite_and]
  split_ifs <;> rfl

private theorem matrixUnitAlgebraSandwich (b i j : ι) (a : Matrix ι ι A) :
    Matrix.single b i (1 : A) * a * Matrix.single j b (1 : A) =
      cornerLinear k ι b (a i j) := by
  simp only [Matrix.single_mul_mul_single, one_mul, mul_one, cornerLinear_eq_single]

private theorem matrixUnitCoefficientSandwich (b i j : ι) (X : Matrix ι ι M) :
    Matrix.single b i (1 : A) • (op (Matrix.single j b (1 : A)) • X) =
      cornerLinear k ι b (X i j) := by
  ext p q
  rw [Coefficients.left_smul_apply, cornerLinear_apply]
  simp_rw [Coefficients.right_smul_apply]
  by_cases hp : p = b
  · subst p
    by_cases hq : q = b
    · subst q
      simp [Matrix.single_apply, ite_smul, apply_ite]
    · simp [Matrix.single_apply, hq, Ne.symm hq, ite_smul, apply_ite]
  · simp [Matrix.single_apply, hp, Ne.symm hp, ite_smul, apply_ite]

/-- The corner chain map at an arbitrary common coefficient lift height. -/
def cornerChainMapAt (b : ι) :
    chainComplex k A (ULift.{max u v w z t} M) ⟶
      chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)) :=
  liftedMapAt.{t} (cornerAlgHom k A ι b)
    (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M)
    (corner_left k A M ι b) (corner_right k A M ι b)

/-- Zero additional height retains the original finite corner chain map. -/
@[simp]
theorem cornerChainMapAt_zero (b : ι) :
    cornerChainMapAt.{0} k A M ι b = cornerChainMap k A M ι b := rfl

/-- The lifted corner retains the coefficient-first tensor formula. -/
theorem cornerChainMapAt_f_tprod (b : ι) (n : ℕ) (m : M) (a : Fin n → A) :
    ((cornerChainMapAt.{t} k A M ι b).f n).hom
      (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (cornerLinear k ι b m) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j)) := by
  simpa only [cornerChainMapAt, cornerAlgHom_apply] using
    (liftedMapAt_f_tprod.{_, _, _, _, _, t}
      (cornerAlgHom k A ι b) (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M)
      (corner_left k A M ι b) (corner_right k A M ι b) n (ULift.up m) a)

/-- Removing the coefficient lift gives the literal corner tensor map. -/
theorem cornerChainMapAt_down (b : ι) (n : ℕ)
    (x : ULift.{max u v w z t} M ⊗[k] TensorPower k n A) :
    (show ULift.{max u v w z t} (Matrix ι ι M) ⊗[k]
        TensorPower k n (Matrix ι ι A) ≃ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) from
        coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) n)
      (((cornerChainMapAt.{t} k A M ι b).f n).hom x) =
      cornerTensor k ι b n
        ((show ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
          M ⊗[k] TensorPower k n A from coefficientUnliftEquiv k A M n) x) := by
  let eS : ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A := coefficientUnliftEquiv k A M n
  let eT : ULift.{max u v w z t} (Matrix ι ι M) ⊗[k]
      TensorPower k n (Matrix ι ι A) ≃ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) :=
    coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) n
  have he : eT.toLinearMap.comp ((cornerChainMapAt.{t} k A M ι b).f n).hom =
      (cornerTensor k ι b n).comp eS.toLinearMap := by
    apply tensorPower_ext
    intro m a
    rcases m with ⟨m⟩
    let c : ULift.{max u v w z t} M ⊗[k] TensorPower k n A →ₗ[k]
        ULift.{max u v w z t} (Matrix ι ι M) ⊗[k]
          TensorPower k n (Matrix ι ι A) :=
      ((cornerChainMapAt.{t} k A M ι b).f n).hom
    change eT (c (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      cornerTensor k ι b n (eS (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a))
    have hCorner : c (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        ULift.up (cornerLinear k ι b m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j)) :=
      cornerChainMapAt_f_tprod.{t} k A M ι b n m a
    have hSource : eS (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        m ⊗ₜ[k] PiTensorProduct.tprod k a :=
      coefficientUnliftEquiv_tprod k A M n (ULift.up m) a
    have hTarget : eT (ULift.up (cornerLinear k ι b m) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j))) =
        cornerLinear k ι b m ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j)) :=
      coefficientUnliftEquiv_tprod k (Matrix ι ι A) (Matrix ι ι M) n
        (ULift.up (cornerLinear k ι b m)) (fun j => cornerLinear k ι b (a j))
    have hTensor : cornerTensor k ι b n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        cornerLinear k ι b m ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j)) :=
      cornerTensor_tmul_tprod k ι b n m a
    exact (congrArg eT hCorner).trans
      (hTarget.trans (hTensor.symm.trans ((congrArg (cornerTensor k ι b n) hSource).symm)))
  exact LinearMap.congr_fun he x

/-- The chosen corner followed by the finite trace is the identity at every height. -/
theorem cornerChainMapAt_comp_trace (b : ι) :
    cornerChainMapAt.{t} k A M ι b ≫ traceChainMapAt.{t} k A M ι =
      𝟙 (chainComplex k A (ULift.{max u v w z t} M)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro m a
  rcases m with ⟨m⟩
  let e : ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A := coefficientUnliftEquiv k A M n
  apply e.injective
  change e (traceLinearLiftAt.{t} k A M ι n
      (((cornerChainMapAt.{t} k A M ι b).f n).hom
        (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
    e (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [cornerChainMapAt_f_tprod, traceLinearLiftAt_down,
    coefficientUnliftEquiv_tprod, generalizedTrace_corner_tprod,
    coefficientUnliftEquiv_tprod]

/-- The matrix-unit frame map is the chosen corner after the finite trace. -/
theorem frameMap_eq_traceCorner (b : ι) :
    normalizedFrameChainMapAt.{t} k (Matrix ι ι A) (Matrix ι ι M) ι
      (fun i => Matrix.single i b (1 : A))
      (fun i => Matrix.single b i (1 : A)) (matrixUnitNormalization A ι b) =
      traceChainMapAt.{t} k A M ι ≫ cornerChainMapAt.{t} k A M ι b := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro X a
  rcases X with ⟨X⟩
  let e : ULift.{max u v w z t} (Matrix ι ι M) ⊗[k]
      TensorPower k n (Matrix ι ι A) ≃ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) :=
    coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) n
  apply e.injective
  change e (((normalizedFrameChainMapAt.{t} k (Matrix ι ι A) (Matrix ι ι M) ι
      (fun i => Matrix.single i b (1 : A))
      (fun i => Matrix.single b i (1 : A)) (matrixUnitNormalization A ι b)).f n).hom
        (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    e (((cornerChainMapAt.{t} k A M ι b).f n).hom
      (traceLinearLiftAt.{t} k A M ι n (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a)))
  calc
    _ = ∑ γ : Fin (n + 1) → ι,
        (Matrix.single b (γ 0) (1 : A) •
          (op (Matrix.single (γ 1) b (1 : A)) • X)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j =>
            Matrix.single b (γ j.succ) (1 : A) * a j *
              Matrix.single (γ (j.succ + 1)) b (1 : A)) :=
      normalizedFrameChainMapAt_down_tprod.{t} k (Matrix ι ι A) (Matrix ι ι M) ι
        (fun i => Matrix.single i b (1 : A))
        (fun i => Matrix.single b i (1 : A)) (matrixUnitNormalization A ι b) n X a
    _ = ∑ γ : Fin (n + 1) → ι,
        cornerLinear k ι b (X (γ 0) (γ 1)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j =>
            cornerLinear k ι b (a j (γ j.succ) (γ (j.succ + 1)))) := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [matrixUnitCoefficientSandwich k A M ι b (γ 0) (γ 1) X]
      apply congrArg (fun q : TensorPower k n (Matrix ι ι A) =>
        cornerLinear k ι b (X (γ 0) (γ 1)) ⊗ₜ[k] q)
      apply congrArg (PiTensorProduct.tprod k)
      funext j
      exact matrixUnitAlgebraSandwich k A ι b (γ j.succ) (γ (j.succ + 1)) (a j)
    _ = cornerTensor k ι b n
        (generalizedTrace k ι n (X ⊗ₜ[k] PiTensorProduct.tprod k a)) := by
      rw [generalizedTrace_tmul_tprod, map_sum]
      apply Finset.sum_congr rfl
      intro γ _
      exact (cornerTensor_tmul_tprod k ι b n (X (γ 0) (γ 1))
        (fun j => a j (γ j.succ) (γ (j.succ + 1)))).symm
    _ = e (((cornerChainMapAt.{t} k A M ι b).f n).hom
        (traceLinearLiftAt.{t} k A M ι n (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a))) := by
      rw [cornerChainMapAt_down, traceLinearLiftAt_down, coefficientUnliftEquiv_tprod]

/-- The identity on matrix Hochschild chains is homotopic to the corner after trace. -/
def traceCornerHomotopyAt (b : ι) :
    _root_.Homotopy
      (𝟙 (chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M))))
      (traceChainMapAt.{t} k A M ι ≫ cornerChainMapAt.{t} k A M ι b) :=
  (normalizedFrameChainHomotopyAt.{t} k (Matrix ι ι A) (Matrix ι ι M) ι
    (fun i => Matrix.single i b (1 : A))
    (fun i => Matrix.single b i (1 : A)) (matrixUnitNormalization A ι b)).symm.trans
      (_root_.Homotopy.ofEq (frameMap_eq_traceCorner.{t} k A M ι b))

/-- Finite matrix Hochschild chains are homotopy equivalent to the original coefficient chains. -/
def finiteEquivalenceAt (b : ι) :
    _root_.HomotopyEquiv
      (chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)))
      (chainComplex k A (ULift.{max u v w z t} M)) where
  hom := traceChainMapAt.{t} k A M ι
  inv := cornerChainMapAt.{t} k A M ι b
  homotopyHomInvId := (traceCornerHomotopyAt.{t} k A M ι b).symm
  homotopyInvHomId := _root_.Homotopy.ofEq (cornerChainMapAt_comp_trace.{t} k A M ι b)

@[simp]
theorem finiteEquivalenceAt_hom (b : ι) :
    (finiteEquivalenceAt.{t} k A M ι b).hom = traceChainMapAt.{t} k A M ι := rfl

@[simp]
theorem finiteEquivalenceAt_inv (b : ι) :
    (finiteEquivalenceAt.{t} k A M ι b).inv = cornerChainMapAt.{t} k A M ι b := rfl

/-- The finite matrix homology isomorphism induced by trace and corner. -/
def finiteHomologyIsoAt (b : ι) (n : ℕ) :
    (chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M))).homology n ≅
      (chainComplex k A (ULift.{max u v w z t} M)).homology n :=
  (finiteEquivalenceAt.{t} k A M ι b).toHomologyIso n

@[simp]
theorem finiteHomologyIsoAt_hom (b : ι) (n : ℕ) :
    (finiteHomologyIsoAt.{t} k A M ι b n).hom =
      HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M ι) n := rfl

@[simp]
theorem finiteHomologyIsoAt_inv (b : ι) (n : ℕ) :
    (finiteHomologyIsoAt.{t} k A M ι b n).inv =
      HomologicalComplex.homologyMap (cornerChainMapAt.{t} k A M ι b) n := rfl

end ModuleCat.Algebra.Hochschild.Matrix.Morita
