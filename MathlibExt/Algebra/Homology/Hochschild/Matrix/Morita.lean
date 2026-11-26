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
# Finite matrix Morita invariance with arbitrary Hochschild coefficients

Let k be a commutative ring, A an associative unital k-algebra and M
an A-bimodule with commuting left and right actions compatible with k.
Let ι be a finite matrix index type with decidable equality and choose
b∈ι. For independent worlds u,v,w,z of k,A,M,ι and an additional
height t, put H=max(u,v,w,z,t).

The Hochschild trace T maps
C_*(Mat_ι(A),ULift^H Mat_ι(M)) → C_*(A,ULift^H M)
by the closed-index-cycle sum. The corner I_b applies the diagonal
entry map E_bb to the coefficient and every algebra factor.
It satisfies T∘I_b=id.

The matrix units μ_i=E_ib and λ_i=E_bi obey ∑_i μ_iλ_i=1.
Their normalized-frame map is I_b∘T, and its conjugation homotopy
gives id≃I_b∘T. Thus trace and corner give a chain homotopy
equivalence and an isomorphism on homology in every degree.
The algebra may be noncommutative, and no projectivity or flatness
of A or M is required.
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

/-- For a ring A, a finite index type ι with decidable equality
and b∈ι, the matrix units satisfy
∑_(i∈ι) E_ib(1) E_bi(1) = 1 in Mat_ι(A).
The multiplication order is μ_iλ_i with μ_i=E_ib and λ_i=E_bi. -/
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

/-- For a commutative ring k, a k-algebra A, a compatible
A-bimodule M, finite ι and b∈ι, the corner at
H=max(u,v,w,z,t) is the chain map
C_*(A,ULift^H M) → C_*(Mat_ι(A),ULift^H Mat_ι(M)).
It applies E_bb to the coefficient and all algebra factors. -/
def cornerChainMapAt (b : ι) :
    chainComplex k A (ULift.{max u v w z t} M) ⟶
      chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)) :=
  liftedMapAt.{t} (cornerAlgHom k A ι b)
    (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M)
    (corner_left k A M ι b) (corner_right k A M ι b)

/-- For a k-algebra A, a compatible A-bimodule M and finite
ι with b∈ι, the corner chain map with t=0 equals the map whose
coefficient height is max(u,v,w,z).
The source, target and degreewise diagonal-entry maps agree. -/
@[simp]
theorem cornerChainMapAt_zero (b : ι) :
    cornerChainMapAt.{0} k A M ι b = cornerChainMap k A M ι b := rfl

/-- For a k-algebra A, a compatible A-bimodule M and finite
ι with b∈ι, the degree-n corner sends
up(m)⊗a₁⊗⋯⊗aₙ to
up(E_bb(m))⊗E_bb(a₁)⊗⋯⊗E_bb(aₙ).
Both coefficient modules are lifted to H=max(u,v,w,z,t). -/
theorem cornerChainMapAt_f_tprod (b : ι) (n : ℕ) (m : M) (a : Fin n → A) :
    ((cornerChainMapAt.{t} k A M ι b).f n).hom
      (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (cornerLinear k ι b m) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => cornerLinear k ι b (a j)) := by
  simpa only [cornerChainMapAt, cornerAlgHom_apply] using
    (liftedMapAt_f_tprod.{_, _, _, _, _, t}
      (cornerAlgHom k A ι b) (cornerLinear k ι b : M →ₗ[k] Matrix ι ι M)
      (corner_left k A M ι b) (corner_right k A M ι b) n (ULift.up m) a)

/-- For a k-algebra A, a compatible A-bimodule M and finite
ι with b∈ι, removing the target coefficient lift after the
degree-n corner equals applying the corner tensor map after
removing the source coefficient lift.
The tensor map is m⊗a₁⊗⋯⊗aₙ ↦ E_bb(m)⊗E_bb(a₁)⊗⋯⊗E_bb(aₙ). -/
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

/-- For a k-algebra A, a compatible A-bimodule M, finite ι
and b∈ι, the corner followed by generalized trace is id on
C_*(A,ULift^H M), with H=max(u,v,w,z,t).
Thus T∘I_b=id as chain maps. -/
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

/-- For a k-algebra A, a compatible A-bimodule M, finite ι
and b∈ι, the normalized-frame endomorphism of matrix Hochschild
chains for μ_i=E_ib and λ_i=E_bi equals I_b∘T.
Its normalization is ∑_i E_ib E_bi=1, and the coefficient
height is H=max(u,v,w,z,t). -/
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

/-- For a k-algebra A, a compatible A-bimodule M, finite ι
and b∈ι, there is a chain homotopy from id on
C_*(Mat_ι(A),ULift^H Mat_ι(M)) to I_b∘T.
It is the normalized matrix-unit frame homotopy, with
H=max(u,v,w,z,t). -/
def traceCornerHomotopyAt (b : ι) :
    _root_.Homotopy
      (𝟙 (chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M))))
      (traceChainMapAt.{t} k A M ι ≫ cornerChainMapAt.{t} k A M ι b) :=
  (normalizedFrameChainHomotopyAt.{t} k (Matrix ι ι A) (Matrix ι ι M) ι
    (fun i => Matrix.single i b (1 : A))
    (fun i => Matrix.single b i (1 : A)) (matrixUnitNormalization A ι b)).symm.trans
      (_root_.Homotopy.ofEq (frameMap_eq_traceCorner.{t} k A M ι b))

/-- For a commutative ring k, a k-algebra A, a compatible
A-bimodule M, finite ι and b∈ι, the matrix coefficient complex
C_*(Mat_ι(A),ULift^H Mat_ι(M)) is homotopy equivalent to
C_*(A,ULift^H M). The forward map is trace T, the inverse is
corner I_b, T I_b=id and I_b T is homotopic to id. -/
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

/-- For a k-algebra A, a compatible A-bimodule M, finite ι,
b∈ι and n≥0, trace and corner induce
H_n(C_*(Mat_ι(A),ULift^H Mat_ι(M))) ≅ H_n(C_*(A,ULift^H M)).
The forward morphism is H_n(T), and the inverse is H_n(I_b),
at the common height H=max(u,v,w,z,t). -/
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
