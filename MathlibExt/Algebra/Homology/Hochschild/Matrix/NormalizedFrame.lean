/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.TraceLift
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.BlockTrace
public import MathlibExt.Algebra.Homology.Hochschild.Conjugation
public import MathlibExt.LinearAlgebra.Matrix.SplitInvolution

/-!
# Finite normalized frames act trivially up to Hochschild homotopy

Let k be a commutative ring, A an associative unital k-algebra, and M an
A-bimodule with commuting k-linear actions. Let J be a finite index type
and μ, λ : J → A satisfy ∑ᵢ μᵢ λᵢ = 1. On I = PUnit ⊕ J these data
give a block unit c whose conjugation carries the PUnit corner of x to
the J×J block with entries λᵢ x μⱼ. On coefficients the corresponding
entries are λᵢ • (op(μⱼ) • m).

At the common height H = max(u,v,w,z,t), the corner map, conjugation by c
and finite matrix trace define an endomorphism F of C_*(A,ULift^H M).
Its degree-n value, after removing the coefficient lift, is
∑_(i₀,…,iₙ) (λ_(i₀) • (op(μ_(i₁)) • m)) ⊗
(λ_(i₁) a₁ μ_(i₂)) ⊗ ⋯ ⊗ (λ_(iₙ) aₙ μ_(i₀)).
The unit-conjugation homotopy gives a chain homotopy F ≃ id.
The universes of k, A, M and J and the extra height t are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe t u v w z

namespace ModuleCat.Algebra.Hochschild.Matrix

attribute [local instance] Coefficients.leftModule Coefficients.rightModule
  Coefficients.commute Coefficients.leftTower Coefficients.rightTower
  ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k]
  (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  (J : Type z) [Fintype J] [DecidableEq J]

local notation "I" => PUnit ⊕ J
local notation "b" => (Sum.inl PUnit.unit : I)

/-- Let k be a commutative ring, A a k-algebra, M an A-bimodule
with commuting k-linear actions and J a finite index type. At
H = max(u,v,w,z,t), the PUnit corner in I = PUnit ⊕ J gives
C_*(A,ULift^H M) → C_*(Mat_I(A),ULift^H Mat_I(M)).
Its components put each coefficient and algebra factor in the
distinguished diagonal entry b = inl(*). -/
def cornerChainMapAt :
    chainComplex k A (ULift.{max u v w z t} M) ⟶
      chainComplex k (Matrix I I A) (ULift.{max u v w z t} (Matrix I I M)) :=
  liftedMapAt.{t} (cornerAlgHom k A I b) (cornerLinear k I b : M →ₗ[k] Matrix I I M)
    (corner_left k A M I b) (corner_right k A M I b)

/-- For the coefficient Hochschild complexes over a k-algebra A
and a compatible A-bimodule M, the PUnit corner into matrices indexed
by I = PUnit ⊕ J followed by finite trace is the identity chain map.
Both coefficient modules are lifted to H = max(u,v,w,z,t). -/
theorem cornerChainMapAt_comp_trace :
    cornerChainMapAt.{t} k A M J ≫ traceChainMapAt.{t} k A M I =
      𝟙 (chainComplex k A (ULift.{max u v w z t} M)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro m a
  let e : ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A := coefficientUnliftEquiv k A M n
  apply e.injective
  change e (((traceChainMapAt.{t} k A M I).f n).hom
      (((cornerChainMapAt.{t} k A M J).f n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
    e (m ⊗ₜ[k] PiTensorProduct.tprod k a)
  have hc : ((cornerChainMapAt.{t} k A M J).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (cornerLinear k I b m.down) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i => cornerLinear k I b (a i)) := by
    change ((liftedMapAt.{t} (cornerAlgHom k A I b)
      (cornerLinear k I b : M →ₗ[k] Matrix I I M)
      (corner_left k A M I b) (corner_right k A M I b)).f n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
    simpa only [cornerAlgHom_apply] using
      (liftedMapAt_f_tprod.{_, _, _, _, _, t} (cornerAlgHom k A I b)
        (cornerLinear k I b : M →ₗ[k] Matrix I I M)
        (corner_left k A M I b) (corner_right k A M I b) n m a)
  rw [hc]
  change e (traceLinearLiftAt.{t} k A M I n
      (ULift.up (cornerLinear k I b m.down) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i => cornerLinear k I b (a i)))) = _
  calc
    _ = generalizedTrace k I n
        (cornerLinear k I b m.down ⊗ₜ[k]
          PiTensorProduct.tprod k (fun i => cornerLinear k I b (a i))) := by
      rw [traceLinearLiftAt_down, coefficientUnliftEquiv_tprod]
    _ = m.down ⊗ₜ[k] PiTensorProduct.tprod k a :=
      generalizedTrace_corner_tprod k I b n m.down a
    _ = _ := (coefficientUnliftEquiv_tprod k A M n m a).symm
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M] [Algebra k A] in
/-- Let M have left A- and right A-actions, let
I = PUnit ⊕ J be finite, and let c be a unit of Mat_I(A).
For b = inl(*), the (i,j) entry of
c⁻¹ • (op(c) • E_bb(m)) is
(c⁻¹)_(i,b) • (op(c_(b,j)) • m).
This identity uses the two coefficient actions without requiring
them to commute or to form scalar towers over k. -/
theorem conjugation_coefficient_corner_entry (c : (Matrix I I A)ˣ) (m : M) (i j : I) :
    letI := Coefficients.leftModule A M I
    letI := Coefficients.rightModule A M I
    (c.inv • (op c.val • cornerLinear k I b m)) i j =
      c.inv i b • (op (c.val b j) • m) := by
  letI := Coefficients.leftModule A M I
  letI := Coefficients.rightModule A M I
  rw [Coefficients.left_smul_apply]
  have hz (p : I) (hp : p ≠ b) : c.inv i p • (op c.val • cornerLinear k I b m) p j = 0 := by
    have hr : (op c.val • cornerLinear k I b m) p j = 0 := by
      rw [Coefficients.right_smul_apply]
      apply Finset.sum_eq_zero
      intro q hq
      rw [cornerLinear_apply]
      simp only [hp, ite_false, smul_zero]
    rw [hr, smul_zero]
  rw [Fintype.sum_eq_single b hz]
  have hz' (q : I) (hq : q ≠ b) : op (c.val q j) • cornerLinear k I b m b q = 0 := by
    rw [cornerLinear_apply]
    simp only [ite_true, hq, ite_false, smul_zero]
  rw [Coefficients.right_smul_apply]
  simp only [unop_op]
  rw [Fintype.sum_eq_single b hz', cornerLinear_apply]
  simp only [ite_true]

variable (μ «λ» : J → A) (h : (∑ i, μ i * «λ» i) = 1)
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M] [Algebra k A] in

/-- Let μ, λ : J → A satisfy ∑ᵢ μᵢ λᵢ = 1, with J finite,
and let M have left and right A-actions. Conjugating E_bb(m) by the
normalized-frame block unit on PUnit ⊕ J gives a matrix whose only
possibly nonzero block is the J×J block
(i,j) ↦ λᵢ • (op(μⱼ) • m).
No commutation or k-scalar-tower condition on these actions is needed
for this entry formula. -/
theorem normalizedFrame_coefficient_corner (m : M) :
    letI := Coefficients.leftModule A M I
    letI := Coefficients.rightModule A M I
    (Matrix.normalizedFrameUnit μ «λ» h).inv •
        (op (Matrix.normalizedFrameUnit μ «λ» h).val • cornerLinear k I b m) =
      Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0
        (Matrix.of (fun i j : J => «λ» i • (op (μ j) • m))) := by
  letI := Coefficients.leftModule A M I
  letI := Coefficients.rightModule A M I
  ext i j
  rw [conjugation_coefficient_corner_entry]
  cases i with
  | inl i =>
    cases i
    cases j with
    | inl j =>
      cases j
      simp only [Matrix.normalizedFrameUnit_inv_inl_inl,
        Matrix.normalizedFrameUnit_val_inl_inl, Matrix.fromBlocks_apply₁₁,
        Matrix.zero_apply, zero_smul]
    | inr j =>
      simp only [Matrix.normalizedFrameUnit_inv_inl_inl,
        Matrix.normalizedFrameUnit_val_inl_inr, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, zero_smul]
  | inr i =>
    cases j with
    | inl j =>
      cases j
      simp only [Matrix.normalizedFrameUnit_inv_inr_inl,
        Matrix.normalizedFrameUnit_val_inl_inl, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, op_zero, zero_smul, smul_zero]
    | inr j =>
      simp only [Matrix.normalizedFrameUnit_inv_inr_inl,
        Matrix.normalizedFrameUnit_val_inl_inr, Matrix.fromBlocks_apply₂₂,
        Matrix.of_apply]

/-- For a k-algebra A, an A-bimodule M with commuting k-linear
actions, finite J and μ, λ : J → A satisfying ∑ᵢ μᵢ λᵢ = 1,
the normalized-frame endomorphism of C_*(A,ULift^H M) is the composite
of the PUnit corner, conjugation by the frame block unit on PUnit ⊕ J,
and the generalized trace. Here H = max(u,v,w,z,t). -/
def normalizedFrameChainMapAt :
    chainComplex k A (ULift.{max u v w z t} M) ⟶
      chainComplex k A (ULift.{max u v w z t} M) :=
  cornerChainMapAt.{t} k A M J ≫
    Conjugation.chainMap (M := ULift.{max u v w z t} (Matrix I I M)) k
      (Matrix.normalizedFrameUnit μ «λ» h) ≫
    traceChainMapAt.{t} k A M I

/-- Let μ, λ : J → A satisfy ∑ᵢ μᵢ λᵢ = 1, and let M be an
A-bimodule with commuting k-linear actions. The normalized-frame
endomorphism F of C_*(A,ULift^H M) has a chain homotopy from F to id,
where H = max(u,v,w,z,t). It is the conjugation homotopy composed
with the PUnit corner on the source and finite trace on the target. -/
def normalizedFrameChainHomotopyAt :
    _root_.Homotopy (normalizedFrameChainMapAt.{t} k A M J μ «λ» h)
      (𝟙 (chainComplex k A (ULift.{max u v w z t} M))) := by
  let c := Matrix.normalizedFrameUnit μ «λ» h
  let H := ((Conjugation.chainHomotopy
      (M := ULift.{max u v w z t} (Matrix I I M)) k c).compLeft
        (cornerChainMapAt.{t} k A M J)).compRight (traceChainMapAt.{t} k A M I)
  have hf : (cornerChainMapAt.{t} k A M J ≫
      Conjugation.chainMap (M := ULift.{max u v w z t} (Matrix I I M)) k c) ≫
      traceChainMapAt.{t} k A M I = normalizedFrameChainMapAt.{t} k A M J μ «λ» h :=
    Category.assoc _ _ _
  have hg : (cornerChainMapAt.{t} k A M J ≫
      𝟙 (chainComplex k (Matrix I I A) (ULift.{max u v w z t} (Matrix I I M)))) ≫
      traceChainMapAt.{t} k A M I = 𝟙 (chainComplex k A (ULift.{max u v w z t} M)) := by
    rw [Category.comp_id, cornerChainMapAt_comp_trace]
  exact ((_root_.Homotopy.ofEq hf).symm.trans H).trans (_root_.Homotopy.ofEq hg)
omit [Fintype J] [DecidableEq J] in

/-- For x ∈ A and I = PUnit ⊕ J, the diagonal matrix E_bb(x),
b = inl(*), equals the block matrix with x in its PUnit×PUnit block
and zero in the other three blocks. This equality does not require
J to be finite. -/
theorem normalizedFrame_corner_eq (x : A) :
    cornerLinear k I b x = Matrix.normalizedFrameCorner (J := J) x := by
  ext i j
  cases i with
  | inl i =>
    cases i
    cases j with
    | inl j =>
      cases j
      simp only [cornerLinear_apply, Matrix.normalizedFrameCorner,
        Matrix.fromBlocks_apply₁₁, Matrix.of_apply, ite_true]
    | inr j =>
      simp only [cornerLinear_apply, Matrix.normalizedFrameCorner,
        Matrix.fromBlocks_apply₁₂, Sum.inr_ne_inl, ite_false, ite_true, Matrix.zero_apply]
  | inr i =>
    cases j with
    | inl j =>
      cases j
      simp only [cornerLinear_apply, Matrix.normalizedFrameCorner,
        Matrix.fromBlocks_apply₂₁, Sum.inr_ne_inl, ite_false, Matrix.zero_apply]
    | inr j =>
      simp only [cornerLinear_apply, Matrix.normalizedFrameCorner,
        Matrix.fromBlocks_apply₂₂, Sum.inr_ne_inl, ite_false, Matrix.zero_apply]

/-- For a k-algebra A, finite J and μ, λ : J → A with
∑ᵢ μᵢ λᵢ = 1, conjugation of E_bb(x) by the normalized-frame block
unit on PUnit ⊕ J gives the block matrix with J×J entries λᵢ x μⱼ
and zero in all other blocks. The multiplication order is retained
for a noncommutative A. -/
theorem normalizedFrame_algebra_corner (x : A) :
    Conjugation.algebraMap k (Matrix.normalizedFrameUnit μ «λ» h) (cornerAlgHom k A I b x) =
      Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0
        (Matrix.of (fun i j : J => «λ» i * x * μ j)) := by
  rw [Conjugation.algebraMap_apply, cornerAlgHom_apply, normalizedFrame_corner_eq]
  exact Matrix.normalizedFrameUnit_conjugateCorner μ «λ» h x

/-- Let M be an A-bimodule with commuting k-linear actions and
let μ, λ : J → A satisfy ∑ᵢ μᵢ λᵢ = 1. For m ∈ M and
a₁,…,aₙ ∈ A, remove the target coefficient lift from the degree-n
normalized-frame map applied to up(m) ⊗ a₁ ⊗ ⋯ ⊗ aₙ. The result is
∑_(i₀,…,iₙ) (λ_(i₀) • (op(μ_(i₁)) • m)) ⊗
(λ_(i₁) a₁ μ_(i₂)) ⊗ ⋯ ⊗ (λ_(iₙ) aₙ μ_(i₀)).
The sum is over J-valued cycles with indices modulo n+1, and the
coefficient height is H = max(u,v,w,z,t). -/
theorem normalizedFrameChainMapAt_down_tprod
    (n : ℕ) (m : M) (a : Fin n → A) :
    (show ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A from coefficientUnliftEquiv k A M n)
      (((normalizedFrameChainMapAt.{t} k A M J μ «λ» h).f n).hom
        (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ∑ γ : Fin (n + 1) → J,
        («λ» (γ 0) • (op (μ (γ 1)) • m)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j =>
            «λ» (γ j.succ) * a j * μ (γ (j.succ + 1))) := by
  let c := Matrix.normalizedFrameUnit μ «λ» h
  let BM : Matrix J J M := Matrix.of (fun i j => «λ» i • (op (μ j) • m))
  let BA : Fin n → Matrix J J A := fun j =>
    Matrix.of (fun i l => «λ» i * a j * μ l)
  have hc : ((cornerChainMapAt.{t} k A M J).f n).hom
      (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (cornerLinear k I b m) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => cornerAlgHom k A I b (a j)) := by
    change ((liftedMapAt.{t} (cornerAlgHom k A I b)
      (cornerLinear k I b : M →ₗ[k] Matrix I I M)
      (corner_left k A M I b) (corner_right k A M I b)).f n).hom
        (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
    exact liftedMapAt_f_tprod.{_, _, _, _, _, t} (cornerAlgHom k A I b)
      (cornerLinear k I b : M →ₗ[k] Matrix I I M)
      (corner_left k A M I b) (corner_right k A M I b) n (ULift.up m) a
  have hm : Conjugation.coefficientMap
      (M := ULift.{max u v w z t} (Matrix I I M)) k c (ULift.up (cornerLinear k I b m)) =
      ULift.up (Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0 BM) := by
    rw [Conjugation.coefficientMap_apply]
    apply ULift.ext
    exact normalizedFrame_coefficient_corner k A M J μ «λ» h m
  have ha (j : Fin n) : Conjugation.algebraMap k c (cornerAlgHom k A I b (a j)) =
      Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (BA j) :=
    normalizedFrame_algebra_corner k A J μ «λ» h (a j)
  have hconj : ((Conjugation.chainMap
      (M := ULift.{max u v w z t} (Matrix I I M)) k c).f n).hom
        (ULift.up (cornerLinear k I b m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j => cornerAlgHom k A I b (a j))) =
      ULift.up (Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0 BM) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j =>
            Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (BA j)) := by
    have hPure := Conjugation.degreeMap_tprod
      (M := ULift.{max u v w z t} (Matrix I I M)) k c n
      (ULift.up (cornerLinear k I b m))
      (fun j => cornerAlgHom k A I b (a j))
    have hWord : (fun j => Conjugation.algebraMap k c (cornerAlgHom k A I b (a j))) =
        (fun j => Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (BA j)) :=
      funext ha
    change Conjugation.degreeMap
      (M := ULift.{max u v w z t} (Matrix I I M)) k c n
        (ULift.up (cornerLinear k I b m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j => cornerAlgHom k A I b (a j))) = _
    exact hPure.trans ((congrArg
      (fun y : ULift.{max u v w z t} (Matrix I I M) => y ⊗ₜ[k]
        PiTensorProduct.tprod k
          (fun j => Conjugation.algebraMap k c (cornerAlgHom k A I b (a j)))) hm).trans
      (congrArg (fun word : Fin n → Matrix I I A =>
        ULift.up (Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0 BM) ⊗ₜ[k]
          PiTensorProduct.tprod k word) hWord))
  change (show ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A from coefficientUnliftEquiv k A M n)
    (((traceChainMapAt.{t} k A M I).f n).hom
      (((Conjugation.chainMap
        (M := ULift.{max u v w z t} (Matrix I I M)) k c).f n).hom
          (((cornerChainMapAt.{t} k A M J).f n).hom
            (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)))) = _
  rw [hc, hconj]
  change (show ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A from coefficientUnliftEquiv k A M n)
    (traceLinearLiftAt.{t} k A M I n
      (ULift.up (Matrix.fromBlocks (0 : Matrix PUnit PUnit M) 0 0 BM) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j =>
            Matrix.fromBlocks (0 : Matrix PUnit PUnit A) 0 0 (BA j)))) = _
  rw [traceLinearLiftAt_down, coefficientUnliftEquiv_tprod, generalizedTrace_fromBlocks,
    generalizedTrace_tmul_tprod]
  simp only [BM, BA, Matrix.of_apply]

end ModuleCat.Algebra.Hochschild.Matrix
