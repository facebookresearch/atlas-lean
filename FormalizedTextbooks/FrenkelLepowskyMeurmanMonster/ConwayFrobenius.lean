/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCommutativity
/-! The associative bilinear form of the concrete Conway Griess algebra.

Each of the six raw product rules is paired with its adjoint block rule.
The short-times-short coefficient is cyclic because the three relevant
short lifts are involutions with the same central product phase. Matrix
and tensor terms use their actual source normalizations, including 1/8.
The final theorem is unconditional on GriessSpace, whose dictionary matrix
block is symmetric. No triality or milestone proof is assumed.
Source: Conway's Griess algebra construction; Seysen, arXiv:2002.10921v3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
-- Conway's block formulas use matrix-valued function abbreviations.
set_option backward.isDefEq.respectTransparency false

private lemma commutative_involution_product_cycle {M : Type*} [CommGroup M]
    (r s u : M) (hs : s * s = 1) : r * s = u ↔ s * u = r := by
  constructor
  · intro h
    rw [← h, ← mul_assoc, mul_comm s r, mul_assoc, hs, mul_one]
  · intro h
    rw [← h, mul_assoc, mul_comm u s, ← mul_assoc, hs, one_mul]

private lemma q_product_base_cycle (r s u : Q) (hs : s * s = 1) :
    (r * s).base = u.base ↔ (s * u).base = r.base :=
  commutative_involution_product_cycle r.base s.base u.base
    (congrArg (fun q : Q => q.base) hs)

lemma griessShortQ_product_base_cycle (r s u : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = (griessShortQ u).base ↔
      (griessShortQ s * griessShortQ u).base = (griessShortQ r).base :=
  q_product_base_cycle (griessShortQ r) (griessShortQ s) (griessShortQ u)
    (griessShortQ_square s)

lemma griessShortQ_product_phase_cycle (r s u : GriessShortIndex)
    (h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    toAdd (griessShortQ r * griessShortQ s).coeff =
      toAdd (griessShortQ s * griessShortQ u).coeff := by
  have he := q_eq_central_short_of_base (griessShortQ r * griessShortQ s) u h
  have hp : griessShortQ s * griessShortQ u =
      qCentral (toAdd (griessShortQ r * griessShortQ s).coeff) * griessShortQ r := by
    calc
      _ = griessShortQ r * (griessShortQ r * griessShortQ s) * griessShortQ u := by
        rw [← mul_assoc, griessShortQ_square, one_mul]
      _ = griessShortQ r *
        (qCentral (toAdd (griessShortQ r * griessShortQ s).coeff) * griessShortQ u) *
          griessShortQ u := congrArg (fun q => griessShortQ r * q * griessShortQ u) he
      _ = qCentral (toAdd (griessShortQ r * griessShortQ s).coeff) * griessShortQ r := by
        rw [← mul_assoc (griessShortQ r), qCentral_commute]
        rw [mul_assoc, mul_assoc, griessShortQ_square, mul_one]
  have hcoeff := congrArg (fun q : Q => toAdd q.coeff) hp
  rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero] at hcoeff
  exact hcoeff.symm

lemma conwayShortShortProduct_frobenius (x y z : GriessShortIndex → ℝ) :
    (∑ u, conwayShortShortProduct x y u * z u) =
      ∑ r, x r * conwayShortShortProduct y z r := by
  unfold conwayShortShortProduct
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
  · have hc := (griessShortQ_product_base_cycle r s u).mp h
    simp only [h, hc, ite_true]
    rw [griessShortQ_product_phase_cycle r s u h]
    ring
  · have hc := mt (griessShortQ_product_base_cycle r s u).mpr h
    simp [h, hc]

private lemma frame_matrix_pairing {R I : Type*} [Fintype R] [Fintype I]
    (x y : R → ℝ) (v : R → I → ℝ) (a : I → I → ℝ) :
    (∑ i, ∑ j, (∑ r, x r * y r * v r i * v r j) * a i j) =
      ∑ r, x r * (∑ i, ∑ j, a i j * v r i * v r j) * y r := by
  simp only [Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma conwayShortShortMatrix_frobenius (x y : GriessShortIndex → ℝ)
    (a : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm (conwayShortShortMatrix x y) a =
      ∑ r, x r * conwayMatrixShortProduct a y r := by
  have hmat (i j : Fin 24) : conwayShortShortMatrix x y i j =
      ∑ r, x r * y r * griessShortVector r i * griessShortVector r j := by
    rw [conwayShortShortMatrix_apply]
    simp_rw [griessShortQ_central_product_iff_same_label]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp_rw [griessShortQ_square]
    simp only [show toAdd (1 : Q).coeff = 0 by rfl, qSign_zero, one_mul]
  rw [conwayMatrixForm_eq_sum]
  simp_rw [hmat]
  simpa only [conwayMatrixShortProduct, conwayShortPairing, mul_assoc] using
    frame_matrix_pairing x y griessShortVector (fun i j => a i j)

lemma conwayMatrixMatrixProduct_frobenius (a b c : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : a.transpose = a) (hb : b.transpose = b) :
    conwayMatrixForm (conwayMatrixMatrixProduct a b) c =
      conwayMatrixForm a (conwayMatrixMatrixProduct b c) := by
  simp only [conwayMatrixForm, conwayMatrixMatrixProduct, Matrix.transpose_smul,
    Matrix.transpose_add, Matrix.transpose_mul, ha, hb, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    smul_eq_mul]
  rw [← Matrix.trace_mul_cycle a c b, Matrix.mul_assoc a b c, Matrix.mul_assoc a c b]
  ring

lemma conwayMatrixForm_add_left (a b c : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm (a + b) c = conwayMatrixForm a c + conwayMatrixForm b c := by
  simp [conwayMatrixForm, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]

lemma conwayMatrixForm_add_right (a b c : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm a (b + c) = conwayMatrixForm a b + conwayMatrixForm a c := by
  simp [conwayMatrixForm, Matrix.mul_add, Matrix.trace_add]

lemma conwayMatrixForm_smul_left (c : ℝ) (a b : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm (c • a) b = c * conwayMatrixForm a b := by
  simp [conwayMatrixForm, Matrix.transpose_smul, Matrix.trace_smul]

lemma conwayMatrixForm_one_left (a : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm 1 a = Matrix.trace a := by simp [conwayMatrixForm]

lemma conwayMatrixForm_vecMulVec (a : Matrix (Fin 24) (Fin 24) ℝ) (v w : Fin 24 → ℝ) :
    conwayMatrixForm (Matrix.vecMulVec v w) a = stdPairingFun v (a *ᵥ w) := by
  rw [conwayMatrixForm_eq_sum]
  simp only [Matrix.vecMulVec_apply, stdPairingFun, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma conwayTensorTensorMatrix_frobenius (x y : SpinIndex → Fin 24 → ℝ)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (ha : a.transpose = a) :
    conwayMatrixForm (conwayTensorTensorMatrix x y) a =
      conwayTensorForm x (conwayMatrixTensorProduct a y) := by
  obtain ⟨x, rfl⟩ := conwayTensorCoordinates.surjective x
  obtain ⟨y, rfl⟩ := conwayTensorCoordinates.surjective y
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    induction y using TensorProduct.inductionOn with
    | tmul u' w =>
      rw [conwayTensorTensorMatrix_tmul, conwayMatrixForm_smul_left,
        conwayMatrixForm_add_left, conwayMatrixForm_add_left,
        conwayMatrixForm_smul_left, conwayMatrixForm_smul_left,
        conwayMatrixForm_smul_left, conwayMatrixForm_one_left,
        conwayMatrixForm_vecMulVec, conwayMatrixForm_vecMulVec,
        conwayMatrixTensorProduct_tmul, conwayTensorForm_tmul, ha]
      have hs : stdPairingFun w (a *ᵥ v) = stdPairingFun v (a *ᵥ w) :=
        Matrix.IsSymm.dotProduct_mulVec_comm ha
      rw [hs]
      have hadd : stdPairingFun v (a *ᵥ w + (Matrix.trace a / 8) • w) =
          stdPairingFun v (a *ᵥ w) + Matrix.trace a / 8 * stdPairingFun v w := by
        simp only [stdPairingFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hadd]
      ring
    | add y z hy hz =>
      simp only [map_add, conwayMatrixForm_add_left, hy, hz]
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, conwayMatrixForm_add_left, hx, hz]

private lemma tensor_short_pairing {R I T : Type*} [Fintype R] [Fintype I] [Fintype T]
    (x : R → ℝ) (op : R → T → I → ℝ) (z : T → I → ℝ) (c : R → I → I → ℝ) :
    (∑ t, ∑ j, ((∑ r, ∑ i, x r * op r t i * c r i j) / 8) * z t j) =
      ∑ r, x r * ((∑ t, ∑ i, ∑ j, op r t i * z t j * c r i j) / 8) := by
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext t
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma conwayShortTensorProduct_frobenius (x : GriessShortIndex → ℝ)
    (y z : SpinIndex → Fin 24 → ℝ) :
    conwayTensorForm (conwayShortTensorProduct x y) z =
      ∑ r, x r * conwayTensorTensorShort y z r := by
  simp only [conwayTensorForm, LinearMap.mk₂_apply]
  simp_rw [conwayShortTensorProduct_apply, conwayTensorTensorShort_apply]
  exact tensor_short_pairing x
    (fun r t i => spinOperator (griessShortQ r) (fun v => y v i) t) z
    conwayTensorCoefficient

lemma conwayMatrixForm_swap (a b : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm a b = conwayMatrixForm b a := by
  rw [conwayMatrixForm_eq_sum, conwayMatrixForm_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma conwayTensorForm_swap (x y : SpinIndex → Fin 24 → ℝ) :
    conwayTensorForm x y = conwayTensorForm y x := by
  simp only [conwayTensorForm, LinearMap.mk₂_apply]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma conwayMatrixShortProduct_selfAdjoint (a : Matrix (Fin 24) (Fin 24) ℝ)
    (x y : GriessShortIndex → ℝ) :
    (∑ r, conwayMatrixShortProduct a x r * y r) =
      ∑ r, x r * conwayMatrixShortProduct a y r := by
  apply Finset.sum_congr rfl
  intro r _
  unfold conwayMatrixShortProduct
  ring

lemma conwayMatrixTensorProduct_selfAdjoint (a : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : a.transpose = a) (x y : SpinIndex → Fin 24 → ℝ) :
    conwayTensorForm (conwayMatrixTensorProduct a x) y =
      conwayTensorForm x (conwayMatrixTensorProduct a y) := by
  rw [conwayTensorForm_swap, ← conwayTensorTensorMatrix_frobenius y x a ha,
    conwayTensorTensorMatrix_comm, conwayTensorTensorMatrix_frobenius x y a ha]

lemma conwayShortTensorProduct_selfAdjoint (a : GriessShortIndex → ℝ)
    (x y : SpinIndex → Fin 24 → ℝ) :
    conwayTensorForm (conwayShortTensorProduct a x) y =
      conwayTensorForm x (conwayShortTensorProduct a y) := by
  rw [conwayShortTensorProduct_frobenius, conwayTensorTensorShort_comm,
    ← conwayShortTensorProduct_frobenius, conwayTensorForm_swap]

lemma conwayMatrixShortProduct_pairing_matrix (a : Matrix (Fin 24) (Fin 24) ℝ)
    (x y : GriessShortIndex → ℝ) :
    (∑ r, conwayMatrixShortProduct a x r * y r) =
      conwayMatrixForm a (conwayShortShortMatrix x y) := by
  rw [conwayMatrixForm_swap, conwayShortShortMatrix_frobenius]
  exact conwayMatrixShortProduct_selfAdjoint a x y

lemma conwayMatrixTensorProduct_pairing_matrix (a : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : a.transpose = a) (x y : SpinIndex → Fin 24 → ℝ) :
    conwayTensorForm (conwayMatrixTensorProduct a x) y =
      conwayMatrixForm a (conwayTensorTensorMatrix x y) := by
  rw [conwayMatrixTensorProduct_selfAdjoint a ha,
    conwayMatrixForm_swap, conwayTensorTensorMatrix_frobenius x y a ha]

lemma conwayTensorTensorShort_pairing_tensor (x y : SpinIndex → Fin 24 → ℝ)
    (z : GriessShortIndex → ℝ) :
    (∑ r, conwayTensorTensorShort x y r * z r) =
      conwayTensorForm x (conwayShortTensorProduct z y) := by
  rw [← conwayShortTensorProduct_selfAdjoint,
    conwayShortTensorProduct_frobenius]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The full raw Frobenius identity on the actual symmetric matrix domain. -/
theorem conwayRawProduct_frobenius (x y z : ConwayRawSpace)
    (hx : x.1.transpose = x.1) (hy : y.1.transpose = y.1) (hz : z.1.transpose = z.1) :
    conwayRawForm (conwayRawProduct x y) z = conwayRawForm x (conwayRawProduct y z) := by
  rw [conwayRawProduct_eq_blocks, conwayRawProduct_eq_blocks]
  simp only [conwayRawForm, conwayMatrixForm_add_left, conwayMatrixForm_add_right,
    Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
    map_add, LinearMap.add_apply]
  rw [conwayMatrixMatrixProduct_frobenius x.1 y.1 z.1 hx hy,
    conwayShortShortMatrix_frobenius,
    conwayTensorTensorMatrix_frobenius x.2.2 y.2.2 z.1 hz,
    conwayMatrixShortProduct_pairing_matrix,
    conwayMatrixShortProduct_selfAdjoint,
    conwayShortShortProduct_frobenius,
    conwayTensorTensorShort_pairing_tensor,
    conwayMatrixTensorProduct_pairing_matrix x.1 hx,
    conwayMatrixTensorProduct_selfAdjoint y.1 hy,
    conwayShortTensorProduct_frobenius,
    conwayShortTensorProduct_selfAdjoint]
  ring

/-- The concrete Griess form is associative with the concrete multiplication. -/
theorem griessProd_frobenius (x y z : GriessSpace) :
    griessForm (griessProd x y) z = griessForm x (griessProd y z) := by
  rw [griessForm_eq_conwayRawForm, griessForm_eq_conwayRawForm,
    griessProd_encode, griessProd_encode]
  apply conwayRawProduct_frobenius
  all_goals
    ext i j
    exact griessConwayEncode_symmetric _ j i
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
