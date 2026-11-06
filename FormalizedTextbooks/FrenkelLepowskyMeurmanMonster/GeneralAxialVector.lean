/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The signed-short transposition vectors `2λ⊗λ−8X_λ` of Conway's Appendix 6,
Invent. Math. 79 (1985), printed page 539, for every actual short label.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialVector

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The signed transposition vector in the actual Conway coordinates. -/
noncomputable def conwayShortAxisRaw (r : GriessShortIndex) (c : ZMod 2) : ConwayRawSpace :=
  ((2 : ℝ) • Matrix.vecMulVec (griessShortVector r) (griessShortVector r),
    ((-8 * qSign c : ℝ) • Pi.single r 1, 0))

/-- The same source transposition vector in the fixed dictionary coordinates. -/
noncomputable def conwayShortAxis (r : GriessShortIndex) (c : ZMod 2) : GriessSpace :=
  griessConwayDecode (conwayShortAxisRaw r c)

/-- Encoding recovers the genuine symmetric-matrix/short-vector coordinates. -/
theorem conwayShortAxis_encode (r : GriessShortIndex) (c : ZMod 2) :
    griessConwayEncode (conwayShortAxis r c) = conwayShortAxisRaw r c := by
  apply griessConwayEncode_decode
  intro i j
  simp only [conwayShortAxisRaw, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- Every actual short vector has Euclidean squared length four. -/
theorem griessShortVector_norm_sq (r : GriessShortIndex) :
    (∑ i, griessShortVector r i * griessShortVector r i) = 4 := by
  have h := leechEmbedding_pairing (griessShortIntegral r)
  rw [griessShortIntegral_squareSum] at h
  change (∑ i, griessShortVector r i * griessShortVector r i) = (32 : ℝ) / 8 at h
  norm_num at h
  exact h

private theorem shortOuter_square (r : GriessShortIndex) (i j : Fin 24) :
    (∑ k, (2 * griessShortVector r i * griessShortVector r k) *
      (2 * griessShortVector r k * griessShortVector r j)) =
      16 * griessShortVector r i * griessShortVector r j := by
  have he (k : Fin 24) :
      (2 * griessShortVector r i * griessShortVector r k) *
      (2 * griessShortVector r k * griessShortVector r j) =
    (4 * griessShortVector r i * griessShortVector r j) *
      (griessShortVector r k * griessShortVector r k) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, griessShortVector_norm_sq]
  ring

private theorem shortOuter_pairing (r : GriessShortIndex) :
    conwayShortPairing ((2 : ℝ) • Matrix.vecMulVec (griessShortVector r) (griessShortVector r)) r =
      32 := by
  unfold conwayShortPairing
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  have he (i j : Fin 24) :
      2 * (griessShortVector r i * griessShortVector r j) *
        griessShortVector r i * griessShortVector r j =
      2 * (griessShortVector r i * griessShortVector r i) *
        (griessShortVector r j * griessShortVector r j) := by ring
  simp_rw [he, ← Finset.mul_sum, griessShortVector_norm_sq]
  rw [← Finset.sum_mul, ← Finset.mul_sum, griessShortVector_norm_sq]
  norm_num

/-- Every signed-short transposition vector has square 64 times itself in the raw algebra. -/
theorem conwayShortAxisRaw_square (r : GriessShortIndex) (c : ZMod 2) :
    conwayRawProduct (conwayShortAxisRaw r c) (conwayShortAxisRaw r c) =
      (64 : ℝ) • conwayShortAxisRaw r c := by
  let A : Matrix (Fin 24) (Fin 24) ℝ :=
    (2 : ℝ) • Matrix.vecMulVec (griessShortVector r) (griessShortVector r)
  let S : GriessShortIndex → ℝ := (-8 * qSign c : ℝ) • Pi.single r 1
  have hs0 : S r = -8 * qSign c := by simp [S]
  have hs (s : GriessShortIndex) (hsr : s ≠ r) : S s = 0 := by simp [S, hsr]
  have hxx (i j : Fin 24) :
      (∑ a, ∑ b, if (griessShortQ a * griessShortQ b).base = 1 then
        qSign (Multiplicative.toAdd (griessShortQ a * griessShortQ b).coeff) * S a * S b *
          griessShortVector a i * griessShortVector a j else 0) =
      64 * griessShortVector r i * griessShortVector r j := by
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single r]
      · rw [griessShortQ_square, hs0]
        change (if True then qSign 0 * (-8 * qSign c) * (-8 * qSign c) * _ * _ else 0) = _
        simp only [ite_true, qSign_zero]
        have he : 1 * (-8 * qSign c) * (-8 * qSign c) = 64 := by
          calc
            _ = 64 * (qSign c * qSign c) := by ring
            _ = 64 := by rw [qSign_sq]; ring
        rw [he]
      · intro s _ hsr
        simp [hs s hsr]
      · simp
    · intro s _ hsr
      simp [hs s hsr]
    · simp
  have hshort (u : GriessShortIndex) :
      (∑ a, ∑ b,
        if (griessShortQ a * griessShortQ b).base = (griessShortQ u).base then
          qSign (Multiplicative.toAdd (griessShortQ a * griessShortQ b).coeff) *
            S a * S b else 0) = 0 := by
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single r]
      · rw [griessShortQ_square]
        change (if (1 : Multiplicative (Fin 24 → ZMod 2)) = (griessShortQ u).base then
          qSign 0 * S r * S r else 0) = 0
        rw [ite_eq_right (Ne.symm (griessShortQ_base_ne_one u))]
      · intro s _ hsr
        simp [hs s hsr]
      · simp
    · intro s _ hsr
      simp [hs s hsr]
    · simp
  change conwayRawProduct (A, (S, 0)) (A, (S, 0)) = (64 : ℝ) • (A, (S, 0))
  apply Prod.ext
  · funext i j
    change 2 * (∑ k, (A i k * A k j + A i k * A k j)) + _ + _ = _
    rw [Finset.sum_add_distrib, hxx]
    simp only [Pi.zero_apply, mul_zero, zero_mul, add_zero, Finset.sum_const_zero,
      zero_div, Prod.smul_fst, Matrix.smul_apply, smul_eq_mul]
    change 2 * ((∑ k, A i k * A k j) + (∑ k, A i k * A k j)) +
      64 * griessShortVector r i * griessShortVector r j = 64 * A i j
    simp only [A, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    have ha : (∑ k, 2 * (griessShortVector r i * griessShortVector r k) *
        (2 * (griessShortVector r k * griessShortVector r j))) =
        16 * griessShortVector r i * griessShortVector r j := by
      calc
        _ = ∑ k, (2 * griessShortVector r i * griessShortVector r k) *
          (2 * griessShortVector r k * griessShortVector r j) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
        _ = _ := shortOuter_square r i j
    rw [ha]
    ring
  · apply Prod.ext
    · funext u
      change conwayShortPairing A u * S u + conwayShortPairing A u * S u + _ + _ = 64 * S u
      rw [hshort]
      simp only [Pi.zero_apply, spinOperator, LinearMap.coe_mk, AddHom.coe_mk,
        mul_zero, zero_mul, add_zero, Finset.sum_const_zero, zero_div]
      by_cases hu : u = r
      · subst u
        rw [show conwayShortPairing A r = 32 from shortOuter_pairing r]
        ring
      · rw [hs u hu]
        ring
    · funext t i
      simp [conwayRawProduct, spinOperator]

/-- Every signed-short transposition vector is a genuine scaled Griess idempotent. -/
theorem conwayShortAxis_square (r : GriessShortIndex) (c : ZMod 2) :
    griessProd (conwayShortAxis r c) (conwayShortAxis r c) = (64 : ℝ) • conwayShortAxis r c := by
  rw [griessProd_eq_conwayRawProduct, conwayShortAxis_encode, conwayShortAxisRaw_square]
  have he := griessConwayEncodeLinear.map_smul 64 (conwayShortAxis r c)
  change griessConwayEncode ((64 : ℝ) • conwayShortAxis r c) =
    (64 : ℝ) • griessConwayEncode (conwayShortAxis r c) at he
  rw [conwayShortAxis_encode] at he
  rw [← he, griessConwayDecode_encode]

/-- Every signed-short transposition vector has the source squared norm 128. -/
theorem conwayShortAxis_norm_sq (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) (conwayShortAxis r c) = 128 := by
  rw [griessForm_eq_conwayRawForm, conwayShortAxis_encode]
  simp only [conwayRawForm, conwayShortAxisRaw, conwayMatrixForm_eq_sum,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have hm : (∑ i, ∑ j,
      (2 * (griessShortVector r i * griessShortVector r j)) *
      (2 * (griessShortVector r i * griessShortVector r j))) = 64 := by
    have he (i j : Fin 24) :
        (2 * (griessShortVector r i * griessShortVector r j)) *
        (2 * (griessShortVector r i * griessShortVector r j)) =
        4 * (griessShortVector r i * griessShortVector r i) *
          (griessShortVector r j * griessShortVector r j) := by ring
    simp_rw [he, ← Finset.mul_sum, griessShortVector_norm_sq]
    rw [← Finset.sum_mul, ← Finset.mul_sum, griessShortVector_norm_sq]
    norm_num
  rw [hm]
  have hs : (-8 * qSign c) * (-8 * qSign c) = 64 := by
    calc
      _ = 64 * (qSign c * qSign c) := by ring
      _ = 64 := by rw [qSign_sq]; ring
  simp [Pi.single_apply, mul_ite, ite_mul]
  nlinarith [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
