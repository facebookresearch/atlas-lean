/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import MathlibExt.ControlTheory.StateSpace.Discrete

/-!
# Discrete-time state growth bound

If the powers of the state map obey `‖(A^k) x‖ ≤ M * ρ^k * ‖x‖` and the
inputs obey `‖u k‖ ≤ K * r^k`, then for every rate `q` strictly above
`ρ` and `r` the trajectory obeys
`‖x k‖ ≤ M * (‖x0‖ + ‖B‖ * K / q) * (1 + k) * q^k`. The factor `1 + k`
covers the case where the two rates coincide.
-/

@[expose] public section

namespace ControlTheory

namespace StateSpaceCoeffs

/-- Growth bound for the discrete trajectory. If every power of `A`
satisfies `‖(A^k) x‖ ≤ M * ρ^k * ‖x‖`, the inputs satisfy
`‖u k‖ ≤ K * r^k`, and `q` strictly exceeds both rates, then
`‖x k‖ ≤ M * (‖x0‖ + ‖B‖ * K / q) * (1 + k) * q^k`. The factor `1 + k`
covers the case where the two rates coincide. -/
theorem dtTraj_growth {𝕜 X U Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S : StateSpaceCoeffs 𝕜 X U Y) (u : ℕ → U) (x0 : X)
    {M K ρ r q : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hpow : ∀ (k : ℕ) (x : X), ‖(S.A ^ k) x‖ ≤ M * ρ ^ k * ‖x‖)
    (hu : ∀ k : ℕ, ‖u k‖ ≤ K * r ^ k)
    (hqρ : ρ < q) (hqr : r < q) (k : ℕ) :
    ‖S.dtTraj u x0 k‖ ≤ M * (‖x0‖ + ‖S.B‖ * K / q) * (1 + k) * q ^ k := by
  have hqpos : 0 < q := lt_of_le_of_lt hρ hqρ
  have hqnn : 0 ≤ q := le_of_lt hqpos
  have hρq : ρ ≤ q := le_of_lt hqρ
  have hrq : r ≤ q := le_of_lt hqr
  have hDnn : 0 ≤ ‖S.B‖ * K / q :=
    div_nonneg (mul_nonneg (norm_nonneg _) hK) hqnn
  cases k with
  | zero =>
      have h0 := hpow 0 x0
      rw [pow_zero, one_apply_eq_self, pow_zero, mul_one] at h0
      have hle : ‖x0‖ ≤ M * (‖x0‖ + ‖S.B‖ * K / q) :=
        calc ‖x0‖ ≤ M * ‖x0‖ := h0
          _ ≤ M * (‖x0‖ + ‖S.B‖ * K / q) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hDnn) hM
      simpa [dtTraj_zero] using hle
  | succ k =>
      show ‖S.dtTraj u x0 (k + 1)‖ ≤ M * (‖x0‖ + ‖S.B‖ * K / q) * (1 + ↑(k + 1)) * q ^ (k + 1)
      have hterm : ∀ j ∈ Finset.range (k + 1),
          ‖(S.A ^ (k + 1 - 1 - j)) (S.B (u j))‖ ≤ M * (‖S.B‖ * K) * q ^ k := by
        intro j hj
        have hjlt : j < k + 1 := Finset.mem_range.mp hj
        have hexp : k + 1 - 1 - j + j = k := by omega
        have h1 := hpow (k + 1 - 1 - j) (S.B (u j))
        have h2 : ‖S.B (u j)‖ ≤ ‖S.B‖ * (K * r ^ j) :=
          calc ‖S.B (u j)‖ ≤ ‖S.B‖ * ‖u j‖ := S.B.le_opNorm _
            _ ≤ ‖S.B‖ * (K * r ^ j) := mul_le_mul_of_nonneg_left (hu j) (norm_nonneg _)
        have h4 : ρ ^ (k + 1 - 1 - j) ≤ q ^ (k + 1 - 1 - j) := pow_le_pow_left₀ hρ hρq _
        have h5 : r ^ j ≤ q ^ j := pow_le_pow_left₀ hr hrq _
        have h6 : ρ ^ (k + 1 - 1 - j) * r ^ j ≤ q ^ (k + 1 - 1 - j) * q ^ j :=
          mul_le_mul h4 h5 (pow_nonneg hr _) (pow_nonneg hqnn _)
        calc ‖(S.A ^ (k + 1 - 1 - j)) (S.B (u j))‖
            ≤ M * ρ ^ (k + 1 - 1 - j) * ‖S.B (u j)‖ := h1
          _ ≤ M * ρ ^ (k + 1 - 1 - j) * (‖S.B‖ * (K * r ^ j)) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hM (pow_nonneg hρ _))
          _ = M * (‖S.B‖ * K) * (ρ ^ (k + 1 - 1 - j) * r ^ j) := by ring
          _ ≤ M * (‖S.B‖ * K) * (q ^ (k + 1 - 1 - j) * q ^ j) :=
              mul_le_mul_of_nonneg_left h6 (mul_nonneg hM (mul_nonneg (norm_nonneg _) hK))
          _ = M * (‖S.B‖ * K) * q ^ k := by rw [← pow_add, hexp]
      have hsum : ‖∑ j ∈ Finset.range (k + 1), (S.A ^ (k + 1 - 1 - j)) (S.B (u j))‖
          ≤ ↑(k + 1) * (M * (‖S.B‖ * K) * q ^ k) := by
        calc ‖∑ j ∈ Finset.range (k + 1), (S.A ^ (k + 1 - 1 - j)) (S.B (u j))‖
            ≤ ∑ j ∈ Finset.range (k + 1), ‖(S.A ^ (k + 1 - 1 - j)) (S.B (u j))‖ :=
              norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.range (k + 1), M * (‖S.B‖ * K) * q ^ k :=
              Finset.sum_le_sum hterm
          _ = ↑(k + 1) * (M * (‖S.B‖ * K) * q ^ k) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hfirst := hpow (k + 1) x0
      have hρpow : ρ ^ (k + 1) ≤ (1 + ↑(k + 1)) * q ^ (k + 1) := by
        calc ρ ^ (k + 1) ≤ q ^ (k + 1) := pow_le_pow_left₀ hρ hρq _
          _ = 1 * q ^ (k + 1) := by rw [one_mul]
          _ ≤ (1 + ↑(k + 1)) * q ^ (k + 1) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg hqnn _)
              exact le_add_of_nonneg_right (Nat.cast_nonneg _)
      have e1 : M * ρ ^ (k + 1) * ‖x0‖ ≤ M * ‖x0‖ * (1 + ↑(k + 1)) * q ^ (k + 1) := by
        calc M * ρ ^ (k + 1) * ‖x0‖ = (M * ‖x0‖) * ρ ^ (k + 1) := by ring
          _ ≤ (M * ‖x0‖) * ((1 + ↑(k + 1)) * q ^ (k + 1)) :=
              mul_le_mul_of_nonneg_left hρpow (mul_nonneg hM (norm_nonneg _))
          _ = M * ‖x0‖ * (1 + ↑(k + 1)) * q ^ (k + 1) := by ring
      have e2 : ↑(k + 1) * (M * (‖S.B‖ * K) * q ^ k)
          ≤ M * (‖S.B‖ * K / q) * (1 + ↑(k + 1)) * q ^ (k + 1) := by
        have hq0 : q ≠ 0 := hqpos.ne'
        have hQ : q ^ (k + 1) = q ^ k * q := pow_succ q k
        calc ↑(k + 1) * (M * (‖S.B‖ * K) * q ^ k)
            ≤ (1 + ↑(k + 1)) * (M * (‖S.B‖ * K) * q ^ k) :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
                (mul_nonneg (mul_nonneg hM (mul_nonneg (norm_nonneg _) hK)) (pow_nonneg hqnn _))
          _ = M * (‖S.B‖ * K / q) * (1 + ↑(k + 1)) * q ^ (k + 1) := by
              rw [hQ]; field_simp
      rw [dtTraj_closedForm]
      refine le_trans (norm_add_le _ _) ?_
      calc ‖(S.A ^ (k + 1)) x0‖ + ‖∑ j ∈ Finset.range (k + 1), (S.A ^ (k + 1 - 1 - j)) (S.B (u j))‖
          ≤ M * ρ ^ (k + 1) * ‖x0‖ + ↑(k + 1) * (M * (‖S.B‖ * K) * q ^ k) :=
            add_le_add hfirst hsum
        _ ≤ M * ‖x0‖ * (1 + ↑(k + 1)) * q ^ (k + 1)
              + M * (‖S.B‖ * K / q) * (1 + ↑(k + 1)) * q ^ (k + 1) := add_le_add e1 e2
        _ = M * (‖x0‖ + ‖S.B‖ * K / q) * (1 + ↑(k + 1)) * q ^ (k + 1) := by ring

end StateSpaceCoeffs

end ControlTheory
