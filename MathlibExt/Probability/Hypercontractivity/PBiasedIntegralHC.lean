/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Hypercontractivity.PBiasedTwoPoint

@[expose] public section

/-!
# The one-variable `p`-biased inequality from a pointwise bound

Writing `m = (1-p) + p z` and `V = 4(q-1) p²(1-p)²(z-1)²`, Bernoulli's inequality gives
`(m² + V)^(q/2) ≤ m^q + (q/2) m^(q-2) V`. So `pbt_OneVarCore p q` follows from the pointwise bound
`StatMech.Probability.pih_KEY p q`: `(q/2) m^(q-2) V ≤ (1-p) + p z^q - m^q` for `z ≥ 0`.

## Main definitions

* `StatMech.Probability.pih_m`, `StatMech.Probability.pih_V`: `m` and `V` above.
* `StatMech.Probability.pih_KEY p q`: the pointwise bound.

## Main results

* `StatMech.Probability.pih_core_of_KEY`: `pih_KEY p q` implies `pbt_OneVarCore p q` for
  `0 < p < 1`, `1 ≤ q ≤ 2`.
* `StatMech.Probability.pih_two_point_value_of_KEY`: the `p`-biased two-point inequality from
  `pih_KEY p q` and `pih_KEY (1 - p) q`.
* `StatMech.Probability.pih_KEY_q_one`: the case `q = 1`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press (2014), Chapter 10
  (hypercontractivity of general product spaces).
-/

open Real Set

namespace StatMech.Probability

/-- The mean `(1-p) + p z` of the `p`-biased two-valued function with values `1` and `z`. -/
def pih_m (p z : ℝ) : ℝ := (1 - p) + p * z

/-- The variance term `4(q-1) p²(1-p)²(z - 1)²`. -/
def pih_V (p q z : ℝ) : ℝ := 4 * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2

theorem pih_g_eq (p q z : ℝ) : pbt_g p q z = (pih_m p z) ^ 2 + pih_V p q z := by
  unfold pbt_g pih_m pih_V; ring

/-- The pointwise bound `(q/2) m^(q-2) V ≤ (1-p) + p z^q - m^q` for all `z ≥ 0`, with
`m = pih_m p z`, `V = pih_V p q z`. -/
def pih_KEY (p q : ℝ) : Prop :=
  ∀ z : ℝ, 0 ≤ z →
    (q / 2) * (pih_m p z) ^ (q - 2) * pih_V p q z ≤ (1 - p) + p * z ^ q - (pih_m p z) ^ q

theorem pih_bernoulli {p q z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hz : 0 ≤ z) :
    (pbt_g p q z) ^ (q / 2)
      ≤ (pih_m p z) ^ q + (q / 2) * (pih_m p z) ^ (q - 2) * pih_V p q z := by
  have hm : 0 < pih_m p z := by unfold pih_m; nlinarith
  have hV : 0 ≤ pih_V p q z := by unfold pih_V; positivity
  set m := pih_m p z with hmdef
  set V := pih_V p q z with hVdef
  have hg : pbt_g p q z = m ^ 2 + V := by rw [hmdef, hVdef, pih_g_eq]
  set s := V / m ^ 2 with hs
  have hsnn : 0 ≤ s := by rw [hs]; positivity
  have hfac : m ^ 2 + V = m ^ 2 * (1 + s) := by rw [hs]; field_simp
  have hgq : (m ^ 2 + V) ^ (q / 2) = (m ^ 2) ^ (q / 2) * (1 + s) ^ (q / 2) := by
    rw [hfac, Real.mul_rpow (by positivity) (by positivity)]
  have hm2q : (m ^ 2) ^ (q / 2) = m ^ q := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hm.le]; congr 1; ring
  have hbern := rpow_one_add_le_one_add_mul_self (by linarith : (-1 : ℝ) ≤ s)
    (by linarith : (0 : ℝ) ≤ q / 2) (by linarith : q / 2 ≤ 1)
  rw [hg, hgq, hm2q]
  have hmq : 0 ≤ m ^ q := (Real.rpow_pos_of_pos hm q).le
  calc m ^ q * (1 + s) ^ (q / 2)
      ≤ m ^ q * (1 + (q / 2) * s) := mul_le_mul_of_nonneg_left hbern hmq
    _ = m ^ q + (q / 2) * m ^ (q - 2) * V := by
        rw [hs, mul_add, mul_one]
        have hmq2 : m ^ (q - 2) = m ^ q * (m ^ 2)⁻¹ := by
          have hsub : m ^ (q - 2) = m ^ q * m ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_add hm]; ring_nf
          rw [hsub, Real.rpow_neg hm.le, Real.rpow_two]
        rw [hmq2]; field_simp

/-- The pointwise bound `pih_KEY p q` implies the one-variable inequality `pbt_OneVarCore p q`. -/
theorem pih_core_of_KEY {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (HKEY : pih_KEY p q) : pbt_OneVarCore p q := by
  intro z hz
  have hq0 : 0 < q := by linarith
  have hgnn : 0 ≤ pbt_g p q z := by unfold pbt_g; positivity
  have hkey := HKEY z hz
  have hstep : (pbt_g p q z) ^ (q / 2) ≤ (1 - p) + p * z ^ q := by
    calc (pbt_g p q z) ^ (q / 2)
        ≤ (pih_m p z) ^ q + (q / 2) * (pih_m p z) ^ (q - 2) * pih_V p q z :=
          pih_bernoulli hp0 hp1 hq1 hq2 hz
      _ ≤ (1 - p) + p * z ^ q := by linarith [hkey]
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hgnn _) hstep
    (by positivity : (0 : ℝ) ≤ 2 / q)
  rwa [← Real.rpow_mul hgnn, show q / 2 * (2 / q) = 1 by field_simp, Real.rpow_one] at hmono

theorem pih_KEY_at_one (p q : ℝ) :
    (q / 2) * (pih_m p 1) ^ (q - 2) * pih_V p q 1
      ≤ (1 - p) + p * (1 : ℝ) ^ q - (pih_m p 1) ^ q := by
  have hV : pih_V p q 1 = 0 := by unfold pih_V; ring
  have hm : pih_m p 1 = 1 := by unfold pih_m; ring
  rw [hV, hm, Real.one_rpow, mul_zero]
  norm_num

theorem pih_KEY_q_one (p : ℝ) : pih_KEY p 1 := by
  intro z _
  have hV : pih_V p 1 z = 0 := by unfold pih_V; ring
  rw [hV, mul_zero]
  unfold pih_m
  rw [Real.rpow_one, Real.rpow_one]
  ring_nf
  rfl

theorem pih_slack_nonneg {p q z : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : 1 ≤ q)
    (hz : 0 ≤ z) : 0 ≤ (1 - p) + p * z ^ q - (pih_m p z) ^ q := by
  have hconv := (convexOn_rpow hq1).2 (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (Set.mem_Ici.mpr hz) (by linarith : (0 : ℝ) ≤ 1 - p) hp0 (by ring)
  simp only [smul_eq_mul, Real.one_rpow, mul_one] at hconv
  have hm : pih_m p z = 1 - p + p * z := by unfold pih_m; ring
  rw [hm]
  linarith [hconv]

theorem pih_slack_crux {p q z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hz : 0 < z) : p * (pih_m p z) ^ (q - 2) ≤ z ^ (q - 2) := by
  have hm : 0 < pih_m p z := by unfold pih_m; nlinarith
  have hmpz : p * z ≤ pih_m p z := by unfold pih_m; nlinarith
  have hpz0 : 0 ≤ p * z := by positivity
  have hmono : (p * z) ^ (2 - q) ≤ (pih_m p z) ^ (2 - q) :=
    Real.rpow_le_rpow hpz0 hmpz (by linarith)
  have hsplit : (p * z) ^ (2 - q) = p ^ (2 - q) * z ^ (2 - q) :=
    Real.mul_rpow hp0.le hz.le
  have hmrw : (pih_m p z) ^ (q - 2) = ((pih_m p z) ^ (2 - q))⁻¹ := by
    rw [← Real.rpow_neg hm.le]; congr 1; ring
  have hzrw : z ^ (q - 2) = (z ^ (2 - q))⁻¹ := by
    rw [← Real.rpow_neg hz.le]; congr 1; ring
  rw [hmrw, hzrw]
  have hmp : 0 < (pih_m p z) ^ (2 - q) := Real.rpow_pos_of_pos hm _
  have hzp : 0 < z ^ (2 - q) := Real.rpow_pos_of_pos hz _
  have hppow : p ≤ p ^ (2 - q) := by
    calc p = p ^ (1 : ℝ) := (Real.rpow_one p).symm
      _ ≤ p ^ (2 - q) := Real.rpow_le_rpow_of_exponent_ge hp0 hp1.le (by linarith)
  have hkey2 : p * z ^ (2 - q) ≤ (pih_m p z) ^ (2 - q) := by
    have hz2 : (0 : ℝ) ≤ z ^ (2 - q) := hzp.le
    calc p * z ^ (2 - q) ≤ p ^ (2 - q) * z ^ (2 - q) :=
          mul_le_mul_of_nonneg_right hppow hz2
      _ = (p * z) ^ (2 - q) := hsplit.symm
      _ ≤ (pih_m p z) ^ (2 - q) := hmono
  rw [mul_inv_le_iff₀ hmp]
  rw [show (z ^ (2 - q))⁻¹ * (pih_m p z) ^ (2 - q)
        = (pih_m p z) ^ (2 - q) / z ^ (2 - q) by ring, le_div_iff₀ hzp]
  exact hkey2

/-- The `p`-biased two-point inequality from `pih_KEY p q` and `pih_KEY (1 - p) q`. -/
theorem pih_two_point_value_of_KEY {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (HKEY : pih_KEY p q) (HKEY' : pih_KEY (1 - p) q) (u v : ℝ) :
    ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2
      ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) := by
  have Hcore : pbt_OneVarCore p q := pih_core_of_KEY hp0 hp1 hq1 hq2 HKEY
  have Hcore' : pbt_OneVarCore (1 - p) q :=
    pih_core_of_KEY (by linarith) (by linarith) hq1 hq2 HKEY'
  exact pbt_two_point_value_of_core hp0.le hp1.le hq1 hq2 Hcore Hcore' u v

end StatMech.Probability
