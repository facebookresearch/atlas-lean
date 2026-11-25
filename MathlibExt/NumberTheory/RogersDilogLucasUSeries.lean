/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.SanfordSymmetricSeries

/-!
# Sanford's Lucas-sequence dilogarithm series for $Q > 0$

We prove Sanford's Lucas-sequence dilogarithm series for $Q > 0$ by applying
Sanford's symmetric dilogarithm series to the ratio of the conjugate roots.
-/

open Real

namespace MetaMathlibExt
namespace rogersDilog_lucasU_series

/-- Binet's formula for a Lucas sequence, for two roots of $x^2 - Px + Q = 0$. -/
private lemma lucasU_eq {params : LucasSequenceParams} {α β : ℝ}
    (hα : α ^ 2 = (params.p : ℝ) * α - (params.q : ℝ))
    (hβ : β ^ 2 = (params.p : ℝ) * β - (params.q : ℝ))
    (hne : α - β ≠ 0) (n : ℕ) :
    (lucasU params n : ℝ) = (α ^ n - β ^ n) / (α - β) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasU]
  | one => simp [lucasU, div_self hne]
  | more n ih1 ih2 =>
    have hrec : (lucasU params (n + 2) : ℝ) =
        (params.p : ℝ) * (lucasU params (n + 1) : ℝ) -
          (params.q : ℝ) * (lucasU params n : ℝ) := by
      have h := lucasU_add_two params n
      exact_mod_cast h
    have eα : α ^ (n + 2) = (params.p : ℝ) * α ^ (n + 1) - (params.q : ℝ) * α ^ n := by
      rw [pow_add, hα]
      ring
    have eβ : β ^ (n + 2) = (params.p : ℝ) * β ^ (n + 1) - (params.q : ℝ) * β ^ n := by
      rw [pow_add, hβ]
      ring
    rw [hrec, ih1, ih2, eα, eβ]
    field_simp
    ring

end rogersDilog_lucasU_series

/-- **Sanford's Lucas-sequence dilogarithm series for $Q > 0$.** Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $(P, Q)$ be Lucas sequence parameters with $P > 0$, $Q > 0$ and
$D = P^2 - 4Q > 0$, let $U = U(P, Q)$ be the Lucas sequence, and put $\alpha = (P + \sqrt{D})/2$.
Then for every integer $k \ge 1$,
$$
\sum_{n \ge 1} L\left(\frac{U_k^2 Q^{kn}}{U_{k(n+1)}^2}\right) =
L\left(\frac{Q^k}{\alpha^{2k}}\right).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 5 (8) (`integers-2025-A52-thm-5`). -/
public theorem rogersDilog_lucasU_series (params : LucasSequenceParams)
    (hP : 0 < params.p) (hQ : 0 < params.q) (hD : 0 < params.p ^ 2 - 4 * params.q)
    {k : ℕ} (hk : 0 < k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    let α : ℝ := (params.p + √((params.p ^ 2 - 4 * params.q : ℤ) : ℝ)) / 2
    ∑' n : ℕ, L ((lucasU params k : ℝ) ^ 2 * (params.q : ℝ) ^ (k * (n + 1)) /
        (lucasU params (k * (n + 2)) : ℝ) ^ 2) = L ((params.q : ℝ) ^ k / α ^ (2 * k)) := by
  intro L α
  have hPℝ : (0 : ℝ) < (params.p : ℝ) := by exact_mod_cast hP
  have hQℝ : (0 : ℝ) < (params.q : ℝ) := by exact_mod_cast hQ
  have hDℝ : (0 : ℝ) < ((params.p ^ 2 - 4 * params.q : ℤ) : ℝ) := by exact_mod_cast hD
  have hcast : ((params.p ^ 2 - 4 * params.q : ℤ) : ℝ) =
      (params.p : ℝ) ^ 2 - 4 * (params.q : ℝ) := by push_cast; ring
  set s : ℝ := √((params.p ^ 2 - 4 * params.q : ℤ) : ℝ) with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.2 hDℝ
  have hs_sq : s ^ 2 = (params.p : ℝ) ^ 2 - 4 * (params.q : ℝ) := by
    rw [hs_def, Real.sq_sqrt hDℝ.le, hcast]
  have hs_lt : s < (params.p : ℝ) := by
    rw [hs_def, Real.sqrt_lt' hPℝ]
    rw [hcast]
    nlinarith [hQℝ]
  have hαeq : α = ((params.p : ℝ) + s) / 2 := rfl
  let β : ℝ := ((params.p : ℝ) - s) / 2
  have hβpos : 0 < β := by dsimp [β]; linarith
  have hαpos : 0 < α := by rw [hαeq]; linarith
  have hdiff : α - β = s := by rw [hαeq]; dsimp [β]; ring
  have hdiff_ne : α - β ≠ 0 := by rw [hdiff]; exact hs_pos.ne'
  have hsum : α + β = (params.p : ℝ) := by rw [hαeq]; dsimp [β]; ring
  have hprod : α * β = (params.q : ℝ) := by
    rw [hαeq]; dsimp [β]
    have h : ((params.p : ℝ) + s) / 2 * (((params.p : ℝ) - s) / 2) =
        ((params.p : ℝ) ^ 2 - s ^ 2) / 4 := by ring
    rw [h, hs_sq]
    ring
  have hαroot : α ^ 2 = (params.p : ℝ) * α - (params.q : ℝ) := by
    rw [hαeq]
    linear_combination hs_sq / 4
  have hβroot : β ^ 2 = (params.p : ℝ) * β - (params.q : ℝ) := by
    dsimp [β]
    linear_combination hs_sq / 4
  have hbinet := rogersDilog_lucasU_series.lucasU_eq hαroot hβroot hdiff_ne
  -- Powers of the conjugate roots.
  let S : ℝ := α ^ k
  let T : ℝ := β ^ k
  have hSpos : 0 < S := pow_pos hαpos k
  have hTpos : 0 < T := pow_pos hβpos k
  have hβα : β < α := by linarith [hdiff, hs_pos]
  have hTS : T < S := by
    dsimp [S, T]
    exact pow_lt_pow_left₀ hβα hβpos.le (by omega)
  have hST : S * T = (params.q : ℝ) ^ k := by
    dsimp [S, T]
    rw [← mul_pow, hprod]
  have hsumST : 0 < S + T := add_pos hSpos hTpos
  -- The parameter for the symmetric series.
  let a : ℝ := (S - T) / (S + T)
  have ha₀ : 0 < a := div_pos (sub_pos.mpr hTS) hsumST
  have ha₁ : a < 1 := by
    rw [div_lt_one hsumST]
    linarith [hTpos]
  have hhalf₁ : 1 / 2 - a / 2 = T / (S + T) := by
    dsimp [a]
    field_simp
    ring
  have hhalf₂ : 1 / 2 + a / 2 = S / (S + T) := by
    dsimp [a]
    field_simp
    ring
  have hseries := MetaMathlibExt.rogersDilog_sanford_symmetric_series (a := a) ha₀ ha₁
  change (∑' n : ℕ, L (a ^ 2 * (1 / 2 - a / 2) ^ (n + 1) * (1 / 2 + a / 2) ^ (n + 1) /
      ((1 / 2 + a / 2) ^ (n + 2) - (1 / 2 - a / 2) ^ (n + 2)) ^ 2)) =
    L ((1 - a) / (1 + a)) at hseries
  have hRHS : (1 - a) / (1 + a) = (params.q : ℝ) ^ k / α ^ (2 * k) := by
    have h1 : 1 - a = 2 * T / (S + T) := by
      dsimp [a]; field_simp; ring
    have h2 : 1 + a = 2 * S / (S + T) := by
      dsimp [a]; field_simp; ring
    have hdiv : (2 * T / (S + T)) / (2 * S / (S + T)) = T / S := by
      field_simp
    rw [h1, h2, hdiv]
    have hpow : α ^ (2 * k) = S ^ 2 := by
      dsimp [S]
      rw [show 2 * k = k * 2 by ring, pow_mul]
    rw [hpow]
    rw [div_eq_div_iff hSpos.ne' (pow_ne_zero 2 hSpos.ne')]
    calc T * S ^ 2 = (T * S) * S := by ring
      _ = (params.q : ℝ) ^ k * S := by rw [mul_comm T S, hST]
      _ = (params.q : ℝ) ^ k * S := rfl
  rw [hRHS] at hseries
  refine (tsum_congr fun n => congrArg L ?_).symm.trans hseries
  -- Identify each summand.
  have hdiff_pow (m : ℕ) : S ^ m - T ^ m =
      s * (lucasU params (k * m) : ℝ) := by
    have h := hbinet (k * m)
    rw [hdiff] at h
    have e1 : α ^ (k * m) = S ^ m := by dsimp [S]; rw [pow_mul]
    have e2 : β ^ (k * m) = T ^ m := by dsimp [T]; rw [pow_mul]
    rw [e1, e2] at h
    rw [h]
    field_simp
  have hUpos (m : ℕ) (hm : 0 < m) : 0 < (lucasU params (k * m) : ℝ) := by
    have h : 0 < S ^ m - T ^ m :=
      sub_pos.mpr (pow_lt_pow_left₀ hTS hTpos.le (by omega))
    rw [hdiff_pow] at h
    exact (pos_of_mul_pos_right h hs_pos.le)
  have hUne (m : ℕ) (hm : 0 < m) : (lucasU params (k * m) : ℝ) ≠ 0 :=
    (hUpos m hm).ne'
  have harg : a ^ 2 * (1 / 2 - a / 2) ^ (n + 1) * (1 / 2 + a / 2) ^ (n + 1) /
        ((1 / 2 + a / 2) ^ (n + 2) - (1 / 2 - a / 2) ^ (n + 2)) ^ 2 =
      (lucasU params k : ℝ) ^ 2 * (params.q : ℝ) ^ (k * (n + 1)) /
        (lucasU params (k * (n + 2)) : ℝ) ^ 2 := by
    rw [hhalf₁, hhalf₂]
    have hSTne : S + T ≠ 0 := hsumST.ne'
    have hcommon : ((S - T) / (S + T)) ^ 2 * (T / (S + T)) ^ (n + 1) *
          (S / (S + T)) ^ (n + 1) /
          ((S / (S + T)) ^ (n + 2) - (T / (S + T)) ^ (n + 2)) ^ 2 =
        (S - T) ^ 2 * (S * T) ^ (n + 1) / (S ^ (n + 2) - T ^ (n + 2)) ^ 2 := by
      rw [show (S / (S + T)) ^ (n + 2) - (T / (S + T)) ^ (n + 2) =
          (S ^ (n + 2) - T ^ (n + 2)) / (S + T) ^ (n + 2) by
        rw [div_pow, div_pow, ← sub_div]]
      rw [div_pow, div_pow, div_pow, div_pow]
      field_simp [hSTne]
      ring_nf
    have ha_eq : a = (S - T) / (S + T) := rfl
    have hdiff1 : S - T = s * (lucasU params k : ℝ) := by
      simpa using hdiff_pow 1
    have hdiff2 : S ^ (n + 2) - T ^ (n + 2) =
        s * (lucasU params (k * (n + 2)) : ℝ) := hdiff_pow (n + 2)
    have hQpow : (params.q : ℝ) ^ (k * (n + 1)) = (S * T) ^ (n + 1) := by
      rw [pow_mul, ← hST]
    rw [ha_eq, hcommon, hdiff1, hdiff2, hQpow]
    field_simp [hs_pos.ne', hUne (n + 2) (by omega)]
  exact harg

end MetaMathlibExt
