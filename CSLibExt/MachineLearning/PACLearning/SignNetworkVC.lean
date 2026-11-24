/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.GrowthFunction
public import CSLibExt.MachineLearning.PACLearning.SignNetworkGrowth
public import CSLibExt.MachineLearning.PACLearning.TraceCard
public import Cslib.MachineLearning.PACLearning.VCDimension

/-!
# VC dimension of sign-activation networks

The VC-dimension corollary of the network growth bound, after
Shalev-Shwartz and Ben-David, *Understanding Machine Learning:
From Theory to Algorithms*, Theorem 20.6: inverting
`2 ^ m ≤ (e * m) ^ E` bounds every shattered sample size by
`4 * E * log (2 * E) / log 2`, where `E = paramCount` counts the
weights and biases of the architecture. Hidden layers are assumed
to have at least one neuron, as in the source.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-- A numeric bound on `log 2`: since `1 - 2⁻¹ ≤ log 2`, doubling gives
`1 ≤ 2 * log 2`. -/
private theorem one_le_two_mul_log_two : (1 : ℝ) ≤ 2 * Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  have heq : (1 : ℝ) - (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [heq] at h
  calc (1 : ℝ) = 2 * (1 / 2) := by ring
    _ ≤ 2 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)

/-- Increment bound for `log`: on `(0, ∞)`, differences are controlled by
`log x' - log x ≤ (x' - x) / x`. -/
private theorem log_sub_le_div_sub (x x' : ℝ) (hx : 0 < x) (hx' : 0 < x') :
    Real.log x' - Real.log x ≤ (x' - x) / x := by
  rw [← Real.log_div hx'.ne' hx.ne']
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx' hx)
  have heq : (x' - x) / x = x' / x - 1 := by
    rw [sub_div, div_self hx.ne']
  rw [heq]
  exact hlog

/-- Core estimate at the threshold point: for `L2 ≤ t` with `1 ≤ 2 * L2`,
`1 ≤ 3 * t - L2 - log t + log L2`. The difference from the value `2 * L2`
at `t = L2` is controlled by the increment bound. -/
private theorem core_inequality (L2 t : ℝ) (hL2 : 0 < L2)
    (h12 : 1 ≤ 2 * L2) (ht : L2 ≤ t) (htpos : 0 < t) :
    1 ≤ 3 * t - L2 - Real.log t + Real.log L2 := by
  have hdiv : Real.log (t / L2) ≤ (t - L2) / L2 := by
    rw [Real.log_div htpos.ne' hL2.ne']
    exact log_sub_le_div_sub L2 t hL2 htpos
  have hinv : (1 : ℝ) / L2 ≤ 3 := by
    rw [div_le_iff₀ hL2]
    linarith only [h12, hL2]
  have hnn : (0 : ℝ) ≤ t - L2 := sub_nonneg.mpr ht
  have hmul : (t - L2) / L2 ≤ 3 * (t - L2) := by
    calc (t - L2) / L2 = (t - L2) * (1 / L2) := by ring
      _ ≤ (t - L2) * 3 := mul_le_mul_of_nonneg_left hinv hnn
      _ = 3 * (t - L2) := by ring
  have hmain : Real.log (t / L2) ≤ 3 * (t - L2) := le_trans hdiv hmul
  have hsplit : Real.log (t / L2) = Real.log t - Real.log L2 :=
    Real.log_div htpos.ne' hL2.ne'
  have hdecomp : 3 * t - L2 - Real.log t + Real.log L2 - 1 =
      (2 * L2 - 1) + (3 * (t - L2) - Real.log (t / L2)) := by
    rw [hsplit]
    ring
  have hpos : (0 : ℝ) ≤ (2 * L2 - 1) + (3 * (t - L2) - Real.log (t / L2)) := by
    refine add_nonneg ?_ (sub_nonneg.mpr hmain)
    linarith only [h12]
  rw [← hdecomp] at hpos
  exact sub_nonneg.mp hpos

/-- Strict increase of `x ↦ x * L2 - E * log x` on points above `E / L2`. -/
private theorem f_strict_mono_on (E L2 x x' : ℝ) (hE1 : 1 ≤ E)
    (hL2 : 0 < L2) (hdiv : E / L2 ≤ x) (hlt : x < x') (hxpos : 0 < x) :
    x * L2 - E * Real.log x < x' * L2 - E * Real.log x' := by
  have hEpos : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE1
  have hx'pos : (0 : ℝ) < x' := lt_trans hxpos hlt
  have hstrict : Real.log (x' / x) < (x' - x) / x := by
    have hgt : (1 : ℝ) < x' / x := by
      rw [lt_div_iff₀ hxpos]
      simpa using hlt
    have hne : x' / x ≠ 1 := ne_of_gt hgt
    have hle := Real.log_lt_sub_one_of_pos (div_pos hx'pos hxpos) hne
    have heq : (x' - x) / x = x' / x - 1 := by
      rw [sub_div, div_self hxpos.ne']
    rw [heq]
    exact hle
  have hEmul : E * Real.log (x' / x) < E * ((x' - x) / x) :=
    mul_lt_mul_of_pos_left hstrict hEpos
  have hEx : E / x ≤ L2 := by
    have h2 : E ≤ x * L2 := by
      have hdiv' := hdiv
      rwa [div_le_iff₀ hL2] at hdiv'
    rwa [div_le_iff₀ hxpos, mul_comm L2 x]
  have hfin : E * ((x' - x) / x) ≤ (x' - x) * L2 := by
    have hnn : (0 : ℝ) ≤ x' - x := sub_nonneg.mpr hlt.le
    calc E * ((x' - x) / x) = (x' - x) * (E / x) := by ring
      _ ≤ (x' - x) * L2 := mul_le_mul_of_nonneg_left hEx hnn
  have hchain : E * Real.log (x' / x) < (x' - x) * L2 :=
    lt_of_lt_of_le hEmul hfin
  have hlogeq : Real.log (x' / x) = Real.log x' - Real.log x :=
    Real.log_div hx'pos.ne' hxpos.ne'
  have hpos : (0 : ℝ) < (x' - x) * L2 - E * (Real.log x' - Real.log x) := by
    rw [← hlogeq]
    exact sub_pos.mpr hchain
  have hdecomp : (x' - x) * L2 - E * (Real.log x' - Real.log x) =
      (x' * L2 - E * Real.log x') - (x * L2 - E * Real.log x) := by
    ring
  rw [hdecomp] at hpos
  exact sub_pos.mp hpos

/-- Inversion of the exponential-polynomial bound: if
`2 ^ m ≤ (e * m) ^ E` with `1 ≤ E`, then
`m ≤ 4 * E * log (2 * E) / log 2`. -/
private theorem le_of_two_pow_le_exp_mul_pow (E m : ℕ) (hE : 1 ≤ E)
    (h : (2 : ℝ) ^ m ≤ (Real.exp 1 * (m : ℝ)) ^ E) :
    (m : ℝ) ≤ 4 * (E : ℝ) * Real.log (2 * (E : ℝ)) / Real.log 2 := by
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE
  have hE0 : (0 : ℝ) ≤ (E : ℝ) := le_trans zero_le_one hE1
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  have hL2 : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have h2E : (1 : ℝ) < 2 * (E : ℝ) := by linarith only [hE1]
  have htpos : (0 : ℝ) < Real.log (2 * (E : ℝ)) := Real.log_pos h2E
  have htL2 : Real.log 2 ≤ Real.log (2 * (E : ℝ)) := by
    apply Real.log_le_log (show (0 : ℝ) < 2 by norm_num)
    linarith only [hE1]
  have h4t : (1 : ℝ) ≤ 4 * Real.log (2 * (E : ℝ)) := by
    linarith only [one_le_two_mul_log_two, htL2]
  have h2Epos : (0 : ℝ) < 2 * (E : ℝ) :=
    mul_pos (show (0 : ℝ) < 2 by norm_num) hEpos
  have h4E : (0 : ℝ) < 4 * (E : ℝ) :=
    mul_pos (show (0 : ℝ) < 4 by norm_num) hEpos
  have hEt : (0 : ℝ) < 4 * (E : ℝ) * Real.log (2 * (E : ℝ)) :=
    mul_pos h4E htpos
  have hx1pos : (0 : ℝ) < 4 * (E : ℝ) * Real.log (2 * (E : ℝ)) / Real.log 2 :=
    div_pos hEt hL2
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hE0' : E ≠ 0 := by omega
    rw [Nat.cast_zero, mul_zero, pow_zero, zero_pow hE0'] at h
    norm_num at h
  · have hmpos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    set B : ℝ := 4 * (E : ℝ) * Real.log (2 * (E : ℝ)) / Real.log 2 with hBdef
    have hdivB : (E : ℝ) / Real.log 2 ≤ B := by
      rw [hBdef, div_le_iff₀ hL2, div_mul_cancel₀ _ hL2.ne']
      calc (E : ℝ) = (E : ℝ) * 1 := (mul_one _).symm
        _ ≤ (E : ℝ) * (4 * Real.log (2 * (E : ℝ))) :=
          mul_le_mul_of_nonneg_left h4t hE0
        _ = 4 * (E : ℝ) * Real.log (2 * (E : ℝ)) := by ring
    have hlogB : Real.log B =
        Real.log 4 + Real.log (E : ℝ) + Real.log (Real.log (2 * (E : ℝ))) -
          Real.log (Real.log 2) := by
      rw [hBdef, Real.log_div hEt.ne' hL2.ne', Real.log_mul h4E.ne' htpos.ne',
        Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hEpos.ne']
    have hlog4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlogE : Real.log (E : ℝ) = Real.log (2 * (E : ℝ)) - Real.log 2 := by
      have h := Real.log_div h2Epos.ne' (show (2 : ℝ) ≠ 0 by norm_num)
      have heq : (2 : ℝ) * (E : ℝ) / 2 = (E : ℝ) := by ring
      rw [heq] at h
      exact h
    have hBL2 : B * Real.log 2 = 4 * (E : ℝ) * Real.log (2 * (E : ℝ)) := by
      rw [hBdef, div_mul_cancel₀ _ hL2.ne']
    have hAtB : (E : ℝ) ≤ B * Real.log 2 - (E : ℝ) * Real.log B := by
      have hexpand : B * Real.log 2 - (E : ℝ) * Real.log B =
          (E : ℝ) * (3 * Real.log (2 * (E : ℝ)) - Real.log 2 -
            Real.log (Real.log (2 * (E : ℝ))) + Real.log (Real.log 2)) := by
        rw [hlogB, hlog4', hlogE, hBL2]
        ring
      rw [hexpand]
      have hcore := core_inequality _ _ hL2 one_le_two_mul_log_two htL2 htpos
      calc (E : ℝ) = (E : ℝ) * 1 := (mul_one _).symm
        _ ≤ (E : ℝ) * (3 * Real.log (2 * (E : ℝ)) - Real.log 2 -
            Real.log (Real.log (2 * (E : ℝ))) + Real.log (Real.log 2)) :=
          mul_le_mul_of_nonneg_left hcore hE0
    by_contra hcon
    rw [not_le] at hcon
    have hmono : B * Real.log 2 - (E : ℝ) * Real.log B <
        (m : ℝ) * Real.log 2 - (E : ℝ) * Real.log (m : ℝ) :=
      f_strict_mono_on _ _ _ _ hE1 hL2 hdivB hcon hx1pos
    have hlt1 : (E : ℝ) < (m : ℝ) * Real.log 2 - (E : ℝ) * Real.log (m : ℝ) :=
      lt_of_le_of_lt hAtB hmono
    have hElog : (E : ℝ) * Real.log (Real.exp 1 * (m : ℝ)) =
        (E : ℝ) + (E : ℝ) * Real.log (m : ℝ) := by
      rw [Real.log_mul (Real.exp_ne_zero 1) hmpos'.ne', Real.log_exp, mul_add,
        mul_one]
    have hlt2 : (E : ℝ) * Real.log (Real.exp 1 * (m : ℝ)) <
        (m : ℝ) * Real.log 2 := by
      rw [hElog]
      have hpos : (0 : ℝ) <
          ((m : ℝ) * Real.log 2 - (E : ℝ) * Real.log (m : ℝ)) - (E : ℝ) :=
        sub_pos.mpr hlt1
      have hdecomp : ((m : ℝ) * Real.log 2 - (E : ℝ) * Real.log (m : ℝ)) -
          (E : ℝ) =
          (m : ℝ) * Real.log 2 - ((E : ℝ) + (E : ℝ) * Real.log (m : ℝ)) := by
        ring
      rw [hdecomp] at hpos
      exact sub_pos.mp hpos
    have hlog2pow : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    have hlogEpow : Real.log ((Real.exp 1 * (m : ℝ)) ^ E) =
        (E : ℝ) * Real.log (Real.exp 1 * (m : ℝ)) := by
      rw [Real.log_pow]
    have hloglt : Real.log ((Real.exp 1 * (m : ℝ)) ^ E) <
        Real.log ((2 : ℝ) ^ m) := by
      rw [hlog2pow, hlogEpow]
      exact hlt2
    have hApos : (0 : ℝ) < (2 : ℝ) ^ m :=
      pow_pos (show (0 : ℝ) < 2 by norm_num) m
    have hBpos : (0 : ℝ) < (Real.exp 1 * (m : ℝ)) ^ E :=
      pow_pos (mul_pos (Real.exp_pos 1) hmpos') E
    have hfinal : (Real.exp 1 * (m : ℝ)) ^ E < (2 : ℝ) ^ m :=
      (Real.log_lt_log_iff hBpos hApos).mp hloglt
    exact absurd h (not_le_of_gt hfinal)

/-- Below threshold: at `E = 2`, `m = 8` the hypothesis holds, so the
inversion gives `8 ≤ 16`. -/
example : (8 : ℝ) ≤ 16 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase : (2 : ℝ) * 8 ≤ Real.exp 1 * 8 :=
    mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ 8 by norm_num)
  have hpow : ((2 : ℝ) * 8) ^ (2 : ℕ) ≤ (Real.exp 1 * 8) ^ (2 : ℕ) :=
    pow_le_pow_left₀
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (show (0 : ℝ) ≤ 8 by norm_num))
      hbase 2
  have hhyp : (2 : ℝ) ^ (8 : ℕ) ≤ (Real.exp 1 * (8 : ℝ)) ^ (2 : ℕ) := by
    calc (2 : ℝ) ^ (8 : ℕ) = 256 := by norm_num
      _ ≤ ((2 : ℝ) * 8) ^ (2 : ℕ) := by norm_num
      _ ≤ (Real.exp 1 * 8) ^ (2 : ℕ) := hpow
  have hcon :=
    le_of_two_pow_le_exp_mul_pow 2 8 (show 1 ≤ 2 by norm_num)
      (by exact_mod_cast hhyp)
  have hRHS : 4 * (2 : ℝ) * Real.log (2 * 2) / Real.log 2 = 16 := by
    have hlog4 : Real.log (2 * 2) = 2 * Real.log 2 := by
      rw [show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hne : Real.log 2 ≠ 0 :=
      (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne'
    rw [hlog4, div_eq_iff hne]
    ring
  have hcon' : (8 : ℝ) ≤ 4 * (2 : ℝ) * Real.log (2 * 2) / Real.log 2 := by
    simpa using hcon
  rw [hRHS] at hcon'
  exact hcon'

/-- Above threshold: at `E = 2`, `m = 20` the conclusion fails, so the
hypothesis fails by contrapositive. -/
example : ¬ (2 : ℝ) ^ (20 : ℕ) ≤ (Real.exp 1 * (20 : ℝ)) ^ (2 : ℕ) := by
  have hRHS : 4 * (2 : ℝ) * Real.log (2 * 2) / Real.log 2 = 16 := by
    have hlog4 : Real.log (2 * 2) = 2 * Real.log 2 := by
      rw [show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hne : Real.log 2 ≠ 0 :=
      (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne'
    rw [hlog4, div_eq_iff hne]
    ring
  have hcon : ¬ ((20 : ℕ) : ℝ) ≤
      4 * ((2 : ℕ) : ℝ) * Real.log (2 * ((2 : ℕ) : ℝ)) / Real.log 2 := by
    have h20 : ¬ ((20 : ℕ) : ℝ) ≤ 16 := by norm_num
    simpa [hRHS] using h20
  intro hhyp
  exact hcon
    (le_of_two_pow_le_exp_mul_pow 2 20 (show 1 ≤ 2 by norm_num)
      (by exact_mod_cast hhyp))

/-- The parameter count is positive: the output summand alone contributes
`fanIn + 1 ≥ 1`. -/
private theorem one_le_paramCount (d : ℕ) (w : ℕ → ℕ) (L : ℕ) :
    1 ≤ paramCount d w L := by
  have hwL : widthAt w L L = 1 := by simp [widthAt]
  unfold paramCount
  have hmem : L ∈ Finset.range (L + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self L)
  have hle : (fanIn d w L + 1) * widthAt w L L ≤
      Finset.sum (Finset.range (L + 1))
        (fun i => (fanIn d w i + 1) * widthAt w L i) :=
    Finset.single_le_sum (f := fun i => (fanIn d w i + 1) * widthAt w L i)
      (s := Finset.range (L + 1)) (a := L) (fun _ _ => Nat.zero_le _) hmem
  rw [hwL, mul_one] at hle
  have h1 : (1 : ℕ) ≤ fanIn d w L + 1 := by omega
  exact le_trans h1 hle

/-- The parameter count is below the VC bound: `E ≤ 4 * E * log (2 * E) /
log 2` since `log 2 ≤ log (2 * E)`. -/
private theorem paramCount_le_vcBound (d : ℕ) (w : ℕ → ℕ) (L : ℕ) :
    (paramCount d w L : ℝ) ≤
      4 * (paramCount d w L : ℝ) *
        Real.log (2 * (paramCount d w L : ℝ)) / Real.log 2 := by
  have hE1 : (1 : ℝ) ≤ (paramCount d w L : ℝ) := by
    exact_mod_cast one_le_paramCount d w L
  have hE0 : (0 : ℝ) ≤ (paramCount d w L : ℝ) := le_trans zero_le_one hE1
  have hL2 : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have h2E : (2 : ℝ) ≤ 2 * (paramCount d w L : ℝ) := by
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (paramCount d w L : ℝ) := mul_le_mul_of_nonneg_left hE1
        (show (0 : ℝ) ≤ 2 by norm_num)
  have ht : Real.log 2 ≤ Real.log (2 * (paramCount d w L : ℝ)) :=
    Real.log_le_log (show (0 : ℝ) < 2 by norm_num) h2E
  have ht0 : (0 : ℝ) ≤ Real.log (2 * (paramCount d w L : ℝ)) :=
    le_trans (le_of_lt hL2) ht
  rw [le_div_iff₀ hL2]
  have h1 : (paramCount d w L : ℝ) * Real.log 2 ≤
      (paramCount d w L : ℝ) * Real.log (2 * (paramCount d w L : ℝ)) :=
    mul_le_mul_of_nonneg_left ht hE0
  have hnn : (0 : ℝ) ≤
      (paramCount d w L : ℝ) * Real.log (2 * (paramCount d w L : ℝ)) :=
    mul_nonneg hE0 ht0
  have h4 : (paramCount d w L : ℝ) * Real.log (2 * (paramCount d w L : ℝ)) ≤
      4 * (paramCount d w L : ℝ) * Real.log (2 * (paramCount d w L : ℝ)) := by
    calc (paramCount d w L : ℝ) * Real.log (2 * (paramCount d w L : ℝ))
        = 1 * ((paramCount d w L : ℝ) *
          Real.log (2 * (paramCount d w L : ℝ))) := by ring
      _ ≤ 4 * ((paramCount d w L : ℝ) *
          Real.log (2 * (paramCount d w L : ℝ))) :=
          mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 4 by norm_num) hnn
      _ = 4 * (paramCount d w L : ℝ) * Real.log (2 * (paramCount d w L : ℝ)) :=
        by ring
  exact le_trans h1 h4

/-- Every shattered sample is below the VC bound: either some fan-in
already exceeds the sample (and `paramCount` dominates that fan-in), or
the collapsed growth bound applies and the numeric inversion finishes. -/
private theorem card_le_bound_of_shatters (d : ℕ) (w : ℕ → ℕ) (L : ℕ)
    (hw : ∀ i, i < L → 0 < w i) (W : Finset (layerTy d w 0))
    (hW : SetShatters (networkClass d w L) ↑W) :
    (W.card : ℝ) ≤
      4 * (paramCount d w L : ℝ) *
        Real.log (2 * (paramCount d w L : ℝ)) / Real.log 2 := by
  by_cases hsmall : ∃ i, i ≤ L ∧ W.card < fanIn d w i + 1
  · obtain ⟨i, hiL, hilt⟩ := hsmall
    have hWle : W.card ≤ fanIn d w i := by omega
    have hsum : (fanIn d w i + 1) * widthAt w L i ≤ paramCount d w L := by
      unfold paramCount
      exact Finset.single_le_sum (f := fun i => (fanIn d w i + 1) * widthAt w L i)
        (s := Finset.range (L + 1)) (a := i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega : i < L + 1))
    have hdom : fanIn d w i < (fanIn d w i + 1) * widthAt w L i := by
      by_cases hiL' : i < L
      · have hwi : widthAt w L i = w i := by simp [widthAt, hiL']
        rw [hwi]
        exact lt_of_lt_of_le (Nat.lt_succ_self _)
          (Nat.le_mul_of_pos_right _ (hw i hiL'))
      · have hiL'' : L = i := by omega
        subst hiL''
        have hwL : widthAt w L L = 1 := by simp [widthAt]
        rw [hwL, mul_one]
        exact Nat.lt_succ_self _
    have hlt : W.card < paramCount d w L :=
      lt_of_le_of_lt hWle (lt_of_lt_of_le hdom hsum)
    have hcast : (W.card : ℝ) ≤ (paramCount d w L : ℝ) := by
      exact_mod_cast Nat.le_of_lt hlt
    exact le_trans hcast (paramCount_le_vcBound d w L)
  · have hsmall' : ∀ i, i ≤ L → fanIn d w i + 1 ≤ W.card := by
      intro i hiL
      by_contra hcon
      rw [not_le] at hcon
      exact hsmall ⟨i, hiL, hcon⟩
    have hE : 1 ≤ paramCount d w L := one_le_paramCount d w L
    have h1 := setShatters_iff_card_traceFamily.mp hW
    have h2 : (traceFamily (networkClass d w L) W).card ≤
        growthFunction (networkClass d w L) W.card :=
      traceFamily_card_le_growthFunction _ _
    have h3 : 2 ^ W.card ≤ growthFunctionVec (networkClass d w L) W.card := by
      rw [← h1, growthFunctionVec_bool_eq]
      exact h2
    have h4 : (2 : ℝ) ^ W.card ≤
        (growthFunctionVec (networkClass d w L) W.card : ℝ) := by
      exact_mod_cast h3
    have h5 : (2 : ℝ) ^ W.card ≤
        (Real.exp 1 * (W.card : ℝ)) ^ paramCount d w L :=
      le_trans h4 (growthFunctionVec_networkClass_le_exp_pow d w L W.card hsmall')
    exact le_of_two_pow_le_exp_mul_pow _ _ hE h5

/-- A sign-activation network with nonempty hidden layers has
finite VC dimension. -/
theorem networkClass_hasFiniteVCDim (d : ℕ) (w : ℕ → ℕ) (L : ℕ)
    (hw : ∀ i, i < L → 0 < w i) :
    HasFiniteVCDim (networkClass d w L) := by
  obtain ⟨N, hN⟩ := exists_nat_ge
    (4 * (paramCount d w L : ℝ) * Real.log (2 * (paramCount d w L : ℝ)) /
      Real.log 2)
  refine hasFiniteVCDim_iff.mpr ⟨N, fun W hW => ?_⟩
  have hnum := card_le_bound_of_shatters d w L hw W hW
  exact Nat.cast_le.mp (le_trans hnum hN)

/-- The VC dimension of a sign-activation network is
`O(E log E)` in its parameter count `E`. -/
theorem vcDim_networkClass_le (d : ℕ) (w : ℕ → ℕ) (L : ℕ)
    (hw : ∀ i, i < L → 0 < w i) :
    (vcDim (networkClass d w L) : ℝ) ≤
      4 * (paramCount d w L : ℝ) *
        Real.log (2 * (paramCount d w L : ℝ)) / Real.log 2 := by
  have hE1 : (1 : ℝ) ≤ (paramCount d w L : ℝ) := by
    exact_mod_cast one_le_paramCount d w L
  have h2E1 : (1 : ℝ) ≤ 2 * (paramCount d w L : ℝ) := by
    calc (1 : ℝ) ≤ (paramCount d w L : ℝ) := hE1
      _ ≤ 2 * (paramCount d w L : ℝ) := by
        calc (paramCount d w L : ℝ) = 1 * (paramCount d w L : ℝ) := by ring
          _ ≤ 2 * (paramCount d w L : ℝ) :=
            mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num)
              (le_trans zero_le_one hE1)
  have ht0 : (0 : ℝ) ≤ Real.log (2 * (paramCount d w L : ℝ)) :=
    Real.log_nonneg h2E1
  have hL2 : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hB0 : (0 : ℝ) ≤ 4 * (paramCount d w L : ℝ) *
      Real.log (2 * (paramCount d w L : ℝ)) / Real.log 2 := by
    apply div_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
          (le_trans zero_le_one hE1)
      · exact ht0
    · exact le_of_lt hL2
  have hfin : BddAbove {n : ℕ | ∃ W : Finset (layerTy d w 0),
      W.card = n ∧ SetShatters (networkClass d w L) ↑W} :=
    networkClass_hasFiniteVCDim d w L hw
  by_cases hne : {n : ℕ | ∃ W : Finset (layerTy d w 0),
      W.card = n ∧ SetShatters (networkClass d w L) ↑W}.Nonempty
  · obtain ⟨W, hWc, hW⟩ := Nat.sSup_mem hne hfin
    have hnum := card_le_bound_of_shatters d w L hw W hW
    have heq : ((sSup {n : ℕ | ∃ W : Finset (layerTy d w 0),
        W.card = n ∧ SetShatters (networkClass d w L) ↑W} : ℕ) : ℝ) =
        (W.card : ℝ) := by
      rw [← hWc]
    unfold vcDim
    rw [heq]
    exact hnum
  · have hSeq : {n : ℕ | ∃ W : Finset (layerTy d w 0),
        W.card = n ∧ SetShatters (networkClass d w L) ↑W} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have hV : vcDim (networkClass d w L) = 0 := by
      unfold vcDim
      rw [hSeq]
      simp
    rw [hV]
    simpa using hB0

/-- Consistency at zero hidden layers: a single neuron is a
halfspace, of VC dimension `d + 1`. -/
theorem vcDim_networkClass_zero (d : ℕ) (w : ℕ → ℕ) :
    vcDim (networkClass d w 0) = d + 1 := by
  exact halfspaceClass_vcDim d

end Cslib.MachineLearning.PACLearning
