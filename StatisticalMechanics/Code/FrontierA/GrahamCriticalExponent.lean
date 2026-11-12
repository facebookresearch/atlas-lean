/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib











open Filter Set

namespace StatMech.FrontierA



noncomputable def grahamExponentRatio (f : Real -> Real) (t : Real) : Real :=
  Real.log (f t) / Real.log t


def HasGrahamCriticalExponent (f : Real -> Real) (a : Real) : Prop :=
  Tendsto (grahamExponentRatio f) (nhdsWithin 0 (Ioi 0)) (nhds a)






theorem grahamCriticalExponent_inequality
    (M chi D : Real -> Real) (beta gamma delta3 : Real)
    (hMpos : forall t, 0 < t -> t < 1 -> 0 < M t)
    (hchipos : forall t, 0 < t -> t < 1 -> 0 < chi t)
    (hDpos : forall t, 0 < t -> t < 1 -> 0 < D t)
    (hineq : forall t, 0 < t -> t < 1 ->
      2 * chi t ^ 2 * M t <= D t)
    (hM : HasGrahamCriticalExponent M beta)
    (hchi : HasGrahamCriticalExponent chi (-gamma))
    (hD : HasGrahamCriticalExponent D (-(gamma + delta3))) :
    gamma - beta <= delta3 := by
  have hnear : Filter.Eventually (fun t : Real => t < 1)
      (nhdsWithin (0 : Real) (Ioi 0)) := by
    exact (eventually_lt_nhds (show (0 : Real) < 1 by norm_num)).filter_mono inf_le_left
  have hev : Filter.Eventually (fun t => grahamExponentRatio D t <=
      2 * grahamExponentRatio chi t + grahamExponentRatio M t)
      (nhdsWithin (0 : Real) (Ioi 0)) := by
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht htp
    have ht0 : 0 < t := htp
    have hmp := hMpos t ht0 ht
    have hcp := hchipos t ht0 ht
    have hdp := hDpos t ht0 ht
    have hprod : chi t ^ 2 * M t <= D t := by
      have hn : 0 <= chi t ^ 2 * M t :=
        mul_nonneg (sq_nonneg _) hmp.le
      nlinarith [hineq t ht0 ht]
    have hlog : Real.log (chi t ^ 2 * M t) <= Real.log (D t) :=
      Real.log_le_log (mul_pos (sq_pos_of_pos hcp) hmp) hprod
    have hltlog : Real.log t < 0 := Real.log_neg ht0 ht
    unfold grahamExponentRatio
    rw [Real.log_mul (pow_ne_zero 2 hcp.ne') hmp.ne', Real.log_pow] at hlog
    have hneg : (-Real.log (D t)) / (-Real.log t) <=
        (-(2 * Real.log (chi t) + Real.log (M t))) / (-Real.log t) :=
      div_le_div_of_nonneg_right (neg_le_neg hlog) (neg_pos.mpr hltlog).le
    convert hneg using 1 <;> ring_nf
  have hright : Tendsto
      (fun t => 2 * grahamExponentRatio chi t + grahamExponentRatio M t)
      (nhdsWithin 0 (Ioi 0)) (nhds (-2 * gamma + beta)) := by
    convert (hchi.const_mul 2).add hM using 1
    all_goals ring_nf
  have hlim := le_of_tendsto_of_tendsto hD hright hev
  linarith

end StatMech.FrontierA
