/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianTrivialityReduction











open Filter Topology

namespace StatMech.FrontierA



theorem log_sq_div_dimensionPower_tendsto_zero
    (d : Nat) (hd : 4 < d) (C : Real) :
    Tendsto
      (fun x : Real => C ^ 2 * Real.log (x ^ 2) ^ 2 / x ^ (d - 4))
      atTop (nhds 0) := by
  have hbase : Tendsto (fun x : Real => Real.log x ^ 2 / x)
      atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hlinear : Tendsto
      (fun x : Real => C ^ 2 * Real.log (x ^ 2) ^ 2 / x)
      atTop (nhds 0) := by
    have hscaled : Tendsto
        (fun x : Real => (4 * C ^ 2) * (Real.log x ^ 2 / x))
        atTop (nhds 0) := by
      simpa using hbase.const_mul (4 * C ^ 2)
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [Real.log_pow]
    ring
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hpow : x <= x ^ (d - 4) := by
      have he : 1 <= d - 4 := by omega
      simpa only [pow_one] using pow_le_pow_right₀ hx he
    exact div_le_div_of_nonneg_left
      (mul_nonneg (sq_nonneg C) (sq_nonneg _)) hxpos hpow
  · exact hlinear







theorem renormalizedCoupling_tendsto_zero_of_treeDiagram_infrared
    (d : Nat) (hd : 4 < d) (C : Real)
    (xi chi coupling : Nat -> Real)
    (hxi : Tendsto xi atTop atTop)
    (hchi : ∀ᶠ n in atTop,
      0 <= chi n /\
        chi n <= C * xi n ^ 2 * Real.log (xi n ^ 2))
    (htree : forall n, 0 <= coupling n /\
      coupling n <= chi n ^ 2 / xi n ^ d) :
    Tendsto coupling atTop (nhds 0) := by
  have henvelope : Tendsto
      (fun n => C ^ 2 * Real.log (xi n ^ 2) ^ 2 / xi n ^ (d - 4))
      atTop (nhds 0) :=
    (log_sq_div_dimensionPower_tendsto_zero d hd C).comp hxi
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => (htree n).1) _ henvelope
  filter_upwards [hchi, hxi.eventually (eventually_ge_atTop (1 : Real))]
      with n hchin hxin
  have hxpos : 0 < xi n := lt_of_lt_of_le zero_lt_one hxin
  have hsquare : chi n ^ 2 <=
      (C * xi n ^ 2 * Real.log (xi n ^ 2)) ^ 2 :=
    (sq_le_sq₀ hchin.1 (hchin.1.trans hchin.2)).2 hchin.2
  have hratio : chi n ^ 2 / xi n ^ d <=
      (C * xi n ^ 2 * Real.log (xi n ^ 2)) ^ 2 / xi n ^ d :=
    div_le_div_of_nonneg_right hsquare (pow_nonneg hxpos.le d)
  have hexact :
      (C * xi n ^ 2 * Real.log (xi n ^ 2)) ^ 2 / xi n ^ d =
        C ^ 2 * Real.log (xi n ^ 2) ^ 2 / xi n ^ (d - 4) := by
    have hd' : d = (d - 4) + 4 := by omega
    rw [hd', pow_add]
    field_simp
    congr 3
    omega
  exact (htree n).2.trans (hratio.trans_eq hexact)

end StatMech.FrontierA
