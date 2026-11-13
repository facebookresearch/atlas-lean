/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.QuantumIsingUniformAsymptotic
import Code.FrontierA.QuantumIsingArcoshAsymptotic
import Code.FrontierA.QuantumIsingReducedParameterBounds









open Filter Set
open scoped Topology

namespace StatMech.FrontierA

noncomputable def quantumIsingScaledArcosh
    (beta h : Real) (n : Nat) (k : Real) : Real :=
  (n + 1 : Real) * Real.arcosh
    (quantumIsingTrotterReducedParameter beta h (n + 1) k)

private theorem quantumIsingScaledReducedLimit_nonneg
    (beta h k : Real) :
    0 <= quantumIsingScaledReducedLimit beta h k := by
  unfold quantumIsingScaledReducedLimit
  positivity

private theorem quantumIsingScaledReducedLimit_le
    (beta h k : Real) :
    quantumIsingScaledReducedLimit beta h k <=
      beta ^ 2 / 8 * (1 + 4 * h ^ 2 + 4 * |h|) := by
  have hcos : h * Real.cos k <= |h| := by
    calc
      h * Real.cos k <= |h * Real.cos k| := le_abs_self _
      _ = |h| * |Real.cos k| := abs_mul _ _
      _ <= |h| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one k) (abs_nonneg h)
      _ = |h| := mul_one _
  have hcoef : 0 <= beta ^ 2 / 8 := by positivity
  unfold quantumIsingScaledReducedLimit quantumIsingDispersion
  rw [Real.sq_sqrt (quantumIsing_radicand_nonneg h k)]
  exact mul_le_mul_of_nonneg_left (by linarith) hcoef



theorem eventually_one_le_quantumIsingTrotterReducedParameter
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    ∀ᶠ n : Nat in atTop, ∀ k : Real,
      1 <= quantumIsingTrotterReducedParameter beta h (n + 1) k := by
  have hxlim : Tendsto
      (fun n : Nat => beta * h / (2 * (n + 1 : Real)))
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (beta * h / 2)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    field_simp
  have hxlt : ∀ᶠ n : Nat in atTop,
      beta * h / (2 * (n + 1 : Real)) < 1 :=
    (tendsto_order.1 hxlim).2 1 (by norm_num)
  filter_upwards [hxlt] with n hn k
  apply one_le_quantumIsingTrotterReducedParameter beta h (n + 1) k
  · positivity
  · exact div_pos (mul_pos hbeta hh) (by positivity)
  · simpa only [Nat.cast_add, Nat.cast_one] using hn


theorem quantumIsingTrotterReducedParameter_tendstoUniformly_one
    (beta h : Real) (hbeta : 0 < beta) :
    TendstoUniformly
      (fun n k => quantumIsingTrotterReducedParameter beta h (n + 1) k)
      (fun _ => 1) atTop := by
  let B : Real := beta ^ 2 / 8 * (1 + 4 * h ^ 2 + 4 * |h|)
  have hB : 0 <= B := by
    dsimp only [B]
    have : 0 <= 1 + 4 * h ^ 2 + 4 * |h| := by positivity
    positivity
  have hscaled := quantumIsingScaledReducedParameter_tendstoUniformly beta h hbeta
  have hscaledOne := (Metric.tendstoUniformly_iff.mp hscaled) 1 (by norm_num)
  have hsmall : Tendsto (fun n : Nat => (B + 1) / (n + 1 : Real))
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (B + 1)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hsmallE⟩ := (Metric.tendsto_atTop.1 hsmall) epsilon hepsilon
  filter_upwards [hscaledOne, eventually_ge_atTop N] with n hn hnN k
  have hne := hsmallE n hnN
  have hnk := hn k
  rw [Real.dist_eq] at hnk hne
  rw [dist_comm, Real.dist_eq]
  have hlimit0 := quantumIsingScaledReducedLimit_nonneg beta h k
  have hlimitB : quantumIsingScaledReducedLimit beta h k <= B := by
    simpa only [B] using quantumIsingScaledReducedLimit_le beta h k
  have hscaledBound : |quantumIsingScaledReducedParameter beta h n k| <= B + 1 := by
    calc
      |quantumIsingScaledReducedParameter beta h n k| <=
          |quantumIsingScaledReducedParameter beta h n k -
            quantumIsingScaledReducedLimit beta h k| +
            |quantumIsingScaledReducedLimit beta h k| := by
              simpa [sub_eq_add_neg, abs_neg, add_comm] using
                abs_add_le
                  (quantumIsingScaledReducedParameter beta h n k -
                    quantumIsingScaledReducedLimit beta h k)
                  (quantumIsingScaledReducedLimit beta h k)
      _ <= 1 + B := by
        rw [abs_of_nonneg hlimit0]
        exact add_le_add (by simpa [abs_sub_comm] using hnk.le) hlimitB
      _ = B + 1 := by ring
  have hnpos : 0 < (n + 1 : Real) := by positivity
  have hnpow : (n + 1 : Real) <= (n + 1 : Real) ^ 2 := by
    have hnat : 1 <= n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hnone : (1 : Real) <= (n + 1 : Real) := by exact_mod_cast hnat
    nlinarith
  change |quantumIsingTrotterReducedParameter beta h (n + 1) k - 1| < epsilon
  have hidentity :
      quantumIsingTrotterReducedParameter beta h (n + 1) k - 1 =
        quantumIsingScaledReducedParameter beta h n k / (n + 1 : Real) ^ 2 := by
    unfold quantumIsingScaledReducedParameter
    field_simp
  rw [hidentity, abs_div]
  have hdenpos : 0 < |(n + 1 : Real) ^ 2| := abs_pos.mpr (by positivity)
  calc
    |quantumIsingScaledReducedParameter beta h n k| /
        |(n + 1 : Real) ^ 2| <= (B + 1) / (n + 1 : Real) ^ 2 := by
      rw [abs_of_pos (by positivity : 0 < (n + 1 : Real) ^ 2)]
      exact div_le_div_of_nonneg_right hscaledBound (by positivity)
    _ <= (B + 1) / (n + 1 : Real) := by
      exact div_le_div_of_nonneg_left (by positivity) hnpos hnpow
    _ < epsilon := by
      have hne' : |(B + 1) / (n + 1 : Real)| < epsilon := by
        simpa only [sub_zero] using hne
      exact lt_of_le_of_lt (le_abs_self _) hne'



theorem quantumIsingTrotter_arcosh_tendstoUniformly_zero
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly
      (fun n k => Real.arcosh
        (quantumIsingTrotterReducedParameter beta h (n + 1) k))
      (fun _ => 0) atTop := by
  have hA := quantumIsingTrotterReducedParameter_tendstoUniformly_one beta h hbeta
  have hbranch := eventually_one_le_quantumIsingTrotterReducedParameter beta h hbeta hh
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hcont := (Metric.continuousWithinAt_iff.mp
    (Real.continuousOn_arcosh 1 (by simp))) epsilon hepsilon
  obtain ⟨delta, hdelta, hmap⟩ := hcont
  have hclose := (Metric.tendstoUniformly_iff.mp hA) delta hdelta
  filter_upwards [hbranch, hclose] with n hn hnc k
  have hm := hmap (hn k) (by simpa [dist_comm] using hnc k)
  have harcoshOne : Real.arcosh 1 = 0 :=
    (Real.arcosh_eq_zero_iff (le_refl (1 : Real))).2 rfl
  simpa [harcoshOne, dist_comm] using hm



theorem quantumIsing_arcoshQuadraticRatio_tendstoUniformly_two
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly
      (fun n k => arcoshQuadraticRatio (Real.arcosh
        (quantumIsingTrotterReducedParameter beta h (n + 1) k)))
      (fun _ => 2) atTop := by
  have hu := quantumIsingTrotter_arcosh_tendstoUniformly_zero beta h hbeta hh
  have hbranch := eventually_one_le_quantumIsingTrotterReducedParameter beta h hbeta hh
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hcont := (Metric.continuousWithinAt_iff.mp
    (continuousOn_arcoshQuadraticRatio 0 (by simp))) epsilon hepsilon
  obtain ⟨delta, hdelta, hmap⟩ := hcont
  have hclose := (Metric.tendstoUniformly_iff.mp hu) delta hdelta
  filter_upwards [hbranch, hclose] with n hn hnc k
  have hnonneg : 0 <= Real.arcosh
      (quantumIsingTrotterReducedParameter beta h (n + 1) k) :=
    Real.arcosh_nonneg (hn k)
  have hm := hmap hnonneg (by simpa [dist_comm] using hnc k)
  simpa [arcoshQuadraticRatio, dist_comm] using hm

private theorem quantumIsingScaledArcosh_sq_tendstoUniformly
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly
      (fun n k => quantumIsingScaledArcosh beta h n k ^ 2)
      (fun k => 2 * quantumIsingScaledReducedLimit beta h k) atTop := by
  let B : Real := beta ^ 2 / 8 * (1 + 4 * h ^ 2 + 4 * |h|)
  have hB : 0 <= B := by
    dsimp only [B]
    positivity
  have hC := quantumIsingScaledReducedParameter_tendstoUniformly beta h hbeta
  have hR := quantumIsing_arcoshQuadraticRatio_tendstoUniformly_two beta h hbeta hh
  have hbranch := eventually_one_le_quantumIsingTrotterReducedParameter beta h hbeta hh
  have hCone := (Metric.tendstoUniformly_iff.mp hC) 1 (by norm_num)
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hden : 0 < 2 * (B + 1) := by positivity
  have hRe := (Metric.tendstoUniformly_iff.mp hR)
    (epsilon / (2 * (B + 1))) (div_pos hepsilon hden)
  have hCe := (Metric.tendstoUniformly_iff.mp hC) (epsilon / 4) (by positivity)
  filter_upwards [hbranch, hCone, hRe, hCe] with n hn hC1 hRn hCn k
  have hC1k := hC1 k
  have hRnk := hRn k
  have hCnk := hCn k
  rw [Real.dist_eq] at hC1k hRnk hCnk ⊢
  have hlimit0 := quantumIsingScaledReducedLimit_nonneg beta h k
  have hlimitB : quantumIsingScaledReducedLimit beta h k <= B := by
    simpa only [B] using quantumIsingScaledReducedLimit_le beta h k
  have hscaledBound : |quantumIsingScaledReducedParameter beta h n k| <= B + 1 := by
    calc
      |quantumIsingScaledReducedParameter beta h n k| <=
          |quantumIsingScaledReducedParameter beta h n k -
            quantumIsingScaledReducedLimit beta h k| +
            |quantumIsingScaledReducedLimit beta h k| := by
              simpa [sub_eq_add_neg, abs_neg, add_comm] using
                abs_add_le
                  (quantumIsingScaledReducedParameter beta h n k -
                    quantumIsingScaledReducedLimit beta h k)
                  (quantumIsingScaledReducedLimit beta h k)
      _ <= 1 + B := by
        rw [abs_of_nonneg hlimit0]
        exact add_le_add (by simpa [abs_sub_comm] using hC1k.le) hlimitB
      _ = B + 1 := by ring
  have hsq := scaled_arcosh_sq_eq_ratio (n + 1 : Real)
    (quantumIsingTrotterReducedParameter beta h (n + 1) k) (hn k)
  change |2 * quantumIsingScaledReducedLimit beta h k -
      quantumIsingScaledArcosh beta h n k ^ 2| < epsilon
  rw [quantumIsingScaledArcosh, hsq]
  change |2 * quantumIsingScaledReducedLimit beta h k -
      arcoshQuadraticRatio (Real.arcosh
        (quantumIsingTrotterReducedParameter beta h (n + 1) k)) *
        quantumIsingScaledReducedParameter beta h n k| < epsilon
  rw [show 2 * quantumIsingScaledReducedLimit beta h k -
      arcoshQuadraticRatio (Real.arcosh
        (quantumIsingTrotterReducedParameter beta h (n + 1) k)) *
        quantumIsingScaledReducedParameter beta h n k =
      (2 - arcoshQuadraticRatio (Real.arcosh
        (quantumIsingTrotterReducedParameter beta h (n + 1) k))) *
          quantumIsingScaledReducedParameter beta h n k +
        2 * (quantumIsingScaledReducedLimit beta h k -
          quantumIsingScaledReducedParameter beta h n k) by ring]
  calc
    |(2 - arcoshQuadraticRatio (Real.arcosh
          (quantumIsingTrotterReducedParameter beta h (n + 1) k))) *
          quantumIsingScaledReducedParameter beta h n k +
        2 * (quantumIsingScaledReducedLimit beta h k -
          quantumIsingScaledReducedParameter beta h n k)| <=
      |2 - arcoshQuadraticRatio (Real.arcosh
          (quantumIsingTrotterReducedParameter beta h (n + 1) k))| *
          |quantumIsingScaledReducedParameter beta h n k| +
        2 * |quantumIsingScaledReducedLimit beta h k -
          quantumIsingScaledReducedParameter beta h n k| := by
      simpa [abs_mul] using abs_add_le
        ((2 - arcoshQuadraticRatio (Real.arcosh
          (quantumIsingTrotterReducedParameter beta h (n + 1) k))) *
            quantumIsingScaledReducedParameter beta h n k)
        (2 * (quantumIsingScaledReducedLimit beta h k -
          quantumIsingScaledReducedParameter beta h n k))
    _ < (epsilon / (2 * (B + 1))) * (B + 1) + 2 * (epsilon / 4) := by
      apply add_lt_add_of_le_of_lt
      · exact mul_le_mul hRnk.le hscaledBound (abs_nonneg _) (by positivity)
      · exact mul_lt_mul_of_pos_left hCnk (by norm_num)
    _ = epsilon := by field_simp; ring

private theorem sq_abs_sub_le_abs_sq_sub_sq (x y : Real)
    (hx : 0 <= x) (hy : 0 <= y) :
    |x - y| ^ 2 <= |x ^ 2 - y ^ 2| := by
  have hdiff : |x - y| <= x + y := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |x - y| ^ 2 <= |x - y| * (x + y) :=
      by simpa [pow_two] using
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg (x - y))
    _ = |x ^ 2 - y ^ 2| := by
      rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul,
        abs_of_nonneg (add_nonneg hx hy)]



theorem quantumIsingScaledArcosh_tendstoUniformly
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly (fun n k => quantumIsingScaledArcosh beta h n k)
      (fun k => Real.sqrt (2 * quantumIsingScaledReducedLimit beta h k)) atTop := by
  have hsq := quantumIsingScaledArcosh_sq_tendstoUniformly beta h hbeta hh
  have hbranch := eventually_one_le_quantumIsingTrotterReducedParameter beta h hbeta hh
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hsqe := (Metric.tendstoUniformly_iff.mp hsq) (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  filter_upwards [hbranch, hsqe] with n hn hs k
  have hsk := hs k
  rw [Real.dist_eq] at hsk ⊢
  have hscaledNonneg : 0 <= quantumIsingScaledArcosh beta h n k := by
    unfold quantumIsingScaledArcosh
    exact mul_nonneg (by positivity) (Real.arcosh_nonneg (hn k))
  have hlimitNonneg : 0 <= 2 * quantumIsingScaledReducedLimit beta h k := by
    exact mul_nonneg (by norm_num) (quantumIsingScaledReducedLimit_nonneg beta h k)
  have hsqrtNonneg := Real.sqrt_nonneg (2 * quantumIsingScaledReducedLimit beta h k)
  have hsqrtSq : Real.sqrt (2 * quantumIsingScaledReducedLimit beta h k) ^ 2 =
      2 * quantumIsingScaledReducedLimit beta h k :=
    Real.sq_sqrt hlimitNonneg
  have hdom := sq_abs_sub_le_abs_sq_sub_sq
    (Real.sqrt (2 * quantumIsingScaledReducedLimit beta h k))
    (quantumIsingScaledArcosh beta h n k) hsqrtNonneg hscaledNonneg
  rw [hsqrtSq] at hdom
  have habsNonneg : 0 <= |Real.sqrt (2 * quantumIsingScaledReducedLimit beta h k) -
      quantumIsingScaledArcosh beta h n k| := abs_nonneg _
  nlinarith [hsk]

theorem sqrt_two_mul_quantumIsingScaledReducedLimit
    (beta h k : Real) (hbeta : 0 < beta) :
    Real.sqrt (2 * quantumIsingScaledReducedLimit beta h k) =
      beta / 2 * quantumIsingDispersion h k := by
  have hb : 0 <= beta / 2 := (div_pos hbeta (by norm_num)).le
  have hd : 0 <= quantumIsingDispersion h k := by
    unfold quantumIsingDispersion
    positivity
  rw [show 2 * quantumIsingScaledReducedLimit beta h k =
      (beta / 2 * quantumIsingDispersion h k) ^ 2 by
    unfold quantumIsingScaledReducedLimit
    ring,
    Real.sqrt_sq (mul_nonneg hb hd)]



theorem quantumIsingScaledArcosh_tendstoUniformly_dispersion
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly (fun n k => quantumIsingScaledArcosh beta h n k)
      (fun k => beta / 2 * quantumIsingDispersion h k) atTop := by
  have hlimit := quantumIsingScaledArcosh_tendstoUniformly beta h hbeta hh
  convert hlimit using 1
  funext k
  exact (sqrt_two_mul_quantumIsingScaledReducedLimit beta h k hbeta).symm

end StatMech.FrontierA
