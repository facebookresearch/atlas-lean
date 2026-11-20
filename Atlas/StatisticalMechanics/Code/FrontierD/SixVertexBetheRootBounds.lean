/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBethePerronBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexSelectedBetheM_norm_ge
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    (c ^ 2 - 2) / 2 ≤
      ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
  let p := sixVertexPositiveHalfBetheRoots hc k j
  let q : Real := (c ^ 2 - 2) / 2
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos p
  let den : Real := 2 - 2 * Real.cos p
  have hphase : sixVertexBethePhase p ≠ 1 := by
    exact sixVertexHalfFilledBetheRoots_phase_ne_one hc k
      (Fin.natAdd (k + 1) j)
  have hformula := sixVertexBetheM_phase_normSq c p hphase
  have hMne := sixVertexBetheM_phase_ne_zero hc p
  have hratioPos : 0 < num / den := by
    rw [← hformula]
    exact Complex.normSq_pos.mpr hMne
  have hden : 0 < den := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · have hnumNonneg : 0 ≤ num := by
        dsimp [num]
        have hcos := Real.neg_one_le_cos p
        have ha : 0 ≤ c ^ 2 - 1 := by nlinarith
        nlinarith [sq_nonneg (c ^ 2 - 2)]
      linarith
  have hdenLe : den ≤ 4 := by
    dsimp [den]
    linarith [Real.neg_one_le_cos p]
  have hq : 0 < q := by dsimp [q]; nlinarith
  have hnum : (c ^ 2 - 2) ^ 2 ≤ num := by
    dsimp [num]
    have hcos := Real.neg_one_le_cos p
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]
  have hratio : q ^ 2 ≤ num / den := by
    calc
      q ^ 2 = (c ^ 2 - 2) ^ 2 / 4 := by dsimp [q]; ring
      _ ≤ (c ^ 2 - 2) ^ 2 / den := by
        exact div_le_div_of_nonneg_left (sq_nonneg (c ^ 2 - 2)) hden hdenLe
      _ ≤ num / den := by
        exact div_le_div_of_nonneg_right hnum hden.le
  rw [← hformula] at hratio
  rw [Complex.normSq_eq_norm_sq] at hratio
  change q ≤ ‖sixVertexBetheM c (sixVertexBethePhase p)‖
  nlinarith [norm_nonneg (sixVertexBetheM c (sixVertexBethePhase p))]

theorem sixVertexSelectedBetheM_log_norm_ge
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.log ((c ^ 2 - 2) / 2) ≤
      Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
  apply Real.log_le_log (by nlinarith)
  exact sixVertexSelectedBetheM_norm_ge hc k j




theorem sixVertexSelectedRootAverage_ge
    {c : Real} (hc : 2 < c) (k : Nat) :
    Real.log ((c ^ 2 - 2) / 2) / 2 ≤
      sixVertexSymmetricBetheRootAverage c
        (sixVertexPositiveHalfBetheRootFamily hc) k := by
  let b : Real := Real.log ((c ^ 2 - 2) / 2)
  have hsum : (k + 1 : Real) * b ≤
      ∑ j : Fin (k + 1), Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
    calc
      (k + 1 : Real) * b = ∑ _j : Fin (k + 1), b := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact sixVertexSelectedBetheM_log_norm_ge hc k j
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexPositiveHalfBetheRootFamily
  rw [le_div_iff₀ hN]
  dsimp [b] at hsum ⊢
  rw [sixVertexFourWidth]
  push_cast
  nlinarith



theorem sixVertexHalfFilledBetheCandidateRate_ge
    {c : Real} (hc : 2 < c) (k : Nat) :
    Real.log ((c ^ 2 - 2) / 2) / 2 ≤
      sixVertexHalfFilledBetheCandidateRate hc k := by
  rw [sixVertexHalfFilledBetheCandidateRate_eq_rootAverage]
  have havg := sixVertexSelectedRootAverage_ge hc k
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hN : (0 : Real) ≤ sixVertexFourWidth 0 k := by positivity
  have hterm : 0 ≤ Real.log 2 / (sixVertexFourWidth 0 k : Real) :=
    div_nonneg hlog hN
  linarith



theorem sixVertexSelectedBetheM_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤
      c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by
  let p := sixVertexPositiveHalfBetheRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos p
  let den : Real := 2 - 2 * Real.cos p
  have hp : 0 < p := sixVertexPositiveHalfBetheRoots_pos hc k j
  have hpPi : p < Real.pi := sixVertexPositiveHalfBetheRoots_lt_pi hc k j
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hs : 0 < s := by dsimp [s]; positivity
  have hphase : sixVertexBethePhase p ≠ 1 :=
    sixVertexHalfFilledBetheRoots_phase_ne_one hc k
      (Fin.natAdd (k + 1) j)
  have hformula := sixVertexBetheM_phase_normSq c p hphase
  have hMne := sixVertexBetheM_phase_ne_zero hc p
  have hratioPos : 0 < num / den := by
    rw [← hformula]
    exact Complex.normSq_pos.mpr hMne
  have hden : 0 < den := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · have hnumNonneg : 0 ≤ num := by
        dsimp [num]
        have hcos := Real.neg_one_le_cos p
        have ha : 0 ≤ c ^ 2 - 1 := by nlinarith
        nlinarith [sq_nonneg (c ^ 2 - 2)]
      linarith
  have hnum : num ≤ c ^ 4 := by
    dsimp [num]
    have hcos := Real.cos_le_one p
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]
  have habsp : |p| ≤ Real.pi := by
    rw [abs_of_pos hp]
    exact hpPi.le
  have hcos := Real.cos_le_one_sub_mul_cos_sq habsp
  have hdenP : 4 * p ^ 2 ≤ Real.pi ^ 2 * den := by
    have hcos' := mul_le_mul_of_nonneg_left hcos (sq_nonneg Real.pi)
    field_simp [Real.pi_ne_zero] at hcos'
    dsimp [den]
    nlinarith
  have hquant := sixVertexPositiveHalfBetheRoots_quantile_lower hc k j
  change Real.pi * s < N * p at hquant
  have hquantSq : Real.pi ^ 2 * s ^ 2 ≤ N ^ 2 * p ^ 2 := by
    have hleft : 0 ≤ Real.pi * s := by positivity
    have hright : 0 ≤ N * p := by positivity
    nlinarith [(sq_le_sq₀ hleft hright).2 hquant.le]
  have hdenQuant : 4 * s ^ 2 ≤ N ^ 2 * den := by
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hNnonneg : 0 ≤ N ^ 2 := sq_nonneg N
    have hs1 := mul_le_mul_of_nonneg_left hdenP hNnonneg
    have hs2 := mul_le_mul_of_nonneg_left hquantSq (by norm_num : (0 : Real) ≤ 4)
    nlinarith
  have hratio : num / den ≤ (c ^ 2 * N / (2 * s)) ^ 2 := by
    rw [div_le_iff₀ hden]
    have hc4 : 0 ≤ c ^ 4 := by positivity
    have hscale := mul_le_mul_of_nonneg_left hdenQuant hc4
    have hsne : s ≠ 0 := hs.ne'
    have hNne : N ≠ 0 := hN.ne'
    calc
      num ≤ c ^ 4 := hnum
      _ ≤ (c ^ 2 * N / (2 * s)) ^ 2 * den := by
        field_simp [hsne, hNne] at hscale ⊢
        nlinarith
  rw [← hformula, Complex.normSq_eq_norm_sq] at hratio
  change ‖sixVertexBetheM c (sixVertexBethePhase p)‖ ≤
    c ^ 2 * N / (2 * s)
  have hright : 0 ≤ c ^ 2 * N / (2 * s) := by positivity
  nlinarith [norm_nonneg (sixVertexBetheM c (sixVertexBethePhase p))]



theorem sixVertexSelectedBetheM_log_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤
      Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1))) := by
  have hleft : 0 < ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ :=
    norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)
  exact Real.log_le_log hleft
    (sixVertexSelectedBetheM_norm_le_quantile hc k j)



noncomputable def sixVertexSelectedInitialLogContribution
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (2 * ∑ j : Fin (k + 1) with j.val < J,
      Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖) /
    (sixVertexFourWidth 0 k : Real)


theorem sixVertexSelectedInitialLogContribution_bounds
    {c : Real} (hc : 2 < c) (J k : Nat) :
    0 ≤ sixVertexSelectedInitialLogContribution hc J k ∧
      sixVertexSelectedInitialLogContribution hc J k ≤
        (2 * (J : Real) *
          Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) /
            (sixVertexFourWidth 0 k : Real) := by
  let S : Finset (Fin (k + 1)) := Finset.univ.filter (fun j => j.val < J)
  let B : Real := Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hq : 1 < (c ^ 2 - 2) / 2 := by nlinarith
  have htermNonneg (j : Fin (k + 1)) :
      0 ≤ Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
    have hnorm := sixVertexSelectedBetheM_norm_ge hc k j
    have hone : 1 ≤ ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ :=
      hq.le.trans hnorm
    exact Real.log_nonneg hone
  have htermUpper (j : Fin (k + 1)) :
      Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤
        B := by
    have hquant := sixVertexSelectedBetheM_log_norm_le_quantile hc k j
    have hj0 : (0 : Real) ≤ j := by positivity
    have hs : (1 : Real) ≤ 2 * (j : Real) + 1 := by linarith
    have hnum : 0 ≤ c ^ 2 * (sixVertexFourWidth 0 k : Real) := by positivity
    have hfrac : c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1)) ≤
        c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2 := by
      apply div_le_div_of_nonneg_left hnum (by positivity)
      nlinarith
    have hleft : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by positivity
    exact hquant.trans (Real.log_le_log hleft hfrac)
  have hcard : (S.card : Real) ≤ J := by
    have hsub : S ⊆ Finset.univ.filter (fun j : Fin (k + 1) => j.val < J) :=
      fun _ h => h
    have hcardNat : S.card ≤ J := by
      dsimp [S]
      calc
        (Finset.univ.filter (fun j : Fin (k + 1) => j.val < J)).card ≤
            (Finset.range J).card := by
          apply Finset.card_le_card_of_injOn (fun j => j.val)
          · intro j hj
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
          · intro a ha b hb hab
            exact Fin.ext hab
        _ = J := by simp
    exact_mod_cast hcardNat
  have hsumNonneg : 0 ≤ ∑ j ∈ S, Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
    apply Finset.sum_nonneg
    intro j hj
    exact htermNonneg j
  have hsumUpper : (∑ j ∈ S, Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖) ≤
      (J : Real) * B := by
    calc
      _ ≤ ∑ _j ∈ S, B := by
        apply Finset.sum_le_sum
        intro j hj
        exact htermUpper j
      _ = (S.card : Real) * B := by simp
      _ ≤ (J : Real) * B := by
        apply mul_le_mul_of_nonneg_right hcard
        dsimp [B]
        apply Real.log_nonneg
        have hN4 : (4 : Real) ≤ sixVertexFourWidth 0 k := by
          rw [sixVertexFourWidth]
          push_cast
          norm_num
        nlinarith [sq_nonneg c]
  unfold sixVertexSelectedInitialLogContribution
  change 0 ≤ (2 * ∑ j ∈ S, _) / _ ∧
    (2 * ∑ j ∈ S, _) / _ ≤ (2 * (J : Real) * B) / _
  constructor
  · positivity
  · apply div_le_div_of_nonneg_right _ hN.le
    nlinarith



theorem sixVertexSelectedInitialLogContribution_tendsto_zero
    {c : Real} (hc : 2 < c) (J : Nat) :
    Tendsto (sixVertexSelectedInitialLogContribution hc J) atTop (nhds 0) := by
  let A : Real := 2 * c ^ 2
  let m : Nat → Real := fun k => (k + 1 : Nat)
  have hA : 0 < A := by dsimp [A]; positivity
  have hm : Tendsto m atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hconst : Tendsto (fun k => Real.log A / m k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hm
  have hlog : Tendsto (fun k => Real.log (m k) / m k) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hm
    simpa [pow_one] using h
  have hupper : Tendsto (fun k : Nat =>
      (2 * (J : Real) *
        Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) /
          (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
    have hadd := hconst.add hlog
    have hmul := hadd.const_mul ((J : Real) / 2)
    convert hmul using 1
    · funext k
      have hmk : 0 < m k := by dsimp [m]; positivity
      rw [sixVertexFourWidth]
      dsimp [m, A]
      push_cast
      rw [show c ^ 2 * (4 * (0 + (k : Real) + 1)) / 2 =
          (2 * c ^ 2) * ((k : Real) + 1) by ring]
      rw [Real.log_mul (by positivity : (2 * c ^ 2 : Real) ≠ 0)
        (by positivity : ((k : Real) + 1) ≠ 0)]
      field_simp
      ring
    · norm_num
  apply squeeze_zero
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc J k).1
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc J k).2
  · exact hupper




theorem sixVertexSelectedInitialLogContribution_tendsto_zero_of_schedule
    {c : Real} (hc : 2 < c) (J : Nat -> Nat)
    (hscale : Tendsto (fun k : Nat =>
      (2 * (J k : Real) *
        Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) /
          (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
    Tendsto (fun k => sixVertexSelectedInitialLogContribution hc (J k) k)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc (J k) k).1
  · intro k
    exact (sixVertexSelectedInitialLogContribution_bounds hc (J k) k).2
  · exact hscale



theorem sixVertexSelectedInitialLogContribution_log2_tendsto_zero
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k => sixVertexSelectedInitialLogContribution hc
      (Nat.log2 (k + 1)) k) atTop (nhds 0) := by
  apply sixVertexSelectedInitialLogContribution_tendsto_zero_of_schedule hc
  let A : Real := 2 * c ^ 2
  let m : Nat -> Real := fun k => (k + 1 : Nat)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAone : 1 <= A := by dsimp [A]; nlinarith [sq_nonneg c]
  have hm : Tendsto m atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog1 : Tendsto (fun k => Real.log (m k) / m k) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hm
    simpa [pow_one] using h
  have hlog2 : Tendsto (fun k => Real.log (m k) ^ 2 / m k) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hm
    simpa using h
  have hupper : Tendsto (fun k =>
      (Real.log A / (2 * Real.log 2)) * (Real.log (m k) / m k) +
      (1 / (2 * Real.log 2)) * (Real.log (m k) ^ 2 / m k))
      atTop (nhds 0) := by
    convert (hlog1.const_mul (Real.log A / (2 * Real.log 2))).add
      (hlog2.const_mul (1 / (2 * Real.log 2))) using 1 <;> norm_num
  refine squeeze_zero ?_ ?_ hupper
  · intro k
    have harg : 1 <= c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2 := by
      have hN : (4 : Real) <= sixVertexFourWidth 0 k := by
        rw [sixVertexFourWidth]
        push_cast
        norm_num
      nlinarith [sq_nonneg c]
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg harg)) (by positivity)
  · intro k
    have hmpos : 0 < m k := by dsimp [m]; positivity
    have hmone : 1 <= m k := by
      dsimp [m]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hlogm : 0 <= Real.log (m k) := Real.log_nonneg hmone
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hJ := Real.log2_le_logb (k + 1)
    change (Nat.log2 (k + 1) : Real) <= Real.log (m k) / Real.log 2 at hJ
    have hfactor : 0 <= Real.log A + Real.log (m k) := by
      exact add_nonneg (Real.log_nonneg hAone) hlogm
    have hmul := mul_le_mul_of_nonneg_right hJ hfactor
    rw [sixVertexFourWidth]
    dsimp [m, A] at hmul ⊢
    push_cast at hmul ⊢
    rw [show c ^ 2 * (4 * (0 + (k : Real) + 1)) / 2 =
        (2 * c ^ 2) * ((k : Real) + 1) by ring]
    rw [Real.log_mul (by positivity : (2 * c ^ 2 : Real) ≠ 0)
      (by positivity : ((k : Real) + 1) ≠ 0)]
    field_simp [hlog2pos.ne', hmpos.ne'] at hmul ⊢
    nlinarith



theorem sixVertex_log2Cutoff_tendsto_atTop :
    Tendsto (fun k : Nat => Nat.log2 (k + 1)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨2 ^ b, ?_⟩
  intro k hk
  rw [Nat.le_log2 (by omega)]
  omega



theorem sixVertex_log2Cutoff_div_width_tendsto_zero :
    Tendsto (fun k : Nat =>
      (Nat.log2 (k + 1) : Real) / (k + 1 : Real)) atTop (nhds 0) := by
  let m : Nat -> Real := fun k => (k + 1 : Nat)
  have hm : Tendsto m atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun k =>
      (1 / Real.log 2) * (Real.log (m k) / m k)) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hm
    have h' : Tendsto (fun k => Real.log (m k) / m k) atTop (nhds 0) := by
      simpa [pow_one] using h
    convert h'.const_mul (1 / Real.log 2) using 1 <;> norm_num
  refine squeeze_zero ?_ ?_ hupper
  · intro k
    positivity
  · intro k
    have hmpos : 0 < m k := by dsimp [m]; positivity
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hJ := Real.log2_le_logb (k + 1)
    change (Nat.log2 (k + 1) : Real) <= Real.log (m k) / Real.log 2 at hJ
    dsimp [m] at hmpos hJ ⊢
    push_cast at hmpos hJ ⊢
    rw [div_le_iff₀ hmpos]
    field_simp [hlog2pos.ne'] at hJ ⊢
    nlinarith

end

end StatMech.FrontierD
