/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronDensity
import Code.FrontierD.SixVertexBetheBulkReduction










open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexEvenPositiveHalfProjection_quantile_lower
    {c : Real} (hc : 2 < c) {k : Nat}
    {p : Fin ((k + 1) + (k + 1)) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) p) (j : Fin (k + 1)) :
    Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth 0 k : Real) *
        sixVertexEvenPositiveHalfProjection (k + 1) p j := by
  let i : Fin ((k + 1) + (k + 1)) := Fin.natAdd (k + 1) j
  have hrevlt : i.rev < i := by
    rw [Fin.lt_def]
    dsimp [i]
    omega
  have hspace := sixVertexBetheSolution_quantumSpacing hc hopen hsol hrevlt
  have hsymm := hopen.2.1 i
  have hI : sixVertexCentralQuantumNumber i -
      sixVertexCentralQuantumNumber i.rev = 2 * (j : Real) + 1 := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp only [Fin.rev, Fin.val_mk]
    dsimp [i]
    have hjle : j.val ≤ k := by omega
    have hnat : k + 1 + (k + 1) - (k + 1 + j.val + 1) =
        k - j.val := by omega
    rw [hnat]
    push_cast [Nat.cast_sub hjle]
    ring
  rw [hI, hsymm] at hspace
  change Real.pi * (2 * (j : Real) + 1) <
    (sixVertexFourWidth 0 k : Real) * p i
  simpa [i] using (show Real.pi * (2 * (j : Real) + 1) <
    (sixVertexFourWidth 0 k : Real) * p i by nlinarith)

theorem sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j ∈
      Set.Ioo 0 Real.pi := by
  apply sixVertexEvenSymmetricLift_positive_mem_Ioo
  unfold sixVertexCanonicalDensityPerronPositiveHalfRoots
  rw [sixVertexEvenSymmetricLift_projection (k + 1)
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k).2.1]
  exact sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k

theorem sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth 0 k : Real) *
        sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j := by
  exact sixVertexEvenPositiveHalfProjection_quantile_lower hc
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
    (sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k) j



theorem sixVertexCanonicalDensityPerronBetheM_norm_ge
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    (c ^ 2 - 2) / 2 ≤
      ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ := by
  let q : Real := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let lower : Real := (c ^ 2 - 2) / 2
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos q
  let den : Real := 2 - 2 * Real.cos q
  have hphase : sixVertexBethePhase q ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (Fin.natAdd (k + 1) j)
  have hformula := sixVertexBetheM_phase_normSq c q hphase
  have hMne := sixVertexBetheM_phase_ne_zero hc q
  have hratioPos : 0 < num / den := by
    rw [← hformula]
    exact Complex.normSq_pos.mpr hMne
  have hden : 0 < den := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · have hnumNonneg : 0 ≤ num := by
        dsimp [num]
        have hcos := Real.neg_one_le_cos q
        have ha : 0 ≤ c ^ 2 - 1 := by nlinarith
        nlinarith [sq_nonneg (c ^ 2 - 2)]
      linarith
  have hdenLe : den ≤ 4 := by
    dsimp [den]
    linarith [Real.neg_one_le_cos q]
  have hlower : 0 < lower := by dsimp [lower]; nlinarith
  have hnum : (c ^ 2 - 2) ^ 2 ≤ num := by
    dsimp [num]
    have hcos := Real.neg_one_le_cos q
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]
  have hratio : lower ^ 2 ≤ num / den := by
    calc
      lower ^ 2 = (c ^ 2 - 2) ^ 2 / 4 := by dsimp [lower]; ring
      _ ≤ (c ^ 2 - 2) ^ 2 / den :=
        div_le_div_of_nonneg_left (sq_nonneg _) hden hdenLe
      _ ≤ num / den := div_le_div_of_nonneg_right hnum hden.le
  rw [← hformula, Complex.normSq_eq_norm_sq] at hratio
  change lower ≤ ‖sixVertexBetheM c (sixVertexBethePhase q)‖
  nlinarith [norm_nonneg (sixVertexBetheM c (sixVertexBethePhase q))]



theorem sixVertexCanonicalDensityPerronBetheM_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ ≤
      c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by
  let p := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos p
  let den : Real := 2 - 2 * Real.cos p
  have hp := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).1
  have hpPi := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hs : 0 < s := by dsimp [s]; positivity
  have hphase : sixVertexBethePhase p ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
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
  have hquant :=
    sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc k j
  change Real.pi * s < N * p at hquant
  have hquantSq : Real.pi ^ 2 * s ^ 2 ≤ N ^ 2 * p ^ 2 := by
    have hleft : 0 ≤ Real.pi * s := by positivity
    have hright : 0 ≤ N * p := by positivity
    nlinarith [(sq_le_sq₀ hleft hright).2 hquant.le]
  have hdenQuant : 4 * s ^ 2 ≤ N ^ 2 * den := by
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hNnonneg : 0 ≤ N ^ 2 := sq_nonneg N
    have hs1 := mul_le_mul_of_nonneg_left hdenP hNnonneg
    have hs2 := mul_le_mul_of_nonneg_left hquantSq
      (by norm_num : (0 : Real) ≤ 4)
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

theorem sixVertexCanonicalDensityPerronBetheM_log_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ ≤
      Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1))) := by
  have hleft : 0 < ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ :=
    norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)
  exact Real.log_le_log hleft
    (sixVertexCanonicalDensityPerronBetheM_norm_le_quantile hc k j)



def sixVertexCanonicalDensityPerronInitialLogContribution
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (2 * ∑ j : Fin (k + 1) with j.val < J,
      Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖) /
    (sixVertexFourWidth 0 k : Real)

theorem sixVertexCanonicalDensityPerronBetheM_log_norm_nonneg
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    0 ≤ Real.log ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ := by
  apply Real.log_nonneg
  have hq : 1 < (c ^ 2 - 2) / 2 := by nlinarith
  exact hq.le.trans
    (sixVertexCanonicalDensityPerronBetheM_norm_ge hc k j)

theorem sixVertexCanonicalDensityPerronInitialLogContribution_nonneg
    {c : Real} (hc : 2 < c) (J k : Nat) :
    0 ≤ sixVertexCanonicalDensityPerronInitialLogContribution hc J k := by
  unfold sixVertexCanonicalDensityPerronInitialLogContribution
  apply div_nonneg
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    exact sixVertexCanonicalDensityPerronBetheM_log_norm_nonneg hc k j
  · positivity



theorem sixVertexCanonicalDensityPerronInitialLogContribution_le_factorial
    {c : Real} (hc : 2 < c) {J k : Nat} (hJ : J ≤ k + 1) :
    sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
      (2 * ((J : Real) *
          Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) -
        Real.log (J.factorial : Real))) /
        (sixVertexFourWidth 0 k : Real) := by
  let S : Finset (Fin (k + 1)) :=
    Finset.univ.filter (fun j => j.val < J)
  let B : Real :=
    Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)
  let f : Fin (k + 1) → Real := fun j =>
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hterm (j : Fin (k + 1)) :
      f j ≤ B - Real.log ((j.val + 1 : Nat) : Real) := by
    have hquant :=
      sixVertexCanonicalDensityPerronBetheM_log_norm_le_quantile hc k j
    have hnum : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) := by
      positivity
    have hjpos : (0 : Real) < (j.val + 1 : Nat) := by positivity
    have hsmall : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by positivity
    have hfrac : c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1)) ≤
        c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * ((j.val + 1 : Nat) : Real)) := by
      apply div_le_div_of_nonneg_left hnum.le (by positivity)
      push_cast
      nlinarith [show (0 : Real) ≤ j by positivity]
    calc
      f j ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1))) := hquant
      _ ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * ((j.val + 1 : Nat) : Real))) :=
        Real.log_le_log hsmall hfrac
      _ = B - Real.log ((j.val + 1 : Nat) : Real) := by
        dsimp [B]
        rw [show c ^ 2 * (sixVertexFourWidth 0 k : Real) /
            (2 * ((j.val + 1 : Nat) : Real)) =
          (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) /
            ((j.val + 1 : Nat) : Real) by ring]
        rw [Real.log_div (by positivity) hjpos.ne']
  have hsum : (∑ j ∈ S, f j) ≤
      ∑ j ∈ S, (B - Real.log ((j.val + 1 : Nat) : Real)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hterm j
  have hindex :
      (∑ j ∈ S, (B - Real.log ((j.val + 1 : Nat) : Real))) =
        ∑ i ∈ Finset.range J,
          (B - Real.log ((i + 1 : Nat) : Real)) := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro a ha b hb hab
      exact Fin.ext hab
    · intro i hi
      have hiJ := Finset.mem_range.mp hi
      let j : Fin (k + 1) := ⟨i, lt_of_lt_of_le hiJ hJ⟩
      refine ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiJ⟩
    · intro j hj
      rfl
  have hlogs :
      (∑ i ∈ Finset.range J, Real.log ((i + 1 : Nat) : Real)) =
        Real.log (J.factorial : Real) := by
    rw [← Real.log_prod (fun i hi => by positivity)]
    apply congrArg Real.log
    norm_cast
    exact Finset.prod_range_add_one_eq_factorial J
  have hsum' : (∑ j ∈ S, f j) ≤
      (J : Real) * B - Real.log (J.factorial : Real) := by
    rw [hindex, Finset.sum_sub_distrib, hlogs] at hsum
    simpa using hsum
  unfold sixVertexCanonicalDensityPerronInitialLogContribution
  change (2 * ∑ j ∈ S, f j) / _ ≤ _
  apply div_le_div_of_nonneg_right _ hN.le
  nlinarith

theorem sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling
    {c : Real} (hc : 2 < c) {J k : Nat} (hJ0 : 0 < J)
    (hJ : J ≤ k + 1) :
    sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
      (2 * (J : Real) *
        (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (J : Real))) + 1)) /
        (sixVertexFourWidth 0 k : Real) := by
  let N : Real := sixVertexFourWidth 0 k
  let B : Real := Real.log (c ^ 2 * N / 2)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hJreal : (0 : Real) < J := by exact_mod_cast hJ0
  have hlogJ : 0 ≤ Real.log (J : Real) :=
    Real.log_nonneg (by exact_mod_cast hJ0)
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hfactorial := Stirling.le_log_factorial_stirling hJ0.ne'
  have hfactorial' :
      (J : Real) * Real.log (J : Real) - (J : Real) ≤
        Real.log (J.factorial : Real) := by
    calc
      (J : Real) * Real.log (J : Real) - (J : Real) ≤
          (J : Real) * Real.log (J : Real) - (J : Real) +
            Real.log (J : Real) / 2 + Real.log (2 * Real.pi) / 2 := by
        nlinarith [hlogJ, hlogTwoPi]
      _ ≤ Real.log (J.factorial : Real) := hfactorial
  have hlog :
      Real.log (c ^ 2 * N / (2 * (J : Real))) =
        B - Real.log (J : Real) := by
    dsimp [B]
    rw [show c ^ 2 * N / (2 * (J : Real)) =
      (c ^ 2 * N / 2) / (J : Real) by ring]
    rw [Real.log_div (by positivity) hJreal.ne']
  have hbase :=
    sixVertexCanonicalDensityPerronInitialLogContribution_le_factorial hc hJ
  change sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
    (2 * ((J : Real) * B - Real.log (J.factorial : Real))) / N at hbase
  change sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
    (2 * (J : Real) *
      (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N
  calc
    sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤
        (2 * ((J : Real) * B - Real.log (J.factorial : Real))) / N := hbase
    _ ≤ (2 * (J : Real) *
        (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      rw [hlog]
      nlinarith



theorem sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear
    {c : Real} (hc : 2 < c) (J : Nat → Nat)
    (hJ0 : ∀ᶠ k in atTop, 0 < J k)
    (hJle : ∀ᶠ k in atTop, J k ≤ k + 1)
    (hsublinear : Tendsto (fun k : Nat =>
      (J k : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronInitialLogContribution hc (J k) k)
      atTop (nhds 0) := by
  let x : Nat → Real := fun k =>
    (J k : Real) / (sixVertexFourWidth 0 k : Real)
  let C : Real := Real.log (c ^ 2 / 2)
  have hx : Tendsto x atTop (nhds 0) := hsublinear
  have hxlog : Tendsto (fun k => x k * Real.log (x k))
      atTop (nhds 0) := by
    have h := Real.continuous_mul_log.continuousAt.tendsto.comp hx
    simpa using h
  have hupper : Tendsto (fun k =>
      2 * x k * (C - Real.log (x k) + 1)) atTop (nhds 0) := by
    have hlinear := hx.const_mul (2 * (C + 1))
    have hlogterm := hxlog.const_mul 2
    convert hlinear.sub hlogterm using 1
    · funext k
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards [] with k
    exact sixVertexCanonicalDensityPerronInitialLogContribution_nonneg hc
      (J k) k
  · filter_upwards [hJ0, hJle] with k hk0 hkle
    have hN : (0 : Real) < sixVertexFourWidth 0 k := by
      exact_mod_cast sixVertexFourWidth_pos 0 k
    have hJreal : (0 : Real) < J k := by exact_mod_cast hk0
    have hxpos : 0 < x k := div_pos hJreal hN
    have hratio :
        c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (J k : Real)) =
          (c ^ 2 / 2) / x k := by
      dsimp [x]
      field_simp [hN.ne', hJreal.ne']
    calc
      sixVertexCanonicalDensityPerronInitialLogContribution hc (J k) k ≤
          (2 * (J k : Real) *
            (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
              (2 * (J k : Real))) + 1)) /
            (sixVertexFourWidth 0 k : Real) :=
        sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling
          hc hk0 hkle
      _ = 2 * x k * (C - Real.log (x k) + 1) := by
        rw [hratio, Real.log_div (by positivity : c ^ 2 / 2 ≠ 0)
          hxpos.ne']
        dsimp [x, C]
        ring
  · exact hupper



theorem sixVertexCanonicalDensityPerronInitialLogContribution_log2_tendsto_zero
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronInitialLogContribution hc
        (Nat.log2 (k + 1)) k) atTop (nhds 0) := by
  apply
    sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear
      hc
  · filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Nat.lt_iff_add_one_le, Nat.le_log2 (by omega)]
    omega
  · filter_upwards [] with k
    exact Nat.log2_le_self (k + 1)
  · have h := sixVertex_log2Cutoff_div_width_tendsto_zero.const_mul
        (1 / 4 : Real)
    convert h using 1
    · funext k
      unfold sixVertexFourWidth
      push_cast
      have hkpos : (0 : Real) < (k : Real) + 1 := by positivity
      field_simp [hkpos.ne']
      ring
    · norm_num

end

end StatMech.FrontierD
