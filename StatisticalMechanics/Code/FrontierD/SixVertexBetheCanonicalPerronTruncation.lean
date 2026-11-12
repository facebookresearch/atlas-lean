/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronBulk









open Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheLogNumerator (c x : Real) : Real :=
  (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x

def sixVertexBetheLogDenominator (x : Real) : Real :=
  2 - 2 * Real.cos x


def sixVertexRegularizedBetheLogKernel
    (c epsilon x : Real) : Real :=
  (1 / 2 : Real) *
    (Real.log (sixVertexBetheLogNumerator c x) -
      Real.log (sixVertexBetheLogDenominator x + epsilon))

theorem sixVertexBetheLogNumerator_lower
    {c : Real} (hc : 2 < c) (x : Real) :
    (c ^ 2 - 2) ^ 2 <= sixVertexBetheLogNumerator c x := by
  unfold sixVertexBetheLogNumerator
  have hcos := Real.neg_one_le_cos x
  have ha : 0 < c ^ 2 - 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]

theorem sixVertexBetheLogNumerator_pos
    {c : Real} (hc : 2 < c) (x : Real) :
    0 < sixVertexBetheLogNumerator c x := by
  have h := sixVertexBetheLogNumerator_lower hc x
  have hc2 : 0 < c ^ 2 - 2 := by
    have hcplus : 0 < c + 2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hc) hcplus]
  have hsquare : 0 < (c ^ 2 - 2) ^ 2 := by
    exact pow_pos hc2 2
  linarith

theorem sixVertexBetheLogDenominator_nonneg (x : Real) :
    0 <= sixVertexBetheLogDenominator x := by
  unfold sixVertexBetheLogDenominator
  linarith [Real.cos_le_one x]

private theorem abs_log_sub_log_le_of_lower
    {m x y : Real} (hm : 0 < m) (hx : m <= x) (hy : m <= y) :
    |Real.log x - Real.log y| <= |x - y| / m := by
  have hxpos : 0 < x := hm.trans_le hx
  have hypos : 0 < y := hm.trans_le hy
  have hforward {u v : Real} (hu : m <= u) (huPos : 0 < u)
      (hvPos : 0 < v) (huv : u <= v) :
      Real.log v - Real.log u <= (v - u) / m := by
    calc
      Real.log v - Real.log u = Real.log (v / u) := by
        rw [Real.log_div hvPos.ne' huPos.ne']
      _ <= v / u - 1 := Real.log_le_sub_one_of_pos (div_pos hvPos huPos)
      _ = (v - u) / u := by field_simp [huPos.ne']
      _ <= (v - u) / m := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hm hu
  rcases le_total x y with hxy | hyx
  · have hlog := hforward hx hxpos hypos hxy
    rw [abs_of_nonpos (sub_nonpos.mpr
      (Real.log_le_log hxpos hxy)), abs_of_nonpos (sub_nonpos.mpr hxy)]
    convert hlog using 1 <;> ring
  · have hlog := hforward hy hypos hxpos hyx
    rw [abs_of_nonneg (sub_nonneg.mpr
      (Real.log_le_log hypos hyx)), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hlog

theorem abs_sixVertexBetheLogNumerator_sub_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    |sixVertexBetheLogNumerator c x -
        sixVertexBetheLogNumerator c y| <=
      (2 * (c ^ 2 - 1)) * |x - y| := by
  unfold sixVertexBetheLogNumerator
  rw [show
    (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x -
        ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos y) =
      (2 * (c ^ 2 - 1)) * (Real.cos x - Real.cos y) by ring,
    abs_mul, abs_of_pos (by nlinarith : 0 < 2 * (c ^ 2 - 1))]
  exact mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le x y)
    (by nlinarith [sq_nonneg c])

theorem abs_sixVertexBetheLogDenominator_sub_le (x y : Real) :
    |sixVertexBetheLogDenominator x -
        sixVertexBetheLogDenominator y| <= 2 * |x - y| := by
  unfold sixVertexBetheLogDenominator
  rw [show (2 - 2 * Real.cos x) - (2 - 2 * Real.cos y) =
      -2 * (Real.cos x - Real.cos y) by ring,
    abs_mul]
  norm_num
  exact Real.abs_cos_sub_cos_le x y


def sixVertexRegularizedBetheLogLipschitzConstant
    (c epsilon : Real) : NNReal :=
  Real.toNNReal ((1 / 2 : Real) *
    ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2 + 2 / epsilon))



theorem lipschitzWith_sixVertexRegularizedBetheLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    LipschitzWith (sixVertexRegularizedBetheLogLipschitzConstant c epsilon)
      (sixVertexRegularizedBetheLogKernel c epsilon) := by
  let A : Real :=
    (1 / 2 : Real) *
      ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2 + 2 / epsilon)
  have hc2 : 0 < c ^ 2 - 2 := by
    have hcplus : 0 < c + 2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hc) hcplus]
  have hc1 : 0 <= 2 * (c ^ 2 - 1) := by nlinarith
  have hA : 0 <= A := by
    dsimp [A]
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hc1 (sq_nonneg _))
        (div_nonneg (by norm_num) hepsilon.le))
  let C : NNReal := sixVertexRegularizedBetheLogLipschitzConstant c epsilon
  change LipschitzWith C _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hnum := abs_log_sub_log_le_of_lower
    (m := (c ^ 2 - 2) ^ 2)
    (pow_pos hc2 2)
    (sixVertexBetheLogNumerator_lower hc x)
    (sixVertexBetheLogNumerator_lower hc y)
  have hden := abs_log_sub_log_le_of_lower
    (m := epsilon)
    (x := sixVertexBetheLogDenominator x + epsilon)
    (y := sixVertexBetheLogDenominator y + epsilon) hepsilon
    (by
      have := sixVertexBetheLogDenominator_nonneg x
      linarith)
    (by
      have := sixVertexBetheLogDenominator_nonneg y
      linarith)
  have hnumDiff := abs_sixVertexBetheLogNumerator_sub_le hc x y
  have hdenDiff := abs_sixVertexBetheLogDenominator_sub_le x y
  rw [show (C : Real) = A by
    dsimp [C, sixVertexRegularizedBetheLogLipschitzConstant]
    exact Real.coe_toNNReal _ hA]
  change |sixVertexRegularizedBetheLogKernel c epsilon x -
      sixVertexRegularizedBetheLogKernel c epsilon y| <= A * |x - y|
  unfold sixVertexRegularizedBetheLogKernel
  have hnum' :
      |Real.log (sixVertexBetheLogNumerator c x) -
          Real.log (sixVertexBetheLogNumerator c y)| <=
        ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2) * |x - y| := by
    calc
      _ <= |sixVertexBetheLogNumerator c x -
          sixVertexBetheLogNumerator c y| / (c ^ 2 - 2) ^ 2 := hnum
      _ <= (2 * (c ^ 2 - 1) * |x - y|) / (c ^ 2 - 2) ^ 2 :=
        div_le_div_of_nonneg_right hnumDiff (sq_nonneg _)
      _ = ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2) * |x - y| := by
        ring
  have hden' :
      |Real.log (sixVertexBetheLogDenominator x + epsilon) -
          Real.log (sixVertexBetheLogDenominator y + epsilon)| <=
        (2 / epsilon) * |x - y| := by
    calc
      _ <= |(sixVertexBetheLogDenominator x + epsilon) -
          (sixVertexBetheLogDenominator y + epsilon)| / epsilon := hden
      _ = |sixVertexBetheLogDenominator x -
          sixVertexBetheLogDenominator y| / epsilon := by
        rw [show (sixVertexBetheLogDenominator x + epsilon) -
          (sixVertexBetheLogDenominator y + epsilon) =
          sixVertexBetheLogDenominator x -
            sixVertexBetheLogDenominator y by ring]
      _ <= (2 * |x - y|) / epsilon :=
        div_le_div_of_nonneg_right hdenDiff hepsilon.le
      _ = (2 / epsilon) * |x - y| := by ring
  calc
    |(1 / 2 : Real) *
        (Real.log (sixVertexBetheLogNumerator c x) -
          Real.log (sixVertexBetheLogDenominator x + epsilon)) -
      (1 / 2 : Real) *
        (Real.log (sixVertexBetheLogNumerator c y) -
          Real.log (sixVertexBetheLogDenominator y + epsilon))| =
      (1 / 2 : Real) *
        |(Real.log (sixVertexBetheLogNumerator c x) -
            Real.log (sixVertexBetheLogNumerator c y)) -
          (Real.log (sixVertexBetheLogDenominator x + epsilon) -
            Real.log (sixVertexBetheLogDenominator y + epsilon))| := by
        rw [← abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 2),
          ← abs_mul]
        congr 1
        ring
    _ <= (1 / 2 : Real) *
        (|Real.log (sixVertexBetheLogNumerator c x) -
            Real.log (sixVertexBetheLogNumerator c y)| +
          |Real.log (sixVertexBetheLogDenominator x + epsilon) -
            Real.log (sixVertexBetheLogDenominator y + epsilon)|) := by
        gcongr
        exact abs_sub _ _
    _ <= (1 / 2 : Real) *
        ((((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2) * |x - y|) +
          ((2 / epsilon) * |x - y|)) := by gcongr
    _ = A * |x - y| := by dsimp [A]; ring

theorem exists_lipschitzWith_sixVertexRegularizedBetheLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    ∃ C : NNReal,
      LipschitzWith C (sixVertexRegularizedBetheLogKernel c epsilon) :=
  ⟨sixVertexRegularizedBetheLogLipschitzConstant c epsilon,
    lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon⟩

theorem continuous_sixVertexRegularizedBetheLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    Continuous (sixVertexRegularizedBetheLogKernel c epsilon) := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon
  exact hC.continuous

theorem periodic_sixVertexRegularizedBetheLogKernel
    (c epsilon : Real) :
    Function.Periodic (sixVertexRegularizedBetheLogKernel c epsilon)
      (2 * Real.pi) := by
  intro x
  unfold sixVertexRegularizedBetheLogKernel sixVertexBetheLogNumerator
    sixVertexBetheLogDenominator
  rw [Real.cos_add_two_pi]

theorem even_sixVertexRegularizedBetheLogKernel
    (c epsilon : Real) :
    Function.Even (sixVertexRegularizedBetheLogKernel c epsilon) := by
  intro x
  unfold sixVertexRegularizedBetheLogKernel sixVertexBetheLogNumerator
    sixVertexBetheLogDenominator
  rw [Real.cos_neg]



theorem sixVertexCanonicalDensityPerronEmpiricalRegularized_eq_positiveHalf
    {c : Real} (hc : 2 < c) (epsilon : Real) (k : Nat) :
    sixVertexCanonicalDensityPerronEmpiricalObservable hc
        (sixVertexRegularizedBetheLogKernel c epsilon) k =
      (2 * ∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j)) /
        (sixVertexFourWidth 0 k : Real) := by
  let p := sixVertexCanonicalDensityPerronBetheRoots hc k
  let q := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k
  have hlift : sixVertexEvenSymmetricLift (k + 1) q = p := by
    exact sixVertexEvenSymmetricLift_projection (k + 1)
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k).2.1
  unfold sixVertexCanonicalDensityPerronEmpiricalObservable
  change (∑ j, sixVertexRegularizedBetheLogKernel c epsilon (p j)) /
      (sixVertexFourWidth 0 k : Real) =
    (2 * ∑ j, sixVertexRegularizedBetheLogKernel c epsilon (q j)) /
      (sixVertexFourWidth 0 k : Real)
  rw [← hlift, Fin.sum_univ_add]
  apply congrArg (fun z : Real => z / (sixVertexFourWidth 0 k : Real))
  have hneg :
      (∑ j : Fin (k + 1), sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift (k + 1) q
          (Fin.castAdd (k + 1) j))) =
      ∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon (q j) := by
    rw [show (∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexEvenSymmetricLift (k + 1) q
            (Fin.castAdd (k + 1) j))) =
        ∑ j : Fin (k + 1),
          sixVertexRegularizedBetheLogKernel c epsilon (q j.rev) by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sixVertexEvenSymmetricLift_castAdd]
      exact even_sixVertexRegularizedBetheLogKernel c epsilon (q j.rev)]
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun j : Fin (k + 1) =>
        sixVertexRegularizedBetheLogKernel c epsilon (q j)))
  have hpos :
      (∑ j : Fin (k + 1), sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift (k + 1) q
          (Fin.natAdd (k + 1) j))) =
      ∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon (q j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sixVertexEvenSymmetricLift_natAdd]
  rw [hneg, hpos]
  ring

theorem sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator
    {c p : Real} (hc : 2 < c) (hp : sixVertexBethePhase p ≠ 1) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ =
      (1 / 2 : Real) *
        (Real.log (sixVertexBetheLogNumerator c p) -
          Real.log (sixVertexBetheLogDenominator p)) := by
  have hden : 0 < sixVertexBetheLogDenominator p := by
    have hratio := sixVertexBetheM_phase_normSq c p hp
    have hratioPos : 0 <
        sixVertexBetheLogNumerator c p /
          sixVertexBetheLogDenominator p := by
      unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
      rw [← hratio]
      exact Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · linarith [sixVertexBetheLogNumerator_pos hc p]
  rw [sixVertexBetheM_phase_log_norm c p hp]
  have hnum' : 0 < (c ^ 2 - 1) ^ 2 + 1 +
      2 * (c ^ 2 - 1) * Real.cos p := by
    simpa only [sixVertexBetheLogNumerator] using
      sixVertexBetheLogNumerator_pos hc p
  have hden' : 0 < 2 - 2 * Real.cos p := by
    simpa only [sixVertexBetheLogDenominator] using hden
  unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
  rw [Real.log_div hnum'.ne' hden'.ne']



theorem sixVertexRegularizedBetheLogKernel_error_bounds
    {c p epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hp : sixVertexBethePhase p ≠ 1) :
    0 <= Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ -
        sixVertexRegularizedBetheLogKernel c epsilon p ∧
      Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ -
          sixVertexRegularizedBetheLogKernel c epsilon p <=
        epsilon / (2 * sixVertexBetheLogDenominator p) := by
  have hden : 0 < sixVertexBetheLogDenominator p := by
    have hratio := sixVertexBetheM_phase_normSq c p hp
    have hratioPos : 0 <
        sixVertexBetheLogNumerator c p /
          sixVertexBetheLogDenominator p := by
      unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
      rw [← hratio]
      exact Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · linarith [sixVertexBetheLogNumerator_pos hc p]
  have hdeneps : 0 < sixVertexBetheLogDenominator p + epsilon :=
    add_pos hden hepsilon
  rw [sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator hc hp]
  unfold sixVertexRegularizedBetheLogKernel
  have herr :
      (1 / 2 : Real) *
          (Real.log (sixVertexBetheLogNumerator c p) -
            Real.log (sixVertexBetheLogDenominator p)) -
        (1 / 2 : Real) *
          (Real.log (sixVertexBetheLogNumerator c p) -
            Real.log (sixVertexBetheLogDenominator p + epsilon)) =
      (1 / 2 : Real) * Real.log
        ((sixVertexBetheLogDenominator p + epsilon) /
          sixVertexBetheLogDenominator p) := by
    rw [Real.log_div hdeneps.ne' hden.ne']
    ring
  rw [herr]
  constructor
  · apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    rw [le_div_iff₀ hden]
    linarith
  · have hlog := Real.log_le_sub_one_of_pos
      (div_pos hdeneps hden)
    have hrewrite :
        (sixVertexBetheLogDenominator p + epsilon) /
            sixVertexBetheLogDenominator p - 1 =
          epsilon / sixVertexBetheLogDenominator p := by
      field_simp [hden.ne'] <;> ring
    rw [hrewrite] at hlog
    calc
      (1 / 2 : Real) * Real.log
          ((sixVertexBetheLogDenominator p + epsilon) /
            sixVertexBetheLogDenominator p) <=
        (1 / 2 : Real) *
          (epsilon / sixVertexBetheLogDenominator p) := by gcongr
      _ = epsilon / (2 * sixVertexBetheLogDenominator p) := by ring

theorem sixVertexRegularizedBetheLogKernel_nonneg
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4) (p : Real) :
    0 <= sixVertexRegularizedBetheLogKernel c epsilon p := by
  have hnumPos := sixVertexBetheLogNumerator_pos hc p
  have hdenNonneg := sixVertexBetheLogDenominator_nonneg p
  have hdenLe : sixVertexBetheLogDenominator p <= 4 := by
    unfold sixVertexBetheLogDenominator
    linarith [Real.neg_one_le_cos p]
  have hdeneps : 0 < sixVertexBetheLogDenominator p + epsilon :=
    add_pos_of_nonneg_of_pos hdenNonneg hepsilon
  have hle : sixVertexBetheLogDenominator p + epsilon <=
      sixVertexBetheLogNumerator c p := by
    have hnumLower := sixVertexBetheLogNumerator_lower hc p
    linarith
  unfold sixVertexRegularizedBetheLogKernel
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr (Real.log_le_log hdeneps hle))



theorem sixVertexCanonicalDensityPerronLogDenominator_quantile_lower
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    4 * (2 * (j : Real) + 1) ^ 2 <=
      (sixVertexFourWidth 0 k : Real) ^ 2 *
        sixVertexBetheLogDenominator
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) := by
  let p := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  have hp := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).1
  have hpPi := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hs : 0 < s := by dsimp [s]; positivity
  have habsp : |p| <= Real.pi := by
    rw [abs_of_pos hp]
    exact hpPi.le
  have hcos := Real.cos_le_one_sub_mul_cos_sq habsp
  have hdenP : 4 * p ^ 2 <= Real.pi ^ 2 *
      sixVertexBetheLogDenominator p := by
    have hcos' := mul_le_mul_of_nonneg_left hcos (sq_nonneg Real.pi)
    field_simp [Real.pi_ne_zero] at hcos'
    unfold sixVertexBetheLogDenominator
    nlinarith
  have hquant :=
    sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc k j
  change Real.pi * s < N * p at hquant
  have hquantSq : Real.pi ^ 2 * s ^ 2 <= N ^ 2 * p ^ 2 := by
    have hleft : 0 <= Real.pi * s := by positivity
    have hright : 0 <= N * p := by positivity
    nlinarith [(sq_le_sq₀ hleft hright).2 hquant.le]
  have hNnonneg : 0 <= N ^ 2 := sq_nonneg N
  have h1 := mul_le_mul_of_nonneg_left hdenP hNnonneg
  have h2 := mul_le_mul_of_nonneg_left hquantSq
    (by norm_num : (0 : Real) <= 4)
  change 4 * s ^ 2 <= N ^ 2 * sixVertexBetheLogDenominator p
  nlinarith [sq_pos_of_pos Real.pi_pos]


theorem sum_Ico_inv_odd_sq_le_inv (J K : Nat) (hJ : 0 < J) :
    (∑ j ∈ Finset.Ico J K,
      (1 : Real) / (2 * (j : Real) + 1) ^ 2) <=
        1 / (J : Real) := by
  by_cases hJK : J <= K
  · calc
      _ <= ∑ j ∈ Finset.Ico J K,
          ((1 : Real) / (j : Real) -
            1 / ((j + 1 : Nat) : Real)) := by
        apply Finset.sum_le_sum
        intro j hjmem
        have hjNat : J <= j := (Finset.mem_Ico.mp hjmem).1
        have hj : (0 : Real) < j := by
          exact_mod_cast hJ.trans_le hjNat
        have hprod : (0 : Real) <
            (j : Real) * ((j + 1 : Nat) : Real) := by positivity
        have hden : (j : Real) * ((j + 1 : Nat) : Real) <=
            (2 * (j : Real) + 1) ^ 2 := by
          push_cast
          nlinarith [sq_nonneg (j : Real)]
        calc
          (1 : Real) / (2 * (j : Real) + 1) ^ 2 <=
              1 / ((j : Real) * ((j + 1 : Nat) : Real)) :=
            one_div_le_one_div_of_le hprod hden
          _ = 1 / (j : Real) - 1 / ((j + 1 : Nat) : Real) := by
            push_cast
            field_simp [hj.ne']
            ring
      _ = 1 / (J : Real) - 1 / (K : Real) := by
        rw [Finset.sum_Ico_eq_sub _ hJK,
          Finset.sum_range_sub'
            (fun j : Nat => (1 : Real) / (j : Real)),
          Finset.sum_range_sub'
            (fun j : Nat => (1 : Real) / (j : Real))]
        ring
      _ <= 1 / (J : Real) := sub_le_self _ (by positivity)
  · rw [Finset.Ico_eq_empty (fun hlt => hJK hlt.le)]
    simp

theorem sixVertexCanonicalDensityPerronRootAverage_sub_regularized_eq
    {c : Real} (hc : 2 < c) (epsilon : Real) (k : Nat) :
    sixVertexSymmetricBetheRootAverage c
        (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
      sixVertexCanonicalDensityPerronEmpiricalObservable hc
        (sixVertexRegularizedBetheLogKernel c epsilon) k =
      (2 * ∑ j : Fin (k + 1),
        (Real.log ‖sixVertexBetheM c (sixVertexBethePhase
            (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))) /
        (sixVertexFourWidth 0 k : Real) := by
  rw [sixVertexCanonicalDensityPerronEmpiricalRegularized_eq_positiveHalf]
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexCanonicalDensityPerronPositiveHalfRootFamily
  rw [Finset.sum_sub_distrib]
  ring

theorem sixVertexCanonicalDensityPerronRegularized_pointwise_error_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (k : Nat) (j : Fin (k + 1)) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
      sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) <=
      epsilon * (sixVertexFourWidth 0 k : Real) ^ 2 /
        (8 * (2 * (j : Real) + 1) ^ 2) := by
  let p := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  have hphase : sixVertexBethePhase p ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (Fin.natAdd (k + 1) j)
  have herror :=
    (sixVertexRegularizedBetheLogKernel_error_bounds hc hepsilon hphase).2
  have hden : 0 < sixVertexBetheLogDenominator p := by
    have hratio := sixVertexBetheM_phase_normSq c p hphase
    have hratioPos : 0 < sixVertexBetheLogNumerator c p /
        sixVertexBetheLogDenominator p := by
      unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
      rw [← hratio]
      exact Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · linarith [sixVertexBetheLogNumerator_pos hc p]
  have hs : 0 < s := by dsimp [s]; positivity
  have hquant :=
    sixVertexCanonicalDensityPerronLogDenominator_quantile_lower hc k j
  change 4 * s ^ 2 <= N ^ 2 * sixVertexBetheLogDenominator p at hquant
  have hinv : 1 / sixVertexBetheLogDenominator p <=
      N ^ 2 / (4 * s ^ 2) := by
    field_simp [hden.ne', hs.ne']
    nlinarith
  change Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ -
      sixVertexRegularizedBetheLogKernel c epsilon p <=
    epsilon * N ^ 2 / (8 * s ^ 2)
  calc
    _ <= epsilon / (2 * sixVertexBetheLogDenominator p) := herror
    _ = (epsilon / 2) *
        (1 / sixVertexBetheLogDenominator p) := by ring
    _ <= (epsilon / 2) * (N ^ 2 / (4 * s ^ 2)) := by
      gcongr
    _ = epsilon * N ^ 2 / (8 * s ^ 2) := by ring

theorem sixVertexCanonicalDensityPerronRegularized_tail_error_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    {J : Nat} (hJ : 0 < J) (k : Nat) :
    (2 * ∑ j : Fin (k + 1) with J <= j.val,
      (Real.log ‖sixVertexBetheM c (sixVertexBethePhase
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))) /
        (sixVertexFourWidth 0 k : Real) <=
      epsilon * (sixVertexFourWidth 0 k : Real) / (4 * (J : Real)) := by
  let N : Real := sixVertexFourWidth 0 k
  let d : Fin (k + 1) -> Real := fun j =>
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
      sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j)
  let w : Nat -> Real := fun j => (1 : Real) / (2 * (j : Real) + 1) ^ 2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hindex :
      (∑ j : Fin (k + 1) with J <= j.val, w j.val) =
        ∑ i ∈ Finset.Ico J (k + 1), w i := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_Ico.mpr
        ⟨(Finset.mem_filter.mp hj).2, j.isLt⟩
    · intro a ha b hb hab
      exact Fin.ext hab
    · intro i hi
      have hi' := Finset.mem_Ico.mp hi
      let j : Fin (k + 1) := ⟨i, hi'.2⟩
      refine ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.1⟩
    · intro j hj
      rfl
  have hsum : (∑ j : Fin (k + 1) with J <= j.val, d j) <=
      (epsilon * N ^ 2 / 8) * (1 / (J : Real)) := by
    calc
      _ <= ∑ j : Fin (k + 1) with J <= j.val,
          (epsilon * N ^ 2 / 8) * w j.val := by
        apply Finset.sum_le_sum
        intro j hj
        have hpoint :=
          sixVertexCanonicalDensityPerronRegularized_pointwise_error_le
            hc hepsilon k j
        dsimp [d, w, N]
        calc
          _ <= epsilon * (sixVertexFourWidth 0 k : Real) ^ 2 /
              (8 * (2 * (j : Real) + 1) ^ 2) := hpoint
          _ = (epsilon * (sixVertexFourWidth 0 k : Real) ^ 2 / 8) *
              (1 / (2 * (j : Real) + 1) ^ 2) := by
            have hs : (0 : Real) < 2 * (j : Real) + 1 := by positivity
            field_simp [hs.ne']
      _ = (epsilon * N ^ 2 / 8) *
          (∑ j : Fin (k + 1) with J <= j.val, w j.val) := by
        rw [Finset.mul_sum]
      _ = (epsilon * N ^ 2 / 8) *
          (∑ i ∈ Finset.Ico J (k + 1), w i) := by rw [hindex]
      _ <= (epsilon * N ^ 2 / 8) * (1 / (J : Real)) := by
        gcongr
        exact sum_Ico_inv_odd_sq_le_inv J (k + 1) hJ
  change (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N <=
    epsilon * N / (4 * (J : Real))
  calc
    (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N <=
        (2 * ((epsilon * N ^ 2 / 8) * (1 / (J : Real)))) / N := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num)) hN.le
    _ = epsilon * N / (4 * (J : Real)) := by
      have hJreal : (0 : Real) < J := by exact_mod_cast hJ
      field_simp [hN.ne', hJreal.ne']
      ring



theorem sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4)
    {J : Nat} (hJ : 0 < J) (k : Nat) :
    0 <= sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c epsilon) k ∧
      sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c epsilon) k <=
        sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
          epsilon * (sixVertexFourWidth 0 k : Real) / (4 * (J : Real)) := by
  let N : Real := sixVertexFourWidth 0 k
  let raw : Fin (k + 1) -> Real := fun j =>
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖
  let reg : Fin (k + 1) -> Real := fun j =>
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j)
  let d : Fin (k + 1) -> Real := fun j => raw j - reg j
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hphase (j : Fin (k + 1)) :
      sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (Fin.natAdd (k + 1) j)
  have hdNonneg (j : Fin (k + 1)) : 0 <= d j := by
    exact (sixVertexRegularizedBetheLogKernel_error_bounds hc hepsilon
      (hphase j)).1
  have hregNonneg (j : Fin (k + 1)) : 0 <= reg j := by
    exact sixVertexRegularizedBetheLogKernel_nonneg hc hepsilon
      hepsilonUpper _
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (k + 1))) (fun j => j.val < J) d
  simp only [not_lt] at hsplit
  have hedge : (∑ j : Fin (k + 1) with j.val < J, d j) <=
      ∑ j : Fin (k + 1) with j.val < J, raw j := by
    apply Finset.sum_le_sum
    intro j hj
    dsimp [d]
    linarith [hregNonneg j]
  have hedgeScaled :
      (2 * ∑ j : Fin (k + 1) with j.val < J, d j) / N <=
        sixVertexCanonicalDensityPerronInitialLogContribution hc J k := by
    unfold sixVertexCanonicalDensityPerronInitialLogContribution
    change (2 * ∑ j : Fin (k + 1) with j.val < J, d j) / N <=
      (2 * ∑ j : Fin (k + 1) with j.val < J, raw j) / N
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hedge (by norm_num)) hN.le
  have htail :=
    sixVertexCanonicalDensityPerronRegularized_tail_error_le
      hc hepsilon hJ k
  change (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N <=
    epsilon * N / (4 * (J : Real)) at htail
  rw [sixVertexCanonicalDensityPerronRootAverage_sub_regularized_eq]
  change 0 <= (2 * ∑ j, d j) / N ∧
    (2 * ∑ j, d j) / N <=
      sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
        epsilon * N / (4 * (J : Real))
  constructor
  · apply div_nonneg
    · exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg (fun j _ => hdNonneg j))
    · exact hN.le
  · calc
      (2 * ∑ j, d j) / N =
          (2 * ∑ j : Fin (k + 1) with j.val < J, d j) / N +
            (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N := by
        rw [← hsplit]
        ring
      _ <= sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
          epsilon * N / (4 * (J : Real)) := add_le_add hedgeScaled htail


def sixVertexCanonicalLinearEdgeCutoff (eta : Real) (k : Nat) : Nat :=
  Nat.ceil (eta * (sixVertexFourWidth 0 k : Real))

theorem sixVertexCanonicalLinearEdgeCutoff_pos
    {eta : Real} (heta : 0 < eta) (k : Nat) :
    0 < sixVertexCanonicalLinearEdgeCutoff eta k := by
  rw [sixVertexCanonicalLinearEdgeCutoff, Nat.ceil_pos]
  exact mul_pos heta (by
    exact_mod_cast sixVertexFourWidth_pos 0 k)

theorem sixVertexCanonicalLinearEdgeCutoff_le
    {eta : Real} (heta : eta <= 1 / 4) (k : Nat) :
    sixVertexCanonicalLinearEdgeCutoff eta k <= k + 1 := by
  rw [sixVertexCanonicalLinearEdgeCutoff, Nat.ceil_le]
  rw [sixVertexFourWidth]
  push_cast
  have hk : (0 : Real) <= (k : Real) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right heta hk]

theorem tendsto_sixVertexCanonicalLinearEdgeCutoff_ratio
    {eta : Real} (heta : 0 <= eta) :
    Tendsto (fun k : Nat =>
      (sixVertexCanonicalLinearEdgeCutoff eta k : Real) /
        (sixVertexFourWidth 0 k : Real)) atTop (nhds eta) := by
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hwidthReal : Tendsto (fun k =>
      (sixVertexFourWidth 0 k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidth
  have hinv : Tendsto (fun k =>
      (1 : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) :=
    hwidthReal.const_div_atTop 1
  have hupper : Tendsto (fun k => eta +
      (1 : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds eta) := by
    simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : Nat => eta) atTop (nhds eta) from
      tendsto_const_nhds) hupper
  · filter_upwards [] with k
    have hN : (0 : Real) < sixVertexFourWidth 0 k := by
      exact_mod_cast sixVertexFourWidth_pos 0 k
    rw [le_div_iff₀ hN]
    exact Nat.le_ceil
      (eta * (sixVertexFourWidth 0 k : Real))
  · filter_upwards [] with k
    have hN : (0 : Real) < sixVertexFourWidth 0 k := by
      exact_mod_cast sixVertexFourWidth_pos 0 k
    rw [div_le_iff₀ hN]
    have hceil := Nat.ceil_lt_add_one
      (mul_nonneg heta hN.le : 0 <=
        eta * (sixVertexFourWidth 0 k : Real))
    change (sixVertexCanonicalLinearEdgeCutoff eta k : Real) <=
      (eta + 1 / (sixVertexFourWidth 0 k : Real)) *
        (sixVertexFourWidth 0 k : Real)
    rw [sixVertexCanonicalLinearEdgeCutoff]
    field_simp [hN.ne']
    linarith

def sixVertexCanonicalRegularizationEnvelope
    (c epsilon eta : Real) : Real :=
  2 * eta * (Real.log (c ^ 2 / (2 * eta)) + 1) +
    epsilon / (4 * eta)

def sixVertexCanonicalRegularizationUpper
    (c epsilon eta : Real) (k : Nat) : Real :=
  let x := (sixVertexCanonicalLinearEdgeCutoff eta k : Real) /
    (sixVertexFourWidth 0 k : Real)
  2 * x * (Real.log (c ^ 2 / (2 * x)) + 1) +
    epsilon / (4 * x)

theorem tendsto_sixVertexCanonicalRegularizationUpper
    {c epsilon eta : Real} (hc0 : c ≠ 0) (heta : 0 < eta) :
    Tendsto (sixVertexCanonicalRegularizationUpper c epsilon eta)
      atTop (nhds (sixVertexCanonicalRegularizationEnvelope c epsilon eta)) := by
  let x : Nat -> Real := fun k =>
    (sixVertexCanonicalLinearEdgeCutoff eta k : Real) /
      (sixVertexFourWidth 0 k : Real)
  have hx : Tendsto x atTop (nhds eta) :=
    tendsto_sixVertexCanonicalLinearEdgeCutoff_ratio heta.le
  have htwo : Tendsto (fun k => 2 * x k) atTop (nhds (2 * eta)) :=
    hx.const_mul 2
  have hratio : Tendsto (fun k => c ^ 2 / (2 * x k)) atTop
      (nhds (c ^ 2 / (2 * eta))) :=
    tendsto_const_nhds.div htwo (by positivity)
  have hlog : Tendsto (fun k => Real.log (c ^ 2 / (2 * x k))) atTop
      (nhds (Real.log (c ^ 2 / (2 * eta)))) :=
    hratio.log (div_ne_zero (pow_ne_zero 2 hc0)
      (by positivity))
  have hfirst : Tendsto (fun k =>
      2 * x k * (Real.log (c ^ 2 / (2 * x k)) + 1)) atTop
      (nhds (2 * eta * (Real.log (c ^ 2 / (2 * eta)) + 1))) :=
    htwo.mul (hlog.add tendsto_const_nhds)
  have hfour : Tendsto (fun k => 4 * x k) atTop (nhds (4 * eta)) :=
    hx.const_mul 4
  have hsecond : Tendsto (fun k => epsilon / (4 * x k)) atTop
      (nhds (epsilon / (4 * eta))) :=
    tendsto_const_nhds.div hfour (by positivity)
  simpa only [sixVertexCanonicalRegularizationUpper,
    sixVertexCanonicalRegularizationEnvelope, x] using hfirst.add hsecond

theorem sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper
    {c epsilon eta : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4)
    (heta : 0 < eta) (hetaUpper : eta <= 1 / 4) (k : Nat) :
    sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c epsilon) k <=
      sixVertexCanonicalRegularizationUpper c epsilon eta k := by
  let J := sixVertexCanonicalLinearEdgeCutoff eta k
  let N : Real := sixVertexFourWidth 0 k
  let x : Real := (J : Real) / N
  have hJ : 0 < J := sixVertexCanonicalLinearEdgeCutoff_pos heta k
  have hJle : J <= k + 1 :=
    sixVertexCanonicalLinearEdgeCutoff_le hetaUpper k
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hJreal : (0 : Real) < J := by exact_mod_cast hJ
  have hx : 0 < x := div_pos hJreal hN
  have hmaster :=
    (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc hepsilon hepsilonUpper hJ k).2
  have hinitial :=
    sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling
      hc hJ hJle
  have hratio : c ^ 2 * N / (2 * (J : Real)) = c ^ 2 / (2 * x) := by
    dsimp [x]
    field_simp [hN.ne', hJreal.ne']
  calc
    _ <= sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
        epsilon * N / (4 * (J : Real)) := hmaster
    _ <= (2 * (J : Real) *
          (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N +
        epsilon * N / (4 * (J : Real)) := by gcongr
    _ = sixVertexCanonicalRegularizationUpper c epsilon eta k := by
      rw [hratio]
      unfold sixVertexCanonicalRegularizationUpper
      change _ = 2 * x * (Real.log (c ^ 2 / (2 * x)) + 1) +
        epsilon / (4 * x)
      dsimp [x]
      field_simp [hN.ne', hJreal.ne', hx.ne']

def sixVertexCanonicalRegularizationDiagonalEnvelope
    (c eta : Real) : Real :=
  sixVertexCanonicalRegularizationEnvelope c (eta ^ 2) eta

theorem tendsto_sixVertexCanonicalRegularizationDiagonalEnvelope
    {c : Real} (hc0 : c ≠ 0) :
    Tendsto (sixVertexCanonicalRegularizationDiagonalEnvelope c)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let C : Real := Real.log (c ^ 2 / 2) + 1
  have hid : Tendsto (fun eta : Real => eta)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hetalog : Tendsto (fun eta : Real => eta * Real.log eta)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    by
      have hfull : Tendsto (fun eta : Real => eta * Real.log eta)
          (nhds (0 : Real)) (nhds ((0 : Real) * Real.log 0)) :=
        Real.continuous_mul_log.continuousAt.tendsto
      simpa using hfull.mono_left inf_le_left
  have hmain : Tendsto (fun eta : Real =>
      2 * eta * (C - Real.log eta) + eta / 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hlinear := hid.const_mul (2 * C)
    have hlog := hetalog.const_mul 2
    have hsmall := hid.const_mul (1 / 4 : Real)
    convert (hlinear.sub hlog).add hsmall using 1
    · funext eta
      ring
    · norm_num
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  have hetaPos : 0 < eta := heta
  have hconst : c ^ 2 / 2 ≠ 0 := by positivity
  unfold sixVertexCanonicalRegularizationDiagonalEnvelope
    sixVertexCanonicalRegularizationEnvelope
  rw [show c ^ 2 / (2 * eta) = (c ^ 2 / 2) / eta by ring,
    Real.log_div hconst hetaPos.ne']
  dsimp [C]
  field_simp [hetaPos.ne']
  ring



theorem eventually_exists_sixVertexCanonicalRegularizedApproximation
    {c : Real} (hc : 2 < c) {delta : Real} (hdelta : 0 < delta) :
    ∃ eta : Real, 0 < eta ∧ eta <= 1 / 4 ∧
      eta ^ 2 <= (c ^ 2 - 2) ^ 2 - 4 ∧
      ∀ᶠ k : Nat in atTop,
        sixVertexSymmetricBetheRootAverage c
            (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
          sixVertexCanonicalDensityPerronEmpiricalObservable hc
            (sixVertexRegularizedBetheLogKernel c (eta ^ 2)) k < delta := by
  let D : Real := (c ^ 2 - 2) ^ 2 - 4
  have hc2 : 2 < c ^ 2 - 2 := by
    nlinarith [sq_nonneg (c - 2)]
  have hD : 0 < D := by dsimp [D]; nlinarith
  let a : Real := min (1 / 4) (min 1 D)
  have ha : 0 < a := by dsimp [a]; positivity
  have henv : ∀ᶠ eta : Real in nhdsWithin 0 (Set.Ioi 0),
      sixVertexCanonicalRegularizationDiagonalEnvelope c eta < delta :=
    (tendsto_sixVertexCanonicalRegularizationDiagonalEnvelope
      (by linarith : c ≠ 0)).eventually (Iio_mem_nhds hdelta)
  have hrange : Set.Ioo (0 : Real) a ∈ nhdsWithin 0 (Set.Ioi 0) :=
    Ioo_mem_nhdsGT ha
  obtain ⟨eta, hetaEnv, hetaRange⟩ :=
    Set.nonempty_def.mp (Filter.nonempty_of_mem (inter_mem henv hrange))
  have heta : 0 < eta := hetaRange.1
  have hetaQuarter : eta <= 1 / 4 :=
    hetaRange.2.le.trans (min_le_left _ _)
  have hetaOne : eta <= 1 :=
    hetaRange.2.le.trans (min_le_right _ _ |>.trans (min_le_left _ _))
  have hetaD : eta <= D :=
    hetaRange.2.le.trans (min_le_right _ _ |>.trans (min_le_right _ _))
  have hetaSq : eta ^ 2 <= D := by
    have : eta ^ 2 <= eta := by nlinarith
    exact this.trans hetaD
  refine ⟨eta, heta, hetaQuarter, by simpa only [D] using hetaSq, ?_⟩
  have hupper := tendsto_sixVertexCanonicalRegularizationUpper
    (c := c) (epsilon := eta ^ 2) (by linarith : c ≠ 0) heta
  have hupperEventually : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalRegularizationUpper c (eta ^ 2) eta k < delta :=
    hupper.eventually (Iio_mem_nhds hetaEnv)
  filter_upwards [hupperEventually] with k hk
  exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper
    hc (sq_pos_of_pos heta) (by simpa only [D] using hetaSq)
    heta hetaQuarter k).trans_lt hk


theorem tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc
      (sixVertexRegularizedBetheLogKernel c epsilon)) atTop
      (nhds (∫ y in -Real.pi..Real.pi,
        sixVertexRegularizedBetheLogKernel c epsilon y *
          sixVertexFourierPhysicalDensity c hc y)) := by
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  have hf : Continuous f :=
    continuous_sixVertexRegularizedBetheLogKernel hc hepsilon
  obtain ⟨C, hC⟩ :=
    exists_lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon
  let B : Real := |f 0| + (C : Real) * Real.pi
  have hbound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B := by
    intro x hx
    have hdist : |f x - f 0| <= (C : Real) * |x| := by
      simpa only [Real.norm_eq_abs, sub_zero] using hC.norm_sub_le x 0
    have hxabs : |x| <= Real.pi := abs_le.mpr hx
    calc
      |f x| = |(f x - f 0) + f 0| := by ring_nf
      _ <= |f x - f 0| + |f 0| := abs_add_le _ _
      _ <= (C : Real) * |x| + |f 0| := by linarith
      _ <= (C : Real) * Real.pi + |f 0| := by
        gcongr
      _ = B := by dsimp [B]; ring
  have hBnonneg : 0 <= B := by
    dsimp [B]
    positivity
  exact tendsto_sixVertexCanonicalDensityPerronEmpiricalObservable hc
    hf hC (periodic_sixVertexRegularizedBetheLogKernel c epsilon)
    hBnonneg hbound



theorem cauchySeq_sixVertexCanonicalDensityPerronRootAverage
    {c : Real} (hc : 2 < c) :
    CauchySeq (sixVertexSymmetricBetheRootAverage c
      (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) := by
  rw [Metric.cauchySeq_iff]
  intro delta hdelta
  obtain ⟨eta, heta, hetaQuarter, hetaSq, happ⟩ :=
    eventually_exists_sixVertexCanonicalRegularizedApproximation hc
      (delta := delta / 3) (by positivity)
  let raw : Nat -> Real := sixVertexSymmetricBetheRootAverage c
    (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)
  let reg : Nat -> Real :=
    sixVertexCanonicalDensityPerronEmpiricalObservable hc
      (sixVertexRegularizedBetheLogKernel c (eta ^ 2))
  have hregT : Tendsto reg atTop (nhds (∫ y in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogKernel c (eta ^ 2) y *
        sixVertexFourierPhysicalDensity c hc y)) :=
    tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel hc
      (sq_pos_of_pos heta)
  have hregC : CauchySeq reg := hregT.cauchySeq
  rw [Metric.cauchySeq_iff] at hregC
  obtain ⟨Nreg, hNreg⟩ := hregC (delta / 3) (by positivity)
  obtain ⟨Napp, hNapp⟩ := eventually_atTop.1 happ
  refine ⟨max Nreg Napp, ?_⟩
  intro m hm n hn
  have hmReg : Nreg <= m := (le_max_left _ _).trans hm
  have hnReg : Nreg <= n := (le_max_left _ _).trans hn
  have hmApp : Napp <= m := (le_max_right _ _).trans hm
  have hnApp : Napp <= n := (le_max_right _ _).trans hn
  have hmClose : raw m - reg m < delta / 3 := hNapp m hmApp
  have hnClose : raw n - reg n < delta / 3 := hNapp n hnApp
  have hmNonneg : 0 <= raw m - reg m := by
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc (sq_pos_of_pos heta) hetaSq
      (sixVertexCanonicalLinearEdgeCutoff_pos heta m) m).1
  have hnNonneg : 0 <= raw n - reg n := by
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc (sq_pos_of_pos heta) hetaSq
      (sixVertexCanonicalLinearEdgeCutoff_pos heta n) n).1
  have hregClose : dist (reg m) (reg n) < delta / 3 :=
    hNreg m hmReg n hnReg
  have hmDist : dist (raw m) (reg m) < delta / 3 := by
    rw [Real.dist_eq, abs_of_nonneg hmNonneg]
    exact hmClose
  have hnDist : dist (reg n) (raw n) < delta / 3 := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hnNonneg]
    exact hnClose
  calc
    dist (raw m) (raw n) <=
        dist (raw m) (reg m) + dist (reg m) (raw n) := dist_triangle _ _ _
    _ <= dist (raw m) (reg m) +
        (dist (reg m) (reg n) + dist (reg n) (raw n)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < delta := by linarith



theorem exists_sixVertexCanonicalDensityPerronRootAverage_limit
    {c : Real} (hc : 2 < c) :
    ∃ a : Real, Tendsto (sixVertexSymmetricBetheRootAverage c
      (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc))
        atTop (nhds a) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_sixVertexCanonicalDensityPerronRootAverage hc)

noncomputable def sixVertexCanonicalDensityPerronRootAverageLimit
    {c : Real} (hc : 2 < c) : Real :=
  Classical.choose (exists_sixVertexCanonicalDensityPerronRootAverage_limit hc)

theorem tendsto_sixVertexCanonicalDensityPerronRootAverage
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexSymmetricBetheRootAverage c
      (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc))
        atTop (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) :=
  Classical.choose_spec
    (exists_sixVertexCanonicalDensityPerronRootAverage_limit hc)



theorem abs_sixVertexCanonicalDensityPerronRootAverageLimit_sub_regularizedIntegral_le
    {c eta : Real} (hc : 2 < c) (heta : 0 < eta)
    (hetaQuarter : eta <= 1 / 4)
    (hetaSq : eta ^ 2 <= (c ^ 2 - 2) ^ 2 - 4) :
    |sixVertexCanonicalDensityPerronRootAverageLimit hc -
        ∫ y in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogKernel c (eta ^ 2) y *
            sixVertexFourierPhysicalDensity c hc y| <=
      sixVertexCanonicalRegularizationDiagonalEnvelope c eta := by
  let raw : Nat -> Real := sixVertexSymmetricBetheRootAverage c
    (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)
  let reg : Nat -> Real :=
    sixVertexCanonicalDensityPerronEmpiricalObservable hc
      (sixVertexRegularizedBetheLogKernel c (eta ^ 2))
  let I : Real := ∫ y in -Real.pi..Real.pi,
    sixVertexRegularizedBetheLogKernel c (eta ^ 2) y *
      sixVertexFourierPhysicalDensity c hc y
  let upper : Nat -> Real :=
    sixVertexCanonicalRegularizationUpper c (eta ^ 2) eta
  let E : Real := sixVertexCanonicalRegularizationDiagonalEnvelope c eta
  have hraw : Tendsto raw atTop
      (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) :=
    tendsto_sixVertexCanonicalDensityPerronRootAverage hc
  have hreg : Tendsto reg atTop (nhds I) :=
    tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel hc
      (sq_pos_of_pos heta)
  have hupper : Tendsto upper atTop (nhds E) := by
    exact tendsto_sixVertexCanonicalRegularizationUpper
      (by linarith : c ≠ 0) heta
  have herror : Tendsto (fun k => raw k - reg k) atTop
      (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc - I)) :=
    hraw.sub hreg
  have hnonnegEventually : ∀ᶠ k : Nat in atTop, 0 <= raw k - reg k := by
    filter_upwards [] with k
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc (sq_pos_of_pos heta) hetaSq
      (sixVertexCanonicalLinearEdgeCutoff_pos heta k) k).1
  have hlimitNonneg : 0 <=
      sixVertexCanonicalDensityPerronRootAverageLimit hc - I :=
    ge_of_tendsto herror hnonnegEventually
  have hupperEventually : ∀ᶠ k : Nat in atTop,
      raw k - reg k <= upper k := by
    filter_upwards [] with k
    exact
      sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper
        hc (sq_pos_of_pos heta) hetaSq heta hetaQuarter k
  have hdiffT : Tendsto (fun k => (raw k - reg k) - upper k) atTop
      (nhds ((sixVertexCanonicalDensityPerronRootAverageLimit hc - I) - E)) :=
    herror.sub hupper
  have hlimitUpper :
      sixVertexCanonicalDensityPerronRootAverageLimit hc - I <= E := by
    have hz : (sixVertexCanonicalDensityPerronRootAverageLimit hc - I) - E <=
        0 := le_of_tendsto hdiffT (by
      filter_upwards [hupperEventually] with k hk
      linarith)
    linarith
  change |sixVertexCanonicalDensityPerronRootAverageLimit hc - I| <= E
  rw [abs_of_nonneg hlimitNonneg]
  exact hlimitUpper



theorem tendsto_sixVertexCentralWidthRate_canonicalDensityPerronLimit
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCentralWidthRate c) atTop
      (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) := by
  have hlog : Tendsto (fun k : Nat =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log 2 / 4)).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext k
    simp [sixVertexFourWidth]
    field_simp
  have hroot := tendsto_sixVertexCanonicalDensityPerronRootAverage hc
  have hsum := hlog.add hroot
  have heq : sixVertexCentralWidthRate c =ᶠ[atTop] fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k := by
    filter_upwards
    [eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue hc]
      with k hk
    unfold sixVertexCentralWidthRate
    rw [hk, sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
    unfold sixVertexSymmetricBetheRootAverage
      sixVertexCanonicalDensityPerronPositiveHalfRootFamily
    ring
  simpa only [zero_add] using hsum.congr' heq.symm

end

end StatMech.FrontierD
