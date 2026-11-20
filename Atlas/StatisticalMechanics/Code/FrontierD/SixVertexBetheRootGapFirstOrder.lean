/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Code.FrontierD.SixVertexBethePairedBounds










namespace StatMech.FrontierD

noncomputable section


theorem abs_width_mul_gap_sub_inv_density_le
    {N gap finiteDensity density lower mesh densityError cellError : Real}
    (hN : 0 < N) (hgap : 0 <= gap) (hlower : 0 < lower)
    (hmeshNonneg : 0 <= mesh) (hdensityErrorNonneg : 0 <= densityError)
    (hcellErrorNonneg : 0 <= cellError)
    (hdensity : lower <= density)
    (hmesh : gap <= mesh / N)
    (hdensityError : |finiteDensity - density| <= densityError / N)
    (hcell : |gap * finiteDensity - 1 / N| <= cellError * gap ^ 2) :
    |N * gap - 1 / density| <=
      (cellError * mesh ^ 2 + mesh * densityError) /
        (lower * N) := by
  have hdensityPos : 0 < density := hlower.trans_le hdensity
  have hscaledGap : N * gap <= mesh := by
    simpa [mul_comm] using (le_div_iff₀ hN).mp hmesh
  have hmain : |density * (N * gap - 1 / density)| <=
      (cellError * mesh ^ 2 + mesh * densityError) / N := by
    have hdecomp : density * (N * gap - 1 / density) =
        N * (gap * finiteDensity - 1 / N) +
          N * gap * (density - finiteDensity) := by
      field_simp [hN.ne', hdensityPos.ne']
      ring
    rw [hdecomp]
    calc
      |N * (gap * finiteDensity - 1 / N) +
          N * gap * (density - finiteDensity)| <=
        |N * (gap * finiteDensity - 1 / N)| +
          |N * gap * (density - finiteDensity)| := abs_add_le _ _
      _ <= N * (cellError * gap ^ 2) +
          (N * gap) * (densityError / N) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hN,
          abs_of_nonneg hgap]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hcell hN.le)
          (mul_le_mul_of_nonneg_left (by simpa [abs_sub_comm] using hdensityError)
            (mul_nonneg hN.le hgap))
      _ <= N * (cellError * (mesh / N) ^ 2) +
          mesh * (densityError / N) := by
        gcongr
      _ = (cellError * mesh ^ 2 + mesh * densityError) / N := by
        field_simp [hN.ne']
  rw [abs_mul, abs_of_pos hdensityPos] at hmain
  have hdiv : |N * gap - 1 / density| <=
      ((cellError * mesh ^ 2 + mesh * densityError) / N) / density :=
    (le_div_iff₀ hdensityPos).2 (by simpa [mul_comm] using hmain)
  calc
    |N * gap - 1 / density| <=
        ((cellError * mesh ^ 2 + mesh * densityError) / N) / density := hdiv
    _ = (cellError * mesh ^ 2 + mesh * densityError) / (N * density) := by
      rw [div_div]
    _ <= (cellError * mesh ^ 2 + mesh * densityError) / (lower * N) := by
      have hnumNonneg : 0 <= cellError * mesh ^ 2 + mesh * densityError :=
        add_nonneg (mul_nonneg hcellErrorNonneg (sq_nonneg mesh))
          (mul_nonneg hmeshNonneg hdensityErrorNonneg)
      apply div_le_div_of_nonneg_left hnumNonneg (mul_pos hlower hN)
      nlinarith




theorem abs_width_mul_adjacentBetheGap_sub_inv_density_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : 2 * (n + 1) <= N)
    {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (j : Fin n)
    {rho : Real -> Real} {lower E : Real}
    (hlower : 0 < lower) (hrho : lower <= rho (p j.castSucc))
    (hE : 0 <= E)
    (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (n + 1) p x - rho x)| <=
          E / N) :
    |(N : Real) * (p j.succ - p j.castSucc) - 1 / rho (p j.castSucc)| <=
      ((sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          (1 / sixVertexTailFiniteDensityFloor c) ^ 2 +
        (1 / sixVertexTailFiniteDensityFloor c) *
          (E / ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c))) /
        (lower * N) := by
  let gap := p j.succ - p j.castSucc
  let rhoN := sixVertexFiniteRootDensity c N (n + 1) p (p j.castSucc)
  let rho0 := rho (p j.castSucc)
  let floor := sixVertexTailFiniteDensityFloor c
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hgap : 0 <= gap := sub_nonneg.mpr (hopen.1 (by simp)).le
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hrootIcc : p j.castSucc ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hopen.2.2 j.castSucc).1.le, (hopen.2.2 j.castSucc).2.le⟩
  have hweight : wmin <= sixVertexRootDensityWeight c (p j.castSucc) := by
    exact sixVertexRootDensityWeight_lower hc _
  have hweightPos : 0 < sixVertexRootDensityWeight c (p j.castSucc) :=
    hwmin.trans_le hweight
  have hdensityError : |rhoN - rho0| <= (E / wmin) / N := by
    have hc0 := hclose (p j.castSucc) hrootIcc
    have habs : |sixVertexRootDensityWeight c (p j.castSucc) *
        (rhoN - rho0)| =
        sixVertexRootDensityWeight c (p j.castSucc) * |rhoN - rho0| := by
      rw [abs_mul, abs_of_pos hweightPos]
    rw [habs] at hc0
    have hw : wmin * |rhoN - rho0| <= E / N :=
      (mul_le_mul_of_nonneg_right hweight (abs_nonneg _)).trans hc0
    rw [show (E / wmin) / (N : Real) = (E / N) / wmin by
      field_simp [hwmin.ne', hNreal.ne']]
    exact (le_div_iff₀ hwmin).2 (by simpa [mul_comm] using hw)
  have hmesh : gap <= (1 / floor) / N := by
    have h := sixVertexBetheSolution_adjacentSpacing_upper_tail
      hc htail hN hhalf hopen hsol j
    dsimp [gap, floor]
    calc
      p j.succ - p j.castSucc <=
          1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := h
      _ = (1 / sixVertexTailFiniteDensityFloor c) / N := by
        field_simp [hfloor.ne', hNreal.ne']
  have hcell := abs_gap_mul_finiteRootDensity_sub_inv_width_le
    hc hN (by omega : n + 1 <= N) hopen hsol j
  have hLip : 0 <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) :=
    NNReal.coe_nonneg _
  have hbound := abs_width_mul_gap_sub_inv_density_le
    hNreal hgap hlower (by positivity : 0 <= 1 / floor)
    (div_nonneg hE hwmin.le) hLip hrho hmesh hdensityError hcell
  simpa [gap, rhoN, rho0, floor, wmin] using hbound



theorem abs_sub_le_of_weighted_abs_sub_le_invWidth
    {N weight wmin E a b : Real} (hN : 0 < N) (hwmin : 0 < wmin)
    (hweight : wmin <= weight)
    (h : |weight * (a - b)| <= E / N) :
    |a - b| <= (E / wmin) / N := by
  have hweightPos : 0 < weight := hwmin.trans_le hweight
  have habs : |weight * (a - b)| = weight * |a - b| := by
    rw [abs_mul, abs_of_pos hweightPos]
  rw [habs] at h
  have hw : wmin * |a - b| <= E / N :=
    (mul_le_mul_of_nonneg_right hweight (abs_nonneg _)).trans h
  rw [show (E / wmin) / N = (E / N) / wmin by
    field_simp [hwmin.ne', hN.ne']]
  exact (le_div_iff₀ hwmin).2 (by simpa [mul_comm] using hw)



theorem sum_sixVertexTheta_zero_of_symmetric (c : Real)
    {n : Nat} {p : Fin n -> Real} (hp : SixVertexRootSymmetric p) :
    (∑ k, sixVertexTheta c 0 (p k)) = 0 := by
  let S := ∑ k, sixVertexTheta c 0 (p k)
  have hrev : (∑ k : Fin n, sixVertexTheta c 0 (p k.rev)) = S := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hpair : S + S = ∑ k, (sixVertexTheta c 0 (p k) +
      sixVertexTheta c 0 (-p k)) := by
    calc
      S + S = S + ∑ k : Fin n, sixVertexTheta c 0 (p k.rev) := by rw [hrev]
      _ = S + ∑ k : Fin n, sixVertexTheta c 0 (-p k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [hp]
      _ = _ := Finset.sum_add_distrib.symm
  have heval : (∑ k : Fin n, (sixVertexTheta c 0 (p k) +
      sixVertexTheta c 0 (-p k))) = 0 := by
    simp_rw [sixVertexTheta_zero_pair]
    simp
  rw [heval] at hpair
  dsimp [S] at hpair ⊢
  linarith

theorem sixVertexBetheCountingFunction_zero_of_symmetric
    (c : Real) (N : Nat) {n : Nat} {p : Fin n -> Real}
    (hp : SixVertexRootSymmetric p) :
    sixVertexBetheCountingFunction c N n p 0 = 0 := by
  unfold sixVertexBetheCountingFunction
  rw [sum_sixVertexTheta_zero_of_symmetric c hp]
  simp





theorem abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose
    {c : Real} (hc : 2 < c) {N np nq : Nat} (hN : 0 < N)
    {p : Fin np -> Real} {q : Fin nq -> Real}
    (hpSymm : SixVertexRootSymmetric p) (hqSymm : SixVertexRootSymmetric q)
    {rho : Real -> Real} {EP EQ : Real} (hEP : 0 <= EP) (hEQ : 0 <= EQ)
    (hpClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N np p y - rho y)| <= EP / N)
    (hqClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N nq q y - rho y)| <= EQ / N)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexBetheCountingFunction c N np p x -
        sixVertexBetheCountingFunction c N nq q x| <=
      (((EP + EQ) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) / N) * Real.pi := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let C := ((EP + EQ) / wmin) / (N : Real)
  let rhoP := sixVertexFiniteRootDensity c N np p
  let rhoQ := sixVertexFiniteRootDensity c N nq q
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hdensityDiff : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |rhoP y - rhoQ y| <= C := by
    intro y hy
    have hweight := sixVertexRootDensityWeight_lower hc y
    have hp := abs_sub_le_of_weighted_abs_sub_le_invWidth
      hNreal hwmin hweight (hpClose y hy)
    have hq := abs_sub_le_of_weighted_abs_sub_le_invWidth
      hNreal hwmin hweight (hqClose y hy)
    calc
      |rhoP y - rhoQ y| =
          |(rhoP y - rho y) - (rhoQ y - rho y)| := by ring
      _ <= |rhoP y - rho y| + |rhoQ y - rho y| := abs_sub _ _
      _ <= (EP / wmin) / N + (EQ / wmin) / N := add_le_add hp hq
      _ = C := by
        dsimp [C]
        field_simp [hwmin.ne', hNreal.ne']
  have hpInt := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p 0 x
  have hqInt := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN q 0 x
  have hpZero := sixVertexBetheCountingFunction_zero_of_symmetric c N hpSymm
  have hqZero := sixVertexBetheCountingFunction_zero_of_symmetric c N hqSymm
  have hIntP : IntervalIntegrable rhoP MeasureTheory.volume 0 x :=
    (continuous_sixVertexFiniteRootDensity hc N np p).intervalIntegrable _ _
  have hIntQ : IntervalIntegrable rhoQ MeasureTheory.volume 0 x :=
    (continuous_sixVertexFiniteRootDensity hc N nq q).intervalIntegrable _ _
  have heq : sixVertexBetheCountingFunction c N np p x -
        sixVertexBetheCountingFunction c N nq q x =
      ∫ y in 0..x, (rhoP y - rhoQ y) := by
    rw [intervalIntegral.integral_sub hIntP hIntQ, hpInt, hqInt,
      hpZero, hqZero]
    ring
  rw [heq]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := x) (C := C) (f := fun y => rhoP y - rhoQ y) (by
      intro y hy
      have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
        have hy' : y ∈ Set.Icc (min 0 x) (max 0 x) :=
          Set.uIoc_subset_uIcc hy
        exact ⟨(le_min (by linarith [Real.pi_pos]) hx.1).trans hy'.1,
          hy'.2.trans (max_le (by linarith [Real.pi_pos]) hx.2)⟩
      simpa [Real.norm_eq_abs] using hdensityDiff y hyIcc)
  rw [Real.norm_eq_abs] at hbound
  calc
    |∫ y in 0..x, (rhoP y - rhoQ y)| <= C * |x - 0| := hbound
    _ <= C * Real.pi := by
      gcongr
      simpa using (abs_le.mpr hx)
    _ = _ := by rfl



theorem lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n -> Real) {lower a b : Real} (hlower : 0 <= lower)
    (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N n p x) :
    lower * |b - a| <=
      |sixVertexBetheCountingFunction c N n p b -
        sixVertexBetheCountingFunction c N n p a| := by
  let rho := sixVertexFiniteRootDensity c N n p
  let F := sixVertexBetheCountingFunction c N n p
  have hInt : forall u v, IntervalIntegrable rho MeasureTheory.volume u v :=
    fun u v => (continuous_sixVertexFiniteRootDensity hc N n p).intervalIntegrable _ _
  have hordered : forall {u v : Real}, u <= v ->
      lower * (v - u) <= F v - F u := by
    intro u v huv
    have hmono := intervalIntegral.integral_mono_on huv
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      (hInt u v) (fun x _ => hdensity x)
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
      hc hN p u v] at hmono
    dsimp [rho, F] at hmono ⊢
    nlinarith

  rcases le_total a b with hab | hba
  · have h := hordered hab
    have hdiff : 0 <= sixVertexBetheCountingFunction c N n p b -
        sixVertexBetheCountingFunction c N n p a := by
      have : 0 <= lower * (b - a) := mul_nonneg hlower (sub_nonneg.mpr hab)
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg hdiff]
    exact h
  · have h := hordered hba
    have hdiff : 0 <= sixVertexBetheCountingFunction c N n p a -
        sixVertexBetheCountingFunction c N n p b := by
      have : 0 <= lower * (a - b) := mul_nonneg hlower (sub_nonneg.mpr hba)
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hba)]
    rw [show |sixVertexBetheCountingFunction c N n p b -
        sixVertexBetheCountingFunction c N n p a| =
      sixVertexBetheCountingFunction c N n p a -
        sixVertexBetheCountingFunction c N n p b by
      rw [abs_of_nonpos (sub_nonpos.mpr (by linarith))]
      ring]
    nlinarith



theorem monotone_sixVertexBetheCountingFunction_of_finiteDensity_nonneg
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n -> Real)
    (hdensity : forall x, 0 <= sixVertexFiniteRootDensity c N n p x) :
    Monotone (sixVertexBetheCountingFunction c N n p) := by
  intro a b hab
  have hmono := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume)
    hab (fun x _ => hdensity x)
  rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p a b] at hmono
  linarith





theorem abs_alignedOffsetIncrement_le
    {N q0 q1 p0 p1 rhoQ rhoP Aq Ap R C : Real}
    (hN : 0 < N) (hR : 0 <= R)
    (hqGap : |N * (q1 - q0) - 1 / rhoQ| <= Aq / N)
    (hpGap : |N * (p1 - p0) - 1 / rhoP| <= Ap / N)
    (hrecip : |1 / rhoQ - 1 / rhoP| <= R * |q0 - p0|)
    (hoffset : |N * (q0 - p0)| <= C) :
    |N * (q1 - p1) - N * (q0 - p0)| <=
      (Aq + Ap + R * C) / N := by
  have hroot : |q0 - p0| <= C / N := by
    rw [abs_mul, abs_of_pos hN] at hoffset
    exact (le_div_iff₀ hN).2 (by simpa [mul_comm] using hoffset)
  have hmiddle : |1 / rhoQ - 1 / rhoP| <= R * (C / N) :=
    hrecip.trans (mul_le_mul_of_nonneg_left hroot hR)
  have hdecomp :
      N * (q1 - p1) - N * (q0 - p0) =
        (N * (q1 - q0) - 1 / rhoQ) +
          (1 / rhoQ - 1 / rhoP) -
            (N * (p1 - p0) - 1 / rhoP) := by ring
  rw [hdecomp]
  calc
    |(N * (q1 - q0) - 1 / rhoQ) + (1 / rhoQ - 1 / rhoP) -
        (N * (p1 - p0) - 1 / rhoP)| <=
      |N * (q1 - q0) - 1 / rhoQ| +
        |1 / rhoQ - 1 / rhoP| +
          |N * (p1 - p0) - 1 / rhoP| := by
        exact (abs_sub _ _).trans
          (add_le_add (abs_add_le _ _) (le_refl _))
    _ <= Aq / N + R * (C / N) + Ap / N := by
      exact add_le_add (add_le_add hqGap hmiddle) hpGap
    _ = (Aq + Ap + R * C) / N := by
      field_simp [hN.ne']
      ring


theorem abs_consecutiveGap_mul_finiteRootDensity_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n <= N) {p : Fin n -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    (i j : Fin n) (hij : j.val = i.val + 1) :
    |(p j - p i) * sixVertexFiniteRootDensity c N n p (p i) - 1 / N| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) * (p j - p i) ^ 2 := by
  have hijLt : i < j := by simpa [Fin.lt_def, hij]
  have horder : p i <= p j := (hopen.1 hijLt).le
  have hquad := abs_gap_mul_left_sub_intervalIntegral_le
    (continuous_sixVertexFiniteRootDensity hc N n p)
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hn p) horder
  have hint := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p (p i) (p j)
  rw [sixVertexBetheCountingFunction_at_root hN hsol i,
    sixVertexBetheCountingFunction_at_root hN hsol j] at hint
  have hquantum : sixVertexCentralQuantumNumber j -
      sixVertexCentralQuantumNumber i = 1 := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [hij]
  rw [← sub_div, hquantum] at hint
  rw [hint] at hquad
  exact hquad

theorem sixVertexBetheSolution_consecutiveSpacing_upper_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : 2 * n <= N)
    {p : Fin n -> Real} (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    (i j : Fin n) (hij : j.val = i.val + 1) :
    p j - p i <= 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
  have hijLt : i < j := by simpa [Fin.lt_def, hij]
  have horder : p i <= p j := (hopen.1 hijLt).le
  have hfloor : 0 < sixVertexTailFiniteDensityFloor c :=
    sixVertexTailFiniteDensityFloor_pos hc htail
  have hint := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p (p i) (p j)
  rw [sixVertexBetheCountingFunction_at_root hN hsol i,
    sixVertexBetheCountingFunction_at_root hN hsol j] at hint
  have hquantum : sixVertexCentralQuantumNumber j -
      sixVertexCentralQuantumNumber i = 1 := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [hij]
  rw [← sub_div, hquantum] at hint
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N n p).intervalIntegrable _ _)
    (fun x _ => sixVertexTailFiniteDensityFloor_le hc hN hhalf p x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [hint] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  rw [le_div_iff₀ (mul_pos hNreal hfloor)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  field_simp [hNreal.ne'] at hmul
  nlinarith



theorem abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : 2 * n <= N)
    {p : Fin n -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    (i j : Fin n)
    {rho : Real -> Real} {lower E : Real}
    (hlower : 0 < lower) (hrho : lower <= rho (p i))
    (hE : 0 <= E)
    (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| <= E / N)
    (hij : j.val = i.val + 1) :
    |(N : Real) * (p j - p i) - 1 / rho (p i)| <=
      ((sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          (1 / sixVertexTailFiniteDensityFloor c) ^ 2 +
        (1 / sixVertexTailFiniteDensityFloor c) *
          (E / ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c))) /
        (lower * N) := by
  let gap := p j - p i
  let rhoN := sixVertexFiniteRootDensity c N n p (p i)
  let rho0 := rho (p i)
  let floor := sixVertexTailFiniteDensityFloor c
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hijLt : i < j := by simpa [Fin.lt_def, hij]
  have horder : p i <= p j := (hopen.1 hijLt).le
  have hgap : 0 <= gap := sub_nonneg.mpr horder
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hiIcc : p i ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hopen.2.2 i).1.le, (hopen.2.2 i).2.le⟩
  have hweight := sixVertexRootDensityWeight_lower hc (p i)
  have hdensityError : |rhoN - rho0| <= (E / wmin) / N :=
    abs_sub_le_of_weighted_abs_sub_le_invWidth hNreal hwmin hweight
      (hclose (p i) hiIcc)
  have hfiniteLower : forall x, floor <=
      sixVertexFiniteRootDensity c N n p x :=
    fun x => sixVertexTailFiniteDensityFloor_le hc hN hhalf p x
  have hint := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p (p i) (p j)
  rw [sixVertexBetheCountingFunction_at_root hN hsol i,
    sixVertexBetheCountingFunction_at_root hN hsol j] at hint
  have hquantum : sixVertexCentralQuantumNumber j -
      sixVertexCentralQuantumNumber i = 1 := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [hij]
  rw [← sub_div, hquantum] at hint
  have hmono := intervalIntegral.integral_mono_on
    horder
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N n p).intervalIntegrable _ _)
    (fun x _ => hfiniteLower x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [hint] at hmono
  have hmesh : gap <= (1 / floor) / N := by
    dsimp [gap]
    rw [le_div_iff₀ hNreal, div_eq_mul_inv]
    have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
    field_simp [hNreal.ne', hfloor.ne'] at hmul ⊢
    nlinarith
  have hcell := abs_consecutiveGap_mul_finiteRootDensity_sub_inv_width_le
    hc hN (by omega) hopen hsol i j hij
  have hLip : 0 <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) :=
    NNReal.coe_nonneg _
  have hbound := abs_width_mul_gap_sub_inv_density_le
    hNreal hgap hlower (by positivity : 0 <= 1 / floor)
    (div_nonneg hE hwmin.le) hLip hrho hmesh hdensityError hcell
  simpa [gap, rhoN, rho0, floor, wmin] using hbound



theorem abs_midpointAlignedOffsetIncrement_le
    {N q0 q1 p00 p01 p10 p11 rhoQ rhoP0 rhoP1 Aq Ap0 Ap1 D : Real}
    (hN : 0 < N)
    (hqGap : |N * (q1 - q0) - 1 / rhoQ| <= Aq / N)
    (hp0Gap : |N * (p01 - p00) - 1 / rhoP0| <= Ap0 / N)
    (hp1Gap : |N * (p11 - p10) - 1 / rhoP1| <= Ap1 / N)
    (hmiddle : |1 / rhoQ - (1 / rhoP0 + 1 / rhoP1) / 2| <= D / N) :
    |N * (q1 - (p01 + p11) / 2) -
        N * (q0 - (p00 + p10) / 2)| <=
      (Aq + (Ap0 + Ap1) / 2 + D) / N := by
  have hpavg :
      |N * ((p01 + p11) / 2 - (p00 + p10) / 2) -
          (1 / rhoP0 + 1 / rhoP1) / 2| <=
        ((Ap0 + Ap1) / 2) / N := by
    have heq : N * ((p01 + p11) / 2 - (p00 + p10) / 2) -
          (1 / rhoP0 + 1 / rhoP1) / 2 =
        ((N * (p01 - p00) - 1 / rhoP0) +
          (N * (p11 - p10) - 1 / rhoP1)) / 2 := by ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |(N * (p01 - p00) - 1 / rhoP0) +
          (N * (p11 - p10) - 1 / rhoP1)| / 2 <=
        (|N * (p01 - p00) - 1 / rhoP0| +
          |N * (p11 - p10) - 1 / rhoP1|) / 2 := by
            gcongr
            exact abs_add_le _ _
      _ <= (Ap0 / N + Ap1 / N) / 2 := by gcongr
      _ = ((Ap0 + Ap1) / 2) / N := by
        field_simp [hN.ne']
  have hdecomp :
      N * (q1 - (p01 + p11) / 2) - N * (q0 - (p00 + p10) / 2) =
        (N * (q1 - q0) - 1 / rhoQ) +
          (1 / rhoQ - (1 / rhoP0 + 1 / rhoP1) / 2) -
          (N * ((p01 + p11) / 2 - (p00 + p10) / 2) -
            (1 / rhoP0 + 1 / rhoP1) / 2) := by ring
  rw [hdecomp]
  calc
    |(N * (q1 - q0) - 1 / rhoQ) +
        (1 / rhoQ - (1 / rhoP0 + 1 / rhoP1) / 2) -
        (N * ((p01 + p11) / 2 - (p00 + p10) / 2) -
          (1 / rhoP0 + 1 / rhoP1) / 2)| <=
      |N * (q1 - q0) - 1 / rhoQ| +
        |1 / rhoQ - (1 / rhoP0 + 1 / rhoP1) / 2| +
        |N * ((p01 + p11) / 2 - (p00 + p10) / 2) -
          (1 / rhoP0 + 1 / rhoP1) / 2| := by
            exact (abs_sub _ _).trans
              (add_le_add (abs_add_le _ _) (le_refl _))
    _ <= Aq / N + D / N + ((Ap0 + Ap1) / 2) / N := by
      exact add_le_add (add_le_add hqGap hmiddle) hpavg
    _ = (Aq + (Ap0 + Ap1) / 2 + D) / N := by
      field_simp [hN.ne']
      ring

end

end StatMech.FrontierD
