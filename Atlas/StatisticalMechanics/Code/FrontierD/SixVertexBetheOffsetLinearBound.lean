/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRootGapFirstOrder
import Code.FrontierD.SixVertexBetheOffsetFinite










namespace StatMech.FrontierD

noncomputable section



theorem lower_mul_abs_sub_le_abs_intervalIntegral
    {rho : Real → Real} {lower a b : Real}
    (hrho : Continuous rho) (hlower : ∀ x, lower ≤ rho x)
    (hlowerNonneg : 0 ≤ lower) :
    lower * |b - a| ≤ |∫ x in a..b, rho x| := by
  have hforward : ∀ {u v : Real}, u ≤ v →
      lower * |v - u| ≤ |∫ x in u..v, rho x| := by
    intro u v huv
    have hconst : IntervalIntegrable (fun _ : Real => lower)
        MeasureTheory.volume u v := continuous_const.intervalIntegrable _ _
    have hrhoInt : IntervalIntegrable rho MeasureTheory.volume u v :=
      hrho.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on huv hconst hrhoInt
      (fun x _ => hlower x)
    have hconstEval : (∫ _x in u..v, lower) = lower * (v - u) := by
      simp
      ring
    rw [hconstEval] at hmono
    have hnonneg : 0 ≤ ∫ x in u..v, rho x :=
      (mul_nonneg hlowerNonneg (sub_nonneg.mpr huv)).trans hmono
    rw [abs_of_nonneg (sub_nonneg.mpr huv), abs_of_nonneg hnonneg]
    exact hmono
  by_cases hab : a ≤ b
  · exact hforward hab
  · have hba : b ≤ a := le_of_not_ge hab
    have hback := hforward hba
    rw [intervalIntegral.integral_symm, abs_neg, abs_sub_comm] at hback
    exact hback



theorem abs_intervalIntegral_sub_const_mul_le_of_lipschitz
    {f : Real → Real} {C : NNReal} {a b u : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hab : a ≤ b) (hu : u ∈ Set.Icc a b) :
    |(∫ x in a..b, f x) - f u * (b - a)| ≤
      (C : Real) * (b - a) ^ 2 := by
  have hcontSub : Continuous (fun x => f x - f u) :=
    hf.sub continuous_const
  have hrearrange :
      (∫ x in a..b, f x) - f u * (b - a) =
        ∫ x in a..b, (f x - f u) := by
    rw [intervalIntegral.integral_sub
      (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
    simp
    ring
  rw [hrearrange]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := (C : Real) * (b - a))
    (f := fun x => f x - f u) (by
      intro x hx
      have hxIcc : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hx
      have hxu : |x - u| ≤ b - a := by
        rw [abs_le]
        constructor <;> linarith [hxIcc.1, hxIcc.2, hu.1, hu.2]
      rw [Real.norm_eq_abs]
      calc
        |f x - f u| = dist (f x) (f u) := by rw [Real.dist_eq]
        _ ≤ (C : Real) * dist x u := hlip.dist_le_mul x u
        _ = (C : Real) * |x - u| := by rw [Real.dist_eq]
        _ ≤ (C : Real) * (b - a) :=
          mul_le_mul_of_nonneg_left hxu (NNReal.coe_nonneg C))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
  simpa [mul_assoc, pow_two] using hbound



theorem abs_sixVertexBetheCountingFunction_midpoint_defect_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n ≤ N) (p : Fin n → Real) {a b : Real} (hab : a ≤ b) :
    |(sixVertexBetheCountingFunction c N n p a +
          sixVertexBetheCountingFunction c N n p b) / 2 -
        sixVertexBetheCountingFunction c N n p ((a + b) / 2)| ≤
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (b - a) ^ 2 / 4 := by
  let F := sixVertexBetheCountingFunction c N n p
  let rho := sixVertexFiniteRootDensity c N n p
  let m := (a + b) / 2
  let C := sixVertexFiniteRootDensityLipschitzConstant c
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hmLeft : m ∈ Set.Icc a m := ⟨ham, le_rfl⟩
  have hmRight : m ∈ Set.Icc m b := ⟨le_rfl, hmb⟩
  have hleft := abs_intervalIntegral_sub_const_mul_le_of_lipschitz
    (continuous_sixVertexFiniteRootDensity hc N n p)
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hn p)
    ham hmLeft
  have hright := abs_intervalIntegral_sub_const_mul_le_of_lipschitz
    (continuous_sixVertexFiniteRootDensity hc N n p)
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hn p)
    hmb hmRight
  have hleftFTC := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p a m
  have hrightFTC := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p m b
  rw [hleftFTC] at hleft
  rw [hrightFTC] at hright
  change |(F m - F a) -
      sixVertexFiniteRootDensity c N n p m * (m - a)| ≤ _ at hleft
  change |(F b - F m) -
      sixVertexFiniteRootDensity c N n p m * (b - m)| ≤ _ at hright
  have hsum := abs_sub_le
    ((F b - F m) - sixVertexFiniteRootDensity c N n p m * (b - m)) 0
    ((F m - F a) - sixVertexFiniteRootDensity c N n p m * (m - a))
  have hdiff :
      |((F b - F m) - sixVertexFiniteRootDensity c N n p m * (b - m)) -
        ((F m - F a) - sixVertexFiniteRootDensity c N n p m * (m - a))| ≤
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          (b - m) ^ 2 +
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          (m - a) ^ 2 := by
    exact hsum.trans (by
      simpa only [sub_zero, zero_sub, abs_neg] using add_le_add hright hleft)
  have hrewrite :
      ((F b - F m) - sixVertexFiniteRootDensity c N n p m * (b - m)) -
        ((F m - F a) - sixVertexFiniteRootDensity c N n p m * (m - a)) =
      2 * ((F a + F b) / 2 - F m) := by
    dsimp [m]
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)] at hdiff
  change |(F a + F b) / 2 - F m| ≤ _
  have hC : 0 ≤ (sixVertexFiniteRootDensityLipschitzConstant c : Real) :=
    NNReal.coe_nonneg _
  dsimp [m] at hdiff ⊢
  nlinarith [hC]




theorem abs_sixVertexBetheCountingFunction_sub_le_mul_abs
    {c : Real} (hc : 2 < c) {N np nq : Nat} (hN : 0 < N)
    {p : Fin np → Real} {q : Fin nq → Real}
    (hpSymm : SixVertexRootSymmetric p) (hqSymm : SixVertexRootSymmetric q)
    {rho : Real → Real} {EP EQ : Real} (hEP : 0 ≤ EP) (hEQ : 0 ≤ EQ)
    (hpClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N np p y - rho y)| ≤ EP / N)
    (hqClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N nq q y - rho y)| ≤ EQ / N)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexBetheCountingFunction c N np p x -
        sixVertexBetheCountingFunction c N nq q x| ≤
      (((EP + EQ) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) / N) * |x| := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let C := ((EP + EQ) / wmin) / (N : Real)
  let rhoP := sixVertexFiniteRootDensity c N np p
  let rhoQ := sixVertexFiniteRootDensity c N nq q
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdensityDiff : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |rhoP y - rhoQ y| ≤ C := by
    intro y hy
    have hweight := sixVertexRootDensityWeight_lower hc y
    have hp := abs_sub_le_of_weighted_abs_sub_le_invWidth
      hNreal hwmin hweight (hpClose y hy)
    have hq := abs_sub_le_of_weighted_abs_sub_le_invWidth
      hNreal hwmin hweight (hqClose y hy)
    calc
      |rhoP y - rhoQ y| ≤ |rhoP y - rho y| + |rhoQ y - rho y| :=
        by simpa [abs_sub_comm] using abs_sub_le (rhoP y) (rho y) (rhoQ y)
      _ ≤ (EP / wmin) / N + (EQ / wmin) / N := add_le_add hp hq
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
  simpa [Real.norm_eq_abs] using hbound



theorem abs_alignedBetheRootOffset_le_mul_abs
    {c : Real} (hc : 2 < c) {N np nq : Nat} (hN : 0 < N)
    {p : Fin np → Real} {q : Fin nq → Real}
    (hpOpen : SixVertexOpenRootSimplex p)
    (hqOpen : SixVertexOpenRootSimplex q)
    (hpSol : SixVertexSatisfiesBetheEquations c N np p)
    (hqSol : SixVertexSatisfiesBetheEquations c N nq q)
    {rho : Real → Real} {EP EQ lower : Real}
    (hEP : 0 ≤ EP) (hEQ : 0 ≤ EQ) (hlower : 0 < lower)
    (hqLower : ∀ x, lower ≤ sixVertexFiniteRootDensity c N nq q x)
    (hpClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N np p y - rho y)| ≤ EP / N)
    (hqClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N nq q y - rho y)| ≤ EQ / N)
    (i : Fin np) (j : Fin nq)
    (hquantum : sixVertexCentralQuantumNumber i =
      sixVertexCentralQuantumNumber j) :
    |(N : Real) * (q j - p i)| ≤
      ((EP + EQ) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) / lower * |p i| := by
  let Fp := sixVertexBetheCountingFunction c N np p
  let Fq := sixVertexBetheCountingFunction c N nq q
  let rhoQ := sixVertexFiniteRootDensity c N nq q
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let C := ((EP + EQ) / wmin) / (N : Real)
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hpIcc : p i ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hpOpen.2.2 i).1.le, (hpOpen.2.2 i).2.le⟩
  have hcount := abs_sixVertexBetheCountingFunction_sub_le_mul_abs
    hc hN hpOpen.2.1 hqOpen.2.1 hEP hEQ hpClose hqClose hpIcc
  have hpRoot := sixVertexBetheCountingFunction_at_root hN hpSol i
  have hqRoot := sixVertexBetheCountingFunction_at_root hN hqSol j
  have hrootEq : Fq (q j) = Fp (p i) := by
    dsimp [Fp, Fq]
    rw [hpRoot, hqRoot, hquantum]
  have hInt := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN q (p i) (q j)
  have hlowerInt := lower_mul_abs_sub_le_abs_intervalIntegral
    (continuous_sixVertexFiniteRootDensity hc N nq q) hqLower hlower.le
    (a := p i) (b := q j)
  rw [hInt] at hlowerInt
  change lower * |q j - p i| ≤ |Fq (q j) - Fq (p i)| at hlowerInt
  rw [hrootEq] at hlowerInt
  have hcount' : |Fp (p i) - Fq (p i)| ≤ C * |p i| := by
    simpa [Fp, Fq, C, wmin] using hcount
  have hgap : lower * |q j - p i| ≤ C * |p i| :=
    hlowerInt.trans hcount'
  rw [abs_mul, abs_of_pos hNreal]
  have hdiv : |q j - p i| ≤ C * |p i| / lower :=
    (le_div_iff₀ hlower).2 (by simpa [mul_comm] using hgap)
  calc
    (N : Real) * |q j - p i| ≤
        (N : Real) * (C * |p i| / lower) :=
      mul_le_mul_of_nonneg_left hdiv hNreal.le
    _ = ((EP + EQ) / wmin) / lower * |p i| := by
      dsimp [C]
      field_simp [hNreal.ne', hlower.ne']
    _ = _ := by rfl


theorem abs_sixVertexEvenChargeBetheOffset_le_mul_abs_halfRoot
    {c : Real} (hc : 2 < c) (s k : Nat)
    {rho : Real → Real} {EP EQ lower : Real}
    (hEP : 0 ≤ EP) (hEQ : 0 ≤ EQ) (hlower : 0 < lower)
    (hfixedLower : ∀ x, lower ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) x)
    (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          ((2 * s + k + 1) + (2 * s + k + 1))
          (sixVertexHalfFilledBetheRoots hc (2 * s + k)) y - rho y)| ≤
        EP / sixVertexFourWidth (2 * s) k)
    (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k) y - rho y)| ≤
        EQ / sixVertexFourWidth (2 * s) k)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexEvenChargeBetheOffset hc s k j| ≤
      ((EP + EQ) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) / lower *
        |sixVertexHalfFilledBetheRoots hc (2 * s + k)
          (sixVertexEvenChargeHalfIndex s k j)| := by
  unfold sixVertexEvenChargeBetheOffset
  exact abs_alignedBetheRootOffset_le_mul_abs hc
    (sixVertexFourWidth_pos (2 * s) k)
    (sixVertexHalfFilledBetheRoots_mem_open hc (2 * s + k))
    (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k)
    (by simpa [sixVertexFourWidth] using
      sixVertexHalfFilledBetheRoots_is_solution hc (2 * s + k))
    (sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k)
    hEP hEQ hlower hfixedLower hhalfClose hfixedClose
    (sixVertexEvenChargeHalfIndex s k j) j
    (sixVertexEvenChargeHalfIndex_quantum s k j)



theorem abs_sixVertexOddChargeBetheOffset_le_mul_abs_halfAverage_add
    {c : Real} (hc : 2 < c) (s k : Nat)
    {rho : Real → Real} {EP EQ lowerP lowerQ : Real}
    (hEP : 0 ≤ EP) (hEQ : 0 ≤ EQ)
    (hlowerP : 0 < lowerP) (hlowerQ : 0 < lowerQ)
    (hhalfLower : ∀ x, lowerP ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) x)
    (hfixedLower : ∀ x, lowerQ ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) x)
    (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
          (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) y - rho y)| ≤
        EP / sixVertexFourWidth (2 * s + 1) k)
    (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) y - rho y)| ≤
        EQ / sixVertexFourWidth (2 * s + 1) k)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    |sixVertexOddChargeBetheOffset hc s k j| ≤
      ((EP + EQ) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) / lowerQ *
        |(sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
            (sixVertexOddChargeLowerHalfIndex s k j) +
          sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
            (sixVertexOddChargeUpperHalfIndex s k j)) / 2| +
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
        (4 * lowerP ^ 2 * lowerQ * sixVertexFourWidth (2 * s + 1) k) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let np := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let nq := sixVertexFixedChargeBetheParticleCount (2 * s + 1) k
  let p := sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let il := sixVertexOddChargeLowerHalfIndex s k j
  let iu := sixVertexOddChargeUpperHalfIndex s k j
  let pl := p il
  let pu := p iu
  let a := (pl + pu) / 2
  let Fp := sixVertexBetheCountingFunction c N np p
  let Fq := sixVertexBetheCountingFunction c N nq q
  let gap := pu - pl
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let C := ((EP + EQ) / wmin) / (N : Real)
  let L : Real := sixVertexFiniteRootDensityLipschitzConstant c
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hnp : np ≤ N := by
    dsimp [np, N]
    unfold sixVertexFourWidth
    omega
  have hpOpen : SixVertexOpenRootSimplex p := by
    dsimp [p, np]
    exact sixVertexHalfFilledBetheRoots_mem_open hc (2 * s + 1 + k)
  have hqOpen : SixVertexOpenRootSimplex q := by
    dsimp [q, nq]
    exact sixVertexFixedChargeBetheRoots_mem_open hc (2 * s + 1) k
  have hpSol : SixVertexSatisfiesBetheEquations c N np p := by
    dsimp [N, np, p]
    simpa [sixVertexFourWidth] using
      sixVertexHalfFilledBetheRoots_is_solution hc (2 * s + 1 + k)
  have hqSol : SixVertexSatisfiesBetheEquations c N nq q := by
    dsimp [N, nq, q]
    exact sixVertexFixedChargeBetheRoots_is_solution hc (2 * s + 1) k
  have hplpu : pl ≤ pu := by
    exact (hpOpen.1 (by
      dsimp [il, iu, sixVertexOddChargeLowerHalfIndex,
        sixVertexOddChargeUpperHalfIndex]
      simp [Fin.lt_iff_val_lt_val])).le
  have hgap : 0 ≤ gap := sub_nonneg.mpr hplpu
  have haIcc : a ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [a]
    constructor
    · have hl := (hpOpen.2.2 il).1.le
      have hu := (hpOpen.2.2 iu).1.le
      linarith
    · have hl := (hpOpen.2.2 il).2.le
      have hu := (hpOpen.2.2 iu).2.le
      linarith
  have hcount := abs_sixVertexBetheCountingFunction_sub_le_mul_abs
    hc hN hpOpen.2.1 hqOpen.2.1 hEP hEQ
    (by simpa [N, np, p] using hhalfClose)
    (by simpa [N, nq, q] using hfixedClose) haIcc
  have hmid := abs_sixVertexBetheCountingFunction_midpoint_defect_le
    hc hN hnp p hplpu
  change |(Fp pl + Fp pu) / 2 - Fp a| ≤ L * gap ^ 2 / 4 at hmid
  have hpLRoot := sixVertexBetheCountingFunction_at_root hN hpSol il
  have hpURoot := sixVertexBetheCountingFunction_at_root hN hpSol iu
  have hqRoot := sixVertexBetheCountingFunction_at_root hN hqSol j
  have hquantum := sixVertexOddChargeHalfIndex_quantum_average s k j
  have hrootAverage : Fq (q j) = (Fp pl + Fp pu) / 2 := by
    dsimp [Fp, Fq, pl, pu]
    rw [hqRoot, hpLRoot, hpURoot]
    rw [← hquantum]
    ring
  have hcount' : |Fp a - Fq a| ≤ C * |a| := by
    simpa [Fp, Fq, C, wmin, N, np, nq, p, q] using hcount
  have hFdiff : |Fq (q j) - Fq a| ≤ C * |a| + L * gap ^ 2 / 4 := by
    rw [hrootAverage]
    calc
      |(Fp pl + Fp pu) / 2 - Fq a| ≤
          |(Fp pl + Fp pu) / 2 - Fp a| + |Fp a - Fq a| :=
        abs_sub_le _ _ _
      _ ≤ L * gap ^ 2 / 4 + C * |a| := add_le_add hmid hcount'
      _ = C * |a| + L * gap ^ 2 / 4 := add_comm _ _
  have hfixedInt := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN q a (q j)
  have hfixedLowerInt := lower_mul_abs_sub_le_abs_intervalIntegral
    (continuous_sixVertexFiniteRootDensity hc N nq q)
    (by simpa [N, nq, q] using hfixedLower) hlowerQ.le
    (a := a) (b := q j)
  rw [hfixedInt] at hfixedLowerInt
  change lowerQ * |q j - a| ≤ |Fq (q j) - Fq a| at hfixedLowerInt
  have hdisplacement : lowerQ * |q j - a| ≤
      C * |a| + L * gap ^ 2 / 4 := hfixedLowerInt.trans hFdiff
  have hhalfInt := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p pl pu
  have hquantumDiff : sixVertexCentralQuantumNumber iu -
      sixVertexCentralQuantumNumber il = 1 := by
    dsimp [il, iu, sixVertexOddChargeLowerHalfIndex,
      sixVertexOddChargeUpperHalfIndex]
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp
  have hhalfMass :
      (∫ x in pl..pu, sixVertexFiniteRootDensity c N np p x) = 1 / N := by
    rw [hhalfInt]
    dsimp [pl, pu]
    rw [hpLRoot, hpURoot, ← sub_div, hquantumDiff]
  have hhalfLowerInt := lower_mul_abs_sub_le_abs_intervalIntegral
    (continuous_sixVertexFiniteRootDensity hc N np p)
    (by simpa [N, np, p] using hhalfLower) hlowerP.le
    (a := pl) (b := pu)
  rw [hhalfMass, abs_of_nonneg (by positivity : (0 : Real) ≤ 1 / N),
    abs_of_nonneg hgap] at hhalfLowerInt
  have hgapBound : gap ≤ 1 / (lowerP * N) := by
    rw [show 1 / (lowerP * (N : Real)) =
      (1 / (N : Real)) / lowerP by
        field_simp [hNreal.ne', hlowerP.ne']]
    exact (le_div_iff₀ hlowerP).2
      (by simpa [mul_comm] using hhalfLowerInt)
  have hinvNonneg : 0 ≤ 1 / (lowerP * N) := by positivity
  have hgapSq : gap ^ 2 ≤ (1 / (lowerP * N)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (lowerP * N) - gap)]
  have hL : 0 ≤ L := by dsimp [L]; exact NNReal.coe_nonneg _
  have hdisp' : |q j - a| ≤
      (C * |a| + L * gap ^ 2 / 4) / lowerQ :=
    (le_div_iff₀ hlowerQ).2 (by simpa [mul_comm] using hdisplacement)
  unfold sixVertexOddChargeBetheOffset
  change |(N : Real) * (q j - a)| ≤ _
  rw [abs_mul, abs_of_pos hNreal]
  calc
    (N : Real) * |q j - a| ≤
        (N : Real) * ((C * |a| + L * gap ^ 2 / 4) / lowerQ) :=
      mul_le_mul_of_nonneg_left hdisp' hNreal.le
    _ ≤ (N : Real) *
        ((C * |a| + L * (1 / (lowerP * N)) ^ 2 / 4) / lowerQ) := by
      gcongr
    _ = ((EP + EQ) / wmin) / lowerQ * |a| +
        L / (4 * lowerP ^ 2 * lowerQ * N) := by
      dsimp [C]
      field_simp [hNreal.ne', hlowerP.ne', hlowerQ.ne']
    _ = _ := by rfl

end

end StatMech.FrontierD
