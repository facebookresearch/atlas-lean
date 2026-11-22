/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.RenewalDerivation
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Renewal derivation tests

* A concrete lattice instance of `LatticeLadderRenewalData` (span `1`, `θ = 1`): `M' = ⌊E⌋` with
  `E ~ Exp(1)`, so `P(M' > k) = e^{-(k + 1)}`, single-step ladder law `g 1 = e^{-1}`, trivial
  excursion `Y = 0`, `D = 0`. The derived lattice tail theorem (no assumed renewal theorem) applies,
  and the Cramér–Lundberg constant evaluates to `C_∞ = e^{-1}`, matching `e^k P(M' > k) = e^{-1}`.
* A nonlattice `LadderRenewalData` with `G = δ₀`, which only shows that the structure can be
  inhabited (the key renewal theorem fails for `δ₀`); its constant evaluates to `0`.
* A nonzero-excursion lattice instance, the `±1` walk with `p = 1/3`, `q = 2/3`
  (`WalkExample.walkData`): the fixed point holds with nontrivial `Y` and `D = -1`, the derived
  tail constant is `1/2`, and a direct computation of `P(Y > k) 2^{k+1} → 1/2` confirms it.
* The excursion step `tendsto_exp_mul_real_lt_of_fixedPoint` on the same fixed point.
* The derived inputs `NonlatticeRenewalInput.ofLadder`, `LatticeRenewalInput.ofLadder` and their
  limit theorems applied to arbitrary hypotheses.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Renewal MathlibExt.Probability.Renewal.LatticeConstants

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- The floor `⌊r⌋` as a real number. -/
noncomputable def flr (r : ℝ) : ℝ := (⌊r⌋ : ℝ)

theorem measurable_flr : Measurable flr :=
  (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp Int.measurable_floor

theorem ae_pos_expMeasure : ∀ᵐ r ∂(expMeasure 1), 0 < r := by
  have h0 : expMeasure 1 (Set.Iic 0) = 0 := by
    have h := cdf_expMeasure_eq one_pos 0
    rw [cdf_eq_real] at h
    simp only [le_refl, ↓reduceIte, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
    exact (measureReal_eq_zero_iff).1 h
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with r hr
  simpa using hr

theorem ae_flr_nonneg : ∀ᵐ r ∂(expMeasure 1), 0 ≤ flr r := by
  filter_upwards [ae_pos_expMeasure] with r hr
  exact Int.cast_nonneg (Int.floor_nonneg.2 hr.le)

/-- `P(⌊E⌋ > m) = P(E ≥ m + 1) = e^{-(m + 1)}`. -/
theorem real_lt_flr (m : ℕ) :
    (expMeasure 1).real {r | (m : ℝ) * 1 < flr r} = Real.exp (-((m : ℝ) + 1)) := by
  have hset : {r : ℝ | (m : ℝ) * 1 < flr r} = (Set.Iio ((m : ℝ) + 1))ᶜ := by
    ext r
    simp only [flr, mul_one, Set.mem_compl_iff, Set.mem_Iio, not_lt]
    rw [show ((m : ℝ)) = ((m : ℤ) : ℝ) by simp, Set.mem_ofPred_eq, Int.cast_lt,
      ← Int.add_one_le_iff, Int.le_floor]
    push_cast; rfl
  have hatom : expMeasure 1 {(m : ℝ) + 1} = 0 :=
    withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  rw [hset, measureReal_compl measurableSet_Iio, probReal_univ, measureReal_def,
    measure_congr (Iio_ae_eq_Iic' hatom), ← measureReal_def, ← cdf_eq_real,
    cdf_expMeasure_eq one_pos]
  have hm0 : (0 : ℝ) ≤ m + 1 := by positivity
  simp only [hm0, ↓reduceIte, one_mul]
  ring

/-- The fixed point with trivial first excursion: `Y = 0`, `D = 0`, `M' = ⌊E⌋`. -/
noncomputable def flFixedPoint : LadderFixedPoint (expMeasure 1) (fun _ => 0) where
  D _ := 0
  M' := flr
  measurable_D := measurable_const
  measurable_M' := measurable_flr
  D_nonpos := ae_of_all _ fun _ => le_rfl
  M'_nonneg := ae_flr_nonneg
  indep := indepFun_const_left _ _
  fixedPoint t := by
    refine measureReal_congr ?_
    filter_upwards [ae_flr_nonneg] with r hr
    rw [zero_add, max_eq_right hr]

/-- The single-step ladder law `g 1 = e^{-1}`. -/
noncomputable def gStep (j : ℕ) : ℝ := if j = 1 then Real.exp (-1) else 0

theorem gStep_mul_exp (j : ℕ) :
    gStep j * Real.exp (1 * 1 * j) = if j = 1 then 1 else 0 := by
  unfold gStep
  split_ifs with h
  · subst h; rw [← Real.exp_add]; norm_num
  · simp

/-- **A concrete lattice instance** (`θ = h = 1`): `P(M' > k) = e^{-(k + 1)}` solves the
defective renewal equation of the single-step ladder law `g 1 = e^{-1}`. -/
noncomputable def flData : LatticeLadderRenewalData (expMeasure 1) (fun _ => 0) 1 1 where
  toLadderFixedPoint := flFixedPoint
  D_lattice := ae_of_all _ fun _ => ⟨0, by simp [flFixedPoint]⟩
  g := gStep
  g_zero := by simp [gStep]
  g_nonneg j := by unfold gStep; split_ifs <;> positivity
  cramer_ladder := by
    simp_rw [gStep_mul_exp]; exact hasSum_ite_eq 1 1
  aperiodic := by
    have hset : {j : ℕ | 0 < gStep j} = {1} := by
      ext j; simp only [gStep, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      split_ifs with h <;> simp [h, Real.exp_pos]
    rw [hset]; exact Nat.dvd_one.1 (Nat.setGcd_dvd_of_mem rfl)
  tiltedMean := 1
  hasSum_tiltedMean := by
    simp_rw [gStep_mul_exp]
    convert hasSum_ite_eq 1 (1 : ℝ) using 1
    ext j; split_ifs with h <;> simp [h]
  renewal n := by
    change (expMeasure 1).real {r | (n : ℝ) * 1 < flr r} = ladderTail gStep n +
      ∑ k ∈ Finset.range (n + 1), gStep k * (expMeasure 1).real {r | ((n - k : ℕ) : ℝ) * 1 < flr r}
    simp_rw [real_lt_flr]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have ht : ladderTail gStep 0 = Real.exp (-1) := by
        rw [ladderTail, tsum_eq_single 0 fun j hj => by simp [gStep, hj]]
        simp [gStep]
      simp [ht, gStep]
    · have ht : ladderTail gStep n = 0 := by
        have h0 : (fun j => gStep (j + n + 1)) = fun _ => 0 :=
          funext fun j => by simp only [gStep]; rw [ite_eq_right (by omega)]
        rw [ladderTail, h0, tsum_zero]
      rw [ht, zero_add, Finset.sum_eq_single 1 (fun k _ hk => by simp [gStep, hk])
        (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
      simp only [gStep, ↓reduceIte]
      rw [← Real.exp_add, Nat.cast_sub hn]
      ring_nf

/-- The lattice Cramér–Lundberg constant of the instance: `C_∞ = e^{-1}`, matching
`e^k P(M' > k) = e^{-1}`. -/
example : flData.allTimeConst = Real.exp (-1) := by
  have hs : ∑' j, gStep j = Real.exp (-1) := by
    rw [tsum_eq_single 1 fun j hj => by simp [gStep, hj]]; simp [gStep]
  change (1 - ∑' j, gStep j) / ((Real.exp (1 * 1) - 1) * 1) = _
  rw [hs, mul_one, mul_one]
  have he : Real.exp 1 - 1 ≠ 0 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  field_simp
  rw [mul_sub, mul_one, ← Real.exp_add]; norm_num

/-- The derived lattice tail on the instance (no renewal theorem assumed). The excursion is
trivial, so the excursion constant is `C = e (e^{-1}) (1 - E e^{0}) = 0`. -/
example : Tendsto (fun k : ℕ => (expMeasure 1).real {_r : ℝ | (k : ℝ) * 1 < (0 : ℝ)} *
    Real.exp (1 * ((k + 1) * 1))) atTop (𝓝 flData.tailConst) :=
  flData.tendsto_tail measurable_const one_pos one_pos

example : flData.tailConst = 0 := by
  simp [LatticeLadderRenewalData.tailConst, flData, flFixedPoint]

/-- The excursion step directly on the fixed point `flFixedPoint`, along the lattice points
`s k = k`: `e^k P(M' > k) = e^{-1}` and `e^u P(M' > u) ≤ 1` give the excursion-tail limit
`e^{-1} (1 - E e^{0})` for `Y = 0`. -/
example : Tendsto (fun k : ℕ => Real.exp (1 * ((k : ℝ) * 1)) *
    (expMeasure 1).real {_r : ℝ | (k : ℝ) * 1 < (0 : ℝ)}) atTop
      (𝓝 (Real.exp (-1) * (1 - ∫ _, Real.exp (1 * (0 : ℝ)) ∂(expMeasure 1)))) := by
  have hC : Tendsto (fun k : ℕ => Real.exp (1 * ((k : ℝ) * 1)) *
      (expMeasure 1).real {r | (k : ℝ) * 1 < flr r}) atTop (𝓝 (Real.exp (-1))) := by
    refine tendsto_const_nhds.congr fun k => ?_
    rw [real_lt_flr, ← Real.exp_add]; ring_nf
  refine tendsto_exp_mul_real_lt_of_fixedPoint (Y := fun _ => (0 : ℝ)) (D := fun _ => 0)
    (M' := flr) one_pos measurable_const measurable_const measurable_flr
    (ae_of_all _ fun _ => le_rfl) (indepFun_const_left _ _) flFixedPoint.fixedPoint
    (tendsto_natCast_atTop_atTop.atTop_mul_const one_pos) (B := 1) (fun u hu => ?_) hC
    (ae_of_all _ fun _ => by simpa using hC)
  -- `e^u P(⌊E⌋ > u) ≤ e^u P(E > u) = 1`
  have hsub : {r | u < flr r} ⊆ {r | u < r} := fun r (h : u < flr r) =>
    lt_of_lt_of_le h (Int.floor_le r)
  have hcdf : (expMeasure 1).real {r | u < r} = Real.exp (-u) := by
    rw [show {r : ℝ | u < r} = (Set.Iic u)ᶜ by ext; simp, measureReal_compl measurableSet_Iic,
      probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq one_pos]
    simp [hu]
  calc Real.exp (1 * u) * (expMeasure 1).real {r | u < flr r}
      ≤ Real.exp (1 * u) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_left (hcdf ▸ measureReal_mono hsub) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- A nonlattice `LadderRenewalData` with ladder law `δ₀` (degenerate: the tilted law is `δ₀`,
for which the key renewal theorem fails, so `tendsto_tail` cannot be applied to it). -/
noncomputable def diracData : LadderRenewalData (expMeasure 1) (fun _ => 0) 1 where
  toLadderFixedPoint := flFixedPoint
  G := Measure.dirac 0
  isFiniteMeasure_G := inferInstance
  G_nonneg := by simp
  cramer_ladder := by simp
  integrable_mean := integrable_dirac (by simp)
  renewal t _ := by simp

example : diracData.allTimeConst = 0 := by
  simp [LadderRenewalData.allTimeConst, diracData]

/-! ### A nonzero excursion: the `±1` walk with `p = 1/3`, `q = 2/3`

`θ = log 2` (`(1/3) · 2 + (2/3) · (1/2) = 1`), `h = 1`. On `ℕ × ℕ` with independent coordinates,
`Y = fst` has the gambler's-ruin tail `P(Y ≥ m) = 1 / (2^{m+1} - 1)`, `M' = snd` the geometric
tail `P(M' ≥ m) = 2^{-m}`, and `D ≡ -1`. The derived excursion constant is `1/2`, checked
against a direct computation of `P(Y > k) 2^{k+1}`. -/

namespace WalkExample

/-- The law on `ℕ` with tail `P(n ≥ m) = a m` (masses `a n - a (n + 1)`). -/
noncomputable def tailLaw (a : ℕ → ℝ) : Measure ℕ :=
  Measure.sum fun n => ENNReal.ofReal (a n - a (n + 1)) • Measure.dirac n

/-- Telescoping: `∑ (b n - b (n + 1)) = b 0` for antitone `b → 0`. -/
theorem hasSum_sub_succ {b : ℕ → ℝ} (hb : Antitone b) (h0 : Tendsto b atTop (𝓝 0)) :
    HasSum (fun n => b n - b (n + 1)) (b 0) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.2 (hb n.le_succ)) _).2 ?_
  simp_rw [Finset.sum_range_sub']
  simpa using tendsto_const_nhds.sub h0

/-- `P(n ≥ m) = a m` under `tailLaw a`, for antitone `a → 0`. -/
theorem tailLaw_le {a : ℕ → ℝ} (ha : Antitone a) (h0 : Tendsto a atTop (𝓝 0)) (m : ℕ) :
    tailLaw a {n | m ≤ n} = ENNReal.ofReal (a m) := by
  set c : ℕ → ℝ := fun n => a (max n m) with hc
  have hcanti : Antitone c := fun i j hij => ha (max_le_max hij le_rfl)
  have hc0 : Tendsto c atTop (𝓝 0) :=
    (h0.comp (tendsto_atTop_mono (fun n => le_max_left n m) tendsto_id)).congr fun _ => rfl
  have hterm : ∀ n, {n | m ≤ n}.indicator (fun n => a n - a (n + 1)) n = c n - c (n + 1) := by
    intro n
    by_cases hn : m ≤ n
    · rw [Set.indicator_of_mem (show n ∈ {n | m ≤ n} from hn), hc]
      simp only
      rw [max_eq_left hn, max_eq_left (by omega)]
    · rw [Set.indicator_of_notMem (show n ∉ {n | m ≤ n} from hn), hc]
      simp only
      rw [max_eq_right (by omega), max_eq_right (by omega), sub_self]
  have hsum : HasSum (fun n => {n | m ≤ n}.indicator (fun n => a n - a (n + 1)) n) (a m) := by
    have h := hasSum_sub_succ hcanti hc0
    simp only [hc, Nat.zero_max] at h
    exact h.congr_fun fun n => by rw [hterm]
  have hnn : ∀ n, 0 ≤ {n | m ≤ n}.indicator (fun n => a n - a (n + 1)) n := fun n =>
    Set.indicator_nonneg (fun n _ => sub_nonneg.2 (ha n.le_succ)) n
  have hmeas : tailLaw a {n | m ≤ n} =
      ∑' n, ENNReal.ofReal ({n | m ≤ n}.indicator (fun n => a n - a (n + 1)) n) := by
    rw [tailLaw, Measure.sum_apply _ (.of_discrete)]
    refine tsum_congr fun n => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ (.of_discrete), smul_eq_mul]
    by_cases hn : m ≤ n
    · simp [Set.indicator_of_mem (show n ∈ {n | m ≤ n} from hn)]
    · simp [Set.indicator_of_notMem (show n ∉ {n | m ≤ n} from hn)]
  rw [hmeas, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]

theorem tailLaw_real_le {a : ℕ → ℝ} (ha : Antitone a) (h0 : Tendsto a atTop (𝓝 0)) (m : ℕ) :
    (tailLaw a).real {n | m ≤ n} = a m := by
  rw [measureReal_def, tailLaw_le ha h0, ENNReal.toReal_ofReal (ha.le_of_tendsto h0 m)]

theorem isProbabilityMeasure_tailLaw {a : ℕ → ℝ} (ha : Antitone a) (h0 : Tendsto a atTop (𝓝 0))
    (h1 : a 0 = 1) : IsProbabilityMeasure (tailLaw a) := by
  have h := tailLaw_le ha h0 0
  simp only [zero_le, Set.ofPred_true, h1, ENNReal.ofReal_one] at h
  exact ⟨h⟩

/-- `{n : ℕ | t < n} = {n | idx t ≤ n}` with `idx t = (⌊t⌋ + 1).toNat`. -/
theorem setOf_lt_natCast (t : ℝ) :
    {n : ℕ | t < (n : ℝ)} = {n | (⌊t⌋ + 1).toNat ≤ n} := by
  ext n
  simp only [Set.mem_ofPred_eq]
  rw [Int.toNat_le, Int.add_one_le_iff, Int.floor_lt]
  push_cast; rfl

theorem tailLaw_real_lt {a : ℕ → ℝ} (ha : Antitone a) (h0 : Tendsto a atTop (𝓝 0)) (t : ℝ) :
    (tailLaw a).real {n : ℕ | t < (n : ℝ)} = a (⌊t⌋ + 1).toNat := by
  rw [setOf_lt_natCast, tailLaw_real_le ha h0]

/-- Gambler's-ruin tail `P(Y ≥ m) = 1 / (2^{m+1} - 1)`: the height of the first excursion of the
`±1` walk with `p = 1/3`, `q = 2/3`. -/
noncomputable def aY (m : ℕ) : ℝ := 1 / (2 ^ (m + 1) - 1)

/-- Geometric tail `P(M' ≥ m) = 2^{-m}`: the all-time maximum of the same walk. -/
noncomputable def aM (m : ℕ) : ℝ := (1 / 2) ^ m

theorem aY_pos_den (m : ℕ) : (0 : ℝ) < 2 ^ (m + 1) - 1 := by
  have : (2 : ℝ) ≤ 2 ^ (m + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ one_le_two (by omega)
  linarith

theorem antitone_aY : Antitone aY := fun i j hij =>
  one_div_le_one_div_of_le (aY_pos_den i)
    (by have := pow_le_pow_right₀ (one_le_two (α := ℝ)) (show i + 1 ≤ j + 1 by omega); linarith)

theorem antitone_aM : Antitone aM := fun _ _ hij =>
  pow_le_pow_of_le_one (by norm_num) (by norm_num) hij

theorem tendsto_aM : Tendsto aM atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem tendsto_aY : Tendsto aY atTop (𝓝 0) := by
  refine squeeze_zero (fun m => (one_div_pos.2 (aY_pos_den m)).le) (fun m => ?_) tendsto_aM
  rw [aY, aM, one_div_pow]
  refine one_div_le_one_div_of_le (by positivity) ?_
  rw [pow_succ]; linarith [one_le_pow₀ (one_le_two (α := ℝ)) (n := m)]

instance : IsProbabilityMeasure (tailLaw aY) :=
  isProbabilityMeasure_tailLaw antitone_aY tendsto_aY (by norm_num [aY])

instance : IsProbabilityMeasure (tailLaw aM) :=
  isProbabilityMeasure_tailLaw antitone_aM tendsto_aM (by simp [aM])

/-- The probability space of the `±1` walk example: `(Y, M')` independent. -/
noncomputable abbrev Pw : Measure (ℕ × ℕ) := (tailLaw aY).prod (tailLaw aM)

theorem Pw_fst_lt (t : ℝ) : Pw.real {ω : ℕ × ℕ | t < (ω.1 : ℝ)} = aY (⌊t⌋ + 1).toNat := by
  rw [show {ω : ℕ × ℕ | t < (ω.1 : ℝ)} = {n : ℕ | t < (n : ℝ)} ×ˢ Set.univ by ext; simp,
    measureReal_prod_prod, probReal_univ, mul_one, tailLaw_real_lt antitone_aY tendsto_aY]

theorem Pw_snd_lt (t : ℝ) : Pw.real {ω : ℕ × ℕ | t < (ω.2 : ℝ)} = aM (⌊t⌋ + 1).toNat := by
  rw [show {ω : ℕ × ℕ | t < (ω.2 : ℝ)} = Set.univ ×ˢ {n : ℕ | t < (n : ℝ)} by ext; simp,
    measureReal_prod_prod, probReal_univ, one_mul, tailLaw_real_lt antitone_aM tendsto_aM]

/-- The fixed point `max Y (D + M') =ᵈ M'` with `D = -1`: for `k = ⌊t⌋ ≥ 0` it is
`(1 - 1/(2^{k+2} - 1)) (1 - 2^{-(k+2)}) = 1 - 2^{-(k+1)}`; both sides are `1` for `t < 0`. -/
theorem Pw_fixedPoint (t : ℝ) :
    Pw.real {ω : ℕ × ℕ | t < max (ω.1 : ℝ) (-1 + ω.2)} = Pw.real {ω : ℕ × ℕ | t < (ω.2 : ℝ)} := by
  have hset : {ω : ℕ × ℕ | t < max (ω.1 : ℝ) (-1 + ω.2)} =
      ({n : ℕ | t < (n : ℝ)}ᶜ ×ˢ {n : ℕ | t + 1 < (n : ℝ)}ᶜ)ᶜ := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_ofPred_eq, lt_max_iff, not_and_or,
      not_not]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [hset, measureReal_compl ((MeasurableSet.of_discrete).prod (.of_discrete)), probReal_univ,
    measureReal_prod_prod, measureReal_compl (.of_discrete), measureReal_compl (.of_discrete),
    probReal_univ, probReal_univ, tailLaw_real_lt antitone_aY tendsto_aY,
    tailLaw_real_lt antitone_aM tendsto_aM, Pw_snd_lt, Int.floor_add_one]
  rcases lt_or_ge ⌊t⌋ 0 with hk | hk
  · rw [Int.toNat_eq_zero.2 (by omega : ⌊t⌋ + 1 ≤ 0)]
    norm_num [aY, aM]
  · obtain ⟨k, hk'⟩ := Int.eq_ofNat_of_zero_le hk
    rw [hk', show ((k : ℤ) + 1).toNat = k + 1 by omega,
      show ((k : ℤ) + 1 + 1).toNat = k + 1 + 1 by omega]
    have hd := aY_pos_den (k + 1)
    simp only [aY, aM, one_div_pow]
    rw [pow_succ 2 (k + 1)] at hd ⊢
    field_simp
    ring

/-- The first excursion height `Y`. -/
noncomputable def wY (ω : ℕ × ℕ) : ℝ := (ω.1 : ℝ)

theorem measurable_wY : Measurable wY :=
  (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp measurable_fst

/-- The descending-ladder fixed point of the walk: `D ≡ -1`, `M' = snd`, independent of `Y`. -/
noncomputable def wFixedPoint : LadderFixedPoint Pw wY where
  D _ := -1
  M' ω := (ω.2 : ℝ)
  measurable_D := measurable_const
  measurable_M' := (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp measurable_snd
  D_nonpos := ae_of_all _ fun _ => by norm_num
  M'_nonneg := ae_of_all _ fun _ => Nat.cast_nonneg _
  indep := indepFun_prod (X := fun n : ℕ => ((n : ℝ), (-1 : ℝ))) (Y := fun n : ℕ => (n : ℝ))
    measurable_from_nat measurable_from_nat
  fixedPoint := Pw_fixedPoint

/-- The single-step ascending ladder law `g 1 = 1/2` (the walk first exceeds `0` w.p. `1/2`). -/
noncomputable def gHalf (j : ℕ) : ℝ := if j = 1 then 1 / 2 else 0

theorem gHalf_mul_exp (j : ℕ) :
    gHalf j * Real.exp (Real.log 2 * 1 * j) = if j = 1 then 1 else 0 := by
  unfold gHalf
  split_ifs with h
  · subst h; rw [Nat.cast_one, mul_one, mul_one, Real.exp_log two_pos]; norm_num
  · simp

theorem Pw_snd_natCast_lt (k : ℕ) :
    Pw.real {ω : ℕ × ℕ | (k : ℝ) * 1 < (ω.2 : ℝ)} = (1 / 2) ^ (k + 1) := by
  rw [mul_one, Pw_snd_lt, Int.floor_natCast, aM]
  congr 1

/-- **Nonzero-excursion lattice instance** (`θ = log 2`, `h = 1`): the `±1` walk with
`p = 1/3`, `q = 2/3`. -/
noncomputable def walkData : LatticeLadderRenewalData Pw wY (Real.log 2) 1 where
  toLadderFixedPoint := wFixedPoint
  D_lattice := ae_of_all _ fun _ => ⟨1, by simp [wFixedPoint]⟩
  g := gHalf
  g_zero := by simp [gHalf]
  g_nonneg j := by unfold gHalf; split_ifs <;> norm_num
  cramer_ladder := by
    simp_rw [gHalf_mul_exp]; exact hasSum_ite_eq 1 1
  aperiodic := by
    have hset : {j : ℕ | 0 < gHalf j} = {1} := by
      ext j; simp only [gHalf, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      split_ifs with h <;> simp [h]
    rw [hset]; exact Nat.dvd_one.1 (Nat.setGcd_dvd_of_mem rfl)
  tiltedMean := 1
  hasSum_tiltedMean := by
    simp_rw [gHalf_mul_exp]
    convert hasSum_ite_eq 1 (1 : ℝ) using 1
    ext j; split_ifs with h <;> simp [h]
  renewal n := by
    change Pw.real {ω : ℕ × ℕ | (n : ℝ) * 1 < (ω.2 : ℝ)} = ladderTail gHalf n +
      ∑ k ∈ Finset.range (n + 1),
        gHalf k * Pw.real {ω : ℕ × ℕ | ((n - k : ℕ) : ℝ) * 1 < (ω.2 : ℝ)}
    simp_rw [Pw_snd_natCast_lt]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have ht : ladderTail gHalf 0 = 1 / 2 := by
        rw [ladderTail, tsum_eq_single 0 fun j hj => by simp [gHalf, hj]]
        simp [gHalf]
      simp [ht, gHalf]
    · have ht : ladderTail gHalf n = 0 := by
        have h0 : (fun j => gHalf (j + n + 1)) = fun _ => 0 :=
          funext fun j => by simp only [gHalf]; rw [ite_eq_right (by omega)]
        rw [ladderTail, h0, tsum_zero]
      rw [ht, zero_add, Finset.sum_eq_single 1 (fun k _ hk => by simp [gHalf, hk])
        (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
      simp only [gHalf, ↓reduceIte]
      rw [show n - 1 + 1 = n by omega, pow_succ]
      ring

/-- The constants, computed from the definitions: `C_∞ = (1 - 1/2) / ((2 - 1) · 1) = 1/2`,
`E e^{θ D} = 1/2`, `C = e^{θ} · C_∞ · (1 - 1/2) = 1/2`. -/
theorem walkData_tailConst : walkData.tailConst = 1 / 2 := by
  have hs : ∑' j, gHalf j = 1 / 2 := by
    rw [tsum_eq_single 1 fun j hj => by simp [gHalf, hj]]; simp [gHalf]
  have hD : ∫ _ : ℕ × ℕ, Real.exp (Real.log 2 * (-1 : ℝ)) ∂Pw = 1 / 2 := by
    rw [integral_const, probReal_univ, one_smul, mul_neg_one, Real.exp_neg,
      Real.exp_log two_pos, one_div]
  change Real.exp (Real.log 2 * 1) * ((1 - ∑' j, gHalf j) /
      ((Real.exp (Real.log 2 * 1) - 1) * 1) *
    (1 - ∫ _ : ℕ × ℕ, Real.exp (Real.log 2 * (-1 : ℝ)) ∂Pw)) = 1 / 2
  rw [hs, hD, mul_one, Real.exp_log two_pos]
  norm_num

/-- The derived lattice tail on the walk, with constant `1/2`. -/
example : Tendsto (fun k : ℕ => Pw.real {ω | (k : ℝ) * 1 < wY ω} *
    Real.exp (Real.log 2 * ((k + 1) * 1))) atTop (𝓝 (1 / 2)) :=
  walkData_tailConst ▸ walkData.tendsto_tail measurable_wY (Real.log_pos one_lt_two) one_pos

/-- Independent cross-check, not via the theorem:
`P(Y > k) 2^{k+1} = 2^{k+1} / (2^{k+2} - 1) = 1 / (2 - 2^{-(k+1)}) → 1/2`. -/
example : Tendsto (fun k : ℕ => Pw.real {ω | (k : ℝ) * 1 < wY ω} *
    Real.exp (Real.log 2 * ((k + 1) * 1))) atTop (𝓝 (1 / 2)) := by
  have hval : ∀ k : ℕ, Pw.real {ω | (k : ℝ) * 1 < wY ω} * Real.exp (Real.log 2 * ((k + 1) * 1)) =
      1 / (2 - (1 / 2) ^ (k + 1)) := by
    intro k
    have hexp : Real.exp (Real.log 2 * ((k + 1) * 1)) = 2 ^ (k + 1) := by
      rw [mul_one, mul_comm, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log two_pos]
    have hY : Pw.real {ω | (k : ℝ) * 1 < wY ω} = aY (k + 1) := by
      rw [mul_one]; exact (Pw_fst_lt _).trans (by rw [Int.floor_natCast]; congr 1)
    have hd := aY_pos_den (k + 1)
    have hp : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    rw [hexp, hY, aY, one_div_pow]
    rw [pow_succ 2 (k + 1)] at hd ⊢
    field_simp
  have hlim : Tendsto (fun k : ℕ => 2 - (1 / 2 : ℝ) ^ (k + 1)) atTop (𝓝 (2 - 0)) :=
    tendsto_const_nhds.sub ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num)).comp (tendsto_add_atTop_nat 1))
  have h := tendsto_const_nhds (x := (1 : ℝ)).div hlim (by norm_num)
  rw [sub_zero] at h
  exact h.congr fun k => (hval k).symm

end WalkExample

/-! ### Derived inputs on arbitrary data -/

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {θ h : ℝ}

example (L : LadderInput P (maxSegmentScoreRV X)) (t : ℝ) :
    P.real {ω | t < L.Y 0 ω} = 1 - L.F t :=
  L.real_Y_lt_eq_one_sub t

example (hX : CramerScores P X θ) (hnl : ∀ h > 0, ¬ ∀ᵐ ω ∂P, ∃ k : ℤ, X 0 ω = k * h)
    (L : LadderInput P (maxSegmentScoreRV X)) (R : LadderRenewalData P (L.Y 0) θ)
    (hKRT : ∀ V v : ℝ → ℝ, KeyRenewalAdmissible V v →
      (∀ t, V t = v t + ∫ x, V (t - x) ∂(R.G.tilted (fun x => θ * x))) →
      Tendsto V atTop (𝓝 ((∫ s in Set.Ioi 0, v s) / ∫ x, x ∂(R.G.tilted (fun x => θ * x)))))
    (x : ℝ) :
    (NonlatticeRenewalInput.ofLadder hX hnl L R hKRT).C = R.tailConst ∧
      Tendsto (fun n : ℕ => P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x}) atTop
        (𝓝 (Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * x)))))) :=
  ⟨rfl, NonlatticeRenewalInput.tendsto_gumbel_ofLadder hX hnl L R hKRT x⟩

example (hX : CramerScores P X θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, X i ω = k * h)
    (L : LadderInput P (maxSegmentScoreRV X)) (hlatY : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, L.Y i ω = k * h)
    (R : LatticeLadderRenewalData P (L.Y 0) θ h) (x : ℝ) (hC : 0 < R.tailConst) :
    (LatticeRenewalInput.ofLadder hX hh hlat L hlatY R).C = R.tailConst ∧
      (∀ᶠ n : ℕ in atTop, Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * x)))) - 1 ≤
          P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x} ∧
        P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x} ≤
          Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * (x + h))))) + 1) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x})
        atTop (𝓝 l) :=
  ⟨rfl, LatticeRenewalInput.eventually_bounds_ofLadder hX hh hlat L hlatY R x one_pos,
    fun ⟨l, hl⟩ => (LatticeRenewalInput.ofLadder hX hh hlat L hlatY R).not_tendsto hC x l hl⟩

end

end Cslib.Bioinformatics.Alignment.ScoreSignificance
