/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.MartingaleTightness
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ConditionalExpectation

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale

namespace MathlibExtTest.Probability.Martingale.MartingaleTightness

noncomputable section

/-! ### Step and polygonal paths, computed from the definitions -/

/-- The constant array with all increments `1`, on a one-point sample space. -/
def onesArray : ℕ → ℕ → Unit → ℝ := fun _ _ _ => 1

def quarter : Set.Icc (0 : ℝ) 1 := ⟨1 / 4, by norm_num, by norm_num⟩

def one : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩

-- At `t = 1` the step path of row `2` has summed both increments.
example : arrayStepProcess 2 onesArray () one = 2 := by
  rw [arrayStepProcess_apply]
  norm_num [one, onesArray]

-- Boundary between the two paths: at `t = 1/4` in row `2` no increment has been placed yet
-- (`⌊2 · 1/4⌋ = 0`), so the step path is still `0` ...
example : arrayStepProcess 2 onesArray () quarter = 0 := by
  rw [arrayStepProcess_apply]
  simp only [quarter]
  rw [show ((2 : ℕ) : ℝ) * (1 / 4) = 1 / 2 by norm_num,
    Nat.floor_eq_zero.2 (by norm_num : (1 / 2 : ℝ) < 1)]
  simp

-- ... while the polygon has already interpolated half of the first increment.
example : arrayPolygon 2 onesArray () quarter = 1 / 2 := by
  rw [arrayPolygon_apply]
  simp only [quarter, show ((2 : ℕ) : ℝ) * (1 / 4) = 1 / 2 by norm_num,
    Nat.floor_eq_zero.2 (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num [onesArray]

-- The two paths differ by at most the largest increment (here `1`).
example (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    |arrayStepProcess n onesArray () t - arrayPolygon n onesArray () t| ≤ 1 :=
  abs_arrayStepProcess_sub_arrayPolygon_le n onesArray () zero_le_one (fun _ _ => by
    simp [onesArray]) t

-- The polygon is pinned at `0`.
example (n : ℕ) : arrayPolygon n onesArray () ⟨0, le_rfl, zero_le_one⟩ = 0 :=
  arrayPolygon_zero n onesArray ()

/-! ### Aldous's condition is not vacuous -/

/-- The trivial filtration on the one-point space, in every row. -/
def topFiltration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Unit) := fun _ => ⊤

-- The zero array satisfies Aldous's condition: every increment vanishes.
example : AldousCondition topFiltration (fun _ _ _ => (0 : ℝ)) (Measure.dirac ()) := by
  intro ε hε η _
  refine ⟨1, one_pos, 0, fun n _ σ ρ _ _ _ => ?_⟩
  have : {ω : Unit | ε ≤ |∑ i ∈ Finset.range (ρ ω), (0 : ℝ) - ∑ i ∈ Finset.range (σ ω), 0|} =
      ∅ := by
    ext ω; simp [not_le.2 hε]
  rw [this, measure_empty]
  exact zero_le

/-- Every row has a deterministic unit jump at its first increment. -/
def firstJumpArray : ℕ → ℕ → Unit → ℝ := fun _ i _ => if i = 0 then 1 else 0

-- Boundary: a deterministic unit jump at time `1/n` violates Aldous's condition. The stopping
-- times `σ = 0 ≤ ρ = 1` lie in every window `⌊n θ⌋ ≥ 1`, and the increment is `1`.
example : ¬ AldousCondition topFiltration firstJumpArray (Measure.dirac ()) := by
  intro h
  obtain ⟨θ, hθ, N, hN⟩ := h (1 / 2) (by norm_num) (1 / 2) (by norm_num)
  set n := max N (⌈1 / θ⌉₊ + 1) with hn
  have hnθ : 1 ≤ ⌊(n : ℝ) * θ⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : (1 / θ : ℝ) ≤ n := by
      have := Nat.le_ceil (1 / θ)
      have h2 : ((⌈1 / θ⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_succ _).trans (le_max_right _ _)
      linarith
    rw [div_le_iff₀ hθ] at h1
    push_cast; linarith
  have hn1 : 1 ≤ n := (Nat.le_add_left 1 _).trans (le_max_right _ _)
  have key := hN n (le_max_left _ _) (fun _ => 0) (fun _ => 1)
    (isStoppingTime_natCast_iff.2 fun i => MeasurableSet.of_discrete)
    (isStoppingTime_natCast_iff.2 fun i => MeasurableSet.of_discrete)
    (fun _ => ⟨Nat.zero_le 1, by simpa using hnθ, hn1⟩)
  have hset : {ω : Unit | (1 / 2 : ℝ) ≤ |∑ i ∈ Finset.range 1, firstJumpArray n i ω -
      ∑ i ∈ Finset.range 0, firstJumpArray n i ω|} = Set.univ := by
    ext ω; norm_num [firstJumpArray]
  rw [hset, measure_univ] at key
  have : ENNReal.ofReal (1 / 2) < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
  exact absurd key (not_le.2 this)

/-! ### Aldous's criterion and the modulus criterion, on a concrete array -/

-- The modulus criterion for the constant zero process.
example : IsTightMeasureSet (Set.range fun _ : ℕ =>
    (Measure.dirac ()).map (fun _ : Unit => (0 : C(Set.Icc (0 : ℝ) 1, ℝ)))) :=
  isTightMeasureSet_of_modulus (P := Measure.dirac ()) (fun _ _ => 0)
    (fun _ => measurable_const) (fun _ _ => rfl)
    (fun ε hε b hb => ⟨1, one_pos, Eventually.of_forall fun _ => by
      have : {ω : Unit | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ 1 ∧
          ε ≤ dist ((0 : C(Set.Icc (0 : ℝ) 1, ℝ)) s) ((0 : C(Set.Icc (0 : ℝ) 1, ℝ)) t)} = ∅ := by
        ext ω; simp [not_le.2 hε]
      rw [this, measureReal_empty]; exact hb.le⟩)

-- Aldous's criterion, all hypotheses discharged, for the zero array.
example : IsTightMeasureSet (Set.range fun n =>
    (Measure.dirac ()).map (arrayPolygon n (fun _ _ (_ : Unit) => (0 : ℝ)))) := by
  refine isTightMeasureSet_arrayPolygon_of_aldousCondition (𝓕 := topFiltration)
    (fun _ _ => measurable_const) (fun ε hε => ?_) ?_
  · have : ∀ n : ℕ, {ω : Unit | ∃ i < n, ε < |(0 : ℝ)|} = ∅ := by
      intro n; ext ω; simp [not_lt.2 hε.le]
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  · intro ε hε η _
    refine ⟨1, one_pos, 0, fun n _ σ ρ _ _ _ => ?_⟩
    have : {ω : Unit | ε ≤ |∑ i ∈ Finset.range (ρ ω), (0 : ℝ) -
        ∑ i ∈ Finset.range (σ ω), 0|} = ∅ := by
      ext ω; simp [not_le.2 hε]
    rw [this, measure_empty]
    exact zero_le

/-! ### A Rademacher array: all martingale hypotheses hold together -/

section Rademacher

/-- The fair coin on `Bool`. -/
def coin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin :=
  ⟨by simp [coin]; exact ENNReal.inv_two_add_inv_two⟩

/-- The Rademacher sign `±1` of a coin flip. -/
def rad (b : Bool) : ℝ := if b then 1 else -1

/-- The i.i.d. fair-coin sequence space. -/
abbrev coinSeq : Measure (ℕ → Bool) := Measure.infinitePi fun _ => coin

/-- Row `n`, increment `i`: the Rademacher sign of coin `i + 1`, scaled by `1/√n`. (Coin `0` is
unused, so that increment `i` is independent of the coins `0, …, i` generating `piLE i`.) -/
def radArray (n i : ℕ) (ω : ℕ → Bool) : ℝ := rad (ω (i + 1)) / Real.sqrt n

/-- The natural filtration of the coins, in every row. -/
def coinFiltration : ℕ → Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)) :=
  fun _ => Filtration.piLE

lemma abs_rad (b : Bool) : |rad b| = 1 := by cases b <;> simp [rad]

lemma integral_rad_coin : ∫ b, rad b ∂coin = 0 := by
  rw [coin, integral_smul_measure, integral_add_measure (Integrable.of_finite)
    (Integrable.of_finite)]
  simp [rad]

lemma radArray_sq (n i : ℕ) (ω : ℕ → Bool) : radArray n i ω ^ 2 = 1 / n := by
  rw [radArray, div_pow, ← sq_abs (rad _), abs_rad, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]

lemma radArray_stronglyMeasurable (n i : ℕ) :
    StronglyMeasurable[coinFiltration n (i + 1)] (radArray n i) := by
  refine Measurable.stronglyMeasurable ?_
  change Measurable[Filtration.piLE (i + 1)] _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have : radArray n i = (fun y : (Finset.Iic (i + 1) → Bool) =>
      rad (y ⟨i + 1, Finset.mem_Iic.2 le_rfl⟩) / Real.sqrt n) ∘ Preorder.frestrictLe (i + 1) := by
    funext ω; rfl
  rw [this]
  exact (measurable_of_countable _).comp (comap_measurable _)

lemma radArray_condExp (n i : ℕ) :
    coinSeq[radArray n i | coinFiltration n i] =ᵐ[coinSeq] 0 := by
  have hind : IndepFun (fun ω : ℕ → Bool => ω (i + 1)) (Preorder.frestrictLe i) coinSeq := by
    have h := (iIndepFun_infinitePi (P := fun _ => coin) (X := fun _ (b : Bool) => b)
      (fun _ => measurable_id)).indepFun_finset {i + 1} (Finset.Iic i)
      (Finset.disjoint_left.2 fun j hj hj' => by
        simp only [Finset.mem_singleton] at hj
        simp only [Finset.mem_Iic] at hj'
        omega) (fun j => measurable_pi_apply j)
    exact h.comp (φ := fun y => y ⟨i + 1, Finset.mem_singleton_self _⟩) (ψ := id)
      (measurable_pi_apply (⟨i + 1, Finset.mem_singleton_self _⟩ : ({i + 1} : Finset ℕ)))
      measurable_id
  rw [IndepFun_iff_Indep] at hind
  have hle₁ : MeasurableSpace.comap (fun ω : ℕ → Bool => ω (i + 1)) inferInstance ≤
      MeasurableSpace.pi := (measurable_pi_apply _).comap_le
  have hmeas : StronglyMeasurable[MeasurableSpace.comap (fun ω : ℕ → Bool => ω (i + 1))
      inferInstance] (radArray n i) :=
    ((measurable_of_countable (fun x : Bool => rad x / Real.sqrt n)).comp
      (comap_measurable _)).stronglyMeasurable
  have h := condExp_indep_eq hle₁ ((coinFiltration n).le i) hmeas
    (by
      show Indep _ (Filtration.piLE (X := fun _ : ℕ => Bool) i) coinSeq
      rw [Filtration.piLE_eq_comap_frestrictLe]; exact hind)
  refine h.trans (Eventually.of_forall fun _ => ?_)
  have hmap : ∫ ω, radArray n i ω ∂coinSeq = ∫ b, rad b / Real.sqrt n ∂coin := by
    rw [← Measure.infinitePi_map_eval (μ := fun _ => coin) (i + 1),
      integral_map (measurable_pi_apply _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
    rfl
  simp only [Pi.zero_apply]
  rw [hmap, integral_div, integral_rad_coin, zero_div]

lemma abs_radArray (n i : ℕ) (ω : ℕ → Bool) : |radArray n i ω| = 1 / Real.sqrt n := by
  rw [radArray, abs_div, abs_rad, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma radArray_memLp (n i : ℕ) : MemLp (radArray n i) 2 coinSeq :=
  MemLp.of_bound ((radArray_stronglyMeasurable n i).mono
    ((coinFiltration n).le _)).aestronglyMeasurable (1 / Real.sqrt n)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_radArray])

/-- The predictable quadratic variation of the Rademacher array is exactly `⌊n t⌋ / n`. -/
lemma radArray_qv (n : ℕ) (t : ℝ) (ω : ℕ → Bool) :
    ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊,
      (coinSeq[fun ω => radArray n j ω ^ 2 | coinFiltration n j]) ω =
      ⌊(n : ℝ) * t⌋₊ * (1 / n) := by
  have : ∀ j, coinSeq[fun ω => radArray n j ω ^ 2 | coinFiltration n j] = fun _ => 1 / (n : ℝ) :=
    fun j => by
      simp_rw [radArray_sq]
      exact condExp_const ((coinFiltration n).le j) _
  simp [this]

lemma tendsto_floor_mul_div {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * t⌋₊ : ℝ) * (1 / n)) atTop (𝓝 t) := by
  have hlow : Tendsto (fun n : ℕ => t - 1 / (n : ℝ)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have := Nat.lt_floor_add_one ((n : ℝ) * t)
    rw [mul_one_div, sub_le_iff_le_add, ← add_div, le_div_iff₀ hnR]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have := Nat.floor_le (mul_nonneg hnR.le ht)
    rw [mul_one_div, div_le_iff₀ hnR]
    linarith

lemma radArray_hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure coinSeq
    (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊,
      (coinSeq[fun ω => radArray n j ω ^ 2 | coinFiltration n j]) ω) atTop (fun _ => t) := by
  intro t ht
  simp_rw [radArray_qv]
  exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall fun _ => tendsto_floor_mul_div ht.1)

lemma radArray_lindeberg : LindebergConditionTriangular radArray coinSeq := by
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / Real.sqrt n ≤ ε := by
    have h : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) := by
      simp_rw [one_div]
      exact tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    exact (h.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hsmall] with n hn
  symm
  refine Finset.sum_eq_zero fun k _ => ?_
  have : {ω' | ε < |radArray n k ω'|} = ∅ := by
    ext ω'; simpa [abs_radArray] using hn
  simp [this]

-- Non-vacuity of the martingale hypotheses: the Rademacher array satisfies Aldous's condition.
example : AldousCondition coinFiltration radArray coinSeq :=
  aldousCondition_of_martingaleDifference radArray_stronglyMeasurable radArray_condExp
    radArray_memLp radArray_hQV

-- Its polygons are tight in `C([0,1])` (Aldous's criterion, all hypotheses discharged).
example : IsTightMeasureSet (Set.range fun n => coinSeq.map (arrayPolygon n radArray)) :=
  isTightMeasureSet_arrayPolygon_of_aldousCondition
    (fun n i => (radArray_stronglyMeasurable n i).measurable)
    (tendsto_measure_exists_abs_gt_of_lindeberg
      (fun n i => ((radArray_stronglyMeasurable n i).mono
        ((coinFiltration n).le _)).measurable) radArray_memLp radArray_lindeberg)
    (aldousCondition_of_martingaleDifference radArray_stronglyMeasurable radArray_condExp
      radArray_memLp radArray_hQV)

-- The functional CLT for the Rademacher array: only the limit `W` and T81's
-- finite-dimensional convergence `hT81` remain hypotheses.
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (W : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hW : AEMeasurable W P')
    (hT81 : ∀ I : Finset (Set.Icc (0 : ℝ) 1), TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict (fun t => ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊,
        radArray n i ω)) atTop (fun ω => I.restrict (fun t => W ω t)) (fun _ => coinSeq) P') :
    TendstoInDistribution (fun n => arrayStepProcess n radArray) atTop
      (fun ω => SkorokhodSpace.ofContinuous (W ω)) (fun _ => coinSeq) P' :=
  tendstoInDistribution_arrayStepProcess radArray_stronglyMeasurable radArray_condExp
    radArray_memLp radArray_hQV radArray_lindeberg W hW hT81

end Rademacher

end

end MathlibExtTest.Probability.Martingale.MartingaleTightness
