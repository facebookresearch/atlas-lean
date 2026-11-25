/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Differential privacy

A *mechanism* is a map `M : X → Measure Ω` sending a database `x` to the law of the released
output. Given a neighbouring relation `Adj` on databases, `M` is `(ε, δ)`-differentially private
when, for all neighbours `x, y` and every measurable event `S`,
`M x S ≤ exp ε * M y S + δ` (Dwork and Roth, *The Algorithmic Foundations of Differential
Privacy*, 2014, Definition 2.4). Dwork and Roth take histograms `x : U → ℕ` with
`‖x - y‖₁ ≤ 1`; that neighbouring relation is `histogramAdj` below, and every result here holds
for an arbitrary relation; `hammingAdj` is the relation for databases given as lists of rows.

* `DifferentiallyPrivate`: the definition; `ε`-differential privacy is the case `δ = 0`.
* `differentiallyPrivate_zero_iff_le_smul`: pure differential privacy is the measure inequality
  `M x ≤ exp ε • M y` on neighbours.
* `DifferentiallyPrivate.map`, `DifferentiallyPrivate.bind` (**post-processing**, Dwork and Roth,
  Proposition 2.1): a measurable map or a Markov kernel applied to the output preserves
  `(ε, δ)`-differential privacy.
* `DifferentiallyPrivate.group` (**group privacy**, Dwork and Roth, Theorem 2.2): along a chain of
  `k` neighbouring steps an `ε`-differentially private mechanism satisfies the `kε` bound;
  `DifferentiallyPrivate.group_histogram` is the statement for histograms at `ℓ₁` distance `≤ k`.
  `DifferentiallyPrivate.group_approx` is the `(k ε, k e^{(k-1) ε} δ)` bound for `δ > 0`.
* `DifferentiallyPrivate.compProd` (**adaptive composition**), `DifferentiallyPrivate.prod`
  (**composition**, Dwork and Roth, Theorem 3.14): running an `ε₁`-private mechanism and then an
  `ε₂`-private one, which may depend on the first output, is `(ε₁ + ε₂)`-private.
  `DifferentiallyPrivate.compProd_approx` and `DifferentiallyPrivate.prod_approx` are the
  `(ε₁ + ε₂, δ₁ + δ₂)` statements for probability measures (Theorem 3.16 for two mechanisms),
  proved by truncating the second-stage probabilities at `1` and applying the layer-cake form of
  the `(ε₁, δ₁)` bound. `differentiallyPrivate_pi` is Theorem 3.16 for `k` independent
  mechanisms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Cslib.Crypto.Privacy

universe u

variable {X Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- **Differential privacy.** A mechanism `M : X → Measure Ω` is `(ε, δ)`-differentially private
for the neighbouring relation `Adj` if for all `x, y` with `Adj x y` and every measurable `S ⊆ Ω`,
`M x S ≤ exp ε · M y S + δ`. With `δ = 0` this is `ε`-differential privacy (Dwork and Roth,
*The Algorithmic Foundations of Differential Privacy*, 2014, Definition 2.4, there for histogram
databases with `‖x - y‖₁ ≤ 1`, which is `histogramAdj`). -/
def DifferentiallyPrivate (Adj : X → X → Prop) (M : X → Measure Ω) (ε : ℝ) (δ : ℝ≥0∞) : Prop :=
  ∀ ⦃x y : X⦄, Adj x y → ∀ S : Set Ω, MeasurableSet S →
    M x S ≤ ENNReal.ofReal (Real.exp ε) * M y S + δ

/-- **Neighbouring histograms.** Two databases over a finite universe `U`, given as histograms
`x y : U → ℕ` (the number of records of each type), are neighbours when
`‖x - y‖₁ = ∑ u, |x u - y u| ≤ 1` (Dwork and Roth, 2014, Definition 2.3 and Definition 2.4). -/
def histogramAdj {U : Type*} [Fintype U] (x y : U → ℕ) : Prop :=
  ∑ u, |(x u : ℤ) - y u| ≤ 1

/-- **Neighbouring row databases.** Two databases of `n` rows, `S S' : Fin n → U`, are neighbours
when they differ in at most one row, i.e. their Hamming distance is at most `1` (Dwork and Roth,
2014, Section 2.3, the representation of databases as ordered lists of rows). Equal databases are
neighbours, also when `n = 0`. -/
def hammingAdj {U : Type*} {n : ℕ} (S S' : Fin n → U) : Prop :=
  S = S' ∨ ∃ i, ∀ j, j ≠ i → S j = S' j

variable {Adj : X → X → Prop} {M : X → Measure Ω} {ε ε' : ℝ} {δ δ' : ℝ≥0∞}

/-- **Monotonicity of the privacy parameters.** An `(ε, δ)`-differentially private mechanism is
`(ε', δ')`-differentially private whenever `ε ≤ ε'` and `δ ≤ δ'` (immediate from Dwork and Roth,
2014, Definition 2.4). -/
theorem DifferentiallyPrivate.mono (h : DifferentiallyPrivate Adj M ε δ) (hε : ε ≤ ε')
    (hδ : δ ≤ δ') : DifferentiallyPrivate Adj M ε' δ' := by
  intro x y hxy S hS
  refine (h hxy S hS).trans (add_le_add (mul_le_mul_left ?_ _) hδ)
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hε)

/-- **Pure differential privacy as a measure inequality.** `M` is `(ε, 0)`-differentially private
if and only if `M x ≤ exp ε • M y` as measures for all neighbours `x, y` (a restatement of Dwork
and Roth, 2014, Definition 2.4 with `δ = 0`). -/
theorem differentiallyPrivate_zero_iff_le_smul :
    DifferentiallyPrivate Adj M ε 0 ↔
      ∀ ⦃x y : X⦄, Adj x y → M x ≤ ENNReal.ofReal (Real.exp ε) • M y := by
  simp only [DifferentiallyPrivate, add_zero, Measure.le_iff, Measure.smul_apply, smul_eq_mul]

/-- **Post-processing by a measurable map.** If `M` is `(ε, δ)`-differentially private and
`f : Ω → Ω'` is measurable, then `x ↦ f_* (M x)` is `(ε, δ)`-differentially private (Dwork and
Roth, 2014, Proposition 2.1, deterministic case). -/
theorem DifferentiallyPrivate.map (h : DifferentiallyPrivate Adj M ε δ) {f : Ω → Ω'}
    (hf : Measurable f) : DifferentiallyPrivate Adj (fun x ↦ (M x).map f) ε δ := by
  intro x y hxy S hS
  simpa only [Measure.map_apply hf hS] using h hxy _ (hf hS)

/-- Layer-cake step of post-processing: an `(ε, δ)` bound on events gives the same bound on the
integral of a measurable function with values in `[0, 1]`. -/
private theorem lintegral_le_of_forall_measurableSet {μ ν : Measure Ω} {c : ℝ≥0∞}
    (h : ∀ S, MeasurableSet S → μ S ≤ c * ν S + δ) {g : Ω → ℝ} (hg : Measurable g)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ ≤ c * ∫⁻ ω, ENNReal.ofReal (g ω) ∂ν + δ := by
  have h0 : (0 : Ω → ℝ) ≤ᵐ[μ] g := Filter.Eventually.of_forall hg0
  have h0' : (0 : Ω → ℝ) ≤ᵐ[ν] g := Filter.Eventually.of_forall hg0
  rw [lintegral_eq_lintegral_meas_lt μ h0 hg.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν h0' hg.aemeasurable]
  have hpt : ∀ t : ℝ,
      μ {a | t < g a} ≤ c * ν {a | t < g a} + (Iio (1 : ℝ)).indicator (fun _ ↦ δ) t := by
    intro t
    by_cases ht : t < 1
    · simpa [Set.indicator_of_mem (show t ∈ Iio (1 : ℝ) from ht)] using
        h _ (measurableSet_lt measurable_const hg)
    · have : {a | t < g a} = ∅ := by
        ext a
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hg1 a).trans (not_lt.mp ht)
      simp [this]
  calc ∫⁻ t in Ioi 0, μ {a | t < g a}
      ≤ ∫⁻ t in Ioi 0, (c * ν {a | t < g a} + (Iio (1 : ℝ)).indicator (fun _ ↦ δ) t) :=
        lintegral_mono fun t ↦ hpt t
    _ = c * (∫⁻ t in Ioi 0, ν {a | t < g a}) +
          ∫⁻ t in Ioi 0, (Iio (1 : ℝ)).indicator (fun _ ↦ δ) t := by
        have hm : Measurable fun t : ℝ ↦ ν {a | t < g a} :=
          Antitone.measurable fun s t hst ↦ measure_mono fun a (ha : t < g a) ↦
            (show s < g a from lt_of_le_of_lt hst ha)
        rw [lintegral_add_left (hm.const_mul c), lintegral_const_mul c hm]
    _ ≤ c * (∫⁻ t in Ioi 0, ν {a | t < g a}) + δ := by
        gcongr
        rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
        calc δ * volume (Iio (1 : ℝ) ∩ Ioi 0) ≤ δ * 1 := by
              gcongr
              rw [Set.Iio_inter_Ioi, Real.volume_Ioo]
              simp
          _ = δ := mul_one δ

/-- **Post-processing by a Markov kernel.** If `M` is `(ε, δ)`-differentially private and
`κ : Kernel Ω Ω'` is a Markov kernel (a randomized map applied to the output, independent of the
database), then `x ↦ (M x).bind κ` is `(ε, δ)`-differentially private (Dwork and Roth, 2014,
Proposition 2.1). -/
theorem DifferentiallyPrivate.bind (h : DifferentiallyPrivate Adj M ε δ) (κ : Kernel Ω Ω')
    [IsMarkovKernel κ] : DifferentiallyPrivate Adj (fun x ↦ (M x).bind κ) ε δ := by
  intro x y hxy S hS
  have hκ : Measurable fun ω ↦ (κ ω S).toReal := (κ.measurable_coe hS).ennreal_toReal
  have key := lintegral_le_of_forall_measurableSet (h hxy) hκ (fun _ ↦ ENNReal.toReal_nonneg)
    (fun ω ↦ ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one))
  simp only [ENNReal.ofReal_toReal (measure_ne_top (κ _) S)] at key
  simpa only [Measure.bind_apply hS κ.aemeasurable] using key

/-- **Group privacy along a chain.** If `M` is `ε`-differentially private and `z 0, …, z k` is a
chain of databases with `Adj (z i) (z (i + 1))` for `i < k`, then
`M (z 0) S ≤ exp (k ε) · M (z k) S` for every measurable `S` (Dwork and Roth, 2014, Theorem 2.2,
whose groups of size `k` are such chains). -/
theorem DifferentiallyPrivate.group (h : DifferentiallyPrivate Adj M ε 0) {k : ℕ} {z : ℕ → X}
    (hz : ∀ i < k, Adj (z i) (z (i + 1))) {S : Set Ω} (hS : MeasurableSet S) :
    M (z 0) S ≤ ENNReal.ofReal (Real.exp (k * ε)) * M (z k) S := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine (ih fun i hi ↦ hz i (by omega)).trans ?_
    have hstep := h (hz k (by omega)) S hS
    rw [add_zero] at hstep
    calc ENNReal.ofReal (Real.exp (k * ε)) * M (z k) S
        ≤ ENNReal.ofReal (Real.exp (k * ε)) * (ENNReal.ofReal (Real.exp ε) * M (z (k + 1)) S) :=
          by gcongr
      _ = ENNReal.ofReal (Real.exp (↑(k + 1) * ε)) * M (z (k + 1)) S := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          push_cast
          ring_nf

/-- **Group privacy along a chain, approximate case.** If `M` is `(ε, δ)`-differentially private
and `z 0, …, z k` is a chain with `Adj (z i) (z (i + 1))` for `i < k`, then for every measurable
`S`, `M (z 0) S ≤ exp (k ε) · M (z k) S + (∑_{i < k} exp (i ε)) · δ` (the iterated form of the
remark in Dwork and Roth, 2014, footnote 1 to Theorem 2.2). -/
theorem DifferentiallyPrivate.group_sum (h : DifferentiallyPrivate Adj M ε δ) {k : ℕ}
    {z : ℕ → X} (hz : ∀ i < k, Adj (z i) (z (i + 1))) {S : Set Ω} (hS : MeasurableSet S) :
    M (z 0) S ≤ ENNReal.ofReal (Real.exp (k * ε)) * M (z k) S +
      (∑ i ∈ Finset.range k, ENNReal.ofReal (Real.exp (i * ε))) * δ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine (ih fun i hi ↦ hz i (by omega)).trans ?_
    have hstep := h (hz k (by omega)) S hS
    calc ENNReal.ofReal (Real.exp (k * ε)) * M (z k) S +
          (∑ i ∈ Finset.range k, ENNReal.ofReal (Real.exp (i * ε))) * δ
        ≤ ENNReal.ofReal (Real.exp (k * ε)) * (ENNReal.ofReal (Real.exp ε) * M (z (k + 1)) S + δ) +
          (∑ i ∈ Finset.range k, ENNReal.ofReal (Real.exp (i * ε))) * δ := by gcongr
      _ = ENNReal.ofReal (Real.exp (↑(k + 1) * ε)) * M (z (k + 1)) S +
          (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (Real.exp (i * ε))) * δ := by
          rw [Finset.sum_range_succ, mul_add, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_mul, add_assoc,
            add_comm (ENNReal.ofReal (Real.exp (k * ε)) * δ)]
          push_cast
          ring_nf

/-- **Group privacy, approximate case.** If `M` is `(ε, δ)`-differentially private with
`ε ≥ 0` and `z 0, …, z k` is a chain of neighbours, then for every measurable `S`,
`M (z 0) S ≤ exp (k ε) · M (z k) S + k exp ((k - 1) ε) δ`: an `(ε, δ)`-private mechanism is
`(k ε, k e^{(k-1) ε} δ)`-private for groups of size `k` (Dwork and Roth, 2014, footnote 1 to
Theorem 2.2). -/
theorem DifferentiallyPrivate.group_approx (h : DifferentiallyPrivate Adj M ε δ) (hε : 0 ≤ ε)
    {k : ℕ} {z : ℕ → X} (hz : ∀ i < k, Adj (z i) (z (i + 1))) {S : Set Ω}
    (hS : MeasurableSet S) :
    M (z 0) S ≤ ENNReal.ofReal (Real.exp (k * ε)) * M (z k) S +
      k * ENNReal.ofReal (Real.exp ((k - 1 : ℝ) * ε)) * δ := by
  refine (h.group_sum hz hS).trans ?_
  gcongr
  calc ∑ i ∈ Finset.range k, ENNReal.ofReal (Real.exp (i * ε))
      ≤ ∑ _i ∈ Finset.range k, ENNReal.ofReal (Real.exp ((k - 1 : ℝ) * ε)) := by
        refine Finset.sum_le_sum fun i hi ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have : (i : ℝ) ≤ k - 1 := by
          have := Finset.mem_range.mp hi
          have : (i : ℝ) + 1 ≤ k := by exact_mod_cast this
          linarith
        exact mul_le_mul_of_nonneg_right this hε
    _ = k * ENNReal.ofReal (Real.exp ((k - 1 : ℝ) * ε)) := by simp

/-- A histogram at `ℓ₁` distance at most `k` from another is joined to it by a chain of at most
`k` neighbouring histograms. -/
private theorem step_abs (a b : ℕ) (h : a ≠ b) :
    |(((if a < b then a + 1 else a - 1 : ℕ)) : ℤ) - b| + 1 = |(a : ℤ) - b| ∧
      |(a : ℤ) - ((if a < b then a + 1 else a - 1 : ℕ) : ℤ)| = 1 := by
  have h' : (a : ℤ) ≠ b := by exact_mod_cast h
  split_ifs with hlt
  · constructor <;>
    rcases abs_cases ((((a + 1 : ℕ)) : ℤ) - b) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases ((a : ℤ) - b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases ((a : ℤ) - ((a + 1 : ℕ) : ℤ)) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
  · constructor <;>
    rcases abs_cases ((((a - 1 : ℕ)) : ℤ) - b) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases ((a : ℤ) - b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases ((a : ℤ) - ((a - 1 : ℕ) : ℤ)) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega

private theorem exists_chain_histogram {U : Type*} [Fintype U] :
    ∀ (k : ℕ) (x y : U → ℕ), ∑ u, |(x u : ℤ) - y u| ≤ k →
      ∃ z : ℕ → U → ℕ, z 0 = x ∧ z k = y ∧ ∀ i < k, histogramAdj (z i) (z (i + 1)) := by
  classical
  intro k
  induction k with
  | zero =>
    intro x y hxy
    have hxy' : x = y := by
      funext u
      have h0 : ∀ v ∈ Finset.univ, |(x v : ℤ) - y v| = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun v _ ↦ abs_nonneg _).mp
          (le_antisymm (by exact_mod_cast hxy) (Finset.sum_nonneg fun v _ ↦ abs_nonneg _))
      have := abs_eq_zero.mp (h0 u (Finset.mem_univ u))
      omega
    exact ⟨fun _ ↦ x, rfl, hxy', fun i hi ↦ by omega⟩
  | succ k ih =>
    intro x y hxy
    by_cases hxy' : x = y
    · refine ⟨fun _ ↦ x, rfl, hxy', fun i _ ↦ ?_⟩
      simp [histogramAdj]
    · obtain ⟨u, hu⟩ : ∃ u, x u ≠ y u := by
        by_contra hne
        push Not at hne
        exact hxy' (funext hne)
      -- move `x` one step towards `y` at coordinate `u`
      set x' : U → ℕ := Function.update x u (if x u < y u then x u + 1 else x u - 1) with hx'
      have hdist : ∑ v, |(x' v : ℤ) - y v| ≤ k := by
        have hsplit : ∀ w : U → ℕ, ∑ v, |(w v : ℤ) - y v| =
            |(w u : ℤ) - y u| + ∑ v ∈ Finset.univ.erase u, |(w v : ℤ) - y v| := fun w ↦
          (Finset.add_sum_erase _ _ (Finset.mem_univ u)).symm
        have hrest : ∑ v ∈ Finset.univ.erase u, |(x' v : ℤ) - y v| =
            ∑ v ∈ Finset.univ.erase u, |(x v : ℤ) - y v| :=
          Finset.sum_congr rfl fun v hv ↦ by
            rw [hx', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
        have hu' : |(x' u : ℤ) - y u| + 1 = |(x u : ℤ) - y u| := by
          rw [hx', Function.update_self]
          exact (step_abs _ _ hu).1
        rw [hsplit x] at hxy
        rw [hsplit x', hrest]
        push_cast at hxy
        omega
      obtain ⟨z, hz0, hzk, hz⟩ := ih x' y hdist
      refine ⟨fun i ↦ if i = 0 then x else z (i - 1), by simp, by simpa using hzk, ?_⟩
      intro i hi
      rcases i with _ | i
      · simp only [ite_true, show (0 : ℕ) + 1 ≠ 0 from one_ne_zero, ite_false, Nat.add_sub_cancel,
          hz0, histogramAdj]
        rw [Finset.sum_eq_single u]
        · rw [hx', Function.update_self]
          exact (step_abs _ _ hu).2.le
        · intro v _ hv
          rw [hx', Function.update_of_ne hv]
          simp
        · simp
      · simpa using hz i (by omega)

/-- **Group privacy for histograms.** If `M` is `ε`-differentially private for neighbouring
histograms, then for all histograms with `‖x - y‖₁ ≤ k` and every measurable `S`,
`M x S ≤ exp (k ε) · M y S` (Dwork and Roth, 2014, Theorem 2.2). -/
theorem DifferentiallyPrivate.group_histogram {U : Type*} [Fintype U] {M : (U → ℕ) → Measure Ω}
    (h : DifferentiallyPrivate histogramAdj M ε 0) {k : ℕ} {x y : U → ℕ}
    (hxy : ∑ u, |(x u : ℤ) - y u| ≤ k) {S : Set Ω} (hS : MeasurableSet S) :
    M x S ≤ ENNReal.ofReal (Real.exp (k * ε)) * M y S := by
  classical
  obtain ⟨z, hz0, hzk, hz⟩ := exists_chain_histogram k x y hxy
  simpa [hz0, hzk] using h.group hz hS

/-- **Adaptive composition of pure differential privacy.** Let `M₁ : X → Measure Ω` be
`ε₁`-differentially private, and let `M₂ x : Kernel Ω Ω'` be a second mechanism that may depend on
the first output `ω`, such that for every `ω` the mechanism `x ↦ M₂ x ω` is `ε₂`-differentially
private. Then releasing both outputs, `x ↦ M₁ x ⊗ₘ M₂ x`, is `(ε₁ + ε₂)`-differentially private
(Dwork and Roth, 2014, Theorem 3.14, here with the second mechanism chosen adaptively). -/
theorem DifferentiallyPrivate.compProd {M₁ : X → Measure Ω} {M₂ : X → Kernel Ω Ω'} {ε₁ ε₂ : ℝ}
    [∀ x, SFinite (M₁ x)] [∀ x, IsSFiniteKernel (M₂ x)]
    (h₁ : DifferentiallyPrivate Adj M₁ ε₁ 0)
    (h₂ : ∀ ω, DifferentiallyPrivate Adj (fun x ↦ M₂ x ω) ε₂ 0) :
    DifferentiallyPrivate Adj (fun x ↦ M₁ x ⊗ₘ M₂ x) (ε₁ + ε₂) 0 := by
  intro x y hxy S hS
  rw [add_zero, Measure.compProd_apply hS, Measure.compProd_apply hS]
  have h₁' := differentiallyPrivate_zero_iff_le_smul.mp h₁ hxy
  have h₂' : ∀ ω, M₂ x ω (Prod.mk ω ⁻¹' S) ≤
      ENNReal.ofReal (Real.exp ε₂) * M₂ y ω (Prod.mk ω ⁻¹' S) := fun ω ↦ by
    simpa using h₂ ω hxy _ (measurable_prodMk_left hS)
  calc ∫⁻ ω, M₂ x ω (Prod.mk ω ⁻¹' S) ∂M₁ x
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ε₂) * M₂ y ω (Prod.mk ω ⁻¹' S)
          ∂(ENNReal.ofReal (Real.exp ε₁) • M₁ y) := lintegral_mono' h₁' h₂'
    _ = ENNReal.ofReal (Real.exp (ε₁ + ε₂)) * ∫⁻ ω, M₂ y ω (Prod.mk ω ⁻¹' S) ∂M₁ y := by
        rw [lintegral_smul_measure, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul,
          ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

/-- **Adaptive composition of approximate differential privacy, two mechanisms.** Let
`M₁ : X → Measure Ω` be `(ε₁, δ₁)`-differentially private with values in probability measures,
and let `M₂ x : Kernel Ω Ω'` be Markov kernels such that, for every first output `ω`,
`x ↦ M₂ x ω` is `(ε₂, δ₂)`-differentially private. Then releasing both outputs,
`x ↦ M₁ x ⊗ₘ M₂ x`, is `(ε₁ + ε₂, δ₁ + δ₂)`-differentially private (Dwork and Roth, 2014,
Theorem 3.16 for `k = 2`, here with the second mechanism chosen adaptively). -/
theorem DifferentiallyPrivate.compProd_approx {M₁ : X → Measure Ω} {M₂ : X → Kernel Ω Ω'}
    {ε₁ ε₂ : ℝ} {δ₁ δ₂ : ℝ≥0∞} [∀ x, IsProbabilityMeasure (M₁ x)] [∀ x, IsMarkovKernel (M₂ x)]
    (h₁ : DifferentiallyPrivate Adj M₁ ε₁ δ₁)
    (h₂ : ∀ ω, DifferentiallyPrivate Adj (fun x ↦ M₂ x ω) ε₂ δ₂) :
    DifferentiallyPrivate Adj (fun x ↦ M₁ x ⊗ₘ M₂ x) (ε₁ + ε₂) (δ₁ + δ₂) := by
  intro x y hxy S hS
  rw [Measure.compProd_apply hS, Measure.compProd_apply hS]
  set c₁ := ENNReal.ofReal (Real.exp ε₁)
  set c₂ := ENNReal.ofReal (Real.exp ε₂)
  -- the second-stage probability of the section, truncated at `1`
  set h : Ω → ℝ≥0∞ := fun ω ↦ min 1 (c₂ * M₂ y ω (Prod.mk ω ⁻¹' S)) with hh
  have hmeas : Measurable fun ω ↦ M₂ y ω (Prod.mk ω ⁻¹' S) :=
    Kernel.measurable_kernel_prodMk_left hS
  have hpt : ∀ ω, M₂ x ω (Prod.mk ω ⁻¹' S) ≤ h ω + δ₂ := by
    intro ω
    have hle := h₂ ω hxy (Prod.mk ω ⁻¹' S) (measurable_prodMk_left hS)
    have hle1 : M₂ x ω (Prod.mk ω ⁻¹' S) ≤ 1 := prob_le_one
    rcases le_total 1 (c₂ * M₂ y ω (Prod.mk ω ⁻¹' S)) with hc | hc
    · simp only [hh, min_eq_left hc]
      exact hle1.trans le_self_add
    · simpa only [hh, min_eq_right hc] using hle
  have hg : Measurable fun ω ↦ (h ω).toReal :=
    ((measurable_const.min (hmeas.const_mul c₂))).ennreal_toReal
  have hfin : ∀ ω, h ω ≠ ⊤ := fun ω ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  have key := lintegral_le_of_forall_measurableSet (h₁ hxy) hg (fun _ ↦ ENNReal.toReal_nonneg)
    (fun ω ↦ ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact min_le_left _ _))
  simp only [ENNReal.ofReal_toReal (hfin _)] at key
  calc ∫⁻ ω, M₂ x ω (Prod.mk ω ⁻¹' S) ∂M₁ x
      ≤ ∫⁻ ω, (h ω + δ₂) ∂M₁ x := lintegral_mono hpt
    _ = ∫⁻ ω, h ω ∂M₁ x + δ₂ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ c₁ * ∫⁻ ω, h ω ∂M₁ y + δ₁ + δ₂ := by gcongr
    _ ≤ c₁ * ∫⁻ ω, c₂ * M₂ y ω (Prod.mk ω ⁻¹' S) ∂M₁ y + δ₁ + δ₂ := by
        gcongr with ω
        exact min_le_right _ _
    _ = ENNReal.ofReal (Real.exp (ε₁ + ε₂)) * ∫⁻ ω, M₂ y ω (Prod.mk ω ⁻¹' S) ∂M₁ y +
          (δ₁ + δ₂) := by
        rw [lintegral_const_mul _ hmeas, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add, add_assoc]

/-- **Composition of approximate differential privacy, two mechanisms.** If `M₁` is
`(ε₁, δ₁)`-differentially private and `M₂` is `(ε₂, δ₂)`-differentially private, both with values
in probability measures, then running them independently, `x ↦ (M₁ x).prod (M₂ x)`, is
`(ε₁ + ε₂, δ₁ + δ₂)`-differentially private (Dwork and Roth, 2014, Theorem 3.16 for `k = 2`). -/
theorem DifferentiallyPrivate.prod_approx {M₁ : X → Measure Ω} {M₂ : X → Measure Ω'}
    {ε₁ ε₂ : ℝ} {δ₁ δ₂ : ℝ≥0∞} [∀ x, IsProbabilityMeasure (M₁ x)]
    [∀ x, IsProbabilityMeasure (M₂ x)]
    (h₁ : DifferentiallyPrivate Adj M₁ ε₁ δ₁) (h₂ : DifferentiallyPrivate Adj M₂ ε₂ δ₂) :
    DifferentiallyPrivate Adj (fun x ↦ (M₁ x).prod (M₂ x)) (ε₁ + ε₂) (δ₁ + δ₂) := by
  have := h₁.compProd_approx (M₂ := fun x ↦ Kernel.const Ω (M₂ x)) fun ω ↦ by simpa using h₂
  simpa only [Measure.compProd_const] using this

/-- **Composition of pure differential privacy.** If `M₁` is `ε₁`-differentially private and `M₂`
is `ε₂`-differentially private, then running both independently,
`x ↦ (M₁ x).prod (M₂ x)`, is `(ε₁ + ε₂)`-differentially private (Dwork and Roth, 2014,
Theorem 3.14). -/
theorem DifferentiallyPrivate.prod {M₁ : X → Measure Ω} {M₂ : X → Measure Ω'} {ε₁ ε₂ : ℝ}
    [∀ x, SFinite (M₁ x)] [∀ x, SFinite (M₂ x)]
    (h₁ : DifferentiallyPrivate Adj M₁ ε₁ 0) (h₂ : DifferentiallyPrivate Adj M₂ ε₂ 0) :
    DifferentiallyPrivate Adj (fun x ↦ (M₁ x).prod (M₂ x)) (ε₁ + ε₂) 0 := by
  have := h₁.compProd (M₂ := fun x ↦ Kernel.const Ω (M₂ x)) fun ω ↦ by simpa using h₂
  simpa only [Measure.compProd_const] using this

/-- **Basic composition.** Let `M i : X → Measure (Ω i)`, for `i < k`, be
`(ε i, δ i)`-differentially private mechanisms with values in probability measures. Running them
independently, `x ↦ ∏ i, M i x`, is `(∑ i, ε i, ∑ i, δ i)`-differentially private: "the epsilons
and the deltas add up" (Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*,
2014, Theorem 3.16; Corollary 3.15 is the case `δ = 0`). -/
theorem differentiallyPrivate_pi : ∀ {k : ℕ} {Ω : Fin k → Type u} [∀ i, MeasurableSpace (Ω i)]
    {M : ∀ i, X → Measure (Ω i)} [∀ i x, IsProbabilityMeasure (M i x)] {ε : Fin k → ℝ}
    {δ : Fin k → ℝ≥0∞}, (∀ i, DifferentiallyPrivate Adj (M i) (ε i) (δ i)) →
    DifferentiallyPrivate Adj (fun x ↦ Measure.pi fun i ↦ M i x) (∑ i, ε i) (∑ i, δ i)
  | 0, Ω, _, M, _, ε, δ, _ => by
    intro x y _ S _
    have : (fun i ↦ M i x) = fun i ↦ M i y := funext fun i ↦ i.elim0
    simp [this]
  | k + 1, Ω, _, M, _, ε, δ, h => by
    have ih := differentiallyPrivate_pi (Ω := fun j ↦ Ω (Fin.succAbove 0 j))
      (M := fun j ↦ M (Fin.succAbove 0 j)) (ε := fun j ↦ ε (Fin.succAbove 0 j))
      (δ := fun j ↦ δ (Fin.succAbove 0 j)) fun j ↦ h (Fin.succAbove 0 j)
    have hm := ((h 0).prod_approx ih).map (MeasurableEquiv.piFinSuccAbove Ω 0).symm.measurable
    rw [Fin.sum_univ_succAbove _ 0, Fin.sum_univ_succAbove _ 0]
    convert hm using 2 with x
    exact ((measurePreserving_piFinSuccAbove (fun i ↦ M i x) 0).symm _).map_eq.symm

end Cslib.Crypto.Privacy
