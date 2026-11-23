/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Generic chaining: the `γ₂` functional and the chaining upper bound

Let `(X_t)_{t ∈ T}` be a centred process indexed by a metric space `(T, d)` with sub-Gaussian
increments,
`P(|X_s - X_t| ≥ u) ≤ 2 exp(-u² / (2 d(s, t)²))` for all `u > 0` (Talagrand's condition (2.4)).
Talagrand's *generic chaining* bounds the size of the process by the geometry of `T` alone:
`E sup_t X_t ≤ L γ₂(T, d)` with a universal constant `L`, where
`γ₂(T, d) = inf sup_t ∑_{n ≥ 0} 2^{n/2} Δ(A_n(t))`, the infimum running over admissible
sequences of partitions (`card A_0 = 1`, `card A_n ≤ 2^{2^n}`, each partition refining the
previous one), `A_n(t)` is the cell of `A_n` containing `t` and `Δ` is the diameter.

As in the source, the index set is **finite**: Talagrand defines `E sup_{t ∈ T} X_t` for infinite
`T` as the supremum over finite subsets (his (2.2)), so the finite case carries the whole content.

## Main definitions

* `chainingCard n`: `N₀ = 1`, `Nₙ = 2^{2^n}` (Talagrand's (2.29)).
* `AdmissibleSequence T`: an admissible sequence of partitions (Definition 2.7.1), recorded by
  the cell map `t ↦ A_n(t)`.
* `diamWith d A`: the diameter of `A` for an extended-valued distance function `d`.
* `gammaFunctional α d`: Talagrand's functional `γ_α(T, d)` (Definition 2.7.3), valued in
  `ℝ≥0∞` so that it is meaningful for every admissible sequence.
* `SatisfiesIncrementCondition P X`: the sub-Gaussian increment condition (2.4), for a
  probability measure `P`.
* `entropyNumber d n`: Talagrand's entropy numbers `e_n(T)` (2.36).

## Main results

* `lintegral_iSup_sub_le_of_chain`: the chaining argument of Section 2.4 along a finite chain of
  approximation maps, with explicit constant `7`; `ofReal_integral_iSup_le_of_chain` adds the
  centring step (2.5) and is shared by the two bounds below.
* `integral_iSup_le_gammaTwo`, `integral_iSup_le_gammaTwo_toReal`: the generic chaining bound,
  Theorem 2.7.11 (via Theorem 2.7.2), `E sup_t X_t ≤ 10 γ₂(T, d)` for finite `T` (Talagrand's
  universal `L`, made explicit).
* `integral_iSup_le_dudley`: Dudley's entropy bound, Proposition 2.5.1,
  `E sup_t X_t ≤ 17 ∑_n 2^{n/2} e_n(T)`, with `tsum_entropyNumber_lt_top` for its finiteness.
* `two_rpow_mul_entropyNumber_le_gammaTwo`: `2^{n/2} e_n(T) ≤ γ₂(T, d)` (Exercise 2.7.8 (a)).
* `diamWith_univ_le_gammaFunctional`: `Δ(T) ≤ γ_α(T, d)` (remark after Definition 2.7.3).
* `gammaFunctional_lt_top`: `γ_α(T, d) < ∞` for finite `T` and a finite distance.

## References

* M. Talagrand, *Upper and Lower Bounds for Stochastic Processes: Decomposition Theorems*,
  2nd ed., Ergebnisse der Mathematik und ihrer Grenzgebiete 60, Springer 2021: (2.2), (2.4),
  (2.29), Section 2.4 (the bound (2.34)), (2.36), Proposition 2.5.1, Definitions 2.7.1 and 2.7.3,
  Theorems 2.7.2 and 2.7.11.
-/

@[expose] public section

namespace MathlibExt.Probability.GenericChaining

open MeasureTheory Finset
open Real (exp log)
open scoped ENNReal NNReal

variable {T : Type*}

/-- **Cardinality bounds of generic chaining.** `N₀ = 1` and `Nₙ = 2^{2^n}` for `n ≥ 1`
(Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, (2.29)). They
satisfy `Nₙ² ≤ Nₙ₊₁`, so `log Nₙ` doubles at each step. -/
def chainingCard (n : ℕ) : ℕ := if n = 0 then 1 else 2 ^ 2 ^ n

theorem one_le_chainingCard (n : ℕ) : 1 ≤ chainingCard n := by
  unfold chainingCard; split_ifs
  · exact le_rfl
  · exact Nat.one_le_two_pow

theorem chainingCard_le_two_pow (n : ℕ) : chainingCard n ≤ 2 ^ 2 ^ n := by
  unfold chainingCard; split_ifs
  · exact Nat.one_le_two_pow
  · exact le_rfl

theorem chainingCard_mono {m n : ℕ} (h : m ≤ n) : chainingCard m ≤ chainingCard n := by
  unfold chainingCard
  split_ifs with hm hn hn
  · exact le_rfl
  · exact Nat.one_le_two_pow
  · omega
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

/-- **Admissible sequence of partitions** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, Definition 2.7.1). An increasing sequence `(A_n)_{n ≥ 0}` of
partitions of `T` with `card A_n ≤ N_n`, i.e. `card A_0 = 1` and `card A_n ≤ 2^{2^n}` for
`n ≥ 1`; each set of `A_{n+1}` is contained in a set of `A_n`. The partition `A_n` is recorded by
its cell map `t ↦ A_n(t)`, the unique element of `A_n` containing `t`. -/
structure AdmissibleSequence (T : Type*) where
  /-- `cell n t` is `A_n(t)`, the cell of the `n`-th partition containing `t`. -/
  cell : ℕ → T → Set T
  mem_cell : ∀ n t, t ∈ cell n t
  cell_eq_of_mem : ∀ n s t, s ∈ cell n t → cell n s = cell n t
  cell_succ_subset : ∀ n t, cell (n + 1) t ⊆ cell n t
  encard_range_le : ∀ n, (Set.range (cell n)).encard ≤ chainingCard n

namespace AdmissibleSequence

/-- **The first partition is trivial.** In an admissible sequence, `card A_0 ≤ N_0 = 1` forces
`A_0 = {T}`: every cell `A_0(t)` is the whole space. -/
theorem cell_zero (A : AdmissibleSequence T) (t : T) : A.cell 0 t = Set.univ := by
  refine Set.eq_univ_of_forall fun s => ?_
  have h : (Set.range (A.cell 0)).encard ≤ 1 := by simpa [chainingCard] using A.encard_range_le 0
  rw [Set.encard_le_one_iff] at h
  have := h (A.cell 0 s) (A.cell 0 t) ⟨s, rfl⟩ ⟨t, rfl⟩
  exact this ▸ A.mem_cell 0 s

theorem cell_subset_of_le (A : AdmissibleSequence T) {m n : ℕ} (h : m ≤ n) (t : T) :
    A.cell n t ⊆ A.cell m t := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (A.cell_succ_subset n t).trans ih

end AdmissibleSequence

/-- **Diameter for a distance function.** For `d : T → T → ℝ≥0∞` and `A ⊆ T`,
`diamWith d A = sup_{s, t ∈ A} d(s, t)`; for `d = edist` this is `Metric.ediam A`. -/
noncomputable def diamWith (d : T → T → ℝ≥0∞) (A : Set T) : ℝ≥0∞ := ⨆ s ∈ A, ⨆ t ∈ A, d s t

/-- **`diamWith` of the extended distance is the diameter.** For an extended metric space,
`diamWith edist A = Metric.ediam A`. -/
theorem diamWith_edist [EDist T] (A : Set T) :
    diamWith (edist : T → T → ℝ≥0∞) A = Metric.ediam A := rfl

theorem le_diamWith (d : T → T → ℝ≥0∞) {A : Set T} {s t : T} (hs : s ∈ A) (ht : t ∈ A) :
    d s t ≤ diamWith d A :=
  le_iSup₂_of_le s hs (le_iSup₂_of_le t ht le_rfl)

/-- **Talagrand's `γ_α` functional** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, Definition 2.7.3). For `α > 0` and a distance `d` on `T`,
`γ_α(T, d) = inf sup_{t ∈ T} ∑_{n ≥ 0} 2^{n/α} Δ(A_n(t))`, the infimum over all admissible
sequences of partitions. The value lies in `[0, ∞]`; `α = 2` gives `γ₂`. -/
noncomputable def gammaFunctional (α : ℝ) (d : T → T → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ A : AdmissibleSequence T, ⨆ t, ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / α) * diamWith d (A.cell n t)

/-- **The diameter is at most `γ_α`** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, remark after Definition 2.7.3): since `A_0(t) = T`,
`Δ(T, d) ≤ γ_α(T, d)`. -/
theorem diamWith_univ_le_gammaFunctional (α : ℝ) (d : T → T → ℝ≥0∞) :
    diamWith d Set.univ ≤ gammaFunctional α d := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t⟩⟩
  · simp [diamWith]
  refine le_iInf fun A => ?_
  refine le_trans ?_ (le_iSup _ t)
  refine le_trans ?_ (ENNReal.le_tsum 0)
  simp [A.cell_zero]

private theorem diamWith_le_sum [Fintype T] (d : T → T → ℝ≥0∞) (A : Set T) :
    diamWith d A ≤ ∑ s, ∑ t, d s t :=
  iSup₂_le fun s _ => iSup₂_le fun t _ =>
    (Finset.single_le_sum (f := fun t => d s t) (fun _ _ => zero_le) (mem_univ t)).trans
      (Finset.single_le_sum (f := fun s => ∑ t, d s t) (fun _ _ => zero_le) (mem_univ s))

private theorem encard_range_le_card [Fintype T] {β : Type*} (f : T → β) :
    (Set.range f).encard ≤ Fintype.card T := by
  classical
  have : Set.range f = ((Finset.univ.image f : Finset β) : Set β) := by simp
  rw [this, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast Finset.card_image_le.trans (by simp)

/-- **`γ_α` is finite on a finite space** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, Definition 2.7.3; compare Exercise 2.7.5). If `T` is finite and `d`
is a finite distance function vanishing on the diagonal, then `γ_α(T, d) < ∞`: refine to
singletons as soon as `N_n ≥ card T`. -/
theorem gammaFunctional_lt_top [Finite T] (α : ℝ) (d : T → T → ℝ≥0∞)
    (hd : ∀ s t, d s t ≠ ⊤) (hdiag : ∀ t, d t t = 0) : gammaFunctional α d < ⊤ := by
  classical
  have := Fintype.ofFinite T
  let A : AdmissibleSequence T :=
    { cell := fun n t => if Fintype.card T ≤ chainingCard n then {t} else Set.univ
      mem_cell := fun n t => by split_ifs <;> simp
      cell_eq_of_mem := fun n s t hs => by
        split_ifs at hs ⊢ with h
        · rw [Set.mem_singleton_iff.mp hs]
        · rfl
      cell_succ_subset := fun n t => by
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact Set.subset_univ _
        · exact absurd (h2.trans (chainingCard_mono (Nat.le_succ n))) h1
        · exact le_rfl
      encard_range_le := fun n => by
        split_ifs with h
        · exact (encard_range_le_card _).trans (by exact_mod_cast h)
        · rcases isEmpty_or_nonempty T with hT | hT
          · simp [Set.range_eq_empty]
          · rw [Set.range_const]; simpa using one_le_chainingCard n }
  refine lt_of_le_of_lt (iInf_le _ A) ?_
  have hsmall : ∀ n, Fintype.card T ≤ n → Fintype.card T ≤ chainingCard n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · omega
    · unfold chainingCard
      rw [ite_eq_right hpos.ne']
      exact hn.trans ((Nat.lt_two_pow_self).le.trans
        (Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le))
  have hterm : ∀ t, ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / α) * diamWith d (A.cell n t)
      = ∑ n ∈ range (Fintype.card T),
          (2 : ℝ≥0∞) ^ ((n : ℝ) / α) * diamWith d (A.cell n t) := by
    intro t
    refine tsum_eq_sum fun n hn => ?_
    have hn' : Fintype.card T ≤ n := by simpa using hn
    have : A.cell n t = {t} := ite_eq_left (hsmall n hn')
    simp [this, diamWith, hdiag]
  simp_rw [hterm]
  have hfin : ∀ t, ∑ n ∈ range (Fintype.card T),
      (2 : ℝ≥0∞) ^ ((n : ℝ) / α) * diamWith d (A.cell n t) ≤
      ∑ n ∈ range (Fintype.card T), (2 : ℝ≥0∞) ^ ((n : ℝ) / α) * ∑ s, ∑ t, d s t :=
    fun t => Finset.sum_le_sum fun n _ => mul_le_mul_right (diamWith_le_sum d _) _
  refine lt_of_le_of_lt (iSup_le hfin) ?_
  refine ENNReal.sum_lt_top.mpr fun n _ => ENNReal.mul_lt_top ?_ ?_
  · exact (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)).lt_top
  · exact ENNReal.sum_lt_top.mpr fun s _ => ENNReal.sum_lt_top.mpr fun t _ => (hd s t).lt_top

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Sub-Gaussian increment condition** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, (2.4)). For a process `(X_t)_{t ∈ T}` on a probability space
`(Ω, P)`, indexed by a metric space `(T, d)`:
`P(|X_s - X_t| ≥ u) ≤ 2 exp(-u² / (2 d(s, t)²))` for all `s, t ∈ T` and `u > 0`. It holds for a
centred Gaussian process with `d(s, t)² = E(X_s - X_t)²`. `P` must be a probability measure:
`P.real` reads an infinite measure as `0`, so under `∞ • P` every process would satisfy the
condition. -/
def SatisfiesIncrementCondition [PseudoMetricSpace T] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) : Prop :=
  ∀ s t : T, ∀ u : ℝ, 0 < u →
    P.real {ω | u ≤ |X s ω - X t ω|} ≤ 2 * exp (-u ^ 2 / (2 * dist s t ^ 2))

/-- The numerical inequality behind the union bound: for `n = i + 1 ≥ 1` and `v = 3 + j`,
`2^{2^{n+1}} · 2 exp(-v² 2^n / 2) ≤ 2 (1/2)^n (1/2)^j`. -/
private theorem chaining_numeric (i j : ℕ) :
    (2 : ℝ) ^ 2 ^ (i + 2) * (2 * exp (-((3 + j : ℝ) ^ 2 * 2 ^ (i + 1)) / 2)) ≤
      2 * ((1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ j) := by
  set a : ℝ := 2 ^ (i + 1) with ha
  have ha1 : (i + 1 : ℝ) ≤ a := by
    have := Nat.lt_two_pow_self (n := i + 1)
    rw [ha]; exact_mod_cast this.le
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlog : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hpow : (2 : ℝ) ^ 2 ^ (i + 2) = exp (2 * a * log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), ha]
    push_cast; ring_nf
  have hhalf : ∀ m : ℕ, exp (-(m : ℝ)) ≤ (1 / 2 : ℝ) ^ m := by
    intro m
    rw [show -(m : ℝ) = m * (-1) by ring, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ m
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp : 2 * a * log 2 + -((3 + j : ℝ) ^ 2 * a) / 2 ≤ -((i + 1 : ℕ) : ℝ) + -(j : ℝ) := by
    have h1 : 2 * a * log 2 ≤ 2 * a * 0.7 := by
      have : 0 < a := by positivity
      nlinarith
    push_cast
    nlinarith [mul_nonneg hj (by positivity : (0 : ℝ) ≤ a), mul_nonneg (mul_nonneg hj hj)
      (by positivity : (0 : ℝ) ≤ a)]
  calc (2 : ℝ) ^ 2 ^ (i + 2) * (2 * exp (-((3 + j : ℝ) ^ 2 * a) / 2))
      = 2 * exp (2 * a * log 2 + -((3 + j : ℝ) ^ 2 * a) / 2) := by
        rw [hpow, Real.exp_add]; ring
    _ ≤ 2 * exp (-((i + 1 : ℕ) : ℝ) + -(j : ℝ)) := by gcongr
    _ = 2 * (exp (-((i + 1 : ℕ) : ℝ)) * exp (-(j : ℝ))) := by rw [Real.exp_add]
    _ ≤ 2 * ((1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ j) := by
        gcongr
        · exact hhalf _
        · exact hhalf _

/-- `ofReal x ≤ 3 + ∑_j 1{3 + j ≤ x}` for every real `x`. -/
private theorem ofReal_le_three_add_tsum (x : ℝ) :
    ENNReal.ofReal x ≤ 3 + ∑' j : ℕ, ({y : ℝ | (3 + j : ℝ) ≤ y}.indicator (fun _ => 1) x) := by
  by_cases hx : x ≤ 3
  · calc ENNReal.ofReal x ≤ ENNReal.ofReal 3 := ENNReal.ofReal_le_ofReal hx
      _ = 3 := by simp
      _ ≤ _ := le_self_add
  push Not at hx
  set J := ⌊x - 3⌋₊
  have hJ : x - 3 < J + 1 := Nat.lt_floor_add_one _
  have hsum : ((J + 1 : ℕ) : ℝ≥0∞) ≤
      ∑' j : ℕ, ({y : ℝ | (3 + j : ℝ) ≤ y}.indicator (fun _ => 1) x) := by
    calc ((J + 1 : ℕ) : ℝ≥0∞) = ∑ j ∈ range (J + 1), (1 : ℝ≥0∞) := by simp
      _ = ∑ j ∈ range (J + 1), ({y : ℝ | (3 + j : ℝ) ≤ y}.indicator (fun _ => 1) x) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Set.indicator_of_mem]
          have hj' : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have : (j : ℝ) ≤ x - 3 :=
            (Nat.cast_le.mpr hj').trans (Nat.floor_le (by linarith))
          change (3 + j : ℝ) ≤ x
          linarith
      _ ≤ _ := ENNReal.sum_le_tsum _
  calc ENNReal.ofReal x ≤ ENNReal.ofReal (3 + ((J + 1 : ℕ) : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by push_cast; linarith)
    _ = 3 + ((J + 1 : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_natCast]; simp
    _ ≤ _ := add_le_add_right hsum _

/-- **The chaining argument along a finite chain** (Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, 2nd ed., 2021, Section 2.4, proof of (2.34), with `T_n = π_n(T)`).
Let `T` be a finite metric space, `(X_t)` a process with the increment condition (2.4), and
`π_0, …, π_M : T → T` approximation maps with `π_0 ≡ t₀`, `π_M = id`, and, for `1 ≤ n ≤ M`, at
most `2^{2^{n+1}}` distinct pairs `(π_n(t), π_{n-1}(t))` (as when `card π_n(T) ≤ N_n`). Then
`E sup_t (X_t - X_{t₀}) ≤ 7 sup_t ∑_{n=1}^{M} 2^{n/2} d(π_n(t), π_{n-1}(t))`. In Lean the maps
are named `φ`, `2^{n/2}` is written `√2^n`, and the expectation is a lower Lebesgue integral. -/
theorem lintegral_iSup_sub_le_of_chain [MetricSpace T] [Fintype T] [DecidableEq T] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hinc : SatisfiesIncrementCondition P X) (M : ℕ) (hM : 0 < M) (φ : ℕ → T → T) (t₀ : T)
    (h0 : ∀ t, φ 0 t = t₀) (hMid : ∀ t, φ M t = t)
    (hcard : ∀ i < M,
      (Finset.univ.image fun t => (φ (i + 1) t, φ i t)).card ≤ 2 ^ 2 ^ (i + 2)) :
    ∫⁻ ω, ENNReal.ofReal (⨆ t, (X t ω - X t₀ ω)) ∂P ≤
      7 * ENNReal.ofReal (⨆ t, ∑ i ∈ range M, √2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t)) := by
  classical
  have : Nonempty T := ⟨t₀⟩
  have : NeZero M := ⟨hM.ne'⟩
  -- the normalised increments along the chain and their maximum
  set c : ℕ → T → ℝ := fun i t => √2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t) with hc
  set W : Fin M × T → Ω → ℝ := fun p ω =>
    |X (φ (p.1 + 1) p.2) ω - X (φ p.1 p.2) ω| / c p.1 p.2 with hW
  set Z : Ω → ℝ := fun ω => ⨆ p, W p ω with hZ
  set S : ℝ := ⨆ t, ∑ i ∈ range M, c i t with hS
  have hc0 : ∀ i t, 0 ≤ c i t := fun i t => by positivity
  have hW0 : ∀ p ω, 0 ≤ W p ω := fun p ω => div_nonneg (abs_nonneg _) (hc0 _ _)
  have hWZ : ∀ p ω, W p ω ≤ Z ω := fun p ω =>
    le_ciSup (f := fun p => W p ω) (Set.finite_range _).bddAbove p
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => (hW0 (⟨0, hM⟩, t₀) ω).trans (hWZ _ ω)
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun i _ => hc0 i t₀).trans
    (le_ciSup (f := fun t => ∑ i ∈ range M, c i t) (Set.finite_range _).bddAbove t₀)
  have hWmeas : ∀ p, Measurable (W p) := fun p =>
    (continuous_abs.measurable.comp ((hX _).sub (hX _))).div_const _
  have hZmeas : Measurable Z := Measurable.iSup hWmeas
  -- step 1: the pointwise chaining bound `sup_t (X_t - X_{t₀}) ≤ S Z`
  have hpoint : ∀ ω, ⨆ t, (X t ω - X t₀ ω) ≤ S * Z ω := by
    intro ω
    refine ciSup_le fun t => ?_
    have htel : X t ω - X t₀ ω =
        ∑ i ∈ range M, (X (φ (i + 1) t) ω - X (φ i t) ω) := by
      rw [Finset.sum_range_sub (fun i => X (φ i t) ω), hMid, h0]
    have hstep : ∀ i ∈ range M, X (φ (i + 1) t) ω - X (φ i t) ω ≤ c i t * Z ω := by
      intro i hi
      have hi' : i < M := Finset.mem_range.mp hi
      by_cases hci : c i t = 0
      · have hd : dist (φ (i + 1) t) (φ i t) = 0 := by
          rcases mul_eq_zero.mp hci with h | h
          · exact absurd h (pow_ne_zero _ (by positivity))
          · exact h
        rw [dist_eq_zero.mp hd, hci]; simp
      · have hle := hWZ (⟨i, hi'⟩, t) ω
        simp only [hW] at hle
        rw [div_le_iff₀ (lt_of_le_of_ne (hc0 i t) (Ne.symm hci))] at hle
        calc X (φ (i + 1) t) ω - X (φ i t) ω ≤ |X (φ (i + 1) t) ω - X (φ i t) ω| :=
              le_abs_self _
          _ ≤ Z ω * c i t := hle
          _ = c i t * Z ω := mul_comm _ _
    calc X t ω - X t₀ ω ≤ ∑ i ∈ range M, c i t * Z ω := htel ▸ Finset.sum_le_sum hstep
      _ = (∑ i ∈ range M, c i t) * Z ω := by rw [Finset.sum_mul]
      _ ≤ S * Z ω := mul_le_mul_of_nonneg_right
          (le_ciSup (f := fun t => ∑ i ∈ range M, c i t) (Set.finite_range _).bddAbove t) (hZ0 ω)
  -- step 2: the union bound for `P(Z ≥ v)`
  have hunion : ∀ v : ℝ, 0 < v → P {ω | v ≤ Z ω} ≤
      ENNReal.ofReal (∑ i ∈ range M,
        (2 : ℝ) ^ 2 ^ (i + 2) * (2 * exp (-(v ^ 2 * 2 ^ (i + 1)) / 2))) := by
    intro v hv
    set img : ℕ → Finset (T × T) := fun i => Finset.univ.image fun t => (φ (i + 1) t, φ i t)
    set B : ℕ → T × T → Set Ω := fun i q =>
      {ω | v ≤ |X q.1 ω - X q.2 ω| / (√2 ^ (i + 1) * dist q.1 q.2)}
    have hsub : {ω | v ≤ Z ω} ⊆ ⋃ i ∈ range M, ⋃ q ∈ img i, B i q := by
      intro ω hω
      obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p => W p ω)
      simp only [Set.mem_iUnion]
      refine ⟨p.1, Finset.mem_range.mpr p.1.2, (φ (p.1 + 1) p.2, φ p.1 p.2),
        Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩, ?_⟩
      have : v ≤ W p ω := hp ▸ hω
      exact this
    have hB : ∀ i, ∀ q : T × T, P (B i q) ≤
        ENNReal.ofReal (2 * exp (-(v ^ 2 * 2 ^ (i + 1)) / 2)) := by
      intro i q
      by_cases hq : dist q.1 q.2 = 0
      · have : B i q = ∅ := by
          ext ω; simp only [B, hq, mul_zero, div_zero, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_le]; exact hv
        simp [this]
      · have hd : 0 < dist q.1 q.2 := lt_of_le_of_ne dist_nonneg (Ne.symm hq)
        have hk : 0 < √2 ^ (i + 1) * dist q.1 q.2 := by positivity
        have hBeq : B i q = {ω | v * (√2 ^ (i + 1) * dist q.1 q.2) ≤ |X q.1 ω - X q.2 ω|} := by
          ext ω; simp only [B, Set.mem_ofPred_eq, le_div_iff₀ hk]
        rw [hBeq]
        have h := hinc q.1 q.2 (v * (√2 ^ (i + 1) * dist q.1 q.2)) (by positivity)
        have hval : -(v * (√2 ^ (i + 1) * dist q.1 q.2)) ^ 2 / (2 * dist q.1 q.2 ^ 2) =
            -(v ^ 2 * 2 ^ (i + 1)) / 2 := by
          have h2 : (√2 ^ (i + 1)) ^ 2 = 2 ^ (i + 1) := by
            rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
          have hd2 : dist q.1 q.2 ^ 2 ≠ 0 := by positivity
          rw [mul_pow, mul_pow, h2]
          field_simp
        rw [hval] at h
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal h
    calc P {ω | v ≤ Z ω} ≤ P (⋃ i ∈ range M, ⋃ q ∈ img i, B i q) := measure_mono hsub
      _ ≤ ∑ i ∈ range M, P (⋃ q ∈ img i, B i q) := measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ range M, ∑ q ∈ img i, P (B i q) :=
          Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ range M, ∑ q ∈ img i,
            ENNReal.ofReal (2 * exp (-(v ^ 2 * 2 ^ (i + 1)) / 2)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun q _ => hB i q
      _ = ∑ i ∈ range M, ((img i).card : ℝ≥0∞) *
            ENNReal.ofReal (2 * exp (-(v ^ 2 * 2 ^ (i + 1)) / 2)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ range M, ENNReal.ofReal ((2 : ℝ) ^ 2 ^ (i + 2)) *
            ENNReal.ofReal (2 * exp (-(v ^ 2 * 2 ^ (i + 1)) / 2)) := by
          refine Finset.sum_le_sum fun i hi => mul_le_mul_left ?_ _
          have := hcard i (Finset.mem_range.mp hi)
          rw [ENNReal.ofReal_pow (by norm_num)]
          simpa using (show ((img i).card : ℝ≥0∞) ≤ ((2 ^ 2 ^ (i + 2) : ℕ) : ℝ≥0∞) by
            exact_mod_cast this)
      _ = ENNReal.ofReal (∑ i ∈ range M,
            (2 : ℝ) ^ 2 ^ (i + 2) * (2 * exp (-(v ^ 2 * 2 ^ (i + 1)) / 2))) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
  -- step 3: `E Z ≤ 7`
  have hEZ : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ 7 := by
    have hmeasS : ∀ j : ℕ, MeasurableSet {ω | (3 + j : ℝ) ≤ Z ω} := fun j =>
      measurableSet_le measurable_const hZmeas
    calc ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P
        ≤ ∫⁻ ω, (3 + ∑' j : ℕ, {ω | (3 + j : ℝ) ≤ Z ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂P :=
          lintegral_mono fun ω => by
            simpa [Set.indicator] using ofReal_le_three_add_tsum (Z ω)
      _ = 3 + ∑' j : ℕ, P {ω | (3 + j : ℝ) ≤ Z ω} := by
          rw [lintegral_add_left measurable_const, lintegral_tsum fun j =>
            (measurable_const.indicator (hmeasS j)).aemeasurable]
          simp only [lintegral_const, measure_univ, mul_one, ne_eq, ENNReal.ofNat_ne_top,
            not_false_eq_true, add_right_inj_of_ne_top]
          exact tsum_congr fun j => lintegral_indicator_one (hmeasS j)
      _ ≤ 3 + ∑' j : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) := by
          refine add_le_add_right (ENNReal.tsum_le_tsum fun j => ?_) _
          refine (hunion (3 + j) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
          calc ∑ i ∈ range M, (2 : ℝ) ^ 2 ^ (i + 2) *
                (2 * exp (-((3 + j : ℝ) ^ 2 * 2 ^ (i + 1)) / 2))
              ≤ ∑ i ∈ range M, 2 * ((1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ j) :=
                Finset.sum_le_sum fun i _ => chaining_numeric i j
            _ = 2 * (1 / 2 : ℝ) ^ j * ((1 / 2) * ∑ i ∈ range M, (1 / 2 : ℝ) ^ i) := by
                rw [Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by ring
            _ ≤ 2 * (1 / 2 : ℝ) ^ j * 1 := by
                gcongr
                linarith [sum_geometric_two_le M]
            _ = 2 * (1 / 2 : ℝ) ^ j := mul_one _
      _ = 3 + 4 := by
          congr 1
          have : ∀ j : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) = 2 * 2⁻¹ ^ j := by
            intro j
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
            simp [ENNReal.ofReal_inv_of_pos]
          simp_rw [this]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
          norm_num
      _ = 7 := by norm_num
  -- step 4: combine
  calc ∫⁻ ω, ENNReal.ofReal (⨆ t, (X t ω - X t₀ ω)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal S * ENNReal.ofReal (Z ω) ∂P :=
        lintegral_mono fun ω => by
          rw [← ENNReal.ofReal_mul hS0]; exact ENNReal.ofReal_le_ofReal (hpoint ω)
    _ = ENNReal.ofReal S * ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal S * 7 := mul_le_mul_right hEZ _
    _ = 7 * ENNReal.ofReal S := mul_comm _ _

/-- **The chaining bound for a centred process** (Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, 2nd ed., 2021, (2.5) and (2.34)). Under the hypotheses of
`lintegral_iSup_sub_le_of_chain`, if moreover every `X_t` is integrable and centred, then
`E sup_t X_t = E sup_t (X_t - X_{t₀})` and
`E sup_t X_t ≤ 7 sup_t ∑_{n=1}^{M} 2^{n/2} d(π_n(t), π_{n-1}(t))`. -/
theorem ofReal_integral_iSup_le_of_chain [MetricSpace T] [Fintype T] [DecidableEq T]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hint : ∀ t, Integrable (X t) P) (hcen : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hinc : SatisfiesIncrementCondition P X) (M : ℕ) (hM : 0 < M) (φ : ℕ → T → T) (t₀ : T)
    (h0 : ∀ t, φ 0 t = t₀) (hMid : ∀ t, φ M t = t)
    (hcard : ∀ i < M,
      (Finset.univ.image fun t => (φ (i + 1) t, φ i t)).card ≤ 2 ^ 2 ^ (i + 2)) :
    ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤
      7 * ENNReal.ofReal (⨆ t, ∑ i ∈ range M, √2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t)) := by
  have : Nonempty T := ⟨t₀⟩
  have hcore := lintegral_iSup_sub_le_of_chain P X hX hinc M hM φ t₀ h0 hMid hcard
  have hY0 : ∀ ω, 0 ≤ ⨆ t, (X t ω - X t₀ ω) := fun ω =>
    (by simp : (0 : ℝ) ≤ X t₀ ω - X t₀ ω).trans
      (le_ciSup (f := fun t => X t ω - X t₀ ω) (Set.finite_range _).bddAbove t₀)
  have hYeq : ∀ ω, ⨆ t, (X t ω - X t₀ ω) = (⨆ t, X t ω) - X t₀ ω := fun ω => by
    refine le_antisymm (ciSup_le fun t => sub_le_sub_right
      (le_ciSup (f := fun t => X t ω) (Set.finite_range _).bddAbove t) _) ?_
    rw [sub_le_iff_le_add]
    refine ciSup_le fun t => ?_
    rw [← sub_le_iff_le_add]
    exact le_ciSup (f := fun t => X t ω - X t₀ ω) (Set.finite_range _).bddAbove t
  by_cases hsup : Integrable (fun ω => ⨆ t, X t ω) P
  · have hYint : Integrable (fun ω => ⨆ t, (X t ω - X t₀ ω)) P := by
      simp_rw [hYeq]; exact hsup.sub (hint t₀)
    have hInt : ∫ ω, ⨆ t, X t ω ∂P = ∫ ω, ⨆ t, (X t ω - X t₀ ω) ∂P := by
      simp_rw [hYeq]; rw [integral_sub hsup (hint t₀), hcen, sub_zero]
    rw [hInt, ofReal_integral_eq_lintegral_ofReal hYint (Filter.Eventually.of_forall hY0)]
    exact hcore
  · rw [integral_undef hsup, ENNReal.ofReal_zero]; exact bot_le


private theorem two_rpow_half (n : ℕ) :
    (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) = ENNReal.ofReal (√2 ^ n) := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- **Generic chaining bound** (Talagrand, *Upper and Lower Bounds for Stochastic Processes*,
2nd ed., 2021, Theorem 2.7.11, through Theorem 2.7.2 and (2.34)). Let `T` be a finite nonempty
metric space and `(X_t)_{t ∈ T}` a process of integrable, centred (`E X_t = 0`) random variables
satisfying the increment condition (2.4). Then
`E sup_{t ∈ T} X_t ≤ L γ₂(T, d)` with `L = 10`. -/
theorem integral_iSup_le_gammaTwo [MetricSpace T] [Finite T] [Nonempty T] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hint : ∀ t, Integrable (X t) P) (hcen : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hinc : SatisfiesIncrementCondition P X) :
    ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤ 10 * gammaFunctional 2 (edist : T → T → ℝ≥0∞) := by
  classical
  have := Fintype.ofFinite T
  rw [gammaFunctional, ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun A => ?_
  set SA := ⨆ t, ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * diamWith edist (A.cell n t)
  by_cases hSA : SA = ⊤
  · rw [hSA, ENNReal.mul_top (by norm_num)]; exact le_top
  -- representatives of the cells
  let f : Set T → T := fun C => if h : C.Nonempty then h.some else Classical.arbitrary T
  have hf : ∀ C : Set T, C.Nonempty → f C ∈ C := fun C h => by
    simp only [f, dite_eq_left h]; exact h.some_mem
  let rep : ℕ → T → T := fun n t => f (A.cell n t)
  have hrep : ∀ n t, rep n t ∈ A.cell n t := fun n t => hf _ ⟨t, A.mem_cell n t⟩
  set M := Fintype.card T + 1 with hMdef
  let φ : ℕ → T → T := fun n t => if n < M then rep n t else t
  set t₀ := f Set.univ
  have h0 : ∀ t, φ 0 t = t₀ := fun t => by simp [φ, M, rep, A.cell_zero, t₀]
  have hMid : ∀ t, φ M t = t := fun t => by simp [φ]
  have hrepcard : ∀ n, (Finset.univ.image (rep n)).card ≤ 2 ^ 2 ^ n := by
    intro n
    refine le_trans ?_ (chainingCard_le_two_pow n)
    have h1 : Finset.univ.image (rep n) = (Finset.univ.image (A.cell n)).image f := by
      rw [Finset.image_image]; rfl
    rw [h1]
    refine Finset.card_image_le.trans ?_
    have h2 := A.encard_range_le n
    have : Set.range (A.cell n) = ((Finset.univ.image (A.cell n) : Finset (Set T)) : Set (Set T)) :=
      by simp
    rw [this, Set.encard_coe_eq_coe_finsetCard] at h2
    exact_mod_cast h2
  have hcard : ∀ i < M,
      (Finset.univ.image fun t => (φ (i + 1) t, φ i t)).card ≤ 2 ^ 2 ^ (i + 2) := by
    intro i hi
    by_cases hi1 : i + 1 < M
    · have hsub : (Finset.univ.image fun t => (φ (i + 1) t, φ i t)) ⊆
          (Finset.univ.image (rep (i + 1))) ×ˢ (Finset.univ.image (rep i)) := by
        intro q hq
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hq
        simp [φ, hi1, hi]
      refine (Finset.card_le_card hsub).trans ?_
      rw [Finset.card_product]
      calc _ ≤ 2 ^ 2 ^ (i + 1) * 2 ^ 2 ^ i := Nat.mul_le_mul (hrepcard _) (hrepcard _)
        _ ≤ 2 ^ 2 ^ (i + 1) * 2 ^ 2 ^ (i + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ i)))
        _ = 2 ^ 2 ^ (i + 2) := by rw [← pow_add]; congr 1; ring
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ]
      have hiM : i + 1 = M := by omega
      have h1 : Fintype.card T < 2 ^ Fintype.card T := Nat.lt_two_pow_self
      have h2 : Fintype.card T ≤ 2 ^ (i + 2) :=
        (Nat.lt_two_pow_self (n := Fintype.card T)).le.trans
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) h2)
  -- bound the chain sum by `√2 · SA`
  have hchain : ENNReal.ofReal (⨆ t, ∑ i ∈ range M, √2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t))
      ≤ ENNReal.ofReal √2 * SA := by
    rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSA)]
    refine ciSup_le fun t => ?_
    rw [← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSA),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    calc ∑ i ∈ range M, ENNReal.ofReal (√2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t))
        ≤ ∑ i ∈ range M, ENNReal.ofReal √2 *
            ((2 : ℝ≥0∞) ^ ((i : ℝ) / 2) * diamWith edist (A.cell i t)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hiM : i < M := Finset.mem_range.mp hi
          have hmem1 : φ (i + 1) t ∈ A.cell i t := by
            by_cases hi1 : i + 1 < M
            · simp only [φ, ite_eq_left hi1]; exact A.cell_succ_subset i t (hrep _ _)
            · simp only [φ, ite_eq_right hi1]; exact A.mem_cell i t
          have hmem2 : φ i t ∈ A.cell i t := by simp only [φ, ite_eq_left hiM]; exact hrep _ _
          rw [ENNReal.ofReal_mul (by positivity), ← edist_dist, two_rpow_half, pow_succ,
            ENNReal.ofReal_mul (by positivity)]
          calc ENNReal.ofReal (√2 ^ i) * ENNReal.ofReal √2 * edist (φ (i + 1) t) (φ i t)
              ≤ ENNReal.ofReal (√2 ^ i) * ENNReal.ofReal √2 * diamWith edist (A.cell i t) :=
                mul_le_mul_right (le_diamWith edist hmem1 hmem2) _
            _ = _ := by ring
      _ = ENNReal.ofReal √2 * ∑ i ∈ range M,
            (2 : ℝ≥0∞) ^ ((i : ℝ) / 2) * diamWith edist (A.cell i t) := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal √2 * SA := by
          refine mul_le_mul_right ?_ _
          exact (ENNReal.sum_le_tsum _).trans (le_iSup
            (fun t => ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * diamWith edist (A.cell n t)) t)
  have hsqrt : ENNReal.ofReal √2 * 7 ≤ 10 := by
    rw [show (7 : ℝ≥0∞) = ENNReal.ofReal 7 by simp, ← ENNReal.ofReal_mul (by positivity),
      show (10 : ℝ≥0∞) = ENNReal.ofReal 10 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  calc ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P)
      ≤ 7 * ENNReal.ofReal (⨆ t, ∑ i ∈ range M, √2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t)) :=
        ofReal_integral_iSup_le_of_chain P X hX hint hcen hinc M (by omega) φ t₀ h0 hMid hcard
    _ ≤ 7 * (ENNReal.ofReal √2 * SA) := mul_le_mul_right hchain _
    _ = (ENNReal.ofReal √2 * 7) * SA := by ring
    _ ≤ 10 * SA := mul_le_mul_left hsqrt _

/-- **Generic chaining bound, real form** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, Theorem 2.7.11). Under the hypotheses of `integral_iSup_le_gammaTwo`,
`E sup_{t ∈ T} X_t ≤ 10 γ₂(T, d)` as real numbers; `γ₂(T, d)` is finite because `T` is. -/
theorem integral_iSup_le_gammaTwo_toReal [MetricSpace T] [Finite T] [Nonempty T] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hint : ∀ t, Integrable (X t) P) (hcen : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hinc : SatisfiesIncrementCondition P X) :
    ∫ ω, ⨆ t, X t ω ∂P ≤ 10 * (gammaFunctional 2 (edist : T → T → ℝ≥0∞)).toReal := by
  have hfin := gammaFunctional_lt_top 2 (edist : T → T → ℝ≥0∞) (fun _ _ => edist_ne_top _ _)
    (fun _ => edist_self _)
  have h := integral_iSup_le_gammaTwo P X hX hint hcen hinc
  rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top (by norm_num) hfin.ne),
    ENNReal.toReal_mul] at h
  simpa using h

/-- **Entropy numbers** (Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed.,
2021, (2.36)). `e_n(T) = inf_{T_n ⊆ T, card T_n ≤ N_n} sup_{t ∈ T} d(t, T_n)`: the smallest radius
`r` such that `T` is covered by at most `N_n` balls of radius `r` centred in `T`. The value lies
in `[0, ∞]`; Talagrand's `e_n` is `e_{2^n}` in the convention of operator theory. -/
noncomputable def entropyNumber (d : T → T → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (F : Finset T) (_ : F.card ≤ chainingCard n), ⨆ t, ⨅ s ∈ F, d t s

/-- **Entropy numbers from Mathlib covers** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, the reformulation of (2.36) by coverings with balls). If `T` has an
internal `ε`-cover in the sense of Mathlib's `Metric.IsCover` by a finite set of at most `N_n`
points, then `e_n(T) ≤ ε`. This connects (2.36) with Mathlib's `Metric.coveringNumber`, the
least cardinality of such a cover. -/
theorem entropyNumber_le_of_isCover [PseudoEMetricSpace T] {n : ℕ} {ε : ℝ≥0} {F : Finset T}
    (hF : F.card ≤ chainingCard n) (hC : Metric.IsCover ε Set.univ (F : Set T)) :
    entropyNumber (edist : T → T → ℝ≥0∞) n ≤ ε := by
  refine (iInf₂_le F hF).trans (iSup_le fun t => ?_)
  obtain ⟨y, hy, hty⟩ := hC (Set.mem_univ t)
  exact (iInf₂_le y hy).trans hty

/-- **Dudley's entropy bound** (Talagrand, *Upper and Lower Bounds for Stochastic Processes*,
2nd ed., 2021, Proposition 2.5.1, from (2.34)). Let `T` be a finite nonempty metric space and
`(X_t)_{t ∈ T}` a process of integrable, centred random variables satisfying the increment
condition (2.4). Then `E sup_{t ∈ T} X_t ≤ L ∑_{n ≥ 0} 2^{n/2} e_n(T)` with `L = 17`. -/
theorem integral_iSup_le_dudley [MetricSpace T] [Finite T] [Nonempty T] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hint : ∀ t, Integrable (X t) P) (hcen : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hinc : SatisfiesIncrementCondition P X) :
    ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤
      17 * ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * entropyNumber (edist : T → T → ℝ≥0∞) n := by
  classical
  have := Fintype.ofFinite T
  set e : ℕ → ℝ≥0∞ := entropyNumber (edist : T → T → ℝ≥0∞) with he
  set S := ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * e n with hSdef
  by_cases hS : S = ⊤
  · rw [hS, ENNReal.mul_top (by norm_num)]; exact le_top
  -- the value of a finite set of centres
  let val : Finset T → ℝ≥0∞ := fun F => ⨆ t, ⨅ s ∈ F, edist t s
  -- optimal centres at every level
  have hopt : ∀ n, ∃ F : Finset T, F.card ≤ chainingCard n ∧ val F = e n := by
    intro n
    have : Nonempty {F : Finset T // F.card ≤ chainingCard n} := ⟨⟨∅, by simp⟩⟩
    obtain ⟨⟨F, hF⟩, hFeq⟩ :=
      exists_eq_ciInf_of_finite (f := fun F : {F : Finset T // F.card ≤ chainingCard n} => val F)
    refine ⟨F, hF, ?_⟩
    rw [hFeq, he, entropyNumber, iInf_subtype']
  choose F hFcard hFval using hopt
  have hen : ∀ n, e n ≠ ⊤ := by
    intro n hn
    have hle : (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * e n ≤ S :=
      ENNReal.le_tsum (f := fun n : ℕ => (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * e n) n
    rw [hn, ENNReal.mul_top (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'] at hle
    exact hS (top_le_iff.mp hle)
  have hFne : ∀ n, (F n).Nonempty := by
    intro n
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : val (F n) = ⊤ := by simp [val, hne]
    exact hen n (hFval n ▸ this)
  -- nearest centres
  have hnear : ∀ n t, ∃ s ∈ F n, edist t s ≤ e n := by
    intro n t
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image (F n) (edist t) (hFne n)
    refine ⟨s, hs, ?_⟩
    calc edist t s ≤ ⨅ s' ∈ F n, edist t s' := le_iInf₂ fun s' hs' => hmin s' hs'
      _ ≤ val (F n) := le_iSup (fun t => ⨅ s' ∈ F n, edist t s') t
      _ = e n := hFval n
  choose near hnearF hneare using hnear
  set M := Fintype.card T + 1 with hMdef
  let φ : ℕ → T → T := fun n t => if n < M then near n t else t
  obtain ⟨c, hc⟩ : ∃ c, F 0 = {c} := by
    refine Finset.card_eq_one.mp (le_antisymm ?_ (Finset.card_pos.mpr (hFne 0)))
    simpa [chainingCard] using hFcard 0
  have h0 : ∀ t, φ 0 t = c := fun t => by
    have := hnearF 0 t
    rw [hc, Finset.mem_singleton] at this
    simp [φ, M, this]
  have hMid : ∀ t, φ M t = t := fun t => by simp [φ]
  have hFcard' : ∀ n, (F n).card ≤ 2 ^ 2 ^ n := fun n =>
    (hFcard n).trans (chainingCard_le_two_pow n)
  have hcard : ∀ i < M,
      (Finset.univ.image fun t => (φ (i + 1) t, φ i t)).card ≤ 2 ^ 2 ^ (i + 2) := by
    intro i hi
    by_cases hi1 : i + 1 < M
    · have hsub : (Finset.univ.image fun t => (φ (i + 1) t, φ i t)) ⊆ F (i + 1) ×ˢ F i := by
        intro q hq
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hq
        simp only [φ, ite_eq_left hi1, ite_eq_left hi, Finset.mem_product]
        exact ⟨hnearF _ _, hnearF _ _⟩
      refine (Finset.card_le_card hsub).trans ?_
      rw [Finset.card_product]
      calc _ ≤ 2 ^ 2 ^ (i + 1) * 2 ^ 2 ^ i := Nat.mul_le_mul (hFcard' _) (hFcard' _)
        _ ≤ 2 ^ 2 ^ (i + 1) * 2 ^ 2 ^ (i + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ i)))
        _ = 2 ^ 2 ^ (i + 2) := by rw [← pow_add]; congr 1; ring
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ]
      have h1 : Fintype.card T < 2 ^ Fintype.card T := Nat.lt_two_pow_self
      have h2 : Fintype.card T ≤ 2 ^ (i + 2) :=
        (Nat.lt_two_pow_self (n := Fintype.card T)).le.trans
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) h2)
  have hcore := ofReal_integral_iSup_le_of_chain P X hX hint hcen hinc M (by omega) φ c h0 hMid
    hcard
  -- every link is at most `e_{n} + e_{n-1}`
  have hlink : ∀ i < M, ∀ t, edist (φ (i + 1) t) (φ i t) ≤ e (i + 1) + e i := by
    intro i hi t
    have h2 : edist t (φ i t) ≤ e i := by simp only [φ, ite_eq_left hi]; exact hneare i t
    have h1 : edist (φ (i + 1) t) t ≤ e (i + 1) := by
      by_cases hi1 : i + 1 < M
      · simp only [φ, ite_eq_left hi1]; rw [edist_comm]; exact hneare _ t
      · simp only [φ, ite_eq_right hi1, edist_self]; exact zero_le
    exact (edist_triangle _ t _).trans (add_le_add h1 h2)
  have hrpow : ∀ n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) = ENNReal.ofReal (√2 ^ n) := two_rpow_half
  have hchain : ENNReal.ofReal (⨆ t, ∑ i ∈ range M, √2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t))
      ≤ (1 + ENNReal.ofReal √2) * S := by
    have hfin : (1 + ENNReal.ofReal √2) * S ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨by norm_num, ENNReal.ofReal_ne_top⟩) hS
    rw [ENNReal.ofReal_le_iff_le_toReal hfin]
    refine ciSup_le fun t => ?_
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    set f : ℕ → ℝ≥0∞ := fun n => (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * e n with hf
    calc ∑ i ∈ range M, ENNReal.ofReal (√2 ^ (i + 1) * dist (φ (i + 1) t) (φ i t))
        ≤ ∑ i ∈ range M, (f (i + 1) + ENNReal.ofReal √2 * f i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [ENNReal.ofReal_mul (by positivity), ← edist_dist]
          calc ENNReal.ofReal (√2 ^ (i + 1)) * edist (φ (i + 1) t) (φ i t)
              ≤ ENNReal.ofReal (√2 ^ (i + 1)) * (e (i + 1) + e i) :=
                mul_le_mul_right (hlink i (Finset.mem_range.mp hi) t) _
            _ = f (i + 1) + ENNReal.ofReal √2 * f i := by
                rw [hf]; dsimp only
                rw [hrpow, hrpow, mul_add, pow_succ', ENNReal.ofReal_mul (by positivity)]
                ring
      _ = ∑ i ∈ range M, f (i + 1) + ENNReal.ofReal √2 * ∑ i ∈ range M, f i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ S + ENNReal.ofReal √2 * S := by
          gcongr
          · calc ∑ i ∈ range M, f (i + 1) ≤ ∑ i ∈ range (M + 1), f i := by
                  rw [Finset.sum_range_succ' f M]; exact le_self_add
              _ ≤ S := ENNReal.sum_le_tsum _
          · exact ENNReal.sum_le_tsum _
      _ = (1 + ENNReal.ofReal √2) * S := by ring
  have hconst : 7 * (1 + ENNReal.ofReal √2) ≤ 17 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_add (by norm_num)
      (by positivity), show (7 : ℝ≥0∞) = ENNReal.ofReal 7 by simp,
      ← ENNReal.ofReal_mul (by norm_num), show (17 : ℝ≥0∞) = ENNReal.ofReal 17 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  calc ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤ 7 * ((1 + ENNReal.ofReal √2) * S) :=
        hcore.trans (mul_le_mul_right hchain _)
    _ = 7 * (1 + ENNReal.ofReal √2) * S := by ring
    _ ≤ 17 * S := mul_le_mul_left hconst _

/-- **Dudley's sum is finite on a finite space** (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, (2.36)). For a finite metric space, `e_n(T) = 0` as soon as
`N_n ≥ card T` (take `T_n = T`), and every `e_n(T)` is finite, so
`∑_{n ≥ 0} 2^{n/2} e_n(T) < ∞` and Dudley's bound is not vacuous. -/
theorem tsum_entropyNumber_lt_top [MetricSpace T] [Finite T] :
    ∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * entropyNumber (edist : T → T → ℝ≥0∞) n < ⊤ := by
  classical
  have := Fintype.ofFinite T
  have hzero : ∀ n, Fintype.card T ≤ n → entropyNumber (edist : T → T → ℝ≥0∞) n = 0 := by
    intro n hn
    have hcardn : Fintype.card T ≤ chainingCard n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · omega
      · unfold chainingCard
        rw [ite_eq_right (hpos.ne')]
        exact hn.trans ((Nat.lt_two_pow_self).le.trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le))
    refine le_antisymm ?_ zero_le
    refine (iInf₂_le (Finset.univ : Finset T) (by simpa using hcardn)).trans ?_
    exact iSup_le fun t => (iInf₂_le t (Finset.mem_univ t)).trans (by simp)
  have hfin : ∀ n, entropyNumber (edist : T → T → ℝ≥0∞) n < ⊤ := by
    intro n
    rcases isEmpty_or_nonempty T with hT | ⟨⟨c⟩⟩
    · refine lt_of_le_of_lt (iInf₂_le (∅ : Finset T) (by simp)) ?_
      simp
    refine lt_of_le_of_lt (iInf₂_le ({c} : Finset T) (by simpa using one_le_chainingCard n)) ?_
    refine lt_of_le_of_lt (iSup_le fun t => (iInf₂_le c (Finset.mem_singleton_self c)).trans
      (Finset.single_le_sum (f := fun t => edist t c) (fun _ _ => zero_le) (Finset.mem_univ t)))
      ?_
    exact ENNReal.sum_lt_top.mpr fun t _ => edist_lt_top t c
  rw [tsum_eq_sum (s := range (Fintype.card T)) fun n hn => by
    rw [hzero n (by simpa using hn), mul_zero]]
  refine ENNReal.sum_lt_top.mpr fun n _ => ENNReal.mul_lt_top ?_ (hfin n)
  exact (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)).lt_top

/-- **Entropy numbers are controlled by `γ₂`** (Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, 2nd ed., 2021, Exercise 2.7.8 (a), (2.57)). For every distance function
`d` and every `n`, `2^{n/2} e_n(T) ≤ γ₂(T, d)`: one point from each cell of `A_n` gives at most
`N_n` centres within `Δ(A_n(t))` of every `t`. Here the constant is `1`. -/
theorem two_rpow_mul_entropyNumber_le_gammaTwo (d : T → T → ℝ≥0∞) (n : ℕ) :
    (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * entropyNumber d n ≤ gammaFunctional 2 d := by
  classical
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · have : entropyNumber d n = 0 :=
      le_antisymm ((iInf₂_le (∅ : Finset T) (by simp)).trans (by simp)) zero_le
    simp [this]
  refine le_iInf fun A => ?_
  let f : Set T → T := fun C => if h : C.Nonempty then h.some else t₀
  have hf : ∀ t, f (A.cell n t) ∈ A.cell n t := fun t => by
    have h : (A.cell n t).Nonempty := ⟨t, A.mem_cell n t⟩
    simp only [f, dite_eq_left h]; exact h.some_mem
  have hfin : (Set.range (A.cell n)).Finite :=
    Set.finite_of_encard_le_coe (A.encard_range_le n)
  let F : Finset T := (hfin.image f).toFinset
  have hFcard : F.card ≤ chainingCard n := by
    have h1 : (F.card : ℕ∞) = (f '' Set.range (A.cell n)).encard := by
      rw [← Set.encard_coe_eq_coe_finsetCard]; simp [F]
    have h2 : (F.card : ℕ∞) ≤ chainingCard n :=
      h1 ▸ (Set.encard_image_le f _).trans (A.encard_range_le n)
    exact_mod_cast h2
  have hmem : ∀ t, f (A.cell n t) ∈ F := fun t => by
    simp only [F, Set.Finite.mem_toFinset]; exact ⟨A.cell n t, ⟨t, rfl⟩, rfl⟩
  have he : entropyNumber d n ≤ ⨆ t, diamWith d (A.cell n t) := by
    refine (iInf₂_le F hFcard).trans (iSup_mono fun t => ?_)
    exact (iInf₂_le _ (hmem t)).trans (le_diamWith d (A.mem_cell n t) (hf t))
  calc (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * entropyNumber d n
      ≤ (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * ⨆ t, diamWith d (A.cell n t) := mul_le_mul_right he _
    _ = ⨆ t, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * diamWith d (A.cell n t) := ENNReal.mul_iSup _ _
    _ ≤ ⨆ t, ∑' k : ℕ, (2 : ℝ≥0∞) ^ ((k : ℝ) / 2) * diamWith d (A.cell k t) :=
        iSup_mono fun t => ENNReal.le_tsum
          (f := fun k : ℕ => (2 : ℝ≥0∞) ^ ((k : ℝ) / 2) * diamWith d (A.cell k t)) n

end MathlibExt.Probability.GenericChaining
