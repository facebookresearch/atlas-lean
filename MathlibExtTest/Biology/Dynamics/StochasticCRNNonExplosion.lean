/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

/-! Tests for the Foster–Lyapunov non-explosion criterion for stochastic reaction networks.

* The linear birth–death–immigration network `∅ → X`, `X → 2X`, `X → ∅` (propensities `1`,
  `2x`, `3x`): the generator of `V(x) = x` is computed from the definitions (`L V = 1 - x`), the
  drift bound `L V ≤ 0 · V + 1` holds, and the chain is non-explosive. `V + 1` satisfies
  `L (V + 1) ≤ 1 · (V + 1)`, which gives the fixed-time moment bound `E[X_t + 1] ≤ e^t (x₀ + 1)`.
* The subcritical linear birth–death network `X → 2X`, `X → ∅` (propensities `2x`, `3x`):
  `L V = -x ≤ 0`, so the first moment stays bounded, `E[X_t] ≤ x₀` for every `t`, and the chain
  reaches `{X ≥ m}` by time `t` with probability at most `x₀ / m`. The empty state is absorbing:
  its holding rate is the fictitious `1` and its jump kernel is `δ_0` (boundary values from the
  definitions).
* The dimerization `2A ⇌ B` (propensities `a (a - 1)` and `4 b`, quadratic): `V = a + 2b` is
  conserved (`L V = 0`), so the chain is non-explosive despite the superlinear propensity.
* The autocatalytic network `2X → 3X` with superlinear propensity `x (x - 1)`: for `V(x) = x`,
  `L V(x) = x (x - 1)`, and no bound `L V ≤ a V + b` holds. The criterion does not apply and no
  non-explosion (or explosion) statement is made. -/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace MathlibExtTest.Biology.Dynamics.StochasticCRNNonExplosion

open MathlibExt.Biology.Dynamics
open MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

/-! ### Birth–death–immigration -/

/-- `∅ → X`, `X → 2X`, `X → ∅` on the single species `X = 0`. -/
def bdiNet : ComplexBalanced.ReactionNetwork (Fin 1) (Fin 3) where
  src := ![![0], ![1], ![1]]
  prod := ![![1], ![2], ![0]]

/-- Immigration at rate `1`, birth at rate `2x`, death at rate `3x`. -/
noncomputable def bdi : StochasticCRN (Fin 1) (Fin 3) where
  network := bdiNet
  propensity := fun r x => ![1, 2 * (x 0 : ℝ), 3 * (x 0 : ℝ)] r
  propensity_nonneg := by
    intro r x; fin_cases r <;> simp
  propensity_eq_zero := by
    intro r x h
    have h0 : r ≠ 0 → x 0 = 0 := fun hr => by
      by_contra hx
      apply h
      rw [Pi.le_def]
      intro s
      fin_cases s
      fin_cases r <;> simp_all [bdiNet] <;> omega
    fin_cases r
    · exact absurd (Pi.le_def.2 fun s => by fin_cases s; simp [bdiNet]) h
    · simp [h0 (by decide)]
    · simp [h0 (by decide)]

/-- The count of `X`, as a Lyapunov function. -/
def count (x : Fin 1 → ℕ) : ℝ≥0 := (x 0 : ℝ≥0)

/-- The generator of the count, computed from the definitions: `L V(x) = 1 + 2x - 3x`. -/
theorem bdi_generator (x : Fin 1 → ℕ) :
    bdi.generator (fun y => (count y : ℝ)) x = 1 - x 0 := by
  simp only [StochasticCRN.generator, Fin.sum_univ_three, bdi, StochasticCRN.jump, bdiNet,
    count, NNReal.coe_natCast]
  rcases Nat.eq_zero_or_pos (x 0) with h | h
  · simp [h, Matrix.vecHead]
  · obtain ⟨n, hn⟩ : ∃ n, x 0 = n + 1 := ⟨x 0 - 1, by omega⟩
    simp [hn, Matrix.vecHead]
    ring

/-- The drift bound `L V ≤ 0 · V + 1`. -/
theorem bdi_drift (x : Fin 1 → ℕ) :
    bdi.generator (fun y => (count y : ℝ)) x ≤ 0 * count x + 1 := by
  rw [bdi_generator]
  simp [count]

/-- **Non-explosion of birth–death–immigration**, from every initial state. -/
theorem bdi_nonexplosive (x₀ : Fin 1 → ℕ) :
    ∀ᵐ ω ∂bdi.inputMeasure, Tendsto (bdi.jumpTime x₀ ω) atTop atTop :=
  bdi.ae_tendsto_jumpTime_atTop_of_coercive count le_rfl zero_le_one bdi_drift
    (fun x => by simp [count]) x₀

/-- `V + 1` satisfies the drift bound `L (V + 1) ≤ 1 · (V + 1)` with no constant. -/
theorem bdi_drift_succ (x : Fin 1 → ℕ) :
    bdi.generator (fun y => ((count y + 1 : ℝ≥0) : ℝ)) x ≤ 1 * (count x + 1 : ℝ≥0) := by
  have h := bdi.generator_add_const (fun y => (count y : ℝ)) 1 x
  simp only [NNReal.coe_add, NNReal.coe_one]
  rw [h, bdi_generator]
  simp only [count, NNReal.coe_natCast, one_mul]
  linarith [Nat.cast_nonneg (α := ℝ) (x 0)]

/-- Total propensity is bounded on sublevel sets of `V + 1`. -/
theorem bdi_bdd (m : ℝ) :
    ∃ K, ∀ x, ((count x + 1 : ℝ≥0) : ℝ) < m → bdi.totalRate x ≤ K :=
  bdi.bddRate_of_coercive _ (fun x => by simp [count]) m

/-- **Linear case, moments stay bounded**: `E[X_t + 1] ≤ e^t (x₀ + 1)` for `t ≥ 0`. -/
theorem bdi_moment (x₀ : Fin 1 → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ((count (bdi.path x₀ ω t) + 1 : ℝ≥0) : ℝ≥0∞) ∂bdi.inputMeasure ≤
      ENNReal.ofReal (Real.exp (1 * t)) * (count x₀ + 1 : ℝ≥0) :=
  bdi.lintegral_path_le (fun y => count y + 1) zero_le_one bdi_drift_succ bdi_bdd x₀ ht

/-! ### Subcritical linear birth–death -/

/-- `X → 2X`, `X → ∅`. -/
def bdNet : ComplexBalanced.ReactionNetwork (Fin 1) (Fin 2) where
  src := ![![1], ![1]]
  prod := ![![2], ![0]]

/-- Birth at rate `2x`, death at rate `3x`. -/
noncomputable def bd : StochasticCRN (Fin 1) (Fin 2) where
  network := bdNet
  propensity := fun r x => ![2 * (x 0 : ℝ), 3 * (x 0 : ℝ)] r
  propensity_nonneg := by
    intro r x; fin_cases r <;> simp
  propensity_eq_zero := by
    intro r x h
    have hx : x 0 = 0 := by
      by_contra hx
      apply h
      rw [Pi.le_def]
      intro s
      fin_cases s
      fin_cases r <;> simp [bdNet] <;> omega
    fin_cases r <;> simp [hx]

/-- The generator of the count: `L V(x) = 2x - 3x = -x`. -/
theorem bd_generator (x : Fin 1 → ℕ) :
    bd.generator (fun y => (count y : ℝ)) x = -(x 0 : ℝ) := by
  simp only [StochasticCRN.generator, Fin.sum_univ_two, bd, StochasticCRN.jump, bdNet,
    count, NNReal.coe_natCast]
  rcases Nat.eq_zero_or_pos (x 0) with h | h
  · simp [h, Matrix.vecHead]
  · obtain ⟨n, hn⟩ : ∃ n, x 0 = n + 1 := ⟨x 0 - 1, by omega⟩
    simp [hn, Matrix.vecHead]
    ring

theorem bd_drift (x : Fin 1 → ℕ) : bd.generator (fun y => (count y : ℝ)) x ≤ 0 * count x := by
  rw [bd_generator]
  simp

/-- The empty state is absorbing: total propensity `0`, so the holding rate is the fictitious
`1` and the jump kernel is `δ_0`. -/
theorem bd_absorbing : bd.totalRate 0 = 0 ∧ bd.holdRate 0 = 1 ∧ bd.jumpPMF 0 = PMF.pure 0 := by
  have h : bd.totalRate 0 = 0 := by
    simp [StochasticCRN.totalRate, bd, Fin.sum_univ_two]
  refine ⟨h, by simp [StochasticCRN.holdRate, h], by simp [StochasticCRN.jumpPMF, h]⟩

/-- At a positive state the total propensity is `5x`. -/
theorem bd_totalRate (x : Fin 1 → ℕ) : bd.totalRate x = 5 * x 0 := by
  simp only [StochasticCRN.totalRate, bd, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem bd_bdd (m : ℝ) : ∃ K, ∀ x, (count x : ℝ) < m → bd.totalRate x ≤ K :=
  bd.bddRate_of_coercive _ (fun x => by simp [count]) m

/-- **Subcritical moments stay bounded uniformly in time**: `E[X_t] ≤ x₀` for every `t ≥ 0`. -/
theorem bd_moment (x₀ : Fin 1 → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (count (bd.path x₀ ω t) : ℝ≥0∞) ∂bd.inputMeasure ≤ count x₀ := by
  have h := bd.lintegral_path_le count le_rfl bd_drift bd_bdd x₀ ht
  simpa using h

/-- The discounted moment along jump times with `c = 0`: `E[X_{Y_n}] ≤ x₀` for every number `n`
of reactions. -/
theorem bd_jump_moment (x₀ : Fin 1 → ℕ) (n : ℕ) :
    ∫⁻ ω, (count (ProbabilityTheory.ctmcJumpChain x₀ ω n) : ℝ≥0∞) ∂bd.inputMeasure ≤
      count x₀ := by
  have h := bd.lintegral_exp_jumpTime_mul_le count le_rfl bd_drift n x₀
  simpa using h

/-- The chain reaches `{X ≥ m}` by time `t` with probability at most `x₀ / m`. -/
theorem bd_reach (x₀ : Fin 1 → ℕ) {m : ℝ≥0} (hm : 0 < m) (t : ℝ) :
    bd.inputMeasure {ω | ∃ k, m ≤ count (ProbabilityTheory.ctmcJumpChain x₀ ω k) ∧
        (∀ j < k, count (ProbabilityTheory.ctmcJumpChain x₀ ω j) < m) ∧
        bd.jumpTime x₀ ω k ≤ t} ≤ count x₀ / m := by
  have h := JumpHold.measure_reach_le (P := bd.jumpPMF) (q := bd.holdRate) (c := 0) (V := count)
    bd.holdRate_pos le_rfl (fun x => bd.drift_of_generator_le count le_rfl x (bd_drift x)) hm t x₀
  simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h
  exact h

/-! ### Dimerization -/

/-- `2A → B` (reaction `0`) and `B → 2A` (reaction `1`) on species `A = 0`, `B = 1`. -/
def dimerNet : ComplexBalanced.ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![2, 0], ![0, 1]]
  prod := ![![0, 1], ![2, 0]]

/-- Propensities `a (a - 1)` (quadratic) and `4 b`. -/
noncomputable def dimer : StochasticCRN (Fin 2) (Fin 2) where
  network := dimerNet
  propensity := fun r x => ![((x 0 * (x 0 - 1) : ℕ) : ℝ), 4 * (x 1 : ℝ)] r
  propensity_nonneg := by
    intro r x; fin_cases r
    · exact Nat.cast_nonneg _
    · simp
  propensity_eq_zero := by
    intro r x h
    fin_cases r
    · have ha : x 0 < 2 := by
        by_contra ha
        apply h
        rw [Pi.le_def]
        intro s
        fin_cases s <;> simp [dimerNet]
        omega
      interval_cases hx : x 0 <;> simp
    · have hb : x 1 = 0 := by
        by_contra hb
        apply h
        rw [Pi.le_def]
        intro s
        fin_cases s <;> simp [dimerNet]
        omega
      simp [hb]

/-- The conserved quantity `a + 2b`. -/
def mass (x : Fin 2 → ℕ) : ℝ≥0 := (x 0 + 2 * x 1 : ℕ)

/-- `a + 2b` is conserved by both reactions: `L V = 0`. -/
theorem dimer_generator (x : Fin 2 → ℕ) : dimer.generator (fun y => (mass y : ℝ)) x = 0 := by
  simp only [StochasticCRN.generator, Fin.sum_univ_two, dimer, StochasticCRN.jump, dimerNet,
    mass, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply]
  have h0 : ((x 0 * (x 0 - 1) : ℕ) : ℝ) *
      ((((x 0 - 2 + 0 + 2 * (x 1 - 0 + 1) : ℕ) : ℝ≥0) : ℝ) - (((x 0 + 2 * x 1 : ℕ) : ℝ≥0) : ℝ))
      = 0 := by
    rcases lt_or_ge (x 0) 2 with ha | ha
    · interval_cases hx : x 0 <;> simp
    · rw [NNReal.coe_natCast, NNReal.coe_natCast, sub_eq_zero.2 (by congr 1; omega), mul_zero]
  have h1 : 4 * (x 1 : ℝ) *
      ((((x 0 - 0 + 2 + 2 * (x 1 - 1 + 0) : ℕ) : ℝ≥0) : ℝ) - (((x 0 + 2 * x 1 : ℕ) : ℝ≥0) : ℝ))
      = 0 := by
    rcases Nat.eq_zero_or_pos (x 1) with hb | hb
    · simp [hb]
    · rw [NNReal.coe_natCast, NNReal.coe_natCast, sub_eq_zero.2 (by congr 1; omega), mul_zero]
  simpa using congrArg₂ (· + ·) h0 h1

/-- **Non-explosion of the dimerization** despite its quadratic propensity. -/
theorem dimer_nonexplosive (x₀ : Fin 2 → ℕ) :
    ∀ᵐ ω ∂dimer.inputMeasure, Tendsto (dimer.jumpTime x₀ ω) atTop atTop :=
  dimer.ae_tendsto_jumpTime_atTop_of_coercive mass le_rfl le_rfl
    (fun x => by rw [dimer_generator]; simp)
    (fun x => by simp [mass, Fin.sum_univ_two]; linarith [Nat.cast_nonneg (α := ℝ) (x 1)]) x₀

/-! ### Superlinear autocatalysis: the criterion fails -/

/-- `2X → 3X`. -/
def autoNet : ComplexBalanced.ReactionNetwork (Fin 1) (Fin 1) where
  src := ![![2]]
  prod := ![![3]]

/-- Propensity `x (x - 1)`. -/
noncomputable def auto : StochasticCRN (Fin 1) (Fin 1) where
  network := autoNet
  propensity := fun _ x => ((x 0 * (x 0 - 1) : ℕ) : ℝ)
  propensity_nonneg := fun _ _ => Nat.cast_nonneg _
  propensity_eq_zero := by
    intro r x h
    have ha : x 0 < 2 := by
      by_contra ha
      apply h
      rw [Pi.le_def]
      intro s
      fin_cases s
      fin_cases r
      simp [autoNet]
      omega
    interval_cases hx : x 0 <;> simp

/-- For the count, `L V(x) = x (x - 1)`, computed from the definitions. -/
theorem auto_generator (x : Fin 1 → ℕ) :
    auto.generator (fun y => (count y : ℝ)) x = ((x 0 * (x 0 - 1) : ℕ) : ℝ) := by
  simp only [StochasticCRN.generator, Fin.sum_univ_one, auto, StochasticCRN.jump, autoNet,
    count, NNReal.coe_natCast]
  rcases lt_or_ge (x 0) 2 with ha | ha
  · interval_cases hx : x 0 <;> simp
  · obtain ⟨n, hn⟩ : ∃ n, x 0 = n + 2 := ⟨x 0 - 2, by omega⟩
    simp [hn, Matrix.vecHead]
    ring

/-- **The Foster–Lyapunov criterion fails for `2X → 3X` with `V(x) = x`**: no bound
`L V ≤ a V + b` holds. (The theorem makes no claim about this chain.) -/
theorem auto_not_drift : ¬ ∃ a b : ℝ, ∀ x : Fin 1 → ℕ,
    auto.generator (fun y => (count y : ℝ)) x ≤ a * count x + b := by
  rintro ⟨a, b, h⟩
  set n : ℕ := ⌈|a| + |b|⌉₊ + 2 with hn
  have hn2 : 2 ≤ n := by omega
  have key := h (fun _ => n)
  rw [auto_generator] at key
  simp only [count, NNReal.coe_natCast] at key
  have hnr : (|a| + |b|) + 2 ≤ (n : ℝ) := by
    rw [hn]; push_cast; linarith [Nat.le_ceil (|a| + |b|)]
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)] at key
  push_cast at key
  have ha := le_abs_self a
  have hb := le_abs_self b
  have hpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [abs_nonneg a, abs_nonneg b]

end MathlibExtTest.Biology.Dynamics.StochasticCRNNonExplosion
