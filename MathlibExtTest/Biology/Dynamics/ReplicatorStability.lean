/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ReplicatorStability
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Tests for `MathlibExt.Biology.Dynamics.ReplicatorStability`:

* an API-00 smoke test that the existing `Replicator.meanFitness` of the matrix fitness is the
  payoff `y · A y`;
* **counterexample first**: in the two-strategy neutral game `!![1, 1; 1, 1]`, the mixed state
  `(1/2, 1/2)` is a Nash equilibrium that is not an ESS and not asymptotically stable: it is
  Lyapunov stable (solutions starting in the simplex are constant) but not attracting (nearby
  rest points give constant solutions that do not converge to it);
* **interior ESS**: in the Hawk–Dove game `!![-1, 2; 0, 1]` (value `V = 2`, cost `C = 4`), the
  state `(1/2, 1/2)` is an interior ESS, the Lyapunov derivative is `-2 (x₀ - 1/2)²`, and the
  main theorem gives local asymptotic stability (with global forward existence); a solution
  from a simplex point other than the ESS exists and converges to it;
* **boundary**: the Hawk–Dove vertex `(1, 0)` is a rest point that is not a Nash equilibrium,
  so boundary rest points fall outside the ESS → stability implication. -/

open Filter Topology Matrix

namespace MathlibExtTest.Biology.Dynamics.ReplicatorStability

open MathlibExt.Biology.Dynamics.Replicator

/-- API-00 smoke test: the repo's mean fitness of the matrix fitness `y ↦ A y` is `y · A y`. -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (y : Fin 2 → ℝ) :
    meanFitness (fun z => A *ᵥ z) y = y ⬝ᵥ A *ᵥ y :=
  rfl

/-- The barycenter `(1/2, 1/2)`. -/
noncomputable def half : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem half_mem : (∀ i, 0 ≤ half i) ∧ ∑ i, half i = 1 :=
  ⟨fun i => by fin_cases i <;> norm_num [half], by norm_num [half, Fin.sum_univ_two]⟩

theorem half_coord_pos : ∀ i, 0 < half i := fun i => by fin_cases i <;> norm_num [half]

/-! ### Counterexample: a Nash equilibrium that is not asymptotically stable -/

/-- The neutral two-strategy game: every strategy earns `1` against everything. -/
def neutral : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

theorem neutral_mulVec (q : Fin 2 → ℝ) : neutral *ᵥ q = ![q 0 + q 1, q 0 + q 1] := by
  ext i
  fin_cases i <;> simp [neutral, mulVec, dotProduct, Fin.sum_univ_two]

/-- `(1/2, 1/2)` is a Nash equilibrium of the neutral game. -/
theorem half_isNash_neutral : IsNash neutral half := by
  refine ⟨half_mem, fun q hq => ?_⟩
  have h1 := hq.2
  simp only [Fin.sum_univ_two] at h1
  simp [neutral_mulVec, dotProduct, Fin.sum_univ_two, half]
  nlinarith

/-- Every point of the simplex is a rest point of the neutral game. -/
theorem neutral_isRestPoint {q : Fin 2 → ℝ} (hq : q 0 + q 1 = 1) :
    IsRestPoint (fun z => neutral *ᵥ z) q := by
  intro i
  fin_cases i <;> simp [meanFitness, neutral_mulVec, Fin.sum_univ_two, hq]

/-- `(1/2, 1/2)` is not an ESS of the neutral game: the pure state `(1, 0)` does as well. -/
theorem half_not_isESS_neutral : ¬ IsESS neutral half := by
  intro h
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ half := fun he => by
    have := congrFun he 0
    norm_num [half] at this
  have := h.2 ![1, 0] ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]⟩ hne
  norm_num [neutral_mulVec, dotProduct, Fin.sum_univ_two, half] at this

/-- In the neutral game every solution starting in the simplex is constant on `[0, ∞)`: it stays
in the simplex (`IsSolution.mem_simplex`), where every fitness and the mean fitness equal `1`, so
its derivative vanishes. -/
theorem neutral_eq_initial {x : ℝ → Fin 2 → ℝ} (hx : IsSolution (fun z => neutral *ᵥ z) x)
    (h0 : (∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1) {t : ℝ} (ht : 0 ≤ t) : x t = x 0 := by
  have hd : ∀ s, 0 ≤ s → ∀ i, HasDerivAt (fun s => x s i) 0 s := fun s hs i => by
    have h1 := (hx.mem_simplex (continuous_mulVec_fitness neutral) h0.1 h0.2 hs).2
    rw [Fin.sum_univ_two] at h1
    convert hx.hasDerivAt i s hs using 1
    fin_cases i <;> simp [meanFitness, neutral_mulVec, Fin.sum_univ_two, h1]
  funext i
  rcases ht.eq_or_lt with rfl | ht'
  · rfl
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope (fun s => x s i) (fun _ => 0) ht'
    (fun s hs => (hd s hs.1 i).continuousAt.continuousWithinAt) fun s hs => hd s hs.1.le i
  rw [eq_comm, div_eq_zero_iff, sub_zero] at hc
  rcases hc with hc | hc
  · linarith
  · exact absurd hc ht'.ne'

/-- **The neutral Nash equilibrium is Lyapunov stable**, since solutions starting in the simplex
are constant. -/
theorem half_lyapunovStable_neutral :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ, IsSolution (fun z => neutral *ᵥ z) x →
      ((∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1) → ‖x 0 - half‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - half‖ < ε :=
  fun ε hε => ⟨ε, hε, fun x hx h0 hd t ht => by rwa [neutral_eq_initial hx h0 ht]⟩

/-- Arbitrarily close to `(1/2, 1/2)` there is another point `(1/2 + s, 1/2 - s)` of the
simplex. -/
theorem exists_near_half {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Fin 2 → ℝ, ((∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) ∧ ‖q - half‖ < δ ∧ q ≠ half ∧
      q 0 + q 1 = 1 := by
  set s := min (δ / 2) (1 / 4) with hs_def
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hs4 : s ≤ 1 / 4 := min_le_right _ _
  have hsδ : s < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  set q : Fin 2 → ℝ := ![1 / 2 + s, 1 / 2 - s] with hq_def
  have hq1 : q 0 + q 1 = 1 := by
    simp only [hq_def, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  refine ⟨q, ⟨fun i => ?_, by rw [Fin.sum_univ_two]; exact hq1⟩, ?_, fun he => ?_, hq1⟩
  · fin_cases i <;> simp [hq_def] <;> linarith
  · rw [pi_norm_lt_iff hδ]
    intro i
    fin_cases i <;> simp [hq_def, half, abs_of_pos hs] <;> linarith
  · have := congrFun he 0
    simp [hq_def, half] at this
    linarith

/-- **Nash alone does not give asymptotic stability.** The Nash equilibrium `(1/2, 1/2)` of the
neutral game is Lyapunov stable (`half_lyapunovStable_neutral`) but not attracting:
for every `δ > 0` there is a solution starting in the simplex within `δ` of it that does not
converge to it. The statement is the negation of the conclusion of `IsESS.asymptoticallyStable`;
the proof refutes its attraction clause. -/
theorem half_not_asymptoticallyStable_neutral :
    ¬ ((∀ x₀ : Fin 2 → ℝ, ((∀ i, 0 ≤ x₀ i) ∧ ∑ i, x₀ i = 1) →
        ∃ x : ℝ → Fin 2 → ℝ, x 0 = x₀ ∧ IsSolution (fun z => neutral *ᵥ z) x) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ, IsSolution (fun z => neutral *ᵥ z) x →
        ((∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1) → ‖x 0 - half‖ < δ →
          ∀ t, 0 ≤ t → ‖x t - half‖ < ε) ∧
      ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ, IsSolution (fun z => neutral *ᵥ z) x →
        ((∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1) → ‖x 0 - half‖ < δ → Tendsto x atTop (𝓝 half)) := by
  rintro ⟨-, -, δ, hδ, h⟩
  obtain ⟨q, hmem, hdist, hne, hq1⟩ := exists_near_half hδ
  have ht := h (fun _ => q) (isSolution_const (neutral_isRestPoint hq1)) hmem hdist
  exact hne ((tendsto_const_nhds_iff).1 ht)

/-! ### Interior ESS: the Hawk–Dove game -/

/-- Hawk–Dove with value `V = 2` and cost `C = 4`: rows/columns are (Hawk, Dove), with payoffs
`(V - C)/2 = -1`, `V = 2`, `0`, `V/2 = 1`. -/
def hawkDove : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 2; 0, 1]

theorem hawkDove_mulVec (q : Fin 2 → ℝ) : hawkDove *ᵥ q = ![-q 0 + 2 * q 1, q 1] := by
  ext i
  fin_cases i <;> simp [hawkDove, mulVec, dotProduct, Fin.sum_univ_two]

/-- **`(1/2, 1/2)` is an interior ESS of Hawk–Dove** (`p = V/C`): against it every mixed `q`
earns `1/2`, and `p · A q - q · A q = 2 (q₀ - 1/2)² > 0` for `q ≠ p`. -/
theorem half_isESS_hawkDove : IsESS hawkDove half := by
  refine ⟨half_mem, fun q hq hne => Or.inr ⟨?_, ?_⟩⟩
  · have h1 := hq.2
    simp only [Fin.sum_univ_two] at h1
    simp [hawkDove_mulVec, dotProduct, Fin.sum_univ_two, half]
    nlinarith
  · have h1 := hq.2
    simp only [Fin.sum_univ_two] at h1
    have h0 : q 0 - 1 / 2 ≠ 0 := fun h0 => hne <| by
      funext i
      fin_cases i <;> simp [half] <;> linarith
    have hsq := pow_pos (abs_pos.2 h0) 2
    rw [sq_abs] at hsq
    simp [hawkDove_mulVec, dotProduct, Fin.sum_univ_two, half]
    nlinarith

/-- **The Lyapunov argument applies:** `(1/2, 1/2)` is locally asymptotically stable for the
replicator dynamics of Hawk–Dove. -/
theorem half_asymptoticallyStable_hawkDove :
    (∀ x₀ : Fin 2 → ℝ, ((∀ i, 0 ≤ x₀ i) ∧ ∑ i, x₀ i = 1) →
      ∃ x : ℝ → Fin 2 → ℝ, x 0 = x₀ ∧ IsSolution (fun z => hawkDove *ᵥ z) x) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ, IsSolution (fun z => hawkDove *ᵥ z) x →
      ((∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1) → ‖x 0 - half‖ < δ → ∀ t, 0 ≤ t → ‖x t - half‖ < ε) ∧
    ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ, IsSolution (fun z => hawkDove *ᵥ z) x →
      ((∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1) → ‖x 0 - half‖ < δ → Tendsto x atTop (𝓝 half) :=
  half_isESS_hawkDove.asymptoticallyStable half_coord_pos

/-- **The attraction clause is not vacuous:** a solution of the Hawk–Dove replicator equation
starting at a simplex point other than the ESS exists and converges to the ESS. -/
example : ∃ x : ℝ → Fin 2 → ℝ, x 0 ≠ half ∧ IsSolution (fun z => hawkDove *ᵥ z) x ∧
    Tendsto x atTop (𝓝 half) := by
  obtain ⟨hex, -, δ, hδ, hatt⟩ := half_asymptoticallyStable_hawkDove
  obtain ⟨q, hmem, hdist, hne, -⟩ := exists_near_half hδ
  obtain ⟨x, hx0, hx⟩ := hex q hmem
  exact ⟨x, hx0 ▸ hne, hx, hatt x hx (hx0 ▸ hmem) (hx0 ▸ hdist)⟩

/-- **The Lyapunov derivative for Hawk–Dove**, computed from the definitions: along a solution in
the open simplex, `d/dt relEntropy half (x t) = -2 (x₀(t) - 1/2)²`, strictly negative away from
the ESS. -/
example (x : ℝ → Fin 2 → ℝ) (hx : IsSolution (fun z => hawkDove *ᵥ z) x) {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ i, x t i ≠ 0) (hsum : x t 0 + x t 1 = 1) :
    HasDerivAt (fun s => relEntropy half (x s)) (-(2 * (x t 0 - 1 / 2) ^ 2)) t := by
  refine (hx.hasDerivAt_relEntropy half_mem.2 ht hpos).congr_deriv ?_
  have h1 : x t 1 = 1 - x t 0 := by linarith
  simp [hawkDove_mulVec, dotProduct, Fin.sum_univ_two, half, h1]
  ring

/-- The ESS is a rest point, so the constant solution witnesses that the solution hypothesis of
the stability theorem is satisfiable. -/
example : IsSolution (fun z => hawkDove *ᵥ z) fun _ => half := by
  refine isSolution_const fun i => ?_
  fin_cases i <;> norm_num [meanFitness, hawkDove_mulVec, Fin.sum_univ_two, half]

/-! ### Boundary rest points are not covered -/

/-- **A boundary rest point need not be Nash.** The all-Hawk vertex `(1, 0)` is a rest point of
the Hawk–Dove replicator equation (every vertex is), but it is not a Nash equilibrium: Dove earns
`0 > -1` against it. The ESS → asymptotic stability theorem says nothing about such points. -/
theorem hawk_isRestPoint_not_isNash :
    IsRestPoint (fun z => hawkDove *ᵥ z) ![1, 0] ∧ ¬ IsNash hawkDove ![1, 0] := by
  refine ⟨fun i => ?_, fun h => ?_⟩
  · fin_cases i <;> norm_num [meanFitness, hawkDove_mulVec, Fin.sum_univ_two]
  · have := h.2 ![0, 1] ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]⟩
    norm_num [hawkDove_mulVec, dotProduct, Fin.sum_univ_two] at this

end MathlibExtTest.Biology.Dynamics.ReplicatorStability
