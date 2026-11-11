/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.Replicator
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Evolutionarily stable states are asymptotically stable (interior case)

For a symmetric matrix game with payoff matrix `A : Matrix ι ι ℝ`, the replicator equation of
`MathlibExt.Biology.Dynamics.Replicator` with fitness `f(x) = A x` reads
`x_i' = x_i ((A x)_i - x · A x)`. This file proves that an **interior** evolutionarily stable
state `p` (all `p i > 0`) is locally asymptotically stable: solutions starting in the simplex
close to `p` stay close to `p` and converge to `p`.

## Definitions

* `IsNash A p`: `p` is a symmetric Nash equilibrium, `q · A p ≤ p · A p` for all mixed `q`.
* `IsESS A p`: `p` is evolutionarily stable in the sense of Maynard Smith and Price: for every
  mixed `q ≠ p`, either `q · A p < p · A p`, or `q · A p = p · A p` and `q · A q < p · A q`.
* `relEntropy p y = ∑ i, p i * (log (p i) - log (y i))`, the Lyapunov function. It equals
  `log P(p) - log P(y)` for the Hofbauer–Sigmund function `P(y) = ∏ i, y i ^ p i`.

## Main results

* `IsESS.isNash`: an ESS is a Nash equilibrium.
* `IsNash.dotProduct_mulVec_eq_of_pos`: an interior Nash equilibrium is an equalizer, so every
  mixed `q` earns `q · A p = p · A p` against it.
* `IsESS.dotProduct_mulVec_lt_of_pos`: an interior ESS beats every other mixed state `q` in the
  simplex, boundary included: `q · A q < p · A q`.
* `relEntropy_pos`: `relEntropy p y > 0` for interior `y ≠ p` in the simplex.
* `IsSolution.hasDerivAt_relEntropy`: along a solution,
  `d/dt relEntropy p (x t) = -(p · A x - x · A x)`.
* `IsESS.lyapunovStable`, `IsESS.tendsto_nhds`, `IsESS.asymptoticallyStable`: an interior ESS
  is Lyapunov stable and locally attracting, i.e. locally asymptotically stable.

## Scope: boundary rest points are not covered

Every vertex of the simplex is a rest point of the replicator equation, and a boundary rest
point need not be a Nash equilibrium (the tests exhibit a vertex of the Hawk–Dove game that is
a rest point but not Nash). The results here are stated **only for interior ESS** (`∀ i,
0 < p i`); the ESS → asymptotic stability implication for an ESS on the boundary of the simplex
(Hofbauer–Sigmund 1998, Theorem 7.2.4 in full generality) is not proved here. A Nash
equilibrium alone does not suffice: the tests give a two-strategy Nash equilibrium that is not
asymptotically stable.

## Implementation notes

The stability argument is Lyapunov's direct method carried out directly for the replicator
equation, using compactness of annuli `{y ∈ Δ | a ≤ ‖y - p‖ ≤ b}` and the intermediate value
theorem. The general Lyapunov criterion of `MathlibExt/Analysis/ODE/LyapunovStability.lean`
(atlas-lean PR #1127) is not on `main` at the base of this file, so it is not used. The
existing definitions `Replicator.IsSolution`, `Replicator.meanFitness` and the invariance
results `IsSolution.mem_simplex`, `IsSolution.pos_of_pos` are reused; `meanFitness` of the
fitness `y ↦ A y` is definitionally `y · A y`.

## Source receipt

* Definition of ESS: J. Maynard Smith and G. R. Price, *The logic of animal conflict*,
  Nature 246 (1973) 15–18; in the form used here, Hofbauer–Sigmund 1998, §6.1, conditions
  (6.3)–(6.4).
* Interior ESS characterization and the Lyapunov function `P(x) = ∏ x_i ^ {p_i}`:
  J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge
  University Press (1998), Theorem 6.4.1 and Theorem 7.2.4 (proof: `P'/P = p · A x - x · A x`).
* P. D. Taylor and L. B. Jonker, *Evolutionarily stable strategies and game dynamics*,
  Math. Biosci. 40 (1978) 145–156.
-/

@[expose] public section

open Set Finset Filter Topology Matrix Real

namespace MathlibExt.Biology.Dynamics.Replicator

variable {ι : Type*} [Fintype ι]

/-- `p` is a **symmetric Nash equilibrium** of the matrix game `A`: `p` is a mixed strategy and
no mixed strategy `q` earns more against `p` than `p` itself, `q · A p ≤ p · A p`. -/
def IsNash (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧
    ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 → q ⬝ᵥ A *ᵥ p ≤ p ⬝ᵥ A *ᵥ p

/-- `p` is an **evolutionarily stable state** of the matrix game `A` (Maynard Smith and Price
1973; Hofbauer–Sigmund 1998, (6.3)–(6.4)): for every mixed strategy `q ≠ p`, either
`q · A p < p · A p`, or `q · A p = p · A p` and `q · A q < p · A q`. -/
def IsESS (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧ ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 → q ≠ p →
    q ⬝ᵥ A *ᵥ p < p ⬝ᵥ A *ᵥ p ∨ (q ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p ∧ q ⬝ᵥ A *ᵥ q < p ⬝ᵥ A *ᵥ q)

/-- The Lyapunov function `relEntropy p y = ∑ i, p i * (log (p i) - log (y i))` (the relative
entropy of `p` with respect to `y`). It equals `log P(p) - log P(y)` for the Hofbauer–Sigmund
function `P(y) = ∏ i, y i ^ p i`. -/
noncomputable def relEntropy (p y : ι → ℝ) : ℝ :=
  ∑ i, p i * (log (p i) - log (y i))

variable {A : Matrix ι ι ℝ} {p : ι → ℝ}

/-- The mean fitness of the matrix game `A` is the payoff of `y` against itself. -/
theorem meanFitness_mulVec (y : ι → ℝ) : meanFitness (fun z => A *ᵥ z) y = y ⬝ᵥ A *ᵥ y :=
  rfl

/-- An ESS is a Nash equilibrium. -/
theorem IsESS.isNash (h : IsESS A p) : IsNash A p := by
  refine ⟨h.1, fun q hq => ?_⟩
  by_cases hqp : q = p
  · rw [hqp]
  · rcases h.2 q hq hqp with h1 | h1
    · exact h1.le
    · exact h1.1.le

/-- **Interior Nash equilibria are equalizers.** If `p` is a Nash equilibrium with every
strategy present, every pure strategy earns `p · A p` against `p`. -/
theorem IsNash.mulVec_eq_of_pos (h : IsNash A p) (hp : ∀ i, 0 < p i) (i : ι) :
    (A *ᵥ p) i = p ⬝ᵥ A *ᵥ p := by
  classical
  have hle : ∀ j, (A *ᵥ p) j ≤ p ⬝ᵥ A *ᵥ p := fun j => by
    have hj : (∀ i, 0 ≤ (Pi.single j 1 : ι → ℝ) i) ∧ ∑ i, (Pi.single j 1 : ι → ℝ) i = 1 :=
      ⟨fun i => by by_cases hij : i = j <;> simp [hij], by simp⟩
    simpa [single_dotProduct] using h.2 _ hj
  have hsum : ∑ j, p j * ((A *ᵥ p) j - p ⬝ᵥ A *ᵥ p) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h.1.2, one_mul]
    exact sub_self _
  have hi := (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (hp j).le (sub_nonpos.2 (hle j))).1 hsum i (mem_univ i)
  rcases mul_eq_zero.1 hi with h0 | h0
  · exact absurd h0 (hp i).ne'
  · exact sub_eq_zero.1 h0

/-- Against an interior Nash equilibrium `p`, every mixed strategy earns `p · A p`. -/
theorem IsNash.dotProduct_mulVec_eq_of_pos (h : IsNash A p) (hp : ∀ i, 0 < p i) {q : ι → ℝ}
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) : q ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p := by
  calc q ⬝ᵥ A *ᵥ p = ∑ i, q i * (p ⬝ᵥ A *ᵥ p) :=
        Finset.sum_congr rfl fun i _ => by rw [h.mulVec_eq_of_pos hp i]
    _ = p ⬝ᵥ A *ᵥ p := by rw [← Finset.sum_mul, hq.2, one_mul]

/-- **An interior ESS beats every other state** (Hofbauer–Sigmund 1998, Theorem 6.4.1): for every
`q ≠ p` in the simplex, boundary included, `q · A q < p · A q`. -/
theorem IsESS.dotProduct_mulVec_lt_of_pos (h : IsESS A p) (hp : ∀ i, 0 < p i) {q : ι → ℝ}
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) (hqp : q ≠ p) : q ⬝ᵥ A *ᵥ q < p ⬝ᵥ A *ᵥ q := by
  have heq := h.isNash.dotProduct_mulVec_eq_of_pos hp hq
  rcases h.2 q hq hqp with h1 | h1
  · exact absurd heq h1.ne
  · exact h1.2

/-- An interior ESS has nonnegative payoff advantage `p · A q - q · A q` on the simplex. -/
theorem IsESS.dotProduct_mulVec_sub_nonneg (h : IsESS A p) (hp : ∀ i, 0 < p i) {q : ι → ℝ}
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) : 0 ≤ p ⬝ᵥ A *ᵥ q - q ⬝ᵥ A *ᵥ q := by
  by_cases hqp : q = p
  · simp [hqp]
  · exact (sub_pos.2 (h.dotProduct_mulVec_lt_of_pos hp hq hqp)).le

theorem relEntropy_self (p : ι → ℝ) : relEntropy p p = 0 := by
  simp [relEntropy]

/-- **The Lyapunov function is positive away from `p`.** For interior `p` and `y` in the simplex
with `y ≠ p`, `relEntropy p y > 0` (from `log z < z - 1` for `z ≠ 1`). -/
theorem relEntropy_pos (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) {y : ι → ℝ}
    (hy : ∀ i, 0 < y i) (hy1 : ∑ i, y i = 1) (hne : y ≠ p) : 0 < relEntropy p y := by
  have key : ∀ i, p i - y i ≤ p i * (log (p i) - log (y i)) ∧
      (y i ≠ p i → p i - y i < p i * (log (p i) - log (y i))) := fun i => by
    have hz : 0 < y i / p i := div_pos (hy i) (hp i)
    have hlog : log (p i) - log (y i) = -log (y i / p i) := by
      rw [log_div (hy i).ne' (hp i).ne']
      ring
    have hmul : p i * (y i / p i - 1) = y i - p i := by
      rw [mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ (hp i).ne']
    rw [hlog]
    refine ⟨?_, fun hne => ?_⟩
    · nlinarith [log_le_sub_one_of_pos hz, hp i]
    · have hz1 : y i / p i ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq (hp i).ne').1 h1)
      nlinarith [log_lt_sub_one_of_pos hz hz1, hp i]
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ p j := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have := Finset.sum_lt_sum (fun i _ => (key i).1) ⟨j, mem_univ j, (key j).2 hj⟩
  rw [Finset.sum_sub_distrib, hp1, hy1, sub_self] at this
  exact this

theorem continuousOn_relEntropy (p : ι → ℝ) :
    ContinuousOn (relEntropy p) {y | ∀ i, y i ≠ 0} := by
  unfold relEntropy
  exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
    (continuousOn_const.sub ((continuous_apply i).continuousOn.log fun y hy => hy i))

theorem continuousAt_relEntropy (hp : ∀ i, 0 < p i) : ContinuousAt (relEntropy p) p := by
  refine (continuousOn_relEntropy p).continuousAt (IsOpen.mem_nhds ?_ fun i => (hp i).ne')
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const

/-- **Derivative of the Lyapunov function** (Hofbauer–Sigmund 1998, proof of Theorem 7.2.4:
`P'/P = p · A x - x · A x`). Along a solution of the replicator equation of the matrix game `A`
with all frequencies nonzero at time `t`, `d/dt relEntropy p (x t) = -(p · A x - x · A x)`. -/
theorem IsSolution.hasDerivAt_relEntropy {x : ℝ → ι → ℝ} (h : IsSolution (fun z => A *ᵥ z) x)
    (hp1 : ∑ i, p i = 1) {t : ℝ} (ht : 0 ≤ t) (hx : ∀ i, x t i ≠ 0) :
    HasDerivAt (fun s => relEntropy p (x s)) (-(p ⬝ᵥ A *ᵥ x t - x t ⬝ᵥ A *ᵥ x t)) t := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (((h.hasDerivAt i t ht).log (hx i)).const_sub (log (p i))).const_mul (p i)
  unfold relEntropy
  convert hs using 1
  have hterm : ∀ i, p i * -(x t i * ((A *ᵥ x t) i - meanFitness (fun z => A *ᵥ z) (x t)) /
      x t i) = -(p i * (A *ᵥ x t) i) + p i * (x t ⬝ᵥ A *ᵥ x t) := fun i => by
    rw [mul_div_cancel_left₀ _ (hx i), meanFitness_mulVec]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_mul, hp1, one_mul]
  simp only [dotProduct]
  ring

/-- Along a solution starting at an interior point of the simplex, if the payoff advantage
`p · A x - x · A x` is at least `c` for all `t ≥ 0`, then `relEntropy p (x t) + c t` is
nonincreasing on `[0, ∞)`. -/
private theorem IsSolution.antitoneOn_relEntropy_add {x : ℝ → ι → ℝ}
    (h : IsSolution (fun z => A *ᵥ z) x) (hp1 : ∑ i, p i = 1)
    (hpos : ∀ s, 0 ≤ s → ∀ i, 0 < x s i) (c : ℝ)
    (hc : ∀ s, 0 ≤ s → c ≤ p ⬝ᵥ A *ᵥ x s - x s ⬝ᵥ A *ᵥ x s) :
    AntitoneOn (fun s => relEntropy p (x s) + c * s) (Ici 0) := by
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun s => relEntropy p (x s) + c * s)
      (-(p ⬝ᵥ A *ᵥ x s - x s ⬝ᵥ A *ᵥ x s) + c) s := fun s hs => by
    have := (h.hasDerivAt_relEntropy hp1 hs fun i => (hpos s hs i).ne').fun_add
      ((hasDerivAt_id' s).const_mul c)
    convert this using 1
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt) fun s hs => ?_
  have := hc s (interior_subset hs)
  linarith

/-- A continuous function, positive on interior points `y ≠ p` of the simplex, is bounded
below by a positive constant on each annulus `{y ∈ Δ | a ≤ ‖y - p‖ ≤ b}` with `a > 0` whose
outer radius `b` keeps it inside the positive orthant. -/
private theorem exists_pos_le_on_annulus {F : (ι → ℝ) → ℝ} {a b : ℝ} (ha : 0 < a)
    (hb : ∀ y : ι → ℝ, ‖y - p‖ ≤ b → ∀ i, 0 < y i) (hF : ContinuousOn F {y | ∀ i, y i ≠ 0})
    (hpos : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 → (∀ i, 0 < y i) → y ≠ p → 0 < F y) :
    ∃ m > 0, ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 → a ≤ ‖y - p‖ → ‖y - p‖ ≤ b → m ≤ F y := by
  set K := {y : ι → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} ∩ {y | a ≤ ‖y - p‖ ∧ ‖y - p‖ ≤ b}
  have hKcl : IsClosed K := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · have hset : {y : ι → ℝ | ∀ i, 0 ≤ y i} = ⋂ i, {y : ι → ℝ | 0 ≤ y i} := by
        ext y
        simp
      have hcl : IsClosed {y : ι → ℝ | ∀ i, 0 ≤ y i} := by
        rw [hset]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
      exact hcl
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    · exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  have hKc : IsCompact K := (isCompact_closedBall p b).of_isClosed_subset hKcl fun y hy => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hy.2.2
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun y hy h1 h2 => ?_⟩
    have : y ∈ K := ⟨hy, h1, h2⟩
    rw [hK] at this
    exact absurd this (notMem_empty y)
  · obtain ⟨y₀, hy₀, hmin⟩ := hKc.exists_isMinOn hK
      (hF.mono fun y hy i => (hb y hy.2.2 i).ne')
    refine ⟨F y₀, hpos y₀ hy₀.1 (hb _ hy₀.2.2) ?_, fun y hy h1 h2 => hmin ⟨hy, h1, h2⟩⟩
    rintro rfl
    have := hy₀.2.1
    rw [sub_self, norm_zero] at this
    exact absurd this (not_le.2 ha)

/-- An interior point has a positive radius `r` with `r ≤ p i` for all `i`; points within sup
distance `< r` of `p` are interior. -/
private theorem exists_pos_radius (hp : ∀ i, 0 < p i) :
    ∃ r > 0, ∀ y : ι → ℝ, ‖y - p‖ < r → ∀ i, 0 < y i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun y _ i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min p
    refine ⟨p i₀, hp i₀, fun y hy i => ?_⟩
    have h1 : |y i - p i| ≤ ‖y - p‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - p) i
    have h2 := neg_abs_le (y i - p i)
    linarith [hi₀ i]

theorem continuous_mulVec_fitness (A : Matrix ι ι ℝ) : Continuous fun z : ι → ℝ => A *ᵥ z :=
  (Matrix.mulVecLin A).continuous_of_finiteDimensional

private theorem continuous_advantage (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    Continuous fun y : ι → ℝ => p ⬝ᵥ A *ᵥ y - y ⬝ᵥ A *ᵥ y := by
  have hm := continuous_mulVec_fitness A
  simp only [dotProduct]
  fun_prop

/-- **Lyapunov stability of an interior ESS** (Hofbauer–Sigmund 1998, Theorem 7.2.4, interior
case). For every `ε > 0` there is `δ > 0` such that every solution of the replicator equation
starting in the simplex within distance `δ` of `p` stays within distance `ε` of `p` for all
`t ≥ 0`. -/
theorem IsESS.lyapunovStable (h : IsESS A p) (hp : ∀ i, 0 < p i) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsSolution (fun z => A *ᵥ z) x →
      (∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1 → ‖x 0 - p‖ < δ → ∀ t, 0 ≤ t → ‖x t - p‖ < ε := by
  intro ε hε
  obtain ⟨r, hr, hrp⟩ := exists_pos_radius hp
  set e := min ε (r / 2) with he_def
  have he : 0 < e := lt_min hε (half_pos hr)
  have hball : ∀ y : ι → ℝ, ‖y - p‖ ≤ e → ∀ i, 0 < y i := fun y hy =>
    hrp y (hy.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr)))
  obtain ⟨m, hm, hmV⟩ := exists_pos_le_on_annulus he hball (continuousOn_relEntropy p)
    fun y hy hy0 hne => relEntropy_pos hp h.1.2 hy0 hy.2 hne
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuousAt_iff.1 (continuousAt_relEntropy hp) m hm
  refine ⟨min δ e, lt_min hδ he, fun x hx hx0 hd t ht => ?_⟩
  have hf := continuous_mulVec_fitness A
  have hpos : ∀ s, 0 ≤ s → ∀ i, 0 < x s i := fun s hs i =>
    hx.pos_of_pos hf (hball _ (hd.le.trans (min_le_right _ _)) i) hs
  have hsimp : ∀ s, 0 ≤ s → (∀ i, 0 ≤ x s i) ∧ ∑ i, x s i = 1 := fun s hs =>
    hx.mem_simplex hf hx0.1 hx0.2 hs
  have hanti := hx.antitoneOn_relEntropy_add h.1.2 hpos 0 fun s hs =>
    h.dotProduct_mulVec_sub_nonneg hp (hsimp s hs)
  simp only [zero_mul, add_zero] at hanti
  have hV0 : relEntropy p (x 0) < m := by
    have := hδV (x := x 0) (by rw [dist_eq_norm]; exact hd.trans_le (min_le_left _ _))
    rw [relEntropy_self, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  by_contra hge
  push Not at hge
  have hcont : ContinuousOn (fun s => ‖x s - p‖) (Icc 0 t) := fun s hs =>
    ((continuousAt_pi.2 fun i => (hx.hasDerivAt i s hs.1).continuousAt).sub
      continuousAt_const).norm.continuousWithinAt
  obtain ⟨s, hs, hse⟩ := intermediate_value_Icc ht hcont
    ⟨(hd.trans_le (min_le_right _ _)).le, (min_le_left _ _).trans hge⟩
  have h1 := hmV (x s) (hsimp s hs.1) hse.ge hse.le
  have h2 := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hs.1) hs.1
  linarith

/-- **Local attraction of an interior ESS** (Hofbauer–Sigmund 1998, Theorem 7.2.4, interior
case). There is `δ > 0` such that every solution of the replicator equation starting in the
simplex within distance `δ` of `p` converges to `p`. -/
theorem IsESS.tendsto_nhds (h : IsESS A p) (hp : ∀ i, 0 < p i) :
    ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsSolution (fun z => A *ᵥ z) x →
      (∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1 → ‖x 0 - p‖ < δ → Tendsto x atTop (𝓝 p) := by
  obtain ⟨r, hr, hrp⟩ := exists_pos_radius hp
  have he₀ : 0 < r / 2 := half_pos hr
  have hball : ∀ y : ι → ℝ, ‖y - p‖ ≤ r / 2 → ∀ i, 0 < y i := fun y hy =>
    hrp y (hy.trans_lt (half_lt_self hr))
  obtain ⟨δ, hδ, hstab⟩ := h.lyapunovStable hp (r / 2) he₀
  refine ⟨δ, hδ, fun x hx hx0 hd => ?_⟩
  have hf := continuous_mulVec_fitness A
  have hin : ∀ s, 0 ≤ s → ‖x s - p‖ < r / 2 := hstab x hx hx0 hd
  have hpos : ∀ s, 0 ≤ s → ∀ i, 0 < x s i := fun s hs i =>
    hx.pos_of_pos hf (hball _ (hin 0 le_rfl).le i) hs
  have hsimp : ∀ s, 0 ≤ s → (∀ i, 0 ≤ x s i) ∧ ∑ i, x s i = 1 := fun s hs =>
    hx.mem_simplex hf hx0.1 hx0.2 hs
  have hanti := hx.antitoneOn_relEntropy_add h.1.2 hpos 0 fun s hs =>
    h.dotProduct_mulVec_sub_nonneg hp (hsimp s hs)
  simp only [zero_mul, add_zero] at hanti
  rw [Metric.tendsto_atTop]
  intro η hη
  set η' := min η (r / 2)
  have hη' : 0 < η' := lt_min hη he₀
  obtain ⟨m, hm, hmV⟩ := exists_pos_le_on_annulus hη' hball (continuousOn_relEntropy p)
    fun y hy hy0 hne => relEntropy_pos hp h.1.2 hy0 hy.2 hne
  obtain ⟨ρ, hρ, hρV⟩ := Metric.continuousAt_iff.1 (continuousAt_relEntropy hp) m hm
  set ρ' := min ρ η'
  have hρ' : 0 < ρ' := lt_min hρ hη'
  obtain ⟨c, hc, hcg⟩ := exists_pos_le_on_annulus hρ' hball
    (continuous_advantage A p).continuousOn fun y hy _ hne =>
      sub_pos.2 (h.dotProduct_mulVec_lt_of_pos hp hy hne)
  have hclaim : ∃ T, 0 ≤ T ∧ relEntropy p (x T) < m := by
    by_contra hno
    push Not at hno
    have hfar : ∀ s, 0 ≤ s → ρ' ≤ ‖x s - p‖ := fun s hs => by
      by_contra hlt
      push Not at hlt
      have := hρV (x := x s) (by rw [dist_eq_norm]; exact hlt.trans_le (min_le_left _ _))
      rw [relEntropy_self, Real.dist_eq, sub_zero] at this
      linarith [hno s hs, le_abs_self (relEntropy p (x s))]
    have hantic := hx.antitoneOn_relEntropy_add h.1.2 hpos c fun s hs =>
      hcg (x s) (hsimp s hs) (hfar s hs) (hin s hs).le
    have hV0 := hno 0 le_rfl
    set T := relEntropy p (x 0) / c + 1
    have hT : 0 ≤ T := by
      have : 0 ≤ relEntropy p (x 0) / c := div_nonneg (hm.le.trans hV0) hc.le
      simp only [T]
      linarith
    have h1 := hantic (mem_Ici.2 le_rfl) (mem_Ici.2 hT) hT
    have hcT : c * T = relEntropy p (x 0) + c := by
      simp only [T]
      field_simp
    simp only [mul_zero, add_zero] at h1
    linarith [hno T hT]
  obtain ⟨T, hT0, hTV⟩ := hclaim
  refine ⟨T, fun s hs => ?_⟩
  rw [dist_eq_norm]
  have hs0 : 0 ≤ s := hT0.trans hs
  have hsT := hanti (mem_Ici.2 hT0) (mem_Ici.2 hs0) hs
  by_contra hge
  push Not at hge
  have := hmV (x s) (hsimp s hs0) ((min_le_left _ _).trans hge) (hin s hs0).le
  linarith

/-- **An interior ESS is locally asymptotically stable** under the replicator dynamics of the
matrix game (Hofbauer–Sigmund 1998, Theorem 7.2.4, interior case): it is Lyapunov stable and
locally attracting. Boundary ESS and boundary rest points are not covered. -/
theorem IsESS.asymptoticallyStable (h : IsESS A p) (hp : ∀ i, 0 < p i) :
    (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsSolution (fun z => A *ᵥ z) x →
      (∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1 → ‖x 0 - p‖ < δ → ∀ t, 0 ≤ t → ‖x t - p‖ < ε) ∧
    ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsSolution (fun z => A *ᵥ z) x →
      (∀ i, 0 ≤ x 0 i) ∧ ∑ i, x 0 i = 1 → ‖x 0 - p‖ < δ → Tendsto x atTop (𝓝 p) :=
  ⟨h.lyapunovStable hp, h.tendsto_nhds hp⟩

end MathlibExt.Biology.Dynamics.Replicator
