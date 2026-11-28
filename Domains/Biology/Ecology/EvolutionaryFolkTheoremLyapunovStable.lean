/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Ecology.BoundaryESSStabilityTendstoOfPos
import Domains.Biology.Dynamics.AsymmetricESS
import Domains.Biology.Dynamics.ReplicatorStability
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Lyapunov-stable rest points are Nash equilibria

For a finite symmetric game with payoff matrix `A`, a rest point in the simplex that is
Lyapunov stable for the replicator equation on that simplex is a Nash equilibrium, even on
its boundary. A pure strategy that earns more than the resident mean payoff is absent at the
rest point. Giving it a small positive frequency produces a nearby initial state. If that
solution stayed near the rest point forever, the logarithm of the strategy's frequency would
grow at a uniformly positive rate, despite the frequency being bounded by one.

## References

* Josef Hofbauer and Karl Sigmund, *Evolutionary game dynamics*, Bull. Amer. Math. Soc. (N.S.)
  40 (2003), no. 4, 479–519, §2.3(d), p. 482; see also §2.1, eq. (2), and §2.2, eq. (3).
* Peter D. Taylor and Leo B. Jonker, *Evolutionarily stable strategies and game dynamics*,
  Math. Biosci. 40 (1978), 145–156, §3, eq. (2) (credited in §2.2 of the survey).
* `Domains.Biology.Dynamics.AsymmetricESS` supplies `isMixed_single` and `IsMixed.dotProduct_le`
  for the pure-reply criterion.
-/

namespace WantedExt.Biology.Ecology.EvolutionaryFolkTheoremWanted

open Matrix
open WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

variable {ι : Type*} [Fintype ι]

@[expose] public section

/-- `p` is a **symmetric Nash equilibrium** of `A`: `p ∈ Δ` and `q · A p ≤ p · A p` for every
`q ∈ Δ`. -/
def IsNash (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧ ∀ q ∈ simplex ι, q ⬝ᵥ A *ᵥ p ≤ p ⬝ᵥ A *ᵥ p

/-- `p` is **Lyapunov stable** for the replicator dynamics of `A` on `Δ`: `p ∈ Δ`, and for every
`ε > 0` there is `δ > 0` such that every solution starting in `Δ` within `δ` of `p` stays within `ε`
of `p` for all `t ≥ 0`. -/
def IsLyapunovStable (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧ ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsReplicatorSolution A x →
    x 0 ∈ simplex ι → ‖x 0 - p‖ < δ → ∀ t, 0 ≤ t → ‖x t - p‖ < ε

end

open MathlibExt.Biology.Dynamics.AsymmetricESS (isMixed_iff isMixed_single)
open MathlibExt.Biology.Dynamics.Replicator
  (continuous_mulVec_fitness exists_isSolution_mulVec meanFitness_mulVec)

/-- **Pure-reply criterion for symmetric Nash equilibrium.** A mixed strategy is Nash exactly
when no pure reply earns more against it than its payoff against itself. -/
public theorem isNash_iff_forall_pure_payoff_le {A : Matrix ι ι ℝ} {p : ι → ℝ} :
    IsNash A p ↔ p ∈ simplex ι ∧ ∀ i, (A *ᵥ p) i ≤ p ⬝ᵥ A *ᵥ p := by
  classical
  constructor
  · intro hp
    refine ⟨hp.1, fun i => ?_⟩
    have he := mem_simplex_iff.mpr (isMixed_iff.mp (isMixed_single i))
    simpa [single_dotProduct] using hp.2 _ he
  · rintro ⟨hp, hpayoff⟩
    exact ⟨hp, fun q hq => (isMixed_iff.mpr (mem_simplex_iff.mp hq)).dotProduct_le hpayoff⟩

/-- **Neighborhood criterion for Lyapunov stability.** A simplex state is stable when each
positive radius admits a neighborhood of initial states whose forward solutions stay within
that radius. -/
public theorem isLyapunovStable_iff {A : Matrix ι ι ℝ} {p : ι → ℝ} :
    IsLyapunovStable A p ↔
      p ∈ simplex ι ∧ ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsReplicatorSolution A x →
        x 0 ∈ simplex ι → x 0 ∈ Metric.ball p δ → ∀ t, 0 ≤ t → x t ∈ Metric.ball p ε := by
  simp only [IsLyapunovStable, Metric.mem_ball, dist_eq_norm]

/-- **Folk theorem (d)** (Hofbauer and Sigmund 2003, §2.3). For every payoff matrix `A`, if
`p ∈ Δ` is a rest point (`F(p) = 0`) that is Lyapunov stable for the replicator dynamics on
`Δ`, then `p` is a Nash equilibrium of `A`.

Source: Hofbauer and Sigmund (2003), §2.3, p. 482. -/
public theorem isNash_of_isLyapunovStable {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (hp : p ∈ simplex ι) (hrest : replicatorField A p = 0) (hstable : IsLyapunovStable A p) :
    IsNash A p := by
  classical
  refine isNash_iff_forall_pure_payoff_le.mpr ⟨hp, fun i => ?_⟩
  by_contra! hi
  have hpi : p i = 0 := by
    have h := congrFun hrest i
    rw [replicatorField_apply, Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_pos.mpr hi).ne'
  let gain (y : ι → ℝ) := (A *ᵥ y) i - y ⬝ᵥ A *ᵥ y
  let c := gain p / 2
  have hc : 0 < c := half_pos (sub_pos.mpr hi)
  have hcp : c < gain p := half_lt_self (sub_pos.mpr hi)
  have hf := continuous_mulVec_fitness A
  have hgain : Continuous gain := by
    dsimp only [gain, dotProduct]
    fun_prop
  obtain ⟨ε, hε, hnear⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hgain) p hcp
  obtain ⟨δ, hδ, hstay⟩ := (isLyapunovStable_iff.mp hstable).2 ε hε
  let e : ι → ℝ := Pi.single i 1
  let y (s : ℝ) := (1 - s) • p + s • e
  have hy : Continuous y := by
    dsimp only [y]
    fun_prop
  have hy0 : y 0 = p := by simp [y]
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp
    (hy.continuousAt : ContinuousAt y 0) δ hδ
  let s := min η 1 / 2
  have hs : 0 < s := half_pos (lt_min hη zero_lt_one)
  have hsη : s < η := (half_lt_self (lt_min hη zero_lt_one)).trans_le (min_le_left _ _)
  have hs₁ : s ≤ 1 := (half_lt_self (lt_min hη zero_lt_one)).le.trans (min_le_right _ _)
  have hdist : y s ∈ Metric.ball p δ := by
    rw [Metric.mem_ball, ← hy0]
    apply hclose
    simpa [Real.dist_eq, abs_of_pos hs] using hsη
  have hp' := mem_simplex_iff.mp hp
  have he : (∀ j, 0 ≤ e j) ∧ ∑ j, e j = 1 := isMixed_iff.mp (isMixed_single i)
  have hy' : (∀ j, 0 ≤ y s j) ∧ ∑ j, y s j = 1 := by
    constructor
    · intro j
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs₁) (hp'.1 j)) (mul_nonneg hs.le (he.1 j))
    · simp [y, Finset.sum_add_distrib, ← Finset.mul_sum, hp'.2, he.2]
  obtain ⟨x, hx0, hx⟩ := exists_isSolution_mulVec A hy'
  have hx0' : (∀ j, 0 ≤ x 0 j) ∧ ∑ j, x 0 j = 1 := hx0.symm ▸ hy'
  have hxi0 : 0 < x 0 i := by simpa [hx0, y, e, hpi] using hs
  have hxmem (t : ℝ) (ht : 0 ≤ t) := hx.mem_simplex hf hx0'.1 hx0'.2 ht
  have hxi (t : ℝ) (ht : 0 ≤ t) : 0 < x t i := hx.pos_of_pos hf hxi0 ht
  have hxle (t : ℝ) (ht : 0 ≤ t) : x t i ≤ 1 := by
    rw [← (hxmem t ht).2]
    exact Finset.single_le_sum (fun j _ => (hxmem t ht).1 j) (Finset.mem_univ i)
  have hgrow (t : ℝ) (ht : 0 ≤ t) : c ≤ gain (x t) :=
    (hnear (hstay x (isReplicatorSolution_iff_isSolution_mulVec.mpr hx)
      (mem_simplex_iff.mpr hx0') (hx0.symm ▸ hdist) t ht)).le
  have hlog (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun u => Real.log (x u i)) (gain (x t)) t := by
    have hd := (hx.hasDerivAt i t ht).log (hxi t ht).ne'
    rwa [meanFitness_mulVec, mul_div_cancel_left₀ _ (hxi t ht).ne'] at hd
  have hbound := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    (f := fun t => Real.log (x t i))
    (fun t ht => (hlog t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hlog t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hlog t (interior_subset ht)).deriv]
      exact hgrow t (interior_subset ht))
  let T := (1 - Real.log (x 0 i)) / c
  have hlog_le (t : ℝ) (ht : 0 ≤ t) : Real.log (x t i) ≤ 0 :=
    Real.log_nonpos (hxi t ht).le (hxle t ht)
  have hT : 0 ≤ T := div_nonneg (by linarith [hlog_le 0 le_rfl]) hc.le
  have hcT : c * T = 1 - Real.log (x 0 i) := by
    dsimp only [T]
    field_simp
  have hgrowth := hbound 0 le_rfl T hT hT
  rw [sub_zero, hcT] at hgrowth
  linarith [hlog_le T hT]

end WantedExt.Biology.Ecology.EvolutionaryFolkTheoremWanted
