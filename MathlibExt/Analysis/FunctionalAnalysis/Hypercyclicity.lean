/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Baire.Lemmas

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Hypercyclic operators and the hypercyclicity criterion

A bounded linear operator `T` on a normed space `E` is *hypercyclic* if
some vector has a dense orbit under iteration of `T`:
`{ x, T x, T² x, … }` is dense in `E`. Hypercyclicity is a
linear-dynamics counterpart of the Baire-category material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/BaireCategory.lean`: the
classical way to produce a hypercyclic vector is the *hypercyclicity
criterion* below, whose proof is a Baire argument. Given a countable
dense set `D`, dense sets `X₀, Y₀ ⊆ E`, a sequence `n_k → ∞`, and maps
`S k : E → E`, assume `T^(n_k) x → 0` on `X₀`, `S k y → 0` on `Y₀`, and
`T^(n_k) (S k y) → y` on `Y₀`. Every rational ball centered at `D` is met
by an orbit after every time threshold. The countable Baire intersection
of these open dense sets gives a vector with a dense orbit.
The explicit countable dense set can be supplied by
`TopologicalSpace.exists_countable_dense` on a separable space.

This is a companion to the Baire-category, bounded-operator, and
Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`. It is not one of the
72 v1 targets, and it is not in the pinned Mathlib or in base
MathlibExt: Mathlib has the Baire theorem and the Banach–Steinhaus
theorem, but no notion of a hypercyclic operator. Classical reference:
C. Kitai, "Invariant closed sets for linear operators", Ph.D. thesis,
University of Toronto, 1982, and R. M. Gethner and J. H. Shapiro,
"Universal vectors for operators on spaces of holomorphic functions",
*Proc. Amer. Math. Soc.* 100 (1987), 281–288. See also F. Bayart and
É. Matheron, *Dynamics of Linear Operators*, Cambridge University Press,
2009, Chapter 1.

## Main declarations

* `IsHypercyclic` : `T` has a vector whose orbit is dense.
* `isHypercyclic_of_criterion` : the hypercyclicity criterion.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity

open Filter Topology Set Metric

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- A bounded operator `T` is *hypercyclic* if some vector has a dense
orbit under iteration of `T`. -/
def IsHypercyclic (T : E →L[𝕜] E) : Prop :=
  ∃ x, Dense (Set.range fun n => (T ^ n) x)

/-- The *hypercyclicity criterion*: along a sequence `n_k → ∞`, suppose
`T^(n_k) x → 0` on the dense set `X₀`, `S k y → 0` on the dense set `Y₀`,
and `T^(n_k) (S k y) → y` on `Y₀`. Then `T` is hypercyclic.
The Baire proof combines all three eventual estimates and uses cofinality
to meet each rational ball after every prescribed time threshold.
This includes the full-iterate, exact-inverse special case by taking
`n_k = id` and converting the exact identities to constant convergence. -/
theorem isHypercyclic_of_criterion [BaireSpace E] [Nonempty E] (T : E →L[𝕜] E)
    (n_k : ℕ → ℕ) (hn_k : Tendsto n_k atTop atTop)
    (D X₀ Y₀ : Set E) (hDcount : D.Countable) (hDdense : Dense D)
    (hX₀ : Dense X₀) (hY₀ : Dense Y₀) (S : ℕ → E → E)
    (hT : ∀ x ∈ X₀, Tendsto (fun k => (T ^ n_k k) x) atTop (𝓝 0))
    (hS : ∀ y ∈ Y₀, Tendsto (fun k => S k y) atTop (𝓝 0))
    (hTS : ∀ y ∈ Y₀, Tendsto (fun k => (T ^ n_k k) (S k y)) atTop (𝓝 y)) :
    IsHypercyclic T := by
  have hCount : Countable D := hDcount
  -- Index rational balls and the time after which the orbit must meet them.
  let O : ({ p : D × ℚ // 0 < p.2 } × ℕ) → Set E :=
    fun p => ⋃ n : ℕ, ⋃ (_ : p.2 ≤ n),
      (T ^ n) ⁻¹' Metric.ball (p.1.1.1 : E) (p.1.1.2 : ℝ)
  have hOopen : ∀ p : { p : D × ℚ // 0 < p.2 } × ℕ, IsOpen (O p) := fun p =>
    isOpen_iUnion fun n => isOpen_iUnion fun _ =>
      ((T ^ n).continuous).isOpen_preimage _ Metric.isOpen_ball
  have hOdense : ∀ p : { p : D × ℚ // 0 < p.2 } × ℕ, Dense (O p) := by
    rintro ⟨p, N⟩
    have hqpos : (0 : ℝ) < (p.1.2 : ℝ) := by exact_mod_cast p.2
    have hballne : (Metric.ball (p.1.1 : E) (p.1.2 : ℝ)).Nonempty :=
      ⟨p.1.1, Metric.mem_ball_self hqpos⟩
    rw [dense_iff_inter_open]
    intro V hVopen hVne
    obtain ⟨x₀, hx₀V, hx₀X⟩ := hX₀.inter_open_nonempty V hVopen hVne
    obtain ⟨y₀, hy₀ball, hy₀Y⟩ :=
      hY₀.inter_open_nonempty _ Metric.isOpen_ball hballne
    obtain ⟨ε, hε, hballV⟩ := Metric.isOpen_iff.mp hVopen x₀ hx₀V
    obtain ⟨δ, hδ, hballU⟩ :=
      Metric.isOpen_iff.mp Metric.isOpen_ball y₀ hy₀ball
    have ev1 : ∀ᶠ n in atTop, ‖S n y₀‖ < ε := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hS y₀ hy₀Y)) ε hε
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have h := hN n hn
      rwa [dist_zero_right] at h
    have ev2 : ∀ᶠ k in atTop, ‖(T ^ n_k k) x₀‖ < δ / 2 := by
      obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp (hT x₀ hx₀X)) (δ / 2) (half_pos hδ)
      refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
      have h := hK k hk
      rwa [dist_zero_right] at h
    have ev3 : ∀ᶠ k in atTop, ‖(T ^ n_k k) (S k y₀) - y₀‖ < δ / 2 := by
      obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp (hTS y₀ hy₀Y)) (δ / 2) (half_pos hδ)
      refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
      have h := hK k hk
      rwa [dist_eq_norm] at h
    have ev4 : ∀ᶠ k in atTop, N ≤ n_k k := hn_k.eventually_ge_atTop N
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (ev1.and (ev2.and (ev3.and ev4))).exists
    refine ⟨x₀ + S k y₀, ?_, ?_⟩
    · -- The small right-inverse vector keeps the starting point in `V`.
      apply hballV
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hk1
    · -- The two output errors place the orbit in the ball after time `N`.
      refine Set.mem_iUnion.mpr ⟨n_k k, Set.mem_iUnion.mpr ⟨hk4, ?_⟩⟩
      rw [Set.mem_preimage]
      apply hballU
      rw [Metric.mem_ball, dist_eq_norm, map_add, add_sub_assoc]
      calc ‖(T ^ n_k k) x₀ + ((T ^ n_k k) (S k y₀) - y₀)‖
          ≤ ‖(T ^ n_k k) x₀‖ + ‖(T ^ n_k k) (S k y₀) - y₀‖ := norm_add_le _ _
        _ < δ / 2 + δ / 2 := add_lt_add hk2 hk3
        _ = δ := add_halves δ
  -- By Baire, the intersection of all the `O p` is dense, hence nonempty.
  have hDense : Dense (⋂ p : { p : D × ℚ // 0 < p.2 } × ℕ, O p) :=
    dense_iInter_of_isOpen hOopen hOdense
  obtain ⟨x, hx⟩ := hDense.nonempty
  refine ⟨x, ?_⟩
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨x₀, hx₀U⟩ := hUne
  obtain ⟨r, hr, hballU⟩ := Metric.isOpen_iff.mp hUopen x₀ hx₀U
  obtain ⟨d, hdBall, hdD⟩ :=
    hDdense.inter_open_nonempty _ Metric.isOpen_ball ⟨x₀, Metric.mem_ball_self (half_pos hr)⟩
  have hdr : dist d x₀ < r / 2 := Metric.mem_ball.mp hdBall
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hdr
  have hqpos : (0 : ℚ) < q := by
    have h : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt dist_nonneg hq1
    exact_mod_cast h
  have hxO : x ∈ O (⟨⟨⟨d, hdD⟩, q⟩, hqpos⟩, 0) := Set.mem_iInter.mp hx _
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxO
  obtain ⟨_, hn⟩ := Set.mem_iUnion.mp hn
  refine ⟨(T ^ n) x, ?_, ⟨n, rfl⟩⟩
  apply hballU
  have hyball : (T ^ n) x ∈ Metric.ball (d : E) (q : ℝ) := Set.mem_preimage.mp hn
  have hdist : dist ((T ^ n) x) x₀ < r := by
    have h1 : dist ((T ^ n) x) d < (q : ℝ) := Metric.mem_ball.mp hyball
    have h2 : dist ((T ^ n) x) x₀ ≤ dist ((T ^ n) x) d + dist d x₀ :=
      dist_triangle _ _ _
    have hq : (q : ℝ) < r / 2 := hq2
    linarith
  exact Metric.mem_ball.mpr hdist

end MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity
