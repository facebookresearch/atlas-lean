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
dense set `D`, dense sets `X₀, Y₀ ⊆ E`, and maps `S n : E → E` with
`Tⁿ x → 0` on `X₀`, `S n y → 0` on `Y₀`, and `Tⁿ (S n y) = y` on `Y₀`,
every ball centered at a point of `D` with rational radius is met by
some orbit, so a Baire intersection over the countably many such balls
gives a vector whose orbit meets every one of them, hence is dense.
The criterion is stated with an explicit countable dense set `D`
rather than a second-countability hypothesis, since second countability
is not inferred for `ℓ²` spaces in the pinned Mathlib.

This is a companion to the Baire-category, bounded-operator, and
Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`. It is not one of the
72 v1 targets, and it is not in the pinned Mathlib or in base
MathlibExt: Mathlib has the Baire theorem and the Banach–Steinhaus
theorem, but no notion of a hypercyclic operator. Classical reference:
G. Godefroy and J. H. Shapiro, "Operators with dense, invariant,
cyclic vector manifolds", *J. Funct. Anal.* 98 (1991), 229–269 (the
criterion); see also F. Bayart and É. Matheron, *Dynamics of Linear
Operators*, Cambridge University Press, 2009, Theorem 1.6.

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

/-- The *hypercyclicity criterion*: if `D` is a countable dense set,
`X₀` and `Y₀` are dense sets, and there are maps `S n` with `Tⁿ x → 0`
for `x ∈ X₀`, `S n y → 0` and `Tⁿ (S n y) = y` for `y ∈ Y₀`, then `T`
is hypercyclic. The proof is a Baire argument: for each ball centered
at a point of `D` with positive rational radius, the union over `n` of
the preimages `(Tⁿ)⁻¹'` of the ball is open and dense, so their
countable intersection is dense, and any vector in it has an orbit
meeting every such ball, hence is dense. -/
theorem isHypercyclic_of_criterion [BaireSpace E] [Nonempty E] (T : E →L[𝕜] E)
    (D X₀ Y₀ : Set E) (hDcount : D.Countable) (hDdense : Dense D)
    (hX₀ : Dense X₀) (hY₀ : Dense Y₀) (S : ℕ → E → E)
    (hT : ∀ x ∈ X₀, Tendsto (fun n => (T ^ n) x) atTop (𝓝 0))
    (hS : ∀ y ∈ Y₀, Tendsto (fun n => S n y) atTop (𝓝 0))
    (hTS : ∀ n, ∀ y ∈ Y₀, (T ^ n) (S n y) = y) :
    IsHypercyclic T := by
  have hCount : Countable D := hDcount
  -- Index the rational balls centered at points of `D`.
  let O : { p : D × ℚ // 0 < p.2 } → Set E :=
    fun p => ⋃ n : ℕ, (T ^ n) ⁻¹' Metric.ball (p.1.1 : E) (p.1.2 : ℝ)
  have hOopen : ∀ p : { p : D × ℚ // 0 < p.2 }, IsOpen (O p) := fun p =>
    isOpen_iUnion fun n => ((T ^ n).continuous).isOpen_preimage _ Metric.isOpen_ball
  have hOdense : ∀ p : { p : D × ℚ // 0 < p.2 }, Dense (O p) := by
    intro p
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
    have ev2 : ∀ᶠ n in atTop, ‖(T ^ n) x₀‖ < δ := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hT x₀ hx₀X)) δ hδ
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have h := hN n hn
      rwa [dist_zero_right] at h
    obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
    refine ⟨x₀ + S n y₀, ?_, ?_⟩
    · -- `x₀ + S n y₀` stays in `V` because `S n y₀` is small.
      apply hballV
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hn1
    · -- The orbit of `x₀ + S n y₀` meets the ball at step `n`.
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      have hcomp : (T ^ n) (x₀ + S n y₀) = (T ^ n) x₀ + y₀ := by
        rw [map_add, hTS n y₀ hy₀Y]
      rw [Set.mem_preimage, hcomp]
      apply hballU
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
      exact hn2
  -- By Baire, the intersection of all the `O p` is dense, hence nonempty.
  have hDense : Dense (⋂ p : { p : D × ℚ // 0 < p.2 }, O p) :=
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
  have hxO : x ∈ O ⟨⟨⟨d, hdD⟩, q⟩, hqpos⟩ := Set.mem_iInter.mp hx _
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxO
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
