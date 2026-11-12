/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Probability.Martingale.Basic
public import MathlibExt.Probability.Donsker
public import MathlibExt.Probability.LindebergFeller

import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ConditionalExpectation
import MathlibExt.Probability.ContinuousPathConvergence

/-!
# Martingale functional CLT in the Skorokhod space `D([0,T])`

This file sets up the Skorokhod space and proves a scoped martingale functional central limit
theorem with tightness, in the Skorokhod J1 topology.

## The D-space topology

* `skorokhodEDist`: the J1 distance
  `inf_φ max (sup_t |φ t - t|) (sup_t |f t - g (φ t)|)` over order isomorphisms `φ` of
  `[0,T]` (Billingsley 1999, (12.13)).
* `SkorokhodSpace T`: càdlàg real paths on `[0,T]` (Mathlib's `IsCadlag`), with the J1
  extended pseudo-metric (`PseudoEMetricSpace` instance) and its Borel σ-algebra.
  Weak convergence is Mathlib's `TendstoInDistribution` for this space.
* `SkorokhodSpace.ofContinuous`: the 1-Lipschitz inclusion `C([0,T]) → D([0,T])`.

## Main results

* `tendstoInDistribution_of_eventually_edist_le`: converging together (Slutsky) in any
  pseudo-emetric space, with closeness controlled by measurable bad sets.
* `tendstoInDistribution_skorokhod_of_tight_of_fdd`: transfer from `C` to `D`. Tightness in
  `C` plus finite-dimensional convergence of continuous processes `Y n` (together equivalent
  to `Y n → Z` in distribution in `C`), and jump control (uniform closeness of the `D`-valued
  `X n` to `Y n`), imply `X n → Z` in distribution in `D` with the J1 topology. This is
  Billingsley's Theorem 3.1 plus the `C → D` inclusion; it has no quadratic-variation
  hypothesis and no martingale structure, and all martingale content lives in its inputs.
* `tendstoInDistribution_skorokhodStepProcess`: the martingale FCLT in `D([0,1])` for
  square-integrable martingales with i.i.d. increments (the step process
  `(√n)⁻¹ ∑_{i < ⌊n t⌋} X i` converges to Brownian motion), proved by discharging the inputs
  of the transfer theorem. Tightness is not assumed: `isTightMeasureSet_donskerProcess_laws`
  derives it from Donsker convergence via Prokhorov's converse.
* Counting-process example, `compensatedBernoulliStep`:
  `tendstoInDistribution_compensatedBernoulliStep` (J1 convergence to `√(p(1-p)) • W`),
  `martingale_compensatedBernoulli` (martingale property),
  `condExp_sq_increment_compensatedBernoulli` and
  `tendsto_compensatedBernoulli_predictableQV` (informally, the predictable quadratic
  variation `p(1-p)⌊nt⌋/n` is deterministic and converges to `p(1-p) t`; no quadratic-variation
  object is defined, the first lemma computes conditional variances and the second is the
  deterministic limit),
  `lindebergConditionTriangular_compensatedBernoulli` (jump control).

## What is weakened relative to Rebolledo's theorem

* No general martingale CLT. For a martingale difference array, the implication
  "predictable quadratic variation converges in probability + Lindeberg ⇒ fdd convergence and
  tightness" is not proved. The transfer theorem takes tightness and fdd convergence as
  inputs. They are discharged (in `tendstoInDistribution_skorokhodStepProcess`) only for
  martingales with i.i.d. square-integrable increments, which includes the compensated
  Bernoulli counting process but not Nelson–Aalen-type martingales with random compensators.
* The predictable quadratic variation is not defined as a general object. For the example,
  the conditional variances of the increments are computed directly.
* The J1 structure is an extended pseudo-metric. Hausdorffness, separability, completeness
  (Billingsley's `d°`), and Borel = projection σ-algebra on `D` are not proved.
* Limits are stated as `σ • W`, not as `W ∘ A` with `A t = σ² t`. Their equality in law
  (Brownian scaling) is not formalized.

Sources: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999),
§§3, 7, 12, 14, 16. R. Rebolledo, *Central limit theorems for local martingales*,
Z. Wahrsch. Verw. Gebiete 51 (1980) 269–286. Andersen, Borgan, Gill, Keiding, *Statistical
Models Based on Counting Processes*, Springer (1993), §II.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open MathlibExt.Probability.DonskerWanted
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

/-- The **Skorokhod J1 extended distance** between two real paths on `[0, T]`:
the infimum over increasing bijections `φ` of `[0, T]` (order isomorphisms, the J1 time
changes) of `max (sup_t |φ t - t|) (sup_t |f t - g (φ t)|)`.

Source: Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), §12, eq. (12.13);
the infimum over `Λ` of `‖λ - id‖ ∨ ‖x - y ∘ λ‖`. Here the comparison is written as
`f t` against `g (φ t)`, which is the same quantity after replacing `φ` by its inverse. -/
def skorokhodEDist {T : ℝ} (f g : Set.Icc (0 : ℝ) T → ℝ) : ℝ≥0∞ :=
  ⨅ φ : Set.Icc (0 : ℝ) T ≃o Set.Icc (0 : ℝ) T,
    max (⨆ t, edist (φ t) t) (⨆ t, edist (f t) (g (φ t)))

/-- The J1 distance from a path to itself is `0`. -/
theorem skorokhodEDist_self {T : ℝ} (f : Set.Icc (0 : ℝ) T → ℝ) :
    skorokhodEDist f f = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le (OrderIso.refl _) ?_
  simp

/-- One direction of symmetry of the J1 distance (invert the time change). -/
theorem skorokhodEDist_comm_le {T : ℝ} (f g : Set.Icc (0 : ℝ) T → ℝ) :
    skorokhodEDist f g ≤ skorokhodEDist g f := by
  refine le_iInf fun ψ => iInf_le_of_le ψ.symm ?_
  refine max_le_max (iSup_le fun t => ?_) (iSup_le fun t => ?_)
  · refine le_iSup_of_le (ψ.symm t) ?_
    rw [ψ.apply_symm_apply, edist_comm]
  · refine le_iSup_of_le (ψ.symm t) ?_
    rw [ψ.apply_symm_apply, edist_comm]

/-- The J1 distance is symmetric. -/
theorem skorokhodEDist_comm {T : ℝ} (f g : Set.Icc (0 : ℝ) T → ℝ) :
    skorokhodEDist f g = skorokhodEDist g f :=
  le_antisymm (skorokhodEDist_comm_le f g) (skorokhodEDist_comm_le g f)

/-- Triangle inequality for the J1 distance (compose time changes). -/
theorem skorokhodEDist_triangle {T : ℝ} (f g h : Set.Icc (0 : ℝ) T → ℝ) :
    skorokhodEDist f h ≤ skorokhodEDist f g + skorokhodEDist g h := by
  refine ENNReal.le_iInf_add_iInf fun φ₁ φ₂ => iInf_le_of_le (φ₁.trans φ₂) ?_
  refine max_le (iSup_le fun t => ?_) (iSup_le fun t => ?_)
  · calc edist ((φ₁.trans φ₂) t) t ≤ edist (φ₂ (φ₁ t)) (φ₁ t) + edist (φ₁ t) t :=
          edist_triangle _ _ _
      _ ≤ (⨆ s, edist (φ₁ s) s) + ⨆ s, edist (φ₂ s) s := by
          exact add_le_add (le_iSup (fun s => edist (φ₂ s) s) (φ₁ t))
            (le_iSup (fun s => edist (φ₁ s) s) t) |>.trans_eq (add_comm _ _)
      _ ≤ _ := add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc edist (f t) (h ((φ₁.trans φ₂) t))
        ≤ edist (f t) (g (φ₁ t)) + edist (g (φ₁ t)) (h (φ₂ (φ₁ t))) :=
          edist_triangle _ _ _
      _ ≤ (⨆ s, edist (f s) (g (φ₁ s))) + ⨆ s, edist (g s) (h (φ₂ s)) :=
          add_le_add (le_iSup (fun s => edist (f s) (g (φ₁ s))) t)
            (le_iSup (fun s => edist (g s) (h (φ₂ s))) (φ₁ t))
      _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)

/-- The J1 distance is bounded by the uniform distance (take the identity time change). -/
theorem skorokhodEDist_le_iSup_edist {T : ℝ} (f g : Set.Icc (0 : ℝ) T → ℝ) :
    skorokhodEDist f g ≤ ⨆ t, edist (f t) (g t) := by
  refine iInf_le_of_le (OrderIso.refl _) ?_
  simp

/-- The **Skorokhod space** `D([0, T], ℝ)`: real càdlàg paths on `[0, T]` (right-continuous
with left limits, Mathlib's `IsCadlag`). It carries the J1 extended pseudo-metric
`skorokhodEDist` and its Borel σ-algebra.

Source: Billingsley (1999), §12 (space `D` with the Skorokhod J1 topology). Only the extended
pseudo-metric axioms are proved here; separability, completeness of the Billingsley metric
`d°`, and the identification of the Borel σ-algebra with the projection σ-algebra are not. -/
def SkorokhodSpace (T : ℝ) : Type :=
  {f : Set.Icc (0 : ℝ) T → ℝ // IsCadlag f}

namespace SkorokhodSpace

variable {T : ℝ}

instance : CoeFun (SkorokhodSpace T) (fun _ => Set.Icc (0 : ℝ) T → ℝ) :=
  ⟨fun f => f.1⟩

/-- Build a Skorokhod path from a càdlàg function. -/
def mk (f : Set.Icc (0 : ℝ) T → ℝ) (hf : IsCadlag f) : SkorokhodSpace T := ⟨f, hf⟩

/-- Evaluation of `mk`. -/
@[simp] theorem mk_apply (f : Set.Icc (0 : ℝ) T → ℝ) (hf : IsCadlag f) (t : Set.Icc (0 : ℝ) T) :
    mk f hf t = f t := rfl

/-- Every Skorokhod path is càdlàg. -/
theorem isCadlag (f : SkorokhodSpace T) : IsCadlag (f : Set.Icc (0 : ℝ) T → ℝ) := f.2

/-- Skorokhod paths are determined by their values. -/
@[ext] theorem ext {f g : SkorokhodSpace T} (h : ∀ t, f t = g t) : f = g :=
  Subtype.ext (funext h)

instance : PseudoEMetricSpace (SkorokhodSpace T) where
  edist f g := skorokhodEDist f.1 g.1
  edist_self f := skorokhodEDist_self f.1
  edist_comm f g := skorokhodEDist_comm f.1 g.1
  edist_triangle f g h := skorokhodEDist_triangle f.1 g.1 h.1

/-- The extended distance on `SkorokhodSpace T` is the J1 distance. -/
theorem edist_def (f g : SkorokhodSpace T) : edist f g = skorokhodEDist f.1 g.1 := rfl

/-- The J1 distance is at most the uniform distance. -/
theorem edist_le_iSup_edist (f g : SkorokhodSpace T) :
    edist f g ≤ ⨆ t, edist (f t) (g t) :=
  skorokhodEDist_le_iSup_edist f.1 g.1

/-- Borel σ-algebra of the J1 topology. -/
instance : MeasurableSpace (SkorokhodSpace T) := borel _

instance : BorelSpace (SkorokhodSpace T) := ⟨rfl⟩

/-- A continuous path, viewed in the Skorokhod space. -/
def ofContinuous (f : C(Set.Icc (0 : ℝ) T, ℝ)) : SkorokhodSpace T :=
  ⟨f, f.continuous.isCadlag⟩

/-- Evaluation of `ofContinuous`. -/
@[simp] theorem ofContinuous_apply (f : C(Set.Icc (0 : ℝ) T, ℝ)) (t : Set.Icc (0 : ℝ) T) :
    ofContinuous f t = f t := rfl

/-- The inclusion `C([0,T]) → D([0,T])` is `1`-Lipschitz from the uniform metric to J1. -/
theorem lipschitzWith_ofContinuous :
    LipschitzWith 1 (ofContinuous : C(Set.Icc (0 : ℝ) T, ℝ) → SkorokhodSpace T) := by
  intro f g
  rw [ENNReal.coe_one, one_mul]
  refine (edist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  simp only [ofContinuous_apply, edist_dist]
  exact ENNReal.ofReal_le_ofReal (ContinuousMap.dist_apply_le_dist t)

/-- The inclusion `C([0,T]) → D([0,T])` is continuous. -/
theorem continuous_ofContinuous :
    Continuous (ofContinuous : C(Set.Icc (0 : ℝ) T, ℝ) → SkorokhodSpace T) :=
  lipschitzWith_ofContinuous.continuous

end SkorokhodSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- **Converging together in a pseudo-emetric space** (Slutsky-type lemma; Billingsley (1999),
Theorem 3.1). If `Y n → Z` in distribution, and for every `ε > 0` the paths `X n` and `Y n`
are `ε`-close outside measurable sets `A n` whose probabilities tend to `0`, then `X n → Z`
in distribution.

Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub` needs a seminormed group; the J1
space is not one, so this version works with an arbitrary pseudo-emetric space and controls
the distance through explicit measurable bad sets (no measurability of `edist (X n) (Y n)`
is required). -/
theorem tendstoInDistribution_of_eventually_edist_le
    {E : Type*} [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X Y : ℕ → Ω → E) (Z : Ω' → E)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P')
    (hX : ∀ n, AEMeasurable (X n) P)
    (hXY : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => P.real (A n)) atTop (𝓝 0) ∧
      ∀ n, ∀ ω ∉ A n, edist (X n ω) (Y n ω) ≤ ENNReal.ofReal ε) :
    TendstoInDistribution X atTop Z (fun _ => P) P' := by
  refine ⟨hX, hY.aemeasurable_limit, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hM⟩ ⟨L, hL⟩
  have hYF := (tendsto_iff_forall_lipschitz_integral_tendsto.1 hY.tendsto) F ⟨M, hM⟩ ⟨L, hL⟩
  simp only [ProbabilityMeasure.coe_mk] at hYF ⊢
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hYmeas := hY.forall_aemeasurable
  have hint : ∀ (W : Ω → E), AEMeasurable W P → Integrable (fun ω => F (W ω)) P := by
    intro W hW
    refine Integrable.of_bound
      (hL.continuous.measurable.comp_aemeasurable hW).aestronglyMeasurable
      (‖F (Y 0 ω₀)‖ + M) (ae_of_all _ fun ω => ?_)
    have h := hM (W ω) (Y 0 ω₀)
    rw [Real.dist_eq] at h
    have := abs_sub_abs_le_abs_sub (F (W ω)) (F (Y 0 ω₀))
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  have hmapX : ∀ n, ∫ x, F x ∂(P.map (X n)) = ∫ ω, F (X n ω) ∂P := fun n =>
    integral_map (hX n) hL.continuous.aestronglyMeasurable
  have hmapY : ∀ n, ∫ x, F x ∂(P.map (Y n)) = ∫ ω, F (Y n ω) ∂P := fun n =>
    integral_map (hYmeas n) hL.continuous.aestronglyMeasurable
  -- the difference of the two integrals tends to `0`
  have hdiff : Tendsto (fun n => ∫ ω, F (X n ω) ∂P - ∫ ω, F (Y n ω) ∂P) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    set ε : ℝ := η / (2 * ((L : ℝ) + 1)) with hε_def
    have hLpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
    have hε : 0 < ε := by positivity
    have hLε : (L : ℝ) * ε < η / 2 := by
      rw [hε_def]
      rw [show (L : ℝ) * (η / (2 * ((L : ℝ) + 1))) = (η / 2) * ((L : ℝ) / ((L : ℝ) + 1)) by
        field_simp]
      have : (L : ℝ) / ((L : ℝ) + 1) < 1 := by
        rw [div_lt_one hLpos]; linarith
      nlinarith
    obtain ⟨A, hAmeas, hAlim, hAclose⟩ := hXY ε hε
    have hMA : Tendsto (fun n => M * P.real (A n)) atTop (𝓝 0) := by
      simpa using hAlim.const_mul M
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hMA (η / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hbound : ∀ ω, |F (X n ω) - F (Y n ω)| ≤
        (L : ℝ) * ε + (A n).indicator (fun _ => M) ω := by
      intro ω
      by_cases hω : ω ∈ A n
      · rw [Set.indicator_of_mem hω]
        have h := hM (X n ω) (Y n ω)
        rw [Real.dist_eq] at h
        have : 0 ≤ (L : ℝ) * ε := by positivity
        linarith
      · rw [Set.indicator_of_notMem hω, add_zero]
        have h1 := hL.edist_le_mul (X n ω) (Y n ω)
        have h2 : (L : ℝ≥0∞) * edist (X n ω) (Y n ω) ≤ ENNReal.ofReal ((L : ℝ) * ε) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
          exact mul_le_mul_right (hAclose n ω hω) _
        have h3 := h1.trans h2
        rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), Real.dist_eq] at h3
        exact h3
    have hint_sub : Integrable (fun ω => F (X n ω) - F (Y n ω)) P :=
      (hint _ (hX n)).sub (hint _ (hYmeas n))
    have hint_bd : Integrable (fun ω => (L : ℝ) * ε + (A n).indicator (fun _ => M) ω) P :=
      (integrable_const _).add ((integrable_const M).indicator (hAmeas n))
    have hle : |∫ ω, F (X n ω) ∂P - ∫ ω, F (Y n ω) ∂P| ≤ (L : ℝ) * ε + M * P.real (A n) := by
      rw [← integral_sub (hint _ (hX n)) (hint _ (hYmeas n))]
      calc |∫ ω, F (X n ω) - F (Y n ω) ∂P|
          ≤ ∫ ω, |F (X n ω) - F (Y n ω)| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ ω, (L : ℝ) * ε + (A n).indicator (fun _ => M) ω ∂P :=
            integral_mono hint_sub.abs hint_bd hbound
        _ = (L : ℝ) * ε + M * P.real (A n) := by
            rw [integral_add (integrable_const _) ((integrable_const M).indicator (hAmeas n)),
              integral_const, integral_indicator_const M (hAmeas n)]
            simp [mul_comm]
    have hNn := hN n hn
    rw [Real.dist_eq, sub_zero] at hNn ⊢
    have : M * P.real (A n) < η / 2 := lt_of_abs_lt hNn
    linarith
  have hsum := hdiff.add (by simpa only [hmapY] using hYF)
  simp only [sub_add_cancel, zero_add] at hsum
  simpa only [hmapX] using hsum

set_option backward.isDefEq.respectTransparency.types false in
/-- **Transfer of functional limit theorems from `C([0,T])` to `D([0,T])` (continuous limit).**

Let `X n` be `D([0,T])`-valued processes and `Y n` continuous processes (for instance linear
interpolations of `X n`). Assume
* *tightness*: the laws of `Y n` on `C([0,T])` form a tight family;
* *finite-dimensional convergence*: for every finite set of times `I`, `(Y n t)_{t ∈ I}`
  converges in distribution to `(Z t)_{t ∈ I}`;
* *jump control*: for each `ε > 0`, outside measurable sets of vanishing probability,
  `sup_t |X n t - Y n t| ≤ ε`.

Then `X n → Z` in distribution in the Skorokhod J1 topology on `D([0,T])`.

Source: Billingsley (1999), Theorem 7.5 (tightness + fdd in `C`), Theorem 3.1 (converging
together), and the J1-vs-uniform comparison of §12; this is the route used for Donsker's
theorem in `D` (Billingsley, Theorem 14.1/16.1). The tightness and fdd hypotheses together
amount to `Y n → Z` in distribution in `C`, so this is converging together (Theorem 3.1) plus
the `C → D` inclusion. It has no quadratic-variation hypothesis and no martingale structure:
the martingale CLT that would produce finite-dimensional convergence and the tightness estimate
are inputs. `tendstoInDistribution_skorokhodStepProcess` discharges them for i.i.d.
increments. -/
theorem tendstoInDistribution_skorokhod_of_tight_of_fdd
    {T : ℝ} (hT : 0 < T)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → SkorokhodSpace T) (Y : ℕ → Ω → C(Set.Icc (0 : ℝ) T, ℝ))
    (Z : Ω' → C(Set.Icc (0 : ℝ) T, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P)
    (hZ : AEMeasurable Z P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map (Y n)))
    (hfdd : ∀ I : Finset (Set.Icc (0 : ℝ) T),
      TendstoInDistribution (fun n ω => I.restrict (fun t => Y n ω t)) atTop
        (fun ω => I.restrict (fun t => Z ω t)) (fun _ => P) P')
    (hjump : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => P.real (A n)) atTop (𝓝 0) ∧
      ∀ n, ∀ ω ∉ A n, ∀ t, |X n ω t - Y n ω t| ≤ ε) :
    TendstoInDistribution X atTop (fun ω => SkorokhodSpace.ofContinuous (Z ω))
      (fun _ => P) P' := by
  let μs : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ) := fun n => ⟨P.map (Y n), inferInstance⟩
  let μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ) := ⟨P'.map Z, inferInstance⟩
  have hconv : Tendsto μs atTop (𝓝 μ) := by
    refine ContinuousPathConvergence.tendsto_continuousPath_of_tight_of_finset_eval T hT μs μ
      ?_ ?_
    · convert htight using 1
      ext ν
      simp [μs]
    · intro I
      let e := fun f : C(Set.Icc (0 : ℝ) T, ℝ) => I.restrict (fun t => f t)
      have he : Continuous e :=
        continuous_pi fun t => continuous_eval_const (t : Set.Icc (0 : ℝ) T)
      have h1 : ∀ n, (μs n).map e =
          (⟨P.map (fun ω => e (Y n ω)), inferInstance⟩ : ProbabilityMeasure _) := by
        intro n
        apply ProbabilityMeasure.toMeasure_injective
        simp only [ProbabilityMeasure.toMeasure_map, μs, ProbabilityMeasure.coe_mk]
        exact AEMeasurable.map_map_of_aemeasurable he.aemeasurable (hY n)
      have h2 : μ.map e =
          (⟨P'.map (fun ω => e (Z ω)), inferInstance⟩ : ProbabilityMeasure _) := by
        apply ProbabilityMeasure.toMeasure_injective
        simp only [ProbabilityMeasure.toMeasure_map, μ, ProbabilityMeasure.coe_mk]
        exact AEMeasurable.map_map_of_aemeasurable he.aemeasurable hZ
      change Tendsto (fun n => (μs n).map e) atTop (𝓝 (μ.map e))
      rw [funext h1, h2]
      exact (hfdd I).tendsto
  have hYZ : TendstoInDistribution Y atTop Z (fun _ => P) P' := ⟨hY, hZ, hconv⟩
  have hYZ' := hYZ.continuous_comp SkorokhodSpace.continuous_ofContinuous
  refine tendstoInDistribution_of_eventually_edist_le X _ _ hYZ' hX ?_
  intro ε hε
  obtain ⟨A, hAm, hAlim, hAclose⟩ := hjump ε hε
  refine ⟨A, hAm, hAlim, fun n ω hω => ?_⟩
  refine (SkorokhodSpace.edist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (hAclose n ω hω t)

/-! ### Normalized partial-sum step processes in `D([0,1])` -/

/-- The unit step `t ↦ 1{c ≤ t}` on `[0, T]` (a càdlàg path, `isCadlag_stepInd`). -/
def stepInd (T c : ℝ) (t : Set.Icc (0 : ℝ) T) : ℝ :=
  if c ≤ (t : ℝ) then 1 else 0

private lemma stepInd_nonneg (T c : ℝ) (t : Set.Icc (0 : ℝ) T) : 0 ≤ stepInd T c t := by
  unfold stepInd; split_ifs <;> norm_num

private lemma stepInd_le_one (T c : ℝ) (t : Set.Icc (0 : ℝ) T) : stepInd T c t ≤ 1 := by
  unfold stepInd; split_ifs <;> norm_num

theorem isCadlag_stepInd (T c : ℝ) : IsCadlag (stepInd T c) where
  isRightContinuous a := by
    unfold ContinuousWithinAt
    refine tendsto_const_nhds.congr' ?_
    by_cases hca : c ≤ (a : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hcx : c ≤ (x : ℝ) := hca.trans (le_of_lt (Subtype.coe_lt_coe.2 hx))
      simp [stepInd, hca, hcx]
    · replace hca := not_le.1 hca
      have hopen : IsOpen {x : Set.Icc (0 : ℝ) T | (x : ℝ) < c} :=
        isOpen_lt continuous_subtype_val continuous_const
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hca)] with x hx
      simp [stepInd, not_le.2 hca, not_le.2 hx]
  tendsto_nhdsLT x := by
    by_cases hcx : c < (x : ℝ)
    · refine ⟨1, tendsto_const_nhds.congr' ?_⟩
      have hopen : IsOpen {y : Set.Icc (0 : ℝ) T | c < (y : ℝ)} :=
        isOpen_lt continuous_const continuous_subtype_val
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hcx)] with y hy
      simp [stepInd, hy.le]
    · replace hcx := not_lt.1 hcx
      refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyc : ¬ c ≤ (y : ℝ) := not_le.2 ((Subtype.coe_lt_coe.2 hy).trans_le hcx)
      simp [stepInd, hyc]

/-- Underlying function of the normalized partial-sum step path on `[0,1]` built from
`n` increments `y : Fin n → ℝ`: `t ↦ (√n)⁻¹ * ∑_{i < n} y i * 1{(i+1)/n ≤ t}`. -/
def stepPathFun (n : ℕ) (y : Fin n → ℝ) (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i : Fin n, y i * stepInd 1 (((i : ℕ) + 1 : ℝ) / n) t

/-- Step paths are càdlàg (finite sums of càdlàg unit steps). -/
theorem isCadlag_stepPathFun (n : ℕ) (y : Fin n → ℝ) : IsCadlag (stepPathFun n y) := by
  have hsum : ∀ s : Finset (Fin n),
      IsCadlag (fun t => ∑ i ∈ s, y i * stepInd 1 (((i : ℕ) + 1 : ℝ) / n) t) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((isCadlag_stepInd 1 _).continuous_comp (continuous_const_mul (y a))).add ih
  exact (hsum Finset.univ).continuous_comp (continuous_const_mul (Real.sqrt n)⁻¹)

private lemma sum_fin_stepInd_eq (n : ℕ) (x : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) :
    ∑ i : Fin n, x i * stepInd 1 (((i : ℕ) + 1 : ℝ) / n) t =
      ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), x i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg hnR.le t.2.1
  have hm_le : Nat.floor ((n : ℝ) * t.1) ≤ n :=
    Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_left t.2.2 hnR.le)
  rw [Fin.sum_univ_eq_sum_range (fun i => x i * stepInd 1 (((i : ℕ) + 1 : ℝ) / n) t)]
  have hiff : ∀ i : ℕ, ((i : ℝ) + 1) / n ≤ t.1 ↔ i < Nat.floor ((n : ℝ) * t.1) := by
    intro i
    rw [div_le_iff₀ hnR, Nat.lt_iff_add_one_le, Nat.le_floor_iff ht0, mul_comm]
    push_cast; rfl
  calc ∑ i ∈ Finset.range n, x i * stepInd 1 (((i : ℕ) + 1 : ℝ) / n) t
      = ∑ i ∈ Finset.range n, if i < Nat.floor ((n : ℝ) * t.1) then x i else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [stepInd, hiff i]
        split_ifs <;> simp
    _ = ∑ i ∈ (Finset.range n).filter (· < Nat.floor ((n : ℝ) * t.1)), x i :=
        (Finset.sum_filter _ _).symm
    _ = ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), x i := by
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨h.trans_le hm_le, h⟩

/-- The normalized partial-sum step path in `D([0,1])` built from `n` increments. -/
def stepPath (n : ℕ) (y : Fin n → ℝ) : SkorokhodSpace 1 :=
  SkorokhodSpace.mk (stepPathFun n y) (isCadlag_stepPathFun n y)

/-- The step-path map `ℝⁿ → D([0,1])` is `n`-Lipschitz (sup norm to J1). -/
theorem lipschitzWith_stepPath (n : ℕ) : LipschitzWith (n : ℝ≥0) (stepPath n) := by
  intro y z
  refine (SkorokhodSpace.edist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  simp only [stepPath, SkorokhodSpace.mk_apply, stepPathFun]
  rw [edist_dist, edist_dist, Real.dist_eq, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [show ((n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) by simp,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : (Real.sqrt n)⁻¹ ≤ 1 ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inr h
    · left
      refine inv_le_one_of_one_le₀ ?_
      exact Real.one_le_sqrt.2 (by exact_mod_cast h)
  rcases hsq with hsq | rfl
  · rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    calc (Real.sqrt n)⁻¹ * |∑ i : Fin n, (y i * stepInd 1 _ t - z i * stepInd 1 _ t)|
        ≤ 1 * ∑ i : Fin n, dist y z := by
          refine mul_le_mul hsq ?_ (abs_nonneg _) zero_le_one
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [← sub_mul, abs_mul, abs_of_nonneg (stepInd_nonneg _ _ _)]
          calc |y i - z i| * stepInd 1 _ t ≤ |y i - z i| * 1 :=
                mul_le_mul_of_nonneg_left (stepInd_le_one _ _ _) (abs_nonneg _)
            _ = dist (y i) (z i) := by rw [mul_one, Real.dist_eq]
            _ ≤ dist y z := dist_le_pi_dist y z i
      _ = (n : ℝ) * dist y z := by simp
  · simp

/-- The step-path map is continuous, hence Borel measurable. -/
theorem continuous_stepPath (n : ℕ) : Continuous (stepPath n) :=
  (lipschitzWith_stepPath n).continuous

/-- The normalized partial-sum **step process** `t ↦ (√n)⁻¹ ∑_{i < ⌊n t⌋} X i` in `D([0,1])`;
see `skorokhodStepProcess_apply`. Unlike Donsker's polygonal process it is a pure-jump
càdlàg path, the natural path of a discrete-time martingale embedded in continuous time. -/
def skorokhodStepProcess {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : SkorokhodSpace 1 :=
  stepPath n (fun i => X i ω)

/-- Explicit partial-sum formula: `(∑_{i < ⌊n t⌋} X i ω) / √n`. -/
theorem skorokhodStepProcess_apply {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) :
    skorokhodStepProcess n X ω t =
      (∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), X i ω) / Real.sqrt n := by
  simp only [skorokhodStepProcess, stepPath, SkorokhodSpace.mk_apply, stepPathFun]
  rw [sum_fin_stepInd_eq n (fun i => X i ω) t, inv_mul_eq_div]

/-- The step process is a measurable `D([0,1])`-valued random variable. -/
theorem measurable_skorokhodStepProcess {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (skorokhodStepProcess n X) :=
  (continuous_stepPath n).measurable.comp (measurable_pi_iff.2 fun i => hX i)

/-! ### Donsker's theorem in `D([0,1])` for the step process -/

private lemma abs_step_sub_polygon_le {Ω : Type*} (n : ℕ) (hn : n ≠ 0) (X : ℕ → Ω → ℝ) (ω : Ω)
    (ε : ℝ) (h : ∀ i < n, |X i ω| ≤ ε * Real.sqrt n) (t : Set.Icc (0 : ℝ) 1) :
    |skorokhodStepProcess n X ω t - donskerProcess n X ω t| ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hε : 0 ≤ ε * Real.sqrt n := (abs_nonneg _).trans (h 0 (Nat.pos_of_ne_zero hn))
  rw [skorokhodStepProcess_apply, donskerProcess_apply_eq n X ω t hn, ← sub_div, abs_div,
    abs_of_pos hsq, div_le_iff₀ hsq]
  set m := Nat.floor ((n : ℝ) * t.1) with hm
  rw [sub_add_cancel_left, abs_neg]
  split_ifs with hmn
  · have ht0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg hnR.le t.2.1
    have hfrac0 : 0 ≤ (n : ℝ) * t.1 - m := Nat.zero_le_self_sub_floor ht0
    have hfrac1 : (n : ℝ) * t.1 - m ≤ 1 := (Nat.self_sub_floor_lt_one _).le
    rw [abs_mul, abs_of_nonneg hfrac0]
    calc |X m ω| * ((n : ℝ) * t.1 - m) ≤ |X m ω| * 1 :=
          mul_le_mul_of_nonneg_left hfrac1 (abs_nonneg _)
      _ ≤ ε * Real.sqrt n := by rw [mul_one]; exact h m hmn
  · simpa using hε

private lemma tendsto_measureReal_large_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n))
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) (hMemLp : MemLp (X 0) 2 P)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P.real (⋃ i ∈ Finset.range n, {ω | ε * Real.sqrt n < |X i ω|}))
      atTop (𝓝 0) := by
  let F : ℕ → Ω → ℝ := fun n =>
    Set.indicator {ω | ε * Real.sqrt n < |X 0 ω|} (fun ω => X 0 ω ^ 2)
  have hset : ∀ n : ℕ, MeasurableSet {ω | ε * Real.sqrt n < |X 0 ω|} := fun n =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hMeas 0))
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    ((hMeas 0).pow_const 2).indicator (hset n)
  have hsqint : Integrable (fun ω => X 0 ω ^ 2) P := hMemLp.integrable_sq
  have hFint : ∀ n, Integrable (F n) P := fun n => hsqint.indicator (hset n)
  have hFnonneg : ∀ n ω, 0 ≤ F n ω := fun n ω =>
    Set.indicator_nonneg (fun ω _ => sq_nonneg (X 0 ω)) ω
  -- dominated convergence: the truncated second moments vanish
  have hFlim : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (F := F) (f := fun _ => (0 : ℝ))
      (fun ω => X 0 ω ^ 2) (fun n => (hFmeas n).aestronglyMeasurable) hsqint
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg n ω)]
        exact Set.indicator_le_self' (fun ω _ => sq_nonneg (X 0 ω)) ω)
      (ae_of_all _ fun ω => by
        refine tendsto_const_nhds.congr' ?_
        have hsqrt : Tendsto (fun n : ℕ => ε * Real.sqrt n) atTop atTop :=
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
        filter_upwards [hsqrt.eventually_ge_atTop |X 0 ω|] with n hn
        simp [F, Set.indicator_of_notMem, not_lt.2 hn])
    simpa using this
  -- union bound plus Chebyshev on the truncated square
  have hbound : ∀ n : ℕ,
      P.real (⋃ i ∈ Finset.range n, {ω | ε * Real.sqrt n < |X i ω|}) ≤
        (∫ ω, F n ω ∂P) / ε ^ 2 := by
    intro n
    have hident : ∀ i, P.real {ω | ε * Real.sqrt n < |X i ω|} =
        P.real {ω | ε * Real.sqrt n < |X 0 ω|} := by
      intro i
      have hs : MeasurableSet {x : ℝ | ε * Real.sqrt n < |x|} :=
        measurableSet_lt measurable_const continuous_abs.measurable
      exact congrArg ENNReal.toReal ((hIdent i).measure_mem_eq hs)
    have hcheb : (ε ^ 2 * n) * P.real {ω | ε * Real.sqrt n < |X 0 ω|} ≤ ∫ ω, F n ω ∂P := by
      refine le_trans ?_ (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (hFnonneg n))
        (hFint n) (ε ^ 2 * n))
      refine mul_le_mul_of_nonneg_left (measureReal_mono ?_) (by positivity)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have hc : 0 ≤ ε * Real.sqrt n := by positivity
      have hsqx : (ε * Real.sqrt n) ^ 2 ≤ X 0 ω ^ 2 := by
        rw [← sq_abs (X 0 ω)]
        exact pow_le_pow_left₀ hc hω.le 2
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hsqx
      simpa [F, Set.indicator_of_mem, hω] using hsqx
    calc P.real (⋃ i ∈ Finset.range n, {ω | ε * Real.sqrt n < |X i ω|})
        ≤ ∑ i ∈ Finset.range n, P.real {ω | ε * Real.sqrt n < |X i ω|} :=
          measureReal_biUnion_finset_le _ _
      _ = n * P.real {ω | ε * Real.sqrt n < |X 0 ω|} := by
          simp [hident]
      _ ≤ (∫ ω, F n ω ∂P) / ε ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [hcheb]
  refine squeeze_zero (fun n => measureReal_nonneg) hbound ?_
  simpa using hFlim.div_const (ε ^ 2)

/-- **Tightness** of Donsker's polygonal laws on `C([0,1])`. This is a consequence of Donsker
convergence (`donsker_invariance_principle`) via Prokhorov's converse: the laws converge
weakly, so their closure in the space of laws is compact, hence the family is tight. It feeds
the tightness input of `tendstoInDistribution_skorokhod_of_tight_of_fdd` in
`tendstoInDistribution_skorokhodStepProcess`.

Source: Billingsley (1999), Theorem 5.2 (Prokhorov, converse half) applied to Theorem 8.2. -/
theorem isTightMeasureSet_donskerProcess_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) (hInt : Integrable (X 0) P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    IsTightMeasureSet (Set.range fun n => P.map (fun ω => donskerProcess n X ω)) := by
  obtain ⟨Y, -, hconv⟩ :=
    donsker_invariance_principle X hMeas hIndep hIdent hInt hMemLp hMean hVar B hB
  let μs : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) 1, ℝ) := fun n =>
    ⟨P.map (fun ω => donskerProcess n X ω), inferInstance⟩
  have hK := hconv.tendsto.isCompact_insert_range
  have hcl : IsCompact (closure (Set.range μs)) :=
    hK.closure_of_subset (Set.subset_insert _ _)
  convert isTightMeasureSet_of_isCompact_closure hcl using 1
  ext ν
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨μs n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

/-- **Donsker's invariance principle in the Skorokhod space `D([0,1])`** for the normalized
partial-sum step process `t ↦ (√n)⁻¹ ∑_{i < ⌊n t⌋} X i` of an i.i.d. mean-zero, variance-one
sequence: it converges in distribution, in the Skorokhod J1 topology, to a continuous version
of Brownian motion on `[0,1]`.

This is the martingale functional CLT restricted to square-integrable martingales with
i.i.d. increments, obtained by discharging the three inputs of
`tendstoInDistribution_skorokhod_of_tight_of_fdd` with `Y n` Donsker's polygonal process:
* tightness: `isTightMeasureSet_donskerProcess_laws` (from Donsker convergence via Prokhorov's
  converse);
* finite-dimensional convergence: continuous mapping applied to `donsker_invariance_principle`;
* jump control: `sup_t |step - polygon| ≤ max_{i<n} |X i| / √n`, which tends to `0` in
  probability (proved here from the second moment of `X 0`).
Mathematically the step process is a martingale in `k = ⌊n t⌋` with deterministic predictable
quadratic variation `⌊n t⌋ / n → t`; those facts are formalized only for the Bernoulli
example (`martingale_compensatedBernoulli`, `condExp_sq_increment_compensatedBernoulli`).

Source: Billingsley (1999), Theorem 16.1 (Donsker in `D`); proof route: Donsker in `C`
(Theorem 8.2, here `donsker_invariance_principle`), sup-distance comparison of the step and
polygonal processes, and converging together (Theorem 3.1). -/
theorem tendstoInDistribution_skorokhodStepProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n)) (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) (hInt : Integrable (X 0) P)
    (hMemLp : MemLp (X 0) 2 P) (hMean : P[X 0] = 0) (hVar : Var[X 0; P] = 1)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    ∃ Y : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ),
      (∀ᵐ ω' ∂P', ∀ t : Set.Icc (0 : ℝ) 1, Y ω' t = B (iccToNNReal t) ω') ∧
      TendstoInDistribution (fun n => skorokhodStepProcess n X) atTop
        (fun ω' => SkorokhodSpace.ofContinuous (Y ω')) (fun _ => P) P' := by
  obtain ⟨Y, hYae, hconv⟩ :=
    donsker_invariance_principle X hMeas hIndep hIdent hInt hMemLp hMean hVar B hB
  refine ⟨Y, hYae, ?_⟩
  refine tendstoInDistribution_skorokhod_of_tight_of_fdd one_pos
    (fun n => skorokhodStepProcess n X) (fun n ω => donskerProcess n X ω) Y
    (fun n => (measurable_skorokhodStepProcess n X hMeas).aemeasurable)
    hconv.forall_aemeasurable hconv.aemeasurable_limit
    (isTightMeasureSet_donskerProcess_laws X hMeas hIndep hIdent hInt hMemLp hMean hVar B hB)
    (fun I => hconv.continuous_comp
      (g := fun g : C(Set.Icc (0 : ℝ) 1, ℝ) => I.restrict (fun t => g t))
      (continuous_pi fun t => continuous_eval_const (t : Set.Icc (0 : ℝ) 1))) ?_
  intro ε hε
  refine ⟨fun n => ⋃ i ∈ Finset.range n, {ω | ε * Real.sqrt n < |X i ω|},
    fun n => Finset.measurableSet_biUnion _ fun i _ =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hMeas i)),
    tendsto_measureReal_large_increment X hMeas hIdent hMemLp ε hε, fun n ω hω t => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [skorokhodStepProcess_apply, donskerProcess, hε.le]
  · refine abs_step_sub_polygon_le n hn X ω ε (fun i hi => ?_) t
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, not_exists,
      not_lt] at hω
    exact hω i hi

namespace SkorokhodSpace

variable {T : ℝ}

/-- Scalar multiple `t ↦ c * f t` of a Skorokhod path. -/
def constMul (c : ℝ) (f : SkorokhodSpace T) : SkorokhodSpace T :=
  mk (fun t => c * f t) (f.isCadlag.continuous_comp (continuous_const_mul c))

/-- Evaluation of `constMul`. -/
@[simp] theorem constMul_apply (c : ℝ) (f : SkorokhodSpace T) (t : Set.Icc (0 : ℝ) T) :
    constMul c f t = c * f t := rfl

/-- Scaling by `c` is `max 1 |c|`-Lipschitz for the J1 distance (time changes are kept). -/
theorem lipschitzWith_constMul (c : ℝ) :
    LipschitzWith (max 1 ‖c‖₊) (constMul (T := T) c) := by
  intro f g
  change skorokhodEDist _ _ ≤ _ * skorokhodEDist _ _
  unfold skorokhodEDist
  rw [ENNReal.mul_iInf_of_ne (by simp) (by simp)]
  refine iInf_mono fun φ => ?_
  have hK : (1 : ℝ≥0∞) ≤ (max 1 ‖c‖₊ : ℝ≥0) := by exact_mod_cast le_max_left _ _
  have hc : ((‖c‖₊ : ℝ≥0) : ℝ≥0∞) ≤ (max 1 ‖c‖₊ : ℝ≥0) := by exact_mod_cast le_max_right _ _
  refine max_le ?_ (iSup_le fun t => ?_)
  · calc (⨆ t, edist (φ t) t) ≤ 1 * max (⨆ t, edist (φ t) t) (⨆ t, edist (f t) (g (φ t))) := by
          rw [one_mul]; exact le_max_left _ _
      _ ≤ _ := mul_le_mul_left hK _
  · calc edist (c * f t) (c * g (φ t)) = ‖c‖₊ * edist (f t) (g (φ t)) := by
          rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
            ENNReal.ofReal_mul (abs_nonneg c)]
          congr 1
          rw [← Real.norm_eq_abs, ofReal_norm, enorm_eq_nnnorm]
      _ ≤ (max 1 ‖c‖₊ : ℝ≥0) * max (⨆ t, edist (φ t) t) (⨆ t, edist (f t) (g (φ t))) :=
          mul_le_mul hc ((le_iSup (fun t => edist (f t) (g (φ t))) t).trans (le_max_right _ _))
            (by simp) (by simp)

/-- Scaling is continuous on `D([0,T])`. -/
theorem continuous_constMul (c : ℝ) : Continuous (constMul (T := T) c) :=
  (lipschitzWith_constMul c).continuous

/-- Scaling commutes with the inclusion of continuous paths. -/
theorem constMul_ofContinuous (c : ℝ) (f : C(Set.Icc (0 : ℝ) T, ℝ)) :
    constMul c (ofContinuous f) = ofContinuous (c • f) := rfl

end SkorokhodSpace

/-! ### Concrete counting-process example -/

/-- The **compensated Bernoulli counting process** in `D([0,1])`: with counting increments
`ξ i ∈ {0, 1}` of success probability `p` and counting process `N k = ∑_{i<k} ξ i`,
`t ↦ (√n)⁻¹ (N ⌊n t⌋ - p ⌊n t⌋)` (counts minus compensator, diffusively scaled; see
`compensatedBernoulliStep_apply`). This is a concrete example only; it does not define a
general counting-process interface. -/
def compensatedBernoulliStep {Ω : Type*} (n : ℕ) (p : ℝ) (ξ : ℕ → Ω → ℝ) (ω : Ω) :
    SkorokhodSpace 1 :=
  skorokhodStepProcess n (fun i ω => ξ i ω - p) ω

/-- Explicit formula: `(N ⌊n t⌋ - p ⌊n t⌋) / √n` with `N k = ∑_{i<k} ξ i`. -/
theorem compensatedBernoulliStep_apply {Ω : Type*} (n : ℕ) (p : ℝ) (ξ : ℕ → Ω → ℝ) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) :
    compensatedBernoulliStep n p ξ ω t =
      ((∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), ξ i ω) -
        p * Nat.floor ((n : ℝ) * t.1)) / Real.sqrt n := by
  simp [compensatedBernoulliStep, skorokhodStepProcess_apply, Finset.sum_sub_distrib,
    mul_comm]

private lemma abs_bernoulli_sub_le {x p : ℝ} (hx : x = 0 ∨ x = 1) (hp0 : 0 < p) (hp1 : p < 1) :
    |x - p| ≤ 1 := by
  rcases hx with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith

private lemma integral_bernoulli_sub_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (x : Ω → ℝ) (hx : Measurable x) (hBern : ∀ ω, x ω = 0 ∨ x ω = 1)
    (p : ℝ) (hMean : P[x] = p) :
    ∫ ω, (x ω - p) ^ 2 ∂P = p * (1 - p) := by
  have hxint : Integrable x P :=
    Integrable.of_bound hx.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rcases hBern ω with h | h <;> simp [h])
  have hpt : ∀ ω, (x ω - p) ^ 2 = x ω * (1 - 2 * p) + p ^ 2 := by
    intro ω; rcases hBern ω with h | h <;> rw [h] <;> ring
  simp_rw [hpt]
  rw [integral_add (hxint.mul_const _) (integrable_const _), integral_mul_const,
    integral_const, hMean]
  simp; ring

/-- **Martingale FCLT for the compensated Bernoulli counting process.** If the counting
increments `ξ i` are i.i.d., `{0,1}`-valued with success probability `p ∈ (0,1)`, then the
compensated counting process `compensatedBernoulliStep n p ξ` converges in distribution in
the Skorokhod J1 topology on `D([0,1])` to `√(p(1-p)) • W`, where `W` is a continuous version
of Brownian motion. In law this is Brownian motion time-changed by `A t = p (1 - p) t`, the
limit of the predictable quadratic variations (`tendsto_compensatedBernoulli_predictableQV`),
by Brownian scaling. That scaling identity is not formalized here.

The Rebolledo hypotheses for this example are proved separately:
`condExp_sq_increment_compensatedBernoulli` (predictable quadratic variation is the
deterministic `p (1-p) ⌊n t⌋ / n`) and `lindebergConditionTriangular_compensatedBernoulli`
(jump control). Source: Billingsley (1999), Theorem 16.1 (Donsker in `D`), specialized to
Bernoulli increments; Andersen–Borgan–Gill–Keiding (1993), §II.5 for the counting-process
reading. -/
theorem tendstoInDistribution_compensatedBernoulliStep
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (ξ : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (ξ n)) (hIndep : iIndepFun ξ P)
    (hIdent : ∀ i, IdentDistrib (ξ i) (ξ 0) P P) (hBern : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hMean : P[ξ 0] = p)
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    ∃ Y : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ),
      (∀ᵐ ω' ∂P', ∀ t : Set.Icc (0 : ℝ) 1, Y ω' t = B (iccToNNReal t) ω') ∧
      TendstoInDistribution (fun n => compensatedBernoulliStep n p ξ) atTop
        (fun ω' => SkorokhodSpace.ofContinuous (Real.sqrt (p * (1 - p)) • Y ω'))
        (fun _ => P) P' := by
  set σ := Real.sqrt (p * (1 - p)) with hσ_def
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hσ : 0 < σ := Real.sqrt_pos.2 hpq
  have hσsq : σ ^ 2 = p * (1 - p) := Real.sq_sqrt hpq.le
  let g : ℝ → ℝ := fun x => (x - p) / σ
  have hg : Measurable g := (measurable_id.sub_const p).div_const σ
  let X : ℕ → Ω → ℝ := fun i ω => g (ξ i ω)
  have hXmeas : ∀ i, Measurable (X i) := fun i => hg.comp (hMeas i)
  have hXind : iIndepFun X P := hIndep.comp (fun _ => g) (fun _ => hg)
  have hXident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i => (hIdent i).comp hg
  have hXbd : ∀ ω, ‖X 0 ω‖ ≤ 1 / σ := by
    intro ω
    simp only [X, g, Real.norm_eq_abs, abs_div, abs_of_pos hσ]
    exact div_le_div_of_nonneg_right (abs_bernoulli_sub_le (hBern 0 ω) hp0 hp1) hσ.le
  have hXMemLp : MemLp (X 0) 2 P :=
    MemLp.of_bound (hXmeas 0).aestronglyMeasurable _ (ae_of_all _ hXbd)
  have hXint : Integrable (X 0) P :=
    Integrable.of_bound (hXmeas 0).aestronglyMeasurable _ (ae_of_all _ hXbd)
  have hξint : Integrable (ξ 0) P :=
    Integrable.of_bound (hMeas 0).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rcases hBern 0 ω with h | h <;> simp [h])
  have hXmean : P[X 0] = 0 := by
    simp only [X, g]
    rw [integral_div, integral_sub hξint (integrable_const p), hMean]
    simp
  have hXvar : Var[X 0; P] = 1 := by
    rw [variance_of_integral_eq_zero (hXmeas 0).aemeasurable hXmean]
    simp only [X, g, div_pow]
    rw [integral_div, integral_bernoulli_sub_sq (ξ 0) (hMeas 0) (hBern 0) p hMean,
      hσsq, div_self hpq.ne']
  obtain ⟨Y, hYae, hconv⟩ := tendstoInDistribution_skorokhodStepProcess X hXmeas hXind
    hXident hXint hXMemLp hXmean hXvar B hB
  refine ⟨Y, hYae, ?_⟩
  have hD := hconv.continuous_comp (SkorokhodSpace.continuous_constMul σ)
  have heq : ∀ n, compensatedBernoulliStep n p ξ =
      SkorokhodSpace.constMul σ ∘ skorokhodStepProcess n X := by
    intro n
    funext ω
    ext t
    simp only [compensatedBernoulliStep, Function.comp_apply, SkorokhodSpace.constMul_apply,
      skorokhodStepProcess_apply, X, g, ← Finset.sum_div]
    field_simp
  simp only [heq]
  exact hD

/-- **Lindeberg (jump-control) condition** for the compensated Bernoulli martingale
differences `(ξ k - p) / √n`: every increment is bounded by `1 / √n`, so all truncated second
moments vanish once `1 / √n < ε`. Uses the repository's `LindebergConditionTriangular`. -/
theorem lindebergConditionTriangular_compensatedBernoulli
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℕ → Ω → ℝ)
    (hBern : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    LindebergConditionTriangular (fun n k ω => (ξ k ω - p) / Real.sqrt n) P := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (1 / ε)] with n hn
  symm
  refine Finset.sum_eq_zero fun k _ => ?_
  have hsq : 0 < Real.sqrt n := (one_div_pos.2 hε).trans hn
  have hzero : ∀ ω, Set.indicator {ω' | ε < |(ξ k ω' - p) / Real.sqrt n|} 1 ω = (0 : ℝ) := by
    intro ω
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_ofPred_eq, not_lt, abs_div, abs_of_pos hsq]
    rw [div_le_iff₀ hsq]
    have h1 := abs_bernoulli_sub_le (hBern k ω) hp0 hp1
    have h2 : 1 < ε * Real.sqrt n := by
      rw [div_lt_iff₀ hε] at hn; linarith
    linarith
  simp [hzero]

/-- **Predictable quadratic variation of the compensated Bernoulli counting process.** With
respect to the natural filtration of the counting increments, the conditional variance of
every future increment is the constant `p (1 - p)`. Informally, the predictable quadratic
variation of `compensatedBernoulliStep n p ξ` at time `t` is therefore the deterministic
`p (1 - p) ⌊n t⌋ / n` (no quadratic-variation object is defined here), whose limit is
`tendsto_compensatedBernoulli_predictableQV`. -/
theorem condExp_sq_increment_compensatedBernoulli
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hsm : ∀ n, StronglyMeasurable (ξ n)) (hIndep : iIndepFun ξ P)
    (hIdent : ∀ i, IdentDistrib (ξ i) (ξ 0) P P) (hBern : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1)
    (p : ℝ) (hMean : P[ξ 0] = p) {i j : ℕ} (hij : i < j) :
    P[fun ω => (ξ j ω - p) ^ 2 | Filtration.natural ξ hsm i] =ᵐ[P] fun _ => p * (1 - p) := by
  have hg : Measurable fun x : ℝ => (x - p) ^ 2 := (measurable_id.sub_const p).pow_const 2
  have hind := hIndep.indep_comap_natural_of_lt hsm hij
  have hfm : StronglyMeasurable[MeasurableSpace.comap (ξ j) inferInstance]
      (fun ω => (ξ j ω - p) ^ 2) :=
    (hg.comp (comap_measurable (ξ j))).stronglyMeasurable
  refine (condExp_indep_eq (hsm j).measurable.comap_le (Filtration.le _ _) hfm hind).trans ?_
  refine Filter.Eventually.of_forall fun _ => ?_
  have hj : ∫ ω, (ξ j ω - p) ^ 2 ∂P = ∫ ω, (ξ 0 ω - p) ^ 2 ∂P :=
    ((hIdent j).comp hg).integral_eq
  simp only
  rw [hj, integral_bernoulli_sub_sq (ξ 0) (hsm 0).measurable (hBern 0) p hMean]

/-- The deterministic sequence `p (1 - p) ⌊n t⌋ / n`, informally the predictable quadratic
variation of the compensated Bernoulli counting process (see
`condExp_sq_increment_compensatedBernoulli`), converges to the continuous increasing limit
`p (1 - p) t`. This is a floor limit; it is not stated in terms of the process. -/
theorem tendsto_compensatedBernoulli_predictableQV (p : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => p * (1 - p) * (Nat.floor ((n : ℝ) * t) / n)) atTop
      (𝓝 (p * (1 - p) * t)) := by
  refine Tendsto.const_mul _ ?_
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) ht).comp tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, mul_comm t]

/-- **The compensated Bernoulli counting process is a martingale**: with i.i.d. `{0,1}`-valued
increments of mean `p`, the partial sums `∑_{i ≤ k} (ξ i - p)` (counts minus compensator) form
a martingale for the natural filtration of `ξ`. This is the discrete-time martingale whose
diffusive rescaling is `compensatedBernoulliStep`. -/
theorem martingale_compensatedBernoulli
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hsm : ∀ n, StronglyMeasurable (ξ n)) (hIndep : iIndepFun ξ P)
    (hIdent : ∀ i, IdentDistrib (ξ i) (ξ 0) P P) (hBern : ∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1)
    (p : ℝ) (hMean : P[ξ 0] = p) :
    Martingale (fun k ω => ∑ i ∈ Finset.range (k + 1), (ξ i ω - p))
      (Filtration.natural ξ hsm) P := by
  set F := Filtration.natural ξ hsm with hF
  set S : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (k + 1), (ξ i ω - p) with hS
  have hξint : ∀ i, Integrable (ξ i) P := fun i =>
    Integrable.of_bound (hsm i).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rcases hBern i ω with h | h <;> simp [h])
  have hint : ∀ i, Integrable (fun ω => ξ i ω - p) P := fun i =>
    (hξint i).sub (integrable_const p)
  have hSint : ∀ k, Integrable (S k) P := fun k =>
    integrable_finsetSum _ fun i _ => hint i
  have hmean : ∀ l, ∫ ω, (ξ l ω - p) ∂P = 0 := by
    intro l
    rw [integral_sub (hξint l) (integrable_const p), (hIdent l).integral_eq, hMean]
    simp
  have hadapt : ∀ k, StronglyMeasurable[F k] (S k) := by
    intro k
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact ((Filtration.stronglyAdapted_natural hsm i).mono (F.mono hik)).sub
      stronglyMeasurable_const
  refine ⟨hadapt, fun i j hij => ?_⟩
  induction j, hij using Nat.le_induction with
  | base => rw [condExp_of_stronglyMeasurable (F.le i) (hadapt i) (hSint i)]
  | succ j hij ih =>
    have hsucc : S (j + 1) = S j + fun ω => ξ (j + 1) ω - p := by
      funext ω
      simp only [hS, Pi.add_apply]
      rw [Finset.sum_range_succ]
    rw [hsucc]
    refine (condExp_add (hSint j) (hint (j + 1)) _).trans ?_
    have hg : Measurable fun x : ℝ => x - p := measurable_id.sub_const p
    have hind := hIndep.indep_comap_natural_of_lt hsm (Nat.lt_succ_of_le hij)
    have hfm : StronglyMeasurable[MeasurableSpace.comap (ξ (j + 1)) inferInstance]
        (fun ω => ξ (j + 1) ω - p) :=
      (hg.comp (comap_measurable (ξ (j + 1)))).stronglyMeasurable
    have hz := condExp_indep_eq (hsm (j + 1)).measurable.comap_le (F.le i) hfm hind
    filter_upwards [ih, hz] with ω h1 h2
    simp only [Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2, hmean, add_zero]

end

end MathlibExt.Probability.Martingale
