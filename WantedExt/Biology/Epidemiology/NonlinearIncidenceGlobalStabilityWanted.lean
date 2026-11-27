/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Global stability of SIR and SEIR models with concave nonlinear incidence

Korobeinikov and Maini (2005, Section 4) consider the normalized models with incidence
`h(S) g(I)`, birth and death rate `μ > 0`, recovery rate `δ ≥ 0` and latency rate `θ > 0`:

  SIR (4.1):  `S' = μ - h(S) g(I) - μ S`,  `I' = h(S) g(I) - (δ + μ) I`;
  SEIR (4.2): `S' = μ - h(S) g(I) - μ S`,  `E' = h(S) g(I) - (θ + μ) E`,
              `I' = θ E - (δ + μ) I`.

The source asks that the incidence `f(S, I) = h(S) g(I)` vanish when `S = 0` or `I = 0` (2.1),
have positive partial derivatives for `S, I > 0` (2.2) and satisfy `∂²f/∂I² ≤ 0` (2.3), and its
proof takes `h` and `g` increasing. The statements below assume an adaptation of these
conditions, `Incidence`: `h` and `g` are `C¹` on `[0, ∞)`, vanish at `0` and are strictly
increasing, and `g` is concave. Neither set of conditions implies the other. The adaptation
relaxes the interior conditions, since a strictly increasing `C¹` function `h` may have a zero
derivative at an interior point and concavity of `g` needs no second derivative. It adds
regularity at the boundary, where `h` and `g` must be `C¹` up to `0`, so that the slope `g'(0)` in
`R₀` is a real number: (2.1)–(2.3) allow `h(S) = S` and `g(I) = √I`, whose slope at `0` is
infinite, and the source keeps a finite slope at `0` as the separate assumption (2.4).
`Incidence` lists why the proof still goes through. With `B = 1` for SIR and
`B = (θ + μ) / θ` for SEIR, the basic reproduction number is `R₀ = h(1) g'(0) / (B (δ + μ))`.
Their Theorem 4.1: if `R₀ > 1` the endemic equilibrium is globally asymptotically stable, and if
`R₀ ≤ 1` the disease-free equilibrium `(1, 0, 0)` is globally asymptotically stable; the proofs
use Volterra-type Lyapunov functions and the inequality `g(I)/g(I*) ≷ I/I*` that concavity gives.
Two points left implicit in the source are made precise here: the basin of the endemic
equilibrium is the set of nonnegative states with `E + I > 0` (`I > 0` for SIR), and the
existence and uniqueness of the endemic equilibrium are part of the statement.

The bilinear SEIR model with vital dynamics, `h(S) = β S / N` and `g(I) = I`, is proved in
`Domains.Biology.Epidemiology.SEIRGlobalStability`.

Sources: A. Korobeinikov and P. K. Maini, "Non-linear incidence and stability of infectious
disease models", Math. Med. Biol. 22 (2005) 113–128, conditions (2.1)–(2.4), Eqs. (4.1)–(4.5)
and Theorem 4.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace WantedExt.Biology.Epidemiology.NonlinearIncidenceGlobalStabilityWanted

open Filter Topology

/-- **Adapted incidence hypotheses.** An adaptation of conditions (2.1)–(2.3), not those
conditions: `h` and `g` are `C¹` on `[0, ∞)`, vanish at `0` and are strictly increasing on
`[0, ∞)`, and `g` is concave on `[0, ∞)`. For the incidence `h(S) g(I)` the source asks for
positive partial derivatives when `S, I > 0` and for `∂²(h(S) g(I))/∂I² ≤ 0`. Neither set of
conditions implies the other. The hypotheses here relax those interior conditions, since a
strictly increasing `C¹` function `h` may have a zero derivative at an interior point and
concavity of `g` needs no second derivative. They add regularity at the boundary: `h` and `g` are
`C¹` up to `0`, so the right slope `g'(0)` in `R₀` is a real number, whereas (2.1)–(2.3) allow
`g(I) = √I`, whose slope at `0` is infinite (the source keeps a finite slope at `0` as the
separate assumption (2.4)). The hypotheses still give what the proof of Theorem 4.1 uses: `h` and
`g` are positive on `(0, ∞)`, so the Lyapunov functions are defined; `h(S) - h(S*)` has the sign
of `S - S*`; `g(I) / I` is nonincreasing on `(0, ∞)`, which gives (4.5) and `g(I) ≤ g'(0) I`;
the partial derivatives `∂V/∂S = 1 - h(S*) / h(S)` and `∂V/∂I = B (1 - g(I*) / g(I))` of the
Lyapunov function (4.4) increase strictly, so `Q*` is its only extremum; and the equilibrium
equations (4.3) have exactly one solution with `I* > 0` when `R₀ > 1` and none when `R₀ ≤ 1`.

Source: Korobeinikov and Maini (2005), conditions (2.1)–(2.4), Eqs. (4.3)–(4.5) and Theorem 4.1. -/
structure Incidence (h g : ℝ → ℝ) : Prop where
  contDiffOn_h : ContDiffOn ℝ 1 h (Set.Ici 0)
  contDiffOn_g : ContDiffOn ℝ 1 g (Set.Ici 0)
  h_zero : h 0 = 0
  g_zero : g 0 = 0
  strictMonoOn_h : StrictMonoOn h (Set.Ici 0)
  strictMonoOn_g : StrictMonoOn g (Set.Ici 0)
  concaveOn_g : ConcaveOn ℝ (Set.Ici 0) g

/-- The right derivative `g'(0)` of `g` at `0`. -/
noncomputable def slopeAtZero (g : ℝ → ℝ) : ℝ :=
  derivWithin g (Set.Ici 0) 0

/-- The SEIR vector field (4.2) on `(S, E, I)`. -/
noncomputable def seirField (h g : ℝ → ℝ) (μ δ θ : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (μ - h x.1 * g x.2.2 - μ * x.1, h x.1 * g x.2.2 - (θ + μ) * x.2.1,
    θ * x.2.1 - (δ + μ) * x.2.2)

/-- The SIR vector field (4.1) on `(S, I)`. -/
noncomputable def sirField (h g : ℝ → ℝ) (μ δ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (μ - h x.1 * g x.2 - μ * x.1, h x.1 * g x.2 - (δ + μ) * x.2)

/-- `R₀ = h(1) g'(0) / (B (δ + μ))` for the SEIR model, with `B = (θ + μ) / θ`. -/
noncomputable def seirR0 (h g : ℝ → ℝ) (μ δ θ : ℝ) : ℝ :=
  h 1 * slopeAtZero g / ((θ + μ) / θ * (δ + μ))

/-- `R₀ = h(1) g'(0) / (δ + μ)` for the SIR model. -/
noncomputable def sirR0 (h g : ℝ → ℝ) (μ δ : ℝ) : ℝ :=
  h 1 * slopeAtZero g / (δ + μ)

/-- Stability of `e` within the state space `D` of the model: `e` is Lyapunov stable for the
solutions of `x' = F x` on `[0, ∞)` (`IsIntegralCurveOn x (fun _ => F) (Set.Ici 0)`, with the
derivative at `0` taken within `[0, ∞)`) that stay in `D`, and attracts every such solution that
starts in `A`. (The incidence functions are only constrained on `[0, ∞)`, so the models live on the
nonnegative orthant; it is forward invariant for every solution of a locally Lipschitz
extension of the vector field.) -/
def GloballyStable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V)
    (D A : Set V) (e : V) : Prop :=
  (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → V, IsIntegralCurveOn x (fun _ => F) (Set.Ici 0) →
      (∀ t, 0 ≤ t → x t ∈ D) → dist (x 0) e < δ → ∀ t, 0 ≤ t → dist (x t) e < ε) ∧
    ∀ x : ℝ → V, IsIntegralCurveOn x (fun _ => F) (Set.Ici 0) → (∀ t, 0 ≤ t → x t ∈ D) →
      x 0 ∈ A → Tendsto x atTop (𝓝 e)

/-- **Korobeinikov–Maini theorem, endemic case, SEIR.** Theorem 4.1(i) of Korobeinikov and Maini
(2005), under the adapted incidence hypotheses `Incidence` in place of (2.1)–(2.3). With `μ > 0`,
`δ ≥ 0`, `θ > 0` and `R₀ > 1`, there is a unique equilibrium of (4.2) in the nonnegative orthant
with `I > 0`; all its coordinates are positive, and it is Lyapunov stable for solutions in the
closed nonnegative orthant and attracts every such solution with `E(0) + I(0) > 0`.

Source: Korobeinikov and Maini (2005), Theorem 4.1. -/
theorem_wanted seir_endemic_globallyStable (h g : ℝ → ℝ) (μ δ θ : ℝ) (hinc : Incidence h g)
    (hμ : 0 < μ) (hδ : 0 ≤ δ) (hθ : 0 < θ) (hR0 : 1 < seirR0 h g μ δ θ) :
    ∃ e : ℝ × ℝ × ℝ, 0 < e.1 ∧ 0 < e.2.1 ∧ 0 < e.2.2 ∧ seirField h g μ δ θ e = 0 ∧
      (∀ e' : ℝ × ℝ × ℝ, 0 ≤ e'.1 → 0 ≤ e'.2.1 → 0 < e'.2.2 → seirField h g μ δ θ e' = 0 →
        e' = e) ∧
      GloballyStable (seirField h g μ δ θ) {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2}
        {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2 ∧ 0 < x.2.1 + x.2.2} e

/-- **Korobeinikov–Maini theorem, disease-free case, SEIR.** Theorem 4.1(ii) of Korobeinikov and
Maini (2005), under the adapted incidence hypotheses `Incidence` in place of (2.1)–(2.3). With
`μ > 0`, `δ ≥ 0`, `θ > 0` and `R₀ ≤ 1` (the case `R₀ = 1` included), the disease-free
equilibrium `(1, 0, 0)` is the only equilibrium in the closed nonnegative orthant, and it is
Lyapunov stable for and attracts every solution in the closed nonnegative orthant.

Source: Korobeinikov and Maini (2005), Theorem 4.1. -/
theorem_wanted seir_diseaseFree_globallyStable (h g : ℝ → ℝ) (μ δ θ : ℝ) (hinc : Incidence h g)
    (hμ : 0 < μ) (hδ : 0 ≤ δ) (hθ : 0 < θ) (hR0 : seirR0 h g μ δ θ ≤ 1) :
    (∀ e : ℝ × ℝ × ℝ, 0 ≤ e.1 → 0 ≤ e.2.1 → 0 ≤ e.2.2 → seirField h g μ δ θ e = 0 →
        e = (1, 0, 0)) ∧
      GloballyStable (seirField h g μ δ θ) {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2}
        {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2} (1, 0, 0)

/-- **Korobeinikov–Maini theorem, endemic case, SIR.** Theorem 4.1(i) of Korobeinikov and Maini
(2005), with `B = 1`, under the adapted incidence hypotheses `Incidence` in place of
(2.1)–(2.3). With `μ > 0`, `δ ≥ 0` and `R₀ > 1`, there is a unique equilibrium of (4.1) in the
nonnegative quadrant with `I > 0`; both its coordinates are positive, and it is Lyapunov stable
for solutions in the closed nonnegative quadrant and attracts every such solution with
`I(0) > 0`.

Source: Korobeinikov and Maini (2005), Theorem 4.1. -/
theorem_wanted sir_endemic_globallyStable (h g : ℝ → ℝ) (μ δ : ℝ) (hinc : Incidence h g)
    (hμ : 0 < μ) (hδ : 0 ≤ δ) (hR0 : 1 < sirR0 h g μ δ) :
    ∃ e : ℝ × ℝ, 0 < e.1 ∧ 0 < e.2 ∧ sirField h g μ δ e = 0 ∧
      (∀ e' : ℝ × ℝ, 0 ≤ e'.1 → 0 < e'.2 → sirField h g μ δ e' = 0 → e' = e) ∧
      GloballyStable (sirField h g μ δ) {x | 0 ≤ x.1 ∧ 0 ≤ x.2}
        {x | 0 ≤ x.1 ∧ 0 < x.2} e

/-- **Korobeinikov–Maini theorem, disease-free case, SIR.** Theorem 4.1(ii) of Korobeinikov and
Maini (2005), with `B = 1`, under the adapted incidence hypotheses `Incidence` in place of
(2.1)–(2.3). With `μ > 0`, `δ ≥ 0` and `R₀ ≤ 1`, the disease-free equilibrium `(1, 0)` is the
only equilibrium in the closed nonnegative quadrant, and it is Lyapunov stable for and attracts
every solution in the closed nonnegative quadrant.

Source: Korobeinikov and Maini (2005), Theorem 4.1. -/
theorem_wanted sir_diseaseFree_globallyStable (h g : ℝ → ℝ) (μ δ : ℝ) (hinc : Incidence h g)
    (hμ : 0 < μ) (hδ : 0 ≤ δ) (hR0 : sirR0 h g μ δ ≤ 1) :
    (∀ e : ℝ × ℝ, 0 ≤ e.1 → 0 ≤ e.2 → sirField h g μ δ e = 0 → e = (1, 0)) ∧
      GloballyStable (sirField h g μ δ) {x | 0 ≤ x.1 ∧ 0 ≤ x.2} {x | 0 ≤ x.1 ∧ 0 ≤ x.2} (1, 0)

end WantedExt.Biology.Epidemiology.NonlinearIncidenceGlobalStabilityWanted
