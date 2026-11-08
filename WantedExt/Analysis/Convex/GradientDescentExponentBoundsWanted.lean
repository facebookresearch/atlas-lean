/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Convex.GradientDescentExponent

@[expose] public section

/-!
# Gradient-descent bound requests and primary-scope variants

These private requests are unproved data, not assumptions or theorem proofs.
The catalogue's unestablished uniform last-iterate transfers are separate from
the primary dyadic-horizon and bounded-sublevel best-iterate statements. The
catalogue attribution of all-horizon decay to the fixed silver schedule is
refuted by its quadratic power-of-two plateau; no such request is retained.
-/

namespace WantedExt.Analysis.Convex.GradientDescentExponentBoundsWanted

/-- Source: OptimizationProblems constant 35a, upper-bound row, folklore and
Nesterov2014. The complete reference-work proof is not retained or proved here. -/
private theorem_wanted upper_bound_two : gradientDescentExponent ≤ (2 : EReal)

/-- Source: OptimizationProblems constant 35a, GSW23 lower-bound row.
This is an unestablished primary-to-catalogue transfer. The retained primary
controls the best iterate with bounded initial sublevel sets, not this
last-iterate optimizer. The exact rational 1.0564 is not a proved bound here. -/
private theorem_wanted gsw_lower_bound :
    ((2641 / 2500 : ℝ) : EReal) ≤ gradientDescentExponent

/-- Source: OptimizationProblems constant 35a, AP24 lower-bound row.
This is an unestablished primary-to-catalogue transfer. The retained primary
controls horizons `2^j - 1`; no all-horizon existence theorem is inferred.
The fixed silver witness does not refute existence of some other schedule. -/
private theorem_wanted silver_lower_bound :
    (silverGradientDescentExponent : EReal) ≤ gradientDescentExponent

/-- Source: OptimizationProblems constant 35a, GSW23 nonconstant nonperiodic
schedule description. This is an unestablished primary-to-catalogue transfer.
The catalogue-scope last-iterate claim is not established by the retained
bounded-sublevel best-iterate theorem or refuted by the fixed silver witness. -/
private theorem_wanted gsw_nonperiodic_uniform_rate :
    ∃ s : ℕ → ℝ,
      (∀ p : ℕ, 0 < p → ∃ k : ℕ, s (k + p) ≠ s k) ∧
        GradientDescentUniformRate s (2641 / 2500)

/-- Source: Altschuler–Parrilo, retained `sections/intro.tex`, main theorem.
The actual silver trajectory is bounded at the dyadic horizons, with arbitrary
finite dimension, minimizer and initialization, normalized to smoothness one. -/
private theorem_wanted silver_dyadic_primary_bound :
    ∀ j : ℕ, 0 < j →
      ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsUnitSmoothConvex f →
        ∀ xstar : EuclideanSpace ℝ (Fin d), (∀ x, f xstar ≤ f x) →
          ∀ x₀ : EuclideanSpace ℝ (Fin d),
            f (gradientDescentTrajectory f silverGradientDescentSchedule x₀ (2 ^ j - 1)) -
                f xstar ≤
              ‖x₀ - xstar‖ ^ 2 /
                (1 + Real.sqrt (4 * gradientDescentSilverRatio ^ (2 * j) - 3))

/-- Source: Grimmer–Shu–Wang, retained introduction, best-iterate rate 1.0564.
One positive schedule and global rate constants precede every objective and
bounded initial sublevel set. D bounds that whole sublevel set, not merely
the initial distance. The explicit block construction and proof are unproved. -/
private theorem_wanted gsw_best_iterate_primary_bound :
    ∃ s : ℕ → ℝ, (∀ k, 0 < s k) ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧
      ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsUnitSmoothConvex f →
        ∀ xstar : EuclideanSpace ℝ (Fin d), (∀ x, f xstar ≤ f x) →
          ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (D : ℝ), 0 ≤ D →
            (∀ x, f x ≤ f x₀ → ‖x - xstar‖ ≤ D) →
              ∀ T : ℕ, K ≤ T → ∃ i : ℕ, i ≤ T ∧
                f (gradientDescentTrajectory f s x₀ i) - f xstar ≤
                  C * D ^ 2 / (T : ℝ) ^ (2641 / 2500 : ℝ)

end WantedExt.Analysis.Convex.GradientDescentExponentBoundsWanted
