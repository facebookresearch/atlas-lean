/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Balke–Pearl bounds for instrumental variables with imperfect compliance

Let `Z` (assignment), `D` (treatment received) and `Y` (response) be binary, with `Z` randomized
and affecting `Y` only through `D`. The latent population splits into sixteen response types
`(r_D, r_Y)`, a compliance map `r_D : Bool → Bool` from assignment to treatment and a response map
`r_Y : Bool → Bool` from treatment to outcome, with an arbitrary distribution `q`. The observed
probabilities are `p_{yd.z} = P(Y = y, D = d | Z = z) = q{r_D(z) = d, r_Y(d) = y}` and the average
causal effect is `ACE = q{r_Y(1) = 1} - q{r_Y(0) = 1}`.

Balke and Pearl give the ACE bounds (4) and (5), each the maximum or minimum of eight linear
combinations of the `p_{yd.z}`, and show that they are the tightest possible. Every observed
distribution satisfies the instrumental inequalities (6), and the width of the bounds never
exceeds the noncompliance rate `P(D = 1 | Z = 0) + P(D = 0 | Z = 1)`. Below, `p y d z` is
`p_{yd.z}`, with `false` for `0` and `true` for `1`.

Sources: A. Balke and J. Pearl, "Bounds on treatment effects from studies with imperfect
compliance", J. Amer. Statist. Assoc. 92 (1997) 1171–1176, equations (1)–(6).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.BalkePearlBoundsWanted

/-- A response type: a compliance map `r_D` from assignment to treatment and a response map
`r_Y` from treatment to outcome. -/
abbrev ResponseType : Type := (Bool → Bool) × (Bool → Bool)

/-- The observed probability `p_{yd.z} = q{r_D(z) = d, r_Y(d) = y}` induced by the distribution
`q` of response types. -/
noncomputable def observed (q : ResponseType → ℝ) (y d z : Bool) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r : ResponseType => r.1 z = d ∧ r.2 d = y), q r

/-- The average causal effect `q{r_Y(1) = 1} - q{r_Y(0) = 1}`. -/
noncomputable def ace (q : ResponseType → ℝ) : ℝ :=
  (∑ r ∈ Finset.univ.filter (fun r : ResponseType => r.2 true = true), q r) -
    ∑ r ∈ Finset.univ.filter (fun r : ResponseType => r.2 false = true), q r

/-- The Balke–Pearl lower bound (4), the maximum of eight linear combinations of the observed
probabilities `p y d z = p_{yd.z}`. -/
noncomputable def lowerBound (p : Bool → Bool → Bool → ℝ) : ℝ :=
  max (max (max (p false false false + p true true true - 1)
        (p false false true + p true true true - 1))
      (max (p true true false + p false false true - 1)
        (p false false false + p true true false - 1)))
    (max (max (2 * p false false false + p true true false + p true false true +
          p true true true - 2)
        (p false false false + 2 * p true true false + p false false true +
          p false true true - 2))
      (max (p true false false + p true true false + 2 * p false false true +
          p true true true - 2)
        (p false false false + p false true false + p false false true +
          2 * p true true true - 2)))

/-- The Balke–Pearl upper bound (5), the minimum of eight linear combinations of the observed
probabilities `p y d z = p_{yd.z}`. -/
noncomputable def upperBound (p : Bool → Bool → Bool → ℝ) : ℝ :=
  min (min (min (1 - p true false false - p false true true)
        (1 - p false true false - p true false true))
      (min (1 - p false true false - p true false false)
        (1 - p false true true - p true false true)))
    (min (min (2 - 2 * p false true false - p true false false - p true false true -
          p true true true)
        (2 - p false true false - 2 * p true false false - p false false true -
          p false true true))
      (min (2 - p true false false - p true true false - 2 * p false true true -
          p true false true)
        (2 - p false false false - p false true false - p false true true -
          2 * p true false true)))

/-- **Soundness of the Balke–Pearl bounds** (Balke and Pearl 1997, (4)–(5)). For every
distribution `q` of the sixteen response types (`q ≥ 0` with total mass `1`), the average causal
effect lies between the lower bound (4) and the upper bound (5) computed from the induced observed
probabilities `p_{yd.z}`.

Sources: Balke and Pearl (1997), p. 1173, (4) and (5). -/
public theorem_wanted lowerBound_le_ace_le_upperBound (q : ResponseType → ℝ)
    (hq : ∀ r, 0 ≤ q r) (hsum : ∑ r, q r = 1) :
    lowerBound (observed q) ≤ ace q ∧ ace q ≤ upperBound (observed q)

/-- **Sharpness of the Balke–Pearl bounds** (Balke and Pearl 1997). For every distribution `q`
of the sixteen response types (`q ≥ 0` with total mass `1`), there are distributions `q_lo` and
`q_hi` of response types (nonnegative, total mass `1`) inducing the same observed probabilities
`p_{yd.z}` as `q`, with `ACE(q_lo)` equal to the lower bound (4) and `ACE(q_hi)` equal to the
upper bound (5).

Sources: Balke and Pearl (1997), abstract ("the tightest possible") and p. 1172. -/
public theorem_wanted bounds_attained (q : ResponseType → ℝ) (hq : ∀ r, 0 ≤ q r)
    (hsum : ∑ r, q r = 1) :
    (∃ q' : ResponseType → ℝ, (∀ r, 0 ≤ q' r) ∧ ∑ r, q' r = 1 ∧ observed q' = observed q ∧
        ace q' = lowerBound (observed q)) ∧
      ∃ q' : ResponseType → ℝ, (∀ r, 0 ≤ q' r) ∧ ∑ r, q' r = 1 ∧ observed q' = observed q ∧
        ace q' = upperBound (observed q)

/-- **The instrumental inequalities** (Balke and Pearl 1997, (6)). For every distribution `q` of
the sixteen response types (`q ≥ 0` with total mass `1`), the induced observed probabilities
satisfy `p_{00.0} + p_{10.1} ≤ 1`, `p_{01.0} + p_{11.1} ≤ 1`, `p_{10.0} + p_{00.1} ≤ 1` and
`p_{11.0} + p_{01.1} ≤ 1`.

Sources: Balke and Pearl (1997), p. 1173, (6). -/
public theorem_wanted instrumental_inequalities (q : ResponseType → ℝ) (hq : ∀ r, 0 ≤ q r)
    (hsum : ∑ r, q r = 1) :
    observed q false false false + observed q true false true ≤ 1 ∧
      observed q false true false + observed q true true true ≤ 1 ∧
      observed q true false false + observed q false false true ≤ 1 ∧
      observed q true true false + observed q false true true ≤ 1

/-- **The width is at most the noncompliance rate** (Balke and Pearl 1997). For every
distribution `q` of the sixteen response types (`q ≥ 0` with total mass `1`), the upper bound (5)
minus the lower bound (4) is at most `P(D = 1 | Z = 0) + P(D = 0 | Z = 1)
= p_{01.0} + p_{11.0} + p_{00.1} + p_{10.1}`.

Sources: Balke and Pearl (1997), p. 1173. -/
public theorem_wanted width_le_noncompliance (q : ResponseType → ℝ) (hq : ∀ r, 0 ≤ q r)
    (hsum : ∑ r, q r = 1) :
    upperBound (observed q) - lowerBound (observed q) ≤
      observed q false true false + observed q true true false +
        observed q false false true + observed q true false true

end WantedExt.Biology.StatisticalGenetics.BalkePearlBoundsWanted
