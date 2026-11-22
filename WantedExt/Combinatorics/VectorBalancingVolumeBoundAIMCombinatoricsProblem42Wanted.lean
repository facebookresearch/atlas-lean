/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Banaszczyk's volume bound is not an upper bound for vector balancing (AimPL Problem 1.5)

AimPL, Hereditary discrepancy and factorization norms, Section 1, Problem 1.5 (Vector balancing):
for norms `X, Y` on `ℝ^d`, `α(X, Y, d)` is the supremum, over `n` and vectors `v₁, …, vₙ` with
`‖vᵢ‖_X ≤ 1`, of the least `‖∑ εᵢ vᵢ‖_Y` over signs `εᵢ = ±1`. Banaszczyk proved `α(X, Y, d) ≥ √d
(vol B_X / vol B_Y)^{1/d}`. Is this lower bound also an upper bound for `α(X, Y, d)` up to `log d`
factors?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Combinatorics.VectorBalancingVolumeBoundAIMCombinatoricsProblem42Wanted

/-!
Source: AimPL: Hereditary discrepancy and factorization norms, Section 1, Problem 1.5 (Vector
balancing), http://aimpl.org/hereddiscrep/1/. UnsolvedMath record UM-20000917
(`AIM-COMBINATORICS-0042`), dataset ulamai/UnsolvedMath v1.8.0.

'Up to log d factors' is read as up to a factor `C (log d)^c` with constants `C, c`, for `d ≥ 2` (at
`d = 1` the factor `log d` vanishes). Norms are definite seminorms on `EuclideanSpace ℝ (Fin d)`;
volumes are Lebesgue measures of the closed unit balls (finite and positive for norms). `α(X, Y, d)
≤ B` is stated as: every family `v₁, …, vₙ` with `X(vᵢ) ≤ 1` has signs with `Y(∑ εᵢ vᵢ) ≤ B` (the
least value over the finitely many signings is attained). The page's remark also proposes a
stronger, ellipsoid-based lower bound that may be an upper bound up to logarithmic factors; that
conjecture is not formalized here.
-/

open MeasureTheory

/-- The AimPL question (Hereditary discrepancy and factorization norms, Problem 1.5) as a claim:
Banaszczyk's volume lower bound `√d (vol B_X / vol B_Y)^{1/d}` for the vector balancing constant
`α(X, Y, d)` is also an upper bound up to polylogarithmic factors. That is, there are constants
`C, c` such that for every `d ≥ 2`, all norms `X, Y` on `ℝ^d` (definite seminorms) and all
vectors `v₁, …, vₙ` with `X(vᵢ) ≤ 1` there are signs `εᵢ = ±1` with
`Y(∑ εᵢ vᵢ) ≤ C (log d)^c √d (vol B_X / vol B_Y)^{1/d}`, where `B_X = {x | X x ≤ 1}`. -/
def volumeBoundIsUpperBound : Prop :=
  ∃ C c : ℝ, ∀ d : ℕ, 2 ≤ d → ∀ X Y : Seminorm ℝ (EuclideanSpace ℝ (Fin d)),
    (∀ x, X x = 0 → x = 0) → (∀ x, Y x = 0 → x = 0) →
    ∀ (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)), (∀ i, X (v i) ≤ 1) →
      ∃ ε : Fin n → ℤˣ, Y (∑ i, ((ε i : ℤ) : ℝ) • v i) ≤
        C * Real.log d ^ c * Real.sqrt d *
          ((volume {x | X x ≤ 1}).toReal / (volume {x | Y x ≤ 1}).toReal) ^ ((1 : ℝ) / d)

/--
Resolved false: the problem list's own remark (S. Nikolov) records that Banaszczyk's volume bound
can be too small by a factor of `√d`, for example for `X = Y = ℓ₁^d`, where the bound is `√d` while
the standard basis vectors have `‖∑ ±eᵢ‖₁ = d` for every choice of signs; a factor `√d` is not
polylogarithmic in `d`. Source: AimPL: Hereditary discrepancy and factorization norms, Section 1,
Problem 1.5 (Vector balancing), http://aimpl.org/hereddiscrep/1/; resolution: AimPL: Hereditary
discrepancy and factorization norms, remark by S. Nikolov to Problem 1.5, remark: 'In fact, this
lower bound can be too small by a factor of √d, for example when X = Y = ℓ_1^d' (for X = Y the
volume bound is √d, while for the standard basis e_1, ..., e_d every signing has ‖∑ ±e_i‖_1 = d),
http://aimpl.org/hereddiscrep/1/.
-/
public theorem_wanted volumeBoundIsUpperBound_refuted : ¬ volumeBoundIsUpperBound

end MathlibExt.Combinatorics.VectorBalancingVolumeBoundAIMCombinatoricsProblem42Wanted
