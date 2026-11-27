/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import MathlibExt.Dynamics.HorocycleOrbits

/-!
# Unipotent flows: Margulis's theorem on values of quadratic forms and horocycle orbits

Two consequences of the dynamics of unipotent flows on homogeneous spaces `Γ \ G`, following
D. W. Morris, *Ratner's theorems on unipotent flows*, Chicago Lectures
in Mathematics, University of Chicago Press (2005), arXiv:math/0310402:

* Margulis's theorem, formerly the Oppenheim conjecture (Morris, Theorem 1.2.2): a real,
  indefinite, nondegenerate quadratic form in at least three variables that is not a scalar
  multiple of a form with integer coefficients takes a dense set of values on `ℤⁿ`;
* the closed-or-dense dichotomy for orbits of the horocycle flow on `SL(2, ℤ) \ SL(2, ℝ)`
  (Morris, Example 1.1.16, deduced there from Ratner's orbit closure theorem, Theorem 1.1.14).

The first statement is wanted. The second is proved in `MathlibExt.Dynamics.HorocycleOrbits`.
-/

@[expose] public section

namespace MathlibExt.Dynamics.UnipotentFlowsWanted

/-- **Margulis's theorem on values of quadratic forms (Oppenheim conjecture).** Let `Q` be a real
quadratic form in `n ≥ 3` variables that is indefinite (it takes a positive and a negative value)
and nondegenerate (no nonzero `x` satisfies `Q(v + x) = Q(v - x)` for all `v`). If `Q` is not a
scalar multiple of a form with integer coefficients, that is, not of the form
`x ↦ c ∑ᵢ ∑ⱼ aᵢⱼ xᵢ xⱼ` with `c ∈ ℝ` and integers `aᵢⱼ`, then `Q(ℤⁿ)` is dense in `ℝ`
(G. A. Margulis, 1987; stated as D. W. Morris, *Ratner's theorems on unipotent flows*,
arXiv:math/0310402, Theorem 1.2.2, with the definitions of Definition 1.2.1).

The test module `MathlibExtTest.Dynamics.UnipotentFlowsHypotheses` restates the three hypotheses
verbatim and checks them on `x₀² + x₁² - √2 x₂²`; keep the two in sync. -/
theorem_wanted margulis_oppenheim {n : ℕ} (hn : 3 ≤ n) (Q : QuadraticForm ℝ (Fin n → ℝ))
    (hindef : (∃ v, 0 < Q v) ∧ ∃ v, Q v < 0)
    (hnondeg : ∀ x, (∀ v, Q (v + x) = Q (v - x)) → x = 0)
    (hirr : ¬ ∃ (c : ℝ) (A : Matrix (Fin n) (Fin n) ℤ),
      ∀ x, Q x = c * ∑ i, ∑ j, (A i j : ℝ) * x i * x j) :
    Dense (Set.range fun z : Fin n → ℤ => Q fun i => (z i : ℝ))

end MathlibExt.Dynamics.UnipotentFlowsWanted
