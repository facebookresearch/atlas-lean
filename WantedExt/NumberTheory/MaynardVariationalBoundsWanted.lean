/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.GPYMaynardSieveReduction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lower bounds for Maynard's variational quantity `M_k`

Statements of Maynard's Proposition 4.3 (J. Maynard, *Small gaps between primes*, Ann. of Math.
181 (2015), 383-413; numbering of arXiv:1311.4600v3) for
`MathlibExt.NumberTheory.GPYMaynard.maynardM`. That definition takes the supremum over bounded
measurable profiles vanishing off the simplex, a class containing an a.e.-equivalent, with the
same `I_k` and `J_k^{(m)}`, of each of Maynard's Riemann-integrable profiles; the two suprema agree
because `I_k` and every `J_k^{(m)}` are continuous for the `L²` norm on the simplex and
Riemann-integrable profiles are dense there.
-/

@[expose] public section

namespace WantedExt.NumberTheory.MaynardVariationalBounds

open MathlibExt.NumberTheory.GPYMaynard

/-- **`M₅ > 2`.** Maynard's variational quantity for `k = 5` exceeds `2` (Maynard, *Small gaps
between primes*, arXiv:1311.4600v3, Proposition 4.3(1)). -/
theorem_wanted two_lt_maynardM_five : 2 < maynardM 5

/-- **`M₁₀₅ > 4`.** Maynard's variational quantity for `k = 105` exceeds `4` (Maynard, *Small gaps
between primes*, arXiv:1311.4600v3, Proposition 4.3(2)). -/
theorem_wanted four_lt_maynardM_105 : 4 < maynardM 105

/-- **Growth of `M_k`.** For all sufficiently large `k`,
`M_k > log k - 2 log log k - 2` (Maynard, *Small gaps between primes*, arXiv:1311.4600v3,
Proposition 4.3(3)). -/
theorem_wanted eventually_log_sub_lt_maynardM :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      Real.log k - 2 * Real.log (Real.log k) - 2 < maynardM k

end WantedExt.NumberTheory.MaynardVariationalBounds
