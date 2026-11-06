/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations

/-!
# Strict growth of regular continued-fraction denominators

This file proves strict growth after the potentially equal initial denominator
pair. The source paper uses the adjacent inequality rather than stating this
universal form verbatim.

Mathlib already supplies weak monotonicity in `GenContFract.of_den_mono`, the
recurrence in `GenContFract.dens_recurrence`, and the alternating error formula
in `GenContFract.sub_convs_eq`. Only the strict order consequence is added.
-/

@[expose] public section

namespace GenContFract

variable {K : Type*} {v : K} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [FloorRing K]

/-- **Strict growth of continued-fraction denominators.** Let $K$ be a linearly ordered field
with a floor function, let $v \in K$, and write $v = [a_0; a_1, a_2, \dots]$ for its regular
continued fraction, with convergent denominators $q_0 = 1$, $q_1 = a_1$ and
$q_{k+2} = a_{k+2} q_{k+1} + q_k$. For every natural number $n$, if the partial quotient
$a_{n+2}$ exists (the continued fraction has not terminated before it), then
$q_{n+1} < q_{n+2}$.

The comparison starts at $q_1$ because $q_0 = 1$ while $q_1 = a_1$ can also equal $1$.

Source: arXiv:2607.23662, item D07, which uses the adjacent inequality $q_{k-1} < q_k$. -/
theorem of_den_succ_lt_succ_succ (n : ℕ)
    (not_terminatedAt : ¬(GenContFract.of v).TerminatedAt (n + 1)) :
    (GenContFract.of v).dens (n + 1) <
      (GenContFract.of v).dens (n + 2) := by
  let g := GenContFract.of v
  obtain ⟨gp, hgp⟩ : ∃ gp, g.s.get? (n + 1) = some gp :=
    Option.ne_none_iff_exists'.mp not_terminatedAt
  have ha : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a hgp)
  have hb : 1 ≤ gp.b := of_one_le_get?_partDen (partDen_eq_s_b hgp)
  have hn : n = 0 ∨ ¬g.TerminatedAt (n - 1) := by
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    · exact Or.inr (mt (terminated_stable (by omega)) not_terminatedAt)
  have hdn : 0 < g.dens n := by
    have hfib : (0 : K) < Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    exact hfib.trans_le (succ_nth_fib_le_of_nth_den hn)
  have hmono : g.dens (n + 1) ≤ gp.b * g.dens (n + 1) := by
    simpa using mul_le_mul_of_nonneg_right hb zero_le_of_den
  rw [dens_recurrence hgp rfl rfl, ha, one_mul]
  exact lt_of_le_of_lt hmono (lt_add_of_pos_right _ hdn)

end GenContFract
