/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Abel

/-!
# The potential method of amortized analysis

Tarjan's "physicist's view" of amortization (R. E. Tarjan, *Amortized computational
complexity*, SIAM J. Algebraic Discrete Methods 6(2) (1985) 306–318, §2). A run of a data
structure is a sequence of configurations `s 0, s 1, …, s m`; operation `i` moves `s i` to
`s (i + 1)` at actual cost `t i`. A potential `Φ` assigns a value to every configuration and
the amortized cost of operation `i` is `t i + Φ (s (i + 1)) - Φ (s i)`. Summing telescopes:
the total actual cost equals the total amortized cost plus the net decrease of the potential.

The statements are generic: costs and potentials take values in any ordered additive
commutative group (`ℤ`, `ℚ`, `ℝ`, …), and the configurations form an arbitrary type, so
they apply to any cost model a client fixes (number of rotations, pointer changes, unit
operations, …). Nothing here refers to a machine model; the cost `t` is whatever the client
counts.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.PotentialMethod

universe u v

variable {S : Type u} {R : Type v}

/-- **Amortized cost of an operation.** For a potential `Φ` on configurations, the amortized
cost of the `i`-th operation of a run `s` with actual costs `t` is
`t i + Φ (s (i + 1)) - Φ (s i)` (Tarjan, *Amortized computational complexity*, SIAM J.
Algebraic Discrete Methods 6(2) (1985), §2, the physicist's view). -/
def amortizedCost [AddCommGroup R] (Φ : S → R) (s : ℕ → S) (t : ℕ → R) (i : ℕ) : R :=
  t i + Φ (s (i + 1)) - Φ (s i)

/-- **Potential method: telescoping identity.** For every potential `Φ`, run `s` and actual
costs `t`, the total actual cost of the first `m` operations equals their total amortized cost
plus the net decrease in potential:
`∑_{i<m} t i = ∑_{i<m} a i + Φ (s 0) - Φ (s m)`, where `a = amortizedCost Φ s t`
(Tarjan, *Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6(2) (1985),
§2, the displayed identity of the physicist's view; Sleator and Tarjan, *Self-adjusting binary
search trees*, J. ACM 32(3) (1985), §2). -/
theorem sum_cost_eq [AddCommGroup R] (Φ : S → R) (s : ℕ → S) (t : ℕ → R) (m : ℕ) :
    ∑ i ∈ Finset.range m, t i =
      ∑ i ∈ Finset.range m, amortizedCost Φ s t i + Φ (s 0) - Φ (s m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp only [amortizedCost]
      abel

/-- **Potential method: amortized costs bound actual costs.** If the final potential is at
least the initial potential, the total actual cost of a run is at most its total amortized
cost (Tarjan, *Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6(2)
(1985), §2). -/
theorem sum_cost_le_sum_amortizedCost [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (Φ : S → R) (s : ℕ → S) (t : ℕ → R) (m : ℕ) (h : Φ (s 0) ≤ Φ (s m)) :
    ∑ i ∈ Finset.range m, t i ≤ ∑ i ∈ Finset.range m, amortizedCost Φ s t i := by
  rw [sum_cost_eq Φ s t m, add_sub_assoc]
  exact add_le_of_le_of_nonpos le_rfl (sub_nonpos.mpr h)

/-- **Potential method with a nonnegative potential that starts at zero.** If `Φ (s 0) = 0`
and the potential is nonnegative on every configuration of the run, then for every `m` the
total actual cost of the first `m` operations is at most their total amortized cost; this is
the case "initial potential zero and potential always nonnegative" singled out by Tarjan
(*Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6(2) (1985), §2),
corresponding to the banker's view without borrowing. -/
theorem sum_cost_le_sum_amortizedCost_of_nonneg [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (Φ : S → R) (s : ℕ → S) (t : ℕ → R) (h0 : Φ (s 0) = 0)
    (hnn : ∀ i, 0 ≤ Φ (s i)) (m : ℕ) :
    ∑ i ∈ Finset.range m, t i ≤ ∑ i ∈ Finset.range m, amortizedCost Φ s t i :=
  sum_cost_le_sum_amortizedCost Φ s t m (h0 ▸ hnn m)

/-- **Potential method with per-operation amortized bounds.** If every operation of a run has
amortized cost at most `c i`, then the total actual cost of the first `m` operations is at
most `∑_{i<m} c i + Φ (s 0) - Φ (s m)`. This is how an amortized bound per operation, such as
the access lemma for splay trees, yields a bound on the total time of a sequence (Sleator and
Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2, the discussion before
Theorem 1). -/
theorem sum_cost_le_of_amortizedCost_le [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (Φ : S → R) (s : ℕ → S) (t c : ℕ → R) (m : ℕ)
    (hc : ∀ i < m, amortizedCost Φ s t i ≤ c i) :
    ∑ i ∈ Finset.range m, t i ≤ ∑ i ∈ Finset.range m, c i + Φ (s 0) - Φ (s m) := by
  rw [sum_cost_eq Φ s t m]
  have hsum : ∑ i ∈ Finset.range m, amortizedCost Φ s t i ≤ ∑ i ∈ Finset.range m, c i :=
    Finset.sum_le_sum fun i hi => hc i (Finset.mem_range.mp hi)
  rw [add_sub_assoc, add_sub_assoc]
  exact add_le_add_left hsum _

end Cslib.Algorithms.Lean.PotentialMethod
