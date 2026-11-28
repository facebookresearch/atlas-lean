/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutCount
-- Reuse the counting implementation without exporting its intermediate types.
import all MathlibExt.Combinatorics.ArithmeticalStructureCoconutCount

/-!
# Counting arithmetical structures on coconut trees with non-smoothable leaves

## References

* A. Diaz-Lopez, B. Ha, P. E. Harris, J. Rogers, T. Koss, and D. Smith,
  *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82,
  pp. 1–23, Corollary 1 and Proposition 4.
* K. Archer, A. C. Bishop, A. Diaz-Lopez, L. D. García Puente, D. Glass, and J. Louwsma,
  *Arithmetical structures on bidents*, Discrete Mathematics 343 (2020), Article 111850,
  Proposition 2.11, the antecedent cited for the descendant enumeration.
* L. Carlitz, *Sequences, paths, ballot numbers*, Fibonacci Quarterly 10 (1972), 531–549,
  the ballot-number interpretation used in the enumeration.
-/

namespace MetaMathlibExt

open Finset ncard_arithmeticalStructure_coconutTree

private def unsmoothedLeavesEquiv (n s : ℕ) (hs : 0 < s) :
    {x : Labels n (Fin s) //
      IsArithmeticalStructure (coconutTree (n + 1) s) x.1 x.2 ∧ ∀ j, 2 ≤ x.1 (.inr j)} ≃
      Reduced n (Fin s) :=
  Equiv.subtypeEquivRight fun x => by
    rw [valid_iff (Or.inr hs) x]
    refine ⟨fun ⟨hx, hl⟩ => ⟨hx, fun j => ?_⟩, fun ⟨hx, hl⟩ => ⟨hx, fun j => ?_⟩⟩
    · have := hl j
      omega
    · have := hx.1 (.inr j)
      have := hl j
      omega

/-- **Counting coconut structures whose leaves cannot be smoothed.** For $p \ge 1$ and $s \ge 2$,
the number of arithmetical structures $(d, r)$ on the coconut tree $CT(p, s)$ with $d(\ell_j) \ge 2$
at every leaf $\ell_j$ is
$$\sum_{i=1}^{p} B(p - 1, p - i)\, N(i),$$
where $B(n, k)$ is the ballot number and $N(i)$ is the number of smooth arithmetical structures on
$CT(i, s)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 1
(`integers-2025-A82-cor-1`). -/
public theorem ncard_arithmeticalStructure_coconutTree_leaves_ge_two {p s : ℕ}
    (hp : 1 ≤ p) (hs : 2 ≤ s) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2 ∧ ∀ j, 2 ≤ x.1 (.inr j)}
      = ∑ i ∈ Finset.Icc 1 p, ballotNumber (p - 1) (p - i) *
          Set.ncard {z : (Fin i ⊕ Fin s → ℕ) × (Fin i ⊕ Fin s → ℕ) |
            IsSmoothCoconut i s z.1 z.2} := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hcard : Set.ncard {x : Labels n (Fin s) |
      IsArithmeticalStructure (coconutTree (n + 1) s) x.1 x.2 ∧ ∀ j, 2 ≤ x.1 (.inr j)} =
      Nat.card (Reduced n (Fin s)) :=
    (Nat.card_coe_set_eq _).symm.trans (Nat.card_congr (unsmoothedLeavesEquiv n s (by omega)))
  rw [hcard, reduced_count, Nat.add_sub_cancel]
  refine sum_bij (fun q _ => q + 1) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_range] at hq
    rw [mem_Icc]
    omega
  · intro q _ q' _ h
    omega
  · intro i hi
    rw [mem_Icc] at hi
    exact ⟨i - 1, mem_range.mpr (by omega), by omega⟩
  · intro q _
    rw [Nat.add_sub_add_right, Nat.card_congr (smoothEquiv q s (by omega))]
    exact congrArg (ballotNumber n (n - q) * ·)
      (Nat.card_coe_set_eq {z : Labels q (Fin s) | IsSmoothCoconut (q + 1) s z.1 z.2})

end MetaMathlibExt
