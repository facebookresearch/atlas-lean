/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TakagiDyadicIdentities

/-!
# Counting D-nodes in divide-and-conquer trees

The number of D-nodes in any divide-and-conquer tree is given by the recurrence on its leaf
count: equal child leaf counts double the child count, and unequal child leaf counts contribute
one additional D-node at the root.

## References

* Laura Monroe, [*Takagi Function Identities on Dyadic Rationals*](https://cs.uwaterloo.ca/journals/JIS/VOL27/Monroe/monroe2.pdf),
  Journal of Integer Sequences 27 (2024), Article 24.2.7, pp. 1–14, Theorem 9.
* Tomás M. Coronado, Mareike Fischer, Lina Herbst, Francesc Rosselló, and Kristina Wicke,
  *On the minimum value of the Colless index and the bifurcating trees that achieve it*,
  Journal of Mathematical Biology 80 (2020), pp. 1993–2054, §3.1 (the underlying recurrence).
-/

namespace MetaMathlibExt

/-- **Coronado et al.'s count of $D$-nodes in divide-and-conquer trees.** Every
divide-and-conquer tree with $n$ leaves has exactly $\delta(n)$ $D$-nodes, where $\delta$ is the
function on positive integers given by $\delta(1) = 0$, $\delta(2m) = 2\delta(m)$ and
$\delta(2m+1) = \delta(m) + \delta(m+1) + 1$ for $m \ge 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`jis-2024-24.2.7-thm-9`). -/
public theorem treeDNodes_eq_dcDNodes_of_isDivideConquerTree (t : BinaryTree Unit)
    (ht : IsDivideConquerTree t) : treeDNodes t = dcDNodes t.numLeaves := by
  induction t with
  | nil => simpa only [BinaryTree.numLeaves, dcDNodes_one] using treeNodes_nil.1
  | node u l r ihl ihr =>
    obtain ⟨⟨hlr, hrl⟩, hl, hr⟩ := (isDivideConquerTree_node u l r).mp ht
    rw [treeDNodes_node, ihl hl, ihr hr]
    change _ = dcDNodes (l.numLeaves + r.numLeaves)
    by_cases heq : l.numLeaves = r.numLeaves
    · rw [ite_eq_left heq, heq, show r.numLeaves + r.numLeaves = 2 * r.numLeaves by omega,
        dcDNodes_two_mul r.numLeaves_pos]
      omega
    · rw [ite_eq_right heq]
      obtain h | h : r.numLeaves = l.numLeaves + 1 ∨ l.numLeaves = r.numLeaves + 1 := by omega
      · rw [show l.numLeaves + r.numLeaves = 2 * l.numLeaves + 1 by omega,
          dcDNodes_two_mul_add_one l.numLeaves_pos, h]
        omega
      · rw [show l.numLeaves + r.numLeaves = 2 * r.numLeaves + 1 by omega,
          dcDNodes_two_mul_add_one r.numLeaves_pos, h]
        omega

end MetaMathlibExt
