/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Doubly transitive groups with infinite cyclic point stabilizer (Kourovka Notebook Problem 10.63)

Kourovka Notebook, Archive of Solved Problems, Problem 10.63 (Ya. P. Sysak): is there a doubly
transitive permutation group in which the stabilizer of a point is infinite cyclic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

@[expose] public section

namespace MathlibExt.GroupTheory.DoublyTransitiveCyclicStabilizerKourovka10Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.63 (Ya. P.
Sysak). UnsolvedMath record UM-00700678 (`KOU-10.63`), dataset ulamai/UnsolvedMath v1.8.0.

A permutation group is a faithful action (`FaithfulSMul`; without faithfulness `ℤ` acting trivially
on one point would qualify). Doubly transitive is `MulAction.IsMultiplyPretransitive G X 2`. The
action is transitive, so all point stabilizers are conjugate and one of them suffices.
-/

/-- **Doubly transitive group with infinite cyclic point stabilizer (Kourovka 10.63).** The
statement that there exist a group $G$ and a faithful action of $G$ on a set $X$ such that for
any two ordered pairs of distinct points of $X$ some element of $G$ maps the first to the second,
and the stabilizer of some point $x \in X$ is isomorphic to the infinite cyclic group $\mathbb{Z}$.
-/
def doublyTransitiveInfiniteCyclicStabilizer : Prop :=
  ∃ (G X : Type) (_ : Group G) (_ : MulAction G X), FaithfulSMul G X ∧
    MulAction.IsMultiplyPretransitive G X 2 ∧
    ∃ x : X, Nonempty (MulAction.stabilizer G x ≃* Multiplicative ℤ)

/--
**No doubly transitive group has an infinite cyclic point stabilizer (Kourovka 10.63).** If a group
$G$ acts faithfully on a set $X$ such that for any two ordered pairs of distinct points of $X$
some element of $G$ maps the first to the second, then no point stabilizer of the action is
isomorphic to the infinite cyclic group $\mathbb{Z}$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.63 (Ya. P.
Sysak); resolution: V. D. Mazurov, Siberian Math. J. 31 (1990), 615-617; Gy. Károlyi, S. J. Kovács
and P. P. Pálfy, Aequationes Math. 39, no. 1 (1990), 161-166, Kourovka Archive, Problem 10.63
("No").
-/
public theorem_wanted doublyTransitiveInfiniteCyclicStabilizer_refuted :
    ¬ doublyTransitiveInfiniteCyclicStabilizer

end MathlibExt.GroupTheory.DoublyTransitiveCyclicStabilizerKourovka10Problem63Wanted
