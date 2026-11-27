/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing

/-!
# Near-universal hash families

A finite family `H` of functions `α → Fin m` is *near-universal* (`IsNearUniversal`) if any two
distinct keys collide under at most a `2 / m` fraction of its members, stated as
`collisionCount H x y * m ≤ 2 * H.card`. This relaxes the bound `1 / m` of universality
(`IsUniversal`), and every universal family is near-universal (`IsUniversal.isNearUniversal`).

## References

* J. Erickson, *Algorithms*, lecture notes, Lecture 5 "Hash Tables" (Spring 2017), Section 5.3.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UniversalHashing

universe u

variable {α : Type u} {m : Nat}

/--
**Near-universal hash family.** A finite family $H$ of functions from a set $\alpha$ to
$\{0, 1, \dots, m - 1\}$ is near-universal if $m > 0$, $H$ is nonempty, and for all distinct
keys $x \ne y$ in $\alpha$ the number of functions $h \in H$ with $h(x) = h(y)$, multiplied by
$m$, is at most $2|H|$; that is, $x$ and $y$ collide under at most a $2/m$ fraction of the
members of $H$.

This is universality with the collision bound $1/m$ relaxed to $2/m$.
-/
public def IsNearUniversal (H : Finset (α → Fin m)) : Prop :=
  0 < m ∧ H.Nonempty ∧ ∀ x y : α, x ≠ y → collisionCount H x y * m ≤ 2 * H.card

public theorem IsUniversal.isNearUniversal {H : Finset (α → Fin m)} (hH : IsUniversal H) :
    IsNearUniversal H :=
  ⟨hH.1, hH.2.1, fun x y hxy => (hH.2.2 x y hxy).trans (Nat.le_mul_of_pos_left _ two_pos)⟩

end Cslib.Algorithms.Lean.UniversalHashing
