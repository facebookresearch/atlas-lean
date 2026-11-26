/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Original formalization by Adam Kiezun, with contributions by Metamate
(consolidation commit `f204b2a6`, PR #9859); ported with attribution.
-/

/-
# Amalgamated products over relatively convex subgroups (Kourovka Notebook Problem 1.48)

Kourovka Notebook, Archive of Solved Problems, Problem 1.48 (A. I. Kokorin): is a free product of
two orderable groups with an amalgamated subgroup that is relatively convex in each of the factors
again an orderable group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PushoutI
public import MathlibExt.GroupTheory.Orderability

@[expose] public section

namespace MathlibExt.GroupTheory.AmalgamRelativelyConvexOrderableKourovka1Problem48Wanted

export MathlibExt.GroupTheory
  (IsBiInvariantOrder IsOrderable IsRelativelyConvex)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.48 (A. I.
Kokorin). UnsolvedMath record UM-00700043 (`KOU-1.48`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). A subgroup is relatively convex
(Kourovka Archive 1.41) if it is convex for some such order of `G`; for a subgroup, convexity is the
condition `1 ≤ g ≤ h`, `h ∈ H` implies `g ∈ H`. The two factors are the family `G : Bool → Type`,
the amalgamated subgroup is `H` with injective homomorphisms `φ i : H →* G i`, and the amalgamated
free product is Mathlib's `Monoid.PushoutI φ`. Relative convexity in each factor refers to an order
of that factor, as the problem states it.
-/

/-- Kourovka 1.48 (A. I. Kokorin): the free product of two orderable groups `G true` and
`G false` amalgamating a common subgroup `H` (embedded by `φ`) that is relatively convex in each
factor is orderable. -/
def amalgamOverRelativelyConvexIsOrderable : Prop :=
  ∀ (G : Bool → Type) [∀ i, Group (G i)] (H : Type) [Group H] (φ : ∀ i, H →* G i),
    (∀ i, Function.Injective (φ i)) → (∀ i, IsOrderable (G i)) →
      (∀ i, IsRelativelyConvex (φ i).range) → IsOrderable (Monoid.PushoutI φ)

/--
Resolved false: the Kourovka Archive answers 1.48 "Not always", citing Kargapolov, Kokorin and
Kopytov (1965). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
1.48 (A. I. Kokorin); resolution: M. I. Kargapolov, A. I. Kokorin and V. M. Kopytov, Algebra i
Logika 4 (1965), no. 6, 21-27 (Russian), Kourovka Archive, Problem 1.48 (Not always).
-/
public theorem_wanted amalgamOverRelativelyConvexIsOrderable_refuted :
    ¬ amalgamOverRelativelyConvexIsOrderable

private example : ProofWanted.Stmt amalgamOverRelativelyConvexIsOrderable_refuted ↔
    ¬ amalgamOverRelativelyConvexIsOrderable :=
  Iff.rfl

end MathlibExt.GroupTheory.AmalgamRelativelyConvexOrderableKourovka1Problem48Wanted
