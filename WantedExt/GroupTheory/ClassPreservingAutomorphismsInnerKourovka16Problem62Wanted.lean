/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups all of whose automorphisms preserve conjugacy classes (Kourovka Notebook Problem 16.62)

Kourovka Notebook, Archive of Solved Problems, Problem 16.62 (D. MacHale): let `G` be a group such
that every `α ∈ Aut G` fixes every conjugacy class of `G` (setwise). Must `Aut G = Inn G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Conj

@[expose] public section

namespace MathlibExt.GroupTheory.ClassPreservingAutomorphismsInnerKourovka16Problem62Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.62 (D.
MacHale). UnsolvedMath record UM-00701254 (`KOU-16.62`), dataset ulamai/UnsolvedMath v1.8.0.

`α` fixes every conjugacy class setwise exactly when `α(g)` is conjugate to `g` for every `g`. The
hypothesis concerns all automorphisms of `G` at once, so this refutation is stronger than that of
`ScottishBook112Wanted` (every class-preserving automorphism is inner).
-/

/-- Kourovka 16.62 (D. MacHale): if every automorphism of a group `G` maps every conjugacy class of
`G` onto itself, then every automorphism of `G` is inner. -/
def classPreservingAutomorphismsInner : Prop :=
  ∀ (G : Type) [Group G], (∀ (α : MulAut G) (g : G), IsConj (α g) g) →
    ∀ α : MulAut G, ∃ h : G, α = MulAut.conj h

/--
Resolved false: the Kourovka Archive answers 16.62 "Not necessarily" (Mann): Heineken constructed
finite `p`-groups all of whose automorphisms preserve every conjugacy class, and Gaschütz' theorem
gives these groups outer automorphisms. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 16.62 (D. MacHale); resolution: H. Heineken, Arch. Math. (Basel) 33
(1979/80), no. 6, 497-503; A. Mann, letter of 20 April 2006, as recorded in the Kourovka Archive,
Kourovka Archive, Problem 16.62 (Not necessarily: Heineken's finite p-groups all of whose
automorphisms preserve all conjugacy classes have outer automorphisms by Gaschütz' theorem).
-/
public theorem_wanted classPreservingAutomorphismsInner_refuted :
    ¬ classPreservingAutomorphismsInner

end MathlibExt.GroupTheory.ClassPreservingAutomorphismsInnerKourovka16Problem62Wanted
