/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups with element orders 1 to 7 (Kourovka Notebook Problem 19.80)

Kourovka Notebook, Archive of Solved Problems, Problem 19.80 (W. J. Shi): for a periodic group `G`
let `π_e(G)` be the set of element orders; `G` is an `OCₙ`-group if `π_e(G) = {1, 2, …, n}`. Is
every `OC₇`-group isomorphic to `A₇`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.SpecificGroups.Alternating

@[expose] public section

namespace MathlibExt.GroupTheory.ElementOrdersOneToSevenAlternatingKourovka19Problem80Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.80 (W. J.
Shi). UnsolvedMath record UM-00701628 (`KOU-19.80`), dataset ulamai/UnsolvedMath v1.8.0.

`π_e(G)` is the range of `orderOf`; since `0 ∉ {1, …, 7}`, the condition already forces `G` to be
periodic. `G : Type` is not assumed finite (the finite case was known).
-/

/-- Kourovka 19.80 (W. J. Shi): every `OC₇`-group, that is, every group whose set of element orders
is exactly `{1, 2, …, 7}` (such a group is periodic), is isomorphic to the alternating group
`A₇`. -/
def ocSevenGroupIsAlternating : Prop :=
  ∀ (G : Type) [Group G], Set.range (fun g : G => orderOf g) = Set.Icc 1 7 →
    Nonempty (G ≃* alternatingGroup (Fin 7))

/--
Resolved true: the Kourovka Archive answers 19.80 "Yes, it is true", citing Jabara and Mamontov:
every (possibly infinite) group with element orders exactly `{1, …, 7}` is isomorphic to `A₇`.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.80 (W. J.
Shi); resolution: A. S. Mamontov and E. Jabara, Recognizing A₇ by its set of element orders,
Siberian Math. J. 62 (2021), no. 1, 93-104, doi:10.1134/S0037446621010109, Kourovka Archive, Problem
19.80: Yes, it is true, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted ocSevenGroupIsAlternating_holds : ocSevenGroupIsAlternating

end MathlibExt.GroupTheory.ElementOrdersOneToSevenAlternatingKourovka19Problem80Wanted
