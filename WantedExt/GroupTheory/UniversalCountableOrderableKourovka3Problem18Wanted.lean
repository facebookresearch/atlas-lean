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
# Countable universal groups for countable orderable groups (Kourovka Notebook Problem 3.18)

Kourovka Notebook, Archive of Solved Problems, Problem 3.18 (B. H. Neumann; A. I. Kokorin): a group
`U` is called universal for a class `𝔎` of groups if `U` contains an isomorphic image of every
member of `𝔎`. Does there exist a countable group that is universal for the class of countable
orderable groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Countable.Defs
public import MathlibExt.GroupTheory.Orderability

@[expose] public section

namespace MathlibExt.GroupTheory.UniversalCountableOrderableKourovka3Problem18Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.18 (B. H.
Neumann; A. I. Kokorin). UnsolvedMath record UM-00700172 (`KOU-3.18`), dataset ulamai/UnsolvedMath
v1.8.0.

Orderable means admitting a bi-invariant linear order (`MathlibExt.GroupTheory.IsOrderable` from
the neutral orderability API); `U` itself need not be orderable. Groups in `Type`.
-/

open MathlibExt.GroupTheory (IsOrderable)

/-- Kourovka 3.18 (B. H. Neumann; A. I. Kokorin): there is a countable group `U` containing an
isomorphic copy of every countable orderable group. -/
def existsCountableUniversalOrderable : Prop :=
  ∃ (U : Type) (_ : Group U), Countable U ∧ ∀ (G : Type) [Group G], Countable G → IsOrderable G →
    ∃ f : G →* U, Function.Injective f

/--
Resolved false: the Kourovka Archive answers 3.18 "No", citing Kargapolov (Algebra and Logic 9
(1970)) and Smith (Pacific J. Math. 35 (1970)): no countable group contains an isomorphic copy of
every countable orderable group. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 3.18 (B. H. Neumann; A. I. Kokorin); resolution: M. I. Kargapolov, Algebra and
Logic 9 (1970), 257-261; D. B. Smith, Pacific J. Math. 35 (1970), 499-502, Kourovka Archive, Problem
3.18: No, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsCountableUniversalOrderable_refuted :
    ¬ existsCountableUniversalOrderable

private example : ProofWanted.Stmt existsCountableUniversalOrderable_refuted ↔
    ¬ existsCountableUniversalOrderable :=
  Iff.rfl

end MathlibExt.GroupTheory.UniversalCountableOrderableKourovka3Problem18Wanted
