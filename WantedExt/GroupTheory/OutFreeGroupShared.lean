/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The outer automorphism group `Out(F_n)` of a free group

Shared helper for the UnsolvedMath entries on `Out(F_n)` from Farb (ed.), Problems on Mapping Class
Groups and Related Topics
(`WantedExt/GroupTheory/AutFreeGroupDehnFunctionAMR109Problem0300Wanted.lean` and
`WantedExt/GroupTheory/OutFreeGroupStableHomologyAMR109Problem0315Wanted.lean`), so both speak
about the same group.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.OutFreeGroupShared

/-- `Out(F_n) = Aut(F_n) / Inn(F_n)`, with `Aut(F_n) = MulAut (FreeGroup (Fin n))`. The inner
automorphisms (the image of `MulAut.conj`) form a normal subgroup, so the normal closure below is
`Inn(F_n)` itself. -/
abbrev OutFreeGroup (n : ℕ) : Type :=
  MulAut (FreeGroup (Fin n)) ⧸ Subgroup.normalClosure
    (Set.range (MulAut.conj : FreeGroup (Fin n) →* MulAut (FreeGroup (Fin n))))

end MathlibExt.GroupTheory.OutFreeGroupShared
