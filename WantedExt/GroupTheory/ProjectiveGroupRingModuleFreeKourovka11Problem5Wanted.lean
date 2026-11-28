/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Projective modules over group rings of polycyclic groups (Kourovka Notebook Problem 11.5)

Kourovka Notebook, Problem 11.5 (V. A. Artamonov): let `k` be a commutative ring and `G` a
torsion-free almost polycyclic group. If `P` is a finitely generated projective `kG`-module
containing two elements independent over `kG`, is `P` free?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Finiteness.Defs
public import MathlibExt.GroupTheory.GroupClassesShared
public import MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5

@[expose] public section

namespace MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.5 (V. A. Artamonov). UnsolvedMath record
UM-00700698 (`KOU-11.5`), dataset ulamai/UnsolvedMath v1.8.0.

The statement is the literal one, over an arbitrary commutative ring `k`, which is what the Notebook
asks and what its accepted answer refutes. Almost polycyclic means polycyclic-by-finite (a
polycyclic subgroup of finite index; `IsAlmostPolycyclic` of `GroupClassesShared`); torsion-free
means no nontrivial element of finite order. The group ring `kG` is `MonoidAlgebra k G`, and two
independent elements are a `kG`-linearly independent pair. The refutation uses a coefficient ring
that is not a field, `𝔽₂ × 𝔽₂` (it has nontrivial idempotents), and the trivial group; the question
for field coefficients is not settled by it.
-/

open MathlibExt.GroupTheory.GroupClassesShared (IsAlmostPolycyclic)

end MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted
