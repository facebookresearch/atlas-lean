/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partitions of `⊕_{ω₁} ℤ/3ℤ` meeting every infinite coset (Kourovka Notebook Problem 16.43)

Kourovka Notebook, Archive of Solved Problems, Problem 16.43 (E. G. Zelenyuk): is there a partition
of the group `⊕_{ω₁} ℤ/3ℤ` into three subsets whose complements do not contain cosets modulo
infinite subgroups? (There is a partition into two such subsets.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.GroupTheory.PartitionMeetingInfiniteCosetsKourovka16Problem43
