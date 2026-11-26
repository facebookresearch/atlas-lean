/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Databases.AcyclicSchema
public import Mathlib.Data.List.TFAE

/-!
# Characterizations of acyclic database schemas

Reference: S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, §6.4,
Theorem 6.4.5, properties (1)–(4). The book also gives a fifth characterization using
articulation sets of restricted, reduced hypergraphs.
-/

public section

namespace Cslib.Databases.AcyclicSchema

/-- **Characterizations of acyclic database schemas.** Let a nonempty finite family of distinct
nonempty sets of attributes be the relation schemes. For finite relations over these schemes
with values in the natural numbers, the following are equivalent: every pairwise consistent
instance is globally consistent; there is a single semijoin program that fully reduces every
instance; there is a join tree with running intersection; every maximal GYO ear-removal run
ends with no scheme left. -/
theorem_wanted acyclicSchema_characterizations {N A : Type*} [Fintype N] [Nonempty N]
    [DecidableEq N] [Fintype A] [DecidableEq A] (sch : N → Finset A)
    (distinct : Function.Injective sch) (nonempty : ∀ i, (sch i).Nonempty) :
    List.TFAE [∀ I, Expr.Conforms sch I → PairwiseConsistent sch I → GloballyConsistent sch I,
      HasFullReducer sch, HasJoinTree sch, GYOEmpties sch]

end Cslib.Databases.AcyclicSchema
