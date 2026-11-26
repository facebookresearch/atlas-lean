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

Beeri, Fagin, Maier and Yannakakis, *On the Desirability of Acyclic Database Schemes*,
J. ACM 30 (1983), Theorem 3.4 (p. 488), characterize acyclicity by, among other conditions,
pairwise-to-global consistency, full reducers, join trees and the success of Graham's algorithm.
The formulation below follows Abiteboul, Hull and Vianu, *Foundations of Databases*, §6.4,
Theorem 6.4.5, properties (1)–(4), using their ear-deletion Algorithm 6.4.4. The book's
fifth property uses articulation sets of restricted, reduced hypergraphs.
-/

public section

namespace Cslib.Databases.AcyclicSchema

/-- **Characterizations of acyclic database schemas.** Let a nonempty finite family of distinct
nonempty sets of attributes be the relation schemes. For finite relations over these schemes
with values in the natural numbers, the following are equivalent: every pairwise consistent
instance is globally consistent; there is a single semijoin program that fully reduces every
instance; there is a join tree (each attribute shared by two schemes occurs throughout the path
between them); every maximal GYO ear-removal run ends with no scheme left.
This is the acyclicity characterization of Beeri–Fagin–Maier–Yannakakis, Theorem 3.4,
in the ear-removal formulation of Abiteboul–Hull–Vianu, Theorem 6.4.5. -/
theorem_wanted acyclicSchema_characterizations {N A : Type*} [Fintype N] [Nonempty N]
    [DecidableEq N] [Fintype A] [DecidableEq A] (sch : N → Finset A)
    (distinct : Function.Injective sch) (nonempty : ∀ i, (sch i).Nonempty) :
    List.TFAE [∀ I, Expr.Conforms sch I → PairwiseConsistent sch I → GloballyConsistent sch I,
      HasFullReducer sch, HasJoinTree sch, GYOEmpties sch]

end Cslib.Databases.AcyclicSchema
