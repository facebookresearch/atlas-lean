/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section

/-!
# Continuous semilinear representations

This file records the object-level data of a continuous semilinear group representation on a
finite free module over a topological ring.

The topology on the module is required to be the finite product topology transported through the
coordinates of `Module.Free.chooseBasis`.
-/

/-- **Continuous semilinear representation.** Let $G$ be a topological group, $R$ a topological
ring and $M$ a topological abelian group that is a finite free $R$-module. Suppose that $G$ acts
on $R$ by ring automorphisms and on $M$ by additive automorphisms, and that the actions of $G$ on
$R$, of $G$ on $M$ and of $R$ on $M$ are jointly continuous. This is a continuous semilinear
representation of $G$ on $M$ when $g \cdot (r x) = (g \cdot r)(g \cdot x)$ for all $g \in G$,
$r \in R$ and $x \in M$, and the coordinate map $M \to R^n$ of a fixed basis of $M$ over $R$,
where $n$ is the size of the basis, is a homeomorphism onto $R^n$ with the product topology.

Source: arXiv:2608.00845, Definition `defsemilinrep` (lines 1947–1950); this class records its
object-level content.
-/
class IsContinuousSemilinearRepresentation (G R M : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    [MulSemiringAction G R] [DistribMulAction G M]
    [ContinuousSMul G R] [ContinuousSMul G M] [ContinuousSMul R M] : Prop
    extends SMulDistribClass G R M where
  /-- The topology on `M` is the product topology transported through coordinates in a finite
  `R`-basis. -/
  isHomeomorph_equivFun : IsHomeomorph (Module.Free.chooseBasis R M).equivFun

end
