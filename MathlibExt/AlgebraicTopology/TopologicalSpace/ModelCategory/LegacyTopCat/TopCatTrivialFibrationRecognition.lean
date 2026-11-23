/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLPReflection
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Trivial-fibration recognition for realized horns in `TopCat`

This file is part of the KQ3 layer. It proves the first remaining cross
inclusion directly by singular/realization transport: a map in
`TopCat.realizedHornInclusions.rlp` that is a weak homotopy equivalence
lies in `TopCat.realizedBoundaryInclusions.rlp`, conditional on the
simplicial-set trivial-fibration characterization
`SSet.modelCategoryQuillen.J.rlp ⊓ SSet.KanComplex.W ≤
SSet.modelCategoryQuillen.I.rlp`.

Two unconditional adjunction transports do the work. Forward, horn-RLP maps
go to `SSet.modelCategoryQuillen.J.rlp` under `TopCat.toSSet` via
`sSetTopAdj.hasLiftingProperty_iff` and
`TopCat.horn_mem_realizedHornInclusions`. Backward, the inverse image of
`SSet.modelCategoryQuillen.I.rlp` lies in realized boundary-RLP maps by the
same adjunction and `SSet.modelCategoryQuillen.boundary_ι_mem_I`. Weak
equivalences transport by definition
(`TopCat.mem_weakHomotopyEquivalences_iff`), so the simplicial hypothesis
closes the singular image and the backward transport returns to spaces.

The simplicial hypothesis is the KQ4-owned key characterization of
weak-equivalence fibrations by boundary lifting (blueprint §5.4 and the KQ4
characterization list); it is not proved here. It is independent of the
Top-side inclusions `J.rlp.llp ≤ W` and `B.rlp ≤ W`: those constrain maps in
`TopCat` through realized generators, while the hypothesis constrains maps
in `SSet` through simplicial generators, so neither side implies the other.
Moreover the two Top cross inclusions are interdependent through the staged
retract/factorization lemmas in `TopCatModelCompatibilityConditional`, so
the Top-side inclusions alone cannot yield the target. This file supplies
the missing premise unlocking those lemmas: with the target proved,
`TopCat.boundaryLLP_inf_W_le_hornLLP` gives the opposite cross inclusion
from horn-cell closure, with no retract argument duplicated here.

This proves only the stated conditional inclusion. It does not supply the
simplicial hypothesis, and claims no reverse inclusion, no equality, and no
model structure. It assumes neither the target inclusion nor a model
structure.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Conditional recognition: horn-RLP weak equivalences are boundary-RLP maps. -/
theorem hornRLP_inf_W_le_boundaryRLP_of_sSet
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences ≤
      realizedBoundaryInclusions.{u}.rlp := by
  intro X Y f hf
  obtain ⟨hfR, hfW⟩ := hf
  have hSingR : SSet.modelCategoryQuillen.J.{u}.rlp (toSSet.map f) :=
    hornRLP_eq_inverseImage_J_rlp.le _ hfR
  have hSingW : SSet.KanComplex.W.{u} (toSSet.map f) :=
    (mem_weakHomotopyEquivalences_iff f).mp hfW
  have hSingI : SSet.modelCategoryQuillen.I.{u}.rlp (toSSet.map f) :=
    hSSet _ ⟨hSingR, hSingW⟩
  exact inverseImage_I_rlp_le_boundaryRLP _ hSingI

end TopCat
