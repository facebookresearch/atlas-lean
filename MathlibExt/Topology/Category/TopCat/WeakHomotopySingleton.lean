/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Weak homotopy equivalences to a singleton

A map from a path-connected topological space to a singleton is a weak
homotopy equivalence when every positive homotopy group at every basepoint
is trivial. The proof compares path components and pointed homotopy groups
through the existing TopCat and singular-complex comparison APIs.
-/

@[expose] public section

universe u

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology Topology.Homotopy

namespace TopCat

section Part1

private theorem positiveGroup_subsingleton_of_space_subsingleton
    (X : TopCat.{u}) (hX : Subsingleton X) (n : ℕ) (x : X) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) := by
  constructor
  intro a b
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective b
  apply congrArg HomotopyGroup.mk
  apply GenLoop.ext
  intro t
  exact hX.elim (p t) (q t)

private theorem zerothHomotopy_subsingleton_of_space_subsingleton
    (X : TopCat.{u}) (hX : Subsingleton X) : Subsingleton (ZerothHomotopy X) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
  exact congrArg ZerothHomotopy.mk (hX.elim x y)

/-- Ordinary weak-equivalence criterion for a map to a singleton space.
The hypotheses are explicitly component and positive-group information;
the projective application below derives both. -/
theorem map_mem_weakHomotopyEquivalences_to_singleton
    {X Z : TopCat.{u}} (f : X ⟶ Z) (hZ : Subsingleton Z)
    (hConn : PathConnectedSpace X)
    (hPositive : ∀ (n : ℕ) (x : X),
      Subsingleton (HomotopyGroup.Pi (n + 1) X x)) :
    TopCat.weakHomotopyEquivalences f := by
  let SX := TopCat.toSSet.obj X
  let SZ := TopCat.toSSet.obj Z
  let s := TopCat.toSSet.map f
  have hSX : SSet.KanComplex SX := TopCat.toSSet_obj_kanComplex X
  have hSZ : SSet.KanComplex SZ := TopCat.toSSet_obj_kanComplex Z
  have hXZero : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp hConn).2
  have hZZero : Subsingleton (ZerothHomotopy Z) :=
    zerothHomotopy_subsingleton_of_space_subsingleton Z hZ
  have hSPiZero : Subsingleton (SSet.π₀ SX) := by
    constructor
    intro a b
    apply (TopCat.zerothHomotopyEquiv (X := X)).symm.injective
    exact hXZero.elim _ _
  have hTPiZero : Subsingleton (SSet.π₀ SZ) := by
    constructor
    intro a b
    apply (TopCat.zerothHomotopyEquiv (X := Z)).symm.injective
    exact hZZero.elim _ _
  apply (TopCat.mem_weakHomotopyEquivalences_iff f).mpr
  refine (@SSet.KanComplex.W_iff SX SZ hSX hSZ s).mpr ⟨?_, ?_⟩
  · constructor
    · intro a b _
      exact hSPiZero.elim a b
    · intro b
      let x := Classical.choice hConn.nonempty
      refine ⟨SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm x), ?_⟩
      exact hTPiZero.elim _ b
  · intro n sx
    obtain ⟨x, rfl⟩ := (TopCat.toSSetObj₀Equiv (X := X)).symm.surjective sx
    have hS : Subsingleton (SSet.KanComplex.π (n + 1) SX
        (TopCat.toSSetObj₀Equiv.symm x)) := by
      constructor
      intro a b
      apply (TopCat.homotopyGroupSingularMulEquiv n X x).symm.injective
      exact (hPositive n x).elim _ _
    have hT : Subsingleton (SSet.KanComplex.π (n + 1) SZ
        (TopCat.toSSetObj₀Equiv.symm (f x))) := by
      constructor
      intro a b
      apply (TopCat.homotopyGroupSingularMulEquiv n Z (f x)).symm.injective
      exact (positiveGroup_subsingleton_of_space_subsingleton Z hZ n (f x)).elim _ _
    constructor
    · intro a b _
      exact hS.elim a b
    · intro b
      refine ⟨TopCat.homotopyGroupSingularMulEquiv n X x 1, ?_⟩
      exact hT.elim _ b

end Part1

end TopCat

end
