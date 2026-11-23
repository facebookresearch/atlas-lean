/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup

/-!
# The second homotopy group of a groupoid nerve

Pointed two-simplices are uniquely determined by their constant horn restriction.
Their quotient therefore has trivial second homotopy group at every vertex of an
arbitrary groupoid nerve, with independent object and Hom universes.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u v

namespace SSet

private theorem pointedNerveTwo_subsingleton (C : Type u) [Groupoid.{v} C]
    (x : CategoryTheory.nerve C _⦋0⦌) :
    Subsingleton ((CategoryTheory.nerve C).PtSimplex 2 x) := by
  constructor
  intro s t
  apply SSet.RelativeMorphism.ext
  apply SSet.yonedaEquiv.injective
  apply CategoryTheory.nerve.eq_of_twoHornRestriction_eq C (1 : Fin 3)
  simpa only [Equiv.symm_apply_apply] using
    (s.comp_map_eq_const (SSet.horn 2 (1 : Fin 3)).ι).trans
      (t.comp_map_eq_const (SSet.horn 2 (1 : Fin 3)).ι).symm

/-- The second homotopy group of a groupoid nerve is trivial at every vertex. -/
theorem piTwo_nerve_subsingleton (C : Type u) [Groupoid.{v} C]
    (x : CategoryTheory.nerve C _⦋0⦌) :
    Subsingleton (SSet.KanComplex.π 2 (CategoryTheory.nerve C) x) := by
  let _ := pointedNerveTwo_subsingleton C x
  exact Function.Surjective.subsingleton SSet.KanComplex.π.mk_surjective

end SSet
