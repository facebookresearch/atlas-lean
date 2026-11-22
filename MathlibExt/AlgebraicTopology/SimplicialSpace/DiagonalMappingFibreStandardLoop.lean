/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibrePathEndpoints

/-!
# The actual original diagonal edge loop

The original endomorphism mapping edge realizes as a compact-open path
with both endpoints equal to the same original diagonal object. This
defines the literal standard edge-loop map used by native bar assembly.
Its weakness will be proved by comparison with the original path fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology
open scoped Simplicial unitInterval

namespace SimplicialSpace.LeftDecalageObject

private theorem realizedMappingSource_constant (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (z : SSet.toTop.obj (mappingFibre W x x)) :
    SSet.toTop.map (mappingFibreDiagonalSource W x x) z = realizedDiagonalPoint W x := by
  unfold mappingFibreDiagonalSource
  rw [Functor.map_comp]
  have hz : SSet.toTop.map (mappingFibre.snd W x x) z =
      (default : SSet.toTop.obj (Δ[0] : SSet.{u})) := Subsingleton.elim _ _
  change SSet.toTop.map (diagonalPoint W x) (SSet.toTop.map (mappingFibre.snd W x x) z) = _
  rw [hz, diagonalPoint_eq_yoneda]
  rfl

/-- The original realized endomorphism edge as a based compact-open loop at its original object. -/
def standardDiagonalLoopValue (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (z : SSet.toTop.obj (mappingFibre W x x)) :
    LoopSpace (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) (realizedDiagonalPoint W x) where
  toFun t := mappingFibreDiagonalPathFamily W x x z (TopCat.I.homeomorph.symm t)
  continuous_toFun := (mappingFibreDiagonalPathFamily W x x z).continuous.comp
    TopCat.I.homeomorph.symm.continuous
  source' := by
    have h := ConcreteCategory.congr_hom (mappingFibreDiagonalPathFamily_zero W x x) z
    change mappingFibreDiagonalPathFamily W x x z (0 : TopCat.I.{u}) = _ at h
    have hi : TopCat.I.homeomorph.symm (0 : unitInterval) = (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    rw [hi]
    exact h.trans (realizedMappingSource_constant W x z)
  target' := by
    have h := ConcreteCategory.congr_hom (mappingFibreDiagonalPathFamily_one W x x) z
    change mappingFibreDiagonalPathFamily W x x z (1 : TopCat.I.{u}) = _ at h
    have hi : TopCat.I.homeomorph.symm (1 : unitInterval) = (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    rw [hi]
    exact h.trans (realizedMappingSource_constant W x z)

end SimplicialSpace.LeftDecalageObject
