/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.HoIsoEquivalenceFibreLift
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance

/-!
# Homotopy-isomorphism transport of mapping-fibre weakness

For a map of Reedy-fibrant Segal spaces, weakness of its original mapping-fibre map is unchanged
when both source objects are replaced by isomorphic objects in the source homotopy category. The
comparison retains chosen equivalence-fibre representatives, their actual images under the map,
and the precomposition and postcomposition homotopies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MorphismProperty Opposite
open scoped Simplicial

namespace SimplicialSpace.IntrinsicDK
open SegalHomotopy SegalEquivalenceHomTransport HoIsoEquivalenceFibreLift

/-- Full weakness of the original fibre map is equivalent at any two
Ho-isomorphic source/target pairs. Both scalar operators use the SAME
chosen EF points and their ACTUAL images, without natural-choice assumptions. -/
theorem mappingFibreWeak_iff_of_HoIsos {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (⟨x⟩ : Object W hW) ≅ (⟨x'⟩ : Object W hW))
    (b : (⟨y⟩ : Object W hW) ≅ (⟨y'⟩ : Object W hW)) :
    SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl) ↔
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x') (y := y') rfl rfl) := by
  let ea := equivalencePointOfIso W hW x x' a
  let eb := equivalencePointOfIso W hW y y' b
  let eaV := (equivalenceFibreMap f hW hV (x := x) (y := x') rfl rfl).app (op ⦋0⦌) ea
  let ebV := (equivalenceFibreMap f hW hV (x := y) (y := y') rfl rfl).app (op ⦋0⦌) eb
  let a0 := (equivalenceFibreToMappingFibre W hW x x').app (op ⦋0⦌) ea
  let b0 := (equivalenceFibreToMappingFibre W hW y y').app (op ⦋0⦌) eb
  let a1 := (equivalenceFibreToMappingFibre V hV
    (mappingVertexMap f x) (mappingVertexMap f x')).app (op ⦋0⦌) eaV
  let b1 := (equivalenceFibreToMappingFibre V hV
    (mappingVertexMap f y) (mappingVertexMap f y')).app (op ⦋0⦌) ebV
  have haPoint : a1 =
      (mappingFibre.map f (x := x) (y := x') rfl rfl).app (op ⦋0⦌) a0 := by
    have e := congrArg (fun k => k.app (op ⦋0⦌) ea)
      (equivalenceFibreMap_laws f hW hV (x := x) (y := x') rfl rfl).2.2.1
    change a1 = (mappingFibre.map f (x := x) (y := x') rfl rfl).app (op ⦋0⦌) a0 at e
    exact e
  have hbPoint : b1 =
      (mappingFibre.map f (x := y) (y := y') rfl rfl).app (op ⦋0⦌) b0 := by
    have e := congrArg (fun k => k.app (op ⦋0⦌) eb)
      (equivalenceFibreMap_laws f hW hV (x := y) (y := y') rfl rfl).2.2.1
    change b1 = (mappingFibre.map f (x := y) (y := y') rfl rfl).app (op ⦋0⦌) b0 at e
    exact e
  let pW := postcomposePoint W hW y y' eb x
  let aW := precomposePoint W hW x x' ea y'
  let pV := postcomposePoint V hV (mappingVertexMap f y) (mappingVertexMap f y')
    ebV (mappingVertexMap f x)
  let aV := precomposePoint V hV (mappingVertexMap f x) (mappingVertexMap f x')
    eaV (mappingVertexMap f y')
  let m0 := mappingFibre.map f (x := x) (y := y) rfl rfl
  let mm := mappingFibre.map f (x := x) (y := y') rfl rfl
  let m1 := mappingFibre.map f (x := x') (y := y') rfl rfl
  have hpW : SSet.realizationWeakEquivalences pW :=
    postcomposePoint_realizationWeak W hW y y' eb x
  have haW : SSet.realizationWeakEquivalences aW :=
    precomposePoint_realizationWeak W hW x x' ea y'
  have hpV : SSet.realizationWeakEquivalences pV :=
    postcomposePoint_realizationWeak V hV _ _ ebV _
  have haV : SSet.realizationWeakEquivalences aV :=
    precomposePoint_realizationWeak V hV _ _ eaV _
  have Hpost : SSet.Homotopy (pW ≫ mm) (m0 ≫ pV) := by
    change SSet.Homotopy
      (mappingPostcomposition W hW x y y' b0 ≫ mm)
      (m0 ≫ mappingPostcomposition V hV (mappingVertexMap f x)
        (mappingVertexMap f y) (mappingVertexMap f y') b1)
    rw [hbPoint]
    exact mappingPostcompositionNaturality f hW hV x y y' b0
  have Hpre : SSet.Homotopy (aW ≫ mm) (m1 ≫ aV) := by
    change SSet.Homotopy
      (mappingPrecomposition W hW x x' y' a0 ≫ mm)
      (m1 ≫ mappingPrecomposition V hV (mappingVertexMap f x)
        (mappingVertexMap f x') (mappingVertexMap f y') a1)
    rw [haPoint]
    exact mappingPrecompositionNaturality f hW hV x x' y' a0
  have hp : SSet.realizationWeakEquivalences m0 ↔ SSet.realizationWeakEquivalences mm :=
    (SSet.realizationWeakEquivalences.postcomp_iff m0 pV hpV).symm.trans
      ((SSet.realizationWeakEquivalences_iff_of_homotopy Hpost).symm.trans
        (SSet.realizationWeakEquivalences.precomp_iff pW mm hpW))
  have ha : SSet.realizationWeakEquivalences mm ↔ SSet.realizationWeakEquivalences m1 :=
    (SSet.realizationWeakEquivalences.precomp_iff aW mm haW).symm.trans
      ((SSet.realizationWeakEquivalences_iff_of_homotopy Hpre).trans
        (SSet.realizationWeakEquivalences.postcomp_iff m1 aV haV))
  exact hp.trans ha

end SimplicialSpace.IntrinsicDK
