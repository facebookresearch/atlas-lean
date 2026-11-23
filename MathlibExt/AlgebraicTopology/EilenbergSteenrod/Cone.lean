/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.TripleSequenceExact
public import MathlibExt.Topology.Category.TopCat.Suspension.HeightCover
public import MathlibExt.Topology.Category.TopPair.Cone
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.MayerVietoris

/-!
# Relative homology of the cone-apex pair

Homotopy invariance and exactness imply that the relative homology of a
nonempty cone modulo its apex vanishes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover

universe w u v

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Relative homology of a nonempty cone modulo its apex vanishes. -/
theorem isZero_relative_coneApex
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) (X : TopCat.{w}) [Nonempty X] :
    IsZero ((E.Hₚ n).obj
      (PointedTopCat.pointedPair.obj (Under.mk (TopCat.conePoint X)))) :=
  (isZero_relative_diag E n (TopCat.of PUnit.{w + 1})).of_iso
    (E.relativeIsoOfHomotopyEquiv (TopPair.coneApexPairHomotopyEquiv X) n)

/-- The outer relative term of the pointed-cone triple vanishes. -/
theorem isZero_pointedConeTriple_pair02
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    IsZero ((E.Hₚ n).obj
      (AlgebraicTopology.topTriplePair02.obj
        (TopCat.pointedConeTripleFunctor.obj X))) := by
  apply isZero_relative_of_homotopyEquiv E n
    (AlgebraicTopology.topTriplePair02.obj
      (TopCat.pointedConeTripleFunctor.obj X))
    (TopCat.pointedConeBasepointHomotopyEquiv X)
  change TopCat.ofHom (TopCat.pointedConeBasepointHomotopyEquiv X).toFun =
    X.hom ≫ TopCat.coneBase X.right
  exact TopCat.pointedConeBasepointHomotopyEquiv_toFun X

/-- The triple boundary for pointed cones is a natural isomorphism. -/
noncomputable def pointedConeTripleBoundaryNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) :
    TopCat.pointedConeTripleFunctor ⋙ AlgebraicTopology.topTriplePair12 ⋙ E.Hₚ n ≅
      TopCat.pointedConeTripleFunctor ⋙ AlgebraicTopology.topTriplePair01 ⋙
        E.Hₚ (n - 1) :=
  tripleBoundaryNatIsoOfIsZeroPair02 E n TopCat.pointedConeTripleFunctor
    (fun X => isZero_pointedConeTriple_pair02 E n X)
    (fun X => isZero_pointedConeTriple_pair02 E (n - 1) X)

/-- The inclusion from the cone/base pair to the cone/lower-neighborhood pair induces
an isomorphism on relative homology. -/
theorem isIso_map_conePairToHeightCover
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    IsIso ((E.Hₚ n).map (TopPair.conePairToHeightCoverNatTrans.app X)) := by
  let f := TopPair.conePairToHeightCoverNatTrans.app X
  let _ : Nonempty X.right := ⟨X.hom PUnit.unit⟩
  let _ : IsIso ((E.H n).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H n).map (TopPair.coneBaseToLower X.right))
    rw [← TopCat.coneBaseToLowerHomotopyEquiv_toFun]
    exact (E.absoluteIsoOfHomotopyEquiv
      (TopCat.coneBaseToLowerHomotopyEquiv X.right) n).isIso_hom
  let _ : IsIso ((E.H n).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H n).map (𝟙 _))
    infer_instance
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H (n - 1)).map (TopPair.coneBaseToLower X.right))
    rw [← TopCat.coneBaseToLowerHomotopyEquiv_toFun]
    exact (E.absoluteIsoOfHomotopyEquiv
      (TopCat.coneBaseToLowerHomotopyEquiv X.right) (n - 1)).isIso_hom
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H (n - 1)).map (𝟙 _))
    infer_instance
  exact isIso_relativeMap_of_isIso_absoluteMaps E n f

/-- Relative homology of the cone/base pair is naturally isomorphic to relative homology
of the cone modulo its lower height neighborhood. -/
noncomputable def conePairHeightCoverNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) :
    TopCat.pointedConeTripleFunctor ⋙ topTriplePair12 ⋙ E.Hₚ n ≅
      Under.forget (TopCat.of PUnit) ⋙ TopCat.coneHeightCoverFunctor ⋙
        spaceLeftPairFunctor ⋙ E.Hₚ n := by
  let α := Functor.whiskerRight TopPair.conePairToHeightCoverNatTrans (E.Hₚ n)
  let _ (X : PointedTopCat.{w}) : IsIso (α.app X) :=
    isIso_map_conePairToHeightCover E n X
  exact NatIso.ofComponents (fun X => asIso (α.app X))
    (fun f => α.naturality f)

/-- The pointed suspension pair and its upper height neighborhood have isomorphic relative
homology. -/
theorem isIso_map_suspensionPairToHeightCover
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    IsIso ((E.Hₚ n).map (TopPair.suspensionPairToHeightCoverNatTrans.app X)) := by
  let f := TopPair.suspensionPairToHeightCoverNatTrans.app X
  let _ : Nonempty X.right := ⟨X.hom PUnit.unit⟩
  let _ : IsIso ((E.H n).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H n).map (TopPair.suspensionPointToUpper X.right))
    rw [← TopCat.suspensionPointToUpperHomotopyEquiv_toFun]
    exact (E.absoluteIsoOfHomotopyEquiv
      (X := TopCat.of PUnit) (Y := TopCat.of (TopCat.suspensionUpperSet X.right))
      (TopCat.suspensionPointToUpperHomotopyEquiv X.right) n).isIso_hom
  let _ : IsIso ((E.H n).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H n).map (𝟙 _))
    infer_instance
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H (n - 1)).map (TopPair.suspensionPointToUpper X.right))
    rw [← TopCat.suspensionPointToUpperHomotopyEquiv_toFun]
    exact (E.absoluteIsoOfHomotopyEquiv
      (X := TopCat.of PUnit) (Y := TopCat.of (TopCat.suspensionUpperSet X.right))
      (TopCat.suspensionPointToUpperHomotopyEquiv X.right) (n - 1)).isIso_hom
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H (n - 1)).map (𝟙 _))
    infer_instance
  exact isIso_relativeMap_of_isIso_absoluteMaps E n f

/-- Relative homology of the pointed suspension pair is naturally isomorphic to relative
homology modulo the upper height neighborhood. -/
noncomputable def suspensionPairHeightCoverNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) :
    Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair ⋙ E.Hₚ n ≅
      Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionHeightCoverFunctor ⋙
        spaceLeftPairFunctor ⋙ E.Hₚ n := by
  let α := Functor.whiskerRight TopPair.suspensionPairToHeightCoverNatTrans (E.Hₚ n)
  let _ (X : PointedTopCat.{w}) : IsIso (α.app X) :=
    isIso_map_suspensionPairToHeightCover E n X
  exact NatIso.ofComponents (fun X => asIso (α.app X))
    (fun f => α.naturality f)

set_option backward.isDefEq.respectTransparency false in
theorem isIso_map_conePairToSuspensionPair
    (E : HomologyTheoryData.{w} C) [E.IsExcisive] [E.IsExact]
    [E.IsHomotopyInvariant] (n : ℤ) (X : PointedTopCat.{w}) :
    IsIso ((E.Hₚ n).map (TopPair.conePairToSuspensionPairNatTrans.app X)) := by
  let fCone := TopPair.conePairToHeightCoverNatTrans.app X
  let fSuspHeight := TopPair.suspensionPairToHeightCoverNatTrans.app X
  let fSuspPair := TopPair.conePairToSuspensionPairNatTrans.app X
  let g := spaceLeftPairFunctor.map
    (TopCat.coneToSuspensionHeightCoverNatTrans.app X.right)
  have hCone : IsIso ((E.Hₚ n).map fCone) :=
    isIso_map_conePairToHeightCover E n X
  have hSuspHeight : IsIso ((E.Hₚ n).map fSuspHeight) :=
    isIso_map_suspensionPairToHeightCover E n X
  have hRight : IsIso ((E.Hₚ n).map
      (rightInterPairFunctor.map
        (TopCat.coneToSuspensionHeightCoverNatTrans.app X.right))) := by
    rw [← TopPair.coneToSuspensionHeightCoverRightInterPairNatIso_hom_app X.right]
    infer_instance
  have hG : IsIso ((E.Hₚ n).map g) := by
    have hIff := HomologyTheoryData.IsExcisive.isIso_map_spaceLeftPairFunctor_map_iff
      (C := C) (E := E) (n := n)
      (f := TopCat.coneToSuspensionHeightCoverNatTrans.app X.right)
    exact hIff.mp hRight
  have hComm : fCone ≫ g = fSuspPair ≫ fSuspHeight :=
    TopPair.conePairToSuspensionPair_heightCover X
  have hLeftComp : IsIso ((E.Hₚ n).map fCone ≫ (E.Hₚ n).map g) := by
    infer_instance
  have hEq : (E.Hₚ n).map fCone ≫ (E.Hₚ n).map g =
      (E.Hₚ n).map fSuspPair ≫ (E.Hₚ n).map fSuspHeight := by
    rw [← Functor.map_comp, ← Functor.map_comp, hComm]
  have hRightComp : IsIso ((E.Hₚ n).map fSuspPair ≫ (E.Hₚ n).map fSuspHeight) := by
    rw [← hEq]
    exact hLeftComp
  have : IsIso ((E.Hₚ n).map fSuspPair ≫ (E.Hₚ n).map fSuspHeight) := hRightComp
  exact IsIso.of_isIso_comp_right ((E.Hₚ n).map fSuspPair) ((E.Hₚ n).map fSuspHeight)

end TopPair.HomologyTheoryData.IsExact
