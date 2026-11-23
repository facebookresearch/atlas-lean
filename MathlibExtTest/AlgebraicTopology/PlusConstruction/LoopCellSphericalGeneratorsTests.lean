/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellSphericalGenerators

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology Topology.CWComplex
open AlgebraicTopology.LoopCellSphericalGenerators
open scoped Simplicial SSet.modelCategoryQuillen

universe u

attribute [local instance] TopCat.toSSet_obj_kanComplex

#check @AlgebraicTopology.LoopCellSphericalGenerators.nativePullbackPiOneEquiv
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.nativePullbackPiOneEquiv
#check @AlgebraicTopology.LoopCellSphericalGenerators.homologyOne_nativePullback_isZero
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.homologyOne_nativePullback_isZero
#check @AlgebraicTopology.LoopCellSphericalGenerators.liftedCharacteristicDiskPair_down
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.liftedCharacteristicDiskPair_down
#check @AlgebraicTopology.LoopCellSphericalGenerators.relativeProjection_epi
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.relativeProjection_epi
#check @AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator
#check @AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator_homology
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator_homology
#check @AlgebraicTopology.LoopCellSphericalGenerators.exists_sphericalGenerators_of_connectedCW
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.exists_sphericalGenerators_of_connectedCW

/-- The computed point and actual P-equivalence retain the original projection. -/
example (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    ((nativePullbackProjection X x P).app _ (nativePullbackPoint X x P) =
      nativeBasePoint X x) ∧
    (letI := nativePullback_kan X x P
     ∀ a : SSet.KanComplex.π 1 (nativePullback X x P) (nativePullbackPoint X x P),
       (nativePullbackPiOneEquiv X x P a).val =
         ((SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd (nativeBasePoint X x)).trans
           (TopCat.singularFundamentalGroupoidEndMulEquiv X x))
           (SSet.KanComplex.π.map (nativePullbackProjection X x P)
             (nativePullbackPoint_projection X x P) 1 a)) := by
  exact ⟨nativePullbackPoint_projection X x P, nativePullbackPiOneEquiv_value X x P⟩

/-- The actual realized old cover has zero H1 for the original perfect subgroup. -/
example (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
        (SSet.toTop.obj (nativePullback X x P))) :=
  homologyOne_nativePullback_isZero X x P

/-- The full original D2 pair and its native/matched-arrow characteristics agree. -/
example (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (liftedCharacteristicDiskPair X x P p ≫ liftedPairToOriginal X x P =
      LoopCellAttachment.cellPairMap X x P p) ∧
    (nativeDiskLift X x P p ≫ SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P) =
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
        ((diskBoundaryArrowIso 2).hom.right ≫ LoopCellAttachment.cell X x P p)) ∧
    (nativeBoundaryLift X x P p ≫ nativePullbackProjection X x P =
      sSetTopAdj.homEquiv (SSet.boundary.{u} 2).toSSet X
        ((diskBoundaryArrowIso 2).hom.left ≫ LoopCellAttachment.attachingMap X x P p)) ∧
    (nativeBoundaryLift X x P p ≫ nativePullbackToCover X x P =
      (SSet.boundary.{u} 2).ι ≫ nativeDiskLift X x P p) ∧
    (TopPair.Hom.fst (liftedCharacteristicDiskPair X x P p) =
      (diskBoundaryArrowIso 2).inv.right ≫ SSet.toTop.map (nativeDiskLift X x P p)) ∧
    (TopPair.Hom.snd (liftedCharacteristicDiskPair X x P p) =
      (diskBoundaryArrowIso 2).inv.left ≫ SSet.toTop.map (nativeBoundaryLift X x P p)) := by
  exact ⟨liftedCharacteristicDiskPair_down X x P p, nativeDiskLift_projection X x P p,
    nativeBoundaryLift_source X x P p, nativeBoundaryLift_toCover X x P p,
    liftedCharacteristicDiskPair_fst X x P p, liftedCharacteristicDiskPair_snd X x P p⟩

/-- The computed upstairs absolute preimage gives the original relative p-coordinate. -/
example (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map (liftedPairToOriginal X x P)
        (relativeProjection X x P (absoluteGenerator X x P p)) =
      LoopCellAttachment.relativeGenerator X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u}) p (ULift.up (1 : ℤ)) :=
  absoluteGenerator_down X x P p

/-- The SAME sphere sends the actual original delta3 generator to every p-coordinate. -/
example (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (p : P) (a : (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    ((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).hom ≫
      ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).app
          (classicalCellDiskPair.{u} 3)).inv ≫
      (singularHomologyIntData AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 3
          (classicalCellDiskPair.{u} 3) ≫
      ((singularHomologyNatToIntIso AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app
          (classicalCellDiskPair.{u} 3).snd).hom ≫
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map (sphericalGenerator X x P p)) ≫
      LoopCellAttachment.absoluteToRelativeHomologyTwo X x P) a =
      LoopCellAttachment.relativeGenerator X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u}) p a := by
  have h := sphericalGenerator_value X x P p a
  rw [classicalCellBoundaryHomologyTwoGenerator_eq_original_boundary] at h
  exact h

/-- The complete original connected-CW input constructs the entire sphere family. -/
example (X : TopCat.{u}) [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    ∃ h : ∀ _p : P, (classicalCellDiskPair.{u} 3).snd ⟶ LoopCellAttachment.space X x P,
      ∀ p : P, classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (h p)) ≫
          LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
            LoopCellAttachment.relativeGenerator X x P
              (singularIntegralCoefficients : AddCommGrpCat.{u}) p :=
  exists_sphericalGenerators_of_connectedCW X x P

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open AlgebraicTopology.LoopCellSphericalGenerators

universe w

#check AlgebraicTopology.LoopCellSphericalGenerators.liftedSphericalGenerator
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.liftedSphericalGenerator
#check AlgebraicTopology.LoopCellSphericalGenerators.liftedSphericalGenerator_value
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.liftedSphericalGenerator_value
#check AlgebraicTopology.LoopCellSphericalGenerators.liftedSphericalGenerator_down
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.liftedSphericalGenerator_down

/-- The entire upstairs boundary morphism, without passing to its augmented downstairs value. -/
theorem client_whole_calibrated_upstairs_boundary (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    classicalCellBoundaryHomologyTwoGenerator.{w} ≫
        (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{w})).map
            (liftedSphericalGenerator X x P p)) ≫ relativeProjection X x P =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{w, w}
        (singularIntegralCoefficients : AddCommGrpCat.{w}) 2).hom ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{w}
            (singularIntegralCoefficients : AddCommGrpCat.{w}) 2).map
              (liftedCharacteristicDiskPair X x P p) := by
  ext a
  exact liftedSphericalGenerator_value X x P p a

/-- The upstairs boundary and its original sphere projection use the SAME actual maps. -/
theorem client_same_sphere_original_projection (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    liftedSphericalGenerator X x P p ≫ TopPair.Hom.fst (liftedPairToOriginal X x P) =
        sphericalGenerator X x P p ∧
      ((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{w, w}
          (singularIntegralCoefficients : AddCommGrpCat.{w}) 2).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{w}
          (singularIntegralCoefficients : AddCommGrpCat.{w}) 2).map
            (liftedCharacteristicDiskPair X x P p)) ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{w}
          (singularIntegralCoefficients : AddCommGrpCat.{w}) 2).map
            (liftedPairToOriginal X x P) =
      LoopCellAttachment.relativeGenerator X x P
        (singularIntegralCoefficients : AddCommGrpCat.{w}) p := by
  constructor
  · exact (congrArg (fun d => liftedSphericalGenerator X x P p ≫ d)
      (liftedPairToOriginal_fst X x P)).trans (liftedSphericalGenerator_down X x P p)
  · let Hrel : TopPair.{w} ⥤ AddCommGrpCat.{w} :=
      relativeSingularHomologyFunctor AddCommGrpCat.{w}
        (singularIntegralCoefficients : AddCommGrpCat.{w}) 2
    let g := (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{w, w}
      (singularIntegralCoefficients : AddCommGrpCat.{w}) 2).hom
    exact (Category.assoc g (Hrel.map (liftedCharacteristicDiskPair X x P p))
        (Hrel.map (liftedPairToOriginal X x P))).trans
      ((congrArg (fun h => g ≫ h)
        (Hrel.map_comp (liftedCharacteristicDiskPair X x P p)
          (liftedPairToOriginal X x P)).symm).trans
        ((congrArg (fun d => g ≫ Hrel.map d)
          (liftedCharacteristicDiskPair_down X x P p)).trans
          (LoopCellAttachment.relativeGenerator_eq_characteristic X x P
            (singularIntegralCoefficients : AddCommGrpCat.{w}) p).symm))

#check @AlgebraicTopology.LoopCellSphericalGenerators.sphericalHomologyTwoSection
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.sphericalHomologyTwoSection
#check @AlgebraicTopology.LoopCellSphericalGenerators.sphericalHomologyTwoSplitting
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.sphericalHomologyTwoSplitting
#check @AlgebraicTopology.LoopCellSphericalGenerators.sphericalHomologyTwoSplitIso
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.sphericalHomologyTwoSplitIso
#check @AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator_homologyTwoCoordinate
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator_homologyTwoCoordinate
#check @AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator_homologyTwoCoordinate_value
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator_homologyTwoCoordinate_value
#check @AlgebraicTopology.LoopCellSphericalGenerators.exists_sphericalGenerators_with_homologyTwoSplit_of_connectedCW
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.exists_sphericalGenerators_with_homologyTwoSplit_of_connectedCW

/-- The SAME actual sphere has both full absolute direct-sum coordinates. -/
theorem client_same_sphere_absolute_coordinate (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    classicalCellBoundaryHomologyTwoGenerator.{w} ≫
        (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{w})).map (sphericalGenerator X x P p)) ≫
      (sphericalHomologyTwoSplitIso X x P).hom =
        Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{w})) p ≫ biprod.inr :=
  sphericalGenerator_homologyTwoCoordinate X x P p

/-- Every integral coefficient of the same class has the stated absolute coordinate. -/
theorem client_same_sphere_integer_coordinate (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (p : P) (a : (singularIntegralCoefficients : AddCommGrpCat.{w})) :
    (classicalCellBoundaryHomologyTwoGenerator.{w} ≫
        (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{w})).map (sphericalGenerator X x P p)) ≫
      (sphericalHomologyTwoSplitIso X x P).hom) a =
        (Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{w})) p ≫ biprod.inr) a :=
  sphericalGenerator_homologyTwoCoordinate_value X x P p a

/-- The original old-space inclusion and actual relative projection are unchanged. -/
theorem client_same_sphere_split_original_maps (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{w})).map (LoopCellAttachment.inclusion X x P)) ≫
        (sphericalHomologyTwoSplitIso X x P).hom = biprod.inl ∧
      (sphericalHomologyTwoSplitIso X x P).hom ≫ biprod.snd =
        LoopCellAttachment.absoluteToRelativeHomologyTwo X x P ≫
          (LoopCellAttachment.relativeHomologyTwoIso X x P
            (singularIntegralCoefficients : AddCommGrpCat.{w})).inv := by
  constructor
  · exact sphericalHomologyTwoSplitIso_inclusion X x P
  · exact (sphericalHomologyTwoSplitIso_projection X x P).trans
      (LoopCellAttachment.homologyTwoProjection_eq X x P)

/-- Both full maps of the same-sphere splitting are strict inverse group maps. -/
theorem client_same_sphere_split_both_inverse (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (sphericalHomologyTwoSplitIso X x P).hom ≫ (sphericalHomologyTwoSplitIso X x P).inv = 𝟙 _ ∧
      (sphericalHomologyTwoSplitIso X x P).inv ≫ (sphericalHomologyTwoSplitIso X x P).hom = 𝟙 _ :=
  ⟨sphericalHomologyTwoSplitIso_hom_inv X x P, sphericalHomologyTwoSplitIso_inv_hom X x P⟩

/-- The section contains the exact chosen spheres, and the inverse contains
that same section with the unchanged original inclusion. -/
theorem client_same_sphere_split_section_and_inverse (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{w})) p ≫
      sphericalHomologyTwoSection X x P =
        classicalCellBoundaryHomologyTwoGenerator.{w} ≫
          (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
            (singularIntegralCoefficients : AddCommGrpCat.{w})).map (sphericalGenerator X x P p)) ∧
      (sphericalHomologyTwoSplitIso X x P).inv =
        biprod.desc
          (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
            (singularIntegralCoefficients : AddCommGrpCat.{w})).map (LoopCellAttachment.inclusion X x P))
          (sphericalHomologyTwoSection X x P) := by
  constructor
  · let j := Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{w})) p
    let s := sphericalHomologyTwoSection X x P
    let e := sphericalHomologyTwoSplitIso X x P
    apply (cancel_mono e.hom).mp
    have hSection : (j ≫ s) ≫ e.hom = j ≫ biprod.inr :=
      (Category.assoc j s e.hom).trans
        (congrArg (fun f => j ≫ f) (sphericalHomologyTwoSection_splitIso X x P))
    exact hSection.trans (sphericalGenerator_homologyTwoCoordinate X x P p).symm
  · exact sphericalHomologyTwoSplitIso_inv X x P

/-- The two same-sphere coordinates reconstruct the entire absolute homology group. -/
theorem client_same_sphere_split_full_decomposition (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    sphericalHomologyTwoRetraction X x P ≫
        (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{w})).map (LoopCellAttachment.inclusion X x P)) +
      LoopCellAttachment.homologyTwoProjection X x P ≫ sphericalHomologyTwoSection X x P = 𝟙 _ :=
  sphericalHomologyTwo_decomposition X x P

set_option linter.unusedVariables false in
/-- The full original connected classical CW scope obtains sphere maps and
one coherent absolute splitting, without a supplied section or spherical lift. -/
theorem client_same_sphere_split_connected_CW (X : TopCat.{w}) [T2Space X]
    [ConnectedSpace X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    ∃ (h : ∀ p : P, (classicalCellDiskPair.{w} 3).snd ⟶ LoopCellAttachment.space X x P)
      (e : (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{w})).obj (LoopCellAttachment.space X x P)) ≅
          (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
            (singularIntegralCoefficients : AddCommGrpCat.{w})).obj X) ⊞
              LoopCellAttachment.homologyTwoCells X x P),
      (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{w})).map (LoopCellAttachment.inclusion X x P)) ≫
          e.hom = biprod.inl ∧
      e.hom ≫ biprod.snd = LoopCellAttachment.homologyTwoProjection X x P ∧
      ∀ p : P, classicalCellBoundaryHomologyTwoGenerator.{w} ≫
        (((singularHomologyFunctor AddCommGrpCat.{w} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{w})).map (h p)) ≫ e.hom =
        Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{w})) p ≫ biprod.inr :=
  exists_sphericalGenerators_with_homologyTwoSplit_of_connectedCW X x P

#check @AlgebraicTopology.LoopCellSphericalGenerators.diskBoundaryArrowIso_eq
#print axioms AlgebraicTopology.LoopCellSphericalGenerators.diskBoundaryArrowIso_eq

/-- The previously returned sphere Arrow API has exactly the same neutral
right component and original classical parameter at every point. -/
theorem client_shared_neutral_sphere_disk_parameter (n : ℕ)
    (z : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (AlgebraicTopology.LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} n).hom.right z =
      ULift.up (SSet.stdSimplex.toClassicalDiskHomeomorph.{u} n z) := by
  have h := congrArg
    (fun e : Arrow.mk (SSet.toTop.map (SSet.boundary.{u} n).ι) ≅
        Arrow.mk (classicalCellDiskPair.{u} n).map => e.hom.right z)
    (AlgebraicTopology.LoopCellSphericalGenerators.diskBoundaryArrowIso_eq.{u} n)
  exact h.trans (SSet.boundary.toClassicalCellDiskArrowIso_hom_right_apply n z)

end
