/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.TopCat.HurewiczTwo

noncomputable section

open CategoryTheory AlgebraicTopology Topology

universe u v

#check Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator
#print axioms Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator
#check Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator_eq_original_boundary
#print axioms Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator_eq_original_boundary
#check Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator_isIso
#print axioms Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator_isIso
#check TopCat.classicalSphereHomologyTwoRepresentative
#print axioms TopCat.classicalSphereHomologyTwoRepresentative
#check TopCat.classicalSphereHomologyTwoRepresentative_homology
#print axioms TopCat.classicalSphereHomologyTwoRepresentative_homology
#check TopCat.classicalSphereHomologyTwoRepresentative_value
#print axioms TopCat.classicalSphereHomologyTwoRepresentative_value
#check TopCat.exists_classicalSphereHomologyTwo_representative
#print axioms TopCat.exists_classicalSphereHomologyTwo_representative

namespace HurewiczTwoDirectClients

variable (Y W : TopCat.{max u v}) (y : Y)
variable [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]

/-- The same chosen map takes the ACTUAL original relative3-disk boundary
to the specified homology class, at every integral coefficient. -/
example
    (z : (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{max u v})).obj Y))
    (a : (singularIntegralCoefficients : AddCommGrpCat.{max u v})) :
    ((Topology.CWComplex.classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{max u v, max u v}
        (singularIntegralCoefficients : AddCommGrpCat.{max u v}) 3).hom ≫
      ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{max u v}
        (singularIntegralCoefficients : AddCommGrpCat.{max u v}) 3).app
          (Topology.CWComplex.classicalCellDiskPair.{max u v} 3)).inv ≫
      (singularHomologyIntData AddCommGrpCat.{max u v}
        (singularIntegralCoefficients : AddCommGrpCat.{max u v})).boundary 3
          (Topology.CWComplex.classicalCellDiskPair.{max u v} 3) ≫
      ((singularHomologyNatToIntIso AddCommGrpCat.{max u v}
        (singularIntegralCoefficients : AddCommGrpCat.{max u v}) 2).app
          (Topology.CWComplex.classicalCellDiskPair.{max u v} 3).snd).hom ≫
      (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{max u v})).map
          (TopCat.classicalSphereHomologyTwoRepresentative Y y z))) a = a.down • z := by
  have h := TopCat.classicalSphereHomologyTwoRepresentative_homology Y y z a
  rw [Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator_eq_original_boundary] at h
  exact h

/-- An arbitrary homology morphism out of the actual integral coefficient
is induced by an actual sphere map; the equality is the whole morphism. -/
example
    (g : (singularIntegralCoefficients : AddCommGrpCat.{max u v}) ⟶
      (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{max u v})).obj Y)) :
    ∃ f : (Topology.CWComplex.classicalCellDiskPair.{max u v} 3).snd ⟶ Y,
      Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{max u v} ≫
        (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{max u v})).map f) = g := by
  let f := TopCat.classicalSphereHomologyTwoRepresentative Y y (g (ULift.up (1 : ℤ)))
  refine ⟨f, ?_⟩
  apply AddCommGrpCat.ext
  intro a
  have h := TopCat.classicalSphereHomologyTwoRepresentative_homology
    Y y (g (ULift.up (1 : ℤ))) a
  have ha : a = a.down •
      (ULift.up (1 : ℤ) : (singularIntegralCoefficients : AddCommGrpCat.{max u v})) := by
    apply ULift.down_injective
    simp
  have hg : g.hom a = a.down • g.hom (ULift.up (1 : ℤ)) := by
    calc
      g.hom a = g.hom (a.down • ULift.up (1 : ℤ)) := congrArg g.hom ha
      _ = a.down • g.hom (ULift.up (1 : ℤ)) := by rw [map_zsmul]
  exact h.trans hg.symm

/-- A map out of the simply connected source pushes the constructed sphere
to ANY ordinary target W. No connectedness or fundamental-group premise on W
is used, as required when pushing a sphere down from a cover. -/
example (p : Y ⟶ W)
    (z : (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{max u v})).obj Y)) :
    (Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{max u v} ≫
      (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{max u v})).map
          (TopCat.classicalSphereHomologyTwoRepresentative Y y z ≫ p)))
      (ULift.up (1 : ℤ)) =
    (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{max u v})).map p) z := by
  let H : TopCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
    (singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{max u v})
  change (Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator ≫
    H.map (TopCat.classicalSphereHomologyTwoRepresentative Y y z ≫ p))
      (ULift.up (1 : ℤ)) = H.map p z
  rw [H.map_comp]
  change H.map p
      ((Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator ≫
        H.map (TopCat.classicalSphereHomologyTwoRepresentative Y y z))
          (ULift.up (1 : ℤ))) = H.map p z
  rw [TopCat.classicalSphereHomologyTwoRepresentative_value]

/-- The original boundary generator has both actual strict inverse laws. -/
example :
    ∃ i :
      (((singularHomologyFunctor AddCommGrpCat.{max u v} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{max u v})).obj
          (Topology.CWComplex.classicalCellDiskPair.{max u v} 3).snd) ⟶
        (singularIntegralCoefficients : AddCommGrpCat.{max u v}),
      Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator ≫ i = 𝟙 _ ∧
        i ≫ Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator = 𝟙 _ := by
  have : IsIso Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{max u v} :=
    Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator_isIso
  let e := asIso Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{max u v}
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

end HurewiczTwoDirectClients

end
