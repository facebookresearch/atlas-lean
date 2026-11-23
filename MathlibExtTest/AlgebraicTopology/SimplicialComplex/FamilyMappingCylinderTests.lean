/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialComplex.FamilyMappingCylinder

noncomputable section
set_option autoImplicit false

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped Classical unitInterval

universe u v w

#check PreAbstractSimplicialComplex.MappingCylinder.FamilyAttachmentData
#print axioms PreAbstractSimplicialComplex.MappingCylinder.FamilyAttachmentData
#check PreAbstractSimplicialComplex.MappingCylinder.familyAttachments
#print axioms PreAbstractSimplicialComplex.MappingCylinder.familyAttachments

namespace FamilyMappingCylinderTests

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)
variable (f : ∀ i, Morphism (P i) Q) (hfinite : ∀ i, Finite (Face (P i)))

-- The old target retains every original coefficient, and ALL its points are fixed throughout.
example (x : Q.Realization) (t : unitInterval) :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    (d.old x).point = x.point.map (Sum.inr : W → (Σ i, Face (P i)) ⊕ W) ∧
      d.retraction (d.old x) = x ∧ d.deformation (t, d.old x) = d.old x := by
  let d := MappingCylinder.familyAttachments P Q f hfinite
  exact ⟨d.old_point x, d.retraction_old x, d.deformation_fixed t x⟩

-- The terminal copied-domain map is the actual given simplicial map, including folding.
example (i : «I») (x : (barycentricSubdivision (P i)).Realization) :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    d.retraction (d.copied i x) = (f i).realization (barycentricHomeomorph (P i) x) := by
  exact (MappingCylinder.familyAttachments P Q f hfinite).retraction_copied i x

-- Compatibility is read from the ACTUAL original cylinder pushout and its literal source maps.
example (i : «I») (x : Q.Realization) :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    d.block i ((MappingCylinder.targetMorphism (f i)).realization x) = d.old x := by
  let d := MappingCylinder.familyAttachments P Q f hfinite
  have h := ConcreteCategory.congr_hom d.cylinder_pushout.w
    (⟨i, ULift.up x⟩ : Σ i, ULift.{max u v w} Q.Realization)
  change d.blocksMap (d.overlapMap ⟨i, ULift.up x⟩) = d.oldMap (d.overlapFold ⟨i, ULift.up x⟩) at h
  rw [d.overlapMap_apply, d.overlapFold_apply, d.blocksMap_apply, d.oldMap_apply] at h
  exact h

-- The ordinary cone base glues to the ENTIRE actual copied domain by the second pushout.
example (i : «I») (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    d.ordinaryCones ⟨i, TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) x⟩ =
      d.cylinderCone (d.domainsCylinder ⟨i, x⟩) := by
  let d := MappingCylinder.familyAttachments P Q f hfinite
  have h := ConcreteCategory.congr_hom d.cone_pushout.w ⟨i, x⟩
  change d.cylinderCone (d.domainsCylinder ⟨i, x⟩) = d.ordinaryCones (d.domainsCones ⟨i, x⟩) at h
  rw [d.domainsCones_apply] at h
  exact h.symm

-- Distinct copied domains and distinct ordinary cones remain disjoint across an arbitrary family.
example (i j : «I») (hij : i ≠ j) :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    Disjoint (Set.range (d.copied i)) (Set.range (d.copied j)) ∧
      Disjoint (Set.range (fun x => d.ordinaryCones ⟨i, x⟩))
        (Set.range (fun x => d.ordinaryCones ⟨j, x⟩)) := by
  let d := MappingCylinder.familyAttachments P Q f hfinite
  exact ⟨d.copied_disjoint i j hij, d.cones_disjoint i j hij⟩

-- Both whole curried endpoints are on the ORIGINAL family space and use its constructed retraction.
example :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    d.deformation.toHomotopy.curry 0 = ContinuousMap.id d.cylinder.Realization ∧
      d.deformation.toHomotopy.curry 1 = d.old.comp d.retraction := by
  let d := MappingCylinder.familyAttachments P Q f hfinite
  exact ⟨d.deformation.toHomotopy.curry_zero, d.deformation.toHomotopy.curry_one⟩

-- The image intersection is exactly the original copied domain, not just its boundary or corners.
example (i : «I») :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    Set.range (fun x => d.ordinaryCones ⟨i, x⟩) ∩ Set.range d.cylinderCone =
      Set.range (fun x : (MappingCylinder.domainComplex (P i) W).Realization =>
        d.cylinderCone (d.domainsCylinder ⟨i, x⟩)) := by
  exact (MappingCylinder.familyAttachments P Q f hfinite).cone_cylinder_intersection i

-- An empty index leaves the old weak target, with no new apex or copied-domain face.
example [IsEmpty «I»] :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    d.cylinder = Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W) ∧
      d.cone = (Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W)).map Function.Embedding.inl := by
  exact (MappingCylinder.familyAttachments P Q f hfinite).empty_family inferInstance

-- Each fresh apex is literal even when that finite domain has no vertex.
example (i : «I») :
    let d := MappingCylinder.familyAttachments P Q f hfinite
    (d.ordinaryCones
      ⟨i, TopCat.conePoint (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) PUnit.unit⟩).point =
        Convexity.StdSimplex.single (Sum.inr i : ((Σ i, Face (P i)) ⊕ W) ⊕ «I») := by
  exact (MappingCylinder.familyAttachments P Q f hfinite).apex_point i

end FamilyMappingCylinderTests
