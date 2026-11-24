/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitDegree
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingProjection
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitExactFunctor

/-!
# Coherence of degree decompositions

The selected kernel and cokernel universal properties construct the
degreewise biproducts. Their coordinate maps give three orthogonal
projectors whose sum is the identity. The homology coordinate agrees with
the normalized homology projector. These comparisons are pointwise and
require no global homology or biproduct structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- The general normalized projector is the actual native pointwise homology coordinate. -/
lemma normalizedHomologyProjector_f_eq_pointwise (s : Splitting K) (i : ι)
    [K.HasHomology i] :
    s.normalizedHomologyProjector.f i =
      s.cyclesRetraction i ≫ K.homologyπ i ≫ s.homologyInclusionComponent i :=
  (s.pointwiseHomologyProjectionInclusion i).symm

section DegreeCoordinates

variable (s : Splitting K) (i : ι) [K.HasHomology i]
  [HasKernel (K.homologyπ i)] [HasCokernel (K.iCycles i)]

/-- The actual incoming coordinate projection/inclusion gives the native incoming projector. -/
lemma degreeDecompositionIso_boundary_projector :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    ((s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.fst) ≫
        (biprod.inl ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv) =
      prevD i s.normalize.hom := by
  letI := s.hasBoundaryHomologyBiproduct i
  letI := s.hasDegreeDecompositionBiproduct i
  rw [s.degreeDecompositionIso_hom_boundary i, s.degreeDecompositionIso_boundary_inv i]
  simpa only [Category.assoc] using s.boundaryKernelProjection_term i

/-- The actual homology coordinate projection/inclusion gives the general normalized projector. -/
lemma degreeDecompositionIso_homology_projector :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    ((s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.snd) ≫
        (biprod.inr ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv) =
      s.normalizedHomologyProjector.f i := by
  letI := s.hasBoundaryHomologyBiproduct i
  letI := s.hasDegreeDecompositionBiproduct i
  rw [s.degreeDecompositionIso_hom_homology i, s.degreeDecompositionIso_homology_inv i]
  simpa only [Category.assoc] using (s.normalizedHomologyProjector_f_eq_pointwise i).symm

/-- The actual outgoing coordinate projection/inclusion gives the native outgoing projector. -/
lemma degreeDecompositionIso_outgoing_projector :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    ((s.degreeDecompositionIso i).hom ≫ biprod.snd) ≫
        (biprod.inr ≫ (s.degreeDecompositionIso i).inv) =
      dNext i s.normalize.hom := by
  letI := s.hasBoundaryHomologyBiproduct i
  letI := s.hasDegreeDecompositionBiproduct i
  rw [s.degreeDecompositionIso_hom_outgoing i, s.degreeDecompositionIso_outgoing_inv i]
  exact s.outgoingCokernelProjectionSection i

/-- The three actual native coordinate projectors reconstruct the original term identity. -/
lemma degreeDecompositionIso_coordinate_identity :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (((s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.fst) ≫
        (biprod.inl ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv)) +
      (((s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.snd) ≫
        (biprod.inr ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv)) +
      (((s.degreeDecompositionIso i).hom ≫ biprod.snd) ≫
        (biprod.inr ≫ (s.degreeDecompositionIso i).inv)) = 𝟙 (K.X i) := by
  letI := s.hasBoundaryHomologyBiproduct i
  letI := s.hasDegreeDecompositionBiproduct i
  rw [s.degreeDecompositionIso_boundary_projector i, s.degreeDecompositionIso_homology_projector i,
    s.degreeDecompositionIso_outgoing_projector i, normalizedHomologyProjector_f]
  abel

/-- In the earned native coordinates, the general projector is precisely the homology diagonal. -/
lemma degreeDecompositionIso_normalizedHomologyProjector :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (s.degreeDecompositionIso i).inv ≫ s.normalizedHomologyProjector.f i ≫
        (s.degreeDecompositionIso i).hom =
      biprod.fst ≫ biprod.snd ≫ biprod.inr ≫ biprod.inl := by
  letI := s.hasBoundaryHomologyBiproduct i
  letI := s.hasDegreeDecompositionBiproduct i
  rw [← s.degreeDecompositionIso_homology_projector i]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end DegreeCoordinates

variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- Actual native pointwise homology-coordinate projectors commute with an additive base functor. -/
lemma pointwiseHomologyProjectionInclusion_map (s : Splitting K) (F : C ⥤ D) [F.Additive]
    (i : ι) [K.HasHomology i]
    [F.PreservesLeftHomologyOf (K.sc i)] [F.PreservesRightHomologyOf (K.sc i)] :
    letI := hasHomology_map_of_preservesHomologyOf K F i
    F.map (s.cyclesRetraction i ≫ K.homologyπ i ≫ s.homologyInclusionComponent i) =
      (s.map F).cyclesRetraction i ≫
        ((F.mapHomologicalComplex c).obj K).homologyπ i ≫
          (s.map F).homologyInclusionComponent i := by
  letI := hasHomology_map_of_preservesHomologyOf K F i
  rw [← s.normalizedHomologyProjector_f_eq_pointwise i,
    ← (s.map F).normalizedHomologyProjector_f_eq_pointwise i]
  exact congrArg (fun f : (F.mapHomologicalComplex c).obj K ⟶
      (F.mapHomologicalComplex c).obj K => f.f i) (s.normalizedHomologyProjector_map F)

end HomologicalComplex.Splitting
