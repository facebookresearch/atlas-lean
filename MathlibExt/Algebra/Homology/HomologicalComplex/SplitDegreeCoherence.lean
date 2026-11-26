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
# Projectors in the three coordinates of a split degree

For a splitting, the boundary, homology and outgoing coordinate
projection–inclusion composites are respectively the normalized incoming
projector, complementary projector and outgoing projector. Their sum is
the identity. The complementary projector is the homology diagonal in
the degree decomposition and is preserved by additive functors under
the stated local homology hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/--
Let K be a c-complex in a preadditive category C, s a splitting, and i a degree with homology.
The complementary normalized projector in degree i equals rᵢ≫πᵢ≫ℓᵢ, where rᵢ:Kᵢ→Zᵢ is the
cycles retraction, πᵢ:Zᵢ→Hᵢ the quotient and ℓᵢ:Hᵢ→Kᵢ the normalized homology inclusion.
-/
lemma normalizedHomologyProjector_f_eq_pointwise (s : Splitting K) (i : ι)
    [K.HasHomology i] :
    s.normalizedHomologyProjector.f i =
      s.cyclesRetraction i ≫ K.homologyπ i ≫ s.homologyInclusionComponent i :=
  (s.pointwiseHomologyProjectionInclusion i).symm

section DegreeCoordinates

variable (s : Splitting K) (i : ι) [K.HasHomology i]
  [HasKernel (K.homologyπ i)] [HasCokernel (K.iCycles i)]

/--
Let K be a c-complex in a preadditive category C, s a splitting, and i a degree with homology.
Assume ker(πᵢ)=Bᵢ and coker(jᵢ)=Qᵢ exist, where jᵢ:Zᵢ→Kᵢ is the cycle inclusion. Let
e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Qᵢ be the canonical decomposition furnished by s. Projecting to Bᵢ by e and
including it back by e^{-1} gives prevD i s.normalize.hom, the normalized incoming-boundary
projector.
-/
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

/--
Let K be a c-complex in a preadditive category C, s a splitting, and i a degree with homology.
Assume ker(πᵢ)=Bᵢ and coker(jᵢ)=Qᵢ exist, where jᵢ:Zᵢ→Kᵢ is the cycle inclusion. Let
e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Qᵢ be the canonical decomposition furnished by s. Projection to Hᵢ followed by
its inverse-coordinate inclusion is the degree-i complementary projector
s.normalizedHomologyProjector.f i.
-/
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

/--
Let K be a c-complex in a preadditive category C, s a splitting, and i a degree with homology.
Assume ker(πᵢ)=Bᵢ and coker(jᵢ)=Qᵢ exist, where jᵢ:Zᵢ→Kᵢ is the cycle inclusion. Let
e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Qᵢ be the canonical decomposition furnished by s. Projection to Qᵢ followed by
its inverse-coordinate inclusion gives dNext i s.normalize.hom, the normalized outgoing
projector.
-/
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

/--
Let K be a c-complex in a preadditive category C, s a splitting, and i a degree with homology.
Assume ker(πᵢ)=Bᵢ and coker(jᵢ)=Qᵢ exist, where jᵢ:Zᵢ→Kᵢ is the cycle inclusion. Let
e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Qᵢ be the canonical decomposition furnished by s. The sum of the three coordinate
projection–inclusion endomorphisms of Kᵢ is 1_{Kᵢ}. Thus the boundary, homology and outgoing
coordinates reconstruct every term.
-/
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

/--
Let K be a c-complex in a preadditive category C, s a splitting, and i a degree with homology.
Assume ker(πᵢ)=Bᵢ and coker(jᵢ)=Qᵢ exist, where jᵢ:Zᵢ→Kᵢ is the cycle inclusion. Let
e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Qᵢ be the canonical decomposition furnished by s. Conjugating the normalized
complementary projector by e gives the diagonal projection onto Hᵢ in (Bᵢ⊞Hᵢ)⊞Qᵢ: it is
identity on Hᵢ and zero on the boundary and outgoing coordinates.
-/
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

/--
Let C,D be preadditive categories, K a c-complex with splitting s, and F:C⥤D additive. Fix i
with homology in K and assume F preserves both left and right homology of
Sᵢ=(K_prev(i)→Kᵢ→K_next(i)). Then F(rᵢ≫πᵢ≫ℓᵢ) equals the homology-coordinate projector of the
mapped splitting s.map F.
-/
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
