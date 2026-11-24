/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitDegree
public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesImage

/-!
# Actual incoming and outgoing image specialization of split degree decomposition

The general pointwise kernel/cokernel core needs no abelian structure. This
separate specialization uses the existing abelian image/cycle/homology
sequences and their universal properties. It retains the original native
image objects and normalized inverse maps, with no image-projectivity or
supplied degree-decomposition premise.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i : ι)

/-- The actual incoming image is the kernel of the original native homology quotient. -/
def incomingImageKernelIso :
    Abelian.image (K.d (c.prev i) i) ≅ kernel (K.homologyπ i) := by
  let e :=
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).fIsKernel.conePointUniqueUpToIso
      (kernelIsKernel (K.homologyπ i))
  exact e

/-- The incoming image/kernel comparison preserves the original boundary-to-cycles map. -/
@[reassoc]
theorem incomingImageKernelIso_hom_ι :
    (incomingImageKernelIso K i).hom ≫ kernel.ι (K.homologyπ i) =
      boundaryCyclesMap K (c.prev i) i := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).fIsKernel
    (kernelIsKernel (K.homologyπ i)) WalkingParallelPair.zero

/-- The actual outgoing image is the cokernel of the original cycles inclusion. -/
def outgoingImageCokernelIso :
    Abelian.image (K.d i (c.next i)) ≅ cokernel (K.iCycles i) := by
  let e := (cyclesImageSequence_shortExact K i (c.next i) rfl).gIsCokernel.coconePointUniqueUpToIso
    (cokernelIsCokernel (K.iCycles i))
  exact e

/-- The outgoing image/cokernel comparison retains the original differential's image projection. -/
@[reassoc]
theorem outgoingImageCokernelIso_π_hom :
    Abelian.factorThruImage (K.d i (c.next i)) ≫ (outgoingImageCokernelIso K i).hom =
      cokernel.π (K.iCycles i) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cyclesImageSequence_shortExact K i (c.next i) rfl).gIsCokernel
    (cokernelIsCokernel (K.iCycles i)) WalkingParallelPair.one

variable {K}

/-- The actual outgoing-image sequence splits by the normalized cycle retraction. -/
def Splitting.outgoingImageSequenceSplitting (s : Splitting K) (i : ι) :
    (cyclesImageSequence K i (c.next i)).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    (cyclesImageSequence_shortExact K i (c.next i) rfl).exact
    (s.cyclesRetraction i) (s.iCycles_cyclesRetraction i)
    (cyclesImageSequence_shortExact K i (c.next i) rfl).epi_g

/-- Its retraction is exactly the normalized cycle retraction, not a projective choice. -/
@[simp]
theorem Splitting.outgoingImageSequenceSplitting_r (s : Splitting K) (i : ι) :
    (s.outgoingImageSequenceSplitting i).r = s.cyclesRetraction i := rfl

/-- The native identity law determines the actual outgoing-image section. -/
@[reassoc]
theorem Splitting.outgoingImageSequenceSplitting_g_s (s : Splitting K) (i : ι) :
    Abelian.factorThruImage (K.d i (c.next i)) ≫ (s.outgoingImageSequenceSplitting i).s =
      𝟙 (K.X i) - s.cyclesRetraction i ≫ K.iCycles i :=
  (s.outgoingImageSequenceSplitting i).g_s

/-- The actual incoming-image sequence splits by the earned native homology section. -/
def Splitting.incomingImageSequenceSplitting (s : Splitting K) (i : ι) :
    (boundariesCyclesHomologySequence K (c.prev i) i).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).exact
    (s.homologyCycleSection i) (s.homologyCycleSection_homologyπ i)
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).mono_f

/-- Its section is the actual homology inclusion followed by the normalized cycle retraction. -/
@[simp]
theorem Splitting.incomingImageSequenceSplitting_s (s : Splitting K) (i : ι) :
    (s.incomingImageSequenceSplitting i).s = s.homologyCycleSection i := rfl

/-- The native identity law fixes the original incoming boundary projection. -/
@[reassoc]
theorem Splitting.incomingImageSequenceSplitting_r_f (s : Splitting K) (i : ι) :
    (s.incomingImageSequenceSplitting i).r ≫ boundaryCyclesMap K (c.prev i) i =
      𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i :=
  (s.incomingImageSequenceSplitting i).r_f

/-- The actual term decomposes into incoming image, original homology and outgoing image. -/
def Splitting.imageDegreeDecompositionIso (s : Splitting K) (i : ι) :
    K.X i ≅ (Abelian.image (K.d (c.prev i) i) ⊞ K.homology i) ⊞
      Abelian.image (K.d i (c.next i)) :=
  s.degreeDecompositionIso i ≪≫
    biprod.mapIso
      (biprod.mapIso (incomingImageKernelIso K i).symm (Iso.refl (K.homology i)))
      (outgoingImageCokernelIso K i).symm

/-- The incoming-image coordinate agrees with the original boundary-kernel coordinate. -/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_hom_boundary (s : Splitting K) (i : ι) :
    (s.imageDegreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.fst ≫
        (incomingImageKernelIso K i).hom =
      s.cyclesRetraction i ≫ s.boundaryKernelProjection i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id,
    degreeDecompositionIso_hom_boundary]

/-- The homology coordinate retains the original normalized cycle quotient. -/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_hom_homology (s : Splitting K) (i : ι) :
    (s.imageDegreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.snd =
      s.cyclesRetraction i ≫ K.homologyπ i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, biprod.map_snd, Iso.refl_hom, Category.comp_id,
    degreeDecompositionIso_hom_homology]

/-- The outgoing-image coordinate is the same native outgoing cokernel coordinate. -/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_hom_outgoing (s : Splitting K) (i : ι) :
    (s.imageDegreeDecompositionIso i).hom ≫ biprod.snd ≫
        (outgoingImageCokernelIso K i).hom = cokernel.π (K.iCycles i) := by
  simp only [imageDegreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_snd_assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id,
    degreeDecompositionIso_hom_outgoing]

/-- The incoming summand uses the actual image inclusion in the original term. -/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_boundary_inv (s : Splitting K) (i : ι) :
    biprod.inl ≫ biprod.inl ≫ (s.imageDegreeDecompositionIso i).inv =
      Abelian.image.ι (K.d (c.prev i) i) := by
  simp only [imageDegreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    Category.assoc, biprod.inl_map_assoc, Iso.symm_inv, degreeDecompositionIso_boundary_inv,
    incomingImageKernelIso_hom_ι_assoc, boundaryCyclesMap_i]

/-- The middle summand includes by the original earned homology inclusion. -/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_homology_inv (s : Splitting K) (i : ι) :
    biprod.inr ≫ biprod.inl ≫ (s.imageDegreeDecompositionIso i).inv =
      s.homologyInclusionComponent i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    Category.assoc, biprod.inl_map_assoc, biprod.inr_map_assoc, Iso.refl_inv, Category.id_comp,
    degreeDecompositionIso_homology_inv]

/-- The outgoing summand includes by the actual earned cokernel section. -/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_outgoing_inv (s : Splitting K) (i : ι) :
    biprod.inr ≫ (s.imageDegreeDecompositionIso i).inv =
      (outgoingImageCokernelIso K i).hom ≫ s.outgoingCokernelSection i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    Category.assoc, biprod.inr_map_assoc, Iso.symm_inv, degreeDecompositionIso_outgoing_inv]

end HomologicalComplex
