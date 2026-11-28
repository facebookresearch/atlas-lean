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
# Degree decomposition by incoming and outgoing images

For a complex in an abelian category, the incoming differential image is
the kernel of the cycles-to-homology quotient, and the outgoing image is
the cokernel of the cycles inclusion.

A splitting therefore gives K_i≅(im d_prev(i),i ⊞ H_i)⊞im d_i,next(i),
with coordinates and inclusions identified with the original image maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i : ι)

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). The incoming image Bᵢ
is canonically isomorphic to ker πᵢ, identifying boundaries inside the cycles.
-/
def incomingImageKernelIso :
    Abelian.image (K.d (c.prev i) i) ≅ kernel (K.homologyπ i) := by
  let e :=
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).fIsKernel.conePointUniqueUpToIso
      (kernelIsKernel (K.homologyπ i))
  exact e

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). For αᵢ:Bᵢ≅ker πᵢ,
αᵢ.hom followed by the kernel inclusion is the original boundary-to-cycles map Bᵢ→Zᵢ.
-/
@[reassoc]
theorem incomingImageKernelIso_hom_ι :
    (incomingImageKernelIso K i).hom ≫ kernel.ι (K.homologyπ i) =
      boundaryCyclesMap K (c.prev i) i := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).fIsKernel
    (kernelIsKernel (K.homologyπ i)) WalkingParallelPair.zero

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). The outgoing image Iᵢ
is canonically isomorphic to coker jᵢ, identifying the quotient of a term by its cycles.
-/
def outgoingImageCokernelIso :
    Abelian.image (K.d i (c.next i)) ≅ cokernel (K.iCycles i) := by
  let e := (cyclesImageSequence_shortExact K i (c.next i) rfl).gIsCokernel.coconePointUniqueUpToIso
    (cokernelIsCokernel (K.iCycles i))
  exact e

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). For βᵢ:Iᵢ≅coker jᵢ,
the differential's factor Pᵢ:Kᵢ→Iᵢ satisfies Pᵢ≫βᵢ.hom=cokernel.π(jᵢ).
-/
@[reassoc]
theorem outgoingImageCokernelIso_π_hom :
    Abelian.factorThruImage (K.d i (c.next i)) ≫ (outgoingImageCokernelIso K i).hom =
      cokernel.π (K.iCycles i) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cyclesImageSequence_shortExact K i (c.next i) rfl).gIsCokernel
    (cokernelIsCokernel (K.iCycles i)) WalkingParallelPair.one

variable {K}

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The short exact sequence 0→Zᵢ→Kᵢ→Iᵢ→0 splits using the
normalized cycles retraction rᵢ:Kᵢ→Zᵢ supplied by s.
-/
def Splitting.outgoingImageSequenceSplitting (s : Splitting K) (i : ι) :
    (cyclesImageSequence K i (c.next i)).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    (cyclesImageSequence_shortExact K i (c.next i) rfl).exact
    (s.cyclesRetraction i) (s.iCycles_cyclesRetraction i)
    (cyclesImageSequence_shortExact K i (c.next i) rfl).epi_g

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The retraction in the splitting of 0→Zᵢ→Kᵢ→Iᵢ→0 is exactly
s.cyclesRetraction i.
-/
@[simp]
theorem Splitting.outgoingImageSequenceSplitting_r (s : Splitting K) (i : ι) :
    (s.outgoingImageSequenceSplitting i).r = s.cyclesRetraction i := rfl

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. Let rᵢ:Kᵢ→Zᵢ be the normalized retraction and uᵢ:Iᵢ→Kᵢ the
outgoing-image section. The image projection Pᵢ:Kᵢ→Iᵢ satisfies Pᵢ≫uᵢ=1_{Kᵢ}−rᵢ≫jᵢ.
-/
@[reassoc]
theorem Splitting.outgoingImageSequenceSplitting_g_s (s : Splitting K) (i : ι) :
    Abelian.factorThruImage (K.d i (c.next i)) ≫ (s.outgoingImageSequenceSplitting i).s =
      𝟙 (K.X i) - s.cyclesRetraction i ≫ K.iCycles i :=
  (s.outgoingImageSequenceSplitting i).g_s

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The short exact sequence 0→Bᵢ→Zᵢ→Hᵢ→0 splits using the
canonical homology-to-cycles section tᵢ:Hᵢ→Zᵢ furnished by s.
-/
def Splitting.incomingImageSequenceSplitting (s : Splitting K) (i : ι) :
    (boundariesCyclesHomologySequence K (c.prev i) i).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).exact
    (s.homologyCycleSection i) (s.homologyCycleSection_homologyπ i)
    (boundariesCyclesHomologySequence_shortExact K (c.prev i) i rfl).mono_f

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The section in the splitting of 0→Bᵢ→Zᵢ→Hᵢ→0 is exactly
tᵢ=s.homologyCycleSection i.
-/
@[simp]
theorem Splitting.incomingImageSequenceSplitting_s (s : Splitting K) (i : ι) :
    (s.incomingImageSequenceSplitting i).s = s.homologyCycleSection i := rfl

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. If bᵢ:Zᵢ→Bᵢ is the incoming-image retraction, kᵢ:Bᵢ→Zᵢ the
boundary-to-cycles map and tᵢ the homology section, then bᵢ≫kᵢ=1_{Zᵢ}−πᵢ≫tᵢ.
-/
@[reassoc]
theorem Splitting.incomingImageSequenceSplitting_r_f (s : Splitting K) (i : ι) :
    (s.incomingImageSequenceSplitting i).r ≫ boundaryCyclesMap K (c.prev i) i =
      𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i :=
  (s.incomingImageSequenceSplitting i).r_f

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The two split short exact sequences yield Kᵢ≅(Bᵢ⊞Hᵢ)⊞Iᵢ.
The boundary coordinate corresponds to the boundary kernel, the homology coordinate is the
normalized cycles retraction followed by πᵢ, and the outgoing coordinate corresponds to coker
jᵢ.
-/
def Splitting.imageDegreeDecompositionIso (s : Splitting K) (i : ι) :
    K.X i ≅ (Abelian.image (K.d (c.prev i) i) ⊞ K.homology i) ⊞
      Abelian.image (K.d i (c.next i)) :=
  s.degreeDecompositionIso i ≪≫
    biprod.mapIso
      (biprod.mapIso (incomingImageKernelIso K i).symm (Iso.refl (K.homology i)))
      (outgoingImageCokernelIso K i).symm

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. For the image decomposition e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Iᵢ and αᵢ:Bᵢ≅ker
πᵢ, its boundary coordinate satisfies e.hom≫fst≫fst≫αᵢ.hom=s.cyclesRetraction
i≫s.boundaryKernelProjection i.
-/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_hom_boundary (s : Splitting K) (i : ι) :
    (s.imageDegreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.fst ≫
        (incomingImageKernelIso K i).hom =
      s.cyclesRetraction i ≫ s.boundaryKernelProjection i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id,
    degreeDecompositionIso_hom_boundary]

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. For e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Iᵢ, the homology coordinate is
e.hom≫fst≫snd=s.cyclesRetraction i≫πᵢ.
-/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_hom_homology (s : Splitting K) (i : ι) :
    (s.imageDegreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.snd =
      s.cyclesRetraction i ≫ K.homologyπ i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, biprod.map_snd, Iso.refl_hom, Category.comp_id,
    degreeDecompositionIso_hom_homology]

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. For e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Iᵢ and βᵢ:Iᵢ≅coker jᵢ, the outgoing
coordinate satisfies e.hom≫snd≫βᵢ.hom=cokernel.π(jᵢ).
-/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_hom_outgoing (s : Splitting K) (i : ι) :
    (s.imageDegreeDecompositionIso i).hom ≫ biprod.snd ≫
        (outgoingImageCokernelIso K i).hom = cokernel.π (K.iCycles i) := by
  simp only [imageDegreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_snd_assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id,
    degreeDecompositionIso_hom_outgoing]

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The inverse of e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Iᵢ restricted to Bᵢ is the
original image inclusion im(d_prev(i),i)→Kᵢ.
-/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_boundary_inv (s : Splitting K) (i : ι) :
    biprod.inl ≫ biprod.inl ≫ (s.imageDegreeDecompositionIso i).inv =
      Abelian.image.ι (K.d (c.prev i) i) := by
  simp only [imageDegreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    Category.assoc, biprod.inl_map_assoc, Iso.symm_inv, degreeDecompositionIso_boundary_inv,
    incomingImageKernelIso_hom_ι_assoc, boundaryCyclesMap_i]

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The inverse of e:Kᵢ≅(Bᵢ⊞Hᵢ)⊞Iᵢ restricted to Hᵢ is the
homology inclusion s.homologyInclusionComponent i:Hᵢ→Kᵢ.
-/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_homology_inv (s : Splitting K) (i : ι) :
    biprod.inr ≫ biprod.inl ≫ (s.imageDegreeDecompositionIso i).inv =
      s.homologyInclusionComponent i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    Category.assoc, biprod.inl_map_assoc, biprod.inr_map_assoc, Iso.refl_inv, Category.id_comp,
    degreeDecompositionIso_homology_inv]

/--
Let K be a complex of shape c in an abelian category C and fix i. Write Zᵢ,Hᵢ for cycles and
homology, jᵢ:Zᵢ→Kᵢ, πᵢ:Zᵢ→Hᵢ, Bᵢ=im(d_prev(i),i) and Iᵢ=im(dᵢ,next(i)). Let s be a
generalized-inverse splitting of K. The inverse restricted to Iᵢ is
βᵢ.hom≫s.outgoingCokernelSection i, where βᵢ:Iᵢ≅coker jᵢ identifies the outgoing image and
cycles quotient.
-/
@[reassoc]
theorem Splitting.imageDegreeDecompositionIso_outgoing_inv (s : Splitting K) (i : ι) :
    biprod.inr ≫ (s.imageDegreeDecompositionIso i).inv =
      (outgoingImageCokernelIso K i).hom ≫ s.outgoingCokernelSection i := by
  simp only [imageDegreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    Category.assoc, biprod.inr_map_assoc, Iso.symm_inv, degreeDecompositionIso_outgoing_inv]

end HomologicalComplex
