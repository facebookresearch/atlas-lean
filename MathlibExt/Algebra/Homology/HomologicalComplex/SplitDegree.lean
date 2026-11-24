/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitHomology
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Pointwise degree decomposition from actual splitting data

Normalized inverse differentials give the existing cycles retraction and
homology inclusion. Their composite is an actual section of the native
homology quotient. Pointwise kernel and cokernel universal properties give
bilimit bicones, and hence the required binary biproducts. There is no
whole-category homology, abelian, zero-object or biproduct assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- The actual native homology inclusion, followed by the normalized cycles retraction. -/
def Splitting.homologyCycleSection (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.homology i ⟶ K.cycles i :=
  s.homologyInclusionComponent i ≫ s.cyclesRetraction i

/-- The earned cycle section retracts the original native homology quotient. -/
@[reassoc]
theorem Splitting.homologyCycleSection_homologyπ (s : Splitting K) (i : ι)
    [K.HasHomology i] : s.homologyCycleSection i ≫ K.homologyπ i = 𝟙 (K.homology i) := by
  have hd : K.d (c.prev i) i ≫ s.cyclesRetraction i ≫ K.homologyπ i = 0 := by
    calc
      _ = (K.toCycles (c.prev i) i ≫ K.iCycles i) ≫ s.cyclesRetraction i ≫ K.homologyπ i := by
        exact congrArg (fun f : K.X (c.prev i) ⟶ K.X i =>
          f ≫ s.cyclesRetraction i ≫ K.homologyπ i) (K.toCycles_i (c.prev i) i).symm
      _ = K.toCycles (c.prev i) i ≫ (K.iCycles i ≫ s.cyclesRetraction i) ≫ K.homologyπ i := by
        simp only [Category.assoc]
      _ = K.toCycles (c.prev i) i ≫ K.homologyπ i := by
        rw [s.iCycles_cyclesRetraction i, Category.id_comp]
      _ = 0 := K.toCycles_comp_homologyπ (c.prev i) i
  have hb : prevD i s.normalize.hom ≫ s.cyclesRetraction i ≫ K.homologyπ i = 0 := by
    change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫
      s.cyclesRetraction i ≫ K.homologyπ i = 0
    simp only [Category.assoc, hd, comp_zero]
  apply (cancel_epi (K.homologyπ i)).1
  calc
    K.homologyπ i ≫ (s.homologyCycleSection i ≫ K.homologyπ i) =
        (K.homologyπ i ≫ s.homologyInclusionComponent i) ≫
          s.cyclesRetraction i ≫ K.homologyπ i := by
      simp only [homologyCycleSection, Category.assoc]
    _ = (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) ≫
          s.cyclesRetraction i ≫ K.homologyπ i := by
      rw [s.homologyπ_homologyInclusionComponent i]
    _ = K.iCycles i ≫ s.cyclesRetraction i ≫ K.homologyπ i -
          K.iCycles i ≫ (prevD i s.normalize.hom ≫ s.cyclesRetraction i ≫ K.homologyπ i) := by
      simp only [Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp,
        Category.id_comp]
    _ = K.homologyπ i := by
      rw [hb, comp_zero, sub_zero, ← Category.assoc,
        s.iCycles_cyclesRetraction i, Category.id_comp]
    _ = K.homologyπ i ≫ 𝟙 (K.homology i) := (Category.comp_id _).symm

/-- The cycle section returns the original homology inclusion after embedding into the term. -/
@[reassoc]
theorem Splitting.homologyCycleSection_iCycles (s : Splitting K) (i : ι)
    [K.HasHomology i] : s.homologyCycleSection i ≫ K.iCycles i =
      s.homologyInclusionComponent i := by
  rw [homologyCycleSection, Category.assoc, s.cyclesRetraction_iCycles i]
  change s.homologyInclusionComponent i ≫
    (𝟙 (K.X i) - K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) = _
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    s.homologyInclusionComponent_d i (c.next i), zero_comp, sub_zero]

/-- The pointwise native homology projector is the complementary normalized projection. -/
theorem Splitting.pointwiseHomologyProjectionInclusion (s : Splitting K) (i : ι)
    [K.HasHomology i] :
    s.cyclesRetraction i ≫ K.homologyπ i ≫ s.homologyInclusionComponent i =
      𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom) := by
  let a : K.X i ⟶ K.X i := dNext i s.normalize.hom
  let b : K.X i ⟶ K.X i := prevD i s.normalize.hom
  have hab : a ≫ b = 0 := by
    change (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫
      (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) = 0
    calc
      _ = K.d i (c.next i) ≫
          (s.normalize.hom (c.next i) i ≫ s.normalize.hom i (c.prev i)) ≫
            K.d (c.prev i) i := by simp only [Category.assoc]
      _ = 0 := by
        rw [s.normalize_hom_comp_hom (c.next i) i (c.prev i)]
        simp only [zero_comp, comp_zero]
  calc
    _ = s.cyclesRetraction i ≫ (K.iCycles i ≫ (𝟙 (K.X i) - b)) := by
      rw [s.homologyπ_homologyInclusionComponent i]
    _ = (𝟙 (K.X i) - a) ≫ (𝟙 (K.X i) - b) := by
      rw [← Category.assoc, s.cyclesRetraction_iCycles i]
    _ = 𝟙 (K.X i) - (a + b) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub,
        Category.id_comp, Category.comp_id, hab]
      abel

section KernelCycles

variable (s : Splitting K) (i : ι) [K.HasHomology i] [HasKernel (K.homologyπ i)]

/-- The actual complement of the native homology section lifts through its kernel. -/
def Splitting.boundaryKernelProjection : K.cycles i ⟶ kernel (K.homologyπ i) :=
  kernel.lift (K.homologyπ i)
    (𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i) (by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        s.homologyCycleSection_homologyπ i, Category.comp_id, sub_self])

@[reassoc]
theorem Splitting.boundaryKernelProjection_ι :
    s.boundaryKernelProjection i ≫ kernel.ι (K.homologyπ i) =
      𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i :=
  kernel.lift_ι _ _ _

/-- The kernel projection is a retraction of the original kernel inclusion. -/
@[reassoc]
theorem Splitting.kernel_ι_boundaryKernelProjection :
    kernel.ι (K.homologyπ i) ≫ s.boundaryKernelProjection i =
      𝟙 (kernel (K.homologyπ i)) := by
  apply (cancel_mono (kernel.ι (K.homologyπ i))).1
  rw [Category.assoc, s.boundaryKernelProjection_ι i]
  simp only [Preadditive.comp_sub, Category.comp_id, kernel.condition_assoc,
    zero_comp, sub_zero, Category.id_comp]

/-- The section has zero boundary-kernel coordinate. -/
@[reassoc]
theorem Splitting.homologyCycleSection_boundaryKernelProjection :
    s.homologyCycleSection i ≫ s.boundaryKernelProjection i = 0 := by
  apply (cancel_mono (kernel.ι (K.homologyπ i))).1
  rw [Category.assoc, s.boundaryKernelProjection_ι i]
  simp only [Preadditive.comp_sub, Category.comp_id,
    s.homologyCycleSection_homologyπ_assoc i,
    sub_self, zero_comp]

/-- The boundary-kernel coordinate followed by actual term inclusion is the incoming normalized projector. -/
theorem Splitting.boundaryKernelProjection_term :
    s.cyclesRetraction i ≫ s.boundaryKernelProjection i ≫
      kernel.ι (K.homologyπ i) ≫ K.iCycles i = prevD i s.normalize.hom := by
  calc
    _ = s.cyclesRetraction i ≫
        (𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i) ≫ K.iCycles i := by
      rw [s.boundaryKernelProjection_ι_assoc i]
    _ = s.cyclesRetraction i ≫ K.iCycles i -
          s.cyclesRetraction i ≫ K.homologyπ i ≫ s.homologyInclusionComponent i := by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp,
        Category.assoc, s.homologyCycleSection_iCycles i]
    _ = (𝟙 (K.X i) - dNext i s.normalize.hom) -
          (𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom)) := by
      rw [s.cyclesRetraction_iCycles i, s.pointwiseHomologyProjectionInclusion i]
    _ = prevD i s.normalize.hom := by abel

/-- The actual kernel, cycle and homology maps form a binary bicone. -/
def Splitting.cyclesBoundaryHomologyBicone :
    BinaryBicone (kernel (K.homologyπ i)) (K.homology i) where
  pt := K.cycles i
  fst := s.boundaryKernelProjection i
  snd := K.homologyπ i
  inl := kernel.ι (K.homologyπ i)
  inr := s.homologyCycleSection i
  inl_fst := s.kernel_ι_boundaryKernelProjection i
  inl_snd := kernel.condition _
  inr_fst := s.homologyCycleSection_boundaryKernelProjection i
  inr_snd := s.homologyCycleSection_homologyπ i

/-- Native kernel recognition proves this actual cycle bicone is a bilimit. -/
def Splitting.cyclesBoundaryHomologyBiconeIsBilimit :
    (s.cyclesBoundaryHomologyBicone i).IsBilimit :=
  BinaryBicone.isBilimitOfKernelInl _ (kernelIsKernel (K.homologyπ i))

include s in
/-- The pointwise boundary-kernel/homology biproduct exists by the constructed universal property. -/
theorem Splitting.hasBoundaryHomologyBiproduct :
    HasBinaryBiproduct (kernel (K.homologyπ i)) (K.homology i) :=
  HasBinaryBiproduct.mk {
    bicone := s.cyclesBoundaryHomologyBicone i
    isBilimit := s.cyclesBoundaryHomologyBiconeIsBilimit i }

/-- The actual cycles decompose into their boundary kernel and original homology. -/
def Splitting.cyclesBoundaryHomologyIso :
    letI := s.hasBoundaryHomologyBiproduct i
    K.cycles i ≅ kernel (K.homologyπ i) ⊞ K.homology i := by
  letI := s.hasBoundaryHomologyBiproduct i
  exact biprod.uniqueUpToIso _ _ (s.cyclesBoundaryHomologyBiconeIsBilimit i)

/-- The cycles isomorphism retains the constructed boundary-kernel projection. -/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_hom_fst :
    letI := s.hasBoundaryHomologyBiproduct i
    (s.cyclesBoundaryHomologyIso i).hom ≫ biprod.fst = s.boundaryKernelProjection i := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.lift_fst]

/-- The cycles isomorphism retains the original native homology quotient. -/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_hom_snd :
    letI := s.hasBoundaryHomologyBiproduct i
    (s.cyclesBoundaryHomologyIso i).hom ≫ biprod.snd = K.homologyπ i := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.lift_snd]

/-- The inverse cycles comparison retains the actual boundary-kernel inclusion. -/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_inl_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    biprod.inl ≫ (s.cyclesBoundaryHomologyIso i).inv = kernel.ι (K.homologyπ i) := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.inl_desc]

/-- The inverse cycles comparison retains the actual earned homology section. -/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_inr_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    biprod.inr ≫ (s.cyclesBoundaryHomologyIso i).inv = s.homologyCycleSection i := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.inr_desc]

end KernelCycles

section CokernelTerm

variable (s : Splitting K) (i : ι) [K.HasHomology i] [HasCokernel (K.iCycles i)]

/-- The actual complement of cycles descends through the cycle-inclusion cokernel. -/
def Splitting.outgoingCokernelSection : cokernel (K.iCycles i) ⟶ K.X i :=
  cokernel.desc (K.iCycles i)
    (𝟙 (K.X i) - s.cyclesRetraction i ≫ K.iCycles i) (by
      rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
        s.iCycles_cyclesRetraction i, Category.id_comp, sub_self])

@[reassoc]
theorem Splitting.cokernel_π_outgoingCokernelSection :
    cokernel.π (K.iCycles i) ≫ s.outgoingCokernelSection i =
      𝟙 (K.X i) - s.cyclesRetraction i ≫ K.iCycles i :=
  cokernel.π_desc _ _ _

/-- The outgoing section retracts the actual cycle-inclusion cokernel projection. -/
@[reassoc]
theorem Splitting.outgoingCokernelSection_cokernel_π :
    s.outgoingCokernelSection i ≫ cokernel.π (K.iCycles i) =
      𝟙 (cokernel (K.iCycles i)) := by
  apply (cancel_epi (cokernel.π (K.iCycles i))).1
  rw [← Category.assoc, s.cokernel_π_outgoingCokernelSection i]
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
    cokernel.condition, comp_zero, sub_zero, Category.comp_id]

/-- The outgoing cokernel section has zero cycles coordinate. -/
@[reassoc]
theorem Splitting.outgoingCokernelSection_cyclesRetraction :
    s.outgoingCokernelSection i ≫ s.cyclesRetraction i = 0 := by
  apply (cancel_epi (cokernel.π (K.iCycles i))).1
  rw [← Category.assoc, s.cokernel_π_outgoingCokernelSection i]
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
    s.iCycles_cyclesRetraction i, Category.comp_id, sub_self, comp_zero]

/-- Projection to the outgoing cokernel followed by its actual section is the outgoing normalized projector. -/
theorem Splitting.outgoingCokernelProjectionSection :
    cokernel.π (K.iCycles i) ≫ s.outgoingCokernelSection i =
      dNext i s.normalize.hom := by
  rw [s.cokernel_π_outgoingCokernelSection i, s.cyclesRetraction_iCycles i]
  abel

/-- The original cycle and cokernel maps form a binary bicone with the actual term. -/
def Splitting.termCyclesOutgoingBicone :
    BinaryBicone (K.cycles i) (cokernel (K.iCycles i)) where
  pt := K.X i
  fst := s.cyclesRetraction i
  snd := cokernel.π (K.iCycles i)
  inl := K.iCycles i
  inr := s.outgoingCokernelSection i
  inl_fst := s.iCycles_cyclesRetraction i
  inl_snd := cokernel.condition _
  inr_fst := s.outgoingCokernelSection_cyclesRetraction i
  inr_snd := s.outgoingCokernelSection_cokernel_π i

/-- Native cokernel recognition proves the actual term bicone is a bilimit. -/
def Splitting.termCyclesOutgoingBiconeIsBilimit :
    (s.termCyclesOutgoingBicone i).IsBilimit :=
  BinaryBicone.isBilimitOfCokernelSnd _ (cokernelIsCokernel (K.iCycles i))

include s in
/-- The pointwise cycles/outgoing-cokernel biproduct exists by the constructed universal property. -/
theorem Splitting.hasCyclesOutgoingBiproduct :
    HasBinaryBiproduct (K.cycles i) (cokernel (K.iCycles i)) :=
  HasBinaryBiproduct.mk {
    bicone := s.termCyclesOutgoingBicone i
    isBilimit := s.termCyclesOutgoingBiconeIsBilimit i }

/-- The actual term decomposes into cycles and their outgoing cokernel. -/
def Splitting.termCyclesOutgoingIso :
    letI := s.hasCyclesOutgoingBiproduct i
    K.X i ≅ K.cycles i ⊞ cokernel (K.iCycles i) := by
  letI := s.hasCyclesOutgoingBiproduct i
  exact biprod.uniqueUpToIso _ _ (s.termCyclesOutgoingBiconeIsBilimit i)

/-- The term comparison uses precisely the normalized cycles retraction. -/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_hom_fst :
    letI := s.hasCyclesOutgoingBiproduct i
    (s.termCyclesOutgoingIso i).hom ≫ biprod.fst = s.cyclesRetraction i := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.lift_fst]

/-- The term comparison keeps the original cycle-inclusion cokernel projection. -/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_hom_snd :
    letI := s.hasCyclesOutgoingBiproduct i
    (s.termCyclesOutgoingIso i).hom ≫ biprod.snd = cokernel.π (K.iCycles i) := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.lift_snd]

/-- The inverse term comparison keeps the actual cycles inclusion. -/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_inl_inv :
    letI := s.hasCyclesOutgoingBiproduct i
    biprod.inl ≫ (s.termCyclesOutgoingIso i).inv = K.iCycles i := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.inl_desc]

/-- The inverse term comparison keeps the earned outgoing cokernel section. -/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_inr_inv :
    letI := s.hasCyclesOutgoingBiproduct i
    biprod.inr ≫ (s.termCyclesOutgoingIso i).inv = s.outgoingCokernelSection i := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.inr_desc]

end CokernelTerm

section DegreeDecomposition

variable (s : Splitting K) (i : ι) [K.HasHomology i]
  [HasKernel (K.homologyπ i)] [HasCokernel (K.iCycles i)]

/-- Native object-isomorphism transport earns the nested pointwise biproduct. -/
theorem Splitting.hasDegreeDecompositionBiproduct :
    letI := s.hasBoundaryHomologyBiproduct i
    HasBinaryBiproduct (kernel (K.homologyπ i) ⊞ K.homology i) (cokernel (K.iCycles i)) := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  exact hasBinaryBiproduct_of_iso (s.cyclesBoundaryHomologyIso i)
    (Iso.refl (cokernel (K.iCycles i)))

/-- The actual degree splits into native boundary kernel, original homology and outgoing cokernel. -/
def Splitting.degreeDecompositionIso :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    K.X i ≅ (kernel (K.homologyπ i) ⊞ K.homology i) ⊞ cokernel (K.iCycles i) := by
  letI := s.hasBoundaryHomologyBiproduct i
  letI := s.hasCyclesOutgoingBiproduct i
  letI := s.hasDegreeDecompositionBiproduct i
  exact s.termCyclesOutgoingIso i ≪≫
    biprod.mapIso (s.cyclesBoundaryHomologyIso i) (Iso.refl (cokernel (K.iCycles i)))

/-- The incoming-kernel coordinate is the actual cycles retraction followed by its kernel projection. -/
@[reassoc]
theorem Splitting.degreeDecompositionIso_hom_boundary :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.fst =
      s.cyclesRetraction i ≫ s.boundaryKernelProjection i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, cyclesBoundaryHomologyIso_hom_fst,
    termCyclesOutgoingIso_hom_fst_assoc]

/-- The homology coordinate is exactly the original normalized cycle projection and native quotient. -/
@[reassoc]
theorem Splitting.degreeDecompositionIso_hom_homology :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.snd =
      s.cyclesRetraction i ≫ K.homologyπ i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, cyclesBoundaryHomologyIso_hom_snd,
    termCyclesOutgoingIso_hom_fst_assoc]

/-- The outgoing coordinate is precisely the original cycle-inclusion cokernel map. -/
@[reassoc]
theorem Splitting.degreeDecompositionIso_hom_outgoing :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (s.degreeDecompositionIso i).hom ≫ biprod.snd = cokernel.π (K.iCycles i) := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_snd, Iso.refl_hom, Category.comp_id,
    termCyclesOutgoingIso_hom_snd]

/-- The incoming coordinate inclusion is the actual native kernel inclusion followed by cycles. -/
@[reassoc]
theorem Splitting.degreeDecompositionIso_boundary_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    biprod.inl ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv =
      kernel.ι (K.homologyπ i) ≫ K.iCycles i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    biprod.inl_map_assoc, cyclesBoundaryHomologyIso_inl_inv_assoc,
    termCyclesOutgoingIso_inl_inv]

/-- The homology coordinate inclusion is the original earned homology inclusion component. -/
@[reassoc]
theorem Splitting.degreeDecompositionIso_homology_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    biprod.inr ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv =
      s.homologyInclusionComponent i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    biprod.inl_map_assoc, cyclesBoundaryHomologyIso_inr_inv_assoc,
    termCyclesOutgoingIso_inl_inv, homologyCycleSection_iCycles]

/-- The outgoing coordinate inclusion is the actual cokernel section earned from the normalized inverse. -/
@[reassoc]
theorem Splitting.degreeDecompositionIso_outgoing_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    biprod.inr ≫ (s.degreeDecompositionIso i).inv = s.outgoingCokernelSection i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    biprod.inr_map_assoc, Iso.refl_inv, Category.id_comp,
    termCyclesOutgoingIso_inr_inv]

end DegreeDecomposition

end HomologicalComplex
