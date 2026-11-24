/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitDegreeCoherence
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingShiftProjection
public import MathlibExt.Algebra.Homology.CochainComplex.ShiftHomologyPointwise

/-!
# Signed cochain shift of actual pointwise decomposition

The original selected homology supplies shifted homology through the native
short-complex isomorphism. The original selected kernel/cokernel supply their
shifted counterparts by native diagram transport. Actual cycle retractions,
homology inclusions, boundary projections and outgoing sections then commute
with the native comparison maps. The resulting nested biproduct comparison
intertwines the actual two constructed degree decompositions.

Only preadditivity and the original selected homology/kernel/cokernel existences
are assumed. No global homology, abelian, zero-object or biproduct premise occurs.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K : CochainComplex C ℤ}

/-- The actual shifted cycles retraction agrees through the native selected cycles comparison. -/
@[reassoc]
lemma cochainShift_cyclesRetraction (s : Splitting K) (a i : ℤ) [K.HasHomology (i + a)] :
    letI := CochainComplex.hasHomology_shift K a i
    (s.cochainShift a).cyclesRetraction i ≫ (CochainComplex.shiftCyclesIso K a i).hom =
      s.cyclesRetraction (i + a) := by
  letI := CochainComplex.hasHomology_shift K a i
  apply (cancel_mono (K.iCycles (i + a))).1
  rw [Category.assoc, CochainComplex.shiftCyclesIso_hom_iCycles,
    (s.cochainShift a).cyclesRetraction_iCycles i,
    s.cyclesRetraction_iCycles (i + a), cochainShift_normalize_dNext]
  rfl

/-- The actual shifted homology inclusion agrees through the native selected homology map. -/
@[reassoc]
lemma cochainShift_homologyInclusionComponent (s : Splitting K) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := CochainComplex.hasHomology_shift K a i
    (CochainComplex.shiftHomologyIso K a i).hom ≫ s.homologyInclusionComponent (i + a) =
      (s.cochainShift a).homologyInclusionComponent i := by
  letI := CochainComplex.hasHomology_shift K a i
  apply (cancel_epi ((K⟦a⟧).homologyπ i)).1
  calc
    _ = ((K⟦a⟧).homologyπ i ≫ (CochainComplex.shiftHomologyIso K a i).hom) ≫
        s.homologyInclusionComponent (i + a) := by simp only [Category.assoc]
    _ = ((CochainComplex.shiftCyclesIso K a i).hom ≫ K.homologyπ (i + a)) ≫
        s.homologyInclusionComponent (i + a) := by
      rw [CochainComplex.shiftHomologyIso_homologyπ]
    _ = (CochainComplex.shiftCyclesIso K a i).hom ≫
        (K.iCycles (i + a) ≫ (𝟙 (K.X (i + a)) - prevD (i + a) s.normalize.hom)) := by
      rw [Category.assoc, s.homologyπ_homologyInclusionComponent (i + a)]
    _ = (K⟦a⟧).iCycles i ≫
        (𝟙 (K.X (i + a)) - prevD (i + a) s.normalize.hom) := by
      rw [← Category.assoc, CochainComplex.shiftCyclesIso_hom_iCycles]
    _ = (K⟦a⟧).iCycles i ≫
        (𝟙 ((K⟦a⟧).X i) - prevD i (s.cochainShift a).normalize.hom) := by
      rw [cochainShift_normalize_prevD]
      rfl
    _ = (K⟦a⟧).homologyπ i ≫ (s.cochainShift a).homologyInclusionComponent i :=
      ((s.cochainShift a).homologyπ_homologyInclusionComponent i).symm

/-- The earned shifted homology section agrees through the native cycle and homology maps. -/
@[reassoc]
lemma cochainShift_homologyCycleSection (s : Splitting K) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := CochainComplex.hasHomology_shift K a i
    (CochainComplex.shiftHomologyIso K a i).hom ≫ s.homologyCycleSection (i + a) =
      (s.cochainShift a).homologyCycleSection i ≫ (CochainComplex.shiftCyclesIso K a i).hom := by
  letI := CochainComplex.hasHomology_shift K a i
  calc
    _ = (s.cochainShift a).homologyInclusionComponent i ≫ s.cyclesRetraction (i + a) := by
      rw [homologyCycleSection, ← Category.assoc, cochainShift_homologyInclusionComponent]
    _ = (s.cochainShift a).homologyInclusionComponent i ≫
        ((s.cochainShift a).cyclesRetraction i ≫ (CochainComplex.shiftCyclesIso K a i).hom) := by
      rw [cochainShift_cyclesRetraction]
    _ = (s.cochainShift a).homologyCycleSection i ≫
        (CochainComplex.shiftCyclesIso K a i).hom := by
      simp only [homologyCycleSection, Category.assoc]

/-- The shifted native pointwise homology coordinate has no residual shift sign. -/
lemma cochainShift_pointwiseHomologyProjectionInclusion (s : Splitting K) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := CochainComplex.hasHomology_shift K a i
    (s.cochainShift a).cyclesRetraction i ≫ (K⟦a⟧).homologyπ i ≫
        (s.cochainShift a).homologyInclusionComponent i =
      s.cyclesRetraction (i + a) ≫ K.homologyπ (i + a) ≫
        s.homologyInclusionComponent (i + a) := by
  letI := CochainComplex.hasHomology_shift K a i
  rw [(s.cochainShift a).pointwiseHomologyProjectionInclusion i,
    s.pointwiseHomologyProjectionInclusion (i + a),
    cochainShift_normalize_dNext, cochainShift_normalize_prevD]
  rfl

/-- The shifted boundary projection agrees through the actual selected kernel comparison. -/
@[reassoc]
lemma cochainShift_boundaryKernelProjection (s : Splitting K) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))] :
    letI := CochainComplex.hasHomology_shift K a i
    letI := CochainComplex.hasKernel_homologyπ_shift K a i
    (s.cochainShift a).boundaryKernelProjection i ≫ (CochainComplex.shiftBoundaryIso K a i).hom =
      (CochainComplex.shiftCyclesIso K a i).hom ≫ s.boundaryKernelProjection (i + a) := by
  letI := CochainComplex.hasHomology_shift K a i
  letI := CochainComplex.hasKernel_homologyπ_shift K a i
  apply (cancel_mono (kernel.ι (K.homologyπ (i + a)))).1
  calc
    _ = (s.cochainShift a).boundaryKernelProjection i ≫
        (kernel.ι ((K⟦a⟧).homologyπ i) ≫ (CochainComplex.shiftCyclesIso K a i).hom) := by
      rw [Category.assoc, CochainComplex.shiftBoundaryIso_hom_ι]
    _ = (𝟙 ((K⟦a⟧).cycles i) -
        (K⟦a⟧).homologyπ i ≫ (s.cochainShift a).homologyCycleSection i) ≫
          (CochainComplex.shiftCyclesIso K a i).hom := by
      rw [← Category.assoc, (s.cochainShift a).boundaryKernelProjection_ι i]
    _ = (CochainComplex.shiftCyclesIso K a i).hom -
        (K⟦a⟧).homologyπ i ≫
          ((s.cochainShift a).homologyCycleSection i ≫ (CochainComplex.shiftCyclesIso K a i).hom) := by
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
    _ = (CochainComplex.shiftCyclesIso K a i).hom -
        (K⟦a⟧).homologyπ i ≫
          ((CochainComplex.shiftHomologyIso K a i).hom ≫ s.homologyCycleSection (i + a)) := by
      rw [← cochainShift_homologyCycleSection]
    _ = (CochainComplex.shiftCyclesIso K a i).hom -
        ((CochainComplex.shiftCyclesIso K a i).hom ≫ K.homologyπ (i + a)) ≫
          s.homologyCycleSection (i + a) := by
      rw [← Category.assoc, CochainComplex.shiftHomologyIso_homologyπ]
    _ = (CochainComplex.shiftCyclesIso K a i).hom ≫
        (𝟙 (K.cycles (i + a)) - K.homologyπ (i + a) ≫ s.homologyCycleSection (i + a)) := by
      simp only [Preadditive.comp_sub, Category.comp_id, Category.assoc]
    _ = ((CochainComplex.shiftCyclesIso K a i).hom ≫ s.boundaryKernelProjection (i + a)) ≫
        kernel.ι (K.homologyπ (i + a)) := by
      rw [Category.assoc, s.boundaryKernelProjection_ι (i + a)]

/-- The shifted outgoing section agrees through the actual selected cokernel comparison. -/
@[reassoc]
lemma cochainShift_outgoingCokernelSection (s : Splitting K) (a i : ℤ)
    [K.HasHomology (i + a)] [HasCokernel (K.iCycles (i + a))] :
    letI := CochainComplex.hasHomology_shift K a i
    letI := CochainComplex.hasCokernel_iCycles_shift K a i
    (CochainComplex.shiftOutgoingIso K a i).hom ≫ s.outgoingCokernelSection (i + a) =
      (s.cochainShift a).outgoingCokernelSection i := by
  letI := CochainComplex.hasHomology_shift K a i
  letI := CochainComplex.hasCokernel_iCycles_shift K a i
  apply (cancel_epi (cokernel.π ((K⟦a⟧).iCycles i))).1
  rw [← Category.assoc, CochainComplex.shiftOutgoingIso_π_hom,
    s.outgoingCokernelProjectionSection (i + a),
    (s.cochainShift a).outgoingCokernelProjectionSection i,
    cochainShift_normalize_dNext]

/-- Actual native boundary/homology/outgoing maps compare the two earned degree decompositions. -/
def cochainShiftDegreeComparison (s : Splitting K) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))]
    [HasCokernel (K.iCycles (i + a))] :
    letI := CochainComplex.hasHomology_shift K a i
    letI := CochainComplex.hasKernel_homologyπ_shift K a i
    letI := CochainComplex.hasCokernel_iCycles_shift K a i
    letI := (s.cochainShift a).hasBoundaryHomologyBiproduct i
    letI := (s.cochainShift a).hasDegreeDecompositionBiproduct i
    letI := s.hasBoundaryHomologyBiproduct (i + a)
    letI := s.hasDegreeDecompositionBiproduct (i + a)
    ((kernel ((K⟦a⟧).homologyπ i) ⊞ (K⟦a⟧).homology i) ⊞ cokernel ((K⟦a⟧).iCycles i)) ≅
      ((kernel (K.homologyπ (i + a)) ⊞ K.homology (i + a)) ⊞ cokernel (K.iCycles (i + a))) := by
  letI := CochainComplex.hasHomology_shift K a i
  letI := CochainComplex.hasKernel_homologyπ_shift K a i
  letI := CochainComplex.hasCokernel_iCycles_shift K a i
  letI := (s.cochainShift a).hasBoundaryHomologyBiproduct i
  letI := (s.cochainShift a).hasDegreeDecompositionBiproduct i
  letI := s.hasBoundaryHomologyBiproduct (i + a)
  letI := s.hasDegreeDecompositionBiproduct (i + a)
  exact biprod.mapIso
    (biprod.mapIso (CochainComplex.shiftBoundaryIso K a i) (CochainComplex.shiftHomologyIso K a i))
    (CochainComplex.shiftOutgoingIso K a i)

/-- The two actual constructed degree isomorphisms commute with the native signed comparison. -/
lemma cochainShiftDegreeComparison_hom (s : Splitting K) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))]
    [HasCokernel (K.iCycles (i + a))] :
    letI := CochainComplex.hasHomology_shift K a i
    letI := CochainComplex.hasKernel_homologyπ_shift K a i
    letI := CochainComplex.hasCokernel_iCycles_shift K a i
    letI := (s.cochainShift a).hasBoundaryHomologyBiproduct i
    letI := (s.cochainShift a).hasDegreeDecompositionBiproduct i
    letI := s.hasBoundaryHomologyBiproduct (i + a)
    letI := s.hasDegreeDecompositionBiproduct (i + a)
    ((s.cochainShift a).degreeDecompositionIso i).hom ≫ (s.cochainShiftDegreeComparison a i).hom =
      (s.degreeDecompositionIso (i + a)).hom := by
  letI := CochainComplex.hasHomology_shift K a i
  letI := CochainComplex.hasKernel_homologyπ_shift K a i
  letI := CochainComplex.hasCokernel_iCycles_shift K a i
  letI := (s.cochainShift a).hasBoundaryHomologyBiproduct i
  letI := (s.cochainShift a).hasDegreeDecompositionBiproduct i
  letI := s.hasBoundaryHomologyBiproduct (i + a)
  letI := s.hasDegreeDecompositionBiproduct (i + a)
  apply biprod.hom_ext
  · apply biprod.hom_ext
    · simp only [cochainShiftDegreeComparison, biprod.mapIso_hom, Category.assoc, biprod.map_fst]
      rw [(s.cochainShift a).degreeDecompositionIso_hom_boundary_assoc i,
        cochainShift_boundaryKernelProjection, cochainShift_cyclesRetraction_assoc,
        s.degreeDecompositionIso_hom_boundary (i + a)]
    · simp only [cochainShiftDegreeComparison, biprod.mapIso_hom, Category.assoc,
        biprod.map_fst, biprod.map_snd]
      rw [(s.cochainShift a).degreeDecompositionIso_hom_homology_assoc i,
        CochainComplex.shiftHomologyIso_homologyπ, cochainShift_cyclesRetraction_assoc,
        s.degreeDecompositionIso_hom_homology (i + a)]
  · simp only [cochainShiftDegreeComparison, biprod.mapIso_hom, Category.assoc, biprod.map_snd]
    rw [(s.cochainShift a).degreeDecompositionIso_hom_outgoing_assoc i,
      CochainComplex.shiftOutgoingIso_π_hom, s.degreeDecompositionIso_hom_outgoing (i + a)]

end HomologicalComplex.Splitting
