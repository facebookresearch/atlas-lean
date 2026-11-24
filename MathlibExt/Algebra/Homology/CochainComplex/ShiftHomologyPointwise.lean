/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Pointwise cochain shift and homology

The signed short-complex shift gives a homology comparison using only the homology and displayed
kernel/cokernel data at the selected degree. The first and third components retain the shift
signs; no global abelian or homology-category hypothesis is required.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Signed short-complex transport gives homology at the selected shifted degree. -/
lemma hasHomology_shift (K : CochainComplex C ℤ) (a i : ℤ) [K.HasHomology (i + a)] :
    (K⟦a⟧).HasHomology i :=
  ShortComplex.hasHomology_of_iso
    ((shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K).symm

private lemma shiftScIso_hom_tau2 (K : CochainComplex C ℤ) (a i : ℤ) :
    (((shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K).hom).τ₂ =
      𝟙 (K.X (i + a)) := by
  rfl

private lemma shiftScIso_inv_tau2 (K : CochainComplex C ℤ) (a i : ℤ) :
    (((shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K).inv).τ₂ =
      𝟙 (K.X (i + a)) := by
  rfl

/-- The short-complex map identifies shifted cycles with the original selected cycles. -/
def shiftCyclesIso (K : CochainComplex C ℤ) (a i : ℤ) [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (K⟦a⟧).cycles i ≅ K.cycles (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  exact ShortComplex.cyclesMapIso e

/-- The short-complex homology map supplies the selected shifted homology isomorphism. -/
def shiftHomologyIso (K : CochainComplex C ℤ) (a i : ℤ) [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (K⟦a⟧).homology i ≅ K.homology (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  exact ShortComplex.homologyMapIso e

/-- The selected cycles comparison preserves the cycles inclusion. -/
@[reassoc]
lemma shiftCyclesIso_hom_iCycles (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (shiftCyclesIso K a i).hom ≫ K.iCycles (i + a) = (K⟦a⟧).iCycles i := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  change ShortComplex.cyclesMap e.hom ≫ (K.sc (i + a)).iCycles =
    ((K⟦a⟧).sc i).iCycles
  have he : e.hom.τ₂ = 𝟙 (K.X (i + a)) := shiftScIso_hom_tau2 K a i
  rw [ShortComplex.cyclesMap_i, he]
  change ((K⟦a⟧).sc i).iCycles ≫ 𝟙 ((K⟦a⟧).sc i).X₂ = ((K⟦a⟧).sc i).iCycles
  exact Category.comp_id _

/-- The inverse selected cycles comparison preserves the original inclusion. -/
@[reassoc]
lemma shiftCyclesIso_inv_iCycles (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (shiftCyclesIso K a i).inv ≫ (K⟦a⟧).iCycles i = K.iCycles (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  change ShortComplex.cyclesMap e.inv ≫ ((K⟦a⟧).sc i).iCycles =
    (K.sc (i + a)).iCycles
  have he : e.inv.τ₂ = 𝟙 (K.X (i + a)) := shiftScIso_inv_tau2 K a i
  rw [ShortComplex.cyclesMap_i, he]
  change (K.sc (i + a)).iCycles ≫ 𝟙 (K.sc (i + a)).X₂ = (K.sc (i + a)).iCycles
  exact Category.comp_id _

/-- The selected cycle and homology comparisons commute with the original quotient. -/
@[reassoc]
lemma shiftHomologyIso_homologyπ (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (K⟦a⟧).homologyπ i ≫ (shiftHomologyIso K a i).hom =
      (shiftCyclesIso K a i).hom ≫ K.homologyπ (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  exact ShortComplex.homologyπ_naturality e.hom

/-- The pointwise shifted cycle comparison is natural in the original complex map. -/
@[reassoc]
lemma shiftCyclesIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) (a i : ℤ)
    [K.HasHomology (i + a)] [L.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    letI := hasHomology_shift L a i
    cyclesMap (f⟦a⟧') i ≫ (shiftCyclesIso L a i).hom =
      (shiftCyclesIso K a i).hom ≫ cyclesMap f (i + a) := by
  letI := hasHomology_shift K a i
  letI := hasHomology_shift L a i
  apply (cancel_mono (L.iCycles (i + a))).1
  simp only [Category.assoc]
  rw [shiftCyclesIso_hom_iCycles, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, CochainComplex.shiftFunctor_map_f']
  simp only [← Category.assoc, shiftCyclesIso_hom_iCycles]

/-- The pointwise shifted homology comparison is natural in the original complex map. -/
@[reassoc]
lemma shiftHomologyIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) (a i : ℤ)
    [K.HasHomology (i + a)] [L.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    letI := hasHomology_shift L a i
    homologyMap (f⟦a⟧') i ≫ (shiftHomologyIso L a i).hom =
      (shiftHomologyIso K a i).hom ≫ homologyMap f (i + a) := by
  letI := hasHomology_shift K a i
  letI := hasHomology_shift L a i
  apply (cancel_epi ((K⟦a⟧).homologyπ i)).1
  rw [HomologicalComplex.homologyπ_naturality_assoc, shiftHomologyIso_homologyπ,
    shiftHomologyIso_homologyπ_assoc, HomologicalComplex.homologyπ_naturality]
  exact shiftCyclesIso_naturality_assoc f a i _

/-- The selected original quotient kernel supplies the shifted quotient kernel by diagram transport. -/
lemma hasKernel_homologyπ_shift (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))] :
    letI := hasHomology_shift K a i
    HasKernel ((K⟦a⟧).homologyπ i) := by
  letI := hasHomology_shift K a i
  let e : parallelPair ((K⟦a⟧).homologyπ i) 0 ≅ parallelPair (K.homologyπ (i + a)) 0 :=
    parallelPair.ext (shiftCyclesIso K a i) (shiftHomologyIso K a i)
      (shiftHomologyIso_homologyπ K a i) (by simp)
  exact hasLimit_of_iso e.symm

/-- The selected original cycle-inclusion cokernel supplies its shifted cokernel by diagram transport. -/
lemma hasCokernel_iCycles_shift (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasCokernel (K.iCycles (i + a))] :
    letI := hasHomology_shift K a i
    HasCokernel ((K⟦a⟧).iCycles i) := by
  letI := hasHomology_shift K a i
  let e : parallelPair ((K⟦a⟧).iCycles i) 0 ≅ parallelPair (K.iCycles (i + a)) 0 :=
    parallelPair.ext (shiftCyclesIso K a i) (Iso.refl _)
      (by
        change (K⟦a⟧).iCycles i ≫ 𝟙 ((K⟦a⟧).X i) =
          (shiftCyclesIso K a i).hom ≫ K.iCycles (i + a)
        exact (Category.comp_id _).trans (shiftCyclesIso_hom_iCycles K a i).symm) (by simp)
  exact hasColimit_of_iso e

/-- Kernel maps identify the selected shifted boundary kernel. -/
def shiftBoundaryIso (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasKernel_homologyπ_shift K a i
    kernel ((K⟦a⟧).homologyπ i) ≅ kernel (K.homologyπ (i + a)) := by
  letI := hasHomology_shift K a i
  letI := hasKernel_homologyπ_shift K a i
  exact kernel.mapIso ((K⟦a⟧).homologyπ i) (K.homologyπ (i + a))
    (shiftCyclesIso K a i) (shiftHomologyIso K a i)
      (shiftHomologyIso_homologyπ K a i)

/-- The selected boundary comparison retains the kernel inclusions. -/
@[reassoc]
lemma shiftBoundaryIso_hom_ι (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasKernel_homologyπ_shift K a i
    (shiftBoundaryIso K a i).hom ≫ kernel.ι (K.homologyπ (i + a)) =
      kernel.ι ((K⟦a⟧).homologyπ i) ≫ (shiftCyclesIso K a i).hom := by
  letI := hasHomology_shift K a i
  letI := hasKernel_homologyπ_shift K a i
  simp [shiftBoundaryIso, kernel.mapIso]

/-- Cokernel maps identify the selected shifted outgoing cokernel. -/
def shiftOutgoingIso (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasCokernel (K.iCycles (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasCokernel_iCycles_shift K a i
    cokernel ((K⟦a⟧).iCycles i) ≅ cokernel (K.iCycles (i + a)) := by
  letI := hasHomology_shift K a i
  letI := hasCokernel_iCycles_shift K a i
  exact cokernel.mapIso ((K⟦a⟧).iCycles i) (K.iCycles (i + a))
    (shiftCyclesIso K a i) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using
        (shiftCyclesIso_hom_iCycles K a i).symm)

/-- The selected outgoing comparison retains the cokernel projections. -/
@[reassoc]
lemma shiftOutgoingIso_π_hom (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasCokernel (K.iCycles (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasCokernel_iCycles_shift K a i
    cokernel.π ((K⟦a⟧).iCycles i) ≫ (shiftOutgoingIso K a i).hom =
      cokernel.π (K.iCycles (i + a)) := by
  letI := hasHomology_shift K a i
  letI := hasCokernel_iCycles_shift K a i
  simp [shiftOutgoingIso, cokernel.mapIso]

end CochainComplex
