/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicCycles
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicFiltration
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientCofiberExactness
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedCofinality
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.ZMod.Basic
public meta import Lean.Elab.Tactic.Omega

/-!
# Nonzero cycles and cofibers in a bounded acyclic complex

The universe-one lift of `ℤ/4` gives the split acyclic complex
`N → N × N → N` in degrees minus one, zero and one. Its differentials
are inclusion into the first coordinate and projection onto the second.
The interior cycle object is nonzero. Top truncation retains the positive
projection sign, and its cofiber descendant is a nonzero quasi-isomorphism.
The finite truncation filtration terminates after three steps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace BoundedAmbientAcyclicNonzeroTests

private abbrev E := ModuleCat.{1} ℤ

private abbrev V := ULift.{1} (ZMod 4)

private abbrev N : E := ModuleCat.of ℤ V

private abbrev P : E := ModuleCat.of ℤ (V × V)

private abbrev inl : N ⟶ P := ModuleCat.ofHom (LinearMap.inl ℤ V V)

private abbrev snd : P ⟶ N := ModuleCat.ofHom (LinearMap.snd ℤ V V)

private theorem inl_snd_zero : inl ≫ snd = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private abbrev terms (j : ℤ) : E :=
  if j = -1 then N else if j = 0 then P else if j = 1 then N else 0

private abbrev step (j : ℤ) : terms j ⟶ terms (j + 1) :=
  if h : j = -1 then by subst j; exact inl
  else if h : j = 0 then by subst j; exact snd
  else 0

private theorem step_square (j : ℤ) : step j ≫ step (j + 1) = 0 := by
  by_cases hn : j = -1
  · subst j
    change inl ≫ snd = 0
    exact inl_snd_zero
  · by_cases hz : j = 0
    · subst j
      change snd ≫ (0 : N ⟶ (0 : E)) = 0
      exact comp_zero
    · have hs : step j = 0 := by
        simp only [step, dite_eq_right hn, dite_eq_right hz]
      rw [hs]
      exact zero_comp

private abbrev raw : CochainComplex E ℤ := CochainComplex.of terms step step_square

private theorem d_neg_one_zero : raw.d (-1) 0 = inl := by
  let claim (j : ℤ) : Prop := HEq (raw.d (-1) j) inl
  have hs : HEq (step (-1)) inl := by
    simp only [step, dite_eq_left]
    rfl
  have hbase : claim ((-1 : ℤ) + 1) :=
    (heq_of_eq (CochainComplex.of_d terms step (-1))).trans hs
  have hzero : claim 0 := Eq.mp (congrArg claim (by omega : (-1 : ℤ) + 1 = 0)) hbase
  exact eq_of_heq hzero

private theorem d_zero_one : raw.d 0 1 = snd := by
  let claim (j : ℤ) : Prop := HEq (raw.d 0 j) snd
  have hs : HEq (step 0) snd := by
    simp only [step, dite_eq_right (by decide : (0 : ℤ) ≠ -1), dite_eq_left]
    rfl
  have hbase : claim ((0 : ℤ) + 1) :=
    (heq_of_eq (CochainComplex.of_d terms step 0)).trans hs
  have hone : claim 1 := Eq.mp (congrArg claim (by omega : (0 : ℤ) + 1 = 1)) hbase
  exact eq_of_heq hone

private theorem support (j : ℤ) (hj : j < -1 ∨ 1 < j) : IsZero (raw.X j) := by
  have hn : j ≠ -1 := by omega
  have hz : j ≠ 0 := by omega
  have ho : j ≠ 1 := by omega
  change IsZero (terms j)
  simp only [terms, if_neg hn, if_neg hz, if_neg ho]
  exact isZero_zero E

private theorem raw_acyclic : raw.Acyclic := by
  intro j
  by_cases hn : j = -1
  · subst j
    apply (raw.exactAt_iff' (-2) (-1) 0 (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change (raw.d (-1) 0).hom x = 0 at hx
    rw [d_neg_one_zero] at hx
    change (x, (0 : V)) = 0 at hx
    have hx0 := congrArg Prod.fst hx
    change x = 0 at hx0
    refine ⟨0, ?_⟩
    change (raw.d (-2) (-1)).hom 0 = x
    rw [map_zero, hx0]
  · by_cases hz : j = 0
    · subst j
      apply (raw.exactAt_iff' (-1) 0 1 (by simp) (by simp)).mpr
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      change (raw.d 0 1).hom x = 0 at hx
      rw [d_zero_one] at hx
      change x.2 = 0 at hx
      refine ⟨x.1, ?_⟩
      change (raw.d (-1) 0).hom x.1 = x
      rw [d_neg_one_zero]
      change (x.1, (0 : V)) = x
      apply Prod.ext
      · rfl
      · exact hx.symm
    · by_cases ho : j = 1
      · subst j
        apply (raw.exactAt_iff' 0 1 2 (by simp) (by simp)).mpr
        rw [ShortComplex.moduleCat_exact_iff]
        intro x _
        refine ⟨(0, x), ?_⟩
        change (raw.d 0 1).hom (0, x) = x
        rw [d_zero_one]
        rfl
      · apply (raw.exactAt_iff' (j - 1) j (j + 1) (by simp) (by simp)).mpr
        rw [ShortComplex.moduleCat_exact_iff]
        intro x _
        have hzero := support j (by omega)
        letI : Subsingleton (raw.X j) := ModuleCat.isZero_iff_subsingleton.mp hzero
        exact ⟨0, Subsingleton.elim _ _⟩

private abbrev K : CochainComplex.Bounded E :=
  CochainComplex.Bounded.of E raw (-1) 1 support

private abbrev F : E ⥤ E := 𝟭 E

private theorem mapped_acyclic : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic := by
  change raw.Acyclic
  exact raw_acyclic

private theorem kernel_closure {X Y : E} (f : X ⟶ Y) [Epi f]
    (_ : F.essImage X) (_ : F.essImage Y) : F.essImage (kernel f) :=
  F.obj_mem_essImage (kernel f)

private instance : F.ReflectsAdmissibleExact where
  reflects_admissibleExact _ h := h

private def splitRow : ShortComplex E := ShortComplex.mk inl snd inl_snd_zero

private theorem splitRow_shortExact : splitRow.ShortExact :=
  ModuleCat.shortComplex_shortExact splitRow Function.Exact.inl_snd
    LinearMap.inl_injective LinearMap.snd_surjective

private abbrev cycle0 :=
  CochainComplex.Bounded.AmbientCycles.dataAt F K (-1) 1 support mapped_acyclic kernel_closure 0

private theorem cycle_kernel_zero : inl ≫ F.map (K.obj.d 0 (0 + 1)) = 0 := by
  change inl ≫ raw.d 0 1 = 0
  rw [d_zero_one]
  exact inl_snd_zero

private def cycle_kernel_limit :
    IsLimit (KernelFork.ofι (f := F.map (K.obj.d 0 (0 + 1))) inl cycle_kernel_zero) := by
  change IsLimit (KernelFork.ofι (f := raw.d 0 1) inl _)
  rw [d_zero_one]
  exact splitRow_shortExact.fIsKernel

private def cycle0Iso : cycle0.Z ≅ N :=
  cycle0.mappedIsLimit.conePointUniqueUpToIso cycle_kernel_limit

private theorem N_nonzero : ¬ IsZero N := by
  intro hzero
  have h : (ULift.up (1 : ZMod 4) : V) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp hzero).elim _ _
  have hdown := congrArg ULift.down h
  change (1 : ZMod 4) = 0 at hdown
  exact (by decide : (1 : ZMod 4) ≠ 0) hdown

private theorem cycle0_nonzero : ¬ IsZero cycle0.Z := by
  intro hzero
  exact N_nonzero (hzero.of_iso cycle0Iso.symm)

private theorem inl_nonzero : inl ≠ 0 := by
  intro hzero
  have h := congrArg (fun f : N ⟶ P => (f.hom (ULift.up (1 : ZMod 4))).1.down) hzero
  change (1 : ZMod 4) = 0 at h
  exact (by decide : (1 : ZMod 4) ≠ 0) h

private theorem snd_nonzero : snd ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun f : P ⟶ N => (f.hom (0, ULift.up (1 : ZMod 4))).down) hzero
  change (1 : ZMod 4) = 0 at h
  exact (by decide : (1 : ZMod 4) ≠ 0) h

private abbrev D :=
  CochainComplex.Bounded.AmbientCycles.admissibleData
    F K (-1) 1 support mapped_acyclic kernel_closure

private abbrev disk := CochainComplex.Bounded.TruncationAt.topDiskRaw (b := 1) K

private abbrev projection := CochainComplex.Bounded.TruncationAt.topDiskProjection (b := 1) K

private abbrev lowerIso := CochainComplex.Bounded.TruncationAt.topDiskLowerIso (b := 1) K

private abbrev upperIso := CochainComplex.Bounded.TruncationAt.topDiskUpperIso (b := 1) K

private theorem projection_lower_positive : projection.f 0 ≫ lowerIso.inv = snd := by
  calc
    projection.f 0 ≫ lowerIso.inv = (raw.d 0 1 ≫ lowerIso.hom) ≫ lowerIso.inv := by
      rw [CochainComplex.Bounded.TruncationAt.topDiskProjection_f_lower]
    _ = raw.d 0 1 := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = snd := d_zero_one

private theorem projection_upper_identity : projection.f 1 ≫ upperIso.inv = 𝟙 N := by
  rw [CochainComplex.Bounded.TruncationAt.topDiskProjection_f_upper]
  exact upperIso.hom_inv_id

private theorem projection_nonzero : projection ≠ 0 := by
  intro hzero
  have hcomp : projection.f 1 = 0 := HomologicalComplex.congr_hom hzero 1
  have hid : (𝟙 N : N ⟶ N) = 0 := by
    rw [← projection_upper_identity, hcomp]
    exact zero_comp
  exact N_nonzero ((IsZero.iff_id_eq_zero N).mpr hid)

private abbrev truncationι :=
  CochainComplex.Bounded.TruncationAt.topTruncationRawι
    (b := 1) (a := -1) (hSupport := support) F kernel_closure K mapped_acyclic

private abbrev cofiber := HomologicalComplex.homotopyCofiber truncationι

private abbrev descendant :=
  CochainComplex.Bounded.TruncationAt.topTruncationCofiberDescRaw
    (b := 1) (a := -1) (hSupport := support) F kernel_closure K mapped_acyclic

private theorem descendant_inr :
    HomologicalComplex.homotopyCofiber.inr truncationι ≫ descendant = projection :=
  CochainComplex.Bounded.TruncationAt.topTruncationCofiber_inr_desc
    (b := 1) (a := -1) (hSupport := support) F kernel_closure K mapped_acyclic

private theorem descendant_nonzero : descendant ≠ 0 := by
  intro hzero
  apply projection_nonzero
  rw [← descendant_inr, hzero]
  exact comp_zero

private def componentChart (j : ℤ) : F.obj (raw.X j) ≅ raw.X j :=
  if j = -1 then (LinearEquiv.neg ℤ : raw.X j ≃ₗ[ℤ] raw.X j).toModuleIso
  else Iso.refl _

private abbrev liftedRaw := F.preimageHomologicalComplex raw raw.X componentChart

private theorem chart_neg_one_hom : (componentChart (-1)).hom = -(𝟙 N) := by
  change (LinearEquiv.neg ℤ : N ≃ₗ[ℤ] N).toModuleIso.hom = -(𝟙 N)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.neg_apply, ModuleCat.hom_neg, ModuleCat.hom_id, LinearMap.neg_apply,
    LinearMap.id_apply]

private theorem chart_zero_inv : (componentChart 0).inv = 𝟙 P := by
  simp only [componentChart, if_neg (by decide : (0 : ℤ) ≠ -1), Iso.refl_inv]

private theorem lifted_negative_differential : liftedRaw.d (-1) 0 = -inl := by
  have h := F.map_preimageHomologicalComplex_d raw raw.X componentChart (-1) 0
  change liftedRaw.d (-1) 0 = (componentChart (-1)).hom ≫ raw.d (-1) 0 ≫
    (componentChart 0).inv at h
  rw [chart_neg_one_hom, chart_zero_inv, d_neg_one_zero, Category.comp_id,
    Preadditive.neg_comp, Category.id_comp] at h
  exact h

example : raw.Acyclic := raw_acyclic

example : raw.d (-1) 0 ≠ 0 := by
  rw [d_neg_one_zero]
  exact inl_nonzero

example : raw.d 0 1 ≠ 0 := by
  rw [d_zero_one]
  exact snd_nonzero

example : ¬ IsZero cycle0.Z := cycle0_nonzero

example (j : ℤ) :
    IsAdmissibleExact (ShortComplex.mk (D.ι j) (D.q j) (D.zero j)) :=
  D.admissible j

example : D.q (-1) ≫ D.ι 0 = inl := (D.factor (-1)).trans d_neg_one_zero

example : D.q 0 ≫ D.ι 1 = snd := (D.factor 0).trans d_zero_one

example : projection.f 0 ≫ lowerIso.inv = snd := projection_lower_positive

example : projection.f 1 ≫ upperIso.inv = 𝟙 N := projection_upper_identity

example : HomologicalComplex.homotopyCofiber.inr truncationι ≫ descendant = projection :=
  descendant_inr

example :
    HomologicalComplex.homotopyCofiber.inlX truncationι 0 (-1) (by simp) ≫
      descendant.f (-1) = 0 :=
  CochainComplex.Bounded.TruncationAt.topTruncationCofiber_inlX_desc_f
    (b := 1) (a := -1) (hSupport := support) F kernel_closure K mapped_acyclic (-1) 0 (by simp)

example : descendant ≠ 0 := descendant_nonzero

example : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map descendant) :=
  CochainComplex.Bounded.TruncationAt.topTruncationCofiberDesc_map_quasiIso
    (b := 1) (a := -1) (hSupport := support) F kernel_closure K mapped_acyclic

example : CochainComplex.Bounded.TruncationFiltration.length (-1) 1 = 3 := by decide

example (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.Bounded.TruncationFiltration.stage
        F kernel_closure K (-1) 1 support mapped_acyclic n).complex.obj).Acyclic :=
  CochainComplex.Bounded.TruncationFiltration.stage_map_acyclic
    F kernel_closure K (-1) 1 support mapped_acyclic n

example :
    IsZero ((CochainComplex.Bounded.TruncationFiltration.stage
      F kernel_closure K (-1) 1 support mapped_acyclic
      (CochainComplex.Bounded.TruncationFiltration.length (-1) 1)).complex) :=
  CochainComplex.Bounded.TruncationFiltration.terminal_isZero
    F kernel_closure K (-1) 1 support mapped_acyclic

example : liftedRaw.d (-1) 0 = -inl := lifted_negative_differential

example : (F.preimageHomologicalComplexIso raw raw.X componentChart).hom.f (-1) =
    (componentChart (-1)).hom :=
  F.preimageHomologicalComplexIso_hom_f raw raw.X componentChart (-1)

example : ∃ L : CochainComplex.Bounded E,
    (F.mapCochainComplexBounded).essImage (K ⊞ (F.mapCochainComplexBounded).obj L) :=
  CochainComplex.BoundedCofinality.strictCofinal F
    (fun X => ⟨0, F.obj_mem_essImage (X ⊞ F.obj (0 : E))⟩) K

end BoundedAmbientAcyclicNonzeroTests
