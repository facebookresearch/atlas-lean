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

public import MathlibExt.Algebra.Homology.ExactSequenceFour
public import MathlibExt.Algebra.Homology.ShortComplex.KernelSequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.NormNum

/-!
# Exact-row recovery and an epimorphism with nonacyclic kernel

The split row `0 → ℤ → ℤ × ℤ → ℤ → 0` recovers the inclusion and projection from its extracted
short exact sequence. Evaluations on three and on `(2,3)` check the actual quotient and kernel
maps.

The degreewise projection from the zero-differential integer-product complex onto the integer
complex is an epimorphism. Its kernel has a degree-zero homology class detected as `(1,0)` by
the kernel inclusion, so the acyclic-kernel criterion proves that this epimorphism is not a
quasi-isomorphism. Degree zero has no outgoing relation in the nonnegative chain shape.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows HomologicalComplex
open scoped ZeroObject

namespace MathlibExtTest.ExactFourKernel

private abbrev E := ModuleCat.{0} ℤ
private abbrev N : E := ModuleCat.of ℤ ℤ
private abbrev P : E := ModuleCat.of ℤ (ℤ × ℤ)
private abbrev Z : E := 0

private def inclusion : N ⟶ P := ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)
private def projection : P ⟶ N := ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ)

private instance : Mono inclusion := (ModuleCat.mono_iff_injective _).mpr (by
  intro x y h
  exact congrArg Prod.fst h)

private instance : Epi projection := (ModuleCat.epi_iff_surjective _).mpr (fun x =>
  ⟨(0, x), rfl⟩)

private abbrev row : ComposableArrows E 4 :=
  mk₄ (0 : Z ⟶ N) inclusion projection (0 : N ⟶ Z)

private theorem row_complex : row.IsComplex where
  zero i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · change (0 : Z ⟶ N) ≫ inclusion = 0
      simp
    · change inclusion ≫ projection = 0
      ext x
      rfl
    · change projection ≫ (0 : N ⟶ Z) = 0
      simp

private theorem row_exact : row.Exact where
  toIsComplex := row_complex
  exact i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · change (ShortComplex.mk (0 : Z ⟶ N) inclusion (by simp)).Exact
      exact (ShortComplex.exact_iff_mono _ rfl).mpr (by infer_instance)
    · change (ShortComplex.mk inclusion projection (by ext x; rfl)).Exact
      apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      intro x
      change x.2 = 0 ↔ ∃ y : ℤ, (y, 0) = x
      constructor
      · intro h
        exact ⟨x.1, Prod.ext rfl h.symm⟩
      · rintro ⟨y, h⟩
        exact (congrArg Prod.snd h).symm
    · change (ShortComplex.mk projection (0 : N ⟶ Z) (by simp)).Exact
      exact (ShortComplex.exact_iff_epi _ rfl).mpr (by infer_instance)

private abbrev extracted := exactSequenceFourShortComplex row row_exact

example : extracted.ShortExact := exactSequenceFourShortComplex_shortExact row row_exact

example : extracted.f.hom ((cokernel.π (row.map' 0 1)).hom (3 : ℤ)) = (3, 0) := by
  have h := exactSequenceFourShortComplex_π_f row row_exact
  change cokernel.π (row.map' 0 1) ≫ extracted.f = inclusion at h
  exact ConcreteCategory.congr_hom h (3 : ℤ)

example : (kernel.ι (row.map' 3 4)).hom (extracted.g.hom (2, 3)) = (3 : ℤ) := by
  have h := exactSequenceFourShortComplex_g_ι row row_exact
  change extracted.g ≫ kernel.ι (row.map' 3 4) = projection at h
  exact ConcreteCategory.congr_hom h ((2 : ℤ), (3 : ℤ))

private abbrev scalarComplex : ChainComplex E ℕ :=
  ChainComplex.of (fun _ => N) (fun _ => 0) (by intro n; simp)

private abbrev productComplex : ChainComplex E ℕ :=
  ChainComplex.of (fun _ => P) (fun _ => 0) (by intro n; simp)

private theorem scalar_d_zero (i j : ℕ) : scalarComplex.d i j = 0 := by
  simp [scalarComplex, ChainComplex.of.d]

private theorem product_d_zero (i j : ℕ) : productComplex.d i j = 0 := by
  simp [productComplex, ChainComplex.of.d]

private def epimorphism : productComplex ⟶ scalarComplex :=
  ChainComplex.ofHom (fun _ => projection) (by
    intro n
    rw [scalar_d_zero, product_d_zero]
    simp)

private instance : Epi epimorphism :=
  HomologicalComplex.epi_of_epi_f _ (fun _ => inferInstanceAs (Epi projection))

private def kernelGeneratorMap : scalarComplex ⟶ kernel epimorphism :=
  kernel.lift epimorphism
    (ChainComplex.ofHom (fun _ => inclusion) (by
      intro n
      rw [scalar_d_zero, product_d_zero]
      simp)) (by
      ext n x
      rfl)

private theorem kernel_d_zero (i j : ℕ) : (kernel epimorphism).d i j = 0 := by
  apply (cancel_mono ((kernel.ι epimorphism).f j)).mp
  rw [zero_comp, ← (kernel.ι epimorphism).comm i j, product_d_zero, comp_zero]

private def kernelCoordinate : (kernel epimorphism).homology 0 ≅ (kernel epimorphism).X 0 :=
  (ShortComplex.HomologyData.ofZeros ((kernel epimorphism).sc 0)
    (kernel_d_zero _ _) (kernel_d_zero _ _)).left.homologyIso

private def kernelOne : (kernel epimorphism).homology 0 :=
  kernelCoordinate.inv.hom ((kernelGeneratorMap.f 0).hom 1)

private theorem kernelOne_value :
    ((kernel.ι epimorphism).f 0).hom (kernelCoordinate.hom.hom kernelOne) = (1, 0) := by
  rw [kernelOne, ModuleCat.hom_inv_apply]
  have h := congrArg (fun f : scalarComplex ⟶ productComplex => f.f 0)
    (kernel.lift_ι epimorphism
      (ChainComplex.ofHom (fun _ => inclusion) (by
        intro n
        rw [scalar_d_zero, product_d_zero]
        simp)) (by ext n x; rfl))
  exact ConcreteCategory.congr_hom h 1

private theorem kernelOne_ne_zero : kernelOne ≠ 0 := by
  intro hzero
  have h := congrArg (fun x => ((kernel.ι epimorphism).f 0).hom
    (kernelCoordinate.hom.hom x)) hzero
  rw [kernelOne_value, map_zero, map_zero] at h
  have hf := congrArg Prod.fst h
  change (1 : ℤ) = 0 at hf
  norm_num at hf

example : ((epimorphism.f 0).hom (2, 3)) = 3 := rfl

example : ∀ j : ℕ, ¬ (ComplexShape.down ℕ).Rel 0 j := by
  intro j h
  change j + 1 = 0 at h
  omega

example : ¬ (kernel epimorphism).Acyclic := by
  intro h
  have hz := (h 0).isZero_homology
  let _ : Subsingleton ((kernel epimorphism).homology 0) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact kernelOne_ne_zero (Subsingleton.elim _ _)

example : ¬ QuasiIso epimorphism := by
  intro h
  have hk := (HomologicalComplex.quasiIso_iff_acyclic_kernel epimorphism).mp h
  have hz := (hk 0).isZero_homology
  let _ : Subsingleton ((kernel epimorphism).homology 0) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact kernelOne_ne_zero (Subsingleton.elim _ _)

end MathlibExtTest.ExactFourKernel
