/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.MonodromyFiltration
public import MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Tests for the monodromy filtration

The zero operator gives the one-jump filtration. A nonzero square-zero block has weights -1 and 1,
with its kernel line in both steps -1 and 0. Two checks of the unit and constant scalars of the
coefficient-ring modules follow.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.CategoryTheory.SemistableMonodromy

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.CategoryTheory.MonodromyFiltration

private abbrev V := ModuleCat.of ℚ (ℚ × ℚ)

private def block : End V := End.of (ModuleCat.ofHom
  { toFun x := (x.2, 0)
    map_add' x y := by ext <;> simp
    map_smul' a x := by ext <;> simp })

example : block ^ 2 = 0 := by
  apply End.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨a, b⟩
  rfl

example : block ≠ 0 := by
  intro h
  have hx := congrArg (fun f : End V ↦ f.asHom.hom (0, 1)) h
  have h1 : (1 : ℚ) = 0 := congrArg Prod.fst hx
  exact one_ne_zero h1

example : step (0 : End V) 0 (-1) = ⊥ := by
  simp [step]

example : step (0 : End V) 0 0 = ⊤ := by
  simpa [step, imageSubobject_mono, Subobject.mk_eq_top_of_isIso] using
    Finset.sup_const
      (show (Finset.univ : Finset (Fin 1 × Fin 1)).Nonempty from
        ⟨(0, 0), Finset.mem_univ _⟩) (⊤ : Subobject V)

private theorem block_image_kernel :
    imageSubobject block.asHom = kernelSubobject block.asHom := by
  let S : ShortComplex (ModuleCat ℚ) :=
    ShortComplex.mk block.asHom block.asHom (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rcases x with ⟨a, b⟩
      rfl)
  apply (S.exact_iff_image_eq_kernel).mp
  apply (S.moduleCat_exact_iff_range_eq_ker).mpr
  ext x
  rcases x with ⟨a, b⟩
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, hy⟩
    change (y.2, 0) = (a, b) at hy
    have hb : b = 0 := (congrArg Prod.snd hy).symm
    change (b, 0) = (0, 0)
    rw [hb]
  · intro h
    change (b, 0) = (0, 0) at h
    have hb : b = 0 := congrArg Prod.fst h
    refine ⟨(0, a), ?_⟩
    change (a, 0) = (a, b)
    rw [hb]

example : step block 1 (-1) = kernelSubobject block.asHom := by
  apply le_antisymm
  · unfold step
    apply Finset.sup_le
    intro ij hij
    have hi := ij.1.isLt
    have hj := ij.2.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    have h0 : ij.1.val = 0 := by omega
    have h1 : ij.2.val = 1 := by omega
    simp [h0, h1, block_image_kernel]
  · unfold step
    apply Finset.le_sup_of_le (b := (0, 1))
    · simp
    · simp [block_image_kernel]

example : step block 1 0 = kernelSubobject block.asHom := by
  apply le_antisymm
  · unfold step
    apply Finset.sup_le
    intro ij hij
    have hi := ij.1.isLt
    have hj := ij.2.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    by_cases h0 : ij.1.val = 0
    · simp [h0]
    · have h1 : ij.2.val = 1 := by omega
      simp [h1, block_image_kernel]
  · unfold step
    apply Finset.le_sup_of_le (b := (0, 1))
    · simp
    · simp [block_image_kernel]

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules

example (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    (X : Scheme) (U : X.ProEtᵒᵖ)
    (a : ((underlying E X).obj
      (SheafOfModules.unit (coefficientRing E X))).obj.obj U) :
    ((unitUnderlyingIso E X).hom.hom.app U).hom a = a := rfl

example (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    (X : Scheme) (a : E) (x : (⊤_ X.ProEt).left) :
    (show C((⊤_ X.ProEt).left, ULift.{1} E) from constantScalars E X a) x =
      ULift.up a := rfl

end MathlibExtTest.CategoryTheory.SemistableMonodromy
