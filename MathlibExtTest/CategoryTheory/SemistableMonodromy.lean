/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.MonodromyFiltration
public import MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence
public import MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Provider-free tests for the canonical monodromy and E1 contracts

The zero operator must give the one-jump filtration. A genuine nonzero
square-zero block has weights -1 and 1, with its kernel line in both
steps -1 and 0. The E1 API is checked at a negative filtration index and
positive total degree against the actual consecutive-step cone.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.CategoryTheory.SemistableMonodromy

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.CategoryTheory.MonodromyFiltration
open MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence

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

example : coreE1.i₀ 3 (-2, 3) = OrderDual.toDual (1 : ℤ) := rfl
example : coreE1.i₁ (-2, 3) = OrderDual.toDual (-1 : ℤ) := rfl
example : coreE1.i₂ (-2, 3) = OrderDual.toDual (-2 : ℤ) := rfl
example : coreE1.i₃ 3 (-2, 3) = OrderDual.toDual (-4 : ℤ) := rfl
example : coreE1.deg (-2, 3) = (1 : ℤ) := rfl

example (F : FilteredObject (CochainComplex (ModuleCat ℚ) ℤ) ℤᵒᵖ) :
    ((spectralSequence F).page 1).X (-2, 3) ≅
      ((HomotopyCategory.homologyFunctor (ModuleCat ℚ) (.up ℤ)
        0).shift (1 : ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat ℚ) (.up ℤ)).obj
          (CochainComplex.mappingCone (F.filtration.diagram.map
            ((homOfLE (show (-2 : ℤ) ≤ -1 by norm_num)).op)))) :=
  firstPageIso F (-2) 3

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
