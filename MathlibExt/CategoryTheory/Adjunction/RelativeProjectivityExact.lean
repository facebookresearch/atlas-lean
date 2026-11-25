/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivity
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Relative projectivity and split exact sequences

Relative projectivity can be tested on exact short complexes whose image under the given functor
splits. Preservation of the displayed kernels relates this test to the lifting property for all
morphisms split after applying the functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
universe uC vC uD vD

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (U : C ⥤ D) [U.PreservesZeroMorphisms]

/-- Lifting through exact short complexes that split after applying `U`. -/
def IsRelativeProjectiveExact (P : C) : Prop :=
  ∀ (S : ShortComplex C) (f : P ⟶ S.X₃), S.Exact →
    Nonempty (S.map U).Splitting → ∃ l : P ⟶ S.X₂, l ≫ S.g = f

/-- Full relative projectivity lifts against every mapped split exact short complex. -/
theorem IsRelativeProjective.exactShortComplex {P : C} (hP : U.IsRelativeProjective P) :
    U.IsRelativeProjectiveExact P := by
  intro S f _hExact hSplit
  obtain ⟨s⟩ := hSplit
  exact hP S.g s.splitEpi_g f

/--
Preservation of the kernel and a section of the mapped morphism give a splitting of the kernel sequence.
-/
noncomputable def kernelSplittingOfSplitEpi {X Y : C} (g : X ⟶ Y)
    (s : SplitEpi (U.map g)) [PreservesLimit (parallelPair g 0) U] :
    ((ShortComplex.mk (kernel.ι g) g (kernel.condition g)).map U).Splitting := by
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hk : IsLimit (KernelFork.ofι (U.map (kernel.ι g))
      (show U.map (kernel.ι g) ≫ U.map g = 0 by
        rw [← U.map_comp, kernel.condition, U.map_zero])) :=
    KernelFork.mapIsLimit (KernelFork.ofι (kernel.ι g) (kernel.condition g))
      (kernelIsKernel g) U
  have hExact : (S.map U).Exact :=
    ShortComplex.exact_of_f_is_kernel (S.map U) hk
  have hMono : Mono (S.map U).f := mono_of_isLimit_fork hk
  exact ShortComplex.Splitting.ofExactOfSection (S.map U) hExact s.section_ s.id hMono

/-- The constructed mapped kernel splitting retains the prescribed section. -/
@[simp]
theorem kernelSplittingOfSplitEpi_s {X Y : C} (g : X ⟶ Y)
    (s : SplitEpi (U.map g)) [PreservesLimit (parallelPair g 0) U] :
    (kernelSplittingOfSplitEpi U g s).s = s.section_ := rfl

/-- Exact-short-complex lifting is the full relative property under the displayed kernel preservation. -/
theorem isRelativeProjectiveExact_iff (P : C)
    (hU : ∀ {X Y : C} (g : X ⟶ Y), SplitEpi (U.map g) →
      PreservesLimit (parallelPair g 0) U) :
    U.IsRelativeProjectiveExact P ↔ U.IsRelativeProjective P := by
  constructor
  · intro hP X Y g s f
    let : PreservesLimit (parallelPair g 0) U := hU g s
    let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
    exact hP S f (ShortComplex.exact_kernel g)
      ⟨kernelSplittingOfSplitEpi U g s⟩
  · intro hP
    exact Functor.IsRelativeProjective.exactShortComplex U hP

end CategoryTheory.Functor
