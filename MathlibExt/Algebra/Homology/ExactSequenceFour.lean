/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# A short exact sequence extracted from five exact objects

For an exact sequence A₀ → A₁ → A₂ → A₃ → A₄ in an abelian category, the middle arrows induce
a short exact sequence coker(A₀ → A₁) → A₂ → ker(A₃ → A₄).

The first map is the cokernel descent of A₁ → A₂, and the second is the kernel lift of A₂ →
A₃. Their composites with the canonical quotient and inclusion recover the middle arrows.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.ComposableArrows

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short complex from an exact four-arrow sequence.

For five exact objects, take the cokernel of the first arrow, the middle object and the kernel
of the last arrow, with maps induced by the two middle arrows. -/
noncomputable def exactSequenceFourShortComplex
    (S : ComposableArrows C 4) (hS : S.Exact) : ShortComplex C :=
  ShortComplex.mk
    (cokernel.desc (S.map' 0 1) (S.map' 1 2)
      (hS.toIsComplex.zero 0))
    (kernel.lift (S.map' 3 4) (S.map' 2 3)
      (hS.toIsComplex.zero 2))
    (by
      apply (cancel_epi (cokernel.π (S.map' 0 1))).1
      apply (cancel_mono (kernel.ι (S.map' 3 4))).1
      simpa only [Category.assoc, cokernel.π_desc_assoc, kernel.lift_ι,
        comp_zero, zero_comp] using hS.toIsComplex.zero 1)

/-- The first term of the extracted short complex.

The first term is the cokernel of A₀ → A₁. -/
@[simp]
theorem exactSequenceFourShortComplex_X₁
    (S : ComposableArrows C 4) (hS : S.Exact) :
    (exactSequenceFourShortComplex S hS).X₁ =
      cokernel (S.map' 0 1) :=
  rfl

/-- The middle term of the extracted short complex.

The middle term is A₂. -/
@[simp]
theorem exactSequenceFourShortComplex_X₂
    (S : ComposableArrows C 4) (hS : S.Exact) :
    (exactSequenceFourShortComplex S hS).X₂ =
      S.obj ⟨2, by omega⟩ :=
  rfl

/-- The last term of the extracted short complex.

The last term is the kernel of A₃ → A₄. -/
@[simp]
theorem exactSequenceFourShortComplex_X₃
    (S : ComposableArrows C 4) (hS : S.Exact) :
    (exactSequenceFourShortComplex S hS).X₃ =
      kernel (S.map' 3 4) :=
  rfl

/-- The first extracted map is a cokernel descent.

Descend A₁ → A₂ through the cokernel of A₀ → A₁. -/
@[simp]
theorem exactSequenceFourShortComplex_f
    (S : ComposableArrows C 4) (hS : S.Exact) :
    (exactSequenceFourShortComplex S hS).f =
      cokernel.desc (S.map' 0 1) (S.map' 1 2)
        (hS.toIsComplex.zero 0) :=
  rfl

/-- The second extracted map is a kernel lift.

Lift A₂ → A₃ into the kernel of A₃ → A₄. -/
@[simp]
theorem exactSequenceFourShortComplex_g
    (S : ComposableArrows C 4) (hS : S.Exact) :
    (exactSequenceFourShortComplex S hS).g =
      kernel.lift (S.map' 3 4) (S.map' 2 3)
        (hS.toIsComplex.zero 2) :=
  rfl

/-- The extracted cokernel map recovers the second arrow.

The quotient A₁ → coker(A₀ → A₁) followed by the extracted map equals A₁ → A₂. -/
@[reassoc (attr := simp)]
theorem exactSequenceFourShortComplex_π_f
    (S : ComposableArrows C 4) (hS : S.Exact) :
    cokernel.π (S.map' 0 1) ≫
        (exactSequenceFourShortComplex S hS).f =
      S.map' 1 2 := by
  unfold exactSequenceFourShortComplex
  apply cokernel.π_desc

/-- The extracted kernel map recovers the third arrow.

The extracted map A₂ → ker(A₃ → A₄) followed by the kernel inclusion equals A₂ → A₃. -/
@[reassoc (attr := simp)]
theorem exactSequenceFourShortComplex_g_ι
    (S : ComposableArrows C 4) (hS : S.Exact) :
    (exactSequenceFourShortComplex S hS).g ≫
        kernel.ι (S.map' 3 4) =
      S.map' 2 3 := by
  unfold exactSequenceFourShortComplex
  apply kernel.lift_ι

/-- The extracted middle sequence is short exact.

For the exact five-object sequence, coker(A₀ → A₁) → A₂ → ker(A₃ → A₄) is short exact. -/
theorem exactSequenceFourShortComplex_shortExact
    (S : ComposableArrows C 4) (hS : S.Exact) :
    (exactSequenceFourShortComplex S hS).ShortExact := by
  let f := cokernel.desc (S.map' 0 1) (S.map' 1 2)
    (hS.toIsComplex.zero 0)
  let g := kernel.lift (S.map' 3 4) (S.map' 2 3)
    (hS.toIsComplex.zero 2)
  have hfg : f ≫ g = 0 := by
    apply (cancel_epi (cokernel.π (S.map' 0 1))).1
    apply (cancel_mono (kernel.ι (S.map' 3 4))).1
    simpa only [f, g, Category.assoc, cokernel.π_desc_assoc, kernel.lift_ι,
      comp_zero, zero_comp] using hS.toIsComplex.zero 1
  let T := ShortComplex.mk f g hfg
  change T.ShortExact
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro Z y hy
    have hy23 : y ≫ S.map' 2 3 = 0 := by
      change y ≫ g = 0 at hy
      calc
        y ≫ S.map' 2 3 = y ≫ (g ≫ kernel.ι (S.map' 3 4)) := by
          dsimp only [g]
          rw [kernel.lift_ι]
        _ = (y ≫ g) ≫ kernel.ι (S.map' 3 4) := by
          rw [Category.assoc]
        _ = 0 := by rw [hy, zero_comp]
    obtain ⟨Z', p, hp, x, hx⟩ :=
      (hS.exact' 1 2 3).exact_up_to_refinements y hy23
    change p ≫ y = x ≫ S.map' 1 2 at hx
    refine ⟨Z', p, hp, x ≫ cokernel.π (S.map' 0 1), ?_⟩
    calc
      p ≫ y = x ≫ S.map' 1 2 := hx
      _ = x ≫ (cokernel.π (S.map' 0 1) ≫ f) := by
        dsimp only [f]
        rw [cokernel.π_desc]
      _ = (x ≫ cokernel.π (S.map' 0 1)) ≫ f := by
        rw [Category.assoc]
  have hmono : Mono T.f := by
    change Mono f
    exact (hS.exact 0).mono_cokernelDesc
  have hepi : Epi T.g := by
    change Epi g
    exact (hS.exact 2).epi_kernelLift
  exact ShortComplex.ShortExact.mk' hT hmono hepi

end CategoryTheory.ComposableArrows

end
