/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeInjectivity
public import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivityExact
public import MathlibExt.CategoryTheory.Functor.Opposite
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Relative injectivity and split exact sequences

Relative injectivity can be tested on exact short complexes whose image under the given functor
splits. Preservation of the displayed cokernels relates this test to extension across all
morphisms split after applying the functor. The proof uses opposite short complexes and the
relative projectivity characterization.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
universe uC vC uD vD

namespace CategoryTheory.Functor


variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (U : C ⥤ D) [U.PreservesZeroMorphisms]




/-- Every map into `P` extends over every exact short complex with a full `U`-splitting. -/
def IsRelativeInjectiveExact (P : C) : Prop :=
  ∀ (S : ShortComplex C) (f : S.X₁ ⟶ P), S.Exact →
    Nonempty (S.map U).Splitting → ∃ e : S.X₂ ⟶ P, S.f ≫ e = f

/-- Opposites transport the complete exact-short-complex test and both splitting maps. -/
theorem isRelativeInjectiveExact_iff_op_isRelativeProjectiveExact (P : C) :
    U.IsRelativeInjectiveExact P ↔ U.op.IsRelativeProjectiveExact (Opposite.op P) := by
  constructor
  · intro hP S f hExact hSplit
    obtain ⟨s⟩ := hSplit
    obtain ⟨e, he⟩ := hP S.unop f.unop hExact.unop ⟨s.unop⟩
    let e' : Opposite.unop S.X₂ ⟶ P := e
    have he' : S.g.unop ≫ e' = f.unop := he
    refine ⟨e'.op, ?_⟩
    exact Quiver.Hom.unop_inj (by
      simpa only [unop_comp, Quiver.Hom.unop_op] using he')
  · intro hP S f hExact hSplit
    obtain ⟨s⟩ := hSplit
    obtain ⟨e, he⟩ := hP S.op f.op hExact.op ⟨s.op⟩
    let e' : Opposite.op P ⟶ Opposite.op S.X₂ := e
    have he' : e' ≫ S.f.op = f.op := he
    refine ⟨e'.unop, ?_⟩
    exact Quiver.Hom.op_inj (by
      simpa only [op_comp, Quiver.Hom.op_unop] using he')

/-- Full relative injectivity supplies the split-exact short-complex extension property. -/
theorem IsRelativeInjective.exactShortComplex {P : C} (hP : U.IsRelativeInjective P) :
    U.IsRelativeInjectiveExact P := by
  exact (isRelativeInjectiveExact_iff_op_isRelativeProjectiveExact U P).mpr
    (Functor.IsRelativeProjective.exactShortComplex U.op
      ((Functor.isRelativeInjective_iff_op_isRelativeProjective U P).mp hP))

private theorem relativeInjectivityExactPreservesKernelOp {X Y : Cᵒᵖ} (g : X ⟶ Y)
    [PreservesColimit (parallelPair g.unop 0) U] :
    PreservesLimit (parallelPair g 0) U.op := by
  let q := cokernel.π g.unop
  let w : q.op ≫ g = 0 := by
    change (cokernel.π g.unop).op ≫ g.unop.op = 0
    rw [← op_comp, cokernel.condition, op_zero]
  let c : KernelFork g := KernelFork.ofι q.op w
  have hc : IsLimit c :=
    CokernelCofork.IsColimit.ofπOp q (cokernel.condition g.unop)
      (cokernelIsCokernel g.unop)
  have hw : U.map g.unop ≫ U.map q = 0 := by
    rw [← U.map_comp, cokernel.condition, U.map_zero]
  have hq : IsColimit (CokernelCofork.ofπ (U.map q) hw) :=
    CokernelCofork.mapIsColimit
      (CokernelCofork.ofπ q (cokernel.condition g.unop))
      (cokernelIsCokernel g.unop) U
  have hmap : IsLimit (c.map U.op) :=
    CokernelCofork.IsColimit.ofπOp (U.map q) hw hq
  exact preservesLimit_of_preserves_limit_cone hc
    ((c.isLimitMapConeEquiv U.op).symm hmap)

/-- Pointwise cokernel preservation identifies the full relative and exact-test properties. -/
theorem isRelativeInjectiveExact_iff (P : C)
    (hU : ∀ {X Y : C} (g : X ⟶ Y), SplitMono (U.map g) →
      PreservesColimit (parallelPair g 0) U) :
    U.IsRelativeInjectiveExact P ↔ U.IsRelativeInjective P := by
  have hUop : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y), SplitEpi (U.op.map g) →
      PreservesLimit (parallelPair g 0) U.op := by
    intro X Y g s
    let t : SplitMono (U.map g.unop) :=
      { retraction := s.section_.unop
        id := Quiver.Hom.op_inj (by simp) }
    let _ : PreservesColimit (parallelPair g.unop 0) U := hU g.unop t
    exact relativeInjectivityExactPreservesKernelOp U g
  calc
    U.IsRelativeInjectiveExact P ↔ U.op.IsRelativeProjectiveExact (Opposite.op P) :=
      isRelativeInjectiveExact_iff_op_isRelativeProjectiveExact U P
    _ ↔ U.op.IsRelativeProjective (Opposite.op P) :=
      Functor.isRelativeProjectiveExact_iff U.op (Opposite.op P) hUop
    _ ↔ U.IsRelativeInjective P :=
      (Functor.isRelativeInjective_iff_op_isRelativeProjective U P).symm

end CategoryTheory.Functor
