/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetSquareTransport
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Weak fibrations detected on the original same-base fibres

For original fibrations over one base, a fibration between them is a global
realization weak equivalence exactly when every original strict fibre map is.
No ambient Kan or properness hypothesis is needed. Every original boundary
square is reduced to constant base, including dimension zero.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- The native same-base fibre map retains its original inclusion pullback. -/
theorem sameBase_mapFiber_isPullback {E D B : SSet.{u}}
    (p : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : p ≫ t = s)
    (b : B _⦋0⦌) :
    IsPullback (Subcomplex.fiber s b).ι
      (Subcomplex.mapFiber (f := s) (f' := t) p (𝟙 B)
        (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl)
      p (Subcomplex.fiber t b).ι := by
  let η := Subcomplex.mapFiber (f := s) (f' := t) p (𝟙 B)
    (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl
  let a := IsTerminal.from stdSimplex.isTerminalObj₀ (Subcomplex.fiber s b : SSet.{u})
  let c := IsTerminal.from stdSimplex.isTerminalObj₀ (Subcomplex.fiber t b : SSet.{u})
  have outer : IsPullback (Subcomplex.fiber s b).ι a (p ≫ t)
      (const (X := Δ[0]) b) := by
    simpa only [h] using Subcomplex.fiber_isPullback s b
  have ha : a = η ≫ c := stdSimplex.isTerminalObj₀.hom_ext _ _
  have inner : IsPullback η (Subcomplex.fiber s b).ι (Subcomplex.fiber t b).ι p :=
    IsPullback.of_right (h₁₂ := c) (h₂₁ := p) (h₂₂ := t)
      (v₁₂ := (Subcomplex.fiber t b).ι)
      (v₁₃ := const (X := Δ[0]) b) (ha ▸ outer.flip)
      (Subcomplex.mapFiber_ι p (𝟙 B) (h.trans (Category.comp_id s).symm) rfl)
      (Subcomplex.fiber_isPullback t b).flip
  exact inner.flip

private theorem fibreMap_fibration {E D B : SSet.{u}}
    (p : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : p ≫ t = s)
    [Fibration p] (b : B _⦋0⦌) :
    Fibration (Subcomplex.mapFiber (f := s) (f' := t) p (𝟙 B)
      (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl) := by
  apply (modelCategoryQuillen.fibration_iff _).mpr
  exact (modelCategoryQuillen.J.{u}.rlp).of_isPullback
    (sameBase_mapFiber_isPullback p s t h b)
    ((modelCategoryQuillen.fibration_iff p).mp inferInstance)

/-- An original fibration between fibrations over the same base is weak
exactly when all of its original strict-fibre maps are weak. -/
theorem realizationWeakEquivalence_iff_fibrewise_of_fibrations
    {E D B : SSet.{u}} (p : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B)
    (h : p ≫ t = s) [Fibration p] [Fibration t] :
    realizationWeakEquivalences p ↔
      ∀ b : B _⦋0⦌, realizationWeakEquivalences
        (Subcomplex.mapFiber (f := s) (f' := t) p (𝟙 B)
          (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl) := by
  let : Fibration s := by rw [← h]; infer_instance
  constructor
  · intro hp b
    let η := Subcomplex.mapFiber (f := s) (f' := t) p (𝟙 B)
      (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl
    let : Fibration η := fibreMap_fibration p s t h b
    have hpI := (modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mpr hp
    have hηI : modelCategoryQuillen.I.{u}.rlp η :=
      (modelCategoryQuillen.I.{u}.rlp).of_isPullback
        (sameBase_mapFiber_isPullback p s t h b) hpI
    exact (modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration η).mp hηI
  · intro hfib
    apply (modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mp
    intro A A' i hi
    cases hi with
    | mk n =>
      constructor
      intro top bottom sq₀
      obtain ⟨y, top₁, sq₁, htop, hlift⟩ := CommSq.exists_const_base_reduction sq₀
      let b := t.app (op ⦋0⦌) y
      let η := Subcomplex.mapFiber (f := s) (f' := t) p (𝟙 B)
        (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl
      let : Fibration η := fibreMap_fibration p s t h b
      have hηI := (modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration η).mpr
        (hfib b)
      have topBase : top₁ ≫ s = const b := by
        rw [← h, ← Category.assoc, htop, const_comp]
      have bottomBase : (const (X := Δ[n]) y) ≫ t = const b := const_comp _ _
      let a := (Subcomplex.fiber s b).lift top₁
        ((Subcomplex.range_le_fiber_iff s b top₁).mpr topBase)
      let d := (Subcomplex.fiber t b).lift (const (X := Δ[n]) y)
        ((Subcomplex.range_le_fiber_iff t b _).mpr bottomBase)
      have square : CommSq a (boundary n).ι η d := by
        constructor
        apply (cancel_mono (Subcomplex.fiber t b).ι).mp
        dsimp only [a, d, η]
        simp only [Category.assoc, Subcomplex.lift_ι, Subcomplex.mapFiber_ι]
        exact sq₁.w
      let : HasLiftingProperty (boundary n).ι η := hηI _ (by constructor)
      let l := square.lift
      have hl := square.fac_left
      have hr := square.fac_right
      apply hlift.mpr
      refine CommSq.HasLift.mk' ⟨l ≫ (Subcomplex.fiber s b).ι, ?_, ?_⟩
      · rw [← Category.assoc]
        change (boundary n).ι ≫ square.lift ≫ (Subcomplex.fiber s b).ι = top₁
        rw [← Category.assoc, hl]
        exact Subcomplex.lift_ι _ _
      · rw [Category.assoc, ← Subcomplex.mapFiber_ι p (𝟙 B)
          (h.trans (Category.comp_id s).symm) rfl, ← Category.assoc]
        change square.lift ≫ η ≫ (Subcomplex.fiber t b).ι = const y
        rw [← Category.assoc, hr]
        exact Subcomplex.lift_ι _ _

/-- The same original strict-fibre map is a full Kan weak equivalence. -/
theorem sameBase_mapFiber_W {E D B : SSet.{u}}
    (p : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : p ≫ t = s)
    [Fibration p] [Fibration t] (hp : realizationWeakEquivalences p)
    (b : B _⦋0⦌) :
    KanComplex.W (Subcomplex.mapFiber (f := s) (f' := t) p (𝟙 B)
      (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl) := by
  let : Fibration s := by rw [← h]; infer_instance
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr
    ((realizationWeakEquivalence_iff_fibrewise_of_fibrations p s t h).mp hp b)

end SSet
