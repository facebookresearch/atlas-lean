/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexFirstContraction
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv

/-!
# Simplicial Whitehead theorem for Kan complexes

This file specializes the generic model-categorical Whitehead theorem to
Kan complexes and converts its two left-homotopy relations into literal
simplicial homotopies through the standard cylinder `X ⊗ Δ[1]`.

The standard cylinder is proved good independently: its projection is a
realization weak equivalence by the first-vertex contraction of `Δ[1]`, and
its codiagonal inclusion is degreewise injective. The selected Kan--Quillen
model is opened only lexically around the private cylinder packaging and the
public proof.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomotopicalAlgebra Limits CartesianMonoidalCategory Opposite
open scoped Simplicial MonoidalCategory

universe u

namespace SSet.KanComplex

/-- The standard cylinder projection followed by its first-vertex section is
simplicially homotopic to the identity, with the `X` coordinate fixed. -/
private noncomputable def standardCylinderProjectionHomotopy (X : SSet.{u}) :
    SSet.Homotopy
      ((fst X (Δ[1] : SSet.{u})) ≫ SSet.ι₀)
      (𝟙 (X ⊗ (Δ[1] : SSet.{u}))) where
  h :=
    lift
      (fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) ≫
        fst X (Δ[1] : SSet.{u}))
      ((snd X (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        (SSet.stdSimplex.homotopyConstFirstId.{u} 1).h)
  h₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp
  h₁ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp
  rel := by
    ext a ⟨⟨x, hx⟩, t⟩
    all_goals
      have hx' : x ∈ (∅ : Set ((X ⊗ (Δ[1] : SSet.{u})).obj a)) := by
        simpa using hx
      have : False := (Set.mem_empty_iff_false x).mp hx'
      exact this.elim

/-- The projection of the standard cylinder is a realization weak
equivalence, independently of the Whitehead theorem proved below. -/
private theorem standardCylinderProjection_mem_realizationWeakEquivalences
    (X : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (fst X (Δ[1] : SSet.{u})) := by
  let p : X ⊗ (Δ[1] : SSet.{u}) ⟶ X := fst X (Δ[1] : SSet.{u})
  let s : X ⟶ X ⊗ (Δ[1] : SSet.{u}) := SSet.ι₀
  have hps : SSet.Homotopy (p ≫ s) (𝟙 _) :=
    standardCylinderProjectionHomotopy X
  have hsp : SSet.Homotopy (s ≫ p) (𝟙 _) := by
    rw [SSet.ι₀_fst]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 X))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 X))
    exact SSet.RelativeMorphism.Homotopy.refl _
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map p)
  exact TopCat.mem_of_eq_toFun
    (SSet.realizedHomotopyEquiv _ _ p s hps hsp) rfl

/-- The underlying standard precylinder. -/
private noncomputable def standardPrecylinder (X : SSet.{u}) :
    Precylinder X where
  I := X ⊗ (Δ[1] : SSet.{u})
  i₀ := SSet.ι₀
  i₁ := SSet.ι₁
  π := fst X (Δ[1] : SSet.{u})

/-- The standard precylinder codiagonal is degreewise injective. -/
private theorem standardPrecylinder_i_mono (X : SSet.{u}) :
    Mono (standardPrecylinder X).i := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  induction n using Opposite.rec with
  | _ n =>
    induction n using SimplexCategory.rec with
    | _ m =>
      rw [mono_iff_injective]
      intro a b hab
      let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋m⦌)
      let hc : IsColimit (BinaryCofan.mk
          ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌))
          ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌))) :=
        mapIsColimitOfPreservesOfIsColimit ev _ _ (coprodIsCoprod X X)
      have hLeft (z : X.obj (op ⦋m⦌)) :
          (standardPrecylinder X).i.app (op ⦋m⦌)
              ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌) z) =
            SSet.ι₀.app (op ⦋m⦌) z := by
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (standardPrecylinder X).inl_i (op ⦋m⦌)) z
      have hRight (z : X.obj (op ⦋m⦌)) :
          (standardPrecylinder X).i.app (op ⦋m⦌)
              ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌) z) =
            SSet.ι₁.app (op ⦋m⦌) z := by
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (standardPrecylinder X).inr_i (op ⦋m⦌)) z
      obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hc a
      obtain ⟨k, y, hy⟩ := Types.jointly_surjective_of_isColimit hc b
      rcases j with (_ | _) <;> rcases k with (_ | _)
      · have hx' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hLeft x, hLeft y] at hab
        have hxy : x = y := congrArg Prod.fst hab
        subst y
        rfl
      · have hx' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hLeft x, hRight y] at hab
        have h01 : (0 : Fin 2) = 1 := congrArg (fun z => z.2 0) hab
        exact (zero_ne_one h01).elim
      · have hx' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hRight x, hLeft y] at hab
        have h10 : (1 : Fin 2) = 0 := congrArg (fun z => z.2 0) hab
        exact (one_ne_zero h10).elim
      · have hx' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hRight x, hRight y] at hab
        have hxy : x = y := congrArg Prod.fst hab
        subst y
        rfl

open scoped SSet.modelCategoryQuillen in
/-- The standard simplicial cylinder in the selected model structure. -/
private noncomputable def standardCylinder (X : SSet.{u}) : Cylinder X where
  __ := standardPrecylinder X
  weakEquivalence_π := by
    rw [weakEquivalence_iff]
    exact standardCylinderProjection_mem_realizationWeakEquivalences X

open scoped SSet.modelCategoryQuillen in
/-- The canonical simplicial cylinder has underlying object `X ⊗ Δ[1]`.
Its projection is weak and its endpoint coproduct is a cofibration. -/
abbrev _root_.SSet.modelCategoryQuillen.standardCylinder (X : SSet.{u}) : Cylinder X where
  I := X ⊗ (Δ[1] : SSet.{u})
  i₀ := SSet.ι₀
  i₁ := SSet.ι₁
  π := fst X (Δ[1] : SSet.{u})
  weakEquivalence_π := by
    rw [weakEquivalence_iff]
    exact standardCylinderProjection_mem_realizationWeakEquivalences X

open scoped SSet.modelCategoryQuillen in
/-- The canonical cylinder's object is the actual tensor with the simplicial interval. -/
@[simp]
theorem _root_.SSet.modelCategoryQuillen.standardCylinder_I (X : SSet.{u}) :
    (SSet.modelCategoryQuillen.standardCylinder X).I = X ⊗ (Δ[1] : SSet.{u}) := rfl

open scoped SSet.modelCategoryQuillen in
/-- The canonical cylinder starts at the actual first-vertex inclusion. -/
@[simp]
theorem _root_.SSet.modelCategoryQuillen.standardCylinder_i₀ (X : SSet.{u}) :
    (SSet.modelCategoryQuillen.standardCylinder X).i₀ = SSet.ι₀ (X := X) := rfl

open scoped SSet.modelCategoryQuillen in
/-- The canonical cylinder ends at the actual last-vertex inclusion. -/
@[simp]
theorem _root_.SSet.modelCategoryQuillen.standardCylinder_i₁ (X : SSet.{u}) :
    (SSet.modelCategoryQuillen.standardCylinder X).i₁ = SSet.ι₁ (X := X) := rfl

open scoped SSet.modelCategoryQuillen in
/-- The canonical cylinder projects to its first tensor coordinate. -/
@[simp]
theorem _root_.SSet.modelCategoryQuillen.standardCylinder_π (X : SSet.{u}) :
    (SSet.modelCategoryQuillen.standardCylinder X).π = fst X (Δ[1] : SSet.{u}) := rfl

open scoped SSet.modelCategoryQuillen in
/-- The two actual endpoint inclusions of the standard cylinder form a cofibration. -/
instance _root_.SSet.modelCategoryQuillen.standardCylinder_isGood (X : SSet.{u}) :
    (SSet.modelCategoryQuillen.standardCylinder X).IsGood where
  cofibration_i := by
    rw [cofibration_iff]
    exact standardPrecylinder_i_mono X

open scoped SSet.modelCategoryQuillen in
/-- A generic left-homotopy relation between simplicial maps with cofibrant
source and fibrant target has a literal standard-cylinder representative. -/
private noncomputable def leftHomotopyRelToHomotopy
    {A B : SSet.{u}} [IsCofibrant A] [IsFibrant B]
    {f g : A ⟶ B} (h : LeftHomotopyRel f g) : SSet.Homotopy f g := by
  let P := standardCylinder A
  letI : P.IsGood :=
    { cofibration_i := by
        rw [cofibration_iff]
        exact standardPrecylinder_i_mono A }
  let H := h.leftHomotopy P
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm f)
    (SSet.RelativeMorphism.botEquiv.symm g)
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁
      rel := by
        ext n ⟨⟨x, hx⟩, t⟩
        all_goals simp at hx }

open scoped SSet.modelCategoryQuillen in
/-- A weak equivalence between Kan complexes admits a homotopy inverse with
both composites connected to their literal identities by simplicial
homotopies. -/
theorem W.exists_homotopy_inverse
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} (hf : W f) :
    ∃ g : Y ⟶ X,
      Nonempty (SSet.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ f) (𝟙 Y)) := by
  let _ : WeakEquivalence f := by
    rw [weakEquivalence_iff]
    exact (W_iff_realizationWeakEquivalence f).mp hf
  obtain ⟨g, hfg, hgf⟩ := LeftHomotopyClass.whitehead f
  exact ⟨g, ⟨leftHomotopyRelToHomotopy hfg⟩,
    ⟨leftHomotopyRelToHomotopy hgf⟩⟩

end SSet.KanComplex

end
