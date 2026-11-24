/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Subfunctor.Cardinality
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Original-point and double-simplex cardinality consumers

The same native generated subpresheaf retains original sections and operators,
including empty unions and all original bidegrees of an uncurried double
presheaf. A constant one-point zero seed has infinitely many original images.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite Cardinal
open scoped Simplicial

namespace CategoryTheory.Subfunctor.CardinalityTest

variable {C : Type} [SmallCategory C] {F : Cᵒᵖ ⥤ Type u}

/-- One actual generated subfunctor retains all original sections and operators. -/
theorem original_sections_and_composites {ι : Type u} {X : ι → Cᵒᵖ}
    {x : ∀ i, F.obj (X i)} {G : Subfunctor F} (h : G.IsGeneratedBy x)
    (i : ι) {U V : Cᵒᵖ} (a : X i ⟶ U) (b : U ⟶ V) :
    x i ∈ G.obj (X i) ∧ F.map (a ≫ b) (x i) ∈ G.obj V ∧
      F.map b (F.map a (x i)) = F.map (a ≫ b) (x i) := by
  refine ⟨h.mem i, h.ofSection_le i V ⟨a ≫ b, rfl⟩, ?_⟩
  rw [Functor.map_comp]
  rfl

/-- An arbitrary empty index has no points in its actual union. -/
theorem empty_union_total_points (S : PEmpty.{u + 1} → Subfunctor F) :
    Cardinal.mk (⨆ i, S i).toFunctor.Elements = 0 := by
  let _ : IsEmpty (⨆ i, S i).toFunctor.Elements := ⟨fun e => by
    let y : F.obj e.obj := e.val.val
    have hx : y ∈ (⨆ i, S i).obj e.obj := e.val.property
    rw [Subfunctor.iSup_obj] at hx
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    exact i.elim⟩
  exact Cardinal.mk_eq_zero _

-- The original double diagram is used through the native product-op equivalence
-- and uncurrying. No designated carrier, enrichment, model or LP is needed.

/-- Every original outer/inner operator is the actual uncurried map. -/
theorem original_bidegree_map
    (D : SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type u)
    {A B : (SimplexCategory × SimplexCategory)ᵒᵖ} (f : A ⟶ B)
    (x : ((prodOpEquiv (C := SimplexCategory) (D := SimplexCategory)).functor ⋙
      Functor.uncurry.obj D).obj A) :
    ((prodOpEquiv (C := SimplexCategory) (D := SimplexCategory)).functor ⋙
      Functor.uncurry.obj D).map f x =
      (D.obj (op B.unop.1)).map f.unop.2.op
        ((D.map f.unop.1.op).app (op A.unop.2) x) := rfl

/-- Regular small-family unions give strict support on the full double site. -/
theorem double_site_generated_small
    (D : SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type u)
    {ι : Type u} (X : ι → (SimplexCategory × SimplexCategory)ᵒᵖ)
    (x : ∀ i, ((prodOpEquiv (C := SimplexCategory) (D := SimplexCategory)).functor ⋙
      Functor.uncurry.obj D).obj (X i))
    {μ : Cardinal.{u}} (hμ : μ.IsRegular) (hω : ℵ₀ < μ)
    (hι : Cardinal.mk ι < μ) :
    let F := (prodOpEquiv (C := SimplexCategory) (D := SimplexCategory)).functor ⋙
      Functor.uncurry.obj D
    let G : Subfunctor F := ⨆ i, Subfunctor.ofSection (x i)
    Cardinal.mk G.toFunctor.Elements < μ ∧
      (∀ i, x i ∈ G.obj (X i)) ∧
      (∀ i U, ∀ a : X i ⟶ U, F.map a (x i) ∈ G.obj U) := by
  dsimp only
  let _ : Countable (SimplexCategory × SimplexCategory)ᵒᵖ :=
    (show Function.Injective
      (fun A : (SimplexCategory × SimplexCategory)ᵒᵖ =>
        (A.unop.1.len, A.unop.2.len)) from by
      intro A B h
      apply congrArg op
      apply _root_.Prod.ext
      · exact congrArg SimplexCategory.mk (congrArg (fun p : ℕ × ℕ => p.1) h)
      · exact congrArg SimplexCategory.mk (congrArg (fun p : ℕ × ℕ => p.2) h)).countable
  let _ (A B : (SimplexCategory × SimplexCategory)ᵒᵖ) :
      Countable (A ⟶ B) :=
    Countable.of_equiv
      ((B.unop.1 ⟶ A.unop.1) × (B.unop.2 ⟶ A.unop.2)) (opEquiv A B).symm
  have hOrbit (i : ι) :
      Cardinal.mk (Subfunctor.ofSection (x i)).toFunctor.Elements < μ := by
    have hOps : Cardinal.mk (ULift.{u}
        (Σ U : (SimplexCategory × SimplexCategory)ᵒᵖ, X i ⟶ U)) ≤ ℵ₀ :=
      Cardinal.mk_le_aleph0
    exact (Subfunctor.mk_elements_ofSection_le (x i)).trans_lt (hOps.trans_lt hω)
  refine ⟨Subfunctor.mk_elements_iSup_lt_of_isRegular
      (fun i => Subfunctor.ofSection (x i)) hμ hι hOrbit, ?_, ?_⟩
  · intro i
    exact (le_iSup (fun i => Subfunctor.ofSection (x i)) i) _
      (Subfunctor.mem_ofSection_obj (x i))
  · intro i U a
    exact (le_iSup (fun i => Subfunctor.ofSection (x i)) i) _ ⟨a, rfl⟩

/-- A zero-bidegree seed has infinitely many original degenerate images. -/
theorem nonfinite_zero_seed_orbit :
    let F := (Functor.const (SimplexCategory × SimplexCategory)ᵒᵖ).obj
      PUnit.{u + 1}
    let X₀ : (SimplexCategory × SimplexCategory)ᵒᵖ := op (⦋0⦌, ⦋0⦌)
    let x : F.obj X₀ := PUnit.unit
    ℵ₀ ≤ Cardinal.mk (Subfunctor.ofSection x).toFunctor.Elements := by
  dsimp only
  let F := (Functor.const (SimplexCategory × SimplexCategory)ᵒᵖ).obj
    PUnit.{u + 1}
  let X₀ : (SimplexCategory × SimplexCategory)ᵒᵖ := op (⦋0⦌, ⦋0⦌)
  let x : F.obj X₀ := PUnit.unit
  let φ : ULift.{u} ℕ → (Subfunctor.ofSection x).toFunctor.Elements := fun n =>
    Functor.elementsMk (Subfunctor.ofSection x).toFunctor (op (⦋n.down⦌, ⦋0⦌))
      ⟨PUnit.unit, ⟨Quiver.Hom.op (CategoryTheory.Prod.mkHom
        (SimplexCategory.isTerminalZero.from ⦋n.down⦌)
        (𝟙 (⦋0⦌ : SimplexCategory))), rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro a b h
    apply ULift.ext
    exact congrArg (fun e => e.obj.unop.1.len) h
  have hCard := Cardinal.mk_le_of_injective hφ
  change ℵ₀ ≤ _ at hCard
  exact hCard

end CategoryTheory.Subfunctor.CardinalityTest
