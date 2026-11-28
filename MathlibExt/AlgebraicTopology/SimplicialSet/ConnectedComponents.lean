/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Connected-component subcomplexes of a simplicial set

For a simplicial set X, the component label of a simplex is the element of π₀(X) represented
by its zeroth vertex. All vertices of that simplex have the same label, so the simplices with
a fixed label c form a subcomplex X_c.

Each X_c is nonempty and connected in the edge-generated sense: its π₀ is a singleton. The
inclusions X_c → X form a coproduct cocone, since in every degree the disjoint union of these
label fibers is bijective to the simplices of X. Thus X is the coproduct of its
connected-component subcomplexes.

The mathematical decomposition follows Joël Riou's
`topcat-model-category` development.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

namespace SSet

variable {X : SSet.{u}}

namespace π₀

private lemma congr_mk_map {n : SimplexCategoryᵒᵖ} (s : X.obj n)
    (α β : ⦋0⦌ ⟶ n.unop) :
    π₀.mk (X.map α.op s) = π₀.mk (X.map β.op s) := by
  obtain ⟨⟨n⟩⟩ := n
  have hα : α = ⦋0⦌.const ⦋n⦌ (α 0) := by
    ext i
    fin_cases i
    rfl
  have hβ : β = ⦋0⦌.const ⦋n⦌ (β 0) := by
    ext i
    fin_cases i
    rfl
  rw [hα, hβ]
  rcases le_total (α 0) (β 0) with h | h
  · apply π₀.sound
    exact Edge.mk (X.map (SimplexCategory.mkOfLe (α 0) (β 0) h).op s)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)
  · symm
    apply π₀.sound
    exact Edge.mk (X.map (SimplexCategory.mkOfLe (β 0) (α 0) h).op s)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)

/-- Subcomplex of simplices in one connected component.

For c ∈ π₀(X), define X_c in degree n by the simplices whose zeroth vertex represents c.
Independence of the chosen vertex makes this family stable under all simplex operators, hence
a subcomplex of X. -/
def component (c : π₀ X) : X.Subcomplex where
  obj n := {s | π₀.mk (X.map (⦋0⦌.const n.unop 0).op s) = c}
  map {n m} f s hs := by
    change π₀.mk (X.map (⦋0⦌.const m.unop 0).op (X.map f s)) = c
    rw [← hs]
    rw [← Functor.map_comp_apply]
    exact congr_mk_map s (⦋0⦌.const m.unop 0 ≫ f.unop)
      (⦋0⦌.const n.unop 0)

@[simp]
private lemma mem_component_zero (c : π₀ X) (x : X _⦋0⦌) :
    x ∈ (component c).obj (op ⦋0⦌) ↔ π₀.mk x = c := by
  simp [component]

private lemma component_mem_of_eqvGen (c : π₀ X) {x y : X _⦋0⦌}
    (h : Relation.EqvGen π₀Rel x y) (hx : x ∈ (component c).obj (op ⦋0⦌)) :
    y ∈ (component c).obj (op ⦋0⦌) := by
  rw [mem_component_zero] at hx ⊢
  exact ((π₀.mk_eq_mk_iff x y).mpr h).symm.trans hx

private lemma component_mk_eq_of_eqvGen (c : π₀ X) {x y : X _⦋0⦌}
    (h : Relation.EqvGen π₀Rel x y)
    (hx : x ∈ (component c).obj (op ⦋0⦌))
    (hy : y ∈ (component c).obj (op ⦋0⦌)) :
    π₀.mk (⟨x, hx⟩ : (component c : SSet) _⦋0⦌) =
      π₀.mk (X := (component c : SSet))
        (⟨y, hy⟩ : (component c : SSet) _⦋0⦌) := by
  induction h with
  | rel x y h =>
      obtain ⟨e⟩ := h
      apply π₀.sound
      have he : e.edge ∈ (component c).obj (op ⦋1⦌) := by
        simp only [component, Set.mem_ofPred_eq]
        rw [← SimplexCategory.δ_one_eq_const]
        change π₀.mk (X.δ 1 e.edge) = c
        rw [e.src_eq]
        exact (mem_component_zero c x).mp hx
      exact (e.toSubcomplex (component c) he).ofEq
        (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)
  | refl => rfl
  | symm x y h ih =>
      exact (ih hy hx).symm
  | trans x y z hxy hyz ihxy ihyz =>
      let hy' := component_mem_of_eqvGen c hxy hx
      exact (ihxy hx hy').trans (ihyz hy' hy)

private instance component_nonempty (c : π₀ X) : (component c : SSet).Nonempty := by
  obtain ⟨x, rfl⟩ := c.mk_surjective
  exact ⟨⟨x, (mem_component_zero _ _).mpr rfl⟩⟩

private instance component_preconnected (c : π₀ X) :
    Subsingleton (π₀ (component c : SSet)) where
  allEq a b := by
    obtain ⟨⟨x, hx⟩, rfl⟩ := a.mk_surjective
    obtain ⟨⟨y, hy⟩, rfl⟩ := b.mk_surjective
    apply component_mk_eq_of_eqvGen c
    rw [← π₀.mk_eq_mk_iff]
    exact ((mem_component_zero c x).mp hx).trans
      ((mem_component_zero c y).mp hy).symm

/-- Connectedness of a component subcomplex.

For c ∈ π₀(X), the simplicial set X_c is nonempty and has singleton π₀. Any two vertices in it
are related by the edge-generated equivalence relation inside the same subcomplex. -/
instance component_isConnected (c : π₀ X) : SSet.IsConnected (component c : SSet) where
  nonempty := inferInstance

variable (X)

/-- Coproduct cocone of connected-component inclusions.

For a simplicial set X, form the cofan indexed by c ∈ π₀(X) with summands X_c, vertex X and
legs the subcomplex inclusions X_c → X. -/
abbrev cofan : Cofan (fun c : π₀ X ↦ (component c : SSet)) :=
  Cofan.mk X (fun c ↦ (component c).ι)

/-- Coproduct universal property of connected components.

The cofan of inclusions X_c → X is a colimit. Degreewise, every simplex has exactly one
component label, so the disjoint union of the component fibers maps bijectively onto X_n. The
pointwise colimit criterion then gives the simplicial coproduct. -/
noncomputable def isColimitCofan : IsColimit (cofan X) :=
  evaluationJointlyReflectsColimits _ (fun n ↦
    (isColimitMapCoconeCofanMkEquiv
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)
      (fun c : π₀ X ↦ (component c : SSet))
      (fun c : π₀ X ↦ (component c).ι)).symm (by
        apply Nonempty.some
        rw [← Cofan.isColimit_cofanTypes_iff]
        apply CofanTypes.isColimit_mk
        · intro s
          let c := π₀.mk (X.map (⦋0⦌.const n.unop 0).op s)
          exact ⟨c, ⟨s, rfl⟩, rfl⟩
        · intro c x y h
          exact Subtype.ext h
        · intro c d x y h
          have hxy : x.1 = y.1 := h
          exact x.2.symm.trans (hxy ▸ y.2)))

end π₀

end SSet
