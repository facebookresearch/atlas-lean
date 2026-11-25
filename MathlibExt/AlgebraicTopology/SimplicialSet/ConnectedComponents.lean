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
# Decomposition of a simplicial set into connected components

Every simplex is assigned the connected component of its canonical zeroth
vertex. This label is independent of the chosen vertex and defines a
subcomplex for each element of `π₀`. The resulting component subcomplexes are
connected and their inclusions exhibit the original simplicial set as their
coproduct.

The mathematical decomposition follows Joël Riou's
`topcat-model-category` development. The proof here is an independent
current-API construction: components are fibers of a canonical vertex label,
and the coproduct is proved pointwise by a bijection of types.
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

/-- The subcomplex consisting of the simplices in a fixed connected
component. -/
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

/-- Every component subcomplex is connected. -/
instance component_isConnected (c : π₀ X) : SSet.IsConnected (component c : SSet) where
  nonempty := inferInstance

variable (X)

/-- The cofan of component inclusions into a simplicial set. -/
abbrev cofan : Cofan (fun c : π₀ X ↦ (component c : SSet)) :=
  Cofan.mk X (fun c ↦ (component c).ι)

/-- A simplicial set is the coproduct of its connected-component
subcomplexes. -/
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
