/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ComponentUnionSubcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Kan inclusions of selected connected components

The literal union of any selected connected-component subcomplexes has a
canonical inclusion which is a Kan fibration for every ambient simplicial
set. A positive-dimensional horn has a retained face; its selected component
label is also the label of the original bottom simplex. That same original
simplex supplies the entire lift. If the ambient simplicial set is Kan,
the selected union is Kan.

These component subspaces are used in Rezk (2001), Sections 5.7 and 11.6.
The proof here uses the existing native component and horn APIs. No
dimension-zero horn lifting property or weakness of the inclusion is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

private theorem componentLabel_map {X : SSet.{u}} {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (q : X.obj n) :
    π₀.mk (X.map (SimplexCategory.const ⦋0⦌ m.unop 0).op (X.map f q)) =
      π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) := by
  let c := π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q)
  have hq : q ∈ (π₀.component c).obj n := rfl
  exact (π₀.component c).map f hq

/-- Every original vertex of a simplex gives the same selected-component test. -/
theorem mem_componentUnion_vertex (X : SSet.{u}) (S : Set (π₀ X))
    (n : SimplexCategoryᵒᵖ) (q : X.obj n) (α : ⦋0⦌ ⟶ n.unop) :
    q ∈ (componentUnion X S).obj n ↔ π₀.mk (X.map α.op q) ∈ S := by
  rw [mem_componentUnion]
  have h : π₀.mk (X.map α.op q) =
      π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) := by
    simpa using componentLabel_map α.op q
  rw [h]

/-- Any original face has precisely the component label of the original simplex. -/
theorem mem_componentUnion_iff_face (X : SSet.{u}) (S : Set (π₀ X))
    (n : ℕ) (j : Fin (n + 2)) (q : X _⦋n + 1⦌) :
    q ∈ (componentUnion X S).obj (op ⦋n + 1⦌) ↔
      X.δ j q ∈ (componentUnion X S).obj (op ⦋n⦌) := by
  rw [mem_componentUnion, mem_componentUnion]
  have h := componentLabel_map (X := X) (SimplexCategory.δ j).op q
  change π₀.mk (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op (X.δ j q)) =
    π₀.mk (X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op q) at h
  rw [h]

/-- The empty selector gives the original empty subcomplex. -/
@[simp]
theorem componentUnion_empty (X : SSet.{u}) : componentUnion X ∅ = ⊥ := by
  ext n q
  rw [mem_componentUnion]
  simp

/-- The full selector gives the original full subcomplex. -/
@[simp]
theorem componentUnion_univ (X : SSet.{u}) : componentUnion X Set.univ = ⊤ := by
  ext n q
  rw [mem_componentUnion]
  simp

/-- A singleton selector gives the same original native component subcomplex. -/
@[simp]
theorem componentUnion_singleton (X : SSet.{u}) (c : π₀ X) :
    componentUnion X {c} = π₀.component c := by
  ext n q
  rw [mem_componentUnion]
  change π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) ∈ {c} ↔
    π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) = c
  exact Set.mem_singleton_iff

private theorem exists_retainedFace (n : ℕ) (i : Fin (n + 2)) :
    ∃ j : Fin (n + 2), j ≠ i := by
  by_cases hi : i = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    intro h
    have hf := congrArg Fin.val (h.trans hi)
    change 1 = 0 at hf
    omega
  · exact ⟨0, fun h => hi h.symm⟩

private theorem componentUnion_hornLift (X : SSet.{u}) (S : Set (π₀ X))
    (n : ℕ) (i : Fin (n + 2))
    (a : (horn (n + 1) i : SSet.{u}) ⟶ (componentUnion X S : SSet.{u}))
    (b : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (sq : CommSq a (horn (n + 1) i).ι (componentUnion X S).ι b) :
    ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ (componentUnion X S : SSet.{u}),
      (horn (n + 1) i).ι ≫ l = a ∧ l ≫ (componentUnion X S).ι = b := by
  obtain ⟨j, hj⟩ := exists_retainedFace n i
  let q := yonedaEquiv b
  let aFace := yonedaEquiv (horn.ι i j hj ≫ a)
  have hface : (horn.ι i j hj ≫ a) ≫ (componentUnion X S).ι = stdSimplex.δ j ≫ b := by
    rw [Category.assoc, sq.w, ← Category.assoc, horn.ι_ι]
  have hqFace := congrArg yonedaEquiv hface
  rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp] at hqFace
  change aFace.val = X.δ j q at hqFace
  have hmemFace : X.δ j q ∈ (componentUnion X S).obj (op ⦋n⦌) :=
    hqFace ▸ aFace.property
  have hmem : q ∈ (componentUnion X S).obj (op ⦋n + 1⦌) :=
    (mem_componentUnion_iff_face X S n j q).mpr hmemFace
  let l : (Δ[n + 1] : SSet.{u}) ⟶ (componentUnion X S : SSet.{u}) :=
    (SSet.yonedaEquiv (X := (componentUnion X S : SSet.{u}))).symm ⟨q, hmem⟩
  have hl : l ≫ (componentUnion X S).ι = b := by
    dsimp only [l]
    rw [yonedaEquiv_symm_comp]
    change yonedaEquiv.symm q = b
    exact Equiv.symm_apply_apply _ _
  refine ⟨l, ?_, hl⟩
  apply (cancel_mono (componentUnion X S).ι).mp
  rw [Category.assoc, hl]
  exact sq.w.symm

/-- The canonical inclusion of any selected component union is a genuine Kan fibration.
No Kan hypothesis on the ambient X is needed. -/
theorem componentUnionInclusionKanFibration (Z : SSet.{u}) (S : Set (π₀ Z)) :
    Fibration (componentUnion Z S).ι := by
  rw [modelCategoryQuillen.fibration_iff]
  intro A B j hj
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨i⟩⟩ := hj
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨l, hl, hp⟩ := componentUnion_hornLift Z S n i a b sq
  exact CommSq.HasLift.mk' ⟨l, hl, hp⟩

/-- A selected component union of an actual Kan complex is itself Kan. -/
theorem componentUnionKanComplex (X : SSet.{u}) (S : Set (π₀ X)) [KanComplex X] :
    KanComplex (componentUnion X S : SSet.{u}) := by
  let : Fibration (componentUnion X S).ι := componentUnionInclusionKanFibration X S
  exact isFibrant_of_fibration (componentUnion X S).ι

end SSet
