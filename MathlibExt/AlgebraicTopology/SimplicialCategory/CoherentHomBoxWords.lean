/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomOpenBoxGeometry
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeCoordinates
import MathlibExt.AlgebraicTopology.CategoricalSource.HornBasic

/-!
# Actual coherent Hom-box word conditions

The original coherent Hom-box membership is stated on the same whole
original path chain. A retained top face means the supplied middle vertex
is in every scalar vertex; another boundary face means its original
vertex is in none or all of them. No compatibility or filler conclusion
is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomBoxWords
open MappingCube CubeCoordinates CubeBoundary

/-- The actual scalar interval word at the supplied original scalar degree. -/
abbrev word {q : SimplexCategoryᵒᵖ} (s : (Δ[1] : SSet.{u}).obj q) : Fin (q.unop.len + 1) →o Fin 2 :=
  (SSet.stdSimplex.objEquiv s).toOrderHom

private theorem bit_one_of_ne_zero (b : Fin 2) (h : b ≠ 0) : b = 1 := by omega
private theorem bit_zero_of_ne_one (b : Fin 2) (h : b ≠ 1) : b = 0 := by omega
private theorem bit_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

/-- The retained upper endpoint horn is exactly a whole original coordinate word at one. -/
theorem upper_word_iff {q : SimplexCategoryᵒᵖ} (s : (Δ[1] : SSet.{u}).obj q) :
    s ∈ (Λ[1, (1 : Fin 2)]).obj q ↔ ∀ t, word s t = 1 := by
  rcases q with ⟨⟨d⟩⟩
  rw [SSet.mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hj, hs⟩
    have he : j = 0 := by fin_cases j <;> simp_all
    subst j
    intro t
    have h : s t ≠ 0 := fun h => hs ⟨t, h⟩
    exact bit_one_of_ne_zero _ h
  · intro h
    refine ⟨0, by decide, ?_⟩
    rintro ⟨t, ht⟩
    have h1 : (s t : Fin 2) = 1 := h t
    exact bit_zero_ne_one (ht.symm.trans h1)

/-- An actual interval boundary word is exactly constant zero or constant one. -/
theorem boundary_word_iff {q : SimplexCategoryᵒᵖ} (s : (Δ[1] : SSet.{u}).obj q) :
    s ∈ (∂Δ[1]).obj q ↔ (∀ t, word s t = 0) ∨ (∀ t, word s t = 1) := by
  rcases q with ⟨⟨d⟩⟩
  rw [SSet.mem_boundary_iff_notMem_range]
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j
    · right
      intro t
      have h : s t ≠ 0 := fun h => hj ⟨t, h⟩
      exact bit_one_of_ne_zero _ h
    · left
      intro t
      have h : s t ≠ 1 := fun h => hj ⟨t, h⟩
      exact bit_zero_of_ne_one _ h
  · rintro (h | h)
    · refine ⟨1, ?_⟩
      rintro ⟨t, ht⟩
      have h0 : (s t : Fin 2) = 0 := h t
      exact bit_zero_ne_one (h0.symm.trans ht)
    · refine ⟨0, ?_⟩
      rintro ⟨t, ht⟩
      have h1 : (s t : Fin 2) = 1 := h t
      exact bit_zero_ne_one (ht.symm.trans h1)

/-- Original coherent Hom-box membership is transported by its actual entire Hom-cube
isomorphism. -/
theorem mem_homBox_iff {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j)
    (k : IntervalHom.Interior i j) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (SimplicialThickening.Path i j)).obj q) :
    p ∈ (HomOpenBox.subcomplex hij k).obj q ↔
      (intervalCubeIso hij).hom.app q p ∈ (CubeBoundary.upperBox k).obj q := by
  change (∃ y : (HomOpenBox.domain k).obj q,
    (HomOpenBox.ι hij k).app q y = p) ↔
      ∃ y : (CubeBoxes.boxDomain k (boundary (CubeBoxes.Remaining k))).obj q,
        (CubeBoxes.boxι k (boundary (CubeBoxes.Remaining k))).app q y =
          (intervalCubeIso hij).hom.app q p
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have he := congr($((intervalCubeIso hij).inv_hom_id).app q
      ((CubeBoxes.boxι k (boundary (CubeBoxes.Remaining k))).app q y))
    exact he.symm.trans (congrArg (fun x => (intervalCubeIso hij).hom.app q x) hy)
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    exact (congrArg (fun x => (intervalCubeIso hij).inv.app q x) hy).trans
      (congr($((intervalCubeIso hij).hom_inv_id).app q p))

/-- Original coordinate zero means absence of that same original interior vertex in the
actual original path. -/
theorem coordinate_zero_iff {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (SimplicialThickening.Path i j)).obj q)
    (t : IntervalHom.Interior i j) (a : Fin (q.unop.len + 1)) :
    word ((Limits.Pi.π (fun _ : IntervalHom.Interior i j => (Δ[1] : SSet.{u})) t).app q
      ((intervalCubeIso hij).hom.app q p)) a = 0 ↔ t.val ∉ (p.obj a).I := by
  have h1 := interval_coordinate_one_iff hij p t a
  constructor
  · intro h0 hm
    have h := h1.mpr hm
    exact bit_zero_ne_one (h0.symm.trans h)
  · intro hm
    have h : word ((Limits.Pi.π (fun _ : IntervalHom.Interior i j => (Δ[1] : SSet.{u})) t).app q
      ((intervalCubeIso hij).hom.app q p)) a ≠ 1 := fun h => hm (h1.mp h)
    exact bit_zero_of_ne_one _ h

end CategoryTheory.CoherentRealization.HomBoxWords

namespace CategoryTheory.CoherentRealization.HomOpenBox
open IntervalHom HomBoxWords CubeCoordinates
variable {J : Type u} [LinearOrder J] {i j : J}

/-- The geometric coherent Hom box consists of chains retaining the distinguished vertex,
or wholly omitting or retaining another interior vertex. -/
theorem mem_iff (hij : i ≤ j) (k : Interior i j) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (SimplicialThickening.Path i j)).obj q) :
    p ∈ (subcomplex hij k).obj q ↔
      (∀ a, k.val ∈ (p.obj a).I) ∨
        ∃ t : CubeBoxes.Remaining k,
          (∀ a, t.val.val ∉ (p.obj a).I) ∨ (∀ a, t.val.val ∈ (p.obj a).I) := by
  rw [mem_homBox_iff, CubeBoundary.mem_upperBox_iff]
  rw [upper_word_iff]
  constructor
  · rintro (h | ⟨t, ht⟩)
    · left
      intro a
      exact (interval_coordinate_one_iff hij p k a).mp (h a)
    · right
      refine ⟨t, ?_⟩
      rcases (boundary_word_iff _).mp ht with ht | ht
      · left
        intro a
        exact (coordinate_zero_iff hij p t.val a).mp (ht a)
      · right
        intro a
        exact (interval_coordinate_one_iff hij p t.val a).mp (ht a)
  · rintro (h | ⟨t, ht⟩)
    · left
      intro a
      exact (interval_coordinate_one_iff hij p k a).mpr (h a)
    · right
      refine ⟨t, (boundary_word_iff _).mpr ?_⟩
      rcases ht with ht | ht
      · left
        intro a
        exact (coordinate_zero_iff hij p t.val a).mpr (ht a)
      · right
        intro a
        exact (interval_coordinate_one_iff hij p t.val a).mpr (ht a)

/-- The range of the geometric coherent Hom box is the intrinsic horn-path subcomplex.
Monotonicity reduces whole-chain omission to the last path and retention to the first. -/
theorem subcomplex_eq_hornPaths (hij : i ≤ j) (k : Interior i j) :
    subcomplex hij k = MathlibExt.CategoricalSource.hornPaths i j k.val := by
  apply Subfunctor.ext
  funext q
  ext p
  rw [mem_iff, MathlibExt.CategoricalSource.mem_hornPaths_iff]
  constructor
  · rintro (h | ⟨t, h | h⟩)
    · exact Or.inr ⟨k.val, k.property.1, k.property.2, h 0⟩
    · refine Or.inl ⟨t.val.val, t.val.property.1, t.val.property.2, ?_, h (Fin.last _)⟩
      intro e
      exact t.property (Subtype.ext e)
    · exact Or.inr ⟨t.val.val, t.val.property.1, t.val.property.2, h 0⟩
  · rintro (⟨t, hti, htj, htk, h⟩ | ⟨t, hti, htj, h⟩)
    · refine Or.inr ⟨⟨⟨t, hti, htj⟩, ?_⟩, Or.inl ?_⟩
      · intro e
        exact htk (congrArg Subtype.val e)
      · intro a ha
        exact h (SimplicialThickening.monotone_chain p (Fin.le_last a) ha)
    · by_cases htk : t = k.val
      · subst t
        exact Or.inl (fun a => SimplicialThickening.monotone_chain p (Fin.zero_le a) h)
      · refine Or.inr ⟨⟨⟨t, hti, htj⟩, ?_⟩, Or.inr ?_⟩
        · intro e
          exact htk (congrArg Subtype.val e)
        · intro a
          exact SimplicialThickening.monotone_chain p (Fin.zero_le a) h

end CategoryTheory.CoherentRealization.HomOpenBox
