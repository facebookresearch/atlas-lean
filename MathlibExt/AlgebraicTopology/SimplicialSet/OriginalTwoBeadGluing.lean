/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadExtensionSpace
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Gluing the complete original two beads

The overlap is the original pivot vertex. Gluing retains both full maps,
and every original extension reads back both maps individually.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.OriginalTwoBead

/-- The complete original face before the pivot. -/
def left {n : ℕ} (k : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex :=
  stdSimplex.face (Finset.univ.filter (fun j => j ≤ k))

/-- The complete original face after the pivot. -/
def right {n : ℕ} (k : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex :=
  stdSimplex.face (Finset.univ.filter (fun j => k ≤ j))

/-- The two whole beads intersect at exactly the original pivot vertex. -/
theorem intersection {n : ℕ} (k : Fin (n + 1)) :
    left.{u} k ⊓ right k = stdSimplex.face {k} := by
  classical
  rw [left, right, stdSimplex.face_inter_face]
  have hs : (Finset.univ.filter (fun j : Fin (n + 1) => j ≤ k)) ⊓
      (Finset.univ.filter (fun j : Fin (n + 1) => k ≤ j)) = {k} := by
    apply Finset.ext
    intro j
    constructor
    · intro h
      have hl := (Finset.mem_filter.1 (Finset.mem_inter.1 h).1).2
      have hr := (Finset.mem_filter.1 (Finset.mem_inter.1 h).2).2
      exact Finset.mem_singleton.2 (le_antisymm hl hr)
    · intro h
      have h := Finset.mem_singleton.1 h
      subst j
      exact Finset.mem_inter.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩⟩
  rw [hs]

/-- The original overlap inclusions. -/
def overlapLeft {n : ℕ} (k : Fin (n + 1)) :
    ((left.{u} k ⊓ right k).toSSet) ⟶ (left k : SSet.{u}) :=
  Subcomplex.homOfLE inf_le_left

/-- The original overlap inclusion into the second complete bead. -/
def overlapRight {n : ℕ} (k : Fin (n + 1)) :
    ((left.{u} k ⊓ right k).toSSet) ⟶ (right k : SSet.{u}) :=
  Subcomplex.homOfLE inf_le_right

/-- The inclusion of the first whole bead into the original bead union. -/
def leftIntoUnion {n : ℕ} (k : Fin (n + 1)) :
    (left.{u} k : SSet.{u}) ⟶ (union k : SSet.{u}) :=
  Subcomplex.homOfLE le_sup_left

/-- The inclusion of the second whole bead into the original bead union. -/
def rightIntoUnion {n : ℕ} (k : Fin (n + 1)) :
    (right.{u} k : SSet.{u}) ⟶ (union k : SSet.{u}) :=
  Subcomplex.homOfLE le_sup_right

/-- The two complete original faces form the genuine original pushout. -/
theorem isPushout {n : ℕ} (k : Fin (n + 1)) :
    IsPushout (overlapLeft.{u} k) (overlapRight k)
      (leftIntoUnion k) (rightIntoUnion k) :=
  Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (left k ⊓ right k) (left k) (right k) (union k) from
      { sup_eq := rfl, inf_eq := rfl })

/-- Glue both complete original bead maps over their same pivot. -/
noncomputable def glue {n : ℕ} (k : Fin (n + 1)) {K : SSet.{u}}
    (l : (left k : SSet.{u}) ⟶ K) (r : (right k : SSet.{u}) ⟶ K)
    (h : overlapLeft k ≫ l = overlapRight k ≫ r) :
    (union k : SSet.{u}) ⟶ K :=
  (isPushout k).desc l r h

/-- Gluing reads back the same full first bead. -/
theorem left_glue {n : ℕ} (k : Fin (n + 1)) {K : SSet.{u}}
    (l : (left k : SSet.{u}) ⟶ K) (r : (right k : SSet.{u}) ⟶ K)
    (h : overlapLeft k ≫ l = overlapRight k ≫ r) :
    leftIntoUnion k ≫ glue k l r h = l :=
  (isPushout k).inl_desc _ _ _

/-- Gluing reads back the same full second bead. -/
theorem right_glue {n : ℕ} (k : Fin (n + 1)) {K : SSet.{u}}
    (l : (left k : SSet.{u}) ⟶ K) (r : (right k : SSet.{u}) ⟶ K)
    (h : overlapLeft k ≫ l = overlapRight k ≫ r) :
    rightIntoUnion k ≫ glue k l r h = r :=
  (isPushout k).inr_desc _ _ _

/-- Every original target map preserves both full bead maps and their gluing. -/
theorem glue_naturality {n : ℕ} (k : Fin (n + 1)) {K L : SSet.{u}}
    (l : (left k : SSet.{u}) ⟶ K) (r : (right k : SSet.{u}) ⟶ K)
    (h : overlapLeft k ≫ l = overlapRight k ≫ r) (f : K ⟶ L) :
    glue k l r h ≫ f = glue k (l ≫ f) (r ≫ f)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x => x ≫ f) h).trans (Category.assoc _ _ _))) := by
  apply (isPushout k).hom_ext
  · rw [← Category.assoc, left_glue, left_glue]
  · rw [← Category.assoc, right_glue, right_glue]

/-- A quasicategory admits a genuine simplex extending both whole original beads. -/
theorem exists_extension_of_two_beads {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} [Quasicategory K]
    (l : (left k : SSet.{u}) ⟶ K) (r : (right k : SSet.{u}) ⟶ K)
    (h : overlapLeft k ≫ l = overlapRight k ≫ r) :
    ∃ τ : (Δ[n] : SSet.{u}) ⟶ K,
      (left k).ι ≫ τ = l ∧ (right k).ι ≫ τ = r := by
  obtain ⟨τ, hτ⟩ := exists_original_extension k (glue k l r h)
  refine ⟨τ, ?_, ?_⟩
  · calc
      (left k).ι ≫ τ = leftIntoUnion k ≫ (union k).ι ≫ τ := rfl
      _ = l := by rw [hτ, left_glue]
  · calc
      (right k).ι ≫ τ = rightIntoUnion k ≫ (union k).ι ≫ τ := rfl
      _ = r := by rw [hτ, right_glue]

end SSet.OriginalTwoBead
