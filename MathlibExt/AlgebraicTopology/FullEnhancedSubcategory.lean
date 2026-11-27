/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed source port, original Apache 2.0 license and authors retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Quasicategory/FullSubcategory.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modification: add this provenance notice and the Atlas module path.
All definitions, hypotheses and proof bodies are retained unchanged.
-/

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Full subcategories of quasicategories

Given a predicate `P` on the vertices of a simplicial set `X`, the full enhanced subcategory
`X.fullEnhancedSubcategory P` is the subcomplex of `X` consisting of the simplices all of whose
vertices satisfy `P`. When `X` is a quasicategory, this is the full subcategory of the
`∞`-category `X` spanned by the objects satisfying `P`.

## Main declarations

* `SSet.fullEnhancedSubcategory`: the full enhanced subcategory of `X` on `P`.
* `SSet.mem_fullEnhancedSubcategory_obj_iff_forall_fin`: an `n`-simplex lies in it exactly
  when each of its `n + 1` vertices satisfies `P`.
* `SSet.le_fullEnhancedSubcategory_iff`: it is the largest subcomplex whose vertices satisfy `P`;
  `SSet.range_le_fullEnhancedSubcategory_iff` is the corresponding factorization criterion for
  maps into `X`.
* `SSet.fullEnhancedSubcategory.verticesEquiv`: its vertices are the vertices of `X` satisfying
  `P`.
* `SSet.hasLiftingProperty_fullEnhancedSubcategory_ι`: the inclusion has the right lifting
  property against every map that is surjective on vertices. In particular it is an inner
  fibration, so the full enhanced subcategory of a quasicategory is a quasicategory.
* `CategoryTheory.ObjectProperty.nerveFullSubcategoryIso`: for the nerve of an ordinary
  category, the full enhanced subcategory is the nerve of the full subcategory.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.11.
-/

public section

open CategoryTheory Opposite Simplicial

universe u v

namespace SSet

variable {X : SSet.{u}}

variable (X) in
/-- The full enhanced subcategory of a simplicial set `X` on a predicate `P` on its vertices: the
subcomplex of the simplices all of whose vertices satisfy `P`. -/
def fullEnhancedSubcategory (P : X _⦋0⦌ → Prop) : X.Subcomplex where
  obj n := {x | ∀ v : ⦋0⦌ ⟶ n.unop, P (X.map v.op x)}
  map f x hx v := by
    simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] using hx (v ≫ f.unop)

variable (P : X _⦋0⦌ → Prop)

/-- A simplex lies in the full enhanced subcategory on `P` exactly when each of its vertices
satisfies `P`. -/
lemma mem_fullEnhancedSubcategory_obj_iff {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    x ∈ (X.fullEnhancedSubcategory P).obj n ↔ ∀ v : ⦋0⦌ ⟶ n.unop, P (X.map v.op x) :=
  Iff.rfl

/-- An `n`-simplex lies in the full enhanced subcategory on `P` exactly when each of its `n + 1`
vertices satisfies `P`. -/
lemma mem_fullEnhancedSubcategory_obj_iff_forall_fin {n : ℕ} (x : X _⦋n⦌) :
    x ∈ (X.fullEnhancedSubcategory P).obj _ ↔
      ∀ i : Fin (n + 1), P (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) := by
  rw [mem_fullEnhancedSubcategory_obj_iff]
  refine ⟨fun h i ↦ h _, fun h v ↦ ?_⟩
  rw [SimplexCategory.eq_const_of_zero v]
  exact h _

/-- A vertex lies in the full enhanced subcategory on `P` exactly when it satisfies `P`. -/
@[simp]
lemma mem_fullEnhancedSubcategory_obj_zero_iff (x : X _⦋0⦌) :
    x ∈ (X.fullEnhancedSubcategory P).obj (op ⦋0⦌) ↔ P x := by
  rw [mem_fullEnhancedSubcategory_obj_iff]
  refine ⟨fun h ↦ by simpa using h (𝟙 _), fun h v ↦ ?_⟩
  rw [Subsingleton.elim v (𝟙 _)]
  simpa using h

/-- The full enhanced subcategory on `P` is the largest subcomplex all of whose vertices
satisfy `P`. -/
lemma le_fullEnhancedSubcategory_iff (A : X.Subcomplex) :
    A ≤ X.fullEnhancedSubcategory P ↔ ∀ x ∈ A.obj (op ⦋0⦌), P x := by
  refine ⟨fun h x hx ↦ ?_, fun h n x hx v ↦ h _ (A.map v.op hx)⟩
  simpa using h _ hx

/-- A map of simplicial sets factors through the full enhanced subcategory on `P` exactly when it
sends every vertex to a vertex satisfying `P`. -/
lemma range_le_fullEnhancedSubcategory_iff {Y : SSet.{u}} (f : Y ⟶ X) :
    Subcomplex.range f ≤ X.fullEnhancedSubcategory P ↔ ∀ y : Y _⦋0⦌, P (f.app _ y) := by
  rw [le_fullEnhancedSubcategory_iff]
  exact ⟨fun h y ↦ h _ ⟨y, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact h y⟩

@[gcongr]
lemma fullEnhancedSubcategory_mono {P Q : X _⦋0⦌ → Prop} (h : P ≤ Q) :
    X.fullEnhancedSubcategory P ≤ X.fullEnhancedSubcategory Q :=
  fun _ _ hx v ↦ h _ (hx v)

variable (X) in
/-- The full enhanced subcategory on the predicate that always holds is everything. -/
@[simp]
lemma fullEnhancedSubcategory_top : X.fullEnhancedSubcategory ⊤ = ⊤ :=
  top_le_iff.mp fun _ _ _ _ ↦ trivial

variable (X) in
/-- The full enhanced subcategory on the predicate that never holds is empty. -/
@[simp]
lemma fullEnhancedSubcategory_bot : X.fullEnhancedSubcategory ⊥ = ⊥ :=
  le_bot_iff.mp fun _ _ hx ↦ (hx (SimplexCategory.const _ _ 0)).elim

/-- The vertices of the full enhanced subcategory on `P` are the vertices satisfying `P`. -/
def fullEnhancedSubcategory.verticesEquiv :
    (X.fullEnhancedSubcategory P).obj (op ⦋0⦌) ≃ {x : X _⦋0⦌ // P x} :=
  Equiv.subtypeEquivRight (mem_fullEnhancedSubcategory_obj_zero_iff P)

@[simp]
lemma fullEnhancedSubcategory.verticesEquiv_apply_coe
    (x : (X.fullEnhancedSubcategory P).obj (op ⦋0⦌)) :
    (verticesEquiv P x : X _⦋0⦌) = x.1 := by
  simp [verticesEquiv]

@[simp]
lemma fullEnhancedSubcategory.verticesEquiv_symm_apply_coe (x : {x : X _⦋0⦌ // P x}) :
    ((verticesEquiv P).symm x).1 = x.1 := by
  simp [verticesEquiv]

/-- The inclusion of a full enhanced subcategory has the right lifting property against every
map of simplicial sets that is surjective on vertices. -/
lemma hasLiftingProperty_fullEnhancedSubcategory_ι {A B : SSet.{u}} (i : A ⟶ B)
    (hi : Function.Surjective (i.app (op ⦋0⦌))) :
    HasLiftingProperty i (X.fullEnhancedSubcategory P).ι where
  sq_hasLift {a b} sq := by
    have hb : Subcomplex.range b ≤ X.fullEnhancedSubcategory P := by
      rw [range_le_fullEnhancedSubcategory_iff]
      intro y
      obtain ⟨z, rfl⟩ := hi y
      have hz : b.app _ (i.app _ z) = (a.app _ z).1 := congr($(sq.w).app _ z).symm
      rw [hz]
      exact (mem_fullEnhancedSubcategory_obj_zero_iff P _).mp (a.app _ z).2
    exact ⟨⟨{ l := Subcomplex.lift b hb
              fac_left := by rw [← cancel_mono (Subcomplex.ι _)]; simp [sq.w] }⟩⟩

/-- The inclusion of a full enhanced subcategory is an inner fibration: inner horn inclusions are
surjective on vertices. -/
instance : InnerFibration (X.fullEnhancedSubcategory P).ι where
  mem := by
    rintro _ _ _ ⟨i, -, -⟩
    refine hasLiftingProperty_fullEnhancedSubcategory_ι P _ fun y ↦ ⟨⟨y, ?_⟩, rfl⟩
    simp

/-- The full enhanced subcategory of a quasicategory is a quasicategory. -/
instance [Quasicategory X] : Quasicategory (X.fullEnhancedSubcategory P : SSet) :=
  quasicategory_of_innerFibration (X.fullEnhancedSubcategory P).ι

end SSet

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- The nerve of the full subcategory of `C` on `P` is isomorphic to the full enhanced
subcategory of the nerve of `C` on the vertices whose object satisfies `P`. -/
def nerveFullSubcategoryIso :
    nerve P.FullSubcategory ≅
      ((nerve C).fullEnhancedSubcategory fun x ↦ P (nerveEquiv x) : SSet) where
  hom := SSet.Subcomplex.lift (nerveMap P.ι) <| by
    rw [SSet.range_le_fullEnhancedSubcategory_iff]
    exact fun y ↦ (nerveEquiv y).property
  -- The `k`-th vertex of a simplex `x` of `nerve C` is `x.obj k` definitionally, and lifting a
  -- functor through `P.FullSubcategory` and composing with `P.ι` are mutually inverse on the nose.
  inv :=
    { app n := ↾fun x ↦ P.lift x.1 fun k ↦ x.2 (SimplexCategory.const _ _ k)
      naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Under `nerveFullSubcategoryIso`, the inclusion of the full enhanced subcategory corresponds to
the nerve of the inclusion of the full subcategory. -/
@[reassoc (attr := simp)]
lemma nerveFullSubcategoryIso_hom_ι :
    P.nerveFullSubcategoryIso.hom ≫ SSet.Subcomplex.ι _ = nerveMap P.ι :=
  (rfl)

end CategoryTheory.ObjectProperty
