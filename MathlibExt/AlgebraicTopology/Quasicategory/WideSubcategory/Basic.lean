/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Native wide subcategories of a simplicial set

A multiplicative class of arrows in the native homotopy category specifies
a class of actual edges. The associated subcomplex retains every original
simplex whose edges belong to that class. Containing every isomorphism
makes this a wide subcategory when the ambient simplicial set is a
quasicategory. The homotopy category is used only to classify edges;
the original higher simplices are retained.

The all-edge construction follows the native equivalence-edge core API.
The input is the wide-subcategory data used in Haugseng, Hebestreit,
Linskens and Nuiten, *Two-variable fibrations, factorisation systems and
infinity-categories of spans*, conventions and Definition 2.1.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y Z : SSet.{u}}

namespace Edge

/-- Equal original one-simplices give the same membership in any class
of arrows of the native homotopy category, including endpoint transport. -/
theorem morphismProperty_iff_of_edge_eq
    (P : MorphismProperty (hoFunctor.obj X))
    {a b c d : X _⦋0⦌} {e : Edge a b} {e' : Edge c d}
    (h : e.edge = e'.edge) :
    P e.toHoHom ↔ P e'.toHoHom := by
  have ha : a = c := by rw [← e.src_eq, ← e'.src_eq, h]
  have hb : b = d := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  subst c
  subst d
  obtain rfl : e = e' := Edge.ext h
  rfl

end Edge

namespace Subcomplex

/-- Every original simplex whose edges represent arrows in P.
No truncation or quotient of the original higher simplices is taken. -/
def ofMorphismProperty (P : MorphismProperty (hoFunctor.obj X)) : X.Subcomplex where
  obj Δ := {x | ∀ φ : ⦋1⦌ ⟶ Δ.unop,
    P (Edge.mk' (X.map φ.op x)).toHoHom}
  map {Δ Δ'} f x hx φ := by
    have h := hx (φ ≫ f.unop)
    rwa [op_comp, X.map_comp] at h

/-- Membership is the original all-edge condition in every degree. -/
@[simp] theorem mem_ofMorphismProperty_iff
    (P : MorphismProperty (hoFunctor.obj X)) {Δ : SimplexCategoryᵒᵖ}
    {x : X.obj Δ} :
    x ∈ (ofMorphismProperty P).obj Δ ↔
      ∀ φ : ⦋1⦌ ⟶ Δ.unop, P (Edge.mk' (X.map φ.op x)).toHoHom :=
  Iff.rfl

/-- The edge of a degenerate simplex represents an identity. -/
theorem property_degenerate (P : MorphismProperty (hoFunctor.obj X))
    [P.ContainsIdentities] (x : X _⦋0⦌) :
    P (Edge.mk' (X.σ (0 : Fin 1) x)).toHoHom := by
  apply (Edge.morphismProperty_iff_of_edge_eq P
    (e := Edge.id x) (e' := Edge.mk' (X.σ (0 : Fin 1) x)) rfl).mp
  rw [Edge.toHoHom_id]
  exact P.id_mem _

/-- Constant edge restrictions are the degenerate edges of original vertices. -/
theorem property_map_const (P : MorphismProperty (hoFunctor.obj X))
    [P.ContainsIdentities] {Δ : SimplexCategory} (x : X.obj (op Δ))
    (i : Fin (Δ.len + 1)) :
    P (Edge.mk' (X.map (SimplexCategory.const ⦋1⦌ Δ i).op x)).toHoHom := by
  have hs : SimplexCategory.σ (0 : Fin 1) =
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 :=
    SimplexCategory.eq_const_to_zero _
  have hf : SimplexCategory.const ⦋1⦌ Δ i =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ Δ i := by
    rw [hs]
    exact (SimplexCategory.const_fac_thru_zero ⦋1⦌ Δ i).symm
  rw [hf, op_comp, X.map_comp]
  exact property_degenerate P (X.map (SimplexCategory.const ⦋0⦌ Δ i).op x)

/-- Identities ensure that every original vertex is retained. -/
@[simp] theorem ofMorphismProperty_obj_zero
    (P : MorphismProperty (hoFunctor.obj X)) [P.ContainsIdentities] :
    (ofMorphismProperty P).obj (op ⦋0⦌) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x φ
  rw [SimplexCategory.eq_const_to_zero φ]
  exact property_map_const P x 0

/-- The one-simplices are exactly the specified native edge class. -/
theorem mem_ofMorphismProperty_obj_one
    (P : MorphismProperty (hoFunctor.obj X)) [P.ContainsIdentities]
    {e : X _⦋1⦌} :
    e ∈ (ofMorphismProperty P).obj (op ⦋1⦌) ↔ P (Edge.mk' e).toHoHom := by
  constructor
  · intro h
    have h1 := h (𝟙 ⦋1⦌)
    rwa [op_id, X.map_id] at h1
  · intro h φ
    rcases SimplexCategory.eq_of_one_to_one φ with ⟨i, rfl⟩ | rfl
    · exact property_map_const P e i
    · rwa [op_id, X.map_id]

/-- All source operators act by the same original simplex maps. -/
theorem map_mem_ofMorphismProperty
    (P : MorphismProperty (hoFunctor.obj X)) {Δ Δ' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') {x : X.obj Δ} (hx : x ∈ (ofMorphismProperty P).obj Δ) :
    X.map f x ∈ (ofMorphismProperty P).obj Δ' :=
  (ofMorphismProperty P).map f hx

/-- Every original simplicial operator is retained on its original simplex data. -/
@[simp] theorem ofMorphismProperty_map_val
    (P : MorphismProperty (hoFunctor.obj X)) {Δ Δ' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (x : (ofMorphismProperty P : SSet.{u}).obj Δ) :
    (((ofMorphismProperty P : SSet.{u}).map f x).1) = X.map f x.1 := rfl

/-- The original face of a retained simplex is its face in the ambient simplicial set. -/
theorem ofMorphismProperty_δ_val
    (P : MorphismProperty (hoFunctor.obj X)) {n : ℕ} (i : Fin (n + 2))
    (x : (ofMorphismProperty P : SSet.{u}) _⦋n + 1⦌) :
    ((ofMorphismProperty P : SSet.{u}).δ i x).1 = X.δ i x.1 := rfl

/-- The original degeneracy of a retained simplex is its ambient degeneracy. -/
theorem ofMorphismProperty_σ_val
    (P : MorphismProperty (hoFunctor.obj X)) {n : ℕ} (i : Fin (n + 1))
    (x : (ofMorphismProperty P : SSet.{u}) _⦋n⦌) :
    ((ofMorphismProperty P : SSet.{u}).σ i x).1 = X.σ i x.1 := rfl

/-- Testing the three original face edges is sufficient in dimension two. -/
theorem mem_ofMorphismProperty_obj_two_of_faces
    (P : MorphismProperty (hoFunctor.obj X)) [P.ContainsIdentities]
    {s : X _⦋2⦌}
    (h0 : P (Edge.mk' (X.δ 0 s)).toHoHom)
    (h1 : P (Edge.mk' (X.δ 1 s)).toHoHom)
    (h2 : P (Edge.mk' (X.δ 2 s)).toHoHom) :
    s ∈ (ofMorphismProperty P).obj (op ⦋2⦌) := by
  intro φ
  have trich : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by
    intro a
    fin_cases a <;> simp
  have hle : φ.toOrderHom 0 ≤ φ.toOrderHom 1 :=
    φ.toOrderHom.monotone (Fin.zero_le 1)
  rcases trich (φ.toOrderHom 0) with ha | ha | ha <;>
    rcases trich (φ.toOrderHom 1) with hb | hb | hb
  · rw [SimplexCategory.Hom.ext_one_left φ
      (SimplexCategory.const ⦋1⦌ ⦋2⦌ 0) ha hb]
    exact property_map_const P s 0
  · rw [SimplexCategory.Hom.ext_one_left φ (SimplexCategory.δ 2) ha hb]
    exact h2
  · rw [SimplexCategory.Hom.ext_one_left φ (SimplexCategory.δ 1) ha hb]
    exact h1
  · exfalso
    rw [ha, hb] at hle
    exact absurd hle (by decide)
  · rw [SimplexCategory.Hom.ext_one_left φ
      (SimplexCategory.const ⦋1⦌ ⦋2⦌ 1) ha hb]
    exact property_map_const P s 1
  · rw [SimplexCategory.Hom.ext_one_left φ (SimplexCategory.δ 0) ha hb]
    exact h0
  · exfalso
    rw [ha, hb] at hle
    exact absurd hle (by decide)
  · exfalso
    rw [ha, hb] at hle
    exact absurd hle (by decide)
  · rw [SimplexCategory.Hom.ext_one_left φ
      (SimplexCategory.const ⦋1⦌ ⦋2⦌ 2) ha hb]
    exact property_map_const P s 2

end Subcomplex

/-- A multiplicative native edge class containing every equivalence.
On a quasicategory, its all-edge subcomplex is a genuine wide subcategory. -/
structure WideSubcategory (X : SSet.{u}) where
  /-- The class classifies arrows of the native homotopy category. -/
  property : MorphismProperty (hoFunctor.obj X)
  /-- The class contains identities and is closed under composition of class members. -/
  isMultiplicative : property.IsMultiplicative
  /-- Every equivalence of the original simplicial set belongs to the class. -/
  contains_isomorphisms : MorphismProperty.isomorphisms (hoFunctor.obj X) ≤ property

attribute [instance] WideSubcategory.isMultiplicative

namespace WideSubcategory

/-- The actual all-degree subcomplex associated to the wide class. -/
abbrev subcomplex (W : WideSubcategory X) : X.Subcomplex :=
  Subcomplex.ofMorphismProperty W.property

/-- Every native core simplex belongs to a wide subcategory. -/
theorem core_le (W : WideSubcategory X) : core X ≤ W.subcomplex := by
  intro Δ x hx φ
  exact W.contains_isomorphisms _ (hx φ)

/-- The least wide class is the class of native equivalences. -/
def equivalences (X : SSet.{u}) : WideSubcategory X where
  property := MorphismProperty.isomorphisms (hoFunctor.obj X)
  isMultiplicative := inferInstance
  contains_isomorphisms := le_rfl

/-- The equivalence-only wide subcategory recovers the actual native core. -/
@[simp] theorem equivalences_subcomplex (X : SSet.{u}) :
    (equivalences X).subcomplex = core X := rfl

end WideSubcategory
end SSet
