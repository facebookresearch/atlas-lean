/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Full subcomplexes spanned by vertices

For a simplicial set `X` and a set `S` of its vertices (`0`-simplices),
`SSet.Subcomplex.full S` is the full subcomplex of `X` spanned by `S`:
its simplices are exactly those simplices of `X` all of whose vertices
(the images under the maps induced by the inclusions `[0] → [n]`) lie
in `S`. It is the largest subcomplex of `X` whose `0`-simplices lie in
`S` (`le_full_iff`), its set of `0`-simplices is `S` itself
(`full_obj_zero`), and it is monotone in `S` (`monotone_full`).

The construction is functorial in the following senses: preimage along
a map `f : Y ⟶ X` is the full subcomplex on the preimage vertex set
(`full_preimage`), the image along `f : X ⟶ Y` is contained in the full
subcomplex on the image vertex set (`image_full_le`), and a map sending
a vertex set `S` into a vertex set `T` induces a map `mapFull` between
the corresponding full subcomplexes.

A standard simplex all of whose vertices lie in `S` factors through
`full S` (`exists_factorThru_full_ι`).

Finally, the inclusion `full S ↪ X` is an inner fibration
(`InnerFibration (full S).ι`). Indeed, it has the right lifting
property against every horn inclusion `Λ[n + 2, i] ↪ Δ[n + 2]` (inner
or outer): such a horn contains all vertices of `Δ[n + 2]`
(`SSet.horn_obj_zero`), so a simplex of `X` whose horn restriction lands
in `full S` already has all its vertices in `S`. No hypothesis on `X`
is needed, so there is no remaining TODO for this statement.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Subcomplex

variable {X Y : SSet.{u}}

/-- The full subcomplex of `X` spanned by a set `S` of vertices: its
simplices are those all of whose vertices lie in `S`. -/
def full (S : Set (X _⦋0⦌)) : X.Subcomplex where
  obj Δ := {x | ∀ (φ : ⦋0⦌ ⟶ Δ.unop), X.map φ.op x ∈ S}
  map {Δ Δ'} f x hx φ := by
    have h := hx (φ ≫ f.unop)
    simpa using h

variable {S T : Set (X _⦋0⦌)}

/-- A simplex lies in `full S` if and only if all of its vertices,
extracted by the maps induced by `⦋0⦌ ⟶ Δ`, lie in `S`. -/
@[simp]
lemma mem_full_obj_iff {Δ : SimplexCategoryᵒᵖ} {x : X.obj Δ} :
    x ∈ (full S).obj Δ ↔ ∀ (φ : ⦋0⦌ ⟶ Δ.unop), X.map φ.op x ∈ S :=
  Iff.rfl

/-- A simplex `x : X _⦋n⦌` lies in `full S` if and only if each of its
`n + 1` ordered vertices lies in `S`. -/
lemma mem_full_obj_iff_vertices {n : ℕ} {x : X _⦋n⦌} :
    x ∈ (full S).obj (op ⦋n⦌) ↔
      ∀ i : Fin (n + 1), X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x ∈ S := by
  refine ⟨fun h i ↦ h _, fun h φ ↦ ?_⟩
  obtain ⟨i, rfl⟩ := SimplexCategory.exists_eq_const_of_zero φ
  exact h i

/-- Simplices of a full subcomplex are stable under all simplicial
operators, in particular under faces and degeneracies. -/
lemma map_mem_full_obj {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    {x : X.obj Δ} (hx : x ∈ (full S).obj Δ) :
    X.map f x ∈ (full S).obj Δ' :=
  (full S).map f hx

/-- The `0`-simplices of `full S` are exactly the elements of `S`. -/
@[simp]
lemma full_obj_zero (S : Set (X _⦋0⦌)) : (full S).obj (op ⦋0⦌) = S := by
  ext x
  rw [mem_full_obj_iff_vertices]
  refine ⟨fun h ↦ ?_, fun hx i ↦ ?_⟩
  · have h0 := h 0
    simpa using h0
  · obtain rfl : i = 0 := by fin_cases i; rfl
    simpa using hx

/-- A `0`-simplex lies in `full S` if and only if it lies in `S`. -/
lemma mem_full_obj_zero_iff {x : X _⦋0⦌} :
    x ∈ (full S).obj (op ⦋0⦌) ↔ x ∈ S := by
  rw [full_obj_zero]

/-- The `0`-simplices of the simplicial set `full S` correspond to the
elements of `S`. -/
def full.obj₀Equiv (S : Set (X _⦋0⦌)) : ((full S : SSet.{u}) _⦋0⦌) ≃ S where
  toFun x := ⟨x.1, mem_full_obj_zero_iff.mp x.2⟩
  invFun s := ⟨s.1, mem_full_obj_zero_iff.mpr s.2⟩
  left_inv _x := Subtype.ext rfl
  right_inv _s := Subtype.ext rfl

/-- The equivalence `full.obj₀Equiv` preserves the underlying `0`-simplex. -/
lemma full_obj₀Equiv_apply_val (S : Set (X _⦋0⦌))
    (x : (full S : SSet.{u}) _⦋0⦌) : (full.obj₀Equiv S x).1 = x.1 :=
  rfl

/-- The inverse of `full.obj₀Equiv` preserves the underlying `0`-simplex. -/
lemma full_obj₀Equiv_symm_apply_val (S : Set (X _⦋0⦌)) (s : S) :
    ((full.obj₀Equiv S).symm s).1 = s.1 :=
  rfl

/-- The full subcomplex spanned by all vertices is `X` itself. -/
@[simp]
lemma full_univ : full (Set.univ : Set (X _⦋0⦌)) = ⊤ := by
  ext Δ x
  simp

/-- The full subcomplex spanned by no vertices is empty. -/
@[simp]
lemma full_empty : full (∅ : Set (X _⦋0⦌)) = ⊥ := by
  ext Δ x
  simp only [mem_full_obj_iff, Subfunctor.bot_obj, Set.mem_empty_iff_false,
    iff_false, not_forall]
  exact ⟨SimplexCategory.const ⦋0⦌ Δ.unop 0, by simp⟩

/-- Enlarging the set of vertices enlarges the full subcomplex. -/
lemma full_le_full (h : S ⊆ T) : full S ≤ full T :=
  fun _ _ hx φ ↦ h (hx φ)

/-- The full-subcomplex construction is monotone in the vertex set. -/
lemma monotone_full : Monotone (full : Set (X _⦋0⦌) → X.Subcomplex) :=
  fun _ _ h ↦ full_le_full h

/-- A subcomplex is contained in `full S` if and only if all of its
`0`-simplices lie in `S`; that is, `full S` is the largest subcomplex
with vertex set contained in `S`. -/
lemma le_full_iff (A : X.Subcomplex) :
    A ≤ full S ↔ A.obj (op ⦋0⦌) ⊆ S := by
  refine ⟨fun h x hx ↦ ?_, fun h Δ x hx φ ↦ h (A.map φ.op hx)⟩
  have hx' := h _ hx
  rwa [full_obj_zero] at hx'

/-- The full subcomplex on an intersection of vertex sets is the
intersection of the full subcomplexes. -/
lemma full_inter (S T : Set (X _⦋0⦌)) :
    full (S ∩ T) = full S ⊓ full T := by
  ext Δ x
  simp [forall_and]

/-- The full subcomplex on an indexed intersection of vertex sets is
the infimum of the full subcomplexes. -/
lemma full_iInter {ι : Type*} (s : ι → Set (X _⦋0⦌)) :
    full (⋂ i, s i) = ⨅ i, full (s i) := by
  ext Δ x
  simp only [mem_full_obj_iff, Subfunctor.iInf_obj, Set.mem_iInter]
  exact forall_comm

section Functoriality

variable (f : X ⟶ Y)

/-- The preimage of a full subcomplex along a map is the full
subcomplex on the preimage of the vertex set. -/
lemma full_preimage (S : Set (Y _⦋0⦌)) :
    (full S).preimage f = full (f.app (op ⦋0⦌) ⁻¹' S) := by
  ext Δ y
  simp only [preimage_obj, Set.mem_preimage, mem_full_obj_iff]
  exact forall_congr' fun φ ↦ by rw [NatTrans.naturality_apply f φ.op y]

/-- The image of a full subcomplex along a map is contained in the
full subcomplex on the image of the vertex set. -/
lemma image_full_le (S : Set (X _⦋0⦌)) :
    (full S).image f ≤ full (f.app (op ⦋0⦌) '' S) := by
  rw [image_le_iff, full_preimage]
  exact full_le_full (Set.subset_preimage_image _ _)

/-- A map `f : X ⟶ Y` sending every vertex in `S` to a vertex in `T`
induces a map from `full S` to `full T`. -/
def mapFull {S : Set (X _⦋0⦌)} {T : Set (Y _⦋0⦌)}
    (h : ∀ ⦃x : X _⦋0⦌⦄, x ∈ S → f.app (op ⦋0⦌) x ∈ T) :
    (full S : SSet.{u}) ⟶ (full T : SSet.{u}) :=
  homOfLE (S₁ := full S) (S₂ := (full T).preimage f)
      (by rw [full_preimage]; exact full_le_full (fun x hx ↦ h hx)) ≫
    (full T).fromPreimage f

/-- The map induced on full subcomplexes is compatible with the
inclusions into `X` and `Y`. -/
@[reassoc (attr := simp)]
lemma mapFull_ι {S : Set (X _⦋0⦌)} {T : Set (Y _⦋0⦌)}
    (h : ∀ ⦃x : X _⦋0⦌⦄, x ∈ S → f.app (op ⦋0⦌) x ∈ T) :
    mapFull f h ≫ (full T).ι = (full S).ι ≫ f := by
  simp [mapFull]

end Functoriality

section InnerFibration

variable (S : Set (X _⦋0⦌))

/-- The inclusion of a full subcomplex has the right lifting property
against every horn inclusion in dimension at least `2`: such a horn
contains all vertices of the standard simplex, so any simplex whose
horn restriction factors through `full S` has all vertices in `S`. -/
theorem hasLiftingProperty_horn_full_ι {n : ℕ} (i : Fin (n + 3)) :
    HasLiftingProperty Λ[n + 2, i].ι (full S).ι where
  sq_hasLift {f g} sq := by
    have hx : yonedaEquiv g ∈ (full S).obj (op ⦋n + 2⦌) := by
      rw [mem_full_obj_iff]
      intro φ
      let v : Δ[n + 2] _⦋0⦌ := stdSimplex.objEquiv.symm φ
      have hv : v ∈ (horn (n + 2) i).obj (op ⦋0⦌) := by
        rw [horn_obj_zero]
        trivial
      have hmem : (f.app (op ⦋0⦌) ⟨v, hv⟩).1 ∈ S :=
        mem_full_obj_zero_iff.mp (f.app (op ⦋0⦌) ⟨v, hv⟩).2
      have he := ConcreteCategory.congr_hom
        (congr_app sq.w (op ⦋0⦌)) ⟨v, hv⟩
      have hg : g.app (op ⦋0⦌) v = X.map φ.op (yonedaEquiv g) := by
        conv_lhs => rw [← yonedaEquiv.symm_apply_apply g]
        exact yonedaEquiv_symm_app_objEquiv_symm (yonedaEquiv g) φ
      have he' : (f.app (op ⦋0⦌) ⟨v, hv⟩).1 = g.app (op ⦋0⦌) v := by
        simpa using he
      rw [← hg, ← he']
      exact hmem
    let l : Δ[n + 2] ⟶ (full S : SSet.{u}) :=
      yonedaEquiv.symm ⟨yonedaEquiv g, hx⟩
    have hfac : l ≫ (full S).ι = g := by
      rw [yonedaEquiv_symm_comp]
      simp
    refine CommSq.HasLift.mk' ⟨l, ?_, hfac⟩
    apply (cancel_mono (full S).ι).mp
    rw [Category.assoc, hfac]
    exact sq.w.symm

/-- The inclusion of a full subcomplex into its ambient simplicial set
is an inner fibration. -/
instance : InnerFibration (full S).ι where
  mem := by
    intro _ _ g hg
    obtain ⟨i, -, -⟩ := hg
    exact hasLiftingProperty_horn_full_ι S i

end InnerFibration

/-- A standard simplex of `X` all of whose vertices lie in `V`
factors through the full subcomplex on `V`: the elementary fact
Stevenson uses (via Remark 2.12 and Lemma 3.11) to restrict to full
simplicial subsets spanned by finitely many vertices. The vertex
hypothesis is on the classified simplex `yonedaEquiv σ`, whose
`i`-th vertex is extracted by `SimplexCategory.const ⦋0⦌ ⦋n⦌ i`. -/
theorem exists_factorThru_full_ι {V : Set (X _⦋0⦌)} {n : ℕ}
    (σ : Δ[n] ⟶ X)
    (hσ : ∀ i : Fin (n + 1),
      X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (yonedaEquiv σ) ∈ V) :
    ∃ σ' : Δ[n] ⟶ (full V : SSet.{u}), σ' ≫ (full V).ι = σ := by
  have hmem : yonedaEquiv σ ∈ (full V).obj (op ⦋n⦌) :=
    mem_full_obj_iff_vertices.mpr hσ
  refine ⟨yonedaEquiv.symm ⟨yonedaEquiv σ, hmem⟩, ?_⟩
  rw [yonedaEquiv_symm_comp]
  simp

end SSet.Subcomplex
