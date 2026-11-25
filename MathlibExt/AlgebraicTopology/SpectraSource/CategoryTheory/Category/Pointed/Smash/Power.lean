/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Category/Pointed/Smash/Power.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Category.Pointed

/-!
# Smash powers of pointed types

The smash power `X^∧ι` of a pointed type `X`, indexed by a type `ι`, is the quotient of the
product `ι → X` collapsing the fat wedge (the families with some coordinate at the basepoint)
to the basepoint, with a basepoint adjoined disjointly when `ι` is empty. We use the model
whose elements are the basepoint and the families avoiding the basepoint in every coordinate;
the class of an arbitrary family is `Pointed.smashPow.mk`. In particular `X^∧∅ = S⁰` has
exactly two elements, while for nonempty `ι` every element is the class of a family.

The smash power is functorial in pointed maps of `X`, acts on bijections of the index type by
reindexing coordinates, and concatenation of families sends `X^∧ι` and `X^∧κ` to `X^∧(ι ⊕ κ)`.
These are the levelwise inputs for the smash powers of pointed simplicial sets, which form the
sphere sequence underlying symmetric spectra.

## Main definitions

* `Pointed.smashPow X ι`: the smash power `X^∧ι`.
* `Pointed.smashPow.mk f`: the class of a family `f : ι → X`.
* `Pointed.smashPow.lift`: the pointed map induced by a function of families sending the fat
  wedge to the basepoint; `Pointed.smashPow.hom_ext` gives uniqueness.
* `Pointed.smashPow.map`: the smash power of a pointed map, and `Pointed.smashPowFunctor ι`, the
  smash power as an endofunctor of pointed types.
* `Pointed.smashPow.reindex`: the action of a bijection of index types.
* `Pointed.smashPow.append`: concatenation of classes of families.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u v w

open CategoryTheory

namespace Pointed

/-- The smash power `X^∧ι` of a pointed type: the basepoint together with the families
`ι → X` avoiding the basepoint in every coordinate. -/
def smashPow (X : Pointed.{u}) (ι : Type v) : Pointed.{max u v} :=
  of (none : Option {f : ι → X // ∀ i, f i ≠ X.point})

namespace smashPow

variable {X Y Z : Pointed.{u}} {W : Pointed.{max u v}} {ι κ μ : Type v}

open Classical in
/-- The class in the smash power `X^∧ι` of a family `f : ι → X`. It is the basepoint exactly
when some coordinate of `f` is the basepoint. -/
noncomputable def mk (f : ι → X) : X.smashPow ι :=
  if h : ∀ i, f i ≠ X.point then (some ⟨f, h⟩ : Option {f : ι → X // ∀ i, f i ≠ X.point})
  else (none : Option {f : ι → X // ∀ i, f i ≠ X.point})

private lemma mk_of_forall {f : ι → X} (h : ∀ i, f i ≠ X.point) :
    mk f = (some ⟨f, h⟩ : Option {f : ι → X // ∀ i, f i ≠ X.point}) :=
  dite_eq_left h

private lemma mk_of_not_forall {f : ι → X} (h : ¬∀ i, f i ≠ X.point) :
    mk f = (X.smashPow ι).point :=
  dite_eq_right h

/-- A family represents the basepoint exactly when it lies in the fat wedge. -/
@[simp]
lemma mk_eq_point_iff {f : ι → X} : mk f = (X.smashPow ι).point ↔ ∃ i, f i = X.point := by
  by_cases h : ∀ i, f i ≠ X.point
  · rw [mk_of_forall h]
    exact iff_of_false (Option.some_ne_none _) fun ⟨i, hi⟩ ↦ h i hi
  · rw [mk_of_not_forall h]
    simpa using h

lemma mk_eq_point {f : ι → X} (i : ι) (hi : f i = X.point) : mk f = (X.smashPow ι).point :=
  mk_eq_point_iff.2 ⟨i, hi⟩

/-- Two families have the same class exactly when they are equal or both lie in the fat
wedge. -/
lemma mk_eq_mk_iff {f g : ι → X} :
    mk f = mk g ↔ f = g ∨ (∃ i, f i = X.point) ∧ ∃ i, g i = X.point := by
  by_cases hf : ∀ i, f i ≠ X.point <;> by_cases hg : ∀ i, g i ≠ X.point
  · rw [mk_of_forall hf, mk_of_forall hg]
    refine ⟨fun h ↦ .inl (congrArg Subtype.val (Option.some.inj h)), ?_⟩
    rintro (rfl | ⟨⟨i, hi⟩, -⟩)
    exacts [rfl, (hf i hi).elim]
  · rw [mk_of_forall hf, mk_of_not_forall hg]
    refine iff_of_false (Option.some_ne_none _) ?_
    rintro (rfl | ⟨⟨i, hi⟩, -⟩)
    exacts [hg hf, hf i hi]
  · rw [mk_of_not_forall hf, mk_of_forall hg]
    refine iff_of_false (Option.some_ne_none _).symm ?_
    rintro (rfl | ⟨-, ⟨i, hi⟩⟩)
    exacts [hf hg, hg i hi]
  · rw [mk_of_not_forall hf, mk_of_not_forall hg]
    exact iff_of_true rfl (.inr ⟨by simpa using hf, by simpa using hg⟩)

/-- Induction on the smash power: it suffices to treat the basepoint and the classes of
families. -/
@[elab_as_elim]
lemma ind {motive : X.smashPow ι → Prop} (point : motive (X.smashPow ι).point)
    (mk : ∀ f, motive (mk f)) (a : X.smashPow ι) : motive a := by
  rcases (a : Option {f : ι → X // ∀ i, f i ≠ X.point}) with _ | ⟨f, hf⟩
  · exact point
  · simpa [mk_of_forall hf] using mk f

/-- The pointed map out of the smash power induced by a function of families sending the fat
wedge to the basepoint. The hypothesis is not needed to define the map in this model, only to
compute it on every class (`lift_mk`). -/
-- The code generator cannot see through the unexposed carrier of the smash power.
noncomputable def lift (F : (ι → X) → W) (_hF : ∀ f i, f i = X.point → F f = W.point) :
    X.smashPow ι ⟶ W where
  toFun a := (a : Option {f : ι → X // ∀ i, f i ≠ X.point}).elim W.point fun f ↦ F f
  map_point := rfl

@[simp]
lemma lift_mk (F : (ι → X) → W) (hF : ∀ f i, f i = X.point → F f = W.point) (f : ι → X) :
    (lift F hF).toFun (mk f) = F f := by
  by_cases h : ∀ i, f i ≠ X.point
  · rw [mk_of_forall h]
    rfl
  · rw [mk_of_not_forall h]
    obtain ⟨i, hi⟩ : ∃ i, f i = X.point := by simpa using h
    exact (hF f i hi).symm

/-- Pointed maps out of the smash power are determined by their values on classes of
families. -/
@[ext]
lemma hom_ext {g h : X.smashPow ι ⟶ W} (H : ∀ f, g.toFun (mk f) = h.toFun (mk f)) : g = h :=
  Hom.ext (funext (ind (g.map_point.trans h.map_point.symm) H))

/-- The smash power of a pointed map, applied in every coordinate. -/
noncomputable def map (ι : Type v) (g : X ⟶ Y) : X.smashPow ι ⟶ Y.smashPow ι :=
  lift (fun f ↦ mk (g.toFun ∘ f)) fun f i hi ↦ mk_eq_point i (by simp [hi, g.map_point])

@[simp]
lemma map_mk (g : X ⟶ Y) (f : ι → X) : (map ι g).toFun (mk f) = mk (g.toFun ∘ f) :=
  lift_mk _ _ f

@[simp]
lemma map_id : map ι (𝟙 X) = 𝟙 (X.smashPow ι) := by
  ext f
  simp

@[simp]
lemma map_comp (g : X ⟶ Y) (h : Y ⟶ Z) : map ι (g ≫ h) = map ι g ≫ map ι h := by
  ext f
  simp [Function.comp_assoc]

end smashPow

/-- The smash power `X ↦ X^∧ι` as a functor of pointed types. -/
@[expose, simps]
noncomputable def smashPowFunctor (ι : Type v) : Pointed.{u} ⥤ Pointed.{max u v} where
  obj X := X.smashPow ι
  map g := smashPow.map ι g
  map_id _ := smashPow.map_id
  map_comp := smashPow.map_comp

namespace smashPow

variable {X Y Z : Pointed.{u}} {ι κ μ : Type v}

/-- The action of a bijection of index types on smash powers, reindexing the coordinates. -/
noncomputable def reindex (X : Pointed.{u}) (e : ι ≃ κ) : X.smashPow ι ⟶ X.smashPow κ :=
  lift (fun f ↦ mk (f ∘ e.symm)) fun f i hi ↦ mk_eq_point (e i) (by simp [hi])

@[simp]
lemma reindex_mk (e : ι ≃ κ) (f : ι → X) : (reindex X e).toFun (mk f) = mk (f ∘ e.symm) :=
  lift_mk _ _ f

@[simp]
lemma reindex_refl : reindex X (Equiv.refl ι) = 𝟙 (X.smashPow ι) := by
  ext f
  simp

@[simp]
lemma reindex_trans (e : ι ≃ κ) (e' : κ ≃ μ) :
    reindex X (e.trans e') = reindex X e ≫ reindex X e' := by
  ext f
  simp [Function.comp_assoc]

/-- Reindexing commutes with the smash power of a pointed map. -/
@[reassoc]
lemma map_reindex (g : X ⟶ Y) (e : ι ≃ κ) :
    map ι g ≫ reindex Y e = reindex X e ≫ map κ g := by
  ext f
  simp [Function.comp_assoc]

/-- Concatenation of classes of families, from `X^∧ι` and `X^∧κ` to `X^∧(ι ⊕ κ)`. -/
noncomputable def append (a : X.smashPow ι) (b : X.smashPow κ) : X.smashPow (ι ⊕ κ) :=
  (lift (fun f ↦ (lift (fun g ↦ mk (Sum.elim f g)) fun g k hk ↦
      mk_eq_point (.inr k) hk).toFun b) fun f i hi ↦ by
    induction b using ind with
    | point => exact Hom.map_point _
    | mk g => exact (lift_mk _ _ g).trans (mk_eq_point (f := Sum.elim f g) (.inl i) hi)).toFun a

@[simp]
lemma append_mk_mk (f : ι → X) (g : κ → X) : append (mk f) (mk g) = mk (Sum.elim f g) := by
  simp [append]

@[simp]
lemma append_point_left (b : X.smashPow κ) :
    append (X.smashPow ι).point b = (X.smashPow (ι ⊕ κ)).point :=
  Hom.map_point _

@[simp]
lemma append_point_right (a : X.smashPow ι) :
    append a (X.smashPow κ).point = (X.smashPow (ι ⊕ κ)).point := by
  induction a using ind with
  | point => exact append_point_left _
  | mk f => exact (lift_mk _ _ f).trans (Hom.map_point _)

/-- Concatenation commutes with the smash power of a pointed map. -/
lemma map_append (g : X ⟶ Y) (a : X.smashPow ι) (b : X.smashPow κ) :
    (map (ι ⊕ κ) g).toFun (append a b) = append ((map ι g).toFun a) ((map κ g).toFun b) := by
  induction a using ind with
  | point => simp [Hom.map_point]
  | mk f =>
    induction b using ind with
    | point => simp [Hom.map_point]
    | mk h => simp [Sum.comp_elim]

end smashPow

end Pointed
