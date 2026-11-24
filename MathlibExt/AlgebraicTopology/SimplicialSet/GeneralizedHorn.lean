/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Generalized horns and face preimages

The generalized horn indexed by an omitted set is the union of the faces
outside that set. Pulling back along an omitted face gives the corresponding
lower generalized horn. The native face-preimage Arrow isomorphism keeps
the original image map, face map, and ambient inclusion equation.

Source: Joyal–Tierney, *Quasi-categories vs Segal spaces*, arXiv
math/0607820v2, proofs of Lemmas 3.5 and 3.7.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet

/-- The union of the faces whose indices lie outside the omitted set `S`. -/
def generalizedHorn (n : ℕ) (S : Finset (Fin (n + 1))) :
    (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i : {i : Fin (n + 1) // i ∉ S}, stdSimplex.face {i.1}ᶜ

/-- Omitting one face gives the ordinary horn. -/
lemma generalizedHorn_singleton (n : ℕ) (i : Fin (n + 1)) :
    generalizedHorn.{u} n {i} = horn n i := by
  rw [horn_eq_iSup]
  ext d x
  simp [generalizedHorn]

/-- A simplex belongs precisely when it avoids a vertex outside the omitted set. -/
lemma mem_generalizedHorn_iff {n d : ℕ} (S : Finset (Fin (n + 1)))
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (generalizedHorn n S).obj (op ⦋d⦌) ↔
      ∃ i, i ∉ S ∧ ∀ j : Fin (d + 1), x j ≠ i := by
  simp [generalizedHorn, stdSimplex.mem_face_iff]

/-- Restoring an included face is the union with that face. -/
lemma generalizedHorn_insert {n : ℕ} (S : Finset (Fin (n + 1)))
    (t : Fin (n + 1)) (ht : t ∉ S) :
    generalizedHorn.{u} n S =
      stdSimplex.face {t}ᶜ ⊔ generalizedHorn n (insert t S) := by
  ext d x
  rcases d with ⟨⟨d⟩⟩
  simp only [Subfunctor.max_obj, Set.mem_union, mem_generalizedHorn_iff,
    stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases hit : i = t
    · subst i
      exact Or.inl hx
    · exact Or.inr ⟨i, by simp [hit, hi], hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨t, ht, hx⟩
    · exact ⟨i, fun h ↦ hi (Or.inr h), hx⟩

/-- Every face outside the omitted set is contained in the generalized horn. -/
lemma face_le_generalizedHorn {n : ℕ} (S : Finset (Fin (n + 1)))
    (t : Fin (n + 1)) (ht : t ∉ S) :
    stdSimplex.face.{u} {t}ᶜ ≤ generalizedHorn n S :=
  le_iSup_of_le ⟨t, ht⟩ le_rfl

/-- The omitted-set index pulled back along the face deleting `t`. -/
def lowerHornIndex {n : ℕ} (t : Fin (n + 2))
    (T : Finset (Fin (n + 2))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun k ↦ t.succAbove k ∈ T)

/-- Membership in the lower omitted set is literal inverse-image membership. -/
lemma mem_lowerHornIndex {n : ℕ} (t : Fin (n + 2))
    (T : Finset (Fin (n + 2))) (k : Fin (n + 1)) :
    k ∈ lowerHornIndex t T ↔ t.succAbove k ∈ T := by
  simp [lowerHornIndex]

/-- Pullback along an omitted face gives the lower generalized horn. -/
lemma generalizedHorn_preimage_δ {n : ℕ} (t : Fin (n + 2))
    (T : Finset (Fin (n + 2))) (ht : t ∈ T) :
    (generalizedHorn.{u} (n + 1) T).preimage (stdSimplex.δ t) =
      generalizedHorn n (lowerHornIndex t T) := by
  ext d x
  rcases d with ⟨⟨d⟩⟩
  rw [Subcomplex.preimage_obj, Set.mem_preimage, mem_generalizedHorn_iff,
    mem_generalizedHorn_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    have hit : i ≠ t := by rintro rfl; exact hi ht
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hit
    refine ⟨k, ?_, ?_⟩
    · simpa [mem_lowerHornIndex, hk] using hi
    · intro j h
      apply hx j
      change t.succAbove (x j) = i
      rw [h, hk]
  · rintro ⟨k, hk, hx⟩
    refine ⟨t.succAbove k, ?_, ?_⟩
    · simpa [mem_lowerHornIndex] using hk
    · intro j h
      exact hx j (Fin.succAbove_right_injective h)

/-- A nonempty omitted set remains nonempty after adding and then deleting a pivot. -/
lemma lowerHornIndex_nonempty {n : ℕ} (S : Finset (Fin (n + 2)))
    (t : Fin (n + 2)) (ht : t ∉ S) (hS : S.Nonempty) :
    (lowerHornIndex t (insert t S)).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  have hst : s ≠ t := by rintro rfl; exact ht hs
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hst
  refine ⟨k, (mem_lowerHornIndex _ _ _).2 ?_⟩
  rw [hk]
  exact Finset.mem_insert_of_mem hs

/-- The one-face enlargement is the literal bicartesian union square. -/
lemma generalizedHorn_insert_bicart_sq {n : ℕ}
    (S : Finset (Fin (n + 1))) (t : Fin (n + 1)) (ht : t ∉ S) :
    Subcomplex.BicartSq
      (stdSimplex.face.{u} {t}ᶜ ⊓ generalizedHorn n (insert t S))
      (generalizedHorn n (insert t S)) (stdSimplex.face {t}ᶜ)
      (generalizedHorn n S) where
  sup_eq := by rw [sup_comm, ← generalizedHorn_insert S t ht]
  inf_eq := inf_comm _ _

namespace stdSimplex

private lemma image_preimage_eq_inf_range {X Y : SSet.{u}} (D : Y.Subcomplex)
    (f : X ⟶ Y) : (D.preimage f).image f = D ⊓ Subcomplex.range f := by
  ext d x
  change x ∈ (f.app d) '' ((f.app d) ⁻¹' D.obj d) ↔
    x ∈ D.obj d ∩ Set.range (f.app d)
  rw [Set.image_preimage_eq_inter_range]

private lemma isIso_toImage_of_mono {X Y : SSet.{u}} (D : X.Subcomplex)
    (f : X ⟶ Y) [Mono f] : IsIso (D.toImage f) := by
  let : Mono (D.toImage f) := mono_of_mono_fac (D.toImage_ι f)
  exact isIso_of_mono_of_epi _

private def faceIntersectionIso {n : ℕ} (D : (Δ[n + 1] : SSet.{u}).Subcomplex)
    (t : Fin (n + 2)) :
    (D.preimage (stdSimplex.δ t) : SSet.{u}) ≅
      (stdSimplex.face {t}ᶜ ⊓ D).toSSet := by
  let : Mono (stdSimplex.δ t : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]) := by
    rw [← stdSimplex.faceSingletonComplIso_hom_ι t]
    infer_instance
  let : IsIso ((D.preimage (stdSimplex.δ t)).toImage (stdSimplex.δ t)) :=
    isIso_toImage_of_mono _ _
  exact asIso ((D.preimage (stdSimplex.δ t)).toImage (stdSimplex.δ t)) ≪≫
    Subcomplex.eqToIso (by
      rw [image_preimage_eq_inf_range, stdSimplex.range_δ, inf_comm])

private lemma faceIntersectionIso_hom {n : ℕ}
    (D : (Δ[n + 1] : SSet.{u}).Subcomplex) (t : Fin (n + 2)) :
    (faceIntersectionIso D t).hom ≫ Subcomplex.homOfLE inf_le_left =
      (D.preimage (stdSimplex.δ t)).ι ≫
        (stdSimplex.faceSingletonComplIso t).hom := by
  apply (cancel_mono (stdSimplex.face {t}ᶜ).ι).1
  simp only [faceIntersectionIso, Iso.trans_hom, asIso_hom,
    Subcomplex.eqToIso_hom, Category.assoc, Subcomplex.homOfLE_ι,
    Subcomplex.toImage_ι, stdSimplex.faceSingletonComplIso_hom_ι]

/-- The preimage inclusion and the original face-intersection inclusion are
isomorphic as complete arrows, using the actual image map and face map. -/
@[no_expose] def facePreimageArrowIso {n : ℕ}
    (D : (Δ[n + 1] : SSet.{u}).Subcomplex) (t : Fin (n + 2)) :
    Arrow.mk (D.preimage (stdSimplex.δ t)).ι ≅
      Arrow.mk (Subcomplex.homOfLE
        (inf_le_left : stdSimplex.face {t}ᶜ ⊓ D ≤ stdSimplex.face {t}ᶜ)) :=
  Arrow.isoMk (faceIntersectionIso D t) (stdSimplex.faceSingletonComplIso t)
    (faceIntersectionIso_hom D t)

/-- The right component is the native map identifying the face with its simplex. -/
lemma facePreimageArrowIso_hom_right {n : ℕ}
    (D : (Δ[n + 1] : SSet.{u}).Subcomplex) (t : Fin (n + 2)) :
    (facePreimageArrowIso D t).hom.right =
      (stdSimplex.faceSingletonComplIso t).hom := by
  rfl

/-- The left component preserves the actual ambient inclusion along the face. -/
lemma facePreimageArrowIso_hom_left_ι {n : ℕ}
    (D : (Δ[n + 1] : SSet.{u}).Subcomplex) (t : Fin (n + 2)) :
    (facePreimageArrowIso D t).hom.left ≫
        (stdSimplex.face {t}ᶜ ⊓ D).ι =
      (D.preimage (stdSimplex.δ t)).ι ≫ stdSimplex.δ t := by
  change (faceIntersectionIso D t).hom ≫ (stdSimplex.face {t}ᶜ ⊓ D).ι = _
  calc
    (faceIntersectionIso D t).hom ≫ (stdSimplex.face {t}ᶜ ⊓ D).ι =
        ((faceIntersectionIso D t).hom ≫ Subcomplex.homOfLE inf_le_left) ≫
          (stdSimplex.face {t}ᶜ).ι := by
      rw [Category.assoc, Subcomplex.homOfLE_ι]
    _ = ((D.preimage (stdSimplex.δ t)).ι ≫
        (stdSimplex.faceSingletonComplIso t).hom) ≫ (stdSimplex.face {t}ᶜ).ι := by
      rw [faceIntersectionIso_hom]
    _ = _ := by rw [Category.assoc, stdSimplex.faceSingletonComplIso_hom_ι]

end stdSimplex
end SSet
