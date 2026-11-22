/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.SaturatedCoproducts
import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralizedHorn
import MathlibExt.CategoryTheory.MorphismProperty.CodomainRetracts

/-!
# Spine saturation for inner anodyne maps

A saturated class of simplicial-set monomorphisms with right cancellation
contains every inner anodyne map if it contains the consecutive-edge spine
inclusions in dimensions at least two. The proof first attaches the two
outer faces to each spine, then inducts on generalized inner horns.

The raw Rezk spine in dimension zero is empty, so the statement retains the
source's dimension-at-least-two premise. The dimension-one identity is used
only as a derived helper. Coproduct closure and arbitrary arrow-retract
closure are derived from the source saturation data.

Source: Joyal–Tierney, *Quasi-categories vs Segal spaces*,
arXiv math/0607820v2, Lemma 3.5.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet
open Rezk

private lemma mem_spine_iff {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (spineSubcomplex.{u} n).obj (op ⦋d⦌) ↔
      ∃ (i : Fin n) (f : ⦋d⦌ ⟶ ⦋1⦌),
        f ≫ SimplexCategory.mkOfSucc i = stdSimplex.objEquiv x := by
  simp only [spineSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subfunctor.range_obj]
  constructor
  · rintro ⟨i, y, hy⟩
    refine ⟨i, stdSimplex.objEquiv y, ?_⟩
    apply stdSimplex.objEquiv.symm.injective
    rw [stdSimplex.objEquiv_symm_comp, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
    exact hy
  · rintro ⟨i, f, hf⟩
    refine ⟨i, stdSimplex.objEquiv.symm f, ?_⟩
    rw [← stdSimplex.objEquiv_symm_comp, hf, Equiv.symm_apply_apply]

private lemma mkOfSucc_apply_val {n : ℕ} (i : Fin n) (j : Fin 2) :
    ((SimplexCategory.mkOfSucc i).toOrderHom j).val = i.val + j.val := by
  fin_cases j <;> rfl

private lemma mem_spine_iff_span_le_one {n d : ℕ} (hn : 1 ≤ n)
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (spineSubcomplex.{u} n).obj (op ⦋d⦌) ↔
      (x (Fin.last d)).val ≤ (x (0 : Fin (d + 1))).val + 1 := by
  constructor
  · intro hx
    obtain ⟨i, f, hf⟩ := (mem_spine_iff x).mp hx
    have h0 := congrArg (fun q : ⦋d⦌ ⟶ ⦋n⦌ =>
      (q.toOrderHom (0 : Fin (d + 1))).val) hf
    have hl := congrArg (fun q : ⦋d⦌ ⟶ ⦋n⦌ =>
      (q.toOrderHom (Fin.last d)).val) hf
    change ((SimplexCategory.mkOfSucc i).toOrderHom
      (f.toOrderHom (0 : Fin (d + 1)))).val = _ at h0
    change ((SimplexCategory.mkOfSucc i).toOrderHom
      (f.toOrderHom (Fin.last d))).val = _ at hl
    rw [mkOfSucc_apply_val] at h0 hl
    change i.val + (f.toOrderHom (0 : Fin (d + 1))).val =
      (x (0 : Fin (d + 1))).val at h0
    change i.val + (f.toOrderHom (Fin.last d)).val = (x (Fin.last d)).val at hl
    have hlast : (f.toOrderHom (Fin.last d)).val < 2 :=
      (f.toOrderHom (Fin.last d)).isLt
    omega
  · intro hx
    let a := (x (0 : Fin (d + 1))).val
    by_cases ha : a < n
    · let i : Fin n := ⟨a, ha⟩
      let f : ⦋d⦌ ⟶ ⦋1⦌ := SimplexCategory.Hom.mk
        { toFun := fun j => ⟨(x j).val - a, by
            have hmin : a ≤ (x j).val :=
              stdSimplex.monotone_apply x (Fin.zero_le j)
            have hmax : (x j).val ≤ (x (Fin.last d)).val :=
              stdSimplex.monotone_apply x (Fin.le_last j)
            change (x j).val - a < 2
            dsimp [a] at hmin ⊢
            omega⟩
          monotone' := by
            intro j k hjk
            change (x j).val - a ≤ (x k).val - a
            exact Nat.sub_le_sub_right (stdSimplex.monotone_apply x hjk) a }
      apply (mem_spine_iff x).mpr
      refine ⟨i, f, ?_⟩
      ext j
      change ((SimplexCategory.mkOfSucc i).toOrderHom (f.toOrderHom j)).val =
        (x j).val
      rw [mkOfSucc_apply_val]
      have hmin : a ≤ (x j).val := stdSimplex.monotone_apply x (Fin.zero_le j)
      change a + ((x j).val - a) = (x j).val
      omega
    · let i : Fin n := ⟨n - 1, by omega⟩
      apply (mem_spine_iff x).mpr
      refine ⟨i, SimplexCategory.const _ _ (1 : Fin 2), ?_⟩
      ext j
      change ((SimplexCategory.mkOfSucc i).toOrderHom (1 : Fin 2)).val =
        (x j).val
      rw [mkOfSucc_apply_val]
      have hmin : a ≤ (x j).val := stdSimplex.monotone_apply x (Fin.zero_le j)
      have hj := (x j).isLt
      dsimp [i, a] at *
      omega

private lemma spine_preimage_first_face (n : ℕ) :
    (spineSubcomplex.{u} (n + 2)).preimage
        (stdSimplex.δ (0 : Fin (n + 3))) = spineSubcomplex (n + 1) := by
  ext d x
  rcases d with ⟨⟨d⟩⟩
  rw [Subcomplex.preimage_obj, Set.mem_preimage,
    mem_spine_iff_span_le_one (n := n + 2) (d := d) (by omega),
    mem_spine_iff_span_le_one (n := n + 1) (d := d) (by omega)]
  change ((0 : Fin (n + 3)).succAbove (x (Fin.last d))).val ≤
      ((0 : Fin (n + 3)).succAbove (x (0 : Fin (d + 1)))).val + 1 ↔ _
  simp only [Fin.succAbove_zero]
  change (x (Fin.last d)).val + 1 ≤ (x (0 : Fin (d + 1))).val + 1 + 1 ↔ _
  omega

private lemma spine_preimage_last_face (n : ℕ) :
    (spineSubcomplex.{u} (n + 2)).preimage
        (stdSimplex.δ (Fin.last (n + 2))) = spineSubcomplex (n + 1) := by
  ext d x
  rcases d with ⟨⟨d⟩⟩
  rw [Subcomplex.preimage_obj, Set.mem_preimage,
    mem_spine_iff_span_le_one (n := n + 2) (d := d) (by omega),
    mem_spine_iff_span_le_one (n := n + 1) (d := d) (by omega)]
  change ((Fin.last (n + 2)).succAbove (x (Fin.last d))).val ≤
      ((Fin.last (n + 2)).succAbove (x (0 : Fin (d + 1)))).val + 1 ↔ _
  have hlast (k : Fin (n + 2)) :
      (Fin.last (n + 2)).succAbove k = k.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ k.isLt
  simp only [hlast]
  rfl

private lemma last_face_preimage_first_face (n : ℕ) :
    (stdSimplex.face.{u} {Fin.last (n + 2)}ᶜ).preimage
        (stdSimplex.δ (0 : Fin (n + 3))) =
      stdSimplex.face {Fin.last (n + 1)}ᶜ := by
  ext d x
  rcases d with ⟨⟨d⟩⟩
  rw [Subcomplex.preimage_obj, Set.mem_preimage,
    stdSimplex.mem_face_iff, stdSimplex.mem_face_iff]
  simp only [Finset.mem_compl, Finset.mem_singleton]
  change (∀ j : Fin (d + 1), (0 : Fin (n + 3)).succAbove (x j) ≠
      Fin.last (n + 2)) ↔ ∀ j : Fin (d + 1), x j ≠ Fin.last (n + 1)
  simp only [Fin.succAbove_zero]
  constructor
  · intro h j hj
    apply h j
    rw [hj]
    rfl
  · intro h j hj
    apply h j
    apply Fin.ext
    have hv := congrArg Fin.val hj
    change (x j).val + 1 = n + 2 at hv
    change (x j).val = n + 1
    omega

private lemma spine_union_last_face_preimage_first_face (n : ℕ) :
    (spineSubcomplex.{u} (n + 2) ⊔ stdSimplex.face {Fin.last (n + 2)}ᶜ).preimage
        (stdSimplex.δ (0 : Fin (n + 3))) =
      spineSubcomplex (n + 1) ⊔ stdSimplex.face {Fin.last (n + 1)}ᶜ := by
  rw [Subcomplex.preimage_max, spine_preimage_first_face,
    last_face_preimage_first_face]

private lemma spine_one_eq_top : spineSubcomplex.{u} 1 = ⊤ := by
  ext d x
  rcases d with ⟨⟨d⟩⟩
  simp only [Subfunctor.top_obj, Set.mem_univ, iff_true]
  apply (mem_spine_iff_span_le_one (by omega) x).2
  have hl : (x (Fin.last d)).val < 2 := (x (Fin.last d)).isLt
  omega

private lemma spine_le_end_faces (n : ℕ) (hn : 2 ≤ n) :
    spineSubcomplex.{u} n ≤
      stdSimplex.face {0}ᶜ ⊔ stdSimplex.face {Fin.last n}ᶜ := by
  intro d x hx
  rcases d with ⟨⟨d⟩⟩
  have hspan := (mem_spine_iff_span_le_one (by omega) x).1 hx
  change x ∈ (stdSimplex.face {0}ᶜ).obj _ ∨
    x ∈ (stdSimplex.face {Fin.last n}ᶜ).obj _
  by_cases h0 : (x (0 : Fin (d + 1))).val = 0
  · right
    apply (stdSimplex.mem_face_iff _ x).2
    intro j
    simp only [Finset.mem_compl, Finset.mem_singleton]
    intro hj
    have hmax : (x j).val ≤ (x (Fin.last d)).val :=
      stdSimplex.monotone_apply x (Fin.le_last j)
    have hv := congrArg Fin.val hj
    change (x j).val = n at hv
    omega
  · left
    apply (stdSimplex.mem_face_iff _ x).2
    intro j
    simp only [Finset.mem_compl, Finset.mem_singleton]
    intro hj
    have hmin : (x (0 : Fin (d + 1))).val ≤ (x j).val :=
      stdSimplex.monotone_apply x (Fin.zero_le j)
    have hv := congrArg Fin.val hj
    change (x j).val = 0 at hv
    omega

private lemma spine_ι_mem_of_spines (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] [P.RespectsIso]
    (hspine : ∀ n, 2 ≤ n → P (spineSubcomplex.{u} n).ι)
    (n : ℕ) (hn : 1 ≤ n) : P (spineSubcomplex.{u} n).ι := by
  by_cases h2 : 2 ≤ n
  · exact hspine n h2
  · have h1 : n = 1 := by omega
    subst n
    rw [spine_one_eq_top]
    exact P.of_isIso _

private lemma spine_to_union_last_mem (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] [P.RespectsIso] [P.IsStableUnderCobaseChange]
    (hspine : ∀ n, 2 ≤ n → P (spineSubcomplex.{u} n).ι)
    (n : ℕ) (hn : 1 ≤ n) :
    P (Subcomplex.homOfLE
      (le_sup_left : spineSubcomplex.{u} n ≤
        spineSubcomplex n ⊔ stdSimplex.face {Fin.last n}ᶜ)) := by
  rcases n with _ | _ | n
  · omega
  · have he : spineSubcomplex.{u} 1 ⊔ stdSimplex.face {Fin.last 1}ᶜ =
        spineSubcomplex 1 := by rw [spine_one_eq_top, top_sup_eq]
    let e := Subcomplex.eqToIso he.symm
    have hh : Subcomplex.homOfLE
        (le_sup_left : spineSubcomplex.{u} 1 ≤
          spineSubcomplex 1 ⊔ stdSimplex.face {Fin.last 1}ᶜ) = e.hom := by
      simp only [e, Subcomplex.eqToIso_hom]
    rw [hh]
    exact P.of_isIso _
  · let D := spineSubcomplex.{u} (n + 2)
    let F : (Δ[n + 2] : SSet.{u}).Subcomplex :=
      stdSimplex.face {Fin.last (n + 2)}ᶜ
    let sq : Subcomplex.BicartSq (F ⊓ D) D F (D ⊔ F) :=
      { sup_eq := rfl
        inf_eq := inf_comm _ _ }
    have hpre : P (D.preimage (stdSimplex.δ (Fin.last (n + 2)))).ι := by
      rw [spine_preimage_last_face]
      exact spine_ι_mem_of_spines P hspine (n + 1) (by omega)
    exact P.of_isPushout sq.isPushout
      ((P.arrow_mk_iso_iff (stdSimplex.facePreimageArrowIso D
        (Fin.last (n + 2)))).1 hpre)

private lemma spine_union_last_ι_mem (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] [P.RespectsIso] [P.IsStableUnderCobaseChange]
    (hcancel : ∀ {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono f → Mono g → P f → P (f ≫ g) → P g)
    (hspine : ∀ n, 2 ≤ n → P (spineSubcomplex.{u} n).ι)
    (n : ℕ) (hn : 1 ≤ n) :
    P (spineSubcomplex.{u} n ⊔ stdSimplex.face {Fin.last n}ᶜ).ι := by
  exact hcancel (Subcomplex.homOfLE le_sup_left)
    (spineSubcomplex.{u} n ⊔ stdSimplex.face {Fin.last n}ᶜ).ι
    inferInstance inferInstance (spine_to_union_last_mem P hspine n hn)
    (by simpa using spine_ι_mem_of_spines P hspine n hn)

private lemma spine_to_end_faces_mem (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] [P.RespectsIso] [P.IsStableUnderCobaseChange]
    (hcancel : ∀ {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono f → Mono g → P f → P (f ≫ g) → P g)
    (hspine : ∀ n, 2 ≤ n → P (spineSubcomplex.{u} n).ι)
    (n : ℕ) (hn : 2 ≤ n) :
    P (Subcomplex.homOfLE (spine_le_end_faces n hn)) := by
  rcases n with _ | _ | n
  · omega
  · omega
  · let D := spineSubcomplex.{u} (n + 2) ⊔
      stdSimplex.face {Fin.last (n + 2)}ᶜ
    let F : (Δ[n + 2] : SSet.{u}).Subcomplex := stdSimplex.face {0}ᶜ
    let E : (Δ[n + 2] : SSet.{u}).Subcomplex :=
      stdSimplex.face {0}ᶜ ⊔ stdSimplex.face {Fin.last (n + 2)}ᶜ
    let sq : Subcomplex.BicartSq (F ⊓ D) D F E :=
      { sup_eq := by
          symm
          change stdSimplex.face {0}ᶜ ⊔ stdSimplex.face {Fin.last (n + 2)}ᶜ =
            (spineSubcomplex (n + 2) ⊔ stdSimplex.face {Fin.last (n + 2)}ᶜ) ⊔
              stdSimplex.face {0}ᶜ
          apply le_antisymm
          · exact sup_le le_sup_right (le_trans le_sup_right le_sup_left)
          · exact sup_le (sup_le (spine_le_end_faces (n + 2) (by omega))
              le_sup_right) le_sup_left
        inf_eq := inf_comm _ _ }
    have hpre : P (D.preimage (stdSimplex.δ (0 : Fin (n + 3)))).ι := by
      rw [spine_union_last_face_preimage_first_face]
      exact spine_union_last_ι_mem P hcancel hspine (n + 1) (by omega)
    have henlarge : P (Subcomplex.homOfLE sq.le₂₄) :=
      P.of_isPushout sq.isPushout
        ((P.arrow_mk_iso_iff (stdSimplex.facePreimageArrowIso D
          (0 : Fin (n + 3)))).1 hpre)
    have hcomp : P (Subcomplex.homOfLE le_sup_left ≫
        Subcomplex.homOfLE sq.le₂₄) :=
      P.comp_mem _ _ (spine_to_union_last_mem P hspine (n + 2) (by omega)) henlarge
    have heq : Subcomplex.homOfLE le_sup_left ≫ Subcomplex.homOfLE sq.le₂₄ =
        Subcomplex.homOfLE (spine_le_end_faces (n + 2) (by omega)) := by
      apply (cancel_mono E.ι).1
      rw [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.homOfLE_ι,
        Subcomplex.homOfLE_ι]
    exact heq ▸ hcomp

private lemma lowerHornIndex_inner {n : ℕ} (t : Fin (n + 2))
    (ht0 : 0 < t) (htlast : t < Fin.last (n + 1))
    (T : Finset (Fin (n + 2)))
    (hT : ∀ k ∈ T, 0 < k ∧ k < Fin.last (n + 1)) :
    ∀ k ∈ lowerHornIndex t T, 0 < k ∧ k < Fin.last n := by
  intro k hk
  have htk := hT _ ((mem_lowerHornIndex _ _ _).1 hk)
  constructor
  · by_cases hk0 : k = 0
    · subst k
      have hzero : t.succAbove (0 : Fin (n + 1)) = 0 :=
        Fin.succAbove_of_castSucc_lt _ _ ht0
      rw [hzero] at htk
      exact (lt_irrefl _ htk.1).elim
    · have hv : k.val ≠ 0 := by
        intro hv
        exact hk0 (Fin.ext hv)
      change 0 < k.val
      omega
  · by_cases hklast : k = Fin.last n
    · subst k
      have hle : t ≤ (Fin.last n).castSucc := by
        change t.val ≤ n
        have ht : t.val < n + 1 := htlast
        omega
      have hlast : t.succAbove (Fin.last n) = Fin.last (n + 1) := by
        rw [Fin.succAbove_of_le_castSucc _ _ hle]
        exact Fin.succ_last n
      rw [hlast] at htk
      exact (lt_irrefl _ htk.2).elim
    · exact lt_of_le_of_ne (Fin.le_last k) hklast

private lemma spine_le_generalizedHorn {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin (n + 1)))
    (hS : ∀ k ∈ S, 0 < k ∧ k < Fin.last n) :
    spineSubcomplex.{u} n ≤ generalizedHorn n S :=
  (spine_le_end_faces n hn).trans (sup_le
    (face_le_generalizedHorn S 0 (fun h ↦ lt_irrefl _ (hS _ h).1))
    (face_le_generalizedHorn S (Fin.last n) (fun h ↦ lt_irrefl _ (hS _ h).2)))

private lemma generalizedHorn_eq_end_faces {n : ℕ}
    (S : Finset (Fin (n + 1)))
    (hS : ∀ k ∈ S, 0 < k ∧ k < Fin.last n)
    (hinterior : ¬ ∃ k, k ∉ S ∧ 0 < k ∧ k < Fin.last n) :
    generalizedHorn.{u} n S =
      stdSimplex.face {0}ᶜ ⊔ stdSimplex.face {Fin.last n}ᶜ := by
  apply le_antisymm
  · unfold generalizedHorn
    apply iSup_le
    rintro ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst k
      exact le_sup_left
    by_cases hklast : k = Fin.last n
    · subst k
      exact le_sup_right
    have hp : 0 < k := by
      have hv : k.val ≠ 0 := fun h ↦ hk0 (Fin.ext h)
      change 0 < k.val
      omega
    exact (hinterior ⟨k, hk, hp, lt_of_le_of_ne (Fin.le_last k) hklast⟩).elim
  · exact sup_le
      (face_le_generalizedHorn S 0 (fun h ↦ lt_irrefl _ (hS _ h).1))
      (face_le_generalizedHorn S (Fin.last n) (fun h ↦ lt_irrefl _ (hS _ h).2))

private lemma homOfLE_comp_eqToIso {X : SSet.{u}} {A B C : X.Subcomplex}
    (hAB : A ≤ B) (hAC : A ≤ C) (hBC : B = C) :
    Subcomplex.homOfLE hAB ≫ (Subcomplex.eqToIso hBC).hom =
      Subcomplex.homOfLE hAC := by
  apply (cancel_mono C.ι).1
  simp only [Category.assoc, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι]

private lemma spine_to_generalizedHorn_mem (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] [P.RespectsIso] [P.IsStableUnderCobaseChange]
    (hcancel : ∀ {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono f → Mono g → P f → P (f ≫ g) → P g)
    (hspine : ∀ n, 2 ≤ n → P (spineSubcomplex.{u} n).ι) :
    ∀ (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin (n + 1)))
      (_ : S.Nonempty) (hS : ∀ k ∈ S, 0 < k ∧ k < Fin.last n),
      P (Subcomplex.homOfLE (spine_le_generalizedHorn hn S hS)) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ihdim =>
    intro hn S
    generalize hk : Sᶜ.card = k
    induction k using Nat.strong_induction_on generalizing S with
    | h k ihcard =>
      intro hS hinner
      by_cases hinterior : ∃ t, t ∉ S ∧ 0 < t ∧ t < Fin.last (n + 1)
      · obtain ⟨t, ht, ht0, htlast⟩ := hinterior
        let T := insert t S
        have hTinner : ∀ a ∈ T, 0 < a ∧ a < Fin.last (n + 1) := by
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact ⟨ht0, htlast⟩
          · exact hinner a ha
        have hcard : Tᶜ.card < k := by
          dsimp [T]
          rw [← hk, Finset.compl_insert]
          exact Finset.card_erase_lt_of_mem (by simpa using ht)
        have hupper : P (Subcomplex.homOfLE
            (spine_le_generalizedHorn hn T hTinner)) :=
          ihcard _ hcard T rfl (Finset.insert_nonempty _ _) hTinner
        let U := lowerHornIndex t T
        have hUne : U.Nonempty := lowerHornIndex_nonempty S t ht hS
        have hUinner : ∀ a ∈ U, 0 < a ∧ a < Fin.last n :=
          lowerHornIndex_inner t ht0 htlast T hTinner
        have hnlow : 2 ≤ n := by
          obtain ⟨a, ha⟩ := hUne
          have hp : 0 < a.val := (hUinner a ha).1
          have hl : a.val < n := (hUinner a ha).2
          omega
        have hlowerSpine : P (Subcomplex.homOfLE
            (spine_le_generalizedHorn hnlow U hUinner)) :=
          ihdim hnlow U hUne hUinner
        have hlower : P (generalizedHorn n U).ι :=
          hcancel (Subcomplex.homOfLE (spine_le_generalizedHorn hnlow U hUinner))
            (generalizedHorn n U).ι inferInstance inferInstance hlowerSpine
            (by simpa using hspine n hnlow)
        have hpre : P ((generalizedHorn (n + 1) T).preimage
            (stdSimplex.δ t)).ι := by
          rw [generalizedHorn_preimage_δ t T (Finset.mem_insert_self _ _)]
          exact hlower
        let sq := generalizedHorn_insert_bicart_sq.{u} S t ht
        have henlarge : P (Subcomplex.homOfLE sq.le₂₄) :=
          P.of_isPushout sq.isPushout
            ((P.arrow_mk_iso_iff (stdSimplex.facePreimageArrowIso
              (generalizedHorn (n + 1) T) t)).1 hpre)
        have hcomp : P (Subcomplex.homOfLE
            (spine_le_generalizedHorn hn T hTinner) ≫ Subcomplex.homOfLE sq.le₂₄) :=
          P.comp_mem _ _ hupper henlarge
        simpa only [Subcomplex.homOfLE_comp] using hcomp
      · have hGH := generalizedHorn_eq_end_faces S hinner hinterior
        apply (P.cancel_right_of_respectsIso
          (Subcomplex.homOfLE (spine_le_generalizedHorn hn S hinner))
          (Subcomplex.eqToIso hGH).hom).1
        rw [homOfLE_comp_eqToIso _ (spine_le_end_faces (n + 1) hn) hGH]
        exact spine_to_end_faces_mem P hcancel hspine (n + 1) hn

private lemma inner_horn_ι_mem_of_spines (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] [P.RespectsIso] [P.IsStableUnderCobaseChange]
    (hcancel : ∀ {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono f → Mono g → P f → P (f ≫ g) → P g)
    (hspine : ∀ n, 2 ≤ n → P (spineSubcomplex.{u} n).ι)
    (n : ℕ) (i : Fin (n + 3)) (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) :
    P (horn (n + 2) i).ι := by
  rw [← generalizedHorn_singleton]
  have hinner : ∀ k ∈ ({i} : Finset (Fin (n + 3))),
      0 < k ∧ k < Fin.last (n + 2) := by
    intro k hk
    rcases Finset.mem_singleton.mp hk with rfl
    exact ⟨h0, hlast⟩
  exact hcancel (Subcomplex.homOfLE (spine_le_generalizedHorn (by omega) {i} hinner))
    (generalizedHorn (n + 2) {i}).ι inferInstance inferInstance
    (spine_to_generalizedHorn_mem P hcancel hspine (n + 2) (by omega) {i}
      (Finset.singleton_nonempty _) hinner)
    (by simpa using hspine (n + 2) (by omega))

private theorem innerHornInclusions_le_of_spines (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] [P.RespectsIso] [P.IsStableUnderCobaseChange]
    (hcancel : ∀ {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono f → Mono g → P f → P (f ≫ g) → P g)
    (hspine : ∀ n, 2 ≤ n → P (spineSubcomplex.{u} n).ι) :
    innerHornInclusions ≤ P := by
  intro X Y f hf
  obtain ⟨i, h0, hlast⟩ := hf
  exact inner_horn_ι_mem_of_spines P hcancel hspine _ i h0 hlast

/-- Joyal–Tierney Lemma 3.5 with the source saturation contract: coproduct
closure and arbitrary-arrow retract closure are derived. -/
theorem innerAnodyneExtensions_le_of_spines (P : MorphismProperty SSet.{u})
    [P.RespectsIso] [P.IsMultiplicative] [P.IsStableUnderCobaseChange]
    [P.IsStableUnderTransfiniteComposition.{u}]
    (hmono : P ≤ MorphismProperty.monomorphisms SSet.{u})
    (hcod : ∀ (X : SSet.{u}) (A B : Under X), Retract A B → P B.hom → P A.hom)
    (hcancel : ∀ {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono f → Mono g → P f → P (f ≫ g) → P g)
    (hspine : ∀ n, 2 ≤ n → P (Rezk.spineSubcomplex.{u} n).ι) :
    innerAnodyneExtensions ≤ P := by
  let : P.IsStableUnderRetracts :=
    MorphismProperty.isStableUnderRetracts_of_codomainRetracts P hcod
  let : P.IsStableUnderCoproducts.{u} :=
    isStableUnderCoproducts_of_le_monomorphisms P hmono
  have hgen : MorphismProperty.coproducts.{u} innerHornInclusions ≤ P :=
    (MorphismProperty.coproducts_monotone
      (innerHornInclusions_le_of_spines P hcancel hspine)).trans P.coproducts_le
  rwa [innerAnodyneExtensions_eq_retracts_transfiniteCompositions,
    MorphismProperty.retracts_le_iff, MorphismProperty.transfiniteCompositions_le_iff,
    MorphismProperty.pushouts_le_iff]

end SSet
