/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SegalOuterHornCovers
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The original U-to-C filtration by inner horns

The proper faces containing zero and one are adjoined in increasing
cardinality. Their original inclusion category is retained: the auxiliary
lexicographic order is used only to enumerate a finite image of keys.
Every nonidentity attachment is the original inner horn of index one.

Source: Rezk (2001), Lemma 11.11. The finite inner-horn filtration proves
locality of the same original inclusion without an arbitrary-limit argument.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Rezk

private def cFaceTie (m : ℕ) :
    outerHornCFaceIndex m ≃ Fin (Fintype.card (outerHornCFaceIndex m)) :=
  Fintype.equivFin _

private def cFaceKey (m : ℕ) : outerHornCFaceIndex m ↪
    (ℕ ×ₗ Fin (Fintype.card (outerHornCFaceIndex m))) where
  toFun S := toLex (S.val.card, cFaceTie m S)
  inj' := by
    intro S T h
    apply (cFaceTie m).injective
    exact congrArg (fun z => (ofLex z).2) h

private def cFaceKeys (m : ℕ) :
    Finset (ℕ ×ₗ Fin (Fintype.card (outerHornCFaceIndex m))) :=
  Finset.univ.map (cFaceKey m)

private theorem cFaceKeys_card (m : ℕ) :
    (cFaceKeys m).card = Fintype.card (outerHornCFaceIndex m) := by
  simp [cFaceKeys]

private def cFaceKeyEquiv (m : ℕ) : outerHornCFaceIndex m ≃ cFaceKeys m where
  toFun S := ⟨cFaceKey m S, Finset.mem_map.mpr ⟨S, Finset.mem_univ S, rfl⟩⟩
  invFun z := (cFaceTie m).symm (ofLex z.val).2
  left_inv S := by
    change (cFaceTie m).symm (cFaceTie m S) = S
    exact (cFaceTie m).symm_apply_apply S
  right_inv z := by
    rcases z with ⟨z, hz⟩
    obtain ⟨S, _, hS⟩ := Finset.mem_map.mp hz
    apply Subtype.ext
    change cFaceKey m ((cFaceTie m).symm (ofLex z).2) = z
    rw [← hS]
    change cFaceKey m ((cFaceTie m).symm (cFaceTie m S)) = cFaceKey m S
    rw [Equiv.symm_apply_apply]

private def cFaceKeyOrderIso (m : ℕ) :
    Fin (Fintype.card (outerHornCFaceIndex m)) ≃o cFaceKeys m :=
  (cFaceKeys m).orderIsoOfFin (cFaceKeys_card m)

/-- The constructed enumeration retains the original face index as a plain type. -/
def outerHornCEnumeration (m : ℕ) :
    Fin (Fintype.card (outerHornCFaceIndex m)) ≃ outerHornCFaceIndex m := by
  exact (cFaceKeyOrderIso m).toEquiv.trans (cFaceKeyEquiv m).symm

/-- Every original face is recovered from its original enumeration position. -/
theorem outerHornCEnumeration_apply_symm (m : ℕ) (S : outerHornCFaceIndex m) :
    outerHornCEnumeration m ((outerHornCEnumeration m).symm S) = S :=
  (outerHornCEnumeration m).apply_symm_apply S

/-- The inverse coordinate recovers every original enumeration position. -/
theorem outerHornCEnumeration_symm_apply (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    (outerHornCEnumeration m).symm (outerHornCEnumeration m i) = i :=
  (outerHornCEnumeration m).symm_apply_apply i

private theorem cFaceKey_enumeration (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    cFaceKey m (outerHornCEnumeration m i) = (cFaceKeyOrderIso m i).val := by
  change (cFaceKeyEquiv m ((cFaceKeyEquiv m).symm (cFaceKeyOrderIso m i))).val = _
  rw [Equiv.apply_symm_apply]

/-- Increasing enumeration positions have nondecreasing original cardinalities. -/
theorem outerHornCEnumeration_card_mono (m : ℕ)
    {i j : Fin (Fintype.card (outerHornCFaceIndex m))} (h : i ≤ j) :
    (outerHornCEnumeration m i).val.card ≤ (outerHornCEnumeration m j).val.card := by
  have hk : (cFaceKeyOrderIso m i).val ≤ (cFaceKeyOrderIso m j).val :=
    (cFaceKeyOrderIso m).monotone h
  have hf := Prod.Lex.monotone_fst _ _ hk
  rw [← cFaceKey_enumeration m i, ← cFaceKey_enumeration m j] at hf
  exact hf

/-- Every strict original lower face occurs before its parent face. -/
theorem outerHornCEnumeration_lower_before (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) (T : outerHornCFaceIndex m)
    (hT : T.val ⊂ (outerHornCEnumeration m i).val) :
    ((outerHornCEnumeration m).symm T).val < i.val := by
  by_contra h
  have hi : i ≤ (outerHornCEnumeration m).symm T := Nat.le_of_not_gt h
  have hc := outerHornCEnumeration_card_mono m hi
  rw [outerHornCEnumeration_apply_symm] at hc
  exact (not_le_of_gt (Finset.card_lt_card hT)) hc

private def cFacePrefix (m n : ℕ) : Finset (Fin (Fintype.card (outerHornCFaceIndex m))) :=
  Finset.univ.filter (fun i => i.val < n)

private theorem cFacePrefix_succ (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    cFacePrefix m (i.val + 1) = insert i (cFacePrefix m i.val) := by
  ext j
  simp only [cFacePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · intro h
    by_cases hj : j.val = i.val
    · exact Or.inl (Fin.ext hj)
    · exact Or.inr (by omega)
  · rintro (rfl | h)
    · omega
    · omega

/-- Each original prefix stage is U together with its preceding original faces. -/
def outerHornCStage (m n : ℕ) : (Δ[m + 2] : SSet.{u}).Subcomplex := by
  exact outerHornCU m ⊔ (cFacePrefix m n).sup
    (fun i => stdSimplex.face (outerHornCEnumeration m i).val)

/-- Stage membership retains the original word and its original face witness. -/
theorem mem_outerHornCStage_iff {m n d : ℕ} (a : (Δ[m + 2] : SSet.{u}) _⦋d⦌) :
    a ∈ (outerHornCStage m n).obj (op ⦋d⦌) ↔
      a ∈ (outerHornCU m).obj (op ⦋d⦌) ∨
      ∃ i : Fin (Fintype.card (outerHornCFaceIndex m)), i.val < n ∧
        a ∈ (stdSimplex.face (outerHornCEnumeration m i).val).obj (op ⦋d⦌) := by
  rw [outerHornCStage, Finset.sup_eq_iSup]
  change a ∈ (outerHornCU m).obj (op ⦋d⦌) ∨
      a ∈ (⨆ i ∈ cFacePrefix m n,
        stdSimplex.face (outerHornCEnumeration m i).val).obj (op ⦋d⦌) ↔ _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, cFacePrefix,
    Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]

/-- The original initial stage is exactly U. -/
theorem outerHornCStage_zero (m : ℕ) : outerHornCStage.{u} m 0 = outerHornCU m := by
  simp [outerHornCStage, cFacePrefix]

/-- Every original prefix stage is a subcomplex of the same C. -/
theorem outerHornCStage_le_C (m n : ℕ) :
    outerHornCStage.{u} m n ≤ outerHornC (m + 2) := by
  apply sup_le (outerHornCU_le_C m)
  exact Finset.sup_le (fun i _ => outerHornCFace_le_C (outerHornCEnumeration m i))

/-- Original prefix inclusions are monotone in their actual positions. -/
theorem outerHornCStage_mono (m : ℕ) {n p : ℕ} (h : n ≤ p) :
    outerHornCStage.{u} m n ≤ outerHornCStage m p := by
  apply sup_le_sup_left
  apply Finset.sup_le
  intro i hi
  have hip : i ∈ cFacePrefix m p := by
    simp only [cFacePrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi h
  exact Finset.le_sup (f := fun j =>
    stdSimplex.face.{u} (outerHornCEnumeration m j).val) hip

/-- Adjoining an original face gives the literal next union stage. -/
theorem outerHornCStage_succ (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    outerHornCStage.{u} m (i.val + 1) =
      outerHornCStage m i.val ⊔ stdSimplex.face (outerHornCEnumeration m i).val := by
  rw [outerHornCStage, cFacePrefix_succ, Finset.sup_insert]
  simp only [outerHornCStage]
  ac_rfl

/-- The last finite prefix stage is exactly the original C. -/
theorem outerHornCStage_end (m : ℕ) :
    outerHornCStage.{u} m (Fintype.card (outerHornCFaceIndex m)) = outerHornC (m + 2) := by
  apply le_antisymm (outerHornCStage_le_C m _)
  rw [← outerHornCFace_iSup m]
  apply iSup_le
  intro S
  let i := (outerHornCEnumeration m).symm S
  have hi : i ∈ cFacePrefix m (Fintype.card (outerHornCFaceIndex m)) := by
    simp only [cFacePrefix, Finset.mem_filter, Finset.mem_univ, true_and]
    exact i.isLt
  apply le_trans ?_ (le_sup_right : (cFacePrefix m _).sup _ ≤ outerHornCStage m _)
  have hf := Finset.le_sup (f := fun i =>
    stdSimplex.face.{u} (outerHornCEnumeration m i).val) hi
  simpa only [i, outerHornCEnumeration_apply_symm] using hf

/-- Every inclusion in the finite stage diagram is its original subcomplex inclusion. -/
@[expose]
def outerHornCStageDiagram (m : ℕ) :
    Fin (Fintype.card (outerHornCFaceIndex m) + 1) ⥤ SSet.{u} where
  obj n := (outerHornCStage m n.val : SSet.{u})
  map {i j} f := Subcomplex.homOfLE (outerHornCStage_mono m
    (show i.val ≤ j.val from leOfHom f))
  map_id _ := by
    ext d a
    rfl
  map_comp _ _ := by
    ext d a
    rfl

/-- The finite diagram keeps the original ambient factor on every stage arrow. -/
@[reassoc]
theorem outerHornCStageDiagram_map_ι (m : ℕ)
    {i j : Fin (Fintype.card (outerHornCFaceIndex m) + 1)} (f : i ⟶ j) :
    (outerHornCStageDiagram.{u} m).map f ≫ (outerHornCStage m j.val).ι =
      (outerHornCStage m i.val).ι := by
  apply NatTrans.ext
  funext d
  ext a
  rfl

/-- Stage arrows act by the same original simplex in every degree. -/
theorem outerHornCStageDiagram_map_app (m : ℕ)
    {i j : Fin (Fintype.card (outerHornCFaceIndex m) + 1)} (f : i ⟶ j)
    (d : SimplexCategoryᵒᵖ) (a : (outerHornCStage.{u} m i.val).obj d) :
    (((outerHornCStageDiagram m).map f).app d a).val = a.val := by
  dsimp only [outerHornCStageDiagram]
  rfl

private def cFaceLower {m : ℕ} (S : outerHornCFaceIndex m) :
    (Δ[m + 2] : SSet.{u}).Subcomplex :=
  (Finset.univ.filter (fun T : outerHornCFaceIndex m => T.val ⊂ S.val)).sup
    (fun T => stdSimplex.face T.val)

private theorem mem_cFaceLower_iff {m d : ℕ} (S : outerHornCFaceIndex m)
    (a : (Δ[m + 2] : SSet.{u}) _⦋d⦌) :
    a ∈ (cFaceLower S).obj (op ⦋d⦌) ↔
      ∃ T : outerHornCFaceIndex m, T.val ⊂ S.val ∧
        a ∈ (stdSimplex.face T.val).obj (op ⦋d⦌) := by
  simp only [cFaceLower, Finset.sup_eq_iSup, Subfunctor.iSup_obj,
    Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]

private theorem cFacePrefix_intersection (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    (cFacePrefix m i.val).sup (fun j =>
      stdSimplex.face.{u} (outerHornCEnumeration m j).val ⊓
        stdSimplex.face (outerHornCEnumeration m i).val) =
      cFaceLower (outerHornCEnumeration m i) := by
  let S := outerHornCEnumeration m i
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have hjlt : j < i := by
      change j.val < i.val
      simpa only [cFacePrefix, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    let T := outerHornCEnumeration m j
    have hc : T.val.card ≤ S.val.card := outerHornCEnumeration_card_mono m hjlt.le
    have hne : (outerHornCFaceInf T S).val ≠ S.val := by
      intro h
      have hs : S.val ⊆ T.val := Finset.inter_eq_right.mp h
      have he : S = T := Subtype.ext (Finset.eq_of_subset_of_card_le hs hc)
      have hji : j = i := (outerHornCEnumeration m).injective he.symm
      exact (ne_of_lt hjlt) hji
    have hproper : (outerHornCFaceInf T S).val ⊂ S.val :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, hne⟩
    have hin : outerHornCFaceInf T S ∈
        Finset.univ.filter (fun V : outerHornCFaceIndex m => V.val ⊂ S.val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hproper
    rw [outerHornCFace_intersection]
    exact Finset.le_sup (f := fun V => stdSimplex.face.{u} V.val) hin
  · apply Finset.sup_le
    intro T hT
    have hproper : T.val ⊂ S.val := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hT
    let j := (outerHornCEnumeration m).symm T
    have hj : j ∈ cFacePrefix m i.val := by
      simp only [cFacePrefix, Finset.mem_filter, Finset.mem_univ, true_and]
      exact outerHornCEnumeration_lower_before m i T hproper
    have hface : stdSimplex.face.{u} T.val ≤ stdSimplex.face S.val :=
      (stdSimplex.face_le_face_iff _ _).mpr hproper.le
    have hf := Finset.le_sup_of_le (s := cFacePrefix m i.val)
      (f := fun j => stdSimplex.face.{u} (outerHornCEnumeration m j).val ⊓
        stdSimplex.face S.val) hj
      (show stdSimplex.face.{u} T.val ≤
        stdSimplex.face (outerHornCEnumeration m j).val ⊓ stdSimplex.face S.val from by
          rw [outerHornCEnumeration_apply_symm]
          exact le_inf le_rfl hface)
    exact hf

private theorem cFaceStage_intersection_basis (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val =
      cFaceLower (outerHornCEnumeration m i) ⊔
        (outerHornCU m ⊓ stdSimplex.face (outerHornCEnumeration m i).val) := by
  ext d a
  obtain ⟨d⟩ := d
  induction d using SimplexCategory.rec with | _ d =>
  change (a ∈ (outerHornCStage m i.val).obj (op ⦋d⦌) ∧
      a ∈ (stdSimplex.face (outerHornCEnumeration m i).val).obj (op ⦋d⦌)) ↔
    a ∈ (cFaceLower (outerHornCEnumeration m i)).obj (op ⦋d⦌) ∨
      (a ∈ (outerHornCU m).obj (op ⦋d⦌) ∧
        a ∈ (stdSimplex.face (outerHornCEnumeration m i).val).obj (op ⦋d⦌))
  constructor
  · rintro ⟨hA, hS⟩
    rcases (mem_outerHornCStage_iff a).mp hA with hU | ⟨j, hj, hT⟩
    · exact Or.inr ⟨hU, hS⟩
    · have hin : j ∈ cFacePrefix m i.val := by
        simpa only [cFacePrefix, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hb := Finset.le_sup (f := fun j =>
        stdSimplex.face.{u} (outerHornCEnumeration m j).val ⊓
          stdSimplex.face (outerHornCEnumeration m i).val) hin
      have hp := hb (op ⦋d⦌) (show a ∈
        (stdSimplex.face.{u} (outerHornCEnumeration m j).val ⊓
          stdSimplex.face (outerHornCEnumeration m i).val).obj (op ⦋d⦌) from ⟨hT, hS⟩)
      rw [cFacePrefix_intersection] at hp
      exact Or.inl hp
  · rintro (hL | ⟨hU, hS⟩)
    · have hp : a ∈ ((cFacePrefix m i.val).sup (fun j =>
          stdSimplex.face.{u} (outerHornCEnumeration m j).val ⊓
            stdSimplex.face (outerHornCEnumeration m i).val)).obj (op ⦋d⦌) := by
        rw [cFacePrefix_intersection]
        exact hL
      simp only [Finset.sup_eq_iSup, Subfunctor.iSup_obj, Set.mem_iUnion] at hp
      obtain ⟨j, hj, hT, hS⟩ := hp
      have hjlt : j.val < i.val := by
        simpa only [cFacePrefix, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      exact ⟨(mem_outerHornCStage_iff a).mpr (Or.inr ⟨j, hjlt, hT⟩), hS⟩
    · exact ⟨(mem_outerHornCStage_iff a).mpr (Or.inl hU), hS⟩

private theorem cFaceInnerHorn (ell : ℕ) (h2 : 2 ≤ ell) :
    outerHornC.{u} ell ⊔ outerHornCIntervalCover ell = horn ell 1 := by
  have hone : (1 : Fin (ell + 1)).val = 1 := by
    change 1 % (ell + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have htail : Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell) =
      ({0}ᶜ : Finset (Fin (ell + 1))) := by
    ext v
    simp only [Finset.mem_Icc, Finset.mem_compl, Finset.mem_singleton,
      Fin.le_def, Fin.ext_iff, Fin.val_zero, Fin.val_last, hone]
    have hv := v.isLt
    omega
  have hedge : Finset.Icc (0 : Fin (ell + 1)) 1 =
      ({0, 1} : Finset (Fin (ell + 1))) := by
    ext v
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      Fin.le_def, Fin.ext_iff, Fin.val_zero, hone]
    omega
  have hC : outerHornC.{u} ell ≤ horn ell 1 := by
    rw [outerHornC, horn_eq_iSup]
    apply iSup_le
    intro r
    have hr : r.val ≠ (1 : Fin (ell + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      rw [hone] at hv
      have hg := r.property
      omega
    exact le_iSup_of_le ⟨r.val, by simpa using hr⟩ le_rfl
  have hT : stdSimplex.face.{u} ({0}ᶜ : Finset (Fin (ell + 1))) ≤ horn ell 1 := by
    rw [horn_eq_iSup]
    have h01 : (0 : Fin (ell + 1)) ≠ 1 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_zero, hone] at hv
      omega
    exact le_iSup_of_le ⟨0, by simpa using h01⟩ le_rfl
  let q : Fin (ell + 1) := ⟨2, by omega⟩
  have hq : q ∉ ({0, 1} : Finset (Fin (ell + 1))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · have hv := congrArg Fin.val h
      change 2 = 0 at hv
      omega
    · have hv := congrArg Fin.val h
      rw [hone] at hv
      change 2 = 1 at hv
      omega
  have hEC : stdSimplex.face.{u} ({0, 1} : Finset (Fin (ell + 1))) ≤ outerHornC ell := by
    have hf : stdSimplex.face.{u} ({0, 1} : Finset (Fin (ell + 1))) ≤
        stdSimplex.face {q}ᶜ := by
      apply (stdSimplex.face_le_face_iff _ _).mpr
      intro v hv
      simp only [Finset.mem_compl, Finset.mem_singleton]
      intro h
      subst v
      exact hq hv
    exact hf.trans (le_iSup_of_le (⟨q, by change 2 ≤ 2; omega⟩ :
      {r : Fin (ell + 1) // 2 ≤ r.val}) le_rfl)
  rw [outerHornCIntervalCover, htail, hedge]
  apply le_antisymm
  · exact sup_le hC (sup_le hT (hEC.trans hC))
  · rw [horn_eq_iSup]
    apply iSup_le
    intro r
    have hr1 : r.val ≠ (1 : Fin (ell + 1)) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.property
    by_cases hr0 : r.val = 0
    · rw [hr0]
      exact le_trans le_sup_left le_sup_right
    · have hv0 : r.val.val ≠ 0 := by
        intro h
        exact hr0 (Fin.ext h)
      have hv1 : r.val.val ≠ 1 := by
        intro h
        apply hr1
        apply Fin.ext
        simpa only [hone] using h
      have hg : 2 ≤ r.val.val := by omega
      exact le_trans (le_iSup_of_le (⟨r.val, hg⟩ :
        {j : Fin (ell + 1) // 2 ≤ j.val}) le_rfl) le_sup_left

private theorem cFaceMap_preimage_face {m : ℕ} (S : outerHornCFaceIndex m) :
    (stdSimplex.face S.val).preimage (outerHornCFaceMap.{u} S) = ⊤ := by
  ext d a
  change (outerHornCFaceMap S).app d a ∈ (stdSimplex.face S.val).obj d ↔ True
  exact ⟨fun _ => trivial, fun _ => ((outerHornCFaceIso S).hom.app d a).property⟩

/-- The original face at a position lies in its actual successor stage. -/
theorem outerHornCFace_le_stage_succ (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    stdSimplex.face.{u} (outerHornCEnumeration m i).val ≤
      outerHornCStage m (i.val + 1) := by
  rw [outerHornCStage_succ]
  exact le_sup_right

/-- The original consecutive stage map is its literal subcomplex inclusion. -/
@[expose]
def outerHornCStageStep (m : ℕ) (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    (outerHornCStage m i.val : SSet.{u}) ⟶ outerHornCStage m (i.val + 1) :=
  Subcomplex.homOfLE (outerHornCStage_mono m (Nat.le_succ i.val))

/-- A stage step retains its same original ambient factor. -/
@[reassoc (attr := simp)]
theorem outerHornCStageStep_ι (m : ℕ) (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    outerHornCStageStep.{u} m i ≫ (outerHornCStage m (i.val + 1)).ι =
      (outerHornCStage m i.val).ι := by
  ext d a
  rfl

/-- The same increasing face representation followed by the original successor inclusion. -/
@[expose]
def outerHornCFaceToNext (m : ℕ) (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶
      outerHornCStage m (i.val + 1) :=
  (outerHornCFaceIso (outerHornCEnumeration m i)).hom ≫
    Subcomplex.homOfLE (outerHornCFace_le_stage_succ m i)

/-- The successor face map has the original increasing ambient-map factor. -/
@[reassoc (attr := simp)]
theorem outerHornCFaceToNext_ι (m : ℕ) (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    outerHornCFaceToNext.{u} m i ≫ (outerHornCStage m (i.val + 1)).ι =
      outerHornCFaceMap (outerHornCEnumeration m i) := by
  dsimp only [outerHornCFaceToNext]
  rw [Category.assoc, Subcomplex.homOfLE_ι, outerHornCFaceIso_hom_ι]

/-- The local dimension-one attachment is exactly the already-present original edge. -/
theorem outerHornCStage_edge_eq (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h1 : outerHornCFaceDim (outerHornCEnumeration m i) = 1) :
    outerHornCStage.{u} m (i.val + 1) = outerHornCStage m i.val := by
  let S := outerHornCEnumeration m i
  have hc : S.val.card = 2 := by
    have h := outerHornCFace_card S
    rw [h1] at h
    exact h
  have hone : (1 : Fin (m + 3)).val = 1 := by
    change 1 % (m + 3) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have h01 : (0 : Fin (m + 3)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_zero, hone] at hv
    omega
  have hp : ({0, 1} : Finset (Fin (m + 3))) ⊆ S.val := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨S.property.1, S.property.2.1⟩
  have hcard : ({0, 1} : Finset (Fin (m + 3))).card = 2 := by simp [h01]
  have he : S.val = {0, 1} :=
    (Finset.eq_of_subset_of_card_le hp (by rw [hc, hcard])).symm
  rw [outerHornCStage_succ, he]
  apply sup_eq_left.mpr
  have hE : stdSimplex.face.{u} ({0, 1} : Finset (Fin (m + 3))) ≤ outerHornCU m :=
    le_sup_right
  exact hE.trans le_sup_left

/-- Every prefix at the original degree-two endpoint is the same original edge. -/
theorem outerHornCStage_low (n : ℕ) :
    outerHornCStage.{u} 0 n = outerHornCU 0 := by
  apply le_antisymm
  · have h := outerHornCStage_le_C.{u} 0 n
    change outerHornCStage 0 n ≤ outerHornC 2 at h
    rw [outerHornC_two] at h
    rw [outerHornCU_zero]
    exact h
  · exact le_sup_left

/-- Successor-face words retain every original sorted coordinate and repetition. -/
theorem outerHornCFaceToNext_coord (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) {d : ℕ}
    (a : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) _⦋d⦌)
    (q : Fin (d + 1)) :
    ((outerHornCFaceToNext.{u} m i).app (op ⦋d⦌) a).val q =
      (outerHornCFaceOrderIso (outerHornCEnumeration m i) (a q)).val := by
  dsimp only [outerHornCFaceToNext]
  exact outerHornCFaceIso_hom_coord (outerHornCEnumeration m i) a q

/-- The successor-face map retains every original simplex-degree operator. -/
theorem outerHornCFaceToNext_operator (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    {d e : SimplexCategoryᵒᵖ} (β : d ⟶ e) :
    (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}).map β ≫
        (outerHornCFaceToNext.{u} m i).app e =
      (outerHornCFaceToNext.{u} m i).app d ≫ (outerHornCStage m (i.val + 1) : SSet.{u}).map β :=
  (outerHornCFaceToNext.{u} m i).naturality β

/-- Every original degree operator commutes with the actual stage inclusion. -/
theorem outerHornCStageStep_operator (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    {d e : SimplexCategoryᵒᵖ} (β : d ⟶ e) :
    (outerHornCStage m i.val : SSet.{u}).map β ≫ (outerHornCStageStep.{u} m i).app e =
      (outerHornCStageStep.{u} m i).app d ≫ (outerHornCStage m (i.val + 1) : SSet.{u}).map β :=
  (outerHornCStageStep.{u} m i).naturality β

private abbrev enumValue {m : ℕ} (S : outerHornCFaceIndex m)
    (r : Fin (outerHornCFaceDim S + 1)) : Fin (m + 3) :=
  (outerHornCFaceOrderIso S r).val

private theorem enumValue_injective {m : ℕ} (S : outerHornCFaceIndex m) :
    Function.Injective (enumValue S) := by
  intro i j h
  exact (outerHornCFaceOrderIso S).injective (Subtype.ext h)

private abbrev localOne {m : ℕ} (S : outerHornCFaceIndex m) :
    Fin (outerHornCFaceDim S + 1) :=
  ⟨1, by have h := outerHornCFaceDim_pos S; omega⟩

private theorem enumValue_zero {m : ℕ} (S : outerHornCFaceIndex m) :
    enumValue S 0 = 0 := outerHornCFaceOrderIso_zero S

private theorem enumValue_one {m : ℕ} (S : outerHornCFaceIndex m) :
    enumValue S (localOne S) = 1 := outerHornCFaceOrderIso_one S

-- This supplies both directions: omitting a local vertex retains original0/1
-- exactly when that local vertex has value at least2.
private theorem enumValue_avoids_zero_one_iff {m : ℕ} (S : outerHornCFaceIndex m)
    (r : Fin (outerHornCFaceDim S + 1)) :
    (enumValue S r ≠ 0 ∧ enumValue S r ≠ 1) ↔ 2 ≤ r.val := by
  constructor
  · rintro ⟨h0, h1⟩
    have hr0 : r.val ≠ 0 := by
      intro h
      have e : r = 0 := Fin.ext h
      exact h0 ((congrArg (enumValue S) e).trans (enumValue_zero S))
    have hr1 : r.val ≠ 1 := by
      intro h
      have e : r = localOne S := Fin.ext h
      exact h1 ((congrArg (enumValue S) e).trans (enumValue_one S))
    omega
  · intro hr
    constructor
    · intro h
      have e : r = 0 := enumValue_injective S
        (h.trans (enumValue_zero S).symm)
      have hv := congrArg Fin.val e
      simp only [Fin.val_zero] at hv
      omega
    · intro h
      have e : r = localOne S := enumValue_injective S
        (h.trans (enumValue_one S).symm)
      have hv := congrArg Fin.val e
      change r.val = 1 at hv
      omega

private theorem erased_contains_zero_one_iff {m : ℕ} (S : outerHornCFaceIndex m)
    (r : Fin (outerHornCFaceDim S + 1)) :
    ((0 : Fin (m + 3)) ∈ S.val.erase (enumValue S r) ∧
      (1 : Fin (m + 3)) ∈ S.val.erase (enumValue S r)) ↔ 2 ≤ r.val := by
  constructor
  · rintro ⟨h0, h1⟩
    apply (enumValue_avoids_zero_one_iff S r).mp
    exact ⟨fun h => (Finset.mem_erase.mp h0).1 h.symm,
      fun h => (Finset.mem_erase.mp h1).1 h.symm⟩
  · intro hr
    obtain ⟨h0, h1⟩ := (enumValue_avoids_zero_one_iff S r).mpr hr
    exact ⟨Finset.mem_erase.mpr ⟨Ne.symm h0, S.property.1⟩,
      Finset.mem_erase.mpr ⟨Ne.symm h1, S.property.2.1⟩⟩

-- No positivity hypothesis is used here. This is the exact all-r coordinate
-- bridge, including r=0/1 and the dimension-one case.
private theorem enum_mem_erased_iff {m : ℕ} (S : outerHornCFaceIndex m)
    (r i : Fin (outerHornCFaceDim S + 1)) :
    enumValue S i ∈ S.val.erase (enumValue S r) ↔ i ≠ r := by
  rw [Finset.mem_erase]
  constructor
  · rintro ⟨h, _⟩ e
    exact h (congrArg (enumValue S) e)
  · intro h
    exact ⟨fun e => h (enumValue_injective S e),
      (outerHornCFaceOrderIso S i).property⟩

private theorem erased_face_mem_iff {m d : ℕ} (S : outerHornCFaceIndex m)
    (r : Fin (outerHornCFaceDim S + 1))
    (a : (Δ[outerHornCFaceDim S] : SSet.{u}) _⦋d⦌) :
    (outerHornCFaceMap S).app (op ⦋d⦌) a ∈
        (stdSimplex.face (S.val.erase (enumValue S r))).obj (op ⦋d⦌) ↔
      r ∉ Set.range a := by
  rw [stdSimplex.mem_face_iff]
  constructor
  · intro h
    rintro ⟨i, hi⟩
    have hm : enumValue S (a i) ∈ S.val.erase (enumValue S r) := by
      simpa only [outerHornCFaceMap_coord, enumValue] using h i
    exact ((enum_mem_erased_iff S r (a i)).mp hm) hi
  · intro h i
    have hm : enumValue S (a i) ∈ S.val.erase (enumValue S r) :=
      (enum_mem_erased_iff S r (a i)).mpr (fun hi => h ⟨i, hi⟩)
    simpa only [outerHornCFaceMap_coord, enumValue] using hm

private theorem erased_face_preimage {m : ℕ} (S : outerHornCFaceIndex m)
    (r : Fin (outerHornCFaceDim S + 1)) :
    (stdSimplex.face.{u} (S.val.erase (enumValue S r))).preimage
        (outerHornCFaceMap S) = stdSimplex.face {r}ᶜ := by
  ext d a
  let b : (Δ[outerHornCFaceDim S] : SSet.{u}) _⦋d.unop.len⦌ := a
  change ((outerHornCFaceMap S).app (op ⦋d.unop.len⦌) b ∈
      (stdSimplex.face (S.val.erase (enumValue S r))).obj (op ⦋d.unop.len⦌)) ↔
    b ∈ (stdSimplex.face {r}ᶜ).obj (op ⦋d.unop.len⦌)
  rw [erased_face_mem_iff, stdSimplex.mem_face_iff]
  simp only [Finset.mem_compl, Finset.mem_singleton, Set.mem_range, not_exists]

private def erasedIndex {m : ℕ} (S : outerHornCFaceIndex m)
    (r : Fin (outerHornCFaceDim S + 1)) (hr : 2 ≤ r.val) : outerHornCFaceIndex m :=
  ⟨S.val.erase (enumValue S r), by
    obtain ⟨h0, h1⟩ := (erased_contains_zero_one_iff S r).mpr hr
    refine ⟨h0, h1, ?_⟩
    intro h
    have hj : enumValue S r ∈ S.val.erase (enumValue S r) := by
      rw [h]
      exact Finset.mem_univ _
    exact (Finset.mem_erase.mp hj).1 rfl⟩

private theorem erasedIndex_ssubset {m : ℕ} (S : outerHornCFaceIndex m)
    (r : Fin (outerHornCFaceDim S + 1)) (hr : 2 ≤ r.val) :
    (erasedIndex S r hr).val ⊂ S.val :=
  Finset.erase_ssubset (outerHornCFaceOrderIso S r).property

-- Every ORIGINAL strict lower face is covered by one of these erasures.
-- The erasure is selected by the finite-subset theorem, not by a stage index.
private theorem strict_lower_le_erased {m : ℕ} (S T : outerHornCFaceIndex m)
    (h : T.val ⊂ S.val) :
    ∃ r : Fin (outerHornCFaceDim S + 1), 2 ≤ r.val ∧
      T.val ⊆ S.val.erase (enumValue S r) := by
  obtain ⟨j, hjS, hT⟩ := Finset.ssubset_iff_exists_subset_erase.mp h
  let r := (outerHornCFaceOrderIso S).symm ⟨j, hjS⟩
  have he : enumValue S r = j :=
    congrArg Subtype.val ((outerHornCFaceOrderIso S).apply_symm_apply ⟨j, hjS⟩)
  have h01 : (0 : Fin (m + 3)) ∈ S.val.erase (enumValue S r) ∧
      (1 : Fin (m + 3)) ∈ S.val.erase (enumValue S r) := by
    constructor
    · simpa only [he] using hT T.property.1
    · simpa only [he] using hT T.property.2.1
  refine ⟨r, (erased_contains_zero_one_iff S r).mp h01, ?_⟩
  simpa only [he] using hT


private theorem cFaceLower_preimage {m : ℕ} (S : outerHornCFaceIndex m) :
    (cFaceLower.{u} S).preimage (outerHornCFaceMap S) =
      outerHornC (outerHornCFaceDim S) := by
  classical
  ext d a
  let b : (Δ[outerHornCFaceDim S] : SSet.{u}) _⦋d.unop.len⦌ := a
  let q := (outerHornCFaceMap S).app (op ⦋d.unop.len⦌) b
  change (q ∈ (cFaceLower S).obj (op ⦋d.unop.len⦌)) ↔
    b ∈ (outerHornC (outerHornCFaceDim S)).obj (op ⦋d.unop.len⦌)
  rw [mem_cFaceLower_iff, mem_outerHornC_iff]
  constructor
  · rintro ⟨T, hTS, hqT⟩
    obtain ⟨r, hr, hT⟩ := strict_lower_le_erased S T hTS
    have hface : stdSimplex.face.{u} T.val ≤
        stdSimplex.face (S.val.erase (enumValue S r)) :=
      (stdSimplex.face_le_face_iff _ _).mpr hT
    exact ⟨r, hr, (erased_face_mem_iff S r b).mp
      (hface (op ⦋d.unop.len⦌) hqT)⟩
  · rintro ⟨r, hr, hb⟩
    let T := erasedIndex S r hr
    refine ⟨T, erasedIndex_ssubset S r hr, ?_⟩
    change q ∈ (stdSimplex.face (S.val.erase (enumValue S r))).obj (op ⦋d.unop.len⦌)
    exact (erased_face_mem_iff S r b).mpr hb


/-- The original successor face meets the previous stage in exactly its inner horn one. -/
theorem outerHornCStage_face_preimage (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (outerHornCStage.{u} m i.val).preimage
        (outerHornCFaceMap (outerHornCEnumeration m i)) =
      horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 := by
  let S := outerHornCEnumeration m i
  let F := outerHornCFaceMap.{u} S
  change (outerHornCStage m i.val).preimage F = horn (outerHornCFaceDim S) 1
  calc
    (outerHornCStage m i.val).preimage F =
        (outerHornCStage m i.val ⊓ stdSimplex.face S.val).preimage F := by
      rw [Subcomplex.preimage_min, cFaceMap_preimage_face, inf_top_eq]
    _ = (cFaceLower S ⊔ (outerHornCU m ⊓ stdSimplex.face S.val)).preimage F := by
      rw [cFaceStage_intersection_basis]
    _ = outerHornC (outerHornCFaceDim S) ⊔ outerHornCIntervalCover (outerHornCFaceDim S) := by
      rw [Subcomplex.preimage_max, cFaceLower_preimage, outerHornCU_intersection_preimage]
    _ = horn (outerHornCFaceDim S) 1 := cFaceInnerHorn _ h2

private def cFaceHornAmbient (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 : SSet.{u}) ⟶ Δ[m + 2] :=
  (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫
    outerHornCFaceMap (outerHornCEnumeration m i)

private theorem cFaceHornAmbient_mono (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) : Mono (cFaceHornAmbient.{u} m i) := by
  have hF : Mono (outerHornCFaceMap.{u} (outerHornCEnumeration m i)) := by
    rw [← outerHornCFaceIso_hom_ι]
    infer_instance
  let _ := hF
  dsimp only [cFaceHornAmbient]
  infer_instance

private theorem cFaceHornAmbient_range (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    Subcomplex.range (cFaceHornAmbient.{u} m i) =
      outerHornCStage m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val := by
  let S := outerHornCEnumeration m i
  let F := outerHornCFaceMap.{u} S
  let I := outerHornCFaceIso.{u} S
  ext d a
  change (∃ b, (cFaceHornAmbient m i).app d b = a) ↔
    a ∈ (outerHornCStage m i.val).obj d ∧ a ∈ (stdSimplex.face S.val).obj d
  constructor
  · rintro ⟨b, hb⟩
    have hp : b.val ∈ ((outerHornCStage m i.val).preimage F).obj d := by
      rw [outerHornCStage_face_preimage m i h2]
      exact b.property
    change F.app d b.val ∈ (outerHornCStage m i.val).obj d at hp
    have hface : F.app d b.val ∈ (stdSimplex.face S.val).obj d :=
      (I.hom.app d b.val).property
    change F.app d b.val = a at hb
    exact hb ▸ ⟨hp, hface⟩
  · rintro ⟨hA, hS⟩
    let af : (stdSimplex.face S.val : SSet.{u}).obj d := ⟨a, hS⟩
    let b := I.inv.app d af
    have hF : F.app d b = a := by
      change ((I.inv ≫ I.hom).app d af).val = a
      rw [Iso.inv_hom_id]
      rfl
    have hb : b ∈ (horn (outerHornCFaceDim S) 1).obj d := by
      rw [← outerHornCStage_face_preimage m i h2]
      change F.app d b ∈ (outerHornCStage m i.val).obj d
      rw [hF]
      exact hA
    exact ⟨⟨b, hb⟩, hF⟩

/-- The actual original inner horn represents the whole old-stage intersection. -/
def outerHornCHornIntersectionIso (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 : SSet.{u}) ≅
      ((outerHornCStage m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val :
        (Δ[m + 2] : SSet.{u}).Subcomplex) : SSet.{u}) := by
  letI : Mono (cFaceHornAmbient.{u} m i) := cFaceHornAmbient_mono m i
  exact asIso (Subcomplex.toRange (cFaceHornAmbient m i)) ≪≫
    Subcomplex.eqToIso (cFaceHornAmbient_range m i h2)

/-- The horn/intersection isomorphism keeps the original ambient horn-simplex composite. -/
@[reassoc (attr := simp)]
theorem outerHornCHornIntersectionIso_hom_ι (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (outerHornCHornIntersectionIso.{u} m i h2).hom ≫
        (outerHornCStage m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val).ι =
      (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫
        outerHornCFaceMap (outerHornCEnumeration m i) := by
  dsimp only [outerHornCHornIntersectionIso]
  rw [Iso.trans_hom, Category.assoc, Subcomplex.eqToIso_hom,
    Subcomplex.homOfLE_ι, asIso_hom, Subcomplex.toRange_ι]
  rfl

/-- The first original intersection leg is the same horn/face comparison. -/
@[reassoc (attr := simp)]
theorem outerHornCHornIntersectionIso_hom_face (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (outerHornCHornIntersectionIso.{u} m i h2).hom ≫
        Subcomplex.homOfLE (inf_le_right :
          outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val ≤
            stdSimplex.face (outerHornCEnumeration m i).val) =
      (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫
        (outerHornCFaceIso (outerHornCEnumeration m i)).hom := by
  rw [← cancel_mono (stdSimplex.face (outerHornCEnumeration m i).val).ι]
  rw [Category.assoc, Subcomplex.homOfLE_ι, outerHornCHornIntersectionIso_hom_ι,
    Category.assoc, outerHornCFaceIso_hom_ι]

/-- The inverse comparison retains the same original face leg. -/
@[reassoc]
theorem outerHornCHornIntersectionIso_inv_face (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (outerHornCHornIntersectionIso.{u} m i h2).inv ≫
        (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫
        (outerHornCFaceIso (outerHornCEnumeration m i)).hom =
      Subcomplex.homOfLE (inf_le_right :
        outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val ≤
          stdSimplex.face (outerHornCEnumeration m i).val) := by
  rw [← outerHornCHornIntersectionIso_hom_face m i h2, Iso.inv_hom_id_assoc]

/-- The original horn attaches by the old-intersection projection into the old stage. -/
@[expose]
def outerHornCAttachment (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 : SSet.{u}) ⟶
      outerHornCStage m i.val :=
  (outerHornCHornIntersectionIso.{u} m i h2).hom ≫ Subcomplex.homOfLE inf_le_left

/-- The attaching map retains the original ambient horn-simplex factor. -/
@[reassoc (attr := simp)]
theorem outerHornCAttachment_ι (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    outerHornCAttachment.{u} m i h2 ≫ (outerHornCStage m i.val).ι =
      (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫
        outerHornCFaceMap (outerHornCEnumeration m i) := by
  dsimp only [outerHornCAttachment]
  rw [Category.assoc, Subcomplex.homOfLE_ι, outerHornCHornIntersectionIso_hom_ι]

/-- The inverse horn comparison retains the second original intersection leg. -/
@[reassoc (attr := simp)]
theorem outerHornCHornIntersectionIso_inv_old (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (outerHornCHornIntersectionIso.{u} m i h2).inv ≫ outerHornCAttachment.{u} m i h2 =
      Subcomplex.homOfLE (inf_le_left :
        outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val ≤
          outerHornCStage m i.val) := by
  dsimp only [outerHornCAttachment]
  rw [Iso.inv_hom_id_assoc]

/-- The literal original inner-horn square is the actual successor pushout. -/
theorem outerHornCAttachment_isPushout (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    IsPushout (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
      (outerHornCAttachment.{u} m i h2) (outerHornCFaceToNext.{u} m i)
      (outerHornCStageStep.{u} m i) := by
  have hs : Subcomplex.BicartSq
      (outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val)
      (stdSimplex.face (outerHornCEnumeration m i).val) (outerHornCStage m i.val)
      (outerHornCStage m (i.val + 1)) :=
    ⟨by rw [sup_comm, ← outerHornCStage_succ], inf_comm _ _⟩
  apply hs.isPushout.of_iso' (outerHornCHornIntersectionIso.{u} m i h2)
    (outerHornCFaceIso (outerHornCEnumeration m i)) (Iso.refl _) (Iso.refl _)
  · exact outerHornCHornIntersectionIso_hom_face m i h2
  · simp only [Iso.refl_hom, Category.comp_id, outerHornCAttachment]
  · simp only [Iso.refl_hom, Category.comp_id, outerHornCFaceToNext]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, outerHornCStageStep]

/-- The chosen original horn pushout is isomorphic to the actual successor stage. -/
@[expose]
def outerHornCAttachmentPushoutIso (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    pushout (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
        (outerHornCAttachment.{u} m i h2) ≅ (outerHornCStage m (i.val + 1) : SSet.{u}) :=
  (outerHornCAttachment_isPushout.{u} m i h2).isoPushout.symm

/-- The first chosen pushout leg is the original increasing successor face. -/
@[reassoc (attr := simp)]
theorem outerHornCAttachmentPushoutIso_inl (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    pushout.inl (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
        (outerHornCAttachment.{u} m i h2) ≫ (outerHornCAttachmentPushoutIso.{u} m i h2).hom =
      outerHornCFaceToNext.{u} m i :=
  (outerHornCAttachment_isPushout.{u} m i h2).inl_isoPushout_inv

/-- The second chosen pushout leg is the original old-stage inclusion. -/
@[reassoc (attr := simp)]
theorem outerHornCAttachmentPushoutIso_inr (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    pushout.inr (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
        (outerHornCAttachment.{u} m i h2) ≫ (outerHornCAttachmentPushoutIso.{u} m i h2).hom =
      outerHornCStageStep.{u} m i :=
  (outerHornCAttachment_isPushout.{u} m i h2).inr_isoPushout_inv

/-- The inverse chosen comparison keeps the original successor-face injection. -/
@[reassoc (attr := simp)]
theorem outerHornCAttachmentPushoutIso_face (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    outerHornCFaceToNext.{u} m i ≫ (outerHornCAttachmentPushoutIso.{u} m i h2).inv =
      pushout.inl (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
        (outerHornCAttachment.{u} m i h2) :=
  (outerHornCAttachment_isPushout.{u} m i h2).inl_isoPushout_hom

/-- The inverse chosen comparison keeps the original old-stage injection. -/
@[reassoc (attr := simp)]
theorem outerHornCAttachmentPushoutIso_old (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    outerHornCStageStep.{u} m i ≫ (outerHornCAttachmentPushoutIso.{u} m i h2).inv =
      pushout.inr (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι
        (outerHornCAttachment.{u} m i h2) :=
  (outerHornCAttachment_isPushout.{u} m i h2).inr_isoPushout_hom

/-- The original compatible legs descend uniquely to the actual successor stage. -/
@[expose]
def outerHornCAttachmentDesc (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SSet.{u}}
    (f : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      outerHornCAttachment.{u} m i h2 ≫ g) : (outerHornCStage m (i.val + 1) : SSet.{u}) ⟶ X :=
  (outerHornCAttachment_isPushout.{u} m i h2).desc f g w

@[reassoc (attr := simp)]
theorem outerHornCAttachmentDesc_face (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SSet.{u}}
    (f : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      outerHornCAttachment.{u} m i h2 ≫ g) :
    outerHornCFaceToNext.{u} m i ≫ outerHornCAttachmentDesc m i h2 f g w = f :=
  (outerHornCAttachment_isPushout.{u} m i h2).inl_desc f g w

@[reassoc (attr := simp)]
theorem outerHornCAttachmentDesc_old (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SSet.{u}}
    (f : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      outerHornCAttachment.{u} m i h2 ≫ g) :
    outerHornCStageStep.{u} m i ≫ outerHornCAttachmentDesc m i h2 f g w = g :=
  (outerHornCAttachment_isPushout.{u} m i h2).inr_desc f g w

/-- Both original injections characterize the descended arrow to any target. -/
theorem outerHornCAttachmentDesc_unique (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SSet.{u}}
    (f : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      outerHornCAttachment.{u} m i h2 ≫ g)
    (d : (outerHornCStage m (i.val + 1) : SSet.{u}) ⟶ X)
    (hf : outerHornCFaceToNext.{u} m i ≫ d = f) (hg : outerHornCStageStep.{u} m i ≫ d = g) :
    d = outerHornCAttachmentDesc m i h2 f g w :=
  (outerHornCAttachment_isPushout.{u} m i h2).hom_ext
    (hf.trans (outerHornCAttachmentDesc_face m i h2 f g w).symm)
    (hg.trans (outerHornCAttachmentDesc_old m i h2 f g w).symm)

/-- Every actual original successor inclusion is inner anodyne. -/
theorem outerHornCStageStep_innerAnodyne (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m))) :
    innerAnodyneExtensions (outerHornCStageStep.{u} m i) := by
  let ell := outerHornCFaceDim (outerHornCEnumeration m i)
  by_cases h2 : 2 ≤ ell
  · have hone : (1 : Fin (ell + 1)).val = 1 := by
      change 1 % (ell + 1) = 1
      exact Nat.mod_eq_of_lt (by omega)
    have h0 : (0 : Fin (ell + 1)) < 1 := by
      simpa only [Fin.lt_def, Fin.val_zero, hone] using (show 0 < 1 by omega)
    have hn : (1 : Fin (ell + 1)) < Fin.last ell := by
      simpa only [Fin.lt_def, Fin.val_last, hone] using (show 1 < ell by omega)
    exact innerAnodyneExtensions.of_isPushout
      (outerHornCAttachment_isPushout.{u} m i h2).flip (innerAnodyneExtensions.horn_ι h0 hn)
  · have hp := outerHornCFaceDim_pos (outerHornCEnumeration m i)
    have h1 : ell = 1 := by omega
    let e := Subcomplex.eqToIso (outerHornCStage_edge_eq.{u} m i h1).symm
    have he : outerHornCStageStep.{u} m i = e.hom := rfl
    rw [he]
    exact innerAnodyneExtensions.of_isIso e.hom

private theorem cFaceStage_from_zero_inner (m n : ℕ)
    (hn : n ≤ Fintype.card (outerHornCFaceIndex m)) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (outerHornCStage_mono.{u} m (Nat.zero_le n))) := by
  induction n with
  | zero =>
    change innerAnodyneExtensions (𝟙 (outerHornCStage m 0 : SSet.{u}))
    exact innerAnodyneExtensions.id_mem _
  | succ n ih =>
    have hi : n < Fintype.card (outerHornCFaceIndex m) := by omega
    let i : Fin (Fintype.card (outerHornCFaceIndex m)) := ⟨n, hi⟩
    have h := innerAnodyneExtensions.comp_mem
      (Subcomplex.homOfLE (outerHornCStage_mono.{u} m (Nat.zero_le n)))
      (outerHornCStageStep.{u} m i) (ih (by omega)) (outerHornCStageStep_innerAnodyne m i)
    simpa only [outerHornCStageStep, Subcomplex.homOfLE_comp] using h

/-- The entire original U-to-C inclusion is inner anodyne in every universe. -/
theorem outerHornCU_to_C_innerAnodyne (m : ℕ) :
    innerAnodyneExtensions (Subcomplex.homOfLE (outerHornCU_le_C.{u} m)) := by
  let N := Fintype.card (outerHornCFaceIndex m)
  let e0 : (outerHornCStage m 0 : SSet.{u}) ≅ (outerHornCU m : SSet.{u}) :=
    Subcomplex.eqToIso (outerHornCStage_zero.{u} m)
  let eN : (outerHornCStage m N : SSet.{u}) ≅ (outerHornC (m + 2) : SSet.{u}) :=
    Subcomplex.eqToIso (outerHornCStage_end.{u} m)
  let g : (outerHornCStage m 0 : SSet.{u}) ⟶ (outerHornCStage m N : SSet.{u}) :=
    Subcomplex.homOfLE (outerHornCStage_mono.{u} m (Nat.zero_le N))
  have hg : innerAnodyneExtensions g := cFaceStage_from_zero_inner.{u} m N le_rfl
  have ht : innerAnodyneExtensions ((e0.inv ≫ g) ≫ eN.hom) :=
    innerAnodyneExtensions.comp_mem _ _
      (innerAnodyneExtensions.comp_mem _ _
        (innerAnodyneExtensions.of_isIso e0.inv) hg)
      (innerAnodyneExtensions.of_isIso eN.hom)
  have he : (e0.inv ≫ g) ≫ eN.hom = Subcomplex.homOfLE (outerHornCU_le_C.{u} m) := by
    ext d a
    rfl
  rw [he] at ht
  exact ht

private theorem cFaceEdge_le_lower {m : ℕ} (S : outerHornCFaceIndex m)
    (h2 : 2 ≤ outerHornCFaceDim S) :
    stdSimplex.face.{u} ({0, 1} : Finset (Fin (m + 3))) ≤ cFaceLower S := by
  let r : Fin (outerHornCFaceDim S + 1) := ⟨2, by omega⟩
  let T := erasedIndex S r (by change 2 ≤ 2; omega)
  have hp : ({0, 1} : Finset (Fin (m + 3))) ⊆ T.val := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨T.property.1, T.property.2.1⟩
  have hin : T ∈ Finset.univ.filter (fun V : outerHornCFaceIndex m => V.val ⊂ S.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact erasedIndex_ssubset S r (by change 2 ≤ 2; omega)
  exact ((stdSimplex.face_le_face_iff _ _).mpr hp).trans
    (Finset.le_sup (f := fun V => stdSimplex.face.{u} V.val) hin)

/-- The complete old intersection is exactly all strict lower faces and the original tail face. -/
theorem outerHornCStage_intersection (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val =
      (Finset.univ.filter (fun T : outerHornCFaceIndex m =>
        T.val ⊂ (outerHornCEnumeration m i).val)).sup (fun T => stdSimplex.face T.val) ⊔
        stdSimplex.face ((outerHornCEnumeration m i).val.erase 0) := by
  have h := cFaceStage_intersection_basis.{u} m i
  rw [outerHornCU_inf_face] at h
  change outerHornCStage m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val =
    cFaceLower (outerHornCEnumeration m i) ⊔
        stdSimplex.face ((outerHornCEnumeration m i).val.erase 0)
  calc
    _ = cFaceLower (outerHornCEnumeration m i) ⊔
        (stdSimplex.face ((outerHornCEnumeration m i).val.erase 0) ⊔ stdSimplex.face {0, 1}) := h
    _ = (cFaceLower (outerHornCEnumeration m i) ⊔
        stdSimplex.face ((outerHornCEnumeration m i).val.erase 0)) ⊔ stdSimplex.face {0, 1} :=
      (sup_assoc _ _ _).symm
    _ = _ := sup_eq_left.mpr ((cFaceEdge_le_lower (outerHornCEnumeration m i) h2).trans le_sup_left)

/-- The inverse horn comparison is the same original inverse sorted-face map. -/
@[reassoc (attr := simp)]
theorem outerHornCHornIntersectionIso_inv_horn (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    (outerHornCHornIntersectionIso.{u} m i h2).inv ≫
        (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι =
      Subcomplex.homOfLE (inf_le_right : outerHornCStage.{u} m i.val ⊓
          stdSimplex.face (outerHornCEnumeration m i).val ≤
        stdSimplex.face (outerHornCEnumeration m i).val) ≫
          (outerHornCFaceIso (outerHornCEnumeration m i)).inv := by
  rw [← cancel_mono (outerHornCFaceIso (outerHornCEnumeration m i)).hom]
  rw [Category.assoc, outerHornCHornIntersectionIso_inv_face, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Every forward horn point is sent by the original increasing ambient map. -/
theorem outerHornCHornIntersectionIso_hom_app (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) (d : SimplexCategoryᵒᵖ)
    (a : (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 : SSet.{u}).obj d) :
    ((outerHornCHornIntersectionIso m i h2).hom.app d a).val =
      (outerHornCFaceMap (outerHornCEnumeration m i)).app d a.val := by
  have h := congrArg (fun f => f.app d a) (outerHornCHornIntersectionIso_hom_ι.{u} m i h2)
  exact h

/-- Every inverse horn point uses the original inverse face coordinate, with its proven
membership. -/
theorem outerHornCHornIntersectionIso_inv_app (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) (d : SimplexCategoryᵒᵖ)
    (a : (outerHornCStage.{u} m i.val ⊓
      stdSimplex.face (outerHornCEnumeration m i).val).obj d) :
    ((outerHornCHornIntersectionIso m i h2).inv.app d a).val =
      (outerHornCFaceIso (outerHornCEnumeration m i)).inv.app d ⟨a.val, a.property.2⟩ := by
  have h := congrArg (fun f => f.app d a) (outerHornCHornIntersectionIso_inv_horn.{u} m i h2)
  exact h

/-- The forward original horn/intersection map retains every degree operator. -/
theorem outerHornCHornIntersectionIso_hom_operator (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i))
    {d e : SimplexCategoryᵒᵖ} (β : d ⟶ e) :
    (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 : SSet.{u}).map β ≫
        (outerHornCHornIntersectionIso m i h2).hom.app e =
      (outerHornCHornIntersectionIso m i h2).hom.app d ≫
        ((outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val :
          (Δ[m + 2] : SSet.{u}).Subcomplex) : SSet.{u}).map β :=
  (outerHornCHornIntersectionIso m i h2).hom.naturality β

/-- The inverse original horn/intersection map retains every degree operator. -/
theorem outerHornCHornIntersectionIso_inv_operator (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i))
    {d e : SimplexCategoryᵒᵖ} (β : d ⟶ e) :
    ((outerHornCStage.{u} m i.val ⊓ stdSimplex.face (outerHornCEnumeration m i).val :
      (Δ[m + 2] : SSet.{u}).Subcomplex) : SSet.{u}).map β ≫
        (outerHornCHornIntersectionIso m i h2).inv.app e =
      (outerHornCHornIntersectionIso m i h2).inv.app d ≫
        (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1 : SSet.{u}).map β :=
  (outerHornCHornIntersectionIso m i h2).inv.naturality β

/-- The original compatible-leg descent is natural under every target postcomposition. -/
theorem outerHornCAttachmentDesc_postcomp (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X Y : SSet.{u}}
    (f : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      outerHornCAttachment.{u} m i h2 ≫ g) (q : X ⟶ Y) :
    outerHornCAttachmentDesc.{u} m i h2 f g w ≫ q =
      outerHornCAttachmentDesc m i h2 (f ≫ q) (g ≫ q)
        (by simpa only [Category.assoc] using congrArg (fun t => t ≫ q) w) := by
  apply (outerHornCAttachment_isPushout.{u} m i h2).hom_ext
  · simp only [← Category.assoc, outerHornCAttachmentDesc_face]
  · simp only [← Category.assoc, outerHornCAttachmentDesc_old]

/-- The same original horn square is a pushout after the actual inner-discrete embedding. -/
theorem innerOuterHornCAttachment_isPushout (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) :
    IsPushout
      (simplicialSpaceDiscrete.{u}.map (horn (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι)
      (simplicialSpaceDiscrete.map (outerHornCAttachment m i h2))
      (simplicialSpaceDiscrete.map (outerHornCFaceToNext m i))
      (simplicialSpaceDiscrete.map (outerHornCStageStep m i)) := by
  apply IsPushout.of_forall_isPushout_app
  intro a
  apply IsPushout.of_forall_isPushout_app
  intro b
  exact (outerHornCAttachment_isPushout.{u} m i h2).app a

/-- The actual inner-discrete square has its original compatible-leg descent to every target. -/
@[expose]
def innerOuterHornCAttachmentDesc (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g) :
    simplicialSpaceDiscrete.obj (outerHornCStage m (i.val + 1) : SSet.{u}) ⟶ X :=
  (innerOuterHornCAttachment_isPushout.{u} m i h2).desc f g w

@[reassoc (attr := simp)]
theorem innerOuterHornCAttachmentDesc_face (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g) :
    dsimp% (simplicialSpaceDiscrete.map (outerHornCFaceToNext m i) ≫
      innerOuterHornCAttachmentDesc m i h2 f g w) = f :=
  (innerOuterHornCAttachment_isPushout.{u} m i h2).inl_desc f g w

@[reassoc (attr := simp)]
theorem innerOuterHornCAttachmentDesc_old (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g) :
    dsimp% (simplicialSpaceDiscrete.map (outerHornCStageStep m i) ≫
      innerOuterHornCAttachmentDesc m i h2 f g w) = g :=
  (innerOuterHornCAttachment_isPushout.{u} m i h2).inr_desc f g w

/-- Both original inner-discrete injections characterize the whole descended arrow. -/
theorem innerOuterHornCAttachmentDesc_unique (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g)
    (d : simplicialSpaceDiscrete.obj (outerHornCStage m (i.val + 1) : SSet.{u}) ⟶ X)
    (hf : simplicialSpaceDiscrete.map (outerHornCFaceToNext m i) ≫ d = f)
    (hg : simplicialSpaceDiscrete.map (outerHornCStageStep m i) ≫ d = g) :
    d = innerOuterHornCAttachmentDesc m i h2 f g w :=
  (innerOuterHornCAttachment_isPushout.{u} m i h2).hom_ext
    (hf.trans (innerOuterHornCAttachmentDesc_face m i h2 f g w).symm)
    (hg.trans (innerOuterHornCAttachmentDesc_old m i h2 f g w).symm)

/-- The original face factor equation holds at both original degrees, including degree zero. -/
theorem innerOuterHornCAttachmentDesc_face_app (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g)
    (a b : SimplexCategoryᵒᵖ)
    (x : (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}).obj a) :
    ((innerOuterHornCAttachmentDesc m i h2 f g w).app a).app b
      ((outerHornCFaceToNext m i).app a x) = (f.app a).app b x :=
  congrArg (fun h => (h.app a).app b x) (innerOuterHornCAttachmentDesc_face m i h2 f g w)

/-- The original old-stage factor equation holds at both original degrees. -/
theorem innerOuterHornCAttachmentDesc_old_app (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g)
    (a b : SimplexCategoryᵒᵖ) (x : (outerHornCStage m i.val : SSet.{u}).obj a) :
    ((innerOuterHornCAttachmentDesc m i h2 f g w).app a).app b
      ((outerHornCStageStep m i).app a x) = (g.app a).app b x :=
  congrArg (fun h => (h.app a).app b x) (innerOuterHornCAttachmentDesc_old m i h2 f g w)

/-- The actual descended simplicial-space arrow preserves every outer operator. -/
theorem innerOuterHornCAttachmentDesc_outer (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g)
    {a b : SimplexCategoryᵒᵖ} (β : a ⟶ b) :
    (simplicialSpaceDiscrete.obj (outerHornCStage m (i.val + 1) : SSet.{u})).map β ≫
        (innerOuterHornCAttachmentDesc m i h2 f g w).app b =
      (innerOuterHornCAttachmentDesc m i h2 f g w).app a ≫ X.map β :=
  (innerOuterHornCAttachmentDesc m i h2 f g w).naturality β

/-- The actual descended arrow preserves every inner operator at each original outer degree. -/
theorem innerOuterHornCAttachmentDesc_inner (m : ℕ)
    (i : Fin (Fintype.card (outerHornCFaceIndex m)))
    (h2 : 2 ≤ outerHornCFaceDim (outerHornCEnumeration m i)) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj
        (Δ[outerHornCFaceDim (outerHornCEnumeration m i)] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (outerHornCStage m i.val : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn
        (outerHornCFaceDim (outerHornCEnumeration m i)) 1).ι ≫ f =
      simplicialSpaceDiscrete.map (outerHornCAttachment m i h2) ≫ g)
    (a : SimplexCategoryᵒᵖ) {b c : SimplexCategoryᵒᵖ} (γ : b ⟶ c) :
    ((simplicialSpaceDiscrete.obj (outerHornCStage m (i.val + 1) : SSet.{u})).obj a).map γ ≫
        ((innerOuterHornCAttachmentDesc m i h2 f g w).app a).app c =
      ((innerOuterHornCAttachmentDesc m i h2 f g w).app a).app b ≫ (X.obj a).map γ :=
  ((innerOuterHornCAttachmentDesc m i h2 f g w).app a).naturality γ

end SSet.Rezk
