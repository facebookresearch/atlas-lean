/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Tactic.Tauto
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.Data.Finset.Sort

/-!
# Weak pullback comparisons for horns

For a map of simplicial sets, weak pullback comparisons along every simplex operator into a fixed simplex imply the weak comparison along each horn of positive dimension. The proof constructs the horn preimage from finite unions of face preimages and proves the required weak union inclusions.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkHornPreimage

private abbrev properUnion {P : SSet.{u}} {ι : Type v}
    (F : Finset ι → P.Subcomplex) (S : Finset ι) : P.Subcomplex :=
  ⨆ T, ⨆ (_ : T ⊂ S), F T

private theorem properUnion_singleton {P : SSet.{u}} {ι : Type v}
    (F : Finset ι → P.Subcomplex) (a : ι) :
    properUnion F {a} = F ∅ := by
  apply le_antisymm
  · refine iSup_le fun T => iSup_le fun hT => ?_
    have hT0 : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxa : x = a := Finset.mem_singleton.mp (hT.le hx)
      subst x
      have : ({a} : Finset ι) ⊆ T := by simpa using hx
      exact hT.ne (Finset.Subset.antisymm hT.le this)
    subst T
    exact le_rfl
  · exact le_iSup_of_le ∅ (le_iSup_of_le (by simp) le_rfl)

private theorem erase_strict_of_strict_insert {ι : Type v} [DecidableEq ι]
    {a : ι} {S T : Finset ι} (hT : T ⊂ insert a S)
    (hat : a ∈ T) : T.erase a ⊂ S := by
  apply lt_of_le_of_ne
  · intro x hx
    have hxT := Finset.mem_of_mem_erase hx
    have hxne := (Finset.mem_erase.mp hx).1
    rcases Finset.mem_insert.mp (hT.le hxT) with hxa | hxS
    · exact (hxne hxa).elim
    · exact hxS
  · intro heq
    have hrec : insert a (T.erase a) = T := Finset.insert_erase hat
    rw [heq] at hrec
    exact hT.ne hrec.symm

private theorem insert_strict_of_strict {ι : Type v} [DecidableEq ι]
    {a : ι} {S T : Finset ι} (ha : a ∉ S) (hT : T ⊂ S) :
    insert a T ⊂ insert a S := by
  apply lt_of_le_of_ne
  · exact Finset.insert_subset_insert a hT.le
  · intro heq
    have haT : a ∉ T := fun h => ha (hT.le h)
    have h := congrArg (fun U : Finset ι => U.erase a) heq
    exact hT.ne (by simpa only [Finset.erase_insert haT, Finset.erase_insert ha] using h)

private theorem properUnion_insert {P : SSet.{u}} {ι : Type v} [DecidableEq ι]
    (F : Finset ι → P.Subcomplex) (hF : Monotone F)
    (a : ι) (S : Finset ι) (ha : a ∉ S) :
    properUnion F (insert a S) = properUnion (fun T => F (insert a T)) S ⊔ F S := by
  apply le_antisymm
  · refine iSup_le fun T => iSup_le fun hT => ?_
    by_cases hat : a ∈ T
    · have ht := erase_strict_of_strict_insert hT hat
      have hrec : insert a (T.erase a) = T := Finset.insert_erase hat
      rw [← hrec]
      exact le_sup_of_le_left
        (le_iSup_of_le (T.erase a) (le_iSup_of_le ht le_rfl))
    · have hTS : T ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp (hT.le hx) with hxa | hxS
        · subst x
          exact (hat hx).elim
        · exact hxS
      exact le_sup_of_le_right (hF hTS)
  · apply sup_le
    · refine iSup_le fun T => iSup_le fun hT => ?_
      exact le_iSup_of_le (insert a T)
        (le_iSup_of_le (insert_strict_of_strict ha hT) le_rfl)
    · exact le_iSup_of_le S
        (le_iSup_of_le (Finset.ssubset_insert ha) le_rfl)

private theorem properUnion_insert_inter {P : SSet.{u}} {ι : Type v}
    [DecidableEq ι] (F : Finset ι → P.Subcomplex)
    (hinter : ∀ T U, F (T ∩ U) = F T ⊓ F U)
    (a : ι) (S : Finset ι) (ha : a ∉ S) :
    properUnion (fun T => F (insert a T)) S ⊓ F S = properUnion F S := by
  ext e x
  simp only [properUnion, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subfunctor.min_obj, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨T, hT, hxT⟩, hxS⟩
    have hset : insert a T ∩ S = T := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hya | hyT, hyS⟩
        · subst y
          exact (ha hyS).elim
        · exact hyT
      · intro hyT
        exact ⟨Or.inr hyT, hT.le hyT⟩
    have hx : x ∈ (F (insert a T) ⊓ F S).obj e := ⟨hxT, hxS⟩
    rw [← hinter, hset] at hx
    exact ⟨T, hT, hx⟩
  · rintro ⟨T, hT, hx⟩
    have hset : insert a T ∩ S = T := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hya | hyT, hyS⟩
        · subst y
          exact (ha hyS).elim
        · exact hyT
      · intro hyT
        exact ⟨Or.inr hyT, hT.le hyT⟩
    have h := hx
    rw [← hset, hinter] at h
    exact ⟨⟨T, hT, h.1⟩, h.2⟩

/-- Finite nonempty conical face diagrams with weak original inclusions have a weak
proper-subset union inclusion. The conclusion contains no private helper name. -/
theorem finiteProperUnion_weak {P : SSet.{u}} {ι : Type v} [DecidableEq ι]
    (S : Finset ι) (hS : S.Nonempty) (F : Finset ι → P.Subcomplex)
    (hF : Monotone F) (hinter : ∀ T U, F (T ∩ U) = F T ⊓ F U)
    (hw : ∀ T, T ⊆ S → realizationWeakEquivalences (F T).ι) :
    realizationWeakEquivalences (⨆ T, ⨆ (_ : T ⊂ S), F T).ι := by
  classical
  refine Finset.strongInductionOn
    (p := fun S : Finset ι =>
      S.Nonempty → ∀ (F : Finset ι → P.Subcomplex),
        Monotone F → (∀ T U, F (T ∩ U) = F T ⊓ F U) →
        (∀ T, T ⊆ S → realizationWeakEquivalences (F T).ι) →
        realizationWeakEquivalences (⨆ T, ⨆ (_ : T ⊂ S), F T).ι)
    S ?_ hS F hF hinter hw
  intro S ih hS F hF hinter hw
  rcases hS.exists_eq_singleton_or_nontrivial with ⟨a, rfl⟩ | hS2
  · change realizationWeakEquivalences (properUnion F {a}).ι
    rw [properUnion_singleton]
    exact hw ∅ (Finset.empty_subset _)
  · obtain ⟨a, ha⟩ := hS
    let W := S.erase a
    have hW : W.Nonempty := hS2.erase_nonempty
    have hWS : W ⊂ S := Finset.erase_ssubset ha
    have haW : a ∉ W := Finset.notMem_erase _ _
    have hrec : insert a W = S := Finset.insert_erase ha
    let F' : Finset ι → P.Subcomplex := fun T => F (insert a T)
    have hF' : Monotone F' := fun T U h => hF (Finset.insert_subset_insert a h)
    have hinter' : ∀ T U, F' (T ∩ U) = F' T ⊓ F' U := by
      intro T U
      dsimp only [F']
      rw [← hinter]
      congr 1
      ext x
      simp only [Finset.mem_insert, Finset.mem_inter]
      tauto
    have hwa : realizationWeakEquivalences (properUnion F W).ι :=
      ih W hWS hW F hF hinter (fun T hT => hw T (hT.trans hWS.le))
    have hwb : realizationWeakEquivalences (properUnion F' W).ι :=
      ih W hWS hW F' hF' hinter' (fun T hT => hw (insert a T) (by
        rw [← hrec]
        exact Finset.insert_subset_insert a hT))
    have hwc : realizationWeakEquivalences (F W).ι := hw W hWS.le
    let A := properUnion F W
    let B := properUnion F' W
    let C := F W
    let U := properUnion F S
    have hsup : B ⊔ C = U := by
      dsimp only [B, C, U, F']
      rw [← hrec, properUnion_insert F hF a W haW]
    have hinf : B ⊓ C = A := by
      dsimp only [B, C, A, F']
      exact properUnion_insert_inter F hinter a W haW
    let sq : Subcomplex.BicartSq A B C U := { sup_eq := hsup, inf_eq := hinf }
    let _ : WeakEquivalence A.ι := (weakEquivalence_iff _).mpr hwa
    let _ : WeakEquivalence B.ι := (weakEquivalence_iff _).mpr hwb
    let _ : WeakEquivalence C.ι := (weakEquivalence_iff _).mpr hwc
    let _ : Cofibration (Subcomplex.homOfLE sq.le₁₂) :=
      (cofibration_iff _).mpr (show Mono (Subcomplex.homOfLE sq.le₁₂) from inferInstance)
    let target : IsPushout (𝟙 P) (𝟙 P) (𝟙 P) (𝟙 P) :=
      IsPushout.of_id_fst
    have hu : WeakEquivalence U.ι :=
      weakEquivalence_map_of_isPushouts_of_cofibrant sq.isPushout target
          (a := A.ι) (b := B.ι) (c := C.ι) (d := U.ι)
        (by simp only [Subcomplex.homOfLE_ι, Category.comp_id])
        (by simp only [Subcomplex.homOfLE_ι, Category.comp_id])
        (by simp only [Subcomplex.homOfLE_ι, Category.comp_id])
        (by simp only [Subcomplex.homOfLE_ι, Category.comp_id])
    exact (weakEquivalence_iff _).mp hu
end SSet.RezkHornPreimage

open Opposite
open scoped Simplicial

namespace SSet.RezkHornPreimage

-- Private notation for the native map, not a new public pullback construction.
private abbrev baseChangeMap {X Y A B : SSet.{u}}
    (p : X ⟶ Y) (b : B ⟶ Y) (i : A ⟶ B) :=
  pullback.map p (i ≫ b) p b (𝟙 X) i (𝟙 Y) (by simp) (by simp)

private theorem preimageSquare {X Y : SSet.{u}} (p : X ⟶ Y)
    (A : Y.Subcomplex) :
    IsPullback (A.preimage p).ι (A.fromPreimage p) p A.ι := by
  apply IsPullback.of_forall_isPullback_app
  intro e
  rw [Types.isPullback_iff]
  refine ⟨congr_app (Subcomplex.fromPreimage_ι A p).symm e, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.1
  · intro x y h
    have hx : x ∈ (A.preimage p).obj e := by
      change p.app e x ∈ A.obj e
      rw [h]
      exact y.property
    exact ⟨⟨x, hx⟩, rfl, Subtype.ext h⟩

@[reducible] private noncomputable def preimageIso {X Y : SSet.{u}} (p : X ⟶ Y)
    (A : Y.Subcomplex) :
    (A.preimage p : SSet.{u}) ≅ pullback p A.ι :=
  (preimageSquare p A).isoPullback

@[reducible] private noncomputable def preimageToLiteralIso {X Y : SSet.{u}}
    (p : X ⟶ Y) {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ Y)
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (A.preimage (pullback.snd p b) : SSet.{u}) ≅ pullback p (A.ι ≫ b) :=
  preimageIso (pullback.snd p b) A ≪≫ pullbackLeftPullbackSndIso p b A.ι

private theorem preimageToLiteralIso_factor {X Y : SSet.{u}}
    (p : X ⟶ Y) {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ Y)
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (preimageToLiteralIso p b A).hom ≫ baseChangeMap p b A.ι =
      (A.preimage (pullback.snd p b)).ι := by
  apply pullback.hom_ext
  · simp only [preimageToLiteralIso, Iso.trans_hom, baseChangeMap,
      Category.assoc, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_fst, preimageIso,
      IsPullback.isoPullback_hom_fst_assoc]
  · have h2 : (pullbackLeftPullbackSndIso p b A.ι).hom ≫
        pullback.snd p (A.ι ≫ b) = pullback.snd (pullback.snd p b) A.ι :=
      pullbackLeftPullbackSndIso_hom_snd p b A.ι
    have h1 : (preimageIso (pullback.snd p b) A).hom ≫
        pullback.snd (pullback.snd p b) A.ι = A.fromPreimage (pullback.snd p b) :=
      (preimageSquare (pullback.snd p b) A).isoPullback_hom_snd
    simp only [preimageToLiteralIso, Iso.trans_hom, baseChangeMap,
      Category.assoc, pullback.lift_snd]
    calc
      (preimageIso (pullback.snd p b) A).hom ≫
          (pullbackLeftPullbackSndIso p b A.ι).hom ≫ pullback.snd p (A.ι ≫ b) ≫ A.ι =
          (preimageIso (pullback.snd p b) A).hom ≫
            pullback.snd (pullback.snd p b) A.ι ≫ A.ι := by
        simpa only [Category.assoc] using
          congrArg (fun t => (preimageIso (pullback.snd p b) A).hom ≫ t ≫ A.ι) h2
      _ = A.fromPreimage (pullback.snd p b) ≫ A.ι := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ A.ι) h1
      _ = (A.preimage (pullback.snd p b)).ι ≫ pullback.snd p b :=
        Subcomplex.fromPreimage_ι _ _

private theorem facePreimage_weak {X Y : SSet.{u}}
    (p : X ⟶ Y) {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ Y)
    (S : Finset (Fin (n + 1))) (hS : S.Nonempty)
    (hδ : ∀ (m : ℕ) (δ : ⦋m⦌ ⟶ ⦋n⦌),
      realizationWeakEquivalences (baseChangeMap p b (SSet.stdSimplex.map δ))) :
    realizationWeakEquivalences
      ((stdSimplex.face S).preimage (pullback.snd p b)).ι := by
  classical
  let m := S.card - 1
  have hm : S.card = m + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (Finset.card_pos.mpr hS))).symm
  let A := stdSimplex.face.{u} S
  let e : (Δ[m] : SSet.{u}) ≅ (A : SSet.{u}) :=
    stdSimplex.isoOfRepresentableBy
      (stdSimplex.faceRepresentableBy S m (Finset.orderIsoOfFin S hm))
  let f : (Δ[m] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) := e.hom ≫ A.ι
  let δ : ⦋m⦌ ⟶ ⦋n⦌ := stdSimplex.objEquiv (yonedaEquiv f)
  have hmap : SSet.stdSimplex.map δ = f := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_map]
    exact stdSimplex.objEquiv.symm_apply_apply (yonedaEquiv f)
  have hf : realizationWeakEquivalences (baseChangeMap p b f) := by
    rw [← hmap]
    exact hδ m δ
  let mid : pullback p (f ≫ b) ⟶ pullback p (A.ι ≫ b) :=
    pullback.map _ _ _ _ (𝟙 X) e.hom (𝟙 Y) (by simp)
      (by simp only [f, Category.comp_id, Category.assoc])
  let _ : IsIso mid := by dsimp only [mid]; infer_instance
  have hfac : mid ≫ baseChangeMap p b A.ι = baseChangeMap p b f := by
    apply pullback.hom_ext
    · simp only [mid, baseChangeMap, pullback.map, Category.assoc, pullback.lift_fst,
        Category.comp_id, f]
    · have hA : baseChangeMap p b A.ι ≫ pullback.snd p b =
          pullback.snd p (A.ι ≫ b) ≫ A.ι := by
        dsimp only [baseChangeMap, pullback.map]
        exact pullback.lift_snd _ _ _
      have hmid : mid ≫ pullback.snd p (A.ι ≫ b) =
          pullback.snd p (f ≫ b) ≫ e.hom := by
        dsimp only [mid, pullback.map]
        exact pullback.lift_snd _ _ _
      have hf' : baseChangeMap p b f ≫ pullback.snd p b =
          pullback.snd p (f ≫ b) ≫ f := by
        dsimp only [baseChangeMap, pullback.map]
        exact pullback.lift_snd _ _ _
      calc
        (mid ≫ baseChangeMap p b A.ι) ≫ pullback.snd p b =
            mid ≫ (baseChangeMap p b A.ι ≫ pullback.snd p b) := Category.assoc _ _ _
        _ = mid ≫ (pullback.snd p (A.ι ≫ b) ≫ A.ι) := congrArg (mid ≫ ·) hA
        _ = (mid ≫ pullback.snd p (A.ι ≫ b)) ≫ A.ι := (Category.assoc _ _ _).symm
        _ = (pullback.snd p (f ≫ b) ≫ e.hom) ≫ A.ι := congrArg (· ≫ A.ι) hmid
        _ = pullback.snd p (f ≫ b) ≫ f := Category.assoc _ _ _
        _ = baseChangeMap p b f ≫ pullback.snd p b := hf'.symm
  have hA : realizationWeakEquivalences (baseChangeMap p b A.ι) := by
    have hw : realizationWeakEquivalences (mid ≫ baseChangeMap p b A.ι) := by
      rw [hfac]
      exact hf
    exact (realizationWeakEquivalences.cancel_left_of_respectsIso _ _).mp hw
  have hi : realizationWeakEquivalences (preimageToLiteralIso p b A).hom :=
    realizationWeakEquivalences.of_isIso _
  have h := realizationWeakEquivalences.comp_mem _ _ hi hA
  rwa [preimageToLiteralIso_factor] at h

private theorem facesContainingVertex_union_eq_horn (n : ℕ) (k : Fin (n + 1)) :
    (⨆ T : Finset (Fin (n + 1)),
      ⨆ (_ : T ⊂ Finset.univ.erase k), stdSimplex.face.{u} (insert k T)) = horn n k := by
  classical
  apply le_antisymm
  · refine iSup_le fun T => iSup_le fun hT => ?_
    obtain ⟨j, hj, hTj⟩ := Finset.ssubset_iff_exists_subset_erase.mp hT
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    have hsub : insert k T ⊆ ({j}ᶜ : Finset (Fin (n + 1))) := by
      intro x hx
      simp only [Finset.mem_compl, Finset.mem_singleton]
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hjk.symm
      · exact (Finset.mem_erase.mp (hTj hxT)).1
    exact ((stdSimplex.face_le_face_iff _ _).mpr hsub).trans
      (face_le_horn j k hjk)
  · rw [horn_eq_iSup]
    refine iSup_le fun (j : ({k}ᶜ : Set (Fin (n + 1)))) => ?_
    have hjk : j.val ≠ k := fun h => j.property (Set.mem_singleton_iff.mpr h)
    have hj : j.val ∈ Finset.univ.erase k := by simp [hjk]
    let T := (Finset.univ.erase k).erase j.val
    have hT : T ⊂ Finset.univ.erase k := Finset.erase_ssubset hj
    have heq : insert k T = ({j.val}ᶜ : Finset (Fin (n + 1))) := by
      ext x
      by_cases hxk : x = k
      · subst x
        simp [T, hjk.symm]
      · simp [T, hxk]
    rw [← heq]
    exact le_iSup_of_le T (le_iSup_of_le hT le_rfl)

/-- Rezk9.3, concrete scalar/all-universe form. All finite face pullbacks and their
weak union are constructed internally; positive horn dimension is essential. -/
theorem horn_preimage_weak {X Y : SSet.{u}} (p : X ⟶ Y)
    (n : ℕ) [NeZero n] (k : Fin (n + 1)) (b : (Δ[n] : SSet.{u}) ⟶ Y)
    (hδ : ∀ (m : ℕ) (δ : ⦋m⦌ ⟶ ⦋n⦌),
      realizationWeakEquivalences
        (pullback.map p (SSet.stdSimplex.map δ ≫ b) p b
          (𝟙 X) (SSet.stdSimplex.map δ) (𝟙 Y) (by simp) (by simp))) :
    realizationWeakEquivalences
      (pullback.map p ((Λ[n, k] : (Δ[n] : SSet.{u}).Subcomplex).ι ≫ b) p b
        (𝟙 X) (Λ[n, k] : (Δ[n] : SSet.{u}).Subcomplex).ι (𝟙 Y)
        (by simp) (by simp)) := by
  classical
  let P := pullback p b
  let V : Finset (Fin (n + 1)) := Finset.univ.erase k
  let F : Finset (Fin (n + 1)) → P.Subcomplex :=
    fun T => (stdSimplex.face (insert k T)).preimage (pullback.snd p b)
  have hVcard : V.card = n := by
    dsimp only [V]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    exact Nat.add_sub_cancel _ _
  have hV : V.Nonempty := Finset.card_pos.mp
    (hVcard.symm ▸ Nat.pos_of_ne_zero (NeZero.ne n))
  have hF : Monotone F := fun T U hTU =>
    Subcomplex.preimage_monotone (pullback.snd p b)
      ((stdSimplex.face_le_face_iff _ _).mpr (Finset.insert_subset_insert k hTU))
  have hinter : ∀ T U, F (T ∩ U) = F T ⊓ F U := by
    intro T U
    dsimp only [F]
    rw [← Subcomplex.preimage_min, stdSimplex.face_inter_face]
    congr 2
    ext x
    simp only [Finset.inf_eq_inter, Finset.mem_insert, Finset.mem_inter]
    tauto
  have hw : ∀ T, T ⊆ V → realizationWeakEquivalences (F T).ι := by
    intro T _
    exact facePreimage_weak p b (insert k T) (Finset.insert_nonempty _ _) hδ
  have hU : realizationWeakEquivalences (⨆ T, ⨆ (_ : T ⊂ V), F T).ι :=
    finiteProperUnion_weak V hV F hF hinter hw
  have heq : (⨆ T, ⨆ (_ : T ⊂ V), F T) =
      (horn n k).preimage (pullback.snd p b) := by
    dsimp only [F]
    calc
      (⨆ T, ⨆ (_ : T ⊂ V), (stdSimplex.face (insert k T)).preimage (pullback.snd p b)) =
          (⨆ T, ⨆ (_ : T ⊂ V), stdSimplex.face (insert k T)).preimage (pullback.snd p b) := by
        ext a x
        simp only [Subfunctor.iSup_obj, Subcomplex.preimage_obj, Set.mem_preimage,
          Set.mem_iUnion]
      _ = (horn n k).preimage (pullback.snd p b) :=
        congrArg (fun A => A.preimage (pullback.snd p b))
          (facesContainingVertex_union_eq_horn n k)
  rw [heq] at hU
  let e := preimageToLiteralIso p b (horn n k)
  have hfac : e.hom ≫ baseChangeMap p b (horn n k).ι =
      ((horn n k).preimage (pullback.snd p b)).ι :=
    preimageToLiteralIso_factor p b (horn n k)
  have hcomp : realizationWeakEquivalences
      (e.hom ≫ baseChangeMap p b (horn n k).ι) := by
    rw [hfac]
    exact hU
  exact (realizationWeakEquivalences.cancel_left_of_respectsIso _ _).mp hcomp

end SSet.RezkHornPreimage
