/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.AlgebraicTopology.SimplicialCategory.TensorCotensor

/-!
# The original H/C outer-horn decomposition

The auxiliary subcomplex consists of faces omitting a vertex at least two.
Its literal intersection with the first coface is the preceding outer horn.
The native bicartesian subcomplex square gives Rezk's original pushout.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Rezk

/-- The original union of cofaces whose omitted vertex is at least two. -/
def outerHornC (k : ℕ) : (Δ[k] : SSet.{u}).Subcomplex :=
  ⨆ (j : {j : Fin (k + 1) // 2 ≤ j.val}), stdSimplex.face {j.val}ᶜ

/-- The union retains the original missing-vertex test in every degree. -/
theorem mem_outerHornC_iff {k d : ℕ} (a : (Δ[k] : SSet.{u}) _⦋d⦌) :
    a ∈ (outerHornC k).obj (op ⦋d⦌) ↔
      ∃ j : Fin (k + 1), 2 ≤ j.val ∧ j ∉ Set.range a := by
  simp only [outerHornC, Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j.val, j.property, ?_⟩
    simpa only [stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton,
      Set.mem_range, not_exists] using hj
  · rintro ⟨j, hj, ha⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    simpa only [stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton,
      Set.mem_range, not_exists] using ha

/-- There is no omitted tail vertex in dimension zero. -/
@[simp] theorem outerHornC_zero : outerHornC.{u} 0 = ⊥ := by
  ext d a
  change (a ∈ (outerHornC 0).obj (op ⦋d.unop.len⦌)) ↔ False
  rw [mem_outerHornC_iff]
  constructor
  · rintro ⟨j, hj, _⟩
    omega
  · exact False.elim

/-- There is no omitted tail vertex in dimension one. -/
@[simp] theorem outerHornC_one : outerHornC.{u} 1 = ⊥ := by
  ext d a
  change (a ∈ (outerHornC 1).obj (op ⦋d.unop.len⦌)) ↔ False
  rw [mem_outerHornC_iff]
  constructor
  · rintro ⟨j, hj, _⟩
    omega
  · exact False.elim

/-- The original zero-dimensional outer horn is empty. -/
@[simp] theorem outerHorn_zero : horn.{u} 0 0 = ⊥ := by
  ext d a
  change (a ∈ (horn 0 0).obj (op ⦋d.unop.len⦌)) ↔ False
  rw [mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hj, _⟩
    exact hj (Fin.ext (by omega))
  · exact False.elim

/-- Every auxiliary face is an original positive face of the outer horn. -/
theorem outerHornC_le_outerHorn (k : ℕ) : outerHornC.{u} k ≤ horn k 0 := by
  apply iSup_le
  intro j
  exact face_le_horn j.val 0 (by intro h; have := j.property; simp [h] at this)

/-- The outer horn is the auxiliary union together with the first coface. -/
theorem outerHorn_eq_sup_C_face (n : ℕ) :
    horn.{u} (n + 1) 0 = outerHornC (n + 1) ⊔ stdSimplex.face {(1 : Fin (n + 2))}ᶜ := by
  ext d a
  change (a ∈ (horn (n + 1) 0).obj (op ⦋d.unop.len⦌)) ↔
    (a ∈ (outerHornC (n + 1)).obj (op ⦋d.unop.len⦌) ∨
      a ∈ (stdSimplex.face {(1 : Fin (n + 2))}ᶜ).obj (op ⦋d.unop.len⦌))
  rw [mem_horn_iff_notMem_range, mem_outerHornC_iff]
  constructor
  · rintro ⟨j, hj, ha⟩
    by_cases h : j = 1
    · right
      subst j
      rw [stdSimplex.mem_face_iff]
      simpa only [Finset.mem_compl, Finset.mem_singleton,
        Set.mem_range, not_exists] using ha
    · left
      refine ⟨j, ?_, ha⟩
      have hz : j.val ≠ 0 := fun e => hj (Fin.ext e)
      have ho : j.val ≠ 1 := fun e => h (Fin.ext (by simpa using e))
      omega
  · rintro (⟨j, hj, ha⟩ | ha)
    · exact ⟨j, by intro h; have := hj; simp [h] at this, ha⟩
    · refine ⟨1, by intro h; have := congrArg Fin.val h; simp at this, ?_⟩
      rw [stdSimplex.mem_face_iff] at ha
      simpa only [Finset.mem_compl, Finset.mem_singleton,
        Set.mem_range, not_exists] using ha

private theorem cofaceOne_apply {n d : ℕ} (a : (Δ[n] : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) :
    ((stdSimplex.δ (1 : Fin (n + 2))).app (op ⦋d⦌) a) i =
      (1 : Fin (n + 2)).succAbove (a i) := rfl

private theorem one_succAbove_ge_two {n : ℕ} (i : Fin (n + 1)) :
    2 ≤ ((1 : Fin (n + 2)).succAbove i).val ↔ i ≠ 0 := by
  by_cases h : i = 0
  · subst i
    simp
  · have hi : 0 < i.val := by
      have : i.val ≠ 0 := fun e => h (Fin.ext e)
      omega
    have e : ∃ j : Fin n, j.succ = i := by
      refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
      apply Fin.ext
      simp
      omega
    obtain ⟨j, rfl⟩ := e
    simp [Fin.one_succAbove_succ]

/-- The original first coface pulls C back to the preceding outer horn. -/
theorem outerHornC_preimage_cofaceOne (n : ℕ) :
    (outerHornC.{u} (n + 1)).preimage (stdSimplex.δ (1 : Fin (n + 2))) =
      horn n 0 := by
  ext d a
  change (((stdSimplex.δ (1 : Fin (n + 2))).app (op ⦋d.unop.len⦌) a) ∈
      (outerHornC (n + 1)).obj (op ⦋d.unop.len⦌)) ↔
    a ∈ (horn n 0).obj (op ⦋d.unop.len⦌)
  rw [mem_outerHornC_iff, mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hj, ha⟩
    have hj1 : j ≠ 1 := fun h => by subst j; simp at hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj1
    refine ⟨i, (one_succAbove_ge_two i).mp (hi ▸ hj), ?_⟩
    rintro ⟨b, hb⟩
    apply ha
    refine ⟨b, ?_⟩
    rw [cofaceOne_apply, hb]
    exact hi
  · rintro ⟨i, hi, ha⟩
    refine ⟨(1 : Fin (n + 2)).succAbove i, (one_succAbove_ge_two i).mpr hi, ?_⟩
    rintro ⟨b, hb⟩
    apply ha
    refine ⟨b, ?_⟩
    rw [cofaceOne_apply] at hb
    exact Fin.succAbove_right_injective hb

/-- The literal map from the preceding horn into C induced by the first coface. -/
def outerHornCoface (n : ℕ) :
    (horn.{u} n 0 : SSet.{u}) ⟶ (outerHornC (n + 1) : SSet.{u}) :=
  Subfunctor.lift ((horn n 0).ι ≫ stdSimplex.δ (1 : Fin (n + 2))) (by
    change Subfunctor.range (Subfunctor.ι (horn.{u} n 0) ≫
      stdSimplex.δ (1 : Fin (n + 2))) ≤ _
    rw [Subfunctor.range_comp, Subfunctor.range_ι]
    change (horn.{u} n 0).image (stdSimplex.δ (1 : Fin (n + 2))) ≤ _
    rw [Subcomplex.image_le_iff, outerHornC_preimage_cofaceOne])

/-- The induced map retains its original ambient coface equation. -/
@[reassoc (attr := simp)] theorem outerHornCoface_ι (n : ℕ) :
    outerHornCoface.{u} n ≫ (outerHornC (n + 1)).ι =
      (horn n 0).ι ≫ stdSimplex.δ (1 : Fin (n + 2)) := rfl

/-- The literal auxiliary inclusion in the original outer horn. -/
def outerHornCInclusion (n : ℕ) :
    (outerHornC.{u} (n + 1) : SSet.{u}) ⟶ (horn (n + 1) 0 : SSet.{u}) :=
  Subcomplex.homOfLE (outerHornC_le_outerHorn (n + 1))

/-- The auxiliary inclusion retains the original ambient inclusion. -/
@[reassoc (attr := simp)] theorem outerHornCInclusion_ι (n : ℕ) :
    outerHornCInclusion.{u} n ≫ (horn (n + 1) 0).ι = (outerHornC (n + 1)).ι := rfl

/-- The image of the preceding horn is the exact C/first-face intersection. -/
theorem outerHorn_image_cofaceOne (n : ℕ) :
    (horn.{u} n 0).image (stdSimplex.δ (1 : Fin (n + 2))) =
      outerHornC (n + 1) ⊓ stdSimplex.face {(1 : Fin (n + 2))}ᶜ := by
  apply le_antisymm
  · exact le_inf
      (by rw [Subcomplex.image_le_iff, outerHornC_preimage_cofaceOne])
      (by simpa only [stdSimplex.range_δ] using
        (horn.{u} n 0).image_le_range (stdSimplex.δ (1 : Fin (n + 2))))
  · intro d a ha
    have hr : a ∈ (Subcomplex.range (stdSimplex.δ (1 : Fin (n + 2)))).obj d := by
      rw [stdSimplex.range_δ]
      exact ha.2
    obtain ⟨b, hb⟩ := hr
    have hc : b ∈ ((outerHornC (n + 1)).preimage
        (stdSimplex.δ (1 : Fin (n + 2)))).obj d := by
      change (stdSimplex.δ (1 : Fin (n + 2))).app d b ∈
        (outerHornC (n + 1)).obj d
      simpa only [hb] using ha.1
    rw [outerHornC_preimage_cofaceOne] at hc
    exact ⟨b, hc, hb⟩

private def intersectionIso (n : ℕ) :
    (horn.{u} n 0 : SSet.{u}) ≅
      ((outerHornC (n + 1) ⊓ stdSimplex.face {(1 : Fin (n + 2))}ᶜ :
        (Δ[n + 1] : SSet.{u}).Subcomplex) : SSet.{u}) := by
  let f := (horn.{u} n 0).toImage (stdSimplex.δ (1 : Fin (n + 2)))
  letI : Mono (stdSimplex.δ (1 : Fin (n + 2)) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]) := by
    rw [← stdSimplex.faceSingletonComplIso_hom_ι (1 : Fin (n + 2))]
    infer_instance
  letI : Mono f := by
    apply mono_of_mono_fac ((horn n 0).toImage_ι (stdSimplex.δ (1 : Fin (n + 2))))
  letI : IsIso f := isIso_of_mono_of_epi f
  let e := asIso f
  exact e ≪≫ Subcomplex.eqToIso (outerHorn_image_cofaceOne n)

private theorem intersectionIso_ι (n : ℕ) :
    (intersectionIso.{u} n).hom ≫
      (outerHornC (n + 1) ⊓ stdSimplex.face {(1 : Fin (n + 2))}ᶜ).ι =
        (horn n 0).ι ≫ stdSimplex.δ (1 : Fin (n + 2)) := by
  simp [intersectionIso, Subcomplex.toImage_ι]

/-- The original H/C square is the native bicartesian subcomplex pushout. -/
theorem outerHornC_isPushout (n : ℕ) :
    IsPushout (horn.{u} n 0).ι (outerHornCoface n)
      (horn.ι 0 (1 : Fin (n + 2)) (by intro h; have := congrArg Fin.val h; simp at this))
      (outerHornCInclusion n) := by
  let C := outerHornC.{u} (n + 1)
  let F := stdSimplex.face.{u} {(1 : Fin (n + 2))}ᶜ
  have square : Subcomplex.BicartSq (C ⊓ F) F C (horn (n + 1) 0) :=
    { sup_eq := by rw [outerHorn_eq_sup_C_face]; exact sup_comm _ _
      inf_eq := inf_comm _ _ }
  have sq := square.isPushout
  let e₁ := intersectionIso.{u} n
  let e₂ := stdSimplex.faceSingletonComplIso.{u} (1 : Fin (n + 2))
  apply sq.of_iso' e₁ e₂ (Iso.refl _) (Iso.refl _)
  · apply (cancel_mono F.ι).mp
    change (intersectionIso n).hom ≫ Subcomplex.homOfLE square.le₁₂ ≫ F.ι =
      (horn n 0).ι ≫ (stdSimplex.faceSingletonComplIso (1 : Fin (n + 2))).hom ≫ F.ι
    dsimp only [F]
    rw [Subcomplex.homOfLE_ι, stdSimplex.faceSingletonComplIso_hom_ι]
    exact intersectionIso_ι n
  · apply (cancel_mono C.ι).mp
    change (intersectionIso n).hom ≫ Subcomplex.homOfLE square.le₁₃ ≫ C.ι =
      outerHornCoface n ≫ C.ι
    dsimp only [C]
    rw [Subcomplex.homOfLE_ι, outerHornCoface_ι]
    exact intersectionIso_ι n
  · apply (cancel_mono (horn.{u} (n + 1) 0).ι).mp
    change (stdSimplex.faceSingletonComplIso (1 : Fin (n + 2))).hom ≫
      Subcomplex.homOfLE square.le₂₄ ≫ (horn (n + 1) 0).ι =
        horn.ι 0 (1 : Fin (n + 2)) _ ≫ (horn (n + 1) 0).ι
    simp only [Subcomplex.homOfLE_ι, stdSimplex.faceSingletonComplIso_hom_ι, horn.ι_ι]
  · rfl

/-- The original double-initial-coface simplex, with ordered range two through k. -/
def outerHornTail (m : ℕ) : (Δ[m + 2] : SSet.{u}) _⦋m⦌ :=
  stdSimplex.objEquiv.symm
    (SimplexCategory.δ (0 : Fin (m + 2)) ≫ SimplexCategory.δ (0 : Fin (m + 3)))

/-- The tail simplex retains the original ordered double-coface values. -/
@[simp] theorem outerHornTail_apply (m : ℕ) (i : Fin (m + 1)) :
    outerHornTail.{u} m i = i.succ.succ := rfl

/-- C excludes the original double-initial-coface simplex. -/
theorem outerHornTail_not_mem_C (m : ℕ) :
    outerHornTail.{u} m ∉ (outerHornC (m + 2)).obj (op ⦋m⦌) := by
  rw [mem_outerHornC_iff]
  rintro ⟨j, hj, ha⟩
  apply ha
  refine ⟨⟨j.val - 2, by omega⟩, ?_⟩
  apply Fin.ext
  simp
  omega

/-- Every subcomplex excluding the original tail simplex lies in C. -/
theorem le_outerHornC_of_tail_not_mem (m : ℕ)
    (K : (Δ[m + 2] : SSet.{u}).Subcomplex)
    (hK : outerHornTail m ∉ K.obj (op ⦋m⦌)) : K ≤ outerHornC (m + 2) := by
  intro d a ha
  induction d using Opposite.rec with | _ d =>
    induction d using SimplexCategory.rec with | _ d =>
      rw [mem_outerHornC_iff]
      by_contra h
      have full : ∀ j : Fin (m + 1), ∃ i : Fin (d + 1),
          a i = j.succ.succ := by
        intro j
        by_contra hn
        exact h ⟨j.succ.succ, by simp, hn⟩
      choose t ht using full
      have monotone : Monotone t := by
        intro i j hij
        rcases eq_or_lt_of_le hij with rfl | hij
        · exact le_rfl
        · by_contra hle
          have hlt : t j ≤ t i := (lt_of_not_ge hle).le
          have hmon : a (t j) ≤ a (t i) := stdSimplex.monotone_apply a hlt
          rw [ht j, ht i] at hmon
          have hv : j.val + 2 ≤ i.val + 2 := hmon
          have hi : i.val < j.val := hij
          omega
      let tHom : ⦋m⦌ ⟶ ⦋d⦌ := SimplexCategory.Hom.mk ⟨t, monotone⟩
      have he : (Δ[m + 2] : SSet.{u}).map tHom.op a = outerHornTail m := by
        apply stdSimplex.ext
        intro i
        exact ht i
      apply hK
      rw [← he]
      exact K.map tHom.op ha

/-- The chosen original pushout comparison to the outer horn. -/
def outerHornCPushoutIso (n : ℕ) :
    pushout (horn.{u} n 0).ι (outerHornCoface n) ≅ (horn (n + 1) 0 : SSet.{u}) :=
  (outerHornC_isPushout.{u} n).isoPushout.symm

/-- The standard-simplex injection is the original retained first coface. -/
@[reassoc (attr := simp)] theorem outerHornCPushoutIso_inl (n : ℕ) :
    pushout.inl _ _ ≫ (outerHornCPushoutIso.{u} n).hom =
      horn.ι 0 (1 : Fin (n + 2)) (by intro h; have := congrArg Fin.val h; simp at this) :=
  (outerHornC_isPushout.{u} n).inl_isoPushout_inv

/-- The auxiliary injection is the original C inclusion. -/
@[reassoc (attr := simp)] theorem outerHornCPushoutIso_inr (n : ℕ) :
    pushout.inr _ _ ≫ (outerHornCPushoutIso.{u} n).hom = outerHornCInclusion n :=
  (outerHornC_isPushout.{u} n).inr_isoPushout_inv

/-- The inverse comparison retains the original first-coface injection. -/
@[reassoc (attr := simp)] theorem outerHornCPushoutIso_face (n : ℕ) :
    horn.ι 0 (1 : Fin (n + 2)) (by intro h; have := congrArg Fin.val h; simp at this) ≫
      (outerHornCPushoutIso.{u} n).inv = pushout.inl _ _ := by
  rw [Iso.comp_inv_eq]
  exact (outerHornCPushoutIso_inl n).symm

/-- The inverse comparison retains the original auxiliary injection. -/
@[reassoc (attr := simp)] theorem outerHornCPushoutIso_C (n : ℕ) :
    outerHornCInclusion n ≫ (outerHornCPushoutIso.{u} n).inv = pushout.inr _ _ := by
  rw [Iso.comp_inv_eq]
  exact (outerHornCPushoutIso_inr n).symm

/-- Every compatible pair of original maps descends uniquely through H. -/
theorem existsUnique_outerHornCDesc (n : ℕ) {X : SSet.{u}}
    (f : (Δ[n] : SSet.{u}) ⟶ X) (g : (outerHornC (n + 1) : SSet.{u}) ⟶ X)
    (h : (horn n 0).ι ≫ f = outerHornCoface n ≫ g) :
    ∃! d : (horn (n + 1) 0 : SSet.{u}) ⟶ X,
      horn.ι 0 (1 : Fin (n + 2)) (by intro h; have := congrArg Fin.val h; simp at this) ≫ d = f ∧
        outerHornCInclusion n ≫ d = g := by
  let d := (outerHornCPushoutIso.{u} n).inv ≫ pushout.desc f g h
  refine ⟨d, ?_, ?_⟩
  · constructor
    · simp [d]
    · simp [d]
  · intro d' hd'
    apply (cancel_epi (outerHornCPushoutIso.{u} n).hom).mp
    apply pushout.hom_ext
    · simpa [d] using hd'.1
    · simpa [d] using hd'.2

/-- The same original square is a pushout under the inner-discrete embedding. -/
theorem innerOuterHornC_isPushout (n : ℕ) :
    IsPushout (simplicialSpaceDiscrete.map (horn.{u} n 0).ι)
      (simplicialSpaceDiscrete.map (outerHornCoface n))
      (simplicialSpaceDiscrete.map
        (horn.ι 0 (1 : Fin (n + 2)) (by intro h; have := congrArg Fin.val h; simp at this)))
      (simplicialSpaceDiscrete.map (outerHornCInclusion n)) := by
  apply IsPushout.of_forall_isPushout_app
  intro d
  apply IsPushout.of_forall_isPushout_app
  intro e
  exact (outerHornC_isPushout.{u} n).app d

end SSet.Rezk
