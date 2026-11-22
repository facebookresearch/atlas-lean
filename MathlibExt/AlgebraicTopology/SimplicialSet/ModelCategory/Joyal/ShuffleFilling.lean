/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleBridges
public import
  MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
public import MathlibExt.Data.Fin.SuccAbove

/-!
# Shuffle horn filling for `Δ[n] ⊗ Δ[2]` (the supporting results)

This module proves the additional comparison obligation of `ShuffleBridges.lean`: the two
cell inputs `SSet.ShuffleHornZeroCellExtension n C` and
`SSet.ShuffleHornTwoCellExtension n C` for every `n` and every
quasicategory `C`, in the unfolded form

```text
SSet.exists_extension_of_unionProd_boundary_horn_zero
SSet.exists_extension_of_unionProd_boundary_horn_two
```
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-!
## Generic helpers for simplices of `Δ[n] ⊗ Δ[2]`

Faces through `prodStdSimplex.objEquiv`, containment in the
boundary/horn product subcomplexes from a missed coordinate,
injectivity of classifying maps of injective chains, ranges of
faces, and the image of a face subcomplex under a classifying
map. These are the `Δ[2]` analogues of the helpers of
`PrismCobase.lean`, whose attachment pushout
(`Subcomplex.isPushout_hornAttach`,
`Subcomplex.exists_extension_sup_of_horn_filler`) is already generic and
is reused unchanged.
-/

section ShuffleGenericHelpers

variable {n m : ℕ}

/-- Faces in `Δ[n] ⊗ Δ[2]` read through `objEquiv` are
precomposition with `Fin.succAbove`. -/
lemma shuffle_objEquiv_δ_apply
    (z : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋m + 1⦌) (j : Fin (m + 2))
    (t : Fin (m + 1)) :
    prodStdSimplex.objEquiv ((Δ[n] ⊗ Δ[2]).δ j z) t =
      prodStdSimplex.objEquiv z (j.succAbove t) :=
  prodStdSimplex.objEquiv_δ_apply z j t

/-- A simplex of `Δ[n] ⊗ Δ[2]` whose first coordinates miss
`v` generates a subcomplex contained in `∂Δ[n] ⊗ Δ[2]`. -/
lemma shuffle_ofSimplex_le_boundary_prod_top_of_fst_miss
    {z : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋m⦌} {v : Fin (n + 1)}
    (h : ∀ t : Fin (m + 1),
      (prodStdSimplex.objEquiv z t).1 ≠ v) :
    Subcomplex.ofSimplex z ≤ (∂Δ[n]).prod ⊤ := by
  rw [Subcomplex.ofSimplex_le_iff]
  exact ⟨mem_boundary_of_forall_ne z.1 v h, Set.mem_univ _⟩

/-- A simplex of `Δ[n] ⊗ Δ[2]` whose second coordinates miss
`w ≠ i` generates a subcomplex contained in `Δ[n] ⊗ Λ[2,i]`. -/
lemma shuffle_ofSimplex_le_top_prod_horn_of_snd_miss
    {z : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋m⦌} {i w : Fin 3}
    (hw : w ≠ i)
    (h : ∀ t : Fin (m + 1),
      (prodStdSimplex.objEquiv z t).2 ≠ w) :
    Subcomplex.ofSimplex z ≤
      (⊤ : (Δ[n]).Subcomplex).prod Λ[2, i] := by
  rw [Subcomplex.ofSimplex_le_iff]
  refine ⟨Set.mem_univ _, ?_⟩
  rw [mem_horn_iff_notMem_range]
  exact ⟨w, hw, fun ⟨t, ht⟩ ↦ h t ht⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The classifying map of an injective chain in
`Fin (n+1) × Fin 3` is injective on simplices (the `Δ[2]`
analogue of the `Mono` instance for `SSet.prismTauMap`, i.e.
for `SSet.prodStdSimplex₁.ι`). -/
lemma shuffle_map_injective_of_injective_objEquiv
    {σ : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋m⦌}
    (hinj : Function.Injective (prodStdSimplex.objEquiv σ))
    {d : ℕ} {s₁ s₂ : (Δ[m] : SSet.{u}) _⦋d⦌}
    (h : (yonedaEquiv.symm σ).app _ s₁ =
      (yonedaEquiv.symm σ).app _ s₂) :
    s₁ = s₂ := by
  obtain ⟨f₁, rfl⟩ := stdSimplex.objEquiv.symm.surjective s₁
  obtain ⟨f₂, rfl⟩ := stdSimplex.objEquiv.symm.surjective s₂
  rw [yonedaEquiv_symm_app_objEquiv_symm,
    yonedaEquiv_symm_app_objEquiv_symm] at h
  have hcomp : (prodStdSimplex.objEquiv.{u} σ).comp f₁.toOrderHom =
      (prodStdSimplex.objEquiv.{u} σ).comp f₂.toOrderHom :=
    congrArg prodStdSimplex.objEquiv h
  have hto : f₁.toOrderHom = f₂.toOrderHom :=
    DFunLike.ext _ _ fun t ↦ hinj (DFunLike.congr_fun hcomp t)
  have hf : f₁ = f₂ := SimplexCategory.Hom.ext_iff.2 hto
  rw [hf]

/-- The range of a face of an injective chain is the range of
the chain minus the omitted vertex. -/
lemma shuffle_mem_range_objEquiv_δ_iff
    {z : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋m + 1⦌}
    (hinj : Function.Injective (prodStdSimplex.objEquiv z))
    (j : Fin (m + 2)) {p : Fin (n + 1) × Fin 3} :
    p ∈ Set.range
        (prodStdSimplex.objEquiv ((Δ[n] ⊗ Δ[2]).δ j z)) ↔
      p ∈ Set.range (prodStdSimplex.objEquiv z) ∧
        p ≠ prodStdSimplex.objEquiv z j := by
  constructor
  · rintro ⟨t, ht⟩
    rw [shuffle_objEquiv_δ_apply] at ht
    refine ⟨⟨j.succAbove t, ht⟩, ?_⟩
    rw [← ht]
    exact fun hEq ↦ Fin.succAbove_ne j t (hinj hEq)
  · rintro ⟨⟨t, ht⟩, hne⟩
    have htj : t ≠ j := by
      rintro rfl
      exact hne ht.symm
    obtain ⟨s, hs⟩ : t ∈ Set.range j.succAbove := by
      rw [Fin.range_succAbove]
      exact Set.mem_compl_singleton_iff.2 htj
    exact ⟨s, by rw [shuffle_objEquiv_δ_apply, hs, ht]⟩

/-- The image of the `j`-th face subcomplex under the
classifying map of `σ` is generated by the `j`-th face of
`σ` (compare `image_face_singleton_compl_prismTauMap`). -/
lemma shuffle_image_face_singleton_compl
    {σ : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋m + 1⦌} (j : Fin (m + 2)) :
    (stdSimplex.face {j}ᶜ).image (yonedaEquiv.symm σ) =
      Subcomplex.ofSimplex ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ j σ) := by
  rw [stdSimplex.face_singleton_compl, Subcomplex.image_ofSimplex,
    yonedaEquiv_symm_app_objEquiv_symm]
  rfl

end ShuffleGenericHelpers

/-!
## Combinatorics of the shuffles `τ_{a,b}`

Injectivity of the shuffle chains, the non-corner face
containment, the four diagonal face equalities between
adjacent shuffles (all from the threshold-shift lemmas
`shuffleSnd_succ/pred_left/right` of `ShuffleCobase.lean`),
and the classification of nondegenerate top simplices.
-/

section ShuffleTauApi

variable {n a b : ℕ}

/-- A first-coordinate value of `τ_{a,b}` at a non-corner
position occurs only there: if `shuffleFst a b u =
shuffleFst a b t` and `t ∉ {a, a+1, b+1, b+2}` then `u = t`. -/
lemma shuffleFst_inj_of_ne_corners (hab : a ≤ b) {t u : ℕ}
    (ht : t ≠ a ∧ t ≠ a + 1 ∧ t ≠ b + 1 ∧ t ≠ b + 2)
    (h : shuffleFst a b u = shuffleFst a b t) :
    u = t := by
  obtain ⟨hna, hna1, hnb1, hnb2⟩ := ht
  have hu := (shuffleFst_eq_iff hab (t := u)
    (v := shuffleFst a b t)).1 h
  have ht2 := (shuffleFst_eq_iff hab (t := t)
    (v := shuffleFst a b t)).1 rfl
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;>
    rcases ht2 with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2⟩ <;> omega

/-- The shuffle chain is injective: coordinate sums recover
the position (`shuffleFst_add_snd`). -/
lemma shuffleTau_objEquiv_injective (hab : a ≤ b) (hb : b ≤ n) :
    Function.Injective
      (prodStdSimplex.objEquiv (shuffleTau n a b hab hb)) := by
  intro s t h
  apply Fin.ext
  have hfst : shuffleFst a b s.val = shuffleFst a b t.val := by
    have h1 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.1.val) h
    rwa [shuffleTau_objEquiv_fst_val hab hb s,
      shuffleTau_objEquiv_fst_val hab hb t] at h1
  have hsnd : shuffleSnd a b s.val = shuffleSnd a b t.val := by
    have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.2.val) h
    rwa [shuffleTau_objEquiv_snd_val hab hb s,
      shuffleTau_objEquiv_snd_val hab hb t] at h2
  have hss := shuffleFst_add_snd a b s.val
  have htt := shuffleFst_add_snd a b t.val
  omega

/-- The classifying map of a shuffle is injective on
simplices, as required by `Subcomplex.isPushout_hornAttach`. -/
lemma shuffleTauMap_app_injective (hab : a ≤ b) (hb : b ≤ n)
    {d : ℕ} {s₁ s₂ : (Δ[n + 2] : SSet.{u}) _⦋d⦌}
    (h : (shuffleTauMap n a b hab hb).app _ s₁ =
      (shuffleTauMap n a b hab hb).app _ s₂) :
    s₁ = s₂ :=
  shuffle_map_injective_of_injective_objEquiv
    (shuffleTau_objEquiv_injective hab hb) h

/-- Omitting a non-corner vertex of `τ_{a,b}` deletes the
first coordinate at that position: the face lies in
`∂Δ[n] ⊗ Δ[2]`. -/
lemma shuffleTau_δ_ofSimplex_le_boundary_prod_top
    (hab : a ≤ b) (hb : b ≤ n) {j : Fin (n + 3)}
    (hj : j.val ≠ a ∧ j.val ≠ a + 1 ∧ j.val ≠ b + 1 ∧
      j.val ≠ b + 2) :
    Subcomplex.ofSimplex
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ j (shuffleTau n a b hab hb)) ≤
      (∂Δ[n]).prod ⊤ := by
  have hle : shuffleFst a b j.val ≤ n :=
    shuffleFst_le_of_le hab hb (by have h2 := j.isLt; omega)
  apply shuffle_ofSimplex_le_boundary_prod_top_of_fst_miss
    (v := ⟨shuffleFst a b j.val, by omega⟩)
  intro t htEq
  have hval : shuffleFst a b (j.succAbove t).val =
      shuffleFst a b j.val := by
    have h2 := congrArg Fin.val htEq
    rw [shuffle_objEquiv_δ_apply,
      shuffleTau_objEquiv_fst_val hab hb] at h2
    exact h2
  exact Fin.succAbove_ne j t
    (Fin.ext (shuffleFst_inj_of_ne_corners hab hj hval))

/-- Two shuffles whose height functions agree off the omitted
position have the same face there (first coordinates are
position minus height). -/
lemma shuffleTau_δ_eq_of_forall_snd_eq {a₁ b₁ a₂ b₂ : ℕ}
    (h₁ : a₁ ≤ b₁) (h₁' : b₁ ≤ n) (h₂ : a₂ ≤ b₂) (h₂' : b₂ ≤ n)
    {j : Fin (n + 3)}
    (hsnd : ∀ t : ℕ, t ≠ j.val →
      shuffleSnd a₂ b₂ t = shuffleSnd a₁ b₁ t) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j (shuffleTau n a₁ b₁ h₁ h₁') =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j (shuffleTau n a₂ b₂ h₂ h₂') := by
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [shuffle_objEquiv_δ_apply, shuffle_objEquiv_δ_apply]
  have hne : (j.succAbove t).val ≠ j.val :=
    fun e ↦ Fin.succAbove_ne j t (Fin.ext e)
  have hs := hsnd (j.succAbove t).val hne
  apply Prod.ext <;> apply Fin.ext
  · rw [shuffleTau_objEquiv_fst_val h₁ h₁',
      shuffleTau_objEquiv_fst_val h₂ h₂']
    have g1 := shuffleFst_add_snd a₁ b₁ (j.succAbove t).val
    have g2 := shuffleFst_add_snd a₂ b₂ (j.succAbove t).val
    omega
  · rw [shuffleTau_objEquiv_snd_val h₁ h₁',
      shuffleTau_objEquiv_snd_val h₂ h₂']
    exact hs.symm

/-- The `(a,1)`-face of `τ_{a,b}` equals the `(a+1,0)`-face
of `τ_{a+1,b}` (both omit position `a+1`). -/
lemma shuffleTau_δ_succ_left (hab : a < b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleTau n a b (le_of_lt hab) hb) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleTau n (a + 1) b hab hb) :=
  shuffleTau_δ_eq_of_forall_snd_eq (le_of_lt hab) hb hab hb
    (fun _t ht ↦ shuffleSnd_succ_left ht)

/-- The `(b,2)`-face of `τ_{a,b}` equals the `(b+1,1)`-face
of `τ_{a,b+1}` (both omit position `b+2`). -/
lemma shuffleTau_δ_succ_right (hab : a ≤ b) (hb : b < n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
        (shuffleTau n a b hab (le_of_lt hb)) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
        (shuffleTau n a (b + 1) (by omega) hb) :=
  shuffleTau_δ_eq_of_forall_snd_eq hab (le_of_lt hb) (by omega) hb
    (fun _t ht ↦ shuffleSnd_succ_right ht)

/-- The `(a,0)`-face of `τ_{a,b}` equals the `(a-1,1)`-face
of `τ_{a-1,b}` (both omit position `a`); the mirror sharing,
used for horn two. -/
lemma shuffleTau_δ_pred_left (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
        (shuffleTau n a b hab hb) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
        (shuffleTau n (a - 1) b (by omega) hb) :=
  shuffleTau_δ_eq_of_forall_snd_eq hab hb (by omega) hb
    (fun _t ht ↦ shuffleSnd_pred_left ha ht)

/-- The `(b,1)`-face of `τ_{a,b}` equals the `(b-1,2)`-face
of `τ_{a,b-1}` (both omit position `b+1`); the mirror
sharing, used for horn two. -/
lemma shuffleTau_δ_pred_right (hab : a < b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 1, by omega⟩
        (shuffleTau n a b (le_of_lt hab) hb) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 1, by omega⟩
        (shuffleTau n a (b - 1) (by omega) (by omega)) :=
  shuffleTau_δ_eq_of_forall_snd_eq (le_of_lt hab) hb (by omega)
    (by omega) (fun _t ht ↦ shuffleSnd_pred_right (by omega) ht)

end ShuffleTauApi

/-!
## Classification of the top simplices

Every nondegenerate `(n+2)`-simplex of `Δ[n] ⊗ Δ[2]` is a
shuffle: its coordinate sums are the positions, so its second
coordinate is a threshold function.
-/

section ShuffleClassification

variable {n : ℕ}

/-- **Classification of top simplices**: every nondegenerate
`(n+2)`-simplex of `Δ[n] ⊗ Δ[2]` is a shuffle `τ_{a,b}`. -/
lemma exists_shuffleTau_of_nonDegenerate
    {z : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋n + 2⦌}
    (hz : z ∈ (Δ[n] ⊗ Δ[2]).nonDegenerate (n + 2)) :
    ∃ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ n),
      shuffleTau n a b hab hb = z := by
  have hid : prodStdSimplex.orderHomOfSimplex z rfl = OrderHom.id :=
    (prodStdSimplex.nonDegenerate_max_dim_iff z).1 hz
  have hsum : ∀ t : Fin (n + 3),
      ((prodStdSimplex.objEquiv z t).1).val +
        ((prodStdSimplex.objEquiv z t).2).val = t.val := by
    intro t
    have h := DFunLike.congr_fun hid t
    simp only [prodStdSimplex.orderHomOfSimplex_coe,
      OrderHom.id_coe, id_eq] at h
    have hv := congrArg Fin.val h
    exact hv
  set s : Fin (n + 3) → ℕ :=
    fun t ↦ ((prodStdSimplex.objEquiv z t).2).val with hs
  have hs_apply : ∀ t,
      s t = ((prodStdSimplex.objEquiv z t).2).val :=
    fun t ↦ rfl
  have hsle : ∀ t, s t ≤ 2 := fun t ↦ by
    have h3 := (prodStdSimplex.objEquiv z t).2.isLt
    have hsa := hs_apply t
    omega
  have hmono : Monotone s := by
    intro x y hxy
    have hle := (prodStdSimplex.objEquiv z).monotone hxy
    exact hle.2
  have hs0 : s 0 = 0 := by
    have h := hsum 0
    have hsa := hs_apply 0
    have h0v : (0 : Fin (n + 3)).val = 0 := rfl
    omega
  have hlast : s (Fin.last (n + 2)) = 2 := by
    have h := hsum (Fin.last (n + 2))
    have hf := (prodStdSimplex.objEquiv z (Fin.last (n + 2))).1.isLt
    have h2 := hsle (Fin.last (n + 2))
    have hsa := hs_apply (Fin.last (n + 2))
    simp only [Fin.val_last] at h
    omega
  have hstep : ∀ t : Fin (n + 2), s t.succ ≤ s t.castSucc + 1 := by
    intro t
    have h1 := hsum t.succ
    have h2 := hsum t.castSucc
    have hf : ((prodStdSimplex.objEquiv z t.castSucc).1).val ≤
        ((prodStdSimplex.objEquiv z t.succ).1).val :=
      ((prodStdSimplex.objEquiv z).monotone
        t.castSucc_le_succ).1
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have hsa1 := hs_apply t.succ
    have hsa2 := hs_apply t.castSucc
    omega
  -- The first position of height `1`, resp. `2`.
  set T₁ : Finset (Fin (n + 3)) :=
    Finset.univ.filter (fun t ↦ s t ≠ 0) with hT₁
  have hne₁ : T₁.Nonempty := by
    refine ⟨Fin.last (n + 2), ?_⟩
    rw [hT₁, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hlast]; omega⟩
  have hmemT₁ : ∀ t : Fin (n + 3), t ∈ T₁ ↔ s t ≠ 0 := by
    intro t
    rw [hT₁, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  set t₁ : Fin (n + 3) := T₁.min' hne₁ with ht₁
  have ht₁mem : s t₁ ≠ 0 :=
    (hmemT₁ t₁).1 (Finset.min'_mem T₁ hne₁)
  have ht₁le : ∀ t : Fin (n + 3), s t ≠ 0 → t₁ ≤ t := by
    intro t ht
    apply Finset.min'_le
    rw [hT₁, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ht⟩
  have hs_t₁ : s t₁ = 1 := by
    rcases Fin.eq_zero_or_eq_succ t₁ with h0 | ⟨p, hp⟩
    · exact absurd (h0 ▸ hs0) ht₁mem
    · have hsp : s p.castSucc = 0 := by
        by_contra hne
        have hle := ht₁le p.castSucc hne
        rw [hp] at hle
        exact absurd hle (by
          rw [Fin.not_le]
          exact Fin.castSucc_lt_succ)
      have hst := hstep p
      rw [hsp, ← hp] at hst
      omega
  set T₂ : Finset (Fin (n + 3)) :=
    Finset.univ.filter (fun t ↦ s t = 2) with hT₂
  have hne₂ : T₂.Nonempty := by
    refine ⟨Fin.last (n + 2), ?_⟩
    rw [hT₂, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hlast⟩
  have hmemT₂ : ∀ t : Fin (n + 3), t ∈ T₂ ↔ s t = 2 := by
    intro t
    rw [hT₂, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  set t₂ : Fin (n + 3) := T₂.min' hne₂ with ht₂
  have ht₂mem : s t₂ = 2 :=
    (hmemT₂ t₂).1 (Finset.min'_mem T₂ hne₂)
  have ht₂le : ∀ t : Fin (n + 3), s t = 2 → t₂ ≤ t := by
    intro t ht
    apply Finset.min'_le
    rw [hT₂, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ht⟩
  set a : ℕ := ((prodStdSimplex.objEquiv z t₁).1).val with ha
  set b : ℕ := ((prodStdSimplex.objEquiv z t₂).1).val with hb
  have ha_eq : a + 1 = t₁.val := by
    have h := hsum t₁
    have hsa := hs_apply t₁
    omega
  have hb_eq : b + 2 = t₂.val := by
    have h := hsum t₂
    have hsa := hs_apply t₂
    omega
  have ht₁₂ : t₁ < t₂ := by
    have hle : t₁ ≤ t₂ := ht₁le t₂ (by rw [ht₂mem]; omega)
    refine hle.lt_of_ne (fun e ↦ by
      have h1 : s t₂ = 1 := e ▸ hs_t₁
      omega)
  have hab : a ≤ b := by
    have hv : t₁.val < t₂.val := ht₁₂
    omega
  have hbn : b ≤ n := by
    have hf := (prodStdSimplex.objEquiv z t₂).1.isLt
    omega
  have hsnd_eq : ∀ t : Fin (n + 3),
      s t = shuffleSnd a b t.val := by
    intro t
    by_cases h1 : t < t₁
    · have hst : s t = 0 := by
        by_contra hne
        exact absurd (ht₁le t hne) (by
          rw [Fin.not_le]
          exact h1)
      have hsh : shuffleSnd a b t.val = 0 :=
        shuffleSnd_eq_zero.2 (by
          have hv : t.val < t₁.val := h1
          omega)
      rw [hst, hsh]
    · by_cases h2 : t < t₂
      · have hst : s t = 1 := by
          have hge : 1 ≤ s t := by
            have hle : t₁ ≤ t := by
              rw [Fin.not_lt] at h1
              exact h1
            have hm := hmono hle
            omega
          have hne2 : s t ≠ 2 := by
            intro e
            exact absurd (ht₂le t e) (by
              rw [Fin.not_le]
              exact h2)
          have hle2 := hsle t
          omega
        have hsh : shuffleSnd a b t.val = 1 :=
          shuffleSnd_eq_one.2 ⟨by
            have hle : t₁ ≤ t := by
              rw [Fin.not_lt] at h1
              exact h1
            have hv : t₁.val ≤ t.val := hle
            omega, by
            have hv : t.val < t₂.val := h2
            omega⟩
        rw [hst, hsh]
      · have hst : s t = 2 := by
          have hle : t₂ ≤ t := by
            rw [Fin.not_lt] at h2
            exact h2
          have hm := hmono hle
          have hle2 := hsle t
          omega
        have hsh : shuffleSnd a b t.val = 2 :=
          (shuffleSnd_eq_two hab).2 (by
            have hle : t₂ ≤ t := by
              rw [Fin.not_lt] at h2
              exact h2
            have hv : t₂.val ≤ t.val := hle
            omega)
        rw [hst, hsh]
  refine ⟨a, b, hab, hbn, ?_⟩
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  apply Prod.ext <;> apply Fin.ext
  · rw [shuffleTau_objEquiv_fst_val hab hbn t]
    have h1 := hsum t
    have h2 := hsnd_eq t
    have h3 := shuffleFst_add_snd a b t.val
    have hsa := hs_apply t
    omega
  · rw [shuffleTau_objEquiv_snd_val hab hbn t]
    exact (hsnd_eq t).symm

/-- Values of the special edge `v₀` through `objEquiv`:
at position `t` it is `(0, t)`. -/
lemma shuffleVert0_objEquiv_apply (t : Fin 2) :
    prodStdSimplex.objEquiv.{u} (shuffleVert0 n) t =
      (0, ⟨t.val, by have h := t.isLt; omega⟩) := by
  fin_cases t <;> rfl

/-- Values of the special edge `v₂` through `objEquiv`:
at position `t` it is `(n, t+1)`. -/
lemma shuffleVert2_objEquiv_apply (t : Fin 2) :
    prodStdSimplex.objEquiv.{u} (shuffleVert2 n) t =
      (Fin.last n, ⟨t.val + 1, by have h := t.isLt; omega⟩) := by
  fin_cases t <;> rfl

/-- The `(0,1)`-edge of `Δ[n+2]` maps under `τ_{0,b}` to
`v₀`: at positions `0, 1` the shuffle takes values
`(0,0), (0,1)`. -/
lemma shuffleTauMap_zero_app_edge {b : ℕ} (hb : b ≤ n) :
    (shuffleTauMap.{u} n 0 b (Nat.zero_le b) hb).app _
        (stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      shuffleVert0 n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t).val = t.val := fun t ↦ by
    fin_cases t <;> rfl
  have h1 : stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩ (Fin.zero_le _) =
      stdSimplex.objEquiv.symm
        (stdSimplex.objEquiv
          (stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩
            (Fin.zero_le _))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, shuffleTauMap, yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply,
    shuffleVert0_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have hsndv : shuffleSnd 0 b t.val = t.val := by
    rcases ht with h0 | h0
    · rw [h0]
      exact shuffleSnd_eq_zero.2 (Nat.zero_le _)
    · rw [h0]
      exact shuffleSnd_eq_one.2 ⟨by omega, by omega⟩
  apply Prod.ext <;> apply Fin.ext
  · have h := shuffleTau_objEquiv_fst_val.{u} (n := n)
      (hab := Nat.zero_le b) (hb := hb)
      (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change shuffleFst 0 b t.val = 0
    have hsum := shuffleFst_add_snd 0 b t.val
    omega
  · have h := shuffleTau_objEquiv_snd_val.{u} (n := n)
      (hab := Nat.zero_le b) (hb := hb)
      (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h, hsndv]

/-- The last edge of `Δ[n+2]` maps under `τ_{a,n}` to `v₂`:
at positions `n+1, n+2` the shuffle takes values
`(n,1), (n,2)`. -/
lemma shuffleTauMap_last_app_edge {a : ℕ} (ha : a ≤ n) :
    (shuffleTauMap.{u} n a n ha (le_refl n)).app _
        (stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩
          ⟨n + 2, by omega⟩ (by simp [Fin.le_def])) =
      shuffleVert2 n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩
          ⟨n + 2, by omega⟩ (by simp [Fin.le_def]))).toOrderHom
          t).val = n + 1 + t.val := fun t ↦ by
    fin_cases t <;> rfl
  have h1 :
      stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩ ⟨n + 2, by omega⟩
          (by simp [Fin.le_def]) =
        stdSimplex.objEquiv.symm
          (stdSimplex.objEquiv
            (stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩
              ⟨n + 2, by omega⟩ (by simp [Fin.le_def]))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, shuffleTauMap, yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply,
    shuffleVert2_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have hsndv : shuffleSnd a n (n + 1 + t.val) = t.val + 1 := by
    rcases ht with h0 | h0
    · rw [h0]
      have h := shuffleSnd_eq_one (a := a) (b := n)
        (t := n + 1 + 0)
      have h' : shuffleSnd a n (n + 1 + 0) = 1 :=
        h.2 ⟨by omega, by omega⟩
      omega
    · rw [h0]
      have h := (shuffleSnd_eq_two (a := a) (b := n)
        (t := n + 1 + 1) ha).2 (by omega)
      omega
  apply Prod.ext <;> apply Fin.ext
  · have h := shuffleTau_objEquiv_fst_val.{u} (n := n)
      (hab := ha) (hb := le_refl n)
      (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩
          ⟨n + 2, by omega⟩ (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change shuffleFst a n (n + 1 + t.val) = n
    have hsum := shuffleFst_add_snd a n (n + 1 + t.val)
    omega
  · have h := shuffleTau_objEquiv_snd_val.{u} (n := n)
      (hab := ha) (hb := le_refl n)
      (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩
          ⟨n + 2, by omega⟩ (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h, hsndv]

end ShuffleClassification

/-!
## The diagonal simplices

`W_{a,b} = δ_{b+1} τ_{a,b}` (`shuffleDiagW`, horn zero) and
`W'_{a,b} = δ_{a+1} τ_{a,b}` (`shuffleDiagW'`, horn two), with
their coordinate functions: both have second coordinate
`shuffleDiagSnd a b` (`0` up to `a`, `1` up to `b`, then `2`);
the first coordinate of `W_{a,b}` is `s` up to `a` then `s-1`
(sole double value `a`), that of `W'_{a,b}` is `s` up to `b`
then `s-1` (sole double value `b`).
-/

section ShuffleDiagonals

variable {n a b : ℕ}

/-- Second coordinates of both diagonal simplices: `0` up to
position `a`, `1` up to position `b`, then `2`. -/
def shuffleDiagSnd (a b s : ℕ) : ℕ :=
  if s ≤ a then 0 else if s ≤ b then 1 else 2

/-- First coordinates of `W_{a,b}`: `s` up to position `a`,
then `s - 1`. -/
def shuffleDiagFst (a s : ℕ) : ℕ :=
  if s ≤ a then s else s - 1

/-- First coordinates of `W'_{a,b}`: `s` up to position `b`,
then `s - 1`. -/
def shuffleDiagFst' (b s : ℕ) : ℕ :=
  if s ≤ b then s else s - 1

lemma shuffleDiagSnd_eq_one {s : ℕ} :
    shuffleDiagSnd a b s = 1 ↔ a < s ∧ s ≤ b := by
  by_cases h1 : s ≤ a
  · have h0 : shuffleDiagSnd a b s = 0 := by
      unfold shuffleDiagSnd
      split_ifs
      omega
    rw [h0]
    constructor <;> intro h <;> omega
  · by_cases h2 : s ≤ b
    · have h1' : shuffleDiagSnd a b s = 1 := by
        unfold shuffleDiagSnd
        split_ifs
        omega
      rw [h1']
      constructor <;> intro h <;> omega
    · have h2' : shuffleDiagSnd a b s = 2 := by
        unfold shuffleDiagSnd
        split_ifs
        omega
      rw [h2']
      constructor <;> intro h <;> omega

lemma shuffleDiagFst_eq_iff {s v : ℕ} :
    shuffleDiagFst a s = v ↔
      (s = v ∧ v ≤ a) ∨ (s = v + 1 ∧ a ≤ v) := by
  unfold shuffleDiagFst
  split_ifs <;> omega

lemma shuffleDiagFst'_eq_iff {s v : ℕ} :
    shuffleDiagFst' b s = v ↔
      (s = v ∧ v ≤ b) ∨ (s = v + 1 ∧ b ≤ v) := by
  unfold shuffleDiagFst'
  split_ifs <;> omega

/-- A first-coordinate value of `W_{a,b}` at a position other
than `a, a+1` occurs only there. -/
lemma shuffleDiagFst_inj_of_ne {s u : ℕ}
    (hs : s ≠ a ∧ s ≠ a + 1)
    (h : shuffleDiagFst a u = shuffleDiagFst a s) :
    u = s := by
  obtain ⟨hna, hna1⟩ := hs
  have hu := (shuffleDiagFst_eq_iff (a := a) (s := u)
    (v := shuffleDiagFst a s)).1 h
  have hs2 := (shuffleDiagFst_eq_iff (a := a) (s := s)
    (v := shuffleDiagFst a s)).1 rfl
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hs2 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega

/-- A first-coordinate value of `W'_{a,b}` at a position other
than `b, b+1` occurs only there. -/
lemma shuffleDiagFst'_inj_of_ne {s u : ℕ}
    (hs : s ≠ b ∧ s ≠ b + 1)
    (h : shuffleDiagFst' b u = shuffleDiagFst' b s) :
    u = s := by
  obtain ⟨hnb, hnb1⟩ := hs
  have hu := (shuffleDiagFst'_eq_iff (b := b) (s := u)
    (v := shuffleDiagFst' b s)).1 h
  have hs2 := (shuffleDiagFst'_eq_iff (b := b) (s := s)
    (v := shuffleDiagFst' b s)).1 rfl
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hs2 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega

lemma shuffleDiagFst_add_snd {a b : ℕ} (hab : a ≤ b) (s : ℕ) :
    shuffleDiagFst a s + shuffleDiagSnd a b s =
      if s ≤ b then s else s + 1 := by
  unfold shuffleDiagFst shuffleDiagSnd
  split_ifs <;> omega

lemma shuffleDiagFst'_add_snd {a b : ℕ} (hab : a ≤ b) (s : ℕ) :
    shuffleDiagFst' b s + shuffleDiagSnd a b s =
      if s ≤ a then s else s + 1 := by
  unfold shuffleDiagFst' shuffleDiagSnd
  split_ifs <;> omega

/-- The horn-zero diagonal simplex `W_{a,b}`: `τ_{a,b}` with
the vertex `(b,1)` (position `b+1`) omitted. -/
noncomputable def shuffleDiagW (n a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋n + 1⦌ :=
  (Δ[n] ⊗ Δ[2]).δ ⟨b + 1, by omega⟩ (shuffleTau n a b hab hb)

/-- The map `Δ[n+1] ⟶ Δ[n] ⊗ Δ[2]` classifying `W_{a,b}`. -/
noncomputable abbrev shuffleDiagWMap (n a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ n) :
    Δ[n + 1] ⟶ (Δ[n] ⊗ Δ[2] : SSet.{u}) :=
  yonedaEquiv.symm (shuffleDiagW n a b hab hb)

/-- The horn-two diagonal simplex `W'_{a,b}`: `τ_{a,b}` with
the vertex `(a,1)` (position `a+1`) omitted. -/
noncomputable def shuffleDiagW' (n a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋n + 1⦌ :=
  (Δ[n] ⊗ Δ[2]).δ ⟨a + 1, by omega⟩ (shuffleTau n a b hab hb)

/-- The map `Δ[n+1] ⟶ Δ[n] ⊗ Δ[2]` classifying `W'_{a,b}`. -/
noncomputable abbrev shuffleDiagW'Map (n a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ n) :
    Δ[n + 1] ⟶ (Δ[n] ⊗ Δ[2] : SSet.{u}) :=
  yonedaEquiv.symm (shuffleDiagW' n a b hab hb)

lemma shuffleDiagW_objEquiv_snd_val (hab : a ≤ b) (hb : b ≤ n)
    (s : Fin (n + 2)) :
    ((prodStdSimplex.objEquiv (shuffleDiagW n a b hab hb) s).2).val =
      shuffleDiagSnd a b s.val := by
  unfold shuffleDiagW
  rw [shuffle_objEquiv_δ_apply, shuffleTau_objEquiv_snd_val hab hb,
    Fin.val_succAbove]
  change shuffleSnd a b (if s.val < b + 1 then s.val else s.val + 1) =
    shuffleDiagSnd a b s.val
  unfold shuffleSnd shuffleDiagSnd
  split_ifs <;> omega

lemma shuffleDiagW_objEquiv_fst_val (hab : a ≤ b) (hb : b ≤ n)
    (s : Fin (n + 2)) :
    ((prodStdSimplex.objEquiv (shuffleDiagW n a b hab hb) s).1).val =
      shuffleDiagFst a s.val := by
  unfold shuffleDiagW
  rw [shuffle_objEquiv_δ_apply, shuffleTau_objEquiv_fst_val hab hb,
    Fin.val_succAbove]
  change shuffleFst a b (if s.val < b + 1 then s.val else s.val + 1) =
    shuffleDiagFst a s.val
  unfold shuffleFst shuffleSnd shuffleDiagFst
  split_ifs <;> omega

lemma shuffleDiagW'_objEquiv_snd_val (hab : a ≤ b) (hb : b ≤ n)
    (s : Fin (n + 2)) :
    ((prodStdSimplex.objEquiv (shuffleDiagW' n a b hab hb) s).2).val =
      shuffleDiagSnd a b s.val := by
  unfold shuffleDiagW'
  rw [shuffle_objEquiv_δ_apply, shuffleTau_objEquiv_snd_val hab hb,
    Fin.val_succAbove]
  change shuffleSnd a b (if s.val < a + 1 then s.val else s.val + 1) =
    shuffleDiagSnd a b s.val
  unfold shuffleSnd shuffleDiagSnd
  split_ifs <;> omega

lemma shuffleDiagW'_objEquiv_fst_val (hab : a ≤ b) (hb : b ≤ n)
    (s : Fin (n + 2)) :
    ((prodStdSimplex.objEquiv (shuffleDiagW' n a b hab hb) s).1).val =
      shuffleDiagFst' b s.val := by
  unfold shuffleDiagW'
  rw [shuffle_objEquiv_δ_apply, shuffleTau_objEquiv_fst_val hab hb,
    Fin.val_succAbove]
  change shuffleFst a b (if s.val < a + 1 then s.val else s.val + 1) =
    shuffleDiagFst' b s.val
  unfold shuffleFst shuffleSnd shuffleDiagFst'
  split_ifs <;> omega

/-- The chain of `W_{a,b}` is injective (coordinate sums are
`s` up to `b` and `s+1` afterwards). -/
lemma shuffleDiagW_objEquiv_injective (hab : a ≤ b) (hb : b ≤ n) :
    Function.Injective
      (prodStdSimplex.objEquiv (shuffleDiagW n a b hab hb)) := by
  intro s t h
  apply Fin.ext
  have hfst : shuffleDiagFst a s.val = shuffleDiagFst a t.val := by
    have h1 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.1.val) h
    rwa [shuffleDiagW_objEquiv_fst_val hab hb s,
      shuffleDiagW_objEquiv_fst_val hab hb t] at h1
  have hsnd : shuffleDiagSnd a b s.val =
      shuffleDiagSnd a b t.val := by
    have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.2.val) h
    rwa [shuffleDiagW_objEquiv_snd_val hab hb s,
      shuffleDiagW_objEquiv_snd_val hab hb t] at h2
  have g1 := shuffleDiagFst_add_snd hab s.val
  have g2 := shuffleDiagFst_add_snd hab t.val
  by_cases hs : s.val ≤ b <;> by_cases ht : t.val ≤ b <;>
    simp only [hs, ht, ↓reduceIte] at g1 g2 <;> omega

/-- The chain of `W'_{a,b}` is injective. -/
lemma shuffleDiagW'_objEquiv_injective (hab : a ≤ b) (hb : b ≤ n) :
    Function.Injective
      (prodStdSimplex.objEquiv (shuffleDiagW' n a b hab hb)) := by
  intro s t h
  apply Fin.ext
  have hfst : shuffleDiagFst' b s.val =
      shuffleDiagFst' b t.val := by
    have h1 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.1.val) h
    rwa [shuffleDiagW'_objEquiv_fst_val hab hb s,
      shuffleDiagW'_objEquiv_fst_val hab hb t] at h1
  have hsnd : shuffleDiagSnd a b s.val =
      shuffleDiagSnd a b t.val := by
    have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.2.val) h
    rwa [shuffleDiagW'_objEquiv_snd_val hab hb s,
      shuffleDiagW'_objEquiv_snd_val hab hb t] at h2
  have g1 := shuffleDiagFst'_add_snd hab s.val
  have g2 := shuffleDiagFst'_add_snd hab t.val
  by_cases hs : s.val ≤ a <;> by_cases ht : t.val ≤ a <;>
    simp only [hs, ht, ↓reduceIte] at g1 g2 <;> omega

lemma shuffleDiagWMap_app_injective (hab : a ≤ b) (hb : b ≤ n)
    {d : ℕ} {s₁ s₂ : (Δ[n + 1] : SSet.{u}) _⦋d⦌}
    (h : (shuffleDiagWMap n a b hab hb).app _ s₁ =
      (shuffleDiagWMap n a b hab hb).app _ s₂) :
    s₁ = s₂ :=
  shuffle_map_injective_of_injective_objEquiv
    (shuffleDiagW_objEquiv_injective hab hb) h

lemma shuffleDiagW'Map_app_injective (hab : a ≤ b) (hb : b ≤ n)
    {d : ℕ} {s₁ s₂ : (Δ[n + 1] : SSet.{u}) _⦋d⦌}
    (h : (shuffleDiagW'Map n a b hab hb).app _ s₁ =
      (shuffleDiagW'Map n a b hab hb).app _ s₂) :
    s₁ = s₂ :=
  shuffle_map_injective_of_injective_objEquiv
    (shuffleDiagW'_objEquiv_injective hab hb) h

/-- The range of `W_{a,b}` is the range of `τ_{a,b}` minus
the omitted vertex at position `b+1`. -/
lemma shuffleDiagW_mem_range_iff (hab : a ≤ b) (hb : b ≤ n)
    {p : Fin (n + 1) × Fin 3} :
    p ∈ Set.range
        (prodStdSimplex.objEquiv.{u}
          (shuffleDiagW.{u} n a b hab hb)) ↔
      p ∈ Set.range
          (prodStdSimplex.objEquiv.{u}
            (shuffleTau.{u} n a b hab hb)) ∧
        p ≠ prodStdSimplex.objEquiv.{u} (shuffleTau.{u} n a b hab hb)
          ⟨b + 1, by omega⟩ := by
  unfold shuffleDiagW
  exact shuffle_mem_range_objEquiv_δ_iff
    (shuffleTau_objEquiv_injective hab hb) _

/-- The range of `W'_{a,b}` is the range of `τ_{a,b}` minus
the omitted vertex at position `a+1`. -/
lemma shuffleDiagW'_mem_range_iff (hab : a ≤ b) (hb : b ≤ n)
    {p : Fin (n + 1) × Fin 3} :
    p ∈ Set.range
        (prodStdSimplex.objEquiv.{u}
          (shuffleDiagW'.{u} n a b hab hb)) ↔
      p ∈ Set.range
          (prodStdSimplex.objEquiv.{u}
            (shuffleTau.{u} n a b hab hb)) ∧
        p ≠ prodStdSimplex.objEquiv.{u} (shuffleTau.{u} n a b hab hb)
          ⟨a + 1, by omega⟩ := by
  unfold shuffleDiagW'
  exact shuffle_mem_range_objEquiv_δ_iff
    (shuffleTau_objEquiv_injective hab hb) _

/-- Omitting a vertex of `W_{a,b}` other than `(a,0)` or
`(a,1)` deletes a first coordinate: the face lies in
`∂Δ[n] ⊗ Δ[2]`. -/
lemma shuffleDiagW_δ_ofSimplex_le_boundary_prod_top
    (hab : a ≤ b) (hb : b ≤ n) {j : Fin (n + 2)}
    (hj : j.val ≠ a ∧ j.val ≠ a + 1) :
    Subcomplex.ofSimplex
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
          (shuffleDiagW n a b hab hb)) ≤
      (∂Δ[n]).prod ⊤ := by
  have hle : shuffleDiagFst a j.val ≤ n := by
    have hj2 := j.isLt
    unfold shuffleDiagFst
    split_ifs <;> omega
  apply shuffle_ofSimplex_le_boundary_prod_top_of_fst_miss
    (v := ⟨shuffleDiagFst a j.val, by omega⟩)
  intro t htEq
  have hval : shuffleDiagFst a (j.succAbove t).val =
      shuffleDiagFst a j.val := by
    have h2 := congrArg Fin.val htEq
    rw [shuffle_objEquiv_δ_apply,
      shuffleDiagW_objEquiv_fst_val hab hb] at h2
    exact h2
  exact Fin.succAbove_ne j t
    (Fin.ext (shuffleDiagFst_inj_of_ne hj hval))

/-- Omitting a vertex of `W'_{a,b}` other than `(b,1)` or
`(b,2)` deletes a first coordinate. -/
lemma shuffleDiagW'_δ_ofSimplex_le_boundary_prod_top
    (hab : a ≤ b) (hb : b ≤ n) {j : Fin (n + 2)}
    (hj : j.val ≠ b ∧ j.val ≠ b + 1) :
    Subcomplex.ofSimplex
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
          (shuffleDiagW' n a b hab hb)) ≤
      (∂Δ[n]).prod ⊤ := by
  have hle : shuffleDiagFst' b j.val ≤ n := by
    have hj2 := j.isLt
    unfold shuffleDiagFst'
    split_ifs <;> omega
  apply shuffle_ofSimplex_le_boundary_prod_top_of_fst_miss
    (v := ⟨shuffleDiagFst' b j.val, by omega⟩)
  intro t htEq
  have hval : shuffleDiagFst' b (j.succAbove t).val =
      shuffleDiagFst' b j.val := by
    have h2 := congrArg Fin.val htEq
    rw [shuffle_objEquiv_δ_apply,
      shuffleDiagW'_objEquiv_fst_val hab hb] at h2
    exact h2
  exact Fin.succAbove_ne j t
    (Fin.ext (shuffleDiagFst'_inj_of_ne hj hval))

/-- The `(a,1)`-face of `W_{a,b}` equals the `(a+1,0)`-face
of `W_{a+1,b}` (both omit position `a+1`; the two diagonal
chains agree off that position). -/
lemma shuffleDiagW_δ_succ (hab : a + 1 < b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleDiagW n a b (by omega) hb) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
        (shuffleDiagW n (a + 1) b (le_of_lt hab) hb) := by
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [shuffle_objEquiv_δ_apply, shuffle_objEquiv_δ_apply]
  have hne : ((⟨a + 1, by omega⟩ : Fin (n + 2)).succAbove t).val ≠
      a + 1 :=
    fun e ↦ Fin.succAbove_ne _ t (Fin.ext e)
  apply Prod.ext <;> apply Fin.ext
  · rw [shuffleDiagW_objEquiv_fst_val (by omega) hb,
      shuffleDiagW_objEquiv_fst_val (le_of_lt hab) hb]
    unfold shuffleDiagFst
    split_ifs <;> omega
  · rw [shuffleDiagW_objEquiv_snd_val (by omega) hb,
      shuffleDiagW_objEquiv_snd_val (le_of_lt hab) hb]
    unfold shuffleDiagSnd
    split_ifs <;> omega

/-- The `(b,1)`-face of `W'_{a,b}` equals the `(b-1,2)`-face
of `W'_{a,b-1}` (both omit position `b`). -/
lemma shuffleDiagW'_δ_pred (hab : a + 1 < b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b, by omega⟩
        (shuffleDiagW' n a b (by omega) hb) =
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b, by omega⟩
        (shuffleDiagW' n a (b - 1) (by omega) (by omega)) := by
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [shuffle_objEquiv_δ_apply, shuffle_objEquiv_δ_apply]
  have hne : ((⟨b, by omega⟩ : Fin (n + 2)).succAbove t).val ≠ b :=
    fun e ↦ Fin.succAbove_ne _ t (Fin.ext e)
  apply Prod.ext <;> apply Fin.ext
  · rw [shuffleDiagW'_objEquiv_fst_val (by omega) hb,
      shuffleDiagW'_objEquiv_fst_val (by omega) (by omega)]
    unfold shuffleDiagFst'
    split_ifs <;> omega
  · rw [shuffleDiagW'_objEquiv_snd_val (by omega) hb,
      shuffleDiagW'_objEquiv_snd_val (by omega) (by omega)]
    unfold shuffleDiagSnd
    split_ifs <;> omega

/-- The `(0,1)`-edge of `Δ[n+1]` maps under `W_{0,b}` to
`v₀`. -/
lemma shuffleDiagWMap_zero_app_edge {b : ℕ} (hb0 : 0 < b)
    (hb : b ≤ n) :
    (shuffleDiagWMap.{u} n 0 b (Nat.zero_le b) hb).app _
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      shuffleVert0 n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t).val = t.val := fun t ↦ by
    fin_cases t <;> rfl
  have h1 : stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _) =
      stdSimplex.objEquiv.symm
        (stdSimplex.objEquiv
          (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
            (Fin.zero_le _))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, shuffleDiagWMap, yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply,
    shuffleVert0_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have ht1 : t.val ≤ 1 := by have h2 := t.isLt; omega
  apply Prod.ext <;> apply Fin.ext
  · have h := shuffleDiagW_objEquiv_fst_val.{u} (n := n)
      (hab := Nat.zero_le b) (hb := hb)
      (s := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change shuffleDiagFst 0 t.val = 0
    unfold shuffleDiagFst
    split_ifs <;> omega
  · have h := shuffleDiagW_objEquiv_snd_val.{u} (n := n)
      (hab := Nat.zero_le b) (hb := hb)
      (s := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change shuffleDiagSnd 0 b t.val = t.val
    unfold shuffleDiagSnd
    split_ifs <;> omega

/-- The last edge of `Δ[n+1]` maps under `W'_{a,n}` to `v₂`. -/
lemma shuffleDiagW'Map_last_app_edge {a : ℕ} (ha : a < n) :
    (shuffleDiagW'Map.{u} n a n (le_of_lt ha) (le_refl n)).app _
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ (by simp [Fin.le_def])) =
      shuffleVert2 n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ (by simp [Fin.le_def]))).toOrderHom
          t).val = n + t.val := fun t ↦ by
    fin_cases t <;> rfl
  have h1 :
      stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]) =
        stdSimplex.objEquiv.symm
          (stdSimplex.objEquiv
            (stdSimplex.edge (n + 1) ⟨n, by omega⟩
              ⟨n + 1, by omega⟩ (by simp [Fin.le_def]))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, shuffleDiagW'Map, yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply,
    shuffleVert2_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have ht1 : t.val ≤ 1 := by have h2 := t.isLt; omega
  apply Prod.ext <;> apply Fin.ext
  · have h := shuffleDiagW'_objEquiv_fst_val.{u} (n := n)
      (hab := le_of_lt ha) (hb := le_refl n)
      (s := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change shuffleDiagFst' n (n + t.val) = n
    unfold shuffleDiagFst'
    split_ifs <;> omega
  · have h := shuffleDiagW'_objEquiv_snd_val.{u} (n := n)
      (hab := le_of_lt ha) (hb := le_refl n)
      (s := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change shuffleDiagSnd a n (n + t.val) = t.val + 1
    unfold shuffleDiagSnd
    split_ifs <;> omega

end ShuffleDiagonals

/-!
## The lexicographic code and non-membership criteria

Pairs `(a, b)` with `b ≤ n` are ordered lexicographically by
the single code `a·(n+1)+b`, so each filtration below is
indexed by one natural number and attaches at most one
simplex per step. A simplex of `Δ[n] ⊗ Δ[2]` whose range has
surjective first coordinates and contains vertices of heights
`1, 2` (resp. `0, 1`) does not lie in `shuffleInit0` (resp.
`shuffleInit2`).
-/

section ShuffleCode

variable {n : ℕ}

/-- The lexicographic code of a shuffle index `(a, b)`. -/
def shuffleCode (n a b : ℕ) : ℕ :=
  a * (n + 1) + b

lemma shuffleCode_succ_left (n a b : ℕ) :
    shuffleCode n a b < shuffleCode n (a + 1) b := by
  unfold shuffleCode
  have h : (a + 1) * (n + 1) = a * (n + 1) + (n + 1) := by
    rw [add_mul, one_mul]
  omega

lemma shuffleCode_succ_right (n a b : ℕ) :
    shuffleCode n a (b + 1) = shuffleCode n a b + 1 := by
  unfold shuffleCode
  rw [Nat.add_assoc]

lemma shuffleCode_lt_of_fst_lt {a a' b b' : ℕ} (h : a < a')
    (hb : b ≤ n) :
    shuffleCode n a b < shuffleCode n a' b' := by
  unfold shuffleCode
  have h1 : a * (n + 1) + b ≤ a * (n + 1) + n :=
    Nat.add_le_add_left hb _
  have h2 : a * (n + 1) + n < (a + 1) * (n + 1) := by
    have e : (a + 1) * (n + 1) = a * (n + 1) + (n + 1) := by
      rw [add_mul, one_mul]
    omega
  have h3 : (a + 1) * (n + 1) ≤ a' * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) h
  have h4 : a' * (n + 1) ≤ a' * (n + 1) + b' := Nat.le_add_right _ _
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (le_trans h3 h4))

lemma shuffleCode_le_of_snd_le {a b b' : ℕ} (h : b ≤ b') :
    shuffleCode n a b ≤ shuffleCode n a b' :=
  Nat.add_le_add_left h _

/-- Codes reflect the lexicographic order on valid pairs. -/
lemma shuffleCode_lt_cases {a b a' b' : ℕ} (_hb : b ≤ n)
    (hb' : b' ≤ n)
    (h : shuffleCode n a b < shuffleCode n a' b') :
    a < a' ∨ (a = a' ∧ b < b') := by
  rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
  · exact Or.inl hlt
  · subst heq
    refine Or.inr ⟨rfl, ?_⟩
    by_contra hle
    exact not_lt_of_ge
      (shuffleCode_le_of_snd_le (Nat.le_of_not_gt hle)) h
  · exact absurd (shuffleCode_lt_of_fst_lt hgt hb') (not_lt_of_gt h)

lemma shuffleCode_inj {a b a' b' : ℕ} (hb : b ≤ n) (hb' : b' ≤ n)
    (h : shuffleCode n a b = shuffleCode n a' b') :
    a = a' ∧ b = b' := by
  rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
  · have hlt2 := shuffleCode_lt_of_fst_lt (n := n) (b' := b') hlt hb
    omega
  · subst heq
    refine ⟨rfl, ?_⟩
    have h2 : a * (n + 1) + b = a * (n + 1) + b' := h
    exact Nat.add_left_cancel h2
  · have hlt2 := shuffleCode_lt_of_fst_lt (n := n) (a := a')
      (a' := a) (b := b') (b' := b) hgt hb'
    omega

lemma shuffleCode_lt_bound {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    shuffleCode n a b < (n + 1) * (n + 1) := by
  have h1 : shuffleCode n a b ≤ n * (n + 1) + n := by
    unfold shuffleCode
    exact Nat.add_le_add
      (Nat.mul_le_mul_right (n + 1) (le_trans hab hb)) hb
  have e : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := by
    rw [add_mul, one_mul]
  omega

end ShuffleCode

section ShuffleNotMemInitial

variable {n m : ℕ} {z : (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋m⦌}

/-- A simplex with surjective first coordinates and vertices
of heights `1` and `2` does not lie in `shuffleInit0`. -/
lemma shuffle_notMem_shuffleInit0_of_range
    (hfst : ∀ v : Fin (n + 1), ∃ h : Fin 3,
      (v, h) ∈ Set.range (prodStdSimplex.objEquiv z))
    (h1 : ∃ v : Fin (n + 1),
      (v, (1 : Fin 3)) ∈ Set.range (prodStdSimplex.objEquiv z))
    (h2 : ∃ v : Fin (n + 1),
      (v, (2 : Fin 3)) ∈ Set.range (prodStdSimplex.objEquiv z)) :
    z ∉ (shuffleInit0 n).obj _ := by
  intro hmem
  have hmem2 := (Subcomplex.mem_unionProd_iff _ _ _).1 hmem
  rcases hmem2 with hsnd | hfstmem
  · obtain ⟨w, hw, hwrange⟩ :=
      (mem_horn_iff_notMem_range _ _).1 hsnd
    have hw01 : w = (1 : Fin 3) ∨ w = (2 : Fin 3) := by
      have h3 := w.isLt
      have hne : w.val ≠ 0 := fun e ↦ hw (Fin.ext e)
      have hv : w.val = 1 ∨ w.val = 2 := by omega
      rcases hv with e | e
      · exact Or.inl (Fin.ext e)
      · exact Or.inr (Fin.ext e)
    rcases hw01 with rfl | rfl
    · obtain ⟨v, t, ht⟩ := h1
      exact hwrange ⟨t, congrArg Prod.snd ht⟩
    · obtain ⟨v, t, ht⟩ := h2
      exact hwrange ⟨t, congrArg Prod.snd ht⟩
  · obtain ⟨v, hvrange⟩ :=
      (mem_boundary_iff_notMem_range _).1 hfstmem
    obtain ⟨h, t, ht⟩ := hfst v
    exact hvrange ⟨t, congrArg Prod.fst ht⟩

/-- A simplex with surjective first coordinates and vertices
of heights `0` and `1` does not lie in `shuffleInit2`. -/
lemma shuffle_notMem_shuffleInit2_of_range
    (hfst : ∀ v : Fin (n + 1), ∃ h : Fin 3,
      (v, h) ∈ Set.range (prodStdSimplex.objEquiv z))
    (h0 : ∃ v : Fin (n + 1),
      (v, (0 : Fin 3)) ∈ Set.range (prodStdSimplex.objEquiv z))
    (h1 : ∃ v : Fin (n + 1),
      (v, (1 : Fin 3)) ∈ Set.range (prodStdSimplex.objEquiv z)) :
    z ∉ (shuffleInit2 n).obj _ := by
  intro hmem
  have hmem2 := (Subcomplex.mem_unionProd_iff _ _ _).1 hmem
  rcases hmem2 with hsnd | hfstmem
  · obtain ⟨w, hw, hwrange⟩ :=
      (mem_horn_iff_notMem_range _ _).1 hsnd
    have hw01 : w = (0 : Fin 3) ∨ w = (1 : Fin 3) := by
      have h3 := w.isLt
      have hne : w.val ≠ 2 := fun e ↦ hw (Fin.ext e)
      have hv : w.val = 0 ∨ w.val = 1 := by omega
      rcases hv with e | e
      · exact Or.inl (Fin.ext e)
      · exact Or.inr (Fin.ext e)
    rcases hw01 with rfl | rfl
    · obtain ⟨v, t, ht⟩ := h0
      exact hwrange ⟨t, congrArg Prod.snd ht⟩
    · obtain ⟨v, t, ht⟩ := h1
      exact hwrange ⟨t, congrArg Prod.snd ht⟩
  · obtain ⟨v, hvrange⟩ :=
      (mem_boundary_iff_notMem_range _).1 hfstmem
    obtain ⟨h, t, ht⟩ := hfst v
    exact hvrange ⟨t, congrArg Prod.fst ht⟩

end ShuffleNotMemInitial

/-!
## The horn-zero diagonal filtration

`shuffleDiagFilt0 n m` is `shuffleInit0 n` together with the
diagonals `W_{a,b}` of code `≥ m` (decreasing order).
-/

section ShuffleDiagFilt0

variable {n : ℕ}

/-- The decreasing diagonal filtration for horn zero:
`S₀` together with `W_{a,b}` for `code(a,b) ≥ m`. -/
noncomputable def shuffleDiagFilt0 (n m : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex :=
  shuffleInit0 n ⊔ ⨆ (a : ℕ) (b : ℕ) (hab : a < b) (hb : b ≤ n)
    (_ : m ≤ shuffleCode n a b),
    Subcomplex.ofSimplex (shuffleDiagW n a b (le_of_lt hab) hb)

lemma shuffleInit0_le_shuffleDiagFilt0 (m : ℕ) :
    shuffleInit0 n ≤ shuffleDiagFilt0 n m :=
  le_sup_left

lemma ofSimplex_shuffleDiagW_le_shuffleDiagFilt0 {m a b : ℕ}
    (hab : a < b) (hb : b ≤ n) (h : m ≤ shuffleCode n a b) :
    Subcomplex.ofSimplex (shuffleDiagW n a b (le_of_lt hab) hb) ≤
      shuffleDiagFilt0 n m := by
  unfold shuffleDiagFilt0
  refine (le_iSup_of_le a ?_).trans le_sup_right
  exact le_iSup_of_le b (le_iSup_of_le hab
    (le_iSup_of_le hb (le_iSup_of_le h le_rfl)))

lemma shuffleDiagFilt0_succ_le (m : ℕ) :
    shuffleDiagFilt0 n (m + 1) ≤ shuffleDiagFilt0 n m := by
  unfold shuffleDiagFilt0
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro h
  exact ofSimplex_shuffleDiagW_le_shuffleDiagFilt0 hab hb
    (Nat.le_trans (Nat.le_succ m) h)

/-- One diagonal filtration step at a valid code. -/
lemma shuffleDiagFilt0_eq_succ_sup {a b : ℕ} (hab : a < b)
    (hb : b ≤ n) :
    shuffleDiagFilt0 n (shuffleCode n a b) =
      shuffleDiagFilt0 n (shuffleCode n a b + 1) ⊔
        Subcomplex.ofSimplex
          (shuffleDiagW n a b (le_of_lt hab) hb) := by
  apply le_antisymm
  · unfold shuffleDiagFilt0
    apply sup_le (le_sup_left.trans le_sup_left)
    apply iSup_le
    intro a'
    apply iSup_le
    intro b'
    apply iSup_le
    intro hab'
    apply iSup_le
    intro hb'
    apply iSup_le
    intro hcode
    by_cases hcc : shuffleCode n a' b' = shuffleCode n a b
    · obtain ⟨rfl, rfl⟩ := shuffleCode_inj hb' hb hcc
      exact le_sup_right
    · have hgt : shuffleCode n a b + 1 ≤ shuffleCode n a' b' := by
        omega
      refine (le_iSup_of_le a' ?_).trans
        (le_sup_right.trans le_sup_left)
      exact le_iSup_of_le b' (le_iSup_of_le hab'
        (le_iSup_of_le hb' (le_iSup_of_le hgt le_rfl)))
  · exact sup_le (shuffleDiagFilt0_succ_le _)
      (ofSimplex_shuffleDiagW_le_shuffleDiagFilt0 hab hb le_rfl)

/-- Invalid codes are skipped by the diagonal filtration. -/
lemma shuffleDiagFilt0_eq_succ_of_not_valid {m : ℕ}
    (h : ∀ a b : ℕ, a < b → b ≤ n → shuffleCode n a b ≠ m) :
    shuffleDiagFilt0 n m = shuffleDiagFilt0 n (m + 1) := by
  apply le_antisymm _ (shuffleDiagFilt0_succ_le m)
  unfold shuffleDiagFilt0
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  have hgt : m + 1 ≤ shuffleCode n a b := by
    have hne := h a b hab hb
    omega
  exact ofSimplex_shuffleDiagW_le_shuffleDiagFilt0 hab hb hgt

/-- The top of the diagonal filtration is `S₀`. -/
lemma shuffleDiagFilt0_top :
    shuffleDiagFilt0 n ((n + 1) * (n + 1)) = shuffleInit0 n := by
  refine le_antisymm ?_ le_sup_left
  unfold shuffleDiagFilt0
  refine sup_le le_rfl ?_
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  exfalso
  have hlt := shuffleCode_lt_bound (le_of_lt hab) hb
  omega

end ShuffleDiagFilt0

/-!
## Corner values and pair-distinguishing helpers

The values of `shuffleFst`/`shuffleSnd` at the four corner
positions, and criteria for an explicit vertex `(v, h)` to
differ from a vertex of a shuffle or diagonal, by a
coordinate-value mismatch.
-/

section ShuffleCornerValues

variable {n a b : ℕ}

lemma shuffleSnd_at_a : shuffleSnd a b a = 0 :=
  shuffleSnd_eq_zero.2 (le_refl a)

lemma shuffleFst_at_a : shuffleFst a b a = a := by
  have h := shuffleFst_add_snd a b a
  rw [shuffleSnd_at_a] at h
  omega

lemma shuffleSnd_at_succ_a (hab : a ≤ b) :
    shuffleSnd a b (a + 1) = 1 :=
  shuffleSnd_eq_one.2 ⟨by omega, by omega⟩

lemma shuffleFst_at_succ_a (hab : a ≤ b) :
    shuffleFst a b (a + 1) = a := by
  have h := shuffleFst_add_snd a b (a + 1)
  rw [shuffleSnd_at_succ_a hab] at h
  omega

lemma shuffleSnd_at_succ_b (hab : a ≤ b) :
    shuffleSnd a b (b + 1) = 1 :=
  shuffleSnd_eq_one.2 ⟨by omega, by omega⟩

lemma shuffleFst_at_succ_b (hab : a ≤ b) :
    shuffleFst a b (b + 1) = b := by
  have h := shuffleFst_add_snd a b (b + 1)
  rw [shuffleSnd_at_succ_b hab] at h
  omega

lemma shuffleSnd_at_b_add_two (hab : a ≤ b) :
    shuffleSnd a b (b + 2) = 2 :=
  (shuffleSnd_eq_two hab).2 (by omega)

lemma shuffleFst_at_b_add_two (hab : a ≤ b) :
    shuffleFst a b (b + 2) = b := by
  have h := shuffleFst_add_snd a b (b + 2)
  rw [shuffleSnd_at_b_add_two hab] at h
  omega

lemma shuffleDiagSnd_at_a : shuffleDiagSnd a b a = 0 := by
  unfold shuffleDiagSnd
  split_ifs <;> omega

lemma shuffleDiagSnd_at_b_add_one (hab : a ≤ b) :
    shuffleDiagSnd a b (b + 1) = 2 := by
  unfold shuffleDiagSnd
  split_ifs <;> omega

lemma shuffleDiagFst_at_a : shuffleDiagFst a a = a := by
  unfold shuffleDiagFst
  split_ifs <;> omega

lemma shuffleDiagFst'_at_b : shuffleDiagFst' b b = b := by
  unfold shuffleDiagFst'
  split_ifs <;> omega

/-- An explicit vertex differs from a shuffle vertex when
their second-coordinate values differ. -/
lemma shuffle_pair_ne_tau_of_snd_ne (hab : a ≤ b) (hb : b ≤ n)
    {v : Fin (n + 1)} {h : Fin 3} {t : Fin (n + 3)}
    (hne : shuffleSnd a b t.val ≠ h.val) :
    (v, h) ≠ prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t := by
  intro e
  have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.2.val) e
  rw [shuffleTau_objEquiv_snd_val hab hb] at h2
  exact hne h2.symm

/-- An explicit vertex differs from a shuffle vertex when
their first-coordinate values differ. -/
lemma shuffle_pair_ne_tau_of_fst_ne (hab : a ≤ b) (hb : b ≤ n)
    {v : Fin (n + 1)} {h : Fin 3} {t : Fin (n + 3)}
    (hne : shuffleFst a b t.val ≠ v.val) :
    (v, h) ≠ prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t := by
  intro e
  have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.1.val) e
  rw [shuffleTau_objEquiv_fst_val hab hb] at h2
  exact hne h2.symm

lemma shuffle_pair_ne_diagW_of_snd_ne (hab : a ≤ b) (hb : b ≤ n)
    {v : Fin (n + 1)} {h : Fin 3} {t : Fin (n + 2)}
    (hne : shuffleDiagSnd a b t.val ≠ h.val) :
    (v, h) ≠
      prodStdSimplex.objEquiv (shuffleDiagW n a b hab hb) t := by
  intro e
  have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.2.val) e
  rw [shuffleDiagW_objEquiv_snd_val hab hb] at h2
  exact hne h2.symm

lemma shuffle_pair_ne_diagW_of_fst_ne (hab : a ≤ b) (hb : b ≤ n)
    {v : Fin (n + 1)} {h : Fin 3} {t : Fin (n + 2)}
    (hne : shuffleDiagFst a t.val ≠ v.val) :
    (v, h) ≠
      prodStdSimplex.objEquiv (shuffleDiagW n a b hab hb) t := by
  intro e
  have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.1.val) e
  rw [shuffleDiagW_objEquiv_fst_val hab hb] at h2
  exact hne h2.symm

lemma shuffle_pair_ne_diagW'_of_snd_ne (hab : a ≤ b) (hb : b ≤ n)
    {v : Fin (n + 1)} {h : Fin 3} {t : Fin (n + 2)}
    (hne : shuffleDiagSnd a b t.val ≠ h.val) :
    (v, h) ≠
      prodStdSimplex.objEquiv (shuffleDiagW' n a b hab hb) t := by
  intro e
  have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.2.val) e
  rw [shuffleDiagW'_objEquiv_snd_val hab hb] at h2
  exact hne h2.symm

lemma shuffle_pair_ne_diagW'_of_fst_ne (hab : a ≤ b) (hb : b ≤ n)
    {v : Fin (n + 1)} {h : Fin 3} {t : Fin (n + 2)}
    (hne : shuffleDiagFst' b t.val ≠ v.val) :
    (v, h) ≠
      prodStdSimplex.objEquiv (shuffleDiagW' n a b hab hb) t := by
  intro e
  have h2 := congrArg (fun p : Fin (n + 1) × Fin 3 ↦ p.1.val) e
  rw [shuffleDiagW'_objEquiv_fst_val hab hb] at h2
  exact hne h2.symm

end ShuffleCornerValues

/-!
## The attaching horn for the diagonal phase (horn zero)

The preimage of the stage before `W_{a,b}` under its
classifying map is `Λ[n+1, a]`: every face except the one
omitting `(a,0)` lies in `S₀` or in `W_{a+1,b}`, and that
face lies in neither `S₀` nor any earlier diagonal.
-/

section ShuffleDiagPreimage0

variable {n a b : ℕ}

/-- **Attaching horn, diagonal phase, horn zero**: the
preimage of `shuffleDiagFilt0 n (code(a,b)+1)` under
`W_{a,b}` is `Λ[n+1, a]`. -/
lemma shuffleDiagFilt0_preimage_shuffleDiagWMap (hab : a < b)
    (hb : b ≤ n) :
    (shuffleDiagFilt0 n (shuffleCode n a b + 1)).preimage
        (shuffleDiagWMap.{u} n a b (le_of_lt hab) hb) =
      (Λ[n + 1, ⟨a, by omega⟩] :
        (Δ[n + 1] : SSet.{u}).Subcomplex) := by
  have hab₀ : a ≤ b := le_of_lt hab
  -- The two range witnesses in the missing face.
  have hA1 : (⟨a, by omega⟩, (1 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleDiagW.{u} n a b hab₀ hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleDiagW_objEquiv_injective.{u} hab₀ hb)
      ⟨a, by omega⟩).2 ⟨?_, ?_⟩
    · refine (shuffleDiagW_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
      · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
          (Or.inr (Or.inl ⟨rfl, le_rfl, hab₀⟩))
      · exact shuffle_pair_ne_tau_of_fst_ne.{u} hab₀ hb (by
          change shuffleFst a b (b + 1) ≠ a
          rw [shuffleFst_at_succ_b hab₀]
          omega)
    · exact shuffle_pair_ne_diagW_of_snd_ne.{u} hab₀ hb (by
        change shuffleDiagSnd a b a ≠ 1
        rw [shuffleDiagSnd_at_a]
        omega)
  have hB2 : (⟨b, by omega⟩, (2 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleDiagW.{u} n a b hab₀ hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleDiagW_objEquiv_injective.{u} hab₀ hb)
      ⟨a, by omega⟩).2 ⟨?_, ?_⟩
    · refine (shuffleDiagW_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
      · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
          (Or.inr (Or.inr ⟨rfl, le_rfl⟩))
      · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab₀ hb (by
          change shuffleSnd a b (b + 1) ≠ 2
          rw [shuffleSnd_at_succ_b hab₀]
          omega)
    · exact shuffle_pair_ne_diagW_of_snd_ne.{u} hab₀ hb (by
        change shuffleDiagSnd a b a ≠ 2
        rw [shuffleDiagSnd_at_a]
        omega)
  -- The missing face is not in `S₀`.
  have hmissInit :
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleDiagW n a b hab₀ hb) ∉
        (shuffleInit0 n).obj _ := by
    refine shuffle_notMem_shuffleInit0_of_range ?_
      ⟨⟨a, by omega⟩, hA1⟩ ⟨⟨b, by omega⟩, hB2⟩
    intro v
    by_cases hv1 : v.val < a
    · refine ⟨(0 : Fin 3), ?_⟩
      refine (shuffle_mem_range_objEquiv_δ_iff.{u}
        (shuffleDiagW_objEquiv_injective.{u} hab₀ hb)
        ⟨a, by omega⟩).2 ⟨?_, ?_⟩
      · refine (shuffleDiagW_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
        · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
            (Or.inl ⟨rfl, Nat.le_of_lt hv1⟩)
        · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab₀ hb (by
            change shuffleSnd a b (b + 1) ≠ 0
            rw [shuffleSnd_at_succ_b hab₀]
            omega)
      · exact shuffle_pair_ne_diagW_of_fst_ne.{u} hab₀ hb (by
          change shuffleDiagFst a a ≠ v.val
          rw [shuffleDiagFst_at_a]
          omega)
    · by_cases hv2 : v.val < b
      · refine ⟨(1 : Fin 3), ?_⟩
        refine (shuffle_mem_range_objEquiv_δ_iff.{u}
          (shuffleDiagW_objEquiv_injective.{u} hab₀ hb)
          ⟨a, by omega⟩).2 ⟨?_, ?_⟩
        · refine (shuffleDiagW_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
          · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
              (Or.inr (Or.inl
                ⟨rfl, Nat.le_of_not_gt hv1, Nat.le_of_lt hv2⟩))
          · exact shuffle_pair_ne_tau_of_fst_ne.{u} hab₀ hb (by
              change shuffleFst a b (b + 1) ≠ v.val
              rw [shuffleFst_at_succ_b hab₀]
              omega)
        · exact shuffle_pair_ne_diagW_of_snd_ne.{u} hab₀ hb (by
            change shuffleDiagSnd a b a ≠ 1
            rw [shuffleDiagSnd_at_a]
            omega)
      · refine ⟨(2 : Fin 3), ?_⟩
        refine (shuffle_mem_range_objEquiv_δ_iff.{u}
          (shuffleDiagW_objEquiv_injective.{u} hab₀ hb)
          ⟨a, by omega⟩).2 ⟨?_, ?_⟩
        · refine (shuffleDiagW_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
          · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
              (Or.inr (Or.inr ⟨rfl, Nat.le_of_not_gt hv2⟩))
          · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab₀ hb (by
              change shuffleSnd a b (b + 1) ≠ 2
              rw [shuffleSnd_at_succ_b hab₀]
              omega)
        · exact shuffle_pair_ne_diagW_of_snd_ne.{u} hab₀ hb (by
            change shuffleDiagSnd a b a ≠ 2
            rw [shuffleDiagSnd_at_a]
            omega)
  apply le_antisymm
  · rw [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl,
      Subcomplex.ofSimplex_le_iff]
    intro hmem
    unfold shuffleDiagFilt0 at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · exact hmissInit h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨a', b', hab', hb', hcode, hmem'⟩ := hI
      have hlt : shuffleCode n a b < shuffleCode n a' b' := hcode
      have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
            ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
              (shuffleDiagW.{u} n a b hab₀ hb))) ⊆
          Set.range (prodStdSimplex.objEquiv.{u}
            (shuffleDiagW.{u} n a' b' (le_of_lt hab') hb')) :=
        (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
          ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
      rcases shuffleCode_lt_cases hb hb' hlt with hgt | ⟨rfl, hgt⟩
      · have hnot : (⟨a, by omega⟩, (1 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleDiagW.{u} n a' b' (le_of_lt hab') hb')) := by
          intro hmem''
          have hτ : (⟨a, by omega⟩, (1 : Fin 3)) ∈ Set.range
                (prodStdSimplex.objEquiv.{u}
                  (shuffleTau.{u} n a' b' (le_of_lt hab') hb')) :=
            ((shuffleDiagW_mem_range_iff.{u} (le_of_lt hab') hb').1
              hmem'').1
          rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
            at hτ
          rcases hτ with ⟨hbad, -⟩ | ⟨-, hbad, -⟩ | ⟨hbad, -⟩
          · exact (by decide : ¬ ((1 : Fin 3)).val = 0) hbad
          · change a' ≤ a at hbad
            omega
          · exact (by decide : ¬ ((1 : Fin 3)).val = 2) hbad
        exact hnot (hle2 hA1)
      · have hnot : (⟨b, by omega⟩, (2 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleDiagW.{u} n a b' (le_of_lt hab') hb')) := by
          intro hmem''
          have hτ : (⟨b, by omega⟩, (2 : Fin 3)) ∈ Set.range
                (prodStdSimplex.objEquiv.{u}
                  (shuffleTau.{u} n a b' (le_of_lt hab') hb')) :=
            ((shuffleDiagW_mem_range_iff.{u} (le_of_lt hab') hb').1
              hmem'').1
          rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
            at hτ
          rcases hτ with ⟨hbad, -⟩ | ⟨hbad, -, -⟩ | ⟨-, hbad⟩
          · exact (by decide : ¬ ((2 : Fin 3)).val = 0) hbad
          · exact (by decide : ¬ ((2 : Fin 3)).val = 1) hbad
          · change b' ≤ b at hbad
            omega
        exact hnot (hle2 hB2)
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    have hjval : j.val ≠ a := by
      have hne : j ≠ ⟨a, by omega⟩ :=
        Set.mem_compl_singleton_iff.1 hj
      exact fun e ↦ hne (Fin.ext e)
    rw [← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl]
    by_cases hj1 : j.val = a + 1
    · by_cases hba : b = a + 1
      · refine (shuffle_ofSimplex_le_top_prod_horn_of_snd_miss
            (i := (0 : Fin 3)) (w := (1 : Fin 3)) (by decide)
            ?_).trans
          ((Subcomplex.top_prod_le_unionProd _ _).trans
            (shuffleInit0_le_shuffleDiagFilt0 _))
        intro t htEq
        have hval : shuffleDiagSnd a b (j.succAbove t).val = 1 := by
          have h2 := congrArg Fin.val htEq
          rw [shuffle_objEquiv_δ_apply,
            shuffleDiagW_objEquiv_snd_val hab₀ hb] at h2
          exact h2
        have hu := shuffleDiagSnd_eq_one.1 hval
        have hne : (j.succAbove t).val ≠ a + 1 := by
          rw [← hj1]
          exact fun e ↦ Fin.succAbove_ne j t (Fin.ext e)
        omega
      · have hab1 : a + 1 < b := by omega
        have hmem2 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
              (shuffleDiagW n a b hab₀ hb) ∈
            (Subcomplex.ofSimplex
              (shuffleDiagW n (a + 1) b (le_of_lt hab1) hb)).obj _ := by
          have h1 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
                (shuffleDiagW n (a + 1) b (le_of_lt hab1) hb) ∈
              (Subcomplex.ofSimplex
                (shuffleDiagW n (a + 1) b (le_of_lt hab1) hb)).obj _ :=
            (Subcomplex.ofSimplex _).map _
              (Subcomplex.mem_ofSimplex_obj _)
          have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                (shuffleDiagW n a b hab₀ hb) =
              (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
                (shuffleDiagW n (a + 1) b (le_of_lt hab1) hb) := by
            have hjj : j = ⟨a + 1, lt_trans
                  (Nat.succ_lt_succ (lt_of_lt_of_le hab hb))
                  (Nat.lt_succ_self _)⟩ := Fin.ext hj1
            subst hjj
            exact shuffleDiagW_δ_succ hab1 hb
          exact hEq.symm ▸ h1
        exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem2).trans
          (ofSimplex_shuffleDiagW_le_shuffleDiagFilt0 hab1 hb
            (shuffleCode_succ_left n a b))
    · exact (shuffleDiagW_δ_ofSimplex_le_boundary_prod_top
          hab₀ hb ⟨hjval, hj1⟩).trans
        ((Subcomplex.prod_top_le_unionProd _ _).trans
          (shuffleInit0_le_shuffleDiagFilt0 _))

end ShuffleDiagPreimage0

/-!
## Extension over the diagonal stage (horn zero)

The special edge of the `a = 0` diagonal attaching horns is
`v₀`; downward induction over the code then extends a map out
of `S₀` over all diagonals.
-/

section ShuffleDiagExtension0

variable {n : ℕ} {C : SSet.{u}}

lemma shuffleVert0_mem_shuffleDiagFilt0 (m : ℕ) :
    shuffleVert0 n ∈ (shuffleDiagFilt0 n m).obj _ :=
  (shuffleInit0_le_shuffleDiagFilt0 m) _
    (shuffleVert0_mem_shuffleInit0 n)

/-- The horn lift for `W_{0,b}` sends the `(0,1)`-edge
simplex of `Λ[m+2, 0]` to `v₀`. -/
lemma shuffleDiagHornLift_app_leftHornEdgeSimplex (m b : ℕ)
    (hb0 : 0 < b) (hb : b ≤ m + 1) :
    (Subcomplex.hornLift
        (shuffleDiagFilt0 (m + 1) (shuffleCode (m + 1) 0 b + 1))
        (shuffleDiagW (m + 1) 0 b (le_of_lt hb0) hb)
        (⟨0, by omega⟩ : Fin (m + 3))
        (shuffleDiagFilt0_preimage_shuffleDiagWMap hb0 hb)).app _
        (leftHornEdgeSimplex.{u} m) =
      ⟨shuffleVert0 (m + 1), shuffleVert0_mem_shuffleDiagFilt0 _⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift
          (shuffleDiagFilt0 (m + 1) (shuffleCode (m + 1) 0 b + 1))
          (shuffleDiagW (m + 1) 0 b (le_of_lt hb0) hb)
          (⟨0, by omega⟩ : Fin (m + 3))
          (shuffleDiagFilt0_preimage_shuffleDiagWMap hb0 hb)).app _
          (leftHornEdgeSimplex.{u} m)).val
      = (shuffleDiagWMap.{u} (m + 1) 0 b (Nat.zero_le b) hb).app _
          (stdSimplex.edge (m + 2) 0 ⟨1, by omega⟩
            (Fin.zero_le _)) :=
        congr($(Subcomplex.hornLift_ι
          (shuffleDiagFilt0_preimage_shuffleDiagWMap hb0 hb)).app _
            (leftHornEdgeSimplex.{u} m))
    _ = shuffleVert0 (m + 1) :=
        shuffleDiagWMap_zero_app_edge hb0 hb

/-- The `(0,1)`-edge of the `a = 0` diagonal horn map is the
image of `v₀`. -/
lemma leftHornEdge_shuffleDiagHornLift_comp (m b : ℕ)
    (hb0 : 0 < b) (hb : b ≤ m + 1)
    (φ : ((shuffleDiagFilt0 (m + 1)
        (shuffleCode (m + 1) 0 b + 1) :
        (Δ[m + 1] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (leftHornEdge
        (Subcomplex.hornLift
          (shuffleDiagFilt0 (m + 1) (shuffleCode (m + 1) 0 b + 1))
          (shuffleDiagW (m + 1) 0 b (le_of_lt hb0) hb)
          (⟨0, by omega⟩ : Fin (m + 3))
          (shuffleDiagFilt0_preimage_shuffleDiagWMap hb0 hb) ≫
            φ)).edge =
      φ.app _ ⟨shuffleVert0 (m + 1),
        shuffleVert0_mem_shuffleDiagFilt0 _⟩ :=
  congrArg (φ.app _)
    (shuffleDiagHornLift_app_leftHornEdgeSimplex m b hb0 hb)

/-- The `a = 0` diagonal horn is special as soon as `v₀` of
the initial datum is an equivalence. -/
lemma isEquivalence_leftHornEdge_shuffleDiagStep (m b : ℕ)
    (hb0 : 0 < b) (hb : b ≤ m + 1)
    {φ : ((shuffleDiagFilt0 (m + 1)
        (shuffleCode (m + 1) 0 b + 1) :
        (Δ[m + 1] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((shuffleInit0 (m + 1) :
        (Δ[m + 1] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE
        (shuffleInit0_le_shuffleDiagFilt0 _) ≫ φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 (m + 1),
        shuffleVert0_mem_shuffleInit0 (m + 1)⟩)).IsEquivalence) :
    (leftHornEdge
        (Subcomplex.hornLift
          (shuffleDiagFilt0 (m + 1) (shuffleCode (m + 1) 0 b + 1))
          (shuffleDiagW (m + 1) 0 b (le_of_lt hb0) hb)
          (⟨0, by omega⟩ : Fin (m + 3))
          (shuffleDiagFilt0_preimage_shuffleDiagWMap hb0 hb) ≫
            φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      leftHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨shuffleVert0 (m + 1),
          shuffleVert0_mem_shuffleInit0 (m + 1)⟩)) ?_).2 hVert
  rw [leftHornEdge_shuffleDiagHornLift_comp m b hb0 hb]
  exact congr($(hrestr).app _ ⟨shuffleVert0 (m + 1),
    shuffleVert0_mem_shuffleInit0 (m + 1)⟩)

private lemma exists_extension_shuffleDiagFilt0 [Quasicategory C]
    (φ₀ : ((shuffleInit0 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence) :
    ∀ (d m : ℕ), m + d = (n + 1) * (n + 1) →
      ∃ φm : ((shuffleDiagFilt0 n m :
          (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (shuffleInit0_le_shuffleDiagFilt0 m) ≫
          φm = φ₀ := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmn : m = (n + 1) * (n + 1) := by omega
    subst hmn
    refine ⟨(Subcomplex.eqToIso shuffleDiagFilt0_top).hom ≫ φ₀, ?_⟩
    have hid : Subcomplex.homOfLE
          (shuffleInit0_le_shuffleDiagFilt0 ((n + 1) * (n + 1))) ≫
          (Subcomplex.eqToIso shuffleDiagFilt0_top).hom = 𝟙 _ := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (shuffleInit0 n).ι]
      simp
    rw [← Category.assoc, hid, Category.id_comp]
  | succ d ih =>
    intro m hm
    have hm1 : (m + 1) + d = (n + 1) * (n + 1) := by omega
    obtain ⟨φ₁, hφ₁⟩ := ih (m + 1) hm1
    by_cases hvalid : ∃ a b : ℕ, a < b ∧ b ≤ n ∧
        shuffleCode n a b = m
    · obtain ⟨a, b, hab, hb, hcode⟩ := hvalid
      have hab₀ : a ≤ b := le_of_lt hab
      have hpre := shuffleDiagFilt0_preimage_shuffleDiagWMap hab hb
      rw [hcode] at hpre
      obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 1] ⟶ C,
          Subcomplex.hornLift (shuffleDiagFilt0 n (m + 1))
              (shuffleDiagW n a b hab₀ hb)
              (⟨a, by omega⟩ : Fin (n + 2)) hpre ≫ φ₁ =
            Λ[n + 1, (⟨a, by omega⟩ : Fin (n + 2))].ι ≫ σC := by
        by_cases ha0 : a = 0
        · subst ha0
          obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
          have hm_eq : m = shuffleCode (m' + 1) 0 b := hcode.symm
          subst hm_eq
          refine exists_fill_horn_left_of_isEquivalence _ ?_
          exact isEquivalence_leftHornEdge_shuffleDiagStep m' b
            hab hb hφ₁ hVert
        · have hk0 : (0 : Fin (n + 2)) < (⟨a, by omega⟩ : Fin (n + 2)) := by
            rw [Fin.lt_def]
            change (0 : ℕ) < a
            omega
          have hkn : (⟨a, by omega⟩ : Fin (n + 2)) <
              Fin.last (n + 1) := by
            rw [Fin.lt_def, Fin.val_last]
            change a < n + 1
            omega
          exact Quasicategory.hornFilling hk0 hkn _
      obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
        (fun h ↦ shuffleDiagWMap_app_injective.{u} hab₀ hb h)
        φ₁ σC hσC
      have hstep : shuffleDiagFilt0 n m =
          shuffleDiagFilt0 n (m + 1) ⊔
            Subcomplex.ofSimplex (shuffleDiagW n a b hab₀ hb) := by
        rw [← hcode]
        exact shuffleDiagFilt0_eq_succ_sup hab hb
      refine ⟨(Subcomplex.eqToIso hstep).hom ≫ φ', ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit0_le_shuffleDiagFilt0 m) ≫
            (Subcomplex.eqToIso hstep).hom =
          Subcomplex.homOfLE
              (shuffleInit0_le_shuffleDiagFilt0 (m + 1)) ≫
            Subcomplex.homOfLE (show shuffleDiagFilt0 n (m + 1) ≤
              shuffleDiagFilt0 n (m + 1) ⊔
                Subcomplex.ofSimplex (shuffleDiagW n a b hab₀ hb)
              from le_sup_left) := by
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
      exact hφ₁
    · have hEq : shuffleDiagFilt0 n m =
          shuffleDiagFilt0 n (m + 1) :=
        shuffleDiagFilt0_eq_succ_of_not_valid (fun a b hab hb hcode ↦
          hvalid ⟨a, b, hab, hb, hcode⟩)
      refine ⟨(Subcomplex.eqToIso hEq).hom ≫ φ₁, ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit0_le_shuffleDiagFilt0 m) ≫
            (Subcomplex.eqToIso hEq).hom =
          Subcomplex.homOfLE
            (shuffleInit0_le_shuffleDiagFilt0 (m + 1)) := by
        rw [Subcomplex.eqToIso_hom,
          ← cancel_mono (shuffleDiagFilt0 n (m + 1)).ι]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp]
      exact hφ₁

/-- Extension of the initial datum over the full diagonal
stage `shuffleDiagFilt0 n 0`. -/
lemma exists_extension_shuffleDiagFilt0_zero [Quasicategory C]
    (φ₀ : ((shuffleInit0 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence) :
    ∃ φD : ((shuffleDiagFilt0 n 0 :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
      Subcomplex.homOfLE (shuffleInit0_le_shuffleDiagFilt0 0) ≫
        φD = φ₀ :=
  exists_extension_shuffleDiagFilt0 φ₀ hVert ((n + 1) * (n + 1)) 0
    (by omega)

end ShuffleDiagExtension0

/-!
## The horn-zero top filtration and its attaching horn

`shuffleTopFilt0 n m` is the diagonal stage together with
the shuffles `τ_{a,b}` of code `≥ m`. The attaching horn of
`τ_{a,b}` is `Λ[n+2, a]`.
-/

section ShuffleTopFilt0

variable {n : ℕ}

/-- The decreasing top filtration for horn zero: all
diagonals together with `τ_{a,b}` for `code(a,b) ≥ m`. -/
noncomputable def shuffleTopFilt0 (n m : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex :=
  shuffleDiagFilt0 n 0 ⊔ ⨆ (a : ℕ) (b : ℕ) (hab : a ≤ b)
    (hb : b ≤ n) (_ : m ≤ shuffleCode n a b),
    Subcomplex.ofSimplex (shuffleTau n a b hab hb)

lemma shuffleDiagFilt0_zero_le_shuffleTopFilt0 (m : ℕ) :
    shuffleDiagFilt0 n 0 ≤ shuffleTopFilt0 n m := by
  unfold shuffleTopFilt0
  exact le_sup_left

lemma shuffleInit0_le_shuffleTopFilt0 (m : ℕ) :
    shuffleInit0 n ≤ shuffleTopFilt0 n m :=
  (shuffleInit0_le_shuffleDiagFilt0 0).trans
    (shuffleDiagFilt0_zero_le_shuffleTopFilt0 m)

lemma ofSimplex_shuffleTau_le_shuffleTopFilt0 {m a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ n) (h : m ≤ shuffleCode n a b) :
    Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb) ≤
      shuffleTopFilt0 n m := by
  unfold shuffleTopFilt0
  refine (le_iSup_of_le a ?_).trans le_sup_right
  exact le_iSup_of_le b (le_iSup_of_le hab
    (le_iSup_of_le hb (le_iSup_of_le h le_rfl)))

lemma shuffleTopFilt0_succ_le (m : ℕ) :
    shuffleTopFilt0 n (m + 1) ≤ shuffleTopFilt0 n m := by
  unfold shuffleTopFilt0
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro h
  exact ofSimplex_shuffleTau_le_shuffleTopFilt0 hab hb
    (Nat.le_trans (Nat.le_succ m) h)

/-- One top filtration step at a valid code. -/
lemma shuffleTopFilt0_eq_succ_sup {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ n) :
    shuffleTopFilt0 n (shuffleCode n a b) =
      shuffleTopFilt0 n (shuffleCode n a b + 1) ⊔
        Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb) := by
  apply le_antisymm
  · unfold shuffleTopFilt0
    apply sup_le (le_sup_left.trans le_sup_left)
    apply iSup_le
    intro a'
    apply iSup_le
    intro b'
    apply iSup_le
    intro hab'
    apply iSup_le
    intro hb'
    apply iSup_le
    intro hcode
    by_cases hcc : shuffleCode n a' b' = shuffleCode n a b
    · obtain ⟨rfl, rfl⟩ := shuffleCode_inj hb' hb hcc
      exact le_sup_right
    · have hgt : shuffleCode n a b + 1 ≤ shuffleCode n a' b' := by
        omega
      refine (le_iSup_of_le a' ?_).trans
        (le_sup_right.trans le_sup_left)
      exact le_iSup_of_le b' (le_iSup_of_le hab'
        (le_iSup_of_le hb' (le_iSup_of_le hgt le_rfl)))
  · exact sup_le (shuffleTopFilt0_succ_le _)
      (ofSimplex_shuffleTau_le_shuffleTopFilt0 hab hb le_rfl)

/-- Invalid codes are skipped by the top filtration. -/
lemma shuffleTopFilt0_eq_succ_of_not_valid {m : ℕ}
    (h : ∀ a b : ℕ, a ≤ b → b ≤ n → shuffleCode n a b ≠ m) :
    shuffleTopFilt0 n m = shuffleTopFilt0 n (m + 1) := by
  apply le_antisymm _ (shuffleTopFilt0_succ_le m)
  unfold shuffleTopFilt0
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  have hgt : m + 1 ≤ shuffleCode n a b := by
    have hne := h a b hab hb
    omega
  exact ofSimplex_shuffleTau_le_shuffleTopFilt0 hab hb hgt

/-- The top of the top filtration is the diagonal stage. -/
lemma shuffleTopFilt0_top :
    shuffleTopFilt0 n ((n + 1) * (n + 1)) =
      shuffleDiagFilt0 n 0 := by
  refine le_antisymm ?_ le_sup_left
  unfold shuffleTopFilt0
  refine sup_le le_rfl ?_
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  exfalso
  have hlt := shuffleCode_lt_bound hab hb
  omega

/-- The bottom of the top filtration is the whole prism
(every nondegenerate top simplex is a shuffle). -/
lemma shuffleTopFilt0_zero : shuffleTopFilt0 n 0 = ⊤ := by
  refine (prodStdSimplex.subcomplex_eq_top_iff
    (shuffleTopFilt0 n 0) rfl).2 ?_
  intro x hx
  obtain ⟨a, b, hab, hb, hτ⟩ :=
    exists_shuffleTau_of_nonDegenerate hx
  rw [← hτ]
  exact ofSimplex_shuffleTau_le_shuffleTopFilt0 hab hb
    (Nat.zero_le _) _ (Subcomplex.mem_ofSimplex_obj _)

end ShuffleTopFilt0

section ShuffleTopPreimage0

variable {n a b : ℕ}

/-- **Attaching horn, top phase, horn zero**: the preimage
of `shuffleTopFilt0 n (code(a,b)+1)` under `τ_{a,b}` is
`Λ[n+2, a]`. -/
lemma shuffleTopFilt0_preimage_shuffleTauMap (hab : a ≤ b)
    (hb : b ≤ n) :
    (shuffleTopFilt0 n (shuffleCode n a b + 1)).preimage
        (shuffleTauMap.{u} n a b hab hb) =
      (Λ[n + 2, ⟨a, by omega⟩] :
        (Δ[n + 2] : SSet.{u}).Subcomplex) := by
  -- Range witnesses in the missing face `δ_a τ_{a,b}`.
  have hA1 : (⟨a, by omega⟩, (1 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleTau.{u} n a b hab hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleTau_objEquiv_injective.{u} hab hb)
      ⟨a, by omega⟩).2 ⟨?_, ?_⟩
    · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
        (Or.inr (Or.inl ⟨rfl, le_rfl, hab⟩))
    · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
        change shuffleSnd a b a ≠ 1
        rw [shuffleSnd_at_a]
        omega)
  have hB1 : (⟨b, by omega⟩, (1 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleTau.{u} n a b hab hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleTau_objEquiv_injective.{u} hab hb)
      ⟨a, by omega⟩).2 ⟨?_, ?_⟩
    · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
        (Or.inr (Or.inl ⟨rfl, hab, le_rfl⟩))
    · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
        change shuffleSnd a b a ≠ 1
        rw [shuffleSnd_at_a]
        omega)
  have hB2 : (⟨b, by omega⟩, (2 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleTau.{u} n a b hab hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleTau_objEquiv_injective.{u} hab hb)
      ⟨a, by omega⟩).2 ⟨?_, ?_⟩
    · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
        (Or.inr (Or.inr ⟨rfl, le_rfl⟩))
    · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
        change shuffleSnd a b a ≠ 2
        rw [shuffleSnd_at_a]
        omega)
  -- The missing face is in no diagonal and not in `S₀`.
  have hmissDiag : ∀ {a' b' : ℕ} (hab' : a' < b') (hb' : b' ≤ n),
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleTau.{u} n a b hab hb) ∉
        (Subcomplex.ofSimplex
          (shuffleDiagW.{u} n a' b' (le_of_lt hab') hb')).obj _ := by
    intro a' b' hab' hb' hmem'
    have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
          ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
            (shuffleTau.{u} n a b hab hb))) ⊆
        Set.range (prodStdSimplex.objEquiv.{u}
          (shuffleDiagW.{u} n a' b' (le_of_lt hab') hb')) :=
      (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
        ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
    by_cases hb'le : b' ≤ b
    · have hnot : (⟨b, by omega⟩, (1 : Fin 3)) ∉ Set.range
          (prodStdSimplex.objEquiv.{u}
            (shuffleDiagW.{u} n a' b' (le_of_lt hab') hb')) := by
        intro hmem''
        have hτ := (shuffleDiagW_mem_range_iff.{u}
          (le_of_lt hab') hb').1 hmem''
        obtain ⟨hτ1, hτ2⟩ := hτ
        rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
          at hτ1
        rcases hτ1 with ⟨hbad, -⟩ | ⟨-, -, hbad⟩ | ⟨hbad, -⟩
        · exact (by decide : ¬ ((1 : Fin 3)).val = 0) hbad
        · change b ≤ b' at hbad
          have hbb : b' = b := by omega
          apply hτ2
          have hEq : prodStdSimplex.objEquiv.{u}
                (shuffleTau.{u} n a' b' (le_of_lt hab') hb')
                ⟨b' + 1, by omega⟩ =
              (⟨b, by omega⟩, (1 : Fin 3)) :=
            (shuffleTau_objEquiv_apply_eq_iff.{u} (le_of_lt hab')
              hb' ⟨b' + 1, by omega⟩).2 ⟨by
                change shuffleFst a' b' (b' + 1) = b
                rw [shuffleFst_at_succ_b (le_of_lt hab'), hbb], by
                change shuffleSnd a' b' (b' + 1) = 1
                exact shuffleSnd_at_succ_b (le_of_lt hab')⟩
          exact hEq.symm
        · exact (by decide : ¬ ((1 : Fin 3)).val = 2) hbad
      exact hnot (hle2 hB1)
    · have hnot : (⟨b, by omega⟩, (2 : Fin 3)) ∉ Set.range
          (prodStdSimplex.objEquiv.{u}
            (shuffleDiagW.{u} n a' b' (le_of_lt hab') hb')) := by
        intro hmem''
        have hτ : (⟨b, by omega⟩, (2 : Fin 3)) ∈ Set.range
              (prodStdSimplex.objEquiv.{u}
                (shuffleTau.{u} n a' b' (le_of_lt hab') hb')) :=
          ((shuffleDiagW_mem_range_iff.{u}
            (le_of_lt hab') hb').1 hmem'').1
        rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
          at hτ
        rcases hτ with ⟨hbad, -⟩ | ⟨hbad, -, -⟩ | ⟨-, hbad⟩
        · exact (by decide : ¬ ((2 : Fin 3)).val = 0) hbad
        · exact (by decide : ¬ ((2 : Fin 3)).val = 1) hbad
        · change b' ≤ b at hbad
          omega
      exact hnot (hle2 hB2)
  have hmissDiagTop :
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
          (shuffleTau.{u} n a b hab hb) ∉
        (shuffleDiagFilt0 n 0).obj _ := by
    intro hmem
    unfold shuffleDiagFilt0 at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · have hmissInit :
          (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
              (shuffleTau.{u} n a b hab hb) ∉
            (shuffleInit0 n).obj _ := by
        refine shuffle_notMem_shuffleInit0_of_range ?_
          ⟨⟨a, by omega⟩, hA1⟩ ⟨⟨b, by omega⟩, hB2⟩
        intro v
        by_cases hv1 : v.val < a
        · refine ⟨(0 : Fin 3), ?_⟩
          refine (shuffle_mem_range_objEquiv_δ_iff.{u}
            (shuffleTau_objEquiv_injective.{u} hab hb)
            ⟨a, by omega⟩).2 ⟨?_, ?_⟩
          · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
              (Or.inl ⟨rfl, Nat.le_of_lt hv1⟩)
          · exact shuffle_pair_ne_tau_of_fst_ne.{u} hab hb (by
              change shuffleFst a b a ≠ v.val
              rw [shuffleFst_at_a]
              omega)
        · by_cases hv2 : v.val ≤ b
          · refine ⟨(1 : Fin 3), ?_⟩
            refine (shuffle_mem_range_objEquiv_δ_iff.{u}
              (shuffleTau_objEquiv_injective.{u} hab hb)
              ⟨a, by omega⟩).2 ⟨?_, ?_⟩
            · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
                (Or.inr (Or.inl
                  ⟨rfl, Nat.le_of_not_gt hv1, hv2⟩))
            · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
                change shuffleSnd a b a ≠ 1
                rw [shuffleSnd_at_a]
                omega)
          · refine ⟨(2 : Fin 3), ?_⟩
            refine (shuffle_mem_range_objEquiv_δ_iff.{u}
              (shuffleTau_objEquiv_injective.{u} hab hb)
              ⟨a, by omega⟩).2 ⟨?_, ?_⟩
            · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
                (Or.inr (Or.inr
                  ⟨rfl, Nat.le_of_lt (Nat.lt_of_not_ge hv2)⟩))
            · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
                change shuffleSnd a b a ≠ 2
                rw [shuffleSnd_at_a]
                omega)
      exact hmissInit h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨a', b', hab', hb', -, hmem'⟩ := hI
      exact hmissDiag hab' hb' hmem'
  apply le_antisymm
  · rw [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl,
      Subcomplex.ofSimplex_le_iff]
    intro hmem
    unfold shuffleTopFilt0 at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · exact hmissDiagTop h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨a', b', hab', hb', hcode, hmem'⟩ := hI
      have hlt : shuffleCode n a b < shuffleCode n a' b' := hcode
      have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
            ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
              (shuffleTau.{u} n a b hab hb))) ⊆
          Set.range (prodStdSimplex.objEquiv.{u}
            (shuffleTau.{u} n a' b' hab' hb')) :=
        (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
          ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
      rcases shuffleCode_lt_cases hb hb' hlt with hgt | ⟨rfl, hgt⟩
      · have hnot : (⟨a, by omega⟩, (1 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleTau.{u} n a' b' hab' hb')) := by
          intro hmem''
          rw [mem_range_shuffleTau_objEquiv.{u} hab' hb'] at hmem''
          rcases hmem'' with ⟨hbad, -⟩ | ⟨-, hbad, -⟩ | ⟨hbad, -⟩
          · exact (by decide : ¬ ((1 : Fin 3)).val = 0) hbad
          · change a' ≤ a at hbad
            omega
          · exact (by decide : ¬ ((1 : Fin 3)).val = 2) hbad
        exact hnot (hle2 hA1)
      · have hnot : (⟨b, by omega⟩, (2 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleTau.{u} n a b' hab' hb')) := by
          intro hmem''
          rw [mem_range_shuffleTau_objEquiv.{u} hab' hb'] at hmem''
          rcases hmem'' with ⟨hbad, -⟩ | ⟨hbad, -, -⟩ | ⟨-, hbad⟩
          · exact (by decide : ¬ ((2 : Fin 3)).val = 0) hbad
          · exact (by decide : ¬ ((2 : Fin 3)).val = 1) hbad
          · change b' ≤ b at hbad
            omega
        exact hnot (hle2 hB2)
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    have hjval : j.val ≠ a := by
      have hne : j ≠ ⟨a, by omega⟩ :=
        Set.mem_compl_singleton_iff.1 hj
      exact fun e ↦ hne (Fin.ext e)
    rw [← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl]
    by_cases hj1 : j.val = a + 1
    · by_cases hba : a = b
      · refine (shuffle_ofSimplex_le_top_prod_horn_of_snd_miss
            (i := (0 : Fin 3)) (w := (1 : Fin 3)) (by decide)
            ?_).trans
          ((Subcomplex.top_prod_le_unionProd _ _).trans
            (shuffleInit0_le_shuffleTopFilt0 _))
        intro t htEq
        have hval : shuffleSnd a b (j.succAbove t).val = 1 := by
          have h2 := congrArg Fin.val htEq
          rw [shuffle_objEquiv_δ_apply,
            shuffleTau_objEquiv_snd_val hab hb] at h2
          exact h2
        have hu := shuffleSnd_eq_one.1 hval
        have hne : (j.succAbove t).val ≠ a + 1 := by
          rw [← hj1]
          exact fun e ↦ Fin.succAbove_ne j t (Fin.ext e)
        omega
      · have hablt : a < b := lt_of_le_of_ne hab hba
        have hmem2 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
              (shuffleTau.{u} n a b hab hb) ∈
            (Subcomplex.ofSimplex
              (shuffleTau.{u} n (a + 1) b hablt hb)).obj _ := by
          have h1 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
                (shuffleTau.{u} n (a + 1) b hablt hb) ∈
              (Subcomplex.ofSimplex
                (shuffleTau.{u} n (a + 1) b hablt hb)).obj _ :=
            (Subcomplex.ofSimplex _).map _
              (Subcomplex.mem_ofSimplex_obj _)
          have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                (shuffleTau.{u} n a b hab hb) =
              (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a + 1, by omega⟩
                (shuffleTau.{u} n (a + 1) b hablt hb) := by
            have hjj : j = ⟨a + 1, Nat.lt_succ_of_le
                  (le_trans (Nat.succ_le_succ (le_trans hab hb))
                    (Nat.le_succ _))⟩ := Fin.ext hj1
            subst hjj
            exact shuffleTau_δ_succ_left hablt hb
          exact hEq.symm ▸ h1
        exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem2).trans
          (ofSimplex_shuffleTau_le_shuffleTopFilt0 hablt hb
            (shuffleCode_succ_left n a b))
    · by_cases hj2 : j.val = b + 1
      · have hablt : a < b := by omega
        have hmem2 : Subcomplex.ofSimplex
              ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                (shuffleTau.{u} n a b hab hb)) ≤
            shuffleDiagFilt0 n 0 := by
          have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                (shuffleTau.{u} n a b hab hb) =
              shuffleDiagW.{u} n a b hab hb := by
            have hjj : j = ⟨b + 1, Nat.lt_succ_of_le
                  (le_trans (Nat.succ_le_succ hb)
                    (Nat.le_succ _))⟩ := Fin.ext hj2
            subst hjj
            rfl
          have hW : Subcomplex.ofSimplex
                (shuffleDiagW.{u} n a b hab hb) ≤
              shuffleDiagFilt0 n 0 :=
            ofSimplex_shuffleDiagW_le_shuffleDiagFilt0 hablt hb
              (Nat.zero_le _)
          exact hEq.symm ▸ hW
        exact hmem2.trans (shuffleDiagFilt0_zero_le_shuffleTopFilt0 _)
      · by_cases hj3 : j.val = b + 2
        · by_cases hbn : b = n
          · refine (shuffle_ofSimplex_le_top_prod_horn_of_snd_miss
                (i := (0 : Fin 3)) (w := (2 : Fin 3)) (by decide)
                ?_).trans
              ((Subcomplex.top_prod_le_unionProd _ _).trans
                (shuffleInit0_le_shuffleTopFilt0 _))
            intro t htEq
            have hval : shuffleSnd a b (j.succAbove t).val = 2 := by
              have h2 := congrArg Fin.val htEq
              rw [shuffle_objEquiv_δ_apply,
                shuffleTau_objEquiv_snd_val hab hb] at h2
              exact h2
            have hu := (shuffleSnd_eq_two hab).1 hval
            have hle : (j.succAbove t).val ≤ n + 2 := by
              have h3 := (j.succAbove t).isLt
              omega
            have hne : (j.succAbove t).val ≠ b + 2 := by
              rw [← hj3]
              exact fun e ↦ Fin.succAbove_ne j t (Fin.ext e)
            omega
          · have hblt : b < n := by omega
            have hmem2 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                  (shuffleTau.{u} n a b hab hb) ∈
                (Subcomplex.ofSimplex
                  (shuffleTau.{u} n a (b + 1) (by omega) hblt)).obj _ := by
              have h1 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ
                    ⟨b + 2, by omega⟩
                    (shuffleTau.{u} n a (b + 1) (by omega) hblt) ∈
                  (Subcomplex.ofSimplex
                    (shuffleTau.{u} n a (b + 1) (by omega) hblt)).obj _ :=
                (Subcomplex.ofSimplex _).map _
                  (Subcomplex.mem_ofSimplex_obj _)
              have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                    (shuffleTau.{u} n a b hab hb) =
                  (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
                    (shuffleTau.{u} n a (b + 1) (by omega) hblt) := by
                have hjj : j = ⟨b + 2, Nat.lt_succ_of_le
                      (Nat.succ_le_succ (Nat.succ_le_succ hb))⟩ :=
                    Fin.ext hj3
                subst hjj
                exact shuffleTau_δ_succ_right hab hblt
              exact hEq.symm ▸ h1
            exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem2).trans
              (ofSimplex_shuffleTau_le_shuffleTopFilt0 (by omega)
                hblt (le_of_eq (shuffleCode_succ_right n a b).symm))
        · exact (shuffleTau_δ_ofSimplex_le_boundary_prod_top
              hab hb ⟨hjval, hj1, hj2, hj3⟩).trans
            ((Subcomplex.prod_top_le_unionProd _ _).trans
              (shuffleInit0_le_shuffleTopFilt0 _))

end ShuffleTopPreimage0

/-!
## Extension over the top stage and horn zero assembly

The special edge of the `a = 0` top attaching horns is `v₀`;
downward induction over the code extends over all shuffles,
and transport across `shuffleTopFilt0 n 0 = ⊤` gives
`ShuffleHornZeroCellExtension`.
-/

section ShuffleTopExtension0

variable {n : ℕ} {C : SSet.{u}}

lemma shuffleVert0_mem_shuffleTopFilt0 (m : ℕ) :
    shuffleVert0 n ∈ (shuffleTopFilt0 n m).obj _ :=
  (shuffleInit0_le_shuffleTopFilt0 m) _
    (shuffleVert0_mem_shuffleInit0 n)

/-- The horn lift for `τ_{0,b}` sends the `(0,1)`-edge
simplex of `Λ[n+2, 0]` to `v₀`. -/
lemma shuffleTopHornLift_app_leftHornEdgeSimplex (b : ℕ)
    (hb : b ≤ n) :
    (Subcomplex.hornLift
        (shuffleTopFilt0 n (shuffleCode n 0 b + 1))
        (shuffleTau n 0 b (Nat.zero_le b) hb)
        ⟨0, by omega⟩
        (shuffleTopFilt0_preimage_shuffleTauMap
          (Nat.zero_le b) hb)).app _
        (leftHornEdgeSimplex.{u} n) =
      ⟨shuffleVert0 n, shuffleVert0_mem_shuffleTopFilt0 _⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift
          (shuffleTopFilt0 n (shuffleCode n 0 b + 1))
          (shuffleTau n 0 b (Nat.zero_le b) hb)
          ⟨0, by omega⟩
          (shuffleTopFilt0_preimage_shuffleTauMap
            (Nat.zero_le b) hb)).app _
          (leftHornEdgeSimplex.{u} n)).val
      = (shuffleTauMap.{u} n 0 b (Nat.zero_le b) hb).app _
          (stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩
            (Fin.zero_le _)) :=
        congr($(Subcomplex.hornLift_ι
          (shuffleTopFilt0_preimage_shuffleTauMap
            (Nat.zero_le b) hb)).app _
            (leftHornEdgeSimplex.{u} n))
    _ = shuffleVert0 n :=
        shuffleTauMap_zero_app_edge hb

/-- The `(0,1)`-edge of the `a = 0` top horn map is the
image of `v₀`. -/
lemma leftHornEdge_shuffleTopHornLift_comp (b : ℕ)
    (hb : b ≤ n)
    (φ : ((shuffleTopFilt0 n (shuffleCode n 0 b + 1) :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (leftHornEdge
        (Subcomplex.hornLift
          (shuffleTopFilt0 n (shuffleCode n 0 b + 1))
          (shuffleTau n 0 b (Nat.zero_le b) hb)
          ⟨0, by omega⟩
          (shuffleTopFilt0_preimage_shuffleTauMap
            (Nat.zero_le b) hb) ≫ φ)).edge =
      φ.app _ ⟨shuffleVert0 n, shuffleVert0_mem_shuffleTopFilt0 _⟩ :=
  congrArg (φ.app _)
    (shuffleTopHornLift_app_leftHornEdgeSimplex b hb)

/-- The `a = 0` top horn is special as soon as `v₀` of the
initial datum is an equivalence. -/
lemma isEquivalence_leftHornEdge_shuffleTopStep (b : ℕ)
    (hb : b ≤ n)
    {φ : ((shuffleTopFilt0 n (shuffleCode n 0 b + 1) :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((shuffleInit0 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE
        (shuffleInit0_le_shuffleTopFilt0 _) ≫ φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence) :
    (leftHornEdge
        (Subcomplex.hornLift
          (shuffleTopFilt0 n (shuffleCode n 0 b + 1))
          (shuffleTau n 0 b (Nat.zero_le b) hb)
          ⟨0, by omega⟩
          (shuffleTopFilt0_preimage_shuffleTauMap
            (Nat.zero_le b) hb) ≫ φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      leftHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨shuffleVert0 n,
          shuffleVert0_mem_shuffleInit0 n⟩)) ?_).2 hVert
  rw [leftHornEdge_shuffleTopHornLift_comp b hb]
  exact congr($(hrestr).app _ ⟨shuffleVert0 n,
    shuffleVert0_mem_shuffleInit0 n⟩)

private lemma exists_extension_shuffleTopFilt0 [Quasicategory C]
    (φ₀ : ((shuffleInit0 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence) :
    ∀ (d m : ℕ), m + d = (n + 1) * (n + 1) →
      ∃ φm : ((shuffleTopFilt0 n m :
          (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (shuffleInit0_le_shuffleTopFilt0 m) ≫
          φm = φ₀ := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmn : m = (n + 1) * (n + 1) := by omega
    subst hmn
    obtain ⟨φD, hφD⟩ :=
      exists_extension_shuffleDiagFilt0_zero φ₀ hVert
    refine ⟨(Subcomplex.eqToIso shuffleTopFilt0_top).hom ≫ φD, ?_⟩
    have hcomp : Subcomplex.homOfLE
          (shuffleInit0_le_shuffleTopFilt0 ((n + 1) * (n + 1))) ≫
          (Subcomplex.eqToIso shuffleTopFilt0_top).hom =
        Subcomplex.homOfLE (shuffleInit0_le_shuffleDiagFilt0 0) := by
      rw [Subcomplex.eqToIso_hom,
        ← cancel_mono (shuffleDiagFilt0 n 0).ι]
      simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcomp]
    exact hφD
  | succ d ih =>
    intro m hm
    have hm1 : (m + 1) + d = (n + 1) * (n + 1) := by omega
    obtain ⟨φ₁, hφ₁⟩ := ih (m + 1) hm1
    by_cases hvalid : ∃ a b : ℕ, a ≤ b ∧ b ≤ n ∧
        shuffleCode n a b = m
    · obtain ⟨a, b, hab, hb, hcode⟩ := hvalid
      have hpre := shuffleTopFilt0_preimage_shuffleTauMap hab hb
      rw [hcode] at hpre
      obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 2] ⟶ C,
          Subcomplex.hornLift (shuffleTopFilt0 n (m + 1))
              (shuffleTau n a b hab hb)
              (⟨a, by omega⟩ : Fin (n + 3)) hpre ≫ φ₁ =
            Λ[n + 2, (⟨a, by omega⟩ : Fin (n + 3))].ι ≫ σC := by
        by_cases ha0 : a = 0
        · subst ha0
          have hm_eq : m = shuffleCode n 0 b := hcode.symm
          subst hm_eq
          refine exists_fill_horn_left_of_isEquivalence _ ?_
          exact isEquivalence_leftHornEdge_shuffleTopStep b
            hb hφ₁ hVert
        · have hk0 : (0 : Fin (n + 3)) <
              (⟨a, by omega⟩ : Fin (n + 3)) := by
            rw [Fin.lt_def]
            change (0 : ℕ) < a
            omega
          have hkn : (⟨a, by omega⟩ : Fin (n + 3)) <
              Fin.last (n + 2) := by
            rw [Fin.lt_def, Fin.val_last]
            change a < n + 2
            omega
          exact Quasicategory.hornFilling hk0 hkn _
      obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
        (fun h ↦ shuffleTauMap_app_injective.{u} hab hb h)
        φ₁ σC hσC
      have hstep : shuffleTopFilt0 n m =
          shuffleTopFilt0 n (m + 1) ⊔
            Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb) := by
        rw [← hcode]
        exact shuffleTopFilt0_eq_succ_sup hab hb
      refine ⟨(Subcomplex.eqToIso hstep).hom ≫ φ', ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit0_le_shuffleTopFilt0 m) ≫
            (Subcomplex.eqToIso hstep).hom =
          Subcomplex.homOfLE
              (shuffleInit0_le_shuffleTopFilt0 (m + 1)) ≫
            Subcomplex.homOfLE (show shuffleTopFilt0 n (m + 1) ≤
              shuffleTopFilt0 n (m + 1) ⊔
                Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb)
              from le_sup_left) := by
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
      exact hφ₁
    · have hEq : shuffleTopFilt0 n m =
          shuffleTopFilt0 n (m + 1) :=
        shuffleTopFilt0_eq_succ_of_not_valid (fun a b hab hb hcode ↦
          hvalid ⟨a, b, hab, hb, hcode⟩)
      refine ⟨(Subcomplex.eqToIso hEq).hom ≫ φ₁, ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit0_le_shuffleTopFilt0 m) ≫
            (Subcomplex.eqToIso hEq).hom =
          Subcomplex.homOfLE
            (shuffleInit0_le_shuffleTopFilt0 (m + 1)) := by
        rw [Subcomplex.eqToIso_hom,
          ← cancel_mono (shuffleTopFilt0 n (m + 1)).ι]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp]
      exact hφ₁

end ShuffleTopExtension0

section ShuffleHornZeroAssembly

variable {n : ℕ} {C : SSet.{u}}

/-- **The horn-zero cell, unfolded form** (the supporting result,
`shuffleInit0` side): a map out of
`∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]` to a quasicategory, taking
`v₀` to an equivalence, extends over `Δ[n] ⊗ Δ[2]`. -/
theorem exists_extension_of_unionProd_boundary_horn_zero
    [Quasicategory C]
    (φ₀ : ((shuffleInit0 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence) :
    ∃ P : (Δ[n] ⊗ Δ[2] : SSet.{u}) ⟶ C,
      (shuffleInit0 n).ι ≫ P = φ₀ := by
  obtain ⟨φm, hφm⟩ := exists_extension_shuffleTopFilt0 φ₀ hVert
    ((n + 1) * (n + 1)) 0 (by omega)
  set iso : ((shuffleTopFilt0 n 0 :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[2] : SSet.{u}) :=
    Subcomplex.eqToIso shuffleTopFilt0_zero ≪≫
      Subcomplex.topIso _ with hiso
  refine ⟨iso.inv ≫ φm, ?_⟩
  have hhom : iso.hom = (shuffleTopFilt0 n 0).ι := by
    rw [hiso, Iso.trans_hom, Subcomplex.eqToIso_hom,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (shuffleInit0 n).ι =
      Subcomplex.homOfLE (shuffleInit0_le_shuffleTopFilt0 0) ≫
        iso.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  rw [hι, Category.assoc, ← Category.assoc iso.hom iso.inv φm,
    Iso.hom_inv_id, Category.id_comp]
  exact hφm

/-- **The horn-zero cell input of `ShuffleBridges.lean`**
(the supporting result): `ShuffleHornZeroCellExtension n C` holds for every
quasicategory `C`. -/
theorem shuffleHornZeroCellExtension_of_quasicategory (n : ℕ)
    (C : SSet.{u}) [Quasicategory C] :
    ShuffleHornZeroCellExtension n C := by
  intro φ₀ hVert
  exact exists_extension_of_unionProd_boundary_horn_zero φ₀ hVert

end ShuffleHornZeroAssembly

/-!
## The horn-two diagonal filtration

Mirror of §2 with increasing codes: `shuffleDiagFilt2 n m` is
`shuffleInit2 n` together with the diagonals `W'_{a,b}` of
code `< m`. The attaching horn of `W'_{a,b}` is
`Λ[n+1, b+1]`.
-/

section ShuffleDiagFilt2

variable {n : ℕ}

/-- The increasing diagonal filtration for horn two:
`S₂` together with `W'_{a,b}` for `code(a,b) < m`. -/
noncomputable def shuffleDiagFilt2 (n m : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex :=
  shuffleInit2 n ⊔ ⨆ (a : ℕ) (b : ℕ) (hab : a < b) (hb : b ≤ n)
    (_ : shuffleCode n a b < m),
    Subcomplex.ofSimplex (shuffleDiagW' n a b (le_of_lt hab) hb)

lemma shuffleInit2_le_shuffleDiagFilt2 (m : ℕ) :
    shuffleInit2 n ≤ shuffleDiagFilt2 n m :=
  le_sup_left

lemma ofSimplex_shuffleDiagW'_le_shuffleDiagFilt2 {m a b : ℕ}
    (hab : a < b) (hb : b ≤ n) (h : shuffleCode n a b < m) :
    Subcomplex.ofSimplex
        (shuffleDiagW'.{u} n a b (le_of_lt hab) hb) ≤
      shuffleDiagFilt2 n m := by
  unfold shuffleDiagFilt2
  refine (le_iSup_of_le a ?_).trans le_sup_right
  exact le_iSup_of_le b (le_iSup_of_le hab
    (le_iSup_of_le hb (le_iSup_of_le h le_rfl)))

lemma shuffleDiagFilt2_le_succ (m : ℕ) :
    shuffleDiagFilt2 n m ≤ shuffleDiagFilt2 n (m + 1) := by
  unfold shuffleDiagFilt2
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro h
  exact ofSimplex_shuffleDiagW'_le_shuffleDiagFilt2 hab hb
    (Nat.lt_succ_of_lt h)

/-- One diagonal filtration step at a valid code. -/
lemma shuffleDiagFilt2_eq_succ_sup {a b : ℕ} (hab : a < b)
    (hb : b ≤ n) :
    shuffleDiagFilt2 n (shuffleCode n a b + 1) =
      shuffleDiagFilt2 n (shuffleCode n a b) ⊔
        Subcomplex.ofSimplex
          (shuffleDiagW'.{u} n a b (le_of_lt hab) hb) := by
  apply le_antisymm
  · unfold shuffleDiagFilt2
    apply sup_le (le_sup_left.trans le_sup_left)
    apply iSup_le
    intro a'
    apply iSup_le
    intro b'
    apply iSup_le
    intro hab'
    apply iSup_le
    intro hb'
    apply iSup_le
    intro hcode
    by_cases hcc : shuffleCode n a' b' = shuffleCode n a b
    · obtain ⟨rfl, rfl⟩ := shuffleCode_inj hb' hb hcc
      exact le_sup_right
    · have hlt : shuffleCode n a' b' < shuffleCode n a b := by
        omega
      refine (le_iSup_of_le a' ?_).trans
        (le_sup_right.trans le_sup_left)
      exact le_iSup_of_le b' (le_iSup_of_le hab'
        (le_iSup_of_le hb' (le_iSup_of_le hlt le_rfl)))
  · exact sup_le (shuffleDiagFilt2_le_succ _)
      (ofSimplex_shuffleDiagW'_le_shuffleDiagFilt2 hab hb
        (Nat.lt_succ_self _))

/-- Invalid codes are skipped. -/
lemma shuffleDiagFilt2_eq_succ_of_not_valid {m : ℕ}
    (h : ∀ a b : ℕ, a < b → b ≤ n → shuffleCode n a b ≠ m) :
    shuffleDiagFilt2 n (m + 1) = shuffleDiagFilt2 n m := by
  apply le_antisymm _ (shuffleDiagFilt2_le_succ m)
  unfold shuffleDiagFilt2
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  have hlt : shuffleCode n a b < m := by
    have hne := h a b hab hb
    omega
  exact ofSimplex_shuffleDiagW'_le_shuffleDiagFilt2 hab hb hlt

/-- The bottom of the increasing diagonal filtration is
`S₂`. -/
lemma shuffleDiagFilt2_zero :
    shuffleDiagFilt2 n 0 = shuffleInit2 n := by
  refine le_antisymm ?_ le_sup_left
  unfold shuffleDiagFilt2
  refine sup_le le_rfl ?_
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  exact absurd hcode (Nat.not_lt_zero _)

end ShuffleDiagFilt2

section ShuffleDiagPreimage2

variable {n a b : ℕ}

/-- **Attaching horn, diagonal phase, horn two**: the
preimage of `shuffleDiagFilt2 n (code(a,b))` under `W'_{a,b}`
is `Λ[n+1, b+1]`. -/
lemma shuffleDiagFilt2_preimage_shuffleDiagW'Map (hab : a < b)
    (hb : b ≤ n) :
    (shuffleDiagFilt2 n (shuffleCode n a b)).preimage
        (shuffleDiagW'Map.{u} n a b (le_of_lt hab) hb) =
      (Λ[n + 1, ⟨b + 1, by omega⟩] :
        (Δ[n + 1] : SSet.{u}).Subcomplex) := by
  have hab₀ : a ≤ b := le_of_lt hab
  -- Range witnesses in the missing face `δ_{b+1} W'_{a,b}`.
  have hA0 : (⟨a, by omega⟩, (0 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 1, by omega⟩
          (shuffleDiagW'.{u} n a b hab₀ hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleDiagW'_objEquiv_injective.{u} hab₀ hb)
      ⟨b + 1, by omega⟩).2 ⟨?_, ?_⟩
    · refine (shuffleDiagW'_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
      · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
          (Or.inl ⟨rfl, le_rfl⟩)
      · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab₀ hb (by
          change shuffleSnd a b (a + 1) ≠ 0
          rw [shuffleSnd_at_succ_a hab₀]
          omega)
    · exact shuffle_pair_ne_diagW'_of_snd_ne.{u} hab₀ hb (by
        change shuffleDiagSnd a b (b + 1) ≠ 0
        rw [shuffleDiagSnd_at_b_add_one hab₀]
        omega)
  have hB1 : (⟨b, by omega⟩, (1 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 1, by omega⟩
          (shuffleDiagW'.{u} n a b hab₀ hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleDiagW'_objEquiv_injective.{u} hab₀ hb)
      ⟨b + 1, by omega⟩).2 ⟨?_, ?_⟩
    · refine (shuffleDiagW'_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
      · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
          (Or.inr (Or.inl ⟨rfl, hab₀, le_rfl⟩))
      · exact shuffle_pair_ne_tau_of_fst_ne.{u} hab₀ hb (by
          change shuffleFst a b (a + 1) ≠ b
          rw [shuffleFst_at_succ_a hab₀]
          omega)
    · exact shuffle_pair_ne_diagW'_of_snd_ne.{u} hab₀ hb (by
        change shuffleDiagSnd a b (b + 1) ≠ 1
        rw [shuffleDiagSnd_at_b_add_one hab₀]
        omega)
  -- The missing face is not in `S₂`.
  have hmissInit :
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 1, by omega⟩
          (shuffleDiagW'.{u} n a b hab₀ hb) ∉
        (shuffleInit2 n).obj _ := by
    refine shuffle_notMem_shuffleInit2_of_range ?_
      ⟨⟨a, by omega⟩, hA0⟩ ⟨⟨b, by omega⟩, hB1⟩
    intro v
    by_cases hv1 : v.val ≤ a
    · refine ⟨(0 : Fin 3), ?_⟩
      refine (shuffle_mem_range_objEquiv_δ_iff.{u}
        (shuffleDiagW'_objEquiv_injective.{u} hab₀ hb)
        ⟨b + 1, by omega⟩).2 ⟨?_, ?_⟩
      · refine (shuffleDiagW'_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
        · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
            (Or.inl ⟨rfl, hv1⟩)
        · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab₀ hb (by
            change shuffleSnd a b (a + 1) ≠ 0
            rw [shuffleSnd_at_succ_a hab₀]
            omega)
      · exact shuffle_pair_ne_diagW'_of_snd_ne.{u} hab₀ hb (by
          change shuffleDiagSnd a b (b + 1) ≠ 0
          rw [shuffleDiagSnd_at_b_add_one hab₀]
          omega)
    · by_cases hv2 : v.val ≤ b
      · refine ⟨(1 : Fin 3), ?_⟩
        refine (shuffle_mem_range_objEquiv_δ_iff.{u}
          (shuffleDiagW'_objEquiv_injective.{u} hab₀ hb)
          ⟨b + 1, by omega⟩).2 ⟨?_, ?_⟩
        · refine (shuffleDiagW'_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
          · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
              (Or.inr (Or.inl
                ⟨rfl, Nat.le_of_lt (Nat.lt_of_not_ge hv1), hv2⟩))
          · exact shuffle_pair_ne_tau_of_fst_ne.{u} hab₀ hb (by
              change shuffleFst a b (a + 1) ≠ v.val
              rw [shuffleFst_at_succ_a hab₀]
              omega)
        · exact shuffle_pair_ne_diagW'_of_snd_ne.{u} hab₀ hb (by
            change shuffleDiagSnd a b (b + 1) ≠ 1
            rw [shuffleDiagSnd_at_b_add_one hab₀]
            omega)
      · refine ⟨(2 : Fin 3), ?_⟩
        refine (shuffle_mem_range_objEquiv_δ_iff.{u}
          (shuffleDiagW'_objEquiv_injective.{u} hab₀ hb)
          ⟨b + 1, by omega⟩).2 ⟨?_, ?_⟩
        · refine (shuffleDiagW'_mem_range_iff.{u} hab₀ hb).2 ⟨?_, ?_⟩
          · exact (mem_range_shuffleTau_objEquiv.{u} hab₀ hb).2
              (Or.inr (Or.inr
                ⟨rfl, Nat.le_of_lt (Nat.lt_of_not_ge hv2)⟩))
          · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab₀ hb (by
              change shuffleSnd a b (a + 1) ≠ 2
              rw [shuffleSnd_at_succ_a hab₀]
              omega)
        · exact shuffle_pair_ne_diagW'_of_fst_ne.{u} hab₀ hb (by
            change shuffleDiagFst' b (b + 1) ≠ v.val
            unfold shuffleDiagFst'
            split_ifs <;> omega)
  apply le_antisymm
  · rw [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl,
      Subcomplex.ofSimplex_le_iff]
    intro hmem
    unfold shuffleDiagFilt2 at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · exact hmissInit h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨a', b', hab', hb', hcode, hmem'⟩ := hI
      have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
            ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 1, by omega⟩
              (shuffleDiagW'.{u} n a b hab₀ hb))) ⊆
          Set.range (prodStdSimplex.objEquiv.{u}
            (shuffleDiagW'.{u} n a' b' (le_of_lt hab') hb')) :=
        (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
          ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
      rcases shuffleCode_lt_cases hb' hb hcode with hgt | ⟨rfl, hgt⟩
      · have hnot : (⟨a, by omega⟩, (0 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleDiagW'.{u} n a' b' (le_of_lt hab') hb')) := by
          intro hmem''
          have hτ : (⟨a, by omega⟩, (0 : Fin 3)) ∈ Set.range
                (prodStdSimplex.objEquiv.{u}
                  (shuffleTau.{u} n a' b' (le_of_lt hab') hb')) :=
            ((shuffleDiagW'_mem_range_iff.{u}
              (le_of_lt hab') hb').1 hmem'').1
          rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
            at hτ
          rcases hτ with ⟨-, hbad⟩ | ⟨hbad, -, -⟩ | ⟨hbad, -⟩
          · change a ≤ a' at hbad
            omega
          · exact (by decide : ¬ ((0 : Fin 3)).val = 1) hbad
          · exact (by decide : ¬ ((0 : Fin 3)).val = 2) hbad
        exact hnot (hle2 hA0)
      · have hnot : (⟨b, by omega⟩, (1 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleDiagW'.{u} n a' b' (le_of_lt hab') hb')) := by
          intro hmem''
          have hτ : (⟨b, by omega⟩, (1 : Fin 3)) ∈ Set.range
                (prodStdSimplex.objEquiv.{u}
                  (shuffleTau.{u} n a' b' (le_of_lt hab') hb')) :=
            ((shuffleDiagW'_mem_range_iff.{u}
              (le_of_lt hab') hb').1 hmem'').1
          rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
            at hτ
          rcases hτ with ⟨hbad, -⟩ | ⟨-, -, hbad⟩ | ⟨hbad, -⟩
          · exact (by decide : ¬ ((1 : Fin 3)).val = 0) hbad
          · change b ≤ b' at hbad
            omega
          · exact (by decide : ¬ ((1 : Fin 3)).val = 2) hbad
        exact hnot (hle2 hB1)
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    have hjval : j.val ≠ b + 1 := by
      have hne : j ≠ ⟨b + 1, by omega⟩ :=
        Set.mem_compl_singleton_iff.1 hj
      exact fun e ↦ hne (Fin.ext e)
    rw [← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl]
    by_cases hjb : j.val = b
    · by_cases hba : b = a + 1
      · refine (shuffle_ofSimplex_le_top_prod_horn_of_snd_miss
            (i := (2 : Fin 3)) (w := (1 : Fin 3)) (by decide)
            ?_).trans
          ((Subcomplex.top_prod_le_unionProd _ _).trans
            (shuffleInit2_le_shuffleDiagFilt2 _))
        intro t htEq
        have hval : shuffleDiagSnd a b (j.succAbove t).val = 1 := by
          have h2 := congrArg Fin.val htEq
          rw [shuffle_objEquiv_δ_apply,
            shuffleDiagW'_objEquiv_snd_val hab₀ hb] at h2
          exact h2
        have hu := shuffleDiagSnd_eq_one.1 hval
        have hne : (j.succAbove t).val ≠ b := by
          rw [← hjb]
          exact fun e ↦ Fin.succAbove_ne j t (Fin.ext e)
        omega
      · have hab1 : a + 1 < b := by omega
        have hab1' : a < b - 1 := by omega
        have hmem2 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
              (shuffleDiagW'.{u} n a b hab₀ hb) ∈
            (Subcomplex.ofSimplex
              (shuffleDiagW'.{u} n a (b - 1) (le_of_lt hab1')
                (by omega))).obj _ := by
          have h1 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b, by omega⟩
                (shuffleDiagW'.{u} n a (b - 1) (le_of_lt hab1')
                  (by omega)) ∈
              (Subcomplex.ofSimplex
                (shuffleDiagW'.{u} n a (b - 1) (le_of_lt hab1')
                  (by omega))).obj _ :=
            (Subcomplex.ofSimplex _).map _
              (Subcomplex.mem_ofSimplex_obj _)
          have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                (shuffleDiagW'.{u} n a b hab₀ hb) =
              (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b, by omega⟩
                (shuffleDiagW'.{u} n a (b - 1) (le_of_lt hab1')
                  (by omega)) := by
            have hjj : j = ⟨b, Nat.lt_succ_of_le
                  (le_trans hb (Nat.le_succ _))⟩ := Fin.ext hjb
            subst hjj
            exact shuffleDiagW'_δ_pred hab1 hb
          exact hEq.symm ▸ h1
        have hlt : shuffleCode n a (b - 1) < shuffleCode n a b := by
          have h1 := shuffleCode_succ_right n a (b - 1)
          have h2 : b - 1 + 1 = b := by omega
          rw [h2] at h1
          omega
        exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem2).trans
          (ofSimplex_shuffleDiagW'_le_shuffleDiagFilt2 hab1'
            (by omega) hlt)
    · exact (shuffleDiagW'_δ_ofSimplex_le_boundary_prod_top
          hab₀ hb ⟨hjb, hjval⟩).trans
        ((Subcomplex.prod_top_le_unionProd _ _).trans
          (shuffleInit2_le_shuffleDiagFilt2 _))

end ShuffleDiagPreimage2

/-!
## Extension over the diagonal stage (horn two)

The special edge of the `b = n` diagonal attaching horns is
`v₂`; upward induction over the code extends a map out of
`S₂` over all diagonals.
-/

section ShuffleDiagExtension2

variable {n : ℕ} {C : SSet.{u}}

lemma shuffleVert2_mem_shuffleDiagFilt2 (m : ℕ) :
    shuffleVert2 n ∈ (shuffleDiagFilt2 n m).obj _ :=
  (shuffleInit2_le_shuffleDiagFilt2 m) _
    (shuffleVert2_mem_shuffleInit2 n)

/-- The horn lift for `W'_{a,m+1}` sends the last-edge
simplex of `Λ[m+2, m+2]` to `v₂`. -/
lemma shuffleDiagW'HornLift_app_rightHornEdgeSimplex (m a : ℕ)
    (ha : a < m + 1) :
    (Subcomplex.hornLift
        (shuffleDiagFilt2 (m + 1)
          (shuffleCode (m + 1) a (m + 1)))
        (shuffleDiagW' (m + 1) a (m + 1) (le_of_lt ha) (le_refl _))
        ⟨(m + 1) + 1, by omega⟩
        (shuffleDiagFilt2_preimage_shuffleDiagW'Map ha
          (le_refl _))).app _
        (rightHornEdgeSimplex.{u} m) =
      ⟨shuffleVert2 (m + 1),
        shuffleVert2_mem_shuffleDiagFilt2 _⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift
          (shuffleDiagFilt2 (m + 1)
            (shuffleCode (m + 1) a (m + 1)))
          (shuffleDiagW' (m + 1) a (m + 1) (le_of_lt ha)
            (le_refl _))
          ⟨(m + 1) + 1, by omega⟩
          (shuffleDiagFilt2_preimage_shuffleDiagW'Map ha
            (le_refl _))).app _
          (rightHornEdgeSimplex.{u} m)).val
      = (shuffleDiagW'Map.{u} (m + 1) a (m + 1) (le_of_lt ha)
            (le_refl _)).app _
          (stdSimplex.edge (m + 2) ⟨m + 1, by omega⟩
            ⟨m + 2, by omega⟩ (by simp [Fin.le_def])) :=
        congr($(Subcomplex.hornLift_ι
          (shuffleDiagFilt2_preimage_shuffleDiagW'Map ha
            (le_refl _))).app _
            (rightHornEdgeSimplex.{u} m))
    _ = shuffleVert2 (m + 1) :=
        shuffleDiagW'Map_last_app_edge ha

/-- The last edge of the `b = n` diagonal horn map is the
image of `v₂`. -/
lemma rightHornEdge_shuffleDiagW'HornLift_comp (m a : ℕ)
    (ha : a < m + 1)
    (φ : ((shuffleDiagFilt2 (m + 1)
        (shuffleCode (m + 1) a (m + 1)) :
        (Δ[m + 1] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (rightHornEdge
        (Subcomplex.hornLift
          (shuffleDiagFilt2 (m + 1)
            (shuffleCode (m + 1) a (m + 1)))
          (shuffleDiagW' (m + 1) a (m + 1) (le_of_lt ha)
            (le_refl _))
          ⟨(m + 1) + 1, by omega⟩
          (shuffleDiagFilt2_preimage_shuffleDiagW'Map ha
            (le_refl _)) ≫ φ)).edge =
      φ.app _ ⟨shuffleVert2 (m + 1),
        shuffleVert2_mem_shuffleDiagFilt2 _⟩ :=
  congrArg (φ.app _)
    (shuffleDiagW'HornLift_app_rightHornEdgeSimplex m a ha)

/-- The `b = n` diagonal horn is special as soon as `v₂` of
the initial datum is an equivalence. -/
lemma isEquivalence_rightHornEdge_shuffleDiagStep (m a : ℕ)
    (ha : a < m + 1)
    {φ : ((shuffleDiagFilt2 (m + 1)
        (shuffleCode (m + 1) a (m + 1)) :
        (Δ[m + 1] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((shuffleInit2 (m + 1) :
        (Δ[m + 1] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE
        (shuffleInit2_le_shuffleDiagFilt2 _) ≫ φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 (m + 1),
        shuffleVert2_mem_shuffleInit2 (m + 1)⟩)).IsEquivalence) :
    (rightHornEdge
        (Subcomplex.hornLift
          (shuffleDiagFilt2 (m + 1)
            (shuffleCode (m + 1) a (m + 1)))
          (shuffleDiagW' (m + 1) a (m + 1) (le_of_lt ha)
            (le_refl _))
          ⟨(m + 1) + 1, by omega⟩
          (shuffleDiagFilt2_preimage_shuffleDiagW'Map ha
            (le_refl _)) ≫ φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      rightHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨shuffleVert2 (m + 1),
          shuffleVert2_mem_shuffleInit2 (m + 1)⟩)) ?_).2 hVert
  rw [rightHornEdge_shuffleDiagW'HornLift_comp m a ha]
  exact congr($(hrestr).app _ ⟨shuffleVert2 (m + 1),
    shuffleVert2_mem_shuffleInit2 (m + 1)⟩)

private lemma exists_extension_shuffleDiagFilt2 [Quasicategory C]
    (φ₀ : ((shuffleInit2 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence) :
    ∀ (m : ℕ), m ≤ (n + 1) * (n + 1) →
      ∃ φm : ((shuffleDiagFilt2 n m :
          (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (shuffleInit2_le_shuffleDiagFilt2 m) ≫
          φm = φ₀ := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨(Subcomplex.eqToIso (shuffleDiagFilt2_zero (n := n))).hom ≫
      φ₀, ?_⟩
    have hid : Subcomplex.homOfLE
          (shuffleInit2_le_shuffleDiagFilt2 (n := n) 0) ≫
          (Subcomplex.eqToIso (shuffleDiagFilt2_zero (n := n))).hom =
        𝟙 _ := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (shuffleInit2 n).ι]
      simp
    rw [← Category.assoc, hid, Category.id_comp]
  | succ m ih =>
    intro hm
    obtain ⟨φ₁, hφ₁⟩ := ih (by omega)
    by_cases hvalid : ∃ a b : ℕ, a < b ∧ b ≤ n ∧
        shuffleCode n a b = m
    · obtain ⟨a, b, hab, hb, hcode⟩ := hvalid
      have hab₀ : a ≤ b := le_of_lt hab
      have hpre := shuffleDiagFilt2_preimage_shuffleDiagW'Map hab hb
      rw [hcode] at hpre
      obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 1] ⟶ C,
          Subcomplex.hornLift (shuffleDiagFilt2 n m)
              (shuffleDiagW' n a b hab₀ hb)
              (⟨b + 1, by omega⟩ : Fin (n + 2)) hpre ≫ φ₁ =
            Λ[n + 1, (⟨b + 1, by omega⟩ : Fin (n + 2))].ι ≫ σC := by
        by_cases hbn : b = n
        · obtain rfl : n = b := hbn.symm
          obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
          have hm_eq : m = shuffleCode (m' + 1) a (m' + 1) :=
            hcode.symm
          subst hm_eq
          refine exists_fill_horn_right_of_isEquivalence _ ?_
          exact isEquivalence_rightHornEdge_shuffleDiagStep m' a
            hab hφ₁ hVert
        · have hk0 : (0 : Fin (n + 2)) <
              (⟨b + 1, by omega⟩ : Fin (n + 2)) := by
            rw [Fin.lt_def]
            change (0 : ℕ) < b + 1
            omega
          have hkn : (⟨b + 1, by omega⟩ : Fin (n + 2)) <
              Fin.last (n + 1) := by
            rw [Fin.lt_def, Fin.val_last]
            change b + 1 < n + 1
            omega
          exact Quasicategory.hornFilling hk0 hkn _
      obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
        (fun h ↦ shuffleDiagW'Map_app_injective.{u} hab₀ hb h)
        φ₁ σC hσC
      have hstep : shuffleDiagFilt2 n (m + 1) =
          shuffleDiagFilt2 n m ⊔
            Subcomplex.ofSimplex
              (shuffleDiagW'.{u} n a b hab₀ hb) := by
        rw [← hcode]
        exact shuffleDiagFilt2_eq_succ_sup hab hb
      refine ⟨(Subcomplex.eqToIso hstep).hom ≫ φ', ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit2_le_shuffleDiagFilt2 (m + 1)) ≫
            (Subcomplex.eqToIso hstep).hom =
          Subcomplex.homOfLE
              (shuffleInit2_le_shuffleDiagFilt2 m) ≫
            Subcomplex.homOfLE (show shuffleDiagFilt2 n m ≤
              shuffleDiagFilt2 n m ⊔
                Subcomplex.ofSimplex
                  (shuffleDiagW'.{u} n a b hab₀ hb)
              from le_sup_left) := by
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
      exact hφ₁
    · have hEq : shuffleDiagFilt2 n (m + 1) =
          shuffleDiagFilt2 n m :=
        shuffleDiagFilt2_eq_succ_of_not_valid (fun a b hab hb hcode ↦
          hvalid ⟨a, b, hab, hb, hcode⟩)
      refine ⟨(Subcomplex.eqToIso hEq).hom ≫ φ₁, ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit2_le_shuffleDiagFilt2 (m + 1)) ≫
            (Subcomplex.eqToIso hEq).hom =
          Subcomplex.homOfLE
            (shuffleInit2_le_shuffleDiagFilt2 m) := by
        rw [Subcomplex.eqToIso_hom,
          ← cancel_mono (shuffleDiagFilt2 n m).ι]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp]
      exact hφ₁

/-- Extension of the initial datum over the full diagonal
stage `shuffleDiagFilt2 n ((n+1)·(n+1))`. -/
lemma exists_extension_shuffleDiagFilt2_bound [Quasicategory C]
    (φ₀ : ((shuffleInit2 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence) :
    ∃ φD : ((shuffleDiagFilt2 n ((n + 1) * (n + 1)) :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
      Subcomplex.homOfLE
          (shuffleInit2_le_shuffleDiagFilt2 _) ≫ φD = φ₀ :=
  exists_extension_shuffleDiagFilt2 φ₀ hVert _ (le_refl _)

end ShuffleDiagExtension2

/-!
## The horn-two top filtration and its attaching horn

`shuffleTopFilt2 n m` is the diagonal stage at the bound
together with the shuffles of code `< m`. The attaching horn
of `τ_{a,b}` is `Λ[n+2, b+2]`.
-/

section ShuffleTopFilt2

variable {n : ℕ}

/-- The increasing top filtration for horn two: all diagonals
(stage at the bound) together with `τ_{a,b}` for
`code(a,b) < m`. -/
noncomputable def shuffleTopFilt2 (n m : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex :=
  shuffleDiagFilt2 n ((n + 1) * (n + 1)) ⊔
    ⨆ (a : ℕ) (b : ℕ) (hab : a ≤ b) (hb : b ≤ n)
      (_ : shuffleCode n a b < m),
      Subcomplex.ofSimplex (shuffleTau n a b hab hb)

lemma shuffleDiagFilt2_bound_le_shuffleTopFilt2 (m : ℕ) :
    shuffleDiagFilt2 n ((n + 1) * (n + 1)) ≤
      shuffleTopFilt2 n m := by
  unfold shuffleTopFilt2
  exact le_sup_left

lemma shuffleInit2_le_shuffleTopFilt2 (m : ℕ) :
    shuffleInit2 n ≤ shuffleTopFilt2 n m :=
  (shuffleInit2_le_shuffleDiagFilt2 _).trans
    (shuffleDiagFilt2_bound_le_shuffleTopFilt2 m)

lemma ofSimplex_shuffleTau_le_shuffleTopFilt2 {m a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ n) (h : shuffleCode n a b < m) :
    Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb) ≤
      shuffleTopFilt2 n m := by
  unfold shuffleTopFilt2
  refine (le_iSup_of_le a ?_).trans le_sup_right
  exact le_iSup_of_le b (le_iSup_of_le hab
    (le_iSup_of_le hb (le_iSup_of_le h le_rfl)))

lemma shuffleTopFilt2_le_succ (m : ℕ) :
    shuffleTopFilt2 n m ≤ shuffleTopFilt2 n (m + 1) := by
  unfold shuffleTopFilt2
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro h
  exact ofSimplex_shuffleTau_le_shuffleTopFilt2 hab hb
    (Nat.lt_succ_of_lt h)

/-- One top filtration step at a valid code. -/
lemma shuffleTopFilt2_eq_succ_sup {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ n) :
    shuffleTopFilt2 n (shuffleCode n a b + 1) =
      shuffleTopFilt2 n (shuffleCode n a b) ⊔
        Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb) := by
  apply le_antisymm
  · unfold shuffleTopFilt2
    apply sup_le (le_sup_left.trans le_sup_left)
    apply iSup_le
    intro a'
    apply iSup_le
    intro b'
    apply iSup_le
    intro hab'
    apply iSup_le
    intro hb'
    apply iSup_le
    intro hcode
    by_cases hcc : shuffleCode n a' b' = shuffleCode n a b
    · obtain ⟨rfl, rfl⟩ := shuffleCode_inj hb' hb hcc
      exact le_sup_right
    · have hlt : shuffleCode n a' b' < shuffleCode n a b := by
        omega
      refine (le_iSup_of_le a' ?_).trans
        (le_sup_right.trans le_sup_left)
      exact le_iSup_of_le b' (le_iSup_of_le hab'
        (le_iSup_of_le hb' (le_iSup_of_le hlt le_rfl)))
  · exact sup_le (shuffleTopFilt2_le_succ _)
      (ofSimplex_shuffleTau_le_shuffleTopFilt2 hab hb
        (Nat.lt_succ_self _))

/-- Invalid codes are skipped. -/
lemma shuffleTopFilt2_eq_succ_of_not_valid {m : ℕ}
    (h : ∀ a b : ℕ, a ≤ b → b ≤ n → shuffleCode n a b ≠ m) :
    shuffleTopFilt2 n (m + 1) = shuffleTopFilt2 n m := by
  apply le_antisymm _ (shuffleTopFilt2_le_succ m)
  unfold shuffleTopFilt2
  apply sup_le le_sup_left
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  have hlt : shuffleCode n a b < m := by
    have hne := h a b hab hb
    omega
  exact ofSimplex_shuffleTau_le_shuffleTopFilt2 hab hb hlt

/-- The bottom of the top filtration is the diagonal stage. -/
lemma shuffleTopFilt2_zero :
    shuffleTopFilt2 n 0 = shuffleDiagFilt2 n ((n + 1) * (n + 1)) := by
  refine le_antisymm ?_ le_sup_left
  unfold shuffleTopFilt2
  refine sup_le le_rfl ?_
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hb
  apply iSup_le
  intro hcode
  exact absurd hcode (Nat.not_lt_zero _)

/-- The top of the top filtration is the whole prism. -/
lemma shuffleTopFilt2_bound :
    shuffleTopFilt2 n ((n + 1) * (n + 1)) = ⊤ := by
  refine (prodStdSimplex.subcomplex_eq_top_iff _ rfl).2 ?_
  intro x hx
  obtain ⟨a, b, hab, hb, hτ⟩ :=
    exists_shuffleTau_of_nonDegenerate hx
  rw [← hτ]
  exact ofSimplex_shuffleTau_le_shuffleTopFilt2 hab hb
    (shuffleCode_lt_bound hab hb) _
    (Subcomplex.mem_ofSimplex_obj _)

end ShuffleTopFilt2

section ShuffleTopPreimage2

variable {n a b : ℕ}

/-- **Attaching horn, top phase, horn two**: the preimage of
`shuffleTopFilt2 n (code(a,b))` under `τ_{a,b}` is
`Λ[n+2, b+2]`. -/
lemma shuffleTopFilt2_preimage_shuffleTauMap (hab : a ≤ b)
    (hb : b ≤ n) :
    (shuffleTopFilt2 n (shuffleCode n a b)).preimage
        (shuffleTauMap.{u} n a b hab hb) =
      (Λ[n + 2, ⟨b + 2, by omega⟩] :
        (Δ[n + 2] : SSet.{u}).Subcomplex) := by
  -- Range witnesses in the missing face `δ_{b+2} τ_{a,b}`.
  have hA0 : (⟨a, by omega⟩, (0 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
          (shuffleTau.{u} n a b hab hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleTau_objEquiv_injective.{u} hab hb)
      ⟨b + 2, by omega⟩).2 ⟨?_, ?_⟩
    · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
        (Or.inl ⟨rfl, le_rfl⟩)
    · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
        change shuffleSnd a b (b + 2) ≠ 0
        rw [shuffleSnd_at_b_add_two hab]
        omega)
  have hA1 : (⟨a, by omega⟩, (1 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
          (shuffleTau.{u} n a b hab hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleTau_objEquiv_injective.{u} hab hb)
      ⟨b + 2, by omega⟩).2 ⟨?_, ?_⟩
    · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
        (Or.inr (Or.inl ⟨rfl, le_rfl, hab⟩))
    · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
        change shuffleSnd a b (b + 2) ≠ 1
        rw [shuffleSnd_at_b_add_two hab]
        omega)
  have hB1 : (⟨b, by omega⟩, (1 : Fin 3)) ∈ Set.range
      (prodStdSimplex.objEquiv.{u}
        ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
          (shuffleTau.{u} n a b hab hb))) := by
    refine (shuffle_mem_range_objEquiv_δ_iff.{u}
      (shuffleTau_objEquiv_injective.{u} hab hb)
      ⟨b + 2, by omega⟩).2 ⟨?_, ?_⟩
    · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
        (Or.inr (Or.inl ⟨rfl, hab, le_rfl⟩))
    · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
        change shuffleSnd a b (b + 2) ≠ 1
        rw [shuffleSnd_at_b_add_two hab]
        omega)
  -- The missing face is in no horn-two diagonal.
  have hmissDiag : ∀ {a' b' : ℕ} (hab' : a' < b') (hb' : b' ≤ n),
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
          (shuffleTau.{u} n a b hab hb) ∉
        (Subcomplex.ofSimplex
          (shuffleDiagW'.{u} n a' b' (le_of_lt hab') hb')).obj _ := by
    intro a' b' hab' hb' hmem'
    have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
          ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
            (shuffleTau.{u} n a b hab hb))) ⊆
        Set.range (prodStdSimplex.objEquiv.{u}
          (shuffleDiagW'.{u} n a' b' (le_of_lt hab') hb')) :=
      (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
        ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
    by_cases hlt : a' < a
    · have hnot : (⟨a, by omega⟩, (0 : Fin 3)) ∉ Set.range
          (prodStdSimplex.objEquiv.{u}
            (shuffleDiagW'.{u} n a' b' (le_of_lt hab') hb')) := by
        intro hmem''
        have hτ : (⟨a, by omega⟩, (0 : Fin 3)) ∈ Set.range
              (prodStdSimplex.objEquiv.{u}
                (shuffleTau.{u} n a' b' (le_of_lt hab') hb')) :=
          ((shuffleDiagW'_mem_range_iff.{u}
            (le_of_lt hab') hb').1 hmem'').1
        rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
          at hτ
        rcases hτ with ⟨-, hbad⟩ | ⟨hbad, -, -⟩ | ⟨hbad, -⟩
        · change a ≤ a' at hbad
          omega
        · exact (by decide : ¬ ((0 : Fin 3)).val = 1) hbad
        · exact (by decide : ¬ ((0 : Fin 3)).val = 2) hbad
      exact hnot (hle2 hA0)
    · have hnot : (⟨a, by omega⟩, (1 : Fin 3)) ∉ Set.range
          (prodStdSimplex.objEquiv.{u}
            (shuffleDiagW'.{u} n a' b' (le_of_lt hab') hb')) := by
        intro hmem''
        have hτ := (shuffleDiagW'_mem_range_iff.{u}
          (le_of_lt hab') hb').1 hmem''
        obtain ⟨hτ1, hτ2⟩ := hτ
        rw [mem_range_shuffleTau_objEquiv.{u} (le_of_lt hab') hb']
          at hτ1
        rcases hτ1 with ⟨hbad, -⟩ | ⟨-, hbad, -⟩ | ⟨hbad, -⟩
        · exact (by decide : ¬ ((1 : Fin 3)).val = 0) hbad
        · change a' ≤ a at hbad
          have haa : a' = a := by omega
          apply hτ2
          have hEq : prodStdSimplex.objEquiv.{u}
                (shuffleTau.{u} n a' b' (le_of_lt hab') hb')
                ⟨a' + 1, by omega⟩ =
              (⟨a, by omega⟩, (1 : Fin 3)) :=
            (shuffleTau_objEquiv_apply_eq_iff.{u} (le_of_lt hab')
              hb' ⟨a' + 1, by omega⟩).2 ⟨by
                change shuffleFst a' b' (a' + 1) = a
                rw [shuffleFst_at_succ_a (le_of_lt hab'), haa], by
                change shuffleSnd a' b' (a' + 1) = 1
                exact shuffleSnd_at_succ_a (le_of_lt hab')⟩
          exact hEq.symm
        · exact (by decide : ¬ ((1 : Fin 3)).val = 2) hbad
      exact hnot (hle2 hA1)
  have hmissDiagTop :
      (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
          (shuffleTau.{u} n a b hab hb) ∉
        (shuffleDiagFilt2 n ((n + 1) * (n + 1))).obj _ := by
    intro hmem
    unfold shuffleDiagFilt2 at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · have hmissInit :
          (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
              (shuffleTau.{u} n a b hab hb) ∉
            (shuffleInit2 n).obj _ := by
        refine shuffle_notMem_shuffleInit2_of_range ?_
          ⟨⟨a, by omega⟩, hA0⟩ ⟨⟨a, by omega⟩, hA1⟩
        intro v
        by_cases hv1 : v.val ≤ a
        · refine ⟨(0 : Fin 3), ?_⟩
          refine (shuffle_mem_range_objEquiv_δ_iff.{u}
            (shuffleTau_objEquiv_injective.{u} hab hb)
            ⟨b + 2, by omega⟩).2 ⟨?_, ?_⟩
          · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
              (Or.inl ⟨rfl, hv1⟩)
          · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
              change shuffleSnd a b (b + 2) ≠ 0
              rw [shuffleSnd_at_b_add_two hab]
              omega)
        · by_cases hv2 : v.val ≤ b
          · refine ⟨(1 : Fin 3), ?_⟩
            refine (shuffle_mem_range_objEquiv_δ_iff.{u}
              (shuffleTau_objEquiv_injective.{u} hab hb)
              ⟨b + 2, by omega⟩).2 ⟨?_, ?_⟩
            · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
                (Or.inr (Or.inl
                  ⟨rfl, Nat.le_of_lt (Nat.lt_of_not_ge hv1), hv2⟩))
            · exact shuffle_pair_ne_tau_of_snd_ne.{u} hab hb (by
                change shuffleSnd a b (b + 2) ≠ 1
                rw [shuffleSnd_at_b_add_two hab]
                omega)
          · refine ⟨(2 : Fin 3), ?_⟩
            refine (shuffle_mem_range_objEquiv_δ_iff.{u}
              (shuffleTau_objEquiv_injective.{u} hab hb)
              ⟨b + 2, by omega⟩).2 ⟨?_, ?_⟩
            · exact (mem_range_shuffleTau_objEquiv.{u} hab hb).2
                (Or.inr (Or.inr
                  ⟨rfl, Nat.le_of_lt (Nat.lt_of_not_ge hv2)⟩))
            · exact shuffle_pair_ne_tau_of_fst_ne.{u} hab hb (by
                change shuffleFst a b (b + 2) ≠ v.val
                rw [shuffleFst_at_b_add_two hab]
                omega)
      exact hmissInit h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨a', b', hab', hb', -, hmem'⟩ := hI
      exact hmissDiag hab' hb' hmem'
  apply le_antisymm
  · rw [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl,
      Subcomplex.ofSimplex_le_iff]
    intro hmem
    unfold shuffleTopFilt2 at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · exact hmissDiagTop h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨a', b', hab', hb', hcode, hmem'⟩ := hI
      have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
            ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 2, by omega⟩
              (shuffleTau.{u} n a b hab hb))) ⊆
          Set.range (prodStdSimplex.objEquiv.{u}
            (shuffleTau.{u} n a' b' hab' hb')) :=
        (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
          ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
      rcases shuffleCode_lt_cases hb' hb hcode with hgt | ⟨rfl, hgt⟩
      · have hnot : (⟨a, by omega⟩, (0 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleTau.{u} n a' b' hab' hb')) := by
          intro hmem''
          rw [mem_range_shuffleTau_objEquiv.{u} hab' hb'] at hmem''
          rcases hmem'' with ⟨-, hbad⟩ | ⟨hbad, -, -⟩ | ⟨hbad, -⟩
          · change a ≤ a' at hbad
            omega
          · exact (by decide : ¬ ((0 : Fin 3)).val = 1) hbad
          · exact (by decide : ¬ ((0 : Fin 3)).val = 2) hbad
        exact hnot (hle2 hA0)
      · have hnot : (⟨b, by omega⟩, (1 : Fin 3)) ∉ Set.range
            (prodStdSimplex.objEquiv.{u}
              (shuffleTau.{u} n a' b' hab' hb')) := by
          intro hmem''
          rw [mem_range_shuffleTau_objEquiv.{u} hab' hb'] at hmem''
          rcases hmem'' with ⟨hbad, -⟩ | ⟨-, -, hbad⟩ | ⟨hbad, -⟩
          · exact (by decide : ¬ ((1 : Fin 3)).val = 0) hbad
          · change b ≤ b' at hbad
            omega
          · exact (by decide : ¬ ((1 : Fin 3)).val = 2) hbad
        exact hnot (hle2 hB1)
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    have hjval : j.val ≠ b + 2 := by
      have hne : j ≠ ⟨b + 2, by omega⟩ :=
        Set.mem_compl_singleton_iff.1 hj
      exact fun e ↦ hne (Fin.ext e)
    rw [← Subcomplex.image_le_iff,
      shuffle_image_face_singleton_compl]
    by_cases hj0 : j.val = a
    · by_cases ha0 : a = 0
      · refine (shuffle_ofSimplex_le_top_prod_horn_of_snd_miss
            (i := (2 : Fin 3)) (w := (0 : Fin 3)) (by decide)
            ?_).trans
          ((Subcomplex.top_prod_le_unionProd _ _).trans
            (shuffleInit2_le_shuffleTopFilt2 _))
        intro t htEq
        have hval : shuffleSnd a b (j.succAbove t).val = 0 := by
          have h2 := congrArg Fin.val htEq
          rw [shuffle_objEquiv_δ_apply,
            shuffleTau_objEquiv_snd_val hab hb] at h2
          exact h2
        have hu := shuffleSnd_eq_zero.1 hval
        have hne : (j.succAbove t).val ≠ a := by
          rw [← hj0]
          exact fun e ↦ Fin.succAbove_ne j t (Fin.ext e)
        omega
      · have ha1 : 1 ≤ a := by omega
        have hmem2 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
              (shuffleTau.{u} n a b hab hb) ∈
            (Subcomplex.ofSimplex
              (shuffleTau.{u} n (a - 1) b (by omega) hb)).obj _ := by
          have h1 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
                (shuffleTau.{u} n (a - 1) b (by omega) hb) ∈
              (Subcomplex.ofSimplex
                (shuffleTau.{u} n (a - 1) b (by omega) hb)).obj _ :=
            (Subcomplex.ofSimplex _).map _
              (Subcomplex.mem_ofSimplex_obj _)
          have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                (shuffleTau.{u} n a b hab hb) =
              (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨a, by omega⟩
                (shuffleTau.{u} n (a - 1) b (by omega) hb) := by
            have hjj : j = ⟨a, Nat.lt_succ_of_le
                  (le_trans (Nat.le_succ_of_le (le_trans hab hb))
                    (Nat.le_succ _))⟩ := Fin.ext hj0
            subst hjj
            exact shuffleTau_δ_pred_left ha1 hab hb
          exact hEq.symm ▸ h1
        have hlt : shuffleCode n (a - 1) b < shuffleCode n a b :=
          shuffleCode_lt_of_fst_lt (b' := b) (by omega) hb
        exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem2).trans
          (ofSimplex_shuffleTau_le_shuffleTopFilt2 (by omega) hb hlt)
    · by_cases hj1 : j.val = a + 1
      · by_cases hba : a = b
        · refine (shuffle_ofSimplex_le_top_prod_horn_of_snd_miss
              (i := (2 : Fin 3)) (w := (1 : Fin 3)) (by decide)
              ?_).trans
            ((Subcomplex.top_prod_le_unionProd _ _).trans
              (shuffleInit2_le_shuffleTopFilt2 _))
          intro t htEq
          have hval : shuffleSnd a b (j.succAbove t).val = 1 := by
            have h2 := congrArg Fin.val htEq
            rw [shuffle_objEquiv_δ_apply,
              shuffleTau_objEquiv_snd_val hab hb] at h2
            exact h2
          have hu := shuffleSnd_eq_one.1 hval
          have hne : (j.succAbove t).val ≠ a + 1 := by
            rw [← hj1]
            exact fun e ↦ Fin.succAbove_ne j t (Fin.ext e)
          omega
        · have hablt : a < b := lt_of_le_of_ne hab hba
          have hmem2 : Subcomplex.ofSimplex
                ((Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                  (shuffleTau.{u} n a b hab hb)) ≤
              shuffleDiagFilt2 n ((n + 1) * (n + 1)) := by
            have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                  (shuffleTau.{u} n a b hab hb) =
                shuffleDiagW'.{u} n a b hab hb := by
              have hjj : j = ⟨a + 1, Nat.lt_succ_of_le
                    (le_trans (Nat.succ_le_succ (le_trans hab hb))
                      (Nat.le_succ _))⟩ := Fin.ext hj1
              subst hjj
              rfl
            have hW : Subcomplex.ofSimplex
                  (shuffleDiagW'.{u} n a b hab hb) ≤
                shuffleDiagFilt2 n ((n + 1) * (n + 1)) :=
              ofSimplex_shuffleDiagW'_le_shuffleDiagFilt2 hablt hb
                (shuffleCode_lt_bound hab hb)
            exact hEq.symm ▸ hW
          exact hmem2.trans
            (shuffleDiagFilt2_bound_le_shuffleTopFilt2 _)
      · by_cases hj2 : j.val = b + 1
        · have hablt : a < b := by omega
          have hmem2 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                (shuffleTau.{u} n a b hab hb) ∈
              (Subcomplex.ofSimplex
                (shuffleTau.{u} n a (b - 1) (by omega)
                  (by omega))).obj _ := by
            have h1 : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ
                  ⟨b + 1, by omega⟩
                  (shuffleTau.{u} n a (b - 1) (by omega)
                    (by omega)) ∈
                (Subcomplex.ofSimplex
                  (shuffleTau.{u} n a (b - 1) (by omega)
                    (by omega))).obj _ :=
              (Subcomplex.ofSimplex _).map _
                (Subcomplex.mem_ofSimplex_obj _)
            have hEq : (Δ[n] ⊗ Δ[2] : SSet.{u}).δ j
                  (shuffleTau.{u} n a b hab hb) =
                (Δ[n] ⊗ Δ[2] : SSet.{u}).δ ⟨b + 1, by omega⟩
                  (shuffleTau.{u} n a (b - 1) (by omega)
                    (by omega)) := by
              have hjj : j = ⟨b + 1, Nat.lt_succ_of_le
                    (le_trans (Nat.succ_le_succ hb)
                      (Nat.le_succ _))⟩ := Fin.ext hj2
              subst hjj
              exact shuffleTau_δ_pred_right hablt hb
            exact hEq.symm ▸ h1
          have hlt : shuffleCode n a (b - 1) <
              shuffleCode n a b := by
            have h1 := shuffleCode_succ_right n a (b - 1)
            have h2 : b - 1 + 1 = b := by omega
            rw [h2] at h1
            omega
          exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem2).trans
            (ofSimplex_shuffleTau_le_shuffleTopFilt2 (by omega)
              (by omega) hlt)
        · exact (shuffleTau_δ_ofSimplex_le_boundary_prod_top
              hab hb ⟨hj0, hj1, hj2, hjval⟩).trans
            ((Subcomplex.prod_top_le_unionProd _ _).trans
              (shuffleInit2_le_shuffleTopFilt2 _))

end ShuffleTopPreimage2

/-!
## Extension over the top stage and horn two assembly

The special edge of the `b = n` top attaching horns is `v₂`;
upward induction over the code extends over all shuffles,
and transport across `shuffleTopFilt2 n ((n+1)·(n+1)) = ⊤`
gives `ShuffleHornTwoCellExtension`.
-/

section ShuffleTopExtension2

variable {n : ℕ} {C : SSet.{u}}

lemma shuffleVert2_mem_shuffleTopFilt2 (m : ℕ) :
    shuffleVert2 n ∈ (shuffleTopFilt2 n m).obj _ :=
  (shuffleInit2_le_shuffleTopFilt2 m) _
    (shuffleVert2_mem_shuffleInit2 n)

/-- The horn lift for `τ_{a,n}` sends the last-edge simplex
of `Λ[n+2, n+2]` to `v₂`. -/
lemma shuffleTopHornLift_app_rightHornEdgeSimplex (a : ℕ)
    (ha : a ≤ n) :
    (Subcomplex.hornLift
        (shuffleTopFilt2 n (shuffleCode n a n))
        (shuffleTau n a n ha (le_refl n))
        ⟨n + 2, by omega⟩
        (shuffleTopFilt2_preimage_shuffleTauMap ha
          (le_refl n))).app _
        (rightHornEdgeSimplex.{u} n) =
      ⟨shuffleVert2 n, shuffleVert2_mem_shuffleTopFilt2 _⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift
          (shuffleTopFilt2 n (shuffleCode n a n))
          (shuffleTau n a n ha (le_refl n))
          ⟨n + 2, by omega⟩
          (shuffleTopFilt2_preimage_shuffleTauMap ha
            (le_refl n))).app _
          (rightHornEdgeSimplex.{u} n)).val
      = (shuffleTauMap.{u} n a n ha (le_refl n)).app _
          (stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩
            ⟨n + 2, by omega⟩ (by simp [Fin.le_def])) :=
        congr($(Subcomplex.hornLift_ι
          (shuffleTopFilt2_preimage_shuffleTauMap ha
            (le_refl n))).app _
            (rightHornEdgeSimplex.{u} n))
    _ = shuffleVert2 n :=
        shuffleTauMap_last_app_edge ha

/-- The last edge of the `b = n` top horn map is the image
of `v₂`. -/
lemma rightHornEdge_shuffleTopHornLift_comp (a : ℕ)
    (ha : a ≤ n)
    (φ : ((shuffleTopFilt2 n (shuffleCode n a n) :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (rightHornEdge
        (Subcomplex.hornLift
          (shuffleTopFilt2 n (shuffleCode n a n))
          (shuffleTau n a n ha (le_refl n))
          ⟨n + 2, by omega⟩
          (shuffleTopFilt2_preimage_shuffleTauMap ha
            (le_refl n)) ≫ φ)).edge =
      φ.app _ ⟨shuffleVert2 n, shuffleVert2_mem_shuffleTopFilt2 _⟩ :=
  congrArg (φ.app _)
    (shuffleTopHornLift_app_rightHornEdgeSimplex a ha)

/-- The `b = n` top horn is special as soon as `v₂` of the
initial datum is an equivalence. -/
lemma isEquivalence_rightHornEdge_shuffleTopStep (a : ℕ)
    (ha : a ≤ n)
    {φ : ((shuffleTopFilt2 n (shuffleCode n a n) :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((shuffleInit2 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE
        (shuffleInit2_le_shuffleTopFilt2 _) ≫ φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence) :
    (rightHornEdge
        (Subcomplex.hornLift
          (shuffleTopFilt2 n (shuffleCode n a n))
          (shuffleTau n a n ha (le_refl n))
          ⟨n + 2, by omega⟩
          (shuffleTopFilt2_preimage_shuffleTauMap ha
            (le_refl n)) ≫ φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      rightHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨shuffleVert2 n,
          shuffleVert2_mem_shuffleInit2 n⟩)) ?_).2 hVert
  rw [rightHornEdge_shuffleTopHornLift_comp a ha]
  exact congr($(hrestr).app _ ⟨shuffleVert2 n,
    shuffleVert2_mem_shuffleInit2 n⟩)

private lemma exists_extension_shuffleTopFilt2 [Quasicategory C]
    (φ₀ : ((shuffleInit2 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence) :
    ∀ (m : ℕ), m ≤ (n + 1) * (n + 1) →
      ∃ φm : ((shuffleTopFilt2 n m :
          (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (shuffleInit2_le_shuffleTopFilt2 m) ≫
          φm = φ₀ := by
  intro m
  induction m with
  | zero =>
    intro _
    obtain ⟨φD, hφD⟩ :=
      exists_extension_shuffleDiagFilt2_bound φ₀ hVert
    refine ⟨(Subcomplex.eqToIso (shuffleTopFilt2_zero (n := n))).hom ≫
      φD, ?_⟩
    have hcomp : Subcomplex.homOfLE
          (shuffleInit2_le_shuffleTopFilt2 (n := n) 0) ≫
          (Subcomplex.eqToIso (shuffleTopFilt2_zero (n := n))).hom =
        Subcomplex.homOfLE (shuffleInit2_le_shuffleDiagFilt2 _) := by
      rw [Subcomplex.eqToIso_hom,
        ← cancel_mono (shuffleDiagFilt2 n ((n + 1) * (n + 1))).ι]
      simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcomp]
    exact hφD
  | succ m ih =>
    intro hm
    obtain ⟨φ₁, hφ₁⟩ := ih (by omega)
    by_cases hvalid : ∃ a b : ℕ, a ≤ b ∧ b ≤ n ∧
        shuffleCode n a b = m
    · obtain ⟨a, b, hab, hb, hcode⟩ := hvalid
      have hpre := shuffleTopFilt2_preimage_shuffleTauMap hab hb
      rw [hcode] at hpre
      obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 2] ⟶ C,
          Subcomplex.hornLift (shuffleTopFilt2 n m)
              (shuffleTau n a b hab hb)
              (⟨b + 2, by omega⟩ : Fin (n + 3)) hpre ≫ φ₁ =
            Λ[n + 2, (⟨b + 2, by omega⟩ : Fin (n + 3))].ι ≫ σC := by
        by_cases hbn : b = n
        · obtain rfl : n = b := hbn.symm
          have hm_eq : m = shuffleCode n a n := hcode.symm
          subst hm_eq
          refine exists_fill_horn_right_of_isEquivalence _ ?_
          exact isEquivalence_rightHornEdge_shuffleTopStep a
            hab hφ₁ hVert
        · have hk0 : (0 : Fin (n + 3)) <
              (⟨b + 2, by omega⟩ : Fin (n + 3)) := by
            rw [Fin.lt_def]
            change (0 : ℕ) < b + 2
            omega
          have hkn : (⟨b + 2, by omega⟩ : Fin (n + 3)) <
              Fin.last (n + 2) := by
            rw [Fin.lt_def, Fin.val_last]
            change b + 2 < n + 2
            omega
          exact Quasicategory.hornFilling hk0 hkn _
      obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
        (fun h ↦ shuffleTauMap_app_injective.{u} hab hb h)
        φ₁ σC hσC
      have hstep : shuffleTopFilt2 n (m + 1) =
          shuffleTopFilt2 n m ⊔
            Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb) := by
        rw [← hcode]
        exact shuffleTopFilt2_eq_succ_sup hab hb
      refine ⟨(Subcomplex.eqToIso hstep).hom ≫ φ', ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit2_le_shuffleTopFilt2 (m + 1)) ≫
            (Subcomplex.eqToIso hstep).hom =
          Subcomplex.homOfLE
              (shuffleInit2_le_shuffleTopFilt2 m) ≫
            Subcomplex.homOfLE (show shuffleTopFilt2 n m ≤
              shuffleTopFilt2 n m ⊔
                Subcomplex.ofSimplex (shuffleTau.{u} n a b hab hb)
              from le_sup_left) := by
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
      exact hφ₁
    · have hEq : shuffleTopFilt2 n (m + 1) =
          shuffleTopFilt2 n m :=
        shuffleTopFilt2_eq_succ_of_not_valid (fun a b hab hb hcode ↦
          hvalid ⟨a, b, hab, hb, hcode⟩)
      refine ⟨(Subcomplex.eqToIso hEq).hom ≫ φ₁, ?_⟩
      have hcomp : Subcomplex.homOfLE
            (shuffleInit2_le_shuffleTopFilt2 (m + 1)) ≫
            (Subcomplex.eqToIso hEq).hom =
          Subcomplex.homOfLE
            (shuffleInit2_le_shuffleTopFilt2 m) := by
        rw [Subcomplex.eqToIso_hom,
          ← cancel_mono (shuffleTopFilt2 n m).ι]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp]
      exact hφ₁

end ShuffleTopExtension2

section ShuffleHornTwoAssembly

variable {n : ℕ} {C : SSet.{u}}

/-- **The horn-two cell, unfolded form** (the supporting result,
`shuffleInit2` side): a map out of
`∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,2]` to a quasicategory, taking
`v₂` to an equivalence, extends over `Δ[n] ⊗ Δ[2]`. -/
theorem exists_extension_of_unionProd_boundary_horn_two
    [Quasicategory C]
    (φ₀ : ((shuffleInit2 n :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence) :
    ∃ P : (Δ[n] ⊗ Δ[2] : SSet.{u}) ⟶ C,
      (shuffleInit2 n).ι ≫ P = φ₀ := by
  obtain ⟨φm, hφm⟩ := exists_extension_shuffleTopFilt2 φ₀ hVert
    ((n + 1) * (n + 1)) (le_refl _)
  set iso : ((shuffleTopFilt2 n ((n + 1) * (n + 1)) :
        (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[2] : SSet.{u}) :=
    Subcomplex.eqToIso shuffleTopFilt2_bound ≪≫
      Subcomplex.topIso _ with hiso
  refine ⟨iso.inv ≫ φm, ?_⟩
  have hhom : iso.hom =
      (shuffleTopFilt2 n ((n + 1) * (n + 1))).ι := by
    rw [hiso, Iso.trans_hom, Subcomplex.eqToIso_hom,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (shuffleInit2 n).ι =
      Subcomplex.homOfLE (shuffleInit2_le_shuffleTopFilt2 _) ≫
        iso.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  rw [hι, Category.assoc, ← Category.assoc iso.hom iso.inv φm,
    Iso.hom_inv_id, Category.id_comp]
  exact hφm

/-- **The horn-two cell input of `ShuffleBridges.lean`**
(the supporting result): `ShuffleHornTwoCellExtension n C` holds for every
quasicategory `C`. -/
theorem shuffleHornTwoCellExtension_of_quasicategory (n : ℕ)
    (C : SSet.{u}) [Quasicategory C] :
    ShuffleHornTwoCellExtension n C := by
  intro φ₀ hVert
  exact exists_extension_of_unionProd_boundary_horn_two φ₀ hVert

end ShuffleHornTwoAssembly

end SSet

end
