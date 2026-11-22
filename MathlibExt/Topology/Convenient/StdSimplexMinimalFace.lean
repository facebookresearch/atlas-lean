/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.StdSimplex
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Minimal support faces of standard-simplex points

Every point of a standard simplex factors through a simplex-category
monomorphism from its support face, with a strictly positive preimage.
The theorem `supportFace_eq` shows that two such presentations have equal
dimensions and agree on vertices after that identification. A simplex-category
monomorphism whose image point has strictly positive coordinates is an
isomorphism, since its range contains every target vertex.
-/

@[expose] public section

namespace Convexity.StdSimplex

variable {n : ℕ}

/-- Every standard-simplex point is the image of a strictly positive point
under a simplex-category monomorphism. The monotone support enumeration
gives its vertex map, with one source vertex for each nonzero barycentric
coordinate. -/
theorem exists_support_face_mono (p : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (k : ℕ) (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk n),
      CategoryTheory.Mono φ ∧
      ∃ q : StdSimplex ℝ (Fin (k + 1)), (∀ i, 0 < q.weights i) ∧
        q.map ⇑φ.toOrderHom = p := by
  classical
  obtain ⟨k', f, hf, q, hq, hmap⟩ :=
    Convexity.StdSimplex.exists_strictly_positive_preimage p
  have hk' : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with rfl | h
    · exfalso
      have hsum := q.total_of_fintype
      simp at hsum
    · exact h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk'.ne'
  set s : Finset (Fin (n + 1)) := Finset.image f Finset.univ with hs_def
  have hs_card : s.card = k + 1 := by
    rw [hs_def, Finset.card_image_of_injective _ hf]
    simp
  set e := s.orderEmbOfFin hs_card with he_def
  have he_range : Set.range (⇑e) = ↑s := by
    rw [he_def]
    exact Finset.range_orderEmbOfFin s hs_card
  have hmem : ∀ i, f i ∈ s := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hex : ∀ i, ∃ j, e j = f i := by
    intro i
    have hrange : f i ∈ Set.range (⇑e) := by
      rw [he_range]
      exact Finset.mem_coe.mpr (hmem i)
    obtain ⟨j, hj⟩ := hrange
    exact ⟨j, hj⟩
  choose σ hσ using hex
  have hσ_inj : Function.Injective σ := by
    intro a b hab
    have h1 : e (σ a) = f a := hσ a
    have h2 : e (σ b) = f b := hσ b
    have heq : f a = f b := by rw [← h1, ← h2, hab]
    exact hf heq
  have hσ_surj : Function.Surjective σ := by
    intro j
    have hj : e j ∈ s := by
      have hrange : e j ∈ Set.range (⇑e) := ⟨j, rfl⟩
      rw [he_range] at hrange
      exact Finset.mem_coe.mp hrange
    rw [hs_def] at hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact ⟨i, e.injective (by rw [hσ i, hi])⟩
  set φ : SimplexCategory.mk k ⟶ SimplexCategory.mk n :=
    SimplexCategory.Hom.mk e.toOrderHom with hφ
  have hφ_inj : Function.Injective ⇑φ.toOrderHom := by
    rw [hφ]
    simp only [SimplexCategory.Hom.toOrderHom_mk]
    exact e.injective
  have hmono : CategoryTheory.Mono φ :=
    SimplexCategory.mono_iff_injective.mpr hφ_inj
  refine ⟨k, φ, hmono, q.map σ,
    fun j => Convexity.StdSimplex.map_surjective_pos hσ_surj hq j, ?_⟩
  have hcomp : (⇑e.toOrderHom ∘ σ) = f := funext fun i => hσ i
  have h1 : (q.map σ).map ⇑e.toOrderHom
      = q.map (⇑e.toOrderHom ∘ σ) :=
    (Convexity.StdSimplex.map_comp q σ ⇑e.toOrderHom).symm
  have h2 : q.map (⇑e.toOrderHom ∘ σ) = p := by
    rw [hcomp]
    exact hmap
  have h3 : (q.map σ).map ⇑e.toOrderHom = p := h1.trans h2
  simpa only [hφ, SimplexCategory.Hom.toOrderHom_mk] using h3

/-- Two monomorphisms presenting the same point as the image of strictly
positive points have equal source dimensions and agree on vertices after
that identification. Both enumerate the same support strictly monotonically,
so uniqueness of `orderEmbOfFin` gives the equality. -/
theorem supportFace_eq
    {p : StdSimplex ℝ (Fin (n + 1))}
    {k₁ : ℕ} {φ₁ : SimplexCategory.mk k₁ ⟶ SimplexCategory.mk n}
    (hmono₁ : CategoryTheory.Mono φ₁)
    {q₁ : StdSimplex ℝ (Fin (k₁ + 1))}
    (hq₁ : ∀ i, 0 < q₁.weights i)
    (hmap₁ : Convexity.StdSimplex.map (fun i => φ₁.toOrderHom i) q₁ = p)
    {k₂ : ℕ} {φ₂ : SimplexCategory.mk k₂ ⟶ SimplexCategory.mk n}
    (hmono₂ : CategoryTheory.Mono φ₂)
    {q₂ : StdSimplex ℝ (Fin (k₂ + 1))}
    (hq₂ : ∀ i, 0 < q₂.weights i)
    (hmap₂ : Convexity.StdSimplex.map (fun i => φ₂.toOrderHom i) q₂ = p) :
    ∃ hkk : k₁ = k₂, ∀ i, φ₁.toOrderHom i = φ₂.toOrderHom (hkk ▸ i) := by
  classical
  have hφ₁inj : Function.Injective (fun i => φ₁.toOrderHom i) :=
    SimplexCategory.mono_iff_injective.mp hmono₁
  have hφ₂inj : Function.Injective (fun i => φ₂.toOrderHom i) :=
    SimplexCategory.mono_iff_injective.mp hmono₂
  have hkk : k₁ = k₂ := by
    have hr₁ : Set.range (fun i => φ₁.toOrderHom i) = {i | p.weights i ≠ 0} :=
      Convexity.StdSimplex.range_eq_support_of_strictly_positive hφ₁inj hq₁ hmap₁
    have hr₂ : Set.range (fun i => φ₂.toOrderHom i) = {i | p.weights i ≠ 0} :=
      Convexity.StdSimplex.range_eq_support_of_strictly_positive hφ₂inj hq₂ hmap₂
    have himg₁ : Finset.image (fun i => φ₁.toOrderHom i) Finset.univ =
        p.weights.support := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and,
        Finsupp.mem_support_iff]
      constructor
      · rintro ⟨i, rfl⟩
        have : φ₁.toOrderHom i ∈ Set.range (fun i => φ₁.toOrderHom i) := ⟨i, rfl⟩
        rw [hr₁] at this
        simpa using this
      · intro hy
        have : y ∈ Set.range (fun i => φ₁.toOrderHom i) := by
          rw [hr₁]
          simpa using hy
        obtain ⟨i, hi⟩ := this
        exact ⟨i, hi⟩
    have himg₂ : Finset.image (fun i => φ₂.toOrderHom i) Finset.univ =
        p.weights.support := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and,
        Finsupp.mem_support_iff]
      constructor
      · rintro ⟨i, rfl⟩
        have : φ₂.toOrderHom i ∈ Set.range (fun i => φ₂.toOrderHom i) := ⟨i, rfl⟩
        rw [hr₂] at this
        simpa using this
      · intro hy
        have : y ∈ Set.range (fun i => φ₂.toOrderHom i) := by
          rw [hr₂]
          simpa using hy
        obtain ⟨i, hi⟩ := this
        exact ⟨i, hi⟩
    have hc₁ : (Finset.image (fun i => φ₁.toOrderHom i) Finset.univ).card = k₁ + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => hφ₁inj hab)]
      simp
    have hc₂ : (Finset.image (fun i => φ₂.toOrderHom i) Finset.univ).card = k₂ + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => hφ₂inj hab)]
      simp
    rw [himg₁] at hc₁
    rw [himg₂] at hc₂
    omega
  subst hkk
  -- Both underlying maps are strictly monotone enumerations of the same support
  -- finset, so `orderEmbOfFin_unique` identifies both with the canonical
  -- enumeration, forcing pointwise equality.
  have hmono₁' : Monotone (fun i => φ₁.toOrderHom i) := φ₁.toOrderHom.monotone
  have hmono₂' : Monotone (fun i => φ₂.toOrderHom i) := φ₂.toOrderHom.monotone
  have hstrict₁ : StrictMono (fun i => φ₁.toOrderHom i) :=
    hmono₁'.strictMono_of_injective hφ₁inj
  have hstrict₂ : StrictMono (fun i => φ₂.toOrderHom i) :=
    hmono₂'.strictMono_of_injective hφ₂inj
  have hmem₁ : ∀ x, (fun i => φ₁.toOrderHom i) x ∈ p.weights.support := by
    intro x
    have hr : Set.range (fun i => φ₁.toOrderHom i) = {i | p.weights i ≠ 0} :=
      Convexity.StdSimplex.range_eq_support_of_strictly_positive hφ₁inj hq₁ hmap₁
    have hmem : φ₁.toOrderHom x ∈ Set.range (fun i => φ₁.toOrderHom i) := ⟨x, rfl⟩
    rw [hr, Set.mem_ofPred_eq, ← Finsupp.mem_support_iff] at hmem
    exact hmem
  have hcard : (p.weights.support).card = k₁ + 1 := by
    have himg : Finset.image (fun i => φ₁.toOrderHom i) Finset.univ =
        p.weights.support := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and,
        Finsupp.mem_support_iff]
      constructor
      · rintro ⟨i, rfl⟩
        have : φ₁.toOrderHom i ∈ Set.range (fun i => φ₁.toOrderHom i) := ⟨i, rfl⟩
        have hr : Set.range (fun i => φ₁.toOrderHom i) = {i | p.weights i ≠ 0} :=
          Convexity.StdSimplex.range_eq_support_of_strictly_positive hφ₁inj hq₁ hmap₁
        rw [hr] at this
        simpa using this
      · intro hy
        have : y ∈ Set.range (fun i => φ₁.toOrderHom i) := by
          rw [Convexity.StdSimplex.range_eq_support_of_strictly_positive hφ₁inj hq₁ hmap₁]
          simpa using hy
        obtain ⟨i, hi⟩ := this
        exact ⟨i, hi⟩
    have hc : (Finset.image (fun i => φ₁.toOrderHom i) Finset.univ).card = k₁ + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => hφ₁inj hab)]
      simp
    rw [himg] at hc
    exact hc
  have e1 : (fun i => φ₁.toOrderHom i) =
      fun i => (p.weights.support).orderEmbOfFin hcard i :=
    Finset.orderEmbOfFin_unique hcard hmem₁ hstrict₁
  have hmem₂ : ∀ x, (fun i => φ₂.toOrderHom i) x ∈ p.weights.support := by
    intro x
    have hr : Set.range (fun i => φ₂.toOrderHom i) = {i | p.weights i ≠ 0} :=
      Convexity.StdSimplex.range_eq_support_of_strictly_positive hφ₂inj hq₂ hmap₂
    have hmem : φ₂.toOrderHom x ∈ Set.range (fun i => φ₂.toOrderHom i) := ⟨x, rfl⟩
    rw [hr, Set.mem_ofPred_eq, ← Finsupp.mem_support_iff] at hmem
    exact hmem
  have e2 : (fun i => φ₂.toOrderHom i) =
      fun i => (p.weights.support).orderEmbOfFin hcard i :=
    Finset.orderEmbOfFin_unique hcard hmem₂ hstrict₂
  exact ⟨rfl, fun i => by rw [congrFun e1 i, congrFun e2 _]⟩

/-- A simplex-category monomorphism whose image point has strictly positive
barycentric coordinates is an isomorphism. Positivity makes its vertex range
the whole target, so it is both mono and epi. -/
theorem isIso_of_mono_map_strictly_positive {k n : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk n)
    [CategoryTheory.Mono φ]
    {q : StdSimplex ℝ (Fin (k + 1))}
    (hpos : ∀ j, 0 < (q.map ⇑φ.toOrderHom).weights j) :
    CategoryTheory.IsIso φ := by
  classical
  have hf_inj : Function.Injective (⇑φ.toOrderHom) :=
    SimplexCategory.mono_iff_injective.mp inferInstance
  have hq_pos : ∀ i, 0 < q.weights i := by
    intro i
    have hmap_eq : (q.map ⇑φ.toOrderHom).weights (φ.toOrderHom i) = q.weights i := by
      rw [Convexity.StdSimplex.weights_map]
      exact Finsupp.mapDomain_apply_of_injective hf_inj _ _
    have h := hpos (φ.toOrderHom i)
    rwa [hmap_eq] at h
  have hrange :=
    Convexity.StdSimplex.range_eq_support_of_map_strictly_positive
      (f := (⇑φ.toOrderHom)) hq_pos
  have hsup : {i | (q.map ⇑φ.toOrderHom).weights i ≠ 0} = Set.univ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ne_of_gt (hpos y)
  have h_range_univ : Set.range (⇑φ.toOrderHom) = Set.univ := by
    rw [hrange, hsup]
  have hsurj : Function.Surjective (⇑φ.toOrderHom) :=
    Set.range_eq_univ.mp h_range_univ
  have hEpi : CategoryTheory.Epi φ := SimplexCategory.epi_iff_surjective.mpr hsurj
  exact @CategoryTheory.isIso_of_mono_of_epi _ _ _ _ _ φ inferInstance hEpi

end Convexity.StdSimplex
