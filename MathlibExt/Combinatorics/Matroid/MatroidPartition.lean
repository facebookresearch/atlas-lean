/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder
import MathlibExt.Combinatorics.Matroid.MatroidIntersection

@[expose] public section

section
namespace MathlibExt.Combinatorics.Matroid.MatroidPartitionWanted

/-!
# Edmonds' matroid partition theorem
-/

/-- Forward direction: a partition into `k` independent sets implies the rank inequality. -/
private theorem mp_aux {E : Type*} [Finite E]
    {M : Matroid E}
    {S : Set E} {k : ℕ} (J : Fin k → Set E)
    (hJ : ∀ i, M.Indep (J i)) (hS : S = ⋃ i, J i)
    (X : Set E) (hX : X ⊆ S) :
    (X.ncard : ℕ∞) ≤ (k : ℕ∞) * M.eRk X := by
  classical
  have := Fintype.ofFinite E
  have hXfin : X.Finite := Set.toFinite X
  have heRk_ne : M.eRk X ≠ ⊤ := by
    have h1 : M.eRk X ≤ X.encard := M.eRk_le_encard X
    have h2 : X.encard < ⊤ := Set.encard_lt_top_iff.mpr hXfin
    exact ne_of_lt (lt_of_le_of_lt h1 h2)
  have hpiece : ∀ i, (X ∩ J i).ncard ≤ (M.eRk X).toNat := by
    intro i
    have hindep : M.Indep (X ∩ J i) := (hJ i).subset Set.inter_subset_right
    have hle : (X ∩ J i).encard ≤ M.eRk X :=
      hindep.encard_le_eRk_of_subset Set.inter_subset_left
    have hfi : (X ∩ J i).Finite := Set.toFinite _
    have hne : (X ∩ J i).encard ≠ ⊤ :=
      ne_of_lt (Set.encard_lt_top_iff.mpr hfi)
    have hcast : (((X ∩ J i).ncard : ℕ) : ℕ∞) = (X ∩ J i).encard :=
      Set.coe_ncard_eq_encard _
    have hle' : ((((X ∩ J i).ncard : ℕ)) : ℕ∞) ≤ M.eRk X := by
      rw [hcast]; exact hle
    have h := ENat.toNat_le_toNat hle' heRk_ne
    rwa [ENat.toNat_natCast] at h
  have hsub : X ⊆ ⋃ i, X ∩ J i := by
    intro x hx
    have hxS : x ∈ S := hX hx
    rw [hS, Set.mem_iUnion] at hxS
    obtain ⟨i, hi⟩ := hxS
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  have hunion : X.ncard ≤ ∑ i, (X ∩ J i).ncard :=
    le_trans (Set.ncard_le_ncard hsub (Set.toFinite _))
      (Set.ncard_iUnion_le_of_fintype _)
  have hsum : ∑ i, (X ∩ J i).ncard ≤ k * (M.eRk X).toNat := by
    calc ∑ i, (X ∩ J i).ncard ≤ ∑ _i : Fin k, (M.eRk X).toNat :=
          Finset.sum_le_sum (fun i _ => hpiece i)
      _ = k * (M.eRk X).toNat := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hcast : ((X.ncard : ℕ) : ℕ∞) ≤ ((k * (M.eRk X).toNat : ℕ) : ℕ∞) :=
    Nat.cast_le.mpr (le_trans hunion hsum)
  rw [Nat.cast_mul, ENat.natCast_toNat heRk_ne] at hcast
  exact hcast

/-- Abstract rank-function form of the partition theorem: a function
`r : Finset E → ℕ` satisfying the rank axioms whose `k`-fold rank dominates
cardinality on subsets of `S₀` yields a cover of `S₀` by `k` "independent"
sets. Proved by reduction to
`MatroidIntersectionWanted.exists_common_indep_of_cut_le` on `E × Fin k`,
pairing the sum of section ranks against the count of fibers meeting a set. -/
private theorem part_core
    {E : Type*} [Finite E] [DecidableEq E]
    (S₀ : Finset E) (k : ℕ) (r : Finset E → ℕ)
    (hle : ∀ X, r X ≤ X.card)
    (hmono : ∀ X Y, X ⊆ Y → r X ≤ r Y)
    (hsub : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y)
    (hcut : ∀ A : Finset E, A ⊆ S₀ → A.card ≤ k * r A) :
    ∃ J : Fin k → Finset E, (∀ i, r (J i) = (J i).card) ∧
      (∀ i, J i ⊆ S₀) ∧ ∀ e ∈ S₀, ∃ i, e ∈ J i := by
  classical
  have := Fintype.ofFinite E
  have := Fintype.ofFinite (E × Fin k)
  set sec : Fin k → Finset (E × Fin k) → Finset E :=
    fun i X => (X.filter (fun p => p.2 = i)).image Prod.fst with hsec
  set r₁ : Finset (E × Fin k) → ℕ := fun X => ∑ i, r (sec i X) with hr₁
  set fib : Finset (E × Fin k) → Finset E :=
    fun X => (X.filter (fun p => p.1 ∈ S₀)).image Prod.fst with hfib
  set r₂ : Finset (E × Fin k) → ℕ := fun X => (fib X).card with hr₂
  set G : Finset (E × Fin k) :=
    Finset.univ.filter (fun p => p.1 ∈ S₀) with hG
  have hmemG : ∀ p : E × Fin k, p ∈ G ↔ p.1 ∈ S₀ := by
    intro p
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsec_mono : ∀ (i : Fin k) (X Y : Finset (E × Fin k)),
      X ⊆ Y → sec i X ⊆ sec i Y := by
    intro i X Y hXY
    simp only [hsec]
    exact Finset.image_subset_image (Finset.filter_subset_filter _ hXY)
  have hsec_card : ∀ (i : Fin k) (X : Finset (E × Fin k)),
      (sec i X).card ≤ (X.filter (fun p => p.2 = i)).card := by
    intro i X
    simp only [hsec]
    exact Finset.card_image_le
  have hcard_fiber : ∀ X : Finset (E × Fin k),
      X.card = ∑ i, (X.filter (fun p => p.2 = i)).card := by
    intro X
    exact Finset.card_eq_sum_card_fiberwise
      (s := X) (t := Finset.univ) (f := Prod.snd)
      (fun _ _ => Finset.mem_univ _)
  have hle₁ : ∀ X : Finset (E × Fin k), r₁ X ≤ X.card := by
    intro X
    simp only [hr₁]
    calc ∑ i, r (sec i X)
        ≤ ∑ i, (X.filter (fun p => p.2 = i)).card :=
          Finset.sum_le_sum (fun i _ => le_trans (hle _) (hsec_card i X))
      _ = X.card := (hcard_fiber X).symm
  have hmono₁ : ∀ X Y : Finset (E × Fin k), X ⊆ Y → r₁ X ≤ r₁ Y := by
    intro X Y hXY
    simp only [hr₁]
    exact Finset.sum_le_sum (fun i _ => hmono _ _ (hsec_mono i X Y hXY))
  have hsec_union : ∀ (i : Fin k) (X Y : Finset (E × Fin k)),
      sec i (X ∪ Y) = sec i X ∪ sec i Y := by
    intro i X Y
    simp only [hsec, Finset.filter_union, Finset.image_union]
  have hsec_inter : ∀ (i : Fin k) (X Y : Finset (E × Fin k)),
      sec i (X ∩ Y) ⊆ sec i X ∩ sec i Y := by
    intro i X Y
    simp only [hsec, Finset.filter_inter_distrib]
    exact Finset.image_inter_subset _ _ _
  have hsub₁ : ∀ X Y : Finset (E × Fin k),
      r₁ (X ∩ Y) + r₁ (X ∪ Y) ≤ r₁ X + r₁ Y := by
    intro X Y
    have hpt : ∀ i : Fin k, r (sec i (X ∩ Y)) + r (sec i (X ∪ Y)) ≤
        r (sec i X) + r (sec i Y) := by
      intro i
      have h1 := hmono _ _ (hsec_inter i X Y)
      have h2 := hsub (sec i X) (sec i Y)
      rw [hsec_union i X Y]
      omega
    have e1 : r₁ (X ∩ Y) + r₁ (X ∪ Y) =
        ∑ i, (r (sec i (X ∩ Y)) + r (sec i (X ∪ Y))) := by
      simp only [hr₁, Finset.sum_add_distrib]
    have e2 : r₁ X + r₁ Y = ∑ i, (r (sec i X) + r (sec i Y)) := by
      simp only [hr₁, Finset.sum_add_distrib]
    rw [e1, e2]
    exact Finset.sum_le_sum (fun i _ => hpt i)
  have hfib_mono : ∀ X Y : Finset (E × Fin k), X ⊆ Y → fib X ⊆ fib Y := by
    intro X Y hXY
    simp only [hfib]
    exact Finset.image_subset_image (Finset.filter_subset_filter _ hXY)
  have hle₂ : ∀ X : Finset (E × Fin k), r₂ X ≤ X.card := by
    intro X
    simp only [hr₂, hfib]
    exact le_trans Finset.card_image_le
      (Finset.card_le_card (Finset.filter_subset _ _))
  have hmono₂ : ∀ X Y : Finset (E × Fin k), X ⊆ Y → r₂ X ≤ r₂ Y := by
    intro X Y hXY
    simp only [hr₂]
    exact Finset.card_le_card (hfib_mono X Y hXY)
  have hfib_union : ∀ X Y : Finset (E × Fin k),
      fib (X ∪ Y) = fib X ∪ fib Y := by
    intro X Y
    simp only [hfib, Finset.filter_union, Finset.image_union]
  have hfib_inter : ∀ X Y : Finset (E × Fin k),
      fib (X ∩ Y) ⊆ fib X ∩ fib Y := by
    intro X Y
    simp only [hfib, Finset.filter_inter_distrib]
    exact Finset.image_inter_subset _ _ _
  have hsub₂ : ∀ X Y : Finset (E × Fin k),
      r₂ (X ∩ Y) + r₂ (X ∪ Y) ≤ r₂ X + r₂ Y := by
    intro X Y
    have h1 : (fib (X ∩ Y)).card ≤ (fib X ∩ fib Y).card :=
      Finset.card_le_card (hfib_inter X Y)
    have h2 : (fib (X ∪ Y)).card = (fib X ∪ fib Y).card := by
      rw [hfib_union]
    have h3 := Finset.card_union_add_card_inter (fib X) (fib Y)
    simp only [hr₂]
    omega
  have hcut' : ∀ X : Finset (E × Fin k),
      X ⊆ G → S₀.card ≤ r₁ X + r₂ (G \ X) := by
    intro X _
    set A : Finset E := S₀.filter (fun e => ∀ i, (e, i) ∈ X) with hA
    have hAsub : A ⊆ S₀ := Finset.filter_subset _ _
    have hfib_sdiff : fib (G \ X) = S₀ \ A := by
      ext e
      simp only [hfib, hG, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_sdiff, hA]
      constructor
      · rintro ⟨p, ⟨⟨hpS, hpX⟩, -⟩, hpeq⟩
        obtain ⟨e', i⟩ := p
        dsimp only at hpS hpX hpeq
        subst hpeq
        exact ⟨hpS, fun h => hpX (h.2 i)⟩
      · rintro ⟨heS, henA⟩
        have hnex : ¬ ∀ i, (e, i) ∈ X := fun hall => henA ⟨heS, hall⟩
        push Not at hnex
        obtain ⟨i, hi⟩ := hnex
        exact ⟨(e, i), ⟨⟨heS, hi⟩, heS⟩, rfl⟩
    have hr₂_sdiff : r₂ (G \ X) = S₀.card - A.card := by
      simp only [hr₂, hfib_sdiff, Finset.card_sdiff_of_subset hAsub]
    have hAsec : ∀ i : Fin k, A ⊆ sec i X := by
      intro i e heA
      simp only [hA, Finset.mem_filter] at heA
      simp only [hsec, Finset.mem_image, Finset.mem_filter]
      exact ⟨(e, i), ⟨heA.2 i, rfl⟩, rfl⟩
    have hAle : A.card ≤ r₁ X := by
      have h1 : A.card ≤ k * r A := hcut A hAsub
      have h2 : k * r A = ∑ _i : Fin k, r A := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have h3 : ∑ _i : Fin k, r A ≤ r₁ X := by
        simp only [hr₁]
        exact Finset.sum_le_sum (fun i _ => hmono _ _ (hAsec i))
      rw [h2] at h1
      exact le_trans h1 h3
    have hAcards : A.card ≤ S₀.card := Finset.card_le_card hAsub
    simp only [hr₂_sdiff]
    omega
  obtain ⟨I, hIsub, hrI1, hrI2, hIk⟩ :=
    MatroidIntersectionWanted.exists_common_indep_of_cut_le G S₀.card r₁ r₂ hle₁
      hle₂ hmono₁ hmono₂ hsub₁ hsub₂ hcut'
  have hpt : ∀ i : Fin k, r (sec i I) = (sec i I).card := by
    have hleF : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        r (sec i I) ≤ (I.filter (fun p => p.2 = i)).card :=
      fun i _ => le_trans (hle _) (hsec_card i I)
    have e1 : r₁ I = ∑ i, r (sec i I) := by simp only [hr₁]
    have hsum : ∑ i, r (sec i I)
        = ∑ i, (I.filter (fun p => p.2 = i)).card := by
      rw [← e1, hrI1, hcard_fiber]
    intro i
    have h1 : r (sec i I) ≤ (sec i I).card := hle _
    have h2 : (sec i I).card ≤ (I.filter (fun p => p.2 = i)).card :=
      hsec_card i I
    have h3 : r (sec i I) = (I.filter (fun p => p.2 = i)).card := by
      by_contra hne
      have hlt : r (sec i I) < (I.filter (fun p => p.2 = i)).card :=
        lt_of_le_of_ne (hleF i (Finset.mem_univ i)) hne
      have hcon := Finset.sum_lt_sum hleF ⟨i, Finset.mem_univ i, hlt⟩
      rw [hsum] at hcon
      exact absurd hcon (lt_irrefl _)
    omega
  have hJsub : ∀ i : Fin k, sec i I ⊆ S₀ := by
    intro i e he
    simp only [hsec, Finset.mem_image, Finset.mem_filter] at he
    obtain ⟨p, ⟨hpI, -⟩, hpe⟩ := he
    have hpG := hIsub hpI
    rw [hmemG] at hpG
    rw [← hpe]
    exact hpG
  have hfibI : fib I = S₀ := by
    have hcardI : (fib I).card = I.card := by
      simp only [hr₂] at hrI2
      exact hrI2
    have hsub2 : fib I ⊆ S₀ := by
      intro e he
      simp only [hfib, Finset.mem_image, Finset.mem_filter] at he
      obtain ⟨p, ⟨-, hpS⟩, hpe⟩ := he
      rw [← hpe]
      exact hpS
    have hcard2 : (fib I).card = S₀.card := by
      have h1 : (fib I).card ≤ S₀.card := Finset.card_le_card hsub2
      omega
    exact Finset.eq_of_subset_of_card_le hsub2 (le_of_eq hcard2.symm)
  have hcover : ∀ e ∈ S₀, ∃ i, e ∈ sec i I := by
    intro e heS
    have heF : e ∈ fib I := by rw [hfibI]; exact heS
    simp only [hfib, Finset.mem_image, Finset.mem_filter] at heF
    obtain ⟨p, ⟨hpI, -⟩, hpe⟩ := heF
    refine ⟨p.2, ?_⟩
    simp only [hsec, Finset.mem_image, Finset.mem_filter]
    exact ⟨p, ⟨hpI, rfl⟩, hpe⟩
  exact ⟨fun i => sec i I, hpt, hJsub, hcover⟩

/--
**Edmonds' matroid partition theorem, arbitrary ground set.** Let $E$ be a finite set, let $M$
be a matroid with ground set $E(M) \subseteq E$, let $S \subseteq E$ and let $k$ be a natural
number. Then $S = J_1 \cup \dots \cup J_k$ for some sets $J_1, \dots, J_k$ that are independent
in $M$ (not necessarily disjoint) if and only if $|X| \le k \, r_M(X)$ for every $X \subseteq S$,
where $r_M(X)$ denotes the rank in $M$ of $X \cap E(M)$.
-/
theorem edmonds_matroid_partition'
    {E : Type*} [Finite E]
    {M : Matroid E}
    {S : Set E} {k : ℕ} :
    (∃ J : Fin k → Set E, (∀ i, M.Indep (J i)) ∧ S = ⋃ i, J i) ↔
      ∀ X : Set E, X ⊆ S → (X.ncard : ℕ∞) ≤ (k : ℕ∞) * M.eRk X := by
  classical
  have := Fintype.ofFinite E
  constructor
  · rintro ⟨J, hJ, hS⟩ X hX
    exact mp_aux J hJ hS X hX
  · intro hcond
    set r : Finset E → ℕ := fun X => (M.eRk (↑X : Set E)).toNat with hr
    have hfin : ∀ X : Finset E, M.eRk (↑X : Set E) ≠ ⊤ := fun X =>
      Matroid.eRk_ne_top_iff.mpr (M.isRkFinite_of_finite X.finite_toSet)
    have hadd : ∀ (a b : ℕ∞), a ≠ ⊤ → b ≠ ⊤ → a + b ≠ ⊤ := by
      intro a b ha hb
      rw [← ENat.natCast_toNat ha, ← ENat.natCast_toNat hb, ← Nat.cast_add]
      exact ENat.natCast_ne_top _
    have hle : ∀ X : Finset E, r X ≤ X.card := by
      intro X
      simp only [hr]
      have h := M.eRk_le_encard (↑X : Set E)
      rw [Set.encard_coe_eq_coe_finsetCard] at h
      have h2 := ENat.toNat_le_toNat h (ENat.natCast_ne_top X.card)
      rwa [ENat.toNat_natCast] at h2
    have hmono : ∀ X Y : Finset E, X ⊆ Y → r X ≤ r Y := by
      intro X Y hXY
      simp only [hr]
      have hXY' : (↑X : Set E) ⊆ ↑Y := by exact_mod_cast hXY
      exact ENat.toNat_le_toNat (M.eRk_mono hXY') (hfin Y)
    have hsub : ∀ X Y : Finset E,
        r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y := by
      intro X Y
      have h := M.eRk_inter_add_eRk_union_le (↑X : Set E) (↑Y : Set E)
      rw [← Finset.coe_inter, ← Finset.coe_union] at h
      have h2 := ENat.toNat_le_toNat h (hadd _ _ (hfin X) (hfin Y))
      have eL := ENat.toNat_add (hfin (X ∩ Y)) (hfin (X ∪ Y))
      have eR := ENat.toNat_add (hfin X) (hfin Y)
      rw [eL, eR] at h2
      simpa only [hr] using h2
    set S₀ : Finset E := S.toFinset with hS₀
    have hmemS₀ : ∀ e : E, e ∈ S₀ ↔ e ∈ S := by
      intro e
      rw [hS₀]
      exact Set.mem_toFinset
    have hcoeS₀ : (↑S₀ : Set E) = S := by
      rw [hS₀]
      exact Set.coe_toFinset S
    have hcut : ∀ A : Finset E, A ⊆ S₀ → A.card ≤ k * r A := by
      intro A hAS
      have hsub' : (↑A : Set E) ⊆ S := by
        have h1 : (↑A : Set E) ⊆ ↑S₀ := by exact_mod_cast hAS
        rwa [hcoeS₀] at h1
      have h := hcond (↑A : Set E) hsub'
      rw [Set.ncard_coe_finset] at h
      have heRk : M.eRk (↑A : Set E) = ((r A : ℕ) : ℕ∞) := by
        simp only [hr]
        exact (ENat.natCast_toNat (hfin A)).symm
      rw [heRk] at h
      have hcast : ((k : ℕ∞) * ((r A : ℕ) : ℕ∞)) = (((k * r A : ℕ)) : ℕ∞) := by
        simp only [Nat.cast_mul]
      rw [hcast] at h
      exact ENat.natCast_le_natCast.mp h
    obtain ⟨J, hJr, hJsub, hcover⟩ := part_core S₀ k r hle hmono hsub hcut
    refine ⟨fun i => (↑(J i) : Set E), fun i => ?_, ?_⟩
    · have hI1' : (M.eRk (↑(J i) : Set E)).toNat = (J i).card := by
        simpa only [hr] using hJr i
      have hne := hfin (J i)
      have he : M.eRk (↑(J i) : Set E) = ((↑(J i) : Set E)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, ← hI1']
        exact (ENat.natCast_toNat hne).symm
      exact (Matroid.indep_iff_eRk_eq_encard_of_finite (J i).finite_toSet).mpr he
    · ext e
      simp only [Set.mem_iUnion, Finset.mem_coe]
      constructor
      · intro h
        obtain ⟨i, hi⟩ := hcover e ((hmemS₀ e).mpr h)
        exact ⟨i, hi⟩
      · intro h
        obtain ⟨i, hi⟩ := h
        exact (hmemS₀ e).mp (hJsub i hi)

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedVariables false in
/--
**Edmonds' matroid partition theorem.** Let $E$ be a finite set, let $M$ be a matroid whose
ground set is all of $E$, let $S \subseteq E$ and let $k$ be a natural number. Then
$S = J_1 \cup \dots \cup J_k$ for some sets $J_1, \dots, J_k$ that are independent in $M$ (not
necessarily disjoint) if and only if $|X| \le k \, r_M(X)$ for every $X \subseteq S$, where $r_M$
is the rank function of $M$.

Proves `Wanted` entry `edmonds_matroid_partition`.

Source: J. Edmonds, Minimum partition of a matroid into independent subsets, J. Res. Natl. Bur.
Standards Sect. B 69B (1965), 67-72, DOI 10.6028/jres.069B.004.
-/
theorem edmonds_matroid_partition
    {E : Type*} [Fintype E] [DecidableEq E]
    {M : Matroid E} (hM : M.E = Set.univ)
    {S : Set E} {k : ℕ} :
    (∃ J : Fin k → Set E, (∀ i, M.Indep (J i)) ∧ S = ⋃ i, J i) ↔
      ∀ X : Set E, X ⊆ S → (X.ncard : ℕ∞) ≤ (k : ℕ∞) * M.eRk X :=
  edmonds_matroid_partition'

end MathlibExt.Combinatorics.Matroid.MatroidPartitionWanted
end
