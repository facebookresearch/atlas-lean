/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Order.CompletePartialOrder

@[expose] public section

section
namespace MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted

/-!
# Edmonds' matroid intersection min-max

Proves the finite matroid-intersection min-max theorem.
-/

/-- **Matroid intersection for abstract rank functions.** Let $E$ be a finite subset of a type
$\alpha$, let $k$ be a natural number, and let $r_1, r_2$ be functions from the finite subsets of
$\alpha$ to $\mathbb{N}$ such that, for $i = 1, 2$ and all finite $X, Y \subseteq \alpha$, we have
$r_i(X) \le |X|$, $r_i(X) \le r_i(Y)$ whenever $X \subseteq Y$, and
$r_i(X \cap Y) + r_i(X \cup Y) \le r_i(X) + r_i(Y)$. If every $X \subseteq E$ satisfies
$k \le r_1(X) + r_2(E \setminus X)$, then there is a set $I \subseteq E$ with
$r_1(I) = r_2(I) = |I|$ and $|I| \ge k$.

Proved by induction on $E$, via deletion and contraction. -/
theorem exists_common_indep_of_cut_le
    {α : Type*} [DecidableEq α]
    (E : Finset α) (k : ℕ) (r₁ r₂ : Finset α → ℕ)
    (hle₁ : ∀ X, r₁ X ≤ X.card)
    (hle₂ : ∀ X, r₂ X ≤ X.card)
    (hmono₁ : ∀ X Y, X ⊆ Y → r₁ X ≤ r₁ Y)
    (hmono₂ : ∀ X Y, X ⊆ Y → r₂ X ≤ r₂ Y)
    (hsub₁ : ∀ X Y, r₁ (X ∩ Y) + r₁ (X ∪ Y) ≤ r₁ X + r₁ Y)
    (hsub₂ : ∀ X Y, r₂ (X ∩ Y) + r₂ (X ∪ Y) ≤ r₂ X + r₂ Y)
    (hcut : ∀ X, X ⊆ E → k ≤ r₁ X + r₂ (E \ X)) :
    ∃ I, I ⊆ E ∧ r₁ I = I.card ∧ r₂ I = I.card ∧ k ≤ I.card := by
  refine Finset.induction_on E (motive := fun E => ∀ (k : ℕ) (r₁ r₂ : Finset α → ℕ),
      (∀ X, r₁ X ≤ X.card) →
      (∀ X, r₂ X ≤ X.card) →
      (∀ X Y, X ⊆ Y → r₁ X ≤ r₁ Y) →
      (∀ X Y, X ⊆ Y → r₂ X ≤ r₂ Y) →
      (∀ X Y, r₁ (X ∩ Y) + r₁ (X ∪ Y) ≤ r₁ X + r₁ Y) →
      (∀ X Y, r₂ (X ∩ Y) + r₂ (X ∪ Y) ≤ r₂ X + r₂ Y) →
      (∀ X, X ⊆ E → k ≤ r₁ X + r₂ (E \ X)) →
      ∃ I, I ⊆ E ∧ r₁ I = I.card ∧ r₂ I = I.card ∧ k ≤ I.card) ?_ ?_
      k r₁ r₂ hle₁ hle₂ hmono₁ hmono₂ hsub₁ hsub₂ hcut
  · intro k r₁ r₂ hle₁ hle₂ hmono₁ hmono₂ hsub₁ hsub₂ hcut
    have h0 := hcut ∅ (Finset.Subset.refl ∅)
    have e1 : r₁ ∅ = 0 := Nat.eq_zero_of_le_zero (by simpa using hle₁ ∅)
    have e2 : r₂ ∅ = 0 := Nat.eq_zero_of_le_zero (by simpa using hle₂ ∅)
    rw [Finset.sdiff_self, e1, e2] at h0
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨∅, Finset.empty_subset _, by simp [e1], by simp [e2], Nat.zero_le _⟩
  · intro e E₀ hmem ih k r₁ r₂ hle₁ hle₂ hmono₁ hmono₂ hsub₁ hsub₂ hcut
    by_cases hk : k = 0
    · subst hk
      exact ⟨∅, Finset.empty_subset _, le_antisymm (hle₁ ∅) (by simp),
        le_antisymm (hle₂ ∅) (by simp), Nat.zero_le _⟩
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      by_cases hdel : ∀ X : Finset α, X ⊆ E₀ → n.succ ≤ r₁ X + r₂ (E₀ \ X)
      · obtain ⟨J, hJsub, hJ1, hJ2, hJk⟩ :=
          ih n.succ r₁ r₂ hle₁ hle₂ hmono₁ hmono₂ hsub₁ hsub₂ hdel
        exact ⟨J, hJsub.trans (Finset.subset_insert e E₀), hJ1, hJ2, hJk⟩
      · push Not at hdel
        obtain ⟨X, hXE, hX⟩ := hdel
        have heX : e ∉ X := fun h => hmem (hXE h)
        have heEX : e ∉ E₀ \ X := fun h => hmem (Finset.mem_sdiff.mp h).1
        have hr10 : r₁ ∅ = 0 := Nat.eq_zero_of_le_zero (by simpa using hle₁ ∅)
        have hr20 : r₂ ∅ = 0 := Nat.eq_zero_of_le_zero (by simpa using hle₂ ∅)
        have hsd1 : ∀ Z : Finset α, e ∉ Z → insert e E₀ \ Z = insert e (E₀ \ Z) := by
          intro Z heZ
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hy, hny⟩
            rcases hy with rfl | hy
            · exact Or.inl rfl
            · exact Or.inr ⟨hy, hny⟩
          · rintro (rfl | ⟨hy, hny⟩)
            · exact ⟨Or.inl rfl, heZ⟩
            · exact ⟨Or.inr hy, hny⟩
        have hsd2 : ∀ Y : Finset α, Y ⊆ E₀ → insert e E₀ \ insert e Y = E₀ \ Y := by
          intro Y hYE
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hy, hny⟩
            rcases hy with rfl | hy
            · simp at hny
            · exact ⟨hy, fun hyY => hny (Or.inr hyY)⟩
          · rintro ⟨hy, hny⟩
            refine ⟨Or.inr hy, ?_⟩
            rintro (rfl | hyY)
            · exact absurd hy hmem
            · exact absurd hyY hny
        have hinter : ∀ Z : Finset α, e ∉ Z → ({e} : Finset α) ∩ Z = ∅ := by
          intro Z heZ
          ext y
          simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty]
          constructor
          · rintro ⟨rfl, hy⟩
            exact absurd hy heZ
          · intro h
            exact False.elim h
        have hinter2 : ∀ Y : Finset α, X ∩ insert e Y = X ∩ Y := by
          intro Y
          ext y
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hyX, rfl | hyY⟩
            · exact absurd hyX heX
            · exact ⟨hyX, hyY⟩
          · rintro ⟨hyX, hyY⟩
            exact ⟨hyX, Or.inr hyY⟩
        have hunion2 : ∀ Y : Finset α, X ∪ insert e Y = insert e (X ∪ Y) := by
          intro Y
          ext y
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto
        have hinter3 : ∀ Y : Finset α, (E₀ \ X) ∩ insert e (E₀ \ Y) = E₀ \ (X ∪ Y) := by
          intro Y
          ext y
          simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert,
            Finset.mem_union]
          constructor
          · rintro ⟨⟨hyE, hnyX⟩, rfl | ⟨hyE', hnyY⟩⟩
            · exact absurd hyE hmem
            · exact ⟨hyE, fun h => h.elim hnyX hnyY⟩
          · rintro ⟨hyE, hny⟩
            exact ⟨⟨hyE, fun hx => hny (Or.inl hx)⟩,
              Or.inr ⟨hyE, fun hy => hny (Or.inr hy)⟩⟩
        have hunion3 : ∀ Y : Finset α,
            (E₀ \ X) ∪ insert e (E₀ \ Y) = insert e (E₀ \ (X ∩ Y)) := by
          intro Y
          ext y
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
            Finset.mem_inter]
          tauto
        have hcutX := hcut X (hXE.trans (Finset.subset_insert e E₀))
        rw [hsd1 X heX] at hcutX
        have hcutXe := hcut (insert e X) (Finset.insert_subset_insert e hXE)
        rw [hsd2 X hXE] at hcutXe
        have hloop1 : r₁ {e} = 1 := by
          have hle := hle₁ {e}
          have hsub := hsub₁ {e} X
          rw [hinter X heX, Finset.singleton_union, hr10] at hsub
          simp only [Finset.card_singleton] at hle
          omega
        have hloop2 : r₂ {e} = 1 := by
          have hle := hle₂ {e}
          have hsub := hsub₂ {e} (E₀ \ X)
          rw [hinter (E₀ \ X) heEX, Finset.singleton_union, hr20] at hsub
          simp only [Finset.card_singleton] at hle
          omega
        by_cases hcon : ∀ Y : Finset α, Y ⊆ E₀ →
            n ≤ (r₁ (insert e Y) - 1) + (r₂ (insert e (E₀ \ Y)) - 1)
        · have hle₁' : ∀ Z : Finset α, r₁ (insert e Z) - 1 ≤ Z.card := by
            intro Z
            have h1 := hle₁ (insert e Z)
            have h2 := Finset.card_insert_le e Z
            omega
          have hle₂' : ∀ Z : Finset α, r₂ (insert e Z) - 1 ≤ Z.card := by
            intro Z
            have h1 := hle₂ (insert e Z)
            have h2 := Finset.card_insert_le e Z
            omega
          have hmono₁' : ∀ X Y : Finset α, X ⊆ Y →
              r₁ (insert e X) - 1 ≤ r₁ (insert e Y) - 1 := by
            intro X Y hXY
            exact Nat.sub_le_sub_right (hmono₁ _ _ (Finset.insert_subset_insert e hXY)) 1
          have hmono₂' : ∀ X Y : Finset α, X ⊆ Y →
              r₂ (insert e X) - 1 ≤ r₂ (insert e Y) - 1 := by
            intro X Y hXY
            exact Nat.sub_le_sub_right (hmono₂ _ _ (Finset.insert_subset_insert e hXY)) 1
          have hsub₁' : ∀ X Y : Finset α,
              (r₁ (insert e (X ∩ Y)) - 1) + (r₁ (insert e (X ∪ Y)) - 1) ≤
              (r₁ (insert e X) - 1) + (r₁ (insert e Y) - 1) := by
            intro X Y
            have h := hsub₁ (insert e X) (insert e Y)
            have hi : (insert e X) ∩ (insert e Y) = insert e (X ∩ Y) := by
              ext y
              simp only [Finset.mem_inter, Finset.mem_insert]
              tauto
            have hu : (insert e X) ∪ (insert e Y) = insert e (X ∪ Y) := by
              ext y
              simp only [Finset.mem_union, Finset.mem_insert]
              tauto
            rw [hi, hu] at h
            have g1 : 1 ≤ r₁ (insert e (X ∩ Y)) := by
              rw [← hloop1]
              exact hmono₁ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
            have g2 : 1 ≤ r₁ (insert e (X ∪ Y)) := by
              rw [← hloop1]
              exact hmono₁ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
            omega
          have hsub₂' : ∀ X Y : Finset α,
              (r₂ (insert e (X ∩ Y)) - 1) + (r₂ (insert e (X ∪ Y)) - 1) ≤
              (r₂ (insert e X) - 1) + (r₂ (insert e Y) - 1) := by
            intro X Y
            have h := hsub₂ (insert e X) (insert e Y)
            have hi : (insert e X) ∩ (insert e Y) = insert e (X ∩ Y) := by
              ext y
              simp only [Finset.mem_inter, Finset.mem_insert]
              tauto
            have hu : (insert e X) ∪ (insert e Y) = insert e (X ∪ Y) := by
              ext y
              simp only [Finset.mem_union, Finset.mem_insert]
              tauto
            rw [hi, hu] at h
            have g1 : 1 ≤ r₂ (insert e (X ∩ Y)) := by
              rw [← hloop2]
              exact hmono₂ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
            have g2 : 1 ≤ r₂ (insert e (X ∪ Y)) := by
              rw [← hloop2]
              exact hmono₂ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
            omega
          obtain ⟨J, hJsub, hcJ1, hcJ2, hJk⟩ :=
            ih n _ _ hle₁' hle₂' hmono₁' hmono₂' hsub₁' hsub₂' hcon
          have heJ : e ∉ J := fun h => hmem (hJsub h)
          have gJ1 : 1 ≤ r₁ (insert e J) := by
            rw [← hloop1]
            exact hmono₁ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
          have gJ2 : 1 ≤ r₂ (insert e J) := by
            rw [← hloop2]
            exact hmono₂ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
          have hcJ1' : r₁ (insert e J) - 1 = J.card := hcJ1
          have hcJ2' : r₂ (insert e J) - 1 = J.card := hcJ2
          have hcardJ : (insert e J).card = J.card + 1 := Finset.card_insert_of_notMem heJ
          refine ⟨insert e J, Finset.insert_subset_insert e hJsub, ?_, ?_, ?_⟩
          · omega
          · omega
          · omega
        · push Not at hcon
          obtain ⟨Y, hYE, hY⟩ := hcon
          have heY : e ∉ Y := fun h => hmem (hYE h)
          have geY1 : 1 ≤ r₁ (insert e Y) := by
            rw [← hloop1]
            exact hmono₁ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
          have geY2 : 1 ≤ r₂ (insert e (E₀ \ Y)) := by
            rw [← hloop2]
            exact hmono₂ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e _))
          have hcutY := hcut Y (hYE.trans (Finset.subset_insert e E₀))
          rw [hsd1 Y heY] at hcutY
          have hcutYe := hcut (insert e Y) (Finset.insert_subset_insert e hYE)
          rw [hsd2 Y hYE] at hcutYe
          have hsub1XY := hsub₁ X (insert e Y)
          rw [hinter2 Y, hunion2 Y] at hsub1XY
          have hsub2XY := hsub₂ (E₀ \ X) (insert e (E₀ \ Y))
          rw [hinter3 Y, hunion3 Y] at hsub2XY
          have heXY : e ∉ X ∩ Y := fun h => heX (Finset.mem_inter.mp h).1
          have hXYE : X ∪ Y ⊆ E₀ := Finset.union_subset hXE hYE
          have hcutXY1 := hcut (X ∩ Y)
            ((Finset.inter_subset_left.trans hXE).trans (Finset.subset_insert e E₀))
          rw [hsd1 (X ∩ Y) heXY] at hcutXY1
          have hcutXY2 := hcut (insert e (X ∪ Y)) (Finset.insert_subset_insert e hXYE)
          rw [hsd2 (X ∪ Y) hXYE] at hcutXY2
          omega

/--
**Edmonds' matroid intersection theorem.** Let $M_1$ and $M_2$ be matroids on a finite type
$\alpha$, with arbitrary ground sets, and let $k$ be a natural number. There is a set
$I \subseteq \alpha$ independent in both $M_1$ and $M_2$ with $|I| \ge k$ if and only if every
$X \subseteq \alpha$ satisfies $k \le r_1(X) + r_2(\alpha \setminus X)$, where $r_i(Y)$ is the
largest size of a subset of $Y$ independent in $M_i$.
-/
theorem edmonds_matroid_intersection'
    {α : Type*} [Finite α]
    {M₁ M₂ : Matroid α}
    {k : ℕ} :
    (∃ I : Finset α, M₁.Indep (I : Set α) ∧
      M₂.Indep (I : Set α) ∧ k ≤ I.card) ↔
    ∀ X : Set α, (k : ℕ∞) ≤ M₁.eRk X + M₂.eRk Xᶜ := by
  classical
  have := Fintype.ofFinite α
  constructor
  · rintro ⟨I, hI1, hI2, hk⟩ X
    have g1 : M₁.Indep ((↑I : Set α) ∩ X) := hI1.subset Set.inter_subset_left
    have g2 : M₂.Indep ((↑I : Set α) \ X) := hI2.subset Set.sdiff_subset
    have l1 := g1.encard_le_eRk_of_subset Set.inter_subset_right
    have l2 := g2.encard_le_eRk_of_subset (Set.sdiff_subset_compl (↑I : Set α) X)
    have hdis : Disjoint ((↑I : Set α) ∩ X) ((↑I : Set α) \ X) := by
      rw [Set.disjoint_left]
      rintro a ⟨haI, haX⟩ ha
      simp only [Set.mem_sdiff] at ha
      exact ha.2 haX
    have hunion : ((↑I : Set α) ∩ X) ∪ ((↑I : Set α) \ X) = (↑I : Set α) :=
      Set.inter_union_sdiff _ _
    have hcard : ((↑I : Set α)).encard = ((I.card : ℕ) : ℕ∞) :=
      Set.encard_coe_eq_coe_finsetCard I
    have hk' : ((k : ℕ) : ℕ∞) ≤ ((I.card : ℕ) : ℕ∞) :=
      ENat.natCast_le_natCast.mpr hk
    calc ((k : ℕ) : ℕ∞) ≤ ((I.card : ℕ) : ℕ∞) := hk'
      _ = ((↑I : Set α)).encard := hcard.symm
      _ = (((↑I : Set α) ∩ X)).encard + (((↑I : Set α) \ X)).encard := by
          rw [← Set.encard_union_eq hdis, hunion]
      _ ≤ M₁.eRk X + M₂.eRk Xᶜ := add_le_add l1 l2
  · intro hcut
    have hfin1 : ∀ X : Finset α, M₁.eRk (↑X : Set α) ≠ ⊤ := fun X =>
      Matroid.eRk_ne_top_iff.mpr (M₁.isRkFinite_of_finite X.finite_toSet)
    have hfin2 : ∀ X : Finset α, M₂.eRk (↑X : Set α) ≠ ⊤ := fun X =>
      Matroid.eRk_ne_top_iff.mpr (M₂.isRkFinite_of_finite X.finite_toSet)
    have hadd : ∀ (a b : ℕ∞), a ≠ ⊤ → b ≠ ⊤ → a + b ≠ ⊤ := by
      intro a b ha hb
      rw [← ENat.natCast_toNat ha, ← ENat.natCast_toNat hb, ← Nat.cast_add]
      exact ENat.natCast_ne_top _
    have hle₁ : ∀ X : Finset α, (M₁.eRk ↑X).toNat ≤ X.card := by
      intro X
      have h := M₁.eRk_le_encard (↑X : Set α)
      rw [Set.encard_coe_eq_coe_finsetCard] at h
      have h2 := ENat.toNat_le_toNat h (ENat.natCast_ne_top X.card)
      rwa [ENat.toNat_natCast] at h2
    have hle₂ : ∀ X : Finset α, (M₂.eRk ↑X).toNat ≤ X.card := by
      intro X
      have h := M₂.eRk_le_encard (↑X : Set α)
      rw [Set.encard_coe_eq_coe_finsetCard] at h
      have h2 := ENat.toNat_le_toNat h (ENat.natCast_ne_top X.card)
      rwa [ENat.toNat_natCast] at h2
    have hmono₁ : ∀ X Y : Finset α, X ⊆ Y → (M₁.eRk ↑X).toNat ≤ (M₁.eRk ↑Y).toNat := by
      intro X Y hXY
      have hXY' : (↑X : Set α) ⊆ ↑Y := by exact_mod_cast hXY
      exact ENat.toNat_le_toNat (M₁.eRk_mono hXY') (hfin1 Y)
    have hmono₂ : ∀ X Y : Finset α, X ⊆ Y → (M₂.eRk ↑X).toNat ≤ (M₂.eRk ↑Y).toNat := by
      intro X Y hXY
      have hXY' : (↑X : Set α) ⊆ ↑Y := by exact_mod_cast hXY
      exact ENat.toNat_le_toNat (M₂.eRk_mono hXY') (hfin2 Y)
    have hsub₁ : ∀ X Y : Finset α,
        (M₁.eRk ↑(X ∩ Y)).toNat + (M₁.eRk ↑(X ∪ Y)).toNat ≤
        (M₁.eRk ↑X).toNat + (M₁.eRk ↑Y).toNat := by
      intro X Y
      have h := M₁.eRk_inter_add_eRk_union_le (↑X : Set α) (↑Y : Set α)
      rw [← Finset.coe_inter, ← Finset.coe_union] at h
      have h2 := ENat.toNat_le_toNat h (hadd _ _ (hfin1 X) (hfin1 Y))
      have eL := ENat.toNat_add (hfin1 (X ∩ Y)) (hfin1 (X ∪ Y))
      have eR := ENat.toNat_add (hfin1 X) (hfin1 Y)
      rw [eL, eR] at h2
      exact h2
    have hsub₂ : ∀ X Y : Finset α,
        (M₂.eRk ↑(X ∩ Y)).toNat + (M₂.eRk ↑(X ∪ Y)).toNat ≤
        (M₂.eRk ↑X).toNat + (M₂.eRk ↑Y).toNat := by
      intro X Y
      have h := M₂.eRk_inter_add_eRk_union_le (↑X : Set α) (↑Y : Set α)
      rw [← Finset.coe_inter, ← Finset.coe_union] at h
      have h2 := ENat.toNat_le_toNat h (hadd _ _ (hfin2 X) (hfin2 Y))
      have eL := ENat.toNat_add (hfin2 (X ∩ Y)) (hfin2 (X ∪ Y))
      have eR := ENat.toNat_add (hfin2 X) (hfin2 Y)
      rw [eL, eR] at h2
      exact h2
    have hcut' : ∀ X : Finset α, X ⊆ Finset.univ →
        k ≤ (M₁.eRk ↑X).toNat + (M₂.eRk ↑(Finset.univ \ X)).toNat := by
      intro X _
      have h := hcut (↑X : Set α)
      have hcomp : ((↑X : Set α))ᶜ = ((Finset.univ \ X : Finset α) : Set α) := by
        rw [Finset.coe_sdiff, Finset.coe_univ, ← Set.compl_eq_univ_sdiff]
      rw [hcomp] at h
      have h2 := ENat.toNat_le_toNat h (hadd _ _ (hfin1 X) (hfin2 _))
      have eS := ENat.toNat_add (hfin1 X) (hfin2 (Finset.univ \ X))
      rw [eS, ENat.toNat_natCast] at h2
      exact h2
    obtain ⟨I, -, hI1, hI2, hIk⟩ :=
      exists_common_indep_of_cut_le Finset.univ k _ _ hle₁ hle₂ hmono₁ hmono₂
        hsub₁ hsub₂ hcut'
    refine ⟨I, ?_, ?_, hIk⟩
    · have hI1' : (M₁.eRk (↑I : Set α)).toNat = I.card := hI1
      have hne := hfin1 I
      have he : M₁.eRk (↑I : Set α) = ((↑I : Set α)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, ← hI1']
        exact (ENat.natCast_toNat hne).symm
      exact (Matroid.indep_iff_eRk_eq_encard_of_finite I.finite_toSet).mpr he
    · have hI2' : (M₂.eRk (↑I : Set α)).toNat = I.card := hI2
      have hne := hfin2 I
      have he : M₂.eRk (↑I : Set α) = ((↑I : Set α)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, ← hI2']
        exact (ENat.natCast_toNat hne).symm
      exact (Matroid.indep_iff_eRk_eq_encard_of_finite I.finite_toSet).mpr he

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedVariables false in
/--
**Edmonds' matroid intersection theorem for matroids on the whole type.** Let $M_1$ and $M_2$ be
matroids on a finite type $\alpha$, each with ground set all of $\alpha$, and let $k$ be a natural
number. There is a set $I \subseteq \alpha$ independent in both $M_1$ and $M_2$ with $|I| \ge k$
if and only if every $X \subseteq \alpha$ satisfies $k \le r_1(X) + r_2(\alpha \setminus X)$,
where $r_i$ is the rank function of $M_i$.

The hypotheses on the ground sets are not needed; the general version drops them.

Proves `Wanted` entry `edmonds_matroid_intersection`.

Source: J. Edmonds, Submodular Functions, Matroids, and Certain Polyhedra, Combinatorial Structures
and Their Applications (1970), 69–87.
-/
theorem edmonds_matroid_intersection
    {α : Type*} [Fintype α] [DecidableEq α]
    {M₁ M₂ : Matroid α}
    (h₁ : M₁.E = Set.univ) (h₂ : M₂.E = Set.univ)
    {k : ℕ} :
    (∃ I : Finset α, M₁.Indep (I : Set α) ∧
      M₂.Indep (I : Set α) ∧ k ≤ I.card) ↔
    ∀ X : Set α, (k : ℕ∞) ≤ M₁.eRk X + M₂.eRk Xᶜ :=
  edmonds_matroid_intersection'

end MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted
