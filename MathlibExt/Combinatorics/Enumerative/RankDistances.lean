/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Kendall's tau distance, Spearman's footrule, and the Diaconis-Graham
inequality on permutations of `Fin n`.

Sources: R. Fagin, R. Kumar and D. Sivakumar, "Comparing top k lists",
SIAM Journal on Discrete Mathematics 17(1), 2003, Section 2 (definitions
of Kendall's tau and Spearman's footrule for permutations, where a
permutation `σ` is a bijection from a domain `D` onto `[n]` and `σ(i)`
is the rank of item `i`), and equation (17) there, which attributes
`K ≤ F ≤ 2K` to Diaconis and Graham (1977). The Diaconis-Graham primary
source is cited through Fagin-Kumar-Sivakumar.

Here `D = Fin n` and a permutation is `Equiv.Perm (Fin n)` read as
item-to-rank with 0-based ranks; relative orders and absolute rank
differences agree with the 1-based convention of the source.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import MathlibExt.Combinatorics.Enumerative.PermutationInversions
public import MathlibExt.Order.StrictTotalOrder
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.NatAbs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators
open Finset

namespace MetaMathlibExt

/-- Items `i` and `j` are discordant between rankings `σ` and `τ` when
they appear in opposite orders: one ranking puts `i` ahead of `j` and
the other puts `j` ahead of `i`. -/
def Discordant {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  (σ i < σ j ∧ τ j < τ i) ∨ (σ j < σ i ∧ τ i < τ j)

/-- Decidability of discordance (order comparisons on `Fin n`). -/
instance discordantDecidable {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Decidable (Discordant σ τ i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Kendall's tau distance: the number of unordered pairs of distinct
items whose relative order differs between `σ` and `τ`, counted here as
pairs `(i, j)` with `i < j` in the index order; this agrees with the
social-choice Kendall tau of the induced orders (see
`MathlibExt.GameTheory.SocialChoice.kendallTau_eq_kendallTau_orderOfPerm`). -/
def kendallTau {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ Discordant σ τ p.1 p.2)).card

/-- Spearman's footrule: the `L1` distance `∑ i, |σ i - τ i|` between
the two rankings, with ranks read through `Fin.val` and the absolute
difference taken in `ℤ`. -/
def spearmanFootrule {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i, Int.natAbs ((σ i).val - (τ i).val : ℤ)

/-- No pair is discordant between a ranking and itself. -/
theorem discordant_self_false {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    ¬ Discordant σ σ i j := by
  intro h
  unfold Discordant at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact lt_irrefl _ (lt_trans h1 h2)

/-- Discordance is symmetric in the two rankings. -/
theorem discordant_arg_comm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Discordant σ τ i j ↔ Discordant τ σ i j := by
  unfold Discordant
  tauto

/-- Discordance is symmetric in the two items. -/
theorem discordant_pair_comm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Discordant σ τ i j ↔ Discordant σ τ j i := by
  unfold Discordant
  exact or_comm

/-- No item is discordant with itself. -/
theorem discordant_irrefl {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i : Fin n) :
    ¬ Discordant σ τ i i := by
  intro h
  unfold Discordant at h
  rcases h with (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact lt_irrefl _ h1

/-- Discordant items are distinct. -/
theorem discordant_ne {n : ℕ} (σ τ : Equiv.Perm (Fin n)) {i j : Fin n}
    (h : Discordant σ τ i j) : i ≠ j := by
  intro heq
  subst heq
  exact discordant_irrefl σ τ _ h

/-- Per-pair triangle inequality for discordance indicators: if `i, j`
are discordant between `σ` and `ρ`, they are discordant between `σ`
and `τ` or between `τ` and `ρ`. -/
theorem discordant_triangle_pair {n : ℕ} (σ τ ρ : Equiv.Perm (Fin n)) {i j : Fin n}
    (hne : i ≠ j) (h : Discordant σ ρ i j) :
    Discordant σ τ i j ∨ Discordant τ ρ i j := by
  have hτ : τ i ≠ τ j := fun e => hne (τ.injective e)
  rcases h with (⟨hσ, hρ⟩ | ⟨hσ, hρ⟩)
  · rcases lt_or_gt_of_ne hτ with hτ | hτ
    · exact Or.inr (Or.inl ⟨hτ, hρ⟩)
    · exact Or.inl (Or.inl ⟨hσ, hτ⟩)
  · rcases lt_or_gt_of_ne hτ with hτ | hτ
    · exact Or.inl (Or.inr ⟨hσ, hτ⟩)
    · exact Or.inr (Or.inr ⟨hτ, hρ⟩)

/-- Kendall's tau of a ranking against itself is `0`. -/
theorem kendallTau_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    kendallTau σ σ = 0 := by
  unfold kendallTau
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨-, h⟩
  exact discordant_self_false σ _ _ h

/-- Kendall's tau is symmetric. -/
theorem kendallTau_comm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    kendallTau σ τ = kendallTau τ σ := by
  unfold kendallTau
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [discordant_arg_comm]

/-- A zero Kendall tau leaves no discordant pair below the diagonal. -/
theorem not_discordant_of_kendallTau_eq_zero {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : kendallTau σ τ = 0) {i j : Fin n} (hij : i < j) :
    ¬ Discordant σ τ i j := by
  unfold kendallTau at h
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h
  have hmem := h (i, j)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  intro hd
  exact hmem ⟨hij, hd⟩

/-- With no discordant pair anywhere, both rankings order every pair
of items the same way. -/
theorem order_iff_of_no_discordant {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : ∀ i j : Fin n, i < j → ¬ Discordant σ τ i j)
    (i j : Fin n) : (σ i < σ j) ↔ (τ i < τ j) := by
  have hne : ∀ {a b : Fin n}, a ≠ b → ¬ Discordant σ τ a b := by
    intro a b hab hd
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact h a b hlt hd
    · exact h b a hlt ((discordant_pair_comm σ τ a b).mp hd)
  constructor
  · intro hs
    by_cases heq : i = j
    · subst heq
      exact absurd hs (lt_irrefl _)
    · rcases lt_trichotomy (τ i) (τ j) with hlt | hlt | hlt
      · exact hlt
      · exact absurd (τ.injective hlt) heq
      · exact absurd (Or.inl ⟨hs, hlt⟩) (hne heq)
  · intro ht
    by_cases heq : i = j
    · subst heq
      exact absurd ht (lt_irrefl _)
    · rcases lt_trichotomy (σ i) (σ j) with hlt | hlt | hlt
      · exact hlt
      · exact absurd (σ.injective hlt) heq
      · exact absurd (Or.inr ⟨hlt, ht⟩) (hne heq)

/-- A rank equals the number of items ranked strictly before it. -/
theorem val_eq_card_filter_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (σ i).val = (Finset.univ.filter (fun j => σ j < σ i)).card := by
  have himg : Finset.image σ (Finset.univ.filter (fun j => σ j < σ i)) =
      Finset.Iio (σ i) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    constructor
    · rintro ⟨j, hlt, rfl⟩
      exact hlt
    · intro hlt
      exact ⟨σ.symm k, by simpa using hlt, Equiv.apply_symm_apply σ k⟩
  have hcard := Finset.card_image_of_injective
    (Finset.univ.filter (fun j => σ j < σ i)) σ.injective
  rw [himg, Fin.card_Iio] at hcard
  exact hcard

/-- Kendall's tau is `0` exactly for equal rankings. -/
theorem kendallTau_eq_zero_iff {n : ℕ} {σ τ : Equiv.Perm (Fin n)} :
    kendallTau σ τ = 0 ↔ σ = τ := by
  constructor
  · intro h
    have hno : ∀ i j : Fin n, i < j → ¬ Discordant σ τ i j :=
      fun i j hij => not_discordant_of_kendallTau_eq_zero h hij
    have hord : ∀ i j : Fin n, (σ i < σ j) ↔ (τ i < τ j) :=
      fun i j => order_iff_of_no_discordant σ τ hno i j
    apply Equiv.ext
    intro i
    apply Fin.val_injective
    have e1 := val_eq_card_filter_lt σ i
    have e2 := val_eq_card_filter_lt τ i
    rw [e1, e2]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hord j i
  · intro h
    subst h
    exact kendallTau_self _

/-- Kendall's tau satisfies the triangle inequality. -/
theorem kendallTau_triangle {n : ℕ} (σ τ ρ : Equiv.Perm (Fin n)) :
    kendallTau σ ρ ≤ kendallTau σ τ + kendallTau τ ρ := by
  unfold kendallTau
  refine le_trans ?_ (Finset.card_union_le _ _)
  apply Finset.card_le_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rintro ⟨hij, h⟩
  rcases discordant_triangle_pair σ τ ρ (ne_of_lt hij) h with h | h
  · exact Or.inl ⟨hij, h⟩
  · exact Or.inr ⟨hij, h⟩

/-- Spearman's footrule of a ranking against itself is `0`. -/
theorem spearmanFootrule_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    spearmanFootrule σ σ = 0 := by
  simp [spearmanFootrule]

/-- Spearman's footrule is symmetric. -/
theorem spearmanFootrule_comm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    spearmanFootrule σ τ = spearmanFootrule τ σ := by
  unfold spearmanFootrule
  apply Finset.sum_congr rfl
  intro i _
  have h : ((σ i).val : ℤ) - (τ i).val = -(((τ i).val : ℤ) - (σ i).val) := by ring
  rw [h, Int.natAbs_neg]

/-- Spearman's footrule is `0` exactly for equal rankings. -/
theorem spearmanFootrule_eq_zero_iff {n : ℕ} {σ τ : Equiv.Perm (Fin n)} :
    spearmanFootrule σ τ = 0 ↔ σ = τ := by
  constructor
  · intro h
    unfold spearmanFootrule at h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)] at h
    apply Equiv.ext
    intro i
    have hi := h i (Finset.mem_univ i)
    rw [Int.natAbs_eq_zero] at hi
    have hcast : ((σ i).val : ℤ) = (τ i).val := sub_eq_zero.mp hi
    have hval : (σ i).val = (τ i).val := by exact_mod_cast hcast
    exact Fin.val_injective hval
  · intro h
    subst h
    exact spearmanFootrule_self _

/-- Spearman's footrule satisfies the triangle inequality. -/
theorem spearmanFootrule_triangle {n : ℕ} (σ τ ρ : Equiv.Perm (Fin n)) :
    spearmanFootrule σ ρ ≤ spearmanFootrule σ τ + spearmanFootrule τ ρ := by
  unfold spearmanFootrule
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h : ((σ i).val : ℤ) - (ρ i).val
      = (((σ i).val : ℤ) - (τ i).val) + (((τ i).val : ℤ) - (ρ i).val) := by ring
  rw [h]
  exact Int.natAbs_add_le _ _

/-- The identity ranking fixes every item. -/
theorem perm_one_apply {n : ℕ} (x : Fin n) : (1 : Equiv.Perm (Fin n)) x = x := rfl

/-- Relabeling items by `τ`: discordance between `σ` and `τ` is
discordance between `σ * τ.symm` and `1` at the relabeled items. -/
theorem discordant_relabel {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Discordant σ τ i j ↔ Discordant (σ * τ.symm) 1 (τ i) (τ j) := by
  unfold Discordant
  simp only [Equiv.Perm.mul_apply, Equiv.symm_apply_apply, perm_one_apply]

/-- Twice Kendall's tau counts all ordered discordant pairs: below- and
above-diagonal pairs are in bijection via swapping coordinates. -/
theorem card_filter_discordant_all {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun p : Fin n × Fin n => Discordant σ τ p.1 p.2)).card =
      kendallTau σ τ + kendallTau σ τ := by
  have hswap : Finset.image Prod.swap
        (Finset.univ.filter
          (fun p : Fin n × Fin n => p.2 < p.1 ∧ Discordant σ τ p.1 p.2)) =
        Finset.univ.filter
          (fun p : Fin n × Fin n => p.1 < p.2 ∧ Discordant σ τ p.1 p.2) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, ⟨hlt, hdp⟩, rfl⟩
      exact ⟨hlt, (discordant_pair_comm σ τ p.1 p.2).mp hdp⟩
    · rintro ⟨hlt, hdp⟩
      exact ⟨Prod.swap q, ⟨hlt, (discordant_pair_comm σ τ q.1 q.2).mp hdp⟩, rfl⟩
  have hcardA : (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ Discordant σ τ p.1 p.2)).card =
      kendallTau σ τ := rfl
  have hcardB : (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2 < p.1 ∧ Discordant σ τ p.1 p.2)).card =
      kendallTau σ τ := by
    have hinj : Function.Injective (Prod.swap : Fin n × Fin n → Fin n × Fin n) := by
      apply Function.Involutive.injective
      intro p
      rfl
    have h := Finset.card_image_of_injective
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2 < p.1 ∧ Discordant σ τ p.1 p.2)) hinj
    rw [hswap] at h
    exact h.symm.trans hcardA
  have hunion : Finset.univ.filter (fun p : Fin n × Fin n => Discordant σ τ p.1 p.2) =
      Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ Discordant σ τ p.1 p.2) ∪
      Finset.univ.filter
        (fun p : Fin n × Fin n => p.2 < p.1 ∧ Discordant σ τ p.1 p.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hd
      rcases lt_or_gt_of_ne (discordant_ne σ τ hd) with hlt | hlt
      · exact Or.inl ⟨hlt, hd⟩
      · exact Or.inr ⟨hlt, hd⟩
    · rintro (⟨-, hd⟩ | ⟨-, hd⟩) <;> exact hd
  have hdisj : Disjoint
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ Discordant σ τ p.1 p.2))
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2 < p.1 ∧ Discordant σ τ p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rintro ⟨hlt, -⟩
    exact absurd (lt_trans hq.1 hlt) (lt_irrefl _)
  rw [hunion, Finset.card_union_of_disjoint hdisj, hcardA, hcardB]

/-- The ordered discordant pairs are preserved under relabeling items
by `τ`. -/
theorem card_all_relabel {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun p : Fin n × Fin n => Discordant σ τ p.1 p.2)).card =
    (Finset.univ.filter
      (fun p : Fin n × Fin n => Discordant (σ * τ.symm) 1 p.1 p.2)).card := by
  have himg : Finset.image (fun p : Fin n × Fin n => (τ p.1, τ p.2))
      (Finset.univ.filter (fun p : Fin n × Fin n => Discordant σ τ p.1 p.2)) =
      Finset.univ.filter
        (fun p : Fin n × Fin n => Discordant (σ * τ.symm) 1 p.1 p.2) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hdp, rfl⟩
      exact (discordant_relabel σ τ p.1 p.2).mp hdp
    · intro hdp
      have e1 : τ (τ.symm q.1) = q.1 := Equiv.apply_symm_apply τ q.1
      have e2 : τ (τ.symm q.2) = q.2 := Equiv.apply_symm_apply τ q.2
      refine ⟨(τ.symm q.1, τ.symm q.2), ?_, ?_⟩
      · have hmem : Discordant (σ * τ.symm) 1 (τ (τ.symm q.1)) (τ (τ.symm q.2)) := by
          rw [e1, e2]
          exact hdp
        exact (discordant_relabel σ τ _ _).mpr hmem
      · exact Prod.ext e1 e2
  have hinj : Function.Injective (fun p : Fin n × Fin n => (τ p.1, τ p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext (τ.injective h1) (τ.injective h2)
  have h := Finset.card_image_of_injective
    (Finset.univ.filter (fun p : Fin n × Fin n => Discordant σ τ p.1 p.2)) hinj
  rw [himg] at h
  exact h.symm

/-- Kendall's tau is invariant under simultaneous relabeling of items:
it suffices to compare one permutation against the identity. -/
theorem kendallTau_relabel {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    kendallTau σ τ = kendallTau (σ * τ.symm) 1 := by
  have h1 := card_filter_discordant_all σ τ
  have h2 := card_filter_discordant_all (σ * τ.symm) 1
  have h3 := card_all_relabel σ τ
  omega

/-- Spearman's footrule is invariant under simultaneous relabeling of
items. -/
theorem spearmanFootrule_relabel {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    spearmanFootrule σ τ = spearmanFootrule (σ * τ.symm) 1 := by
  have hsum : (∑ i, Int.natAbs ((σ i).val - (τ i).val : ℤ)) =
      ∑ i, Int.natAbs ((σ (τ.symm i)).val - (τ (τ.symm i)).val : ℤ) :=
    (Equiv.sum_comp τ.symm _).symm
  unfold spearmanFootrule
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, perm_one_apply]

/-- Against the identity, discordance below the diagonal is just an
inversion of `π`. -/
theorem discordant_one_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i < j) : Discordant π 1 i j ↔ π j < π i := by
  unfold Discordant
  simp only [perm_one_apply]
  constructor
  · rintro (⟨-, hji⟩ | ⟨hji, -⟩)
    · exact absurd hji (not_lt_of_gt hij)
    · exact hji
  · intro h
    exact Or.inr ⟨h, hij⟩

/-- Kendall's tau against the identity is the inversion count. -/
theorem kendallTau_one_eq {n : ℕ} (π : Equiv.Perm (Fin n)) :
    kendallTau π 1 = MetaMathlibExt.permInversionCount π := by
  unfold kendallTau MetaMathlibExt.permInversionCount MetaMathlibExt.permInversions
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hij, hd⟩
    exact ⟨hij, (discordant_one_of_lt π hij).mp hd⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, (discordant_one_of_lt π hij).mpr h⟩

/-- The identity ranking has value `i.val` at `i`. -/
theorem one_apply_val {n : ℕ} (i : Fin n) :
    ((1 : Equiv.Perm (Fin n)) i).val = i.val := rfl

/-- Footrule against the identity is the total displacement. -/
theorem spearmanFootrule_one_eq {n : ℕ} (π : Equiv.Perm (Fin n)) :
    spearmanFootrule π 1 = ∑ i, Int.natAbs (((π i).val : ℤ) - (i.val : ℤ)) := by
  unfold spearmanFootrule
  apply Finset.sum_congr rfl
  intro i _
  rw [one_apply_val]

/-- `L j`: earlier items ranked after `j`. -/
def leftCount {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun k => k < j ∧ π j < π k)).card

/-- `R j`: later items ranked before `j`. -/
def rightCount {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun k => j < k ∧ π k < π j)).card

/-- Rank balance: `(π j).val + L j = j.val + R j`. Both sides count
predecessors of `j` in rank and in index, split at `j`. -/
theorem disp_balance {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    (π j).val + leftCount π j = j.val + rightCount π j := by
  have e1 : (π j).val =
      (Finset.univ.filter (fun k => k < j ∧ π k < π j)).card + rightCount π j := by
    have hunion : Finset.univ.filter (fun k => π k < π j) =
        Finset.univ.filter (fun k => k < j ∧ π k < π j) ∪
        Finset.univ.filter (fun k => j < k ∧ π k < π j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hk
        have hne : k ≠ j := by
          intro heq
          subst heq
          exact lt_irrefl _ hk
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨hlt, hk⟩
        · exact Or.inr ⟨hlt, hk⟩
      · rintro (⟨-, hk⟩ | ⟨-, hk⟩) <;> exact hk
    have hdisj : Disjoint
        (Finset.univ.filter (fun k => k < j ∧ π k < π j))
        (Finset.univ.filter (fun k => j < k ∧ π k < π j)) := by
      rw [Finset.disjoint_left]
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rintro ⟨hlt, -⟩
      exact absurd (lt_trans hk.1 hlt) (lt_irrefl _)
    have hval := val_eq_card_filter_lt π j
    rw [hunion, Finset.card_union_of_disjoint hdisj] at hval
    unfold rightCount
    exact hval
  have e2 : j.val =
      (Finset.univ.filter (fun k => k < j ∧ π k < π j)).card + leftCount π j := by
    have hunion : Finset.univ.filter (fun k => k < j) =
        Finset.univ.filter (fun k => k < j ∧ π k < π j) ∪
        Finset.univ.filter (fun k => k < j ∧ π j < π k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hk
        have hne : π k ≠ π j := fun heq => ne_of_lt hk (π.injective heq)
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨hk, hlt⟩
        · exact Or.inr ⟨hk, hlt⟩
      · rintro (⟨hk, -⟩ | ⟨hk, -⟩) <;> exact hk
    have hdisj : Disjoint
        (Finset.univ.filter (fun k => k < j ∧ π k < π j))
        (Finset.univ.filter (fun k => k < j ∧ π j < π k)) := by
      rw [Finset.disjoint_left]
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rintro ⟨-, hlt⟩
      exact absurd (lt_trans hk.2 hlt) (lt_irrefl _)
    have hval : (Finset.univ.filter (fun k : Fin n => k < j)).card = j.val := by
      have hIio : Finset.univ.filter (fun k : Fin n => k < j) = Finset.Iio j := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      rw [hIio]
      exact Fin.card_Iio j
    rw [hunion, Finset.card_union_of_disjoint hdisj] at hval
    unfold leftCount
    exact hval.symm
  omega

/-- Each displacement is bounded by `L j + R j`. -/
theorem natAbs_disp_le {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    Int.natAbs (((π j).val : ℤ) - (j.val : ℤ)) ≤ leftCount π j + rightCount π j := by
  have hbal := disp_balance π j
  have heq : (((π j).val : ℤ) - (j.val : ℤ)) =
      ((rightCount π j : ℕ) : ℤ) - ((leftCount π j : ℕ) : ℤ) := by
    omega
  rw [heq]
  calc Int.natAbs (((rightCount π j : ℕ) : ℤ) - ((leftCount π j : ℕ) : ℤ))
      ≤ Int.natAbs ((rightCount π j : ℕ) : ℤ)
        + Int.natAbs ((leftCount π j : ℕ) : ℤ) :=
        Int.natAbs_sub_le _ _
    _ = leftCount π j + rightCount π j := by
        rw [Int.natAbs_natCast, Int.natAbs_natCast]
        omega

/-- Fibers of the inversion set over the first coordinate count `R`. -/
theorem fiber_fst_card {n : ℕ} (π : Equiv.Perm (Fin n)) (b : Fin n) :
    ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)).filter
      (fun p => p.1 = b)).card = rightCount π b := by
  have himg : Finset.image Prod.snd
      ((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)).filter
        (fun p => p.1 = b)) =
      Finset.univ.filter (fun k => b < k ∧ π k < π b) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, ⟨⟨⟨hlt1, hlt2⟩, heq⟩, hsnd⟩⟩
      rw [heq, hsnd] at hlt1 hlt2
      exact ⟨hlt1, hlt2⟩
    · rintro ⟨hlt1, hlt2⟩
      exact ⟨(b, k), ⟨⟨⟨hlt1, hlt2⟩, rfl⟩, rfl⟩⟩
  have hinj : Set.InjOn Prod.snd
      ((↑((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)).filter
        (fun p => p.1 = b)) : Set (Fin n × Fin n))) := by
    intro p hp q hq h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨-, heqp⟩ := hp
    obtain ⟨-, heqq⟩ := hq
    exact Prod.ext (heqp.trans heqq.symm) h
  have h := Finset.card_image_of_injOn hinj
  rw [himg] at h
  unfold rightCount
  exact h.symm

/-- Fibers of the inversion set over the second coordinate count `L`. -/
theorem fiber_snd_card {n : ℕ} (π : Equiv.Perm (Fin n)) (b : Fin n) :
    ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)).filter
      (fun p => p.2 = b)).card = leftCount π b := by
  have himg : Finset.image Prod.fst
      ((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)).filter
        (fun p => p.2 = b)) =
      Finset.univ.filter (fun k => k < b ∧ π b < π k) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, ⟨⟨⟨hlt1, hlt2⟩, heq⟩, hfst⟩⟩
      rw [heq, hfst] at hlt1 hlt2
      exact ⟨hlt1, hlt2⟩
    · rintro ⟨hlt1, hlt2⟩
      exact ⟨(k, b), ⟨⟨⟨hlt1, hlt2⟩, rfl⟩, rfl⟩⟩
  have hinj : Set.InjOn Prod.fst
      ((↑((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)).filter
        (fun p => p.2 = b)) : Set (Fin n × Fin n))) := by
    intro p hp q hq h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨-, heqp⟩ := hp
    obtain ⟨-, heqq⟩ := hq
    exact Prod.ext h (heqp.trans heqq.symm)
  have h := Finset.card_image_of_injOn hinj
  rw [himg] at h
  unfold leftCount
  exact h.symm

/-- Summing `R` over all positions gives the inversion count. -/
theorem sum_rightCount_eq {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∑ j, rightCount π j = MetaMathlibExt.permInversionCount π := by
  have hmaps : Set.MapsTo Prod.fst
      ((↑(Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)) : Set (Fin n × Fin n)))
      ((↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) :=
    fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  unfold MetaMathlibExt.permInversionCount MetaMathlibExt.permInversions
  rw [hfib]
  exact Finset.sum_congr rfl (fun b _ => (fiber_fst_card π b).symm)

/-- Summing `L` over all positions gives the inversion count. -/
theorem sum_leftCount_eq {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∑ j, leftCount π j = MetaMathlibExt.permInversionCount π := by
  have hmaps : Set.MapsTo Prod.snd
      ((↑(Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)) : Set (Fin n × Fin n)))
      ((↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) :=
    fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  unfold MetaMathlibExt.permInversionCount MetaMathlibExt.permInversions
  rw [hfib]
  exact Finset.sum_congr rfl (fun b _ => (fiber_snd_card π b).symm)

/-- Diaconis-Graham upper bound against the identity. -/
theorem upper_bound_one {n : ℕ} (π : Equiv.Perm (Fin n)) :
    spearmanFootrule π 1 ≤ 2 * kendallTau π 1 := by
  rw [spearmanFootrule_one_eq, kendallTau_one_eq]
  have hsum : (∑ i, Int.natAbs (((π i).val : ℤ) - (i.val : ℤ))) ≤
      ∑ i, (leftCount π i + rightCount π i) :=
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => natAbs_disp_le π i)
  have hLR : (∑ i, (leftCount π i + rightCount π i)) =
      MetaMathlibExt.permInversionCount π + MetaMathlibExt.permInversionCount π := by
    rw [Finset.sum_add_distrib, sum_leftCount_eq, sum_rightCount_eq]
  omega

/-- Every absolute difference splits into upward plus downward parts. -/
theorem natAbs_sub_eq (A J : ℕ) :
    Int.natAbs ((A : ℤ) - (J : ℤ)) = (A - J) + (J - A) := by
  by_cases h : J ≤ A
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.sub_eq_zero_of_le h, add_zero]
  · have hle : A ≤ J := le_of_not_ge h
    rw [Nat.sub_eq_zero_of_le hle, zero_add]
    have hflip : ((A : ℤ) - J) = -(((J : ℤ) - A)) := by ring
    rw [hflip, Int.natAbs_neg, Int.natAbs_natCast_sub_natCast_of_ge hle]

/-- Type-`A` fibers over the second coordinate fit in the downward gap:
inversions `(i, b)` with `π b < i` are counted by `b.val - (π b).val`. -/
theorem fiberA_card {n : ℕ} (π : Equiv.Perm (Fin n)) (b : Fin n) :
    ((Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1)).filter
      (fun p => p.2 = b)).card ≤ b.val - (π b).val := by
  have himg : Finset.image (fun p : Fin n × Fin n => (p.1).val)
      ((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1)).filter
        (fun p => p.2 = b)) ⊆ Finset.Ico (π b).val (b.val) := by
    intro m hm
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico] at hm ⊢
    obtain ⟨p, hmem, rfl⟩ := hm
    obtain ⟨hA, heq⟩ := hmem
    obtain ⟨hlt1, hlt2, hlt3⟩ := hA
    rw [heq] at hlt1 hlt3
    exact ⟨le_of_lt hlt3, hlt1⟩
  have hinj : Set.InjOn (fun p : Fin n × Fin n => (p.1).val)
      ((↑((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1)).filter
        (fun p => p.2 = b)) : Set (Fin n × Fin n))) := by
    intro p hp q hq h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨-, heqp⟩ := hp
    obtain ⟨-, heqq⟩ := hq
    have h1 : p.1 = q.1 := Fin.val_injective h
    exact Prod.ext h1 (heqp.trans heqq.symm)
  have hcard := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card himg
  rw [Nat.card_Ico] at hle
  omega

/-- Type-`B` fibers over the first coordinate fit in the upward gap:
inversions `(a, j)` with `a ≤ π j` are counted by `(π a).val - a.val`. -/
theorem fiberB_card {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin n) :
    ((Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)).filter
      (fun p => p.1 = a)).card ≤ (π a).val - a.val := by
  have himg : Finset.image (fun p : Fin n × Fin n => (π p.2).val)
      ((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)).filter
        (fun p => p.1 = a)) ⊆ Finset.Ico (a.val) ((π a).val) := by
    intro m hm
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico] at hm ⊢
    obtain ⟨p, hmem, rfl⟩ := hm
    obtain ⟨hB, heq⟩ := hmem
    obtain ⟨hlt1, hlt2, hle3⟩ := hB
    rw [heq] at hlt2 hle3
    exact ⟨hle3, hlt2⟩
  have hinj : Set.InjOn (fun p : Fin n × Fin n => (π p.2).val)
      ((↑((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)).filter
        (fun p => p.1 = a)) : Set (Fin n × Fin n))) := by
    intro p hp q hq h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨-, heqp⟩ := hp
    obtain ⟨-, heqq⟩ := hq
    have h2 : p.2 = q.2 := π.injective (Fin.val_injective h)
    exact Prod.ext (heqp.trans heqq.symm) h2
  have hcard := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card himg
  rw [Nat.card_Ico] at hle
  omega

/-- Diaconis-Graham lower bound against the identity: split inversions
by whether `π j < i` or `i ≤ π j` and charge each side to the matching
one-sided displacement. -/
theorem lower_bound_one {n : ℕ} (π : Equiv.Perm (Fin n)) :
    kendallTau π 1 ≤ spearmanFootrule π 1 := by
  rw [kendallTau_one_eq, spearmanFootrule_one_eq]
  have hunion : (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1)) =
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1)) ∪
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hlt1, hlt2⟩
      rcases lt_or_ge (π q.2) (q.1) with hlt | hle
      · exact Or.inl ⟨hlt1, hlt2, hlt⟩
      · exact Or.inr ⟨hlt1, hlt2, hle⟩
    · rintro (⟨hlt1, hlt2, -⟩ | ⟨hlt1, hlt2, -⟩) <;> exact ⟨hlt1, hlt2⟩
  have hdisj : Disjoint
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1))
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)) := by
    rw [Finset.disjoint_left]
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rintro ⟨-, -, hle⟩
    exact absurd hle (not_le_of_gt hq.2.2)
  have hinv : MetaMathlibExt.permInversionCount π =
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1)).card +
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)).card := by
    unfold MetaMathlibExt.permInversionCount MetaMathlibExt.permInversions
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hsumA : (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1)).card ≤
      ∑ i, (i.val - (π i).val) := by
    have hmaps : Set.MapsTo Prod.snd
        ((↑(Finset.univ.filter
          (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ π p.2 < p.1)) :
          Set (Fin n × Fin n)))
        ((↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) :=
      fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
    have hfib := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hfib]
    exact Finset.sum_le_sum (fun b _ => fiberA_card π b)
  have hsumB : (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)).card ≤
      ∑ i, ((π i).val - i.val) := by
    have hmaps : Set.MapsTo Prod.fst
        ((↑(Finset.univ.filter
          (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1 ∧ p.1 ≤ π p.2)) :
          Set (Fin n × Fin n)))
        ((↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) :=
      fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
    have hfib := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hfib]
    exact Finset.sum_le_sum (fun a _ => fiberB_card π a)
  have hF : (∑ i, Int.natAbs (((π i).val : ℤ) - (i.val : ℤ))) =
      (∑ i, ((π i).val - i.val)) + (∑ i, (i.val - (π i).val)) := by
    have hpt : ∀ i ∈ Finset.univ, Int.natAbs (((π i).val : ℤ) - (i.val : ℤ)) =
        ((π i).val - i.val) + (i.val - (π i).val) :=
      fun i _ => natAbs_sub_eq _ _
    rw [Finset.sum_congr rfl hpt]
    exact Finset.sum_add_distrib
  omega

/-- Diaconis-Graham, lower bound: Kendall's tau is at most Spearman's
footrule. -/
theorem kendallTau_le_spearmanFootrule {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    kendallTau σ τ ≤ spearmanFootrule σ τ := by
  rw [kendallTau_relabel, spearmanFootrule_relabel]
  exact lower_bound_one _

/-- Diaconis-Graham, upper bound: Spearman's footrule is at most twice
Kendall's tau. -/
theorem spearmanFootrule_le_two_mul_kendallTau {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    spearmanFootrule σ τ ≤ 2 * kendallTau σ τ := by
  rw [spearmanFootrule_relabel, kendallTau_relabel]
  exact upper_bound_one _

/-- The strict total order on items induced by a ranking `σ` read as
item-to-rank: `i` precedes `j` exactly when `σ i < σ j`. -/
def orderOfPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MathlibExt.Order.StrictTotalOrder (Fin n) where
  lt := fun i j => σ i < σ j
  irrefl := fun i => lt_irrefl (σ i)
  trans := fun {a b c} h1 h2 => lt_trans h1 h2
  total := fun {a b} h => by
    have hne : σ a ≠ σ b := fun e => h (σ.injective e)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt

end MetaMathlibExt
