/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Monochrome symmetric subsets of infinite abelian groups (Kourovka Notebook Problem 15.77)

Every finite colouring admits a monochrome symmetric subset of each cardinality below that of
the group.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.77 (I. V. Protasov). UnsolvedMath record
UM-00701165 (`KOU-15.77`), dataset ulamai/UnsolvedMath v1.8.0.

Abelian groups are written additively, so `a = g b⁻¹ g` reads `a = 2g - b`, and a symmetric set is
one closed under `a ↦ 2g - a`. The number `n` of colours is arbitrary (the case `n ≤ 3` was known),
and `α` ranges over all cardinals below `|G|`, finite or infinite.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.MonochromeSymmetricSubsetKourovka15Problem77Wanted

/-- **Monochrome symmetric subsets (Kourovka 15.77).** The statement, written additively, that for
every infinite abelian group $G$, every cardinal $\alpha < |G|$, every natural number $n$ and every
colouring $\chi \colon G \to \{0, \dots, n - 1\}$, there are a set $A \subseteq G$ of cardinality
$\alpha$ on which $\chi$ is constant and an element $g \in G$ such that $2g - a \in A$ for every
$a \in A$; that is, $A$ is a monochrome set symmetric with respect to $g$. -/
def monochromeSymmetricSubsetExists : Prop :=
  ∀ (G : Type) [AddCommGroup G], Infinite G → ∀ α : Cardinal, α < Cardinal.mk G →
    ∀ (n : ℕ) (χ : G → Fin n), ∃ A : Set G, Cardinal.mk A = α ∧ (∃ c, ∀ a ∈ A, χ a = c) ∧
      ∃ g : G, ∀ a ∈ A, g + g - a ∈ A

open Cardinal Set
open scoped Cardinal

private theorem largeFiber {V K : Type} {P : Set V} {κ : Cardinal}
    (hκ : ℵ₀ ≤ κ) (hP : κ < #P) (hK : #K ≤ κ) (f : P → K) :
    ∃ (k : K) (S : Set V) (h : S ⊆ P), κ < #S ∧ ∀ x (hx : x ∈ S), f ⟨x, h hx⟩ = k := by
  obtain ⟨k, S, h, hS, hf⟩ := infinite_pigeonhole_set f (Order.succ κ)
    (Order.succ_le_of_lt hP) (hκ.trans (Order.le_succ _))
    ((hK.trans_lt (Order.lt_succ _)).trans_le (isRegular_succ hκ).2)
  exact ⟨k, S, h, (Order.lt_succ κ).trans_le hS, fun _ hx ↦ hf hx⟩

-- A colour on the two edges of a directed path with many possible middle vertices.
private theorem manyPaths {V : Type} {κ : Cardinal} (hκ : ℵ₀ ≤ κ) (hV : κ < #V)
    {n : ℕ} (col : V → V → Fin n) :
    ∃ x z c, κ ≤ #({y | col x y = c ∧ col y z = c} : Set V) := by
  classical
  by_contra! hpair
  -- All colours in s have small incoming fibres in P. Extend s by finding a
  -- large monochromatic outgoing fibre, then restricting P to that fibre.
  let rec step (s : Finset (Fin n)) (P : Set V) (hP : κ < #P)
      (hs : ∀ z, #({y ∈ P | col y z ∈ s} : Set V) < κ) : False := by
    obtain ⟨T, hTP, hT⟩ := le_mk_iff_exists_subset.mp hP.le
    have pick (z : P) : ∃ t : T, col t z ∉ s := by
      by_contra! h
      exact (hs z).not_ge (hT ▸ mk_le_mk_of_subset (show T ⊆ {y ∈ P | col y z ∈ s} from
        fun y hy ↦ ⟨hTP hy, h ⟨y, hy⟩⟩))
    choose t ht using pick
    let f (z : P) : T × Fin n := (t z, col (t z) z)
    have hK : #(T × Fin n) ≤ κ := by
      simp only [mk_prod, lift_id, hT]
      have hn := (lt_aleph0_of_finite (Fin n)).le.trans hκ
      exact (mul_le_mul_right hn κ).trans (mul_eq_self hκ).le
    obtain ⟨⟨a, c⟩, S, hSP, hS, hf⟩ := largeFiber hκ hP hK f
    have hc (z) (hz : z ∈ S) : col a z = c ∧ c ∉ s := by
      have he := hf z hz
      have ha : t ⟨z, hSP hz⟩ = a := congrArg Prod.fst he
      have hb : col (t ⟨z, hSP hz⟩) z = c := congrArg Prod.snd he
      exact ⟨ha ▸ hb, hb ▸ ht ⟨z, hSP hz⟩⟩
    obtain ⟨⟨z, hz⟩⟩ := mk_ne_zero_iff.mp (aleph0_pos.trans (hκ.trans_lt hS)).ne'
    have hcs := (hc z hz).2
    refine step (insert c s) S hS fun w ↦ ?_
    let B : Set V := {y ∈ P | col y w ∈ s}
    let D : Set V := {y | col a y = c ∧ col y w = c}
    have hsub : {y ∈ S | col y w ∈ insert c s} ⊆ B ∪ D := by
      rintro y ⟨hy, hyc⟩
      rcases Finset.mem_insert.mp hyc with he | he
      · exact Or.inr ⟨(hc y hy).1, he⟩
      · exact Or.inl ⟨hSP hy, he⟩
    exact ((mk_le_mk_of_subset hsub).trans (mk_union_le B D)).trans_lt
      (add_lt_of_lt hκ (hs w) (hpair a w c))
  termination_by n - s.card
  decreasing_by
    have := Finset.card_le_univ (insert c s)
    simp [Finset.card_insert_of_notMem hcs] at this ⊢
    omega
  exact step ∅ univ (by simpa) (fun _ ↦ by simpa using aleph0_pos.trans_le hκ)

private abbrev HasSubset {G : Type} [AddCommGroup G] {n : ℕ} (χ : G → Fin n) (α : Cardinal) :=
  ∃ A : Set G, #A = α ∧ (∃ c, ∀ a ∈ A, χ a = c) ∧ ∃ g : G, ∀ a ∈ A, g + g - a ∈ A

-- On a fibre of doubling, reflection about any point in the fibre fixes every point.
private theorem subsetOfFiber {G : Type} [AddCommGroup G] {n : ℕ} (χ : G → Fin n)
    (α : Cardinal) (g : G) (c : Fin n) (S : Set G) (hS : α ≤ #S)
    (h : ∀ x ∈ S, x + x = g + g ∧ χ x = c) : HasSubset χ α := by
  obtain ⟨A, hA, hcard⟩ := le_mk_iff_exists_subset.mp hS
  refine ⟨A, hcard, ⟨c, fun x hx ↦ (h x (hA hx)).2⟩, g, fun x hx ↦ ?_⟩
  rwa [← (h x (hA hx)).1, add_sub_cancel_right]

private theorem infiniteSize {G : Type} [AddCommGroup G] {n : ℕ} (χ : G → Fin n)
    {α : Cardinal} (hα : ℵ₀ ≤ α) (hG : α < #G) : HasSubset χ α := by
  classical
  let D := range (fun x : G ↦ x + x)
  by_cases hD : #D ≤ α
  · let f (x : (univ : Set G)) : D × Fin n := (⟨x + x, x, rfl⟩, χ x)
    have hK : #(D × Fin n) ≤ α := by
      simp only [mk_prod, lift_id]
      exact (mul_le_mul' hD ((lt_aleph0_of_finite (Fin n)).le.trans hα)).trans (mul_eq_self hα).le
    obtain ⟨⟨⟨_, g, rfl⟩, c⟩, S, hS, hcard, hf⟩ :=
      largeFiber hα (P := univ) (by simpa using hG) hK f
    exact subsetOfFiber χ α g c S hcard.le fun x hx ↦
      ⟨congrArg (fun p : D × Fin n ↦ p.1.val) (hf x hx), congrArg Prod.snd (hf x hx)⟩
  -- The differences along a path from 2u to 2v sum to 2(u - v).
  obtain ⟨⟨_, u, rfl⟩, ⟨_, v, rfl⟩, c, hm⟩ :=
    manyPaths hα (lt_of_not_ge hD) (fun x y : D ↦ χ (x.val - y.val))
  obtain ⟨T, hT, hcard⟩ := le_mk_iff_exists_subset.mp hm
  let left (y : D) := (u + u) - y.val
  let right (y : D) := y.val - (v + v)
  refine ⟨left '' T ∪ right '' T, ?_, ⟨c, ?_⟩, u - v, ?_⟩
  · have hleft : #(left '' T) = α :=
      (mk_image_eq (f := left) (fun _ _ h ↦ Subtype.ext (sub_right_inj.mp h))).trans hcard
    apply le_antisymm _ (hleft ▸ mk_le_mk_of_subset subset_union_left)
    calc
      _ ≤ #(left '' T) + #(right '' T) := mk_union_le _ _
      _ ≤ α + α := add_le_add hleft.le (mk_image_le.trans hcard.le)
      _ = α := add_eq_self hα
  · rintro x (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact (hT hy).1
    · exact (hT hy).2
  · rintro x (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Or.inr ⟨y, hy, by dsimp [left, right]; abel⟩
    · exact Or.inl ⟨y, hy, by dsimp [left, right]; abel⟩

-- Three disjoint translates of a finite set form the next coordinate of a ternary cube.
private theorem separateDigits {G X : Type} [AddCommGroup G] [Finite X]
    (hD : (range (fun x : G ↦ x + x)).Infinite) (F : X → G) :
    ∃ d : G, ∀ (i j : Fin 3) (a b : X), i < j → F a + i.val • d ≠ F b + j.val • d := by
  classical
  let B := range (fun p : X × X ↦ F p.1 - F p.2)
  have hB : B.Finite := finite_range _
  obtain ⟨_, ⟨d, rfl⟩, hd⟩ := Set.not_subset.mp
    (fun h ↦ hD ((hB.union (hB.image (fun x ↦ x + x))).subset h))
  have h₁ (a b : X) (he : F a - F b = d) : False :=
    hd (Or.inr ⟨d, ⟨(a, b), he⟩, rfl⟩)
  have h₂ (a b : X) (he : F a - F b = d + d) : False := hd (Or.inl ⟨(a, b), he⟩)
  refine ⟨d, fun i j a b hij he ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> try (revert hij; decide)
  · simp only [zero_nsmul, add_zero] at he
    exact h₁ a b (by rw [he]; abel)
  · simp only [zero_nsmul, add_zero, two_nsmul] at he
    exact h₂ a b (by rw [he]; abel)
  · change F a + (1 : ℕ) • d = F b + (2 : ℕ) • d at he
    rw [one_nsmul, two_nsmul] at he
    apply h₁ a b
    calc
      F a - F b = (F a + d) - (F b + d) := by abel
      _ = d := by rw [he]; abel

private theorem ternaryCube {G : Type} [AddCommGroup G]
    (hD : (range (fun x : G ↦ x + x)).Infinite) (k : ℕ) :
    ∃ F : (Fin k → Fin 3) → G, Function.Injective F ∧
      ∀ x y z, (∀ i, (x i).val + (y i).val = (z i).val + (z i).val) →
        F x + F y = F z + F z := by
  induction k with
  | zero => exact ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _, by simp⟩
  | succ k ih =>
    obtain ⟨F, hinj, hmid⟩ := ih
    obtain ⟨d, hd⟩ := separateDigits hD F
    let tail (x : Fin (k + 1) → Fin 3) := x ∘ Fin.succ
    refine ⟨fun x ↦ F (tail x) + (x 0).val • d, ?_, ?_⟩
    · intro x y he
      change F (tail x) + (x 0).val • d = F (tail y) + (y 0).val • d at he
      have h0 : x 0 = y 0 := (lt_trichotomy (x 0) (y 0)).resolve_left
        (fun h ↦ hd _ _ _ _ h he) |>.resolve_right (fun h ↦ hd _ _ _ _ h he.symm)
      have ht : tail x = tail y := hinj (add_right_cancel (h0 ▸ he))
      exact funext (Fin.cases h0 (fun i ↦ congrFun ht i))
    · intro x y z h
      have ht := hmid (tail x) (tail y) (tail z) (fun i ↦ h i.succ)
      simp only [add_add_add_comm (F _) _ (F _), ← add_nsmul, h 0, ht]

-- The words labelled by a and its reversal have complementary ternary digits.
-- An odd-sized alphabet has one fixed label, which maps to the centre of the cube.
private def digits {m : ℕ} (a j : Fin m) : Fin 3 :=
  if a = a.rev then 1 else if j = a then 2 else if j = a.rev then 0 else 1

private theorem digits_injective {m : ℕ} : Function.Injective (@digits m) := by
  have eq_of_moving {a b : Fin m} (ha : a ≠ a.rev) (h : digits a = digits b) : a = b := by
    by_contra hab
    have he := congrFun h a
    simp only [digits, ite_eq_right ha, ite_eq_right hab] at he
    split_ifs at he <;> contradiction
  intro a b h
  by_cases ha : a = a.rev
  · by_cases hb : b = b.rev
    · have ha' := congrArg Fin.val ha
      have hb' := congrArg Fin.val hb
      simp only [Fin.val_rev] at ha' hb'
      exact Fin.ext (by omega)
    · exact (eq_of_moving hb h.symm).symm
  · exact eq_of_moving ha h

private theorem digits_add_rev {m : ℕ} (a j : Fin m) :
    (digits a j).val + (digits a.rev j).val = 2 := by
  simp only [digits, Fin.rev_rev]
  split_ifs <;> first | rfl | grind

private theorem finiteSize {G : Type} [AddCommGroup G] [Infinite G] {n : ℕ}
    (χ : G → Fin n) (m : ℕ) : HasSubset χ m := by
  classical
  by_cases hd : (range (fun x : G ↦ x + x)).Finite
  · let D := range (fun x : G ↦ x + x)
    have : Finite D := hd
    let f (x : G) : D × Fin n := (⟨x + x, x, rfl⟩, χ x)
    obtain ⟨⟨⟨_, g, rfl⟩, c⟩, hc⟩ := infinite_pigeonhole_card f ℵ₀
      (aleph0_le_mk G) le_rfl (by rw [isRegular_aleph0.cof_ord]; exact lt_aleph0_of_finite _)
    exact subsetOfFiber χ m g c _ (natCast_le_aleph0.trans hc) fun x hx ↦
      ⟨congrArg (fun p : D × Fin n ↦ p.1.val) hx, congrArg Prod.snd hx⟩
  obtain ⟨k, hk⟩ := Combinatorics.Subspace.exists_mono_in_high_dimension_fin (Fin 3) (Fin n) (Fin m)
  obtain ⟨F, hinj, hmid⟩ := ternaryCube hd k
  obtain ⟨l, c, hc⟩ := hk (χ ∘ F)
  let pt (a : Fin m) := F (l (digits a))
  have hp : Function.Injective pt := by
    intro a b he
    apply digits_injective
    funext j
    obtain ⟨i, hi⟩ := l.proper j
    simpa only [l.apply_inr hi] using congrFun (hinj he) i
  refine ⟨range pt, by rw [mk_range_eq pt hp, mk_fin], ⟨c, fun _ ⟨a, ha⟩ ↦ ha ▸ hc (digits a)⟩,
    F (l (fun _ ↦ 1)), ?_⟩
  rintro _ ⟨a, rfl⟩
  refine ⟨a.rev, eq_sub_iff_add_eq.mpr (hmid _ _ _ fun i ↦ ?_)⟩
  cases hi : l.idxFun i with
  | inl b => simp only [l.apply_inl hi]
  | inr j => simpa only [l.apply_inr hi, Fin.rev_rev, Fin.val_one] using digits_add_rev a.rev j

/-- **Monochromatic symmetric subsets in finite colourings (Jayadevan).** Let $G$ be an infinite
abelian group, written additively, let $\alpha$ be a cardinal with $\alpha < |G|$, and let $n$ be
a natural number. For every colouring $\chi \colon G \to \{0, \dots, n - 1\}$ there are a set
$A \subseteq G$ of cardinality $\alpha$ on which $\chi$ is constant and an element $g \in G$ such
that $2g - a \in A$ for every $a \in A$.

This answers Kourovka Problem 15.77 (I. V. Protasov) affirmatively; the Kourovka Notebook (21st
issue) marks it solved, "Yes, it is true" (AI solution confirmed by I. V. Protasov).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.77 (I. V.
Protasov); resolution: A. Jayadevan, Monochromatic symmetric subsets in finite colourings of
infinite abelian groups, preprint, Zenodo record 22909420 (2026), AI-generated solution confirmed by
I. V. Protasov, main theorem (for G infinite abelian and α < |G|, every finite colouring has a
monochromatic S with |S| = α and 2g - S = S for some g); the Kourovka Notebook (21st issue) marks
15.77 solved, https://zenodo.org/records/22909420.
-/
public theorem monochromeSymmetricSubsetExists_holds : monochromeSymmetricSubsetExists := by
  intro G _ _ α hG n χ
  rcases lt_or_ge α ℵ₀ with hα | hα
  · obtain ⟨m, rfl⟩ := lt_aleph0.mp hα
    exact finiteSize χ m
  · exact infiniteSize χ hα hG

end MathlibExt.GroupTheory.MonochromeSymmetricSubsetKourovka15Problem77Wanted
