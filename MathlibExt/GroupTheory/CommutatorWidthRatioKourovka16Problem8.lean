/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

/-!
# Commutator width relative to group order

The ratio of commutator width to order is at most one sixth for finite nonabelian groups,
with equality for the symmetric group on three letters.

Consider a shortest walk from the identity to an element of the derived subgroup, where
each step multiplies by a commutator. If every centralizer has order at least three, each
edge has at least six right translates that start at the identity or have conjugate endpoints.
The sets of translating elements are disjoint along the walk, giving the bound on its length.
If some centralizer has order two, every element of the derived subgroup is a single commutator.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.CommutatorWidthRatioKourovka16Problem8Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.8 (V. G.
Bardakov). UnsolvedMath record UM-00701200 (`KOU-16.8`), dataset ulamai/UnsolvedMath v1.8.0.

Commutators are `a b a⁻¹ b⁻¹` (the same set as for `a⁻¹ b⁻¹ a b`), `w(G')` is the infimum of the
admissible positive `m`, and the target is the problem's claim: `w(G')/|G| ≤ 1/6` for every finite
non-abelian `G`, with equality for `S₃ = Equiv.Perm (Fin 3)`.
-/

/-- **Products of a bounded number of commutators.** For a group $G$, a natural number $m$ and
$g \in G$, $g$ is a product of at most $m$ commutators when there are $k \le m$ and
$a_1, b_1, \dots, a_k, b_k \in G$ with $g = [a_1, b_1] \cdots [a_k, b_k]$, where
$[a, b] = aba^{-1}b^{-1}$; for $k = 0$ the empty product is the identity. -/
def IsProductOfCommutators {G : Type*} [Group G] (m : ℕ) (g : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ m ∧ (l.map fun p => p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod = g

/-- **Commutator width of the derived subgroup.** For a group $G$ with derived subgroup $G'$, the
commutator width $w(G')$ is the least positive integer $m$ such that every element of $G'$ is a
product of at most $m$ commutators $aba^{-1}b^{-1}$ with $a, b \in G$; it is $0$ when no such $m$
exists. -/
noncomputable def commutatorWidth (G : Type*) [Group G] : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ g ∈ commutator G, IsProductOfCommutators m g}

/-- **Bardakov's commutator width ratio claim (Kourovka 16.8).** The proposition that for every
finite non-abelian group $G$ the commutator width $w(G')$ of its derived subgroup $G'$ satisfies
$w(G')/|G| \le 1/6$, and that for the symmetric group $S_3$ equality holds:
$w(S_3')/|S_3| = 1/6$. -/
def maxCommutatorWidthRatioIsOneSixth : Prop :=
  (∀ (G : Type) [Group G] [Finite G], (∃ a b : G, a * b ≠ b * a) →
      (commutatorWidth G : ℚ) / Nat.card G ≤ 1 / 6) ∧
    (commutatorWidth (Equiv.Perm (Fin 3)) : ℚ) / Nat.card (Equiv.Perm (Fin 3)) = 1 / 6

open scoped commutatorElement
open Set

variable {G : Type*} [Group G]

-- An edge multiplies on the left by a commutator. Identity steps are allowed.
private inductive Walk : ℕ → G → G → Prop
  | nil (x) : Walk 0 x x
  | step {n x y} (w : Walk n x y) (a b : G) : Walk (n + 1) x (⁅a, b⁆ * y)

private theorem Walk.join {m n : ℕ} {x y z : G} (u : Walk m x y) (v : Walk n y z) :
    Walk (m + n) x z := by
  induction v with
  | nil => exact u
  | step _ a b ih => exact (ih u).step a b

private theorem Walk.rightMul {n : ℕ} {x y : G} (w : Walk n x y) (t : G) :
    Walk n (x * t) (y * t) := by
  induction w with
  | nil => exact .nil _
  | step _ a b ih => simpa only [mul_assoc] using ih.step a b

private theorem Walk.conjugate {n : ℕ} {x y : G} (w : Walk n x y) (t : G) :
    Walk n (t * x * t⁻¹) (t * y * t⁻¹) := by
  induction w with
  | nil => exact .nil _
  | step _ a b ih =>
    simpa only [← conjugate_commutatorElement, conj_mul] using
      ih.step (t * a * t⁻¹) (t * b * t⁻¹)

private theorem Walk.toProduct {n : ℕ} {x y : G} (w : Walk n x y) :
    IsProductOfCommutators n (y * x⁻¹) := by
  induction w with
  | nil => exact ⟨[], by simp, by simp⟩
  | step _ a b ih =>
    obtain ⟨l, hl, he⟩ := ih
    exact ⟨(a, b) :: l, by simpa using hl, by
      simp only [List.map_cons, List.prod_cons, he, commutatorElement_def]
      simp only [mul_assoc]⟩

private theorem exists_walk {g : G} (hg : g ∈ commutator G) : ∃ n, Walk n 1 g := by
  rw [commutator_eq_closure] at hg
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, .nil _⟩
  | mul_left a ha y _ ih =>
    obtain ⟨u, v, rfl⟩ := ha
    obtain ⟨n, w⟩ := ih
    exact ⟨_, w.step u v⟩
  | inv_mul_cancel a ha y _ ih =>
    obtain ⟨u, v, rfl⟩ := ha
    obtain ⟨n, w⟩ := ih
    exact ⟨_, by simpa only [commutatorElement_inv] using w.step v u⟩

-- Changing both endpoints by conjugacy costs at most one extra edge.
private theorem walk_of_conjugate_ends {n : ℕ} {u v x y : G} (w : Walk n u v)
    (hu : IsConj u x) (hv : IsConj v y) : Walk (n + 1) x y := by
  obtain ⟨t, rfl⟩ := isConj_iff.mp hu
  obtain ⟨s, rfl⟩ := isConj_iff.mp hv
  convert (w.conjugate t).step (s * t⁻¹) (t * v * t⁻¹) using 1
  simp [commutatorElement_def, mul_assoc]

private theorem Walk.path {n : ℕ} {x y : G} (w : Walk n x y) :
    ∃ p : ℕ → G, p 0 = x ∧ p n = y ∧
      ∀ i < n, ∃ a b : G, p (i + 1) = ⁅a, b⁆ * p i := by
  classical
  induction w with
  | nil => exact ⟨fun _ ↦ _, rfl, rfl, by simp⟩
  | @step n x y _ a b ih =>
    obtain ⟨p, h0, hn, hstep⟩ := ih
    refine ⟨Function.update p (n + 1) (⁅a, b⁆ * y), by simpa using h0, by simp, ?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (by omega : i ≤ n) with h | rfl
    · simpa [Function.update_of_ne (by omega : i + 1 ≠ n + 1),
        Function.update_of_ne (by omega : i ≠ n + 1)] using hstep i h
    · exact ⟨a, b, by simp [hn]⟩

private theorem walk_segment {p : ℕ → G} {n i j : ℕ}
    (hs : ∀ k < n, ∃ a b : G, p (k + 1) = ⁅a, b⁆ * p k) (hi : i ≤ j) (hj : j ≤ n) :
    Walk (j - i) (p i) (p j) := by
  induction j, hi using Nat.le_induction with
  | base => simpa using Walk.nil (p i)
  | succ j hij ih =>
    obtain ⟨a, b, he⟩ := hs j (by omega)
    rw [he, show j + 1 - i = j - i + 1 by omega]
    exact (ih (by omega)).step a b

private def markers (u v : G) : Set G := {x | u * x = 1 ∨ IsConj (u * x) (v * x)}

-- Two marked edges would shorten the segment between their outer endpoints.
private theorem disjoint_markers {p : ℕ → G} {n : ℕ}
    (seg : ∀ i j, i ≤ j → j ≤ n → Walk (j - i) (p i) (p j))
    (shortest : ∀ i j m, i ≤ j → j ≤ n → Walk m (p i) (p j) → j - i ≤ m)
    {i j : ℕ} (hij : i < j) (hj : j < n) :
    Disjoint (markers (p i) (p (i + 1))) (markers (p j) (p (j + 1))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  let q (k : ℕ) := p k * x
  have upper (a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) :
      Walk (b - a) (q a) (q b) := (seg a b hab hb).rightMul x
  have lower {a b m : ℕ} (hab : a ≤ b) (hb : b ≤ n) (w : Walk m (q a) (q b)) :
      b - a ≤ m := shortest a b m hab hb (by simpa [q] using w.rightMul x⁻¹)
  change q i = 1 ∨ IsConj (q i) (q (i + 1)) at hx
  change q j = 1 ∨ IsConj (q j) (q (j + 1)) at hy
  rcases hx with hi | hi <;> rcases hy with he | he
  · have w : Walk 0 (q i) (q j) := by rw [hi, he]; exact .nil _
    have := lower hij.le hj.le w
    omega
  · obtain ⟨s, hs⟩ := isConj_iff.mp he
    have w : Walk (j - i) (q i) (q (j + 1)) := by
      simpa [hs, hi] using (upper i j hij.le hj.le).conjugate s
    have := lower (by omega) (by omega) w
    omega
  · obtain ⟨s, hs⟩ := isConj_iff.mp hi.symm
    have w : Walk (j - (i + 1)) (q i) (q j) := by
      simpa [hs, he] using (upper (i + 1) j hij hj.le).conjugate s
    have := lower hij.le hj.le w
    omega
  · have w := walk_of_conjugate_ends (upper (i + 1) j hij hj.le) hi.symm he
    have := lower (by omega) (by omega) w
    omega

private abbrev cent (a : G) := Subgroup.centralizer ({a} : Set G)

private theorem five_le_union [Finite G] {A B : Subgroup G} (ha : 3 ≤ Nat.card A)
    (hb : 3 ≤ Nat.card B) (hab : ¬ A ≤ B) (hba : ¬ B ≤ A) :
    5 ≤ ((A : Set G) ∪ B).ncard := by
  let U := (A : Set G) ∪ B
  have hA : Nat.card A < U.ncard := Set.ncard_lt_ncard (by
    exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_union_left,
      fun h ↦ hba (fun _ hy ↦ h.symm.subset (Or.inr hy))⟩)
  have hB : Nat.card B < U.ncard := Set.ncard_lt_ncard (by
    exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_union_right,
      fun h ↦ hab (fun _ hx ↦ h.symm.subset (Or.inl hx))⟩)
  have hcard := Set.ncard_union_add_ncard_inter (A : Set G) B
  change U.ncard + Nat.card (A ⊓ B : Subgroup G) = Nat.card A + Nat.card B at hcard
  have hmul := A.relIndex_mul_card B
  change 5 ≤ U.ncard
  by_contra! h
  have hI : Nat.card (A ⊓ B : Subgroup G) = 2 := by omega
  rw [hI] at hmul
  omega

-- For c = [a,b], the translates with conjugate endpoints include an injective
-- image of the union of the two centralizers.
private theorem six_le_markers [Finite G] (hc : ∀ a : G, 3 ≤ Nat.card (cent a))
    {a b u : G} (hne : ⁅a, b⁆ ≠ 1) :
    6 ≤ (markers u (⁅a, b⁆ * u)).ncard := by
  let v := ⁅a, b⁆ * u
  let f (z : G) := v⁻¹ * a * z * b⁻¹
  have hf : Function.Injective f := fun z w h ↦ mul_left_cancel (mul_right_cancel h)
  let U := (cent a : Set G) ∪ (cent b : Set G)
  have nc : ¬ Commute a b := mt commutatorElement_eq_one_iff_commute.mpr hne
  have self_mem (x : G) : x ∈ cent x :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x)
  have hU : 5 ≤ U.ncard := five_le_union (hc a) (hc b)
    (fun h ↦ nc (Subgroup.mem_centralizer_singleton_iff.mp (h (self_mem a))))
    (fun h ↦ nc (Subgroup.mem_centralizer_singleton_iff.mp (h (self_mem b))).symm)
  have him (z : G) (hz : z ∈ U) : IsConj (v * f z) (u * f z) := by
    have hv : v * f z = a * z * b⁻¹ := by simp [f, mul_assoc]
    have hu : u * f z = b * a * b⁻¹ * z * b⁻¹ := by
      simp [f, v, commutatorElement_def, mul_assoc]
    rw [hv, hu, isConj_iff]
    rcases hz with hz | hz
    · have h := (Subgroup.mem_centralizer_singleton_iff.mp hz).symm.eq
      refine ⟨b * a * b⁻¹, ?_⟩
      calc
        _ = b * a * b⁻¹ * (a * z) * a⁻¹ * b⁻¹ := by group
        _ = _ := by rw [h]; group
    · have h := (Subgroup.mem_centralizer_singleton_iff.mp hz).inv_right.eq
      refine ⟨b, ?_⟩
      calc
        _ = b * a * (z * b⁻¹) * b⁻¹ := by group
        _ = _ := by rw [h]; group
  have hmiss : u⁻¹ ∉ f '' U := by
    rintro ⟨z, hz, he⟩
    have h := him z hz
    simp [he, v, hne] at h
  have hsub : insert u⁻¹ (f '' U) ⊆ markers u v := by
    rintro x (rfl | ⟨z, hz, rfl⟩)
    · exact Or.inl (mul_inv_cancel _)
    · exact Or.inr (him z hz).symm
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem hmiss, Set.ncard_image_of_injective _ hf] at h
  change 6 ≤ (markers u v).ncard
  omega

private theorem packing_bound [Finite G] (hc : ∀ a : G, 3 ≤ Nat.card (cent a))
    {g : G} (hg : g ∈ commutator G) : IsProductOfCommutators (Nat.card G / 6) g := by
  classical
  let ex := exists_walk hg
  let n := Nat.find ex
  have w : Walk n 1 g := Nat.find_spec ex
  obtain ⟨p, h0, hn, hs⟩ := w.path
  have seg := fun i j (hi : i ≤ j) (hj : j ≤ n) ↦ walk_segment hs hi hj
  have shortest (i j m : ℕ) (hij : i ≤ j) (hj : j ≤ n) (v : Walk m (p i) (p j)) :
      j - i ≤ m := by
    have h := ((seg 0 i (by omega) (by omega)).join v).join (seg j n hj le_rfl)
    rw [h0, hn] at h
    have : n ≤ _ := Nat.find_min' ex h
    omega
  let S (i : Fin n) := markers (p i) (p (i + 1 : ℕ))
  have size (i : Fin n) : 6 ≤ (S i).ncard := by
    obtain ⟨a, b, h⟩ := hs i i.isLt
    have ne : ⁅a, b⁆ ≠ 1 := by
      intro he
      have eq : p (i + 1 : ℕ) = p i := by simpa [he] using h
      have := shortest i (i + 1) 0 (by omega) i.isLt (eq ▸ Walk.nil _)
      omega
    simpa only [S, h] using six_le_markers (u := p i) hc ne
  have disj : Pairwise (fun i j ↦ Disjoint (S i) (S j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact disjoint_markers seg shortest h j.isLt
    · exact (disjoint_markers seg shortest h i.isLt).symm
  have count := (Set.iUnion S).ncard_le_card
  rw [Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) disj, finsum_eq_sum_of_fintype] at count
  have bound : n * 6 ≤ Nat.card G := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ size i)).trans count
  obtain ⟨l, hl, he⟩ := w.toProduct
  exact ⟨l, hl.trans (by omega), by simpa using he⟩

private theorem six_le_order [Finite G] (hn : ∃ a b : G, a * b ≠ b * a) : 6 ≤ Nat.card G := by
  obtain ⟨a, b, hab⟩ := hn
  by_contra! h
  have pos := Nat.card_pos (α := G)
  have prime_case {p : ℕ} [Fact p.Prime] (hp : Nat.card G = p) : False :=
    hab ((isCyclic_of_prime_card hp).isMulCommutative.is_comm.comm a b)
  interval_cases e : Nat.card G
  · have := (Nat.card_eq_one_iff_unique.mp e).1
    exact hab (Subsingleton.elim _ _)
  · exact prime_case rfl
  · exact prime_case rfl
  · exact hab ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) e).is_comm.comm _ _)
  · have : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact prime_case rfl

-- An element with centralizer of order two has a conjugacy class of half the group.
-- Multiplication by any member interchanges this class and its complement.
private theorem single_of_small_centralizer [Finite G] (horder : 6 ≤ Nat.card G)
    {t : G} (hsmall : Nat.card (cent t) < 3) {g : G} (hg : g ∈ commutator G) :
    IsProductOfCommutators 1 g := by
  classical
  have ht : t ≠ 1 := by
    rintro rfl
    have eq : cent (1 : G) = ⊤ := by ext; simp [cent, Subgroup.mem_centralizer_singleton_iff]
    rw [eq, Subgroup.card_top] at hsmall
    omega
  let T := conjugatesOf t
  have tmem : t ∈ T := IsConj.refl _
  have one_out : 1 ∉ T := fun h ↦ ht (isConj_one_left.mp h)
  have pair_sub (s : G) : ({1, s} : Set G) ⊆ cent s := by
    rintro _ (rfl | rfl)
    · exact (cent _).one_mem
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _)
  have two : Nat.card (cent t) = 2 := by
    have h := Set.ncard_le_ncard (pair_sub t)
    rw [Set.ncard_pair ht.symm] at h
    change 2 ≤ Nat.card (cent t) at h
    omega
  have half := (cent t).card_mul_index
  rw [two, Subgroup.index_centralizer_eq_ncard] at half
  change 2 * T.ncard = Nat.card G at half
  have hcent {s : G} (hs : s ∈ T) : (cent s : Set G) = {1, s} := by
    have h := (cent s).card_mul_index
    rw [Subgroup.index_centralizer_eq_ncard, ← (show IsConj t s from hs).conjugatesOf_eq] at h
    change Nat.card (cent s) * T.ncard = Nat.card G at h
    have card : Nat.card (cent s) = 2 := Nat.eq_of_mul_eq_mul_right
      (by omega : 0 < T.ncard) (h.trans half.symm)
    apply Eq.symm
    apply Set.eq_of_subset_of_ncard_le (pair_sub s)
    rw [Set.ncard_pair (show 1 ≠ s from fun e ↦ one_out (e ▸ hs))]
    exact card.le
  have inv {s : G} (hs : s ∈ T) : s⁻¹ = s := by
    have hm : s⁻¹ ∈ cent s := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl s).inv_left
    change s⁻¹ ∈ (cent s : Set G) at hm
    rw [hcent hs] at hm
    rcases hm with h | h
    · exact False.elim (one_out ((inv_eq_one.mp h) ▸ hs))
    · exact h
  have hinv (x : G) : x⁻¹ ∈ T ↔ x ∈ T :=
    ⟨fun h ↦ (by rw [← inv_inv x, inv h]; exact h), fun h ↦ (by rwa [inv h])⟩
  have flip {s : G} (hs : s ∈ T) (x : G) : x * s ∈ T ↔ x ∉ T := by
    have im : (fun y : G ↦ y * s) '' T = Tᶜ := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · rintro _ ⟨y, hy, rfl⟩ hys
        have hc : y ∈ cent s := Subgroup.mem_centralizer_singleton_iff.mpr (by
          have e := inv hys
          rw [mul_inv_rev, inv hy, inv hs] at e
          exact e.symm)
        change y ∈ (cent s : Set G) at hc
        rw [hcent hs] at hc
        rcases hc with h | h
        · exact one_out (h ▸ hy)
        · have e : y * s = 1 := by rw [h, ← mul_inv_cancel s, inv hs]
          exact one_out (e ▸ hys)
      · rw [Set.ncard_image_of_injective _ (mul_left_injective s), Set.ncard_compl]
        omega
    have eq : x ∈ T ↔ x * s ∉ T := by
      change x ∈ T ↔ x * s ∈ Tᶜ
      rw [← im]
      exact ⟨fun h ↦ ⟨x, h, rfl⟩, fun ⟨y, hy, he⟩ ↦ mul_right_cancel he ▸ hy⟩
    tauto
  have mul_class (x y : G) : x * y ∈ T ↔ (x ∈ T ↔ y ∉ T) := by
    by_cases hy : y ∈ T
    · simp [hy, flip hy]
    · have hyt := (flip tmem y).mpr hy
      have h := flip hyt x
      rw [← mul_assoc, flip tmem] at h
      tauto
  let H : Subgroup G :=
    { carrier := Tᶜ
      one_mem' := one_out
      mul_mem' := by
        intro x y hx hy
        change x ∉ T at hx
        change y ∉ T at hy
        change x * y ∉ T
        simp [mul_class, hx, hy]
      inv_mem' := fun {x} hx ↦ mt (hinv x).mp hx }
  have hle : commutator G ≤ H := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    change ⁅a, b⁆ ∉ T
    simp only [commutatorElement_def, mul_class, hinv]
    tauto
  obtain ⟨a, ha⟩ := isConj_iff.mp ((flip tmem g).mpr (hle hg))
  refine ⟨[(a, t)], by simp, ?_⟩
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using
    (mul_inv_eq_iff_eq_mul.mpr ha : a * t * a⁻¹ * t⁻¹ = g)

private theorem width_bounds [Finite G] (hn : ∃ a b : G, a * b ≠ b * a) :
    0 < commutatorWidth G ∧ commutatorWidth G ≤ Nat.card G / 6 := by
  classical
  have order := six_le_order hn
  have adm : Nat.card G / 6 ∈
      {m : ℕ | 0 < m ∧ ∀ g ∈ commutator G, IsProductOfCommutators m g} := by
    refine ⟨by omega, fun g hg ↦ ?_⟩
    by_cases hc : ∀ a : G, 3 ≤ Nat.card (cent a)
    · exact packing_bound hc hg
    · push Not at hc
      obtain ⟨t, ht⟩ := hc
      obtain ⟨l, hl, he⟩ := single_of_small_centralizer order ht hg
      exact ⟨l, by omega, he⟩
  exact ⟨(Nat.sInf_mem ⟨_, adm⟩).1, Nat.sInf_le adm⟩

/-- **The maximal commutator width ratio is one sixth.** For every finite non-abelian group $G$,
the commutator width $w(G')$ of its derived subgroup satisfies $w(G')/|G| \le 1/6$, and for the
symmetric group $S_3$ equality holds, $w(S_3')/|S_3| = 1/6$; so Kourovka Problem 16.8 has a
positive answer.

The Kourovka Archive answers 16.8 "Yes, it is", citing Bonner (2008) for the bound; $S_3$ attains
it because its derived subgroup $A_3$ consists of commutators.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 16.8 (V. G. Bardakov); resolution: T. Bonner, J. Algebra 320 (2008), 3165-3171,
Kourovka Archive, Problem 16.8 (Yes, it is).
-/
public theorem maxCommutatorWidthRatioIsOneSixth_holds : maxCommutatorWidthRatioIsOneSixth := by
  constructor
  · intro G _ _ hn
    have bound := (width_bounds hn).2
    have h : commutatorWidth G * 6 ≤ Nat.card G := by omega
    have hq : (commutatorWidth G : ℚ) * 6 ≤ Nat.card G := by exact_mod_cast h
    have hpos : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos
    exact (div_le_div_iff₀ hpos (by norm_num)).mpr (by simpa using hq)
  · let S := Equiv.Perm (Fin 3)
    have hn : ∃ a b : S, a * b ≠ b * a :=
      ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
    have hc : Nat.card S = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
    obtain ⟨pos, bound⟩ := width_bounds hn
    rw [hc] at bound
    have hw : commutatorWidth S = 1 := by omega
    change (commutatorWidth S : ℚ) / Nat.card S = 1 / 6
    rw [hw, hc]
    norm_num

end MathlibExt.GroupTheory.CommutatorWidthRatioKourovka16Problem8Wanted
