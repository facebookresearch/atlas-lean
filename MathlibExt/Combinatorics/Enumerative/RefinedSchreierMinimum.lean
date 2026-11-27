/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SchreierSparseCount

/-!
# Refined Schreier sets with a prescribed minimum

To raise the minimum threshold by `t`, translate the whole set by `t`. On the partition
side, raise a largest part by `t`, increasing the gap between the two largest parts by `t`.
Both operations increase the ambient parameter by `t`. The fixed-cardinality correspondence
therefore identifies the two threshold counts; subtracting successive counts gives the exact
minimum and exact gap identity.

## References

* Kevin Beanland and Hùng Việt Chu, *On Schreier-Type Sets, Partitions, and Compositions*,
  Journal of Integer Sequences 27 (2024), Article 24.4.4, pp. 1–13, Lemma 11 and Corollary 12.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

/-- **Partitions with a given gap between the two largest parts.** For natural numbers $n$,
$\ell$, $k$ and $q$, $|E_{n,\ell,k,q}|$ is the number of partitions of $n$ into exactly $k$ parts,
all at least $\ell$, whose largest part exceeds the second largest part (counted with
multiplicity) by exactly $q$; such a partition has at least two parts, so the count is $0$ for
$k < 2$. -/
noncomputable def partitionMinPartGapCount (n l k q : ℕ) : ℕ := by
  classical
  exact ((Nat.Partition.restricted n (fun x => l ≤ x)).filter
    (fun P => P.parts.card = k ∧
      ∃ b : ℕ, ∃ rest : Multiset ℕ,
        P.parts = (b + q) ::ₘ b ::ₘ rest ∧
          ∀ x ∈ rest, x ≤ b)).card

/-- **Refined Schreier sets with a given size and minimum.** For natural numbers $n$ and
$\ell$, let $F_{n,\ell}$ be the family of finite sets $A$ of natural numbers such that $A$ has
largest element $n + 1$ and at least three elements, $A$ is sparse (the differences of
consecutive elements, in increasing order, are non-decreasing) and $\ell$-strong Schreier
($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and third largest elements
$b > a$ of $A$ satisfy $n + 1 + a = 2b$. For natural numbers $k$ and $q$, $|F_{n,\ell,k,q}|$
is the number of sets in $F_{n,\ell}$ with exactly $k$ elements whose smallest element is
$q$. -/
def refinedSchreierCardMinCount (n l k q : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (fun A => IsRefinedSchreier n l A ∧ A.card = k ∧
      q ∈ A ∧ ∀ x ∈ A, q ≤ x)).card

private abbrev refinedAtLeast (n l k t : ℕ) :=
  (Finset.Icc 0 (n + 1)).powerset.filter
    (fun A => IsRefinedSchreier n l A ∧ A.card = k + 1 ∧ ∀ a ∈ A, l * k + 1 + t ≤ a)

-- Keep the strong Schreier lower bound in the explicit threshold only.
private theorem mem_refinedAtLeast {n l k t : ℕ} {A : Finset ℕ} (hk : 2 ≤ k) :
    A ∈ refinedAtLeast n l k t ↔
      A.card = k + 1 ∧ (∀ a ∈ A, l * k + 1 + t ≤ a) ∧
      n + 1 ∈ A ∧ (∀ a ∈ A, a ≤ n + 1) ∧ IsSparse A ∧
      ∃ a ∈ A, ∃ b ∈ A, a < b ∧ b < n + 1 ∧
        (∀ x ∈ A, x ≤ b ∨ x = n + 1) ∧
        (∀ x ∈ A, x ≤ a ∨ x = b ∨ x = n + 1) ∧ n + 1 + a = 2 * b := by
  unfold refinedAtLeast
  rw [Finset.mem_filter]
  unfold IsRefinedSchreier
  constructor
  · rintro ⟨-, ⟨hn, hb, -, hs, -, he⟩, hc, ht⟩
    exact ⟨hc, ht, hn, hb, hs, he⟩
  · rintro ⟨hc, ht, hn, hb, hs, he⟩
    refine ⟨Finset.mem_powerset.mpr (fun a ha => Finset.mem_Icc.mpr ⟨Nat.zero_le _, hb a ha⟩),
      ⟨hn, hb, by omega, hs, ?_, he⟩, hc, ht⟩
    intro a ha
    rw [hc, Nat.mul_succ]
    have := ht a ha
    omega

private def shift (t : ℕ) : ℕ ↪ ℕ := ⟨(· + t), fun _ _ h => Nat.add_right_cancel h⟩

private theorem shift_apply (t a : ℕ) : shift t a = a + t := rfl

private theorem mem_refinedAtLeast_shift {n l k t : ℕ} {A : Finset ℕ} (hk : 2 ≤ k) :
    A.map (shift t) ∈ refinedAtLeast (n + t) l k t ↔ A ∈ refinedAtLeast n l k 0 := by
  rw [mem_refinedAtLeast hk, mem_refinedAtLeast hk]
  have hex (p : ℕ → Prop) : (∃ x ∈ A.map (shift t), p x) ↔ ∃ x ∈ A, p (x + t) := by
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
      exact ⟨a, ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a + t, ⟨a, ha, rfl⟩, h⟩
  have hmax : n + 1 + t ∈ A.map (shift t) ↔ n + 1 ∈ A :=
    Finset.mem_map' (shift t)
  have hAP (a b : ℕ) : n + 1 + t + (a + t) = 2 * (b + t) ↔ n + 1 + a = 2 * b := by
    omega
  simp only [Finset.card_map, hmax, IsSparse, Finset.forall_mem_map, hex,
    show n + t + 1 = n + 1 + t by omega, shift_apply,
    Nat.add_le_add_iff_right, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff,
    Nat.add_sub_add_right, Nat.add_zero, hAP]

private theorem refinedAtLeast_shift (n l k t : ℕ) (hk : 2 ≤ k) :
    (refinedAtLeast n l k 0).card = (refinedAtLeast (n + t) l k t).card := by
  refine Finset.card_nbij (Finset.map (shift t)) (fun _ h => (mem_refinedAtLeast_shift hk).2 h)
    (fun _ _ _ _ h => Finset.map_injective (shift t) h) ?_
  intro A hA
  have hge (a : ℕ) (ha : a ∈ A) : t ≤ a := by
    have := ((mem_refinedAtLeast hk).mp hA).2.1 a ha
    omega
  have hmap : (A.image (· - t)).map (shift t) = A := by
    ext a
    simp only [Finset.mem_map, Finset.mem_image, shift_apply]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      rwa [Nat.sub_add_cancel (hge b hb)]
    · intro ha
      exact ⟨a - t, ⟨a, ha, rfl⟩, Nat.sub_add_cancel (hge a ha)⟩
  exact ⟨A.image (· - t), (mem_refinedAtLeast_shift hk).1 (hmap ▸ hA), hmap⟩

private def IsTopPair (s : Multiset ℕ) (a b : ℕ) (r : Multiset ℕ) : Prop :=
  s = a ::ₘ b ::ₘ r ∧ b ≤ a ∧ ∀ x ∈ r, x ≤ b

private theorem IsTopPair.le_top {s r : Multiset ℕ} {a b x : ℕ}
    (h : IsTopPair s a b r) (hx : x ∈ s) : x ≤ a := by
  rw [h.1, Multiset.mem_cons, Multiset.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · exact le_rfl
  · exact h.2.1
  · exact (h.2.2 _ hx).trans h.2.1

private theorem IsTopPair.unique {s r r' : Multiset ℕ} {a b a' b' : ℕ}
    (h : IsTopPair s a b r) (h' : IsTopPair s a' b' r') : a = a' ∧ b = b' ∧ r = r' := by
  have ha : a = a' := le_antisymm (h'.le_top (by simp [h.1])) (h.le_top (by simp [h'.1]))
  subst a'
  have he : b ::ₘ r = b' ::ₘ r' := by simpa using h.1.symm.trans h'.1
  have hb : b = b' := by
    have hb₁ : b ∈ b' ::ₘ r' := he ▸ Multiset.mem_cons_self b r
    have hb₂ : b' ∈ b ::ₘ r := he.symm ▸ Multiset.mem_cons_self b' r'
    rw [Multiset.mem_cons] at hb₁ hb₂
    exact le_antisymm (hb₁.elim (·.le) (h'.2.2 b)) (hb₂.elim (·.le) (h.2.2 b'))
  subst b'
  exact ⟨rfl, rfl, by simpa using he⟩

private theorem exists_topPair {s : Multiset ℕ} (h : 2 ≤ s.card) :
    ∃ a b r, IsTopPair s a b r := by
  have hs := s.pairwise_sort (· ≥ ·)
  have he := s.sort_eq (· ≥ ·)
  have hc := s.length_sort (· ≥ ·)
  rcases hl : s.sort (· ≥ ·) with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> rw [hl] at hc
  · simp at hc
    omega
  · simp at hc
    omega
  · rw [hl] at hs he
    refine ⟨a, b, r, he.symm, ?_, ?_⟩
    · exact (List.pairwise_cons.mp hs).1 b (by simp)
    · simpa using (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1

private abbrev fixedParts (n l k : ℕ) :=
  (Nat.Partition.restricted n (fun x => l + 1 ≤ x)).filter (fun P => P.parts.card = k)

private def GapAtLeast (t : ℕ) (s : Multiset ℕ) : Prop :=
  ∃ a b r, IsTopPair s a b r ∧ b + t ≤ a

private noncomputable def partsAtLeast (n l k t : ℕ) : Finset (Nat.Partition n) := by
  classical
  exact (fixedParts n l k).filter (fun P => GapAtLeast t P.parts)

private theorem mem_fixedParts {n l k : ℕ} {P : Nat.Partition n} :
    P ∈ fixedParts n l k ↔ (∀ x ∈ P.parts, l + 1 ≤ x) ∧ P.parts.card = k := by
  simp [fixedParts, Nat.Partition.restricted]

-- Replacing a largest part by a number at least as large as the second part preserves
-- the order of the displayed top pair, the lower bound on parts, and the part count.
private theorem replace_top {n m l k a b c : ℕ} {P : Nat.Partition n} {r : Multiset ℕ}
    (hP : P ∈ fixedParts n l k) (hp : IsTopPair P.parts a b r) (hbc : b ≤ c)
    (hsum : c + b + r.sum = m) :
    ∃ Q ∈ fixedParts m l k, IsTopPair Q.parts c b r := by
  obtain ⟨hge, hcard⟩ := mem_fixedParts.mp hP
  have hbound (x : ℕ) (hx : x ∈ c ::ₘ b ::ₘ r) : l + 1 ≤ x := by
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact (hge b (by simp [hp.1])).trans hbc
    · exact hge x (by rw [hp.1]; exact Multiset.mem_cons_of_mem hx)
  let Q : Nat.Partition m := ⟨c ::ₘ b ::ₘ r, fun hx => Nat.zero_lt_of_lt (hbound _ hx),
    by simpa [Multiset.sum_cons, Nat.add_assoc] using hsum⟩
  have hc : Q.parts.card = k := by
    simpa [Q, hp.1] using hcard
  exact ⟨Q, mem_fixedParts.mpr ⟨hbound, hc⟩, rfl, hbc, hp.2.2⟩

-- The witnesses on the two sides share their second part and all smaller parts.
private def Raised {n : ℕ} (t : ℕ) (P : Nat.Partition n) (Q : Nat.Partition (n + t)) : Prop :=
  ∃ a b r, IsTopPair P.parts a b r ∧ IsTopPair Q.parts (a + t) b r

private theorem partsAtLeast_shift (n l k t : ℕ) (hk : 2 ≤ k) :
    (fixedParts n l k).card = (partsAtLeast (n + t) l k t).card := by
  classical
  have forward (P : Nat.Partition n) (hP : P ∈ fixedParts n l k) :
      ∃ Q ∈ partsAtLeast (n + t) l k t, Raised t P Q := by
    have hcard := (mem_fixedParts.mp hP).2
    obtain ⟨a, b, r, hp⟩ := exists_topPair (hcard.symm ▸ hk)
    have hsum := P.parts_sum
    simp only [hp.1, Multiset.sum_cons] at hsum
    have hba := hp.2.1
    obtain ⟨Q, hQ, hq⟩ := replace_top (m := n + t) hP hp (c := a + t) (by omega) (by omega)
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, a + t, b, r, hq, by omega⟩, a, b, r, hp, hq⟩
  have backward (Q : Nat.Partition (n + t)) (hQ : Q ∈ partsAtLeast (n + t) l k t) :
      ∃ P ∈ fixedParts n l k, Raised t P Q := by
    obtain ⟨hfixed, a, b, r, hq, hgap⟩ := Finset.mem_filter.mp hQ
    have hsum := Q.parts_sum
    simp only [hq.1, Multiset.sum_cons] at hsum
    obtain ⟨P, hP, hp⟩ := replace_top (m := n) hfixed hq (c := a - t) (by omega) (by omega)
    exact ⟨P, hP, a - t, b, r, hp, by rwa [Nat.sub_add_cancel (by omega : t ≤ a)]⟩
  have left_unique {P P' : Nat.Partition n} {Q : Nat.Partition (n + t)}
      (h : Raised t P Q) (h' : Raised t P' Q) : P = P' := by
    obtain ⟨a, b, r, hp, hq⟩ := h
    obtain ⟨a', b', r', hp', hq'⟩ := h'
    obtain ⟨ha, rfl, rfl⟩ := hq.unique hq'
    have := Nat.add_right_cancel ha
    exact Nat.Partition.ext (hp.1.trans (this ▸ hp'.1.symm))
  have right_unique {P : Nat.Partition n} {Q Q' : Nat.Partition (n + t)}
      (h : Raised t P Q) (h' : Raised t P Q') : Q = Q' := by
    obtain ⟨a, b, r, hp, hq⟩ := h
    obtain ⟨a', b', r', hp', hq'⟩ := h'
    obtain ⟨rfl, rfl, rfl⟩ := hp.unique hp'
    exact Nat.Partition.ext (hq.1.trans hq'.1.symm)
  refine Finset.card_bij (fun P hP => (forward P hP).choose)
    (fun P hP => (forward P hP).choose_spec.1) ?_ ?_
  · intro P hP P' hP' he
    exact left_unique (forward P hP).choose_spec.2 (he.symm ▸ (forward P' hP').choose_spec.2)
  · intro Q hQ
    obtain ⟨P, hP, h⟩ := backward Q hQ
    exact ⟨P, hP, right_unique (forward P hP).choose_spec.2 h⟩

private theorem fixed_counts (n l k : ℕ) (hk : 2 ≤ k) :
    (refinedAtLeast n l k 0).card = (fixedParts n l k).card := by
  have hr : refinedSchreierCardCount n l (k + 1) = (refinedAtLeast n l k 0).card := by
    unfold refinedSchreierCardCount
    congr 1
    ext A
    simp only [refinedAtLeast, Finset.mem_filter, and_congr_right_iff]
    intro _ hA
    constructor
    · intro hc
      refine ⟨hc, fun a ha => ?_⟩
      have h := hA.2.2.2.2.1 a ha
      rw [hc, Nat.mul_succ] at h
      omega
    · exact And.left
  rw [← hr]
  change refinedSchreierCardCount n l (k + 1) = partitionMinPartExactCount n (l + 1) k
  by_cases hn : l + 1 ≤ n
  · exact (partitionMinPartExactCount_eq_refined n l k hn hk).symm
  · have hmul : l ≤ l * k := Nat.le_mul_of_pos_right l (by omega)
    have hA : refinedSchreierCardCount n l (k + 1) = 0 := by
      unfold refinedSchreierCardCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      obtain ⟨-, ⟨-, -, -, -, hstrong, a, ha, b, -, hab, hbn, _⟩, hcard⟩ :=
        Finset.mem_filter.mp hA
      have h := hstrong a ha
      rw [hcard, Nat.mul_succ] at h
      omega
    have hP : partitionMinPartExactCount n (l + 1) k = 0 := by
      change (fixedParts n l k).card = 0
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro P hP
      obtain ⟨hge, hcard⟩ := mem_fixedParts.mp hP
      obtain ⟨a, b, r, h⟩ := exists_topPair (hcard.symm ▸ hk)
      have ha : a ∈ P.parts := by simp [h.1]
      exact hn ((hge a ha).trans (Nat.Partition.le_of_mem_parts ha))
    rw [hA, hP]

private theorem threshold_counts (n l k t : ℕ) (hk : 2 ≤ k) :
    (refinedAtLeast n l k t).card = (partsAtLeast n l k t).card := by
  by_cases ht : t ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' ht
    rw [← refinedAtLeast_shift m l k t hk, ← partsAtLeast_shift m l k t hk]
    exact fixed_counts m l k hk
  · suffices refinedAtLeast n l k t = ∅ ∧ partsAtLeast n l k t = ∅ by
      simp [this.1, this.2]
    refine ⟨Finset.eq_empty_iff_forall_notMem.mpr ?_, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    · intro A hA
      obtain ⟨-, hlo, hmax, _⟩ := (mem_refinedAtLeast hk).mp hA
      have := hlo (n + 1) hmax
      omega
    · classical
      intro P hP
      obtain ⟨-, a, b, r, htop, hgap⟩ := Finset.mem_filter.mp hP
      have ha : a ∈ P.parts := by simp [htop.1]
      have := Nat.Partition.le_of_mem_parts ha
      omega

private theorem refined_exact (n l k t : ℕ) :
    (refinedAtLeast n l k (t + 1)).card + refinedSchreierCardMinCount n l (k + 1)
      (l * k + 1 + t) = (refinedAtLeast n l k t).card := by
  classical
  let p (A : Finset ℕ) := ∀ a ∈ A, l * k + 1 + (t + 1) ≤ a
  have hge : (refinedAtLeast n l k t).filter p = refinedAtLeast n l k (t + 1) := by
    ext A
    simp only [refinedAtLeast, p, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2⟩,
      fun h => ⟨⟨h.1, h.2.1, h.2.2.1, fun a ha => by have := h.2.2.2 a ha; omega⟩, h.2.2.2⟩⟩
  have he : ((refinedAtLeast n l k t).filter (fun A => ¬ p A)).card =
      refinedSchreierCardMinCount n l (k + 1) (l * k + 1 + t) := by
    unfold refinedSchreierCardMinCount
    congr 1
    ext A
    simp only [refinedAtLeast, p, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hsub, hA, hc, hlo⟩, hnot⟩
      push Not at hnot
      obtain ⟨a, ha, hlt⟩ := hnot
      have := hlo a ha
      have heq : a = l * k + 1 + t := by omega
      exact ⟨hsub, hA, hc, heq ▸ ha, hlo⟩
    · rintro ⟨hsub, hA, hc, hm, hlo⟩
      exact ⟨⟨hsub, hA, hc, hlo⟩, fun h => by have := h _ hm; omega⟩
  simpa only [hge, he] using
    (Finset.card_filter_add_card_filter_not (s := refinedAtLeast n l k t) p)

private theorem partitions_exact (n l k t : ℕ) :
    (partsAtLeast n l k (t + 1)).card + partitionMinPartGapCount n (l + 1) k t =
      (partsAtLeast n l k t).card := by
  classical
  let p (P : Nat.Partition n) := GapAtLeast (t + 1) P.parts
  have hge : (partsAtLeast n l k t).filter p = partsAtLeast n l k (t + 1) := by
    ext P
    simp only [partsAtLeast, p, Finset.mem_filter]
    refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
    obtain ⟨a, b, r, hp, ht⟩ := h.2
    exact ⟨a, b, r, hp, by omega⟩
  have he : ((partsAtLeast n l k t).filter (fun P => ¬ p P)).card =
      partitionMinPartGapCount n (l + 1) k t := by
    unfold partitionMinPartGapCount
    congr 1
    ext P
    simp only [partsAtLeast, fixedParts, p, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨hsub, hc⟩, a, b, r, hp, hle⟩, hnot⟩
      have hlt : ¬ b + (t + 1) ≤ a := fun h => hnot ⟨a, b, r, hp, h⟩
      have ha : a = b + t := by omega
      exact ⟨hsub, hc, b, r, ha ▸ hp.1, hp.2.2⟩
    · rintro ⟨hsub, hc, b, r, heq, hr⟩
      have hp : IsTopPair P.parts (b + t) b r := ⟨heq, by omega, hr⟩
      refine ⟨⟨⟨hsub, hc⟩, b + t, b, r, hp, le_rfl⟩, ?_⟩
      rintro ⟨a', b', r', hp', hle⟩
      obtain ⟨ha, hb, -⟩ := hp.unique hp'
      omega
  simpa only [hge, he] using
    (Finset.card_filter_add_card_filter_not (s := partsAtLeast n l k t) p)

-- The parameter range in the source includes `l + 1 ≤ n`; the count identity also holds below it.
set_option linter.unusedVariables false in
/-- **Refined Schreier sets with a given minimum and partitions with a given top gap.** Let
$n$, $\ell$, $k$ and $q$ be natural numbers with $n \ge \ell + 1$, $k \ge 2$ and $q \ge 1$.
Let $F_{n,\ell}$ be the family of finite sets $A$ of natural numbers such that $A$ has largest
element $n + 1$ and at least three elements, $A$ is sparse (the differences of consecutive
elements, in increasing order, are non-decreasing) and $\ell$-strong Schreier
($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and third largest elements
$b > a$ of $A$ satisfy $n + 1 + a = 2b$. Then the number $|F_{n,\ell,k+1,\ell k+q}|$ of sets
in $F_{n,\ell}$ with exactly $k + 1$ elements and smallest element $\ell k + q$ equals the
number $|E_{n,\ell+1,k,q-1}|$ of partitions of $n$ into exactly $k$ parts, all at least
$\ell + 1$, whose largest part exceeds the second largest part (counted with multiplicity) by
exactly $q - 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Lemma 11. -/
theorem refinedSchreierCardMinCount_eq (n l k q : ℕ)
    (hn : l + 1 ≤ n) (hk : 2 ≤ k) (hq : 1 ≤ q) :
    refinedSchreierCardMinCount n l (k + 1) (l * k + q) =
      partitionMinPartGapCount n (l + 1) k (q - 1) := by
  have h := refined_exact n l k (q - 1)
  rw [threshold_counts n l k _ hk, threshold_counts n l k _ hk] at h
  have hq' : l * k + 1 + (q - 1) = l * k + q := by omega
  rw [hq'] at h
  exact Nat.add_left_cancel (h.trans (partitions_exact n l k (q - 1)).symm)

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted
