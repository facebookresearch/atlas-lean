/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

/-!
# Weighted fence tilings

The half-cells of an $n$-board split into two paths: fences only join half-cells of the same
parity. Each path has the same alternating half-square weights. The weighted count of fence
tilings is therefore the square of the weighted count of path matchings, whose two-term recurrence
gives the even-board recurrence of Belaggoun and Belbachir.
-/

namespace MetaMathlibExt

open Finset

@[expose] public section

/-- **Fence tilings of a board.** Number the half-cells of an $n$-board $0, \dots, 2n - 1$. The
tilings of the $n$-board by half-squares and $(1/2, 1/2)$-fences are encoded as the sets $F$ of
fence positions $k < 2n - 2$ (the fence at $k$ has posts on half-cells $k$ and $k + 2$) whose
posts are pairwise disjoint, that is, $k + 2 \notin F$ for every $k \in F$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2. -/
def fenceTilings (n : ℕ) : Finset (Finset ℕ) :=
  (range (2 * n - 2)).powerset.filter fun F => ∀ k ∈ F, k + 2 ∉ F

/-- **Weight of a fence tiling.** Let $a$, $b$ be elements of a commutative semiring, let $n \ge 0$,
and let $F$ be a finite set of natural numbers (fence positions; the fence at $k$ has posts on
half-cells $k$ and $k + 2$). The weight of $F$ on the $n$-board is the product, over the
half-cells $h \in \{0, \dots, 2n - 1\}$ that neither lie in $F$ nor equal $k + 2$ for some
$k \in F$, of $a$ if $\lfloor h/2 \rfloor$ is even (a half-square in the odd cell
$\lfloor h/2 \rfloor + 1$) and of $b$ otherwise (a half-square in an even cell).

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2. -/
def fenceTilingWeight {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) (F : Finset ℕ) : R :=
  ∏ h ∈ range (2 * n) \ (F ∪ F.image (· + 2)), if h / 2 % 2 = 0 then a else b

/-- **Weighted count of fence tilings.** Let $a$, $b$ be elements of a commutative semiring and
$n \ge 0$. The weighted number $S_n$ of tilings of an $n$-board by half-squares and
$(1/2, 1/2)$-fences is the sum, over all fence tilings $F$ of the $n$-board, of the weight of $F$,
in which a half-square weighs $a$ in an odd cell and $b$ in an even cell and fences weigh $1$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2 (before Lemma 2.1). -/
def fenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ fenceTilings n, fenceTilingWeight a b n F


/-- **Weighted count of bifence-free fence tilings.** Let $a$, $b$ be elements of a commutative
semiring and $n \ge 0$. Two fences at positions $k$ and $k + 1$ form a bifence. The weighted number
$C_n$ of tilings with no bifence is the sum of the weights, with half-square weights $a$ and $b$,
of the fence tilings $F$ of the $n$-board with no bifence, that is, with $k + 1 \notin F$ for every
$k \in F$.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15. -/
def noBifenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ (fenceTilings n).filter (fun F => ∀ k ∈ F, k + 1 ∉ F), fenceTilingWeight a b n F

end

private def uncovered (n d : ℕ) (F : Finset ℕ) : Finset ℕ :=
  range n \ (F ∪ F.image (· + d))

private theorem mem_uncovered {n d k : ℕ} {F : Finset ℕ} :
    k ∈ uncovered n d F ↔ k < n ∧ k ∉ F ∧ (d ≤ k → k - d ∉ F) := by
  simp only [uncovered, mem_sdiff, mem_range, mem_union, not_or, mem_image]
  constructor <;> rintro ⟨hk, hf, hd⟩ <;> refine ⟨hk, hf, ?_⟩
  · intro h hmem
    exact hd ⟨k - d, hmem, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    exact hd (by omega) (by simpa using hj)

-- A path matching is specified by the left endpoints of its dimers.
private def pathTilings (n : ℕ) : Finset (Finset ℕ) :=
  (range (n - 1)).powerset.filter fun F => ∀ k ∈ F, k + 1 ∉ F

private theorem mem_pathTilings {n : ℕ} {F : Finset ℕ} :
    F ∈ pathTilings n ↔ (∀ k ∈ F, k + 1 < n) ∧ (∀ k ∈ F, k + 1 ∉ F) := by
  rw [pathTilings, mem_filter, mem_powerset]
  refine and_congr_left' ?_
  simp only [Finset.subset_iff, mem_range]
  exact forall_congr' fun _ => imp_congr_right fun _ => by omega

private theorem mem_fenceTilings {n : ℕ} {F : Finset ℕ} :
    F ∈ fenceTilings n ↔ (∀ k ∈ F, k + 2 < 2 * n) ∧ (∀ k ∈ F, k + 2 ∉ F) := by
  rw [fenceTilings, mem_filter, mem_powerset]
  refine and_congr_left' ?_
  simp only [Finset.subset_iff, mem_range]
  exact forall_congr' fun _ => imp_congr_right fun _ => by omega

private def halfCell (p : ℕ) : ℕ ↪ ℕ :=
  ⟨fun i => 2 * i + p, by
    intro i j h
    change 2 * i + p = 2 * j + p at h
    omega⟩

private theorem halfCell_apply (p i : ℕ) : halfCell p i = 2 * i + p := rfl

private def side (p : ℕ) (F : Finset ℕ) : Finset ℕ :=
  (F.filter fun k => k % 2 = p).image (· / 2)

private theorem mem_side {F : Finset ℕ} {p i : ℕ} (hp : p < 2) :
    i ∈ side p F ↔ 2 * i + p ∈ F := by
  simp only [side, mem_image, mem_filter]
  constructor
  · rintro ⟨k, ⟨hk, hpar⟩, hdiv⟩
    rwa [show 2 * i + p = k by omega]
  · intro hi
    exact ⟨2 * i + p, ⟨hi, by omega⟩, by omega⟩

private def mergeSides (E O : Finset ℕ) : Finset ℕ :=
  E.map (halfCell 0) ∪ O.map (halfCell 1)

private theorem mem_mergeSides {E O : Finset ℕ} {p i : ℕ} (hp : p < 2) :
    2 * i + p ∈ mergeSides E O ↔ i ∈ (if p = 0 then E else O) := by
  simp only [mergeSides, mem_union, mem_map, halfCell_apply]
  constructor
  · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
    · obtain rfl : j = i := by omega
      rwa [ite_eq_left (show p = 0 by omega)]
    · obtain rfl : j = i := by omega
      rwa [ite_eq_right (show p ≠ 0 by omega)]
  · split_ifs with h
    · exact fun hi => Or.inl ⟨i, hi, by omega⟩
    · exact fun hi => Or.inr ⟨i, hi, by omega⟩

private theorem mergeSides_side (F : Finset ℕ) : mergeSides (side 0 F) (side 1 F) = F := by
  ext k
  obtain ⟨i, p, hp, rfl⟩ : ∃ i p : ℕ, p < 2 ∧ k = 2 * i + p :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  by_cases h : p = 0
  · subst p
    rw [mem_mergeSides (by decide), ite_eq_left rfl, mem_side (by decide)]
  · obtain rfl : p = 1 := by omega
    rw [mem_mergeSides (by decide), ite_eq_right (by decide), mem_side (by decide)]

private theorem mergeSides_mem {n : ℕ} {E O : Finset ℕ} :
    mergeSides E O ∈ fenceTilings n ↔ E ∈ pathTilings n ∧ O ∈ pathTilings n := by
  rw [mem_fenceTilings, mem_pathTilings, mem_pathTilings]
  have mem (p i : ℕ) (hp : p < 2) :
      2 * i + p ∈ mergeSides E O ↔ i ∈ (if p = 0 then E else O) := mem_mergeSides hp
  have step (p i : ℕ) (hp : p < 2) :
      2 * i + p + 2 ∈ mergeSides E O ↔ i + 1 ∈ (if p = 0 then E else O) := by
    rw [show 2 * i + p + 2 = 2 * (i + 1) + p by omega, mem p (i + 1) hp]
  constructor
  · rintro ⟨hbound, hsep⟩
    have path (p : ℕ) (hp : p < 2) :
        (∀ i ∈ (if p = 0 then E else O), i + 1 < n) ∧
          (∀ i ∈ (if p = 0 then E else O), i + 1 ∉ (if p = 0 then E else O)) := by
      refine ⟨fun i hi => ?_, fun i hi hj => ?_⟩
      · have := hbound _ ((mem p i hp).mpr hi)
        omega
      · exact hsep _ ((mem p i hp).mpr hi) ((step p i hp).mpr hj)
    exact ⟨by simpa using path 0 (by decide), by simpa using path 1 (by decide)⟩
  · rintro ⟨hE, hO⟩
    have path (p : ℕ) (hp : p < 2) :
        (∀ i ∈ (if p = 0 then E else O), i + 1 < n) ∧
          (∀ i ∈ (if p = 0 then E else O), i + 1 ∉ (if p = 0 then E else O)) := by
      split_ifs <;> assumption
    refine ⟨fun k hk => ?_, fun k hk hk' => ?_⟩
    · obtain ⟨i, p, hp, rfl⟩ : ∃ i p : ℕ, p < 2 ∧ k = 2 * i + p :=
        ⟨k / 2, k % 2, by omega, by omega⟩
      have := (path p hp).1 i ((mem p i hp).mp hk)
      omega
    · obtain ⟨i, p, hp, rfl⟩ : ∃ i p : ℕ, p < 2 ∧ k = 2 * i + p :=
        ⟨k / 2, k % 2, by omega, by omega⟩
      exact (path p hp).2 i ((mem p i hp).mp hk) ((step p i hp).mp hk')

private def cellWeight {R : Type*} (a b : R) (i : ℕ) : R :=
  if i % 2 = 0 then a else b

private def pathWeight {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) (F : Finset ℕ) : R :=
  ∏ i ∈ uncovered n 1 F, cellWeight a b i

private def pathSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ pathTilings n, pathWeight a b n F

private theorem uncovered_mergeSides (n : ℕ) (E O : Finset ℕ) :
    uncovered (2 * n) 2 (mergeSides E O) = mergeSides (uncovered n 1 E) (uncovered n 1 O) := by
  ext k
  obtain ⟨i, p, hp, rfl⟩ : ∃ i p : ℕ, p < 2 ∧ k = 2 * i + p :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  have hChoice : (if p = 0 then uncovered n 1 E else uncovered n 1 O) =
      uncovered n 1 (if p = 0 then E else O) := by split_ifs <;> rfl
  rw [mem_uncovered, mem_mergeSides hp, mem_mergeSides hp, hChoice, mem_uncovered]
  have hlt : 2 * i + p < 2 * n ↔ i < n := by omega
  have hle : 2 ≤ 2 * i + p ↔ 1 ≤ i := by omega
  rw [hlt, hle]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine imp_congr_right fun hi => ?_
  rw [show 2 * i + p - 2 = 2 * (i - 1) + p by omega, mem_mergeSides hp]

private theorem pathWeight_mul (R : Type*) [CommSemiring R] (a b : R) (n : ℕ)
    (E O : Finset ℕ) :
    fenceTilingWeight a b n (mergeSides E O) = pathWeight a b n E * pathWeight a b n O := by
  change (∏ k ∈ uncovered (2 * n) 2 (mergeSides E O), cellWeight a b (k / 2)) = _
  rw [uncovered_mergeSides, mergeSides, prod_union, prod_map, prod_map]
  · have hdiv (p : ℕ) (hp : p < 2) (i : ℕ) : halfCell p i / 2 = i := by
      change (2 * i + p) / 2 = i
      omega
    simp only [hdiv 0 (by decide), hdiv 1 (by decide), pathWeight]
  · rw [disjoint_left]
    simp only [mem_map, halfCell_apply, not_exists, not_and]
    rintro _ ⟨i, _, hi⟩ j _ hj
    omega

-- The even and odd half-cells are independent copies of the same weighted path.
private theorem fenceTilingSum_eq_pathSum_sq {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    fenceTilingSum a b n = pathSum a b n ^ 2 := by
  rw [sq, pathSum, sum_mul_sum, ← sum_product']
  unfold fenceTilingSum
  symm
  refine sum_bij (fun P _ => mergeSides P.1 P.2) ?_ ?_ ?_ ?_
  · intro P hP
    exact mergeSides_mem.mpr (mem_product.mp hP)
  · rintro ⟨E, O⟩ _ ⟨E', O'⟩ _ h
    have side_eq (p : ℕ) (hp : p < 2) : (if p = 0 then E else O) =
        (if p = 0 then E' else O') := by
      ext i
      rw [← mem_mergeSides hp, ← mem_mergeSides hp, h]
    exact Prod.ext (by simpa using side_eq 0 (by decide)) (by simpa using side_eq 1 (by decide))
  · intro F hF
    refine ⟨(side 0 F, side 1 F), ?_, mergeSides_side F⟩
    exact mem_product.mpr (mergeSides_mem.mp (by rwa [mergeSides_side]))
  · rintro ⟨E, O⟩ _
    exact (pathWeight_mul R a b n E O).symm

private theorem pathTilings_succ_succ (n : ℕ) :
    pathTilings (n + 2) = pathTilings (n + 1) ∪ (pathTilings n).image (insert n) := by
  ext F
  simp only [mem_union, mem_image, mem_pathTilings]
  constructor
  · rintro ⟨hb, hs⟩
    by_cases hn : n ∈ F
    · right
      refine ⟨F.erase n, ⟨fun i hi => ?_, fun i hi hj => ?_⟩, insert_erase hn⟩
      · obtain ⟨hne, hmem⟩ := mem_erase.mp hi
        have hlt := hb _ hmem
        have hnmem := hs _ hmem
        by_contra! h
        exact hnmem (by rwa [show i + 1 = n by omega])
      · exact hs _ (mem_of_mem_erase hi) (mem_of_mem_erase hj)
    · exact Or.inl ⟨fun i hi => by
        have := hb _ hi
        by_contra! h
        exact hn (by rwa [show n = i by omega]), hs⟩
  · rintro (⟨hb, hs⟩ | ⟨G, ⟨hb, hs⟩, rfl⟩)
    · exact ⟨fun i hi => by have := hb _ hi; omega, hs⟩
    · refine ⟨fun i hi => ?_, fun i hi hj => ?_⟩
      · rcases mem_insert.mp hi with rfl | hi
        · omega
        · have := hb _ hi
          omega
      · rcases mem_insert.mp hi with rfl | hi
        · rcases mem_insert.mp hj with h | hj
          · omega
          · have := hb _ hj
            omega
        · rcases mem_insert.mp hj with h | hj
          · have := hb _ hi
            omega
          · exact hs _ hi hj

private theorem pathSum_zero {R : Type*} [CommSemiring R] (a b : R) : pathSum a b 0 = 1 := by
  simp [pathSum, pathTilings, pathWeight, uncovered, filter_singleton]

private theorem pathSum_one {R : Type*} [CommSemiring R] (a b : R) : pathSum a b 1 = a := by
  simp [pathSum, pathTilings, pathWeight, uncovered, cellWeight, filter_singleton]

private theorem pathSum_rec {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    pathSum a b (n + 2) = cellWeight a b (n + 1) * pathSum a b (n + 1) + pathSum a b n := by
  have not_last {m : ℕ} {F : Finset ℕ} (hf : F ∈ pathTilings m) {i : ℕ} (hi : m ≤ i + 1) :
      i ∉ F := fun h => (Nat.not_lt_of_ge hi) ((mem_pathTilings.mp hf).1 _ h)
  unfold pathSum
  rw [pathTilings_succ_succ, sum_union, sum_image, mul_sum]
  · congr 1
    · refine sum_congr rfl fun F hF => ?_
      have hu : uncovered (n + 2) 1 F = insert (n + 1) (uncovered (n + 1) 1 F) := by
        ext i
        simp only [mem_uncovered, mem_insert]
        by_cases hi : i = n + 1
        · subst i
          have hn := not_last hF (i := n) (by omega)
          have hn' := not_last hF (i := n + 1) (by omega)
          simp [hn, hn']
        · have hlt : i < n + 2 ↔ i < n + 1 := by omega
          simp [hi, hlt]
      rw [pathWeight, hu, prod_insert (fun h => by have := (mem_uncovered.mp h).1; omega)]
      rfl
    · refine sum_congr rfl fun F _ => ?_
      have hu : uncovered (n + 2) 1 (insert n F) = uncovered n 1 F := by
        ext i
        simp only [mem_uncovered, mem_insert, not_or]
        constructor
        · rintro ⟨hi, ⟨hne, hf⟩, hp⟩
          refine ⟨?_, hf, fun h => (hp h).2⟩
          have hh : i ≠ n + 1 := fun h => (hp (by omega)).1 (by omega)
          omega
        · rintro ⟨hi, hf, hp⟩
          exact ⟨by omega, ⟨by omega, hf⟩, fun h => ⟨by omega, hp h⟩⟩
      simp only [pathWeight, hu]
  · intro F hF G hG he
    have hF' := not_last hF (i := n) (by omega)
    have hG' := not_last hG (i := n) (by omega)
    ext i
    have hm : i ∈ insert n F ↔ i ∈ insert n G := by rw [he]
    by_cases hi : i = n
    · simp [hi, hF', hG']
    · simpa [mem_insert, hi] using hm
  · rw [disjoint_left]
    intro F hF h
    obtain ⟨G, _, rfl⟩ := mem_image.mp h
    exact not_last hF (i := n) (by omega) (mem_insert_self _ _)

-- Expanding the cross term twice leaves the preceding cross term, with no subtraction.
private theorem evenCross {R : Type*} [CommSemiring R] (a b : R) (k : ℕ) :
    b * pathSum a b (2 * k + 1) * pathSum a b (2 * k) =
      a * b * ∑ i ∈ range (k + 1), pathSum a b (2 * i) ^ 2 +
        b ^ 2 * ∑ i ∈ range k, pathSum a b (2 * i + 1) ^ 2 := by
  induction k with
  | zero => simp [pathSum_zero, pathSum_one, mul_comm]
  | succ k ih =>
    have ho : pathSum a b (2 * (k + 1) + 1) =
        a * pathSum a b (2 * (k + 1)) + pathSum a b (2 * k + 1) := by
      simpa only [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        show 2 * (k + 1) = (2 * k + 1) + 1 by omega, cellWeight,
        ite_eq_left (show (2 * k + 1 + 1) % 2 = 0 by omega)] using pathSum_rec a b (2 * k + 1)
    have he : pathSum a b (2 * (k + 1)) =
        b * pathSum a b (2 * k + 1) + pathSum a b (2 * k) := by
      simpa only [show 2 * (k + 1) = 2 * k + 2 by omega, cellWeight,
        ite_eq_right (show (2 * k + 1) % 2 ≠ 0 by omega)] using pathSum_rec a b (2 * k)
    rw [ho, sum_range_succ (fun i => pathSum a b (2 * i) ^ 2) (k + 1),
      sum_range_succ (fun i => pathSum a b (2 * i + 1) ^ 2) k]
    calc
      _ = a * b * pathSum a b (2 * (k + 1)) ^ 2 +
          b * pathSum a b (2 * k + 1) * pathSum a b (2 * (k + 1)) := by ring
      _ = a * b * pathSum a b (2 * (k + 1)) ^ 2 +
          (b ^ 2 * pathSum a b (2 * k + 1) ^ 2 +
            b * pathSum a b (2 * k + 1) * pathSum a b (2 * k)) := by
        congr 1
        rw [he]
        ring
      _ = _ := by rw [ih]; ring

private theorem sum_reverse_interval {M : Type*} [AddCommMonoid M] (f : ℕ → M) (l m : ℕ) :
    ∑ j ∈ Icc l m, f (m - j) = ∑ i ∈ range (m + 1 - l), f i := by
  refine sum_bij (fun j _ => m - j) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j hj
    rw [mem_Icc] at hj
    rw [mem_range]
    omega
  · intro j hj k hk h
    rw [mem_Icc] at hj hk
    omega
  · intro i hi
    rw [mem_range] at hi
    exact ⟨m - i, mem_Icc.mpr (by omega), by omega⟩

/-- **Recurrence for weighted fence tilings of even boards.** Let $a$ and $b$ be elements of a
commutative semiring $R$, and let $S_m$ be the weighted number of tilings of an $m$-board, with
cells numbered $1, \dots, m$, by half-squares and $(1/2, 1/2)$-fences, a half-square weighing $a$
in an odd cell and $b$ in an even cell. Then for every even $n \ge 2$,
$$
S_n = b^2 S_{n-1} + (2ab+1) S_{n-2} +
2ab \sum_{j=2}^{n/2} S_{n-2j} + 2b^2 \sum_{j=1}^{n/2-1} S_{n-2j-1}.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 2.1, (2.1) (`fq-2024-belaggoun01132024-lem-2.1`). -/
public theorem fenceTilingSum_even {R : Type*} [CommSemiring R] (a b : R) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) :
    fenceTilingSum a b n =
      b ^ 2 * fenceTilingSum a b (n - 1) + (2 * a * b + 1) * fenceTilingSum a b (n - 2) +
        2 * a * b * ∑ j ∈ Icc 2 (n / 2), fenceTilingSum a b (n - 2 * j) +
        2 * b ^ 2 * ∑ j ∈ Icc 1 (n / 2 - 1), fenceTilingSum a b (n - 2 * j - 1) := by
  obtain ⟨m, hm⟩ := he
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h : n = 2 * k + 2 := by omega
  rw [h]
  simp only [fenceTilingSum_eq_pathSum_sq, show (2 * k + 2) / 2 = k + 1 by omega,
    show 2 * k + 2 - 1 = 2 * k + 1 by omega, show 2 * k + 2 - 2 = 2 * k by omega,
    Nat.add_sub_cancel]
  have hEven : (∑ j ∈ Icc 2 (k + 1), pathSum a b (2 * k + 2 - 2 * j) ^ 2) =
      ∑ i ∈ range k, pathSum a b (2 * i) ^ 2 := by
    simp_rw [show ∀ j : ℕ, 2 * k + 2 - 2 * j = 2 * (k + 1 - j) from fun j => by omega]
    simpa only [show k + 1 + 1 - 2 = k by omega] using
      sum_reverse_interval (fun i => pathSum a b (2 * i) ^ 2) 2 (k + 1)
  have hOdd : (∑ j ∈ Icc 1 k, pathSum a b (2 * k + 2 - 2 * j - 1) ^ 2) =
      ∑ i ∈ range k, pathSum a b (2 * i + 1) ^ 2 := by
    calc
      _ = ∑ j ∈ Icc 1 k, pathSum a b (2 * (k - j) + 1) ^ 2 := by
        refine sum_congr rfl fun j hj => ?_
        have := (mem_Icc.mp hj).2
        rw [show 2 * k + 2 - 2 * j - 1 = 2 * (k - j) + 1 by omega]
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          sum_reverse_interval (fun i => pathSum a b (2 * i + 1) ^ 2) 1 k
  have hRec : pathSum a b (2 * k + 2) = b * pathSum a b (2 * k + 1) + pathSum a b (2 * k) := by
    simpa only [cellWeight, ite_eq_right (show (2 * k + 1) % 2 ≠ 0 by omega)] using
      pathSum_rec a b (2 * k)
  rw [hEven, hOdd, hRec]
  calc
    _ = b ^ 2 * pathSum a b (2 * k + 1) ^ 2 + pathSum a b (2 * k) ^ 2 +
        2 * (b * pathSum a b (2 * k + 1) * pathSum a b (2 * k)) := by ring
    _ = _ := by rw [evenCross, sum_range_succ (n := k)]; ring

-- The starts of disjoint length-three blocks in a span of m half-cells.
private def spacedTilings (m i : ℕ) : Finset (Finset ℕ) :=
  ((range (m - 2)).powersetCard i).filter fun F => ∀ j ∈ F, ∀ k ∈ F, j < k → j + 3 ≤ k

private theorem mem_spacedTilings {m i : ℕ} {F : Finset ℕ} :
    F ∈ spacedTilings m i ↔ (∀ k ∈ F, k + 2 < m) ∧ F.card = i ∧
      (∀ j ∈ F, ∀ k ∈ F, j < k → j + 3 ≤ k) := by
  simp only [spacedTilings, mem_filter, mem_powersetCard, Finset.subset_iff, mem_range, and_assoc]
  exact and_congr_left' (forall_congr' fun _ => imp_congr_right fun _ => by omega)

-- Either the last half-cell is free, or it ends a block beginning at m.
private theorem spacedTilings_split (m i : ℕ) :
    spacedTilings (m + 3) (i + 1) =
      spacedTilings (m + 2) (i + 1) ∪ (spacedTilings m i).image (insert m) := by
  ext F
  simp only [mem_union, mem_image, mem_spacedTilings]
  constructor
  · rintro ⟨hbound, hcard, hsep⟩
    by_cases hm : m ∈ F
    · right
      refine ⟨F.erase m, ⟨fun k hk => ?_, by rw [card_erase_of_mem hm, hcard]; omega,
        fun j hj k hk hjk => hsep j (mem_of_mem_erase hj) k (mem_of_mem_erase hk) hjk⟩,
        insert_erase hm⟩
      obtain ⟨hne, hk⟩ := mem_erase.mp hk
      have := hbound k hk
      have := hsep k hk m hm (by omega)
      omega
    · refine Or.inl ⟨fun k hk => ?_, hcard, hsep⟩
      have := hbound k hk
      by_contra! h
      exact hm (by rwa [show m = k by omega])
  · rintro (⟨hbound, hcard, hsep⟩ | ⟨G, ⟨hbound, hcard, hsep⟩, rfl⟩)
    · exact ⟨fun k hk => by have := hbound k hk; omega, hcard, hsep⟩
    · have hm : m ∉ G := fun h => by have := hbound m h; omega
      refine ⟨?_, by rw [card_insert_of_notMem hm, hcard], ?_⟩
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · omega
        · have := hbound k hk
          omega
      · intro j hj k hk hjk
        rcases mem_insert.mp hj with hj | hj
        · rcases mem_insert.mp hk with hk | hk
          · omega
          · have := hbound k hk
            omega
        · rcases mem_insert.mp hk with hk | hk
          · have := hbound j hj
            omega
          · exact hsep j hj k hk hjk

private theorem card_spacedTilings (m i : ℕ) :
    (spacedTilings m i).card = (m - 2 * i).choose i := by
  induction m using Nat.strong_induction_on generalizing i with
  | ind m ih =>
    cases i with
    | zero => simp [spacedTilings, filter_singleton]
    | succ i =>
      obtain rfl | rfl | rfl | ⟨m, rfl⟩ : m = 0 ∨ m = 1 ∨ m = 2 ∨ ∃ k, m = k + 3 := by
        by_cases h : m < 3
        · omega
        · exact Or.inr (Or.inr (Or.inr ⟨m - 3, by omega⟩))
      · simp [spacedTilings]
      · simp [spacedTilings, show 1 - 2 * (i + 1) = 0 by omega]
      · simp [spacedTilings, show 2 - 2 * (i + 1) = 0 by omega]
      have fresh (F : Finset ℕ) (hF : F ∈ spacedTilings m i) : m ∉ F := fun h => by
        have := (mem_spacedTilings.mp hF).1 m h
        omega
      have hinj : Set.InjOn (fun F : Finset ℕ => insert m F) ↑(spacedTilings m i) := by
        intro F hF G hG eq
        simpa only [erase_insert (fresh F hF), erase_insert (fresh G hG)] using
          congrArg (fun S : Finset ℕ => S.erase m) eq
      have hdisj : Disjoint (spacedTilings (m + 2) (i + 1))
          ((spacedTilings m i).image (insert m)) := by
        rw [disjoint_left]
        intro F hF himage
        obtain ⟨G, _, rfl⟩ := mem_image.mp himage
        have := (mem_spacedTilings.mp hF).1 m (mem_insert_self m G)
        omega
      rw [spacedTilings_split, card_union_of_disjoint hdisj, card_image_of_injOn hinj,
        ih (m + 2) (by omega), ih m (by omega)]
      by_cases h : 2 * i ≤ m
      · rw [show m + 3 - 2 * (i + 1) = (m - 2 * i) + 1 by omega,
          show m + 2 - 2 * (i + 1) = m - 2 * i by omega, Nat.choose_succ_succ, add_comm]
      · have hz := Nat.choose_eq_zero_of_lt (show 0 < i by omega)
        simp [show m + 3 - 2 * (i + 1) = 0 by omega,
          show m + 2 - 2 * (i + 1) = 0 by omega, show m - 2 * i = 0 by omega, hz]

private theorem mem_noBifenceFiber {n i : ℕ} {F : Finset ℕ} :
    F ∈ ((fenceTilings n).filter (fun F => ∀ k ∈ F, k + 1 ∉ F)).filter (fun F => F.card = i) ↔
      F ∈ spacedTilings (2 * n) i := by
  simp only [mem_filter, mem_fenceTilings, mem_spacedTilings]
  constructor
  · rintro ⟨⟨⟨hb, h₂⟩, h₁⟩, hc⟩
    refine ⟨hb, hc, fun j hj k hk hjk => ?_⟩
    by_contra! h
    obtain rfl | rfl : k = j + 1 ∨ k = j + 2 := by omega
    · exact h₁ j hj hk
    · exact h₂ j hj hk
  · rintro ⟨hb, hc, hs⟩
    exact ⟨⟨⟨hb, fun k hk hj => by have := hs k hk (k + 2) hj (by omega); omega⟩,
      fun k hk hj => by have := hs k hk (k + 1) hj (by omega); omega⟩, hc⟩

private theorem card_le_span {m i : ℕ} {F : Finset ℕ} (hF : F ∈ spacedTilings m i) :
    i ≤ m / 3 := by
  have hpos : 0 < (spacedTilings m i).card := card_pos.mpr ⟨F, hF⟩
  rw [card_spacedTilings] at hpos
  by_contra! h
  rw [Nat.choose_eq_zero_of_lt (show m - 2 * i < i by omega)] at hpos
  omega

-- The product on the completely uncovered board. Adding a cell adds two equal weights.
private theorem prod_halfCellWeight {K : Type*} [Field K] (a b : K) (hb : b ≠ 0) (n : ℕ) :
    (∏ k ∈ range (2 * n), cellWeight a b (k / 2)) = (a / b) ^ (n % 2) * (a * b) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, prod_range_succ, prod_range_succ, ih,
      show (2 * n + 1) / 2 = n by omega, show (2 * n) / 2 = n by omega]
    have hcancel := div_mul_cancel₀ a hb
    by_cases he : n % 2 = 0
    · simp only [cellWeight, he, ite_true, pow_zero, one_mul,
        show (n + 1) % 2 = 1 by omega, pow_one, pow_succ (a * b) n]
      calc
        _ = (a / b * b) * a * (a * b) ^ n := by rw [hcancel]; ring
        _ = _ := by ring
    · simp only [cellWeight, show n % 2 = 1 by omega, ite_eq_right (by decide : (1 : ℕ) ≠ 0),
        pow_one, show (n + 1) % 2 = 0 by omega, pow_zero, one_mul, pow_succ (a * b) n]
      calc
        _ = (a / b * b) * b * (a * b) ^ n := by ring
        _ = _ := by rw [hcancel]; ring

-- Each fence has one post in each color; the removed factor is ab per fence.
private theorem fenceTilingWeight_eq_pow {K : Type*} [Field K] {a b : K} (ha : a ≠ 0)
    (hb : b ≠ 0) {n : ℕ} {F : Finset ℕ} (hF : F ∈ fenceTilings n) (hc : F.card ≤ n) :
    fenceTilingWeight a b n F = (a / b) ^ (n % 2) * (a * b) ^ (n - F.card) := by
  obtain ⟨hbound, hsep⟩ := mem_fenceTilings.mp hF
  have hsub : F ∪ F.image (· + 2) ⊆ range (2 * n) := by
    intro k hk
    rw [mem_range]
    rcases mem_union.mp hk with hk | hk
    · have := hbound k hk
      omega
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      exact hbound j hj
  have hdisj : Disjoint F (F.image (· + 2)) := by
    rw [disjoint_left]
    intro k hk himage
    obtain ⟨j, hj, rfl⟩ := mem_image.mp himage
    exact hsep j hj hk
  have hposts : (∏ k ∈ F ∪ F.image (· + 2), cellWeight a b (k / 2)) = (a * b) ^ F.card := by
    rw [prod_union hdisj, prod_image (fun i _ j _ hij => by omega), ← prod_mul_distrib]
    calc
      _ = ∏ _k ∈ F, a * b := by
        refine prod_congr rfl fun k _ => ?_
        have hstep : (k + 2) / 2 = k / 2 + 1 := by omega
        rw [hstep, cellWeight, cellWeight]
        by_cases h : k / 2 % 2 = 0
        · simp [h, show (k / 2 + 1) % 2 ≠ 0 by omega]
        · simp [h, show (k / 2 + 1) % 2 = 0 by omega, mul_comm]
      _ = _ := prod_const _
  apply mul_right_cancel₀ (pow_ne_zero F.card (mul_ne_zero ha hb))
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hc, ← prod_halfCellWeight a b hb n, ← hposts]
  exact prod_sdiff hsub

/-- **Closed formula for bifence-free fence tilings.** Let $a$, $b$ be nonzero elements of a field
and let $\xi(n) = n \bmod 2$. For every natural number $n$, the weighted number $C_n$ of tilings of
the $n$-board by half-squares and $(1/2, 1/2)$-fences with no bifence, with half-square weights
$a$ and $b$, is
$$
C_n = \left(\frac{a}{b}\right)^{\xi(n)}
\sum_{i=0}^{\lfloor 2n/3 \rfloor} \binom{2n-2i}{i} (ab)^{n-i}.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15 (`fq-2024-belaggoun01132024-lem-3.15`). -/
public theorem noBifenceTilingSum_eq_sum_choose {K : Type*} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    noBifenceTilingSum a b n =
      (a / b) ^ (n % 2) *
        ∑ i ∈ range (2 * n / 3 + 1), ((2 * n - 2 * i).choose i : K) * (a * b) ^ (n - i) := by
  have maps (F : Finset ℕ) (hF : F ∈ (fenceTilings n).filter
      (fun F => ∀ k ∈ F, k + 1 ∉ F)) : F.card ∈ range (2 * n / 3 + 1) := by
    have h := card_le_span (mem_noBifenceFiber.mp (mem_filter.mpr ⟨hF, rfl⟩))
    exact mem_range.mpr (by omega)
  rw [noBifenceTilingSum, ← sum_fiberwise_of_maps_to (g := Finset.card) maps, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := by have := mem_range.mp hi; omega
  have hfiber := Finset.ext fun F => @mem_noBifenceFiber n i F
  rw [hfiber]
  calc
    _ = ∑ _F ∈ spacedTilings (2 * n) i, (a / b) ^ (n % 2) * (a * b) ^ (n - i) := by
      refine sum_congr rfl fun F hF => ?_
      obtain ⟨hF', hc⟩ := mem_filter.mp (mem_noBifenceFiber.mpr hF)
      rw [fenceTilingWeight_eq_pow ha hb (mem_filter.mp hF').1 (by omega), hc]
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_spacedTilings]; ring

end MetaMathlibExt
