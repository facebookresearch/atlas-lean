/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Finite.Sigma
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting sums of proper Zeckendorf blocks

A sum supported in the first `n` indices is determined by its first proper block and the
translated remainder. A gap at the start can be filled by the zero singleton block.

This proves the recurrence printed in Chang's Proposition 4 (arXiv:2308.12872v1,
Proposition 4.8) for the zero-inclusive count of bounded block sums. For `n > 0`, the
paper's prose restricts $S_n$ to the nonzero collection $E^*$. A bounded decomposition
that ends before the paper's one-based index `n` can be extended to that endpoint by
appending a zero singleton block at `n`, since $e_1 > 0$. Thus the bounded collection
counted here is exactly $S_n \cup \{0\}$ for `n > 0`.

## References

* Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
  pp. 1–45, Definition 17 and Proposition 4.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The maximal $L^*$-block.** Let $L = (e_1, \dots, e_N)$ be a list of natural numbers and $s$
an index, with indices starting at $0$. The maximal $L^*$-block starting at $s$ is the
coefficient function whose entry at index $i$ is $0$ for $i < s$, and $e_j$ for $i \ge s$, where
$j - 1 = (i - s) \bmod N$ (every entry is $0$ when $L$ is empty). It is the paper's
$\bar\beta^{s+1}$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def maxLStarBlock (L : List ℕ) (s i : ℕ) : ℕ :=
  if i < s then 0 else L.getD ((i - s) % L.length) 0

/-- **Digits before the start of a maximal block.** A maximal $L^*$-block has digit zero at
any index strictly before its starting index. -/
public theorem maxLStarBlock_of_lt {L : List ℕ} {s i : ℕ} (h : i < s) :
    maxLStarBlock L s i = 0 := by
  simp [maxLStarBlock, h]

/-- **Digits at and after the start of a maximal block.** From its starting index onward, a
maximal $L^*$-block repeats the entries of `L`, taking the default digit zero if `L` is empty. -/
public theorem maxLStarBlock_of_le {L : List ℕ} {s i : ℕ} (h : s ≤ i) :
    maxLStarBlock L s i = L.getD ((i - s) % L.length) 0 := by
  simp [maxLStarBlock, not_lt.mpr h]

/-- **Sums of disjoint proper $L^\ast$-blocks.** Let $L$ be a list of natural numbers, and for
each $s$ let $\bar\beta^{s+1}$ be the maximal $L^*$-block starting at (zero-based) index $s$. Let
$I$ be a finite or infinite set of pairs $(s, k)$ of natural numbers. A coefficient function
$\varepsilon : \mathbb N \to \mathbb N$ is the sum of the disjoint proper $L^*$-blocks with
support intervals $[s, k]$, $(s, k) \in I$, if $s \le k$ for every $(s, k) \in I$, the intervals
$[s, k]$ of distinct pairs in $I$ are pairwise disjoint, for every $(s, k) \in I$ we have
$\varepsilon_i = \bar\beta^{s+1}_i$ whenever $s \le i < k$ and
$\varepsilon_k < \bar\beta^{s+1}_k$, and $\varepsilon_i = 0$ for every index $i$ that lies in
none of the intervals.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def IsLStarBlockSum (L : List ℕ) (I : Set (ℕ × ℕ)) (ε : ℕ → ℕ) : Prop :=
  (∀ p ∈ I, p.1 ≤ p.2) ∧ I.PairwiseDisjoint (fun p => Set.Icc p.1 p.2) ∧
    (∀ p ∈ I, (∀ i, p.1 ≤ i → i < p.2 → ε i = maxLStarBlock L p.1 i) ∧
      ε p.2 < maxLStarBlock L p.1 p.2) ∧
    ∀ i, (∀ p ∈ I, i ∉ Set.Icc p.1 p.2) → ε i = 0

/-- **Block sums by disjoint intervals and support.** A coefficient function is a sum of
proper $L^*$-blocks on `I` precisely when the intervals are disjoint, each interval has
ordered endpoints and the prescribed digits, and their union contains every nonzero digit. -/
public theorem isLStarBlockSum_iff {L : List ℕ} {I : Set (ℕ × ℕ)} {ε : ℕ → ℕ} :
    IsLStarBlockSum L I ε ↔
      I.PairwiseDisjoint (fun p => Set.Icc p.1 p.2) ∧
      (∀ p ∈ I, p.1 ≤ p.2 ∧ Set.EqOn ε (maxLStarBlock L p.1) (Set.Ico p.1 p.2) ∧
        ε p.2 < maxLStarBlock L p.1 p.2) ∧
      Function.support ε ⊆ ⋃ p ∈ I, Set.Icc p.1 p.2 := by
  classical
  constructor
  · rintro ⟨horder, hdisj, hdigit, hzero⟩
    refine ⟨hdisj, fun p hp => ⟨horder p hp, fun _ h => (hdigit p hp).1 _ h.1 h.2,
      (hdigit p hp).2⟩, fun i hi => ?_⟩
    simp only [Set.mem_iUnion, exists_prop]
    by_contra! h
    exact hi (hzero i h)
  · rintro ⟨hdisj, hdigit, hsupport⟩
    refine ⟨fun p hp => (hdigit p hp).1, hdisj,
      fun p hp => ⟨fun i hlo hhi => (hdigit p hp).2.1 ⟨hlo, hhi⟩, (hdigit p hp).2.2⟩,
      fun i hi => ?_⟩
    by_contra h
    have hmem := hsupport (show i ∈ Function.support ε from h)
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨p, hp, hpi⟩ := hmem
    exact hi p hp hpi

/-- **Number of $L^*$-block sums of length $n$.** For a list $L$ of natural numbers and $n \ge 0$,
with coefficient functions indexed from $1$, $C_n$ is the number of functions
$\varepsilon : \mathbb N \to \mathbb N$ that are sums of disjoint proper $L^*$-blocks with
support intervals inside $[1, n]$. The zero function (the empty sum) is counted, so $C_0 = 1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (arXiv:2308.12872v1, Section 4.1). -/
public noncomputable def lStarBlockSumCount (L : List ℕ) (n : ℕ) : ℕ :=
  {ε : ℕ → ℕ | ∃ I, IsLStarBlockSum L I ε ∧ ∀ p ∈ I, p.2 < n}.ncard

end

private abbrev blockWords (L : List ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {ε | ∃ I, IsLStarBlockSum L I ε ∧ ∀ p ∈ I, p.2 < n}

private def shift (d : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + d, p.2 + d)

private lemma shift_injective (d : ℕ) : Function.Injective (shift d) := by
  intro p q h
  exact Prod.ext (Nat.add_right_cancel (congrArg Prod.fst h))
    (Nat.add_right_cancel (congrArg Prod.snd h))

private lemma mem_shift_Icc (d i : ℕ) (p : ℕ × ℕ) :
    i + d ∈ Set.Icc (shift d p).1 (shift d p).2 ↔ i ∈ Set.Icc p.1 p.2 := by
  simp [shift]

private lemma maxLStarBlock_shift (L : List ℕ) (d s i : ℕ) :
    maxLStarBlock L (s + d) (i + d) = maxLStarBlock L s i := by
  simp [maxLStarBlock, show i + d - (s + d) = i - s by omega]

-- An interval covering zero supplies the first block. Otherwise the zero digit supplies a
-- singleton block. In either case every interval other than this first block starts later.
private lemma exists_head (L : List ℕ) (he : L.getD 0 0 ≠ 0) {n : ℕ} (hn : 0 < n)
    {I : Set (ℕ × ℕ)} {ε : ℕ → ℕ} (h : IsLStarBlockSum L I ε)
    (hbound : ∀ p ∈ I, p.2 < n) :
    ∃ j < n, (∀ i < j, ε i = maxLStarBlock L 0 i) ∧ ε j < maxLStarBlock L 0 j ∧
      ∀ p ∈ I, p ≠ (0, j) → j < p.1 := by
  by_cases hzero : ∃ j, (0, j) ∈ I
  · obtain ⟨j, hj⟩ := hzero
    obtain ⟨hprefix, hdigit⟩ := h.2.2.1 (0, j) hj
    refine ⟨j, hbound (0, j) hj, fun i hi => hprefix i (Nat.zero_le _) hi, hdigit, ?_⟩
    intro p hp hne
    by_contra! hle
    exact Set.disjoint_left.mp (h.2.1 hp hj hne) ⟨le_rfl, h.1 _ hp⟩ ⟨Nat.zero_le _, hle⟩
  · have hpos : ∀ p ∈ I, 0 < p.1 := by
      rintro ⟨s, k⟩ hp
      by_contra! hs
      exact hzero ⟨k, by simpa [show s = 0 by omega] using hp⟩
    have hε : ε 0 = 0 := h.2.2.2 0 (fun p hp hi => (Nat.not_lt_of_ge hi.1) (hpos p hp))
    refine ⟨0, hn, by simp, ?_, fun p hp _ => hpos p hp⟩
    simpa [hε, maxLStarBlock] using Nat.pos_of_ne_zero he

private lemma tail_mem (L : List ℕ) {n j : ℕ} {I : Set (ℕ × ℕ)} {ε : ℕ → ℕ}
    (h : IsLStarBlockSum L I ε) (hbound : ∀ p ∈ I, p.2 < n)
    (hrest : ∀ p ∈ I, p ≠ (0, j) → j < p.1) :
    (fun i => ε (i + (j + 1))) ∈ blockWords L (n - (j + 1)) := by
  let d := j + 1
  let J := shift d ⁻¹' I
  have lower (p : ℕ × ℕ) (hp : p ∈ J) : p.1 ≤ p.2 := by
    simpa [shift] using h.1 (shift d p) hp
  refine ⟨J, ⟨lower, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp q hq hpq
    refine Set.disjoint_left.mpr fun i hi hj => ?_
    exact Set.disjoint_left.mp (h.2.1 hp hq ((shift_injective d).ne hpq))
      ((mem_shift_Icc d i p).mpr hi) ((mem_shift_Icc d i q).mpr hj)
  · intro p hp
    obtain ⟨hprefix, hdigit⟩ := h.2.2.1 (shift d p) hp
    refine ⟨fun i hsi hik => ?_, ?_⟩
    · simpa [shift, maxLStarBlock_shift] using
        hprefix (i + d) (Nat.add_le_add_right hsi d) (Nat.add_lt_add_right hik d)
    · simpa [shift, maxLStarBlock_shift] using hdigit
  · intro i hi
    apply h.2.2.2
    intro p hp hpi
    have hj : j < p.1 := hrest p hp (by
      intro heq
      rw [heq] at hpi
      have hupper := hpi.2
      change i + d ≤ j at hupper
      dsimp [d] at hupper
      omega)
    have hs : shift d (p.1 - d, p.2 - d) = p := by
      have := h.1 p hp
      apply Prod.ext <;> dsimp [shift, d] <;> omega
    apply hi (p.1 - d, p.2 - d) (show shift d (p.1 - d, p.2 - d) ∈ I by rwa [hs])
    exact (mem_shift_Icc d i _).mp (by rwa [hs])
  · intro p hp
    have hb := hbound (shift d p) hp
    dsimp [shift, d] at hb
    omega

private def graft (L : List ℕ) (j a : ℕ) (ε : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < j then maxLStarBlock L 0 i else if i = j then a else ε (i - (j + 1))

private lemma graft_at_head (L : List ℕ) (j a : ℕ) (ε : ℕ → ℕ) : graft L j a ε j = a := by
  simp [graft]

private lemma graft_at_tail (L : List ℕ) (j a : ℕ) (ε : ℕ → ℕ) (i : ℕ) :
    graft L j a ε (i + (j + 1)) = ε i := by
  simp [graft, show ¬ i + (j + 1) < j by omega, show i + (j + 1) ≠ j by omega]

private lemma graft_mem (L : List ℕ) {n j a : ℕ} (hj : j < n)
    (ha : a < maxLStarBlock L 0 j) {ε : ℕ → ℕ} (hε : ε ∈ blockWords L (n - (j + 1))) :
    graft L j a ε ∈ blockWords L n := by
  obtain ⟨I, h, hbound⟩ := hε
  let d := j + 1
  let J := shift d '' I
  have later (p : ℕ × ℕ) (hp : p ∈ J) : j < p.1 := by
    obtain ⟨q, _, rfl⟩ := hp
    dsimp [shift, d]
    omega
  have unshift (p : ℕ × ℕ) (i : ℕ) (hi : i ∈ Set.Icc (shift d p).1 (shift d p).2) :
      i - d ∈ Set.Icc p.1 p.2 := by
    have hdi : d ≤ i := le_trans (Nat.le_add_left d p.1) hi.1
    apply (mem_shift_Icc d _ p).mp
    rwa [Nat.sub_add_cancel hdi]
  refine ⟨insert (0, j) J, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    rw [Set.mem_insert_iff] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact Nat.zero_le _
    · exact Nat.add_le_add_right (h.1 _ hq) d
  · rw [Set.pairwiseDisjoint_insert]
    constructor
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
      refine Set.disjoint_left.mpr fun i hi hqi => ?_
      exact Set.disjoint_left.mp (h.2.1 hp hq (ne_of_apply_ne _ hpq))
        (unshift p i hi) (unshift q i hqi)
    · intro p hp _
      exact Set.disjoint_left.mpr fun i hi hpi => (not_le_of_gt (later p hp)) (hpi.1.trans hi.2)
  · intro p hp
    rw [Set.mem_insert_iff] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact ⟨fun i _ hi => by simp [graft, hi], by rwa [graft_at_head]⟩
    · obtain ⟨hprefix, hdigit⟩ := h.2.2.1 _ hq
      constructor
      · intro i hsi hik
        have hdi : d ≤ i := le_trans (Nat.le_add_left d q.1) hsi
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hdi
        rw [Nat.add_comm d t] at hsi hik ⊢
        change graft L j a ε (t + d) = maxLStarBlock L (q.1 + d) (t + d)
        rw [graft_at_tail, maxLStarBlock_shift]
        apply hprefix
        · exact Nat.le_of_add_le_add_right hsi
        · exact Nat.lt_of_add_lt_add_right hik
      · simpa [shift, d, graft_at_tail, maxLStarBlock_shift] using hdigit
  · intro i hi
    have hji : j < i := by
      by_contra! hle
      exact hi (0, j) (Set.mem_insert _ _) ⟨Nat.zero_le _, hle⟩
    have hdi : d ≤ i := hji
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hdi
    rw [Nat.add_comm d t] at hi ⊢
    rw [graft_at_tail]
    apply h.2.2.2
    intro p hp hpi
    exact hi (shift d p) (Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hp))
      ((mem_shift_Icc d t p).mpr hpi)
  · intro p hp
    rw [Set.mem_insert_iff] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact hj
    · have := hbound _ hq
      dsimp [shift, d]
      omega

private lemma maxLStarBlock_start (L : List ℕ) (j : ℕ) :
    maxLStarBlock L 0 j = L.getD (j % L.length) 0 := by
  simp [maxLStarBlock]

private abbrev headAndTail (L : List ℕ) (n : ℕ) :=
  Σ j : Fin n, Fin (L.getD (j.val % L.length) 0) × ↥(blockWords L (n - (j.val + 1)))

private def fromHeadAndTail (L : List ℕ) (n : ℕ) (x : headAndTail L n) : blockWords L n :=
  ⟨graft L x.1 x.2.1 x.2.2,
    graft_mem L x.1.isLt (by simpa [maxLStarBlock_start] using x.2.1.isLt) x.2.2.property⟩

private lemma head_le_of_graft_eq (L : List ℕ) {j k a b : ℕ} {ε δ : ℕ → ℕ}
    (ha : a < maxLStarBlock L 0 j) (h : graft L j a ε = graft L k b δ) : k ≤ j := by
  by_contra! hjk
  have hval := congrFun h j
  rw [graft_at_head] at hval
  exact (ne_of_lt ha) (hval.trans (by simp [graft, hjk]))

private lemma fromHeadAndTail_injective (L : List ℕ) (n : ℕ) :
    Function.Injective (fromHeadAndTail L n) := by
  rintro ⟨j, a, ε⟩ ⟨k, b, δ⟩ h
  have hh : graft L j a ε = graft L k b δ := congrArg Subtype.val h
  have ha : a.val < maxLStarBlock L 0 j := by simpa [maxLStarBlock_start] using a.isLt
  have hb : b.val < maxLStarBlock L 0 k := by simpa [maxLStarBlock_start] using b.isLt
  have hjk : j = k := Fin.ext (le_antisymm (head_le_of_graft_eq L hb hh.symm)
    (head_le_of_graft_eq L ha hh))
  subst k
  have hab : a = b := Fin.ext (by simpa only [graft_at_head] using congrFun hh j.val)
  have ht : ε = δ := Subtype.ext (funext fun i => by
    simpa only [graft_at_tail] using congrFun hh (i + (j.val + 1)))
  subst b
  subst δ
  rfl

private lemma fromHeadAndTail_surjective (L : List ℕ) (he : L.getD 0 0 ≠ 0) {n : ℕ}
    (hn : 0 < n) : Function.Surjective (fromHeadAndTail L n) := by
  rintro ⟨ε, I, h, hbound⟩
  obtain ⟨j, hj, hprefix, hdigit, hrest⟩ := exists_head L he hn h hbound
  refine ⟨⟨⟨j, hj⟩, ⟨ε j, by simpa [maxLStarBlock_start] using hdigit⟩,
    ⟨_, tail_mem L h hbound hrest⟩⟩, Subtype.ext (funext fun i => ?_)⟩
  change graft L j (ε j) (fun t => ε (t + (j + 1))) i = ε i
  by_cases hi : i < j
  · simp [graft, hi, hprefix i hi]
  by_cases heq : i = j
  · subst i
    exact graft_at_head _ _ _ _
  simp [graft, hi, heq, Nat.sub_add_cancel (show j + 1 ≤ i by omega)]

private noncomputable def wordEquiv (L : List ℕ) (he : L.getD 0 0 ≠ 0) {n : ℕ} (hn : 0 < n) :
    headAndTail L n ≃ blockWords L n :=
  Equiv.ofBijective _ ⟨fromHeadAndTail_injective L n, fromHeadAndTail_surjective L he hn⟩

private lemma finite_blockWords (L : List ℕ) (he : L.getD 0 0 ≠ 0) (n : ℕ) :
    Finite ↥(blockWords L n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      have hz (ε : blockWords L 0) : ε.val = 0 := by
        obtain ⟨I, h, hb⟩ := ε.property
        funext i
        exact h.2.2.2 i (fun p hp _ => Nat.not_lt_zero _ (hb p hp))
      exact Finite.of_injective (fun _ => ()) (fun ε δ _ => Subtype.ext ((hz ε).trans (hz δ).symm))
    · have (j : Fin n) : Finite ↥(blockWords L (n - (j.val + 1))) :=
        ih _ (by have := j.isLt; omega)
      exact Finite.of_equiv _ (wordEquiv L he (Nat.pos_of_ne_zero hn))

-- First-block lengths are indexed by their zero-based endpoints. The digit at that endpoint
-- ranges over `Fin (L.getD (j % L.length) 0)` independently of the remaining word.
private lemma count_eq_sum_range (L : List ℕ) (he : L.getD 0 0 ≠ 0) {n : ℕ} (hn : 0 < n) :
    lStarBlockSumCount L n = ∑ j ∈ Finset.range n,
      L.getD (j % L.length) 0 * lStarBlockSumCount L (n - (j + 1)) := by
  have (j : Fin n) : Finite ↥(blockWords L (n - (j.val + 1))) := finite_blockWords L he _
  rw [← Fin.sum_univ_eq_sum_range]
  change (blockWords L n).ncard = _
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (wordEquiv L he hn), Nat.card_sigma]
  simp only [Nat.card_prod, Nat.card_fin, Nat.card_coe_set_eq, lStarBlockSumCount]

/-- **Recurrence for the number of $L^*$-block sums.** Let $L = (e_1, \dots, e_N)$ be a list of
natural numbers with $N \ge 2$ and $e_1 \ne 0$, index coefficient functions from $1$, and let
$C_n$ be the number of functions $\mathbb N \to \mathbb N$ that are sums of disjoint proper
$L^*$-blocks with support intervals inside $[1, n]$. Then $C_k = \sum_{j=1}^{k} e_j C_{k-j}$ for
$1 \le k \le N$, and $C_n = \sum_{k=1}^{N-1} e_k C_{n-k} + (1 + e_N) C_{n-N}$ for $n \ge N + 1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (`integers-2025-A25-prop-4`; arXiv:2308.12872v1, Section 4.1). -/
public theorem lStarBlockSumCount_recurrence (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    (∀ k, 1 ≤ k → k ≤ L.length → lStarBlockSumCount L k =
      ∑ j ∈ Finset.Icc 1 k, L.getD (j - 1) 0 * lStarBlockSumCount L (k - j)) ∧
    ∀ n, L.length + 1 ≤ n → lStarBlockSumCount L n =
      ∑ k ∈ Finset.Ico 1 L.length, L.getD (k - 1) 0 * lStarBlockSumCount L (n - k) +
        (1 + L.getD (L.length - 1) 0) * lStarBlockSumCount L (n - L.length) := by
  constructor
  · intro k hk hkle
    rw [count_eq_sum_range L he (by omega : 0 < k), ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    rw [show k + 1 - 1 = k by omega]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    rw [Nat.mod_eq_of_lt (show j < L.length by omega), Nat.add_comm 1 j]
    simp
  · intro n hn
    have hlen : 0 < L.length := by omega
    have htail : 0 < n - L.length := by omega
    have hsplit : n = L.length + (n - L.length) := by omega
    calc
      lStarBlockSumCount L n =
          (∑ i ∈ Finset.range L.length,
            L.getD i 0 * lStarBlockSumCount L (n - (i + 1))) +
          lStarBlockSumCount L (n - L.length) := by
        rw [count_eq_sum_range L he (by omega : 0 < n)]
        nth_rw 1 [hsplit]
        rw [Finset.sum_range_add, count_eq_sum_range L he htail]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
        · apply Finset.sum_congr rfl
          intro i _
          rw [Nat.add_mod_left, show n - (L.length + i + 1) = n - L.length - (i + 1) by omega]
      _ = _ := by
        rw [Finset.sum_Ico_eq_sum_range]
        have hN : L.length - 1 + 1 = L.length := by omega
        nth_rw 1 [← hN]
        rw [Finset.sum_range_succ]
        simp only [Nat.add_comm 1, hN, add_mul, one_mul]
        ac_rfl

end MetaMathlibExt
