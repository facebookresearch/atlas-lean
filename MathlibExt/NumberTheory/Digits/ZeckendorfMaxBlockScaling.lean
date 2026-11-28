/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.Digits.ZeckendorfBlockCountRecurrence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Shifted maximal blocks scale geometrically

Let $\tilde L = (e_1, \dots, e_N)$ be a list of natural numbers with $N \ge 2$ and $e_1 \ne 0$, and
let $\tilde Q$ be a strictly decreasing sequence in $(0, 1)$ such that
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde Q_k$ is a bijection from the periodic Zeckendorf
collection $\tilde E^*$ for $(0, 1)$ determined by $\tilde L$ onto $(0, 1)$. The main result,
`tsum_maxLStarBlock_mul_eq`, is Lemma 16 of Sungkon Chang, *Distribution of Zeckendorf
Expressions*, INTEGERS 25 (2025), Article A25: for every list $L$, the maximal $L^*$-blocks
$\bar\beta_s$ satisfy
$\sum_k (\bar\beta_s)_k \tilde Q_k = \tilde Q_0^{\,s} \sum_k (\bar\beta_0)_k \tilde Q_k$.
The module also holds the definition `lStarCollection` of the collection $E^*$.

The source derives the lemma from $\tilde Q_k = \tilde\omega^k$ (its Theorem 6, quoted from
Sungkon Chang, *The weak converse of Zeckendorf's Theorem*, Research in Number Theory 7 (2021),
Article 48). We prove the part of that theorem needed here directly from the bijection. Indices
start at $0$; put $p_0 = 1$ and $p_{m+1} = \tilde Q_m$. Following Lemmas 38 and 39 and
Proposition 40 of arXiv:2007.12169v3, $\sum_k (\bar\beta_m)_k \tilde Q_k = p_m$ for every $m$,
where $\bar\beta_m$ is the maximal $\tilde L^*$-block starting at index $m$; hence
$p_m = \sum_{k=1}^{N-1} e_k p_{m+k} + (1 + e_N) p_{m+N}$. Instead of Daykin's theorem and
Rouché's theorem used there, an elementary minimum principle shows that the only positive
solution of this recurrence with $p_0 = 1$ is $p_m = \omega^m$, where $\omega > 0$ solves
$\sum_{k=1}^{N-1} e_k \omega^k + (1 + e_N) \omega^N = 1$: the sequence $p_m / \omega^m$ is a
convex combination of its next $N$ terms, with positive weight on the first of them, so it attains
its infimum at $m = 0$ and is constant. Thus $\tilde Q_m = \tilde Q_0^{\,m+1}$, and the lemma
follows by shifting the series.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The periodic collection $E^*$.** For a list $L$ of natural numbers, $E^*$ is the set of
nonzero coefficient functions $\varepsilon : \mathbb{N} \to \mathbb{N}$ that are sums of finitely
or infinitely many disjoint proper $L^*$-blocks, that is, the $\varepsilon \ne 0$ that are
$L^*$-block sums over some set of support intervals. It is the collection $E^*$ for the interval
$(0, 1)$ determined by $L$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def lStarCollection (L : List ℕ) : Set (ℕ → ℕ) :=
  {ε | ε ≠ 0 ∧ ∃ I, IsLStarBlockSum L I ε}

end

section FundamentalSequence

open Finset

/-- The standing hypotheses of Theorem 6 of the source: `Q` is a strictly decreasing sequence in
`(0, 1)` whose evaluation map is a bijection from `lStarCollection L` onto `(0, 1)`. -/
private structure FundHyp (L : List ℕ) (Q : ℕ → ℝ) : Prop where
  two_le : 2 ≤ L.length
  head_ne : L.getD 0 0 ≠ 0
  anti : StrictAnti Q
  pos : ∀ n, 0 < Q n
  lt_one : ∀ n, Q n < 1
  bij : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L) (Set.Ioo 0 1)

variable {L : List ℕ} {Q : ℕ → ℝ}

private theorem mlb_add (s j : ℕ) : maxLStarBlock L s (j + s) = maxLStarBlock L 0 j := by
  rw [maxLStarBlock_of_le (Nat.le_add_left s j), maxLStarBlock_of_le (Nat.zero_le j)]
  simp

private theorem mlb_self (s : ℕ) : maxLStarBlock L s s = L.getD 0 0 := by
  simp [maxLStarBlock_of_le (le_refl s)]

private theorem mlb_add_mul (s k : ℕ) : maxLStarBlock L s (s + L.length * k) = L.getD 0 0 := by
  simp [maxLStarBlock_of_le (Nat.le_add_right s (L.length * k))]

/-- Past index `m + N`, the maximal blocks starting at `m` and at `m + N` agree. -/
private theorem mlb_tail (m i : ℕ) :
    maxLStarBlock L m (i + (m + L.length)) =
      maxLStarBlock L (m + L.length) (i + (m + L.length)) := by
  rw [maxLStarBlock_of_le (show m ≤ i + (m + L.length) by omega),
    maxLStarBlock_of_le (Nat.le_add_left (m + L.length) i)]
  congr 1
  rw [show i + (m + L.length) - m = i + L.length by omega,
    show i + (m + L.length) - (m + L.length) = i by omega, Nat.add_mod_right]

/-- A single proper block with support interval `[s, k]` is a block sum. -/
private theorem isLStarBlockSum_single {ζ : ℕ → ℕ} {s k : ℕ} (hsk : s ≤ k)
    (hmid : ∀ i, s ≤ i → i < k → ζ i = maxLStarBlock L s i) (hk : ζ k < maxLStarBlock L s k)
    (hout : ∀ i, i < s ∨ k < i → ζ i = 0) : IsLStarBlockSum L {(s, k)} ζ := by
  refine ⟨?_, Set.pairwiseDisjoint_singleton _ _, ?_, ?_⟩
  · simpa using hsk
  · simp only [Set.mem_singleton_iff, forall_eq]
    exact ⟨hmid, hk⟩
  · intro i hi
    have := hi (s, k) rfl
    simp only [Set.mem_Icc, not_and_or, not_le] at this
    exact hout i this

/-- A block of length at least two starts with the first entry of `L`. -/
private theorem IsLStarBlockSum.apply_fst {I : Set (ℕ × ℕ)} {ε : ℕ → ℕ}
    (h : IsLStarBlockSum L I ε) {p : ℕ × ℕ} (hp : p ∈ I) (hlt : p.1 < p.2) :
    ε p.1 = L.getD 0 0 := by
  rw [(h.2.2.1 p hp).1 p.1 le_rfl hlt, mlb_self]

private theorem IsLStarBlockSum.eq_of_mem {I : Set (ℕ × ℕ)} {ε : ℕ → ℕ}
    (h : IsLStarBlockSum L I ε) {p q : ℕ × ℕ} (hp : p ∈ I) (hq : q ∈ I) {i : ℕ}
    (hip : i ∈ Set.Icc p.1 p.2) (hiq : i ∈ Set.Icc q.1 q.2) : p = q := by
  by_contra hne
  exact Set.disjoint_left.mp (h.2.1 hp hq hne) hip hiq

/-- No block runs across the start of another block. -/
private theorem IsLStarBlockSum.free_fst {I : Set (ℕ × ℕ)} {ε : ℕ → ℕ}
    (h : IsLStarBlockSum L I ε) {p : ℕ × ℕ} (hp : p ∈ I) :
    ∀ q ∈ I, q.1 < p.1 → q.2 < p.1 := by
  intro q hq hq1
  by_contra hq2
  push Not at hq2
  have := h.eq_of_mem hq hp (i := p.1) ⟨hq1.le, hq2⟩ ⟨le_rfl, h.1 p hp⟩
  rw [this] at hq1
  exact lt_irrefl _ hq1

/-- A block sum supported below `b`, followed by a block sum vanishing below `b`, is a block
sum. -/
private theorem isLStarBlockSum_add (he : L.getD 0 0 ≠ 0) {I J : Set (ℕ × ℕ)} {η θ : ℕ → ℕ}
    {b : ℕ} (hη : IsLStarBlockSum L I η) (hI : ∀ p ∈ I, p.2 < b)
    (hθ : IsLStarBlockSum L J θ) (hθb : ∀ i, i < b → θ i = 0) :
    IsLStarBlockSum L (I ∪ {p ∈ J | b ≤ p.1}) (η + θ) := by
  have hηb : ∀ i, b ≤ i → η i = 0 := fun i hi =>
    hη.2.2.2 i fun p hp hmem => absurd hmem.2 (by have := hI p hp; omega)
  have hJ : ∀ p ∈ J, p.1 < b → p.2 < b := by
    intro p hp h1
    by_contra h2
    push Not at h2
    have := hθ.apply_fst hp (by omega)
    rw [hθb _ h1] at this
    exact he this.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro p (hp | ⟨hp, -⟩)
    exacts [hη.1 p hp, hθ.1 p hp]
  · rintro p (hp | ⟨hp, hpb⟩) q (hq | ⟨hq, hqb⟩) hpq
    · exact hη.2.1 hp hq hpq
    · refine Set.disjoint_left.mpr fun i hi hi' => ?_
      have := hI p hp
      simp only [Set.mem_Icc] at hi hi'
      omega
    · refine Set.disjoint_left.mpr fun i hi hi' => ?_
      have := hI q hq
      simp only [Set.mem_Icc] at hi hi'
      omega
    · exact hθ.2.1 hp hq hpq
  · rintro p (hp | ⟨hp, hpb⟩)
    · obtain ⟨hmid, hend⟩ := hη.2.2.1 p hp
      have hp2 := hI p hp
      refine ⟨fun i hi1 hi2 => ?_, ?_⟩
      · simp [hmid i hi1 hi2, hθb i (by omega)]
      · simpa [hθb p.2 hp2] using hend
    · obtain ⟨hmid, hend⟩ := hθ.2.2.1 p hp
      have hp12 := hθ.1 p hp
      refine ⟨fun i hi1 hi2 => ?_, ?_⟩
      · simp [hmid i hi1 hi2, hηb i (by omega)]
      · simpa [hηb p.2 (by omega)] using hend
  · intro i hi
    simp only [Pi.add_apply]
    by_cases hib : i < b
    · rw [hθb i hib, hη.2.2.2 i (fun p hp => hi p (Or.inl hp)), add_zero]
    · push Not at hib
      rw [hηb i hib, zero_add]
      refine hθ.2.2.2 i fun p hp hmem => ?_
      by_cases hpb : b ≤ p.1
      · exact hi p (Or.inr ⟨hp, hpb⟩) hmem
      · push Not at hpb
        have := hJ p hp hpb
        exact absurd hmem.2 (by omega)

/-- The coefficient function with a single entry `1` at index `j` lies in `E*`. -/
private theorem unit_mem (hL : 1 ≤ L.length) (he : L.getD 0 0 ≠ 0) (j : ℕ) :
    (fun i => if i = j then 1 else 0) ∈ lStarCollection L := by
  classical
  refine ⟨fun h => by simpa using congrFun h j, ?_⟩
  have hex : ∃ r, (if r = 0 then 1 else 0) < L.getD (r % L.length) 0 :=
    ⟨L.length, by simpa [show L.length ≠ 0 by omega] using Nat.pos_of_ne_zero he⟩
  set r := Nat.find hex with hr
  have hrspec : (if r = 0 then 1 else 0) < L.getD (r % L.length) 0 := Nat.find_spec hex
  refine ⟨{(j, j + r)}, isLStarBlockSum_single (by omega) ?_ ?_ ?_⟩
  · intro i hi1 hi2
    have hmin := Nat.find_min hex (show i - j < r by omega)
    push Not at hmin
    rw [maxLStarBlock_of_le hi1]
    refine le_antisymm ?_ ?_
    · by_cases hij : i = j
      · subst hij
        simpa using Nat.one_le_iff_ne_zero.mpr he
      · simp [hij]
    · by_cases hij : i = j
      · subst hij
        simpa using hmin
      · simpa [hij, show i - j ≠ 0 by omega] using hmin
  · rw [maxLStarBlock_of_le (by omega), show j + r - j = r by omega]
    by_cases hr0 : r = 0
    · simpa [hr0] using hrspec
    · simpa [hr0, show j + r ≠ j by omega] using hrspec
  · intro i hi
    simp only [ite_eq_right_iff]
    intro hij
    omega

/-- The fundamental sequence shifted by one index, with `1` in front: `p 0 = 1` and
`p (n + 1) = Q n`. -/
private noncomputable def pSeq (Q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Q n

@[simp] private theorem pSeq_zero : pSeq Q 0 = 1 := rfl

@[simp] private theorem pSeq_succ (n : ℕ) : pSeq Q (n + 1) = Q n := rfl

private theorem FundHyp.pSeq_strictAnti (h : FundHyp L Q) : StrictAnti (pSeq Q) := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  cases n with
  | zero => simpa using h.lt_one 0
  | succ n => simpa using h.anti (Nat.lt_succ_self n)

private theorem FundHyp.pSeq_pos (h : FundHyp L Q) (n : ℕ) : 0 < pSeq Q n := by
  cases n with
  | zero => simp
  | succ n => simpa using h.pos n

private theorem FundHyp.pSeq_le_one (h : FundHyp L Q) (n : ℕ) : pSeq Q n ≤ 1 := by
  simpa using h.pSeq_strictAnti.antitone (Nat.zero_le n)

private theorem FundHyp.len_pos (h : FundHyp L Q) : 1 ≤ L.length := by
  have := h.two_le
  omega

private theorem FundHyp.term_nonneg (h : FundHyp L Q) (ε : ℕ → ℕ) (k : ℕ) :
    0 ≤ (ε k : ℝ) * Q k :=
  mul_nonneg (Nat.cast_nonneg _) (h.pos k).le

/-- The series of a member of `E*` converges, since its sum is not `0`. -/
private theorem FundHyp.summable_of_mem (h : FundHyp L Q) {ε : ℕ → ℕ}
    (hε : ε ∈ lStarCollection L) : Summable fun k => (ε k : ℝ) * Q k := by
  by_contra hns
  have := (h.bij.mapsTo hε).1
  simp only [tsum_eq_zero_of_not_summable hns, lt_irrefl] at this

private theorem FundHyp.term_le_tsum (h : FundHyp L Q) {ε : ℕ → ℕ}
    (hs : Summable fun k => (ε k : ℝ) * Q k) (i : ℕ) :
    (ε i : ℝ) * Q i ≤ ∑' k, (ε k : ℝ) * Q k :=
  hs.le_tsum i fun k _ => h.term_nonneg ε k

private theorem tsum_eq_sum_range_of_le {ε : ℕ → ℕ} {M : ℕ} (hε : ∀ i, M < i → ε i = 0) :
    ∑' k, (ε k : ℝ) * Q k = ∑ k ∈ range (M + 1), (ε k : ℝ) * Q k :=
  tsum_eq_sum fun k hk => by
    simp only [mem_range, not_lt] at hk
    simp [hε k (by omega)]

private theorem summable_of_le {ε : ℕ → ℕ} {M : ℕ} (hε : ∀ i, M < i → ε i = 0) :
    Summable fun k => (ε k : ℝ) * Q k :=
  summable_of_ne_finset_zero (s := range (M + 1)) fun k hk => by
    simp only [mem_range, not_lt] at hk
    simp [hε k (by omega)]

private theorem sum_range_mlb_eq_sum_Ico (s n : ℕ) (hsn : s ≤ n) :
    ∑ k ∈ range n, (maxLStarBlock L s k : ℝ) * Q k =
      ∑ k ∈ Ico s n, (maxLStarBlock L s k : ℝ) * Q k := by
  rw [← sum_range_add_sum_Ico _ hsn, sum_eq_zero (fun k hk => ?_), zero_add]
  simp [maxLStarBlock_of_lt (mem_range.mp hk)]

/-- **Partial sums of a maximal block** (Chang 2021, Lemma 38 of arXiv:2007.12169v3). Every
partial sum of $\sum_k (\bar\beta_m)_k Q_k$ is at most $p_m$. For `m = 0` the truncations of
$\bar\beta_0$ lie in `E*`, so their values are below `1`. For `m ≥ 1`, a partial sum above
`Q (m - 1)` yields a proper block `ζ` at index `m` with
`∑ ζ Q ≤ Q (m - 1) < ∑ ζ Q + Q M`; completing `ζ` by the expansion of the difference gives a
second member of `E*` with value `Q (m - 1)`, besides the unit at `m - 1`. -/
private theorem FundHyp.sum_range_mlb_le (h : FundHyp L Q) (m n : ℕ) :
    ∑ k ∈ range n, (maxLStarBlock L m k : ℝ) * Q k ≤ pSeq Q m := by
  classical
  have he := h.head_ne
  have hN := h.len_pos
  cases m with
  | zero =>
    set M := L.length * (n + 1) with hM
    have hnM : n ≤ M := by nlinarith
    set τ : ℕ → ℕ := fun i => if i < M then maxLStarBlock L 0 i else
      if i = M then L.getD 0 0 - 1 else 0 with hτ
    have hτM : maxLStarBlock L 0 M = L.getD 0 0 := by
      simpa using mlb_add_mul (L := L) 0 (n + 1)
    have hτmem : τ ∈ lStarCollection L := by
      refine ⟨fun h0 => ?_, {(0, M)}, isLStarBlockSum_single (Nat.zero_le _) ?_ ?_ ?_⟩
      · have := congrFun h0 0
        simp only [hτ, show 0 < M by positivity, ite_true, Pi.zero_apply, mlb_self] at this
        exact he this
      · intro i _ hi
        simp [hτ, hi]
      · simp only [hτ, lt_irrefl, ite_false, ite_true, hτM]
        omega
      · intro i hi
        rcases hi with hi | hi
        · omega
        · simp [hτ, show ¬ i < M by omega, show i ≠ M by omega]
    have hlt := (h.bij.mapsTo hτmem).2
    rw [tsum_eq_sum_range_of_le (M := M) (fun i hi => by
      simp [hτ, show ¬ i < M by omega, show i ≠ M by omega])] at hlt
    rw [pSeq_zero]
    refine le_trans ?_ hlt.le
    calc ∑ k ∈ range n, (maxLStarBlock L 0 k : ℝ) * Q k
        ≤ ∑ k ∈ range M, (maxLStarBlock L 0 k : ℝ) * Q k :=
          sum_le_sum_of_subset_of_nonneg (range_mono hnM) fun k _ _ =>
            h.term_nonneg (maxLStarBlock L 0) k
      _ = ∑ k ∈ range M, (τ k : ℝ) * Q k :=
          sum_congr rfl fun k hk => by simp [hτ, mem_range.mp hk]
      _ ≤ ∑ k ∈ range (M + 1), (τ k : ℝ) * Q k := by
          rw [sum_range_succ]
          linarith [h.term_nonneg τ M]
  | succ m =>
    rw [pSeq_succ]
    by_contra hcon
    push Not at hcon
    have hex : ∃ n, Q m < ∑ k ∈ range n, (maxLStarBlock L (m + 1) k : ℝ) * Q k := ⟨n, hcon⟩
    set n₀ := Nat.find hex with hn₀
    have hspec : Q m < ∑ k ∈ range n₀, (maxLStarBlock L (m + 1) k : ℝ) * Q k :=
      Nat.find_spec hex
    have hn₀0 : n₀ ≠ 0 := by
      intro h0
      rw [h0] at hspec
      simp only [range_zero, sum_empty] at hspec
      linarith [h.pos m]
    obtain ⟨M, hM⟩ : ∃ M, n₀ = M + 1 := ⟨n₀ - 1, by omega⟩
    have hSM : ∑ k ∈ range M, (maxLStarBlock L (m + 1) k : ℝ) * Q k ≤ Q m := by
      have := Nat.find_min hex (show M < n₀ by omega)
      push Not at this
      exact this
    rw [hM, sum_range_succ] at hspec
    set S := ∑ k ∈ range M, (maxLStarBlock L (m + 1) k : ℝ) * Q k with hS
    have hmM : m + 1 ≤ M := by
      by_contra hlt
      push Not at hlt
      have h0 : S = 0 := sum_eq_zero fun k hk => by
        simp [maxLStarBlock_of_lt (show k < m + 1 by have := mem_range.mp hk; omega)]
      rw [h0, maxLStarBlock_of_lt hlt] at hspec
      simp at hspec
      linarith [h.pos m]
    have hQM := h.pos M
    set x := (Q m - S) / Q M with hx
    have hx0 : 0 ≤ x := div_nonneg (by linarith) hQM.le
    set c := ⌊x⌋₊ with hc
    have hc_le : (c : ℝ) * Q M ≤ Q m - S := by
      have := Nat.floor_le hx0
      rw [← hc] at this
      rwa [hx, le_div_iff₀ hQM] at this
    have hc_lt : Q m - S < ((c : ℝ) + 1) * Q M := by
      have := Nat.lt_floor_add_one x
      rw [← hc, hx, div_lt_iff₀ hQM] at this
      exact this
    have hcβ : c < maxLStarBlock L (m + 1) M := by
      rw [hc, Nat.floor_lt hx0, hx, div_lt_iff₀ hQM]
      linarith
    set ζ : ℕ → ℕ := fun i => if i < M then maxLStarBlock L (m + 1) i else
      if i = M then c else 0 with hζ
    have hζblock : IsLStarBlockSum L {(m + 1, M)} ζ := by
      refine isLStarBlockSum_single hmM (fun i _ hi => by simp [hζ, hi]) ?_ (fun i hi => ?_)
      · simpa [hζ] using hcβ
      · rcases hi with hi | hi
        · simp [hζ, show i < M by omega, maxLStarBlock_of_lt hi]
        · simp [hζ, show ¬ i < M by omega, show i ≠ M by omega]
    have hζout : ∀ i, M < i → ζ i = 0 := fun i hi => by
      simp [hζ, show ¬ i < M by omega, show i ≠ M by omega]
    have hζval : ∑' k, (ζ k : ℝ) * Q k = S + c * Q M := by
      rw [tsum_eq_sum_range_of_le hζout, sum_range_succ, hS]
      congr 1
      · exact sum_congr rfl fun k hk => by simp [hζ, mem_range.mp hk]
      · simp [hζ]
    have hζm : ζ m = 0 := by
      simp [hζ, show m < M by omega, maxLStarBlock_of_lt (show m < m + 1 by omega)]
    -- a member of `E*` vanishing at `m` with value `Q m`
    have key : ∃ η ∈ lStarCollection L, η m = 0 ∧ ∑' k, (η k : ℝ) * Q k = Q m := by
      rcases eq_or_lt_of_le (show S + c * Q M ≤ Q m by linarith) with heq | hlt
      · refine ⟨ζ, ⟨fun h0 => ?_, _, hζblock⟩, hζm, by rw [hζval, heq]⟩
        rw [h0] at hζval
        simp only [Pi.zero_apply, Nat.cast_zero, zero_mul, tsum_zero] at hζval
        linarith [h.pos m]
      · set y := Q m - (S + c * Q M) with hy
        have hy01 : y ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨by linarith, by linarith [h.lt_one M]⟩
        obtain ⟨δ, hδ, hδy⟩ := h.bij.surjOn hy01
        simp only at hδy
        have hδs := h.summable_of_mem hδ
        have hδzero : ∀ i, i < M + 1 → δ i = 0 := by
          intro i hi
          by_contra hne
          have h1 := h.term_le_tsum hδs i
          have h2 : Q M ≤ Q i := h.anti.antitone (by omega)
          have h3 : (1 : ℝ) ≤ δ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          nlinarith [h.pos i]
        obtain ⟨hδ0, J, hδJ⟩ := hδ
        refine ⟨ζ + δ, ⟨fun h0 => hδ0 ?_, _,
          isLStarBlockSum_add he hζblock (by simp) hδJ hδzero⟩, ?_, ?_⟩
        · funext i
          have := congrFun h0 i
          simp only [Pi.add_apply, Pi.zero_apply, Nat.add_eq_zero_iff] at this
          exact this.2
        · simp [hζm, hδzero m (by omega)]
        · simp only [Pi.add_apply, Nat.cast_add, add_mul]
          rw [(summable_of_le hζout).tsum_add hδs, hζval, hδy, hy]
          ring
    obtain ⟨η, hη, hηm, hηval⟩ := key
    have hunit := unit_mem hN he m
    have hunitval : ∑' k, ((if k = m then 1 else 0 : ℕ) : ℝ) * Q k = Q m := by
      rw [tsum_eq_single m fun k hk => by simp [hk]]
      simp
    have := h.bij.injOn hη hunit (hηval.trans hunitval.symm)
    have := congrFun this m
    simp [hηm] at this

/-- **Partial sums of a block sum** (Chang 2021, Lemma 39 of arXiv:2007.12169v3). Let `ε` be a
block sum and `b` an index that no block runs across. Every partial sum of
$\sum_{k \ge b} \varepsilon_k Q_k$ is at most $p_b$. At every index `n ≥ b` that no block runs
across, the partial sum up to `n` plus $p_n$ is at most $p_b$, by a telescoping induction over
the blocks. -/
private theorem FundHyp.sum_Ico_le (h : FundHyp L Q) {I : Set (ℕ × ℕ)} {ε : ℕ → ℕ}
    (hε : IsLStarBlockSum L I ε) {b : ℕ} (hb : ∀ p ∈ I, p.1 < b → p.2 < b) (n : ℕ) :
    ∑ k ∈ Ico b n, (ε k : ℝ) * Q k ≤ pSeq Q b := by
  have step : ∀ n, b ≤ n → (∀ p ∈ I, p.1 < n → p.2 < n) →
      ∑ k ∈ Ico b n, (ε k : ℝ) * Q k + pSeq Q n ≤ pSeq Q b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hbn hfree
      rcases eq_or_lt_of_le hbn with rfl | hlt
      · simp
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      by_cases hcov : ∃ p ∈ I, p.1 ≤ n' ∧ n' ≤ p.2
      · obtain ⟨p, hp, h1, h2⟩ := hcov
        have hp2 : p.2 = n' := by
          have := hfree p hp (by omega)
          omega
        have hbp : b ≤ p.1 := by
          by_contra hlt'
          push Not at hlt'
          have := hb p hp hlt'
          omega
        have ih' := ih p.1 (by omega) hbp (hε.free_fst hp)
        obtain ⟨hmid, hend⟩ := hε.2.2.1 p hp
        rw [hp2] at hmid hend
        have hblock : ∑ k ∈ Ico p.1 (n' + 1), (ε k : ℝ) * Q k ≤
            ∑ k ∈ range (n' + 1), (maxLStarBlock L p.1 k : ℝ) * Q k - Q n' := by
          rw [sum_range_mlb_eq_sum_Ico _ _ (by omega), sum_Ico_succ_top h1, sum_Ico_succ_top h1]
          have hsum : ∑ k ∈ Ico p.1 n', (ε k : ℝ) * Q k =
              ∑ k ∈ Ico p.1 n', (maxLStarBlock L p.1 k : ℝ) * Q k :=
            sum_congr rfl fun k hk => by
              rw [mem_Ico] at hk
              rw [hmid k hk.1 hk.2]
          have hlast : (ε n' : ℝ) + 1 ≤ maxLStarBlock L p.1 n' := by exact_mod_cast hend
          rw [hsum]
          nlinarith [h.pos n']
        have hL1 := h.sum_range_mlb_le p.1 (n' + 1)
        rw [← sum_Ico_consecutive _ hbp (by omega : p.1 ≤ n' + 1), pSeq_succ]
        linarith
      · push Not at hcov
        have hεn' : ε n' = 0 := hε.2.2.2 n' fun p hp hmem => by
          have := hcov p hp hmem.1
          exact absurd hmem.2 (by omega)
        have hfree' : ∀ p ∈ I, p.1 < n' → p.2 < n' := fun p hp h1 => by
          by_contra h2
          push Not at h2
          have := hcov p hp h1.le
          omega
        have ih' := ih n' (by omega) (by omega) hfree'
        rw [sum_Ico_succ_top (by omega), hεn']
        have := h.pSeq_strictAnti.antitone (Nat.le_succ n')
        simp only [Nat.cast_zero, zero_mul, add_zero]
        linarith
  by_cases hnb : n ≤ b
  · rw [Ico_eq_empty_of_le hnb, sum_empty]
    exact (h.pSeq_pos b).le
  push Not at hnb
  by_cases hfree : ∀ p ∈ I, p.1 < n → p.2 < n
  · have := step n hnb.le hfree
    linarith [h.pSeq_pos n]
  · push Not at hfree
    obtain ⟨p, hp, h1, h2⟩ := hfree
    have hbp : b ≤ p.1 := by
      by_contra hlt'
      push Not at hlt'
      have := hb p hp hlt'
      omega
    have hstep := step p.1 hbp (hε.free_fst hp)
    obtain ⟨hmid, -⟩ := hε.2.2.1 p hp
    have hsum : ∑ k ∈ Ico p.1 n, (ε k : ℝ) * Q k =
        ∑ k ∈ range n, (maxLStarBlock L p.1 k : ℝ) * Q k := by
      rw [sum_range_mlb_eq_sum_Ico _ _ h1.le]
      exact sum_congr rfl fun k hk => by
        rw [mem_Ico] at hk
        rw [hmid k hk.1 (by omega)]
    have hL1 := h.sum_range_mlb_le p.1 n
    rw [← sum_Ico_consecutive _ hbp h1.le, hsum]
    linarith

private theorem FundHyp.summable_mlb (h : FundHyp L Q) (m : ℕ) :
    Summable fun k => (maxLStarBlock L m k : ℝ) * Q k :=
  summable_of_sum_range_le (h.term_nonneg _) (h.sum_range_mlb_le m)

/-- The tail of a maximal block after any index is positive. -/
private theorem FundHyp.tail_pos (h : FundHyp L Q) (m a : ℕ) :
    0 < ∑' i, (maxLStarBlock L m (i + a) : ℝ) * Q (i + a) := by
  have hs : Summable fun i => (maxLStarBlock L m (i + a) : ℝ) * Q (i + a) :=
    (summable_nat_add_iff a).mpr (h.summable_mlb m)
  have hN := h.len_pos
  have hi₀ : m + L.length * (a + 1) - a + a = m + L.length * (a + 1) := by
    have : a + 1 ≤ L.length * (a + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  refine hs.tsum_pos (fun i => h.term_nonneg (maxLStarBlock L m) (i + a))
    (m + L.length * (a + 1) - a) ?_
  rw [hi₀, mlb_add_mul]
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero h.head_ne) (h.pos _)

private theorem FundHyp.tsum_mlb_split (h : FundHyp L Q) (m a : ℕ) :
    ∑' k, (maxLStarBlock L m k : ℝ) * Q k = ∑ k ∈ range a, (maxLStarBlock L m k : ℝ) * Q k +
      ∑' i, (maxLStarBlock L m (i + a) : ℝ) * Q (i + a) :=
  ((h.summable_mlb m).sum_add_tsum_nat_add a).symm

/-- **The long recursion** (Chang 2021, Proposition 40 of arXiv:2007.12169v3):
$\sum_k (\bar\beta_m)_k Q_k = p_m$. If the sum were smaller, it would be the value of some
`ε ∈ E*`; comparing values shows that `ε` starts with a proper block at index `m`, and the
partial-sum bounds then give `∑ ε Q < ∑ β̄_m Q`. -/
private theorem FundHyp.tsum_mlb (h : FundHyp L Q) (m : ℕ) :
    ∑' k, (maxLStarBlock L m k : ℝ) * Q k = pSeq Q m := by
  classical
  have he := h.head_ne
  have hle : ∑' k, (maxLStarBlock L m k : ℝ) * Q k ≤ pSeq Q m :=
    Real.tsum_le_of_sum_range_le (h.term_nonneg _) (h.sum_range_mlb_le m)
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  set y := ∑' k, (maxLStarBlock L m k : ℝ) * Q k with hy
  have hQy : Q m < y := by
    rw [hy, h.tsum_mlb_split m (m + 1), sum_range_succ, mlb_self]
    have h1 : (1 : ℝ) ≤ L.getD 0 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    have h2 : 0 ≤ ∑ k ∈ range m, (maxLStarBlock L m k : ℝ) * Q k :=
      sum_nonneg fun k _ => h.term_nonneg _ k
    have h3 := h.tail_pos m (m + 1)
    nlinarith [h.pos m]
  have hy01 : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [h.pos m], by linarith [h.pSeq_le_one m]⟩
  obtain ⟨ε, hε, hεy⟩ := h.bij.surjOn hy01
  have hεs := h.summable_of_mem hε
  obtain ⟨hε0, I, hεI⟩ := hε
  have hex : ∃ i, ε i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hε0 (funext hall)
  set m₁ := Nat.find hex with hm₁
  have hm₁ne : ε m₁ ≠ 0 := Nat.find_spec hex
  have hbelow : ∀ i, i < m₁ → ε i = 0 := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this
  have hfree₁ : ∀ p ∈ I, p.1 < m₁ → p.2 < m₁ := by
    intro p hp h1
    by_contra h2
    push Not at h2
    have := hεI.apply_fst hp (by omega)
    rw [hbelow _ h1] at this
    exact he this.symm
  have hy_le : y ≤ pSeq Q m₁ := by
    rw [← hεy]
    refine Real.tsum_le_of_sum_range_le (h.term_nonneg ε) fun n => ?_
    have := h.sum_Ico_le hεI hfree₁ n
    by_cases hn : m₁ ≤ n
    · rwa [← sum_range_add_sum_Ico _ hn,
        sum_eq_zero (fun k hk => by simp [hbelow k (mem_range.mp hk)]), zero_add]
    · push Not at hn
      rw [sum_eq_zero (fun k hk => by simp [hbelow k (by have := mem_range.mp hk; omega)])]
      exact (h.pSeq_pos _).le
  have hQ₁ : Q m₁ ≤ y := by
    rw [← hεy]
    have h1 := h.term_le_tsum hεs m₁
    have h2 : (1 : ℝ) ≤ ε m₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm₁ne
    nlinarith [h.pos m₁]
  have hm₁m : m₁ = m := by
    have hA : pSeq Q (m₁ + 1) < pSeq Q m := by rw [pSeq_succ]; linarith
    have hB : pSeq Q (m + 1) < pSeq Q m₁ := by rw [pSeq_succ]; linarith
    have hA' := h.pSeq_strictAnti.lt_iff_gt.mp hA
    have hB' := h.pSeq_strictAnti.lt_iff_gt.mp hB
    omega
  have hmne : ε m ≠ 0 := hm₁m ▸ hm₁ne
  have hbelow' : ∀ i, i < m → ε i = 0 := fun i hi => hbelow i (by omega)
  obtain ⟨p, hp, hpm⟩ : ∃ p ∈ I, m ∈ Set.Icc p.1 p.2 := by
    by_contra hnone
    push Not at hnone
    exact hmne (hεI.2.2.2 m hnone)
  have hp1 : p.1 = m := by
    by_contra hne
    have hlt : p.1 < m := lt_of_le_of_ne hpm.1 hne
    have := hεI.apply_fst hp (by have := hpm.2; omega)
    rw [hbelow' _ hlt] at this
    exact he this.symm
  obtain ⟨hmid, hend⟩ := hεI.2.2.1 p hp
  rw [hp1] at hmid hend
  have hma : m ≤ p.2 := hpm.2
  have hfreea : ∀ q ∈ I, q.1 < p.2 + 1 → q.2 < p.2 + 1 := by
    intro q hq h1
    by_contra h2
    push Not at h2
    have := hεI.eq_of_mem hq hp (i := p.2) ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩
    rw [this] at h2
    omega
  set a := p.2 with ha
  set T := ∑ k ∈ range (a + 1), (maxLStarBlock L m k : ℝ) * Q k with hT
  have hhead : ∑ k ∈ range (a + 1), (ε k : ℝ) * Q k ≤ T - Q a := by
    rw [hT, sum_range_succ, sum_range_succ]
    have hsum : ∑ k ∈ range a, (ε k : ℝ) * Q k =
        ∑ k ∈ range a, (maxLStarBlock L m k : ℝ) * Q k :=
      sum_congr rfl fun k hk => by
        have hk' := mem_range.mp hk
        by_cases hkm : k < m
        · rw [hbelow' k hkm, maxLStarBlock_of_lt hkm]
        · rw [hmid k (by omega) hk']
    have hlast : (ε a : ℝ) + 1 ≤ maxLStarBlock L m a := by exact_mod_cast hend
    rw [hsum]
    nlinarith [h.pos a]
  have hεle : y ≤ T := by
    rw [← hεy]
    refine Real.tsum_le_of_sum_range_le (h.term_nonneg ε) fun n => ?_
    by_cases hn : a + 1 ≤ n
    · rw [← sum_range_add_sum_Ico _ hn]
      have := h.sum_Ico_le hεI hfreea n
      rw [pSeq_succ] at this
      linarith
    · push Not at hn
      have : ∑ k ∈ range n, (ε k : ℝ) * Q k ≤ ∑ k ∈ range (a + 1), (ε k : ℝ) * Q k :=
        sum_le_sum_of_subset_of_nonneg (range_mono hn.le) fun k _ _ => h.term_nonneg ε k
      linarith [h.pos a]
  have hTy : T < y := by
    rw [hy, h.tsum_mlb_split m (a + 1)]
    linarith [h.tail_pos m (a + 1)]
  linarith

/-- **The short recursion** `p m = ∑_{k < N} L[k] * p (m + k + 1) + p (m + N)`, obtained from the
long recursion at `m` and `m + N` as in the proof of Lemma 41 of arXiv:2007.12169v3 (whose list
convention adds `1` to the last entry). -/
private theorem FundHyp.pSeq_rec (h : FundHyp L Q) (m : ℕ) :
    pSeq Q m = ∑ k ∈ range L.length, (L.getD k 0 : ℝ) * pSeq Q (m + k + 1) +
      pSeq Q (m + L.length) := by
  rw [← h.tsum_mlb m, ← h.tsum_mlb (m + L.length), h.tsum_mlb_split m (m + L.length),
    h.tsum_mlb_split (m + L.length) (m + L.length)]
  have hzero : ∑ k ∈ range (m + L.length), (maxLStarBlock L (m + L.length) k : ℝ) * Q k = 0 :=
    sum_eq_zero fun k hk => by simp [maxLStarBlock_of_lt (mem_range.mp hk)]
  have htail : ∑' i, (maxLStarBlock L m (i + (m + L.length)) : ℝ) * Q (i + (m + L.length)) =
      ∑' i, (maxLStarBlock L (m + L.length) (i + (m + L.length)) : ℝ) *
        Q (i + (m + L.length)) :=
    tsum_congr fun i => by rw [mlb_tail]
  have hhead : ∑ k ∈ range (m + L.length), (maxLStarBlock L m k : ℝ) * Q k =
      ∑ k ∈ range L.length, (L.getD k 0 : ℝ) * pSeq Q (m + k + 1) := by
    rw [sum_range_add, sum_eq_zero (fun k hk => by simp [maxLStarBlock_of_lt (mem_range.mp hk)]),
      zero_add]
    refine sum_congr rfl fun k hk => ?_
    rw [pSeq_succ, maxLStarBlock_of_le (by omega), show m + k - m = k by omega,
      Nat.mod_eq_of_lt (mem_range.mp hk)]
  rw [hzero, zero_add, htail, hhead]

/-- **Positive solutions of a convex recurrence are geometric.** Let `c k ≥ 0` with `c 0 > 0`,
let `ω > 0` satisfy `∑_{k < N} c k * ω ^ (k + 1) = 1`, and let `p` be a positive sequence with
`p 0 = 1` and `p n = ∑_{k < N} c k * p (n + k + 1)`. Then `p n = ω ^ n`. The sequence
`u n = p n / ω ^ n` is a convex combination of its next `N` terms; for `v = u - inf u` this gives
`v 0 ≤ v (n + k)` for some `k < N` and `(c 0 * ω) ^ k * v (n + k) ≤ v n`, so `v 0 = 0`, and then
`v = 0`. -/
private theorem eq_pow_of_rec {N : ℕ} (hN : 0 < N) (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hc0 : 0 < c 0) {p : ℕ → ℝ} (hp : ∀ n, 0 < p n) (hp0 : p 0 = 1)
    (hrec : ∀ n, p n = ∑ k ∈ range N, c k * p (n + k + 1))
    {ω : ℝ} (hω : 0 < ω) (hroot : ∑ k ∈ range N, c k * ω ^ (k + 1) = 1) :
    ∀ n, p n = ω ^ n := by
  set u : ℕ → ℝ := fun n => p n / ω ^ n with hu
  set w : ℕ → ℝ := fun k => c k * ω ^ (k + 1) with hw
  have hupos : ∀ n, 0 < u n := fun n => div_pos (hp n) (pow_pos hω n)
  have hw0 : 0 < w 0 := mul_pos hc0 (pow_pos hω 1)
  have hwnn : ∀ k, 0 ≤ w k := fun k => mul_nonneg (hc k) (pow_pos hω _).le
  have hwsum : ∑ k ∈ range N, w k = 1 := hroot
  have hurec : ∀ n, u n = ∑ k ∈ range N, w k * u (n + k + 1) := by
    intro n
    simp only [hu, hw]
    rw [hrec n, sum_div]
    refine sum_congr rfl fun k _ => ?_
    have hω' : ω ^ n ≠ 0 := (pow_pos hω n).ne'
    have hω'' : ω ^ (n + k + 1) ≠ 0 := (pow_pos hω _).ne'
    field_simp
    ring
  set t := ⨅ n, u n with ht
  have hbdd : BddBelow (Set.range u) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hupos n).le⟩
  have htle : ∀ n, t ≤ u n := fun n => ciInf_le hbdd n
  set v : ℕ → ℝ := fun n => u n - t with hv
  have hvnn : ∀ n, 0 ≤ v n := fun n => sub_nonneg.mpr (htle n)
  have hvrec : ∀ n, v n = ∑ k ∈ range N, w k * v (n + k + 1) := by
    intro n
    simp only [hv, mul_sub, sum_sub_distrib, ← sum_mul, hwsum, one_mul]
    rw [← hurec n]
  have hw0le : w 0 ≤ 1 := by
    rw [← hwsum]
    exact single_le_sum (fun k _ => hwnn k) (mem_range.mpr hN)
  have hA : ∀ n, w 0 * v (n + 1) ≤ v n := by
    intro n
    rw [hvrec n]
    have := single_le_sum (f := fun k => w k * v (n + k + 1))
      (fun k _ => mul_nonneg (hwnn k) (hvnn _)) (mem_range.mpr hN)
    simpa using this
  have hB : ∀ n, ∃ k < N, v 0 ≤ v (n + k) := by
    intro n
    induction n with
    | zero => exact ⟨0, hN, by simp⟩
    | succ n ih =>
      obtain ⟨k, hk, hvk⟩ := ih
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · by_contra hall
        push Not at hall
        have hlt : ∑ j ∈ range N, w j * v (n + j + 1) < ∑ j ∈ range N, w j * v n := by
          refine sum_lt_sum (fun j hj => ?_) ⟨0, mem_range.mpr hN, ?_⟩
          · have h1 := hall j (mem_range.mp hj)
            rw [show n + 1 + j = n + j + 1 by omega] at h1
            exact mul_le_mul_of_nonneg_left (by simp at hvk; linarith) (hwnn j)
          · have h1 := hall 0 hN
            simp only [add_zero] at h1 hvk
            simp only [add_zero]
            exact mul_lt_mul_of_pos_left (by linarith) hw0
        rw [← sum_mul, hwsum, one_mul, ← hvrec n] at hlt
        exact lt_irrefl _ hlt
      · exact ⟨k - 1, by omega, by rwa [show n + 1 + (k - 1) = n + k by omega]⟩
  have hC : ∀ n k, w 0 ^ k * v (n + k) ≤ v n := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      calc w 0 ^ (k + 1) * v (n + (k + 1)) = w 0 ^ k * (w 0 * v (n + k + 1)) := by ring_nf
        _ ≤ w 0 ^ k * v (n + k) := mul_le_mul_of_nonneg_left (hA (n + k)) (pow_nonneg hw0.le k)
        _ ≤ v n := ih
  have hD : ∀ n, w 0 ^ (N - 1) * v 0 ≤ v n := by
    intro n
    obtain ⟨k, hk, hvk⟩ := hB n
    calc w 0 ^ (N - 1) * v 0 ≤ w 0 ^ (N - 1) * v (n + k) :=
          mul_le_mul_of_nonneg_left hvk (pow_nonneg hw0.le _)
      _ ≤ w 0 ^ k * v (n + k) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hw0.le hw0le (by omega)) (hvnn _)
      _ ≤ v n := hC n k
  have hv0 : v 0 = 0 := by
    have hle : t + w 0 ^ (N - 1) * v 0 ≤ t := le_ciInf fun n => by
      have := hD n
      simp only [hv] at this
      linarith
    have hpos : 0 < w 0 ^ (N - 1) := pow_pos hw0 _
    have := hvnn 0
    nlinarith
  have hvall : ∀ n, v n = 0 := by
    intro n
    induction n with
    | zero => exact hv0
    | succ n ih =>
      have h1 := hA n
      rw [ih] at h1
      have h2 := hvnn (n + 1)
      nlinarith
  intro n
  have h1 : u n = u 0 := by
    have := hvall n
    have := hvall 0
    simp only [hv] at *
    linarith
  have h2 : u 0 = 1 := by simp [hu, hp0]
  have h3 : p n / ω ^ n = 1 := by
    rw [← h2, ← h1]
  rwa [div_eq_one_iff_eq (pow_pos hω n).ne'] at h3

/-- A polynomial with no constant term and coefficient sum at least `1` takes the value `1` at a
positive point. -/
private theorem exists_root (N : ℕ) (c : ℕ → ℝ) (h1 : 1 ≤ ∑ k ∈ range N, c k) :
    ∃ ω, 0 < ω ∧ ∑ k ∈ range N, c k * ω ^ (k + 1) = 1 := by
  set g : ℝ → ℝ := fun x => ∑ k ∈ range N, c k * x ^ (k + 1) with hgdef
  have hg : ContinuousOn g (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    simp only [hgdef]
    fun_prop
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hg1 : g 1 = ∑ k ∈ range N, c k := by simp [hgdef]
  obtain ⟨ω, hω, hgω⟩ := intermediate_value_Icc zero_le_one hg
    (show (1 : ℝ) ∈ Set.Icc (g 0) (g 1) from ⟨by rw [hg0]; norm_num, by rw [hg1]; exact h1⟩)
  refine ⟨ω, lt_of_le_of_ne hω.1 ?_, hgω⟩
  rintro rfl
  rw [hg0] at hgω
  norm_num at hgω

/-- **The fundamental sequence is geometric** (the part of Theorem 6 of the source used here):
`Q n = Q 0 ^ (n + 1)`. -/
private theorem FundHyp.eq_pow (h : FundHyp L Q) : ∀ n, Q n = Q 0 ^ (n + 1) := by
  have hN := h.len_pos
  set c : ℕ → ℝ := fun k => (L.getD k 0 : ℝ) + if k = L.length - 1 then 1 else 0 with hc
  have hcnn : ∀ k, 0 ≤ c k := fun k =>
    add_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num)
  have hc0 : 0 < c 0 :=
    add_pos_of_pos_of_nonneg (by exact_mod_cast Nat.pos_of_ne_zero h.head_ne)
      (by split_ifs <;> norm_num)
  have hcsum : ∑ k ∈ range L.length, c k = ∑ k ∈ range L.length, (L.getD k 0 : ℝ) + 1 := by
    simp only [hc, sum_add_distrib, sum_ite_eq', mem_range]
    simp [show L.length - 1 < L.length by omega]
  have h1 : 1 ≤ ∑ k ∈ range L.length, c k := by
    rw [hcsum]
    linarith [sum_nonneg fun k (_ : k ∈ range L.length) =>
      (Nat.cast_nonneg (L.getD k 0) : (0 : ℝ) ≤ _)]
  obtain ⟨ω, hω, hroot⟩ := exists_root L.length c h1
  have hrec : ∀ n, pSeq Q n = ∑ k ∈ range L.length, c k * pSeq Q (n + k + 1) := by
    intro n
    rw [h.pSeq_rec n]
    simp only [hc, add_mul, sum_add_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range,
      show L.length - 1 < L.length by omega, ite_true]
    rw [show n + (L.length - 1) + 1 = n + L.length by omega]
  have hp := eq_pow_of_rec (by omega) c hcnn hc0 h.pSeq_pos pSeq_zero hrec hω hroot
  have hQ : ∀ n, Q n = ω ^ (n + 1) := fun n => by simpa using hp (n + 1)
  intro n
  rw [hQ n, hQ 0, zero_add, pow_one]

end FundamentalSequence

-- `hL` and `he` are hypotheses of the source's statement that the proof does not need: the
-- identity holds for every list `L` once `Q'` is geometric.
set_option linter.unusedVariables false in
/-- **Shifted maximal blocks scale geometrically.** Let $L = (e_1, \dots, e_N)$ and $\tilde L$ be
lists of natural numbers of length at least $2$ with nonzero first entries, and let $\tilde Q$ be
a strictly decreasing sequence with values in $(0, 1)$ such that
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde Q_k$ is a bijection from $\tilde E^*$, the
periodic Zeckendorf collection for $(0, 1)$ determined by $\tilde L$, onto $(0, 1)$. For
$s \in \mathbb{N}$ let $\bar\beta_s$ be the maximal $L^*$-block starting at index $s$: it is $0$
at indices $i < s$ and $e_j$ at indices $i \ge s$ with $j - 1 \equiv i - s \pmod N$. Then
$\sum_k (\bar\beta_s)_k \tilde Q_k = \tilde Q_0^{\,s} \sum_k (\bar\beta_0)_k \tilde Q_k$ for every
$s \in \mathbb{N}$.

Indices are zero-based: $\bar\beta_s$ is the paper's $\bar\beta^{s+1}$ and $\tilde Q_0$ is its
$\tilde Q_1 = \tilde\omega$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 16 (`integers-2025-A25-lem-16`; arXiv:2308.12872v1, Section 4.1). -/
public theorem tsum_maxLStarBlock_mul_eq (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0) {Q' : ℕ → ℝ}
    (hQ' : StrictAnti Q') (hQ'01 : ∀ n, 0 < Q' n ∧ Q' n < 1)
    (hbij' : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q' k) (lStarCollection L')
      (Set.Ioo 0 1)) (s : ℕ) :
    ∑' k, (maxLStarBlock L s k : ℝ) * Q' k = Q' 0 ^ s * ∑' k, (maxLStarBlock L 0 k : ℝ) * Q' k := by
  have h : FundHyp L' Q' :=
    ⟨hL', he', hQ', fun n => (hQ'01 n).1, fun n => (hQ'01 n).2, hbij'⟩
  have hgeom := h.eq_pow
  have hsupp : Function.support (fun k => (maxLStarBlock L s k : ℝ) * Q' k) ⊆
      Set.range (· + s) := by
    intro k hk
    by_contra hnot
    have hks : k < s := by
      by_contra hks
      push Not at hks
      exact hnot ⟨k - s, by simp only; omega⟩
    exact hk (by simp [maxLStarBlock_of_lt hks])
  rw [← (add_left_injective s).tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [mlb_add, hgeom (j + s), hgeom j]
  ring

end MetaMathlibExt
