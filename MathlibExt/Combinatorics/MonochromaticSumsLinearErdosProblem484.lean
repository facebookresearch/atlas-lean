/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Many monochromatic sums in colourings of `{1, …, N}` (Erdős Problem 484)

Erdős Problem 484 (Roth) asks whether there is an absolute `c > 0` such that for every
`k`-colouring of `{1, …, N}` (`N` large in terms of `k`) at least `c N` integers of `{1, …, N}`
are sums `a + b` with `a ≠ b` in `{1, …, N}` of the same colour. The main result,
`monochromaticSumsLinearCount_holds`, answers it positively with `c = 1 / 4`.

## Proof outline

Fix `k`, let `N` be large, `M = N / 2`, and let `E ⊆ {1, …, M}` be the set of `m` such that `2 m`
is not a sum of two distinct elements of `{1, …, N}` of the same colour.

* An iterated pigeonhole step, a weak form of the Hilbert cube lemma: if `A ⊆ {1, …, M}` has at
  least `M / q` elements and `M` is large, some difference `d ∈ {1, …, M}` (avoiding finitely many
  given values) occurs between at least `M / (4 q²)` pairs of `A`, so `{x ∈ A | x + d ∈ A}` is
  again dense. Repeating this `k` times gives `a` and `k` distinct positive integers
  `d₁, …, d_k` such that `a`, every `a + dᵢ` and every `a + dᵢ + dⱼ` with `i ≠ j` lie in `A`.
* If `E` had at least `M / 4` elements, the `k + 1` integers `a, a + 2 d₁, …, a + 2 d_k` would
  lie in `{1, …, N}`, so two of them would have the same colour. Their sum is `2 (a + dᵢ)` or
  `2 (a + dᵢ + dⱼ)`, twice an element of `E`: a contradiction.
* So more than `3 M / 4` of the even numbers `2 m ≤ N` are monochromatic sums; as
  `N ≤ 2 M + 1`, they number at least `N / 4`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticSumsLinearErdosProblem484Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #484, https://www.erdosproblems.com/484 (status PROVED
(LEAN)). UnsolvedMath record UM-30006894 (`EP-484`), dataset ulamai/UnsolvedMath v1.8.0.

A colouring is any `f : ℕ → Fin k`; only its values on `{1, …, N}` matter. `c` does not depend on
`k`; `N₀` does. Compared with the formal-conjectures statement `ErdosProblems/484.lean` (equivalent;
no code imported).
-/

/-- **Erdős Problem 484: linearly many monochromatic sums.** This is the statement that there is a
real constant $c > 0$ such that for every integer $k \ge 1$ there is an $N_0 \in \mathbb{N}$ with
the following property: for every $N \ge N_0$ and every colouring
$f : \mathbb{N} \to \{0, \dots, k-1\}$, at least $cN$ of the integers $n \in \{1, \dots, N\}$ can
be written as $n = a + b$ with $a, b \in \{1, \dots, N\}$, $a \ne b$ and $f(a) = f(b)$.

Only the colours of $1, \dots, N$ matter, so this is a statement about $k$-colourings of
$\{1, \dots, N\}$; $c$ does not depend on $k$, while $N_0$ may. -/
def monochromaticSumsLinearCount : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ℕ → Fin k,
    c * N ≤ ({n : ℕ | n ∈ Finset.Icc 1 N ∧
      ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n}.ncard : ℝ)

/-- `a`, every `a + d` and every `a + d + d'` with `d ≠ d'` in `D` lie in `A`: the part of the
Hilbert cube `{a + ∑ i ∈ S, i | S ⊆ D}` with `|S| ≤ 2`. -/
private def IsCubeBase (A : Finset ℕ) (a : ℕ) (D : Finset ℕ) : Prop :=
  a ∈ A ∧ (∀ d ∈ D, a + d ∈ A) ∧ ∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → a + d + d' ∈ A

/-- A cube base of `{x ∈ A | x + d ∈ A}` with differences `D` is a cube base of `A` with the
differences `insert d D`. -/
private theorem isCubeBase_insert {A : Finset ℕ} {a d : ℕ} {D : Finset ℕ}
    (h : IsCubeBase (A.filter (· + d ∈ A)) a D) : IsCubeBase A a (insert d D) := by
  obtain ⟨ha, hD, hDD⟩ := h
  simp only [Finset.mem_filter] at ha hD hDD
  refine ⟨ha.1, fun e he => ?_, fun e he e' he' hne => ?_⟩
  · rcases Finset.mem_insert.1 he with rfl | he
    · exact ha.2
    · exact (hD e he).1
  · rcases Finset.mem_insert.1 he with h | h <;> rcases Finset.mem_insert.1 he' with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · subst h
      rw [add_right_comm]
      exact (hD e' h').2
    · subst h'
      exact (hD e h).2
    · exact (hDD e h e' h' hne).1

/-- Counting the pairs `x < y` of `A` from both ends: twice their number plus `#A` is `#A²`. -/
private theorem two_mul_sum_card_lt_add_card (A : Finset ℕ) :
    2 * ∑ x ∈ A, (A.filter (x < ·)).card + A.card = A.card * A.card := by
  have hcomm : ∑ x ∈ A, (A.filter (x < ·)).card = ∑ x ∈ A, (A.filter (· < x)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hsplit : ∀ x ∈ A,
      (A.filter (x < ·)).card + (A.filter (· < x)).card + 1 = A.card := by
    intro x hx
    have h1 := Finset.card_filter_add_card_filter_not (s := A) (fun y => x < y)
    have h2 : A.filter (fun y => ¬ x < y) = insert x (A.filter (· < x)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
      constructor
      · rintro ⟨hy, hyx⟩
        rcases hyx.lt_or_eq with h | h
        · exact Or.inr ⟨hy, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨hy, h⟩)
        · exact ⟨hx, le_rfl⟩
        · exact ⟨hy, h.le⟩
    rw [h2, Finset.card_insert_of_notMem (by simp)] at h1
    omega
  calc 2 * ∑ x ∈ A, (A.filter (x < ·)).card + A.card
      = ∑ x ∈ A, ((A.filter (x < ·)).card + (A.filter (· < x)).card + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hcomm]
        simp only [Finset.sum_const, smul_eq_mul, mul_one]
        ring
    _ = ∑ x ∈ A, A.card := Finset.sum_congr rfl hsplit
    _ = A.card * A.card := by simp

/-- For `A ⊆ {1, …, M}`, the pairs `x < y` of `A` are counted by their differences
`y - x ∈ {1, …, M}`. -/
private theorem card_mul_card_le (M : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 M) :
    A.card * A.card ≤
      2 * ∑ d ∈ Finset.Icc 1 M, (A.filter (· + d ∈ A)).card + A.card := by
  have h1 : ∑ d ∈ Finset.Icc 1 M, (A.filter (· + d ∈ A)).card =
      ∑ x ∈ A, ((Finset.Icc 1 M).filter (x + · ∈ A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : ∀ x ∈ A,
      (A.filter (x < ·)).card ≤ ((Finset.Icc 1 M).filter (x + · ∈ A)).card := by
    intro x hx
    refine Finset.card_le_card_of_injOn (fun y => y - x) (fun y hy => ?_) (fun y hy z hz hyz => ?_)
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hy ⊢
      have := Finset.mem_Icc.1 (hA hy.1)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.add_sub_cancel' hy.2.le]
      exact hy.1
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hy hz
      simp only at hyz
      omega
  have h3 := two_mul_sum_card_lt_add_card A
  have h4 := Finset.sum_le_sum h2
  rw [h1]
  omega

/-- The cube lemma for the part of a Hilbert cube used here: for all `j`, `q` and `p`, every
`A ⊆ {1, …, M}` with `M ≤ q * #A` has a cube base with `j` distinct positive differences avoiding
any given set of at most `p` values, once `M` is large. -/
private theorem exists_isCubeBase (j : ℕ) : ∀ q p : ℕ, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M → M ≤ q * A.card → ∀ P : Finset ℕ, P.card ≤ p →
      ∃ a D, D.card = j ∧ Disjoint D P ∧ (∀ d ∈ D, 0 < d) ∧ IsCubeBase A a D := by
  induction j with
  | zero =>
    refine fun q p => ⟨1, fun M hM A hA hq P hP => ?_⟩
    obtain ⟨a, ha⟩ : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp only [Finset.card_empty, mul_zero, nonpos_iff_eq_zero] at hq
      omega
    exact ⟨a, ∅, rfl, Finset.disjoint_empty_left _, by simp, ha, by simp, by simp⟩
  | succ j ih =>
    intro q p
    obtain ⟨M₁, hM₁⟩ := ih (4 * q * q) (p + 1)
    refine ⟨max M₁ (2 * q * (2 * p + 1) + 1), fun M hM A hA hq P hP => ?_⟩
    have hM1 : M₁ ≤ M := le_of_max_le_left hM
    have hM2 : 2 * q * (2 * p + 1) + 1 ≤ M := le_of_max_le_right hM
    obtain ⟨d, hd, hdP, hdA⟩ : ∃ d ∈ Finset.Icc 1 M, d ∉ P ∧
        M ≤ 4 * q * q * (A.filter (· + d ∈ A)).card := by
      by_contra! h
      set s := A.card
      set S1 := ∑ d ∈ (Finset.Icc 1 M).filter (· ∉ P), (A.filter (· + d ∈ A)).card
      set S2 := ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ∉ P), (A.filter (· + d ∈ A)).card
      have hsum : ∑ d ∈ Finset.Icc 1 M, (A.filter (· + d ∈ A)).card = S1 + S2 :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hpair := card_mul_card_le M A hA
      have hS1 : 4 * q * q * S1 ≤ M * M := by
        rw [Finset.mul_sum]
        calc ∑ d ∈ (Finset.Icc 1 M).filter (· ∉ P), 4 * q * q * (A.filter (· + d ∈ A)).card
            ≤ ∑ d ∈ (Finset.Icc 1 M).filter (· ∉ P), M := by
              refine Finset.sum_le_sum fun d hd => ?_
              simp only [Finset.mem_filter] at hd
              exact (h d hd.1 hd.2).le
          _ ≤ M * M := by
              rw [Finset.sum_const, smul_eq_mul]
              refine Nat.mul_le_mul_right _ ?_
              calc _ ≤ (Finset.Icc 1 M).card := Finset.card_filter_le _ _
                _ = M := by simp
      have hS2 : S2 ≤ p * s := by
        calc S2 ≤ ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ d ∉ P), s :=
              Finset.sum_le_sum fun d _ => Finset.card_filter_le _ _
          _ ≤ p * s := by
              rw [Finset.sum_const, smul_eq_mul]
              refine Nat.mul_le_mul_right _ (le_trans (Finset.card_le_card fun d hd => ?_) hP)
              simp only [Finset.mem_filter, not_not] at hd
              exact hd.2
      have hMq : M * M ≤ q * q * (s * s) := by
        have := Nat.mul_le_mul hq hq
        nlinarith [this]
      have hq0 : 0 < q := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hq; omega
      have hs0 : 0 < s := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hq; omega
      have key : (q * q * s) * (2 * s) ≤ (q * q * s) * (4 * (2 * p + 1)) := by
        nlinarith [hpair, hsum, hS1, hS2, hMq]
      have hs_le : 2 * s ≤ 4 * (2 * p + 1) :=
        Nat.le_of_mul_le_mul_left key (by positivity)
      have : M ≤ q * (2 * (2 * p + 1)) := le_trans hq (Nat.mul_le_mul_left _ (by omega))
      nlinarith [this, hM2]
    obtain ⟨a, D, hDcard, hDP, hDpos, hcube⟩ := hM₁ M hM1 (A.filter (· + d ∈ A))
      ((Finset.filter_subset _ _).trans hA) hdA (insert d P)
      ((Finset.card_insert_le _ _).trans (by omega))
    have hdD : d ∉ D := fun h => Finset.disjoint_left.1 hDP h (Finset.mem_insert_self _ _)
    refine ⟨a, insert d D, ?_, ?_, fun e he => ?_, isCubeBase_insert hcube⟩
    · rw [Finset.card_insert_of_notMem hdD, hDcard]
    · rw [Finset.disjoint_insert_left]
      exact ⟨hdP, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hDP⟩
    · rcases Finset.mem_insert.1 he with rfl | he
      · exact (Finset.mem_Icc.1 hd).1
      · exact hDpos e he

/--
**Erdős–Sárközy–Sós theorem on monochromatic sums (Erdős Problem 484).** There is a real constant
$c > 0$ such that for every integer $k \ge 1$ there is an $N_0 \in \mathbb{N}$ such that for every
$N \ge N_0$ and every colouring $f : \mathbb{N} \to \{0, \dots, k-1\}$, at least $cN$ of the
integers $n \in \{1, \dots, N\}$ can be written as $n = a + b$ with $a, b \in \{1, \dots, N\}$,
$a \ne b$ and $f(a) = f(b)$.

Erdős, Sárközy and Sós proved that at least $N/2 - O(N^{1 - 1/2^{k+1}})$ even numbers in
$\{1, \dots, N\}$ are such monochromatic sums, so any $c < 1/2$ works.

Source: T. F. Bloom, Erdős
Problems, Problem #484, https://www.erdosproblems.com/484 (status PROVED (LEAN)); resolution: P.
Erdős, A. Sárközy and V. T. Sós, On a conjecture of Roth and some related problems. I (1989), 47-59,
erdosproblems.com/484: at least N/2 - O(N^{1 - 1/2^{k+1}}) even numbers are monochromatic sums,
https://www.erdosproblems.com/484.
-/
theorem monochromaticSumsLinearCount_holds : monochromaticSumsLinearCount := by
  refine ⟨1 / 4, by norm_num, fun k _ => ?_⟩
  obtain ⟨M₀, hM₀⟩ := exists_isCubeBase k 4 0
  refine ⟨2 * M₀, fun N hN f => ?_⟩
  classical
  set M := N / 2 with hMdef
  -- `mono m`: `2 * m` is a sum of two distinct elements of `[1, N]` of the same colour.
  let mono : ℕ → Prop := fun m =>
    ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = 2 * m
  set E := (Finset.Icc 1 M).filter (fun m => ¬ mono m) with hE
  set T := (Finset.Icc 1 M).filter mono with hT
  have hET : T.card + E.card = M := by
    rw [hT, hE, Finset.card_filter_add_card_filter_not]
    simp
  -- Fewer than a quarter of the even numbers `2 * m ≤ N` are not monochromatic sums.
  have hEsmall : 4 * E.card < M := by
    by_contra! hbig
    obtain ⟨a, D, hDcard, -, hDpos, ha, haD, haDD⟩ :=
      hM₀ M (by omega) E (Finset.filter_subset _ _) hbig ∅ (by simp)
    have hEM : ∀ m ∈ E, 1 ≤ m ∧ m ≤ M := fun m hm =>
      Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1
    have hEmono : ∀ m ∈ E, ¬ mono m := fun m hm => (Finset.mem_filter.1 hm).2
    have hM2 : 2 * M ≤ N := by omega
    -- The `k + 1` points `a` and `a + 2 * d` for `d ∈ D`; two of them share a colour.
    set X := insert a (D.image (fun d => a + 2 * d)) with hX
    have hXcard : X.card = k + 1 := by
      rw [hX, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ ?_, hDcard]
      · intro x y hxy
        simp only at hxy
        omega
      · simp only [Finset.mem_image, not_exists, not_and]
        intro d hd h
        have := hDpos d hd
        omega
    obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := X) (t := (Finset.univ : Finset (Fin k))) (by simp [hXcard]) (f := f)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    have hmem : ∀ z ∈ X, z ∈ Finset.Icc 1 N := by
      intro z hz
      rw [hX, Finset.mem_insert, Finset.mem_image] at hz
      rcases hz with rfl | ⟨d, hd, rfl⟩
      · have := hEM _ ha
        exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
      · have := hEM _ (haD d hd)
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have key : ∀ m ∈ E, x + y = 2 * m → False := fun m hm hsum =>
      hEmono m hm ⟨x, hmem x hx, y, hmem y hy, hxy, hfxy, hsum⟩
    rw [Finset.mem_insert, Finset.mem_image] at hx hy
    rcases hx with rfl | ⟨d, hd, rfl⟩ <;> rcases hy with h | ⟨d', hd', rfl⟩
    · exact hxy h.symm
    · exact key _ (haD d' hd') (by ring)
    · exact key _ (haD d hd) (by rw [h]; ring)
    · have hdd : d ≠ d' := by
        rintro rfl
        exact hxy rfl
      exact key _ (haDD d hd d' hd' hdd) (by ring)
  -- The doubles of the elements of `T` are monochromatic sums.
  have hsub : ((T.image (2 * ·) : Finset ℕ) : Set ℕ) ⊆ {n : ℕ | n ∈ Finset.Icc 1 N ∧
      ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n} := by
    intro n hn
    rw [Finset.coe_image, Set.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, hm.2⟩
  have hfin : {n : ℕ | n ∈ Finset.Icc 1 N ∧
      ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n}.Finite :=
    (Finset.Icc 1 N).finite_toSet.subset fun n hn => hn.1
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
    at hcard
  have hN : N ≤ 4 * T.card := by omega
  have hN' : (N : ℝ) ≤ 4 * T.card := by exact_mod_cast hN
  have hcard' := (Nat.cast_le (α := ℝ)).2 hcard
  linarith

end MathlibExt.Combinatorics.MonochromaticSumsLinearErdosProblem484Wanted
