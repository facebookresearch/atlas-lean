/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# An improved upper bound for Sidon subsets of an interval

The maximum size of a Sidon subset of `{1, …, N}` is at most
`√N + c * N ^ (1 / 4)` for some constant `c < 1` and all sufficiently large `N`.
The proof uses the two-window method of Carter, Hunter and O'Bryant
(https://arxiv.org/abs/2310.20032).

Source: B. Green, 100 open problems, Problem 31 (manuscript, update of December 2025),
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf. UnsolvedMath record UM-00000162
(`GREEN-074`), dataset ulamai/UnsolvedMath v1.8.0.

`F(N)` is the largest size of a Sidon subset of `{1, …, N}` (MathlibExt `Set.IsSidon`: all pairwise
sums distinct up to order). The target is the improvement of Lindström's upper bound recorded in
Green's own update to Problem 31: `F(N) ≤ N^{1/2} + c N^{1/4}` for all large `N` with a constant `c
< 1`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SidonUpperBoundImprovementGreenProblem31Wanted

/-- **Largest Sidon subset of $\{1, \dots, N\}$ (Green's Problem 31).** For a natural number
$N$, $F(N)$ is the largest cardinality of a Sidon subset of $[N] = \{1, \dots, N\}$. -/
noncomputable def maxSidonSubsetSize (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ (A : Set ℕ).IsSidon ∧ A.card = k}

/-- **Green's Problem 31: improving Lindström's upper bound.** Let $F(N)$ be the largest
size of a Sidon subset of $\{1, \dots, N\}$. The statement is that there are a real constant
$c < 1$ and a natural number $N_0$ such that $F(N) \le \sqrt{N} + c N^{1/4}$ for all $N \ge N_0$.

Lindström's bound is $F(N) \le N^{1/2} + N^{1/4} + O(1)$; the statement asks for a constant
below $1$ in the second term. -/
def sidonUpperBoundImproved : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (maxSidonSubsetSize N : ℝ) ≤ Real.sqrt N + c * (N : ℝ) ^ ((1 : ℝ) / 4)

open Finset
open scoped Pointwise

/-- The elements of `A` lying in the window ending at `x` of length `M`. -/
private def window (A : Finset ℕ) (M x : ℕ) : Finset ℕ :=
  A.filter fun a ↦ a ≤ x ∧ x < a + M

private lemma card_window_eq_card_fiber (A : Finset ℕ) (M x : ℕ) :
    (window A M x).card = ((A ×ˢ range M).filter fun p ↦ p.1 + p.2 = x).card := by
  refine card_bij (fun a _ ↦ (a, x - a)) ?_ ?_ ?_
  · intro a ha
    simp only [window, mem_filter] at ha
    simp only [mem_filter, mem_product, mem_range]
    exact ⟨⟨ha.1, by omega⟩, by omega⟩
  · intro a _ b _ h
    exact congrArg Prod.fst h
  · rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_product, mem_range] at h
    exact ⟨a, mem_filter.mpr ⟨h.1.1, by omega, by omega⟩, by congr 1; omega⟩

/-- The number of coincidences among translates is bounded by the diagonal incidences
and the number of ordered pairs of distinct shifts. -/
private lemma energy_le {A T : Finset ℕ} (hA : (A : Set ℕ).IsSidon) :
    A.addEnergy T ≤ A.card * T.card + T.offDiag.card := by
  let code (p : (ℕ × ℕ) × ℕ × ℕ) : (ℕ × ℕ) ⊕ (ℕ × ℕ) :=
    if p.2.1 = p.2.2 then .inl (p.1.1, p.2.1) else .inr p.2
  rw [← card_product, ← card_disjSum]
  unfold addEnergy
  apply card_le_card_of_injOn code
  · rintro ⟨⟨a, b⟩, u, v⟩ h
    simp only [SetLike.mem_coe, mem_filter, mem_product] at h
    by_cases huv : u = v
    · simp [code, huv, h.1.1.1, h.1.2.2]
    · simp [code, huv, h.1.2.1, h.1.2.2, mem_offDiag]
  · rintro ⟨⟨a, b⟩, u, v⟩ hab ⟨⟨c, d⟩, w, z⟩ hcd he
    simp only [mem_coe, mem_filter, mem_product] at hab hcd
    by_cases huv : u = v <;> by_cases hwz : w = z <;>
      simp only [code, huv, hwz, ↓reduceIte, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, Prod.mk.injEq] at he
    · obtain ⟨rfl, rfl⟩ := he
      have := hab.2
      have := hcd.2
      simp_all
    · obtain ⟨rfl, rfl⟩ := he
      rcases hA a hab.1.1.1 d hcd.1.1.2 c hcd.1.1.1 b hab.1.1.2 (by omega) with h | h
      · simp [h.1, h.2]
      · have := h.1
        have := hab.2
        omega

-- Count incidences, then count pairs of incidences with the same endpoint.
private lemma sum_window_moments {N : ℕ} {A : Finset ℕ}
    (hN : A ⊆ Icc 1 N) (hA : (A : Set ℕ).IsSidon) (M : ℕ) :
    (∑ x ∈ range (N + M), (window A M x).card) = A.card * M ∧
      (∑ x ∈ range (N + M), (window A M x).card ^ 2) ≤ A.card * M + M ^ 2 := by
  have hMaps : Set.MapsTo (fun p : ℕ × ℕ ↦ p.1 + p.2)
      (↑(A ×ˢ range M)) (↑(range (N + M))) := by
    intro p hp
    obtain ⟨ha, ht⟩ := mem_product.mp hp
    exact mem_range.mpr (Nat.add_lt_add_of_le_of_lt (mem_Icc.mp (hN ha)).2 (mem_range.mp ht))
  constructor
  · simp_rw [card_window_eq_card_fiber]
    rw [← card_eq_sum_card_fiberwise hMaps, card_product, card_range]
  · simp_rw [card_window_eq_card_fiber]
    have hsum : A + range M ⊆ range (N + M) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hx
      exact hMaps (x := (a, b)) (mem_product.mpr ⟨ha, hb⟩)
    rw [← sum_subset hsum, ← addEnergy_eq_sum_sq']
    · calc
        _ ≤ A.card * (range M).card + (range M).offDiag.card := energy_le hA
        _ ≤ _ := by
          rw [offDiag_card, card_range, sq]
          exact Nat.add_le_add_left (Nat.sub_le _ _) _
    · intro x _ hx
      rw [filter_eq_empty_iff.mpr, card_empty, zero_pow (by decide)]
      intro p hp he
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      exact hx (mem_add.mpr ⟨p.1, ha, p.2, hb, he⟩)

/-- Sum of the squared deviations of the window counts from a chosen reference value. -/
private noncomputable def windowDeviation (A : Finset ℕ) (N M : ℕ) (a : ℝ) : ℝ :=
  ∑ x ∈ range (N + M), ((window A M x).card - a) ^ 2

-- Centering at an arbitrary value keeps the bound linear in the cardinality of A.
private lemma windowDeviation_le {N M : ℕ} {A : Finset ℕ} {q : ℝ}
    (hN : A ⊆ Icc 1 N) (hA : (A : Set ℕ).IsSidon) (hq : (N : ℝ) = q ^ 4)
    (a : ℝ) :
    windowDeviation A N M a ≤
      ((M : ℝ) - q ^ 2 * a) ^ 2 + M * (q ^ 2 + a ^ 2 - (2 * a - 1) * (A.card - q ^ 2)) := by
  obtain ⟨h₁, h₂⟩ := sum_window_moments hN hA M
  have hsum : (∑ x ∈ range (N + M), ((window A M x).card : ℝ)) = A.card * M := by
    exact_mod_cast h₁
  have hsquares : (∑ x ∈ range (N + M), ((window A M x).card : ℝ) ^ 2) ≤
      A.card * M + (M : ℝ) ^ 2 := by
    exact_mod_cast h₂
  calc
    windowDeviation A N M a =
        (∑ x ∈ range (N + M), ((window A M x).card : ℝ) ^ 2) -
          (2 * a) * (A.card * M) + (N + M : ℝ) * a ^ 2 := by
      unfold windowDeviation
      simp_rw [sub_sq]
      simp only [mul_right_comm 2 _ a, sum_add_distrib, sum_sub_distrib, ← mul_sum, hsum,
        sum_const, card_range, nsmul_eq_mul, Nat.cast_add]
    _ ≤ _ := by
      rw [hq]
      linear_combination hsquares

private lemma le_windowDeviation {A : Finset ℕ} {N M : ℕ} {a d : ℝ} {S : Finset ℕ}
    (hS : S ⊆ range (N + M))
    (hd : ∀ x ∈ S, d ^ 2 ≤ ((window A M x).card - a) ^ 2) :
    S.card * d ^ 2 ≤ windowDeviation A N M a := by
  calc
    _ = ∑ _x ∈ S, d ^ 2 := by simp
    _ ≤ ∑ x ∈ S, ((window A M x).card - a) ^ 2 := sum_le_sum hd
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hS fun _ _ _ ↦ sq_nonneg _

/-- Rounding the window length down to a multiple of its scaling factor costs at most
one unit per shift in the bound on the sum of squared deviations. -/
private lemma scaled_windowDeviation_le {N : ℕ} {A : Finset ℕ} {q : ℝ}
    (hN : A ⊆ Icc 1 N) (hA : (A : Set ℕ).IsSidon) (hNq : (N : ℝ) = q ^ 4)
    (hq : 100000 ≤ q) (hlarge : q ^ 2 + (99999 / 100000) * q < (A.card : ℝ))
    {m j : ℕ} (hm : m = ⌊q ^ 3 / 100⌋₊) (hj₁ : 1 ≤ j) (hj₂ : j ≤ 100) :
    windowDeviation A N (j * m) (j * q / 100) ≤
      (j * m : ℝ) * (q ^ 2 + (j * q / 100) ^ 2 -
        (2 * (j * q / 100) - 1) * ((99999 / 100000) * q) + 1) := by
  have hq₀ : 0 ≤ q := by linarith
  have hj₁' : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
  have hj₂' : (j : ℝ) ≤ 100 := by exact_mod_cast hj₂
  have hfloor : (m : ℝ) ≤ q ^ 3 / 100 := hm ▸ Nat.floor_le (by positivity)
  have hceil : q ^ 3 / 100 < (m : ℝ) + 1 := hm ▸ Nat.lt_floor_add_one _
  have hm_large : (10000 : ℝ) ≤ m := by
    have hq₃ : (100000 : ℝ) ^ 3 ≤ q ^ 3 := by gcongr
    linarith
  have hround : ((j * m : ℝ) - q ^ 2 * (j * q / 100)) ^ 2 ≤ j * m := by
    calc
      _ = ((j : ℝ) * (q ^ 3 / 100 - m)) ^ 2 := by ring
      _ ≤ (100 : ℝ) ^ 2 := by
        refine (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hfloor))
          (by norm_num)).2 ?_
        calc
          _ ≤ (j : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith only [hceil]) (Nat.cast_nonneg _)
          _ ≤ _ := by simpa using hj₂'
      _ ≤ _ := by
        norm_num
        exact hm_large.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hj₁')
  have hcoeff : 0 ≤ 2 * ((j : ℝ) * q / 100) - 1 := by
    have hjq := le_mul_of_one_le_left hq₀ hj₁'
    linarith
  have hmul := mul_le_mul_of_nonneg_left
    (show (99999 / 100000 : ℝ) * q ≤ A.card - q ^ 2 by linarith only [hlarge]) hcoeff
  have hdev := windowDeviation_le (M := j * m) hN hA hNq (j * q / 100)
  push_cast at hdev
  calc
    _ ≤ _ := hdev
    _ ≤ (j * m : ℝ) + (j * m : ℝ) * (q ^ 2 + (j * q / 100) ^ 2 -
        (2 * (j * q / 100) - 1) * ((99999 / 100000) * q)) :=
      add_le_add hround (mul_le_mul_of_nonneg_left (sub_le_sub_left hmul _) (by positivity))
    _ = _ := by ring

private lemma card_le_of_large_interval {N : ℕ} {A : Finset ℕ} {q : ℝ}
    (hN : A ⊆ Icc 1 N) (hA : (A : Set ℕ).IsSidon) (hNq : (N : ℝ) = q ^ 4)
    (hq : 100000 ≤ q) :
    (A.card : ℝ) ≤ q ^ 2 + (99999 / 100000) * q := by
  by_contra! hlarge
  let m := ⌊q ^ 3 / 100⌋₊
  have hq₀ : 0 ≤ q := by linarith
  have hq₂ : 100000 * q ≤ q ^ 2 := by
    nlinarith only [mul_nonneg hq₀ (sub_nonneg.mpr hq)]
  have hm : 0 < m := by
    have hq₃ : (100000 : ℝ) ^ 3 ≤ q ^ 3 := by gcongr
    exact (Nat.one_le_floor_iff _).mpr (by linarith)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hLong : windowDeviation A N (100 * m) q ≤ (m : ℝ) * (q ^ 2 / 200) := by
    have h := scaled_windowDeviation_le hN hA hNq hq hlarge (m := m) (j := 100)
      rfl (by decide) (by decide)
    have ha : (100 : ℝ) * q / 100 = q := by ring
    simp only [Nat.cast_ofNat, ha] at h
    refine h.trans ?_
    calc
      _ ≤ (100 * m : ℝ) * (q ^ 2 / 20000) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hq, hq₂]) (by positivity)
      _ = _ := by ring
  have hShort : windowDeviation A N (97 * m) (97 * q / 100) ≤ (m : ℝ) * (q ^ 2 / 10) := by
    have h := scaled_windowDeviation_le hN hA hNq hq hlarge (m := m) (j := 97)
      rfl (by decide) (by decide)
    refine h.trans ?_
    calc
      _ ≤ (97 * m : ℝ) * (q ^ 2 / 1000) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hq, hq₂]) (by positivity)
      _ ≤ _ := by nlinarith only [mul_nonneg hm'.le (sq_nonneg q)]
  -- Up to the long window length, the windows count entire prefixes of A.
  let initial (x : ℕ) := A.filter fun a ↦ a ≤ x
  have hpmono {x y : ℕ} (hxy : x ≤ y) : initial x ⊆ initial y :=
    fun _ ha ↦ mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.trans hxy⟩
  have hprefix (x : ℕ) (hx : x < 100 * m) : window A (100 * m) x = initial x := by
    ext a
    have hax : x < a + 100 * m := by omega
    simp [window, initial, hax]
  have hgap : (m : ℝ) * (q ^ 2 / 200) < (m : ℝ) * (q / 10) ^ 2 :=
    mul_lt_mul_of_pos_left (by nlinarith only [sq_pos_of_pos (show 0 < q by linarith)]) hm'
  -- At either end of this initial segment, a deviation from the reference value
  -- persists on an interval of length m by monotonicity of the prefix counts.
  have hlow : (9 / 10 : ℝ) * q < (initial m).card := by
    by_contra! h
    have hV : (m : ℝ) * (q / 10) ^ 2 ≤ windowDeviation A N (100 * m) q := by
      suffices ((range m).card : ℝ) * (q / 10) ^ 2 ≤ windowDeviation A N (100 * m) q by
        simpa only [card_range] using this
      apply le_windowDeviation
      · intro x hx
        exact mem_range.mpr (by have := mem_range.mp hx; omega)
      · intro x hx
        have hx' := mem_range.mp hx
        have hcard : ((initial x).card : ℝ) ≤ (initial m).card := by
          exact_mod_cast card_le_card (hpmono hx'.le)
        rw [hprefix x (by omega)]
        rw [← neg_sq (((initial x).card : ℝ) - q)]
        exact sq_le_sq' (by linarith only [hq, h, hcard]) (by linarith only [h, hcard])
    exact hgap.not_ge (hV.trans hLong)
  have hhigh : ((initial (99 * m)).card : ℝ) < (11 / 10 : ℝ) * q := by
    by_contra! h
    have hV : (m : ℝ) * (q / 10) ^ 2 ≤ windowDeviation A N (100 * m) q := by
      have hcard : (Ico (99 * m) (100 * m)).card = m := by rw [Nat.card_Ico]; omega
      suffices ((Ico (99 * m) (100 * m)).card : ℝ) * (q / 10) ^ 2 ≤
          windowDeviation A N (100 * m) q by simpa only [hcard] using this
      apply le_windowDeviation
      · intro x hx
        exact mem_range.mpr (by have := (mem_Ico.mp hx).2; omega)
      · intro x hx
        obtain ⟨hx₁, hx₂⟩ := mem_Ico.mp hx
        have hcard' : ((initial (99 * m)).card : ℝ) ≤ (initial x).card := by
          exact_mod_cast card_le_card (hpmono hx₁)
        rw [hprefix x hx₂]
        exact sq_le_sq' (by linarith only [h, hcard']) (by linarith only [hq, h, hcard'])
    exact hgap.not_ge (hV.trans hLong)
  -- The short windows here fit between the two cutoffs, where there are few elements.
  have hV : (m : ℝ) * (q / 2) ^ 2 ≤ windowDeviation A N (97 * m) (97 * q / 100) := by
    have hcard : (Ico (98 * m) (99 * m)).card = m := by rw [Nat.card_Ico]; omega
    suffices ((Ico (98 * m) (99 * m)).card : ℝ) * (q / 2) ^ 2 ≤
        windowDeviation A N (97 * m) (97 * q / 100) by simpa only [hcard] using this
    apply le_windowDeviation
    · intro x hx
      have hx' := (mem_Ico.mp hx).2
      have hmN : (100 * m : ℝ) ≤ N := by
        have hfloor := Nat.floor_le (a := q ^ 3 / 100) (by positivity)
        have hpows : q ^ 3 ≤ q ^ 4 := by
          rw [pow_succ]
          exact le_mul_of_one_le_right (by positivity) (by linarith)
        change (m : ℝ) ≤ q ^ 3 / 100 at hfloor
        linarith only [hNq, hfloor, hpows]
      have hmN' : 100 * m ≤ N := by exact_mod_cast hmN
      exact mem_range.mpr (by omega)
    · intro x hx
      obtain ⟨hx₁, hx₂⟩ := mem_Ico.mp hx
      have hsub : window A (97 * m) x ⊆ initial (99 * m) \ initial m := by
        intro a ha
        simp only [window, mem_filter] at ha
        simp only [initial, mem_sdiff, mem_filter]
        exact ⟨⟨ha.1, by omega⟩, by omega⟩
      have hcard' : ((window A (97 * m) x).card : ℝ) + (initial m).card ≤
          (initial (99 * m)).card := by
        have hle := Nat.add_le_add_right (card_le_card hsub) (initial m).card
        rw [card_sdiff_add_card_eq_card (hpmono (by omega))] at hle
        exact_mod_cast hle
      rw [← neg_sq (((window A (97 * m) x).card : ℝ) - 97 * q / 100)]
      exact sq_le_sq' (by linarith only [hq, hcard', hhigh, hlow])
        (by linarith only [hq, hcard', hhigh, hlow])
  have hgapShort : (m : ℝ) * (q ^ 2 / 10) < (m : ℝ) * (q / 2) ^ 2 :=
    mul_lt_mul_of_pos_left (by nlinarith only [sq_pos_of_pos (show 0 < q by linarith)]) hm'
  exact hgapShort.not_ge (hV.trans hShort)

/--
**Lindström's upper bound for Sidon sets can be improved.** Let $F(N)$ be the largest size of a
Sidon subset of $\{1, \dots, N\}$. There are a real constant $c < 1$ and a natural number $N_0$
such that $F(N) \le \sqrt{N} + c N^{1/4}$ for all $N \ge N_0$.

Balogh, Füredi and Roy proved this with $c = 0.998$; Carter, Hunter and O'Bryant later lowered
the constant to $0.98183$.

Source: B. Green, 100 open problems, Problem 31
(manuscript, update of December 2025),
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf; resolution: J. Balogh, Z. Füredi and
S. Roy, An upper bound on the size of Sidon sets, Amer. Math. Monthly 130 (2023), 437-445,
doi:10.1080/00029890.2023.2176667; arXiv:2103.15850, abstract: the maximum size of a Sidon set of
{1, ..., n} is at most √n + 0.998 n^{1/4} for sufficiently large n; Green, Problem 31, 'Update 2021'
records this bound and its 2023 improvement to 0.98183 (D. Carter, Z. Hunter and K. O'Bryant, Acta
Math. Hungar. 175 (2025), 108-126), https://arxiv.org/abs/2310.20032.
-/
public theorem sidonUpperBoundImproved_holds : sidonUpperBoundImproved := by
  refine ⟨99999 / 100000, by norm_num, 100000 ^ 4, ?_⟩
  intro N hN
  let q := (N : ℝ) ^ ((1 : ℝ) / 4)
  have hN₀ : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hq₀ : 0 ≤ q := Real.rpow_nonneg hN₀ _
  have hq₄ : (N : ℝ) = q ^ 4 := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hN₀]
    norm_num
  have hq₂ : Real.sqrt N = q ^ 2 := by
    rw [hq₄, show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg q)]
  have hq : (100000 : ℝ) ≤ q := by
    have hN' : (100000 : ℝ) ^ 4 ≤ N := by exact_mod_cast hN
    rw [hq₄] at hN'
    exact (pow_le_pow_iff_left₀ (by norm_num) hq₀ (by decide : 4 ≠ 0)).mp hN'
  have hAttained : ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ (A : Set ℕ).IsSidon ∧
      A.card = maxSidonSubsetSize N := by
    let sizes : Set ℕ := {k | ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ (A : Set ℕ).IsSidon ∧ A.card = k}
    change sSup sizes ∈ sizes
    apply Set.Nonempty.csSup_mem
    · refine ⟨0, ∅, empty_subset _, ?_, card_empty⟩
      simp [Set.IsSidon]
    · refine (Set.finite_le_nat N).subset ?_
      rintro k ⟨A, hA, _, rfl⟩
      exact (card_le_card hA).trans (by simp)
  obtain ⟨A, hAN, hA, hcard⟩ := hAttained
  rw [← hcard, hq₂]
  exact card_le_of_large_interval hAN hA hq₄ hq

end MathlibExt.Combinatorics.SidonUpperBoundImprovementGreenProblem31Wanted
