/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sums and products along the edges of a graph

We prove that the restricted sum-product bound in Erdős Problem 808 fails.
The construction uses the reciprocal factors in the examples of Alon, Ruzsa and Solymosi.
For each label `p` it joins two arithmetic progressions scaled by `1/p` and `p`,
clearing all denominators by a common factorial. The products are independent of the label,
while the sums for a fixed label belong to a short arithmetic progression.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.GraphRestrictedSumProductErdosProblem808Wanted

/-- **Erdős Problem 808 (sums and products along graphs).** The statement that for all real
numbers $c > 0$ and $\varepsilon > 0$ and all sufficiently large natural numbers $n$ the following
holds. Let $A$ be a set of $n$ positive integers and let $E$ be a finite set of pairs $(a, b)$ with
$a, b \in A$ and $a < b$ (the edges of a graph on $A$) such that $|E| \ge n^{1+c}$. Write
$A +_E A = \{a + b : (a, b) \in E\}$ and $A \cdot_E A = \{ab : (a, b) \in E\}$. Then
$\max(|A +_E A|, |A \cdot_E A|) \ge n^{1+c-\varepsilon}$. -/
def restrictedSumProductAlongGraphs : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ, 0 ∉ A → A.card = n →
    ∀ E : Finset (ℕ × ℕ), (∀ p ∈ E, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2) →
      (n : ℝ) ^ (1 + c) ≤ E.card →
        (n : ℝ) ^ (1 + c - ε) ≤
          max ((E.image fun p => p.1 + p.2).card : ℝ) ((E.image fun p => p.1 * p.2).card : ℝ)

open Finset

/-- The two ends of an edge with label `p + 1` use reciprocal factors. The residue
of its left end modulo `D` recovers `M / (p + 1)`, and hence its label. -/
private theorem graph_bounds (k u : ℕ) (hk : 0 < k) :
    ∃ (A : Finset ℕ) (E : Finset (ℕ × ℕ)),
      0 ∉ A ∧ k * u ≤ A.card ∧ A.card ≤ 2 * k * u ∧
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 < e.2) ∧ E.card = k * u ^ 2 ∧
      (E.image fun e => e.1 + e.2).card ≤ 3 * k ^ 3 * u ∧
      (E.image fun e => e.1 * e.2).card ≤ u ^ 2 := by
  let M := k.factorial
  let D := M + 1
  let d (p : ℕ) := M / (p + 1)
  have hM : 0 < M := k.factorial_pos
  have hD : 0 < D := Nat.succ_pos _
  have hd (p : ℕ) (hp : p < k) : d p * (p + 1) = M :=
    Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hp)
  have hdpos (p : ℕ) (hp : p < k) : 0 < d p := by
    exact Nat.div_pos (Nat.le_of_dvd hM (Nat.dvd_factorial (by omega) hp)) (Nat.succ_pos _)
  have hdlt (p : ℕ) : d p < D := Nat.lt_succ_of_le (Nat.div_le_self ..)
  let left (p j : ℕ) := d p * (D * j + 1)
  let right (p i : ℕ) := M * (p + 1) * (D * (u + i + 1))
  let S := range k ×ˢ range u
  let L := S.image fun x => left x.1 x.2
  let R := S.image fun x => right x.1 x.2
  let edge (x : (ℕ × ℕ) × ℕ) := (left x.1.1 x.1.2, right x.1.1 x.2)
  let E := (S ×ˢ range u).image edge
  -- Distinct left endpoints determine both their label and their progression index.
  have hleft : Set.InjOn (fun x : ℕ × ℕ => left x.1 x.2) S := by
    rintro ⟨p, j⟩ hp ⟨q, i⟩ hq he
    simp only [S, mem_coe, mem_product, mem_range] at hp hq
    change left p j = left q i at he
    have hmod (p j : ℕ) : left p j % D = d p := by
      simp [left, Nat.mul_add, mul_left_comm, Nat.mod_eq_of_lt (hdlt p)]
    have hd' : d p = d q := by simpa only [hmod] using congrArg (· % D) he
    have heq : d p * (p + 1) = d p * (q + 1) := by rw [hd p hp.1, hd', hd q hq.1]
    have hpq := Nat.eq_of_mul_eq_mul_left (hdpos p hp.1) heq
    have : p = q := by omega
    subst q
    have := Nat.eq_of_mul_eq_mul_left (hdpos p hp.1) he
    have : D * j = D * i := by omega
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hD this)
  have hL : L.card = k * u := by
    rw [show L.card = S.card from card_image_of_injOn hleft]
    simp [S]
  refine ⟨L ∪ R, E, ?_, hL ▸ card_le_card subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_union, L, R, mem_image, S, mem_product, mem_range, not_or]
    constructor
    · rintro ⟨⟨p, j⟩, ⟨hp, _⟩, he⟩
      exact (Nat.mul_pos (hdpos p hp) (Nat.succ_pos _)).ne' he
    · rintro ⟨⟨p, i⟩, _, he⟩
      exact (Nat.mul_pos (Nat.mul_pos hM (Nat.succ_pos _))
        (Nat.mul_pos hD (Nat.succ_pos _))).ne' he
  · calc
      _ ≤ L.card + R.card := card_union_le ..
      _ ≤ k * u + S.card := Nat.add_le_add (le_of_eq hL) card_image_le
      _ = _ := by simp [S]; ring
  · rintro e he
    obtain ⟨⟨⟨p, j⟩, i⟩, hx, rfl⟩ := mem_image.mp he
    obtain ⟨hpj, hi⟩ := mem_product.mp hx
    obtain ⟨hp, hj⟩ := mem_product.mp hpj
    refine ⟨mem_union_left _ (mem_image_of_mem _ hpj),
      mem_union_right _ (mem_image_of_mem (fun x : ℕ × ℕ => right x.1 x.2)
        (show (p, i) ∈ S from mem_product.mpr ⟨hp, hi⟩)), ?_⟩
    change left p j < right p i
    have hj' : j < u := mem_range.mp hj
    have hstep : D * j + 1 < D * (u + i + 1) := by
      nlinarith only [Nat.mul_le_mul_left D (show j + 1 ≤ u + i by omega), hD]
    calc
      left p j ≤ M * (D * j + 1) := Nat.mul_le_mul_right _ (Nat.div_le_self ..)
      _ < M * (D * (u + i + 1)) := Nat.mul_lt_mul_of_pos_left hstep hM
      _ ≤ right p i := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right M (Nat.succ_pos _))
  · have hinj : Set.InjOn edge ↑(S ×ˢ range u) := by
      rintro ⟨⟨p, j⟩, i⟩ hx ⟨⟨q, l⟩, m⟩ hy he
      obtain ⟨hpq, hi⟩ := Prod.mk.inj he
      have hpair := hleft (mem_product.mp hx).1 (mem_product.mp hy).1 hpq
      cases hpair
      change M * (p + 1) * (D * (u + i + 1)) = M * (p + 1) * (D * (u + m + 1)) at hi
      have := Nat.eq_of_mul_eq_mul_left hD
        (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hM (Nat.succ_pos _)) hi)
      congr 1
      omega
    rw [show E.card = (S ×ˢ range u).card from card_image_of_injOn hinj]
    simp [S, pow_two, mul_assoc]
  · -- For each label, a sum depends only on the single index j + (p + 1)² (u + i + 1).
    let sums := (range k ×ˢ range (3 * k ^ 2 * u)).image
      (fun x : ℕ × ℕ => left x.1 x.2)
    have hsub : (E.image fun e => e.1 + e.2) ⊆ sums := by
      rintro _ hz
      obtain ⟨_, he, rfl⟩ := mem_image.mp hz
      obtain ⟨⟨⟨p, j⟩, i⟩, hx, rfl⟩ := mem_image.mp he
      simp only [S, mem_product, mem_range] at hx
      obtain ⟨⟨hp, hj⟩, hi⟩ := hx
      refine mem_image.mpr ⟨(p, j + (p + 1) ^ 2 * (u + i + 1)), ?_, ?_⟩
      · simp only [mem_product, mem_range, hp, true_and]
        have hmul := Nat.mul_le_mul (Nat.pow_le_pow_left (show p + 1 ≤ k by omega) 2)
          (show u + i + 1 ≤ 2 * u by omega)
        have hu' : u ≤ k ^ 2 * u := Nat.le_mul_of_pos_left u (by positivity)
        nlinarith only [hj, hmul, hu']
      · change d p * (D * (j + (p + 1) ^ 2 * (u + i + 1)) + 1) = left p j + right p i
        dsimp only [left, right]
        rw [← hd p hp]
        ring
    calc
      _ ≤ sums.card := card_le_card hsub
      _ ≤ (range k ×ˢ range (3 * k ^ 2 * u)).card := card_image_le
      _ = _ := by simp; ring
  · -- In a product the factors d p and p + 1 cancel to the fixed value M.
    let prods := (range u ×ˢ range u).image
      (fun x : ℕ × ℕ => M ^ 2 * (D * x.1 + 1) * (D * (u + x.2 + 1)))
    have hsub : (E.image fun e => e.1 * e.2) ⊆ prods := by
      rintro _ hz
      obtain ⟨_, he, rfl⟩ := mem_image.mp hz
      obtain ⟨⟨⟨p, j⟩, i⟩, hx, rfl⟩ := mem_image.mp he
      simp only [S, mem_product, mem_range] at hx
      obtain ⟨⟨hp, hj⟩, hi⟩ := hx
      refine mem_image.mpr ⟨(j, i), by simpa using And.intro hj hi, ?_⟩
      change M ^ 2 * (D * j + 1) * (D * (u + i + 1)) = left p j * right p i
      dsimp only [left, right]
      rw [← hd p hp]
      ring
    calc
      _ ≤ prods.card := card_le_card hsub
      _ ≤ (range u ×ˢ range u).card := card_image_le
      _ = _ := by simp [pow_two]

/-- **Erdős Problem 808 is false.** There are real numbers $c > 0$ and $\varepsilon > 0$ such
that for infinitely many natural numbers $n$ there are a set $A$ of $n$ positive integers and a
finite set $E$ of pairs $(a, b)$ with $a, b \in A$ and $a < b$ (the edges of a graph on $A$)
such that $|E| \ge n^{1+c}$ and
$\max(|\{a + b : (a, b) \in E\}|, |\{ab : (a, b) \in E\}|) < n^{1+c-\varepsilon}$.

Alon, Ruzsa and Solymosi constructed, for arbitrarily large $n$, sets of $n$ integers with
graphs of $n^{5/3 - o(1)}$ edges along which both the sums and the products take at most
$n^{4/3 + o(1)}$ values, and counterexamples in $\mathbb{N}$ for every $0 < c < 1$.

Source: T. F. Bloom, Erdős Problems, Problem #808, https://www.erdosproblems.com/808
(status DISPROVED); resolution: N. Alon, I. Ruzsa and J. Solymosi, Sums, products and ratios along
the edges of a graph, Publ. Mat. 64 (2020), 143-155, Theorem 3: for arbitrarily large m_0 there are
a set A of m ≥ m_0 integers and a graph on A with Ω(m^{5/3}/log^{1/3} m) edges such that |A +_G A| +
|A ·_G A| = O((m log m)^{4/3}), refuting their Conjecture 2 (the strong Erdős-Szemerédi conjecture);
the construction takes A = {uw/v} for positive integers u, v, w scaled by a common denominator, so A
consists of positive integers; Theorem 4 gives counterexamples A ⊂ ℕ for every 0 < c < 1,
https://web.math.princeton.edu/~nalon/PDFS/sumprodrat7.pdf.
-/
public theorem restrictedSumProductAlongGraphs_refuted : ¬ restrictedSumProductAlongGraphs := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h (2 / 3) (1 / 15) (by norm_num) (by norm_num))
  let t := max N 4
  have ht : 4 ≤ t := le_max_right ..
  have htpos : 0 < t := by omega
  obtain ⟨A, E, hpos, hlow, hhigh, hgraph, hedges, hsums, hprods⟩ :=
    graph_bounds (t ^ 5) (t ^ 15) (by positivity)
  -- There are between t²⁰ and t²¹ vertices, exactly t³⁵ edges, and at most 3t³⁰ values.
  have hlo : t ^ 20 ≤ A.card := by convert hlow using 1; ring
  have hhi : A.card ≤ t ^ 21 := calc
    _ ≤ 2 * t ^ 5 * t ^ 15 := hhigh
    _ = t ^ 20 * 2 := by ring
    _ ≤ t ^ 20 * t := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring
  have he : E.card = t ^ 35 := by rw [hedges]; ring
  have hn : N ≤ A.card :=
    (le_max_left N 4).trans ((le_self_pow₀ (by omega : 1 ≤ t) (by decide : 20 ≠ 0)).trans hlo)
  have hlarge : (A.card : ℝ) ^ (1 + 2 / 3 : ℝ) ≤ E.card := calc
    _ ≤ ((t : ℝ) ^ 21) ^ (1 + 2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhi) (by norm_num)
    _ = (t : ℝ) ^ 35 := by rw [← Real.rpow_natCast_mul (by positivity)]; norm_num
    _ = _ := by exact_mod_cast he.symm
  have hbound := hN A.card hn A hpos rfl E hgraph hlarge
  have hsmall : max (E.image fun e => e.1 + e.2).card (E.image fun e => e.1 * e.2).card <
      t ^ 32 := by
    apply lt_of_le_of_lt (b := 3 * t ^ 30)
    · apply max_le
      · convert hsums using 1; ring
      · calc
          _ ≤ (t ^ 15) ^ 2 := hprods
          _ = t ^ 30 := by ring
          _ ≤ _ := by omega
    · rw [show t ^ 32 = t ^ 30 * t ^ 2 by ring, mul_comm 3]
      exact Nat.mul_lt_mul_of_pos_left (by nlinarith only [ht]) (by positivity)
  have hlower : (t : ℝ) ^ 32 ≤ (A.card : ℝ) ^ (1 + 2 / 3 - 1 / 15 : ℝ) := calc
    _ = ((t : ℝ) ^ 20) ^ (1 + 2 / 3 - 1 / 15 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) (by norm_num)
  exact (not_lt_of_ge (hlower.trans hbound)) (by exact_mod_cast hsmall)

end MathlibExt.Combinatorics.GraphRestrictedSumProductErdosProblem808Wanted
