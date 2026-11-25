/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Multicolored sunflowers in (ℤ/3)ⁿ (Oberwolfach Reports 54/2012)

Oberwolfach workshop Complexity Theory (2012), Conjecture 7 (C. Umans; Alon, Shpilka and Umans):
there is `c > 0` such that every set `S` of triples in `((ℤ/3)ⁿ)³` with `|S| ≥ 3^{n(1-c)}` and `x +
y + z = 0` for all `(x, y, z) ∈ S` contains three triples with `x₁ + y₂ + z₃ = 0`.

We prove the conjecture by expanding the zero-sum indicator over the field of three elements.

Source: C. Umans, in Complexity Theory, Oberwolfach Reports 9 (2012), no. 54, p. 3292, Conjecture 7,
DOI 10.4171/OWR/2012/54. UnsolvedMath record UM-30002241 (`OWR-12177-010`), dataset
ulamai/UnsolvedMath v1.8.0.

The three triples must not all be equal, and the bound is required only for `n > n₀`, as in Alon,
Shpilka and Umans's statement of the conjecture (On sunflowers and matrix multiplication, CCC 2012,
Conjecture 6), which the source cites; the source's wording has neither, and three copies of one
triple always qualify, while for `n = 0` the single triple `(0, 0, 0)` meets the size bound and has
no multicolored sunflower. `x + y + z = 0` says that `{x, y, z}` is a sunflower in `(ℤ/3)ⁿ` (in each
coordinate the entries are all equal or all distinct).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MulticoloredSunflowerTernaryOWR12177Problem010Wanted

/-- **Ternary vectors.** For a natural number $n$, the vectors of length $n$ over $\mathbb{Z}/3$,
that is, the functions from $\{0, 1, \dots, n - 1\}$ to $\mathbb{Z}/3$. -/
abbrev TernaryVec (n : ℕ) : Type := Fin n → ZMod 3

/-- **Multicolored sunflower.** Let $n$ be a natural number and let $S$ be a finite set of triples
$(x, y, z)$ of vectors in $(\mathbb{Z}/3)^n$. Then $S$ contains a multicolored sunflower if there
are triples $(x_1, y_1, z_1), (x_2, y_2, z_2), (x_3, y_3, z_3) \in S$, not all three equal, with
$x_1 + y_2 + z_3 = 0$. -/
def HasMulticoloredSunflower {n : ℕ} (S : Finset (TernaryVec n × TernaryVec n × TernaryVec n)) :
    Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ¬ (a = b ∧ b = c) ∧ a.1 + b.2.1 + c.2.2 = 0

/-- **Multicolored sunflower conjecture.** There are a real number $\varepsilon > 0$ and a natural
number $n_0$ such that for every $n > n_0$, every finite set $S$ of triples $(x, y, z)$ of vectors
in $(\mathbb{Z}/3)^n$ with $x + y + z = 0$ for every $(x, y, z) \in S$ and with
$|S| \ge 3^{(1 - \varepsilon) n}$ contains a multicolored sunflower: triples
$(x_1, y_1, z_1), (x_2, y_2, z_2), (x_3, y_3, z_3) \in S$, not all three equal, with
$x_1 + y_2 + z_3 = 0$.

The conjecture is due to Alon, Shpilka and Umans (Oberwolfach Report 54/2012, Conjecture 7). -/
def multicoloredSunflowerConjecture : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
    ∀ S : Finset (TernaryVec n × TernaryVec n × TernaryVec n),
      (∀ t ∈ S, t.1 + t.2.1 + t.2.2 = 0) → (3 : ℝ) ^ ((1 - ε) * n) ≤ S.card →
        HasMulticoloredSunflower S

open Finset

private abbrev F := ZMod 3

/-- Extract pivot rows for a family of evaluations. Each remaining row has a relation with
coefficient one there and all other coefficients supported on the pivots. -/
private lemma exists_pivots {I D : Type*} [Fintype I] [Fintype D]
    (A : Finset I) (v : I → D → F) :
    ∃ P ⊆ A, P.card ≤ Fintype.card D ∧ ∀ t ∈ A, t ∉ P →
      ∃ w : I → F, w t = 1 ∧ (∀ i, i ≠ t → i ∉ P → w i = 0) ∧
        ∀ d, ∑ i, w i * v i d = 0 := by
  classical
  obtain ⟨B, hBA, -, hspan, hind⟩ := exists_linearIndepOn_extension
    (v := v) (linearIndepOn_empty F v) (Set.empty_subset (A : Set I))
  let P := B.toFinset
  have hcard := hind.linearIndependent.fintype_card_le_finrank
  refine ⟨P, by simpa [P] using hBA, ?_, ?_⟩
  · simpa [P, Module.finrank_pi] using hcard
  intro t ht htp
  have hmem : v t ∈ Submodule.span F (v '' (P : Set I)) := by
    simpa [P] using hspan (Set.mem_image_of_mem v ht)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' F).mp hmem
  let w (i : I) : F := (if i = t then 1 else 0) - (if i ∈ P then c i else 0)
  refine ⟨w, by simp [w, htp], fun i hit hip ↦ by simp [w, hit, hip], ?_⟩
  intro d
  have heq := congrFun hc d
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heq
  simpa [w, sub_mul, sum_sub_distrib, ite_mul, sub_eq_zero] using heq.symm

/-- Three small spaces of evaluations can be annihilated with weights whose product on
the diagonal sums to one. Choose the second set of pivot rows outside the first. -/
private lemma exists_weights {I D : Type*} [Fintype I] [Fintype D]
    (x y z : I → D → F) (h : 3 * Fintype.card D < Fintype.card I) :
    ∃ u v w : I → F, (∑ i, u i * v i * w i) = 1 ∧
      (∀ d, ∑ i, u i * x i d = 0) ∧ (∀ d, ∑ i, v i * y i d = 0) ∧
      ∀ d, ∑ i, w i * z i d = 0 := by
  classical
  obtain ⟨P, -, hp, hP⟩ := exists_pivots univ x
  obtain ⟨Q, hQP, hq, hQ⟩ := exists_pivots (univ \ P) y
  obtain ⟨R, -, hr, hR⟩ := exists_pivots univ z
  have hlt : (P ∪ Q ∪ R).card < (univ : Finset I).card := by
    have := card_union_le P Q
    have := card_union_le (P ∪ Q) R
    rw [card_univ]
    omega
  obtain ⟨t, ht, hout⟩ := exists_mem_notMem_of_card_lt_card hlt
  simp only [mem_union, not_or] at hout
  obtain ⟨u, hut, hu, hux⟩ := hP t ht hout.1.1
  obtain ⟨v, hvt, hv, hvy⟩ := hQ t (mem_sdiff.mpr ⟨ht, hout.1.1⟩) hout.1.2
  obtain ⟨w, hwt, -, hwz⟩ := hR t ht hout.2
  refine ⟨u, v, w, ?_, hux, hvy, hwz⟩
  rw [sum_eq_single t]
  · simp [hut, hvt, hwt]
  · intro i _ hit
    by_cases hip : i ∈ P
    · have hiq : i ∉ Q := fun hi ↦ (mem_sdiff.mp (hQP hi)).2 hip
      simp [hv i hit hiq]
    · simp [hu i hit hip]
  · simp

private abbrev Exponents (n : ℕ) := Fin n → Fin 3

private def lowDegree (n : ℕ) : Finset (Exponents n) :=
  univ.filter fun e ↦ 3 * ∑ i, (e i).val ≤ 2 * n

private def monomial {n : ℕ} (e : Exponents n) (x : TernaryVec n) : F :=
  ∏ i, x i ^ (e i).val

-- The seven monomials of 1 - (x + y + z)² over the ternary field.
private def xExp : Fin 7 → Fin 3 := ![0, 2, 0, 0, 1, 1, 0]
private def yExp : Fin 7 → Fin 3 := ![0, 0, 2, 0, 1, 0, 1]
private def zExp : Fin 7 → Fin 3 := ![0, 0, 0, 2, 0, 1, 1]
private def coeff : Fin 7 → F := ![1, -1, -1, -1, 1, 1, 1]

private lemma coordinate_expansion : ∀ x y z : F,
    (if x + y + z = 0 then 1 else 0) =
      ∑ k, coeff k * x ^ (xExp k).val * y ^ (yExp k).val * z ^ (zExp k).val := by
  decide

private lemma indicator_expansion {n : ℕ} (x y z : TernaryVec n) :
    (if x + y + z = 0 then (1 : F) else 0) =
      ∑ k : Fin n → Fin 7, (∏ i, coeff (k i)) *
        monomial (xExp ∘ k) x * monomial (yExp ∘ k) y * monomial (zExp ∘ k) z := by
  classical
  have h : x + y + z = 0 ↔ ∀ i, x i + y i + z i = 0 := funext_iff
  calc
    _ = ∏ i, (if x i + y i + z i = 0 then (1 : F) else 0) := by
      rw [Fintype.prod_boole]
      by_cases hz : x + y + z = 0 <;> simp [hz, ← h]
    _ = _ := by
      simp_rw [coordinate_expansion, Fintype.prod_sum]
      simp only [prod_mul_distrib, monomial, Function.comp_apply]

private lemma lowDegree_cover {n : ℕ} (k : Fin n → Fin 7) :
    xExp ∘ k ∈ lowDegree n ∨ yExp ∘ k ∈ lowDegree n ∨ zExp ∘ k ∈ lowDegree n := by
  have h : ∀ j, (xExp j).val + (yExp j).val + (zExp j).val ≤ 2 := by decide
  have hsum := sum_le_sum (s := (univ : Finset (Fin n))) fun i _ ↦ h (k i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  simp only [lowDegree, mem_filter, mem_univ, true_and, Function.comp_apply]
  omega

private def contract {I : Type*} [Fintype I] (u v w : I → F) (K : I → I → I → F) : F :=
  ∑ p : I × I × I, u p.1 * v p.2.1 * w p.2.2 * K p.1 p.2.1 p.2.2

private lemma contract_sum {I J : Type*} [Fintype I] [Fintype J] (u v w : I → F)
    (K : J → I → I → I → F) :
    contract u v w (fun a b c ↦ ∑ j, K j a b c) = ∑ j, contract u v w (K j) := by
  simp only [contract, mul_sum]
  rw [sum_comm]

private lemma contract_monomial {I : Type*} [Fintype I] (u v w x y z : I → F) (s : F) :
    contract u v w (fun a b c ↦ s * x a * y b * z c) =
      s * (∑ i, u i * x i) * (∑ i, v i * y i) * (∑ i, w i * z i) := by
  calc
    _ = ∑ a, ∑ b, ∑ c, (s * (u a * x a)) * (v b * y b) * (w c * z c) := by
      simp only [contract, Fintype.sum_prod_type, mul_left_comm, mul_comm]
    _ = _ := by simp only [← mul_sum, ← sum_mul]

private lemma contract_diagonal {I : Type*} [Fintype I] [DecidableEq I] (u v w : I → F) :
    contract u v w (fun a b c ↦ if a = b ∧ b = c then 1 else 0) =
      ∑ i, u i * v i * w i := by
  simp only [contract, Fintype.sum_prod_type, ite_and, mul_ite, mul_one, mul_zero]
  simp [sum_ite_irrel]

/-- On a tricolored sum-free family the indicator is diagonal. Contracting it with the
three systems of weights counts one diagonal entry, while killing every monomial. -/
private lemma card_le_of_diagonal {I : Type*} [Fintype I] {n : ℕ}
    (x y z : I → TernaryVec n)
    (hd : ∀ a b c, x a + y b + z c = 0 ↔ a = b ∧ b = c) :
    Fintype.card I ≤ 3 * (lowDegree n).card := by
  classical
  by_contra! h
  let eval (f : I → TernaryVec n) (i : I) (d : lowDegree n) := monomial d.val (f i)
  obtain ⟨u, v, w, hone, hx, hy, hz⟩ := exists_weights (eval x) (eval y) (eval z)
    (by simpa only [Fintype.card_coe] using h)
  have hone' : contract u v w (fun a b c ↦ if x a + y b + z c = 0 then 1 else 0) = 1 := by
    simpa only [hd, contract_diagonal] using hone
  have hzero : contract u v w (fun a b c ↦ if x a + y b + z c = 0 then 1 else 0) = 0 := by
    simp_rw [indicator_expansion]
    rw [contract_sum]
    apply sum_eq_zero
    intro k _
    rw [contract_monomial]
    rcases lowDegree_cover k with h | h | h
    · simp [show (∑ i, u i * monomial (xExp ∘ k) (x i)) = 0 from hx ⟨_, h⟩]
    · simp [show (∑ i, v i * monomial (yExp ∘ k) (y i)) = 0 from hy ⟨_, h⟩]
    · simp [show (∑ i, w i * monomial (zExp ∘ k) (z i)) = 0 from hz ⟨_, h⟩]
  exact one_ne_zero (hone'.symm.trans hzero)

/-- Weight an exponent vector of degree d by r^(3d). Each low-degree vector has
weight at least r^(2n), while the sum of all weights factors by coordinate. -/
private lemma card_lowDegree (n : ℕ) : ((lowDegree n).card : ℝ) ≤ (14 / 5 : ℝ) ^ n := by
  let r : ℝ := 4 / 5
  have hr : 0 < r := by norm_num [r]
  let weight (e : Exponents n) := ∏ i, r ^ (3 * (e i).val)
  have hlow (e : Exponents n) (he : e ∈ lowDegree n) : r ^ (2 * n) ≤ weight e := by
    unfold weight
    rw [prod_pow_eq_pow_sum, ← mul_sum]
    exact pow_le_pow_of_le_one hr.le (by norm_num [r]) (mem_filter.mp he).2
  have hbound : ((lowDegree n).card : ℝ) * r ^ (2 * n) ≤ (1 + r ^ 3 + r ^ 6) ^ n := calc
    _ = ∑ _e ∈ lowDegree n, r ^ (2 * n) := by simp
    _ ≤ ∑ e ∈ lowDegree n, weight e := sum_le_sum hlow
    _ ≤ ∑ e, weight e := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun e _ _ ↦
      prod_nonneg fun i _ ↦ pow_nonneg hr.le _
    _ = _ := by
      unfold weight
      rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 3) ↦ r ^ (3 * j.val))]
      simp [Fin.sum_univ_three]
  rw [pow_mul] at hbound
  apply (le_of_mul_le_mul_right · (pow_pos (sq_pos_of_pos hr) n))
  refine hbound.trans ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by norm_num [r]) _

/-- **The multicolored sunflower conjecture holds.** There are a real number $\varepsilon > 0$ and a
natural number $n_0$ such that for every $n > n_0$, every finite set $S$ of triples $(x, y, z)$ of
vectors in $(\mathbb{Z}/3)^n$ with $x + y + z = 0$ for every $(x, y, z) \in S$ and with
$|S| \ge 3^{(1 - \varepsilon) n}$ contains a multicolored sunflower: triples
$(x_1, y_1, z_1), (x_2, y_2, z_2), (x_3, y_3, z_3) \in S$, not all three equal, with
$x_1 + y_2 + z_3 = 0$.

This was resolved in the affirmative: a set $S$ as above with no multicolored sunflower is a
tricolored sum-free set ($x_a + y_b + z_c = 0$ only for $a = b = c$), and Blasiak, Church, Cohn,
Grochow, Naslund, Sawin and Umans proved (Theorem A′) that such sets in $(\mathbb{Z}/3)^n$ have at
most $3 \cdot 3^{(1 - \delta/\log 3) n}$ elements, $\delta = 0.0566\ldots$; Alon, Shpilka and Umans
had shown that this tricolored version of the cap set bound disproves the strong USP conjecture.

Source: C. Umans, in Complexity Theory, Oberwolfach Reports 9 (2012), no. 54, p.
3292, Conjecture 7, DOI 10.4171/OWR/2012/54; resolution: J. Blasiak, T. Church, H. Cohn, J. A.
Grochow, E. Naslund, W. F. Sawin and C. Umans, On cap sets and the group-theoretic approach to
matrix multiplication, Discrete Anal. 2017:3, arXiv:1605.06702, Theorem A′: for H ≅ (ℤ/q)ⁿ, q a
prime power, every tricolored sum-free set in H (Definition 3.1) has at most 3 |H|^{1 - δ/log q}
elements, δ = 0.0566...; Section 1: Alon, Shpilka and Umans showed that a tricolored version of the
cap set bounds would disprove the strong USP conjecture (the source's Theorem 8), and Theorem A
disproves it via their result; Kleinberg, Sawin and Speyer, arXiv:1607.00047, abstract, restate the
bound as 3 θⁿ, θ ≈ 2.755, https://arxiv.org/abs/1605.06702.
-/
theorem multicoloredSunflowerConjecture_holds : multicoloredSunflowerConjecture := by
  classical
  refine ⟨1 - Real.logb 3 (29 / 10), sub_pos.mpr ?_, 56, ?_⟩
  · apply (Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)).mpr
    norm_num
  intro n hn S hsum hsize
  by_contra hfree
  have hd (a b c : S) : a.val.1 + b.val.2.1 + c.val.2.2 = 0 ↔ a = b ∧ b = c := by
    constructor
    · intro habc
      by_contra hne
      exact hfree ⟨a, a.prop, b, b.prop, c, c.prop, by simpa using hne, habc⟩
    · rintro ⟨rfl, rfl⟩
      exact hsum _ a.prop
  have hcard := card_le_of_diagonal _ _ _ hd
  rw [Fintype.card_coe] at hcard
  have hupper : (S.card : ℝ) ≤ 3 * (14 / 5 : ℝ) ^ n := by
    calc
      _ ≤ 3 * ((lowDegree n).card : ℝ) := by exact_mod_cast hcard
      _ ≤ _ := mul_le_mul_of_nonneg_left (card_lowDegree n) (by norm_num)
  rw [sub_sub_cancel, Real.rpow_mul_natCast (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)] at hsize
  have hn' : (56 : ℝ) < n := by exact_mod_cast hn
  have hratio : (3 : ℝ) < ((29 / 10) / (14 / 5)) ^ n := by
    apply lt_of_lt_of_le _ (one_add_mul_sub_le_pow (by norm_num) n)
    linarith
  rw [div_pow, lt_div_iff₀ (by positivity)] at hratio
  exact (not_lt_of_ge (hsize.trans hupper)) hratio

end MathlibExt.Combinatorics.MulticoloredSunflowerTernaryOWR12177Problem010Wanted
