/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination

/-!
# A reverse Littlewood–Offord problem (Erdős Problem 395)

Erdős Problem 395: if `z₁, …, zₙ ∈ ℂ` with `|zᵢ| = 1`, is the probability that `|ε₁z₁ + ⋯ + εₙzₙ| ≤
√2`, for independent uniform signs `εᵢ ∈ {-1, 1}`, at least `≫ 1/n`? The main result,
`reverseLittlewoodOffordSqrtTwo_holds`, answers it positively: one absolute constant `c > 0` works
for every `n ≥ 1` and all complex numbers `z₁, …, zₙ` of modulus `1`.

Source: T. F. Bloom, Erdős Problems, Problem #395, https://www.erdosproblems.com/395 (status PROVED
(LEAN)). UnsolvedMath record UM-30006851 (`EP-395`), dataset ulamai/UnsolvedMath v1.8.0.

The probability is the proportion of the `2ⁿ` sign vectors, encoded as `Fin n → Bool`; the constant
is absolute and `n ≥ 1`. Compared with the formal-conjectures statement `ErdosProblems/395.lean`
(equivalent; no code imported).

## Proof outline

The proof uses the pairing argument of X. He, T. Juškevičius, B. Narayanan and S. Spiro
(arXiv:2408.11034, Lemmas 2.2, 2.3 and 2.5) in counting form, and replaces the geometric case
analysis of their Section 3 by a correction step.

1. *Pairing.* If unit vectors `u₁, u₁', …, u_m, u_m'` satisfy `∑ ‖uⱼ - uⱼ'‖² ≤ 21/40`, then at
   least `4ᵐ / (38832 m)` of the `4ᵐ` sign vectors give a signed sum of norm at most `1`. A coupling
   of two independent signed sums of the averages `(uⱼ + uⱼ') / 2` with independent signs on the
   differences `uⱼ - uⱼ'` reduces this to a collision bound (Chebyshev's inequality and
   Cauchy–Schwarz over a grid of squares) and a second-moment bound for the differences.
2. *Correction.* For every point `w` of the closed disk of radius `√2` and all unit vectors
   `u, u'`, some signs give `‖w ± u ± u'‖ ≤ √2`; one unit vector brings the closed unit disk into
   that disk. So any finite family of unit vectors brings the unit disk into the `√2`-disk, and a
   sign vector of a subfamily with signed sum of norm at most `1` extends to a sign vector of the
   whole family with signed sum of norm at most `√2`.
3. *Choice of pairs.* Sorting the `zᵢ` by argument and pairing neighbours, the gaps between the
   arguments within the pairs add up to at most `2π`. At most `75` pairs have a gap of at least
   `1/12`, and the other pairs satisfy the hypothesis of step 1 because a chord of the unit circle
   is at most the difference of the arguments of its ends. Steps 1 and 2 give
   `c = 1 / (38832 · 2¹⁵¹)`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395Wanted

open Finset

/-- **Number of short signed sums.** For complex numbers $z_1, \dots, z_n$, this is the number of
sign vectors $(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ with
$|\varepsilon_1 z_1 + \dots + \varepsilon_n z_n| \le \sqrt{2}$. -/
noncomputable def smallSignedSumCount {n : ℕ} (z : Fin n → ℂ) : ℕ :=
  {ε : Fin n → Bool | ‖∑ i, (if ε i then (1 : ℂ) else -1) * z i‖ ≤ Real.sqrt 2}.ncard

/-- **Reverse Littlewood–Offord statement of Erdős Problem 395.** The statement that there is a
real constant $c > 0$ such that for every natural number $n \ge 1$ and all complex numbers
$z_1, \dots, z_n$ with $|z_i| = 1$ for every $i$, the number $N$ of sign vectors
$(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ with
$|\varepsilon_1 z_1 + \dots + \varepsilon_n z_n| \le \sqrt{2}$ satisfies $c/n \le N/2^n$. That is,
for independent uniformly random signs this inequality holds with probability at least $c/n$. -/
def reverseLittlewoodOffordSqrtTwo : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) →
    c / n ≤ (smallSignedSumCount z : ℝ) / 2 ^ n

/-- The sign `±1` attached to a Boolean, as a real number. -/
private def sgnR (b : Bool) : ℝ := if b then 1 else -1

/-- The sign `±1` attached to a Boolean, as a complex number, as in `smallSignedSumCount`. -/
private def sgnC (b : Bool) : ℂ := if b then 1 else -1

private lemma sgnR_mul_self (b : Bool) : sgnR b * sgnR b = 1 := by cases b <;> simp [sgnR]

/-- Orthogonality of the coordinate signs: summed over all sign vectors, the product of the
signs at `j` and `k` is `2 ^ card κ` if `j = k` and `0` otherwise. -/
private lemma sum_sgnR_mul_sgnR {κ : Type*} [Fintype κ] [DecidableEq κ] (j k : κ) :
    ∑ ε : κ → Bool, sgnR (ε j) * sgnR (ε k) = if j = k then (2 : ℝ) ^ Fintype.card κ else 0 := by
  split_ifs with hjk
  · subst hjk
    simp [sgnR_mul_self]
  · let e : (κ → Bool) ≃ (κ → Bool) :=
      { toFun := fun ε => Function.update ε j (!ε j)
        invFun := fun ε => Function.update ε j (!ε j)
        left_inv := fun ε => by ext i; by_cases h : i = j <;> simp [Function.update, h]
        right_inv := fun ε => by ext i; by_cases h : i = j <;> simp [Function.update, h] }
    have h1 := e.sum_comp (fun ε => sgnR (ε j) * sgnR (ε k))
    have h2 : ∀ ε : κ → Bool, sgnR (e ε j) * sgnR (e ε k) = -(sgnR (ε j) * sgnR (ε k)) := by
      intro ε
      have hkj : k ≠ j := Ne.symm hjk
      simp only [e, Equiv.coe_fn_mk, Function.update_self, Function.update_of_ne hkj]
      cases ε j <;> cases ε k <;> simp [sgnR]
    simp only [h2, Finset.sum_neg_distrib] at h1
    linarith

/-- Second moment of a real signed sum over all sign vectors. -/
private lemma sum_sq_sum_sgnR_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    ∑ ε : κ → Bool, (∑ j, sgnR (ε j) * a j) ^ 2 = 2 ^ Fintype.card κ * ∑ j, a j ^ 2 := by
  have : ∀ ε : κ → Bool, (∑ j, sgnR (ε j) * a j) ^ 2
      = ∑ j, ∑ k, (a j * a k) * (sgnR (ε j) * sgnR (ε k)) := by
    intro ε
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [this]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := κ → Bool) (s := Finset.univ) (t := Finset.univ), ← Finset.mul_sum,
    sum_sgnR_mul_sgnR]
  simp [Finset.mul_sum, sq, mul_comm]

/-- The squared norm of a complex number in coordinates. -/
private lemma norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- Second moment of a complex signed sum: summed over all sign vectors, `‖∑ ±xⱼ‖²` gives
`2 ^ card κ * ∑ ‖xⱼ‖²`. -/
private lemma sum_norm_sq_sum_sgnC_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ → ℂ) :
    ∑ ε : κ → Bool, ‖∑ j, sgnC (ε j) * x j‖ ^ 2 = 2 ^ Fintype.card κ * ∑ j, ‖x j‖ ^ 2 := by
  have hre : ∀ ε : κ → Bool, (∑ j, sgnC (ε j) * x j).re = ∑ j, sgnR (ε j) * (x j).re := by
    intro ε; rw [Complex.re_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    cases ε j <;> simp [sgnC, sgnR]
  have him : ∀ ε : κ → Bool, (∑ j, sgnC (ε j) * x j).im = ∑ j, sgnR (ε j) * (x j).im := by
    intro ε; rw [Complex.im_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    cases ε j <;> simp [sgnC, sgnR]
  simp_rw [norm_sq_eq_re_im, hre, him, Finset.sum_add_distrib, sum_sq_sum_sgnR_mul, ← mul_add]

/-- Markov's inequality in counting form. -/
private lemma card_sub_sum_div_le_card_filter {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (c : ℝ) (hc : 0 < c) :
    (Fintype.card α : ℝ) - (∑ x, f x) / c ≤ ((univ.filter fun x => f x ≤ c).card : ℝ) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun x => f x ≤ c)
  have h2 : ((univ.filter fun x => ¬ f x ≤ c).card : ℝ) * c ≤ ∑ x, f x := by
    calc ((univ.filter fun x => ¬ f x ≤ c).card : ℝ) * c
        = ∑ x ∈ univ.filter (fun x => ¬ f x ≤ c), c := by simp [mul_comm]
      _ ≤ ∑ x ∈ univ.filter (fun x => ¬ f x ≤ c), f x :=
          Finset.sum_le_sum fun x hx => by simp only [mem_filter] at hx; linarith [hx.2]
      _ ≤ ∑ x, f x :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x _ _ => hf x)
  have h3 : ((univ.filter fun x => ¬ f x ≤ c).card : ℝ) ≤ (∑ x, f x) / c := by
    rw [le_div_iff₀ hc]; exact h2
  have h4 : ((univ.filter fun x => f x ≤ c).card : ℝ)
      + ((univ.filter fun x => ¬ f x ≤ c).card : ℝ) = Fintype.card α := by
    exact_mod_cast h1
  linarith

/-- **Collision bound** (Lemma 2.3 of He, Juškevičius, Narayanan and Spiro, through Chebyshev's
inequality and Cauchy–Schwarz over a grid of squares of side `s`). For vectors of norm at most `1`
and `√(2m) ≤ M s`, two signed sums lie within `2 s` of each other for at least a
`1 / (4 (2M + 1)²)` fraction of the pairs of sign vectors. -/
private lemma collision_count_ge {κ : Type*} [Fintype κ] [DecidableEq κ] (W : κ → ℂ)
    (hW : ∀ j, ‖W j‖ ≤ 1)
    (hm : 0 < Fintype.card κ) (s : ℝ) (hs : 0 < s) (M : ℕ)
    (hM : √(2 * Fintype.card κ) ≤ M * s) :
    (4 : ℝ) ^ Fintype.card κ / (4 * (2 * M + 1) ^ 2) ≤
    ((univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
        ‖∑ j, sgnC (ηη.1 j) * W j - ∑ j, sgnC (ηη.2 j) * W j‖ < 2 * s).card : ℝ) := by
  set m := Fintype.card κ with hmdef
  set σ : (κ → Bool) → ℂ := fun η => ∑ j, sgnC (η j) * W j with hσ
  set A := univ.filter fun η : κ → Bool => ‖σ η‖ ^ 2 ≤ 2 * m with hA
  have hA2 : (2 : ℝ) ^ m ≤ 2 * A.card := by
    have h := card_sub_sum_div_le_card_filter (fun η => ‖σ η‖ ^ 2) (fun _ => by positivity)
      (2 * m) (by positivity)
    have hsum : ∑ η, ‖σ η‖ ^ 2 = 2 ^ m * ∑ j, ‖W j‖ ^ 2 := sum_norm_sq_sum_sgnC_mul W
    have hW2 : ∑ j, ‖W j‖ ^ 2 ≤ m := by
      calc ∑ j, ‖W j‖ ^ 2 ≤ ∑ _j : κ, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => by
              have := hW j; have := norm_nonneg (W j); nlinarith
        _ = m := by simp [hmdef]
    have hcard : (Fintype.card (κ → Bool) : ℝ) = 2 ^ m := by simp [hmdef]
    rw [hcard, hsum] at h
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have : ((2 : ℝ) ^ m * ∑ j, ‖W j‖ ^ 2) / (2 * m) ≤ 2 ^ m / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h2m : (0 : ℝ) < 2 ^ m := by positivity
      nlinarith
    have hAeq : A = univ.filter fun η : κ → Bool => ‖σ η‖ ^ 2 ≤ 2 * m := rfl
    rw [← hAeq] at h
    linarith
  set cell : (κ → Bool) → ℤ × ℤ := fun η => (⌊(σ η).re / s⌋, ⌊(σ η).im / s⌋) with hcell
  set K : Finset (ℤ × ℤ) := (Icc (-(M : ℤ)) M) ×ˢ (Icc (-(M : ℤ)) M) with hK
  have hKcard : (K.card : ℝ) = (2 * M + 1) ^ 2 := by
    simp only [hK, card_product, Int.card_Icc]
    push_cast
    have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [this]; push_cast; ring
  have hbound : ∀ x : ℝ, |x| ≤ M * s → ⌊x / s⌋ ∈ Icc (-(M : ℤ)) M := by
    intro x hx
    rw [abs_le] at hx
    simp only [mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast
      rw [le_div_iff₀ hs]; linarith
    · have : ⌊x / s⌋ ≤ x / s := Int.floor_le _
      have h2 : x / s ≤ M := by rw [div_le_iff₀ hs]; linarith
      exact_mod_cast this.trans h2
  have hmaps : Set.MapsTo cell A K := by
    intro η hη
    simp only [hA, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hη
    have hn : ‖σ η‖ ≤ M * s := by
      have : ‖σ η‖ ≤ √(2 * m) := Real.le_sqrt_of_sq_le hη
      linarith
    simp only [hK, coe_product, Set.mem_prod, mem_coe]
    exact ⟨hbound _ ((Complex.abs_re_le_norm _).trans hn),
      hbound _ ((Complex.abs_im_le_norm _).trans hn)⟩
  have hclose : ∀ η η', cell η = cell η' → ‖σ η - σ η'‖ < 2 * s := by
    intro η η' h
    simp only [hcell, Prod.mk.injEq] at h
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h.1
    have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h.2
    rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs] at h1 h2
    have hsq : ‖σ η - σ η'‖ ^ 2 < (2 * s) ^ 2 := by
      rw [norm_sq_eq_re_im, Complex.sub_re, Complex.sub_im]
      have := sq_abs ((σ η).re - (σ η').re)
      have := sq_abs ((σ η).im - (σ η').im)
      have := abs_nonneg ((σ η).re - (σ η').re)
      have := abs_nonneg ((σ η).im - (σ η').im)
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  set P := (A ×ˢ A).filter (fun p => cell p.1 = cell p.2) with hP
  have hsub : P ⊆ univ.filter (fun ηη : (κ → Bool) × (κ → Bool) =>
      ‖∑ j, sgnC (ηη.1 j) * W j - ∑ j, sgnC (ηη.2 j) * W j‖ < 2 * s) := by
    intro p hp
    simp only [hP, mem_filter] at hp
    simp only [mem_filter, mem_univ, true_and]
    exact hclose _ _ hp.2
  have hcount : P.card = ∑ k ∈ K, (A.filter (fun η => cell η = k)).card ^ 2 := by
    have hm2 : Set.MapsTo (fun p : (κ → Bool) × (κ → Bool) => cell p.1) P K := by
      intro p hp
      simp only [hP, coe_filter, mem_product, Set.mem_ofPred_eq] at hp
      exact hmaps hp.1.1
    rw [card_eq_sum_card_fiberwise hm2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : P.filter (fun p => cell p.1 = k)
        = (A.filter (fun η => cell η = k)) ×ˢ (A.filter (fun η => cell η = k)) := by
      ext ⟨η, η'⟩
      simp only [hP, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨⟨h1, h4⟩, ⟨h2, h3 ▸ h4⟩⟩
      · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩⟩
        exact ⟨⟨⟨h1, h2⟩, h4.trans h5.symm⟩, h4⟩
    rw [this, card_product, sq]
  have hsumA : A.card = ∑ k ∈ K, (A.filter (fun η => cell η = k)).card :=
    card_eq_sum_card_fiberwise hmaps
  have hCS := sq_sum_le_card_mul_sum_sq (s := K)
    (f := fun k => ((A.filter (fun η => cell η = k)).card : ℝ))
  have hAr : (A.card : ℝ) = ∑ k ∈ K, ((A.filter (fun η => cell η = k)).card : ℝ) := by
    exact_mod_cast hsumA
  have hPr : (P.card : ℝ) = ∑ k ∈ K, ((A.filter (fun η => cell η = k)).card : ℝ) ^ 2 := by
    exact_mod_cast hcount
  rw [← hAr, ← hPr, hKcard] at hCS
  have hPle : (P.card : ℝ) ≤ ((univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
      ‖∑ j, sgnC (ηη.1 j) * W j - ∑ j, sgnC (ηη.2 j) * W j‖ < 2 * s).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  refine le_trans ?_ hPle
  have hpos : (0 : ℝ) < (2 * M + 1) ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have h4 : (4 : ℝ) ^ m = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  have h0 : (0 : ℝ) ≤ 2 ^ m := by positivity
  nlinarith

/-- One coordinate of the coupling in `pairing_count_ge`: the signed sum of a pair `u, u'`
splits into a difference of signed averages and a signed difference. -/
private lemma pair_coord_sum (a a' c : Bool) (u u' : ℂ) :
    sgnC (if a = a' then c else a) * u + sgnC (if a = a' then !c else a) * u'
      = (sgnC a * ((u + u') / 2) - sgnC a' * ((u + u') / 2))
        + sgnC c * (if a = a' then u - u' else 0) := by
  cases a <;> cases a' <;> cases c <;> simp [sgnC] <;> ring

/-- The coupling in `pairing_count_ge` is injective in each coordinate. -/
private lemma pair_coord_inj : ∀ a a' c b b' d : Bool,
    (if a = a' then c else a) = (if b = b' then d else b) →
    (if a = a' then !c else a) = (if b = b' then !d else b) →
    (if a = a' then a else c) = (if b = b' then b else d) →
    a = b ∧ a' = b' ∧ c = d := by decide

/-- **Pairing lemma** (Lemmas 2.2 and 2.5 of He, Juškevičius, Narayanan and Spiro, in counting
form). The number of sign vectors of the family `u₁, …, u_m, u₁', …, u_m'` with signed sum of norm
at most `a + b` is at least `1 - ∑ ‖uⱼ - uⱼ'‖² / b²` times the number of pairs of sign vectors whose
signed sums of the averages `(uⱼ + uⱼ') / 2` lie within `a` of each other. -/
private lemma pairing_count_ge {κ : Type*} [Fintype κ] [DecidableEq κ] (u u' : κ → ℂ) (a b : ℝ)
    (hb : 0 < b) :
    ((univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
        ‖∑ j, sgnC (ηη.1 j) * ((u j + u' j) / 2) - ∑ j, sgnC (ηη.2 j) * ((u j + u' j) / 2)‖
          ≤ a).card : ℝ) * (1 - (∑ j, ‖u j - u' j‖ ^ 2) / b ^ 2)
    ≤ ((univ.filter fun ε : κ ⊕ κ → Bool =>
        ‖∑ i, sgnC (ε i) * Sum.elim u u' i‖ ≤ a + b).card : ℝ) := by
  set m := Fintype.card κ with hmdef
  set W : κ → ℂ := fun j => (u j + u' j) / 2 with hW
  set D := ∑ j, ‖u j - u' j‖ ^ 2 with hD
  set C := univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
    ‖∑ j, sgnC (ηη.1 j) * W j - ∑ j, sgnC (ηη.2 j) * W j‖ ≤ a with hC
  set T := univ.filter fun ε : κ ⊕ κ → Bool => ‖∑ i, sgnC (ε i) * Sum.elim u u' i‖ ≤ a + b
    with hT
  set x : (κ → Bool) × (κ → Bool) → κ → ℂ :=
    fun q j => if q.1 j = q.2 j then u j - u' j else 0 with hx
  set tau : (κ → Bool) × (κ → Bool) → (κ → Bool) → ℂ :=
    fun q ζ => ∑ j, sgnC (ζ j) * x q j with htau
  set S3 : ((κ → Bool) × (κ → Bool)) × (κ → Bool) → ℂ := fun p =>
    (∑ j, sgnC (p.1.1 j) * W j - ∑ j, sgnC (p.1.2 j) * W j) + tau p.1 p.2 with hS3
  set TT := univ.filter fun p : ((κ → Bool) × (κ → Bool)) × (κ → Bool) => ‖S3 p‖ ≤ a + b
    with hTT
  set Ψ : ((κ → Bool) × (κ → Bool)) × (κ → Bool) → (κ ⊕ κ → Bool) × (κ → Bool) := fun p =>
    (Sum.elim (fun j => if p.1.1 j = p.1.2 j then p.2 j else p.1.1 j)
              (fun j => if p.1.1 j = p.1.2 j then !p.2 j else p.1.1 j),
     fun j => if p.1.1 j = p.1.2 j then p.1.1 j else p.2 j) with hΨ
  have hΨsum : ∀ p, ∑ i, sgnC ((Ψ p).1 i) * Sum.elim u u' i = S3 p := by
    intro p
    rw [Fintype.sum_sum_type]
    simp only [hΨ, Sum.elim_inl, Sum.elim_inr, hS3, htau, hx, hW]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => pair_coord_sum _ _ _ _ _
  -- The coupling is injective, so there are at most `2 ^ m` times as many good triples as
  -- good sign vectors of the family.
  have hi : TT.card ≤ (T ×ˢ (univ : Finset (κ → Bool))).card := by
    refine card_le_card_of_injOn Ψ ?_ ?_
    · intro p hp
      simp only [hTT, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
      simp only [hT, coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, coe_univ,
        Set.mem_univ, and_true, Set.mem_ofPred_eq]
      rw [hΨsum]; exact hp
    · rintro ⟨⟨η, η'⟩, ζ⟩ _ ⟨⟨θ, θ'⟩, ξ⟩ _ h
      simp only [hΨ, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have key : ∀ j, η j = θ j ∧ η' j = θ' j ∧ ζ j = ξ j := by
        intro j
        have e1 := congrFun h1 (Sum.inl j)
        have e2 := congrFun h1 (Sum.inr j)
        have e3 := congrFun h2 j
        simp only [Sum.elim_inl, Sum.elim_inr] at e1 e2
        exact pair_coord_inj _ _ _ _ _ _ e1 e2 e3
      simp only [Prod.mk.injEq]
      exact ⟨⟨funext fun j => (key j).1, funext fun j => (key j).2.1⟩,
        funext fun j => (key j).2.2⟩
  have hiR : (TT.card : ℝ) ≤ T.card * 2 ^ m := by
    have := hi
    rw [card_product, card_univ, Fintype.card_fun, Fintype.card_bool] at this
    exact_mod_cast this
  -- For each pair of sign vectors, Markov's inequality for the signs on the differences.
  have hmark : ∀ q, (2 : ℝ) ^ m * (1 - D / b ^ 2)
      ≤ ((univ.filter fun ζ : κ → Bool => ‖tau q ζ‖ ≤ b).card : ℝ) := by
    intro q
    have h := card_sub_sum_div_le_card_filter (fun ζ => ‖tau q ζ‖ ^ 2) (fun _ => by positivity)
      (b ^ 2) (by positivity)
    have hsum : ∑ ζ, ‖tau q ζ‖ ^ 2 = 2 ^ m * ∑ j, ‖x q j‖ ^ 2 := sum_norm_sq_sum_sgnC_mul (x q)
    have hxD : ∑ j, ‖x q j‖ ^ 2 ≤ D := by
      refine Finset.sum_le_sum fun j _ => ?_
      simp only [hx]
      split_ifs <;> simp
    have hcard : (Fintype.card (κ → Bool) : ℝ) = 2 ^ m := by simp [hmdef]
    have hset : (univ.filter fun ζ : κ → Bool => ‖tau q ζ‖ ^ 2 ≤ b ^ 2)
        = univ.filter fun ζ : κ → Bool => ‖tau q ζ‖ ≤ b := by
      ext ζ
      simp only [mem_filter, mem_univ, true_and]
      exact sq_le_sq₀ (norm_nonneg _) hb.le
    rw [hcard, hsum, hset] at h
    have h2 : ((2 : ℝ) ^ m * ∑ j, ‖x q j‖ ^ 2) / b ^ 2 ≤ 2 ^ m * D / b ^ 2 := by
      gcongr
    have h3 : (2 : ℝ) ^ m * (1 - D / b ^ 2) = 2 ^ m - 2 ^ m * D / b ^ 2 := by ring
    rw [h3]
    linarith
  -- Split the count of good triples over the pairs of sign vectors.
  have hii : (C.card : ℝ) * (2 ^ m * (1 - D / b ^ 2)) ≤ TT.card := by
    have hTTsum : (TT.card : ℝ) = ∑ q : (κ → Bool) × (κ → Bool),
        ∑ ζ : κ → Bool, (if ‖S3 (q, ζ)‖ ≤ a + b then (1 : ℝ) else 0) := by
      rw [hTT, card_filter]
      push_cast
      rw [Fintype.sum_prod_type]
    rw [hTTsum]
    calc (C.card : ℝ) * (2 ^ m * (1 - D / b ^ 2))
        = ∑ q ∈ C, (2 : ℝ) ^ m * (1 - D / b ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ C, ((univ.filter fun ζ : κ → Bool => ‖tau q ζ‖ ≤ b).card : ℝ) :=
          Finset.sum_le_sum fun q _ => hmark q
      _ = ∑ q ∈ C, ∑ ζ : κ → Bool, (if ‖tau q ζ‖ ≤ b then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [card_filter]; push_cast; rfl
      _ ≤ ∑ q ∈ C, ∑ ζ : κ → Bool, (if ‖S3 (q, ζ)‖ ≤ a + b then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun ζ _ => ?_
          simp only [hC, mem_filter, mem_univ, true_and] at hq
          by_cases h : ‖tau q ζ‖ ≤ b
          · have : ‖S3 (q, ζ)‖ ≤ a + b := by
              simp only [hS3]
              exact (norm_add_le _ _).trans (add_le_add hq h)
            simp [h, this]
          · simp only [h, ite_false]
            split_ifs <;> norm_num
      _ ≤ ∑ q : (κ → Bool) × (κ → Bool),
            ∑ ζ : κ → Bool, (if ‖S3 (q, ζ)‖ ≤ a + b then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun q _ _ => ?_
          exact Finset.sum_nonneg fun ζ _ => by split_ifs <;> norm_num
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have := hii.trans hiR
  have h5 : (C.card : ℝ) * (1 - D / b ^ 2) * 2 ^ m ≤ T.card * 2 ^ m := by linarith
  exact le_of_mul_le_mul_right h5 h2m

/-- The inequality behind `exists_two_signs_le_sqrt_two`, in terms of `p = ‖u + u'‖²`,
`q = ‖u - u'‖²`, `P = ⟪w, u + u'⟫`, `Q = ⟪w, u - u'⟫` and `δ = 2 - ‖w‖²`. -/
private lemma two_signs_core (pp qq P Q δ : ℝ) (hid : qq * P ^ 2 + pp * Q ^ 2 = pp * qq * (2 - δ))
    (hsum : pp + qq = 4) (hδ0 : 0 ≤ δ) (e1 : 0 < pp - δ + 2 * P) (e2 : 0 < pp - δ - 2 * P)
    (e3 : 0 < qq - δ + 2 * Q) (e4 : 0 < qq - δ - 2 * Q) : False := by
  have f1 : 0 < (pp - δ) ^ 2 - 4 * P ^ 2 := by nlinarith [mul_pos e1 e2]
  have f2 : 0 < (qq - δ) ^ 2 - 4 * Q ^ 2 := by nlinarith [mul_pos e3 e4]
  have hp0 : 0 < pp := by linarith
  have hq0 : 0 < qq := by linarith
  have g : 0 < qq * ((pp - δ) ^ 2 - 4 * P ^ 2) + pp * ((qq - δ) ^ 2 - 4 * Q ^ 2) := by
    have := mul_pos hq0 f1
    have := mul_pos hp0 f2
    linarith
  have g2 : qq * ((pp - δ) ^ 2 - 4 * P ^ 2) + pp * ((qq - δ) ^ 2 - 4 * Q ^ 2)
      = 4 * δ ^ 2 - 4 * pp * qq := by
    have : qq * ((pp - δ) ^ 2 - 4 * P ^ 2) + pp * ((qq - δ) ^ 2 - 4 * Q ^ 2)
        = pp * qq * (pp + qq) - 4 * pp * qq * δ + (pp + qq) * δ ^ 2
          - 4 * (qq * P ^ 2 + pp * Q ^ 2) := by ring
    rw [this, hid, hsum]; ring
  have k1 := mul_pos (show 0 < pp - δ by linarith) hq0
  have k2 := mul_nonneg hδ0 (show 0 ≤ qq - δ by linarith)
  have g3 : 0 < pp * qq - δ ^ 2 := by nlinarith
  linarith

/-- The inequality behind `exists_two_signs_le_sqrt_two`, in coordinates, with `A = u + u'` and
`B = u - u'`. -/
private lemma two_signs_coords (x y A1 A2 B1 B2 : ℝ) (hAB : A1 * B1 + A2 * B2 = 0)
    (hpq : A1 ^ 2 + A2 ^ 2 + (B1 ^ 2 + B2 ^ 2) = 4) (hw : x ^ 2 + y ^ 2 ≤ 2)
    (h1 : 2 < (x + A1) ^ 2 + (y + A2) ^ 2) (h2 : 2 < (x - A1) ^ 2 + (y - A2) ^ 2)
    (h3 : 2 < (x + B1) ^ 2 + (y + B2) ^ 2) (h4 : 2 < (x - B1) ^ 2 + (y - B2) ^ 2) : False := by
  have hid : (B1 ^ 2 + B2 ^ 2) * (x * A1 + y * A2) ^ 2 + (A1 ^ 2 + A2 ^ 2) * (x * B1 + y * B2) ^ 2
      = (A1 ^ 2 + A2 ^ 2) * (B1 ^ 2 + B2 ^ 2) * (2 - (2 - (x ^ 2 + y ^ 2))) := by
    linear_combination (2 * (x * A1 + y * A2) * (x * B1 + y * B2)
      - (A1 * B1 + A2 * B2) * (x ^ 2 + y ^ 2)) * hAB
  exact two_signs_core (A1 ^ 2 + A2 ^ 2) (B1 ^ 2 + B2 ^ 2) (x * A1 + y * A2) (x * B1 + y * B2)
    (2 - (x ^ 2 + y ^ 2)) hid hpq (by linarith) (by nlinarith) (by nlinarith) (by nlinarith)
    (by nlinarith)

/-- A complex number of norm greater than `√2` has squared coordinates adding up to more than
`2`. -/
private lemma two_lt_re_sq_add_im_sq {z : ℂ} (h : √2 < ‖z‖) : 2 < z.re ^ 2 + z.im ^ 2 := by
  have h0 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have h1 : (√2) ^ 2 < ‖z‖ ^ 2 := by gcongr
  rw [Real.sq_sqrt (by norm_num), Complex.sq_norm, Complex.normSq_apply] at h1
  nlinarith

/-- Two unit vectors bring the `√2`-disk back into itself. -/
private lemma exists_two_signs_le_sqrt_two (u u' w : ℂ) (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hw : ‖w‖ ≤ √2) :
    ∃ a b : Bool, ‖w + sgnC a * u + sgnC b * u'‖ ≤ √2 := by
  by_contra hcon
  push Not at hcon
  have h1 := two_lt_re_sq_add_im_sq (hcon true true)
  have h2 := two_lt_re_sq_add_im_sq (hcon false false)
  have h3 := two_lt_re_sq_add_im_sq (hcon true false)
  have h4 := two_lt_re_sq_add_im_sq (hcon false true)
  have hu2 := norm_sq_eq_re_im u
  have hu2' := norm_sq_eq_re_im u'
  rw [hu] at hu2
  rw [hu'] at hu2'
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 2 := by
    rw [← norm_sq_eq_re_im]
    have := pow_le_pow_left₀ (norm_nonneg w) hw 2
    rwa [Real.sq_sqrt (by norm_num)] at this
  simp only [sgnC, ↓reduceIte, Bool.false_eq_true, one_mul, neg_one_mul, Complex.add_re,
    Complex.add_im, Complex.neg_re, Complex.neg_im] at h1 h2 h3 h4
  exact two_signs_coords w.re w.im (u.re + u'.re) (u.im + u'.im) (u.re - u'.re) (u.im - u'.im)
    (by nlinarith) (by nlinarith) hw2 (by linarith) (by linarith) (by linarith) (by linarith)

/-- One unit vector brings the unit disk into the `√2`-disk. -/
private lemma exists_sign_le_sqrt_two (u w : ℂ) (hu : ‖u‖ = 1) (hw : ‖w‖ ≤ 1) :
    ∃ a : Bool, ‖w + sgnC a * u‖ ≤ √2 := by
  by_contra hcon
  push Not at hcon
  have h1 := two_lt_re_sq_add_im_sq (hcon true)
  have h2 := two_lt_re_sq_add_im_sq (hcon false)
  have hu2 := norm_sq_eq_re_im u
  rw [hu] at hu2
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    rw [← norm_sq_eq_re_im]
    have := pow_le_pow_left₀ (norm_nonneg w) hw 2
    simpa using this
  simp only [sgnC, ↓reduceIte, Bool.false_eq_true, one_mul, neg_one_mul, Complex.add_re,
    Complex.add_im, Complex.neg_re, Complex.neg_im] at h1 h2
  nlinarith

/-- Any finite family of unit vectors brings the unit disk into the `√2`-disk. -/
private lemma exists_signs_le_sqrt_two {ι : Type*} (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (s : Finset ι) :
    ∀ w : ℂ, ‖w‖ ≤ 1 → ∃ δ : ι → Bool, ‖w + ∑ i ∈ s, sgnC (δ i) * z i‖ ≤ √2 := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro w hw
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · refine ⟨fun _ => true, ?_⟩
      simp only [Finset.sum_empty, add_zero]
      exact hw.trans (by rw [Real.one_le_sqrt]; norm_num)
    · by_cases hs : (s.erase a).Nonempty
      · obtain ⟨b, hb⟩ := hs
        have hba : b ≠ a := Finset.ne_of_mem_erase hb
        set s' := (s.erase a).erase b
        have hss : s' ⊂ s := by
          refine lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset ha)
        obtain ⟨δ, hδ⟩ := ih s' hss w hw
        obtain ⟨α, β, hαβ⟩ := exists_two_signs_le_sqrt_two (z a) (z b)
          (w + ∑ i ∈ s', sgnC (δ i) * z i) (hz a) (hz b) hδ
        refine ⟨Function.update (Function.update δ a α) b β, ?_⟩
        rw [← Finset.add_sum_erase s _ ha, ← Finset.add_sum_erase (s.erase a) _ hb]
        have hsum : ∑ i ∈ s', sgnC (Function.update (Function.update δ a α) b β i) * z i
            = ∑ i ∈ s', sgnC (δ i) * z i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hib : i ≠ b := Finset.ne_of_mem_erase hi
          have hia : i ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
          rw [Function.update_of_ne hib, Function.update_of_ne hia]
        rw [hsum, Function.update_of_ne hba.symm, Function.update_self, Function.update_self]
        convert hαβ using 1
        ring_nf
      · have hsa : s = {a} := by
          rw [Finset.not_nonempty_iff_eq_empty] at hs
          rw [← Finset.insert_erase ha, hs]; rfl
        obtain ⟨α, hα⟩ := exists_sign_le_sqrt_two (z a) w (hz a) hw
        refine ⟨fun _ => α, ?_⟩
        simpa [hsa] using hα

/-- A good sign vector for a subfamily extends to the whole family. -/
private lemma card_le_card_extend {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (f : κ → ι) (hf : Function.Injective f) :
    (univ.filter fun ε : κ → Bool => ‖∑ k, sgnC (ε k) * z (f k)‖ ≤ 1).card ≤
    (univ.filter fun ε : ι → Bool => ‖∑ i, sgnC (ε i) * z i‖ ≤ √2).card := by
  set s : Finset ι := (univ.map ⟨f, hf⟩)ᶜ with hs
  have hc := exists_signs_le_sqrt_two z hz s
  have hex : ∀ w : ℂ, ∃ δ : ι → Bool, ‖w‖ ≤ 1 → ‖w + ∑ i ∈ s, sgnC (δ i) * z i‖ ≤ √2 := by
    intro w
    by_cases hw : ‖w‖ ≤ 1
    · obtain ⟨δ, hδ⟩ := hc w hw
      exact ⟨δ, fun _ => hδ⟩
    · exact ⟨fun _ => true, fun h => absurd h hw⟩
  choose Dfun hD using hex
  set E : (κ → Bool) → (ι → Bool) := fun ε =>
    Function.extend f ε (Dfun (∑ k, sgnC (ε k) * z (f k))) with hE
  have hEf : ∀ ε k, E ε (f k) = ε k := fun ε k => hf.extend_apply _ _ _
  have hEs : ∀ ε, ∀ i ∈ s, E ε i = Dfun (∑ k, sgnC (ε k) * z (f k)) i := by
    intro ε i hi
    simp only [hs, mem_compl, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk,
      not_exists] at hi
    exact Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ => hi k hk)
  refine card_le_card_of_injOn E ?_ ?_
  · intro ε hε
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hε ⊢
    set w := ∑ k, sgnC (ε k) * z (f k) with hw
    have h1 : ∑ i ∈ s, sgnC (E ε i) * z i = ∑ i ∈ s, sgnC (Dfun w i) * z i :=
      Finset.sum_congr rfl fun i hi => by rw [hEs ε i hi]
    have h2 : ∑ i ∈ univ.map ⟨f, hf⟩, sgnC (E ε i) * z i = w := by
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, hEf, hw]
    calc ‖∑ i, sgnC (E ε i) * z i‖ = ‖w + ∑ i ∈ s, sgnC (Dfun w i) * z i‖ := by
          rw [← Finset.sum_compl_add_sum (univ.map ⟨f, hf⟩), ← hs, h1, h2, add_comm]
      _ ≤ √2 := hD w hε
  · intro ε _ ε' _ h
    funext k
    have := congrFun h (f k)
    rwa [hEf, hEf] at this

/-- A chord of the unit circle is at most the difference of the arguments of its ends. -/
private lemma norm_sub_sq_le_arg_sub_sq (p q : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖p - q‖ ^ 2 ≤ (Complex.arg p - Complex.arg q) ^ 2 := by
  have hpr : p.re = Real.cos (Complex.arg p) := by
    have := Complex.norm_mul_cos_arg p; rw [hp, one_mul] at this; exact this.symm
  have hpi : p.im = Real.sin (Complex.arg p) := by
    have := Complex.norm_mul_sin_arg p; rw [hp, one_mul] at this; exact this.symm
  have hqr : q.re = Real.cos (Complex.arg q) := by
    have := Complex.norm_mul_cos_arg q; rw [hq, one_mul] at this; exact this.symm
  have hqi : q.im = Real.sin (Complex.arg q) := by
    have := Complex.norm_mul_sin_arg q; rw [hq, one_mul] at this; exact this.symm
  rw [norm_sq_eq_re_im, Complex.sub_re, Complex.sub_im, hpr, hpi, hqr, hqi]
  have hc := Real.one_sub_sq_div_two_le_cos (x := Complex.arg p - Complex.arg q)
  rw [Real.cos_sub] at hc
  have h1 := Real.sin_sq_add_cos_sq (Complex.arg p)
  have h2 := Real.sin_sq_add_cos_sq (Complex.arg q)
  nlinarith

/-- For a monotone sequence, the increments over the pairs `(2j, 2j + 1)` add up to at most
the total increment. -/
private lemma sum_range_odd_sub_even_le (T : ℕ → ℝ) (hT : Monotone T) (m : ℕ) :
    ∑ j ∈ range m, (T (2 * j + 1) - T (2 * j)) ≤ T (2 * m) - T 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h1 : T (2 * m + 1) ≤ T (2 * (m + 1)) := hT (by omega)
    linarith

/-- The pairing lemma with explicit constants: if `∑ ‖uⱼ - uⱼ'‖² ≤ 21/40`, at least
`4ᵐ / (38832 m)` sign vectors of the family `u₁, …, u_m, u₁', …, u_m'` give a signed sum of norm at
most `1`. -/
private lemma pair_count_ge {κ : Type*} [Fintype κ] [DecidableEq κ] (u u' : κ → ℂ)
    (hu : ∀ j, ‖u j‖ = 1) (hu' : ∀ j, ‖u' j‖ = 1) (hm : 0 < Fintype.card κ)
    (hD : ∑ j, ‖u j - u' j‖ ^ 2 ≤ 21 / 40) :
    (4 : ℝ) ^ Fintype.card κ / (38832 * Fintype.card κ) ≤
    ((univ.filter fun ε : κ ⊕ κ → Bool => ‖∑ i, sgnC (ε i) * Sum.elim u u' i‖ ≤ 1).card : ℝ) := by
  set m := Fintype.card κ with hmdef
  have hW : ∀ j, ‖(u j + u' j) / 2‖ ≤ 1 := by
    intro j
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le (u j) (u' j)
    rw [hu, hu'] at this
    linarith
  set M := ⌈√(2 * (m : ℝ)) / (1 / 10)⌉₊ with hMdef
  have hM : √(2 * (m : ℝ)) ≤ M * (1 / 10) := by
    have := Nat.le_ceil (√(2 * (m : ℝ)) / (1 / 10))
    rw [← hMdef] at this
    linarith
  have hM2 : (M : ℝ) < √(2 * (m : ℝ)) / (1 / 10) + 1 := by
    rw [hMdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hcoll := collision_count_ge (fun j => (u j + u' j) / 2) hW hm (1 / 10) (by norm_num) M hM
  have hpair := pairing_count_ge u u' (1 / 5) (4 / 5) (by norm_num)
  have hsub : (univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
        ‖∑ j, sgnC (ηη.1 j) * ((u j + u' j) / 2) - ∑ j, sgnC (ηη.2 j) * ((u j + u' j) / 2)‖
          < 2 * (1 / 10))
      ⊆ (univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
        ‖∑ j, sgnC (ηη.1 j) * ((u j + u' j) / 2) - ∑ j, sgnC (ηη.2 j) * ((u j + u' j) / 2)‖
          ≤ 1 / 5) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    linarith
  have hsubR := card_le_card hsub
  have hab : (1 : ℝ) / 5 + 4 / 5 = 1 := by norm_num
  rw [hab] at hpair
  have hfac : (1 : ℝ) / 6 ≤ 1 - (∑ j, ‖u j - u' j‖ ^ 2) / (4 / 5) ^ 2 := by
    have : (∑ j, ‖u j - u' j‖ ^ 2) / (4 / 5) ^ 2 ≤ (21 / 40) / (4 / 5) ^ 2 := by gcongr
    linarith
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : (2 * (M : ℝ) + 1) ^ 2 ≤ 1618 * m := by
    have hs0 : 0 ≤ √(2 * (m : ℝ)) := Real.sqrt_nonneg _
    have hs2 : √(2 * (m : ℝ)) ^ 2 = 2 * m := Real.sq_sqrt (by positivity)
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hle : 2 * (M : ℝ) + 1 ≤ 20 * √(2 * (m : ℝ)) + 3 := by
      have : √(2 * (m : ℝ)) / (1 / 10) = 10 * √(2 * (m : ℝ)) := by ring
      linarith
    have h0 : 0 ≤ 2 * (M : ℝ) + 1 := by positivity
    nlinarith [sq_nonneg (20 * √(2 * (m : ℝ)) - 3)]
  have hC : (4 : ℝ) ^ m / (4 * (2 * M + 1) ^ 2) ≤
      ((univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
        ‖∑ j, sgnC (ηη.1 j) * ((u j + u' j) / 2) - ∑ j, sgnC (ηη.2 j) * ((u j + u' j) / 2)‖
          ≤ 1 / 5).card : ℝ) := by
    refine hcoll.trans ?_
    exact_mod_cast hsubR
  have h4 : (4 : ℝ) ^ m / (38832 * m) ≤ (1 / 6) * ((4 : ℝ) ^ m / (4 * (2 * M + 1) ^ 2)) := by
    have hpos : (0 : ℝ) < 4 ^ m := by positivity
    have hp2 : (0 : ℝ) < (2 * M + 1) ^ 2 := by positivity
    rw [div_le_iff₀ (by positivity)]
    rw [show (1 : ℝ) / 6 * (4 ^ m / (4 * (2 * M + 1) ^ 2)) * (38832 * m)
        = 4 ^ m * (1618 * m / (2 * M + 1) ^ 2) by field_simp; ring]
    have : 1 ≤ 1618 * (m : ℝ) / (2 * M + 1) ^ 2 := by
      rw [le_div_iff₀ hp2]; linarith
    nlinarith
  calc (4 : ℝ) ^ m / (38832 * m) ≤ (1 / 6) * ((4 : ℝ) ^ m / (4 * (2 * M + 1) ^ 2)) := h4
    _ ≤ (1 / 6) * ((univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
        ‖∑ j, sgnC (ηη.1 j) * ((u j + u' j) / 2) - ∑ j, sgnC (ηη.2 j) * ((u j + u' j) / 2)‖
          ≤ 1 / 5).card : ℝ) := by gcongr
    _ ≤ (1 - (∑ j, ‖u j - u' j‖ ^ 2) / (4 / 5) ^ 2) *
        ((univ.filter fun ηη : (κ → Bool) × (κ → Bool) =>
        ‖∑ j, sgnC (ηη.1 j) * ((u j + u' j) / 2) - ∑ j, sgnC (ηη.2 j) * ((u j + u' j) / 2)‖
          ≤ 1 / 5).card : ℝ) := by gcongr
    _ ≤ _ := by rw [mul_comm]; exact hpair

/-- The reverse Littlewood–Offord bound with an explicit constant, as a count of sign vectors. -/
private theorem main_count_ge (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    1 / (38832 * 2 ^ 151 * (n : ℝ)) ≤
      ((univ.filter fun ε : Fin n → Bool => ‖∑ i, sgnC (ε i) * z i‖ ≤ √2).card : ℝ) / 2 ^ n := by
  set θ : Fin n → ℝ := fun i => Complex.arg (z i) with hθ
  set σ := Tuple.sort θ with hσ
  have hmono : Monotone (θ ∘ σ) := Tuple.monotone_sort θ
  set m := n / 2 with hm
  have hidx0 : ∀ j : Fin m, 2 * (j : ℕ) < n := fun j => by have := j.2; omega
  have hidx1 : ∀ j : Fin m, 2 * (j : ℕ) + 1 < n := fun j => by have := j.2; omega
  set e0 : Fin m → Fin n := fun j => σ ⟨2 * j, hidx0 j⟩ with he0
  set e1 : Fin m → Fin n := fun j => σ ⟨2 * j + 1, hidx1 j⟩ with he1
  set h : Fin m → ℝ := fun j => θ (e1 j) - θ (e0 j) with hh
  have hh0 : ∀ j, 0 ≤ h j := fun j => by
    have := hmono (show (⟨2 * j, hidx0 j⟩ : Fin n) ≤ ⟨2 * j + 1, hidx1 j⟩ by
      rw [Fin.mk_le_mk]; omega)
    simp only [Function.comp_apply] at this
    simp only [hh, he0, he1]; linarith
  have hsumh : ∑ j, h j ≤ 2 * Real.pi := by
    set T : ℕ → ℝ := fun k => θ (σ ⟨min k (n - 1), by omega⟩) with hT
    have hTmono : Monotone T := fun k l hkl => hmono (by rw [Fin.mk_le_mk]; omega)
    have hTh : ∀ j : Fin m, h j = T (2 * j + 1) - T (2 * j) := by
      intro j
      have h1 : min (2 * (j : ℕ) + 1) (n - 1) = 2 * j + 1 := by have := hidx1 j; omega
      have h2 : min (2 * (j : ℕ)) (n - 1) = 2 * j := by have := hidx1 j; omega
      simp only [hh, he0, he1, hT, h1, h2]
    calc ∑ j, h j = ∑ j ∈ range m, (T (2 * j + 1) - T (2 * j)) := by
          rw [← Fin.sum_univ_eq_sum_range (fun j => T (2 * j + 1) - T (2 * j))]
          exact sum_congr rfl fun j _ => hTh j
      _ ≤ T (2 * m) - T 0 := sum_range_odd_sub_even_le T hTmono m
      _ ≤ 2 * Real.pi := by
          have h1 := Complex.arg_le_pi (z (σ ⟨min (2 * m) (n - 1), by omega⟩))
          have h2 := Complex.neg_pi_lt_arg (z (σ ⟨min 0 (n - 1), by omega⟩))
          simp only [hT, hθ]; linarith
  have hchord : ∀ j, ‖z (e0 j) - z (e1 j)‖ ^ 2 ≤ h j ^ 2 := by
    intro j
    have := norm_sub_sq_le_arg_sub_sq (z (e0 j)) (z (e1 j)) (hz _) (hz _)
    have hsq : (Complex.arg (z (e0 j)) - Complex.arg (z (e1 j))) ^ 2 = h j ^ 2 := by
      simp only [hh, hθ]; ring
    linarith
  set G := univ.filter fun j : Fin m => h j < 1 / 12 with hG
  set R := univ.filter fun j : Fin m => ¬ h j < 1 / 12 with hR
  have hGR : G.card + R.card = m := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun j => h j < 1 / 12)
    rw [card_univ, Fintype.card_fin] at this
    exact this
  have hRcard : R.card ≤ 75 := by
    have h1 : R.card • (1 / 12 : ℝ) ≤ ∑ j ∈ R, h j :=
      card_nsmul_le_sum R h (1 / 12) (fun j hj => by
        simp only [hR, mem_filter, mem_univ, true_and, not_lt] at hj; exact hj)
    rw [nsmul_eq_mul] at h1
    have h2 : ∑ j ∈ R, h j ≤ ∑ j, h j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hh0 j)
    have h3 : (R.card : ℝ) < 76 := by nlinarith [Real.pi_lt_d2]
    have h4 : R.card < 76 := by exact_mod_cast h3
    omega
  have hGD : ∑ j ∈ G, ‖z (e0 j) - z (e1 j)‖ ^ 2 ≤ 21 / 40 := by
    calc ∑ j ∈ G, ‖z (e0 j) - z (e1 j)‖ ^ 2 ≤ ∑ j ∈ G, h j ^ 2 := sum_le_sum fun j _ => hchord j
      _ ≤ ∑ j ∈ G, (1 / 12) * h j := sum_le_sum fun j hj => by
          simp only [hG, mem_filter, mem_univ, true_and] at hj
          nlinarith [hh0 j]
      _ = (1 / 12) * ∑ j ∈ G, h j := by rw [mul_sum]
      _ ≤ (1 / 12) * ∑ j, h j :=
          mul_le_mul_of_nonneg_left
            (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hh0 j)) (by norm_num)
      _ ≤ (1 / 12) * (2 * Real.pi) := by gcongr
      _ ≤ 21 / 40 := by nlinarith [Real.pi_lt_d2]
  -- the kept pairs
  let u : G → ℂ := fun j => z (e0 j.1)
  let u' : G → ℂ := fun j => z (e1 j.1)
  let f : G ⊕ G → Fin n := Sum.elim (fun j => e0 j.1) (fun j => e1 j.1)
  have hf : Function.Injective f := by
    rintro (⟨j, hj⟩ | ⟨j, hj⟩) (⟨j', hj'⟩ | ⟨j', hj'⟩) hjj
    all_goals
      simp only [f, Sum.elim_inl, Sum.elim_inr, he0, he1, σ.injective.eq_iff, Fin.mk.injEq] at hjj
    · have : (j : ℕ) = j' := by omega
      exact congrArg Sum.inl (Subtype.ext (Fin.ext this))
    · omega
    · omega
    · have : (j : ℕ) = j' := by omega
      exact congrArg Sum.inr (Subtype.ext (Fin.ext this))
  have hext := card_le_card_extend z hz f hf
  have hzf : ∀ i, z (f i) = Sum.elim u u' i := by intro i; cases i <;> rfl
  simp only [hzf] at hext
  set N := (univ.filter fun ε : Fin n → Bool => ‖∑ i, sgnC (ε i) * z i‖ ≤ √2).card with hN
  set g := G.card with hg
  have hcardG : Fintype.card G = g := Fintype.card_coe G
  have hn2 : n ≤ 2 * g + 151 := by omega
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) h2n, one_mul]
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  · -- no kept pairs: the empty signed sum is small
    have hN1 : 1 ≤ N := by
      refine le_trans ?_ hext
      refine Finset.card_pos.mpr ⟨fun _ => true, ?_⟩
      have hGe : IsEmpty G := by
        rw [← Fintype.card_eq_zero_iff, hcardG, hg0]
      simp only [mem_filter, mem_univ, true_and]
      rw [Fintype.sum_empty, norm_zero]
      norm_num
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hpow : (2 : ℝ) ^ n ≤ 2 ^ 151 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
    generalize (2 : ℝ) ^ 151 = K at hpow ⊢
    generalize (2 : ℝ) ^ n = P at hpow h2n ⊢
    have hK : 0 < K := lt_of_lt_of_le h2n hpow
    have e1 : K ≤ K * n := by nlinarith
    have e2 : 38832 * K * n ≤ N * (38832 * K * n) := by
      have : 0 ≤ 38832 * K * n := by positivity
      nlinarith
    nlinarith
  · have hpb := pair_count_ge u u' (fun j => hz _) (fun j => hz _) (by rw [hcardG]; exact hgpos)
      ((le_of_eq (Finset.sum_coe_sort G (fun j => ‖z (e0 j) - z (e1 j)‖ ^ 2))).trans hGD)
    rw [hcardG] at hpb
    have hNR : (4 : ℝ) ^ g / (38832 * g) ≤ N := by
      refine hpb.trans ?_
      exact_mod_cast hext
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hgn : (g : ℝ) ≤ n := by exact_mod_cast (show g ≤ n by omega)
    have hpow : (2 : ℝ) ^ n ≤ 4 ^ g * 2 ^ 151 := by
      calc (2 : ℝ) ^ n ≤ 2 ^ (2 * g + 151) := pow_le_pow_right₀ (by norm_num) hn2
        _ = 4 ^ g * 2 ^ 151 := by rw [pow_add, pow_mul]; norm_num
    rw [div_le_iff₀ (by positivity)] at hNR
    have h4 : (0 : ℝ) < 4 ^ g := by positivity
    generalize (2 : ℝ) ^ 151 = K at hpow ⊢
    generalize (2 : ℝ) ^ n = P at hpow h2n ⊢
    generalize (4 : ℝ) ^ g = Q at hpow hNR h4 ⊢
    have hK : 0 < K := by
      by_contra hK; push Not at hK
      have : Q * K ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h4.le hK
      linarith
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have e1 : Q * K ≤ N * (38832 * g) * K := mul_le_mul_of_nonneg_right hNR hK.le
    have e2 : N * (38832 * g) * K ≤ N * (38832 * K * n) := by
      have : N * (38832 * g) * K = (N * 38832 * K) * g := by ring
      rw [this]
      have : N * (38832 * K * n) = (N * 38832 * K) * n := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hgn (by positivity)
    linarith

/--
**Erdős Problem 395 holds: the reverse Littlewood–Offord bound.** There is a real constant
$c > 0$ such that for every natural number $n \ge 1$ and all complex numbers $z_1, \dots, z_n$
with $|z_i| = 1$ for every $i$, at least a $c/n$ fraction of the $2^n$ sign vectors
$(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ satisfy
$|\varepsilon_1 z_1 + \dots + \varepsilon_n z_n| \le \sqrt{2}$. That is, for independent uniformly
random signs this inequality holds with probability at least $c/n$.

This was proved by He, Juškevičius, Narayanan and Spiro. The order $1/n$ is sharp: take half of the
$z_i$ equal to $1$ and the rest equal to the imaginary unit $\mathrm{i}$.

Source: T. F. Bloom, Erdős
Problems, Problem #395, https://www.erdosproblems.com/395 (status PROVED (LEAN)); resolution: X. He,
T. Juškevičius, B. Narayanan and S. Spiro, The reverse Littlewood-Offord problem of Erdős,
arXiv:2408.11034 (2024), probability ≫ 1/n, sharp (erdosproblems.com/395),
https://arxiv.org/abs/2408.11034.
-/
theorem reverseLittlewoodOffordSqrtTwo_holds : reverseLittlewoodOffordSqrtTwo := by
  refine ⟨1 / (38832 * 2 ^ 151), by positivity, fun n hn z hz => ?_⟩
  have hset : {ε : Fin n → Bool | ‖∑ i, (if ε i then (1 : ℂ) else -1) * z i‖ ≤ Real.sqrt 2}
      = ↑(univ.filter fun ε : Fin n → Bool => ‖∑ i, sgnC (ε i) * z i‖ ≤ √2) := by
    ext ε
    simp [sgnC]
  rw [smallSignedSumCount, hset, Set.ncard_coe_finset, div_div]
  exact main_count_ge n hn z hz

end MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395Wanted
