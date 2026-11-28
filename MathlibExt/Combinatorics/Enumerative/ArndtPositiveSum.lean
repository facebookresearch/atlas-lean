/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
public import MathlibExt.Combinatorics.Enumerative.ArndtCompositions
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Positive sum formula for Arndt compositions

For `m ≥ 1` and `h = ⌊m/2⌋`, the number `a(n, m)` of Arndt compositions of `n` with `m` parts is
`∑_{ℓ=0}^{⌊(n-m-h)/2⌋} C(h+ℓ-1, ℓ) C(n-2h-2ℓ-1, ⌊(m-1)/2⌋)` when `m + h ≤ n`, and `0` otherwise
(`MetaMathlibExt.arndtCompositionCount_eq_positive_sum`; D. F. Checa and J. L. Ramírez,
arXiv:2311.15388v1, Theorem 2.3).

As in the paper, the proof extracts coefficients of a generating function. Removing the leading
descending pair gives `A_{m+2} = P A_m` in `ℕ⟦X⟧`, where `A_m = ∑ₙ a(n, m) xⁿ` and
`P = ∑ₛ ⌊(s-1)/2⌋ xˢ = x³/((1-x)(1-x²))`. Hence `A_m = x^(m+h) (1-x²)^(-h) (1-x)^(-(m-h))`, and
the sum is the convolution of the coefficients of the last two factors.
-/

namespace MetaMathlibExt

namespace arndtCompositionCount_eq_positive_sum

open Finset PowerSeries

-- `valid`, `count_eq`, `valid_cons`, `count_pair`, `count_zero` and `count_one` repeat the
-- private declarations of the same names in
-- `MathlibExt/Combinatorics/Enumerative/ArndtCompositions.lean`, which are not exported.
private abbrev valid {k : ℕ} (c : Fin k → ℕ) :=
  (∀ i, 0 < c i) ∧ ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i

private lemma count_eq (n k : ℕ) :
    arndtCompositionCount (fun _ => True) n k =
      ((Nat.antidiagonalTuple k n).filter valid).card := by
  unfold arndtCompositionCount
  congr 1
  exact filter_congr fun c _ => by simp [valid]

private lemma valid_cons {k a b : ℕ} {c : Fin k → ℕ} :
    valid (Fin.cons a (Fin.cons b c)) ↔ 0 < b ∧ b < a ∧ valid c := by
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp (Fin.succ 0), hd 0 (Fin.succ 0) rfl rfl, fun i ↦ hp i.succ.succ, ?_⟩
    intro i j hi hj
    apply hd i.succ.succ j.succ.succ <;> simp only [Fin.val_succ] <;> omega
  · rintro ⟨hb, hba, hp, hd⟩
    constructor
    · intro i
      refine Fin.cases (by simpa using hb.trans hba) (fun i ↦ ?_) i
      exact Fin.cases hb hp i
    · intro i
      refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
      · intro j _ hj
        have : j = Fin.succ 0 := Fin.ext (by simpa using hj)
        simpa [this] using hba
      · simp
      · intro j
        refine Fin.cases (by simp) (fun j ↦ Fin.cases (by simp) (fun j ↦ ?_) j) j
        intro hi hj
        exact hd i j (by simp only [Fin.val_succ] at hi; omega)
          (by simp only [Fin.val_succ] at hj; omega)

-- Removing the leading descending pair `(s - j - 1, j + 1)`, `j < ⌊(s - 1)/2⌋`, of weight `s`.
private lemma count_pair (n k : ℕ) :
    arndtCompositionCount (fun _ => True) n (k + 2) =
      ∑ p ∈ antidiagonal n, (p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 k := by
  let tails (t : ℕ) := (Nat.antidiagonalTuple k t).filter valid
  let pieces := (antidiagonal n).sigma fun p ↦ range ((p.1 - 1) / 2) ×ˢ tails p.2
  let join (z : Σ _ : ℕ × ℕ, ℕ × (Fin k → ℕ)) : Fin (k + 2) → ℕ :=
    Fin.cons (z.1.1 - (z.2.1 + 1)) (Fin.cons (z.2.1 + 1) z.2.2)
  let split (c : Fin (k + 2) → ℕ) : Σ _ : ℕ × ℕ, ℕ × (Fin k → ℕ) :=
    ⟨(c 0 + c (Fin.succ 0), ∑ i : Fin k, c i.succ.succ),
      c (Fin.succ 0) - 1, fun i ↦ c i.succ.succ⟩
  have mem_pieces (p : ℕ × ℕ) (j : ℕ) (c : Fin k → ℕ) :
      (⟨p, j, c⟩ : Σ _ : ℕ × ℕ, ℕ × (Fin k → ℕ)) ∈ pieces ↔
        p.1 + p.2 = n ∧ j < (p.1 - 1) / 2 ∧ (∑ i, c i) = p.2 ∧ valid c := by
    simp [pieces, tails, Nat.mem_antidiagonalTuple]
  have hcard : pieces.card =
      ∑ p ∈ antidiagonal n, (p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 k := by
    simp only [pieces, card_sigma, card_product, card_range, count_eq, tails]
  rw [← hcard, count_eq]
  symm
  apply card_nbij' join split
  · rintro ⟨⟨s, t⟩, j, c⟩ hz
    obtain ⟨hst, hj, ht, hc⟩ := (mem_pieces _ _ _).mp hz
    simp only [mem_coe, mem_filter, Nat.mem_antidiagonalTuple, join, Fin.sum_cons, valid_cons]
    dsimp at *
    exact ⟨by omega, by omega, by omega, hc⟩
  · intro c hc
    obtain ⟨hs, hv⟩ := mem_filter.mp hc
    rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
    have hb := hv.1 (Fin.succ 0)
    have hba := hv.2 0 (Fin.succ 0) rfl rfl
    change 0 < c 1 at hb
    change c 1 < c 0 at hba
    change c 0 + (c 1 + ∑ i : Fin k, c i.succ.succ) = n at hs
    apply (mem_pieces _ _ _).mpr
    refine ⟨by dsimp; omega, by dsimp; omega, rfl, ?_⟩
    exact ⟨fun i ↦ hv.1 i.succ.succ, fun i j hi hj ↦
      hv.2 i.succ.succ j.succ.succ (by simp; omega) (by simp; omega)⟩
  · rintro ⟨⟨s, t⟩, j, c⟩ hz
    obtain ⟨_, hj, ht, _⟩ := (mem_pieces _ _ _).mp hz
    simp [split, join, ht, show j + 1 ≤ s by dsimp at hj; omega]
  · intro c hc
    have hb := (mem_filter.mp hc).2.1 (Fin.succ 0)
    change 0 < c 1 at hb
    funext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun _ ↦ rfl) i) i <;>
      simp [join, split] <;> omega

private lemma count_zero (n : ℕ) :
    arndtCompositionCount (fun _ => True) n 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp [arndtCompositionCount]

private lemma count_one (n : ℕ) :
    arndtCompositionCount (fun _ => True) n 1 = if n = 0 then 0 else 1 := by
  cases n <;> simp [arndtCompositionCount, Nat.antidiagonalTuple_one, Fin.forall_fin_one,
    filter_singleton]

/-- The generating function `∑ₙ a(n, m) xⁿ` of Arndt compositions with `m` parts. -/
private noncomputable def partsSeries (m : ℕ) : PowerSeries ℕ :=
  mk fun n ↦ arndtCompositionCount (fun _ => True) n m

/-- The series `∑ₙ xⁿ = 1/(1 - x)`. -/
private noncomputable def geomSeries : PowerSeries ℕ :=
  mk fun _ ↦ 1

/-- The series `∑ₙ x^(2n) = 1/(1 - x²)`. -/
private noncomputable def evenSeries : PowerSeries ℕ :=
  mk fun j ↦ if 2 ∣ j then 1 else 0

/-- The series `∑ₛ ⌊(s - 1)/2⌋ xˢ` counting descending pairs `(a, b)`, `a > b ≥ 1`, by weight. -/
private noncomputable def pairSeries : PowerSeries ℕ :=
  mk fun s ↦ (s - 1) / 2

private lemma partsSeries_zero : partsSeries 0 = 1 := by
  ext n
  simp [partsSeries, count_zero, coeff_one]

private lemma partsSeries_one : partsSeries 1 = X * geomSeries := by
  ext n
  rcases n with _ | n <;> simp [partsSeries, geomSeries, count_one, coeff_succ_X_mul]

private lemma partsSeries_add_two (k : ℕ) :
    partsSeries (k + 2) = pairSeries * partsSeries k := by
  ext n
  simp only [partsSeries, pairSeries, coeff_mul, coeff_mk]
  exact count_pair n k

-- Multiplying by a series supported on even degrees.
private lemma coeff_even_mul {g : PowerSeries ℕ} (hg : ∀ j, ¬ 2 ∣ j → coeff j g = 0)
    (f : PowerSeries ℕ) (N : ℕ) :
    coeff N (g * f) = ∑ ℓ ∈ range (N / 2 + 1), coeff (2 * ℓ) g * coeff (N - 2 * ℓ) f := by
  have himage : ∑ k ∈ (range (N / 2 + 1)).image (2 * ·), coeff k g * coeff (N - k) f =
      ∑ ℓ ∈ range (N / 2 + 1), coeff (2 * ℓ) g * coeff (N - 2 * ℓ) f :=
    sum_image fun a _ b _ hab ↦ by omega
  rw [← himage, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply sum_subset
  · intro k hk
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hk
    rw [mem_range] at hℓ ⊢
    omega
  · intro k hk hk'
    have hodd : ¬ 2 ∣ k := by
      rintro ⟨ℓ, rfl⟩
      exact hk' (mem_image.mpr ⟨ℓ, by rw [mem_range] at hk ⊢; omega, rfl⟩)
    simp [hg k hodd]

private lemma pairSeries_eq : pairSeries = X ^ 3 * (evenSeries * geomSeries) := by
  ext s
  rw [coeff_X_pow_mul']
  split_ifs with hs
  · rw [coeff_even_mul (fun j hj ↦ by simp [evenSeries, hj])]
    simp only [pairSeries, evenSeries, geomSeries, coeff_mk, dvd_mul_right, ite_true, mul_one,
      sum_const, card_range, smul_eq_mul]
    omega
  · simp only [pairSeries, coeff_mk]
    omega

private lemma partsSeries_eq (m : ℕ) :
    partsSeries m = X ^ (m + m / 2) * (evenSeries ^ (m / 2) * geomSeries ^ (m - m / 2)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [partsSeries_zero]
    | 1 => simp [partsSeries_one]
    | k + 2 =>
      rw [partsSeries_add_two, ih k (by omega), pairSeries_eq,
        show k + 2 + (k + 2) / 2 = k + k / 2 + 3 by omega,
        show (k + 2) / 2 = k / 2 + 1 by omega,
        show k + 2 - (k / 2 + 1) = k - k / 2 + 1 by omega]
      ring

-- The hockey-stick identity; for `h = 0`, truncated subtraction gives `C(i - 1, i) = [i = 0]`.
private lemma sum_range_choose (h k : ℕ) :
    ∑ i ∈ range (k + 1), (i + h - 1).choose i = (k + h).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, show k + 1 + h - 1 = k + h by omega,
      show k + 1 + h = k + h + 1 by omega, Nat.choose_succ_succ']

private lemma coeff_geomSeries_pow (d j : ℕ) :
    coeff j (geomSeries ^ d) = (j + d - 1).choose j := by
  induction d generalizing j with
  | zero => rcases j with _ | j <;> simp [coeff_one]
  | succ d ih =>
    rw [pow_succ, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [ih]
    simp only [geomSeries, coeff_mk, mul_one]
    rw [sum_range_choose, show j + (d + 1) - 1 = j + d by omega]

private lemma coeff_evenSeries_pow (h j : ℕ) :
    coeff j (evenSeries ^ h) = if 2 ∣ j then (j / 2 + h - 1).choose (j / 2) else 0 := by
  induction h generalizing j with
  | zero =>
    rw [pow_zero, coeff_one]
    by_cases hj : j = 0
    · simp [hj]
    · rw [ite_eq_right hj]
      split_ifs
      · exact (Nat.choose_eq_zero_of_lt (by omega)).symm
      · rfl
  | succ h ih =>
    have hodd : ∀ i, ¬ 2 ∣ i → coeff i (evenSeries ^ h) = 0 := fun i hi ↦ by
      rw [ih, ite_eq_right hi]
    rw [pow_succ, coeff_even_mul hodd]
    split_ifs with hj
    · rw [show j / 2 + (h + 1) - 1 = j / 2 + h by omega, ← sum_range_choose]
      refine sum_congr rfl fun ℓ hℓ ↦ ?_
      rw [mem_range] at hℓ
      rw [ih, ite_eq_left (dvd_mul_right 2 ℓ), Nat.mul_div_cancel_left ℓ two_pos]
      simp [evenSeries, show 2 ∣ j - 2 * ℓ by omega]
    · refine sum_eq_zero fun ℓ hℓ ↦ ?_
      rw [mem_range] at hℓ
      simp [evenSeries, show ¬ 2 ∣ j - 2 * ℓ by omega]

private lemma ringChoose_add_sub_one (h ℓ : ℕ) :
    Ring.choose ((h : ℤ) + ℓ - 1) ℓ = ((ℓ + h - 1).choose ℓ : ℤ) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  · rw [show (h : ℤ) + ℓ - 1 = ((ℓ + h - 1 : ℕ) : ℤ) by omega, Ring.choose_natCast]

end arndtCompositionCount_eq_positive_sum

open arndtCompositionCount_eq_positive_sum in
/-- **Positive sum for Arndt compositions.** Let $a(n, m)$ be the number of Arndt compositions of
$n$ with $m$ parts, and write $h = \lfloor m/2 \rfloor$. For all $n \ge 0$ and $m \ge 1$: if
$m + h \le n$, then
$$a(n, m) = \sum_{\ell=0}^{\lfloor (n-m-h)/2 \rfloor} \binom{h+\ell-1}{\ell}
\binom{n-2h-2\ell-1}{\lfloor (m-1)/2 \rfloor},$$
and otherwise $a(n, m) = 0$. Here $\binom{-1}{0} = 1$ (this term occurs for $m = 1$).

The paper states it for all $n, m \ge 0$; at $n = m = 0$ it fails ($a(0, 0) = 1$, while the only
term has lower index $\lfloor -1/2 \rfloor = -1$ and vanishes), so the case $m = 0$ is omitted.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 3 (`integers-2024-A35-thm-3`). -/
public theorem arndtCompositionCount_eq_positive_sum (n m : ℕ) (hm : 0 < m) :
    (arndtCompositionCount (fun _ => True) n m : ℤ) =
      if m + m / 2 ≤ n then
        ∑ ℓ ∈ Finset.range ((n - m - m / 2) / 2 + 1),
          Ring.choose (((m / 2 : ℕ) : ℤ) + ℓ - 1) ℓ *
            Ring.choose ((n : ℤ) - 2 * (m / 2 : ℕ) - 2 * ℓ - 1) ((m - 1) / 2)
      else 0 := by
  have hc : arndtCompositionCount (fun _ => True) n m = PowerSeries.coeff n (partsSeries m) := by
    simp [partsSeries]
  rw [hc, partsSeries_eq, PowerSeries.coeff_X_pow_mul', Nat.sub_sub n m]
  split_ifs with hle
  · rw [coeff_even_mul (fun j hj ↦ by rw [coeff_evenSeries_pow, ite_eq_right hj]), Nat.cast_sum]
    refine Finset.sum_congr rfl fun ℓ hℓ ↦ ?_
    rw [Finset.mem_range] at hℓ
    rw [coeff_evenSeries_pow, ite_eq_left (dvd_mul_right 2 ℓ), Nat.mul_div_cancel_left ℓ two_pos,
      coeff_geomSeries_pow, Nat.cast_mul, ringChoose_add_sub_one,
      show n - (m + m / 2) - 2 * ℓ + (m - m / 2) - 1 = n - (m + m / 2) - 2 * ℓ + (m - 1) / 2 by
        omega,
      Nat.choose_symm_add,
      show (n : ℤ) - 2 * (m / 2 : ℕ) - 2 * ℓ - 1 = ((n - (m + m / 2) - 2 * ℓ + (m - 1) / 2 : ℕ) : ℤ)
        by omega,
      Ring.choose_natCast]
  · simp

end MetaMathlibExt
