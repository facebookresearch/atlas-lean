/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability

/-!
# Ramanujan's Entry 30 (i)–(iii) for the general theta function

Splitting the series of Ramanujan's general theta function `f(a, b)` into its even-indexed and
odd-indexed terms gives `f(a, b) + f(-a, -b) = 2 f(a³b, ab³)` and, for `a ≠ 0`,
`f(a, b) - f(-a, -b) = 2a f(b/a, a⁵b³)`. Together with the product identity of Entry 29
(`ramanujanTheta_mul_of_mul_eq`) they give `f(a, ab²) f(b, a²b) = f(a, b) ψ(ab)`, where
`ψ(q) = f(q, q³)`. The main result, `ramanujanTheta_entry30`, states the three identities on
`‖ab‖ < 1`.
-/

namespace MetaMathlibExt

namespace ramanujanTheta_entry30

private def tri (n : ℤ) : ℕ := (n * (n - 1) / 2).toNat

private lemma twice_tri (n : ℤ) : 2 * (tri n : ℤ) = n * (n - 1) := by
  have hn : 0 ≤ n * (n - 1) := by
    rcases le_or_gt n 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg h.le (by omega)
  rw [tri, Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide))]
  exact Int.two_mul_ediv_two_of_even (Int.even_mul_pred_self n)

private lemma term_eq (a b : ℂ) (n : ℤ) :
    ramanujanThetaTerm a b n = a ^ tri (-n) * b ^ tri n := by
  simp only [tri, ramanujanThetaTerm, show -n * (-n - 1) = n * (n + 1) by ring]

/-- The term of even index `2k` is the term of index `k` of `f(a³b, ab³)`. -/
private lemma term_even (a b : ℂ) (k : ℤ) :
    ramanujanThetaTerm a b (2 * k) = ramanujanThetaTerm (a ^ 3 * b) (a * b ^ 3) k := by
  have h₁ : tri (-(2 * k)) = 3 * tri (-k) + tri k := by
    zify
    linarith [twice_tri (-(2 * k)), twice_tri (-k), twice_tri k]
  have h₂ : tri (2 * k) = tri (-k) + 3 * tri k := by
    zify
    linarith [twice_tri (2 * k), twice_tri (-k), twice_tri k]
  rw [term_eq, term_eq, h₁, h₂]
  ring

/-- Changing the signs of both parameters does not change the even-indexed terms. -/
private lemma term_even_neg (a b : ℂ) (k : ℤ) :
    ramanujanThetaTerm (-a) (-b) (2 * k) = ramanujanThetaTerm (a ^ 3 * b) (a * b ^ 3) k := by
  rw [term_even]
  congr 1 <;> ring

/-- Changing the signs of both parameters changes the sign of the odd-indexed terms. -/
private lemma term_odd_neg (a b : ℂ) (k : ℤ) :
    ramanujanThetaTerm (-a) (-b) (1 - 2 * k) = -ramanujanThetaTerm a b (1 - 2 * k) := by
  have hodd : Odd (tri (-(1 - 2 * k)) + tri (1 - 2 * k)) := by
    rw [← Int.odd_natCast]
    refine ⟨2 * k ^ 2 - 2 * k, ?_⟩
    push_cast
    linarith [twice_tri (-(1 - 2 * k)), twice_tri (1 - 2 * k)]
  rw [term_eq, term_eq, neg_pow a, neg_pow b,
    show ∀ x y u v : ℂ, x * u * (y * v) = (x * y) * (u * v) by intros; ring, ← pow_add,
    hodd.neg_one_pow, neg_one_mul]

-- Only the exponent of the nonzero parameter `a` needs to be signed.
private noncomputable def monomial (a b : ℂ) (i : ℤ) (j : ℕ) : ℂ := a ^ i * b ^ j

private lemma monomial_mul {a b : ℂ} (ha : a ≠ 0) (i i' : ℤ) (j j' : ℕ) :
    monomial a b i j * monomial a b i' j' = monomial a b (i + i') (j + j') := by
  simp only [monomial, zpow_add₀ ha, pow_add]
  ring

private lemma monomial_pow (a b : ℂ) (i : ℤ) (j n : ℕ) :
    monomial a b i j ^ n = monomial a b (i * n) (j * n) := by
  simp only [monomial, mul_pow, pow_mul, zpow_mul, zpow_natCast]

/-- For `a ≠ 0`, the term of odd index `1 - 2k` is `a` times the term of index `k` of
`f(b/a, a⁵b³)`. -/
private lemma term_odd {a b : ℂ} (ha : a ≠ 0) (k : ℤ) :
    ramanujanThetaTerm a b (1 - 2 * k) = a * ramanujanThetaTerm (b / a) (a ^ 5 * b ^ 3) k := by
  let M := monomial a b
  have ea : a = M 1 0 := by simp [M, monomial]
  have ei : a⁻¹ = M (-1) 0 := by simp [M, monomial]
  have eb : b = M 0 1 := by simp [M, monomial]
  rw [div_eq_mul_inv, ei, ea, eb]
  simp only [M, term_eq, monomial_pow, monomial_mul ha]
  congr 1
  · push_cast
    linarith only [twice_tri (-(1 - 2 * k)), twice_tri (-k), twice_tri k]
  · apply Int.ofNat_inj.mp
    push_cast
    linarith only [twice_tri (1 - 2 * k), twice_tri (-k), twice_tri k]

-- The even indices `2k` and the odd indices `1 - 2k` together cover `ℤ` once.
private def parityEquiv : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun k => 2 * k) (fun k => 1 - 2 * k)
  invFun n := if n % 2 = 0 then .inl (n / 2) else .inr ((1 - n) / 2)
  left_inv := by
    rintro (k | k) <;> dsimp <;> split <;> simp_all
  right_inv := by
    intro n
    dsimp
    split <;> dsimp <;> omega

private lemma hasSum_even_add_odd {a b E O : ℂ}
    (he : HasSum (fun k : ℤ => ramanujanThetaTerm a b (2 * k)) E)
    (ho : HasSum (fun k : ℤ => ramanujanThetaTerm a b (1 - 2 * k)) O) :
    HasSum (ramanujanThetaTerm a b) (E + O) :=
  parityEquiv.hasSum_iff.mp (HasSum.sum he ho)

private lemma norm_lt_one {a b x y : ℂ} (hab : ‖a * b‖ < 1) (h : x * y = (a * b) ^ 4) :
    ‖x * y‖ < 1 := by
  rw [h, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hab (by norm_num)

end ramanujanTheta_entry30

open ramanujanTheta_entry30

/-- **Ramanujan's Entry 30 (i)–(iii) for the general theta function.** Let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function and $\psi(q) = f(q, q^3)$. For all complex numbers $a$ and $b$ with $|ab| < 1$,
$f(a, ab^2) f(b, a^2 b) = f(a, b) \psi(ab)$ and $f(a, b) + f(-a, -b) = 2 f(a^3 b, a b^3)$, and if
moreover $a \ne 0$, then $f(a, b) - f(-a, -b) = 2a f(b/a, a^5 b^3)$.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Lemma 2 of Section 2, Equations (8)-(10) (`integers-2025-A16-sec-2-lem-2`),
quoting C. Adiga, B. C. Berndt, S. Bhargava, and G. N. Watson, Mem. Amer. Math. Soc. 53
(1985), no. 315, Entry 30 (i)-(iii); see also B. C. Berndt, *Ramanujan's Notebooks, Part III*,
Springer, 1991, Chapter 16, Entry 30 (i)-(iii). -/
public theorem ramanujanTheta_entry30 (a b : ℂ) (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a (a * b ^ 2) * ramanujanThetaRaw b (a ^ 2 * b) =
        ramanujanThetaRaw a b * ramanujanThetaRaw (a * b) ((a * b) ^ 3) ∧
      ramanujanThetaRaw a b + ramanujanThetaRaw (-a) (-b) =
        2 * ramanujanThetaRaw (a ^ 3 * b) (a * b ^ 3) ∧
      (a ≠ 0 → ramanujanThetaRaw a b - ramanujanThetaRaw (-a) (-b) =
        2 * a * ramanujanThetaRaw (b / a) (a ^ 5 * b ^ 3)) := by
  -- The even-indexed terms of `f(a, b)` and of `f(-a, -b)` are those of `f(a³b, ab³)`.
  have hE := (ramanujanTheta_summable (a ^ 3 * b) (a * b ^ 3)
    (norm_lt_one hab (by ring))).of_norm.hasSum
  have he : HasSum (fun k : ℤ => ramanujanThetaTerm a b (2 * k))
      (ramanujanThetaRaw (a ^ 3 * b) (a * b ^ 3)) := hE.congr_fun (term_even a b)
  have he' : HasSum (fun k : ℤ => ramanujanThetaTerm (-a) (-b) (2 * k))
      (ramanujanThetaRaw (a ^ 3 * b) (a * b ^ 3)) := hE.congr_fun (term_even_neg a b)
  -- The odd-indexed terms of `f(-a, -b)` are the negatives of those of `f(a, b)`.
  obtain ⟨O, ho⟩ : Summable (fun k : ℤ => ramanujanThetaTerm a b (1 - 2 * k)) :=
    (ramanujanTheta_summable a b hab).of_norm.comp_injective fun x y h => by omega
  have ho' : HasSum (fun k : ℤ => ramanujanThetaTerm (-a) (-b) (1 - 2 * k)) (-O) :=
    ho.neg.congr_fun (term_odd_neg a b)
  have hf : ramanujanThetaRaw a b = ramanujanThetaRaw (a ^ 3 * b) (a * b ^ 3) + O :=
    (hasSum_even_add_odd he ho).tsum_eq
  have hf' : ramanujanThetaRaw (-a) (-b) = ramanujanThetaRaw (a ^ 3 * b) (a * b ^ 3) + -O :=
    (hasSum_even_add_odd he' ho').tsum_eq
  -- For `a ≠ 0` the odd-indexed terms of `f(a, b)` are `a` times those of `f(b/a, a⁵b³)`.
  have hodd (ha : a ≠ 0) : O = a * ramanujanThetaRaw (b / a) (a ^ 5 * b ^ 3) := by
    have hO := (ramanujanTheta_summable (b / a) (a ^ 5 * b ^ 3)
      (norm_lt_one hab (by field_simp))).of_norm.hasSum.mul_left a
    exact ho.unique (hO.congr_fun (term_odd ha))
  refine ⟨?_, by rw [hf, hf']; ring, fun ha => by rw [hf, hf', hodd ha]; ring⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [ramanujanThetaRaw_symm b 0]
    ring
  -- Entry 29 with `(a, ab², b, a²b)`, whose parameter products are both `(ab)²`.
  have hP := ramanujanTheta_mul_of_mul_eq (a := a) (b := a * b ^ 2) (c := b) (d := a ^ 2 * b) ha
    (by rw [show a * (a * b ^ 2) = (a * b) ^ 2 by ring, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hab two_ne_zero)
    (by ring)
  rw [show a * (a ^ 2 * b) = a ^ 3 * b by ring, show a * b ^ 2 * b = a * b ^ 3 by ring,
    show a * b ^ 2 * (a ^ 2 * b) = (a * b) ^ 3 by ring,
    show a ^ 2 * (a * b ^ 2) * (a ^ 2 * b) = a ^ 5 * b ^ 3 by ring,
    show a ^ 2 * b / a = a * b by rw [div_eq_iff ha]; ring,
    show a ^ 2 * (a * b ^ 2) * b = (a * b) ^ 3 by ring] at hP
  rw [hP, hf, hodd ha]
  ring

end MetaMathlibExt
