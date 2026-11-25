/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ramanujan's theta product identity

For two theta functions with equal parameter products, `ramanujanTheta_mul_of_mul_eq`
splits their product according to the parity of the two summation indices.
-/

namespace MetaMathlibExt

private def triangular (n : ℤ) : ℕ := (n * (n - 1) / 2).toNat

private lemma twice_triangular (n : ℤ) :
    2 * (triangular n : ℤ) = n * (n - 1) := by
  have hn : 0 ≤ n * (n - 1) := by
    rcases lt_or_ge n 1 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  rw [triangular, Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide)), mul_comm]
  exact Int.ediv_mul_cancel (Int.even_mul_pred_self n).two_dvd

private lemma term_eq (a b : ℂ) (n : ℤ) :
    ramanujanThetaTerm a b n = a ^ triangular (-n) * b ^ triangular n := by
  simp only [ramanujanThetaTerm, triangular, show -n * (-n - 1) = n * (n + 1) by ring]

-- Only the exponent of the nonzero parameter a needs to be signed.
private noncomputable def monomial (a c d : ℂ) (i : ℤ) (j k : ℕ) : ℂ :=
  a ^ i * c ^ j * d ^ k

private lemma monomial_mul {a c d : ℂ} (ha : a ≠ 0) (i i' : ℤ) (j k j' k' : ℕ) :
    monomial a c d i j k * monomial a c d i' j' k' =
      monomial a c d (i + i') (j + j') (k + k') := by
  simp only [monomial, zpow_add₀ ha, pow_add]
  ac_rfl

private lemma monomial_pow (a c d : ℂ) (i : ℤ) (j k n : ℕ) :
    monomial a c d i j k ^ n = monomial a c d (i * n) (j * n) (k * n) := by
  simp only [monomial, mul_pow, pow_mul, zpow_mul, zpow_natCast]

private lemma product_terms {a b c d : ℂ} (ha : a ≠ 0) (h : a * b = c * d) (i j : ℤ) :
    ramanujanThetaTerm a b (i + j) * ramanujanThetaTerm c d (j - i) =
        ramanujanThetaTerm (a * d) (b * c) i * ramanujanThetaTerm (a * c) (b * d) j ∧
      ramanujanThetaTerm a b (1 - i - j) * ramanujanThetaTerm c d (i - j) =
        a * (ramanujanThetaTerm (c / a) (a ^ 2 * b * d) i *
          ramanujanThetaTerm (d / a) (a ^ 2 * b * c) j) := by
  let M := monomial a c d
  have ea : a = M 1 0 0 := by simp [M, monomial]
  have ei : a⁻¹ = M (-1) 0 0 := by simp [M, monomial]
  have eb : b = M (-1) 1 1 := by simp [M, monomial, mul_assoc, ← h, ha]
  have ec : c = M 0 1 0 := by simp [M, monomial]
  have ed : d = M 0 0 1 := by simp [M, monomial]
  rw [div_eq_mul_inv, div_eq_mul_inv, ei, ea, eb, ec, ed]
  simp only [M, term_eq, monomial_pow, monomial_mul ha]
  constructor <;> congr 1 <;> try apply Int.ofNat_inj.mp
  all_goals push_cast
  all_goals linarith only [twice_triangular i, twice_triangular (-i),
    twice_triangular j, twice_triangular (-j), twice_triangular (i + j),
    twice_triangular (-(i + j)), twice_triangular (j - i), twice_triangular (-(j - i)),
    twice_triangular (1 - i - j), twice_triangular (-(1 - i - j)),
    twice_triangular (i - j), twice_triangular (-(i - j))]

-- Equal parity gives (i+j, j-i), and opposite parity gives (1-i-j, i-j).
private def parityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun (i, j) => (i + j, j - i)) (fun (i, j) => (1 - i - j, i - j))
  invFun := fun (n, m) => if (n + m) % 2 = 0 then .inl ((n - m) / 2, (n + m) / 2)
    else .inr ((1 - n + m) / 2, (1 - n - m) / 2)
  left_inv := by
    rintro (⟨i, j⟩ | ⟨i, j⟩) <;> dsimp <;> split <;> simp_all <;> omega
  right_inv := by
    rintro ⟨n, m⟩
    dsimp
    split <;> dsimp <;> congr 1 <;> omega

private lemma product_hasSum {a b c d : ℂ} (hab : ‖a * b‖ < 1) (hcd : ‖c * d‖ < 1) :
    HasSum (fun p : ℤ × ℤ => ramanujanThetaTerm a b p.1 * ramanujanThetaTerm c d p.2)
      (ramanujanThetaRaw a b * ramanujanThetaRaw c d) := by
  have h₁ := ramanujanTheta_summable a b hab
  have h₂ := ramanujanTheta_summable c d hcd
  simpa only [ramanujanThetaRaw, tsum_mul_tsum_of_summable_norm h₁ h₂] using
    (summable_mul_of_summable_norm h₁ h₂).hasSum

/-- **Ramanujan's theta product identity for $ab = cd$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function. If $a, b, c, d$ are complex numbers with $a \ne 0$, $|ab| < 1$ and $ab = cd$, then
$$f(a,b)\,f(c,d) = f(ad,bc)\,f(ac,bd) + a\,f(c/a, a^2bd)\,f(d/a, a^2bc).$$

In each of the six theta functions the two arguments have product of modulus $|ab|$ or
$|ab|^2$, which is less than $1$, so every series converges.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 1, eq. (12), quoting
Berndt, *Ramanujan's Notebooks, Part III*, p. 45, Entry 29 (`integers-2025-A17-lem-1`). -/
public theorem ramanujanTheta_mul_of_mul_eq {a b c d : ℂ} (ha : a ≠ 0)
    (hab : ‖a * b‖ < 1) (h : a * b = c * d) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d =
      ramanujanThetaRaw (a * d) (b * c) * ramanujanThetaRaw (a * c) (b * d) +
        a * ramanujanThetaRaw (c / a) (a ^ 2 * b * d) *
          ramanujanThetaRaw (d / a) (a ^ 2 * b * c) := by
  have small {x y : ℂ} (hxy : x * y = (a * b) * (c * d)) : ‖x * y‖ < 1 := by
    rw [hxy, ← h, ← sq, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hab two_ne_zero
  have evenSum := product_hasSum (small (x := a * d) (y := b * c) (by ring))
    (small (x := a * c) (y := b * d) (by ring))
  have oddSum := product_hasSum (small (x := c / a) (y := a ^ 2 * b * d) (by field_simp))
    (small (x := d / a) (y := a ^ 2 * b * c) (by field_simp))
  rw [mul_assoc a]
  apply (product_hasSum hab (h ▸ hab)).unique
  apply parityEquiv.hasSum_iff.mp
  apply HasSum.sum
  · exact evenSum.congr_fun fun ⟨i, j⟩ => (product_terms ha h i j).1
  · exact (oddSum.mul_left a).congr_fun fun ⟨i, j⟩ => (product_terms ha h i j).2

end MetaMathlibExt
