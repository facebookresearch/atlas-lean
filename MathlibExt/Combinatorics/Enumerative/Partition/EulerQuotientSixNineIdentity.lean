/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An eta-quotient identity in the powers $q^3$, $q^6$, $q^9$ and $q^{18}$

`MetaMathlibExt.eulerFunction_six_cube_nine_six_div_eq` proves, for $|q| < 1$ and
$E_k = (q^k; q^k)_\infty$, the identity
$$\frac{E_6^3 E_9^6}{E_3^3 E_{18}^3} =
  \frac{E_6^8 E_9}{E_3^4 E_{18}^2} - q^3 \, \frac{E_{18}^6}{E_9^3}.$$

Write $x = q^3$ and $f(a, b)$ for Ramanujan's theta function. With its denominators cleared, the
identity reads $E_6^8 E_9^4 E_{18} = E_3 E_6^3 E_9^9 + x E_3^4 E_{18}^9$. The Jacobi triple
product writes $f(-x^a, -x^{6-a})$, for $a = 1, 2, 3$, as products of the factors $1 - x^m$
over residue classes of $m$ modulo $6$, which turns the cleared identity into
$$f(-x^2, -x^4)^4 = f(-x, -x^5) \, f(-x^3, -x^3)^3 + x \, f(-x, -x^5)^4.$$
Ramanujan's product formula `ramanujanTheta_mul_of_mul_eq` writes each of
$f(-x^2, -x^4)^2$, $f(-x, -x^5) f(-x^3, -x^3)$, $f(-x, -x^5)^2$ and $f(-x^3, -x^3)^2$ through
$f(x^4, x^8)$, $f(x^2, x^{10})$, $f(x^6, x^6)$ and $f(1, x^{12})$, and in these four
quantities the relation above is a polynomial identity.
-/

namespace MetaMathlibExt

namespace eulerFunction_six_cube_nine_six_div_eq

open QPochhammer

/-- The product of `1 - x ^ m` over the exponents `m ≡ r (mod d)`, `m ≥ r`. -/
private noncomputable def prog (x : ℂ) (d r : ℕ) : ℂ :=
  ∏' n : ℕ, (1 - x ^ (d * n + r))

private lemma norm_pow_lt {x : ℂ} (hx : ‖x‖ < 1) {k : ℕ} (hk : k ≠ 0) : ‖x ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hx hk

private lemma hasProd_prog {x : ℂ} (hx : ‖x‖ < 1) (d r : ℕ) (hd : d ≠ 0) :
    HasProd (fun n : ℕ => 1 - x ^ (d * n + r)) (prog x d r) := by
  have h := hasProd_qPochhammerInf (x ^ r) (x ^ d) (norm_pow_lt hx hd)
  simpa only [prog, qPochhammerInf, qPochhammerInfRaw, pow_add, pow_mul,
    mul_comm (x ^ r)] using h

-- Split the positive exponents into the residue classes 1, ..., d modulo d.
private lemma prog_split {x : ℂ} (hx : ‖x‖ < 1) (d : ℕ) [NeZero d] :
    prog x 1 1 = ∏ j : Fin d, prog x d (j.val + 1) := by
  have h := hasProd_prog hx 1 1 one_ne_zero
  let e := (Equiv.prodComm (Fin d) ℕ).trans (Nat.divModEquiv d).symm
  have hp := e.hasProd_iff.mpr h
  have hs := hp.prod_fiberwise (g := fun j : Fin d => prog x d (j.val + 1)) (by
    intro j
    simpa [e, mul_comm d, Nat.add_assoc] using hasProd_prog hx d (j.val + 1) (NeZero.ne d))
  exact hs.unique (hasProd_fintype _)

private lemma prog_pow (x : ℂ) (s d r : ℕ) :
    prog (x ^ s) d r = prog x (s * d) (s * r) := by
  unfold prog
  simp_rw [← pow_mul, Nat.mul_add, Nat.mul_assoc]

private lemma diag_eq_prog (y : ℂ) : qPochhammerInfRaw y y = prog y 1 1 := by
  unfold qPochhammerInfRaw prog
  congr 1
  funext n
  ring

private lemma diag_ne_zero {y : ℂ} (h : ‖y‖ < 1) : qPochhammerInfRaw y y ≠ 0 := by
  simp only [qPochhammerInfRaw, sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n he
    have heq : y ^ (n + 1) = 1 := by rw [pow_succ']; linear_combination -he
    have := pow_lt_one₀ (norm_nonneg y) h (Nat.succ_ne_zero n)
    rwa [← norm_pow, heq, norm_one, lt_self_iff_false] at this
  · simpa [norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg y) h).mul_left ‖y‖

-- Twice the triangular exponents of a theta summand.
private lemma twice_up (n : ℤ) : 2 * (((n * (n + 1) / 2).toNat : ℕ) : ℤ) = n * (n + 1) := by
  have hn : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide)), mul_comm]
  exact Int.ediv_mul_cancel (Int.even_mul_succ_self n).two_dvd

private lemma twice_down (n : ℤ) : 2 * (((n * (n - 1) / 2).toNat : ℕ) : ℤ) = n * (n - 1) := by
  simpa only [show -n * (-n + 1) = n * (n - 1) by ring] using twice_up (-n)

-- The summand of `f(-x^(m+c), -x^(m-c))` as a Jacobi triple product summand.
private lemma theta_term {x : ℂ} (hx : x ≠ 0) (m c : ℕ) (hc : c ≤ m) (n : ℤ) :
    ramanujanThetaTerm (-x ^ (m + c)) (-x ^ (m - c)) n =
      (-x ^ c) ^ n * (x ^ m) ^ (n * n).toNat := by
  set u := (n * (n + 1) / 2).toNat
  set v := (n * (n - 1) / 2).toNat
  have hu : 2 * (u : ℤ) = n * (n + 1) := twice_up n
  have hv : 2 * (v : ℤ) = n * (n - 1) := twice_down n
  have huv : (u : ℤ) = n + v := by linarith only [hu, hv]
  have hnn : (((n * n).toNat : ℕ) : ℤ) = n * n := Int.toNat_of_nonneg (mul_self_nonneg n)
  have hL : ramanujanThetaTerm (-x ^ (m + c)) (-x ^ (m - c)) n =
      (-1) ^ (u + v) * x ^ ((m + c) * u + (m - c) * v) := by
    change (-x ^ (m + c)) ^ u * (-x ^ (m - c)) ^ v = _
    rw [neg_pow (x ^ (m + c)), neg_pow (x ^ (m - c)), ← pow_mul, ← pow_mul]
    ring
  have hsign : (-1 : ℂ) ^ (u + v) = (-1) ^ n := by
    rw [← zpow_natCast, Nat.cast_add, huv, add_assoc, ← two_mul,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
    norm_num
  have hexp : x ^ ((m + c) * u + (m - c) * v) = x ^ ((c : ℤ) * n) * x ^ (m * (n * n).toNat) := by
    rw [← zpow_natCast x ((m + c) * u + (m - c) * v), ← zpow_natCast x (m * (n * n).toNat),
      ← zpow_add₀ hx]
    congr 1
    push_cast [Nat.cast_sub hc, hnn]
    linear_combination ((m : ℤ) + c) * huv + (m : ℤ) * hv
  rw [hL, hsign, hexp, neg_eq_neg_one_mul (x ^ c), mul_zpow, ← zpow_natCast (x : ℂ) c, ←
    zpow_mul, ← pow_mul]
  ring

-- The Jacobi triple product for `f(-x^(m+c), -x^(m-c))`, `c ≤ m`.
private lemma theta_product {x : ℂ} (hx : ‖x‖ < 1) (hx0 : x ≠ 0) (m c : ℕ) (hm : m ≠ 0)
    (hc : c ≤ m) :
    ramanujanThetaRaw (-x ^ (m + c)) (-x ^ (m - c)) =
      prog x (2 * m) (2 * m) * prog x (2 * m) (m + c) * prog x (2 * m) (m - c) := by
  have hz : (-x ^ c : ℂ) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hx0)
  obtain ⟨-, -, hj⟩ := Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product
    (-x ^ c) (x ^ m) hz (norm_pow_lt hx hm)
  rw [ramanujanThetaRaw]
  simp_rw [theta_term hx0 m c hc]
  rw [hj]
  have hd : 2 * m ≠ 0 := by omega
  have hp := ((hasProd_prog hx (2 * m) (2 * m) hd).mul
    (hasProd_prog hx (2 * m) (m + c) hd)).mul (hasProd_prog hx (2 * m) (m - c) hd)
  refine (hp.congr_fun (fun n => ?_)).tprod_eq
  have hxc : x ^ c ≠ 0 := pow_ne_zero _ hx0
  have h1 : (x ^ m) ^ (2 * n + 2) = x ^ (2 * m * n + 2 * m) := by
    rw [← pow_mul]; congr 1; ring
  have h2 : (x ^ m) ^ (2 * n + 1) = x ^ c * x ^ (2 * m * n + (m - c)) := by
    rw [← pow_mul, ← pow_add]; congr 1; zify [hc]; ring
  have h3 : x ^ (2 * m * n + (m + c)) = x ^ c * x ^ c * x ^ (2 * m * n + (m - c)) := by
    rw [← pow_add, ← pow_add]; congr 1; zify [hc]; ring
  rw [h1, h2, h3]
  field_simp
  ring

-- The Euler products `(x^k; x^k)_∞` for `k ∣ 6`, split into residue classes modulo 6.
private lemma euler_one {x : ℂ} (hx : ‖x‖ < 1) :
    qPochhammerInfRaw x x =
      prog x 6 1 * prog x 6 2 * prog x 6 3 * prog x 6 4 * prog x 6 5 * prog x 6 6 := by
  rw [diag_eq_prog, prog_split hx 6, Fin.prod_univ_six]
  rfl

private lemma euler_two {x : ℂ} (hx : ‖x‖ < 1) :
    qPochhammerInfRaw (x ^ 2) (x ^ 2) = prog x 6 2 * prog x 6 4 * prog x 6 6 := by
  rw [diag_eq_prog, prog_split (norm_pow_lt hx two_ne_zero) 3, Fin.prod_univ_three]
  simp only [prog_pow]
  rfl

private lemma euler_three {x : ℂ} (hx : ‖x‖ < 1) :
    qPochhammerInfRaw (x ^ 3) (x ^ 3) = prog x 6 3 * prog x 6 6 := by
  rw [diag_eq_prog, prog_split (norm_pow_lt hx three_ne_zero) 2, Fin.prod_univ_two]
  simp only [prog_pow]
  rfl

private lemma euler_six (x : ℂ) : qPochhammerInfRaw (x ^ 6) (x ^ 6) = prog x 6 6 := by
  rw [diag_eq_prog, prog_pow]

-- Ramanujan's product formula, with the arguments of the theta functions on the right named.
private lemma theta_mul {a b c d a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℂ} (ha : a ≠ 0)
    (hab : ‖a * b‖ < 1) (h : a * b = c * d) (h₁ : a * d = a₁) (h₁' : b * c = b₁)
    (h₂ : a * c = a₂) (h₂' : b * d = b₂) (h₃ : c / a = a₃) (h₃' : a ^ 2 * b * d = b₃)
    (h₄ : d / a = a₄) (h₄' : a ^ 2 * b * c = b₄) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d =
      ramanujanThetaRaw a₁ b₁ * ramanujanThetaRaw a₂ b₂ +
        a * ramanujanThetaRaw a₃ b₃ * ramanujanThetaRaw a₄ b₄ := by
  subst h₁ h₁' h₂ h₂' h₃ h₃' h₄ h₄'
  exact ramanujanTheta_mul_of_mul_eq ha hab h

-- The quartic relation between the theta functions `f(-x^a, -x^(6-a))`, `a = 1, 2, 3`.
private lemma theta_quartic {x : ℂ} (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ramanujanThetaRaw (-x ^ 2) (-x ^ 4) ^ 4 =
      ramanujanThetaRaw (-x) (-x ^ 5) * ramanujanThetaRaw (-x ^ 3) (-x ^ 3) ^ 3 +
        x * ramanujanThetaRaw (-x) (-x ^ 5) ^ 4 := by
  have h6 : ‖x ^ 6‖ < 1 := norm_pow_lt hx (by norm_num)
  have h22 := theta_mul (a := -x ^ 2) (b := -x ^ 4) (c := -x ^ 2) (d := -x ^ 4)
    (a₁ := x ^ 6) (b₁ := x ^ 6) (a₂ := x ^ 4) (b₂ := x ^ 8) (a₃ := 1) (b₃ := x ^ 12)
    (a₄ := x ^ 2) (b₄ := x ^ 10) (by simpa using hx0)
    (by rw [show -x ^ 2 * -x ^ 4 = x ^ 6 by ring]; exact h6) (by ring) (by ring) (by ring)
    (by ring) (by ring) (by field_simp) (by ring) (by field_simp) (by ring)
  have h13 := theta_mul (a := -x) (b := -x ^ 5) (c := -x ^ 3) (d := -x ^ 3)
    (a₁ := x ^ 4) (b₁ := x ^ 8) (a₂ := x ^ 4) (b₂ := x ^ 8) (a₃ := x ^ 2) (b₃ := x ^ 10)
    (a₄ := x ^ 2) (b₄ := x ^ 10) (by simpa using hx0)
    (by rw [show -x * -x ^ 5 = x ^ 6 by ring]; exact h6) (by ring) (by ring) (by ring)
    (by ring) (by ring) (by field_simp) (by ring) (by field_simp) (by ring)
  have h11 := theta_mul (a := -x) (b := -x ^ 5) (c := -x) (d := -x ^ 5)
    (a₁ := x ^ 6) (b₁ := x ^ 6) (a₂ := x ^ 2) (b₂ := x ^ 10) (a₃ := 1) (b₃ := x ^ 12)
    (a₄ := x ^ 4) (b₄ := x ^ 8) (by simpa using hx0)
    (by rw [show -x * -x ^ 5 = x ^ 6 by ring]; exact h6) (by ring) (by ring) (by ring)
    (by ring) (by ring) (by field_simp) (by ring) (by field_simp) (by ring)
  have h33 := theta_mul (a := -x ^ 3) (b := -x ^ 3) (c := -x ^ 3) (d := -x ^ 3)
    (a₁ := x ^ 6) (b₁ := x ^ 6) (a₂ := x ^ 6) (b₂ := x ^ 6) (a₃ := 1) (b₃ := x ^ 12)
    (a₄ := 1) (b₄ := x ^ 12) (by simpa using hx0)
    (by rw [show -x ^ 3 * -x ^ 3 = x ^ 6 by ring]; exact h6) (by ring) (by ring) (by ring)
    (by ring) (by ring) (by field_simp) (by ring) (by field_simp) (by ring)
  set T₁ := ramanujanThetaRaw (-x) (-x ^ 5)
  set T₂ := ramanujanThetaRaw (-x ^ 2) (-x ^ 4)
  set T₃ := ramanujanThetaRaw (-x ^ 3) (-x ^ 3)
  set X := ramanujanThetaRaw (x ^ 4) (x ^ 8)
  set Y := ramanujanThetaRaw (x ^ 2) (x ^ 10)
  set Z := ramanujanThetaRaw (x ^ 6) (x ^ 6)
  set W := ramanujanThetaRaw 1 (x ^ 12)
  linear_combination (T₂ * T₂ + Z * X - x ^ 2 * W * Y) * h22 - (T₃ * T₃) * h13 -
    (X * X - x * Y * Y) * h33 - x * (T₁ * T₁ + Z * Y - x * W * X) * h11

-- The identity with the denominators cleared, in the variable `x = q^3`.
private lemma cleared {x : ℂ} (hx : ‖x‖ < 1) :
    qPochhammerInfRaw (x ^ 2) (x ^ 2) ^ 8 * qPochhammerInfRaw (x ^ 3) (x ^ 3) ^ 4 *
        qPochhammerInfRaw (x ^ 6) (x ^ 6) =
      qPochhammerInfRaw x x * qPochhammerInfRaw (x ^ 2) (x ^ 2) ^ 3 *
          qPochhammerInfRaw (x ^ 3) (x ^ 3) ^ 9 +
        x * qPochhammerInfRaw x x ^ 4 * qPochhammerInfRaw (x ^ 6) (x ^ 6) ^ 9 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [qPochhammerInfRaw]
  have hq := theta_quartic hx hx0
  have t₁ := theta_product hx hx0 3 2 (by norm_num) (by norm_num)
  have t₂ := theta_product hx hx0 3 1 (by norm_num) (by norm_num)
  have t₃ := theta_product hx hx0 3 0 (by norm_num) (by norm_num)
  norm_num at t₁ t₂ t₃
  rw [ramanujanThetaRaw_symm (-x) (-x ^ 5), t₁, ramanujanThetaRaw_symm (-x ^ 2) (-x ^ 4), t₂,
    t₃] at hq
  rw [euler_one hx, euler_two hx, euler_three hx, euler_six x]
  linear_combination (prog x 6 2 ^ 4 * prog x 6 3 ^ 4 * prog x 6 4 ^ 4 * prog x 6 6 ^ 9) * hq

end eulerFunction_six_cube_nine_six_div_eq

-- Keep the tactic proof of `‖q ^ k‖ < 1` inline in the statement, as in the wanted statement.
set_option backward.proofsInPublic true in
open eulerFunction_six_cube_nine_six_div_eq in
/-- **Eta-quotient identity in the powers $q^3$, $q^6$, $q^9$ and $q^{18}$.** Let $q$ be a complex
number with $|q| < 1$, and for each integer $k \ge 1$ write $E_k = (q^k; q^k)_\infty$, the
infinite q-Pochhammer symbol $\prod_{n=0}^{\infty} (1 - q^{k(n+1)})$. Then

$$
\frac{E_6^3 E_9^6}{E_3^3 E_{18}^3} =
  \frac{E_6^8 E_9}{E_3^4 E_{18}^2} - q^3 \, \frac{E_{18}^6}{E_9^3}.
$$

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Lemma 1, identity (10) (`integers-2025-A76-lem-1`). Identity (9) of the same
lemma is `ramanujanPsi_three_dissection` (`OverpartitionSpt2CongruencesWanted`). -/
public theorem eulerFunction_six_cube_nine_six_div_eq (q : ℂ) (hq : ‖q‖ < 1) :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      QPochhammer.qPochhammerInf (q ^ k) (q ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hk)
    E 6 ^ 3 * E 9 ^ 6 / (E 3 ^ 3 * E 18 ^ 3) =
      E 6 ^ 8 * E 9 / (E 3 ^ 4 * E 18 ^ 2) - q ^ 3 * (E 18 ^ 6 / E 9 ^ 3) := by
  intro E
  have hE : ∀ k : ℕ, k ≠ 0 → E k = QPochhammer.qPochhammerInfRaw (q ^ k) (q ^ k) :=
    fun k hk => by simp [E, hk, QPochhammer.qPochhammerInf]
  have h := cleared (norm_pow_lt hq three_ne_zero)
  simp only [← pow_mul] at h
  norm_num at h
  have n₃ := diag_ne_zero (norm_pow_lt hq (show 3 ≠ 0 by norm_num))
  have n₉ := diag_ne_zero (norm_pow_lt hq (show 9 ≠ 0 by norm_num))
  have n₁₈ := diag_ne_zero (norm_pow_lt hq (show 18 ≠ 0 by norm_num))
  rw [hE 3 (by norm_num), hE 6 (by norm_num), hE 9 (by norm_num), hE 18 (by norm_num)]
  field_simp
  linear_combination -h

end MetaMathlibExt
