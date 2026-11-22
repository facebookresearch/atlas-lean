/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

/-!
# Theta-function lemmas for the order-eighteen Rogers-Ramanujan-Slater relations

Statements from A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103: Section 2 (Lemmas 1-5, classical identities quoted from
Berndt's *Ramanujan's Notebooks*) and the modular relations of Theorems 1 and 2.

Ramanujan's notation, on the open unit disk `‖q‖ < 1`:
* `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` is `ramanujanThetaRaw a b`;
* `φ(q) = f(q, q)`, `ψ(q) = f(q, q³)`, `f(-q) = f(-q, -q²)`;
* `χ(q) = (-q; q²)_∞` is `qPochhammerInfRaw (-q) (q ^ 2)`.
All raw sums and products converge on the disk (for `f(a, b)`, when `‖ab‖ < 1`), where they
equal the canonical values. Identities with a theta quotient are stated with the denominator
cleared; the cleared factor does not vanish on the disk.
-/

namespace MetaMathlibExt

@[expose] public section

open MetaMathlibExt.QPochhammer

/-- First identity of Lemma 2 (Berndt, Entry 29(i)): if `ab = cd` and `‖ab‖ < 1`, then
`f(a, b) f(c, d) + f(-a, -b) f(-c, -d) = 2 f(ac, bd) f(ad, bc)`. The convergence hypothesis
`‖ab‖ < 1` is the domain of Ramanujan's `f`.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 2, Equation (6) (`integers-2024-A103-lem-2`). -/
public theorem_wanted ramanujanTheta_mul_add_mul_neg {a b c d : ℂ} (habcd : a * b = c * d)
    (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d +
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * ramanujanThetaRaw (a * c) (b * d) * ramanujanThetaRaw (a * d) (b * c)

/-- Second identity of Lemma 2 (Berndt, Entry 29(ii)): if `ab = cd`, `‖ab‖ < 1` and
`c, d ≠ 0`, then
`f(a, b) f(c, d) - f(-a, -b) f(-c, -d) = 2a f(b/c, (c/b)abcd) f(b/d, (d/b)abcd)`, written with
`(c/b)abcd = ac²d` and `(d/b)abcd = acd²`. The hypotheses `c ≠ 0`, `d ≠ 0` make the quotients
`b/c`, `b/d` meaningful.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 2, Equation (7) (`integers-2024-A103-lem-2`). -/
public theorem_wanted ramanujanTheta_mul_sub_mul_neg {a b c d : ℂ} (habcd : a * b = c * d)
    (hab : ‖a * b‖ < 1) (hc : c ≠ 0) (hd : d ≠ 0) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d -
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * a * ramanujanThetaRaw (b / c) (a * c ^ 2 * d) *
        ramanujanThetaRaw (b / d) (a * c * d ^ 2)

/-- `f(q, q⁵) = χ(q) ψ(-q³)` for `‖q‖ < 1`.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 3, Equation (9) (`integers-2024-A103-lem-3`). -/
public theorem_wanted ramanujanTheta_one_five {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 5) =
      qPochhammerInfRaw (-q) (q ^ 2) * ramanujanThetaRaw (-q ^ 3) ((-q ^ 3) ^ 3)

/-- `f(-q, -q⁸) f(-q², -q⁷) f(-q⁴, -q⁵) = f(-q) f³(-q⁹) / f(-q³)` for `‖q‖ < 1`, stated with
`f(-q³)` cleared.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 4, Equation (10) (`integers-2024-A103-lem-4`). -/
public theorem_wanted ramanujanTheta_order_nine_product {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) (-q ^ 8) * ramanujanThetaRaw (-q ^ 2) (-q ^ 7) *
        ramanujanThetaRaw (-q ^ 4) (-q ^ 5) * ramanujanThetaRaw (-q ^ 3) (-(q ^ 3) ^ 2) =
      ramanujanThetaRaw (-q) (-q ^ 2) * ramanujanThetaRaw (-q ^ 9) (-(q ^ 9) ^ 2) ^ 3

/-- `f(q, q²) = φ(-q³) / χ(-q)` for `‖q‖ < 1`, stated with `χ(-q) = (q; q²)_∞` cleared.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 5, Equation (11) (`integers-2024-A103-lem-5`). -/
public theorem_wanted ramanujanTheta_one_two {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 2) * qPochhammerInfRaw q (q ^ 2) =
      ramanujanThetaRaw (-q ^ 3) (-q ^ 3)

/-- Lemma 1, the classical eta-quotients of Ramanujan's functions: with
`f_k = (q^k; q^k)_∞`, for `‖q‖ < 1`,
`φ(q) = f₂⁵ / (f₁² f₄²)`, `ψ(q) = f₂² / f₁`, `φ(-q) = f₁² / f₂`, `ψ(-q) = f₁ f₄ / f₂`,
`f(q) = f₂³ / (f₁ f₄)`, `χ(q) = f₂² / (f₁ f₄)`, and `χ(-q) = f₁ / f₂`, each stated with the
denominator cleared. Here `f(q) = f(q, -q²)` and `χ(-q) = (q; q²)_∞`, the `q ↦ -q` images of
`f(-q)` and `χ(q)`.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 1 (quoted from Berndt) (`integers-2024-A103-lem-1`). -/
public theorem_wanted ramanujanTheta_eta_quotients {q : ℂ} (hq : ‖q‖ < 1) :
    let f₁ := qPochhammerInfRaw q q
    let f₂ := qPochhammerInfRaw (q ^ 2) (q ^ 2)
    let f₄ := qPochhammerInfRaw (q ^ 4) (q ^ 4)
    ramanujanThetaRaw q q * (f₁ ^ 2 * f₄ ^ 2) = f₂ ^ 5 ∧
      ramanujanThetaRaw q (q ^ 3) * f₁ = f₂ ^ 2 ∧
      ramanujanThetaRaw (-q) (-q) * f₂ = f₁ ^ 2 ∧
      ramanujanThetaRaw (-q) (-q ^ 3) * f₂ = f₁ * f₄ ∧
      ramanujanThetaRaw q (-q ^ 2) * (f₁ * f₄) = f₂ ^ 3 ∧
      qPochhammerInfRaw (-q) (q ^ 2) * (f₁ * f₄) = f₂ ^ 2 ∧
      qPochhammerInfRaw q (q ^ 2) * f₂ = f₁

/-- Theorem 1, the seven modular relations (12)-(18) for the order-eighteen
Rogers-Ramanujan-Slater type functions. With `f_k = (q^k; q^k)_∞` and, following the paper's
Equations (2)-(4), `P(q) = f(-q⁷, -q¹¹) / f(-q⁶)`, `Q(q) = f(-q⁵, -q¹³) / f(-q⁶)`,
`R(q) = f(-q, -q¹⁷) / f(-q⁶)`, write `P_n = P(q^n)`, `Q_n = Q(q^n)`, `R_n = R(q^n)`; here
`f(-q^{6n}) = f_{6n}`. The hypothesis `q ≠ 0` is needed for the factor `1 / q` on the right.

Deviation: in (14) the paper prints `f₄₈` in the last denominator; that is false
(the `q⁵⁶` coefficients of the two sides are `0` and `-1`). The statement uses `f₅₄`, the
`f_{6n}` factor that (12), (13) and (15) carry at this place (`f₄₈ = f_{6·8}` is the value from
(12)); with `f₅₄` the relation checks exactly through `q¹⁹⁸`.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Theorem 1, Equations (12)-(18) (`integers-2024-A103-thm-1`). -/
public theorem_wanted slaterOrderEighteen_modular_relations {q : ℂ} (hq : ‖q‖ < 1)
    (hq0 : q ≠ 0) :
    let f : ℕ → ℂ := fun k => qPochhammerInfRaw (q ^ k) (q ^ k)
    let P : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n) ^ 7) (-(q ^ n) ^ 11) / f (6 * n)
    let Q : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n) ^ 5) (-(q ^ n) ^ 13) / f (6 * n)
    let R : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n)) (-(q ^ n) ^ 17) / f (6 * n)
    (P 1 * P 8 + q ^ 3 * Q 1 * Q 8 + q ^ 15 * R 1 * R 8 =
        1 / (2 * q * f 6 * f 48) *
            (f 2 ^ 5 * f 8 ^ 2 / (f 1 ^ 2 * f 4 ^ 2 * f 16) -
              f 9 ^ 2 * f 72 ^ 2 / (f 18 * f 144)) -
          q ^ 8 * (f 3 * f 18 ^ 2 * f 24 * f 144 ^ 2 / (f 6 ^ 2 * f 9 * f 48 ^ 2 * f 72))) ∧
      (P 2 * P 7 + q ^ 3 * Q 2 * Q 7 + q ^ 15 * R 2 * R 7 =
        1 / (2 * q * f 12 * f 42) *
            (f 2 ^ 5 * f 14 ^ 2 / (f 1 ^ 2 * f 4 ^ 2 * f 28) -
              f 18 ^ 2 * f 63 ^ 2 / (f 36 * f 126)) -
          q ^ 8 * (f 6 * f 21 * f 36 ^ 2 * f 126 ^ 2 / (f 12 ^ 2 * f 18 * f 42 ^ 2 * f 63))) ∧
      (P 3 * P 6 + q ^ 3 * Q 3 * Q 6 + q ^ 15 * R 3 * R 6 =
        1 / (2 * q) *
            (f 2 ^ 5 * f 18 / (f 1 ^ 2 * f 4 ^ 2 * f 36 ^ 2) -
              f 27 ^ 2 * f 54 ^ 2 / (f 18 * f 36 * f 54 * f 108)) -
          q ^ 8 * (f 9 * f 54 ^ 2 * f 108 ^ 2 / (f 18 * f 27 * f 36 ^ 2 * f 54))) ∧
      (P 4 * P 5 + q ^ 3 * Q 4 * Q 5 + q ^ 15 * R 4 * R 5 =
        1 / (2 * q * f 24 * f 30) *
            (f 2 ^ 5 * f 20 ^ 2 / (f 1 ^ 2 * f 4 ^ 2 * f 40) -
              f 36 ^ 2 * f 45 ^ 2 / (f 72 * f 90)) -
          q ^ 8 * (f 12 * f 15 * f 72 ^ 2 * f 90 ^ 2 / (f 24 ^ 2 * f 30 ^ 2 * f 36 * f 45))) ∧
      (P 1 * Q 2 - q ^ 3 * Q 1 * R 2 + q * R 1 * P 2 =
        1 / (2 * q * f 6 * f 12) * (f 9 ^ 2 * f 18 / f 36 - f 1 ^ 2 * f 2 / f 4) +
          q ^ 2 * (f 3 * f 18 * f 36 ^ 2 / (f 6 * f 9 * f 12 ^ 2))) ∧
      (q ^ 5 * P 1 * Q 20 - q ^ 32 * Q 1 * R 20 + R 1 * P 20 =
        1 / (2 * q ^ 4 * f 6 * f 120) *
            (f 9 ^ 2 * f 180 ^ 2 / (f 18 * f 360) - f 4 ^ 2 * f 10 ^ 5 / (f 5 ^ 2 * f 8 * f 20 ^ 2)) +
          q ^ 17 * (f 3 * f 18 ^ 2 * f 60 * f 360 ^ 2 / (f 6 ^ 2 * f 9 * f 120 ^ 2 * f 180))) ∧
      (q ^ 23 * P 1 * R 14 + Q 1 * P 14 - q ^ 6 * R 1 * Q 14 =
        1 / (2 * q ^ 2 * f 6 * f 84) *
            (f 9 ^ 2 * f 126 ^ 2 / (f 18 * f 252) - f 2 ^ 2 * f 14 ^ 5 / (f 4 * f 7 ^ 2 * f 28 ^ 2)) +
          q ^ 13 * (f 3 * f 18 ^ 2 * f 42 * f 252 ^ 2 / (f 6 ^ 2 * f 9 * f 84 ^ 2 * f 126)))

/-- Theorem 2, relations (21)-(27) between the order-eighteen functions `P, Q, R` of Theorem 1
and the nonic Rogers-Ramanujan functions `A(q) = f(-q⁴, -q⁵) / f(-q³)`,
`B(q) = f(-q², -q⁷) / f(-q³)`, `C(q) = f(-q, -q⁸) / f(-q³)` (the product forms the paper quotes
from Baruah and Bora), with `X_n = X(q^n)`, `f_k = (q^k; q^k)_∞` and
`χ(-q) = (q; q²)_∞`.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Theorem 2, Equations (21)-(27) (`integers-2024-A103-thm-2`). -/
public theorem_wanted slaterOrderEighteen_nonic_relations {q : ℂ} (hq : ‖q‖ < 1) :
    let f : ℕ → ℂ := fun k => qPochhammerInfRaw (q ^ k) (q ^ k)
    let P : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n) ^ 7) (-(q ^ n) ^ 11) / f (6 * n)
    let Q : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n) ^ 5) (-(q ^ n) ^ 13) / f (6 * n)
    let R : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n)) (-(q ^ n) ^ 17) / f (6 * n)
    let A : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n) ^ 4) (-(q ^ n) ^ 5) / f (3 * n)
    let B : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n) ^ 2) (-(q ^ n) ^ 7) / f (3 * n)
    let C : ℕ → ℂ := fun n => ramanujanThetaRaw (-(q ^ n)) (-(q ^ n) ^ 8) / f (3 * n)
    P 1 * Q 1 * R 1 =
        qPochhammerInfRaw q (q ^ 2) * f 18 ^ 3 / (qPochhammerInfRaw (q ^ 3) (q ^ 6) * f 6 ^ 3) ∧
      (P 1 * A 2 + q ^ 3 * R 1 * C 2) / A 1 = f 9 ^ 2 / (f 6 * f 18) ∧
      (Q 1 * A 2 - q ^ 2 * R 1 * B 2) / B 1 = f 9 ^ 2 / (f 6 * f 18) ∧
      (P 1 * B 2 - q * Q 1 * C 2) / C 1 = f 9 ^ 2 / (f 6 * f 18) ∧
      (P 1 * A 2 + Q 1 * B 2 + q ^ 3 * R 1 * C 2) / A 1 =
        f 9 ^ 2 / (f 6 * f 18) + f 3 * f 18 ^ 2 / (f 6 ^ 2 * f 9) ∧
      (Q 1 * A 2 - q ^ 2 * R 1 * B 2 + P 1 * C 2) / B 1 =
        f 9 ^ 2 / (f 6 * f 18) + f 3 * f 18 ^ 2 / (f 6 ^ 2 * f 9) ∧
      (R 1 * A 2 + P 1 * B 2 - q * Q 1 * C 2) / C 1 =
        f 9 ^ 2 / (f 6 * f 18) + f 3 * f 18 ^ 2 / (f 6 ^ 2 * f 9)

end

end MetaMathlibExt
