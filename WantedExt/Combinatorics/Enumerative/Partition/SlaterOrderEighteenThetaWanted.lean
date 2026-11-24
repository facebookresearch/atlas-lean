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

/-- **Ramanujan's theta function: sum of products when $ab = cd$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function. For
complex numbers $a, b, c, d$ with $ab = cd$ and $|ab| < 1$,
$f(a,b) f(c,d) + f(-a,-b) f(-c,-d) = 2 f(ac,bd) f(ad,bc)$.

This is Entry 29(i) of Berndt's *Ramanujan's Notebooks*; the hypothesis $|ab| < 1$ makes all
the theta series converge.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 2, Equation (6) (`integers-2024-A103-lem-2`). -/
public theorem_wanted ramanujanTheta_mul_add_mul_neg {a b c d : ℂ} (habcd : a * b = c * d)
    (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d +
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * ramanujanThetaRaw (a * c) (b * d) * ramanujanThetaRaw (a * d) (b * c)

/-- **Ramanujan's theta function: difference of products when $ab = cd$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function. For
complex numbers $a, b, c, d$ with $ab = cd$, $|ab| < 1$, $c \ne 0$ and $d \ne 0$,
$f(a,b) f(c,d) - f(-a,-b) f(-c,-d) = 2a \, f(b/c, ac^2 d) \, f(b/d, acd^2)$.

This is Entry 29(ii) of Berndt's *Ramanujan's Notebooks*, where the second arguments are written
$(c/b)abcd = ac^2 d$ and $(d/b)abcd = acd^2$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 2, Equation (7) (`integers-2024-A103-lem-2`). -/
public theorem_wanted ramanujanTheta_mul_sub_mul_neg {a b c d : ℂ} (habcd : a * b = c * d)
    (hab : ‖a * b‖ < 1) (hc : c ≠ 0) (hd : d ≠ 0) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d -
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * a * ramanujanThetaRaw (b / c) (a * c ^ 2 * d) *
        ramanujanThetaRaw (b / d) (a * c * d ^ 2)

/-- **Ramanujan's theta function at $(q, q^5)$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function and
$(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$. For every complex number $q$ with $|q| < 1$,
$f(q,q^5) = (-q;q^2)_\infty \, f(-q^3,-q^9)$, that is, $f(q,q^5) = \chi(q) \psi(-q^3)$ with
$\chi(q) = (-q;q^2)_\infty$ and $\psi(q) = f(q,q^3)$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 3, Equation (9) (`integers-2024-A103-lem-3`). -/
public theorem_wanted ramanujanTheta_one_five {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 5) =
      qPochhammerInfRaw (-q) (q ^ 2) * ramanujanThetaRaw (-q ^ 3) ((-q ^ 3) ^ 3)

/-- **Product of the nonic theta functions.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function and
write $f(-x) = f(-x,-x^2)$. For every complex number $q$ with $|q| < 1$,
$f(-q,-q^8) f(-q^2,-q^7) f(-q^4,-q^5) f(-q^3) = f(-q) f(-q^9)^3$, that is,
$f(-q,-q^8) f(-q^2,-q^7) f(-q^4,-q^5) = f(-q) f^3(-q^9)/f(-q^3)$ with the denominator cleared.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 4, Equation (10) (`integers-2024-A103-lem-4`). -/
public theorem_wanted ramanujanTheta_order_nine_product {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) (-q ^ 8) * ramanujanThetaRaw (-q ^ 2) (-q ^ 7) *
        ramanujanThetaRaw (-q ^ 4) (-q ^ 5) * ramanujanThetaRaw (-q ^ 3) (-(q ^ 3) ^ 2) =
      ramanujanThetaRaw (-q) (-q ^ 2) * ramanujanThetaRaw (-q ^ 9) (-(q ^ 9) ^ 2) ^ 3

/-- **Ramanujan's theta function at $(q, q^2)$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function and
$(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$. For every complex number $q$ with $|q| < 1$,
$f(q,q^2) \, (q;q^2)_\infty = f(-q^3,-q^3)$, that is, $f(q,q^2) = \varphi(-q^3)/\chi(-q)$ with
the denominator cleared, where $\varphi(q) = f(q,q)$ and $\chi(-q) = (q;q^2)_\infty$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 5, Equation (11) (`integers-2024-A103-lem-5`). -/
public theorem_wanted ramanujanTheta_one_two {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 2) * qPochhammerInfRaw q (q ^ 2) =
      ramanujanThetaRaw (-q ^ 3) (-q ^ 3)

/-- **Eta-quotients of Ramanujan's theta functions.** Let $q$ be a complex number with
$|q| < 1$. Write $(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ and $f_k = (q^k;q^k)_\infty$, and
let $f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function.
Then $f(q,q) f_1^2 f_4^2 = f_2^5$, $f(q,q^3) f_1 = f_2^2$, $f(-q,-q) f_2 = f_1^2$,
$f(-q,-q^3) f_2 = f_1 f_4$, $f(q,-q^2) f_1 f_4 = f_2^3$, $(-q;q^2)_\infty f_1 f_4 = f_2^2$ and
$(q;q^2)_\infty f_2 = f_1$.

These are the classical eta-quotients $\varphi(q) = f_2^5/(f_1^2 f_4^2)$, $\psi(q) = f_2^2/f_1$,
$\varphi(-q) = f_1^2/f_2$, $\psi(-q) = f_1 f_4/f_2$, $f(q) = f_2^3/(f_1 f_4)$,
$\chi(q) = f_2^2/(f_1 f_4)$ and $\chi(-q) = f_1/f_2$ with the denominators cleared, where
$\varphi(q) = f(q,q)$, $\psi(q) = f(q,q^3)$, $f(q) = f(q,-q^2)$ and $\chi(q) = (-q;q^2)_\infty$.

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

/-- **Modular relations for the order-eighteen Rogers–Ramanujan–Slater functions.** Let $q$ be
a complex number with $0 < |q| < 1$. Write $(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ and
$f_k = (q^k;q^k)_\infty$, let $f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be
Ramanujan's theta function, and set $P_n = f(-q^{7n},-q^{11n})/f_{6n}$,
$Q_n = f(-q^{5n},-q^{13n})/f_{6n}$ and $R_n = f(-q^n,-q^{17n})/f_{6n}$. Then the following seven
relations hold.

$$P_1 P_8 + q^3 Q_1 Q_8 + q^{15} R_1 R_8 = \frac{1}{2q f_6 f_{48}} \left(
\frac{f_2^5 f_8^2}{f_1^2 f_4^2 f_{16}} - \frac{f_9^2 f_{72}^2}{f_{18} f_{144}}\right) -
q^8 \frac{f_3 f_{18}^2 f_{24} f_{144}^2}{f_6^2 f_9 f_{48}^2 f_{72}}$$

$$P_2 P_7 + q^3 Q_2 Q_7 + q^{15} R_2 R_7 = \frac{1}{2q f_{12} f_{42}} \left(
\frac{f_2^5 f_{14}^2}{f_1^2 f_4^2 f_{28}} - \frac{f_{18}^2 f_{63}^2}{f_{36} f_{126}}\right) -
q^8 \frac{f_6 f_{21} f_{36}^2 f_{126}^2}{f_{12}^2 f_{18} f_{42}^2 f_{63}}$$

$$P_3 P_6 + q^3 Q_3 Q_6 + q^{15} R_3 R_6 = \frac{1}{2q} \left(
\frac{f_2^5 f_{18}}{f_1^2 f_4^2 f_{36}^2} - \frac{f_{27}^2 f_{54}^2}{f_{18} f_{36} f_{54} f_{108}}
\right) - q^8 \frac{f_9 f_{54}^2 f_{108}^2}{f_{18} f_{27} f_{36}^2 f_{54}}$$

$$P_4 P_5 + q^3 Q_4 Q_5 + q^{15} R_4 R_5 = \frac{1}{2q f_{24} f_{30}} \left(
\frac{f_2^5 f_{20}^2}{f_1^2 f_4^2 f_{40}} - \frac{f_{36}^2 f_{45}^2}{f_{72} f_{90}}\right) -
q^8 \frac{f_{12} f_{15} f_{72}^2 f_{90}^2}{f_{24}^2 f_{30}^2 f_{36} f_{45}}$$

$$P_1 Q_2 - q^3 Q_1 R_2 + q R_1 P_2 = \frac{1}{2q f_6 f_{12}} \left(
\frac{f_9^2 f_{18}}{f_{36}} - \frac{f_1^2 f_2}{f_4}\right) +
q^2 \frac{f_3 f_{18} f_{36}^2}{f_6 f_9 f_{12}^2}$$

$$q^5 P_1 Q_{20} - q^{32} Q_1 R_{20} + R_1 P_{20} = \frac{1}{2q^4 f_6 f_{120}} \left(
\frac{f_9^2 f_{180}^2}{f_{18} f_{360}} - \frac{f_4^2 f_{10}^5}{f_5^2 f_8 f_{20}^2}\right) +
q^{17} \frac{f_3 f_{18}^2 f_{60} f_{360}^2}{f_6^2 f_9 f_{120}^2 f_{180}}$$

$$q^{23} P_1 R_{14} + Q_1 P_{14} - q^6 R_1 Q_{14} = \frac{1}{2q^2 f_6 f_{84}} \left(
\frac{f_9^2 f_{126}^2}{f_{18} f_{252}} - \frac{f_2^2 f_{14}^5}{f_4 f_7^2 f_{28}^2}\right) +
q^{13} \frac{f_3 f_{18}^2 f_{42} f_{252}^2}{f_6^2 f_9 f_{84}^2 f_{126}}$$

These are the source's relations (12)–(18), in order, for $P_n = P(q^n)$, $Q_n = Q(q^n)$ and
$R_n = R(q^n)$, where $P(q) = f(-q^7,-q^{11})/f(-q^6)$, $Q(q) = f(-q^5,-q^{13})/f(-q^6)$ and
$R(q) = f(-q,-q^{17})/f(-q^6)$ are the order-eighteen functions and $f(-q^6) = f_6$.

Deviation: in (14), the third relation, the paper prints $f_{48}$ in the last denominator; that
is false (the coefficients of $q^{56}$ of the two sides are $0$ and $-1$). The statement uses
$f_{54}$, the $f_{6n}$ factor that (12), (13) and (15) carry at this place ($f_{48} = f_{6 \cdot 8}$
is the value from (12)); with $f_{54}$ the relation checks exactly through $q^{198}$.

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

/-- **Relations between the order-eighteen and the nonic Rogers–Ramanujan functions.** Let $q$
be a complex number with $|q| < 1$. Write $(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ and
$f_k = (q^k;q^k)_\infty$, let $f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be
Ramanujan's theta function, and set $P_n = f(-q^{7n},-q^{11n})/f_{6n}$,
$Q_n = f(-q^{5n},-q^{13n})/f_{6n}$, $R_n = f(-q^n,-q^{17n})/f_{6n}$,
$A_n = f(-q^{4n},-q^{5n})/f_{3n}$, $B_n = f(-q^{2n},-q^{7n})/f_{3n}$ and
$C_n = f(-q^n,-q^{8n})/f_{3n}$. Then

$$P_1 Q_1 R_1 = \frac{(q;q^2)_\infty \, f_{18}^3}{(q^3;q^6)_\infty \, f_6^3},$$

$$\frac{P_1 A_2 + q^3 R_1 C_2}{A_1} = \frac{Q_1 A_2 - q^2 R_1 B_2}{B_1} =
\frac{P_1 B_2 - q Q_1 C_2}{C_1} = \frac{f_9^2}{f_6 f_{18}}$$

and

$$\frac{P_1 A_2 + Q_1 B_2 + q^3 R_1 C_2}{A_1} = \frac{Q_1 A_2 - q^2 R_1 B_2 + P_1 C_2}{B_1} =
\frac{R_1 A_2 + P_1 B_2 - q Q_1 C_2}{C_1} = \frac{f_9^2}{f_6 f_{18}} +
\frac{f_3 f_{18}^2}{f_6^2 f_9}.$$

These are the source's relations (21)–(27). Here $P_n$, $Q_n$, $R_n$ are the order-eighteen
functions of Theorem 1 and $A_n$, $B_n$, $C_n$ the nonic Rogers–Ramanujan functions
$A(q) = f(-q^4,-q^5)/f(-q^3)$, $B(q) = f(-q^2,-q^7)/f(-q^3)$, $C(q) = f(-q,-q^8)/f(-q^3)$
evaluated at $q^n$, with $f(-q^3) = f_3$; the first relation reads
$P_1 Q_1 R_1 = \chi(-q) f_{18}^3 / (\chi(-q^3) f_6^3)$ with $\chi(-q) = (q;q^2)_\infty$.

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
