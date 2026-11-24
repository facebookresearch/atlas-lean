/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.QAnalogCollatz
public import MathlibExt.NumberTheory.QCollatzParityFlip

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **The $q$-Collatz map is conjugate to the $2$-adic $3x+1$ map.** Let $A$ and $B$ be odd
power series in $\mathbb{F}_2[[q]]$ (constant term $1$), let $T_{A,B}$ be the $q$-analog of the
$3x+1$ map on $\mathbb{F}_2[[q]]$, and let $T$ be the $3x+1$ map on the $2$-adic integers
$\mathbb{Z}_2$. Then there is a bijection $h : \mathbb{Z}_2 \to \mathbb{F}_2[[q]]$ with
$h^{-1}(T_{A,B}(h(x))) = T(x)$ for every $x \in \mathbb{Z}_2$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 2 (`jis-2025-25.6.8-thm-2`). -/
public theorem_wanted qCollatz_conjugate_twoAdicCollatz (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
      ∀ x, h.symm (qCollatz A B (h x)) = twoAdicCollatz x

/-- **The map $T_{1+q,1}$ is conjugate to the $2$-adic $3x+1$ map.** Let $T_q = T_{1+q,1}$
be the $q$-analog of the $3x+1$ map with $A = 1 + q$ and $B = 1$, so that $T_q(x) = x/q$ if $q$
divides $x$ and $T_q(x) = ((1+q)x + 1)/q$ otherwise, and let $T$ be the $3x+1$ map on the
$2$-adic integers $\mathbb{Z}_2$. Then there is a bijection $h : \mathbb{Z}_2 \to \mathbb{F}_2[[q]]$
with $h^{-1}(T_q(h(x))) = T(x)$ for every $x \in \mathbb{Z}_2$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 3 (`jis-2025-25.6.8-cor-3`). -/
public theorem_wanted qCollatz_one_add_X_conjugate_twoAdicCollatz :
    ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
      ∀ x, h.symm (qCollatz (1 + X) 1 (h x)) = twoAdicCollatz x

/-- **Polynomial orbits of $T_{1,1+q^2}$.** Let $T = T_{1,1+q^2}$ be the $q$-analog of the $3x+1$
map with $A = 1$ and $B = 1 + q^2$. For every polynomial $p$ over $\mathbb{F}_2$, some iterate
$T^k(p)$ with $k \ge 0$ lies in $\{0, 1 + q, 1, q\}$, the set formed by the fixed points $0$ and
$1 + q$ of $T$ and its $2$-cycle $\{1, q\}$. Moreover, for every $x \in \mathbb{F}_2[[q]]$, $T(x)$
is a polynomial if and only if $x$ is a polynomial.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 5 (`jis-2025-25.6.8-thm-5`). -/
public theorem_wanted qCollatz_one_one_add_X_sq_polynomial :
    (∀ p : Polynomial (ZMod 2), ∃ k : ℕ,
      (qCollatz 1 (1 + X ^ 2))^[k] (p : PowerSeries (ZMod 2)) ∈
        ({0, 1 + X, 1, X} : Set (PowerSeries (ZMod 2)))) ∧
    ∀ x : PowerSeries (ZMod 2),
      (∃ p : Polynomial (ZMod 2), qCollatz 1 (1 + X ^ 2) x = p) ↔
        ∃ p : Polynomial (ZMod 2), x = p

/-- **A perturbation at $q^{n+1}$ moves to $q^n$ under $T_{A,B}$.** Let $A, B, U, V$ be power
series in $\mathbb{F}_2[[q]]$ with $A$, $B$ and $V$ odd (constant term $1$), let $T_{A,B}$ be the
$q$-analog of the $3x+1$ map, and let $n \ge 0$ be an integer. Then there is an odd power series
$W \in \mathbb{F}_2[[q]]$ with $T_{A,B}(U + q^{n+1} V) = T_{A,B}(U) + q^n W$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 7 (`jis-2025-25.6.8-lem-7`). -/
public theorem_wanted qCollatz_add_X_pow_mul (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) :
    ∃ W : PowerSeries (ZMod 2), constantCoeff W ≠ 0 ∧
      qCollatz A B (U + X ^ (n + 1) * V) = qCollatz A B U + X ^ n * W

/-- **Parity vectors detect congruence modulo $q^{n+1}$.** Let $A, B \in \mathbb{F}_2[[q]]$ be odd
(constant term $1$), let $\mathrm{PV}_{A,B}$ be the parity vector map of the $q$-analog $T_{A,B}$
of the $3x+1$ map, and let $n \ge 0$ be an integer. For all $a, b \in \mathbb{F}_2[[q]]$, we have
$\mathrm{PV}_{A,B}(a) \equiv \mathrm{PV}_{A,B}(b) \pmod{2^{n+1}}$ in $\mathbb{Z}_2$ if and only if
$q^{n+1}$ divides $a - b$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 11 (`jis-2025-25.6.8-thm-11`). -/
public theorem_wanted qCollatzParityVector_modEq_iff (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (a b : PowerSeries (ZMod 2)) :
    PadicInt.toZModPow (n + 1) (qCollatzParityVector A B a) =
        PadicInt.toZModPow (n + 1) (qCollatzParityVector A B b) ↔
      X ^ (n + 1) ∣ a - b

/-- **Parity vectors induce bijections modulo $q^n$.** Let $A, B \in \mathbb{F}_2[[q]]$ be odd
(constant term $1$), let $\mathrm{PV}_{A,B}$ be the parity vector map of the $q$-analog $T_{A,B}$
of the $3x+1$ map, and let $n \ge 1$ be an integer. Then there is a bijection
$e : \mathbb{F}_2[[q]]/(q^n) \to \mathbb{Z}/2^n\mathbb{Z}$ such that, for every
$a \in \mathbb{F}_2[[q]]$, $e$ sends the class of $a$ to the residue of $\mathrm{PV}_{A,B}(a)$
modulo $2^n$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 12 (`jis-2025-25.6.8-cor-12`). -/
public theorem_wanted qCollatzParityVector_quotient_bijection (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (PowerSeries (ZMod 2) ⧸ Ideal.span {(X : PowerSeries (ZMod 2)) ^ n}) ≃ ZMod (2 ^ n),
      ∀ a, e (Ideal.Quotient.mk _ a) = PadicInt.toZModPow n (qCollatzParityVector A B a)

/-- **Fixed points and the $2$-cycle of the $q$-Collatz map.** Let $A, B \in \mathbb{F}_2[[q]]$ be
odd (constant term $1$) and let $T_{A,B}$ be the $q$-analog of the $3x+1$ map. For every
$x \in \mathbb{F}_2[[q]]$, $T_{A,B}(x) = x$ holds exactly when $x = 0$ or $x = B/(A+q)$. Moreover,
for every $x \in \mathbb{F}_2[[q]]$, $T_{A,B}(T_{A,B}(x)) = x$ and $T_{A,B}(x) \ne x$ hold together
exactly when $x = B/(A+q^2)$ or $x = qB/(A+q^2)$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 13 (`jis-2025-25.6.8-lem-13`). -/
public theorem_wanted qCollatz_fixedPoints_and_twoCycle (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    (∀ x, qCollatz A B x = x ↔ x = 0 ∨ x = B * (A + X)⁻¹) ∧
    ∀ x, (qCollatz A B (qCollatz A B x) = x ∧ qCollatz A B x ≠ x) ↔
      x = B * (A + X ^ 2)⁻¹ ∨ x = X * (B * (A + X ^ 2)⁻¹)

end

end MetaMathlibExt
