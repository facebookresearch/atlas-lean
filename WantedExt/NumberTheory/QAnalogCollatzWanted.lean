/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **Division by $q$ in $\mathbb{F}_2[[q]]$.** For a power series
$x = \sum_n x_n q^n \in \mathbb{F}_2[[q]]$, its shift is the power series $\sum_n x_{n+1} q^n$,
obtained by discarding the constant term of $x$ and dividing by $q$. In particular, the shift of
$qy$ is $y$ for every $y \in \mathbb{F}_2[[q]]$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (the quotients `x/q` and `(Ax+B)/q` in the
definition of `T_{A,B}`). -/
noncomputable def qShift (x : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => coeff (n + 1) x

/-- **Dividing a multiple of $q$ by $q$.** For every power series $y \in \mathbb{F}_2[[q]]$,
applying the shift $\sum_n x_n q^n \mapsto \sum_n x_{n+1} q^n$ to $qy$ gives back $y$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (division by `q`). -/
theorem qShift_X_mul (y : PowerSeries (ZMod 2)) : qShift (X * y) = y := by
  ext n
  simp [qShift, coeff_succ_X_mul]

/-- **The q-analog of the 3x+1 map.** For a power series $y = \sum_n y_n q^n \in \mathbb{F}_2[[q]]$,
write $y/q$ for the power series $\sum_n y_{n+1} q^n$: the constant term of $y$ is discarded and the
rest is divided by $q$. For power series $A, B \in \mathbb{F}_2[[q]]$, the map
$T_{A,B} : \mathbb{F}_2[[q]] \to \mathbb{F}_2[[q]]$ is defined by $T_{A,B}(x) = x/q$ if the
constant term of $x$ is $0$, and $T_{A,B}(x) = (Ax + B)/q$ otherwise.

When $A$ and $B$ have constant term $1$, the numerator $Ax + B$ has constant term $0$ whenever
$x$ has constant term $1$, so in that case the division by $q$ is exact.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T_{A,B}`). -/
noncomputable def qCollatz (A B x : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  if constantCoeff x = 0 then qShift x else qShift (A * x + B)

/-- **The q-analog 3x+1 map on multiples of $q$.** For all power series
$A, B, y \in \mathbb{F}_2[[q]]$, the $q$-analog $3x+1$ map satisfies $T_{A,B}(qy) = y$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T_{A,B}`). -/
theorem qCollatz_X_mul (A B y : PowerSeries (ZMod 2)) : qCollatz A B (X * y) = y := by
  simp [qCollatz, qShift_X_mul]

/-- **Zero is a fixed point of the q-analog 3x+1 map.** For all power series
$A, B \in \mathbb{F}_2[[q]]$, the $q$-analog $3x+1$ map satisfies $T_{A,B}(0) = 0$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T_{A,B}`). -/
theorem qCollatz_zero (A B : PowerSeries (ZMod 2)) : qCollatz A B 0 = 0 := by
  simpa using qCollatz_X_mul A B 0

/-- **Divisibility by $2$ from the residue modulo $2$.** If the residue modulo $2$ of a $2$-adic
integer $y \in \mathbb{Z}_2$ is zero, then $2$ divides $y$ in $\mathbb{Z}_2$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (parity in `ℤ₂`, so that `T` is a self-map). -/
theorem two_dvd_of_toZMod_eq_zero {y : ℤ_[2]} (h : PadicInt.toZMod y = 0) :
    (2 : ℤ_[2]) ∣ y := by
  have hy : y ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := h
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hy
  exact_mod_cast hy

/-- **$3x + 1$ is even for odd $2$-adic $x$.** For every $2$-adic integer $x \in \mathbb{Z}_2$ whose
residue modulo $2$ is nonzero, the residue of $3x + 1$ modulo $2$ is zero.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem toZMod_three_mul_add_one_of_odd {x : ℤ_[2]} (h : PadicInt.toZMod x ≠ 0) :
    PadicInt.toZMod (3 * x + 1) = 0 := by
  have key : ∀ a : ZMod 2, a ≠ 0 → 3 * a + 1 = 0 := by decide
  have h3 : PadicInt.toZMod (3 : ℤ_[2]) = 3 := map_ofNat _ 3
  rw [map_add, map_mul, map_one, h3]
  exact key _ h

/-- **The $2$-adic $3x+1$ map.** The map $T : \mathbb{Z}_2 \to \mathbb{Z}_2$ is defined by
$T(x) = x/2$ if $x$ is even and $T(x) = (3x+1)/2$ if $x$ is odd, where even and odd refer to the
residue of $x$ modulo $2$.

In both cases the numerator is divisible by $2$ in $\mathbb{Z}_2$, so the division is exact.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T` extended to `ℤ₂`). -/
noncomputable def twoAdicCollatz (x : ℤ_[2]) : ℤ_[2] :=
  if h : PadicInt.toZMod x = 0 then (two_dvd_of_toZMod_eq_zero h).choose
  else (two_dvd_of_toZMod_eq_zero (toZMod_three_mul_add_one_of_odd h)).choose

/-- **Even branch of the $2$-adic $3x+1$ map.** Let $T : \mathbb{Z}_2 \to \mathbb{Z}_2$ be
the $3x+1$ map on the $2$-adic integers. For every $x \in \mathbb{Z}_2$ whose residue modulo $2$
is zero, $2\,T(x) = x$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem two_mul_twoAdicCollatz_of_even {x : ℤ_[2]} (h : PadicInt.toZMod x = 0) :
    2 * twoAdicCollatz x = x := by
  simp only [twoAdicCollatz, h, dite_true]
  exact (two_dvd_of_toZMod_eq_zero h).choose_spec.symm

/-- **Odd branch of the $2$-adic $3x+1$ map.** Let $T : \mathbb{Z}_2 \to \mathbb{Z}_2$ be
the $3x+1$ map on the $2$-adic integers. For every $x \in \mathbb{Z}_2$ whose residue modulo $2$
is nonzero, $2\,T(x) = 3x + 1$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem two_mul_twoAdicCollatz_of_odd {x : ℤ_[2]} (h : PadicInt.toZMod x ≠ 0) :
    2 * twoAdicCollatz x = 3 * x + 1 := by
  simp only [twoAdicCollatz, h, dite_false]
  exact (two_dvd_of_toZMod_eq_zero (toZMod_three_mul_add_one_of_odd h)).choose_spec.symm

/-- **The $2$-adic $3x+1$ map swaps $1$ and $2$.** The $2$-adic $3x+1$ map
$T : \mathbb{Z}_2 \to \mathbb{Z}_2$ satisfies $T(1) = 2$ and $T(2) = 1$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T`). -/
theorem twoAdicCollatz_one_two : twoAdicCollatz 1 = 2 ∧ twoAdicCollatz 2 = 1 := by
  have h1 : (PadicInt.toZMod (1 : ℤ_[2]) : ZMod 2) ≠ 0 := by simp
  have h2 : (PadicInt.toZMod (2 : ℤ_[2]) : ZMod 2) = 0 := by
    rw [map_ofNat]; decide
  have h20 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  refine ⟨mul_left_cancel₀ h20 ?_, mul_left_cancel₀ h20 ?_⟩
  · rw [two_mul_twoAdicCollatz_of_odd h1]; norm_num
  · rw [two_mul_twoAdicCollatz_of_even h2]; norm_num

/-- **The parity vector of the q-analog 3x+1 map.** For power series
$A, B, x \in \mathbb{F}_2[[q]]$, the parity vector of $x$ is the $2$-adic integer
$\mathrm{PV}_{A,B}(x) = \sum_{k \ge 0} x_k 2^k \in \mathbb{Z}_2$, where $x_k \in \{0, 1\}$ is the
constant coefficient of the $k$-th iterate $T_{A,B}^k(x)$ of the $q$-analog $3x+1$ map $T_{A,B}$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Definition 10. -/
noncomputable def qCollatzParityVector (A B x : PowerSeries (ZMod 2)) : ℤ_[2] :=
  ∑' k : ℕ, ((constantCoeff ((qCollatz A B)^[k] x)).val : ℤ_[2]) * 2 ^ k

/-- **The parity vector of $0$.** For all $A, B \in \mathbb{F}_2[[q]]$, the parity vector of $0$
under the $q$-analog $T_{A,B}$ of the $3x+1$ map is $0$, that is, $\mathrm{PV}_{A,B}(0) = 0$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Definition 10. -/
theorem qCollatzParityVector_zero (A B : PowerSeries (ZMod 2)) :
    qCollatzParityVector A B 0 = 0 := by
  have h : ∀ k, (qCollatz A B)^[k] 0 = 0 := fun k =>
    Function.iterate_fixed (qCollatz_zero A B) k
  simp [qCollatzParityVector, h]

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

/-- **Iterates of $T_{A,B}$ move a perturbation at $q^{n+1}$ to $q^{n+1-k}$.** Let $A, B, U, V$
be power series in $\mathbb{F}_2[[q]]$ with $A$, $B$ and $V$ odd (constant term $1$), let
$T_{A,B}$ be the $q$-analog of the $3x+1$ map, and let $n$ and $k$ be natural numbers with
$k \le n + 1$. Write $T_{A,B}^k$ for the $k$-th iterate of $T_{A,B}$. Then there is an odd power
series $W \in \mathbb{F}_2[[q]]$ with $T_{A,B}^k(U + q^{n+1} V) = T_{A,B}^k(U) + q^{n+1-k} W$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 8 (`jis-2025-25.6.8-cor-8`). -/
public theorem_wanted qCollatz_iterate_add_X_pow_mul (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) (k : ℕ) (hk : k ≤ n + 1) :
    ∃ W : PowerSeries (ZMod 2), constantCoeff W ≠ 0 ∧
      (qCollatz A B)^[k] (U + X ^ (n + 1) * V) =
        (qCollatz A B)^[k] U + X ^ (n + 1 - k) * W

/-- **A perturbation at $q^n$ flips the parity of the $n$-th iterate.** Let
$A, B, U, V \in \mathbb{F}_2[[q]]$ with $A$, $B$ and $V$ odd (constant term $1$), let $T_{A,B}$ be
the $q$-analog of the $3x+1$ map, and let $n \ge 0$ be an integer. Then the $n$-th iterates
$T_{A,B}^n(U + q^n V)$ and $T_{A,B}^n(U)$ have different constant terms.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 9 (`jis-2025-25.6.8-cor-9`). -/
public theorem_wanted qCollatz_iterate_parity_flip (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) :
    constantCoeff ((qCollatz A B)^[n] (U + X ^ n * V)) ≠
      constantCoeff ((qCollatz A B)^[n] U)

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
