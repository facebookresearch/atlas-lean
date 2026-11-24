/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Data.ZMod.Basic

/-!
# Constant terms of powers of Laurent polynomials

Kohen's Cartier operator extracts the coefficients at multiples of an exponent scale.
It transfers a dilation of exponents from one factor of a constant term to the other.
Under Kohen's defining congruence for $\tilde P$, the constant terms of $P^n$ and $\tilde P^n$
agree modulo $p$ for every $n$.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Cartier operator $\Lambda_k$ on Laurent polynomials.** Let $R$ be a semiring and $f$ a
Laurent polynomial in $r$ variables with coefficients in $R$. For a natural number $k > 0$,
$\Lambda_k f$ keeps the terms of $f$ whose exponents are all multiples of $k$ and substitutes
$x_s^k \mapsto x_s$ for each variable, so that the coefficient of $x^j$ in $\Lambda_k f$ is the
coefficient of $x^{kj}$ in $f$ for every $j \in \mathbb{Z}^r$. For $k = 0$ it is set to
$\Lambda_0 f = 0$ (the paper uses only positive $k$).

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 2 (definition of `Λ_k`). -/
public noncomputable def laurentCartier {R : Type*} [Semiring R] {r : ℕ} (k : ℕ)
    (f : AddMonoidAlgebra R (Fin r → ℤ)) : AddMonoidAlgebra R (Fin r → ℤ) :=
  if hk : k = 0 then 0 else
    .ofCoeff (Finsupp.comapDomain (fun j => k • j) f.coeff
      (fun _ _ _ _ h => smul_right_injective (Fin r → ℤ) hk h))

/-- **Coefficients of Kohen's operator $\Lambda_k$.** Let $R$ be a semiring and let $r$ and
$k \ne 0$ be natural numbers. For every Laurent polynomial $f$ in $r$ variables with coefficients
in $R$ and every $j \in \mathbb{Z}^r$, the coefficient of $x^j$ in $\Lambda_k f$ is the
coefficient of $x^{kj}$ in $f$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 2 (definition of `Λ_k`). -/
public theorem coeff_laurentCartier {R : Type*} [Semiring R] {r k : ℕ} (hk : k ≠ 0)
    (f : AddMonoidAlgebra R (Fin r → ℤ)) (j : Fin r → ℤ) :
    (laurentCartier k f).coeff j = f.coeff (k • j) := by
  simp [laurentCartier, hk]

namespace constantTerm_pow_mul_modEq_tilde

private theorem coeff_zero_mapDomain_mul {R : Type*} [Semiring R] {r q : ℕ} (hq : q ≠ 0)
    (F G : AddMonoidAlgebra R (Fin r → ℤ)) :
    (AddMonoidAlgebra.mapDomain (fun j => q • j) F * G).coeff 0 =
      (F * laurentCartier q G).coeff 0 := by
  simp [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_mapDomain_index, add_mul,
    coeff_laurentCartier hq]

end constantTerm_pow_mul_modEq_tilde

namespace constantTerm_tilde_pow_mul_modEq_laurentCartier

private theorem pow_mul_modEq_cartier {r q m : ℕ} (hq : q ≠ 0)
    (F G R : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hFG : ∀ j, F.coeff j ≡ (AddMonoidAlgebra.mapDomain (fun j => q • j) G).coeff j [ZMOD m])
    (n : ℕ) :
    (F ^ n * R).coeff 0 ≡ (G ^ n * laurentCartier q R).coeff 0 [ZMOD m] := by
  let reduce := AddMonoidAlgebra.mapRingHom (Fin r → ℤ) (Int.castRingHom (ZMod m))
  let dilate := AddMonoidAlgebra.mapDomainRingHom ℤ (nsmulAddMonoidHom (α := Fin r → ℤ) q)
  have h : reduce F = reduce (dilate G) := by
    ext j
    exact (ZMod.intCast_eq_intCast_iff _ _ _).2 (hFG j)
  rw [← ZMod.intCast_eq_intCast_iff,
    ← constantTerm_pow_mul_modEq_tilde.coeff_zero_mapDomain_mul hq (G ^ n) R]
  change (reduce (F ^ n * R)).coeff 0 = (reduce (dilate (G ^ n) * R)).coeff 0
  simp only [map_mul, map_pow, h]

end constantTerm_tilde_pow_mul_modEq_laurentCartier

open constantTerm_tilde_pow_mul_modEq_laurentCartier

set_option linter.unusedVariables false in
/-- **Passing from $P$ to $\tilde P$ modulo $p^a$.** Let $p$ be a prime, let $a \ge 1$ and $\ell$
be natural numbers, and let $P$ and $\tilde P$ be Laurent polynomials in $r$ variables with
integer coefficients such that $P^{p^{a-1}} \equiv \tilde P(x^{p^\ell}) \pmod{p^a}$
coefficientwise, where $\tilde P(x^q)$ is obtained from $\tilde P$ by replacing each monomial
$x^e$ with $x^{qe}$. Write $\operatorname{ct}[F]$ for the constant term of a Laurent polynomial
$F$ and $\Lambda_q$ for Kohen's operator, which keeps the terms whose exponents are all divisible
by $q$ and replaces $x^{qj}$ by $x^j$. Then for every Laurent polynomial $Q$ in $r$ variables
with integer coefficients and all natural numbers $n$ and $k$,
$\operatorname{ct}[P^{p^{a-1} n + k} Q] \equiv
\operatorname{ct}[\tilde P^n \Lambda_{p^\ell}(P^k Q)] \pmod{p^a}$.

The statement holds for every natural number $k$; the paper restricts to $k < p^{a-1}$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 23 (`jis-2026-26.4.2-prop-23`). -/
public theorem constantTerm_pow_mul_modEq_tilde {r p a ℓ : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (P ^ (p ^ (a - 1))).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p ^ ℓ • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (P ^ (p ^ (a - 1) * n + k) * Q).coeff 0 ≡
      (Pt ^ n * laurentCartier (p ^ ℓ) (P ^ k * Q)).coeff 0 [ZMOD (p : ℤ) ^ a] := by
  rw [pow_add, pow_mul, mul_assoc, ← Nat.cast_pow]
  exact pow_mul_modEq_cartier (pow_ne_zero ℓ hp.ne_zero) _ Pt _ (by simpa using hPt) n

/-- **Rowland–Zeilberger congruence modulo $p^a$.** Let $p$ be a prime, let $a$ be a natural
number, and let $\tilde P$ be a Laurent polynomial in $r$ variables with integer coefficients
such that $\tilde P^p \equiv \tilde P(x^p) \pmod{p^a}$ coefficientwise, where $\tilde P(x^p)$
is obtained from $\tilde P$ by replacing each monomial $x^e$ with $x^{pe}$. Write
$\operatorname{ct}[F]$ for the constant term of a Laurent polynomial $F$ and $\Lambda_p$ for
Kohen's operator, which keeps the terms whose exponents are all divisible by $p$ and replaces
$x^{pj}$ by $x^j$. Then for every Laurent polynomial $Q$ in $r$ variables with integer
coefficients and all natural numbers $n$ and $k$,
$\operatorname{ct}[\tilde P^{pn+k} Q] \equiv
\operatorname{ct}[\tilde P^n \Lambda_p(\tilde P^k Q)] \pmod{p^a}$.

The statement holds for every natural number $k$; the paper states it for $k \in \mathbb{F}_p$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 24 (`jis-2026-26.4.2-lem-24`). -/
public theorem constantTerm_tilde_pow_mul_modEq_laurentCartier {r p a : ℕ}
    (hp : p.Prime) (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (Pt ^ (p * n + k) * Q).coeff 0 ≡ (Pt ^ n * laurentCartier p (Pt ^ k * Q)).coeff 0
      [ZMOD (p : ℤ) ^ a] := by
  rw [pow_add, pow_mul, mul_assoc, ← Nat.cast_pow]
  exact pow_mul_modEq_cartier hp.ne_zero _ Pt _ (by simpa using hPt) n

namespace exists_constantTerm_pow_dvd_iff_tilde

open AddMonoidAlgebra

private theorem constantTerm_pow_prime_pow_modEq {r p : ℕ} (hp : p.Prime) (k : ℕ)
    (F : AddMonoidAlgebra ℤ (Fin r → ℤ)) : (F ^ p ^ k).coeff 0 ≡ F.coeff 0 [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  let A := AddMonoidAlgebra (ZMod p) (Fin r → ℤ)
  let : CharP A p := charP_of_injective_ringHom
    (f := singleZeroRingHom (R := ZMod p)) single_right_injective p
  let dilate := mapDomainRingHom (ZMod p) (nsmulAddMonoidHom (α := Fin r → ℤ) (p ^ k))
  -- The iterated Frobenius fixes the prime field and scales each monomial's exponent.
  have hfrob : iterateFrobenius A p k = dilate := by
    apply AddMonoidAlgebra.ringHom_ext' (Subsingleton.elim _ _)
    apply MonoidHom.ext
    intro m
    change (single m.toAdd (1 : ZMod p)) ^ p ^ k = dilate (single m.toAdd 1)
    simp [dilate]
  let reduce := mapRingHom (Fin r → ℤ) (Int.castRingHom (ZMod p))
  rw [← ZMod.intCast_eq_intCast_iff]
  change (reduce (F ^ p ^ k)).coeff 0 = (reduce F).coeff 0
  rw [map_pow]
  change (iterateFrobenius A p k (reduce F)).coeff 0 = _
  rw [hfrob]
  change Finsupp.mapDomain (fun j => p ^ k • j) (reduce F).coeff 0 = _
  simpa only [smul_zero] using Finsupp.mapDomain_apply_of_injective
    (smul_right_injective (Fin r → ℤ) (pow_ne_zero k hp.ne_zero)) (reduce F).coeff 0

private theorem cartier_one {r q : ℕ} (hq : q ≠ 0) :
    laurentCartier q (1 : AddMonoidAlgebra ℤ (Fin r → ℤ)) = 1 := by
  simpa only [laurentCartier, dite_eq_right hq, one_def, comapDomain, smul_zero] using
    comapDomain_single_map (fun j : Fin r → ℤ => q • j) (smul_right_injective (Fin r → ℤ) hq)
      0 (1 : ℤ)

end exists_constantTerm_pow_dvd_iff_tilde

open exists_constantTerm_pow_dvd_iff_tilde

/-- **Divisibility of constant terms of powers of $P$ and $\tilde P$.** Let $p$ be a prime, let
$a \ge 1$ and $\ell$ be natural numbers, and let $P$ and $\tilde P$ be Laurent polynomials in $r$
variables with integer coefficients such that $P^{p^{a-1}} \equiv \tilde P(x^{p^\ell}) \pmod{p^a}$
coefficientwise, where $\tilde P(x^q)$ is obtained from $\tilde P$ by replacing each monomial
$x^e$ with $x^{qe}$. Write $\operatorname{ct}[F]$ for the constant term of a Laurent polynomial
$F$. Then $p$ divides $\operatorname{ct}[P^{n_0}]$ for some natural number $n_0$ if and only if
$p$ divides $\operatorname{ct}[\tilde P^{n_1}]$ for some natural number $n_1$; moreover, for every
natural number $n_0$ with $p \mid \operatorname{ct}[P^{n_0}]$, also
$p \mid \operatorname{ct}[\tilde P^{n_0}]$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 22 (`jis-2026-26.4.2-lem-22`). -/
public theorem exists_constantTerm_pow_dvd_iff_tilde {r p a ℓ : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (P ^ (p ^ (a - 1))).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p ^ ℓ • j) Pt).coeff j [ZMOD (p : ℤ) ^ a]) :
    ((∃ n₀, (p : ℤ) ∣ (P ^ n₀).coeff 0) ↔ ∃ n₁, (p : ℤ) ∣ (Pt ^ n₁).coeff 0) ∧
      ∀ n₀, (p : ℤ) ∣ (P ^ n₀).coeff 0 → (p : ℤ) ∣ (Pt ^ n₀).coeff 0 := by
  have same (n : ℕ) : (P ^ n).coeff 0 ≡ (Pt ^ n).coeff 0 [ZMOD p] := by
    apply (constantTerm_pow_prime_pow_modEq hp (a - 1) (P ^ n)).symm.trans
    apply Int.ModEq.of_dvd (dvd_pow_self (p : ℤ) ha.ne')
    simpa only [pow_zero, add_zero, mul_one, cartier_one (pow_ne_zero ℓ hp.ne_zero),
      ← pow_mul, Nat.mul_comm n] using constantTerm_pow_mul_modEq_tilde hp ha P Pt hPt 1 n 0
  exact ⟨exists_congr fun n => (same n).dvd_iff, fun n => (same n).dvd_iff.mp⟩

end

end MetaMathlibExt
