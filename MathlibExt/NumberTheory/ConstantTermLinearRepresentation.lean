/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Basic

/-!
# Constant terms of powers of Laurent polynomials

Kohen's Cartier operator extracts the coefficients at multiples of an exponent scale.
It transfers a dilation of exponents from one factor of a constant term to the other.
Under Kohen's defining congruence for $\tilde P$, the constant terms of $P^n$ and $\tilde P^n$
agree modulo $p$ for every $n$. The powers of the zero-digit matrix stabilize at the matrix
unit indexed by the origin.
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

/-- **Degree of a Laurent polynomial.** Let $R$ be a semiring and let $f$ be a Laurent polynomial
in $r$ variables $x_1, \dots, x_r$ with coefficients in $R$. Kohen's degree $\deg f$ of $f$ is the
largest absolute value $|j_i|$ of a single exponent, taken over all $i$ and all exponent vectors
$j \in \mathbb{Z}^r$ whose monomial $x^j$ has nonzero coefficient in $f$, and is $0$ if there is
no such exponent (in particular for the zero polynomial). For example, over $\mathbb{Z}$ in two
variables $x, y$ one has $\deg(5x^{-3}y^{-2} + 2xy^{-1}) = 3$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 1.1. -/
public def laurentDeg {R : Type*} [Semiring R] {r : ℕ}
    (f : AddMonoidAlgebra R (Fin r → ℤ)) : ℕ :=
  f.coeff.support.sup fun j => Finset.univ.sup fun i => (j i).natAbs

/-- **Exponent criterion for the degree of a Laurent polynomial.** Let $R$ be a semiring, let
$r$ and $m$ be natural numbers, and let $f$ be a Laurent polynomial in $r$ variables
$x_1, \dots, x_r$ with coefficients in $R$. Then Kohen's degree of $f$ (the largest absolute
value of a single exponent occurring in $f$, or $0$ if there is none) is at most $m$ if and only
if every exponent vector $j \in \mathbb{Z}^r$ whose monomial $x^j$ has nonzero coefficient in
$f$ satisfies $|j_i| \le m$ for every $i$, that is, lies in $[-m, m]^r$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 1.1. -/
public theorem laurentDeg_le_iff {R : Type*} [Semiring R] {r : ℕ}
    (f : AddMonoidAlgebra R (Fin r → ℤ)) (m : ℕ) :
    laurentDeg f ≤ m ↔ ∀ j ∈ f.coeff.support, ∀ i, (j i).natAbs ≤ m := by
  simp [laurentDeg, Finset.sup_le_iff]

namespace laurentCartier_pow_mul_single_eq_sum

private theorem laurentDeg_pow_le {R : Type*} [Semiring R] {r : ℕ}
    (f : AddMonoidAlgebra R (Fin r → ℤ)) (k : ℕ) :
    laurentDeg (f ^ k) ≤ k * laurentDeg f := by
  classical
  induction k with
  | zero =>
    rw [laurentDeg_le_iff]
    intro j hj i
    simp only [pow_zero] at hj
    have hj0 : j = 0 := by
      by_contra hne
      have h0 : (1 : AddMonoidAlgebra R (Fin r → ℤ)).coeff j = 0 := by
        simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
          Finsupp.single_apply, hne, eq_comm, ite_false]
      exact Finsupp.mem_support_iff.mp hj h0
    subst hj0
    simp
  | succ k ih =>
    rw [laurentDeg_le_iff]
    intro j hj i
    rw [pow_succ] at hj
    have hj' := AddMonoidAlgebra.support_coeff_mul_subset (f ^ k) f hj
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hj'
    rw [← hab]
    have ha' := (laurentDeg_le_iff (f ^ k) _).mp ih a ha i
    have hb' := (laurentDeg_le_iff f _).mp le_rfl b hb i
    have htri : ((a + b) i).natAbs ≤ (a i).natAbs + (b i).natAbs := by
      simpa using Int.natAbs_add_le (a i) (b i)
    have hmul : (k + 1) * laurentDeg f = k * laurentDeg f + laurentDeg f := by ring
    omega

end laurentCartier_pow_mul_single_eq_sum

open laurentCartier_pow_mul_single_eq_sum in
/-- **Cartier operator applied to a power times a monomial.** Let $p$ be a prime and $P$ a
Laurent polynomial in $r$ variables with integer coefficients. Write $\mathrm{coef}_e[F]$ for the
coefficient of $x^e$ in a Laurent polynomial $F$, $\deg F$ for the largest absolute value of an
exponent of a variable occurring in $F$, and $\Lambda_p$ for the Cartier operator with
$\mathrm{coef}_j[\Lambda_p F] = \mathrm{coef}_{pj}[F]$. Let $m \in \mathbb{N}$ with
$\deg P \le m + 1$, put $T = [-m, m]^r \subset \mathbb{Z}^r$, and let $k < p$ be a natural
number and $i \in T$. Then
$\Lambda_p(P^k x^i) = \sum_{j \in T} \mathrm{coef}_{pj - i}[P^k] \, x^j$.

In Kohen's notation $\mathrm{coef}_{pj - i}[P^k]$ is $a^k_{i - pj}$. Kohen states the identity
over the prime field $\mathbb{F}_p$; here it holds over $\mathbb{Z}$, an integral lift from which
Kohen's version follows by reducing the coefficients modulo $p$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 6 (`jis-2026-26.4.2-prop-6`). -/
public theorem laurentCartier_pow_mul_single_eq_sum {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) (k : ℕ)
    (hk : k < p) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    laurentCartier p (P ^ k * AddMonoidAlgebra.single i 1) =
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        AddMonoidAlgebra.single j ((P ^ k).coeff (p • j - i)) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  ext e
  rw [coeff_laurentCartier hp0]
  have hL : (P ^ k * AddMonoidAlgebra.single i 1).coeff (p • e) =
      (P ^ k).coeff (p • e - i) := by
    have h := AddMonoidAlgebra.coeff_mul_single_add (P ^ k) (1 : ℤ) i (p • e - i)
    rwa [sub_add_cancel, mul_one] at h
  rw [hL]
  have hsum : (∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        AddMonoidAlgebra.single j ((P ^ k).coeff (p • j - i))).coeff e =
      if e ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) then
        (P ^ k).coeff (p • e - i) else 0 := by
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      Finset.sum_ite_eq', Fintype.mem_piFinset]
  rw [hsum]
  by_cases he : e ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m)
  · simp only [he, ite_true]
  · simp only [he, ite_false]
    by_contra hne
    have hmem : p • e - i ∈ (P ^ k).coeff.support := Finsupp.mem_support_iff.mpr hne
    have hbound := (laurentDeg_le_iff (P ^ k) _).mp
      (laurentDeg_pow_le P k) (p • e - i) hmem
    obtain ⟨t, ht⟩ : ∃ t, e t ∉ Finset.Icc (-(m : ℤ)) m := by
      have hnot : ¬ ∀ t, e t ∈ Finset.Icc (-(m : ℤ)) m :=
        fun h => he (Fintype.mem_piFinset.mpr h)
      obtain ⟨t, ht⟩ := not_forall.mp hnot
      exact ⟨t, ht⟩
    have hbox : e t < -(m : ℤ) ∨ (m : ℤ) < e t := by
      rw [Finset.mem_Icc] at ht
      omega
    have hi_t : (i t).natAbs ≤ m := by
      have hibt := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hi t)
      omega
    have hsub : (p • e - i) t = (p : ℤ) * e t - i t := by
      simp [Pi.sub_apply, nsmul_eq_mul]
    have hle : ((p : ℤ) * e t - i t).natAbs ≤ k * laurentDeg P := by
      have hbt := hbound t
      rwa [hsub] at hbt
    have htri : ((p : ℤ) * e t).natAbs ≤
        ((p : ℤ) * e t - i t).natAbs + (i t).natAbs := by
      have h := Int.natAbs_add_le ((p : ℤ) * e t - i t) (i t)
      rwa [sub_add_cancel] at h
    have hnat : ((p : ℤ) * e t).natAbs = p * (e t).natAbs := by
      simp [Int.natAbs_mul]
    have hem : m + 1 ≤ (e t).natAbs := by
      rcases hbox with h | h <;> omega
    have hpE : p * (m + 1) ≤ p * (e t).natAbs := Nat.mul_le_mul_left p hem
    have hprod : k * laurentDeg P + (m + 1) ≤ p * (m + 1) := by
      have h1 : k * laurentDeg P ≤ k * (m + 1) := Nat.mul_le_mul_left k hm
      have h2 : (k + 1) * (m + 1) ≤ p * (m + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : (k + 1) * (m + 1) = k * (m + 1) + (m + 1) := by ring
      omega
    omega

-- Keep the two proofs of origin membership inline in the matrix indices.
set_option backward.proofsInPublic true in
/-- **Powers of $\gamma(0)$ modulo $p$ stabilize at a matrix unit.** Let $p$ be a prime, let
$r, m \ge 0$ be natural numbers, let $T = \{-m, \dots, m\}^r \subseteq \mathbb{Z}^r$, and let
$\gamma(0)$ be the $T \times T$ matrix over $\mathbb{Z}/p\mathbb{Z}$ whose $(i, j)$ entry is $1$
if $i = p j$ and $0$ otherwise. Then there is $s \in \mathbb{N}$ such that for every $s' \ge s$,
$\gamma(0)^{s'}$ is the matrix whose $(0, 0)$ entry is $1$ and whose other entries are $0$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 11 (`jis-2026-26.4.2-lem-11`). -/
public theorem exists_gammaZero_pow_eq_single {p : ℕ} (hp : p.Prime) (r m : ℕ) :
    ∃ s : ℕ, ∀ s' ≥ s,
      (Matrix.of fun i j : ↥(Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) =>
        if (i : Fin r → ℤ) = p • (j : Fin r → ℤ) then (1 : ZMod p) else 0) ^ s' =
        Matrix.single ⟨0, by simp⟩ ⟨0, by simp⟩ 1 := by
  let T := Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m
  let A := Matrix.of fun i j : ↥T => if i.val = p • j.val then (1 : ZMod p) else 0
  let z : ↥T := ⟨0, by simp [T]⟩
  -- A nonzero entry of a power follows a chain of dilations inside the box.
  have support (n : ℕ) (i j : ↥T) (h : (A ^ n) i j ≠ 0) : i.val = p ^ n • j.val := by
    induction n generalizing i j with
    | zero =>
      by_contra hne
      have hij : i ≠ j := by simpa using hne
      simp [hij] at h
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply] at h
      obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have hkj : k.val = p • j.val := by
        by_contra hne
        simp only [A, Matrix.of_apply, ite_eq_right hne, mul_zero, ne_self_iff_false] at hk
      rw [ih i k (left_ne_zero_of_mul hk), hkj, smul_smul, pow_succ]
  have origin (n : ℕ) : (A ^ n) z z = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      have hz (k : ↥T) : A k z = if k = z then 1 else 0 := by
        simp [A, z, Subtype.ext_iff]
      simpa [hz, mul_ite] using ih
  refine ⟨m, ?_⟩
  change ∀ n ≥ m, A ^ n = Matrix.single z z 1
  intro n hn
  ext i j
  by_cases hij : z = i ∧ z = j
  · obtain ⟨rfl, rfl⟩ := hij
    simpa using origin n
  rw [Matrix.single_apply, ite_eq_right hij]
  by_contra h
  have heq := support n i j h
  have hi : i.val = 0 := by
    funext t
    have hbox := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp i.property t)
    have hc := congrFun heq t
    simp only [Pi.smul_apply, nsmul_eq_mul] at hc
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j.val t, hc⟩
    exact (show (i.val t).natAbs ≤ m by omega).trans_lt (hn.trans_lt (n.lt_pow_self hp.one_lt))
  have hj : j.val = 0 := smul_right_injective (Fin r → ℤ) (pow_ne_zero n hp.ne_zero)
    (by simpa only [smul_zero] using heq.symm.trans hi)
  exact hij ⟨Subtype.ext hi.symm, Subtype.ext hj.symm⟩

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
