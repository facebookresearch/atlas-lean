/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Choose.Factorization
import MathlibExt.NumberTheory.PrimeGapLiminf

/-!
# Completely additive heights and the ordinary partition profile

For the constant profile, the height of a prime is its one-based index. Chebyshev bounds
on the prime count control the prime-harmonic sum. Complete additivity turns the sum of
heights up to an integer into the height of its factorial.

For a completely additive height $H$ on the positive integers, with positive prime heights
and finite prime fibers, the level at any $n \ge 0$ is counted by coloured partitions of $n$.
The colour multiplicity at size $\ell$ is the number of primes of height $\ell$. Prime
exponents give the part multiplicities, with $1$ corresponding to the empty partition at $n=0$.
This is the fixed-level counting consequence of the bijection in Proposition 1.

## References

* Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds, and
  Inverse Growth*, INTEGERS 26 (2026), Article A116, pp. 1–45. The multipartition correspondence
  is Proposition 1 (pp. 4–5); the ordinary partition profile growth laws are Corollary 3.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Completely additive functions on the positive integers.** A function
$H : \mathbb{N} \to \mathbb{N}$ is completely additive on the positive integers if
$H(ab) = H(a) + H(b)$ for all integers $a, b \ge 1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public def IsCompletelyAdditiveNat (H : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → H (a * b) = H a + H b

/-- **A completely additive function vanishes at one.** If $H : \mathbb{N} \to \mathbb{N}$ is
completely additive on the positive integers, that is, $H(ab) = H(a) + H(b)$ for all $a, b \ge 1$,
then $H(1) = 0$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public theorem IsCompletelyAdditiveNat.map_one {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    H 1 = 0 := by
  have := hH 1 1 one_pos one_pos
  simp at this
  omega

/-- **Height functions.** A function $H : \mathbb{N} \to \mathbb{N}$ is a height function if it is
completely additive on the positive integers, that is $H(ab) = H(a) + H(b)$ for all integers
$a, b \ge 1$; if $H(p) \ge 1$ for every prime $p$; and if for every $n \ge 1$ only finitely many
primes $p$ have $H(p) = n$.

Complete additivity forces $H(1) = 0$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public structure IsHeightFunction (H : ℕ → ℕ) : Prop where
  additive : IsCompletelyAdditiveNat H
  prime_pos : ∀ p : ℕ, p.Prime → 1 ≤ H p
  finite_primes : ∀ n : ℕ, 1 ≤ n → {p : ℕ | p.Prime ∧ H p = n}.Finite

/-- **Level construction for a height function.** Let $H$ be a height function and let $n \ge 1$,
and for $k \ge 0$ write $\mathcal{H}_k = \{m \ge 1 : H(m) = k\}$. Then $\mathcal{H}_n$ is the union
of two sets: the set of products $p m'$, where $p$ is a prime with $H(p) = \ell$ for some integer
$\ell$ with $1 \le \ell \le \lfloor n/2 \rfloor$ and $m' \in \mathcal{H}_{n - \ell}$; and the set
of primes $p$ with $H(p) = n$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 1 (`integers-2026-A116-thm-1`). -/
public theorem heightLevel_eq_products_union_primes {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {n : ℕ} (hn : 1 ≤ n) :
    {m : ℕ | 0 < m ∧ H m = n} =
      {m : ℕ | ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ n / 2 ∧ ∃ p m', p.Prime ∧ H p = ℓ ∧ 0 < m' ∧ H m' = n - ℓ ∧
        m = p * m'} ∪ {p : ℕ | p.Prime ∧ H p = n} := by
  ext m
  constructor
  · rintro ⟨hm, hmn⟩
    by_cases hmprime : m.Prime
    · exact Or.inr ⟨hmprime, hmn⟩
    left
    have hm₁ : m ≠ 1 := by
      rintro rfl
      rw [hH.additive.map_one] at hmn
      omega
    -- Choose a prime factor of least height. Its cofactor still has a prime factor.
    obtain ⟨p, hpm, hmin⟩ := m.primeFactors.exists_min_image H
      (Nat.nonempty_primeFactors.mpr (by omega))
    obtain ⟨hp, ⟨k, rfl⟩, _⟩ := Nat.mem_primeFactors.mp hpm
    have hkpos : 0 < k := Nat.pos_of_mul_pos_left hm
    have hsmall : H p ≤ H k := by
      have hk : k ≠ 1 := by
        rintro rfl
        exact hmprime (by simpa using hp)
      obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk
      refine (hmin q (hq.mem_primeFactors (dvd_mul_of_dvd_right hqk p) hm.ne')).trans ?_
      obtain ⟨r, rfl⟩ := hqk
      rw [hH.additive q r hq.pos (Nat.pos_of_mul_pos_left hkpos)]
      exact Nat.le_add_right _ _
    rw [hH.additive p k hp.pos hkpos] at hmn
    exact ⟨H p, hH.prime_pos p hp, by omega, p, k, hp, rfl, hkpos, by omega, rfl⟩
  · rintro (⟨ℓ, _, hℓ, p, k, hp, hpℓ, hk, hHk, rfl⟩ | ⟨hp, hpn⟩)
    · refine ⟨Nat.mul_pos hp.pos hk, ?_⟩
      rw [hH.additive p k hp.pos hk, hpℓ, hHk]
      omega
    · exact ⟨hp.pos, hpn⟩

/-- **The $i$-th prime.** For a natural number $i \ge 1$, $p_i$ denotes the $i$-th prime in
increasing order, so that $p_1 = 2$. For $i = 0$ the definition also gives $p_0 = 2$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (notation `pᵢ`). -/
public noncomputable def nthPrimeOne (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i - 1)

/-- **The first three primes.** With primes indexed from one, the first three primes are
$p_1 = 2$, $p_2 = 3$ and $p_3 = 5$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (notation `pᵢ`). -/
public theorem nthPrimeOne_one_two_three :
    nthPrimeOne 1 = 2 ∧ nthPrimeOne 2 = 3 ∧ nthPrimeOne 3 = 5 :=
  ⟨Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five⟩

/-- **The $k$-th prime exceeds $2k$ for $k \ge 6$.** For every natural number $k \ge 6$, the
$k$-th prime $p_k$, indexed from one so that $p_1 = 2$, satisfies $p_k > 2k$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 2 (`integers-2026-A116-lem-2`). -/
public theorem two_mul_lt_nthPrimeOne {k : ℕ} (hk : 6 ≤ k) : 2 * k < nthPrimeOne k := by
  unfold nthPrimeOne
  induction k, hk using Nat.le_induction with
  | base =>
    exact (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp
      (by decide : Nat.count Nat.Prime 13 ≤ 5)
  | succ k hk ih =>
    have hgap := MathlibExt.NumberTheory.two_le_primeGap (k - 1) (by omega)
    unfold primeGap at hgap
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hgap
    change 2 * (k + 1) < Nat.nth Nat.Prime k
    omega

/-- **Completely additive function with prescribed prime values.** Given a function
$v : \mathbb{N} \to \mathbb{N}$, this is the function $\mathbb{N} \to \mathbb{N}$ that sends each
$m \ge 1$ with prime factorization $m = \prod_p p^{a_p}$ to $\sum_p a_p\, v(p)$, and sends $0$
to $0$. Only the values of $v$ at primes matter.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public noncomputable def additiveOfPrimeValues (v : ℕ → ℕ) (m : ℕ) : ℕ :=
  m.factorization.sum fun p a => a * v p

/-- **The completely additive extension vanishes at one.** For every function
$v : \mathbb{N} \to \mathbb{N}$, the completely additive function with prime values $v$ (which
sends $m = \prod_p p^{a_p}$ to $\sum_p a_p\, v(p)$) takes the value $0$ at $1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem additiveOfPrimeValues_one (v : ℕ → ℕ) : additiveOfPrimeValues v 1 = 0 := by
  simp [additiveOfPrimeValues]

/-- **The completely additive extension at a prime.** For every function
$v : \mathbb{N} \to \mathbb{N}$ and every prime $p$, the completely additive function with prime
values $v$ (which sends $m = \prod_q q^{a_q}$ to $\sum_q a_q\, v(q)$) takes the value $v(p)$
at $p$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem additiveOfPrimeValues_prime (v : ℕ → ℕ) {p : ℕ} (hp : p.Prime) :
    additiveOfPrimeValues v p = v p := by
  simp [additiveOfPrimeValues, hp.factorization]

/-- **The extension from prime values is completely additive.** For every function
$v : \mathbb{N} \to \mathbb{N}$, let $H_v$ be the function with $H_v(m) = \sum_p a_p v(p)$ for
$m = \prod_p p^{a_p}$. Then $H_v$ is completely additive on the positive integers:
$H_v(ab) = H_v(a) + H_v(b)$ for all integers $a, b \ge 1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem isCompletelyAdditiveNat_additiveOfPrimeValues (v : ℕ → ℕ) :
    IsCompletelyAdditiveNat (additiveOfPrimeValues v) := by
  intro a b ha hb
  unfold additiveOfPrimeValues
  rw [Nat.factorization_mul ha.ne' hb.ne']
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

namespace sum_height_eq_sum_prime_powers

open Finset

private theorem height_eq_prime_values {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (n : ℕ) (hn : 0 < n) : H n = additiveOfPrimeValues H n := by
  induction n using Nat.prime_composite_induction with
  | zero => omega
  | one => rw [hH.map_one, additiveOfPrimeValues_one]
  | prime p hp => exact (additiveOfPrimeValues_prime H hp).symm
  | composite a ha iha b hb ihb =>
    have ha' : 0 < a := by omega
    have hb' : 0 < b := by omega
    rw [hH a b ha' hb', isCompletelyAdditiveNat_additiveOfPrimeValues H a b ha' hb',
      iha ha', ihb hb']

private theorem sum_height_eq_factorization_sum {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (n : ℕ) :
    ∑ k ∈ Icc 1 n, H k = ∑ p ∈ n.primesLE, n.factorial.factorization p * H p := by
  have hfac : ∑ k ∈ Icc 1 n, H k = H n.factorial := by
    induction n with
    | zero => simp [hH.map_one]
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
        hH _ _ (Nat.succ_pos n) (Nat.factorial_pos n), add_comm]
  rw [hfac, height_eq_prime_values hH _ (Nat.factorial_pos n), additiveOfPrimeValues]
  apply Finsupp.sum_of_support_subset _ _ _ (by simp)
  intro p hp
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primesLE.mpr ⟨hprime.dvd_factorial.mp hdvd, hprime⟩

end sum_height_eq_sum_prime_powers

/-- **Height levels are counted by coloured partitions.** Let $H$ be a height function and, for
$\ell \ge 1$, let $\pi_\ell$ be the number of primes $p$ with $H(p) = \ell$. For every $n \ge 0$,
the number of positive integers $m$ with $H(m) = n$ equals the number of families
$(\alpha_{\ell,j})$ of nonnegative integers indexed by $1 \le \ell \le n$ and $0 \le j < \pi_\ell$
with $\sum_{\ell,j} \ell\, \alpha_{\ell,j} = n$, that is, the number of partitions of $n$ in which
a part of size $\ell$ comes in $\pi_\ell$ colours.

This is the level-by-level form of the statement that $H$ induces a height-preserving bijection
between the positive integers and such coloured partitions.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 1
(`integers-2026-A116-prop-1`). -/
public theorem heightLevel_card_eq_multipartitions {H : ℕ → ℕ} (hH : IsHeightFunction H)
    (n : ℕ) :
    Nat.card {m : ℕ // 0 < m ∧ H m = n} =
      Nat.card {α : (Σ ℓ : Fin n, Fin {p : ℕ | p.Prime ∧ H p = ℓ.1 + 1}.ncard) → ℕ //
        ∑ x, (x.1.1 + 1) * α x = n} := by
  classical
  let fiber (ℓ : Fin n) : Set ℕ := {p | p.Prime ∧ H p = ℓ.1 + 1}
  let Labels := Σ ℓ : Fin n, Fin (fiber ℓ).ncard
  let e (ℓ : Fin n) : Fin (fiber ℓ).ncard ≃ fiber ℓ := by
    letI : Finite (fiber ℓ) := (hH.finite_primes (ℓ.1 + 1) (Nat.succ_pos _)).to_subtype
    exact (Finite.equivFin (fiber ℓ)).symm
  let primeOf (i : Labels) : ℕ := (e i.1 i.2).1
  have hprime (i : Labels) : (primeOf i).Prime := (e i.1 i.2).2.1
  have hweight (i : Labels) : H (primeOf i) = i.1.1 + 1 := (e i.1 i.2).2.2
  let p : Labels ↪ ℕ := ⟨primeOf, by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := Fin.ext (Nat.succ.inj ((hweight ⟨i, a⟩).symm.trans
      ((congrArg H h).trans (hweight ⟨j, b⟩))))
    subst j
    exact congrArg (Sigma.mk i) ((e i).injective (Subtype.ext h))⟩
  -- Every prime divisor of a positive integer at level n has a label.
  have hsupp (m : {m : ℕ // 0 < m ∧ H m = n}) :
      ↑m.1.factorization.support ⊆ Set.range p := by
    intro q hq
    obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp (by simpa using hq)
    obtain ⟨k, hk⟩ := hqdvd
    have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ m.2.1)
    have hqle : H q ≤ n := by
      rw [← m.2.2, hk, hH.additive q k hqprime.pos hkpos]
      exact Nat.le_add_right _ _
    have hqpos := hH.prime_pos q hqprime
    let ℓ : Fin n := ⟨H q - 1, by omega⟩
    let r : fiber ℓ := ⟨q, hqprime, by dsimp [ℓ]; omega⟩
    exact ⟨⟨ℓ, (e ℓ).symm r⟩, congrArg Subtype.val ((e ℓ).apply_symm_apply r)⟩
  have sum_labels (f : ℕ →₀ ℕ) (hf : ↑f.support ⊆ Set.range p) :
      f.sum (fun q a => a * H q) = ∑ i : Labels, (i.1.1 + 1) * f (p i) := by
    have hs : f.support ⊆ Finset.univ.map p := by
      intro q hq
      obtain ⟨i, rfl⟩ := hf hq
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [Finsupp.sum_of_support_subset f hs (fun q a => a * H q) (fun _ _ => zero_mul _),
      Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by rw [show H (p i) = _ from hweight i, Nat.mul_comm]
  -- Extend the multiplicities by zero outside the labelled primes before inverting factorization.
  let extend (a : Labels → ℕ) : ℕ →₀ ℕ := (Finsupp.equivFunOnFinite.symm a).embDomain p
  have extend_support (a : Labels → ℕ) : ↑(extend a).support ⊆ Set.range p := by
    simp only [extend, Finsupp.support_embDomain, Finset.coe_map]
    exact Set.image_subset_range _ _
  let factors (a : Labels → ℕ) : {f : ℕ →₀ ℕ // ∀ q ∈ f.support, q.Prime} :=
    ⟨extend a, fun q hq => by
      obtain ⟨i, rfl⟩ := extend_support a hq
      exact hprime i⟩
  let rebuild (a : Labels → ℕ) : ℕ+ := Nat.factorizationEquiv.symm (factors a)
  have hfac (a : Labels → ℕ) : (rebuild a : ℕ).factorization = extend a :=
    congrArg Subtype.val (Nat.factorizationEquiv.apply_symm_apply (factors a))
  refine Nat.card_congr
    { toFun := fun m => ⟨fun i => m.1.factorization (p i), ?_⟩
      invFun := fun a => ⟨rebuild a.1, (rebuild a.1).2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← sum_labels _ (hsupp m), ← additiveOfPrimeValues,
      ← sum_height_eq_sum_prime_powers.height_eq_prime_values hH.additive _ m.2.1]
    exact m.2.2
  · calc
      H (rebuild a.1) = additiveOfPrimeValues H (rebuild a.1) :=
        sum_height_eq_sum_prime_powers.height_eq_prime_values hH.additive _ (rebuild a.1).2
      _ = n := by
        rw [additiveOfPrimeValues, hfac, sum_labels _ (extend_support a.1)]
        simpa only [extend, Finsupp.embDomain_apply_self, Finsupp.coe_equivFunOnFinite_symm]
          using a.2
  · intro m
    apply Subtype.ext
    apply Nat.factorization_inj (show (rebuild _ : ℕ) ≠ 0 from (rebuild _).2.ne') m.2.1.ne'
    rw [hfac]
    change extend (fun i => m.1.factorization (p i)) = m.1.factorization
    rw [show (fun i => m.1.factorization (p i)) =
      ⇑(Finsupp.comapDomain p m.1.factorization p.injective.injOn) from rfl]
    dsimp only [extend]
    rw [Finsupp.equivFunOnFinite_symm_coe]
    exact Finsupp.embDomain_comapDomain (hsupp m)
  · intro a
    apply Subtype.ext
    funext i
    change (rebuild a.1 : ℕ).factorization (p i) = a.1 i
    rw [hfac]
    simp only [extend, Finsupp.embDomain_apply_self, Finsupp.coe_equivFunOnFinite_symm]

/-- **Prime-power decomposition of summatory heights.** Let $H : \mathbb{N} \to \mathbb{N}$ be
completely additive on the positive integers, and let $x \ge 2$ be a natural number. Then
$$\sum_{m=1}^{x} H(m) = \sum_{p \le x} \sum_{\alpha \ge 1,\ p^\alpha \le x} H(p)
\left\lfloor \frac{x}{p^\alpha} \right\rfloor,$$
where $p$ runs over the primes $p \le x$.

The paper states this for real $x \ge 2$; both sides depend on $x$ only through $\lfloor x \rfloor$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7
(`integers-2026-A116-prop-7`), Equation (6). -/
public theorem sum_height_eq_sum_prime_powers {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    {x : ℕ} (hx : 2 ≤ x) :
    ∑ m ∈ Finset.Icc 1 x, H m =
      ∑ p ∈ (Finset.Iic x).filter Nat.Prime,
        ∑ α ∈ (Finset.Icc 1 x).filter (fun α => p ^ α ≤ x), H p * (x / p ^ α) := by
  rw [sum_height_eq_sum_prime_powers.sum_height_eq_factorization_sum hH,
    ← Nat.range_succ_eq_Iic, ← Nat.primesLE_eq_filter_range]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hcut : (Finset.Icc 1 x).filter (fun α => p ^ α ≤ x) = Finset.Icc 1 (Nat.log p x) := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_Icc,
      ← Nat.le_log_iff_pow_le hprime.one_lt (by omega : x ≠ 0)]
    have := Nat.log_le_self p x
    omega
  rw [hcut, Nat.factorization_factorial hprime (Nat.lt_add_one (Nat.log p x)),
    Finset.Ico_add_one_right_eq_Icc, Nat.mul_comm, Finset.mul_sum]

/-- **Gutman–Ivić maximal Matula numbers.** Write $p_i$ for the $i$-th prime, indexed from one
($p_1 = 2$). For a natural number $n$, $P(n)$ is the result of applying $i \mapsto p_i$ to $8$
exactly $n - 3$ times, so $P(4) = p_8$ and $P(n) = p_{P(n-1)}$ for $n \ge 5$. For $n \le 3$ there
are no applications and $P(n) = 8$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public noncomputable def matulaMax (n : ℕ) : ℕ :=
  nthPrimeOne^[n - 3] 8

/-- **The first maximal Matula number.** The Gutman–Ivić maximal Matula number $P(4)$ equals
$p_8$, the eighth prime.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public theorem matulaMax_four : matulaMax 4 = nthPrimeOne 8 :=
  rfl

/-- **Recursion for the maximal Matula numbers.** Write $p_i$ for the $i$-th prime, indexed from
one ($p_1 = 2$). For every $n \ge 4$ the Gutman–Ivić maximal Matula numbers satisfy
$P(n + 1) = p_{P(n)}$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public theorem matulaMax_succ {n : ℕ} (hn : 4 ≤ n) :
    matulaMax (n + 1) = nthPrimeOne (matulaMax n) := by
  unfold matulaMax
  rw [show n + 1 - 3 = (n - 3) + 1 by omega, Function.iterate_succ_apply']

/-- **Weighted partition coefficients.** Given real weights $(b_k)_{k \ge 0}$, the coefficients
$a_n$ of the weighted partition product $\prod_{k \ge 1} (1 - q^k)^{-b_k}$ are defined by $a_0 = 1$
and, for $n \ge 1$, the logarithmic-derivative recurrence
$n a_n = \sum_{m=1}^{n} \big(\sum_{k \mid m} k b_k\big) a_{n-m}$ (valid for real exponents $b_k$).
The value $b_0$ is unused.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public noncomputable def weightedPartitionCoeff (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (∑ m : Fin (n + 1), (∑ k ∈ (m.1 + 1).divisors, (k : ℝ) * b k) *
      weightedPartitionCoeff b (n - m.1)) / (n + 1)
decreasing_by omega

/-- **Zeroth weighted partition coefficient.** For every sequence of real weights $(b_k)$, the
weighted partition coefficient $a_0$ attached to $(b_k)$ equals $1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public theorem weightedPartitionCoeff_zero (b : ℕ → ℝ) : weightedPartitionCoeff b 0 = 1 := by
  simp [weightedPartitionCoeff]

/-- **First weighted partition coefficient.** For every sequence of real weights $(b_k)$, the
weighted partition coefficient $a_1$ attached to $(b_k)$ equals $b_1$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public theorem weightedPartitionCoeff_one (b : ℕ → ℝ) : weightedPartitionCoeff b 1 = b 1 := by
  simp [weightedPartitionCoeff]

/-- **Meinardus' hypotheses.** Let $b_1, b_2, \dots$ be real weights (the value $b_0$ is unused),
let $\alpha$ and $A$ be reals and let $G : \mathbb{C} \to \mathbb{C}$. The weights satisfy
Meinardus' hypotheses (M1)–(M3) with exponent $\alpha$, residue $A$ and continuation $G$ if there
is $C_0$ with $0 < C_0 < 1$ such that: (M1) for $\operatorname{Re} s > \alpha$ the Dirichlet series
$B(s) = \sum_{k \ge 1} b_k k^{-s}$ converges absolutely and equals $G(s)$, and there is a function
$R : \mathbb{C} \to \mathbb{C}$ that is complex differentiable at every point of the closed
half-plane $\{s : \operatorname{Re} s \ge -C_0\}$ relative to that half-plane, with
$G(s) = A/(s - \alpha) + R(s)$ for all $s \ne \alpha$ with $\operatorname{Re} s \ge -C_0$; (M2)
there are $c > 0$ and reals $K$, $T$ with $|G(s)| \le K (1 + |\operatorname{Im} s|)^c$ whenever
$\operatorname{Re} s \ge -C_0$ and $|\operatorname{Im} s| \ge T$; (M3) there are
$\varepsilon > 0$, $C_3 > 0$ and $y_0 > 0$ such that, with
$g(\tau) = \sum_{k \ge 1} b_k e^{-k\tau}$, the inequality
$\operatorname{Re} g(y + 2\pi i x) - g(y) \le -C_3 y^{-\varepsilon}$ holds for all reals
$x$, $y$ with $0 < y < y_0$ and $y^{1 + \varepsilon/2} \le |x| \le 1/2$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (hypotheses of Theorem 3). -/
public def MeinardusHypotheses (b : ℕ → ℝ) (α A : ℝ) (G : ℂ → ℂ) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ C₀ < 1 ∧
    (∀ s : ℂ, α < s.re →
      LSeriesSummable (fun k => (b k : ℂ)) s ∧ LSeries (fun k => (b k : ℂ)) s = G s) ∧
    (∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s | -C₀ ≤ s.re} ∧
      ∀ s : ℂ, -C₀ ≤ s.re → s ≠ α → G s = A / (s - α) + R s) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ K T : ℝ, ∀ s : ℂ, -C₀ ≤ s.re → T ≤ |s.im| →
      ‖G s‖ ≤ K * (1 + |s.im|) ^ c) ∧
    (∃ ε C₃ y₀ : ℝ, 0 < ε ∧ 0 < C₃ ∧ 0 < y₀ ∧ ∀ y x : ℝ, 0 < y → y < y₀ →
      y ^ (1 + ε / 2) ≤ |x| → |x| ≤ 1 / 2 →
      (∑' k : ℕ, (b (k + 1) : ℂ) *
          Complex.exp (-((k : ℂ) + 1) * ((y : ℂ) + 2 * Real.pi * Complex.I * x))).re -
        ∑' k : ℕ, b (k + 1) * Real.exp (-((k : ℝ) + 1) * y) ≤ -C₃ * y ^ (-ε))

/-- **Cumulative profile.** For a sequence $\pi : \mathbb{N} \to \mathbb{N}$ and a natural number
$k$, the cumulative profile is $\Pi_k = \sum_{j=1}^{k} \pi_j$. The value $\pi_0$ is not used, and
$\Pi_0 = 0$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public def profilePartialSum (π : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 k, π j

/-- **Recursion for the cumulative profile.** For every sequence $\pi : \mathbb{N} \to \mathbb{N}$
with cumulative profile $\Pi_k = \sum_{j=1}^{k} \pi_j$ and every natural number $k$,
$\Pi_{k+1} = \Pi_k + \pi_{k+1}$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public theorem profilePartialSum_succ (π : ℕ → ℕ) (k : ℕ) :
    profilePartialSum π (k + 1) = profilePartialSum π k + π (k + 1) := by
  simp [profilePartialSum, Finset.sum_Icc_succ_top]

/-- **Block index of a profile.** Let $\pi : \mathbb{N} \to \mathbb{N}$ be a sequence with
cumulative profile $\Pi_k = \sum_{j=1}^{k} \pi_j$. For a natural number $i$, the block index $k(i)$
is the least natural number $k$ with $i \le \Pi_k$, and $k(i) = 0$ if there is no such $k$. When
$i \ge 1$ and $\Pi$ is unbounded, $k(i)$ is the unique $k$ with $\Pi_{k-1} < i \le \Pi_k$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public noncomputable def seqHeightIndex (π : ℕ → ℕ) (i : ℕ) : ℕ :=
  sInf {k | i ≤ profilePartialSum π k}

/-- **Block index of the constant profile.** For the constant profile $\pi_k = 1$, whose cumulative
profile is $\Pi_k = \sum_{j=1}^{k} \pi_j = k$, the block index $k(i)$, the least $k$ with
$i \le \Pi_k$, equals $i$ for every natural number $i$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public theorem seqHeightIndex_const_one (i : ℕ) : seqHeightIndex (fun _ => 1) i = i := by
  have h : ∀ k, profilePartialSum (fun _ => 1) k = k := fun k => by simp [profilePartialSum]
  simp only [seqHeightIndex, h]
  exact le_antisymm (Nat.sInf_le (show i ≤ i from le_rfl))
    (le_csInf ⟨i, show i ≤ i from le_rfl⟩ fun k hk => hk)

/-- **Canonical sequential realization of a profile.** Let $(\pi_k)_{k \ge 1}$ be a sequence of
nonnegative integers with partial sums $\Pi_k = \sum_{1 \le j \le k} \pi_j$. For $i \ge 1$ let
$k(i)$ be the least $k \ge 0$ with $i \le \Pi_k$, or $0$ if there is none, and let
$p_1 = 2, p_2 = 3, \dots$ be the primes in increasing order. The canonical sequential realization
$H_{\mathrm{seq}}$ of $\pi$ is the function $\mathbb{N} \to \mathbb{N}$ that sends $m \ge 1$ to
$\sum_{i \ge 1} a_i\, k(i)$, where $a_i$ is the exponent of $p_i$ in $m$, and sends $0$ to $0$;
thus $H_{\mathrm{seq}}$ is completely additive with $H_{\mathrm{seq}}(p_i) = k(i)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Definition 2 (canonical sequential
realization, Section 7.2). -/
public noncomputable def canonicalSeqHeight (π : ℕ → ℕ) : ℕ → ℕ :=
  additiveOfPrimeValues fun p => seqHeightIndex π (Nat.count Nat.Prime p + 1)

namespace canonicalSeq_partitionProfile_growth

open Finset Real Asymptotics

private noncomputable abbrev height := canonicalSeqHeight (fun _ => 1)

private lemma height_prime {p : ℕ} (hp : p.Prime) : height p = p.primeCounting := by
  rw [height, canonicalSeqHeight, additiveOfPrimeValues_prime _ hp, seqHeightIndex_const_one]
  exact (Nat.count_succ_eq_succ_count hp).symm

private lemma primeCounting_le (n : ℕ) : n.primeCounting ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
  simpa using card_filter_le (s := Icc 1 n) Nat.Prime

-- The sum of the first m prime heights is the triangular number m(m+1)/2.
private lemma sum_prime_heights (n : ℕ) :
    2 * (∑ p ∈ n.primesLE, (height p : ℝ)) =
      (n.primeCounting : ℝ) * (n.primeCounting + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : (n + 1).Prime
    · have hc : (n + 1).primeCounting = n.primeCounting + 1 :=
        Nat.count_succ_eq_succ_count h
      rw [Nat.primesLE_succ, ite_eq_left h, sum_insert (Nat.notMem_primesLE n), height_prime h, hc]
      push_cast
      linarith
    · have hc : (n + 1).primeCounting = n.primeCounting := Nat.count_succ_eq_count h
      simpa [Nat.primesLE_succ, h, hc] using ih

private noncomputable abbrev harmonic (x : ℝ) :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, (height p : ℝ) / p

private noncomputable abbrev total (x : ℝ) :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (height n : ℝ)

-- Legendre's bound for the exponent of p in n! controls all multiples of p at once.
private lemma total_le {x : ℝ} (hx : 0 ≤ x) : total x ≤ 2 * x * harmonic x := by
  let n := ⌊x⌋₊
  have hsum := sum_height_eq_sum_prime_powers.sum_height_eq_factorization_sum
    (H := height) (isCompletelyAdditiveNat_additiveOfPrimeValues _) n
  change (∑ k ∈ Icc 1 n, (height k : ℝ)) ≤ 2 * x * ∑ p ∈ n.primesLE, (height p : ℝ) / p
  rw [← Nat.cast_sum, hsum, Nat.cast_sum, mul_sum]
  refine sum_le_sum fun p hp => ?_
  have hp₂ := Nat.two_le_of_mem_primesLE hp
  have he : (p - 1) * n.factorial.factorization p ≤ n :=
    (Nat.sub_one_mul_factorization_factorial (Nat.prime_of_mem_primesLE hp)).trans_le
      (Nat.sub_le _ _)
  have hpn : p * n.factorial.factorization p ≤ 2 * n := by
    calc
      _ ≤ (2 * (p - 1)) * n.factorial.factorization p := by gcongr; omega
      _ ≤ 2 * n := by simpa [mul_assoc] using Nat.mul_le_mul_left 2 he
  have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
  have he' : (p : ℝ) * n.factorial.factorization p ≤ 2 * x := by
    calc
      _ ≤ 2 * (n : ℝ) := by exact_mod_cast hpn
      _ ≤ 2 * x := by gcongr; exact Nat.floor_le hx
  push_cast
  rw [← mul_div_assoc, le_div_iff₀ hp']
  linarith only [mul_le_mul_of_nonneg_right he' (Nat.cast_nonneg (height p))]

private lemma primeCounting_upper :
    ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 3 * x / log x := by
  filter_upwards [Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x h hx
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (log_nonneg hx.le)
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num1
  linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]

private lemma primeCounting_lower :
    ∀ᶠ x : ℝ in atTop, x / log x ≤ 4 * (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp (isLittleO_log_id_atTop.bound (by norm_num : 0 < (1/8 : ℝ)))
  filter_upwards [eventually_ge_atTop a, eventually_ge_atTop (6 : ℝ)] with x hxa hx
  have h := ha (x + 2) (by linarith)
  rw [Real.norm_of_nonneg (log_nonneg (by linarith)), id_eq, Real.norm_of_nonneg (by linarith)] at h
  have hl := log_pos (show 1 < x by linarith)
  have hπ := (div_le_iff₀ hl).mp (Chebyshev.pi_ge' (show 1 < x by linarith))
  apply (div_le_iff₀ hl).mpr
  nlinarith [mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ log 2 - 1/2 by
    linarith [one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)])]

private lemma sqrt_le_main_term :
    ∀ᶠ x : ℝ in atTop, √x ≤ x / log x ^ 2 := by
  have h := (isLittleO_log_rpow_rpow_atTop 2 (show 0 < (1 / 2 : ℝ) by norm_num)).bound zero_lt_one
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  simp only [rpow_two, ← sqrt_eq_rpow, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (sqrt_nonneg _), one_mul] at hx
  apply (le_div_iff₀ (sq_pos_of_pos (log_pos hx₁))).mpr
  simpa [mul_self_sqrt (by linarith : 0 ≤ x)] using
    mul_le_mul_of_nonneg_left hx (sqrt_nonneg x)

-- Below √x each summand is at most one. Above √x each is at most 6/log x.
private lemma harmonic_upper :
    ∀ᶠ x : ℝ in atTop, harmonic x ≤ 19 * (x / log x ^ 2) := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp primeCounting_upper
  filter_upwards [sqrt_le_main_term, primeCounting_upper, eventually_gt_atTop (1 : ℝ),
    tendsto_sqrt_atTop.eventually (eventually_ge_atTop a)] with x hs hπ hx hsa
  have hl := log_pos hx
  let s := Nat.primesLE ⌊x⌋₊
  have hcut : (s.filter fun p : ℕ => (p : ℝ) ≤ √x) ⊆ Icc 1 ⌊√x⌋₊ := by
    intro p hp
    obtain ⟨hm, hle⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hm).one_le, Nat.le_floor hle⟩
  have hcard : ((s.filter fun p : ℕ => (p : ℝ) ≤ √x).card : ℝ) ≤ √x := by
    refine le_trans ?_ (Nat.floor_le (sqrt_nonneg x))
    have h := card_le_card hcut
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast h
  have hterm (p : ℕ) (hp : p ∈ s) :
      (height p : ℝ) / p ≤ (if (p : ℝ) ≤ √x then 1 else 0) + 6 / log x := by
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    rw [height_prime hprime]
    split_ifs with h
    · have h₁ : (p.primeCounting : ℝ) / p ≤ 1 := by
        rw [div_le_one hp₀]
        exact_mod_cast primeCounting_le p
      linarith [show 0 ≤ 6 / log x by positivity]
    · have hbound := ha p (hsa.trans (le_of_not_ge h))
      rw [Nat.floor_natCast] at hbound
      have hlog : log x / 2 ≤ log p := by
        rw [← log_sqrt (by linarith : 0 ≤ x)]
        exact log_le_log (sqrt_pos.2 (by linarith)) (le_of_not_ge h)
      have hlp : 0 < log p := by linarith
      rw [zero_add, div_le_div_iff₀ hp₀ hl]
      calc
        (p.primeCounting : ℝ) * log x ≤ p.primeCounting * (2 * log p) := by
          gcongr; linarith
        _ ≤ 6 * p := by linarith [(le_div_iff₀ hlp).mp hbound]
  calc
    harmonic x ≤ ∑ p ∈ s, ((if (p : ℝ) ≤ √x then (1 : ℝ) else 0) + 6 / log x) :=
      sum_le_sum hterm
    _ = ((s.filter fun p : ℕ => (p : ℝ) ≤ √x).card : ℝ) + ⌊x⌋₊.primeCounting * (6 / log x) := by
      simp [sum_add_distrib, s]
    _ ≤ √x + (3 * x / log x) * (6 / log x) := by gcongr
    _ ≤ x / log x ^ 2 + (3 * x / log x) * (6 / log x) := by gcongr
    _ = 19 * (x / log x ^ 2) := by ring

-- The prime contributions alone suffice for both lower bounds.
private lemma lower_bounds :
    ∀ᶠ x : ℝ in atTop, x / log x ^ 2 ≤ 32 * harmonic x ∧ x ^ 2 / log x ^ 2 ≤ 32 * total x := by
  filter_upwards [primeCounting_lower, eventually_gt_atTop (1 : ℝ)] with x hπ hx
  let n := ⌊x⌋₊
  let P := ∑ p ∈ n.primesLE, (height p : ℝ)
  have hx₀ : 0 < x := by linarith
  have hl := log_pos hx
  have hP : x ^ 2 / log x ^ 2 ≤ 32 * P := by
    rw [← div_pow]
    calc
      _ ≤ (4 * (n.primeCounting : ℝ)) ^ 2 := by gcongr
      _ ≤ 32 * P := by
        nlinarith [sum_prime_heights n, Nat.cast_nonneg (α := ℝ) n.primeCounting]
  have hH : P ≤ x * harmonic x := by
    rw [harmonic, mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    have hpx : (p : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hp)).trans (Nat.floor_le hx₀.le)
    rw [← mul_div_assoc, le_div_iff₀ hp₀, mul_comm x]
    gcongr
  have hT : P ≤ total x := by
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => mem_Icc.mpr ?_) (by intros; positivity)
    exact ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
  refine ⟨?_, hP.trans (by gcongr)⟩
  apply le_of_mul_le_mul_left (a := x) _ hx₀
  calc
    x * (x / log x ^ 2) = x ^ 2 / log x ^ 2 := by ring
    _ ≤ 32 * P := hP
    _ ≤ 32 * (x * harmonic x) := by gcongr
    _ = x * (32 * harmonic x) := by ring

end canonicalSeq_partitionProfile_growth

open canonicalSeq_partitionProfile_growth in
/-- **Growth for the ordinary partition profile.** Let $H_{\mathrm{seq}}$ be the canonical
sequential realization of the constant profile $\pi_k = 1$ for all $k \ge 1$ (so
$H_{\mathrm{seq}}(p_i) = i$ for the $i$-th prime $p_i$). Then, as $x \to \infty$ over the reals,
$\sum_{p \le x} H_{\mathrm{seq}}(p)/p = \Theta\bigl(x / (\log x)^2\bigr)$, the sum running over
primes $p \le x$, and
$\sum_{1 \le n \le x} H_{\mathrm{seq}}(n) = \Theta\bigl(x^2 / (\log x)^2\bigr)$, where
$f = \Theta(g)$ means $f = O(g)$ and $g = O(f)$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 3 (`integers-2026-A116-cor-3`). -/
public theorem canonicalSeq_partitionProfile_growth :
    (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight (fun _ => 1) p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x / Real.log x ^ 2) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun _ => 1) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ 2 / Real.log x ^ 2) := by
  have hset (n : ℕ) : (Finset.Iic n).filter Nat.Prime = n.primesLE := by
    ext p
    simp [Nat.mem_primesLE]
  simp only [hset]
  change (harmonic =Θ[atTop] _) ∧ (total =Θ[atTop] _)
  refine ⟨⟨.of_bound 19 ?_, .of_bound 32 ?_⟩, ⟨.of_bound 38 ?_, .of_bound 32 ?_⟩⟩
  · filter_upwards [harmonic_upper, eventually_gt_atTop (1 : ℝ)] with x h hx
    simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ harmonic x),
      Real.norm_of_nonneg (by positivity : 0 ≤ x / Real.log x ^ 2)] using h
  · filter_upwards [lower_bounds, eventually_gt_atTop (1 : ℝ)] with x h hx
    simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ harmonic x),
      Real.norm_of_nonneg (by positivity : 0 ≤ x / Real.log x ^ 2)] using h.1
  · filter_upwards [harmonic_upper, eventually_gt_atTop (1 : ℝ)] with x h hx
    have hx₀ : 0 ≤ x := by linarith
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ total x),
      Real.norm_of_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ 2)]
    calc
      total x ≤ 2 * x * harmonic x := total_le hx₀
      _ ≤ 2 * x * (19 * (x / Real.log x ^ 2)) := by gcongr
      _ = 38 * (x ^ 2 / Real.log x ^ 2) := by ring
  · filter_upwards [lower_bounds] with x h
    simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ total x),
      Real.norm_of_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ 2)] using h.2

end

end MetaMathlibExt
