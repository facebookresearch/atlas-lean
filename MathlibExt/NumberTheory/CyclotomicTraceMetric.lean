/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A trace metric on cyclotomic fields

The squared trace norm sums the squares of the traces of an element times the nonconstant
powers of a chosen primitive root of unity. For prime conductor, each shift singles out
the coefficient with complementary exponent. Summing these squared traces gives the
coordinate formula of Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*.
The trace coordinates define a norm on the cyclotomic field over the rationals.
-/

namespace MetaMathlibExt

@[expose] public section

open IsCyclotomicExtension

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

/-- **Squared trace norm on a cyclotomic field.** Let $p$ be a positive integer, let $K$ be a
$p$-th cyclotomic extension of $\mathbb{Q}$, and let $\omega$ be the chosen primitive $p$-th root
of unity in $K$. The squared trace norm of $\alpha \in K$ is the rational number
$$\lVert \alpha \rVert^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}(\alpha \omega^j)^2.$$

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1 (Definition 2.1 of arXiv:2410.22687). -/
noncomputable def cyclotomicTraceNormSq (p : ℕ) [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    (α : K) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (p - 1),
    Algebra.trace ℚ K (α * zeta p ℚ K ^ j) ^ 2

/-- **Trace norm on a cyclotomic field.** Let $p$ be a positive integer, let $K$ be a $p$-th
cyclotomic extension of $\mathbb{Q}$, and let $\omega$ be the chosen primitive $p$-th root of
unity in $K$. The trace norm of $\alpha \in K$ is the real number
$$\|\alpha\| = \sqrt{\sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}(\alpha \omega^j)^2},$$
the Euclidean length of the vector
$(\mathrm{Tr}_{K/\mathbb{Q}}(\alpha \omega^j))_{1 \le j \le p-1}$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1 (Definition 2.1 of arXiv:2410.22687). -/
noncomputable def cyclotomicTraceNorm (p : ℕ) [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    (α : K) : ℝ :=
  √(cyclotomicTraceNormSq p α : ℝ)

/-- **Trace metric on a cyclotomic field.** Let $p$ be a positive integer and let $K$ be a $p$-th
cyclotomic extension of $\mathbb{Q}$. The trace distance between $\alpha, \beta \in K$ is the real
number $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$, where $\lVert \cdot \rVert$ is the trace
norm on $K$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 2 (Definition 2.2 of arXiv:2410.22687). -/
noncomputable def cyclotomicTraceDist (p : ℕ) [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    (α β : K) : ℝ :=
  cyclotomicTraceNorm p (α - β)

/-- **Lattice points of a cyclotomic field.** Let $p$ be a positive integer, let $K$ be a $p$-th
cyclotomic extension of $\mathbb{Q}$, and let $\omega$ be the chosen primitive $p$-th root of
unity in $K$. For integers $a_1, \dots, a_{p-1}$, the lattice point with coefficients
$a_1, \dots, a_{p-1}$ is the element $a_1 \omega + a_2 \omega^2 + \cdots + a_{p-1} \omega^{p-1}$
of $K$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
noncomputable def cyclotomicLatticePoint (K : Type*) [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K]
    (a : Fin (p - 1) → ℤ) : K :=
  ∑ i, (a i : K) * zeta p ℚ K ^ (i.val + 1)

/-- **The cyclotomic box.** For natural numbers $p$ and $N$, the box $B(p, N)$ is the finite set
of integer vectors $a = (a_1, \dots, a_{p-1}) \in \mathbb{Z}^{p-1}$ with $-N \le a_i \le N$ for
every $i$.

The vector $a$ stands for the point $a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ of the $p$-th
cyclotomic field $\mathbb{Q}(\omega)$, where $\omega$ is a primitive $p$-th root of unity.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
def cyclotomicBox (p N : ℕ) : Finset (Fin (p - 1) → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- **Moments of the trace distance on the cyclotomic box.** Let $p \ge 1$, $N$ and $k$ be natural
numbers, and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity,
with fixed primitive $p$-th root of unity $\omega \in K$. Let $d$ be the trace metric on $K$, given
by $d(\alpha, \beta) \ge 0$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, and write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. The $k$-th moment
of $d$ over $B(p, N)$ is the real number
$$
M_k(p, N) = \frac{1}{\lvert B(p, N) \rvert^2} \sum_{a \in B(p, N)} \sum_{b \in B(p, N)}
d(\alpha_a, \alpha_b)^k.
$$

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 6 (Definition 6.1 of arXiv:2410.22687). -/
noncomputable def cyclotomicDistMoment (p : ℕ) [NeZero p] (K : Type*) [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (N k : ℕ) : ℝ :=
  (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ^ k) /
    ((cyclotomicBox p N).card : ℝ) ^ 2

/-- **Squared trace norm of zero.** Let $p$ be a positive integer and let $K$ be a $p$-th
cyclotomic extension of $\mathbb{Q}$. The squared trace norm of $0 \in K$ is $0$, that is,
$\lVert 0 \rVert^2 = 0$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1. -/
@[simp] theorem cyclotomicTraceNormSq_zero : cyclotomicTraceNormSq p (0 : K) = 0 := by
  simp [cyclotomicTraceNormSq]

/-- **The squared trace norm is invariant under negation.** Let $p$ be a positive integer and
let $K$ be a $p$-th cyclotomic extension of $\mathbb{Q}$. For every $\alpha \in K$, the squared
trace norm satisfies $\lVert -\alpha \rVert^2 = \lVert \alpha \rVert^2$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1. -/
@[simp] theorem cyclotomicTraceNormSq_neg (α : K) :
    cyclotomicTraceNormSq p (-α) = cyclotomicTraceNormSq p α := by
  simp [cyclotomicTraceNormSq, neg_mul, map_neg]

/-- **Trace distance from a point to itself.** Let $p$ be a positive integer and let $K$ be a
$p$-th cyclotomic extension of $\mathbb{Q}$. For every $\alpha \in K$, the trace distance satisfies
$d(\alpha, \alpha) = 0$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 2. -/
@[simp] theorem cyclotomicTraceDist_self (α : K) :
    cyclotomicTraceDist p α α = 0 := by
  simp [cyclotomicTraceDist, cyclotomicTraceNorm]

/-- **Symmetry of the trace metric.** Let $p$ be a positive integer and let $K$ be a $p$-th
cyclotomic extension of $\mathbb{Q}$. For all $\alpha, \beta \in K$, the trace distance satisfies
$d(\alpha, \beta) = d(\beta, \alpha)$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 2. -/
theorem cyclotomicTraceDist_comm (α β : K) :
    cyclotomicTraceDist p α β = cyclotomicTraceDist p β α := by
  rw [cyclotomicTraceDist, cyclotomicTraceDist, ← neg_sub, cyclotomicTraceNorm,
    cyclotomicTraceNorm, cyclotomicTraceNormSq_neg]

/-- **Galois invariance of the trace metric.** Let $p$ be a prime and let $K$ be a $p$-th
cyclotomic extension of $\mathbb{Q}$. For every $\mathbb{Q}$-algebra automorphism $\sigma$ of $K$
and all $\alpha, \beta \in K$, the trace distance satisfies
$d(\sigma \alpha, \sigma \beta) = d(\alpha, \beta)$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Proposition 1 (`integers-2025-A10-prop-1`). -/
theorem cyclotomicTraceDist_algEquiv (hp : p.Prime)
    (σ : K ≃ₐ[ℚ] K) (α β : K) :
    cyclotomicTraceDist p (σ α) (σ β) = cyclotomicTraceDist p α β := by
  let f (u : K) := Algebra.trace ℚ K ((σ α - σ β) * u) ^ 2
  -- The powers with exponents from 1 to p - 1 enumerate all primitive p-th roots.
  have sum_powers {ω : K} (hω : IsPrimitiveRoot ω p) :
      (∑ j ∈ Finset.Icc 1 (p - 1), f (ω ^ j)) = ∑ u ∈ primitiveRoots p K, f u := by
    apply Finset.sum_bij (fun j _ => ω ^ j)
    · intro j hj
      obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
      exact (mem_primitiveRoots hp.pos).mpr
        (hω.pow_of_coprime j (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm)
    · intro i hi j hj hij
      simp only [Finset.mem_Icc] at hi hj
      exact hω.pow_inj (by omega) (by omega) hij
    · intro u hu
      obtain ⟨j, hj, hc, rfl⟩ :=
        hω.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hu)
      have hj₀ : j ≠ 0 := by
        rintro rfl
        exact hp.ne_one (by simpa using hc)
      exact ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · intro j _
      rfl
  apply congrArg (fun q : ℚ => √(q : ℝ))
  have hζ := zeta_spec p ℚ K
  calc
    _ = ∑ j ∈ Finset.Icc 1 (p - 1), f (σ (zeta p ℚ K) ^ j) :=
      (sum_powers hζ).trans (sum_powers (hζ.map_of_injective σ.injective)).symm
    _ = _ := by
      simp only [f, ← map_sub, ← map_pow, ← map_mul, Algebra.trace_eq_of_algEquiv,
        cyclotomicTraceNormSq]

/-- **The zero coefficient vector gives the zero lattice point.** Let $p \ge 1$ be a natural
number and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with
fixed primitive $p$-th root of unity $\omega \in K$. For an integer vector
$a = (a_1, \dots, a_{p-1})$ write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. Then
$\alpha_0 = 0$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
@[simp] theorem cyclotomicLatticePoint_zero :
    cyclotomicLatticePoint K (0 : Fin (p - 1) → ℤ) = 0 := by
  simp [cyclotomicLatticePoint]

/-- **The cyclotomic box of radius zero.** Let $p$ be a natural number and, for a natural number
$N$, let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with
$-N \le a_i \le N$ for all $i$. Then $B(p, 0) = \{0\}$: the zero vector is the only element of the
box of radius $0$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
theorem cyclotomicBox_zero (p : ℕ) : cyclotomicBox p 0 = {0} := by
  ext a
  simp [cyclotomicBox, funext_iff]

/-- **The zero vector lies in every box.** For all natural numbers $p$ and $N$, the zero vector
lies in the box $B(p, N)$, the set of integer vectors $(a_1, \dots, a_{p-1})$ with
$|a_i| \le N$ for all $i$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
theorem zero_mem_cyclotomicBox (p N : ℕ) : (0 : Fin (p - 1) → ℤ) ∈ cyclotomicBox p N := by
  simp [cyclotomicBox]

/-- **The zeroth moment of the trace distance is one.** Let $p \ge 1$ and $N$ be natural numbers,
and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed
primitive $p$-th root of unity $\omega \in K$. Let $d$ be the trace metric on $K$, given by
$d(\alpha, \beta) \ge 0$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$, and let
$M_k(p, N) = \lvert B(p, N) \rvert^{-2} \sum_{a, b \in B(p, N)} d(\alpha_a, \alpha_b)^k$ be the
$k$-th moment of $d$ over $B(p, N)$. Then $M_0(p, N) = 1$, with the convention $0^0 = 1$ for
coinciding points.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 6 (Definition 6.1 of arXiv:2410.22687). -/
theorem cyclotomicDistMoment_zero (N : ℕ) : cyclotomicDistMoment p K N 0 = 1 := by
  have h : ((cyclotomicBox p N).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨0, zero_mem_cyclotomicBox p N⟩).ne'
  simp [cyclotomicDistMoment, sq, h]

namespace cyclotomicTraceNormSq_eq_and_ge

open Polynomial in
private theorem trace_zeta_pow (hp : p.Prime) (n : ℕ) :
    Algebra.trace ℚ K (zeta p ℚ K ^ n) = (if p ∣ n then (p : ℚ) else 0) - 1 := by
  have hζ := zeta_spec p ℚ K
  have hirr := cyclotomic.irreducible_rat hp.pos
  by_cases hn : p ∣ n
  · rw [ite_eq_left hn, (hζ.pow_eq_one_iff_dvd n).2 hn, ← map_one (algebraMap ℚ K),
      Algebra.trace_algebraMap, IsCyclotomicExtension.finrank K hirr, Nat.totient_prime hp]
    simp [nsmul_eq_mul, Nat.cast_sub hp.one_le]
  · have hprim := hζ.pow_of_coprime n (hp.coprime_iff_not_dvd.mpr hn).symm
    have hdeg : (cyclotomic p ℚ).natDegree = p - 1 := by
      rw [natDegree_cyclotomic, Nat.totient_prime hp]
    have htwo := hp.two_le
    let : Fact p.Prime := ⟨hp⟩
    rw [ite_eq_right hn, zero_sub, ← hprim.powerBasis_gen ℚ,
      PowerBasis.trace_gen_eq_nextCoeff_minpoly, hprim.powerBasis_gen ℚ,
      ← hprim.minpoly_eq_cyclotomic_of_irreducible hirr,
      nextCoeff_of_natDegree_pos (by omega), hdeg, cyclotomic_prime, finsetSum_coeff]
    simp [coeff_X_pow, show p - 1 - 1 < p by omega]

end cyclotomicTraceNormSq_eq_and_ge

/-- **Squared trace norm in coordinates.** Let $p$ be a prime, let $K$ be a $p$-th cyclotomic
extension of $\mathbb{Q}$, let $\omega$ be the chosen primitive $p$-th root of unity in $K$, and
let $\mathrm{Tr}$ be the trace from $K$ to $\mathbb{Q}$. For rational numbers
$a_1, \dots, a_{p-1}$, put $\alpha = a_1 \omega + a_2 \omega^2 + \cdots + a_{p-1} \omega^{p-1}$
and $\lVert \alpha \rVert_E^2 = a_1^2 + a_2^2 + \cdots + a_{p-1}^2$. Then the squared trace
norm of $\alpha$ satisfies
$$\lVert \alpha \rVert^2 = p^2 \lVert \alpha \rVert_E^2 - (p + 1) \mathrm{Tr}(\alpha)^2,$$
and $\lVert \alpha \rVert_E^2 \le \lVert \alpha \rVert^2$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 1 (`integers-2025-A10-lem-1`). -/
theorem cyclotomicTraceNormSq_eq_and_ge (hp : p.Prime) (a : Fin (p - 1) → ℚ) :
    let α : K :=
      ∑ i, (a i : K) * zeta p ℚ K ^ (i.val + 1)
    cyclotomicTraceNormSq p α =
        (p : ℚ) ^ 2 * ∑ i, a i ^ 2 - (p + 1) * Algebra.trace ℚ K α ^ 2 ∧
      ∑ i, a i ^ 2 ≤ cyclotomicTraceNormSq p α := by
  intro α
  let S := ∑ i, a i
  have trace_term (q : ℚ) (n : ℕ) :
      Algebra.trace ℚ K ((q : K) * zeta p ℚ K ^ n) =
        q * ((if p ∣ n then (p : ℚ) else 0) - 1) := by
    rw [← cyclotomicTraceNormSq_eq_and_ge.trace_zeta_pow (K := K) hp]
    simpa only [Rat.smul_def, Rat.cast_id] using
      (Algebra.trace ℚ K).map_smul q (zeta p ℚ K ^ n)
  have trace_shift (j : ℕ) : Algebra.trace ℚ K (α * zeta p ℚ K ^ j) =
      (∑ i, if p ∣ i.val + 1 + j then (p : ℚ) * a i else 0) - S := by
    dsimp only [α, S]
    rw [Finset.sum_mul, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, ← pow_add, trace_term]
    split <;> ring
  have hsmall (i : Fin (p - 1)) : ¬p ∣ i.val + 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have htrace : Algebra.trace ℚ K α = -S := by
    simpa [hsmall] using trace_shift 0
  -- Index the shifts by the unique coordinate whose exponent becomes a multiple of p.
  have hnorm : cyclotomicTraceNormSq p α = ∑ i, ((p : ℚ) * a i - S) ^ 2 := by
    symm
    apply Finset.sum_bij (fun (i : Fin (p - 1)) _ => p - (i.val + 1))
    · intro i _
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ k _ hik
      exact Fin.ext (by omega)
    · intro j hj
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
      exact ⟨⟨p - j - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
    · intro i _
      have hdiv (k : Fin (p - 1)) : p ∣ k.val + 1 + (p - (i.val + 1)) ↔ k = i := by
        constructor
        · intro hd
          have := Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by omega)
          exact Fin.ext (by omega)
        · intro hki
          subst k
          rw [show i.val + 1 + (p - (i.val + 1)) = p by omega]
      simp [trace_shift, hdiv]
  have heq : cyclotomicTraceNormSq p α =
      (p : ℚ) ^ 2 * ∑ i, a i ^ 2 - (p + 1) * Algebra.trace ℚ K α ^ 2 := by
    rw [hnorm, htrace]
    calc
      _ = ∑ i, ((p : ℚ) ^ 2 * a i ^ 2 - (2 * p * S) * a i + S ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_sub hp.one_le, Nat.cast_one]
        dsimp only [S]
        ring
  refine ⟨heq, ?_⟩
  rw [heq, htrace]
  have hCS : S ^ 2 ≤ ((p : ℚ) - 1) * ∑ i, a i ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_sub hp.one_le, Nat.cast_one, S]
      using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a))
  nlinarith only [mul_le_mul_of_nonneg_left hCS (show 0 ≤ (p : ℚ) + 1 by positivity)]

namespace cyclotomicTraceNorm_isNorm

private theorem eq_zero_of_trace_powers_eq_zero (hp : p.Prime) (α : K)
    (h : ∀ j ∈ Finset.Icc 1 (p - 1), Algebra.trace ℚ K (α * zeta p ℚ K ^ j) = 0) :
    α = 0 := by
  have hζ := zeta_spec p ℚ K
  let b := hζ.powerBasis ℚ
  have hdim : b.dim = p - 1 := by
    rw [← b.finrank, IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.pos),
      Nat.totient_prime hp]
  -- Shifting the usual power basis by one power gives exactly the tested exponents.
  have hform : Algebra.traceForm ℚ K (α * zeta p ℚ K) = 0 := by
    apply b.basis.ext
    intro i
    have hi : i.val + 1 ∈ Finset.Icc 1 (p - 1) := by
      have := i.isLt
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [LinearMap.zero_apply, Algebra.traceForm_apply, b.basis_eq_pow,
      IsPrimitiveRoot.powerBasis_gen, mul_assoc, ← pow_succ']
    exact h _ hi
  have := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  have hz := (traceForm_nondegenerate ℚ K).1 _ (LinearMap.congr_fun hform)
  exact (mul_eq_zero.mp hz).resolve_right (hζ.ne_zero hp.ne_zero)

end cyclotomicTraceNorm_isNorm

/-- **The trace norm is a norm.** Let $p$ be a prime and let $K$ be a $p$-th cyclotomic extension
of $\mathbb{Q}$, viewed as a $\mathbb{Q}$-vector space. The trace norm $\lVert \cdot \rVert$ on $K$
is a norm: for all $\alpha, \beta \in K$ and $q \in \mathbb{Q}$, we have
$\lVert \alpha \rVert = 0$ if and only if $\alpha = 0$,
$\lVert \alpha + \beta \rVert \le \lVert \alpha \rVert + \lVert \beta \rVert$, and
$\lVert q \alpha \rVert = |q| \, \lVert \alpha \rVert$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 2 (`integers-2025-A10-thm-2`). -/
theorem cyclotomicTraceNorm_isNorm (hp : p.Prime) :
    (∀ α : K, cyclotomicTraceNorm p α = 0 ↔ α = 0) ∧
    (∀ α β : K,
      cyclotomicTraceNorm p (α + β) ≤ cyclotomicTraceNorm p α + cyclotomicTraceNorm p β) ∧
    ∀ (q : ℚ) (α : K), cyclotomicTraceNorm p (q • α) = |(q : ℝ)| * cyclotomicTraceNorm p α := by
  let J := ↥(Finset.Icc 1 (p - 1))
  let T : K →ₗ[ℚ] PiLp 2 (fun _ : J => ℚ) :=
    (WithLp.linearEquiv 2 ℚ _).symm.toLinearMap.comp
      (LinearMap.pi fun j : J => (Algebra.traceForm ℚ K).flip (zeta p ℚ K ^ (j : ℕ)))
  have hnorm (α : K) : cyclotomicTraceNorm p α = ‖T α‖ := by
    rw [PiLp.norm_eq_of_L2]
    change √(cyclotomicTraceNormSq p α : ℝ) =
      √(∑ j : J, |(Algebra.trace ℚ K (α * zeta p ℚ K ^ (j : ℕ)) : ℝ)| ^ 2)
    simp only [sq_abs, cyclotomicTraceNormSq, Rat.cast_sum, Rat.cast_pow]
    rw [← Finset.sum_coe_sort]
  refine ⟨fun α => ⟨fun hα => ?_, ?_⟩, fun α β => ?_, fun q α => ?_⟩
  · have hz : T α = 0 := norm_eq_zero.mp ((hnorm α).symm.trans hα)
    apply cyclotomicTraceNorm_isNorm.eq_zero_of_trace_powers_eq_zero hp α
    intro j hj
    exact congrArg (fun v : PiLp 2 (fun _ : J => ℚ) => v.ofLp ⟨j, hj⟩) hz
  · rintro rfl
    simp [cyclotomicTraceNorm]
  · simpa only [hnorm, map_add] using norm_add_le (T α) (T β)
  · rw [hnorm, hnorm, map_smul, norm_smul]
    rfl

end

end MetaMathlibExt
