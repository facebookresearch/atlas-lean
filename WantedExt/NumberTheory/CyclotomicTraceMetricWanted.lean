/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.Analysis.Real.Sqrt

/-!
# A trace metric on the `p`-th cyclotomic field

Statements from Katerina Saettone, Alexandru Zaharescu and Zhuo Zhang, *On a Special
Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10 (arXiv:2410.22687).

For `K = ℚ(ω)` with `ω` a primitive `p`-th root of unity, `α ∈ K` is sent to the vector
`(Tr_{K/ℚ}(α ω^j))_{1 ≤ j ≤ p-1} ∈ ℚ^{p-1}`; `‖α‖` is its Euclidean length and
`d(α, β) = ‖α - β‖`. The field is any `K` with `IsCyclotomicExtension {p} ℚ K` (for
example `CyclotomicField p ℚ`), and `ω = IsCyclotomicExtension.zeta p ℚ K`.
The box `B(p, N)` consists of the points `a₁ ω + ⋯ + a_{p-1} ω^{p-1}` with integer
`aᵢ ∈ [-N, N]`; it is indexed by its coefficient vectors, which is faithful since
`ω, …, ω^{p-1}` is a `ℚ`-basis of `K`.

The paper fixes `p` an odd prime throughout; statements that also hold for `p = 2`
assume only that `p` is prime.
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

/-- **Galois invariance of the trace metric.** Let $p$ be a prime and let $K$ be a $p$-th
cyclotomic extension of $\mathbb{Q}$. For every $\mathbb{Q}$-algebra automorphism $\sigma$ of $K$
and all $\alpha, \beta \in K$, the trace distance satisfies
$d(\sigma \alpha, \sigma \beta) = d(\alpha, \beta)$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Proposition 1 (`integers-2025-A10-prop-1`). -/
public theorem_wanted cyclotomicTraceDist_algEquiv (hp : p.Prime)
    (σ : K ≃ₐ[ℚ] K) (α β : K) :
    cyclotomicTraceDist p (σ α) (σ β) = cyclotomicTraceDist p α β

/-- **The trace norm is a norm.** Let $p$ be a prime and let $K$ be a $p$-th cyclotomic extension
of $\mathbb{Q}$, viewed as a $\mathbb{Q}$-vector space. The trace norm $\lVert \cdot \rVert$ on $K$
is a norm: for all $\alpha, \beta \in K$ and $q \in \mathbb{Q}$, we have
$\lVert \alpha \rVert = 0$ if and only if $\alpha = 0$,
$\lVert \alpha + \beta \rVert \le \lVert \alpha \rVert + \lVert \beta \rVert$, and
$\lVert q \alpha \rVert = |q| \, \lVert \alpha \rVert$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 2 (`integers-2025-A10-thm-2`). -/
public theorem_wanted cyclotomicTraceNorm_isNorm (hp : p.Prime) :
    (∀ α : K, cyclotomicTraceNorm p α = 0 ↔ α = 0) ∧
    (∀ α β : K,
      cyclotomicTraceNorm p (α + β) ≤ cyclotomicTraceNorm p α + cyclotomicTraceNorm p β) ∧
    ∀ (q : ℚ) (α : K), cyclotomicTraceNorm p (q • α) = |(q : ℝ)| * cyclotomicTraceNorm p α

/-- **Krasner-type lemma for the cyclotomic trace metric.** Let $p$ be a prime and let $K$ be a
field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed primitive $p$-th
root of unity $\omega \in K$. Write $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$ for the trace
metric on $K$, where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $\alpha, \beta \in K$ and suppose that $d(\alpha, \beta) < d(\alpha, \sigma(\alpha)) / 2$ for
every automorphism $\sigma$ of $K$ over $\mathbb{Q}$ with $\sigma(\alpha) \ne \alpha$. Then
$\mathbb{Q}(\alpha) \subseteq \mathbb{Q}(\beta)$ as subfields of $K$.

Since $K / \mathbb{Q}$ is Galois, the elements $\sigma(\alpha) \ne \alpha$ are exactly the
conjugates of $\alpha$ over $\mathbb{Q}$ other than $\alpha$ itself.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 4 (`integers-2025-A10-thm-4`). -/
public theorem_wanted adjoin_le_adjoin_of_cyclotomicTraceDist_lt (hp : p.Prime)
    {α β : K}
    (h : ∀ σ : K ≃ₐ[ℚ] K, σ α ≠ α →
      cyclotomicTraceDist p α β < cyclotomicTraceDist p α (σ α) / 2) :
    IntermediateField.adjoin ℚ {α} ≤ IntermediateField.adjoin ℚ {β}

/-- **Primitive elements α + nβ in a prime cyclotomic field.** Let $p$ be a prime and let $K$
be a $p$-th cyclotomic extension of $\mathbb{Q}$. For all $\alpha, \beta \in K$ there is a
natural number $n_0$ such that, for every natural number $n \ge n_0$, the subfields
$\mathbb{Q}(\alpha + n\beta)$ and $\mathbb{Q}(\alpha, \beta)$ of $K$ are equal.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Corollary 1 (`integers-2025-A10-cor-1`). -/
public theorem_wanted eventually_adjoin_add_nsmul_eq (hp : p.Prime) (α β : K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IntermediateField.adjoin ℚ {α + (n : K) * β} =
        IntermediateField.adjoin ℚ {α, β}

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
public theorem_wanted cyclotomicTraceNormSq_eq_and_ge (hp : p.Prime) (a : Fin (p - 1) → ℚ) :
    let α : K :=
      ∑ i, (a i : K) * zeta p ℚ K ^ (i.val + 1)
    cyclotomicTraceNormSq p α =
        (p : ℚ) ^ 2 * ∑ i, a i ^ 2 - (p + 1) * Algebra.trace ℚ K α ^ 2 ∧
      ∑ i, a i ^ 2 ≤ cyclotomicTraceNormSq p α

/-- **Diameter of the cyclotomic box.** Let $p$ be an odd prime, let $N$ be a natural number, and
let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed
primitive $p$-th root of unity $\omega \in K$. Let $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$
be the trace metric on $K$, where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, and write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. Then
$d(\alpha_a, \alpha_b) \le 2 N p \sqrt{p - 1}$ for all $a, b \in B(p, N)$, and this bound is
attained: $d(\alpha, -\alpha) = 2 N p \sqrt{p - 1}$ for
$\alpha = N \omega - N \omega^2 + \dots + N \omega^{p-2} - N \omega^{p-1}$, the point whose
coefficient of $\omega^i$ is $(-1)^{i-1} N$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 2 (`integers-2025-A10-lem-2`). -/
public theorem_wanted cyclotomicBox_diam (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    (∀ a ∈ cyclotomicBox p N, ∀ b ∈ cyclotomicBox p N,
      cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ≤
        2 * N * p * √(p - 1 : ℝ)) ∧
    cyclotomicTraceDist p (cyclotomicLatticePoint K fun i : Fin (p - 1) => (N : ℤ) * (-1) ^ i.val)
        (cyclotomicLatticePoint K fun i : Fin (p - 1) => -((N : ℤ) * (-1) ^ i.val)) =
      2 * N * p * √(p - 1 : ℝ)

/-- **Power sums over a symmetric interval.** For natural numbers $N$ and $r$, let
$S_r(N) = \sum_{a=-N}^{N} a^r$, the sum over the integers $a$ with $-N \le a \le N$. Then
$S_r(N) = 0$ for every odd $r$, and
$$S_2(N) = \frac{N(N+1)(2N+1)}{3}, \qquad S_4(N) = \frac{N(N+1)(2N+1)(3N^2+3N-1)}{15}.$$

The paper takes $N \ge 1$; here $N = 0$ is allowed.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 3 (`integers-2025-A10-lem-3`). -/
public theorem_wanted symmetric_power_sums (N : ℕ) :
    (∀ r : ℕ, Odd r → ∑ a ∈ Finset.Icc (-(N : ℤ)) N, a ^ r = 0) ∧
    ∑ a ∈ Finset.Icc (-(N : ℤ)) N, (a : ℚ) ^ 2 = N * (N + 1) * (2 * N + 1) / 3 ∧
    ∑ a ∈ Finset.Icc (-(N : ℤ)) N, (a : ℚ) ^ 4 =
      N * (N + 1) * (2 * N + 1) * (3 * N ^ 2 + 3 * N - 1) / 15

/-- **Second moment of the trace distance on the cyclotomic box.** Let $p$ be a prime, let $N$ be
a natural number, and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of
unity, with fixed primitive $p$-th root of unity $\omega \in K$. Let $M_2(p, N)$ be the second
moment of the trace metric $d$ of $K$ over the box $B(p, N)$: the average of
$d(\alpha_a, \alpha_b)^2$ over all pairs $(a, b)$ of integer vectors in $\mathbb{Z}^{p-1}$ whose
coordinates lie in $[-N, N]$, where $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Then $M_2(p, N) = \frac{2}{3} (p^3 - 2 p^2 + 1) N (N + 1)$.

The asymptotic form $M_2(p, N) = \frac{2}{3} p^3 N^2 + O(p^2 N^2 + p^3 N)$ follows from this
exact formula.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 4 (`integers-2025-A10-lem-4`). -/
public theorem_wanted cyclotomicDistMoment_two (hp : p.Prime) (N : ℕ) :
    cyclotomicDistMoment p K N 2 = 2 / 3 * ((p : ℝ) ^ 3 - 2 * p ^ 2 + 1) * N * (N + 1)

/-- **Fourth-power sum of coordinate differences over a box.** Let $p$ be a prime and $N$ a
natural number, and let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$
with $|a_i| \le N$ for all $i$. Then
$$\sum_{i=1}^{p-1} \sum_{j=1}^{p-1} \sum_{a, b \in B(p, N)} (a_i - b_i)^2 (a_j - b_j)^2 =
(2N+1)^{2(p-1)} \cdot \tfrac{2}{45} N (N+1) (p-1) (10N^2 p + 4N^2 + 10Np + 4N - 3).$$

This corrects the paper's printed right side, which omits the factor $(2N+1)^{2(p-1)}$: for
$p = 3$ and $N = 1$ the sum is $936$, while the printed right side is $104/9$. The paper's own
proof carries the factors $(2N+1)^{2p-4}$ and $(2N+1)^{2p-6}$ in its pieces (10) and (11), and
combining them gives the value above; the printed formula is the sum divided by
$|B(p, N)|^2 = (2N+1)^{2(p-1)}$. The paper takes $p$ an odd prime; here only $p$ prime is
assumed.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 5 (`integers-2025-A10-lem-5`). -/
public theorem_wanted sum_sq_sub_mul_sq_sub_box (p : ℕ) (hp : p.Prime) (N : ℕ) :
    ∑ i : Fin (p - 1), ∑ j : Fin (p - 1),
      ∑ a ∈ Fintype.piFinset (fun _ : Fin (p - 1) => Finset.Icc (-(N : ℤ)) N),
        ∑ b ∈ Fintype.piFinset (fun _ : Fin (p - 1) => Finset.Icc (-(N : ℤ)) N),
          (((a i - b i) ^ 2 * (a j - b j) ^ 2 : ℤ) : ℚ) =
      (2 * N + 1) ^ (2 * (p - 1)) * (2 / 45 * N * (N + 1) * ((p : ℚ) - 1) *
        (10 * N ^ 2 * p + 4 * N ^ 2 + 10 * N * p + 4 * N - 3))

/-- **Fourth moment of the trace distance on the cyclotomic box.** Let $p$ be a prime, let $N$ be
a natural number, and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of
unity, with fixed primitive $p$-th root of unity $\omega \in K$. Let $M_4(p, N)$ be the fourth
moment of the trace metric $d$ of $K$ over the box $B(p, N)$: the average of
$d(\alpha_a, \alpha_b)^4$ over all pairs $(a, b)$ of integer vectors in $\mathbb{Z}^{p-1}$ whose
coordinates lie in $[-N, N]$, where $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Then
$$
M_4(p, N) = \frac{2}{45} N (N + 1) (p - 1) \bigl( (2 N^2 + 2 N)
(5 p^5 - 8 p^4 + p^3 + 8 p^2 - 21 p - 18) - 3 (p^2 - p - 1)^2 \bigr).
$$

The asymptotic form $M_4(p, N) = \frac{4}{9} p^6 N^4 + O(p^5 N^4 + p^6 N^3)$ follows from this
exact formula.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 6 (`integers-2025-A10-lem-6`). -/
public theorem_wanted cyclotomicDistMoment_four (hp : p.Prime) (N : ℕ) :
    cyclotomicDistMoment p K N 4 = 2 / 45 * N * (N + 1) * (p - 1) *
      ((2 * (N : ℝ) ^ 2 + 2 * N) * (5 * p ^ 5 - 8 * p ^ 4 + p ^ 3 + 8 * p ^ 2 - 21 * p - 18) -
        3 * ((p : ℝ) ^ 2 - p - 1) ^ 2)

/-- **Variance bound for squared trace distances in the box.** There is a real number $C$
such that the following holds for every prime $p$, every integer $N \ge 1$ and every $p$-th
cyclotomic extension $K$ of $\mathbb{Q}$. Let $\omega$ be the chosen primitive $p$-th root of
unity in $K$, let $d$ be the trace distance on $K$, and let $B(p, N)$ be the set of integer
vectors $a = (a_1, \dots, a_{p-1})$ with $|a_i| \le N$ for all $i$, where $a$ stands for the
point $a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ of $K$. Then
$$R(p, N) = \frac{1}{|B(p, N)|^2} \sum_{\alpha, \beta \in B(p, N)}
\left( d(\alpha, \beta)^2 - \tfrac{2}{3} p^3 N^2 \right)^2 \le
C \left( p^5 N^4 + p^6 N^3 \right).$$

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 7 (`integers-2025-A10-lem-7`). -/
public theorem_wanted exists_cyclotomicDist_variance_le :
    ∃ C : ℝ, ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → 1 ≤ N →
      (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
          (cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ^ 2 -
            2 / 3 * (p : ℝ) ^ 3 * N ^ 2) ^ 2) / ((cyclotomicBox p N).card : ℝ) ^ 2 ≤
        C * ((p : ℝ) ^ 5 * N ^ 4 + (p : ℝ) ^ 6 * N ^ 3)

/-- **Almost all pairs in the cyclotomic box are nearly equidistant.** For every real
$\varepsilon > 0$ there is a natural number $A$ with the following property. Let $p$ be a prime
and $N$ a natural number with $p > A$ and $N > A$, and let $K$ be a field generated over
$\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed primitive $p$-th root of unity
$\omega \in K$. Let $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$ be the trace metric on $K$,
where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, and write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. Then fewer than
$\varepsilon \lvert B(p, N) \rvert^2$ pairs $(a, b) \in B(p, N)^2$ satisfy
$$
\left| \frac{d(\alpha_a, \alpha_b)}{2 N p \sqrt{p - 1}} - \frac{1}{\sqrt{6}} \right| > \varepsilon.
$$

The constant $A$ depends only on $\varepsilon$; it is not claimed to be effectively computable.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 1 (`integers-2025-A10-thm-1`). -/
public theorem_wanted cyclotomicBox_almost_equidistant :
    ∀ ε > (0 : ℝ), ∃ A : ℕ, ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → A < p → A < N →
      ((((cyclotomicBox p N ×ˢ cyclotomicBox p N).filter fun ab =>
          ε < |cyclotomicTraceDist p (cyclotomicLatticePoint K ab.1)
              (cyclotomicLatticePoint K ab.2) /
            (2 * N * p * √(p - 1 : ℝ)) - 1 / √6|).card : ℝ)) <
        ε * ((cyclotomicBox p N).card : ℝ) ^ 2

/-- **Concentration of trace distances in the box, quantitative form.** There is a real
number $C$ such that the following holds for every real $\varepsilon > 0$, every prime $p$,
every integer $N \ge 1$ and every $p$-th cyclotomic extension $K$ of $\mathbb{Q}$. Let $\omega$
be the chosen primitive $p$-th root of unity in $K$, let $d$ be the trace distance on $K$, and
let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $|a_i| \le N$ for
all $i$, where $a$ stands for the point $a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ of $K$.
Among all pairs $(\alpha, \beta) \in B(p, N)^2$, the proportion of pairs with
$$\left| \frac{d(\alpha, \beta)}{2 N p^{3/2}} - \frac{1}{\sqrt{6}} \right| > \varepsilon$$
is at most $C \varepsilon^{-2} (1/p + 1/N)$.

The paper takes $p$ odd; here $p = 2$ is allowed. The paper also shows that $C$ is
effectively computable; only its existence is stated here.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 5 (`integers-2025-A10-thm-5`). -/
public theorem_wanted exists_cyclotomicBox_deviation_le :
    ∃ C : ℝ, ∀ ε > (0 : ℝ), ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → 1 ≤ N →
      ((((cyclotomicBox p N ×ˢ cyclotomicBox p N).filter fun ab =>
          ε < |cyclotomicTraceDist p (cyclotomicLatticePoint K ab.1)
              (cyclotomicLatticePoint K ab.2) /
            (2 * N * (p * √(p : ℝ))) - 1 / √6|).card : ℝ)) /
        ((cyclotomicBox p N).card : ℝ) ^ 2 ≤ C / ε ^ 2 * (1 / p + 1 / N)

end

end MetaMathlibExt
