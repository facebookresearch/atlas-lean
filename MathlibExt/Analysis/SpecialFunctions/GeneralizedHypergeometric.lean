/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Generalized hypergeometric series `ₚF_q`

This file defines the ordinary generalized hypergeometric coefficient

  `pFqCoeff(a, b, n) = (a₁)ₙ ⋯ (aₚ)ₙ / ((b₁)ₙ ⋯ (b_q)ₙ · n!)`

over an arbitrary field `K` and packages it as a `FormalMultilinearSeries`.
Here `(x)ₙ = (ascPochhammer K n).eval x` is the ascending Pochhammer symbol
`x·(x+1)⋯(x+n-1)` with `(x)₀ = 1`, and `p = a.card`, `q = b.card`.

Parameters are `Multiset K` because only multiplicity matters and order is
irrelevant; this matches Mathlib's `Complex.regularizedHGFunCoeff` API and
retains repeated parameters, while removing the source archive's ordered `List`
and permutation wrappers.

The definition uses totalized inverses in `K`.  A vanishing lower Pochhammer
product or factorial cast therefore gives the totalized value `0` rather than an
undefined term.  In particular the coefficient is defined as a formal algebraic
expression even at singular lower parameters `bᵢ ∈ {0, -1, -2, …}` and in
positive characteristic where `(n ! : K) = 0`; no analytic convergence claim is
made.  The regularized variant `Complex.regularizedHGFunCoeff` is distinct: it
is `ℂ`-only and replaces `((bᵢ)ₙ)⁻¹` by `(Γ(bᵢ+n))⁻¹`.

## Main definitions

* `MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient`
* `MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricSeries`

## Main results

* Construction: `generalizedHypergeometricCoefficient_zero`,
  `generalizedHypergeometricCoefficient_empty`,
  `generalizedHypergeometricCoefficient_cons_upper`,
  `generalizedHypergeometricCoefficient_cons_lower`
* Cancellation of a common non-singular parameter:
  `generalizedHypergeometricCoefficient_cons_both_cancel`
* Singular lower boundary (totalized `0`):
  `generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower`,
  `generalizedHypergeometricCoefficient_eq_zero_of_zero_mem_lower`
* Singular upper boundary:
  `generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper`
* Compatibility with Mathlib's `₂F₁`:
  `generalizedHypergeometricCoefficient_two_one`,
  `generalizedHypergeometricSeries_two_one`
* Formal series packaging:
  `generalizedHypergeometricSeries_apply_eq`,
  `generalizedHypergeometricSeries_apply_zero`

## Analytic layer (ℂ)

Following arXiv:2608.10675 `KMY-Conj.tex:456-470`, `_{m+1}F_m` is presented as
the infinite sum of Pochhammer-product coefficients with lower parameters
excluded from `ℤ_{\le 0}`. The `ℂ`-valued `tsum` is defined unconditionally
as `∑' n, coeff n * z^n`; admissibility and summability appear only as
hypotheses of theorems where they are used. The source asserts absolute
convergence for `|z| < 1`, but this module proves only the terminating
finite-support case, not a radius theorem. The finite-sum identification
for a terminating upper parameter `-(N:ℂ)` is a generic algebraic consequence
of `ascPochhammer_eval_neg_coe_nat_of_lt` and needs no admissibility.

## Analytic definitions

* `MetaMathlibExt.GeneralizedHypergeometric.LowerParametersAdmissible`
* `MetaMathlibExt.GeneralizedHypergeometric.SummableHypergeometric`
* `MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricValue`

## Analytic statements

* `generalizedHypergeometricValue_eq_tsum`, `generalizedHypergeometricValue_hasSum`
* `lowerParametersAdmissible_ascPochhammer_ne_zero`,
  `lowerParametersAdmissible_forall_mem_ne_zero`
* `summableHypergeometric_of_neg_coe_nat_mem_upper`
* `generalizedHypergeometric_tsum_eq_finset_sum`,
  `generalizedHypergeometricValue_terminating_eq_finset_sum`

## References

* [Evaluations of the areal Mahler measure of multivariable
  polynomials](https://arxiv.org/abs/2306.15727)
* [Two supercongruences involving truncated hypergeometric
  series](https://arxiv.org/abs/2307.10000)
* [A proof of a weighted sum conjecture for finite multiple zeta values of level
  two](https://arxiv.org/abs/2608.10675)
-/

@[expose] public section

namespace MetaMathlibExt.GeneralizedHypergeometric

variable {K : Type*} [Field K]

/-- **Generalized hypergeometric coefficient.** Let $K$ be a field, let $a$ and $b$ be finite
multisets of elements of $K$ (the upper and lower parameters), and let $n$ be a natural number.
The $n$-th generalized hypergeometric coefficient is
$$
(n!)^{-1} \prod_{x \in a} (x)_n \Big(\prod_{y \in b} (y)_n\Big)^{-1},
$$
where $(x)_n = x(x+1)\cdots(x+n-1)$ is the rising factorial, with $(x)_0 = 1$, and the products
run over the multisets with multiplicity. It is the coefficient of $z^n$ in the generalized
hypergeometric series ${}_pF_q$ with $p = |a|$ and $q = |b|$.

Inverses are taken in $K$ with the convention $0^{-1} = 0$, so the coefficient is $0$ whenever
the lower product or $n!$ is zero in $K$; the latter can happen in positive characteristic. -/
noncomputable def generalizedHypergeometricCoefficient (a b : Multiset K) (n : ℕ) : K :=
  (n.factorial : K)⁻¹ * (a.map fun x => (ascPochhammer K n).eval x).prod *
    (b.map fun x => (ascPochhammer K n).eval x).prod⁻¹

@[simp]
theorem generalizedHypergeometricCoefficient_zero (a b : Multiset K) :
    generalizedHypergeometricCoefficient a b 0 = 1 := by
  simp [generalizedHypergeometricCoefficient]

@[simp]
theorem generalizedHypergeometricCoefficient_empty (n : ℕ) :
    generalizedHypergeometricCoefficient (0 : Multiset K) 0 n = (n.factorial : K)⁻¹ := by
  simp [generalizedHypergeometricCoefficient]

theorem generalizedHypergeometricCoefficient_cons_upper (x : K) (a b : Multiset K) (n : ℕ) :
    generalizedHypergeometricCoefficient (x ::ₘ a) b n =
      (ascPochhammer K n).eval x * generalizedHypergeometricCoefficient a b n := by
  simp [generalizedHypergeometricCoefficient, mul_assoc, mul_left_comm]

theorem generalizedHypergeometricCoefficient_cons_lower (a b : Multiset K) (x : K) (n : ℕ) :
    generalizedHypergeometricCoefficient a (x ::ₘ b) n =
      generalizedHypergeometricCoefficient a b n * ((ascPochhammer K n).eval x)⁻¹ := by
  simp only [generalizedHypergeometricCoefficient, Multiset.map_cons, Multiset.prod_cons, mul_inv]
  ac_rfl

theorem generalizedHypergeometricCoefficient_cons_both_cancel
    (x : K) (a b : Multiset K) (n : ℕ)
    (hx : (ascPochhammer K n).eval x ≠ 0) :
    generalizedHypergeometricCoefficient (x ::ₘ a) (x ::ₘ b) n =
      generalizedHypergeometricCoefficient a b n := by
  rw [generalizedHypergeometricCoefficient_cons_lower,
    generalizedHypergeometricCoefficient_cons_upper]
  calc
    (ascPochhammer K n).eval x * generalizedHypergeometricCoefficient a b n *
        ((ascPochhammer K n).eval x)⁻¹ =
      generalizedHypergeometricCoefficient a b n *
        ((ascPochhammer K n).eval x * ((ascPochhammer K n).eval x)⁻¹) := by ac_rfl
    _ = generalizedHypergeometricCoefficient a b n := by simp [hx]

theorem generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower
    (a b : Multiset K) {n k : ℕ} (hk : k < n) (hmem : -(k : K) ∈ b) :
    generalizedHypergeometricCoefficient a b n = 0 := by
  have hzero : (0 : K) ∈ b.map fun x => (ascPochhammer K n).eval x :=
    Multiset.mem_map.mpr ⟨-(k : K), hmem, ascPochhammer_eval_neg_coe_nat_of_lt hk⟩
  simp [generalizedHypergeometricCoefficient, Multiset.prod_eq_zero hzero]

theorem generalizedHypergeometricCoefficient_eq_zero_of_zero_mem_lower
    (a b : Multiset K) {n : ℕ} (hn : 0 < n) (hmem : (0 : K) ∈ b) :
    generalizedHypergeometricCoefficient a b n = 0 :=
  generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower a b (k := 0) hn
    (by simpa using hmem)

theorem generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper
    (a b : Multiset K) {n k : ℕ} (hk : k < n) (hmem : -(k : K) ∈ a) :
    generalizedHypergeometricCoefficient a b n = 0 := by
  have hzero : (0 : K) ∈ a.map fun x => (ascPochhammer K n).eval x :=
    Multiset.mem_map.mpr ⟨-(k : K), hmem, ascPochhammer_eval_neg_coe_nat_of_lt hk⟩
  simp [generalizedHypergeometricCoefficient, Multiset.prod_eq_zero hzero]

theorem generalizedHypergeometricCoefficient_two_one (a b c : K) (n : ℕ) :
    generalizedHypergeometricCoefficient ({a, b} : Multiset K) {c} n =
      ordinaryHypergeometricCoefficient a b c n := by
  simp [generalizedHypergeometricCoefficient, ordinaryHypergeometricCoefficient, mul_assoc]

variable {A : Type*} [Ring A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Generalized hypergeometric series.** Let $K$ be a field and $A$ a topological ring that is
a $K$-algebra. For finite multisets $a$ and $b$ of elements of $K$, the generalized
hypergeometric series is the formal multilinear series on $A$ whose $n$-th term is the
$n$-linear map $(x_1, \dots, x_n) \mapsto c_n \, x_1 x_2 \cdots x_n$, where $c_n \in K$ is the
$n$-th generalized hypergeometric coefficient with upper parameters $a$ and lower parameters
$b$. -/
noncomputable def generalizedHypergeometricSeries (a b : Multiset K) :
    FormalMultilinearSeries K A A :=
  FormalMultilinearSeries.ofScalars A (generalizedHypergeometricCoefficient a b)

theorem generalizedHypergeometricSeries_apply_eq (a b : Multiset K) (x : A) (n : ℕ) :
    generalizedHypergeometricSeries (A := A) a b n (fun _ => x) =
      generalizedHypergeometricCoefficient a b n • x ^ n := by
  simp [generalizedHypergeometricSeries, FormalMultilinearSeries.ofScalars_apply_eq]

theorem generalizedHypergeometricSeries_apply_zero (a b : Multiset K) (n : ℕ) :
    generalizedHypergeometricSeries (A := A) a b n (fun _ => (0 : A)) =
      Pi.single (M := fun _ => A) 0 1 n := by
  rw [generalizedHypergeometricSeries_apply_eq]
  cases n <;> simp

theorem generalizedHypergeometricSeries_two_one (a b c : K) :
    generalizedHypergeometricSeries (A := A) ({a, b} : Multiset K) {c} =
      ordinaryHypergeometricSeries A a b c := by
  simp only [generalizedHypergeometricSeries, ordinaryHypergeometricSeries]
  congr 1
  ext n
  exact generalizedHypergeometricCoefficient_two_one a b c n

/-! ### Complex analytic layer -/

/-- **Admissible lower parameters.** A finite multiset $B$ of complex numbers is admissible as
lower parameters if no element of $B$ is $0$ or a negative integer, that is, $-k \notin B$ for
every natural number $k$.

Source: arXiv:2608.10675, KMY-Conj.tex lines 456–470, the exclusion of lower parameters from
$\mathbb{Z}_{\le 0}$ for ${}_{m+1}F_m$. -/
def LowerParametersAdmissible (bs : Multiset ℂ) : Prop :=
  ∀ k : ℕ, (-(k : ℂ) ∉ bs)

/-- **Summability of the generalized hypergeometric series.** For finite multisets $a$ and $b$ of
complex numbers and $z \in \mathbb{C}$, the generalized hypergeometric series with upper
parameters $a$ and lower parameters $b$ is summable at $z$ if the family $(c_n z^n)_{n \ge 0}$ is
summable in $\mathbb{C}$, where $c_n$ is the $n$-th generalized hypergeometric coefficient.

Summability of a family in $\mathbb{C}$ is unconditional summability, which is equivalent to
absolute convergence of $\sum_n c_n z^n$. -/
abbrev SummableHypergeometric (a b : Multiset ℂ) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => generalizedHypergeometricCoefficient a b n * z ^ n)

/-- **Generalized hypergeometric function.** For finite multisets $a$ and $b$ of complex numbers
and $z \in \mathbb{C}$, the value ${}_pF_q(a; b; z)$, where $p = |a|$ and $q = |b|$, is the sum
$\sum_{n \ge 0} c_n z^n$, where $c_n$ is the $n$-th generalized hypergeometric coefficient with
upper parameters $a$ and lower parameters $b$.

The sum is the unconditional sum of the family $(c_n z^n)_{n \ge 0}$, which is $0$ by convention
when that family is not summable; no condition on the parameters or on $z$ is imposed.

Source: arXiv:2608.10675, KMY-Conj.tex lines 456–470, the infinite-sum presentation of
${}_{m+1}F_m$. -/
noncomputable def generalizedHypergeometricValue (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, generalizedHypergeometricCoefficient a b n * z ^ n

theorem generalizedHypergeometricValue_eq_tsum (a b : Multiset ℂ) (z : ℂ) :
    generalizedHypergeometricValue a b z =
      ∑' n : ℕ, generalizedHypergeometricCoefficient a b n * z ^ n :=
  rfl

theorem generalizedHypergeometricValue_hasSum {a b : Multiset ℂ} {z : ℂ}
    (hsum : SummableHypergeometric a b z) :
    HasSum (fun n : ℕ => generalizedHypergeometricCoefficient a b n * z ^ n)
      (generalizedHypergeometricValue a b z) :=
  hsum.hasSum

/-- **Rising factorials at admissible lower parameters are nonzero.** Let $B$ be a finite
multiset of complex numbers that is admissible as lower parameters. Then for every $b \in B$ and
every natural number $n$, the rising factorial $(b)_n = b(b+1)\cdots(b+n-1)$, with $(b)_0 = 1$,
is nonzero.

This follows because over $\mathbb{C}$, $(b)_n = 0$ if and only if $b = -k$ for some natural
number $k < n$. -/
theorem lowerParametersAdmissible_ascPochhammer_ne_zero {bs : Multiset ℂ}
    (hadm : LowerParametersAdmissible bs) {b : ℂ} (hb : b ∈ bs) (n : ℕ) :
    (ascPochhammer ℂ n).eval b ≠ 0 := by
  intro h0
  rw [ascPochhammer_eval_eq_zero_iff] at h0
  obtain ⟨k, hk, hk_eq⟩ := h0
  have hb_eq : b = -(k : ℂ) := by
    calc b = - -b := (neg_neg b).symm
      _ = -(k : ℂ) := by rw [← hk_eq]
  have : (-(k : ℂ) ∈ bs) := hb_eq ▸ hb
  exact hadm k this

theorem lowerParametersAdmissible_forall_mem_ne_zero {bs : Multiset ℂ}
    (hadm : LowerParametersAdmissible bs) :
    ∀ b ∈ bs, ∀ n : ℕ, (ascPochhammer ℂ n).eval b ≠ 0 :=
  fun b hb n => lowerParametersAdmissible_ascPochhammer_ne_zero (b := b) hadm hb n

/-- **Terminating generalized hypergeometric series are summable.** Let $a$ and $b$ be finite
multisets of complex numbers, and let $c_n$ be the $n$-th generalized hypergeometric coefficient
with upper parameters $a$ and lower parameters $b$. If $-N \in a$ for some natural number $N$,
then for every $z \in \mathbb{C}$ the family $(c_n z^n)_{n \ge 0}$ is summable, that is, the
generalized hypergeometric series with these parameters is summable at $z$.

Only finitely many terms are nonzero, since $c_n = 0$ for $n > N$; no condition on the lower
parameters is needed. -/
theorem summableHypergeometric_of_neg_coe_nat_mem_upper
    {a b : Multiset ℂ} {N : ℕ} {z : ℂ}
    (hmem : (-(N : ℂ) ∈ a)) :
    SummableHypergeometric a b z := by
  unfold SummableHypergeometric
  have hzero : ∀ n : ℕ, N < n → generalizedHypergeometricCoefficient a b n * z ^ n = 0 := by
    intro n hlt
    rw [generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper a b hlt hmem,
      zero_mul]
  have hzero' : ∀ n : ℕ, n ∉ Finset.range (N + 1) →
      generalizedHypergeometricCoefficient a b n * z ^ n = 0 := by
    intro n hn
    have hlt : N < n := by
      simp [Finset.mem_range] at hn
      omega
    exact hzero n hlt
  exact summable_of_ne_finset_zero hzero'

/-- **Terminating generalized hypergeometric series are finite sums.** Let $a$ and $b$ be finite
multisets of complex numbers, and let $c_n$ be the $n$-th generalized hypergeometric coefficient
with upper parameters $a$ and lower parameters $b$. If $-N \in a$ for some natural number $N$,
then for every $z \in \mathbb{C}$
$$
\sum_{n=0}^{\infty} c_n z^n = \sum_{n=0}^{N} c_n z^n.
$$

No condition on the lower parameters is needed: $c_n = 0$ for $n > N$ because the rising
factorial $(-N)_n = (-N)(-N+1)\cdots(-N+n-1)$ vanishes. -/
theorem generalizedHypergeometric_tsum_eq_finset_sum
    {a b : Multiset ℂ} {N : ℕ} {z : ℂ}
    (hmem : (-(N : ℂ) ∈ a)) :
    (∑' n : ℕ, generalizedHypergeometricCoefficient a b n * z ^ n) =
      ∑ n ∈ Finset.range (N + 1), generalizedHypergeometricCoefficient a b n * z ^ n := by
  have hzero : ∀ n : ℕ, N < n → generalizedHypergeometricCoefficient a b n * z ^ n = 0 := by
    intro n hlt
    rw [generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper a b hlt hmem,
      zero_mul]
  have hzero' : ∀ n : ℕ, n ∉ Finset.range (N + 1) →
      generalizedHypergeometricCoefficient a b n * z ^ n = 0 := by
    intro n hn
    have hlt : N < n := by
      simp [Finset.mem_range] at hn
      omega
    exact hzero n hlt
  exact tsum_eq_sum hzero'

theorem generalizedHypergeometricValue_terminating_eq_finset_sum
    {a b : Multiset ℂ} {N : ℕ} {z : ℂ}
    (hmem : (-(N : ℂ) ∈ a)) :
    generalizedHypergeometricValue a b z =
      ∑ n ∈ Finset.range (N + 1), generalizedHypergeometricCoefficient a b n * z ^ n := by
  unfold generalizedHypergeometricValue
  exact generalizedHypergeometric_tsum_eq_finset_sum hmem

end MetaMathlibExt.GeneralizedHypergeometric
