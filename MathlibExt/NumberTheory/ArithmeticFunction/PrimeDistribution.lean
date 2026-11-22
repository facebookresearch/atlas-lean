/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Finite arithmetic discrepancy and positive-index convolution

Finite arithmetic sequences are ordinary `Finsupp`s, with index zero discarded.
Discrepancy supports real or complex coefficients. Multiplicative convolution
uses Mathlib's monoid-algebra product, not additive convolution or supplied data.
Primitive-residue maxima have intrinsically positive moduli.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeDistribution

/-- **Discrepancy in a residue class.** Let $K$ be a field of characteristic zero, let
$\alpha : \mathbb{N} \to K$ be finitely supported, let $q$ be a positive integer and let $a$ be a
natural number. The discrepancy of $\alpha$ in the residue class of $a$ modulo $q$ is
$$\Delta(\alpha; a \bmod q) = \sum_{\substack{n \ge 1 \\ n \equiv a \pmod{q}}} \alpha(n) -
\frac{1}{\varphi(q)} \sum_{\substack{n \ge 1 \\ \gcd(n, q) = 1}} \alpha(n),$$
where $\varphi$ is Euler's totient function. The value $\alpha(0)$ does not contribute. -/
noncomputable def discrepancy {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : ℕ →₀ 𝕜)
    (q : ℕ+) (a : ℕ) : 𝕜 :=
  α.sum (fun n v ↦ if 0 < n ∧ n % q = a % q then v else 0) -
    α.sum (fun n v ↦ if 0 < n ∧ Nat.Coprime n q then v else 0) / (Nat.totient (q : ℕ) : 𝕜)

/-- **A sequence supported at index zero has zero discrepancy.** Let $K$ be a field of
characteristic zero, let $v \in K$, let $q$ be a positive integer and let $a \in \mathbb{N}$. The
sequence with value $v$ at index $0$ and $0$ at every other index has discrepancy $0$ at
modulus $q$ and residue $a$. -/
@[simp] theorem discrepancy_single_zero {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (v : 𝕜)
    (q : ℕ+) (a : ℕ) :
    discrepancy (Finsupp.single 0 v) q a = 0 := by
  simp [discrepancy]

/-- **Discrepancy of a single positive term.** Let $K$ be a field of characteristic zero, let $n$
be a positive integer, let $v \in K$, let $q$ be a positive integer and let $a \in \mathbb{N}$.
Let $e$ be the sequence with value $v$ at index $n$ and $0$ at every other index. Then the
discrepancy of $e$ at modulus $q$ and residue $a$ equals $A - B/\varphi(q)$, where $A = v$ if
$n \equiv a \pmod{q}$ and $A = 0$ otherwise, $B = v$ if $\gcd(n, q) = 1$ and $B = 0$ otherwise,
and $\varphi$ is Euler's totient function. -/
theorem discrepancy_single {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (n : ℕ) (hn : 0 < n)
    (v : 𝕜) (q : ℕ+) (a : ℕ) :
    discrepancy (Finsupp.single n v) q a =
      (if n % q = a % q then v else 0) -
        (if Nat.Coprime n q then v else 0) / (Nat.totient (q : ℕ) : 𝕜) := by
  simp [discrepancy, hn]

/-- **Primitive discrepancy.** For a finitely supported sequence
$\alpha : \mathbb{N} \to \mathbb{R}$ and a positive integer $q$, the primitive discrepancy of
$\alpha$ modulo $q$ is the maximum, over the residue classes $a$ modulo $q$ that are coprime to
$q$, of $|\Delta(\alpha; a \bmod q)|$, where $\Delta(\alpha; a \bmod q)$ is the discrepancy of
$\alpha$ in the residue class of $a$ modulo $q$. -/
noncomputable def primitiveDiscrepancy (α : ℕ →₀ ℝ) (q : ℕ+) : ℝ :=
  ⨆ a : (ZMod (q : ℕ))ˣ, |discrepancy α q a.val.val|

/-- **The primitive discrepancy is attained.** For every finitely supported sequence
$\alpha : \mathbb{N} \to \mathbb{R}$ and every positive integer $q$, there is a residue class $a$
modulo $q$ coprime to $q$ such that the primitive discrepancy of $\alpha$ modulo $q$ equals
$|\Delta(\alpha; a \bmod q)|$, the absolute value of the discrepancy of $\alpha$ in the residue
class of $a$ modulo $q$. -/
theorem primitiveDiscrepancy_attained (α : ℕ →₀ ℝ) (q : ℕ+) :
    ∃ a : (ZMod (q : ℕ))ˣ, primitiveDiscrepancy α q = |discrepancy α q a.val.val| := by
  let : NeZero (q : ℕ) := ⟨ne_of_gt q.pos⟩
  obtain ⟨a, ha⟩ := Finite.ciSup_mem (fun a : (ZMod (q : ℕ))ˣ ↦
    |discrepancy α q a.val.val|)
  exact ⟨a, ha.symm⟩

/-- **Primitive residue-class discrepancies are bounded by the primitive discrepancy.** Let
$\alpha$ be a finitely supported real sequence indexed by $\mathbb{N}$, let $q$ be a positive
integer, and let $a$ be a unit of $\mathbb{Z}/q\mathbb{Z}$, represented by its least nonnegative
residue. Then the absolute value of the discrepancy of $\alpha$ at modulus $q$ and residue $a$ is
at most the primitive discrepancy of $\alpha$ at modulus $q$. -/
theorem abs_discrepancy_le_primitiveDiscrepancy (α : ℕ →₀ ℝ) (q : ℕ+)
    (a : (ZMod (q : ℕ))ˣ) : |discrepancy α q a.val.val| ≤ primitiveDiscrepancy α q := by
  let : NeZero (q : ℕ) := ⟨ne_of_gt q.pos⟩
  exact le_ciSup (Set.finite_range (fun a : (ZMod (q : ℕ))ˣ ↦
    |discrepancy α q a.val.val|)).bddAbove a

/-- **Averaged discrepancy.** For a finitely supported real sequence $\alpha$ indexed by
$\mathbb{N}$ and a natural number $Q$, the averaged discrepancy of $\alpha$ up to $Q$ is the sum
$\sum_{q=1}^{Q} \Delta^*(\alpha; q)$, where $\Delta^*(\alpha; q)$ is the primitive discrepancy
of $\alpha$ at modulus $q$.

The sum is not divided by $Q$. -/
noncomputable def averagedDiscrepancy (α : ℕ →₀ ℝ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, if h : 0 < q then primitiveDiscrepancy α ⟨q, h⟩ else 0

/-- **The averaged discrepancy with cutoff zero vanishes.** For every finitely supported real
sequence $\alpha$ indexed by $\mathbb{N}$, the averaged discrepancy of $\alpha$ with cutoff
$Q = 0$ equals $0$, since there are no positive moduli $q \le 0$. -/
@[simp] theorem averagedDiscrepancy_zero (α : ℕ →₀ ℝ) : averagedDiscrepancy α 0 = 0 := by
  simp [averagedDiscrepancy]

/-- **Multiplicative convolution of finitely supported sequences.** Let $R$ be a semiring and let
$\alpha, \beta \colon \mathbb{N} \to R$ be finitely supported. Their convolution
$\alpha \star \beta$ is the finitely supported sequence whose value at $n$ is
$\sum_{a, b \ge 1,\ ab = n} \alpha(a)\beta(b)$; the values of $\alpha$ and $\beta$ at index $0$
are discarded. -/
noncomputable def convolution {R : Type*} [Semiring R] (α β : ℕ →₀ R) : ℕ →₀ R :=
  (MonoidAlgebra.ofCoeff (α.filter (fun n ↦ 0 < n)) *
    MonoidAlgebra.ofCoeff (β.filter (fun n ↦ 0 < n)) : MonoidAlgebra R ℕ).coeff

/-- **Coefficients of the multiplicative convolution.** Let $R$ be a semiring and let
$\alpha, \beta \colon \mathbb{N} \to R$ be finitely supported, with convolution
$\alpha \star \beta$. For every $n \in \mathbb{N}$,
$$(\alpha \star \beta)(n) = \sum_{a} \sum_{b} [ab = n]\, \alpha(a)\beta(b),$$
where $a$ ranges over the positive indices with $\alpha(a) \ne 0$, $b$ ranges over the positive
indices with $\beta(b) \ne 0$, and $[ab = n]$ is $1$ if $ab = n$ and $0$ otherwise. -/
theorem convolution_apply {R : Type*} [Semiring R] (α β : ℕ →₀ R) (n : ℕ) :
    convolution α β n =
      (α.filter (fun a ↦ 0 < a)).sum (fun a u ↦
        (β.filter (fun b ↦ 0 < b)).sum (fun b v ↦ if a * b = n then u * v else 0)) :=
  MonoidAlgebra.coeff_mul _ _ _

/-- **The multiplicative convolution vanishes at index zero.** Let $R$ be a semiring and let
$\alpha, \beta \colon \mathbb{N} \to R$ be finitely supported. Then their convolution
$\alpha \star \beta$ has value $0$ at index $0$. -/
@[simp] theorem convolution_apply_zero {R : Type*} [Semiring R] (α β : ℕ →₀ R) :
    convolution α β 0 = 0 := by
  rw [convolution_apply, Finsupp.sum_filter_index]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finsupp.sum_filter_index]
  apply Finset.sum_eq_zero
  intro b hb
  have ha_pos : 0 < a := by
    rw [Finsupp.support_filter] at ha
    exact (Finset.mem_filter.mp ha).2
  have hb_pos : 0 < b := by
    rw [Finsupp.support_filter] at hb
    exact (Finset.mem_filter.mp hb).2
  simp [Nat.ne_of_gt ha_pos, Nat.ne_of_gt hb_pos]

/-- **Convolving a sequence supported at zero gives zero.** Let $R$ be a semiring, let $v \in R$,
and let $\beta \colon \mathbb{N} \to R$ be finitely supported. If $e$ is the sequence with value
$v$ at index $0$ and $0$ at every other index, then the convolution $e \star \beta$ is the zero
sequence. -/
@[simp] theorem convolution_single_zero_left {R : Type*} [Semiring R]
    (v : R) (β : ℕ →₀ R) : convolution (Finsupp.single 0 v) β = 0 := by
  simp [convolution]

/-- **Convolving with a sequence supported at zero gives zero.** Let $R$ be a semiring, let
$\alpha \colon \mathbb{N} \to R$ be finitely supported, and let $v \in R$. If $e$ is the sequence
with value $v$ at index $0$ and $0$ at every other index, then the convolution
$\alpha \star e$ is the zero sequence. -/
@[simp] theorem convolution_single_zero_right {R : Type*} [Semiring R]
    (α : ℕ →₀ R) (v : R) : convolution α (Finsupp.single 0 v) = 0 := by
  simp [convolution]

/-- **Von Mangoldt function on a dyadic interval.** For a real number $x$, this is the finitely
supported function on $\mathbb{N}$ whose value at $n$ is $\Lambda(n)$ when $n \ge 1$ and
$x \le n \le 2x$, and $0$ otherwise, where $\Lambda$ is the von Mangoldt function.

Source: Polymath8b v4, Claim 2.2 and the positive-integer convention before Definition 1.6. -/
noncomputable def dyadicVonMangoldt (x : ℝ) : ℕ →₀ ℝ :=
  Finsupp.onFinset (Finset.Icc 1 ⌊2 * x⌋₊)
    (fun n ↦ if n ∈ Finset.Icc 1 ⌊2 * x⌋₊ ∧ x ≤ (n : ℝ) then
      ArithmeticFunction.vonMangoldt n else 0)
    (by intro n; contrapose!; simp_all)

/-- **Values of the dyadic von Mangoldt function.** For every real $x > 0$ and every natural
number $n$, the von Mangoldt function on the dyadic interval for $x$ takes at $n$ the value
$\Lambda(n)$ if $x \le n \le 2x$, and $0$ otherwise, where $\Lambda$ is the von Mangoldt function.

Source: Polymath8b v4, Claim 2.2. -/
theorem dyadicVonMangoldt_apply (x : ℝ) (hx : 0 < x) (n : ℕ) :
    dyadicVonMangoldt x n =
      if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then ArithmeticFunction.vonMangoldt n else 0 := by
  unfold dyadicVonMangoldt
  rw [Finsupp.onFinset_apply]
  congr 1
  apply propext
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hfloor⟩, hxle⟩
    exact ⟨hxle, (Nat.cast_le.mpr hfloor).trans (Nat.floor_le (by positivity))⟩
  · rintro ⟨hxle, hnle⟩
    have hn : 1 ≤ n := by
      by_contra h
      have hn0 : n = 0 := by omega
      simp [hn0] at hxle
      linarith
    exact ⟨⟨hn, Nat.le_floor hnle⟩, hxle⟩

end MathlibExt.NumberTheory.PrimeDistribution
