/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Zeckendorf
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.Data.Set.Density
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic

/-!
# Variation of the Zeckendorf sum of digits

Density statements from Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf
Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of
Integer Sequences 27 (2024), Article 24.3.2 (definitions read from arXiv:2309.14285v2).

The Zeckendorf sum of digits `s(n)` is the number of Fibonacci terms in the Zeckendorf
representation of `n`, i.e. `(Nat.zeckendorf n).length`. For `r, n ∈ ℕ` the variation is
`Δ^{(r)}(n) = s(n + r) - s(n)`, and `μ^{(r)}(d)` is the asymptotic density
`lim_{N → ∞} |{n < N : Δ^{(r)}(n) = d}| / N`. It is stated with `Set.HasDensity` from
`MathlibExt.Data.Set.Density` (natural density over `ℕ`). The paper's Fibonacci numbers
`F_1 = F_2 = 1` are `Nat.fib`, and `φ` is `Real.goldenRatio`.

The second part states the paper's results on the Zeckendorf-adic integers `𝕏` (`zeckAdic`,
digit sequences `ℕ → Bool` indexed from `2`), the odometer `T(x) = x + 1` (`zeckOdometer`, with
`x + r = T^[r] x`), its invariant measure `ℙ` (any `T`-invariant probability measure on
`ℕ → Bool` carried by `𝕏`; it is unique by Proposition 15), and the variation
`Δ^{(r)} = lim_k Δ_k^{(r)}` on `𝕏`, the Rokhlin towers and new-information zones `NIZ_k` of the
paper's algorithm, and the block decomposition `Δ^{(r)} = ∑ X_i^{(r)}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fibonacci shifts have the same Zeckendorf variation densities as shift one.** For
$n \in \mathbb{N}$ let $s(n)$ be the number of terms in the Zeckendorf representation of $n$, and
let $F_\ell$ be the $\ell$-th Fibonacci number ($F_1 = F_2 = 1$). Let $\ell \ge 2$ and let
$\mu : \mathbb{Z} \to \mathbb{R}$ be such that for every $d \in \mathbb{Z}$ the set
$\{n \in \mathbb{N} : s(n + 1) - s(n) = d\}$ has natural density $\mu(d)$. Then for every
$d \in \mathbb{Z}$ the set $\{n \in \mathbb{N} : s(n + F_\ell) - s(n) = d\}$ also has natural
density $\mu(d)$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Theorem 3 (`jis-2024-24.3.2-thm-3`, for `ℓ ≥ 3`) and its restatement in
Section 6 (`jis-2024-24.3.2-thm-unnumbered-1`, for `ℓ ≥ 2`). -/
public theorem_wanted zeckendorf_variation_density_fib_eq_one {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (μ : ℤ → ℝ)
    (hμ : ∀ d : ℤ, Set.HasDensity
        {n : ℕ | ((Nat.zeckendorf (n + 1)).length : ℤ) - (Nat.zeckendorf n).length = d}
        (μ d))
    (d : ℤ) :
    Set.HasDensity
        {n : ℕ | ((Nat.zeckendorf (n + Nat.fib ℓ)).length : ℤ) - (Nat.zeckendorf n).length = d}
        (μ d)

/-- **Distribution of the Zeckendorf digit-sum variation for shift one.** For $n \in \mathbb{N}$
let $s(n)$ be the number of terms in the Zeckendorf representation of $n$, and let $\varphi$ be the
golden ratio. For every $d \in \mathbb{Z}$ the set $\{n \in \mathbb{N} : s(n + 1) - s(n) = d\}$
has natural density $0$ if $d \ge 2$, $1/\varphi^2$ if $d = 1$, and $1/\varphi^{2 - 2d}$ if
$d \le 0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 39 (`jis-2024-24.3.2-prop-39`). -/
public theorem_wanted zeckendorf_variation_density_one (d : ℤ) :
    Set.HasDensity
        {n : ℕ | ((Nat.zeckendorf (n + 1)).length : ℤ) - (Nat.zeckendorf n).length = d}
        (if 2 ≤ d then 0 else if d = 1 then 1 / Real.goldenRatio ^ 2
          else 1 / Real.goldenRatio ^ (2 - 2 * d))

/-- **Zeckendorf variation densities exist, with finite moments and mean zero.** For
$n \in \mathbb{N}$ let $s(n)$ be the number of terms in the Zeckendorf representation of $n$. For
every $r \in \mathbb{N}$ there is a function $\mu : \mathbb{Z} \to \mathbb{R}$ such that for every
$d \in \mathbb{Z}$ the set $\{n \in \mathbb{N} : s(n + r) - s(n) = d\}$ has natural density
$\mu(d)$, the series $\sum_{d \in \mathbb{Z}} |d|^k \mu(d)$ converges absolutely for every
$k \in \mathbb{N}$, and $\sum_{d \in \mathbb{Z}} d \, \mu(d) = 0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 24 (`jis-2024-24.3.2-cor-24`), with the remark after it for
`r = 0`. -/
public theorem_wanted zeckendorf_variation_density_exists_moments (r : ℕ) :
    ∃ μ : ℤ → ℝ,
      (∀ d : ℤ, Set.HasDensity
        {n : ℕ | ((Nat.zeckendorf (n + r)).length : ℤ) - (Nat.zeckendorf n).length = d}
        (μ d)) ∧
      (∀ k : ℕ, Summable fun d : ℤ => |(d : ℝ)| ^ k * μ d) ∧
      ∑' d : ℤ, (d : ℝ) * μ d = 0

/-- **Geometric negative tail of the Zeckendorf variation densities.** For $n \in \mathbb{N}$ let
$s(n)$ be the number of terms in the Zeckendorf representation of $n$, and let $\varphi$ be the
golden ratio. Let $r \in \mathbb{N}$ and let $\mu : \mathbb{Z} \to \mathbb{R}$ be such that for
every $d \in \mathbb{Z}$ the set $\{n \in \mathbb{N} : s(n + r) - s(n) = d\}$ has natural density
$\mu(d)$. Then there is $D \in \mathbb{Z}$ such that $\mu(d - 1) = \mu(d)/\varphi^2$ for every
integer $d \le D$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 1 (`jis-2024-24.3.2-cor-1`) and its restatement in Section 5
(`jis-2024-24.3.2-cor-unnumbered-1`). -/
public theorem_wanted zeckendorf_variation_density_tail (r : ℕ) (μ : ℤ → ℝ)
    (hμ : ∀ d : ℤ, Set.HasDensity
        {n : ℕ | ((Nat.zeckendorf (n + r)).length : ℤ) - (Nat.zeckendorf n).length = d}
        (μ d)) :
    ∃ D : ℤ, ∀ d ≤ D, μ (d - 1) = μ d / Real.goldenRatio ^ 2


/-! ### The Zeckendorf-adic odometer -/

/-- **The Zeckendorf-adic integers.** The Zeckendorf-adic integers $\mathbb{X}$ are the digit
sequences $x = (x_k)_{k \ge 0}$ with $x_k \in \{0, 1\}$ such that $x_0 = x_1 = 0$ and no two
consecutive digits are both $1$, that is, $x_k x_{k+1} = 0$ for every $k$.

Digit $k \ge 2$ carries the weight $F_k$ (with $F_1 = F_2 = 1$). The unused digits $x_0$ and
$x_1$ keep the paper's indexing, in which
$\mathbb{X} = \{x \in \{0,1\}^{\mathbb{N}_{\ge 2}} : x_k x_{k+1} = 0 \text{ for all } k \ge 2\}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (arXiv:2309.14285v2). -/
public def zeckAdic : Set (ℕ → Bool) :=
  {x | x 0 = false ∧ x 1 = false ∧ ∀ k, x k = false ∨ x (k + 1) = false}

/-- **Zeckendorf digit sequence of a natural number.** Let $F_k$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = F_2 = 1$). Every $n \in \mathbb{N}$ has a unique Zeckendorf representation
$n = F_{k_1} + \dots + F_{k_m}$ with $k_1 > \dots > k_m \ge 2$ and no two consecutive indices.
The Zeckendorf digit sequence of $n$ is the binary sequence $(x_k)_{k \in \mathbb{N}}$ with
$x_k = 1$ if $k$ is one of the indices $k_1, \dots, k_m$ and $x_k = 0$ otherwise.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (the map `i`). -/
public def zeckAdicOfNat (n : ℕ) : ℕ → Bool := fun k => decide (k ∈ Nat.zeckendorf n)

/-- **The Zeckendorf odometer.** The odometer is the map $T$ on digit sequences
$x = (x_k)_{k \in \mathbb{N}}$ with $x_k \in \{0, 1\}$ defined as follows. If $x_k = x_{k+1} = 0$
for some $k \ge 2$, let $k$ be the least such index; then $T(x)_j = 0$ for $j < k$, $T(x)_k = 1$
and $T(x)_j = x_j$ for $j > k$. If there is no such $k$, then $T(x)$ is the zero sequence.

On a Zeckendorf-adic integer, where digit $k \ge 2$ carries the weight of the Fibonacci number
$F_k$, the map $T$ is addition of $1$, and $x + r$ denotes $T^r(x)$ for $r \in \mathbb{N}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (definition of `T`). -/
public noncomputable def zeckOdometer (x : ℕ → Bool) : ℕ → Bool :=
  open Classical in
  if h : ∃ k, 2 ≤ k ∧ x k = false ∧ x (k + 1) = false then
    fun j => if j < Nat.find h then false else if j = Nat.find h then true else x j
  else fun _ => false

/-- **Zeckendorf digit sequence of zero.** The Zeckendorf digit sequence of $0$ is the zero
sequence: all of its digits are $0$, because the Zeckendorf representation of $0$ is empty.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (characteristic lemma for the map `i`). -/
public theorem zeckAdicOfNat_zero : zeckAdicOfNat 0 = fun _ => false := by
  funext k
  simp [zeckAdicOfNat]

/-- **The odometer on a point ending in $00$.** If a Zeckendorf-adic integer
$x = (x_k)_{k \ge 2}$ has $x_2 = x_3 = 0$, then the odometer $T(x) = x + 1$ sets the unit digit
$x_2$ to $1$ and leaves every other digit of $x$ unchanged.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (case `ℓ = 0` of the definition of `T`). -/
public theorem zeckOdometer_eq_update {x : ℕ → Bool} (hx : x ∈ zeckAdic) (h2 : x 2 = false)
    (h3 : x 3 = false) : zeckOdometer x = Function.update x 2 true := by
  have hP : ∃ k, 2 ≤ k ∧ x k = false ∧ x (k + 1) = false := ⟨2, le_rfl, h2, h3⟩
  unfold zeckOdometer
  split
  · rename_i hP'
    have hfind : Nat.find hP' = 2 :=
      (Nat.find_eq_iff hP').2 ⟨⟨le_rfl, h2, h3⟩, fun n hn h => by omega⟩
    funext j
    rw [hfind]
    rcases hx with ⟨h0, h1, -⟩
    rcases Nat.lt_trichotomy j 2 with hj | rfl | hj
    · interval_cases j <;> simp [h0, h1]
    · simp
    · simp [Function.update, show ¬ j < 2 by omega, show j ≠ 2 by omega]
  · exact absurd hP ‹_›

/-- **The odometer on sequences without two consecutive zeros.** Let $T$ be the Zeckendorf
odometer and let $x = (x_k)_{k \in \mathbb{N}}$ be a digit sequence with $x_k \in \{0, 1\}$ such
that for every $k \ge 2$ we have $x_k = 1$ or $x_{k+1} = 1$. Then $T(x)$ is the zero sequence.

Among the Zeckendorf-adic integers, the sequences satisfying this hypothesis are the two whose
digits from index $2$ on alternate, $(10)^\infty$ and $(01)^\infty$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (last two cases of the definition of `T`). -/
public theorem zeckOdometer_of_forall {x : ℕ → Bool}
    (h : ∀ k, 2 ≤ k → x k = true ∨ x (k + 1) = true) : zeckOdometer x = fun _ => false := by
  unfold zeckOdometer
  split
  · rename_i hP
    obtain ⟨k, hk, h1, h2⟩ := hP
    rcases h k hk with h' | h' <;> simp_all
  · rfl

/-- **Truncated variation of the Zeckendorf digit sum.** Let $T$ be the Zeckendorf odometer
$x \mapsto x + 1$ on binary sequences, and write $x + r = T^r(x)$ for its $r$-th iterate. For
$r, k \in \mathbb{N}$ and a binary sequence $x = (x_i)_{i \in \mathbb{N}}$, let
$s_k(x) = x_2 + \dots + x_k$. The truncated variation is the integer
$\Delta_k^{(r)}(x) = s_k(x + r) - s_k(x)$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (definition of `s_k` and `Δ_k^{(r)}`). -/
public noncomputable def zeckAdicTruncVariation (r k : ℕ) (x : ℕ → Bool) : ℤ :=
  ∑ i ∈ Finset.Icc 2 k, ((zeckOdometer^[r] x i).toNat : ℤ) -
    ∑ i ∈ Finset.Icc 2 k, ((x i).toNat : ℤ)

/-- **The truncated variation vanishes for zero steps.** Let $T$ be the Zeckendorf odometer and,
for a binary sequence $x$, let $s_k(x) = x_2 + \dots + x_k$ and
$\Delta_k^{(r)}(x) = s_k(T^r(x)) - s_k(x)$. Then $\Delta_k^{(0)}(x) = 0$ for every
$k \in \mathbb{N}$ and every binary sequence $x$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ_k^{(r)}`). -/
public theorem zeckAdicTruncVariation_zero (k : ℕ) (x : ℕ → Bool) :
    zeckAdicTruncVariation 0 k x = 0 := by
  simp [zeckAdicTruncVariation]

/-- **The variation of the Zeckendorf digit sum.** For $r \in \mathbb{N}$ and a digit sequence
$x : \mathbb{N} \to \{0, 1\}$, let $\Delta_k^{(r)}(x)$ be the truncated variation of order $k$. If
the integer sequence $(\Delta_k^{(r)}(x))_k$ is eventually constant, the variation
$\Delta^{(r)}(x) = \lim_{k \to \infty} \Delta_k^{(r)}(x)$ is its eventual value; otherwise
$\Delta^{(r)}(x) = 0$.

The value $0$ is a junk value. The paper shows that the Zeckendorf-adic integers at which the
limit does not exist form a finite set.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (definition of `Δ^{(r)}` on `𝕏`). -/
public noncomputable def zeckAdicVariation (r : ℕ) (x : ℕ → Bool) : ℤ :=
  open Classical in
  if h : ∃ d, ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation r k x = d then h.choose else 0

/-- **The variation is the eventual value of the truncated variations.** Let $r \in \mathbb{N}$,
let $x$ be a binary sequence and let $d \in \mathbb{Z}$. If the truncated variation
$\Delta_k^{(r)}(x)$ equals $d$ for all sufficiently large $k$, then the variation
$\Delta^{(r)}(x)$ equals $d$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ^{(r)}`). -/
public theorem zeckAdicVariation_eq_of_eventually {r : ℕ} {x : ℕ → Bool} {d : ℤ}
    (h : ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation r k x = d) :
    zeckAdicVariation r x = d := by
  have hex : ∃ d, ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation r k x = d := ⟨d, h⟩
  unfold zeckAdicVariation
  split
  · rename_i hex'
    obtain ⟨k, hk1, hk2⟩ := (hex'.choose_spec.and h).exists
    rw [← hk1, hk2]
  · exact absurd hex ‹_›

/-- **The variation for $r = 0$ vanishes.** For every digit sequence $x : \mathbb{N} \to \{0, 1\}$,
not only for Zeckendorf-adic integers, the variation satisfies $\Delta^{(0)}(x) = 0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ^{(r)}`). -/
public theorem zeckAdicVariation_zero (x : ℕ → Bool) : zeckAdicVariation 0 x = 0 :=
  zeckAdicVariation_eq_of_eventually (Filter.Eventually.of_forall fun k =>
    zeckAdicTruncVariation_zero k x)

/-- **Adding $r$ without low digits leaves the low digits unchanged.** Write $F_j$ for the
Fibonacci numbers ($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in
the Zeckendorf representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two
consecutive), and let $r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones), and write $x + n = T^n(x)$ for the $n$-th
iterate of the Zeckendorf odometer $T$. Let $x \in \mathbb{X}$ and $\ell \ge 2$ with
$x_\ell = x_{\ell+1} = 0$, and let $r$ satisfy $r_j = 0$ for $2 \le j \le \ell + 1$. Then
$(x + r)_n = x_n$ for every $n$ with $2 \le n \le \ell - 2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 9 (`jis-2024-24.3.2-cor-9`). -/
public theorem_wanted zeckOdometer_iterate_low_digits {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hx0 : x ℓ = false) (hx1 : x (ℓ + 1) = false)
    (hr : ∀ j, 2 ≤ j → j ≤ ℓ + 1 → j ∉ Nat.zeckendorf r) :
    ∀ n, 2 ≤ n → n ≤ ℓ - 2 → zeckOdometer^[r] x n = x n

/-- **Adding a small $r$ leaves the high digits unchanged.** Write $F_j$ for the Fibonacci
numbers ($F_1 = F_2 = 1$). Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of
Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive ones), and write
$x + r = T^r(x)$ for the $r$-th iterate of the Zeckendorf odometer $T$. Let $x \in \mathbb{X}$,
$\ell \ge 2$ and $r < F_{\ell+1}$, and suppose that $x_{\ell+2} = x_{\ell+3} = 0$. Then
$(x + r)_k = x_k$ for every $k \ge \ell + 3$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 10 (`jis-2024-24.3.2-lem-10`). -/
public theorem_wanted zeckOdometer_iterate_high_digits {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hr : r < Nat.fib (ℓ + 1)) (hx2 : x (ℓ + 2) = false)
    (hx3 : x (ℓ + 3) = false) :
    ∀ k, ℓ + 3 ≤ k → zeckOdometer^[r] x k = x k

/-- **Adding $r$ across a window of four zero digits.** Write $F_j$ for the Fibonacci numbers
($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in the Zeckendorf
representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two consecutive), and let
$r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$
be the set of Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive
ones), and write $x + n = T^n(x)$ for the $n$-th iterate of the Zeckendorf odometer $T$. Let
$x \in \mathbb{X}$ and $\ell \ge 2$ with $x_{\ell+1} = x_{\ell+2} = x_{\ell+3} = x_{\ell+4} = 0$,
and let $r < F_{\ell+3}$ with $r_{\ell+2} = 1$. Then either $(x + r)_{\ell+k} = r_{\ell+k}$ for
$k = 1, 2, 3, 4$, or $(x + r)_{\ell+1} = 0$ and $(x + r)_{\ell+3} = 1$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 11 (`jis-2024-24.3.2-lem-11`). -/
public theorem_wanted zeckOdometer_iterate_block_digits {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hx0 : ∀ k, 1 ≤ k → k ≤ 4 → x (ℓ + k) = false)
    (hr : ℓ + 2 ∈ Nat.zeckendorf r) (hrlt : r < Nat.fib (ℓ + 3)) :
    (∀ k, 1 ≤ k → k ≤ 4 → zeckOdometer^[r] x (ℓ + k) = decide (ℓ + k ∈ Nat.zeckendorf r)) ∨
      (zeckOdometer^[r] x (ℓ + 1) = false ∧ zeckOdometer^[r] x (ℓ + 3) = true)

/-- **Stopping condition for a block of size one.** Write $F_j$ for the Fibonacci numbers
($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in the Zeckendorf
representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two consecutive), and let
$r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$
be the set of Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive
ones), and write $x + n = T^n(x)$ for the $n$-th iterate of the Zeckendorf odometer $T$. Let
$x \in \mathbb{X}$ and $\ell \ge 2$ with $x_i = 0$ for $\ell \le i \le \ell + 5$, and let $r$
satisfy $r_{\ell+1} = r_{\ell+5} = 0$ and $r_{\ell+3} = 1$. Let
$\tilde r = \sum_{j \in Z(r),\, j \le \ell} F_j$ be the part of $r$ of index at most $\ell$. Then
$(x + \tilde r + F_{\ell+3})_k = (x + \tilde r)_k = x_k$ for every $k \ge \ell + 4$, and
$(x + r)_k = (x + \tilde r + F_{\ell+3})_k = (x + \tilde r)_k$ for every $k$ with
$2 \le k \le \ell + 2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 12 (`jis-2024-24.3.2-cor-12`). -/
public theorem_wanted zeckOdometer_stopping_block_one {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hx0 : ∀ i, ℓ ≤ i → i ≤ ℓ + 5 → x i = false)
    (hr1 : ℓ + 1 ∉ Nat.zeckendorf r) (hr5 : ℓ + 5 ∉ Nat.zeckendorf r)
    (hr3 : ℓ + 3 ∈ Nat.zeckendorf r) :
    let rt := (((Nat.zeckendorf r).filter (· ≤ ℓ)).map Nat.fib).sum
    (∀ k, ℓ + 4 ≤ k → zeckOdometer^[rt + Nat.fib (ℓ + 3)] x k = zeckOdometer^[rt] x k ∧
        zeckOdometer^[rt] x k = x k) ∧
      ∀ k, 2 ≤ k → k ≤ ℓ + 2 → zeckOdometer^[r] x k = zeckOdometer^[rt + Nat.fib (ℓ + 3)] x k ∧
        zeckOdometer^[rt + Nat.fib (ℓ + 3)] x k = zeckOdometer^[rt] x k

/-- **Stopping condition for a block of size $m + 2$.** Write $F_j$ for the Fibonacci numbers
($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in the Zeckendorf
representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two consecutive), and let
$r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$
be the set of Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive
ones), and write $x + n = T^n(x)$ for the $n$-th iterate of the Zeckendorf odometer $T$. Let
$x \in \mathbb{X}$, $\ell \ge 2$ and $m \in \mathbb{N}$ with $x_i = 0$ for
$i \in \{\ell, \ell+1, \ell+2, \ell+3, \ell+2m+4, \ell+2m+5, \ell+2m+6, \ell+2m+7\}$, and let
$r$ satisfy $r_{\ell+1} = r_{\ell+2m+7} = 0$ and $r_{\ell+2i+3} = 1$ for $i = 0, \dots, m+1$.
Let $\tilde r = \sum_{j \in Z(r),\, j \le \ell} F_j$ be the part of $r$ of index at most $\ell$,
and let $S = \sum_{i=0}^{m+1} F_{\ell+2i+3}$. Then
$(x + \tilde r + S)_k = (x + \tilde r)_k = x_k$ for every $k \ge \ell + 2m + 7$, and
$(x + r)_k = (x + \tilde r + S)_k$ for every $k$ with $2 \le k \le \ell + 2m + 2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 14 (`jis-2024-24.3.2-cor-14`). -/
public theorem_wanted zeckOdometer_stopping_block {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ m r : ℕ} (hℓ : 2 ≤ ℓ)
    (hx0 : ∀ i ∈ ({ℓ, ℓ + 1, ℓ + 2, ℓ + 3, ℓ + 2 * m + 4, ℓ + 2 * m + 5, ℓ + 2 * m + 6,
      ℓ + 2 * m + 7} : Finset ℕ), x i = false)
    (hr1 : ℓ + 1 ∉ Nat.zeckendorf r) (hr7 : ℓ + 2 * m + 7 ∉ Nat.zeckendorf r)
    (hrb : ∀ i ≤ m + 1, ℓ + 2 * i + 3 ∈ Nat.zeckendorf r) :
    let rt := (((Nat.zeckendorf r).filter (· ≤ ℓ)).map Nat.fib).sum
    let S := ∑ i ∈ Finset.range (m + 2), Nat.fib (ℓ + 2 * i + 3)
    (∀ k, ℓ + 2 * m + 7 ≤ k → zeckOdometer^[rt + S] x k = zeckOdometer^[rt] x k ∧
        zeckOdometer^[rt] x k = x k) ∧
      ∀ k, 2 ≤ k → k ≤ ℓ + 2 * m + 2 → zeckOdometer^[r] x k = zeckOdometer^[rt + S] x k

open MeasureTheory

/-- **Unique ergodicity of the Zeckendorf odometer.** Let $\mathbb{X}$ be the set of
Zeckendorf-adic integers, a subset of the space $\{0,1\}^{\mathbb{N}}$ of digit sequences with its
product $\sigma$-algebra, and let $T$ be the Zeckendorf odometer on $\{0,1\}^{\mathbb{N}}$. There
is exactly one probability measure $\mu$ on $\{0,1\}^{\mathbb{N}}$ such that
$\mu(\{0,1\}^{\mathbb{N}} \setminus \mathbb{X}) = 0$ and $T$ preserves $\mu$, that is, $T$ is
measurable and $\mu(T^{-1}(A)) = \mu(A)$ for every measurable set $A$.

In other words, $(\mathbb{X}, T)$ is uniquely ergodic.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 15 (`jis-2024-24.3.2-prop-15`), first part. -/
public theorem_wanted zeckOdometer_uniquely_ergodic :
    ∃! μ : Measure (ℕ → Bool),
      IsProbabilityMeasure μ ∧ μ zeckAdicᶜ = 0 ∧ MeasurePreserving zeckOdometer μ μ

/-- **Mass of a cylinder under the invariant measure.** Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones), let $T$ be the Zeckendorf odometer, and let
$\varphi$ be the golden ratio. Let $\mu$ be a probability measure on $\{0,1\}^{\mathbb{N}}$ with
$\mu(\mathbb{X}^c) = 0$ that is preserved by $T$. Let $\ell \ge 2$ and $y \in \mathbb{X}$, and let
$C = \{x : x_i = y_i \text{ for } 2 \le i \le \ell\}$ be the cylinder of the digits
$y_\ell \cdots y_2$. Then $\mu(C) = 1/\varphi^\ell$ if $y_\ell = 1$, and
$\mu(C) = 1/\varphi^{\ell - 1}$ if $y_\ell = 0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 15 (`jis-2024-24.3.2-prop-15`), cylinder formula. -/
public theorem_wanted zeckOdometer_invariant_measure_cylinder (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {y : ℕ → Bool} (hy : y ∈ zeckAdic) :
    μ {x | ∀ i, 2 ≤ i → i ≤ ℓ → x i = y i} =
      ENNReal.ofReal (1 / Real.goldenRatio ^ (if y ℓ = true then ℓ else ℓ - 1))

/-- **Renewal property of the invariant measure.** Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones) and let $T$ be the Zeckendorf odometer. Let
$\mu$ be a probability measure on $\{0,1\}^{\mathbb{N}}$ with $\mu(\mathbb{X}^c) = 0$ that is
preserved by $T$. Let $k \ge 2$, $\ell_0 \in \mathbb{N}$ and $y, z \in \mathbb{X}$, and let
$C = \{x : x_i = z_i \text{ for } 2 \le i \le \ell_0\}$. Let
$E_0 = \{x : x_{k+1} = 0 \text{ and } x_i = y_i \text{ for } 2 \le i \le k\}$ and
$E_1 = \{x : x_{k+1} = 1 \text{ and } x_i = y_i \text{ for } 2 \le i \le k\}$. Then
$\mu(\{x : x_{i+k} = z_i \text{ for } 2 \le i \le \ell_0\} \mid E_0) = \mu(C)$, and if
$y_k = 0$, then also
$\mu(\{x : x_{i+k+1} = z_i \text{ for } 2 \le i \le \ell_0\} \mid E_1) = \mu(C)$.

With the shift $(\sigma x)_i = x_{i+1}$, the two conditioned events are $\sigma^k x \in C$ and
$\sigma^{k+1} x \in C$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 16 (`jis-2024-24.3.2-prop-16`). -/
public theorem_wanted zeckOdometer_invariant_measure_renewal (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {k ℓ₀ : ℕ} (hk : 2 ≤ k) {y z : ℕ → Bool} (hy : y ∈ zeckAdic) (hz : z ∈ zeckAdic) :
    ProbabilityTheory.cond μ {x | x (k + 1) = false ∧ ∀ i, 2 ≤ i → i ≤ k → x i = y i}
        {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x (i + k) = z i} =
      μ {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x i = z i} ∧
    (y k = false →
      ProbabilityTheory.cond μ {x | x (k + 1) = true ∧ ∀ i, 2 ≤ i → i ≤ k → x i = y i}
          {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x (i + (k + 1)) = z i} =
        μ {x | ∀ i, 2 ≤ i → i ≤ ℓ₀ → x i = z i})

/-- **Bradley's inequality between the $\alpha$- and $\varphi$-mixing coefficients.** Let
$(X_j)_{j \ge 1}$ be random variables on a probability space $(\Omega, \mathbb{P})$ with values in
a measurable space, and let $k \ge 1$. Suppose a real number $c$ bounds every term defining the
$\varphi$-mixing coefficient $\varphi(k)$: for every $p \ge 1$, every event
$A \in \sigma(X_j : 1 \le j \le p)$ with $\mathbb{P}(A) > 0$ and every event
$B \in \sigma(X_j : j \ge k + p)$, $|\mathbb{P}(B \mid A) - \mathbb{P}(B)| \le c$. Then $c/2$
bounds every term defining the $\alpha$-mixing coefficient $\alpha(k)$: for every $p \ge 1$,
every event $A \in \sigma(X_j : 1 \le j \le p)$ and every event $B \in \sigma(X_j : j \ge k + p)$,
$|\mathbb{P}(A \cap B) - \mathbb{P}(A)\mathbb{P}(B)| \le c/2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 18 (Bradley) (`jis-2024-24.3.2-prop-18`). -/
public theorem_wanted alpha_mixing_le_half_phi_mixing {Ω β : Type*} [MeasurableSpace Ω]
    [mβ : MeasurableSpace β] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → β)
    (hX : ∀ j, Measurable (X j)) {k : ℕ} (hk : 1 ≤ k) (c : ℝ)
    (hc : ∀ p, 1 ≤ p → ∀ A B : Set Ω,
      MeasurableSet[⨆ j ∈ Finset.Icc 1 p, mβ.comap (X j)] A →
      MeasurableSet[⨆ (j : ℕ) (_ : k + p ≤ j), mβ.comap (X j)] B → μ A ≠ 0 →
      |(ProbabilityTheory.cond μ A B).toReal - (μ B).toReal| ≤ c)
    {p : ℕ} (hp : 1 ≤ p) {A B : Set Ω}
    (hA : MeasurableSet[⨆ j ∈ Finset.Icc 1 p, mβ.comap (X j)] A)
    (hB : MeasurableSet[⨆ (j : ℕ) (_ : k + p ≤ j), mβ.comap (X j)] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ c / 2

/-- **Mixing of the Zeckendorf digits under the invariant measure.** Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones), let $T$ be the Zeckendorf odometer, and let
$\varphi$ be the golden ratio. Let $\mu$ be a probability measure on $\{0,1\}^{\mathbb{N}}$ with
$\mu(\mathbb{X}^c) = 0$ that is preserved by $T$, and let $k, p \ge 1$. Let $A$ be a set that is
measurable for the $\sigma$-algebra generated by the digits $x_2, \dots, x_{p+1}$, with
$\mu(A) > 0$, and let $B$ be a set that is measurable for the $\sigma$-algebra generated by the
digits $x_j$ with $j \ge k + p + 1$. Then $|\mu(B \mid A) - \mu(B)| \le 2/\varphi^{2k}$.

For the coordinate process $X_j = x_{j+1}$ ($j \ge 1$) this bounds every term in the supremum
that defines the $\phi$-mixing coefficient $\phi(k)$, so $\phi(k) \le 2/\varphi^{2k}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 19 (`jis-2024-24.3.2-prop-19`). -/
public theorem_wanted zeckOdometer_invariant_measure_phi_mixing (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {k p : ℕ} (hk : 1 ≤ k) (hp : 1 ≤ p) {A B : Set (ℕ → Bool)}
    (hA : MeasurableSet[⨆ j ∈ Finset.Icc 1 p,
      MeasurableSpace.comap (fun x : ℕ → Bool => x (j + 1)) inferInstance] A)
    (hB : MeasurableSet[⨆ (j : ℕ) (_ : k + p ≤ j),
      MeasurableSpace.comap (fun x : ℕ → Bool => x (j + 1)) inferInstance] B)
    (hA0 : μ A ≠ 0) :
    |(ProbabilityTheory.cond μ A B).toReal - (μ B).toReal| ≤ 2 / Real.goldenRatio ^ (2 * k)

/-- **The Zeckendorf Markov chain.** Let $\varphi$ be the golden ratio, and let $\psi(0, t) = 1$
if $t < 1/\varphi^2$, $\psi(0, t) = 0$ otherwise, and $\psi(1, t) = 0$. For a real sequence
$(u_n)_{n \ge 0}$, written $u_n = U_{n+2}$, the chain $(y_j)_{j \in \mathbb{N}}$ is the sequence in
$\{0, 1\}$ with $y_0 = y_1 = 0$ and $y_j = \psi(y_{j-1}, U_j)$ for $j \ge 2$; that is,
$y_{n+2} = 1$ exactly when $y_{n+1} = 0$ and $u_n < 1/\varphi^2$.

The paper starts the chain at $y_1 = 0$; the extra digit $y_0 = 0$ matches the indexing of
Zeckendorf-adic digit sequences.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.3 (the maps `ψ` and `(y_j)`). -/
public noncomputable def zeckMarkovPath (u : ℕ → ℝ) : ℕ → Bool
  | 0 => false
  | 1 => false
  | j + 2 => !zeckMarkovPath u (j + 1) && decide (u j < 1 / Real.goldenRatio ^ 2)

/-- **The first step of the Zeckendorf Markov chain.** For every real sequence $(u_n)_{n \ge 0}$,
the digit $y_2$ of the chain driven by $(u_n)$ is $1$ exactly when $u_0 < 1/\varphi^2$, where
$\varphi$ is the golden ratio. In the paper's notation, where $u_n = U_{n+2}$, this says that
$y_2 = 1$ if and only if $U_2 < 1/\varphi^2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.3 (characteristic lemma for `(y_j)`). -/
public theorem zeckMarkovPath_two (u : ℕ → ℝ) :
    zeckMarkovPath u 2 = decide (u 0 < 1 / Real.goldenRatio ^ 2) := by
  simp [zeckMarkovPath]

/-- **After a one, the Zeckendorf Markov chain emits a zero.** For every real sequence
$(u_n)_{n \ge 0}$ and every $j \ge 1$, if the digit $y_j$ of the chain driven by $(u_n)$ is $1$,
then $y_{j+1} = 0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.3 (characteristic lemma: `ψ(1, t) = 0`). -/
public theorem zeckMarkovPath_succ_of_true (u : ℕ → ℝ) {j : ℕ}
    (h : zeckMarkovPath u (j + 1) = true) : zeckMarkovPath u (j + 2) = false := by
  simp [zeckMarkovPath, h]

/-- **The Zeckendorf Markov chain has the invariant law.** Let $\mathbb{X}$ be the set of
Zeckendorf-adic integers: the digit sequences $x \in \{0, 1\}^{\mathbb{N}}$ with $x_0 = x_1 = 0$
and no two consecutive digits equal to $1$. Let $\mu$ be a probability measure on
$\{0, 1\}^{\mathbb{N}}$ with $\mu(\mathbb{X}^c) = 0$ that is preserved by the odometer $T$. Let
$(\Omega, \nu)$ be a probability space and let $(U_n)_{n \ge 0}$ be independent measurable real
random variables on $\Omega$, each uniformly distributed on $[0, 1]$. Then the law under $\nu$ of
the digit sequence $\omega \mapsto (y_j(\omega))_{j \in \mathbb{N}}$ of the Zeckendorf Markov chain
driven by $(U_n(\omega))_{n \ge 0}$ is $\mu$.

The paper indexes the uniform variables from $2$, writing $U_{n+2}$ for the $U_n$ here; the
measure $\mu$ is the paper's $\mathbb{P}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 20 (`jis-2024-24.3.2-lem-20`). -/
public theorem_wanted zeckMarkovPath_law (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ) {Ω : Type*}
    [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (U : ℕ → Ω → ℝ)
    (hU : ∀ j, Measurable (U j)) (hind : ProbabilityTheory.iIndepFun U ν)
    (hunif : ∀ j, ν.map (U j) = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    ν.map (fun ω => zeckMarkovPath fun j => U j ω) = μ

/-- **Conditional probability that prescribed later digits vanish.** Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones), let $T$ be the Zeckendorf odometer, and let
$\varphi$ be the golden ratio. Let $\mu$ be a probability measure on $\{0,1\}^{\mathbb{N}}$ with
$\mu(\mathbb{X}^c) = 0$ that is preserved by $T$. Let $\ell \in \mathbb{N}$ and let
$k_0, \dots, k_\ell$ be natural numbers with $2 \le k_0 < k_1 < \dots < k_\ell$. Let
$A \subseteq \{0,1\}^{\mathbb{N}}$ be a set such that whether $x \in A$ depends only on the digits
$x_2, \dots, x_{k_0}$, with $x_{k_0} = 0$ for every $x \in A$ and $\mu(A) > 0$. Then the event
$E = \{x : x_{k_i} = 0 \text{ for } 1 \le i \le \ell\}$ has conditional probability
$1/\varphi^\ell \le \mu(E \mid A) \le (2/\varphi^2)^\ell$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 21 (`jis-2024-24.3.2-prop-21`). -/
public theorem_wanted zeckOdometer_invariant_measure_cond_zeros (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {ℓ : ℕ} {k : ℕ → ℕ} (hk0 : 2 ≤ k 0) (hk : ∀ i < ℓ, k i < k (i + 1))
    {A : Set (ℕ → Bool)} (hA : ∀ x y, (∀ i, 2 ≤ i → i ≤ k 0 → x i = y i) → x ∈ A → y ∈ A)
    (hA0 : ∀ x ∈ A, x (k 0) = false) (hApos : μ A ≠ 0) :
    ENNReal.ofReal (1 / Real.goldenRatio ^ ℓ) ≤
        ProbabilityTheory.cond μ A {x | ∀ i, 1 ≤ i → i ≤ ℓ → x (k i) = false} ∧
      ProbabilityTheory.cond μ A {x | ∀ i, 1 ≤ i → i ≤ ℓ → x (k i) = false} ≤
        ENNReal.ofReal ((2 / Real.goldenRatio ^ 2) ^ ℓ)

/-- **Ergodic averages of the variation for functions of polynomial growth.** Let $\mathbb{X}$ be
the set of Zeckendorf-adic integers, $T$ the Zeckendorf odometer, and $\mathbb{P}$ a
$T$-invariant probability measure on binary sequences with $\mathbb{P}(\mathbb{X}^c) = 0$. Let
$s(n)$ be the number of terms in the Zeckendorf representation of $n \in \mathbb{N}$, let
$r \ge 1$, and let $\Delta^{(r)}$ and $\Delta_k^{(r)}$ be the variation and the truncated
variation on binary sequences. Let $f : \mathbb{Z} \to \mathbb{C}$ and let $\alpha \ge 1$ and
$C > 0$ be reals with $|f(n)| \le C|n|^\alpha + |f(0)|$ for all $n \in \mathbb{Z}$. Then
$f \circ \Delta^{(r)}$ is $\mathbb{P}$-integrable,
$$\frac{1}{N} \sum_{n=0}^{N-1} f\bigl(s(n + r) - s(n)\bigr)
\to \int f \circ \Delta^{(r)}\,d\mathbb{P}$$
as $N \to \infty$, and
$\int f \circ \Delta_k^{(r)}\,d\mathbb{P} \to \int f \circ \Delta^{(r)}\,d\mathbb{P}$
as $k \to \infty$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 23 (`jis-2024-24.3.2-prop-23`). -/
public theorem_wanted zeckAdicVariation_ergodic_average_of_growth (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {r : ℕ} (hr : 1 ≤ r) (f : ℤ → ℂ) {α C : ℝ} (hα : 1 ≤ α) (hC : 0 < C)
    (hf : ∀ n : ℤ, ‖f n‖ ≤ C * |(n : ℝ)| ^ α + ‖f 0‖) :
    Integrable (fun x => f (zeckAdicVariation r x)) μ ∧
      Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          f (((Nat.zeckendorf (n + r)).length : ℤ) - (Nat.zeckendorf n).length))
        Filter.atTop (nhds (∫ x, f (zeckAdicVariation r x) ∂μ)) ∧
      Filter.Tendsto (fun k => ∫ x, f (zeckAdicTruncVariation r k x) ∂μ) Filter.atTop
        (nhds (∫ x, f (zeckAdicVariation r x) ∂μ))

/-- **Counting values of the variation against the invariant measure.** Let $\mathbb{X}$ be the
set of Zeckendorf-adic integers, $T$ the Zeckendorf odometer, and $\mathbb{P}$ a $T$-invariant
probability measure on binary sequences with $\mathbb{P}(\mathbb{X}^c) = 0$. Let $s(n)$ be the
number of terms in the Zeckendorf representation of $n \in \mathbb{N}$, let $\iota(n)$ be the
Zeckendorf digit sequence of $n$, let $\Delta^{(r)}$ and $\Delta_k^{(r)}$ be the variation and the
truncated variation on binary sequences, and let $\varphi$ be the golden ratio. Then for all
integers $r \ge 1$, $N \ge 1$, $k \ge 2$ and $d, d' \in \mathbb{Z}$,
$$\frac{1}{N}\,\#\{n < N : s(n + r) - s(n) = d,\ \Delta_k^{(r)}(\iota(n)) = d'\}
\le r\varphi^3\,\mathbb{P}(\Delta^{(r)} = d,\ \Delta_k^{(r)} = d')$$
and
$$\frac{1}{N}\,\#\{n < N : s(n + r) - s(n) = d\} \le r\varphi^3\,\mathbb{P}(\Delta^{(r)} = d).$$

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 26 (`jis-2024-24.3.2-lem-26`). -/
public theorem_wanted zeckAdicVariation_count_le (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {r N k : ℕ} (hr : 1 ≤ r) (hN : 1 ≤ N) (hk : 2 ≤ k) (d d' : ℤ) :
    ((({n ∈ Finset.range N |
        ((Nat.zeckendorf (n + r)).length : ℤ) - (Nat.zeckendorf n).length = d ∧
          zeckAdicTruncVariation r k (zeckAdicOfNat n) = d'}.card : ℕ) : ℝ) / N ≤
        r * Real.goldenRatio ^ 3 *
          (μ {x | zeckAdicVariation r x = d ∧ zeckAdicTruncVariation r k x = d'}).toReal) ∧
      ((({n ∈ Finset.range N |
        ((Nat.zeckendorf (n + r)).length : ℤ) - (Nat.zeckendorf n).length = d}.card : ℕ) : ℝ) /
          N ≤ r * Real.goldenRatio ^ 3 * (μ {x | zeckAdicVariation r x = d}).toReal)

/-- **When the variation $\Delta^{(1)}$ exists.** Let $x$ be a Zeckendorf-adic integer with digits
$x_k$, and let $\Delta_k^{(1)}(x)$ be its truncated variation of order $k$ for $r = 1$. The
integer sequence $(\Delta_k^{(1)}(x))_k$ is eventually constant (equivalently, the variation
$\Delta^{(1)}(x) = \lim_{k \to \infty} \Delta_k^{(1)}(x)$ exists) if and only if there is
$d \ge 0$ such that either $x_{2d+3} = x_{2d+2} = 0$ and $x_{2i+1} = 1$, $x_{2i} = 0$ for
$1 \le i \le d$ (the cylinder $C_{00(10)^d}$), or $x_{2d+4} = x_{2d+3} = 0$, $x_{2d+2} = 1$ and
$x_{2i+1} = 0$, $x_{2i} = 1$ for $1 \le i \le d$ (the cylinder $C_{001(01)^d}$).

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 27 (`jis-2024-24.3.2-lem-27`), first part. -/
public theorem_wanted zeckAdicVariation_one_exists_iff {x : ℕ → Bool} (hx : x ∈ zeckAdic) :
    (∃ d, ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation 1 k x = d) ↔
      ∃ d : ℕ,
        (x (2 * d + 3) = false ∧ x (2 * d + 2) = false ∧
          ∀ i, 1 ≤ i → i ≤ d → x (2 * i + 1) = true ∧ x (2 * i) = false) ∨
        (x (2 * d + 4) = false ∧ x (2 * d + 3) = false ∧ x (2 * d + 2) = true ∧
          ∀ i, 1 ≤ i → i ≤ d → x (2 * i + 1) = false ∧ x (2 * i) = true)

/-- **The variation $\Delta^{(1)}$ on the cylinder $C_{00(10)^d}$.** Let $d \ge 0$ and let $x$ be a
Zeckendorf-adic integer in the cylinder $C_{00(10)^d}$, that is, one whose digits satisfy
$x_{2d+3} = x_{2d+2} = 0$ and $x_{2i+1} = 1$, $x_{2i} = 0$ for $1 \le i \le d$. Write
$\Delta_k^{(1)}(x)$ for the truncated variation of order $k$ and $\Delta^{(1)}(x)$ for the
variation, both for $r = 1$. Then $\Delta^{(1)}(x) = 1 - d$, and for every $k \ge 2$:
$\Delta_k^{(1)}(x) = (2 - k)/2$ if $k$ is even and $k \le 2d$; $\Delta_k^{(1)}(x) = (1 - k)/2$ if
$k$ is odd and $k \le 2d + 1$; and $\Delta_k^{(1)}(x) = 1 - d$ if $k \ge 2d + 2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 27 (`jis-2024-24.3.2-lem-27`), first cylinder. -/
public theorem_wanted zeckAdicVariation_one_of_mem_cylinder_even {x : ℕ → Bool}
    (hx : x ∈ zeckAdic) {d : ℕ} (h3 : x (2 * d + 3) = false) (h2 : x (2 * d + 2) = false)
    (hb : ∀ i, 1 ≤ i → i ≤ d → x (2 * i + 1) = true ∧ x (2 * i) = false) :
    zeckAdicVariation 1 x = 1 - d ∧ ∀ k, 2 ≤ k →
      (k % 2 = 0 → k ≤ 2 * d → 2 * zeckAdicTruncVariation 1 k x = 2 - k) ∧
      (k % 2 = 1 → k ≤ 2 * d + 1 → 2 * zeckAdicTruncVariation 1 k x = 1 - k) ∧
      (2 * d + 2 ≤ k → zeckAdicTruncVariation 1 k x = 1 - d)

/-- **The variation $\Delta^{(1)}$ on the cylinder $C_{001(01)^d}$.** Let $d \ge 0$ and let $x$ be a
Zeckendorf-adic integer in the cylinder $C_{001(01)^d}$, that is, one whose digits satisfy
$x_{2d+4} = x_{2d+3} = 0$, $x_{2d+2} = 1$ and $x_{2i+1} = 0$, $x_{2i} = 1$ for $1 \le i \le d$.
Write $\Delta_k^{(1)}(x)$ for the truncated variation of order $k$ and $\Delta^{(1)}(x)$ for the
variation, both for $r = 1$. Then $\Delta^{(1)}(x) = -d$, and for every $k \ge 2$:
$\Delta_k^{(1)}(x) = -k/2$ if $k$ is even and $k \le 2d + 2$; $\Delta_k^{(1)}(x) = (1 - k)/2$ if
$k$ is odd and $k \le 2d + 1$; $\Delta_k^{(1)}(x) = (3 - k)/2$ if $k = 2d + 3$; and
$\Delta_k^{(1)}(x) = -d$ if $k \ge 2d + 4$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 27 (`jis-2024-24.3.2-lem-27`), second cylinder. -/
public theorem_wanted zeckAdicVariation_one_of_mem_cylinder_odd {x : ℕ → Bool}
    (hx : x ∈ zeckAdic) {d : ℕ} (h4 : x (2 * d + 4) = false) (h3 : x (2 * d + 3) = false)
    (h2 : x (2 * d + 2) = true)
    (hb : ∀ i, 1 ≤ i → i ≤ d → x (2 * i + 1) = false ∧ x (2 * i) = true) :
    zeckAdicVariation 1 x = -d ∧ ∀ k, 2 ≤ k →
      (k % 2 = 0 → k ≤ 2 * d + 2 → 2 * zeckAdicTruncVariation 1 k x = -k) ∧
      (k % 2 = 1 → k ≤ 2 * d + 1 → 2 * zeckAdicTruncVariation 1 k x = 1 - k) ∧
      (k = 2 * d + 3 → 2 * zeckAdicTruncVariation 1 k x = 3 - k) ∧
      (2 * d + 4 ≤ k → zeckAdicTruncVariation 1 k x = -d)

/-- **Ergodic theorem for the Zeckendorf digit-sum variation.** Let $\mu$ be a probability
measure on the digit sequences $x : \mathbb{N} \to \{0, 1\}$ that gives the complement of the
Zeckendorf-adic integers $\mathbb{X}$ measure zero and is preserved by the odometer $T$. Let
$r \ge 1$ and let $f : \mathbb{Z} \to \mathbb{C}$ be such that $f \circ \Delta^{(r)}$ is
$\mu$-integrable, where $\Delta^{(r)}$ is the variation on $\mathbb{X}$. Write $s(n)$ for the
number of terms in the Zeckendorf representation of $n$. Then
$$\frac{1}{N} \sum_{n=0}^{N-1} f\bigl(s(n + r) - s(n)\bigr) \to \int f(\Delta^{(r)}(x))\, d\mu(x)$$
as $N \to \infty$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 28 (`jis-2024-24.3.2-prop-28`). -/
public theorem_wanted zeckAdicVariation_ergodic_average (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {r : ℕ} (hr : 1 ≤ r) (f : ℤ → ℂ) (hf : Integrable (fun x => f (zeckAdicVariation r x)) μ) :
    Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        f (((Nat.zeckendorf (n + r)).length : ℤ) - (Nat.zeckendorf n).length))
      Filter.atTop (nhds (∫ x, f (zeckAdicVariation r x) ∂μ))


/-! ### Rokhlin towers and new-information zones -/

/-- **Prefix value of a digit sequence.** For $k \in \mathbb{N}$ and a binary sequence
$x = (x_i)_{i \in \mathbb{N}}$, the prefix value of order $k$ is the natural number
$v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, where $F_i$ is the $i$-th Fibonacci number
($F_1 = F_2 = 1$). It is the value of the block $x_{k+1} \cdots x_2$ of the $k$ rightmost digits
of $x$, the name of the cylinder of order $k$ that contains $x$.

In the paper the levels of the two Rokhlin towers of order $k$ are level sets of $v_k$: the
large tower has levels $\{v_k = j - 1\}$ for $1 \le j \le F_{k+1}$, and the small tower has
levels $\{v_k = F_{k+1} + j - 1\}$ for $1 \le j \le F_k$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.1 (cylinders of order `k` and the two towers). -/
public def zeckAdicPrefixValue (k : ℕ) (x : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.Icc 2 (k + 1), if x i = true then Nat.fib i else 0

/-- **Prefix value of order one.** For every binary sequence $x = (x_i)_{i \in \mathbb{N}}$, the
prefix value of order $1$ is $v_1(x) = x_2 F_2$, where $F_2 = 1$ is the second Fibonacci number.
It equals $x_2$: it is $1$ if $x_2 = 1$ and $0$ otherwise.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.1 (characteristic lemma: towers of order `1`). -/
public theorem zeckAdicPrefixValue_one (x : ℕ → Bool) :
    zeckAdicPrefixValue 1 x = if x 2 = true then 1 else 0 := by
  simp [zeckAdicPrefixValue]

/-- **The sets $\mathrm{CST}_k$.** Fix $r, k \in \mathbb{N}$. For a digit sequence
$x = (x_i)_{i \in \mathbb{N}}$ in $\{0, 1\}$ let $v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, where $F_i$
is the $i$-th Fibonacci number ($F_1 = F_2 = 1$). The set $\mathrm{CST}_k$ (for the shift $r$)
consists of the digit sequences $x$ such that either $v_k(x) + r < F_{k+1}$, or both
$F_{k+1} \le v_k(x)$ and $v_k(x) + r < F_{k+2}$.

In terms of the Rokhlin towers of order $k$, this is the union of the levels of the large and the
small tower except the $r$ highest levels of each tower.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (definition of `CST_k`). -/
public def zeckCST (r k : ℕ) : Set (ℕ → Bool) :=
  {x | zeckAdicPrefixValue k x + r < Nat.fib (k + 1) ∨
    (Nat.fib (k + 1) ≤ zeckAdicPrefixValue k x ∧ zeckAdicPrefixValue k x + r < Nat.fib (k + 2))}

/-- **$\mathrm{CST}_1$ is empty for every positive shift.** For every $r \ge 1$, the set
$\mathrm{CST}_1$ for the shift $r$ is empty.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 ("We observe `CST_1 = ∅`"). -/
public theorem zeckCST_one {r : ℕ} (hr : 1 ≤ r) : zeckCST r 1 = ∅ := by
  ext x
  have h2 : Nat.fib (1 + 1) = 1 := rfl
  have h3 : Nat.fib (1 + 2) = 2 := rfl
  simp only [zeckCST, Set.mem_empty_iff_false, iff_false]
  show ¬(_ ∨ _)
  rw [h2, h3]
  omega

/-- **New-information zone.** Let $F_1 = F_2 = 1, F_3 = 2, \dots$ be the Fibonacci numbers, and
for a digit sequence $x = (x_i)_{i \ge 0}$ with $x_i \in \{0, 1\}$ and $j \in \mathbb{N}$ let
$v_j(x) = \sum_{i=2}^{j+1} x_i F_i$. For $r \in \mathbb{N}$ let $\mathrm{CST}_j$ be the
set of digit sequences $x$ with $v_j(x) + r < F_{j+1}$, or with $F_{j+1} \le v_j(x)$ and
$v_j(x) + r < F_{j+2}$. For $k \in \mathbb{N}$, the new-information zone of order $k$
for $r$ is $\mathrm{NIZ}_k = \mathrm{CST}_k \setminus \mathrm{CST}_{k-1}$, where $k - 1$ is read
as $0$ when $k = 0$ (so $\mathrm{NIZ}_0 = \emptyset$).

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (definition of `NIZ_k`). -/
public def zeckNIZ (r k : ℕ) : Set (ℕ → Bool) := zeckCST r k \ zeckCST r (k - 1)

/-- **New-information zones lie in $\mathrm{CST}_k$.** For all $r, k \in \mathbb{N}$, the
new-information zone $\mathrm{NIZ}_k$ of order $k$ for the shift $r$ is contained in the set
$\mathrm{CST}_k$ for the shift $r$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (characteristic lemma for `NIZ_k`). -/
public theorem zeckNIZ_subset_zeckCST (r k : ℕ) : zeckNIZ r k ⊆ zeckCST r k :=
  fun _ hx => hx.1

/-- **The new-information zones as tower levels.** Let $\ell \ge 2$ and let $r$ satisfy
$F_\ell \le r < F_{\ell+1}$, where $F_1 = F_2 = 1, F_3 = 2, \dots$ are the Fibonacci numbers. For
a Zeckendorf-adic integer $x = (x_i)_{i \ge 2}$ let $v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, and let
$\mathrm{NIZ}_k$ be the new-information zone of order $k$ for $r$. Then for every
Zeckendorf-adic integer $x$: $x \notin \mathrm{NIZ}_k$ whenever $2 \le k \le \ell - 1$;
$x \in \mathrm{NIZ}_\ell$ if and only if $v_\ell(x) + r < F_{\ell+1}$;
$x \in \mathrm{NIZ}_{\ell+1}$ if and only if $F_{\ell+1} \le v_{\ell+1}(x) + r < F_{\ell+2}$; and
for every $k > \ell + 1$, $x \in \mathrm{NIZ}_k$ if and only if $F_k \le v_k(x) + r$ and
$v_k(x) < F_k$.

Since level $j$ of the large tower of order $k$ is $\{v_k = j - 1\}$, this says that
$\mathrm{NIZ}_\ell$ consists of the first $F_{\ell+1} - r$ levels of the large tower of order
$\ell$, $\mathrm{NIZ}_{\ell+1}$ of the levels $F_{\ell+1} - r + 1, \dots, F_{\ell+2} - r$ of the
large tower of order $\ell + 1$, and $\mathrm{NIZ}_k$ for $k > \ell + 1$ of the levels
$F_k - r + 1, \dots, F_k$ of the large tower of order $k$ (as subsets of the Zeckendorf-adic
integers).

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 29 (`jis-2024-24.3.2-prop-29`). -/
public theorem_wanted zeckNIZ_levels {r ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hr : Nat.fib ℓ ≤ r)
    (hr' : r < Nat.fib (ℓ + 1)) {x : ℕ → Bool} (hx : x ∈ zeckAdic) :
    (∀ k, 2 ≤ k → k ≤ ℓ - 1 → x ∉ zeckNIZ r k) ∧
    (x ∈ zeckNIZ r ℓ ↔ zeckAdicPrefixValue ℓ x + r < Nat.fib (ℓ + 1)) ∧
    (x ∈ zeckNIZ r (ℓ + 1) ↔ Nat.fib (ℓ + 1) ≤ zeckAdicPrefixValue (ℓ + 1) x + r ∧
      zeckAdicPrefixValue (ℓ + 1) x + r < Nat.fib (ℓ + 2)) ∧
    ∀ k, ℓ + 1 < k → (x ∈ zeckNIZ r k ↔
      Nat.fib k ≤ zeckAdicPrefixValue k x + r ∧ zeckAdicPrefixValue k x < Nat.fib k)

/-- **Points of $\mathrm{NIZ}_k$ have leading digits $00$.** Let $r \ge 1$ and $k \ge 2$, and
let $\mathrm{NIZ}_k$ be the new-information zone of order $k$ for $r$. Every Zeckendorf-adic
integer $x = (x_i)_{i \ge 2}$ in $\mathrm{NIZ}_k$ has $x_{k+1} = x_k = 0$, that is, the name
$x_{k+1} \cdots x_2$ of its cylinder of order $k$ starts with $00$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 32 (`jis-2024-24.3.2-lem-32`). -/
public theorem_wanted zeckNIZ_leading_zeros {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k)
    {x : ℕ → Bool} (hx : x ∈ zeckAdic) (h : x ∈ zeckNIZ r k) :
    x (k + 1) = false ∧ x k = false

/-- **Shifting a new-information cylinder by two orders.** Let $\mathbb{X}$ be the set of
Zeckendorf-adic integers: the digit sequences $x = (x_i)_{i \in \mathbb{N}}$ in $\{0, 1\}$ with
$x_0 = x_1 = 0$ and no two consecutive digits equal to $1$. Let $r \ge 1$, $k \ge 2$ and
$y \in \mathbb{X}$. Suppose that every $x \in \mathbb{X}$ with $x_{k+1} = x_k = 0$ and $x_i = y_i$
for $2 \le i \le k - 1$ lies in the new-information zone $\mathrm{NIZ}_k$ (for the shift $r$).
Then every $x \in \mathbb{X}$ with $x_{k+3} = x_{k+2} = 0$, $x_{k+1} = 1$, $x_k = 0$ and
$x_i = y_i$ for $2 \le i \le k - 1$ lies in $\mathrm{NIZ}_{k+2}$.

In the paper's cylinder notation, where $C_w$ is the set of points of $\mathbb{X}$ whose digits
ending at $x_2$ read $w$, and with $n_i = y_i$: $C_{00 n_{k-1} \cdots n_2} \subseteq \mathrm{NIZ}_k$
implies $C_{0010 n_{k-1} \cdots n_2} \subseteq \mathrm{NIZ}_{k+2}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 33 (`jis-2024-24.3.2-lem-33`). -/
public theorem_wanted zeckNIZ_cylinder_shift {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k)
    {y : ℕ → Bool} (hy : y ∈ zeckAdic)
    (h : zeckAdic ∩ {x | x (k + 1) = false ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i} ⊆ zeckNIZ r k) :
    zeckAdic ∩ {x | x (k + 3) = false ∧ x (k + 2) = false ∧ x (k + 1) = true ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i} ⊆ zeckNIZ r (k + 2)

/-- **Lifting a cylinder of $\mathrm{NIZ}_k$ to order $k + 2$ lowers the variation by $1$.**
Let $\ell \ge 2$, let $r$ satisfy $F_\ell \le r < F_{\ell+1}$, where $F_1 = F_2 = 1, F_3 = 2,
\dots$ are the Fibonacci numbers, and let $k \ge \ell$. Write $\Delta^{(r)}$ for the variation
of the Zeckendorf sum of digits under adding $r$ on the Zeckendorf-adic integers $\mathbb{X}$,
and $\mathrm{NIZ}_k$ for the new-information zone of order $k$ for $r$. Let $y \in \mathbb{X}$
and $d \in \mathbb{Z}$. Let $C$ be the set of $x \in \mathbb{X}$ with $x_{k+1} = x_k = 0$ and
$x_i = y_i$ for $2 \le i \le k - 1$, and let $C'$ be the set of $x \in \mathbb{X}$ with
$x_{k+3} = x_{k+2} = 0$, $x_{k+1} = 1$, $x_k = 0$ and $x_i = y_i$ for $2 \le i \le k - 1$. If
$C \subseteq \mathrm{NIZ}_k$ and $\Delta^{(r)}(x) = d$ for every $x \in C$, then
$\Delta^{(r)}(x) = d - 1$ for every $x \in C'$.

In the paper's notation, $C = C_{00 n_{k-1} \cdots n_2}$ and $C' = C_{0010 n_{k-1} \cdots n_2}$
with $n_i = y_i$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 35 (`jis-2024-24.3.2-lem-35`). -/
public theorem_wanted zeckNIZ_variation_shift {r ℓ k : ℕ} (hℓ : 2 ≤ ℓ) (hr : Nat.fib ℓ ≤ r)
    (hr' : r < Nat.fib (ℓ + 1)) (hk : ℓ ≤ k) {y : ℕ → Bool} (hy : y ∈ zeckAdic)
    (h : zeckAdic ∩ {x | x (k + 1) = false ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i} ⊆ zeckNIZ r k) {d : ℤ}
    (hd : ∀ x ∈ zeckAdic ∩ {x | x (k + 1) = false ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i}, zeckAdicVariation r x = d) :
    ∀ x ∈ zeckAdic ∩ {x | x (k + 3) = false ∧ x (k + 2) = false ∧ x (k + 1) = true ∧
      x k = false ∧ ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i}, zeckAdicVariation r x = d - 1

/-- **Values of the variation on $\mathrm{NIZ}_{k+2}$ are shifted by $-1$.** Let $\ell \ge 2$,
let $r$ satisfy $F_\ell \le r < F_{\ell+1}$, where $F_1 = F_2 = 1, F_3 = 2, \dots$ are the
Fibonacci numbers, and let $k \ge \ell + 4$. Write $\Delta^{(r)}$ for the variation of the
Zeckendorf sum of digits under adding $r$ on the Zeckendorf-adic integers, $\mathrm{NIZ}_m$ for
the new-information zone of order $m$ for $r$, and $i(v)$ for the Zeckendorf-adic integer whose
digits are the Zeckendorf digits of $v \in \mathbb{N}$. Then for every integer $d$, the number
of $v < F_{k+4}$ with $i(v) \in \mathrm{NIZ}_{k+2}$ and $\Delta^{(r)}(i(v)) = d - 1$ equals
the number of $v < F_{k+2}$ with $i(v) \in \mathrm{NIZ}_k$ and $\Delta^{(r)}(i(v)) = d$.

Each $v < F_{m+2}$ stands for the cylinder of order $m$ whose name is its digits, so the values
of $\Delta^{(r)}$ on the cylinders in $\mathrm{NIZ}_{k+2}$ are those on the cylinders in
$\mathrm{NIZ}_k$ shifted by $-1$, with multiplicity.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 36 (`jis-2024-24.3.2-cor-36`). -/
public theorem_wanted zeckNIZ_values_shift {r ℓ k : ℕ} (hℓ : 2 ≤ ℓ) (hr : Nat.fib ℓ ≤ r)
    (hr' : r < Nat.fib (ℓ + 1)) (hk : ℓ + 4 ≤ k) (d : ℤ) :
    {v | v < Nat.fib (k + 4) ∧ zeckAdicOfNat v ∈ zeckNIZ r (k + 2) ∧
        zeckAdicVariation r (zeckAdicOfNat v) = d - 1}.ncard =
      {v | v < Nat.fib (k + 2) ∧ zeckAdicOfNat v ∈ zeckNIZ r k ∧
        zeckAdicVariation r (zeckAdicOfNat v) = d}.ncard

/-- **Exactly $2r$ new-information cylinders carry each small value.** Let $r \ge 1$, and let
$F_n$ denote the $n$-th Fibonacci number ($F_1 = F_2 = 1$). There is an integer $D$ such that for
every integer $d \le D$ there are exactly $2r$ pairs $(k, v)$ of natural numbers with
$v < F_{k+2}$ such that the Zeckendorf digit sequence $i(v)$ of $v$ lies in the new-information
zone $\mathrm{NIZ}_k$ (for the shift $r$) and the variation $\Delta^{(r)}$ satisfies
$\Delta^{(r)}(i(v)) = d$.

A pair $(k, v)$ stands for the cylinder of order $k$ whose name is the Zeckendorf expansion of
$v$, so the $2r$ cylinders may have equal orders.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 37 (`jis-2024-24.3.2-prop-37`). -/
public theorem_wanted zeckNIZ_count_small_values {r : ℕ} (hr : 1 ≤ r) :
    ∃ D : ℤ, ∀ d ≤ D,
      {p : ℕ × ℕ | p.2 < Nat.fib (p.1 + 2) ∧ zeckAdicOfNat p.2 ∈ zeckNIZ r p.1 ∧
        zeckAdicVariation r (zeckAdicOfNat p.2) = d}.encard = 2 * r

/-- **The variation by $F_\ell$ on $\mathrm{NIZ}_\ell$ is $1$.** Let $\ell \ge 3$, let
$F_1 = F_2 = 1, F_3 = 2, \dots$ be the Fibonacci numbers, and let $\Delta^{(F_\ell)}$ be the
variation of the Zeckendorf sum of digits under adding $F_\ell$ on the Zeckendorf-adic integers
$\mathbb{X}$. Then $\Delta^{(F_\ell)}(x) = 1$ for every $x \in \mathbb{X}$ in the
new-information zone $\mathrm{NIZ}_\ell$ of order $\ell$ for $r = F_\ell$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 40 (`jis-2024-24.3.2-lem-40`). -/
public theorem_wanted zeckNIZ_fib_variation_order {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    ∀ x ∈ zeckAdic ∩ zeckNIZ (Nat.fib ℓ) ℓ, zeckAdicVariation (Nat.fib ℓ) x = 1

/-- **Values of the variation by $F_\ell$ on $\mathrm{NIZ}_{\ell+1}$.** Let $\ell \ge 3$, let
$F_1 = F_2 = 1, F_3 = 2, \dots$ be the Fibonacci numbers, and let $\Delta^{(F_\ell)}$ be the
variation of the Zeckendorf sum of digits under adding $F_\ell$ on the Zeckendorf-adic integers.
For $v \in \mathbb{N}$ write $i(v)$ for the Zeckendorf-adic integer whose digits are the
Zeckendorf digits of $v$. Among the $v < F_{\ell+3}$ with $i(v)$ in the new-information zone
$\mathrm{NIZ}_{\ell+1}$ of order $\ell + 1$ for $r = F_\ell$, exactly $F_{\ell-1}$ satisfy
$\Delta^{(F_\ell)}(i(v)) = 0$ and exactly $F_{\ell-2}$ satisfy $\Delta^{(F_\ell)}(i(v)) = 1$.

Each such $v$ stands for the level (cylinder of order $\ell + 1$) whose name is its digits.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 41 (`jis-2024-24.3.2-prop-41`). -/
public theorem_wanted zeckNIZ_fib_variation_order_succ {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 0}.ncard = Nat.fib (ℓ - 1) ∧
      {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 1}.ncard = Nat.fib (ℓ - 2)

/-- **The variation by $F_\ell$ on $\mathrm{NIZ}_{\ell+2}$ is $0$.** Let $\ell \ge 3$, let
$F_1 = F_2 = 1, F_3 = 2, \dots$ be the Fibonacci numbers, and let $\Delta^{(F_\ell)}$ be the
variation of the Zeckendorf sum of digits under adding $F_\ell$ on the Zeckendorf-adic integers
$\mathbb{X}$. Then $\Delta^{(F_\ell)}(x) = 0$ for every $x \in \mathbb{X}$ in the
new-information zone $\mathrm{NIZ}_{\ell+2}$ of order $\ell + 2$ for $r = F_\ell$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 42 (`jis-2024-24.3.2-prop-42`). -/
public theorem_wanted zeckNIZ_fib_variation_order_add_two {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    ∀ x ∈ zeckAdic ∩ zeckNIZ (Nat.fib ℓ) (ℓ + 2), zeckAdicVariation (Nat.fib ℓ) x = 0

/-! ### Mixing of the block actions -/

/-- **Blocks of a Zeckendorf representation.** Let $r \in \mathbb{N}$ have Zeckendorf
representation $r = F_{i_1} + \dots + F_{i_s}$ with $i_1 > \dots > i_s \ge 2$ (Fibonacci numbers
with $F_1 = F_2 = 1$). The blocks of $r$ are the maximal runs of successive terms of the list
$i_1, \dots, i_s$ in which each index is exactly $2$ less than the one before it (the maximal
factors $(10)^m$ of the expansion, a final $1$ at the unit position counting as $10$). The blocks
are listed from the unit digit, so the first block contains $i_s$ and the last contains $i_1$, and
each block lists its indices in decreasing order. The number of blocks of $r$ is $\rho(r)$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Definition 2 (blocks) and Section 7.1. -/
public def zeckBlocks (r : ℕ) : List (List ℕ) :=
  ((Nat.zeckendorf r).splitBy fun a b => a == b + 2).reverse

/-- **Block prefixes of a natural number.** The blocks of $r \in \mathbb{N}$ are the maximal runs
of Zeckendorf indices of $r$ in which consecutive indices differ by exactly $2$, listed from the
unit digit. For $i \in \mathbb{N}$, the block prefix $r[i]$ is the sum of the Fibonacci numbers
$F_j$ over the indices $j$ in the first $i$ blocks of $r$, or in all blocks when $i$ exceeds the
number $\rho(r)$ of blocks. Thus $r[0] = 0$ and $r[i] = r$ for $i \ge \rho(r)$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 7.1 (definition of `r[i]`). -/
public def zeckBlockPrefix (r i : ℕ) : ℕ :=
  (((zeckBlocks r).take i).map fun B => (B.map Nat.fib).sum).sum

/-- **The empty block prefix is zero.** For every natural number $r$, the block prefix $r[0]$,
formed by the first $0$ blocks of the Zeckendorf representation of $r$, equals $0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 7.1 (convention `r[0] := 0`). -/
public theorem zeckBlockPrefix_zero (r : ℕ) : zeckBlockPrefix r 0 = 0 := by
  simp [zeckBlockPrefix]

/-- **Zero has no blocks.** The list of blocks of $0$ is empty; that is, the number $\rho(0)$ of
blocks of $0$ is $0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Definition 2 (characteristic lemma: `ρ(0) = 0`). -/
public theorem zeckBlocks_zero : zeckBlocks 0 = [] := by
  simp [zeckBlocks]
  rfl

/-- **An $\alpha$-mixing bound for the block variations.** Let $\mu$ be a probability measure on
the digit sequences $x : \mathbb{N} \to \{0, 1\}$ that gives the complement of the
Zeckendorf-adic integers measure zero and is preserved by the odometer $T$. Let $r \ge 1$, let
$\rho(r)$ be the number of blocks of $r$ and $r[i]$ its block prefixes, and for
$1 \le i \le \rho(r)$ let $X_i(x) = \Delta^{(r[i] - r[i-1])}(T^{r[i-1]}(x))$, where $\Delta^{(m)}$
is the variation and $T^{m}$ the $m$-fold iterate of $T$. Let $k, p \ge 1$, let $A$ be
measurable for the $\sigma$-algebra generated by the $X_i$ with $1 \le i \le \min(p, \rho(r))$,
and let $B$ be measurable for the $\sigma$-algebra generated by the $X_i$ with
$k + p \le i \le \rho(r)$ (the trivial $\sigma$-algebra when there is no such $i$). Then, with
$\varphi$ the golden ratio,
$$|\mu(A \cap B) - \mu(A)\mu(B)| \le 12 (1 - 1/\varphi^8)^{k/6} + 1/\varphi^{2k}.$$

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Theorem 6 (`jis-2024-24.3.2-thm-6`) and its restatement in Section 7
(`jis-2024-24.3.2-thm-unnumbered-2`). -/
public theorem_wanted zeckBlockAction_alpha_mixing (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {r k p : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hp : 1 ≤ p) {A B : Set (ℕ → Bool)}
    (hA : MeasurableSet[⨆ (i : ℕ) (_ : 1 ≤ i ∧ i ≤ p ∧ i ≤ (zeckBlocks r).length),
      MeasurableSpace.comap (fun x => zeckAdicVariation
        (zeckBlockPrefix r i - zeckBlockPrefix r (i - 1))
        (zeckOdometer^[zeckBlockPrefix r (i - 1)] x)) inferInstance] A)
    (hB : MeasurableSet[⨆ (i : ℕ) (_ : k + p ≤ i ∧ i ≤ (zeckBlocks r).length),
      MeasurableSpace.comap (fun x => zeckAdicVariation
        (zeckBlockPrefix r i - zeckBlockPrefix r (i - 1))
        (zeckOdometer^[zeckBlockPrefix r (i - 1)] x)) inferInstance] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤
      12 * (1 - 1 / Real.goldenRatio ^ 8) ^ ((k : ℝ) / 6) + 1 / Real.goldenRatio ^ (2 * k)

end

end MetaMathlibExt
