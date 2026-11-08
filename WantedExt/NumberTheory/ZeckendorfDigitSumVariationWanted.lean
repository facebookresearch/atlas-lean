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

/-- `μ^{(F_ℓ)} = μ^{(1)}` for every `ℓ ≥ 2`: whenever `μ d` is the asymptotic density of
`{n : s(n + 1) - s(n) = d}` for every `d`, it is also the density of
`{n : s(n + F_ℓ) - s(n) = d}`.

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

/-- The distribution of `Δ^{(1)}`: `μ^{(1)}(d) = 0` for `d ≥ 2`, `μ^{(1)}(1) = 1/φ²`, and
`μ^{(1)}(d) = 1/φ^{2 - 2d}` for `d ≤ 0`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 39 (`jis-2024-24.3.2-prop-39`). -/
public theorem_wanted zeckendorf_variation_density_one (d : ℤ) :
    Set.HasDensity
        {n : ℕ | ((Nat.zeckendorf (n + 1)).length : ℤ) - (Nat.zeckendorf n).length = d}
        (if 2 ≤ d then 0 else if d = 1 then 1 / Real.goldenRatio ^ 2
          else 1 / Real.goldenRatio ^ (2 - 2 * d))

/-- For every `r ∈ ℕ` the densities `μ^{(r)}(d)` exist for all `d ∈ ℤ`, and the resulting law of
`Δ^{(r)}` has finite moments of every order and mean zero.

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

/-- The negative tail of `μ^{(r)}` is geometric with ratio `1/φ²`: if `μ d` is the density of
`{n : s(n + r) - s(n) = d}` for every `d`, then `μ(d - 1) = μ(d) / φ²` for all sufficiently
small `d`.

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

/-- The Zeckendorf-adic integers `𝕏 = {x ∈ {0,1}^{ℕ_{≥2}} : x_k x_{k+1} = 0 for all k ≥ 2}`.
A point is a digit sequence `x : ℕ → Bool` in which digit `k ≥ 2` carries the weight `F_k`
(`Nat.fib k`); the unused digits `0` and `1` are `false`, so the paper's indexing is kept.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (arXiv:2309.14285v2). -/
public def zeckAdic : Set (ℕ → Bool) :=
  {x | x 0 = false ∧ x 1 = false ∧ ∀ k, x k = false ∨ x (k + 1) = false}

/-- The inclusion `ℕ → 𝕏`: digit `k` of `n` is set exactly when `F_k` occurs in the Zeckendorf
representation of `n`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (the map `i`). -/
public def zeckAdicOfNat (n : ℕ) : ℕ → Bool := fun k => decide (k ∈ Nat.zeckendorf n)

/-- The odometer `T : 𝕏 → 𝕏`, `T(x) = x + 1`. If `k ≥ 2` is the least index with
`x_k = x_{k+1} = 0`, then `T` sets digit `k` and clears every digit below `k`; this is the
paper's case table `⋯00(10)^ℓ ↦ ⋯01(00)^ℓ`, `⋯001(01)^ℓ ↦ ⋯010(00)^ℓ`. If no such `k`
exists (`x = (10)^∞` or `(01)^∞`), then `T(x) = 0^∞`. Adding `r ∈ ℕ` to `x` is `T^[r] x`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (definition of `T`). -/
public noncomputable def zeckOdometer (x : ℕ → Bool) : ℕ → Bool :=
  open Classical in
  if h : ∃ k, 2 ≤ k ∧ x k = false ∧ x (k + 1) = false then
    fun j => if j < Nat.find h then false else if j = Nat.find h then true else x j
  else fun _ => false

/-- The inclusion sends `0` to the zero sequence.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (characteristic lemma for the map `i`). -/
public theorem zeckAdicOfNat_zero : zeckAdicOfNat 0 = fun _ => false := by
  funext k
  simp [zeckAdicOfNat]

/-- On a point of `𝕏` ending in `00`, the odometer sets the unit digit `x_2`.

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

/-- On `(10)^∞` and `(01)^∞` (no two consecutive zero digits) the odometer returns `0^∞`.

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

/-- The truncated variation `Δ_k^{(r)}(x) = s_k(x + r) - s_k(x)`, where
`s_k(x) = x_2 + ⋯ + x_k` and `x + r = T^[r] x`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (definition of `s_k` and `Δ_k^{(r)}`). -/
public noncomputable def zeckAdicTruncVariation (r k : ℕ) (x : ℕ → Bool) : ℤ :=
  ∑ i ∈ Finset.Icc 2 k, ((zeckOdometer^[r] x i).toNat : ℤ) -
    ∑ i ∈ Finset.Icc 2 k, ((x i).toNat : ℤ)

/-- `Δ_k^{(0)} = 0`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ_k^{(r)}`). -/
public theorem zeckAdicTruncVariation_zero (k : ℕ) (x : ℕ → Bool) :
    zeckAdicTruncVariation 0 k x = 0 := by
  simp [zeckAdicTruncVariation]

/-- The variation `Δ^{(r)}(x) = lim_{k → ∞} Δ_k^{(r)}(x)` on `𝕏`, where the integer sequence
`Δ_k^{(r)}(x)` is eventually constant; it is `0` (a junk value) elsewhere, a set the paper shows
to be finite.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (definition of `Δ^{(r)}` on `𝕏`). -/
public noncomputable def zeckAdicVariation (r : ℕ) (x : ℕ → Bool) : ℤ :=
  open Classical in
  if h : ∃ d, ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation r k x = d then h.choose else 0

/-- If `Δ_k^{(r)}(x)` is eventually `d`, then `Δ^{(r)}(x) = d`.

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

/-- `Δ^{(0)} = 0` on all of `𝕏`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ^{(r)}`). -/
public theorem zeckAdicVariation_zero (x : ℕ → Bool) : zeckAdicVariation 0 x = 0 :=
  zeckAdicVariation_eq_of_eventually (Filter.Eventually.of_forall fun k =>
    zeckAdicTruncVariation_zero k x)

/-- If `x_ℓ = x_{ℓ+1} = 0` (`ℓ ≥ 2`) and the Zeckendorf digits `r_2, …, r_{ℓ+1}` of `r` vanish,
then `(x + r)_n = x_n` for `2 ≤ n ≤ ℓ - 2`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 9 (`jis-2024-24.3.2-cor-9`). -/
public theorem_wanted zeckOdometer_iterate_low_digits {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hx0 : x ℓ = false) (hx1 : x (ℓ + 1) = false)
    (hr : ∀ j, 2 ≤ j → j ≤ ℓ + 1 → j ∉ Nat.zeckendorf r) :
    ∀ n, 2 ≤ n → n ≤ ℓ - 2 → zeckOdometer^[r] x n = x n

/-- If `r < F_{ℓ+1}` (`ℓ ≥ 2`) and `x_{ℓ+2} = x_{ℓ+3} = 0`, then `(x + r)_k = x_k` for all
`k ≥ ℓ + 3`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 10 (`jis-2024-24.3.2-lem-10`). -/
public theorem_wanted zeckOdometer_iterate_high_digits {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hr : r < Nat.fib (ℓ + 1)) (hx2 : x (ℓ + 2) = false)
    (hx3 : x (ℓ + 3) = false) :
    ∀ k, ℓ + 3 ≤ k → zeckOdometer^[r] x k = x k

/-- If `x_{ℓ+1} = ⋯ = x_{ℓ+4} = 0` (`ℓ ≥ 2`), `r_{ℓ+2} = 1` and `r < F_{ℓ+3}`, then either
`(x + r)_{ℓ+k} = r_{ℓ+k}` for `k = 1, 2, 3, 4`, or `(x + r)_{ℓ+1} = 0` and `(x + r)_{ℓ+3} = 1`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 11 (`jis-2024-24.3.2-lem-11`). -/
public theorem_wanted zeckOdometer_iterate_block_digits {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hx0 : ∀ k, 1 ≤ k → k ≤ 4 → x (ℓ + k) = false)
    (hr : ℓ + 2 ∈ Nat.zeckendorf r) (hrlt : r < Nat.fib (ℓ + 3)) :
    (∀ k, 1 ≤ k → k ≤ 4 → zeckOdometer^[r] x (ℓ + k) = decide (ℓ + k ∈ Nat.zeckendorf r)) ∨
      (zeckOdometer^[r] x (ℓ + 1) = false ∧ zeckOdometer^[r] x (ℓ + 3) = true)

/-- Stopping condition for a block of size one: if `x_ℓ = ⋯ = x_{ℓ+5} = 0` (`ℓ ≥ 2`),
`r_{ℓ+1} = r_{ℓ+5} = 0`, `r_{ℓ+3} = 1`, and `r̃ = [r_ℓ ⋯ r_2]` is the part of `r` of index
`≤ ℓ`, then `(x + r̃ + F_{ℓ+3})_k = (x + r̃)_k = x_k` for `k ≥ ℓ + 4` and
`(x + r)_k = (x + r̃ + F_{ℓ+3})_k = (x + r̃)_k` for `2 ≤ k ≤ ℓ + 2`.

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

/-- Stopping condition for a block of size `m + 2`: if `x_i = 0` for
`i ∈ {ℓ, ℓ+1, ℓ+2, ℓ+3, ℓ+2m+4, ℓ+2m+5, ℓ+2m+6, ℓ+2m+7}` (`ℓ ≥ 2`), `r_{ℓ+1} = r_{ℓ+2m+7} = 0`,
`r_{ℓ+2i+3} = 1` for `i = 0, …, m+1`, and `r̃ = [r_ℓ ⋯ r_2]`, then with
`S = ∑_{i=0}^{m+1} F_{ℓ+2i+3}`: `(x + r̃ + S)_k = (x + r̃)_k = x_k` for `k ≥ ℓ + 2m + 7`, and
`(x + r)_k = (x + r̃ + S)_k` for `2 ≤ k ≤ ℓ + 2m + 2`.

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

/-- `(𝕏, T)` is uniquely ergodic: there is exactly one `T`-invariant Borel probability measure
carried by `𝕏` (measures on `𝕏` are taken as measures on `ℕ → Bool` with `μ 𝕏ᶜ = 0`).

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 15 (`jis-2024-24.3.2-prop-15`), first part. -/
public theorem_wanted zeckOdometer_uniquely_ergodic :
    ∃! μ : Measure (ℕ → Bool),
      IsProbabilityMeasure μ ∧ μ zeckAdicᶜ = 0 ∧ MeasurePreserving zeckOdometer μ μ

/-- The `T`-invariant probability measure `ℙ` gives the cylinder `C_{r_ℓ ⋯ r_2}` (`ℓ ≥ 2`,
`(r_ℓ, …, r_2)` admissible, here the digits of some `y ∈ 𝕏`) the mass `1/φ^{ℓ-1}` if `r_ℓ = 0`
and `1/φ^ℓ` if `r_ℓ = 1`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 15 (`jis-2024-24.3.2-prop-15`), cylinder formula. -/
public theorem_wanted zeckOdometer_invariant_measure_cylinder (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {y : ℕ → Bool} (hy : y ∈ zeckAdic) :
    μ {x | ∀ i, 2 ≤ i → i ≤ ℓ → x i = y i} =
      ENNReal.ofReal (1 / Real.goldenRatio ^ (if y ℓ = true then ℓ else ℓ - 1))

/-- Renewal property of `ℙ`, with `σ` the shift `(σ x)_i = x_{i+1}`: for a cylinder
`C = C_{z_{ℓ₀} ⋯ z_2}`, `k ≥ 2` and admissible `(r_k, …, r_2)` (the digits of `y ∈ 𝕏`),
`ℙ(σ^k x ∈ C | x ∈ C_{0 r_k ⋯ r_2}) = ℙ(C)`, and if `r_k = 0` then
`ℙ(σ^{k+1} x ∈ C | x ∈ C_{1 r_k ⋯ r_2}) = ℙ(C)`.

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

/-- Bradley's inequality `α(k) ≤ φ(k)/2` between the `α`- and `φ`-mixing coefficients of a
sequence of random variables `(X_j)_{j ≥ 1}`, stated through the suprema: if `c` bounds every
term `|ℙ_A(B) - ℙ(B)|` defining `φ(k)` (`p ≥ 1`, `A ∈ σ(X_j : 1 ≤ j ≤ p)`, `ℙ(A) > 0`,
`B ∈ σ(X_j : j ≥ k + p)`), then `c/2` bounds every term `|ℙ(A ∩ B) - ℙ(A)ℙ(B)|` defining `α(k)`.

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

/-- `φ`-mixing of the digits under `ℙ`: for the coordinate process `X_j = x_{j+1}` (`j ≥ 1`),
every term defining `φ(k)` is at most `2/φ^{2k}`, i.e. `φ(k) ≤ 2/φ^{2k}` for `k ≥ 1`.

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

/-- The Markov chain `y_1 = 0`, `y_j = ψ(y_{j-1}, U_j)` driven by `u j = U_{j+2}`, where
`ψ(0, t) = 1` if `t < 1/φ²`, `ψ(0, t) = 0` otherwise, and `ψ(1, t) = 0`. Digits `0` and `1`
are `false`, matching `zeckAdic`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.3 (the maps `ψ` and `(y_j)`). -/
public noncomputable def zeckMarkovPath (u : ℕ → ℝ) : ℕ → Bool
  | 0 => false
  | 1 => false
  | j + 2 => !zeckMarkovPath u (j + 1) && decide (u j < 1 / Real.goldenRatio ^ 2)

/-- The first digit of the chain is set exactly when `U_2 < 1/φ²`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.3 (characteristic lemma for `(y_j)`). -/
public theorem zeckMarkovPath_two (u : ℕ → ℝ) :
    zeckMarkovPath u 2 = decide (u 0 < 1 / Real.goldenRatio ^ 2) := by
  simp [zeckMarkovPath]

/-- After a set digit the chain emits `0`: `y_j = 1 → y_{j+1} = 0`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.3 (characteristic lemma: `ψ(1, t) = 0`). -/
public theorem zeckMarkovPath_succ_of_true (u : ℕ → ℝ) {j : ℕ}
    (h : zeckMarkovPath u (j + 1) = true) : zeckMarkovPath u (j + 2) = false := by
  simp [zeckMarkovPath, h]

/-- If `U_2, U_3, …` are independent and uniform on `[0, 1]`, the law of `(y_j)_{j ≥ 2}` is the
`T`-invariant measure `ℙ`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 20 (`jis-2024-24.3.2-lem-20`). -/
public theorem_wanted zeckMarkovPath_law (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (hX : μ zeckAdicᶜ = 0) (hT : MeasurePreserving zeckOdometer μ μ) {Ω : Type*}
    [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (U : ℕ → Ω → ℝ)
    (hU : ∀ j, Measurable (U j)) (hind : ProbabilityTheory.iIndepFun U ν)
    (hunif : ∀ j, ν.map (U j) = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    ν.map (fun ω => zeckMarkovPath fun j => U j ω) = μ

/-- For `2 ≤ k_0 < k_1 < ⋯ < k_ℓ` and a union `A` of cylinders of order `k_0 - 1` (a set
determined by `x_2, …, x_{k_0}`) with `x_{k_0} = 0` on `A` and `ℙ(A) > 0`:
`1/φ^ℓ ≤ ℙ_A(x_{k_i} = 0 for 1 ≤ i ≤ ℓ) ≤ (2/φ²)^ℓ`.

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

/-- Ergodic averages of `f ∘ Δ^{(r)}` for `f` of polynomial growth: if
`|f(n)| ≤ C|n|^α + |f(0)|` with `α ≥ 1`, `C > 0`, then `f ∘ Δ^{(r)} ∈ L¹(ℙ)` and
`(1/N) ∑_{n<N} f(Δ^{(r)}(n)) → ∫ f ∘ Δ^{(r)} dℙ = lim_k ∫ f ∘ Δ_k^{(r)} dℙ`, where on `ℕ`
`Δ^{(r)}(n) = s(n + r) - s(n)`.

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

/-- For `r ≥ 1`, `N ≥ 1`, `k ≥ 2` and `d, d' ∈ ℤ`:
`(1/N)|{n < N : (Δ^{(r)}(n), Δ_k^{(r)}(n)) = (d, d')}| ≤ rφ³ ℙ(Δ^{(r)} = d, Δ_k^{(r)} = d')`,
and in particular `(1/N)|{n < N : Δ^{(r)}(n) = d}| ≤ rφ³ ℙ(Δ^{(r)} = d)`.

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

/-- `Δ^{(1)}(x) = lim_k Δ_k^{(1)}(x)` exists for `x ∈ 𝕏` iff `x ∈ C_{00(10)^d} ∪ C_{001(01)^d}`
for some `d ≥ 0`.

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

/-- On `C_{00(10)^d}`: `Δ^{(1)} = 1 - d`, and for `k ≥ 2`, `Δ_k^{(1)} = (2 - k)/2` if `k` is even
and `k ≤ 2d`, `(1 - k)/2` if `k` is odd and `k ≤ 2d + 1`, and `1 - d` if `k ≥ 2d + 2` (halves
written as `2 Δ_k^{(1)} = ⋯`).

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

/-- On `C_{001(01)^d}`: `Δ^{(1)} = -d`, and for `k ≥ 2`, `Δ_k^{(1)} = -k/2` if `k` is even and
`k ≤ 2d + 2`, `(1 - k)/2` if `k` is odd and `k ≤ 2d + 1`, `(3 - k)/2` if `k = 2d + 3`, and `-d` if
`k ≥ 2d + 4` (halves written as `2 Δ_k^{(1)} = ⋯`).

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

/-- For `r ≥ 1` and `f : ℤ → ℂ` with `f ∘ Δ^{(r)} ∈ L¹(ℙ)`:
`(1/N) ∑_{n<N} f(Δ^{(r)}(n)) → ∫ f ∘ Δ^{(r)} dℙ`, where on `ℕ` `Δ^{(r)}(n) = s(n + r) - s(n)`.

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

/-- `v_k(x) = ∑_{i=2}^{k+1} x_i F_i`, the value of the name `x_{k+1} ⋯ x_2` of the cylinder of
order `k` (the rightmost `k` digits) containing `x`. The `j`-th level (counted from `1`) of the
large Rokhlin tower of order `k` is `{v_k = j - 1}` for `j ≤ F_{k+1}`; the levels of the small
tower are `{v_k = F_{k+1} + j - 1}` for `j ≤ F_k`, and `T` moves each level to the next one.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.1 (cylinders of order `k` and the two towers). -/
public def zeckAdicPrefixValue (k : ℕ) (x : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.Icc 2 (k + 1), if x i = true then Nat.fib i else 0

/-- `v_1(x) = x_2`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.1 (characteristic lemma: towers of order `1`). -/
public theorem zeckAdicPrefixValue_one (x : ℕ → Bool) :
    zeckAdicPrefixValue 1 x = if x 2 = true then 1 else 0 := by
  simp [zeckAdicPrefixValue]

/-- `CST_k`: the union of the levels of the large and small towers of order `k`, except the `r`
highest levels of each tower, i.e. `v_k + r < F_{k+1}` or `F_{k+1} ≤ v_k` and
`v_k + r < F_{k+2}`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (definition of `CST_k`). -/
public def zeckCST (r k : ℕ) : Set (ℕ → Bool) :=
  {x | zeckAdicPrefixValue k x + r < Nat.fib (k + 1) ∨
    (Nat.fib (k + 1) ≤ zeckAdicPrefixValue k x ∧ zeckAdicPrefixValue k x + r < Nat.fib (k + 2))}

/-- `CST_1 = ∅` for `r ≥ 1`.

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

/-- The new-information zone `NIZ_k = CST_k \ CST_{k-1}` of the towers of order `k`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (definition of `NIZ_k`). -/
public def zeckNIZ (r k : ℕ) : Set (ℕ → Bool) := zeckCST r k \ zeckCST r (k - 1)

/-- `NIZ_k ⊆ CST_k`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (characteristic lemma for `NIZ_k`). -/
public theorem zeckNIZ_subset_zeckCST (r k : ℕ) : zeckNIZ r k ⊆ zeckCST r k :=
  fun _ hx => hx.1

/-- Description of `NIZ_k` by tower levels, for `r ≥ 1` and `ℓ ≥ 2` with `F_ℓ ≤ r < F_{ℓ+1}`
(levels counted from `1`, level `j` of the large tower of order `k` being `{v_k = j - 1}`):
`NIZ_k = ∅` for `2 ≤ k ≤ ℓ - 1`; `NIZ_ℓ` is the first `F_{ℓ+1} - r` levels of the large tower of
order `ℓ`; `NIZ_{ℓ+1}` is the levels `F_{ℓ+1} - r + 1, …, F_{ℓ+2} - r` of the large tower of order
`ℓ + 1`; for `k > ℓ + 1`, `NIZ_k` is the levels `F_k - r + 1, …, F_k` of the large tower of
order `k` (all as subsets of `𝕏`).

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

/-- For `r ≥ 1` and `k ≥ 2`, the cylinders of order `k` in `NIZ_k` have names starting with
`00`: `x_{k+1} = x_k = 0` on `𝕏 ∩ NIZ_k`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 32 (`jis-2024-24.3.2-lem-32`). -/
public theorem_wanted zeckNIZ_leading_zeros {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k)
    {x : ℕ → Bool} (hx : x ∈ zeckAdic) (h : x ∈ zeckNIZ r k) :
    x (k + 1) = false ∧ x k = false

/-- For `r ≥ 1`, `k ≥ 2` and an admissible word `n_{k-1} ⋯ n_2` (the digits of `y ∈ 𝕏`):
`C_{00 n_{k-1} ⋯ n_2} ⊆ NIZ_k` implies `C_{0010 n_{k-1} ⋯ n_2} ⊆ NIZ_{k+2}`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 33 (`jis-2024-24.3.2-lem-33`). -/
public theorem_wanted zeckNIZ_cylinder_shift {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k)
    {y : ℕ → Bool} (hy : y ∈ zeckAdic)
    (h : zeckAdic ∩ {x | x (k + 1) = false ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i} ⊆ zeckNIZ r k) :
    zeckAdic ∩ {x | x (k + 3) = false ∧ x (k + 2) = false ∧ x (k + 1) = true ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i} ⊆ zeckNIZ r (k + 2)

/-- For `r ≥ 1`, `ℓ ≥ 2` with `F_ℓ ≤ r < F_{ℓ+1}`, `k ≥ ℓ`, and a cylinder
`C_{00 n_{k-1} ⋯ n_2} ⊆ NIZ_k` on which `Δ^{(r)} = d`: `Δ^{(r)} = d - 1` on
`C_{0010 n_{k-1} ⋯ n_2}`.

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

/-- For `k ≥ ℓ + 4` (`F_ℓ ≤ r < F_{ℓ+1}`, `ℓ ≥ 2`), the values of `Δ^{(r)}` on the cylinders of
order `k + 2` in `NIZ_{k+2}` are those on the cylinders of order `k` in `NIZ_k` shifted by `-1`,
with multiplicity: each cylinder of order `k` is represented by the integer `v < F_{k+2}` whose
Zeckendorf digits are its name, and for every `d` the number of cylinders of `NIZ_{k+2}` with
value `d - 1` equals the number of cylinders of `NIZ_k` with value `d`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 36 (`jis-2024-24.3.2-cor-36`). -/
public theorem_wanted zeckNIZ_values_shift {r ℓ k : ℕ} (hℓ : 2 ≤ ℓ) (hr : Nat.fib ℓ ≤ r)
    (hr' : r < Nat.fib (ℓ + 1)) (hk : ℓ + 4 ≤ k) (d : ℤ) :
    {v | v < Nat.fib (k + 4) ∧ zeckAdicOfNat v ∈ zeckNIZ r (k + 2) ∧
        zeckAdicVariation r (zeckAdicOfNat v) = d - 1}.ncard =
      {v | v < Nat.fib (k + 2) ∧ zeckAdicOfNat v ∈ zeckNIZ r k ∧
        zeckAdicVariation r (zeckAdicOfNat v) = d}.ncard

/-- For `r ≥ 1` and all sufficiently small `d`, exactly `2r` cylinders, of possibly equal orders
`k_1, …, k_{2r}` with the cylinder of order `k_i` in `NIZ_{k_i}`, carry the value
`Δ^{(r)} = d` (cylinders of order `k` represented by `v < F_{k+2}` as in Corollary 36).

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 37 (`jis-2024-24.3.2-prop-37`). -/
public theorem_wanted zeckNIZ_count_small_values {r : ℕ} (hr : 1 ≤ r) :
    ∃ D : ℤ, ∀ d ≤ D,
      {p : ℕ × ℕ | p.2 < Nat.fib (p.1 + 2) ∧ zeckAdicOfNat p.2 ∈ zeckNIZ r p.1 ∧
        zeckAdicVariation r (zeckAdicOfNat p.2) = d}.encard = 2 * r

/-- For `r = F_ℓ`, `ℓ ≥ 3`: `Δ^{(F_ℓ)} = 1` on `NIZ_ℓ`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 40 (`jis-2024-24.3.2-lem-40`). -/
public theorem_wanted zeckNIZ_fib_variation_order {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    ∀ x ∈ zeckAdic ∩ zeckNIZ (Nat.fib ℓ) ℓ, zeckAdicVariation (Nat.fib ℓ) x = 1

/-- For `r = F_ℓ`, `ℓ ≥ 3`: among the levels (cylinders of order `ℓ + 1`, represented by
`v < F_{ℓ+3}`) in `NIZ_{ℓ+1}`, exactly `F_{ℓ-1}` carry `Δ^{(F_ℓ)} = 0` and exactly `F_{ℓ-2}`
carry `Δ^{(F_ℓ)} = 1`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 41 (`jis-2024-24.3.2-prop-41`). -/
public theorem_wanted zeckNIZ_fib_variation_order_succ {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 0}.ncard = Nat.fib (ℓ - 1) ∧
      {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 1}.ncard = Nat.fib (ℓ - 2)

/-- For `r = F_ℓ`, `ℓ ≥ 3`: `Δ^{(F_ℓ)} = 0` on `NIZ_{ℓ+2}`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 42 (`jis-2024-24.3.2-prop-42`). -/
public theorem_wanted zeckNIZ_fib_variation_order_add_two {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    ∀ x ∈ zeckAdic ∩ zeckNIZ (Nat.fib ℓ) (ℓ + 2), zeckAdicVariation (Nat.fib ℓ) x = 0

/-! ### Mixing of the block actions -/

/-- The blocks of `r`: the maximal runs of Zeckendorf indices of `r` with consecutive gaps
exactly `2` (maximal factors `(10)^m` of the expansion, a final `1` at the unit position counting
as `10`), listed from the unit digit; `ρ(r)` is their number.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Definition 2 (blocks) and Section 7.1. -/
public def zeckBlocks (r : ℕ) : List (List ℕ) :=
  ((Nat.zeckendorf r).splitBy fun a b => a == b + 2).reverse

/-- `r[i]`: the integer whose expansion is formed by the first `i` blocks of `r` (from the unit
digit), so `r[0] = 0` and `r[ρ(r)] = r`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 7.1 (definition of `r[i]`). -/
public def zeckBlockPrefix (r i : ℕ) : ℕ :=
  (((zeckBlocks r).take i).map fun B => (B.map Nat.fib).sum).sum

/-- `r[0] = 0`.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 7.1 (convention `r[0] := 0`). -/
public theorem zeckBlockPrefix_zero (r : ℕ) : zeckBlockPrefix r 0 = 0 := by
  simp [zeckBlockPrefix]

/-- `0` has no blocks.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Definition 2 (characteristic lemma: `ρ(0) = 0`). -/
public theorem zeckBlocks_zero : zeckBlocks 0 = [] := by
  simp [zeckBlocks]
  rfl

/-- The `α`-mixing bound for the block actions
`X_i^{(r)} = Δ^{(r[i] - r[i-1])} ∘ T^{r[i-1]}` (`1 ≤ i ≤ ρ(r)`, `r ≥ 1`) under `ℙ`: for
`k, p ≥ 1`, `A ∈ σ(X_i : 1 ≤ i ≤ min p ρ(r))` and `B ∈ σ(X_i : k + p ≤ i ≤ ρ(r))` (trivial when
empty), `|ℙ(A ∩ B) - ℙ(A)ℙ(B)| ≤ 12 (1 - 1/φ^8)^{k/6} + 1/φ^{2k}`, i.e. the bound on `α(k)`.

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
