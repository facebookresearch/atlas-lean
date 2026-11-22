/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Order.LiminfLimsup

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

/-- The `n`-Lagrange approximability `λₙ(ξ) = limsup_{s/t → ξ} gcd(t, n)/(t² |s/t - ξ|)` in `EReal`,
the limsup over rationals `s/t ≠ ξ` (in lowest terms) tending to `ξ`; `λ₁` is the classical
Lagrange approximability `λ`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (3). -/
noncomputable def nLagrangeApproximability (n : ℕ) (ξ : ℝ) : EReal :=
  limsup (fun q : ℚ => (((Nat.gcd q.den n : ℝ) / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) : ℝ) : EReal))
    (comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ))

/-- For `n = 1` the factor `gcd(t, 1)` is `1`: `λ₁` is the classical approximability.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equations (1) and (3). -/
theorem nLagrangeApproximability_one (ξ : ℝ) :
    nLagrangeApproximability 1 ξ =
      limsup (fun q : ℚ => ((1 / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) : ℝ) : EReal))
        (comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ)) := by
  simp [nLagrangeApproximability]

/-- The `n`-Markoff approximability
`μₙ(ξ, ξ') = sup_{(s,t) ∈ ℤ² ∖ 0} gcd(t, n) |ξ - ξ'| / (|s - tξ| |s - tξ'|)` in `EReal`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
noncomputable def nMarkoffApproximability (n : ℕ) (ξ ξ' : ℝ) : EReal :=
  ⨆ st : {p : ℤ × ℤ // p ≠ 0},
    ((((Int.gcd st.1.2 n : ℝ) * |ξ - ξ'| /
      (|(st.1.1 : ℝ) - st.1.2 * ξ| * |(st.1.1 : ℝ) - st.1.2 * ξ'|) : ℝ)) : EReal)

/-- `μₙ` is symmetric in its two arguments.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
theorem nMarkoffApproximability_comm (n : ℕ) (ξ ξ' : ℝ) :
    nMarkoffApproximability n ξ ξ' = nMarkoffApproximability n ξ' ξ := by
  simp only [nMarkoffApproximability, abs_sub_comm ξ ξ', mul_comm |(_ : ℝ) - _ * ξ|]

/-- The `n`-Lagrange spectrum `Lₙ`: the real values of `λₙ(ξ)` over irrational `ξ`; `L₁` is the
classical Lagrange spectrum `L`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (3). -/
def nLagrangeSpectrum (n : ℕ) : Set ℝ :=
  {α | ∃ ξ : ℝ, Irrational ξ ∧ nLagrangeApproximability n ξ = α}

/-- Membership in `Lₙ`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (3). -/
theorem mem_nLagrangeSpectrum (n : ℕ) (α : ℝ) :
    α ∈ nLagrangeSpectrum n ↔ ∃ ξ : ℝ, Irrational ξ ∧ nLagrangeApproximability n ξ = α :=
  Iff.rfl

/-- The `n`-Markoff spectrum `Mₙ`: the real values of `μₙ(ξ, ξ')` over distinct irrationals
`ξ, ξ'`; `M₁` is the classical Markoff spectrum `M`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
def nMarkoffSpectrum (n : ℕ) : Set ℝ :=
  {α | ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧ nMarkoffApproximability n ξ ξ' = α}

/-- Membership in `Mₙ`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
theorem mem_nMarkoffSpectrum (n : ℕ) (α : ℝ) :
    α ∈ nMarkoffSpectrum n ↔
      ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧ nMarkoffApproximability n ξ ξ' = α :=
  Iff.rfl

/-- Classical facts for an irrational `ξ = [a₀; a₁, a₂, …]` with complete quotients `ξ_k`
(`ξ₀ = ξ`, `ξ_{k+1} = 1/{ξ_k}`) and digits `a_k = ⌊ξ_k⌋`: (a) for `k ≥ 1` the convergent
`p_k/q_k = [a₀; …, a_{k-1}]` has `(-1)^k/(q_k² (p_k/q_k - ξ)) = a_k + [0; a_{k-1}, …, a₁] +
[0; a_{k+1}, …]`; (c) `λ(ξ)` is the limsup over `k` of these cut qualities.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 4 (`integers-2025-A47-prop-4`), parts (a) and (c), quoted from Cusick and Flahive,
Appendix 1. -/
public theorem_wanted convergent_quality_and_lagrange_limsup (ξ : ℝ) (hξ : Irrational ξ) :
    let cq : ℕ → ℝ := fun k => (fun x : ℝ => (Int.fract x)⁻¹)^[k] ξ
    let a : ℕ → ℤ := fun k => ⌊cq k⌋
    let rev : ℕ → ℝ := fun k =>
      ((List.range (k - 1)).reverse.map (fun i => a (i + 1))).foldr
        (fun b acc => 1 / ((b : ℝ) + acc)) 0
    let cut : ℕ → ℝ := fun k => (a k : ℝ) + rev k + Int.fract (cq k)
    (∀ k : ℕ, 1 ≤ k →
        (-1 : ℝ) ^ k / (((ξ.convergent (k - 1)).den : ℝ) ^ 2 *
          ((ξ.convergent (k - 1) : ℝ) - ξ)) = cut k) ∧
      nLagrangeApproximability 1 ξ = limsup (fun k => ((cut k : ℝ) : EReal)) atTop

/-- If two simple continued fractions agree in their initial terms `a₀, …, a_k`, their values differ
by at most `2^{1-k}`. Digits are those of Mathlib's `GenContFract.of` (`h = a₀`,
`partDens.get? i = a_{i+1}`).

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Lemma 5 (`integers-2025-A47-lem-5`), quoted from Cusick and Flahive, Lemma 1. -/
public theorem_wanted abs_sub_le_of_contFrac_prefix_eq (ξ ξ' : ℝ) (k : ℕ)
    (h0 : (GenContFract.of ξ).h = (GenContFract.of ξ').h)
    (hk : ∀ i < k, (GenContFract.of ξ).partDens.get? i = (GenContFract.of ξ').partDens.get? i) :
    |ξ - ξ'| ≤ 2 ^ (1 - (k : ℤ))

/-- For each `n ≥ 1` and irrationals `ξ ≠ ξ'`, `λₙ(ξ) = max_{g ∣ n} λ(gξ)` and
`μₙ(ξ, ξ') = max_{g ∣ n} μ(gξ, gξ')`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 6 (`integers-2025-A47-prop-6`). -/
public theorem_wanted nApproximability_eq_sup_divisors (n : ℕ) (hn : 1 ≤ n) (ξ ξ' : ℝ)
    (hξ : Irrational ξ) (hξ' : Irrational ξ') (hne : ξ ≠ ξ') :
    nLagrangeApproximability n ξ =
        n.divisors.sup (fun g => nLagrangeApproximability 1 (g * ξ)) ∧
      nMarkoffApproximability n ξ ξ' =
        n.divisors.sup (fun g => nMarkoffApproximability 1 (g * ξ) (g * ξ'))

/-- If `m ∣ n` then `Lₙ ⊆ L_m` and `Mₙ ⊆ M_m`; in particular `Lₙ ⊆ L` and `Mₙ ⊆ M`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Corollary 7 (`integers-2025-A47-cor-7`), equations (8) and (9). -/
public theorem_wanted nSpectrum_subset_of_dvd (m n : ℕ) (hm : 1 ≤ m) (hmn : m ∣ n) (hn : 1 ≤ n) :
    (nLagrangeSpectrum n ⊆ nLagrangeSpectrum m ∧ nMarkoffSpectrum n ⊆ nMarkoffSpectrum m) ∧
      nLagrangeSpectrum n ⊆ nLagrangeSpectrum 1 ∧ nMarkoffSpectrum n ⊆ nMarkoffSpectrum 1

/-- `Lₙ ⊆ Mₙ`, and every `α ∈ Lₙ` is `μₙ(ξ, ξ')` for some `ξ, ξ'` at which the supremum in the definition
of `μₙ` is attained.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 9 (`integers-2025-A47-prop-9`). -/
public theorem_wanted nLagrangeSpectrum_subset_nMarkoffSpectrum_attained (n : ℕ) (hn : 1 ≤ n) :
    nLagrangeSpectrum n ⊆ nMarkoffSpectrum n ∧
      ∀ α ∈ nLagrangeSpectrum n, ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧
        nMarkoffApproximability n ξ ξ' = α ∧
        ∃ s t : ℤ, (s, t) ≠ 0 ∧
          (((Int.gcd t n : ℝ) * |ξ - ξ'| / (|(s : ℝ) - t * ξ| * |(s : ℝ) - t * ξ'|) : ℝ) : EReal) = α

/-- Every `α ∈ Mₙ` is `μₙ(ξ, ξ')` for some `ξ, ξ'` at which the supremum is attained.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 10 (`integers-2025-A47-prop-10`). -/
public theorem_wanted nMarkoffSpectrum_attained (n : ℕ) (hn : 1 ≤ n) :
    ∀ α ∈ nMarkoffSpectrum n, ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧
      nMarkoffApproximability n ξ ξ' = α ∧
        ∃ s t : ℤ, (s, t) ≠ 0 ∧
          (((Int.gcd t n : ℝ) * |ξ - ξ'| / (|(s : ℝ) - t * ξ| * |(s : ℝ) - t * ξ'|) : ℝ) : EReal) = α

/-- `Mₙ` is closed.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 11 (`integers-2025-A47-prop-11`). -/
public theorem_wanted isClosed_nMarkoffSpectrum (n : ℕ) (hn : 1 ≤ n) :
    IsClosed (nMarkoffSpectrum n)

/-- `Lₙ` and `Mₙ` have a common minimum.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 12 (`integers-2025-A47-prop-12`). -/
public theorem_wanted exists_isLeast_nLagrangeSpectrum_nMarkoffSpectrum (n : ℕ) (hn : 1 ≤ n) :
    ∃ α : ℝ, IsLeast (nLagrangeSpectrum n) α ∧ IsLeast (nMarkoffSpectrum n) α

/-- `nL ⊆ Lₙ` and `nM ⊆ Mₙ`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 13 (`integers-2025-A47-prop-13`). -/
public theorem_wanted smul_spectrum_subset_nSpectrum (n : ℕ) (hn : 1 ≤ n) :
    (fun α => (n : ℝ) * α) '' nLagrangeSpectrum 1 ⊆ nLagrangeSpectrum n ∧
      (fun α => (n : ℝ) * α) '' nMarkoffSpectrum 1 ⊆ nMarkoffSpectrum n

/-- Hall's ray for the `n`-spectra: `[nF, ∞) ⊆ Lₙ ⊆ Mₙ`, where Freĭman's constant `F` is the least
`F` with `[F, ∞) ⊆ L`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 14 (`integers-2025-A47-prop-14`). -/
public theorem_wanted hall_ray_nLagrangeSpectrum (n : ℕ) (hn : 1 ≤ n) :
    Set.Ici ((n : ℝ) * sInf {F : ℝ | Set.Ici F ⊆ nLagrangeSpectrum 1}) ⊆ nLagrangeSpectrum n ∧
      nLagrangeSpectrum n ⊆ nMarkoffSpectrum n

/-- `Lₙ` is closed.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 19 (`integers-2025-A47-prop-19`). -/
public theorem_wanted isClosed_nLagrangeSpectrum (n : ℕ) (hn : 1 ≤ n) :
    IsClosed (nLagrangeSpectrum n)

/-- `Lₙ` is the closure of the set `Pₙ` of `n`-approximabilities of quadratic irrationals.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 20 (`integers-2025-A47-prop-20`). -/
public theorem_wanted nLagrangeSpectrum_eq_closure_quadratic (n : ℕ) (hn : 1 ≤ n) :
    nLagrangeSpectrum n = closure {α : ℝ | ∃ ξ : ℝ, Irrational ξ ∧
      (∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * ξ ^ 2 + b * ξ + c = 0) ∧
      nLagrangeApproximability n ξ = α}


/-- Conjecture 1 for primes below 2000: for every prime `p < 2000`, `L_p` has a least element `α`
that is an isolated point of `L_p` and is the irrational square root of a rational number.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Theorem 2 (`integers-2025-A47-thm-2`), with Conjecture 1. -/
public theorem_wanted min_nLagrangeSpectrum_isolated_sqrt_rat_of_prime_lt_2000 (p : ℕ)
    (hp : p.Prime) (hp2000 : p < 2000) :
    ∃ α : ℝ, IsLeast (nLagrangeSpectrum p) α ∧
      (∃ ε > 0, ∀ β ∈ nLagrangeSpectrum p, |β - α| < ε → β = α) ∧
      Irrational α ∧ ∃ r : ℚ, α = Real.sqrt r

/-- `p = 67` is the only prime `p < 2000` for which no irrational `ξ` has both `ξ` and `pξ` with
continued fraction digits eventually in `{1, 2}`. Digits are `a_k = ⌊ξ_k⌋` for the complete
quotients `ξ₀ = ξ`, `ξ_{k+1} = 1/{ξ_k}`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Theorem 3 (`integers-2025-A47-thm-3`). -/
public theorem_wanted no_eventually_one_two_contFrac_pair_iff_eq_67 (p : ℕ) (hp : p.Prime)
    (hp2000 : p < 2000) :
    (¬ ∃ ξ : ℝ, Irrational ξ ∧ ∀ᶠ k in atTop,
        ⌊(fun x : ℝ => (Int.fract x)⁻¹)^[k] ξ⌋ ∈ ({1, 2} : Set ℤ) ∧
          ⌊(fun x : ℝ => (Int.fract x)⁻¹)^[k] ((p : ℝ) * ξ)⌋ ∈ ({1, 2} : Set ℤ)) ↔
      p = 67

/-- Markoff points in `L_p`: for a Markoff triple `x ≤ y ≤ z` (`x² + y² + z² = 3xyz`) with
`λ_z = √(9 - 4/z²)` and `D = 9z² - 4` (`z` odd) or `(9z² - 4)/4` (`z` even), and a prime `p`:
(a) if `p` is the product of two principal primes of the quadratic order `O_D`, i.e. some
`u + v(D + √D)/2 ∈ O_D` has norm `±p`, then `λ_z ∈ L_p`; (b) conversely, if `λ_z ∈ L_p` and
`(9z² - 4)/(9z'² - 4)` is not a rational square for every other sorted Markoff triple
`(x', y', z')` with `z' ≤ z`, then `p` is such a product.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 26 (`integers-2025-A47-prop-26`); the printed `λ_p ∈ L_p` is read as `λ_z ∈ L_p`, as in
the proof. -/
public theorem_wanted markoff_point_mem_nLagrangeSpectrum_iff_principal_norm (x y z p : ℕ)
    (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z) (hM : x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z)
    (hp : p.Prime) :
    let D : ℤ := if z % 2 = 1 then 9 * (z : ℤ) ^ 2 - 4 else (9 * (z : ℤ) ^ 2 - 4) / 4
    let principalNorm : Prop :=
      ∃ u v : ℤ, |u ^ 2 + D * u * v + (D ^ 2 - D) / 4 * v ^ 2| = (p : ℤ)
    (principalNorm → Real.sqrt (9 - 4 / (z : ℝ) ^ 2) ∈ nLagrangeSpectrum p) ∧
      (Real.sqrt (9 - 4 / (z : ℝ) ^ 2) ∈ nLagrangeSpectrum p →
        (∀ x' y' z' : ℕ, 0 < x' → x' ≤ y' → y' ≤ z' →
          x' ^ 2 + y' ^ 2 + z' ^ 2 = 3 * x' * y' * z' → z' ≤ z → (x', y', z') ≠ (x, y, z) →
          ¬ IsSquare ((9 * (z : ℚ) ^ 2 - 4) / (9 * (z' : ℚ) ^ 2 - 4))) →
        principalNorm)

/-- Congruence conditions for the Markoff points `√5, 2√2, √221/5, √1517/13, √7565/29` in `L_p`,
`p` prime: (a) `√5 ∈ L_p ↔ p ≡ 0, ±1 (mod 5)`; (b) `2√2 ∈ L_p ↔ p ≡ 2, ±1 (mod 8)`;
(c) `√221/5 ∈ L_p ↔ p` is a square mod `13` and `17`; (d) `√1517/13 ∈ L_p ↔ p` is a square mod
`37` and `41`; (e) `√7565/29 ∈ L_p ↔ p` is a square mod `5`, `17` and `89`. "Square mod `m`" is
`IsSquare` in `ZMod m` (so `0` counts). Part (f) (`10√26/17`) is omitted: as printed it fails at
`p = 17`.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Corollary 27 (`integers-2025-A47-cor-27`). -/
public theorem_wanted markoff_points_mem_nLagrangeSpectrum_iff (p : ℕ) (hp : p.Prime) :
    (Real.sqrt 5 ∈ nLagrangeSpectrum p ↔ p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 4) ∧
      (2 * Real.sqrt 2 ∈ nLagrangeSpectrum p ↔ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 7) ∧
      (Real.sqrt 221 / 5 ∈ nLagrangeSpectrum p ↔
        IsSquare (p : ZMod 13) ∧ IsSquare (p : ZMod 17)) ∧
      (Real.sqrt 1517 / 13 ∈ nLagrangeSpectrum p ↔
        IsSquare (p : ZMod 37) ∧ IsSquare (p : ZMod 41)) ∧
      (Real.sqrt 7565 / 29 ∈ nLagrangeSpectrum p ↔
        IsSquare (p : ZMod 5) ∧ IsSquare (p : ZMod 17) ∧ IsSquare (p : ZMod 89))

end

end MetaMathlibExt
