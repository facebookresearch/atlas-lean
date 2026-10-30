/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

namespace MetaMathlibExt

@[expose] public noncomputable section

section LaurentContinuedFraction

variable {K : Type*} [Field K]

/-- The variable `x` of the field `𝔽_q((x⁻¹))` of formal Laurent series in `x⁻¹`, realized in
Mathlib's `LaurentSeries K` (series in `X = x⁻¹`) as `X⁻¹ = single (-1) 1`. A series
`∑ c_n Xⁿ` is `∑ c_n x⁻ⁿ`, so its degree valuation is `|α| = |x|^{-α.order}`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
def laurentInvVar (K : Type*) [Field K] : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) (1 : K)

/-- `x · x⁻¹ = 1` in `LaurentSeries K`, with `x = laurentInvVar K` and `x⁻¹ = single 1 1`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
theorem laurentInvVar_mul_single_one :
    laurentInvVar K * HahnSeries.single (1 : ℤ) (1 : K) = 1 := by
  simp [laurentInvVar, HahnSeries.single_mul_single]

/-- The embedding `𝔽_q[x] → 𝔽_q((x⁻¹))`, `x ↦ laurentInvVar K`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
def polyToLaurentInv (p : Polynomial K) : LaurentSeries K :=
  Polynomial.aeval (laurentInvVar K) p

/-- The polynomial `x` embeds as `laurentInvVar K`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Section 1. -/
theorem polyToLaurentInv_X : polyToLaurentInv (Polynomial.X : Polynomial K) = laurentInvVar K := by
  simp [polyToLaurentInv]

/-- The polynomial part `[α]` of `α ∈ 𝔽_q((x⁻¹))`: the terms `c_n x⁻ⁿ` with `n ≤ 0`, i.e. the
coefficients of `Xⁿ`, `n ≤ 0`, in `LaurentSeries K`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
def laurentPolyPart (α : LaurentSeries K) : LaurentSeries K where
  coeff n := if n ≤ 0 then α.coeff n else 0
  isPWO_support' := α.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn
    split_ifs at hn with h
    · exact hn
    · exact (hn rfl).elim

/-- Coefficients of the polynomial part.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
theorem laurentPolyPart_coeff (α : LaurentSeries K) (n : ℤ) :
    (laurentPolyPart α).coeff n = if n ≤ 0 then α.coeff n else 0 :=
  rfl

/-- The polynomial part of `x` is `x`, and that of `x⁻¹` is `0`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
theorem laurentPolyPart_laurentInvVar :
    laurentPolyPart (laurentInvVar K) = laurentInvVar K ∧
      laurentPolyPart (HahnSeries.single (1 : ℤ) (1 : K)) = 0 := by
  constructor
  · ext n
    simp only [laurentPolyPart_coeff, laurentInvVar, HahnSeries.coeff_single]
    split_ifs <;> first | rfl | omega
  · ext n
    simp only [laurentPolyPart_coeff, HahnSeries.coeff_single, HahnSeries.coeff_zero]
    split_ifs with h₁ h₂ <;> first | rfl | omega

/-- The complete quotients `α₀ = α`, `α_{n+1} = (α_n - [α_n])⁻¹` of the continued fraction
expansion of `α ∈ 𝔽_q((x⁻¹))` (they become `0` after a finite expansion ends).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
def laurentCompleteQuotient (α : LaurentSeries K) : ℕ → LaurentSeries K
  | 0 => α
  | n + 1 => (laurentCompleteQuotient α n - laurentPolyPart (laurentCompleteQuotient α n))⁻¹

/-- The partial quotients `b_n = [α_n]` of `α = [b₀, b₁, b₂, …]`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
def laurentPartialQuotient (α : LaurentSeries K) (n : ℕ) : LaurentSeries K :=
  laurentPolyPart (laurentCompleteQuotient α n)

/-- `b₀ = [α]` and `α₁ = (α - [α])⁻¹`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1, (1.3). -/
theorem laurentPartialQuotient_zero (α : LaurentSeries K) :
    laurentPartialQuotient α 0 = laurentPolyPart α ∧
      laurentCompleteQuotient α 1 = (α - laurentPolyPart α)⁻¹ :=
  ⟨rfl, rfl⟩

/-- `α` has bounded partial quotients: the degrees in `x` of all partial quotients are bounded,
i.e. some `B` has `(b_n).coeff m = 0` (coefficient of `x⁻ᵐ`) for all `n` and `m < -B`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def LaurentHasBoundedPartialQuotients (α : LaurentSeries K) : Prop :=
  ∃ B : ℤ, ∀ n : ℕ, ∀ m : ℤ, m < -B → (laurentPartialQuotient α n).coeff m = 0

/-- Numerators of the convergents, shifted by one: `laurentConvNum α (n + 1) = P_n`, with
`P_{-1} = 1`, `P₀ = b₀`, `P_{n+1} = b_{n+1} P_n + P_{n-1}`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def laurentConvNum (α : LaurentSeries K) : ℕ → LaurentSeries K
  | 0 => 1
  | 1 => laurentPartialQuotient α 0
  | n + 2 => laurentPartialQuotient α (n + 1) * laurentConvNum α (n + 1) + laurentConvNum α n

/-- Denominators of the convergents, shifted by one: `laurentConvDen α (n + 1) = Q_n`, with
`Q_{-1} = 0`, `Q₀ = 1`, `Q_{n+1} = b_{n+1} Q_n + Q_{n-1}`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def laurentConvDen (α : LaurentSeries K) : ℕ → LaurentSeries K
  | 0 => 0
  | 1 => 1
  | n + 2 => laurentPartialQuotient α (n + 1) * laurentConvDen α (n + 1) + laurentConvDen α n

/-- The recursions of the convergents: `P₁ = b₁ b₀ + 1` and `Q₁ = b₁`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
theorem laurentConv_two (α : LaurentSeries K) :
    laurentConvNum α 2 = laurentPartialQuotient α 1 * laurentPartialQuotient α 0 + 1 ∧
      laurentConvDen α 2 = laurentPartialQuotient α 1 := by
  simp [laurentConvNum, laurentConvDen]

/-- `α ∈ 𝔽_q((x⁻¹))` is irrational: `Q α ≠ P` for all polynomials `P` and `Q ≠ 0`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
def LaurentIsIrrational (α : LaurentSeries K) : Prop :=
  ∀ P Q : Polynomial K, Q ≠ 0 → polyToLaurentInv Q * α ≠ polyToLaurentInv P

/-- Polynomials are not irrational.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Section 1. -/
theorem not_laurentIsIrrational_polyToLaurentInv (P : Polynomial K) :
    ¬ LaurentIsIrrational (polyToLaurentInv P) := fun h =>
  h P 1 one_ne_zero (by simp [polyToLaurentInv])

/-- Baum–Sweet: a root `f ∈ 𝔽₂((x⁻¹))` of `f³ + p⁻¹ f + 1 = 0`, `p ∈ 𝔽₂[x]`, `deg p ≥ 1`, has
bounded partial quotients (quoted result).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 1 (quoting Baum and Sweet, Corollary 3) (`integers-2026-A57-thm-1`). -/
public theorem_wanted baumSweet_cubic_boundedPartialQuotients (p : Polynomial (ZMod 2))
    (hp : 1 ≤ p.natDegree) (f : LaurentSeries (ZMod 2))
    (hf : f ^ 3 + (polyToLaurentInv p)⁻¹ * f + 1 = 0) :
    LaurentHasBoundedPartialQuotients f

/-- Baum–Sweet: if `f ∈ 𝔽₂((x⁻¹))` satisfies `f^{2ⁿ+1} + g⁻¹ f + 1 = 0` with `n > 1`,
`g ∈ 𝔽₂[x]`, `deg g ≥ 1`, then `f` has unbounded partial quotients (quoted result).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 2 (quoting Baum and Sweet, Theorem 5) (`integers-2026-A57-thm-2`). -/
public theorem_wanted baumSweet_unboundedPartialQuotients (n : ℕ) (hn : 1 < n)
    (g : Polynomial (ZMod 2)) (hg : 1 ≤ g.natDegree) (f : LaurentSeries (ZMod 2))
    (hf : f ^ (2 ^ n + 1) + (polyToLaurentInv g)⁻¹ * f + 1 = 0) :
    ¬ LaurentHasBoundedPartialQuotients f

/-- Baum–Sweet: for `n ≥ 0` and `P, Q ∈ 𝔽₂[x]` with `P + Q^{2ⁿ} ∉ {0, 1}`, the equation
`f^{2ⁿ+1} + Q f^{2ⁿ} + P f + Q P + 1 = 0` has a root `f ∈ 𝔽₂((x⁻¹))` with continued fraction
`[Q; P + Q^{2ⁿ}, P^{2ⁿ} + Q^{2^{2n}}, P^{2^{2n}} + Q^{2^{3n}}, …]`, i.e. `b₀ = Q` and
`b_k = P^{2^{(k-1)n}} + Q^{2^{kn}}` for `k ≥ 1`. The paper also claims the root is unique; that
part is omitted: for `n = 0`, `P = x`, `Q = 0` the equation `f (f + x) = 1` has the two roots
`[0; x, x, …]` and `[x; x, x, …]`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 3 (quoting Baum and Sweet) (`integers-2026-A57-thm-3`). -/
public theorem_wanted baumSweet_exists_root_continuedFraction (n : ℕ)
    (P Q : Polynomial (ZMod 2)) (h0 : P + Q ^ (2 ^ n) ≠ 0) (h1 : P + Q ^ (2 ^ n) ≠ 1) :
    ∃ f : LaurentSeries (ZMod 2),
      f ^ (2 ^ n + 1) + polyToLaurentInv Q * f ^ (2 ^ n) + polyToLaurentInv P * f +
          polyToLaurentInv Q * polyToLaurentInv P + 1 = 0 ∧
        laurentPartialQuotient f 0 = polyToLaurentInv Q ∧
        ∀ k, 1 ≤ k → laurentPartialQuotient f k =
          polyToLaurentInv (P ^ (2 ^ ((k - 1) * n)) + Q ^ (2 ^ (k * n)))

/-- Standard properties of the convergents `P_n / Q_n` of an irrational `α ∈ 𝔽_q((x⁻¹))`
(`P_n = laurentConvNum α (n + 1)`, `Q_n = laurentConvDen α (n + 1)`, `|y| = |x|^{-y.order}`):
(i) `(β P_n + P_{n-1}) / (β Q_n + Q_{n-1}) = [b₀, …, b_n, β]` for `β ≠ 0` whose tails
`[b_k, …, b_n, β]` (`1 ≤ k ≤ n`) are nonzero (with the totalized inverse `0⁻¹ = 0` the fold
otherwise disagrees: `n = 2`, `β = -b₂⁻¹` gives `b₀` on the left and `b₀ + b₁⁻¹` on the right);
(ii) `P_n Q_{n-1} - P_{n-1} Q_n = (-1)^{n-1}`; (iii) `|Q_n| > |Q_{n-1}| > 0`;
(iv) `|Q_n| = |b₁ ⋯ b_n|`; (v) `|α - P_n/Q_n| = 1 / (|b_{n+1}| |Q_n|²)`;
(vi) `|Q_{n+1} α - P_{n+1}| < |Q_n α - P_n|`. Parts (iii)–(vi) are stated for `n ≥ 1` (the paper
puts `n ≥ 1` on (iv)–(vi); (iii) fails at `n = 0` because `Q_{-1} = 0`).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 1 (`integers-2026-A57-lem-1`). -/
public theorem_wanted laurentConvergent_properties (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) :
    (∀ n : ℕ, ∀ β : LaurentSeries K, β ≠ 0 →
        (∀ k, 1 ≤ k → k ≤ n → ((List.range' k (n + 1 - k)).map (laurentPartialQuotient α)).foldr
          (fun b t => b + t⁻¹) β ≠ 0) →
        (β * laurentConvNum α (n + 1) + laurentConvNum α n) /
            (β * laurentConvDen α (n + 1) + laurentConvDen α n) =
          ((List.range (n + 1)).map (laurentPartialQuotient α)).foldr (fun b t => b + t⁻¹) β) ∧
      (∀ n : ℕ, laurentConvNum α (n + 1) * laurentConvDen α n -
          laurentConvNum α n * laurentConvDen α (n + 1) = (-1) ^ (n + 1)) ∧
      (∀ n : ℕ, 1 ≤ n → laurentConvDen α n ≠ 0 ∧
          (laurentConvDen α (n + 1)).order < (laurentConvDen α n).order) ∧
      (∀ n : ℕ, 1 ≤ n → (laurentConvDen α (n + 1)).order =
          ∑ i ∈ Finset.Icc 1 n, (laurentPartialQuotient α i).order) ∧
      (∀ n : ℕ, 1 ≤ n → (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order =
          -(laurentPartialQuotient α (n + 1)).order - 2 * (laurentConvDen α (n + 1)).order) ∧
      (∀ n : ℕ, 1 ≤ n → (laurentConvDen α (n + 1) * α - laurentConvNum α (n + 1)).order <
          (laurentConvDen α (n + 2) * α - laurentConvNum α (n + 2)).order)

/-- Frobenius and continued fractions: over `𝔽_q` the continued fraction of `α^q` is
`[b₀^q, b₁^q, …]` and its convergents are `P_n^q / Q_n^q`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 2 (`integers-2026-A57-lem-2`). -/
public theorem_wanted laurentPartialQuotient_pow_card [Fintype K] (α : LaurentSeries K) (n : ℕ) :
    laurentPartialQuotient (α ^ Fintype.card K) n =
        laurentPartialQuotient α n ^ Fintype.card K ∧
      laurentConvNum (α ^ Fintype.card K) n = laurentConvNum α n ^ Fintype.card K ∧
      laurentConvDen (α ^ Fintype.card K) n = laurentConvDen α n ^ Fintype.card K

/-- Let `α` be irrational and `P, Q ∈ 𝔽_q[x]` coprime, `Q ≠ 0`. (i) If
`|Q α - P| = |x|^{-s} |Q|^{-1}` for some `s ≥ 1`, then `P = c P_n` and `Q = c Q_n` for some
`n ≥ 0` and `c ∈ 𝔽_q \ {0}`, and `|b_{n+1}| = |x|^s`. (ii) If `|Q α - P| = |Q|^{-1}`, then
`P = c P_n + d P_{n-1}` and `Q = c Q_n + d Q_{n-1}` for some `n ≥ 0` and `c, d ∈ 𝔽_q \ {0}`.
Degrees are written with `order` (`|y| = |x|^{-y.order}`, `|Q| = |x|^{deg Q}`).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 3 (generalizing Baum and Sweet, Lemma 1) (`integers-2026-A57-lem-3`). -/
public theorem_wanted laurent_eq_convergent_of_order (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0) :
    (∀ s : ℕ, 1 ≤ s →
        (polyToLaurentInv Q * α - polyToLaurentInv P).order = s + Q.natDegree →
        ∃ (n : ℕ) (c : K), c ≠ 0 ∧
          polyToLaurentInv P = HahnSeries.C c * laurentConvNum α (n + 1) ∧
          polyToLaurentInv Q = HahnSeries.C c * laurentConvDen α (n + 1) ∧
          (laurentPartialQuotient α (n + 1)).order = -(s : ℤ)) ∧
      ((polyToLaurentInv Q * α - polyToLaurentInv P).order = Q.natDegree →
        ∃ (n : ℕ) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧
          polyToLaurentInv P =
            HahnSeries.C c * laurentConvNum α (n + 1) + HahnSeries.C d * laurentConvNum α n ∧
          polyToLaurentInv Q =
            HahnSeries.C c * laurentConvDen α (n + 1) + HahnSeries.C d * laurentConvDen α n)

/-- Let `α` be irrational with convergents `P_n / Q_n`. (i) If `|α| ≥ 1`, then
`|α - P_n/Q_n| < |α|` for all `n ≥ 0`. (ii) If `|α| < 1`, then `|α - P₀/Q₀| = |α|` and
`|α - P_n/Q_n| < |α|` for all `n ≥ 1` (`|y| = |x|^{-y.order}`).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 4 (`integers-2026-A57-lem-4`). -/
public theorem_wanted laurent_sub_convergent_order (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) :
    (α.order ≤ 0 → ∀ n : ℕ,
        α.order < (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order) ∧
      (0 < α.order →
        (α - laurentConvNum α 1 / laurentConvDen α 1).order = α.order ∧
          ∀ n : ℕ, 1 ≤ n →
            α.order < (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order)

/-- Lasjaunias's lemma: let `α ∈ 𝔽_q((x⁻¹))` be irrational with `α = (A α^q + B)/(C α^q + D)`,
`A, B, C, D ∈ 𝔽_q[x]`, `Δ = AD - BC ≠ 0`, `C ≠ 0`. If `P/Q = P_n/Q_n` is a convergent in lowest
terms with `|α - P/Q| < |α - A/C|`, and, writing `R₁ = DP - BQ`, `S₁ = -CP + AQ`,
`δ₁ = gcd(R₁, S₁)`, `R₁' = R₁/δ₁`, `S₁' = S₁/δ₁`, one of `R₁'`, `S₁'` is not a `q`-th power in
`𝔽_q[x]`, then the next partial quotient satisfies `|b_{n+1}| < |Δ| |δ₁|^{-2}`. The hypothesis
`C ≠ 0` makes `A/C` meaningful (implicit in the paper).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 5 (quoting Lasjaunias, Lemma 1) (`integers-2026-A57-lem-5`). -/
public theorem_wanted lasjaunias_partialQuotient_bound [Fintype K] [DecidableEq K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1))
    (hclose : (α - polyToLaurentInv A / polyToLaurentInv C).order <
      (α - polyToLaurentInv P / polyToLaurentInv Q).order)
    (hpow : (¬ ∃ T : Polynomial K,
        (D * P - B * Q) / gcd (D * P - B * Q) (-C * P + A * Q) = T ^ Fintype.card K) ∨
      ¬ ∃ T : Polynomial K,
        (-C * P + A * Q) / gcd (D * P - B * Q) (-C * P + A * Q) = T ^ Fintype.card K) :
    -(laurentPartialQuotient α (n + 1)).order <
      ((A * D - B * C).natDegree : ℤ) - 2 * (gcd (D * P - B * Q) (-C * P + A * Q)).natDegree

/-- Let `α ∈ 𝔽_q((x⁻¹))` be irrational with `α = f(α^q)`, `f(T) = (AT + B)/(CT + D)`,
`Δ = AD - BC ≠ 0`, and let `P, Q ∈ 𝔽_q[x]`, `Q ≠ 0`, with `R₁ = DP - BQ`, `S₁ = -CP + AQ`,
`R₂ = AP^q + BQ^q`, `S₂ = CP^q + DQ^q`, `S₁ ≠ 0`, `S₂ ≠ 0` (for `C ≠ 0` these say
`P/Q ≠ A/C` and `(P/Q)^q ≠ -D/C`). Then
`α^q - R₁/S₁ = Δ (Qα - P) / ((A - Cα) S₁)` and `α - R₂/S₂ = Δ (Qα - P)^q / ((Cα^q + D) S₂)`
(equations (3.4) and (3.5); their middle expressions `f⁻¹(α) - f⁻¹(P/Q)` and
`f(α^q) - f((P/Q)^q)` are omitted). The hypotheses `gcd(A, B, C, D) = 1` and that `P/Q` is a
convergent in lowest terms are dropped as unused by the identities.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 6 (`integers-2026-A57-lem-6`). -/
public theorem_wanted laurentMobius_sub_identities [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (hQ : Q ≠ 0) (hS₁ : -C * P + A * Q ≠ 0)
    (hS₂ : C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0) :
    α ^ Fintype.card K - polyToLaurentInv (D * P - B * Q) / polyToLaurentInv (-C * P + A * Q) =
        polyToLaurentInv (A * D - B * C) * (polyToLaurentInv Q * α - polyToLaurentInv P) /
          ((polyToLaurentInv A - polyToLaurentInv C * α) * polyToLaurentInv (-C * P + A * Q)) ∧
      α - polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K) /
          polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) =
        polyToLaurentInv (A * D - B * C) *
            (polyToLaurentInv Q * α - polyToLaurentInv P) ^ Fintype.card K /
          ((polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D) *
            polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K))

/-- In the setting of Lemma 6, with `P/Q = P_n/Q_n` a convergent in lowest terms and
`b_α(P, Q) = b_{n+1}` the next partial quotient: (i) if `|α - P/Q| < |α - A/C|`, then
`|S₁ α^q - R₁| = |Δ| |b_{n+1}|^{-1} |S₁|^{-1}`; (ii) if `|α - P/Q| < |α^q + D/C|^{1/q}`, then
`|S₂ α - R₂| = |Δ| |b_{n+1}|^{-q} |S₂|^{-1}` (degrees via `order`, `|y| = |x|^{-y.order}`). The
hypothesis `C ≠ 0` makes `A/C`, `D/C` meaningful (implicit in the paper).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 7, (3.7) and (3.8) (`integers-2026-A57-lem-7`). -/
public theorem_wanted laurentMobius_order_identities [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1)) :
    ((α - polyToLaurentInv A / polyToLaurentInv C).order <
        (α - polyToLaurentInv P / polyToLaurentInv Q).order →
      (polyToLaurentInv (-C * P + A * Q) * α ^ Fintype.card K -
          polyToLaurentInv (D * P - B * Q)).order =
        ((-C * P + A * Q).natDegree : ℤ) - (A * D - B * C).natDegree -
          (laurentPartialQuotient α (n + 1)).order) ∧
      ((α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
          Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order →
        (polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) * α -
            polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K)).order =
          ((C * P ^ Fintype.card K + D * Q ^ Fintype.card K).natDegree : ℤ) -
            (A * D - B * C).natDegree -
            Fintype.card K * (laurentPartialQuotient α (n + 1)).order)

/-- Lasjaunias's criterion: let `α` be irrational with `α = (A α^q + B)/(C α^q + D)`,
`Δ = AD - BC ≠ 0`, `C ≠ 0`. If some convergent `P/Q = P_n/Q_n` in lowest terms lies in
`F = {P/Q : |α - P/Q| < |α^q + D/C|^{1/q}}` and satisfies
`|α - P/Q| < |Δ|^{1/(q-1)} |C α^q + D|^{2/(q-1)}` and `|b_{n+1}| > |Δ|^{1/(q-1)}`, then `α` has
unbounded partial quotients. Fractional exponents are cleared by multiplying the logarithmic
(degree) inequalities by `q` or `q - 1`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 8 (quoting Lasjaunias) (`integers-2026-A57-lem-8`). -/
public theorem_wanted lasjaunias_unbounded_criterion [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1))
    (hF : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
      Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order)
    (h₁ : -((Fintype.card K : ℤ) - 1) * (α - polyToLaurentInv P / polyToLaurentInv Q).order <
      ((A * D - B * C).natDegree : ℤ) -
        2 * (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D).order)
    (h₂ : ((A * D - B * C).natDegree : ℤ) <
      -((Fintype.card K : ℤ) - 1) * (laurentPartialQuotient α (n + 1)).order) :
    ¬ LaurentHasBoundedPartialQuotients α

/-- Ayadi et al.: over `𝔽₂`, a root `α` of positive degree of `C T³ + A T² + 1 = 0` with
`C = x^ℓ`, `ℓ ≥ 2`, and `A = x^{2ℓ} + ∑_{i=2}^{2ℓ-1} e_i x^i + x + 1` has bounded partial quotients
(`A` is any polynomial of degree `2ℓ` with constant and linear coefficients `1`; positive degree is
`α.order < 0`).

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Corollary 1 (`integers-2026-A57-cor-1`). -/
public theorem_wanted ayadi_cubic_boundedPartialQuotients (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (A : Polynomial (ZMod 2)) (hA : A.natDegree = 2 * ℓ) (hA₁ : A.coeff 1 = 1)
    (hA₀ : A.coeff 0 = 1) (α : LaurentSeries (ZMod 2)) (hdeg : α.order < 0)
    (hroot : laurentInvVar (ZMod 2) ^ ℓ * α ^ 3 + polyToLaurentInv A * α ^ 2 + 1 = 0) :
    LaurentHasBoundedPartialQuotients α

/-- Over `𝔽₂`, a root `α` of the irreducible equation `x T³ + T + x = 0` has bounded partial
quotients, all of degree at most `2`.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Corollary 2 (`integers-2026-A57-cor-2`). -/
public theorem_wanted baumSweet_x_cubic_partialQuotient_degree_le_two
    (α : LaurentSeries (ZMod 2))
    (hroot : laurentInvVar (ZMod 2) * α ^ 3 + α + laurentInvVar (ZMod 2) = 0) :
    ∀ n : ℕ, ∀ m : ℤ, m < -2 → (laurentPartialQuotient α n).coeff m = 0

/-- Let `α ∈ 𝔽_q((x⁻¹))` be an irrational root of `x T^{q+1} + D T + x^ℓ = 0` with `ℓ ≥ 1` and
`D ∈ 𝔽_q[x]`, `D(0) ≠ 0`. If `|α| < |x|^{-((q-1)ℓ+1)}` (i.e. `α.order > (q - 1)ℓ + 1`), then `α`
has unbounded partial quotients.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Theorem 6 (`integers-2026-A57-thm-6`). -/
public theorem_wanted lasjaunias_unboundedPartialQuotients_of_small [Fintype K] (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (D : Polynomial K) (hD : D.coeff 0 ≠ 0) (α : LaurentSeries K)
    (hα : LaurentIsIrrational α)
    (hroot : laurentInvVar K * α ^ (Fintype.card K + 1) + polyToLaurentInv D * α +
      laurentInvVar K ^ ℓ = 0)
    (hsmall : ((Fintype.card K : ℤ) - 1) * ℓ + 1 < α.order) :
    ¬ LaurentHasBoundedPartialQuotients α

end LaurentContinuedFraction

end

end MetaMathlibExt
