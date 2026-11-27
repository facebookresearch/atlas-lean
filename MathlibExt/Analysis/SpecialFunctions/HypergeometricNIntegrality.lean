/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.GeneralizedHypergeometric
public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Tactic

/-!
# Integrality of rational hypergeometric coefficients

For multisets `α β` of rational parameters, the
Delaygue–Rivoal–Roques coefficient is the Pochhammer ratio
`∏ (αᵢ)ₙ / ∏ (βⱼ)ₙ` over `ℚ`, with no `1 / n!` factor.  This file
defines that coefficient, Christol's ordering and counting functions,
`N`-integrality (integrality after a positive rational rescaling), and
the explicit scaling term in the Delaygue–Rivoal–Roques formula for
the least rescaling.  Christol's criterion and the scaling formula
themselves are recorded as wanted results; see
`WantedExt.Analysis.SpecialFunctions.ChristolHypergeometricIntegralityWanted`.

Conventions follow E. Delaygue, T. Rivoal and J. Roques, *On Dwork's
`p`-adic formal congruences theorem and hypergeometric mirror maps*,
Mem. Amer. Math. Soc. 246 (2017), §2.1.  Two points in the source need
care.  First, its phrase "there exists `c ∈ ℚ`" for `N`-integrality
cannot include `c = 0`, which trivialises the notion; the source's
least constant is taken over positive rationals, and `NIntegral` here
requires `0 < C`.  Second, the source defines
`λₚ = #{i : αᵢ ∈ ℤₚ} - #{j : βⱼ ∈ ℤₚ}`; for a rational number `t`,
membership in `ℤₚ` is equivalent to `p ∤ t.den`, which is the form
used in `lambda`.

## Main definitions

* `pochhammerCoeff`: the coefficient `∏ (αᵢ)ₙ / ∏ (βⱼ)ₙ` over `ℚ`.
* `AdmissibleParams`: no parameter lies in `ℤ_{≤ 0}`.
* `modFract`: the modified fractional part, with values in `(0, 1]`.
* `ChristolLE`: Christol's order on `ℝ`.
* `paramDenLcm`: the least common multiple of the parameter
  denominators.
* `christolXi`: Christol's counting function `ξ_{α,β}(a, x)`.
* `GoodScaling`, `NIntegral`: integrality after rescaling.
* `lambda`, `exceptionalPrimes`, `baseConstant`: the explicit term in
  the least-scaling formula.

## References

* E. Delaygue, T. Rivoal, J. Roques, *On Dwork's `p`-adic formal
  congruences theorem and hypergeometric mirror maps*, Mem. Amer.
  Math. Soc. **246** (2017), no. 1163, §2.1.
* G. Christol, *Fonctions hypergéométriques bornées*, Groupe de
  Travail d'Analyse Ultramétrique **14** (1986–1987), exp. 8, 1–16.
-/

@[expose] public section

namespace MetaMathlibExt.HypergeometricNIntegrality

/-- The Delaygue–Rivoal–Roques hypergeometric coefficient
`∏ (αᵢ)ₙ / ∏ (βⱼ)ₙ` over `ℚ`, where `(x)ₙ` is the ascending
Pochhammer symbol.  There is no `1 / n!` factor; see
`pochhammerCoeff_eq_generalizedHypergeometricCoefficient` for the
relation to `generalizedHypergeometricCoefficient`.  Division is the
totalised field division, so the value is `0` if a lower Pochhammer
product vanishes; under `AdmissibleParams β` that cannot happen. -/
noncomputable def pochhammerCoeff (α β : Multiset ℚ) (n : ℕ) : ℚ :=
  (α.map fun t => (ascPochhammer ℚ n).eval t).prod /
    (β.map fun t => (ascPochhammer ℚ n).eval t).prod

/-- A multiset of rational parameters is admissible when none of its
elements lies in `ℤ_{≤ 0}`, the parameter domain
`ℚ \ ℤ_{≤ 0}` of Delaygue–Rivoal–Roques, §2. -/
def AdmissibleParams (γ : Multiset ℚ) : Prop :=
  ∀ t ∈ γ, ∀ k : ℕ, t ≠ -(k : ℚ)

theorem ascPochhammer_eval_ne_zero_of_ne_neg_natCast {t : ℚ}
    (ht : ∀ k : ℕ, t ≠ -(k : ℚ)) (n : ℕ) :
    (ascPochhammer ℚ n).eval t ≠ 0 := by
  intro h0
  obtain ⟨k, -, h⟩ := (ascPochhammer_eval_eq_zero_iff n t).mp h0
  exact ht k (by linarith)

theorem pochhammerCoeff_eq_generalizedHypergeometricCoefficient
    (α β : Multiset ℚ) (n : ℕ) :
    pochhammerCoeff α β n =
      MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient
        (1 ::ₘ α) β n := by
  have hfact : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient_cons_upper,
    ascPochhammer_eval_one]
  unfold pochhammerCoeff
    MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient
  rw [div_eq_mul_inv, mul_assoc ((n.factorial : ℚ))⁻¹ _ _, mul_inv_cancel_left₀ hfact]

@[simp]
theorem pochhammerCoeff_zero (α β : Multiset ℚ) :
    pochhammerCoeff α β 0 = 1 := by
  simp [pochhammerCoeff]

/-- The modified fractional part `⟨x⟩`, the unique element of
`(0, 1]` with `x - ⟨x⟩ ∈ ℤ`.  It agrees with `Int.fract x` except
that integers map to `1`, not `0`. -/
noncomputable def modFract (x : ℝ) : ℝ :=
  if Int.fract x = 0 then 1 else Int.fract x

theorem modFract_mem_Ioc (x : ℝ) : 0 < modFract x ∧ modFract x ≤ 1 := by
  unfold modFract
  split_ifs with h
  · exact ⟨one_pos, le_refl 1⟩
  · exact ⟨lt_of_le_of_ne (Int.fract_nonneg x) (fun hh => h hh.symm),
      (Int.fract_lt_one x).le⟩

theorem modFract_eq_one_iff {x : ℝ} :
    modFract x = 1 ↔ ∃ z : ℤ, x = (z : ℝ) := by
  by_cases h : Int.fract x = 0
  · rw [modFract, ite_eq_left h]
    constructor
    · intro _
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h
      exact ⟨z, hz.symm⟩
    · intro _
      rfl
  · rw [modFract, ite_eq_right h]
    constructor
    · intro h1
      exfalso
      linarith [Int.fract_lt_one x]
    · rintro ⟨z, rfl⟩
      exact absurd (Int.fract_eq_zero_iff.mpr ⟨z, rfl⟩) h

theorem exists_int_eq_sub_modFract (x : ℝ) :
    ∃ z : ℤ, x - modFract x = (z : ℝ) := by
  by_cases h : Int.fract x = 0
  · refine ⟨⌊x⌋ - 1, ?_⟩
    rw [modFract, ite_eq_left h, Int.cast_sub, Int.cast_one, ← Int.self_sub_fract x, h]
    ring
  · exact ⟨⌊x⌋, by rw [modFract, ite_eq_right h, Int.self_sub_fract]⟩

/-- Christol's order `≼` on `ℝ`: `x ≼ y` when `⟨x⟩ < ⟨y⟩`, or
`⟨x⟩ = ⟨y⟩` and `x ≥ y`.  Equal modified fractional parts are thus
ordered by decreasing value. -/
def ChristolLE (x y : ℝ) : Prop :=
  modFract x < modFract y ∨ (modFract x = modFract y ∧ y ≤ x)

theorem christolLE_refl (x : ℝ) : ChristolLE x x :=
  Or.inr ⟨rfl, le_refl x⟩

noncomputable instance (x y : ℝ) : Decidable (ChristolLE x y) :=
  Classical.propDecidable _

private theorem lcm_pos_of_forall_pos {s : Multiset ℕ}
    (h : ∀ a ∈ s, 0 < a) : 0 < s.lcm := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.lcm_cons]
    exact Nat.lcm_pos_iff.mpr ⟨h a (by simp), ih (fun b hb => h b (by simp [hb]))⟩

/-- The least common multiple `d_{α,β}` of the exact denominators of
the parameters in `α` and `β`. -/
noncomputable def paramDenLcm (α β : Multiset ℚ) : ℕ :=
  ((α + β).map Rat.den).lcm

theorem paramDenLcm_pos (α β : Multiset ℚ) : 0 < paramDenLcm α β := by
  apply lcm_pos_of_forall_pos
  intro a ha
  obtain ⟨t, -, rfl⟩ := Multiset.mem_map.mp ha
  exact Rat.den_pos t

/-- Christol's counting function
`ξ_{α,β}(a, x) = #{i : a αᵢ ≼ x} - #{j : a βⱼ ≼ x}`, with
multiplicities counted. -/
noncomputable def christolXi (α β : Multiset ℚ) (a : ℕ) (x : ℝ) : ℤ :=
  ((α.filter fun t : ℚ => ChristolLE ((a : ℝ) * (t : ℝ)) x).card : ℤ) -
    ((β.filter fun t : ℚ => ChristolLE ((a : ℝ) * (t : ℝ)) x).card : ℤ)

/-- A rational number `C` is a good scaling for `(α, β)` when every
rescaled coefficient `C ^ n * ∏ (αᵢ)ₙ / ∏ (βⱼ)ₙ` is an integer.
Note `C = 0` always satisfies this; the rescalings of interest are
the positive ones, as in `NIntegral`. -/
def GoodScaling (α β : Multiset ℚ) (C : ℚ) : Prop :=
  ∀ n : ℕ, ∃ m : ℤ, C ^ n * pochhammerCoeff α β n = (m : ℚ)

/-- `N`-integrality of the hypergeometric series with coefficients
`pochhammerCoeff α β`: some positive rational rescaling makes every
coefficient an integer.  Positivity is essential; with `C = 0`
allowed the condition would be vacuous. -/
def NIntegral (α β : Multiset ℚ) : Prop :=
  ∃ C : ℚ, 0 < C ∧ GoodScaling α β C

/-- The count `λₚ = #{i : p ∤ den αᵢ} - #{j : p ∤ den βⱼ}`.  For a
rational number `t`, `p ∤ t.den` is equivalent to `t ∈ ℤₚ`, which is
the form used by Delaygue–Rivoal–Roques, §2.1. -/
noncomputable def lambda (α β : Multiset ℚ) (p : ℕ) : ℤ :=
  ((α.filter fun t => ¬ p ∣ t.den).card : ℤ) -
    ((β.filter fun t => ¬ p ∣ t.den).card : ℤ)

/-- The finite set of exceptional primes in the least-scaling
formula: the primes dividing `d_{α,β}`, together with the primes
`p ≤ r - s + 1` (written without integer subtraction as
`p + s ≤ r + 1`).  The divisor branch uses `Nat.primeFactors`
rather than enumerating up to `d_{α,β}`, which can be enormous. -/
noncomputable def exceptionalPrimes (α β : Multiset ℚ) : Finset ℕ :=
  (paramDenLcm α β).primeFactors ∪
    (Finset.Icc 2 (α.card + 1)).filter
      (fun p => p.Prime ∧ p + β.card ≤ α.card + 1)

theorem mem_exceptionalPrimes {α β : Multiset ℚ} {p : ℕ} :
    p ∈ exceptionalPrimes α β ↔
      p.Prime ∧ (p ∣ paramDenLcm α β ∨ p + β.card ≤ α.card + 1) := by
  have hd : 0 < paramDenLcm α β := paramDenLcm_pos α β
  unfold exceptionalPrimes
  rw [Finset.mem_union, Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro (⟨hp, hdvd, -⟩ | ⟨-, hp, h⟩)
    · exact ⟨hp, Or.inl hdvd⟩
    · exact ⟨hp, Or.inr h⟩
  · rintro ⟨hp, hdvd | hle⟩
    · exact Or.inl ⟨hp, hdvd, by omega⟩
    · exact Or.inr ⟨⟨hp.two_le, by omega⟩, hp, hle⟩

/-- The explicit term in the Delaygue–Rivoal–Roques least-scaling
formula (Theorem 4):
`(∏ den αᵢ / ∏ den βⱼ) * ∏_{p} p ^ (-⌊λₚ / (p - 1)⌋)`, the product
running over `exceptionalPrimes α β`.  The quotient
`lambda α β p / (p - 1)` is integer (floor) division. -/
noncomputable def baseConstant (α β : Multiset ℚ) : ℚ :=
  (α.map fun t => (t.den : ℚ)).prod / (β.map fun t => (t.den : ℚ)).prod *
    ∏ p ∈ exceptionalPrimes α β, (p : ℚ) ^ (-(lambda α β p / ((p : ℤ) - 1)))

theorem baseConstant_pos (α β : Multiset ℚ) : 0 < baseConstant α β := by
  unfold baseConstant
  apply mul_pos
  · apply div_pos <;>
      · apply Multiset.prod_pos
        intro a ha
        obtain ⟨t, -, rfl⟩ := Multiset.mem_map.mp ha
        exact Nat.cast_pos.mpr (Rat.den_pos t)
  · apply Finset.prod_pos
    intro p hp
    exact zpow_pos (Nat.cast_pos.mpr (mem_exceptionalPrimes.mp hp).1.pos) _

end MetaMathlibExt.HypergeometricNIntegrality
