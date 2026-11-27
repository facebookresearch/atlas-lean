/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# The minimal discriminant of an elliptic curve over a number field

Let `L` be a number field and `W` a Weierstrass curve over `L` with nonzero discriminant
(`[W.IsElliptic]`). For a finite place `v` of `L` (a maximal ideal `𝔭` of `𝓞 L`), a Weierstrass
equation is *integral at `𝔭`* if `ord_𝔭(a_i) ≥ 0` for its coefficients, and `δ_𝔭(W)` is the least
`ord_𝔭(Δ)` among the equations `C • W` integral at `𝔭`, over all variable changes `C`. The
*minimal discriminant* is the ideal `Δ_{W/L} = ∏_𝔭 𝔭 ^ δ_𝔭(W)` of `𝓞 L`.

## Main definitions

* `WeierstrassCurve.IsIntegralAt`, `WeierstrassCurve.minimalDiscriminantOrd`,
  `WeierstrassCurve.minimalDiscriminant`.
* `WeierstrassCurve.isIntegralAt_iff_isIntegral`: integrality at `v` is Mathlib's
  `WeierstrassCurve.IsIntegral` over the valuation ring of `v`.

## Main results

* `WeierstrassCurve.exists_variableChange_isIntegralAt_forall`: there is a nonzero `c ∈ 𝓞 L`
  such that the variable change `x = c⁻² x'`, `y = c⁻³ y'` makes the equation integral at
  every `𝔭`.
* For `Δ_W ≠ 0`: `WeierstrassCurve.exists_minimalDiscriminantOrd` and
  `WeierstrassCurve.minimalDiscriminantOrd_le` (`δ_𝔭(W)` is attained and is the least such
  order) and `WeierstrassCurve.finite_minimalDiscriminantOrd_ne_zero` (`δ_𝔭(W) = 0` for all but
  finitely many `𝔭`).
* `WeierstrassCurve.minimalDiscriminant_variableChange`: `Δ_{W/L}` depends only on `W` up to a
  variable change.
* `WeierstrassCurve.absNorm_minimalDiscriminant`: for `Δ_W ≠ 0`,
  `N(Δ_{W/L}) = ∏_𝔭 N𝔭 ^ δ_𝔭(W)`.

For a discrete valuation ring Mathlib has `WeierstrassCurve.IsMinimal`; this file works with the
places of a number field directly.
-/

@[expose] public section

open IsDedekindDomain NumberField WithZero

namespace WeierstrassCurve

variable {L : Type*} [Field L] [NumberField L]

/-- A Weierstrass curve over a number field `L` is **integral at the finite place `v`** if each of
its coefficients `a₁, a₂, a₃, a₄, a₆` has `v`-adic valuation at most `1`, that is,
`ord_𝔭(a_i) ≥ 0`. -/
def IsIntegralAt (W : WeierstrassCurve L) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  v.valuation L W.a₁ ≤ 1 ∧ v.valuation L W.a₂ ≤ 1 ∧ v.valuation L W.a₃ ≤ 1 ∧
    v.valuation L W.a₄ ≤ 1 ∧ v.valuation L W.a₆ ≤ 1

/-- **Integrality at a place is integrality over its valuation ring**: `W` is integral at `v`
if and only if it is integral, in the sense of Mathlib's `WeierstrassCurve.IsIntegral`, over the
valuation ring `{x ∈ L : v(x) ≤ 1}` of `v`. -/
theorem isIntegralAt_iff_isIntegral (W : WeierstrassCurve L) (v : HeightOneSpectrum (𝓞 L)) :
    W.IsIntegralAt v ↔ IsIntegral (v.valuation L).integer W := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
    exact isIntegral_of_exists_lift _ ⟨⟨_, h₁⟩, rfl⟩ ⟨⟨_, h₂⟩, rfl⟩ ⟨⟨_, h₃⟩, rfl⟩ ⟨⟨_, h₄⟩, rfl⟩
      ⟨⟨_, h₆⟩, rfl⟩
  · rintro ⟨W', rfl⟩
    exact ⟨W'.a₁.2, W'.a₂.2, W'.a₃.2, W'.a₄.2, W'.a₆.2⟩

/-- The discriminant of an equation integral at `v` has `v`-adic valuation at most `1`. -/
theorem valuation_Δ_le_one_of_isIntegralAt {W : WeierstrassCurve L} {v : HeightOneSpectrum (𝓞 L)}
    (h : W.IsIntegralAt v) : v.valuation L W.Δ ≤ 1 := by
  have := (isIntegralAt_iff_isIntegral W v).mp h
  obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral (v.valuation L).integer W
  rw [← hr]
  exact r.2

variable (W : WeierstrassCurve L)

/-- The orders `ord_v(Δ(C • W))` of the discriminants of the equations `C • W` integral at `v`. -/
def discriminantOrds (v : HeightOneSpectrum (𝓞 L)) : Set ℕ :=
  {n | ∃ C : VariableChange L, (C • W).IsIntegralAt v ∧
    v.valuation L (C • W).Δ = exp (-(n : ℤ))}

/-- A nonzero element `x` of `L` with `v(x) ≤ 1` has `v(x) = exp(-n)` for some `n : ℕ`. -/
theorem exists_valuation_eq_exp_neg {v : HeightOneSpectrum (𝓞 L)} {x : L} (hx : x ≠ 0)
    (h : v.valuation L x ≤ 1) : ∃ n : ℕ, v.valuation L x = exp (-(n : ℤ)) := by
  have h0 : v.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨(-(v.valuation L x).log).toNat, ?_⟩
  have hlog : (v.valuation L x).log ≤ 0 := by
    rw [← log_one (M := ℤ), log_le_log h0 one_ne_zero]
    exact h
  rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]

/-- **An integral model at every place.** There is a nonzero `c ∈ 𝓞 L` such that the variable
change `x = c⁻² x'`, `y = c⁻³ y'` (`u = c⁻¹`, `r = s = t = 0`), which multiplies `a_i` by `c^i`,
gives an equation integral at every finite place of `L`. -/
theorem exists_variableChange_isIntegralAt_forall :
    ∃ (c : 𝓞 L) (hc : (c : L) ≠ 0), ∀ v : HeightOneSpectrum (𝓞 L),
      ((⟨(Units.mk0 (c : L) hc)⁻¹, 0, 0, 0⟩ : VariableChange L) • W).IsIntegralAt v := by
  have hden : ∀ a : L, ∃ d : 𝓞 L, d ≠ 0 ∧ ∃ n : 𝓞 L, (d : L) * a = n := by
    intro a
    obtain ⟨⟨n, d⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 L)) a
    exact ⟨d, nonZeroDivisors.ne_zero d.2, n, by rw [mul_comm]; exact h⟩
  obtain ⟨d₁, hd₁, n₁, e₁⟩ := hden W.a₁
  obtain ⟨d₂, hd₂, n₂, e₂⟩ := hden W.a₂
  obtain ⟨d₃, hd₃, n₃, e₃⟩ := hden W.a₃
  obtain ⟨d₄, hd₄, n₄, e₄⟩ := hden W.a₄
  obtain ⟨d₆, hd₆, n₆, e₆⟩ := hden W.a₆
  set c : 𝓞 L := d₁ * d₂ * d₃ * d₄ * d₆
  have hc : (c : L) ≠ 0 := by
    simp only [c, map_mul, ne_eq, mul_eq_zero, RingOfIntegers.coe_eq_zero_iff, not_or]
    exact ⟨⟨⟨⟨hd₁, hd₂⟩, hd₃⟩, hd₄⟩, hd₆⟩
  refine ⟨c, hc, fun v ↦ ?_⟩
  have hv : ∀ m : 𝓞 L, v.valuation L (m : L) ≤ 1 := fun m ↦ by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one m
  -- `c a_i = (c / d_i) (d_i a_i)` lies in `𝓞 L`.
  have hca : ∀ (d n : 𝓞 L) (a : L), (d : L) * a = n → d ∣ c → v.valuation L ((c : L) * a) ≤ 1 := by
    rintro d n a e ⟨q, hq⟩
    have : (c : L) * a = q * n := by
      rw [hq, ← e]
      push_cast
      ring
    rw [this, map_mul]
    exact mul_le_one' (hv q) (hv n)
  have hpow : ∀ (k : ℕ) (a : L), v.valuation L ((c : L) * a) ≤ 1 →
      v.valuation L ((c : L) ^ (k + 1) * a) ≤ 1 := by
    intro k a h
    rw [pow_succ, mul_assoc, map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (hv c) k) h
  simp only [IsIntegralAt, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, inv_inv, Units.val_mk0, mul_zero, add_zero, sub_zero,
    zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hpow 0 _ (hca d₁ n₁ _ e₁ ⟨d₂ * d₃ * d₄ * d₆, by simp only [c]; ring⟩)
  · exact hpow 1 _ (hca d₂ n₂ _ e₂ ⟨d₁ * d₃ * d₄ * d₆, by simp only [c]; ring⟩)
  · exact hpow 2 _ (hca d₃ n₃ _ e₃ ⟨d₁ * d₂ * d₄ * d₆, by simp only [c]; ring⟩)
  · exact hpow 3 _ (hca d₄ n₄ _ e₄ ⟨d₁ * d₂ * d₃ * d₆, by simp only [c]; ring⟩)
  · exact hpow 5 _ (hca d₆ n₆ _ e₆ ⟨d₁ * d₂ * d₃ * d₄, by simp only [c]; ring⟩)

omit [NumberField L] in
theorem Δ_variableChange_ne_zero [W.IsElliptic] (C : VariableChange L) : (C • W).Δ ≠ 0 :=
  (C • W).isUnit_Δ.ne_zero

/-- For `Δ_W ≠ 0`, some Weierstrass equation of `W` is integral at `v`, so the set of orders
defining `δ_v(W)` is nonempty. -/
theorem discriminantOrds_nonempty [W.IsElliptic] (v : HeightOneSpectrum (𝓞 L)) :
    (W.discriminantOrds v).Nonempty := by
  obtain ⟨c, hc, hC⟩ := W.exists_variableChange_isIntegralAt_forall
  obtain ⟨n, hn⟩ := exists_valuation_eq_exp_neg (W.Δ_variableChange_ne_zero _)
    (valuation_Δ_le_one_of_isIntegralAt (hC v))
  exact ⟨n, _, hC v, hn⟩

/-- **The order of the minimal discriminant at a finite place** `v` of `L`: the least
`ord_v(Δ(C • W))` among the Weierstrass equations `C • W` of `W` that are integral at `v`, over all
variable changes `C` (`x = u² x' + r`, `y = u³ y' + u² s x' + t`, `u ∈ Lˣ`, `r, s, t ∈ L`).
For `Δ_W ≠ 0` this set of orders is nonempty (`WeierstrassCurve.discriminantOrds_nonempty`);
for `Δ_W = 0` it is empty and the definition gives `0`. -/
noncomputable def minimalDiscriminantOrd (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  sInf (W.discriminantOrds v)

/-- **The minimal discriminant** `Δ_{W/L} = ∏_𝔭 𝔭 ^ δ_𝔭(W)` of an elliptic curve over a number
field `L`, an ideal of `𝓞 L`, the product running over the maximal ideals `𝔭` of `𝓞 L` and
`δ_𝔭(W)` being `WeierstrassCurve.minimalDiscriminantOrd`. It is meant for `Δ_W ≠ 0`; for
`Δ_W = 0` every `δ_𝔭(W)` is `0` and the product is the unit ideal.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter II, §3, p. 59:
a Weierstrass equation over `ℚ` is minimal when a variable change makes its coefficients integers
with `|Δ|` minimal. Here minimality is taken one prime at a time, over a number field, and the
local orders are collected into an ideal. -/
noncomputable def minimalDiscriminant : Ideal (𝓞 L) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 L), v.asIdeal ^ W.minimalDiscriminantOrd v

/-- **`δ_v(W)` is attained.** If `Δ_W ≠ 0`, some Weierstrass equation `C • W` integral at `v` has
`ord_v(Δ(C • W)) = δ_v(W)`. -/
theorem exists_minimalDiscriminantOrd [W.IsElliptic] (v : HeightOneSpectrum (𝓞 L)) :
    ∃ C : VariableChange L, (C • W).IsIntegralAt v ∧
      v.valuation L (C • W).Δ = exp (-(W.minimalDiscriminantOrd v : ℤ)) :=
  Nat.sInf_mem (W.discriminantOrds_nonempty v)

/-- **`δ_v(W)` is the least order.** If `Δ_W ≠ 0`, every Weierstrass equation `C • W` integral at
`v` has `ord_v(Δ(C • W)) ≥ δ_v(W)`, that is, `v(Δ(C • W)) ≤ exp(-δ_v(W))`. -/
theorem minimalDiscriminantOrd_le [W.IsElliptic] (v : HeightOneSpectrum (𝓞 L))
    (C : VariableChange L) (hC : (C • W).IsIntegralAt v) :
    v.valuation L (C • W).Δ ≤ exp (-(W.minimalDiscriminantOrd v : ℤ)) := by
  obtain ⟨n, hn⟩ := exists_valuation_eq_exp_neg (W.Δ_variableChange_ne_zero C)
    (valuation_Δ_le_one_of_isIntegralAt hC)
  rw [hn, exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Nat.sInf_le ⟨C, hC, hn⟩

/-- **`δ_𝔭(W) = 0` for all but finitely many `𝔭`**, for `Δ_W ≠ 0`. -/
theorem finite_minimalDiscriminantOrd_ne_zero [W.IsElliptic] :
    {v : HeightOneSpectrum (𝓞 L) | W.minimalDiscriminantOrd v ≠ 0}.Finite := by
  obtain ⟨c, hc, hC⟩ := W.exists_variableChange_isIntegralAt_forall
  set C : VariableChange L := ⟨(Units.mk0 (c : L) hc)⁻¹, 0, 0, 0⟩
  refine (HeightOneSpectrum.Support.finite (𝓞 L) (C • W).Δ⁻¹).subset fun v hv ↦ ?_
  simp only [HeightOneSpectrum.Support, Set.mem_ofPred_eq, map_inv₀]
  have hle := valuation_Δ_le_one_of_isIntegralAt (hC v)
  rcases hle.lt_or_eq with hlt | heq
  · exact one_lt_inv_iff₀.mpr ⟨(Valuation.pos_iff _).mpr (W.Δ_variableChange_ne_zero C), hlt⟩
  · have h0 : 0 ∈ W.discriminantOrds v := ⟨C, hC v, by simp [heq]⟩
    exact absurd (Nat.eq_zero_of_le_zero (Nat.sInf_le h0)) hv

theorem discriminantOrds_variableChange (C : VariableChange L) (v : HeightOneSpectrum (𝓞 L)) :
    (C • W).discriminantOrds v = W.discriminantOrds v := by
  ext n
  constructor
  · rintro ⟨C', h, h'⟩
    exact ⟨C' * C, by rwa [mul_smul], by rwa [mul_smul]⟩
  · rintro ⟨C', h, h'⟩
    exact ⟨C' * C⁻¹, by rwa [mul_smul, inv_smul_smul], by rwa [mul_smul, inv_smul_smul]⟩

/-- **`δ_v` depends only on `W` up to a variable change.** -/
theorem minimalDiscriminantOrd_variableChange (C : VariableChange L)
    (v : HeightOneSpectrum (𝓞 L)) :
    (C • W).minimalDiscriminantOrd v = W.minimalDiscriminantOrd v := by
  rw [minimalDiscriminantOrd, minimalDiscriminantOrd, discriminantOrds_variableChange]

/-- **The minimal discriminant depends only on `W` up to a variable change**, that is, on the
elliptic curve up to isomorphism over `L`. -/
theorem minimalDiscriminant_variableChange (C : VariableChange L) :
    (C • W).minimalDiscriminant = W.minimalDiscriminant := by
  simp only [minimalDiscriminant, minimalDiscriminantOrd_variableChange]

/-- **The norm of the minimal discriminant**: for `Δ_W ≠ 0`,
`N(Δ_{W/L}) = #(𝓞 L / Δ_{W/L}) = ∏_𝔭 #(𝓞 L / 𝔭) ^ δ_𝔭(W)`. -/
theorem absNorm_minimalDiscriminant [W.IsElliptic] :
    Ideal.absNorm W.minimalDiscriminant =
      ∏ᶠ v : HeightOneSpectrum (𝓞 L), Ideal.absNorm v.asIdeal ^ W.minimalDiscriminantOrd v := by
  have hfin : Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 L) ↦ v.asIdeal ^ W.minimalDiscriminantOrd v := by
    refine (W.finite_minimalDiscriminantOrd_ne_zero).subset fun v hv ↦ ?_
    intro h0
    apply hv
    simp only [h0, pow_zero]
  have := MonoidHom.map_finprod (Ideal.absNorm (S := 𝓞 L)).toMonoidHom hfin
  simpa [minimalDiscriminant] using this

end WeierstrassCurve
