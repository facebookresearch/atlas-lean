/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Oesterlé's fundamental identity `J(U) = -J(U*)`

Let `d, M > 0`, `γ(s) = M^s Γ(s)²`, let `Ψ = L(ψ, ·)` and `G = L(g, ·)` be Dirichlet series and
suppose that `G` is an Euler product of Oesterlé's factors
`G_p(s) = (1 + α_p p^{-s})(1 + β_p p^{-s}) / ((1 + α'_p p^{-s})(1 + β'_p p^{-s}))` with
`|α_p|, |β_p|, |α'_p|, |β'_p| ≤ √p`. If `F = d^s γ Ψ G` extends to an entire function of rapid
decay in vertical strips, with `F(2 - s) = F(s)` and a zero of order at least three at `s = 1`,
and `γΨ` is of rapid decay in vertical strips of `Re s ≥ 1`, then for `σ > 3/2`
* the integral `∫_{(σ)} d^{s-1} γ(s) Ψ(s) G(s) (s-1)^{-3} ds/(2πi)` vanishes;
* for `U ≥ 1` the analogous integrals `J(U)` and `J(U*)` with `G` replaced by the partial
  Euler product `G(U, s) = ∏_{p<U} G_p(s)` and by `G(U*, s) = G(s) - G(U, s)` converge
  absolutely and `J(U) = -J(U*)`;
* `G(U*, s) = G(U, s) ((∏_{p ≥ U} G_p(s)) - 1)` for `Re s > 3/2`.

The vanishing is proved by moving the line of integration to `Re s = 1` (on `Re s > 3/2` the
integrand is `d^{-1} F₁(s)`, an entire function of rapid decay in vertical strips). On
`Re s = 1` the function `t ↦ F₁(1 + it)` is odd for `t ≠ 0` by the functional equation, hence odd
almost everywhere, so its integral vanishes.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3 and §3.1.
-/

@[expose] public section

namespace MetaMathlibExt
namespace OesterleFundamentalIdentity

open Complex MeasureTheory Filter Set
open scoped Topology

/-- Oesterlé's Euler factor
`G_p(s) = (1 + α_p p^{-s})(1 + β_p p^{-s}) / ((1 + α'_p p^{-s})(1 + β'_p p^{-s}))`. -/
noncomputable def eulerFactor (α β α' β' : ℕ → ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 + α p * (p : ℂ) ^ (-s)) * (1 + β p * (p : ℂ) ^ (-s)) /
    ((1 + α' p * (p : ℂ) ^ (-s)) * (1 + β' p * (p : ℂ) ^ (-s)))

/-- Rapid decay at infinity in every vertical strip `σ₁ ≤ Re s ≤ σ₂` with `[σ₁, σ₂] ⊆ S`: for
every `k` there are `C` and `T` with `‖F(σ + it)‖ |t|^k ≤ C` for `σ ∈ [σ₁, σ₂]` and `|t| ≥ T`. -/
def RapidDecayInStrips (F : ℂ → ℂ) (S : Set ℝ) : Prop :=
  ∀ (k : ℕ) (σ₁ σ₂ : ℝ), Set.Icc σ₁ σ₂ ⊆ S → ∃ C T : ℝ, ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ t : ℝ,
    T ≤ |t| → ‖F (σ + t * I)‖ * |t| ^ k ≤ C

/-- The partial Euler product `G(U, s) = ∏_{p<U} G_p(s)` over the primes `p < ⌈U⌉₊`, that is,
over the primes with `(p : ℝ) < U`. -/
noncomputable def partialEuler (α β α' β' : ℕ → ℂ) (U : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ (Finset.range ⌈U⌉₊).filter Nat.Prime, eulerFactor α β α' β' p s

/-- The integrand `d^{s-1} γ(s) Ψ(s) H(s) (s-1)^{-3}` of Oesterlé's (3.1.1) on the line
`s = σ + it`, where `γ(s) = M^s Γ(s)²` and `Ψ = L(ψ, ·)`. -/
noncomputable def oesterleIntegrand (d M : ℝ) (ψ : ℕ → ℂ) (H : ℂ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  let s := (σ : ℂ) + t * I
  (d : ℂ) ^ (s - 1) * ((M : ℂ) ^ s * Gamma s ^ 2) * LSeries ψ s * H s * ((s - 1) ^ 3)⁻¹

/-- The integral `∫_{σ-i∞}^{σ+i∞} d^{s-1} γ(s) Ψ(s) H(s) (s-1)^{-3} ds/(2πi)`, written as
`(2π)⁻¹ ∫_ℝ (integrand at σ + it) dt` (the normalisation of `mellinInv`). -/
noncomputable def oesterleIntegral (d M : ℝ) (ψ : ℕ → ℂ) (H : ℂ → ℂ) (σ : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ t : ℝ, oesterleIntegrand d M ψ H σ t

/-! ### Euler factor estimates -/

variable {α β α' β' : ℕ → ℂ}

/-- For a prime `p` and `‖a‖ ≤ √p`, `‖a p^{-s}‖ ≤ p^{1/2 - Re s}`. -/
lemma norm_coeff_mul_cpow_le {a : ℂ} {p : ℕ} (hp : p.Prime) (ha : ‖a‖ ≤ √p) (s : ℂ) :
    ‖a * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (1 / 2 - s.re) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re, sub_eq_add_neg,
    Real.rpow_add hp0, ← Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_right ha (by positivity)

/-- For a prime `p` and `σ > 3/2`, `p^{1/2 - σ} ≤ 1/2`. -/
lemma rpow_half_sub_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 3 / 2 < σ) :
    (p : ℝ) ^ (1 / 2 - σ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc (p : ℝ) ^ (1 / 2 - σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := by gcongr

/-- If `x, y, x', y'` have norm at most `ε ≤ 1/2`, then `(1 + x')(1 + y') ≠ 0` and
`‖(1 + x)(1 + y)/((1 + x')(1 + y')) - 1‖ ≤ 20 ε`. -/
lemma quotient_estimate {x y x' y' : ℂ} {ε : ℝ} (hε : ε ≤ 1 / 2) (hx : ‖x‖ ≤ ε)
    (hy : ‖y‖ ≤ ε) (hx' : ‖x'‖ ≤ ε) (hy' : ‖y'‖ ≤ ε) :
    (1 + x') * (1 + y') ≠ 0 ∧ ‖(1 + x) * (1 + y) / ((1 + x') * (1 + y')) - 1‖ ≤ 20 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hx
  have h1 : ∀ z : ℂ, ‖z‖ ≤ ε → 1 / 2 ≤ ‖1 + z‖ := fun z hz => by
    have := norm_sub_norm_le (1 : ℂ) (-z)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hd : 1 / 4 ≤ ‖(1 + x') * (1 + y')‖ := by
    rw [norm_mul]; nlinarith [h1 x' hx', h1 y' hy']
  have hd0 : (1 + x') * (1 + y') ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; norm_num at hd
  refine ⟨hd0, ?_⟩
  have hnum : ‖(1 + x) * (1 + y) - (1 + x') * (1 + y')‖ ≤ 5 * ε := by
    have e : (1 + x) * (1 + y) - (1 + x') * (1 + y') = x + y + x * y - x' - y' - x' * y' := by
      ring
    rw [e]
    have e1 := norm_sub_le (x + y + x * y - x' - y') (x' * y')
    have e2 := norm_sub_le (x + y + x * y - x') y'
    have e3 := norm_sub_le (x + y + x * y) x'
    have e4 := norm_add_le (x + y) (x * y)
    have e5 := norm_add_le x y
    rw [norm_mul] at e1 e4
    have m1 : ‖x‖ * ‖y‖ ≤ ε * ε := mul_le_mul hx hy (norm_nonneg _) hε0
    have m2 : ‖x'‖ * ‖y'‖ ≤ ε * ε := mul_le_mul hx' hy' (norm_nonneg _) hε0
    nlinarith
  rw [div_sub_one hd0, norm_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- Under (C2), for a prime `p` and `Re s > 3/2`, the denominator of `G_p(s)` is nonzero and
`‖G_p(s) - 1‖ ≤ 20 p^{1/2 - Re s}`. -/
lemma eulerFactor_estimate
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 3 / 2 < s.re) :
    (1 + α' p * (p : ℂ) ^ (-s)) * (1 + β' p * (p : ℂ) ^ (-s)) ≠ 0 ∧
      ‖eulerFactor α β α' β' p s - 1‖ ≤ 20 * (p : ℝ) ^ (1 / 2 - s.re) := by
  obtain ⟨ha, hb, ha', hb'⟩ := hC2 p hp
  exact quotient_estimate (rpow_half_sub_le hp hs) (norm_coeff_mul_cpow_le hp ha s)
    (norm_coeff_mul_cpow_le hp hb s) (norm_coeff_mul_cpow_le hp ha' s)
    (norm_coeff_mul_cpow_le hp hb' s)

/-- Under (C2), `‖G_p(s)‖ ≤ 11` for a prime `p` and `Re s > 3/2`. -/
lemma norm_eulerFactor_le
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 3 / 2 < s.re) :
    ‖eulerFactor α β α' β' p s‖ ≤ 11 := by
  have h1 := (eulerFactor_estimate hC2 hp hs).2
  have h2 := rpow_half_sub_le hp hs
  have h3 := norm_sub_norm_le (eulerFactor α β α' β' p s) 1
  rw [norm_one] at h3
  linarith

/-- Under (C2), `G(U, s)` is bounded on `Re s > 3/2`. -/
lemma norm_partialEuler_le
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    (U : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    ‖partialEuler α β α' β' U s‖ ≤ 11 ^ ((Finset.range ⌈U⌉₊).filter Nat.Prime).card := by
  unfold partialEuler
  rw [norm_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p hp => norm_eulerFactor_le hC2 (Finset.mem_filter.1 hp).2 hs)

/-! ### The tail of the Euler product (Oesterlé's (3.1.3)) -/

/-- Under (C2), `∑_p ‖G_p(s) - 1‖ < ∞` for `Re s > 3/2`. -/
lemma summable_norm_eulerFactor_sub_one
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖eulerFactor α β α' β' p s - 1‖) := by
  have hsum : Summable (fun p : Nat.Primes => 20 * ((p : ℕ) : ℝ) ^ (1 / 2 - s.re)) :=
    ((Real.summable_nat_rpow.2 (by linarith)).subtype (fun n => n.Prime)).mul_left 20
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => (eulerFactor_estimate hC2 p.prop hs).2) hsum

/-- Under (C2), the tail product `∏_{p ≥ U} G_p(s)` converges for `Re s > 3/2`. -/
lemma multipliable_tail
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    {s : ℂ} (hs : 3 / 2 < s.re) (U : ℝ) :
    Multipliable (fun p : {p : Nat.Primes // U ≤ (p : ℝ)} => eulerFactor α β α' β' p s) := by
  have h := (summable_norm_eulerFactor_sub_one hC2 hs).subtype (fun p : Nat.Primes => U ≤ (p : ℝ))
  refine (multipliable_one_add_of_summable
    (f := fun p : {p : Nat.Primes // U ≤ (p : ℝ)} => eulerFactor α β α' β' p s - 1) h).congr ?_
  intro p
  ring

/-- If `G = ∏_p G_p` on `Re s > 3/2` and (C2) holds, then `G(s) = G(U, s) ∏_{p ≥ U} G_p(s)` for
`Re s > 3/2` and every real `U`. -/
lemma lSeries_eq_partialEuler_mul_tail {g : ℕ → ℂ}
    (hprod : ∀ s : ℂ, 3 / 2 < s.re →
      HasProd (fun p : Nat.Primes => eulerFactor α β α' β' p s) (LSeries g s))
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    (U : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries g s = partialEuler α β α' β' U s *
      ∏' p : {p : Nat.Primes // U ≤ (p : ℝ)}, eulerFactor α β α' β' p s := by
  classical
  let f : Nat.Primes → ℂ := fun p => eulerFactor α β α' β' p s
  let S : Finset Nat.Primes := (Finset.range ⌈U⌉₊).subtype Nat.Prime
  have hS : (S : Set Nat.Primes) = {p : Nat.Primes | (p : ℝ) < U} := by
    ext p
    rw [Finset.mem_coe]
    exact Finset.mem_subtype.trans (Finset.mem_range.trans Nat.lt_ceil)
  have hT : {p : Nat.Primes | U ≤ (p : ℝ)} = {p : Nat.Primes | (p : ℝ) < U}ᶜ := by
    ext p; simp [not_lt]
  have hcompl : IsCompl (S : Set Nat.Primes) {p : Nat.Primes | U ≤ (p : ℝ)} := by
    rw [hS, hT]; exact isCompl_compl
  have h1 : HasProd (f ∘ Subtype.val : ↥(S : Set Nat.Primes) → ℂ) (partialEuler α β α' β' U s) := by
    have := S.hasProd f
    convert this using 1
    exact (Finset.prod_subtype_eq_prod_filter (fun n => eulerFactor α β α' β' n s)).symm
  have h2 : HasProd (f ∘ Subtype.val : ↥{p : Nat.Primes | U ≤ (p : ℝ)} → ℂ)
      (∏' p : {p : Nat.Primes // U ≤ (p : ℝ)}, eulerFactor α β α' β' p s) :=
    (multipliable_tail hC2 hs U).hasProd
  exact (hprod s hs).unique (HasProd.mul_isCompl hcompl h1 h2)

/-- **Oesterlé's (3.1.3).** If `G = ∏_p G_p` on `Re s > 3/2` and (C2) holds, then
`G(U*, s) = G(s) - G(U, s) = G(U, s)((∏_{p ≥ U} G_p(s)) - 1)` for `Re s > 3/2` and every real
`U`. -/
theorem lSeries_sub_partialEuler {g : ℕ → ℂ}
    (hprod : ∀ s : ℂ, 3 / 2 < s.re →
      HasProd (fun p : Nat.Primes => eulerFactor α β α' β' p s) (LSeries g s))
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    (U : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries g s - partialEuler α β α' β' U s = partialEuler α β α' β' U s *
      ((∏' p : {p : Nat.Primes // U ≤ (p : ℝ)}, eulerFactor α β α' β' p s) - 1) := by
  rw [lSeries_eq_partialEuler_mul_tail hprod hC2 U hs]
  ring

/-! ### Integrals along vertical lines -/

/-- The vertical line `t ↦ σ + it` is continuous. -/
lemma continuous_line (σ : ℝ) : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop

/-- `‖(σ + it - 1)^{-3}‖ ≤ 1` for `|t| ≥ 1`. -/
lemma norm_inv_cube_le_one (σ : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖(((σ : ℂ) + t * I - 1) ^ 3)⁻¹‖ ≤ 1 := by
  have h : |t| ≤ ‖(σ : ℂ) + t * I - 1‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + t * I - 1)
  rw [norm_inv, norm_pow]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (ht.trans h))

/-- A decay bound `‖f(σ + it)‖ |t|^k ≤ C` for `|t| ≥ T` survives multiplication by
`(σ + it - 1)^{-3}` for `|t| ≥ max(T, 1)`. -/
lemma decay_mul_inv_cube {f : ℂ → ℂ} {σ C T : ℝ} {k : ℕ}
    (hd : ∀ t : ℝ, T ≤ |t| → ‖f (σ + t * I)‖ * |t| ^ k ≤ C) (t : ℝ) (ht : max T 1 ≤ |t|) :
    ‖f (σ + t * I) * (((σ : ℂ) + t * I - 1) ^ 3)⁻¹‖ * |t| ^ k ≤ C := by
  have h1 := hd t ((le_max_left _ _).trans ht)
  have h2 := norm_inv_cube_le_one σ ((le_max_right _ _).trans ht)
  rw [norm_mul]
  calc ‖f (σ + t * I)‖ * ‖(((σ : ℂ) + t * I - 1) ^ 3)⁻¹‖ * |t| ^ k
      ≤ ‖f (σ + t * I)‖ * 1 * |t| ^ k := by gcongr
    _ ≤ C := by simpa using h1

/-- A continuous function on `ℝ` with `‖h t‖ t² ≤ C` for `|t| ≥ T` is integrable. -/
lemma integrable_of_decay {h : ℝ → ℂ} (hc : Continuous h) {C T : ℝ}
    (hd : ∀ t : ℝ, T ≤ |t| → ‖h t‖ * |t| ^ 2 ≤ C) : Integrable h := by
  set T' := max T 1
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T') (b := T')).exists_bound_of_continuousOn
    hc.continuousOn
  set K := max (B * (1 + T' ^ 2)) (2 * C)
  refine (integrable_inv_one_add_sq.const_mul K).mono' hc.aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have hn := norm_nonneg (h t)
  by_cases ht : |t| ≤ T'
  · have h1 := hB t (Set.mem_Icc.2 (abs_le.1 ht))
    have h2 : t ^ 2 ≤ T' ^ 2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    have h3 : B * (1 + T' ^ 2) ≤ K := le_max_left _ _
    nlinarith
  · replace ht := not_le.1 ht
    have h1 := hd t ((le_max_left T 1).trans ht.le)
    rw [sq_abs] at h1
    have h2 : 1 ≤ t ^ 2 := by
      rw [← sq_abs t]; nlinarith [le_max_right T 1]
    have h3 : 2 * C ≤ K := le_max_right _ _
    nlinarith

/-- A continuous function of rapid decay in the vertical strips of `S` is integrable on every
line `Re s = σ` with `σ ∈ S`. -/
lemma integrable_line_of_rapidDecay {f : ℂ → ℂ} {S : Set ℝ} (hf : Continuous f)
    (hdec : RapidDecayInStrips f S) {σ : ℝ} (hσ : σ ∈ S) :
    Integrable (fun t : ℝ => f (σ + t * I)) := by
  obtain ⟨C, T, h⟩ := hdec 2 σ σ (by simpa using hσ)
  exact integrable_of_decay (hf.comp (continuous_line σ)) (fun t ht => h σ ⟨le_rfl, le_rfl⟩ t ht)

/-- If `F(s) = (s - 1)³ F₁(s)` and `F` is of rapid decay in vertical strips, so is `F₁`. -/
lemma rapidDecay_of_eq_cube_mul {F F₁ : ℂ → ℂ} {S : Set ℝ} (hF : ∀ s, F s = (s - 1) ^ 3 * F₁ s)
    (hdec : RapidDecayInStrips F S) : RapidDecayInStrips F₁ S := by
  intro k σ₁ σ₂ hI
  obtain ⟨C, T, h⟩ := hdec k σ₁ σ₂ hI
  refine ⟨C, max T 1, fun σ hσ t ht => ?_⟩
  have hne : (σ : ℂ) + t * I - 1 ≠ 0 := by
    intro h0
    have h0' : t = 0 := by simpa using congrArg Complex.im h0
    have : (1 : ℝ) ≤ |t| := (le_max_right _ _).trans ht
    rw [h0'] at this; norm_num at this
  have e : F₁ (σ + t * I) = F (σ + t * I) * (((σ : ℂ) + t * I - 1) ^ 3)⁻¹ := by
    rw [hF]; field_simp
  rw [e]
  exact decay_mul_inv_cube (fun t ht => h σ hσ t ht) t ht

/-- Moving a vertical line of integration: for an entire function `f` of rapid decay in vertical
strips and real `a ≤ b`, `∫ f(b + it) dt = ∫ f(a + it) dt`. -/
theorem integral_vertical_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hdec : RapidDecayInStrips f Set.univ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t : ℝ, f (b + t * I) = ∫ t : ℝ, f (a + t * I) := by
  have hia := integrable_line_of_rapidDecay hf.continuous hdec (Set.mem_univ a)
  have hib := integrable_line_of_rapidDecay hf.continuous hdec (Set.mem_univ b)
  obtain ⟨C, T₀, hC⟩ := hdec 1 a b (Set.subset_univ _)
  have key : ∀ T : ℝ, I • ((∫ y in (-T)..T, f (b + y * I)) - ∫ y in (-T)..T, f (a + y * I)) =
      (∫ x in a..b, f (x + T * I)) - ∫ x in a..b, f (x + ((-T : ℝ) : ℂ) * I) := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩
      hf.differentiableOn
    dsimp only at h
    simp only [smul_eq_mul] at h ⊢
    linear_combination h
  have hL := ((intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id)).const_smul I
  have hH : ∀ s T : ℝ, max T₀ 1 ≤ T → |s| = T →
      ‖∫ x in a..b, f (x + s * I)‖ ≤ C / T * (b - a) := by
    intro s T hT hs
    have hT1 : 0 < T := by linarith [le_max_right T₀ 1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := C / T)
      (f := fun x : ℝ => f (x + s * I)) ?_
    · rwa [abs_of_nonneg (by linarith)] at this
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have h1 := hC x ⟨hx.1.le, hx.2⟩ s (by rw [hs]; exact (le_max_left _ _).trans hT)
    rw [pow_one, hs] at h1
    rw [le_div_iff₀ hT1]
    exact h1
  have hbound : Tendsto (fun T : ℝ => C / T * (b - a)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := C)).div_atTop tendsto_id).mul_const (b - a)
  have hR1 : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + T * I)) atTop (𝓝 0) :=
    squeeze_zero_norm' (eventually_atTop.2 ⟨max T₀ 1, fun T hT =>
      hH T T hT (abs_of_pos (by linarith [le_max_right T₀ 1]))⟩) hbound
  have hR2 : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) :=
    squeeze_zero_norm' (eventually_atTop.2 ⟨max T₀ 1, fun T hT =>
      hH (-T) T hT (by rw [abs_neg, abs_of_pos (by linarith [le_max_right T₀ 1])])⟩) hbound
  have hR := hR1.sub hR2
  rw [sub_zero] at hR
  have heq := tendsto_nhds_unique (hL.congr key) hR
  rcases smul_eq_zero.1 heq with h | h
  · exact absurd h I_ne_zero
  · exact sub_eq_zero.1 h

/-- If `F(s) = (s-1)³ F₁(s)` and `F(2-s) = F(s)`, then on the line `Re s = 1` the function
`t ↦ F₁(1 + it)` is odd for `t ≠ 0`, hence odd almost everywhere, so its integral over `ℝ`
vanishes. -/
theorem integral_line_one_eq_zero {F F₁ : ℂ → ℂ} (hsymm : ∀ s, F (2 - s) = F s)
    (hF : ∀ s, F s = (s - 1) ^ 3 * F₁ s) : ∫ t : ℝ, F₁ (1 + t * I) = 0 := by
  have hodd : ∀ t : ℝ, t ≠ 0 → F₁ (1 + ((-t : ℝ) : ℂ) * I) = -F₁ (1 + t * I) := by
    intro t ht
    have h := hsymm (1 + t * I)
    have e : (2 : ℂ) - (1 + t * I) = 1 + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    rw [e, hF, hF] at h
    have hne : ((t : ℂ) * I) ^ 3 ≠ 0 := pow_ne_zero _ (mul_ne_zero (ofReal_ne_zero.2 ht) I_ne_zero)
    apply mul_left_cancel₀ hne
    push_cast at h ⊢
    linear_combination -h
  have hae : (fun t : ℝ => F₁ (1 + ((-t : ℝ) : ℂ) * I)) =ᵐ[volume] fun t => -F₁ (1 + t * I) := by
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with t ht
    exact hodd t ht
  have h1 : ∫ t : ℝ, F₁ (1 + t * I) = -∫ t : ℝ, F₁ (1 + t * I) := by
    calc ∫ t : ℝ, F₁ (1 + t * I) = ∫ t : ℝ, F₁ (1 + ((-t : ℝ) : ℂ) * I) :=
          (integral_neg_eq_self (fun t : ℝ => F₁ (1 + t * I)) volume).symm
      _ = ∫ t : ℝ, -F₁ (1 + t * I) := integral_congr_ae hae
      _ = -∫ t : ℝ, F₁ (1 + t * I) := integral_neg _
  linear_combination h1 / 2

/-! ### Oesterlé's (3.1.1) and (3.1.4) -/

variable {d M : ℝ} {ψ g : ℕ → ℂ} {F F₁ : ℂ → ℂ}

/-- If `d > 0`, `F = d^s γ Ψ G` on `Re s > 3/2` and `F(s) = (s - 1)³ F₁(s)`, then on
`Re s = σ > 3/2` the integrand of (3.1.1) is `d^{-1} F₁(s)`. -/
lemma oesterleIntegrand_lSeries_eq (hd : 0 < d)
    (hFeq : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (d : ℂ) ^ s * ((M : ℂ) ^ s * Gamma s ^ 2) * LSeries ψ s * LSeries g s)
    (hF : ∀ s, F s = (s - 1) ^ 3 * F₁ s) {σ : ℝ} (hσ : 3 / 2 < σ) (t : ℝ) :
    oesterleIntegrand d M ψ (LSeries g) σ t = (d : ℂ)⁻¹ * F₁ (σ + t * I) := by
  have hre : 3 / 2 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hre1 : ((σ : ℂ) + t * I - 1).re ≠ 0 := by simp; linarith
  simp only [oesterleIntegrand]
  generalize (σ : ℂ) + t * I = s at hre hre1 ⊢
  have hs1 : s - 1 ≠ 0 := fun h => hre1 (by rw [h, zero_re])
  have hne : (s - 1) ^ 3 ≠ 0 := pow_ne_zero _ hs1
  have hd0 : (d : ℂ) ≠ 0 := ofReal_ne_zero.2 hd.ne'
  have hFs := hFeq s hre
  rw [hF s] at hFs
  rw [cpow_sub _ _ hd0, cpow_one]
  calc (d : ℂ) ^ s / d * ((M : ℂ) ^ s * Gamma s ^ 2) * LSeries ψ s * LSeries g s *
        ((s - 1) ^ 3)⁻¹
      = (d : ℂ)⁻¹ * ((d : ℂ) ^ s * ((M : ℂ) ^ s * Gamma s ^ 2) * LSeries ψ s * LSeries g s) *
        ((s - 1) ^ 3)⁻¹ := by ring
    _ = (d : ℂ)⁻¹ * F₁ s := by rw [← hFs]; field_simp

/-- **Oesterlé's (3.1.1).** Under (C3), for `σ > 3/2` the integral
`∫_{(σ)} d^{s-1} γ(s) Ψ(s) G(s) (s-1)^{-3} ds/(2πi)` vanishes. -/
theorem oesterleIntegral_lSeries_eq_zero (hd : 0 < d)
    (hFeq : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (d : ℂ) ^ s * ((M : ℂ) ^ s * Gamma s ^ 2) * LSeries ψ s * LSeries g s)
    (hFdec : RapidDecayInStrips F Set.univ) (hsymm : ∀ s, F (2 - s) = F s)
    (hF₁ : Differentiable ℂ F₁) (hF : ∀ s, F s = (s - 1) ^ 3 * F₁ s) {σ : ℝ} (hσ : 3 / 2 < σ) :
    oesterleIntegral d M ψ (LSeries g) σ = 0 := by
  unfold oesterleIntegral
  simp_rw [oesterleIntegrand_lSeries_eq hd hFeq hF hσ]
  rw [integral_const_mul, integral_vertical_eq hF₁ (rapidDecay_of_eq_cube_mul hF hFdec)
    (by linarith : (1 : ℝ) ≤ σ), ofReal_one, integral_line_one_eq_zero hsymm hF, mul_zero,
    smul_zero]

/-- Under (C3), with `F(s) = (s - 1)³ F₁(s)` and `F₁` entire, the integrand of (3.1.1) is
integrable on `Re s = σ > 3/2`. -/
lemma integrable_oesterleIntegrand_lSeries (hd : 0 < d)
    (hFeq : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (d : ℂ) ^ s * ((M : ℂ) ^ s * Gamma s ^ 2) * LSeries ψ s * LSeries g s)
    (hFdec : RapidDecayInStrips F Set.univ) (hF₁ : Differentiable ℂ F₁)
    (hF : ∀ s, F s = (s - 1) ^ 3 * F₁ s) {σ : ℝ} (hσ : 3 / 2 < σ) :
    Integrable (oesterleIntegrand d M ψ (LSeries g) σ) := by
  rw [show oesterleIntegrand d M ψ (LSeries g) σ = fun t : ℝ => (d : ℂ)⁻¹ * F₁ (σ + t * I) from
    funext (oesterleIntegrand_lSeries_eq hd hFeq hF hσ)]
  exact (integrable_line_of_rapidDecay hF₁.continuous (rapidDecay_of_eq_cube_mul hF hFdec)
    (Set.mem_univ σ)).const_mul _

/-- Under (C2), `t ↦ G_p(σ + it)` is continuous for a prime `p` and `σ > 3/2`. -/
lemma continuous_eulerFactor_line
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 3 / 2 < σ) :
    Continuous (fun t : ℝ => eulerFactor α β α' β' p ((σ : ℂ) + t * I)) := by
  have hc : Continuous (fun t : ℝ => (p : ℂ) ^ (-((σ : ℂ) + t * I))) :=
    (continuous_line σ).neg.const_cpow (Or.inl (by exact_mod_cast hp.ne_zero))
  refine Continuous.div (by fun_prop) (by fun_prop) (fun t => ?_)
  exact (eulerFactor_estimate hC2 hp (by simpa using hσ)).1

/-- **Absolute convergence of `J(U)`**, following Oesterlé: under (C2) and (C4), for
`σ > 3/2` and every real `U`, `G(U, ·)` and `d^{s-1}` are bounded on `Re s = σ` and
`γΨ(s)(s-1)^{-3}` is integrable there. -/
theorem integrable_oesterleIntegrand_partialEuler (hd : 0 < d) (hM : 0 < M)
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    (hC4 : ∃ (V : Set ℂ) (Ψ' : ℂ → ℂ), IsOpen V ∧ {s | 1 ≤ s.re} ⊆ V ∧ DifferentiableOn ℂ Ψ' V ∧
      (∀ s, 1 < s.re → Ψ' s = LSeries ψ s) ∧
      RapidDecayInStrips (fun s => (M : ℂ) ^ s * Gamma s ^ 2 * Ψ' s) (Set.Ici 1))
    {σ : ℝ} (hσ : 3 / 2 < σ) (U : ℝ) :
    Integrable (oesterleIntegrand d M ψ (partialEuler α β α' β' U) σ) := by
  obtain ⟨V, Ψ', hV, hsub, hΨ'd, hΨ'eq, hdec⟩ := hC4
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t => by simp
  -- the factor `γ Ψ (s - 1)⁻³` is integrable on the line
  have hγ : Continuous (fun t : ℝ => (M : ℂ) ^ ((σ : ℂ) + t * I) * Gamma ((σ : ℂ) + t * I) ^ 2 *
      Ψ' ((σ : ℂ) + t * I)) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    refine ContinuousAt.comp (g := fun s => (M : ℂ) ^ s * Gamma s ^ 2 * Ψ' s) ?_
      (continuous_line σ).continuousAt
    have hs1 : 1 ≤ ((σ : ℂ) + t * I).re := by rw [hre]; linarith
    have hΓ : ContinuousAt Gamma ((σ : ℂ) + t * I) := by
      refine (differentiableAt_Gamma _ fun m h => ?_).continuousAt
      have := congrArg Complex.re h
      rw [hre] at this; simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact (((continuous_id.const_cpow (Or.inl (ofReal_ne_zero.2 hM.ne'))).continuousAt).mul
      (hΓ.pow 2)).mul ((hΨ'd.differentiableAt (hV.mem_nhds (hsub hs1))).continuousAt)
  have hne : ∀ t : ℝ, ((σ : ℂ) + t * I - 1) ^ 3 ≠ 0 := fun t => pow_ne_zero _ fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hA : Integrable (fun t : ℝ => (M : ℂ) ^ ((σ : ℂ) + t * I) * Gamma ((σ : ℂ) + t * I) ^ 2 *
      Ψ' ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I - 1) ^ 3)⁻¹) := by
    obtain ⟨C, T, h⟩ := hdec 2 σ σ (by intro x hx; simp only [Set.mem_Ici]; linarith [hx.1])
    exact integrable_of_decay (hγ.mul ((((continuous_line σ).sub continuous_const).pow 3).inv₀ hne))
      (C := C) (T := max T 1) (decay_mul_inv_cube (f := fun s => (M : ℂ) ^ s * Gamma s ^ 2 * Ψ' s)
        (fun t ht => h σ ⟨le_rfl, le_rfl⟩ t ht))
  have hB : Continuous (fun t : ℝ => (d : ℂ) ^ ((σ : ℂ) + t * I - 1) *
      partialEuler α β α' β' U ((σ : ℂ) + t * I)) := by
    refine (((continuous_line σ).sub continuous_const).const_cpow
      (Or.inl (ofReal_ne_zero.2 hd.ne'))).mul ?_
    unfold partialEuler
    exact continuous_finsetProd _ fun p hp =>
      continuous_eulerFactor_line hC2 (Finset.mem_filter.1 hp).2 hσ
  have hBb : ∀ t : ℝ, ‖(d : ℂ) ^ ((σ : ℂ) + t * I - 1) *
      partialEuler α β α' β' U ((σ : ℂ) + t * I)‖ ≤
      d ^ (σ - 1) * 11 ^ ((Finset.range ⌈U⌉₊).filter Nat.Prime).card := by
    intro t
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hd]
    have : ((σ : ℂ) + t * I - 1).re = σ - 1 := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (norm_partialEuler_le hC2 U (by rw [hre]; exact hσ))
      (by positivity)
  refine (hA.bdd_mul hB.aestronglyMeasurable (ae_of_all _ hBb)).congr (ae_of_all _ fun t => ?_)
  simp only [oesterleIntegrand]
  rw [hΨ'eq _ (by rw [hre]; linarith)]
  ring

/-- The integrand of `J(U*)` is that of (3.1.1) minus that of `J(U)`. -/
lemma oesterleIntegrand_tail_eq (U σ t : ℝ) :
    oesterleIntegrand d M ψ (fun s => LSeries g s - partialEuler α β α' β' U s) σ t =
      oesterleIntegrand d M ψ (LSeries g) σ t -
        oesterleIntegrand d M ψ (partialEuler α β α' β' U) σ t := by
  simp only [oesterleIntegrand]
  ring

/-- **Oesterlé's fundamental identity `J(U) = -J(U*)`.**
Let $d > 0$ and $M > 0$ be real numbers and put $\gamma(s) = M^s \Gamma(s)^2$. Let
$\Psi(s) = \sum_{n \ge 1} \psi_n n^{-s}$ be a Dirichlet series converging absolutely for
$\operatorname{Re} s > 1$, and let $G(s) = \sum_{n \ge 1} g_n n^{-s}$ be a Dirichlet series
converging absolutely for $\operatorname{Re} s > 3/2$ that is an Euler product
$G = \prod_p G_p$ in which, for each prime $p$,
$$G_p(s) = \frac{(1 + \alpha_p p^{-s})(1 + \beta_p p^{-s})}
{(1 + \alpha'_p p^{-s})(1 + \beta'_p p^{-s})}$$
with complex numbers $\alpha_p, \beta_p, \alpha'_p, \beta'_p$ of absolute value at most
$\sqrt p$ (Oesterlé's condition (C2)). Suppose (condition (C3)) that the function
$F(s) = d^s \gamma(s) \Psi(s) G(s)$, $\operatorname{Re} s > 3/2$, extends to an entire function on
$\mathbb{C}$ that is of rapid decay at infinity in vertical strips (for every $k \ge 0$ and every
bounded interval $I$, $|F(\sigma + it)| |t|^k$ stays bounded as $|t| \to \infty$, uniformly for
$\sigma \in I$), satisfies $F(2 - s) = F(s)$ and has a zero of order at least $3$ at $s = 1$, that
is, $F(s) = (s - 1)^3 F_1(s)$ with $F_1$ entire. Suppose also, as in Oesterlé's condition (C4),
that $\Psi$ extends holomorphically to a neighbourhood of the half-plane
$\operatorname{Re} s \ge 1$ and that $\gamma\Psi$ is of rapid decay at infinity in every vertical
strip of that half-plane. Then for every $\sigma > 3/2$ (Oesterlé's (3.1.1))
$$\int_{\sigma - i\infty}^{\sigma + i\infty} d^{s-1} \gamma(s) \Psi(s) G(s) (s - 1)^{-3}
\,\frac{ds}{2\pi i} = 0.$$
For a real number $U \ge 1$ put (3.1.2)–(3.1.3)
$$G(U, s) = \prod_{p < U} G_p(s), \qquad
G(U^*, s) = G(s) - G(U, s) = G(U, s)\Big(\Big(\prod_{p \ge U} G_p(s)\Big) - 1\Big),$$
and let $J(U)$ and $J(U^*)$ be the integrals of (3.1.1) with $G(s)$ replaced by $G(U, s)$ and by
$G(U^*, s)$. These integrals converge absolutely and (3.1.4) $J(U) = -J(U^*)$.

Here $\Psi$ is `LSeries ψ`, $G$ is `LSeries g`, $G_p$ is `eulerFactor α β α' β' p`,
$G(U, \cdot)$ is `partialEuler α β α' β' U`, the integrals are `oesterleIntegral`, and the
holomorphic extension of $\Psi$ is `Ψ'` on the open set `V`. The identity of (3.1.3) is stated
for $\operatorname{Re} s > 3/2$ and every real $U$.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
exposé 631, Astérisque 121–122 (1985), 309–323, §3, conditions (C1)–(C4) (p. 314), and §3.1,
(3.1.1)–(3.1.4) (pp. 314–315). -/
theorem oesterle_fundamental_identity (hd : 0 < d) (hM : 0 < M)
    (_hψ : ∀ s : ℂ, 1 < s.re → LSeriesSummable ψ s)
    (_hg : ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable g s)
    (hprod : ∀ s : ℂ, 3 / 2 < s.re →
      HasProd (fun p : Nat.Primes => eulerFactor α β α' β' p s) (LSeries g s))
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    (F : ℂ → ℂ) (_hFd : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (d : ℂ) ^ s * ((M : ℂ) ^ s * Gamma s ^ 2) * LSeries ψ s * LSeries g s)
    (hFdec : RapidDecayInStrips F Set.univ) (hsymm : ∀ s, F (2 - s) = F s)
    (hzero : ∃ F₁ : ℂ → ℂ, Differentiable ℂ F₁ ∧ ∀ s, F s = (s - 1) ^ 3 * F₁ s)
    (hC4 : ∃ (V : Set ℂ) (Ψ' : ℂ → ℂ), IsOpen V ∧ {s | 1 ≤ s.re} ⊆ V ∧ DifferentiableOn ℂ Ψ' V ∧
      (∀ s, 1 < s.re → Ψ' s = LSeries ψ s) ∧
      RapidDecayInStrips (fun s => (M : ℂ) ^ s * Gamma s ^ 2 * Ψ' s) (Set.Ici 1))
    {σ : ℝ} (hσ : 3 / 2 < σ) :
    oesterleIntegral d M ψ (LSeries g) σ = 0 ∧
    (∀ U : ℝ, 1 ≤ U → Integrable (oesterleIntegrand d M ψ (partialEuler α β α' β' U) σ) ∧
      Integrable (oesterleIntegrand d M ψ (fun s => LSeries g s - partialEuler α β α' β' U s) σ) ∧
      oesterleIntegral d M ψ (partialEuler α β α' β' U) σ =
        -oesterleIntegral d M ψ (fun s => LSeries g s - partialEuler α β α' β' U s) σ) ∧
    (∀ (U : ℝ) (s : ℂ), 3 / 2 < s.re → LSeries g s - partialEuler α β α' β' U s =
      partialEuler α β α' β' U s *
        ((∏' p : {p : Nat.Primes // U ≤ (p : ℝ)}, eulerFactor α β α' β' p s) - 1)) := by
  obtain ⟨F₁, hF₁, hF⟩ := hzero
  have h0 := oesterleIntegral_lSeries_eq_zero hd hFeq hFdec hsymm hF₁ hF hσ
  refine ⟨h0, fun U _ => ?_, fun U s hs => lSeries_sub_partialEuler hprod hC2 U hs⟩
  have hfull := integrable_oesterleIntegrand_lSeries hd hFeq hFdec hF₁ hF hσ
  have hpart := integrable_oesterleIntegrand_partialEuler hd hM hC2 hC4 hσ U
  have e : oesterleIntegrand d M ψ (fun s => LSeries g s - partialEuler α β α' β' U s) σ =
      oesterleIntegrand d M ψ (LSeries g) σ -
        oesterleIntegrand d M ψ (partialEuler α β α' β' U) σ :=
    funext (oesterleIntegrand_tail_eq U σ)
  refine ⟨hpart, e ▸ hfull.sub hpart, ?_⟩
  unfold oesterleIntegral at h0 ⊢
  rw [e]
  simp only [Pi.sub_apply]
  rw [integral_sub hfull hpart, smul_sub, h0, zero_sub, neg_neg]

end OesterleFundamentalIdentity
end MetaMathlibExt
