/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Parabolic, strictly hyperbolic and elliptic Möbius transformations

A Möbius (linear fractional) transformation `S z = (a * z + b) / (c * z + d)` of the Riemann
sphere is the action of `g = !![a, b; c, d] : GL (Fin 2) ℂ` on `OnePoint ℂ`
(`OnePoint.instGLAction`). Every notion below is stated through this action, so it depends only
on the transformation `S` and not on the matrix chosen to represent it.

A transformation with two distinct fixed points `α ≠ β` has the normal form (12)
`(S z - α) / (S z - β) = k * (z - α) / (z - β)`. With `T z = (z - α) / (z - β)`, a Möbius map
sending `α` to `0` and `β` to `∞`, (12) reads `T (S z) = k * T z`. `Moebius.IsMultiplier g k`
says this for some Möbius map `T`, on the whole sphere (so fixed points at `∞` are allowed); the
points `T⁻¹ 0` and `T⁻¹ ∞` are then two distinct fixed points of `S`.

## Main definitions

* `Moebius.IsMultiplier`: `k` is a multiplier of `S` in the normal form (12).
* `Moebius.IsParabolic`: `S` is the identity or has exactly one fixed point.
* `Moebius.IsStrictlyHyperbolic`: `k > 0` in (12) but `k ≠ 1`.
* `Moebius.IsElliptic`: `|k| = 1` in (12) but `S` is not the identity.

## Main results

* `Moebius.isMultiplier_iff`: (12) holds for some `T` iff it holds for every Möbius map `T`
  sending the two fixed points to `0` and `∞`.
* `Moebius.sub_div_sub_eq_mul_sub_div_sub`: (12) as an identity of complex numbers when both
  fixed points are finite.
* `Moebius.isParabolic_iff_discr_eq_zero`: `S` is parabolic iff `tr g ^ 2 - 4 * det g = 0`.
* `Moebius.isStrictlyHyperbolic_iff_trace_sq_div_det`: `S` is strictly hyperbolic iff
  `tr g ^ 2 / det g` is a real number `> 4`.
* `Moebius.isElliptic_iff_trace_sq_div_det`: `S` is elliptic iff `tr g ^ 2 / det g` is a real
  number in `[0, 4)`.
* `Moebius.classification_by_trace`: the three criteria together.

The proofs go through fixed points. A nonzero discriminant gives two distinct fixed points (the
quadratic formula, or `∞` and one finite point); a Möbius map sending them to `0` and `∞`
conjugates `g` to `z ↦ k * z`; and trace and determinant are conjugation invariants, so
`tr g ^ 2 * k = det g * (k + 1) ^ 2`, that is, `tr g ^ 2 / det g = k + 1 / k + 2`. Mathlib has
the action, the fixed-point polynomial and the unique fixed point of a parabolic element
(`Matrix.GeneralLinearGroup.IsParabolic.smul_eq_self_iff`), but not the normal form (12), its
multiplier, or the trace classification of Möbius maps over `ℂ`; MathlibExt had none of these.

Note that `Moebius.IsParabolic` contains the identity (scalar matrices), while Mathlib's
`Matrix.GeneralLinearGroup.IsParabolic` (that is, `Matrix.IsParabolic`) excludes scalar matrices;
the two agree on non-scalar `g`. Mathlib's `Matrix.IsHyperbolic` and `Matrix.IsElliptic` are
discriminant-sign notions over ordered rings, not the multiplier notions of (12). The `Moebius`
namespace keeps these names apart.

Rubric-guided revision of v1 ComplexVariables target 08 (`MoebiusTrans.IsParabolic` in
`v1/Atlas/ComplexVariables/code/Lecture7.lean` at commit 6191bf1ba03d204784385ef5be2472be88035b93),
Lecture 7, Definition 1. The archived formalization defined only the parabolic clause: the
strictly hyperbolic and elliptic clauses and the normal form (12) with its multiplier `k` were
missing. It also used a parallel `MoebiusTrans` structure (duplicating the project's
`Lecture6.MoebiusTransformation`) whose `eval` returns a junk value at the pole, with an ad hoc
`IsFixedPointAtInfty` predicate and `c * z + d ≠ 0` guards; here Mathlib's `GL (Fin 2) ℂ` action
on `OnePoint ℂ` treats `∞` as an ordinary point. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Matrix OnePoint

namespace Moebius

/-- `k` is a multiplier of `g` in the normal form (12): there is a Möbius map `T` with
`T (g x) = k * T x` for every `x` on the Riemann sphere. The fixed points of (12) are
`T⁻¹ 0` and `T⁻¹ ∞`, and `T` may be any map sending them to `0` and `∞`
(`Moebius.isMultiplier_iff`). -/
@[expose] public def IsMultiplier (g : GL (Fin 2) ℂ) (k : ℂ) : Prop :=
  ∃ T : GL (Fin 2) ℂ, ∀ x : OnePoint ℂ, T • g • x = (T • x).map (k * ·)

/-- A Möbius transformation is *parabolic* if it is the identity or has exactly one fixed point
on the Riemann sphere. -/
@[expose] public def IsParabolic (g : GL (Fin 2) ℂ) : Prop :=
  (∀ x : OnePoint ℂ, g • x = x) ∨ ∃! x : OnePoint ℂ, g • x = x

/-- A Möbius transformation is *strictly hyperbolic* if its multiplier `k` in the normal
form (12) satisfies `k > 0` and `k ≠ 1`. -/
@[expose] public def IsStrictlyHyperbolic (g : GL (Fin 2) ℂ) : Prop :=
  ∃ k : ℝ, IsMultiplier g k ∧ 0 < k ∧ k ≠ 1

/-- A Möbius transformation is *elliptic* if its multiplier `k` in the normal form (12)
satisfies `|k| = 1` and the transformation is not the identity. -/
@[expose] public def IsElliptic (g : GL (Fin 2) ℂ) : Prop :=
  (∃ k : ℂ, IsMultiplier g k ∧ ‖k‖ = 1) ∧ ¬∀ x : OnePoint ℂ, g • x = x

variable {g : GL (Fin 2) ℂ}

/-- A finite point `z` is fixed iff it is a root of `c * z ^ 2 + (d - a) * z - b`. -/
private lemma smul_coe_eq_self_iff {z : ℂ} :
    g • (z : OnePoint ℂ) = z ↔ g 1 0 * z ^ 2 + (g 1 1 - g 0 0) * z - g 0 1 = 0 := by
  rw [← GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff]
  simp only [GeneralLinearGroup.fixpointPolynomial, map_sub, map_mul, map_add,
    Polynomial.aeval_X_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    Algebra.algebraMap_self_apply]

/-- A Möbius transformation that fixes every point has a scalar matrix, so discriminant `0`. -/
private lemma discr_eq_zero_of_forall_smul_eq (h : ∀ x : OnePoint ℂ, g • x = x) :
    g.val.discr = 0 := by
  have h10 : g 1 0 = 0 := smul_infty_eq_self_iff.mp (h ∞)
  have hdet := g.det_ne_zero
  rw [det_fin_two, h10, mul_zero, sub_zero] at hdet
  have h11 : g 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have h0 := h ((0 : ℂ) : OnePoint ℂ)
  have h1 := h ((1 : ℂ) : OnePoint ℂ)
  rw [smul_some_eq_ite] at h0 h1
  have h01 : g 0 1 = 0 := by simpa [h10, h11, OnePoint.coe_eq_coe] using h0
  have h00 : g 0 0 = g 1 1 := by
    simp only [h10, h01, zero_add, mul_one, add_zero, h11, ↓reduceIte,
      OnePoint.coe_eq_coe] at h1
    exact (div_eq_one_iff_eq h11).mp h1
  rw [discr_fin_two, trace_fin_two, det_fin_two, h10, h01, h00]
  ring

/-- If the discriminant is nonzero, the transformation has two distinct fixed points. -/
private lemma exists_ne_fixed_of_discr_ne_zero (hd : g.val.discr ≠ 0) :
    ∃ α β : OnePoint ℂ, α ≠ β ∧ g • α = α ∧ g • β = β := by
  rw [discr_fin_two, trace_fin_two, det_fin_two] at hd
  by_cases hc : g 1 0 = 0
  · have had : g 1 1 - g 0 0 ≠ 0 := by
      intro h
      apply hd
      rw [hc]
      linear_combination (g 1 1 - g 0 0) * h
    refine ⟨∞, ↑(g 0 1 / (g 1 1 - g 0 0)), OnePoint.infty_ne_coe _,
      smul_infty_eq_self_iff.mpr hc, ?_⟩
    have e : (g 1 1 - g 0 0) * (g 0 1 / (g 1 1 - g 0 0)) = g 0 1 := by field_simp
    rw [smul_coe_eq_self_iff]
    linear_combination (g 0 1 / (g 1 1 - g 0 0)) ^ 2 * hc + e
  · obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1))
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hd
      simp only [discrim, mul_zero] at hs
      linear_combination hs
    have hroot (z : ℂ) (hz : z = (-(g 1 1 - g 0 0) + s) / (2 * g 1 0) ∨
        z = (-(g 1 1 - g 0 0) - s) / (2 * g 1 0)) : g • (z : OnePoint ℂ) = z := by
      rw [smul_coe_eq_self_iff]
      linear_combination (quadratic_eq_zero_iff hc hs z).mpr hz
    refine ⟨_, _, ?_, hroot _ (Or.inl rfl), hroot _ (Or.inr rfl)⟩
    rw [Ne, OnePoint.coe_eq_coe, div_left_inj' (mul_ne_zero two_ne_zero hc)]
    intro h
    apply hs0
    linear_combination h / 2

/-- For finite `α ≠ β`, the map `T z = (z - α) / (z - β)` of (12), given by `!![1, -α; 1, -β]`,
is a Möbius map sending `β` to `∞`. -/
private lemma exists_smul_eq_sub_div_sub {α β : ℂ} (h : α ≠ β) :
    ∃ T : GL (Fin 2) ℂ, T • (β : OnePoint ℂ) = ∞ ∧
      ∀ z : ℂ, z ≠ β → T • (z : OnePoint ℂ) = ↑((z - α) / (z - β)) := by
  have hdet : (!![1, -α; 1, -β] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [det_fin_two_of]
    intro h'
    apply sub_ne_zero.mpr h
    linear_combination h'
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_, fun z hz ↦ ?_⟩
  · rw [smul_some_eq_ite]
    simp
  · have hz' : z + -β ≠ 0 := by rwa [← sub_eq_add_neg, sub_ne_zero]
    rw [smul_some_eq_ite]
    simp [hz', sub_eq_add_neg]

/-- Two distinct points of the Riemann sphere can be sent to `0` and `∞` by a Möbius map. -/
private lemma exists_smul_eq_zero_and_smul_eq_infty {α β : OnePoint ℂ} (h : α ≠ β) :
    ∃ T : GL (Fin 2) ℂ, T • α = ((0 : ℂ) : OnePoint ℂ) ∧ T • β = ∞ := by
  cases α with
  | infty =>
    cases β with
    | infty => exact absurd rfl h
    | coe b =>
      refine ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, -b] (by simp [det_fin_two]), ?_, ?_⟩
      · rw [smul_infty_eq_ite]
        simp
      · rw [smul_some_eq_ite]
        simp
  | coe a =>
    cases β with
    | infty =>
      refine ⟨GeneralLinearGroup.mkOfDetNeZero !![1, -a; 0, 1] (by simp [det_fin_two]), ?_, ?_⟩
      · rw [smul_some_eq_ite]
        simp
      · rw [smul_infty_eq_ite]
        simp
    | coe b =>
      have hab : a ≠ b := fun hab ↦ h (by rw [hab])
      obtain ⟨T, hTb, hT⟩ := exists_smul_eq_sub_div_sub hab
      exact ⟨T, by rw [hT a hab, sub_self, zero_div], hTb⟩

/-- A Möbius map fixing `0` and `∞` is `z ↦ c * z`. -/
private lemma smul_eq_map_mul {m : GL (Fin 2) ℂ}
    (hm0 : m • ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ))
    (hminf : m • (∞ : OnePoint ℂ) = ∞) (y : OnePoint ℂ) :
    m • y = y.map (m 0 0 / m 1 1 * ·) := by
  have h10 : m 1 0 = 0 := smul_infty_eq_self_iff.mp hminf
  rw [smul_some_eq_ite] at hm0
  have h11 : m 1 1 ≠ 0 := by
    intro h11
    simp [h10, h11] at hm0
  have h01 : m 0 1 = 0 := by simpa [h10, h11, OnePoint.coe_eq_coe] using hm0
  cases y with
  | infty => simpa using hminf
  | coe z =>
    rw [smul_some_eq_ite]
    simp only [h10, h01, zero_mul, zero_add, add_zero, h11, ↓reduceIte, OnePoint.map_some,
      OnePoint.coe_eq_coe]
    ring

/-- A transformation with two distinct fixed points has a normal form (12). -/
private lemma exists_isMultiplier {α β : OnePoint ℂ} (hne : α ≠ β) (hα : g • α = α)
    (hβ : g • β = β) : ∃ k, IsMultiplier g k := by
  obtain ⟨T, hTα, hTβ⟩ := exists_smul_eq_zero_and_smul_eq_infty hne
  set m := T * g * T⁻¹ with hm
  have hm0 : m • ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
    rw [← hTα, hm, mul_smul, mul_smul, inv_smul_smul, hα]
  have hminf : m • (∞ : OnePoint ℂ) = ∞ := by
    rw [← hTβ, hm, mul_smul, mul_smul, inv_smul_smul, hβ]
  refine ⟨m 0 0 / m 1 1, T, fun x ↦ ?_⟩
  rw [← smul_eq_map_mul hm0 hminf, hm, mul_smul, mul_smul, inv_smul_smul]

/-- The normal form (12) does not depend on the choice of `T`: `k` is a multiplier of `g` iff
`g` has two distinct fixed points `α, β` such that *every* Möbius map `T` with `T α = 0` and
`T β = ∞` satisfies `T (g x) = k * T x`. For finite `α, β` one such map is the map
`T z = (z - α) / (z - β)` of (12), given by `!![1, -α; 1, -β]`
(`Moebius.sub_div_sub_eq_mul_sub_div_sub`). -/
public theorem isMultiplier_iff {k : ℂ} :
    IsMultiplier g k ↔ ∃ α β : OnePoint ℂ, α ≠ β ∧ g • α = α ∧ g • β = β ∧
      ∀ T : GL (Fin 2) ℂ, T • α = ((0 : ℂ) : OnePoint ℂ) → T • β = ∞ →
        ∀ x : OnePoint ℂ, T • g • x = (T • x).map (k * ·) := by
  constructor
  · rintro ⟨T₁, hT₁⟩
    refine ⟨T₁⁻¹ • ((0 : ℂ) : OnePoint ℂ), T₁⁻¹ • ∞, ?_, ?_, ?_, fun T hT0 hTinf x ↦ ?_⟩
    · rw [Ne, smul_left_cancel_iff]
      exact OnePoint.coe_ne_infty _
    · rw [← smul_left_cancel_iff T₁, hT₁, smul_inv_smul]
      simp
    · rw [← smul_left_cancel_iff T₁, hT₁, smul_inv_smul]
      simp
    · -- `U = T * T₁⁻¹` fixes `0` and `∞`, so it is `z ↦ c * z`, which commutes with `z ↦ k * z`.
      have hU0 : (T * T₁⁻¹) • ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
        rw [mul_smul, hT0]
      have hUinf : (T * T₁⁻¹) • (∞ : OnePoint ℂ) = ∞ := by
        rw [mul_smul, hTinf]
      rw [← inv_mul_cancel_right T T₁, mul_smul (T * T₁⁻¹) T₁, mul_smul (T * T₁⁻¹) T₁, hT₁,
        smul_eq_map_mul hU0 hUinf, smul_eq_map_mul hU0 hUinf]
      generalize T₁ • x = y
      cases y with
      | infty => simp
      | coe z =>
        simp only [OnePoint.map_some, OnePoint.coe_eq_coe]
        ring
  · rintro ⟨α, β, hne, -, -, hT⟩
    obtain ⟨T, hTα, hTβ⟩ := exists_smul_eq_zero_and_smul_eq_infty hne
    exact ⟨T, hT T hTα hTβ⟩

/-- The normal form (12) as an identity of complex numbers. Let `α ≠ β` be finite and suppose
every Möbius map `T` with `T α = 0` and `T β = ∞` satisfies `T (g x) = k * T x` (the condition
of `Moebius.isMultiplier_iff`). Then `(w - α) / (w - β) = k * ((z - α) / (z - β))` whenever
`z ≠ β` and `w = g z` is finite. -/
public theorem sub_div_sub_eq_mul_sub_div_sub {α β k : ℂ} (hne : α ≠ β)
    (hT : ∀ T : GL (Fin 2) ℂ, T • (α : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) →
      T • (β : OnePoint ℂ) = ∞ → ∀ x : OnePoint ℂ, T • g • x = (T • x).map (k * ·))
    {z w : ℂ} (hz : z ≠ β) (hw : g • (z : OnePoint ℂ) = w) :
    (w - α) / (w - β) = k * ((z - α) / (z - β)) := by
  obtain ⟨T, hTβ, hTz⟩ := exists_smul_eq_sub_div_sub hne
  have h := hT T (by rw [hTz α hne, sub_self, zero_div]) hTβ z
  rw [hw, hTz z hz, OnePoint.map_some] at h
  have hwβ : w ≠ β := by
    rintro rfl
    rw [hTβ] at h
    exact OnePoint.infty_ne_coe _ h
  rwa [hTz w hwβ, OnePoint.coe_eq_coe] at h

/-- The multiplier `k` is nonzero and satisfies `tr g ^ 2 * k = det g * (k + 1) ^ 2`, that is,
`tr g ^ 2 / det g = k + 1 / k + 2`. -/
private lemma IsMultiplier.trace_sq {k : ℂ} (hk : IsMultiplier g k) :
    k ≠ 0 ∧ g.val.trace ^ 2 * k = g.val.det * (k + 1) ^ 2 := by
  obtain ⟨T, hT⟩ := hk
  set m := T * g * T⁻¹ with hm
  have key (y : OnePoint ℂ) : m • y = y.map (k * ·) := by
    have := hT (T⁻¹ • y)
    rwa [smul_inv_smul, ← mul_smul, ← mul_smul, ← hm] at this
  have h10 : m 1 0 = 0 := smul_infty_eq_self_iff.mp (by simpa using key ∞)
  have h0 := key ((0 : ℂ) : OnePoint ℂ)
  have h1 := key ((1 : ℂ) : OnePoint ℂ)
  rw [smul_some_eq_ite] at h0 h1
  have h11 : m 1 1 ≠ 0 := by
    intro h11
    simp [h10, h11] at h0
  have h01 : m 0 1 = 0 := by simpa [h10, h11, OnePoint.coe_eq_coe] using h0
  have h00 : m 0 0 = k * m 1 1 := by
    simp only [h10, h01, zero_add, mul_one, add_zero, h11, ↓reduceIte,
      OnePoint.map_some, OnePoint.coe_eq_coe] at h1
    exact (div_eq_iff h11).mp h1
  have htr : g.val.trace = m.val.trace := by
    rw [hm, Units.val_mul, Units.val_mul, trace_units_conj]
  have hdet : g.val.det = m.val.det := by
    rw [hm, Units.val_mul, Units.val_mul, det_units_conj]
  have hgdet := g.det_ne_zero
  rw [hdet, det_fin_two, h10, h01, h00] at hgdet
  rw [htr, hdet, trace_fin_two, det_fin_two, h10, h01, h00]
  exact ⟨fun hk0 ↦ hgdet (by simp [hk0]), by ring⟩

/-- A multiplier `k` satisfies `tr g ^ 2 / det g * k = (k + 1) ^ 2`. -/
private lemma IsMultiplier.trace_sq_div_det_mul {k : ℂ} (hk : IsMultiplier g k) :
    g.val.trace ^ 2 / g.val.det * k = (k + 1) ^ 2 := by
  rw [div_mul_eq_mul_div, div_eq_iff g.det_ne_zero, hk.trace_sq.2]
  ring

/-- The multiplier `1` occurs only for the identity. -/
private lemma IsMultiplier.forall_smul_eq (hk : IsMultiplier g 1) (x : OnePoint ℂ) :
    g • x = x := by
  obtain ⟨T, hT⟩ := hk
  rw [← smul_left_cancel_iff T, hT x]
  generalize T • x = y
  cases y <;> simp

/-- A real value `r ≠ 4` of `tr g ^ 2 / det g` forces a nonzero discriminant. -/
private lemma discr_ne_zero_of_trace_sq_div_det_eq {r : ℝ} (hr : r ≠ 4)
    (ht : g.val.trace ^ 2 / g.val.det = r) : g.val.discr ≠ 0 := by
  intro hd
  rw [div_eq_iff g.det_ne_zero] at ht
  rw [discr_fin_two, ht, ← sub_mul, mul_eq_zero, sub_eq_zero] at hd
  exact hr (by exact_mod_cast hd.resolve_right g.det_ne_zero)

/-- If `r * k = (k + 1) ^ 2` for a real `r > 4`, then `k` is real, positive and different
from `1`. -/
private lemma exists_real_of_mul_eq_sq {r : ℝ} {k : ℂ} (h : (r : ℂ) * k = (k + 1) ^ 2)
    (hr : 4 < r) : ∃ ρ : ℝ, k = ρ ∧ 0 < ρ ∧ ρ ≠ 1 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, sq,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_mul, sub_zero,
    add_zero] at hre him
  have hy : k.im = 0 := by
    by_contra hy
    have hx : r = 2 * (k.re + 1) := mul_right_cancel₀ hy (by linear_combination him)
    subst hx
    nlinarith [mul_self_pos.mpr hy, mul_pos (by linarith : (0 : ℝ) < k.re - 1)
      (by linarith : (0 : ℝ) < k.re + 1)]
  rw [hy, mul_zero, sub_zero] at hre
  refine ⟨k.re, Complex.ext (by simp) (by simpa using hy), ?_, ?_⟩
  · nlinarith [mul_self_nonneg (k.re + 1), mul_self_nonneg k.re]
  · rintro h1
    rw [h1] at hre
    linarith

/-- If `r * k = (k + 1) ^ 2` for a real `0 ≤ r < 4`, then `|k| = 1`. -/
private lemma norm_eq_one_of_mul_eq_sq {r : ℝ} {k : ℂ} (h : (r : ℂ) * k = (k + 1) ^ 2)
    (hr0 : 0 ≤ r) (hr4 : r < 4) : ‖k‖ = 1 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, sq,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_mul, sub_zero,
    add_zero] at hre him
  have hsq : k.re * k.re + k.im * k.im = 1 := by
    by_cases hy : k.im = 0
    · rw [hy, mul_zero, sub_zero] at hre
      have hr : r = 0 := by nlinarith [sq_nonneg (2 * k.re + 2 - r)]
      rw [hr, zero_mul, eq_comm, mul_self_eq_zero] at hre
      rw [hy, show k.re = -1 by linarith]
      norm_num
    · have hx : r = 2 * (k.re + 1) := mul_right_cancel₀ hy (by linear_combination him)
      rw [hx] at hre
      linear_combination hre
  rw [← pow_left_inj₀ (norm_nonneg k) zero_le_one two_ne_zero, Complex.sq_norm,
    Complex.normSq_apply, hsq, one_pow]

/-- A Möbius transformation is parabolic iff its discriminant `tr g ^ 2 - 4 * det g` vanishes. -/
public theorem isParabolic_iff_discr_eq_zero (g : GL (Fin 2) ℂ) :
    IsParabolic g ↔ g.val.discr = 0 := by
  refine ⟨?_, fun hd ↦ ?_⟩
  · rintro (hid | ⟨x, -, huniq⟩)
    · exact discr_eq_zero_of_forall_smul_eq hid
    · by_contra hd
      obtain ⟨α, β, hne, hα, hβ⟩ := exists_ne_fixed_of_discr_ne_zero hd
      exact hne ((huniq α hα).trans (huniq β hβ).symm)
  · by_cases hs : g.val ∈ Set.range (scalar _)
    · left
      have hP := GeneralLinearGroup.fixpointPolynomial_eq_zero_iff.mpr hs
      intro x
      cases x with
      | infty =>
        refine smul_infty_eq_self_iff.mpr ?_
        simpa [GeneralLinearGroup.fixpointPolynomial] using congr(Polynomial.coeff $hP 2)
      | coe z =>
        rw [← GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff, hP, map_zero]
    · have hpar : GeneralLinearGroup.IsParabolic g := ⟨hs, hd⟩
      right
      exact ⟨_, (GeneralLinearGroup.IsParabolic.smul_eq_self_iff hpar).mpr rfl,
        fun y ↦ (GeneralLinearGroup.IsParabolic.smul_eq_self_iff hpar).mp⟩

/-- A Möbius transformation is strictly hyperbolic iff `tr g ^ 2 / det g` is a real number
`> 4`. -/
public theorem isStrictlyHyperbolic_iff_trace_sq_div_det (g : GL (Fin 2) ℂ) :
    IsStrictlyHyperbolic g ↔ ∃ r : ℝ, 4 < r ∧ g.val.trace ^ 2 / g.val.det = r := by
  constructor
  · rintro ⟨ρ, hk, hρ, hρ1⟩
    have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    refine ⟨(ρ + 1) ^ 2 / ρ, ?_, ?_⟩
    · rw [lt_div_iff₀ hρ]
      nlinarith [mul_self_pos.mpr (sub_ne_zero.mpr hρ1)]
    · exact_mod_cast (eq_div_iff hρ0).mpr hk.trace_sq_div_det_mul
  · rintro ⟨r, hr, ht⟩
    obtain ⟨α, β, hne, hα, hβ⟩ :=
      exists_ne_fixed_of_discr_ne_zero (discr_ne_zero_of_trace_sq_div_det_eq hr.ne' ht)
    obtain ⟨k, hk⟩ := exists_isMultiplier hne hα hβ
    obtain ⟨ρ, rfl, hρ, hρ1⟩ :=
      exists_real_of_mul_eq_sq (r := r) (k := k) (ht ▸ hk.trace_sq_div_det_mul) hr
    exact ⟨ρ, hk, hρ, hρ1⟩

/-- A Möbius transformation is elliptic iff `tr g ^ 2 / det g` is a real number in `[0, 4)`. -/
public theorem isElliptic_iff_trace_sq_div_det (g : GL (Fin 2) ℂ) :
    IsElliptic g ↔ ∃ r : ℝ, 0 ≤ r ∧ r < 4 ∧ g.val.trace ^ 2 / g.val.det = r := by
  constructor
  · rintro ⟨⟨k, hk, hk1⟩, hid⟩
    have hk0 := hk.trace_sq.1
    have hkne : k ≠ 1 := by
      rintro rfl
      exact hid hk.forall_smul_eq
    have hsq : k.re * k.re + k.im * k.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hk1, one_pow]
    have hre1 : k.re ≠ 1 := by
      intro h1
      apply hkne
      refine Complex.ext (by simpa using h1) ?_
      rw [h1] at hsq
      simpa using (mul_self_eq_zero.mp (by linarith : k.im * k.im = 0))
    have hle : |k.re| ≤ 1 := hk1 ▸ Complex.abs_re_le_norm k
    refine ⟨2 * k.re + 2, by linarith [neg_le_of_abs_le hle], by
      linarith [lt_of_le_of_ne (le_of_abs_le hle) hre1], ?_⟩
    apply mul_right_cancel₀ hk0
    rw [hk.trace_sq_div_det_mul]
    apply Complex.ext
    · simp only [sq, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
        Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      linear_combination -hsq
    · simp only [sq, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re,
        Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
  · rintro ⟨r, hr0, hr4, ht⟩
    have hd := discr_ne_zero_of_trace_sq_div_det_eq hr4.ne ht
    obtain ⟨α, β, hne, hα, hβ⟩ := exists_ne_fixed_of_discr_ne_zero hd
    obtain ⟨k, hk⟩ := exists_isMultiplier hne hα hβ
    exact ⟨⟨k, hk, norm_eq_one_of_mul_eq_sq (r := r) (k := k)
      (ht ▸ hk.trace_sq_div_det_mul) hr0 hr4⟩,
      fun hid ↦ hd (discr_eq_zero_of_forall_smul_eq hid)⟩

/-- **Classification by trace.** For `g : GL (Fin 2) ℂ`, with `tr g ^ 2 / det g` the
scale-invariant trace (equal to `k + 1 / k + 2` for a multiplier `k` in the normal form (12)):
* `g` is parabolic iff `discr g = tr g ^ 2 - 4 * det g = 0`;
* `g` is strictly hyperbolic iff `tr g ^ 2 / det g` is a real number `> 4`;
* `g` is elliptic iff `tr g ^ 2 / det g` is a real number in `[0, 4)`. -/
public theorem classification_by_trace (g : GL (Fin 2) ℂ) :
    (IsParabolic g ↔ g.val.discr = 0) ∧
    (IsStrictlyHyperbolic g ↔ ∃ r : ℝ, 4 < r ∧ g.val.trace ^ 2 / g.val.det = r) ∧
    (IsElliptic g ↔ ∃ r : ℝ, 0 ≤ r ∧ r < 4 ∧ g.val.trace ^ 2 / g.val.det = r) :=
  ⟨isParabolic_iff_discr_eq_zero g, isStrictlyHyperbolic_iff_trace_sq_div_det g,
    isElliptic_iff_trace_sq_div_det g⟩

end Moebius
