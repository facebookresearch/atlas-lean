/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Uniqueness of minimal Weierstrass equations

Let `R` be a discrete valuation ring with fraction field `K`, and let `W` be a Weierstrass curve
over `K` with nonzero discriminant (`W.IsElliptic`). We prove that a minimal Weierstrass equation
is unique up to a change of variables with coefficients in `R` and unit scaling factor:

* `WeierstrassCurve.valuation_Δ_eq_of_isMinimal`: if `W` and `C • W` are both minimal, their
  discriminants have the same valuation (no ellipticity hypothesis needed).
* `WeierstrassCurve.exists_unit_eq_u_of_isMinimal`: if moreover `W.IsElliptic`, the scaling
  factor `C.u ∈ Kˣ` is the image of a unit of `R` (with the transformation law `ω' = u ω` of the
  invariant differential, this is the uniqueness of the invariant differential of a minimal
  equation up to `R*`, Silverman VII.1.3(c)).
* `WeierstrassCurve.exists_baseChange_eq_of_isMinimal`: if `W.IsElliptic` and `W`, `C • W` are
  both minimal, then `C = C'⁄K` for some change of variables `C'` over `R`
  (i.e. `u ∈ Rˣ` and `r, s, t ∈ R`).
* `WeierstrassCurve.isMinimal_baseChange_smul`: conversely, a change of variables over `R`
  takes a minimal equation to a minimal equation.
* `WeierstrassCurve.isMinimal_smul_iff`: the two combined: for `W` minimal and elliptic,
  `C • W` is minimal if and only if `C` comes from a change of variables over `R`.

The ellipticity hypothesis cannot be dropped: for `W : y² = x³` (discriminant `0`) every integral
equation `C • W` is minimal, including those with non-unit scaling factor.

The integrality of `r, s, t` once `u` is known to be a unit is Mathlib's
`WeierstrassCurve.variableChange_integral_of_u_integral` (proved there via integral closedness);
the new input here is that the scaling factor of a change between minimal equations is a unit.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009,
  Chapter VII, Proposition 1.3, pp. 186–187: part (b) (a minimal Weierstrass equation is unique
  up to a change of coordinates with `u ∈ R*`, `r, s, t ∈ R`) and part (c) (the invariant
  differential of a minimal equation is unique up to `R*`). The parts are as read by the
  reviewer of this file; the book itself was not read here.
* B. Conrad, *Minimal models for elliptic curves* (21 November 2015), §2: Corollary 2.9
  (isomorphisms between planar integral Weierstrass models are given by `u ∈ R×`, `r, s, t ∈ R`),
  Corollary 2.10 and the paragraph after it on p. 6 (the `R`-line of invariant differentials and
  the uniqueness of minimal Weierstrass models, citing Silverman VII.1.3 for the direct
  calculation that is carried out here).
-/

@[expose] public section

namespace WeierstrassCurve

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- If `W` is minimal and `C • W` is integral, then the valuation of the discriminant of `C • W`
is at most that of `W` (multiplicative valuation, so "at most" means "order at least"). -/
theorem valuation_Δ_le_of_isMinimal {W : WeierstrassCurve K} [hW : IsMinimal R W]
    (C : VariableChange K) [IsIntegral R (C • W)] :
    valuation K (maximalIdeal R) (C • W).Δ ≤ valuation K (maximalIdeal R) W.Δ := by
  have key : valuation_Δ_aux R (C • W) ≤ valuation_Δ_aux R W := by
    rcases le_total (valuation_Δ_aux R (C • W)) (valuation_Δ_aux R ((1 : VariableChange K) • W))
      with h | h
    · simpa using h
    · simpa using hW.val_Δ_maximal.2 (j := C) ‹_› h
  have h₁ := valuation_Δ_aux_eq_of_isIntegral R (C • W)
  have h₂ := valuation_Δ_aux_eq_of_isIntegral R W
  rw [← h₁, ← h₂]
  exact_mod_cast key

/-- If `W` and `C • W` are both minimal Weierstrass equations over the fraction field `K` of a
discrete valuation ring `R`, then their discriminants have the same valuation. -/
theorem valuation_Δ_eq_of_isMinimal (W : WeierstrassCurve K) (C : VariableChange K)
    [IsMinimal R W] [IsMinimal R (C • W)] :
    valuation K (maximalIdeal R) (C • W).Δ = valuation K (maximalIdeal R) W.Δ := by
  refine le_antisymm (valuation_Δ_le_of_isMinimal R C) ?_
  have : IsIntegral R (C⁻¹ • C • W) := by rw [inv_smul_smul]; infer_instance
  simpa using valuation_Δ_le_of_isMinimal R (W := C • W) C⁻¹

/-- If `W` is elliptic and `W`, `C • W` are both minimal, then the scaling factor `C.u` has
valuation one. -/
theorem valuation_u_eq_one_of_isMinimal (W : WeierstrassCurve K) [W.IsElliptic]
    (C : VariableChange K) [IsMinimal R W] [IsMinimal R (C • W)] :
    valuation K (maximalIdeal R) (C.u : K) = 1 := by
  have h := valuation_Δ_eq_of_isMinimal R W C
  rw [variableChange_Δ, map_mul, map_pow] at h
  have hΔ : valuation K (maximalIdeal R) W.Δ ≠ 0 := by
    simpa using W.isUnit_Δ.ne_zero
  have h12 : valuation K (maximalIdeal R) ((C.u⁻¹ : Kˣ) : K) ^ 12 = 1 := by
    simpa using mul_right_cancel₀ hΔ (h.trans (one_mul _).symm)
  have h1 : valuation K (maximalIdeal R) ((C.u⁻¹ : Kˣ) : K) = 1 := by
    rcases lt_trichotomy (valuation K (maximalIdeal R) ((C.u⁻¹ : Kˣ) : K)) 1 with h | h | h
    · exact absurd h12 (pow_lt_one₀ zero_le h (by norm_num)).ne
    · exact h
    · exact absurd h12 (one_lt_pow₀ h (by norm_num)).ne'
  simpa using h1

/-- **Silverman VII.1.3(b), scaling factor.** If `W` is elliptic and `W`, `C • W` are both
minimal Weierstrass equations over the fraction field `K` of a discrete valuation ring `R`, then
the scaling factor `C.u` of the change of variables is the image of a unit of `R`. With the
transformation law `ω' = u ω` of the invariant differential, this gives Silverman VII.1.3(c): the
invariant differential of a minimal equation is unique up to multiplication by `R*`. -/
theorem exists_unit_eq_u_of_isMinimal (W : WeierstrassCurve K) [W.IsElliptic]
    (C : VariableChange K) [IsMinimal R W] [IsMinimal R (C • W)] :
    ∃ u : Rˣ, algebraMap R K u = C.u := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_valuation_eq (A := R) (1 : K) (C.u : K)
    (by rw [map_one, valuation_u_eq_one_of_isMinimal R W C])
  exact ⟨u, by rwa [Units.smul_def, Algebra.smul_def, mul_one] at hu⟩

/-- **Uniqueness of minimal Weierstrass equations** (Silverman VII.1.3(b); Conrad, Corollary 2.9
and p. 6). If `W` is an elliptic Weierstrass curve over the fraction field `K` of a discrete
valuation ring `R`, and both `W` and `C • W` are minimal Weierstrass equations, then the change of
variables `C` is the base change of a change of variables `C'` over `R`; that is, `C.u` is the
image of a unit of `R` and `C.r`, `C.s`, `C.t` are images of elements of `R`.

The hypothesis `W.IsElliptic` (nonzero discriminant) is the setting of the source (elliptic
curves) and is necessary; see the module docstring. -/
theorem exists_baseChange_eq_of_isMinimal (W : WeierstrassCurve K) [W.IsElliptic]
    (C : VariableChange K) [IsMinimal R W] [IsMinimal R (C • W)] :
    ∃ C' : VariableChange R, C'.baseChange K = C := by
  obtain ⟨u, hu⟩ := exists_unit_eq_u_of_isMinimal R W C
  exact variableChange_integral_of_u_integral (W := W) (W' := C • W) rfl hu

variable {R}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- A change of variables over `R` takes an integral Weierstrass equation over `K` to an integral
one. -/
theorem isIntegral_baseChange_smul {W : WeierstrassCurve K} [hW : IsIntegral R W]
    (C : VariableChange R) : IsIntegral R (C.baseChange K • W) := by
  obtain ⟨W₀, rfl⟩ := hW.integral
  exact ⟨C • W₀, map_variableChange W₀ C (algebraMap R K)⟩

/-- A change of variables over `R` does not change the valuation of the discriminant. -/
theorem valuation_Δ_baseChange_smul (W : WeierstrassCurve K) (C : VariableChange R) :
    valuation K (maximalIdeal R) (C.baseChange K • W).Δ = valuation K (maximalIdeal R) W.Δ := by
  have hu : valuation K (maximalIdeal R) (algebraMap R K (C.u : R)) = 1 :=
    (valuation_eq_one_iff_notMem _).mpr
      ((IsLocalRing.mem_maximalIdeal _).not.mpr (not_not.mpr (Units.isUnit _)))
  rw [variableChange_Δ, map_mul, map_pow]
  simp [VariableChange.baseChange, hu]

/-- An integral Weierstrass equation whose discriminant has valuation one (i.e. is a unit of `R`)
is minimal. -/
theorem isMinimal_of_valuation_Δ_eq_one {W : WeierstrassCurve K} [hW : IsIntegral R W]
    (hΔ : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using hW, fun j _ _ ↦ ?_⟩⟩
  simp only [one_smul]
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R W, hΔ]
  exact (valuation_Δ_aux R (j • W)).2

/-- **Converse of Silverman VII.1.3(b).** A change of variables with coefficients in
`R` (so with scaling factor a unit of `R`) takes a minimal Weierstrass equation over `K` to a
minimal one. No ellipticity hypothesis is needed. -/
theorem isMinimal_baseChange_smul {W : WeierstrassCurve K} [hW : IsMinimal R W]
    (C : VariableChange R) : IsMinimal R (C.baseChange K • W) := by
  have hint := isIntegral_baseChange_smul (R := R) (W := W) C
  refine ⟨⟨by simpa using hint, fun j hj _ ↦ ?_⟩⟩
  have hj₁ : IsIntegral R (j • C.baseChange K • W) := hj
  have hj₂ : IsIntegral R ((j * C.baseChange K) • W) := by rwa [mul_smul]
  have h := valuation_Δ_le_of_isMinimal R (W := W) (j * C.baseChange K)
  simp only [one_smul]
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral,
    valuation_Δ_baseChange_smul, ← mul_smul]
  exact h

/-- **Uniqueness of minimal Weierstrass equations, iff form** (Silverman VII.1.3(b)). For an
elliptic minimal Weierstrass equation `W` over the fraction field `K` of a discrete valuation
ring `R`, the equation `C • W` is minimal if and only if `C` is the base change of a change of
variables over `R`. -/
theorem isMinimal_smul_iff (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K} [W.IsElliptic] [IsMinimal R W]
    (C : VariableChange K) :
    IsMinimal R (C • W) ↔ ∃ C' : VariableChange R, C'.baseChange K = C := by
  refine ⟨fun _ ↦ exists_baseChange_eq_of_isMinimal R W C, ?_⟩
  rintro ⟨C', rfl⟩
  exact isMinimal_baseChange_smul C'

end WeierstrassCurve
