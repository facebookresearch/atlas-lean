/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/LogPTildeFontaine.lean`,
`ZInQKernel/Contrib/OneProof/LogPTranscendence.lean`,
`ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean`,
`ZInQKernel/Contrib/OneProof/BergerBst.lean`, `ZInQKernel/Contrib/OneProof/PanBergerPst.lean`
and `ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.FontaineLogLemma
public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingInvariants
public import MathlibExt.RingTheory.Perfectoid.MaximalPeriodRing

/-!
# The transcendence of `log [p̃]`

Let `u = log [p̃] = log([p̃]/p) ∈ B_dR^+` (`PadicComplexInt.logPTilde`), where `p̃ = p♭` is a
chosen element of the tilt of `𝓞_ℂ_[p]` with `p̃♯ = p`. We prove:

* **Fontaine's Lemme 4.3.1**: `u` is not in the fraction field of `B_max` inside the field `B_dR`
  (`PadicComplexInt.mul_algebraMap_logPTilde_ne`): there are no `a ≠ 0` and `b` in `B_max` with
  `a u = b`. Following Fontaine's proof (§4.3.2), every element of `B_max` is a quotient of two
  elements of `A_max ⊆ S = W(𝓞_ℂ_[p]♭)⟦ξ/p⟧`, and `a u ∉ S` for every nonzero `a ∈ S`
  (`AdicCompletion.mul_evalPowerSeries_logOneSubSeries_not_mem`).
* **The transcendence of `log [p̃]`**: `u` is transcendental over `B_max`
  (`PadicComplexInt.transcendental_logPTilde`), equivalently the evaluation
  `B_max[X] → B_dR`, `X ↦ log [p̃]`, is injective (`PadicComplexInt.aeval_logPTilde_injective`).
  This is the argument of Fontaine's §4.3.3 (`PadicComplexInt.transcendental_of_forall_mul_ne`):
  `σ(u) = u + log [u_σ]` with `log [u_σ] ∈ B_max`, so if `P` is the minimal polynomial of `u` over
  `B_max`, of degree `d ≥ 1` with coefficients `c_i`, then `c_{d-1}/c_d + d u` is fixed by
  `Gal(ℚ̄_p/ℚ_p)`, hence lies in `(B_dR)^{Gal(ℚ̄_p/ℚ_p)} = ℚ_p`
  (`PadicComplexInt.exists_eq_algebraMap_of_forall_galoisBDeRham_eq_self`); then `u` would lie in
  the fraction field of `B_max`.

Fontaine states Lemme 4.3.1 for `B_cris`. Since `Σ aₙ ξⁿ/n! = Σ (pⁿ/n!) aₙ βⁿ` with
`pⁿ/n! ∈ ℤ_p`, `A_cris ⊆ A_max` and `B_cris ⊆ B_max` (as Fontaine shows `A_cris ⊆ S` in §4.3.2
p. 88), so the statements for `B_max` proved here imply those for `B_cris`. Fontaine uses them
to prove that `K ⊗_{K₀} B_st → B_dR` is injective (Théorème 4.2.4 p. 86).

## References

* J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II,
  §4.3: Lemme 4.3.1 p. 87, §4.3.2 pp. 87–88 and §4.3.3 pp. 88–89.
-/

@[expose] public noncomputable section

open Ideal WittVector PowerSeries Polynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-! ### The Galois reduction -/

/-- The coefficient of `X ^ (d - 1)` in `f (X + r)`, for `f` of degree `d ≥ 1`, is
`f_{d-1} + d r f_d`. -/
private theorem coeff_taylor_natDegree_sub_one {R : Type*} [CommRing R] (f : R[X]) (r : R)
    {d : ℕ} (hd : f.natDegree = d) (hd0 : d ≠ 0) :
    (taylor r f).coeff (d - 1) = f.coeff (d - 1) + d * r * f.coeff d := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
  rw [taylor_coeff]
  have hdeg : (hasseDeriv (n + 1 - 1) f).natDegree < 2 := by
    have := natDegree_hasseDeriv_le f (n + 1 - 1)
    omega
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_one, hasseDeriv_coeff,
    hasseDeriv_coeff]
  simp only [Nat.succ_sub_one, zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one,
    pow_one]
  rw [show 1 + n = n + 1 by omega, Nat.choose_succ_self_right]
  push_cast
  ring

/-- The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on a subalgebra `B` of `B_dR` stable under it. -/
private def galoisRestrict (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : B →+* B :=
  RingHom.codRestrict ((galoisBDeRham p σ : 𝔹 →+* 𝔹).comp (algebraMap B 𝔹)) B
    fun x => hB σ x x.2

/-- `galoisRestrict p B hB σ` is the restriction of `σ` to `B`. -/
private theorem coe_galoisRestrict (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : B) :
    (galoisRestrict p B hB σ x : 𝔹) = galoisBDeRham p σ x :=
  rfl

/-- The action of `σ` on a stable subalgebra `B` is injective. -/
private theorem galoisRestrict_injective (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Function.Injective (galoisRestrict p B hB σ) :=
  fun _ _ hxy => Subtype.ext (galoisBDeRham_injective p σ (congrArg Subtype.val hxy))

/-- `P^σ(σ x) = σ(P(x))` for `P ∈ B[X]`, where `P^σ` is `P` with `σ` applied to its
coefficients. -/
private theorem aeval_map_galoisRestrict (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (P : B[X]) (x : 𝔹) :
    aeval (galoisBDeRham p σ x) (P.map (galoisRestrict p B hB σ)) =
      galoisBDeRham p σ (aeval x P) := by
  rw [aeval_def, aeval_def, eval₂_map]
  exact (hom_eval₂ P (algebraMap B 𝔹) (galoisBDeRham p σ : 𝔹 →+* 𝔹) x).symm

/-- The two top coefficients of a minimal relation: let `P ∈ B[X]` be a nonzero polynomial of
least degree `d ≥ 1` with `P(u) = 0`, and let `σ(u) = u + δ` with `δ ∈ B`. Then
`P_σ(X) = P^σ(X + δ)` also vanishes at `u` and has degree `d`, so `σ(c_d) P = c_d P_σ` by
minimality, and the coefficients of `X ^ (d - 1)` give
`σ(c_d) c_{d-1} = c_d (σ(c_{d-1}) + d δ σ(c_d))`. -/
private theorem galoisRestrict_coeff_relation (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    {u : 𝔹} (P : B[X]) {d : ℕ} (hPd : P.natDegree = d) (hd0 : d ≠ 0) (hPu : aeval u P = 0)
    (hmin : ∀ Q : B[X], Q ≠ 0 → aeval u Q = 0 → d ≤ Q.natDegree)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (δ : B) (hδ : galoisBDeRham p σ u = u + δ) :
    galoisRestrict p B hB σ (P.coeff d) * P.coeff (d - 1) =
      P.coeff d * (galoisRestrict p B hB σ (P.coeff (d - 1)) +
        d * δ * galoisRestrict p B hB σ (P.coeff d)) := by
  set s := galoisRestrict p B hB σ
  set Pσ := taylor δ (P.map s) with hPσ
  have hPσu : aeval u Pσ = 0 := by
    rw [hPσ, taylor_apply, aeval_comp]
    simp only [map_add, aeval_X, aeval_C]
    rw [show u + algebraMap B 𝔹 δ = galoisBDeRham p σ u from hδ.symm,
      aeval_map_galoisRestrict, hPu, map_zero]
  have hmapd : (P.map s).natDegree = d := by
    rw [natDegree_map_eq_of_injective (galoisRestrict_injective p B hB σ)]
    exact hPd
  set Q := Polynomial.C (s (P.coeff d)) * P + Polynomial.C (-P.coeff d) * Pσ with hQ
  have hQu : aeval u Q = 0 := by
    rw [hQ, map_add, map_mul, map_mul, hPu, hPσu, mul_zero, mul_zero, add_zero]
  have hQd : ∀ N, d - 1 < N → Q.coeff N = 0 := by
    intro N hN
    rw [hQ, coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    rcases (show N = d ∨ d < N by omega) with rfl | hN'
    · have h1 := coeff_taylor_natDegree (r := δ) (f := P.map s)
      rw [hmapd] at h1
      rw [hPσ, h1, Polynomial.leadingCoeff, hmapd, Polynomial.coeff_map]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < N),
        coeff_eq_zero_of_natDegree_lt (by rw [hPσ, natDegree_taylor, hmapd]; omega :
          Pσ.natDegree < N)]
      ring
  have hQ0 : Q = 0 := by
    by_contra hQne
    have h1 := hmin Q hQne hQu
    have h2 : Q.natDegree ≤ d - 1 := natDegree_le_iff_coeff_eq_zero.mpr hQd
    omega
  have hc := congrArg (fun R => R.coeff (d - 1)) hQ0
  simp only [hQ, coeff_add, Polynomial.coeff_C_mul, coeff_zero] at hc
  rw [hPσ, coeff_taylor_natDegree_sub_one (P.map s) δ hmapd hd0, Polynomial.coeff_map,
    Polynomial.coeff_map] at hc
  linear_combination hc

/-- **Fontaine's Galois argument** (Exposé II, §4.3.3): let `B` be a `ℚ_[p]`-subalgebra of `B_dR`
stable under `Gal(ℚ̄_p/ℚ_p)`, and let `u ∈ B_dR` satisfy `σ(u) - u ∈ B` for every `σ`. If `u` is
not in the fraction field of `B` (there are no `a ≠ 0` and `b` in `B` with `a u = b`), then `u` is
transcendental over `B`. -/
theorem transcendental_of_forall_mul_ne (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    {u : 𝔹} (hu : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∃ δ ∈ B, galoisBDeRham p σ u = u + δ)
    (h : ∀ a ∈ B, ∀ b ∈ B, a ≠ 0 → a * u ≠ b) : Transcendental B u := by
  classical
  rintro ⟨P0, hP00, hP0u⟩
  have hex : ∃ d : ℕ, ∃ P : B[X], P ≠ 0 ∧ P.natDegree = d ∧ aeval u P = 0 :=
    ⟨_, P0, hP00, rfl, hP0u⟩
  obtain ⟨P, hP0, hPd, hPu⟩ := Nat.find_spec hex
  have hmin : ∀ Q : B[X], Q ≠ 0 → aeval u Q = 0 → Nat.find hex ≤ Q.natDegree :=
    fun Q hQ hQu => Nat.find_min' hex ⟨Q, hQ, rfl, hQu⟩
  set d := Nat.find hex
  have ha0 : P.coeff d ≠ 0 := by
    rw [← hPd]
    exact leadingCoeff_ne_zero.mpr hP0
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hPd
    rw [eq_C_of_natDegree_eq_zero hPd, aeval_C] at hPu
    apply ha0
    rw [h0]
    exact Subtype.ext hPu
  have haB : (P.coeff d : 𝔹) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hdB : (d : 𝔹) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[p] 𝔹)]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd0)
  -- With `a = c_d`, `b = c_{d-1}` and `e = 1/(d a)`, the element `u + b e` is invariant.
  set a : 𝔹 := (P.coeff d : 𝔹) with ha_def
  set b : 𝔹 := (P.coeff (d - 1) : 𝔹) with hb_def
  set e : 𝔹 := ((d : 𝔹) * a)⁻¹
  have he : (d : 𝔹) * a * e = 1 := mul_inv_cancel₀ (mul_ne_zero hdB haB)
  have hy : ∀ σ, galoisBDeRham p σ (u + b * e) = u + b * e := by
    intro σ
    obtain ⟨δ, hδB, hδ⟩ := hu σ
    have hr := congrArg (fun z : B => (z : 𝔹))
      (galoisRestrict_coeff_relation p B hB P hPd hd0 hPu hmin σ ⟨δ, hδB⟩ hδ)
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_galoisRestrict,
      SubringClass.coe_natCast] at hr
    rw [← ha_def, ← hb_def] at hr
    have hX := congrArg (galoisBDeRham p σ) he
    rw [map_mul, map_mul, map_natCast, map_one] at hX
    rw [map_add, map_mul, hδ]
    linear_combination (b * e - δ * (d * a) * e) * hX +
      (-δ - galoisBDeRham p σ b * galoisBDeRham p σ e) * he +
      (-(d : 𝔹) * galoisBDeRham p σ e * e) * hr
  -- Hence `u + b e = c ∈ ℚ_[p]`, and `a u = c a - b/d ∈ B`.
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_galoisBDeRham_eq_self p hy
  have hq : algebraMap ℚ_[p] 𝔹 (d : ℚ_[p])⁻¹ * (d : 𝔹) = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] 𝔹), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd0), map_one]
  refine h a (P.coeff d).2 (algebraMap ℚ_[p] 𝔹 c * a - algebraMap ℚ_[p] 𝔹 (d : ℚ_[p])⁻¹ * b)
    (B.sub_mem (B.mul_mem (B.algebraMap_mem c) (P.coeff d).2)
      (B.mul_mem (B.algebraMap_mem _) (P.coeff (d - 1)).2)) haB ?_
  rw [← hc]
  linear_combination (-algebraMap ℚ_[p] 𝔹 (d : ℚ_[p])⁻¹ * b) * he + (a * b * e) * hq

/-! ### `log [p̃]` is not in the fraction field of `B_max` -/

/-- The image in `B_dR` of `z ∈ ℤ_[p]` under `ℤ_[p] → W(𝓞_ℂ_[p]♭) → B_dR^+ → B_dR` is the image
of `z ∈ ℚ_[p]`. -/
private theorem algebraMap_algebraMap_padicIntToAinf (z : ℤ_[p]) :
    algebraMap 𝔹⁺ 𝔹 (algebraMap 𝔸 𝔹⁺ (padicIntToAinf p z)) = algebraMap ℚ_[p] 𝔹 (z : ℚ_[p]) := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] 𝔹⁺ 𝔹, IsScalarTower.algebraMap_apply ℚ_[p] 𝔸ₚ 𝔹⁺,
    IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺]
  congr 2
  exact (padicToLocalizationAway_coe p z).symm

/-- Every element of `B_max` is a quotient `y / z` of two elements `y` and `z ≠ 0` of `A_max`. -/
private theorem exists_mul_eq_of_mem_bMax {x : 𝔹} (hx : x ∈ bMax p) :
    ∃ y ∈ aMax p, ∃ z ∈ aMax p,
      algebraMap 𝔹⁺ 𝔹 z ≠ 0 ∧ x * algebraMap 𝔹⁺ 𝔹 z = algebraMap 𝔹⁺ 𝔹 y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨y, hy, rfl⟩ | ⟨ε, h, hne, rfl⟩
    · exact ⟨y, hy, 1, (aMax p).one_mem, by rw [map_one]; exact one_ne_zero,
        by rw [map_one, mul_one]⟩
    · have hz : algebraMap 𝔹⁺ 𝔹 (logTeichmuller p h) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).mpr (logTeichmuller_ne_zero p h hne)
      exact ⟨1, (aMax p).one_mem, logTeichmuller p h, logTeichmuller_mem_aMax p h, hz,
        by rw [inv_mul_cancel₀ hz, map_one]⟩
  | algebraMap c =>
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) c
    have hy0 : (y : ℚ_[p]) ≠ 0 := fun h0 =>
      nonZeroDivisors.ne_zero hy (PadicInt.coe_eq_zero.mp h0)
    refine ⟨algebraMap 𝔸 𝔹⁺ (padicIntToAinf p x), algebraMap_mem_aMax p _,
      algebraMap 𝔸 𝔹⁺ (padicIntToAinf p y), algebraMap_mem_aMax p _, ?_, ?_⟩
    · rw [algebraMap_algebraMap_padicIntToAinf]
      exact (_root_.map_ne_zero _).mpr hy0
    · rw [algebraMap_algebraMap_padicIntToAinf, algebraMap_algebraMap_padicIntToAinf, ← map_mul]
      congr 1
      exact div_mul_cancel₀ _ hy0
  | add x y _ _ hx hy =>
    obtain ⟨y1, hy1, z1, hz1, hz10, e1⟩ := hx
    obtain ⟨y2, hy2, z2, hz2, hz20, e2⟩ := hy
    refine ⟨y1 * z2 + y2 * z1, add_mem (mul_mem hy1 hz2) (mul_mem hy2 hz1), z1 * z2,
      mul_mem hz1 hz2, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hz10 hz20
    · rw [map_mul, map_add, map_mul, map_mul, ← e1, ← e2]
      ring
  | mul x y _ _ hx hy =>
    obtain ⟨y1, hy1, z1, hz1, hz10, e1⟩ := hx
    obtain ⟨y2, hy2, z2, hz2, hz20, e2⟩ := hy
    refine ⟨y1 * y2, mul_mem hy1 hy2, z1 * z2, mul_mem hz1 hz2, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hz10 hz20
    · rw [map_mul, map_mul, ← e1, ← e2]
      ring

/-- `A_max` lies in the ring `W(𝓞_ℂ_[p]♭)⟦ξ/p⟧` of the values at `ξ/p` of the power series over
`W(𝓞_ℂ_[p]♭)`. -/
private theorem mem_evalPowerSeriesRange_of_mem_aMax {y : 𝔹⁺} (hy : y ∈ aMax p) :
    y ∈ AdicCompletion.evalPowerSeriesRange 𝔸 𝕀 (xiDivP_mem_ker p) := by
  obtain ⟨f, -, rfl⟩ := Subring.mem_map.mp hy
  exact RingHom.mem_range.mpr ⟨f, rfl⟩

/-- For `n ≠ 0`, `p ^ v_p(n) / n` is the image of an element of `W(𝓞_ℂ_[p]♭)`. -/
private theorem exists_algebraMap_mul_natCast_eq (n : ℕ) (hn : n ≠ 0) :
    ∃ w : 𝔸, algebraMap 𝔸 𝔸ₚ w * (n : 𝔸ₚ) = (p : 𝔸ₚ) ^ padicValNat p n := by
  obtain ⟨v, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hval : padicValNat p (p ^ v * m) = v := by
    rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hp.out.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hpm, add_zero]
  have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
  refine ⟨padicIntToAinf p ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  have key : ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((p ^ v * m : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ v := by
    rw [Nat.cast_mul, Nat.cast_pow, mul_left_comm, hu.val_inv_mul, mul_one]
  have key' : padicIntToAinf p ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((p ^ v * m : ℕ) : 𝔸) =
      (p : 𝔸) ^ v := by
    simpa only [map_mul, map_pow, map_natCast] using congrArg (padicIntToAinf p) key
  rw [hval, ← map_natCast (algebraMap 𝔸 𝔸ₚ) (p ^ v * m), ← map_mul, key', map_pow, map_natCast]

/-- `ξ` is a non-zero-divisor of `B_dR^+`. -/
private theorem eq_zero_of_algebraMap_xi_mul_eq_zero (x : AdicCompletion 𝕀 𝔸ₚ)
    (hx : algebraMap 𝔸ₚ (AdicCompletion 𝕀 𝔸ₚ) (algebraMap 𝔸 𝔸ₚ (xi p)) * x = 0) : x = 0 := by
  have h : algebraMap 𝔸 𝔹⁺ (xi p) * (show 𝔹⁺ from x) = 0 := hx
  exact (mul_eq_zero.mp h).resolve_left (algebraMap_xi_ne_zero p)

/-- `log [p̃] = log(1 - ξ/p) = -Σ_{n ≥ 1} (ξ/p)ⁿ/n`: the value of `log(1 + X)` at `-ξ/p` is that of
`log(1 - X)` at `ξ/p`. -/
private theorem logPTilde_eq_evalPowerSeries :
    logPTilde p = AdicCompletion.evalPowerSeries 𝕀 (xiDivP_mem_ker p)
      (AdicCompletion.logOneSubSeries fun n => algebraMap ℚ_[p] 𝔸ₚ (n : ℚ_[p])⁻¹) := by
  rw [AdicCompletion.logOneSubSeries_eq_map_rescale_log]
  refine AdicCompletion.evalPowerSeries_eq_of_coeff_mul_pow_eq _ _ _ _ _ fun k => ?_
  rw [logSeries, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_rescale, map_mul,
    map_pow, map_neg, map_one, neg_pow (xiDivP p)]
  ring

/-- **Fontaine's Lemme 4.3.1, for `B_max`**: `log [p̃]` is not in the fraction field of `B_max`
inside `B_dR`: if `a, b ∈ B_max` and `a ≠ 0`, then `a · log [p̃] ≠ b`. -/
theorem mul_algebraMap_logPTilde_ne {a b : 𝔹} (ha : a ∈ bMax p) (hb : b ∈ bMax p)
    (ha0 : a ≠ 0) : a * algebraMap 𝔹⁺ 𝔹 (logPTilde p) ≠ b := by
  intro he
  obtain ⟨y1, hy1, z1, hz1, hz10, e1⟩ := exists_mul_eq_of_mem_bMax p ha
  obtain ⟨y2, hy2, z2, hz2, hz20, e2⟩ := exists_mul_eq_of_mem_bMax p hb
  have hy10 : y1 * z2 ≠ 0 := by
    intro h0
    have h1 : algebraMap 𝔹⁺ 𝔹 y1 * algebraMap 𝔹⁺ 𝔹 z2 = 0 := by rw [← map_mul, h0, map_zero]
    rw [← e1] at h1
    exact ha0 ((mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hz20)).resolve_right hz10)
  -- `y1 z2 log [p̃] = y2 z1` with `y1 z2 ≠ 0`, both sides in `W(𝓞_ℂ_[p]♭)⟦ξ/p⟧`.
  have hrel : y1 * z2 * logPTilde p = y2 * z1 := by
    apply algebraMap_bDeRham_injective p
    rw [map_mul, map_mul, map_mul, ← e1, ← e2, ← he]
    ring
  have hmem : y1 * z2 * logPTilde p ∈
      AdicCompletion.evalPowerSeriesRange 𝔸 𝕀 (xiDivP_mem_ker p) := by
    rw [hrel]
    exact mem_evalPowerSeriesRange_of_mem_aMax p (mul_mem hy2 hz1)
  rw [logPTilde_eq_evalPowerSeries] at hmem
  exact AdicCompletion.mul_evalPowerSeries_logOneSubSeries_not_mem 𝔸 𝕀 p (xiDivP_mem_ker p)
    (xi p) (natCast_mul_xiDivP p) (natCast_mul_algebraMap_inv p hp.out.ne_zero)
    (algebraMap_mem_ker_fontaineThetaInvertP p (fontaineTheta_xi p))
    (fun n => algebraMap ℚ_[p] 𝔸ₚ (n : ℚ_[p])⁻¹) (fun _ hn => natCast_mul_algebraMap_inv p hn)
    (exists_algebraMap_mul_natCast_eq p)
    (fun k a h => mem_span_xi_pow_of_algebraMap_mem p k a
      (by rwa [ker_fontaineThetaInvertP_pow_eq_span_xi_pow] at h))
    (mem_span_xi_pow_of_forall p) (eq_zero_of_algebraMap_xi_mul_eq_zero p)
    (mem_evalPowerSeriesRange_of_mem_aMax p (mul_mem hy1 hz2)) hy10 hmem

/-! ### The transcendence of `log [p̃]` -/

/-- **The transcendence of `log [p̃]`** (Fontaine, *Le corps des périodes p-adiques*, Exposé II,
§4.3.3, there over `B_cris`): `log [p̃] = log([p̃]/p)` is transcendental over `B_max`, inside the
field `B_dR`. -/
theorem transcendental_logPTilde : Transcendental (bMax p) (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) :=
  transcendental_of_forall_mul_ne p (bMax p)
    (fun σ x hx => bMax_le_comap p σ hx)
    (fun σ => by
      obtain ⟨u, hu, hu1⟩ := exists_preTiltMap_pFlat_eq_mul p σ
      refine ⟨algebraMap 𝔹⁺ 𝔹 (logTeichmuller p hu1),
        algebraMap_mem_bMax p (logTeichmuller_mem_aMax p hu1), ?_⟩
      rw [galoisBDeRham_algebraMap, galoisBDeRhamPlus_logPTilde p σ hu hu1, map_add, add_comm])
    fun a ha b hb ha0 => mul_algebraMap_logPTilde_ne p ha hb ha0

/-- **The evaluation `B_max[X] → B_dR` at `log [p̃]` is injective.** -/
theorem aeval_logPTilde_injective :
    Function.Injective (aeval (R := bMax p) (algebraMap 𝔹⁺ 𝔹 (logPTilde p))) :=
  transcendental_iff_injective.mp (transcendental_logPTilde p)

end PadicComplexInt
