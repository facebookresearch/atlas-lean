/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/AcrisImage.lean`,
`ZInQKernel/Contrib/OneProof/AbstractAcris.lean`, `ZInQKernel/Contrib/OneProof/PanBerger.lean`
and `ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRing
public import MathlibExt.RingTheory.Perfectoid.MaximalPeriodRing

/-!
# The Galois action on Fontaine's ring `A_cris`

Let `w` be a generator of the kernel of Fontaine's map `θ : W(𝓞_ℂ_[p]♭) → 𝓞_ℂ_[p]` and let
`A_cris = PadicComplexInt.CrystallineCompletion p w` be the `p`-adic completion of
`D = W(𝓞_ℂ_[p]♭)[w^n/n! : n ≥ 1] ⊆ W(𝓞_ℂ_[p]♭)[1/p]` (J.-M. Fontaine, *Le corps des périodes
p-adiques*, Astérisque 223 (1994), Exposé II, §2.3.3 p. 78). An element `σ` of
`Gal(ℚ̄_p/ℚ_p)` acts on `W(𝓞_ℂ_[p]♭)[1/p]` by functoriality; since `σ(w)` is again in
`ker θ = (w)`, it preserves `D` (`PadicComplexInt.galoisFiniteDividedPowers`) and hence acts on
its `p`-adic completion (`PadicComplexInt.galoisCrystallineCompletion`). We show:

* the injective map `A_cris → B_dR^+` of Fontaine, *op. cit.*, §4.1.2 p. 83
  (`PadicComplexInt.toBDeRhamPlus`) is Galois equivariant
  (`PadicComplexInt.toBDeRhamPlus_galoisCrystallineCompletion`), and the action is a group
  action (`PadicComplexInt.galoisCrystallineCompletion_mul`,
  `PadicComplexInt.galoisCrystallineCompletion_one`);
* its image `PadicComplexInt.aCris` does not depend on the generator `w`
  (`PadicComplexInt.range_toBDeRhamPlus_eq_aCris`), is stable under `Gal(ℚ̄_p/ℚ_p)`
  (`PadicComplexInt.galoisBDeRhamPlus_mem_aCris`), contains the periods `log [ε]` for `ε♯ = 1`
  (`PadicComplexInt.logTeichmuller_mem_aCris`) and lies in `A_max`
  (`PadicComplexInt.aCris_le_aMax`, as Fontaine shows `A_cris ⊆ W(𝓞_ℂ_[p]♭)⟦ξ/p⟧` in §4.3.2
  p. 88);
* the period `log [ε] ∈ A_cris` (`PadicComplexInt.logTeichmullerCrystalline`), the element whose
  image in `B_dR^+` is `log [ε]`, is permuted by the Galois action
  (`PadicComplexInt.galoisCrystallineCompletion_logTeichmullerCrystalline`).

The equivariance is proved on representatives: every element of `A_cris` is the limit of a
restricted series `Σ aₙ w^n/n!` (`PadicComplexInt.exists_ofRestricted_eq`), `σ` sends it to the
limit of `Σ σ(aₙ) cⁿ w^n/n!` where `σ(w) = w c`, and the map to `B_dR^+` sends both series to
their values.

`MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings` constructs `A_cris` and
`B_cris^+ = A_cris[1/p]` of a semiperfect ring of characteristic `p` from its universal divided
power hull; here `A_cris` is Fontaine's ring of `𝓞_ℂ_[p]`, presented through a generator of
`ker θ`, with its Galois action.
-/

@[expose] public noncomputable section

open Ideal WittVector PowerSeries

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p

/-! ### The action on `W(𝓞_ℂ_[p]♭)[w^n/n!]` -/

section FiniteDividedPowers

variable {p} {w : WittVector p (PreTilt 𝓞_ℂ_[p] p)}

/-- For a generator `w` of the kernel of `θ`, `σ(w) = w c` for some `c ∈ W(𝓞_ℂ_[p]♭)`, since
`σ(w) ∈ ker θ = (w)`. -/
private theorem exists_map_eq_mul (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    ∃ c : 𝔸, WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) w = w * c :=
  dvd_of_fontaineTheta_eq_zero hgen (by
    rw [WittVector.fontaineTheta_map, fontaineTheta_eq_zero_of_ker_eq_span hgen, map_zero])

/-- `(w c)^n/n! = cⁿ · (w^n/n!)`. -/
private theorem dividedPower_mul_right (w c : 𝔸) (n : ℕ) :
    dividedPower (w * c) n = algebraMap 𝔸 𝔸ₚ (c ^ n) * dividedPower w n := by
  rw [dividedPower, dividedPower, map_mul, mul_pow, map_pow]
  ring

/-- `σ(w^n/n!) = σ(w)^n/n!`. -/
private theorem galoisLocalization_dividedPower (σ : Gal(PadicAlgCl p/ℚ_[p])) (w : 𝔸) (n : ℕ) :
    galoisLocalization p σ (dividedPower w n) =
      dividedPower (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) w) n := by
  rw [dividedPower, dividedPower, map_mul, map_pow, Localization.awayMapNatCast_algebraMap,
    IsUnit.map_ringInverse _ (isUnit_natCast_factorial n), map_natCast]

/-- For a generator `w` of the kernel of `θ`, the action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on
`W(𝓞_ℂ_[p]♭)[1/p]` preserves `W(𝓞_ℂ_[p]♭)[w^n/n!]`. -/
theorem awayMapNatCast_mem_finiteDividedPowers
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ : Gal(PadicAlgCl p/ℚ_[p]))
    {x : 𝔸ₚ} (hx : x ∈ finiteDividedPowers p w) :
    Localization.awayMapNatCast (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom)) p
      x ∈ finiteDividedPowers p w := by
  obtain ⟨c, hc⟩ := exists_map_eq_mul hgen σ
  have h : finiteDividedPowers p w ≤ (finiteDividedPowers p w).comap (galoisLocalization p σ) := by
    rw [finiteDividedPowers, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | ⟨n, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, Localization.awayMapNatCast_algebraMap]
      exact algebraMap_mem_finiteDividedPowers w _
    · rw [SetLike.mem_coe, Subring.mem_comap, galoisLocalization_dividedPower, hc,
        dividedPower_mul_right]
      exact Subring.mul_mem _ (algebraMap_mem_finiteDividedPowers w _) (dividedPower_mem w _)
  exact h hx

variable (p) in
/-- For a generator `w` of the kernel of `θ`, the action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on
`W(𝓞_ℂ_[p]♭)[w^n/n!]`: the restriction of the action on `W(𝓞_ℂ_[p]♭)[1/p]` induced by
`integralGalois p σ`. -/
def galoisFiniteDividedPowers (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (σ : Gal(PadicAlgCl p/ℚ_[p])) : finiteDividedPowers p w →+* finiteDividedPowers p w :=
  (Localization.awayMapNatCast (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom))
    p).restrict _ _ fun _ hx => awayMapNatCast_mem_finiteDividedPowers hgen σ hx

/-- `galoisFiniteDividedPowers p hgen σ` is the restriction of the action on
`W(𝓞_ℂ_[p]♭)[1/p]`. -/
@[simp]
theorem coe_galoisFiniteDividedPowers
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ : Gal(PadicAlgCl p/ℚ_[p]))
    (x : finiteDividedPowers p w) :
    (galoisFiniteDividedPowers p hgen σ x : 𝔸ₚ) =
      Localization.awayMapNatCast (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom))
        p x :=
  rfl

end FiniteDividedPowers

/-! ### The action on `A_cris` -/

section Completion

variable {p} {w : WittVector p (PreTilt 𝓞_ℂ_[p] p)}

/-- The action of `σ` on `W(𝓞_ℂ_[p]♭)[w^n/n!]` maps the ideal `(p)` into itself. -/
theorem map_pIdeal_galoisFiniteDividedPowers_le
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    (pIdeal w).map (galoisFiniteDividedPowers p hgen σ) ≤ pIdeal w := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

variable (p) in
/-- **The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `A_cris`**: for a generator `w` of the kernel of `θ`,
the map of `p`-adic completions induced by the action `galoisFiniteDividedPowers p hgen σ` on
`W(𝓞_ℂ_[p]♭)[w^n/n!]`. -/
def galoisCrystallineCompletion (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (σ : Gal(PadicAlgCl p/ℚ_[p])) : CrystallineCompletion p w →+* CrystallineCompletion p w :=
  AdicCompletion.mapRingHom (pIdeal w) (pIdeal w) (galoisFiniteDividedPowers p hgen σ)
    (map_pIdeal_galoisFiniteDividedPowers_le hgen σ)

/-- On `W(𝓞_ℂ_[p]♭)[w^n/n!]`, the action on `A_cris` is the action on
`W(𝓞_ℂ_[p]♭)[w^n/n!]`. -/
theorem galoisCrystallineCompletion_algebraMap
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ : Gal(PadicAlgCl p/ℚ_[p]))
    (x : finiteDividedPowers p w) :
    galoisCrystallineCompletion p hgen σ
        (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x) =
      algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w)
        (galoisFiniteDividedPowers p hgen σ x) :=
  AdicCompletion.mapRingHom_of _ _ _ _ x

/-- If `σ(w) = w c`, then `σ(Σ_{n<N} aₙ w^n/n!) = Σ_{n<N} σ(aₙ) cⁿ w^n/n!`. -/
private theorem galoisLocalization_dividedPowerSum (σ : Gal(PadicAlgCl p/ℚ_[p])) {c : 𝔸}
    (hc : WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) w = w * c) (f : 𝔸⟦X⟧)
    (N : ℕ) :
    galoisLocalization p σ (dividedPowerSum w f N) =
      dividedPowerSum w (rescale c
        (PowerSeries.map (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom)) f)) N := by
  rw [dividedPowerSum, dividedPowerSum, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, Localization.awayMapNatCast_algebraMap, galoisLocalization_dividedPower, hc,
    dividedPower_mul_right, PowerSeries.coeff_rescale, PowerSeries.coeff_map, map_mul]
  ring

/-- If `σ(w) = w c`, then `σ` maps the element of `A_cris` defined by a restricted series
`Σ aₙ Xⁿ` to the element defined by `Σ σ(aₙ) cⁿ Xⁿ`. -/
private theorem galoisCrystallineCompletion_ofRestricted
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ : Gal(PadicAlgCl p/ℚ_[p]))
    {c : 𝔸} (hc : WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) w = w * c)
    {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p)
    (hf' : rescale c (PowerSeries.map (WittVector.map
      (PreTilt.map p (integralGalois p σ).toRingHom)) f) ∈ restrictedPowerSeries p) :
    galoisCrystallineCompletion p hgen σ (ofRestricted w hf) = ofRestricted w hf' := by
  refine AdicCompletion.ext_evalₐ fun k => ?_
  -- Rewriting with these equations is very slow at this ring, so they are chained by
  -- transitivity.
  have h₁ := AdicCompletion.evalₐ_mapRingHom (pIdeal w) (pIdeal w)
    (galoisFiniteDividedPowers p hgen σ) (map_pIdeal_galoisFiniteDividedPowers_le hgen σ) k
    (ofRestricted w hf)
  have h₂ := congrArg (MathlibExt.RingTheory.AdicCompletionMaps.quotientMap (pIdeal w) (pIdeal w)
    (galoisFiniteDividedPowers p hgen σ) (map_pIdeal_galoisFiniteDividedPowers_le hgen σ) k)
    (evalₐ_ofRestricted w hf k _ (le_max_left (decayBound hf k) (decayBound hf' k)))
  have h₃ := evalₐ_ofRestricted w hf' k _ (le_max_right (decayBound hf k) (decayBound hf' k))
  refine h₁.trans (h₂.trans (Eq.trans ?_ h₃.symm))
  exact congrArg _ (Subtype.ext (galoisLocalization_dividedPowerSum σ hc f _))

/-- The `n`-th term of the divided-power series of `f = Σ aₖ Xᵏ` at `w` is `aₙ w^n/n!`. -/
private theorem coeff_dividedPowerSeries_mul_pow (f : 𝔸⟦X⟧) (w : 𝔸) (n : ℕ) :
    PowerSeries.coeff n (dividedPowerSeries p f) * algebraMap 𝔸 𝔸ₚ w ^ n =
      algebraMap 𝔸 𝔸ₚ (PowerSeries.coeff n f) * dividedPower w n := by
  rw [dividedPowerSeries, PowerSeries.coeff_mk, dividedPower]
  ring

/-- `σ(aₙ/n!) σ(w)ⁿ = σ(aₙ) σ(w)^n/n!`. -/
private theorem galoisLocalization_coeff_mul_pow (σ : Gal(PadicAlgCl p/ℚ_[p])) (f : 𝔸⟦X⟧) (w : 𝔸)
    (n : ℕ) :
    galoisLocalization p σ (PowerSeries.coeff n (dividedPowerSeries p f)) *
        galoisLocalization p σ (algebraMap 𝔸 𝔸ₚ w) ^ n =
      algebraMap 𝔸 𝔸ₚ
          (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) (PowerSeries.coeff n f)) *
        dividedPower (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) w) n := by
  rw [← map_pow, ← map_mul, coeff_dividedPowerSeries_mul_pow, map_mul,
    Localization.awayMapNatCast_algebraMap, galoisLocalization_dividedPower]

/-- **The map `A_cris → B_dR^+` is Galois equivariant**: `j(σ x) = σ(j x)`. -/
theorem toBDeRhamPlus_galoisCrystallineCompletion
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ : Gal(PadicAlgCl p/ℚ_[p]))
    (x : CrystallineCompletion p w) :
    toBDeRhamPlus hgen (galoisCrystallineCompletion p hgen σ x) =
      galoisBDeRhamPlus p σ (toBDeRhamPlus hgen x) := by
  -- `obtain` on a term generalizes it in the goal, which is slow for this large goal, so the
  -- terms are named first.
  have hx := exists_ofRestricted_eq w x
  have hσ := exists_map_eq_mul hgen σ
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨c, hc⟩ := hσ
  have hw := algebraMap_mem_ker_of_ker_eq_span hgen
  have hf' := rescale_mem_restrictedPowerSeries p c (map_mem_restrictedPowerSeries p
    (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom)) hf)
  refine (congrArg (toBDeRhamPlus hgen)
    (galoisCrystallineCompletion_ofRestricted hgen σ hc hf hf')).trans <|
    (toBDeRhamPlus_ofRestricted hgen hf').trans <|
    Eq.trans ?_ ((congrArg (galoisBDeRhamPlus p σ) (toBDeRhamPlus_ofRestricted hgen hf)).trans
      (galoisBDeRhamPlus_evalBDeRhamPlus p σ hw _)).symm
  refine AdicCompletion.evalPowerSeries_eq_of_coeff_mul_pow_eq _ _ _ _ _ fun k => ?_
  rw [coeff_dividedPowerSeries_mul_pow, PowerSeries.coeff_map, galoisLocalization_coeff_mul_pow, hc,
    dividedPower_mul_right, PowerSeries.coeff_rescale, PowerSeries.coeff_map, map_mul]
  ring

/-- The action on `A_cris` is multiplicative: `σ τ` acts as `τ` followed by `σ`. -/
theorem galoisCrystallineCompletion_mul
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ τ : Gal(PadicAlgCl p/ℚ_[p])) :
    galoisCrystallineCompletion p hgen (σ * τ) =
      (galoisCrystallineCompletion p hgen σ).comp (galoisCrystallineCompletion p hgen τ) :=
  RingHom.ext fun x => toBDeRhamPlus_injective hgen <|
    (toBDeRhamPlus_galoisCrystallineCompletion hgen (σ * τ) x).trans <|
      (AlgHom.congr_fun (galoisBDeRhamPlus_mul p σ τ) _).trans <|
        (congrArg (galoisBDeRhamPlus p σ)
          (toBDeRhamPlus_galoisCrystallineCompletion hgen τ x).symm).trans
          (toBDeRhamPlus_galoisCrystallineCompletion hgen σ _).symm

/-- The identity acts trivially on `A_cris`. -/
theorem galoisCrystallineCompletion_one
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    galoisCrystallineCompletion p hgen 1 = RingHom.id _ :=
  RingHom.ext fun x => toBDeRhamPlus_injective hgen <|
    (toBDeRhamPlus_galoisCrystallineCompletion hgen 1 x).trans
      (AlgHom.congr_fun (galoisBDeRhamPlus_one p) _)

end Completion

/-! ### The image of `A_cris` in `B_dR^+` -/

/-- **`A_cris` inside `B_dR^+`**: the image of the injective map `A_cris → B_dR^+` for the
generator `ξ = p - [p♭]` of the kernel of `θ`; by `range_toBDeRhamPlus_eq_aCris` it is the image
for every generator. -/
def aCris : Subring 𝔹⁺ :=
  (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p)).range

/-- If `w = w' c`, then `Σ aₙ w^n/n! = Σ cⁿ aₙ w'^n/n!` in `B_dR^+`. -/
private theorem evalBDeRhamPlus_dividedPowerSeries_eq {w w' c : 𝔸}
    (hw : algebraMap 𝔸 𝔸ₚ w ∈ 𝕀) (hw' : algebraMap 𝔸 𝔸ₚ w' ∈ 𝕀) (hc : w = w' * c)
    (f : 𝔸⟦X⟧) :
    evalBDeRhamPlus p hw (dividedPowerSeries p f) =
      evalBDeRhamPlus p hw' (dividedPowerSeries p (rescale c f)) :=
  AdicCompletion.evalPowerSeries_eq_of_coeff_mul_pow_eq _ _ _ _ _ fun k => by
    rw [coeff_dividedPowerSeries_mul_pow, coeff_dividedPowerSeries_mul_pow, hc,
      dividedPower_mul_right, PowerSeries.coeff_rescale, map_mul]
    ring

/-- **`A_cris` does not depend on the generator**: for every generator `w` of the kernel of `θ`,
the image of `A_cris = CrystallineCompletion p w` in `B_dR^+` is `aCris p`. -/
theorem range_toBDeRhamPlus_eq_aCris {w : 𝔸}
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    (toBDeRhamPlus hgen).range = aCris p := by
  have hw := algebraMap_mem_ker_of_ker_eq_span hgen
  have hξ := algebraMap_mem_ker_fontaineThetaInvertP p (fontaineTheta_xi p)
  obtain ⟨u, hu⟩ := exists_eq_xi_mul_unit hgen
  refine SetLike.coe_injective ?_
  rw [aCris, RingHom.coe_range, RingHom.coe_range, range_toBDeRhamPlus hgen,
    range_toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p)]
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨rescale (u : 𝔸) f, rescale_mem_restrictedPowerSeries p _ hf,
      evalBDeRhamPlus_dividedPowerSeries_eq p hw hξ hu f⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨rescale (↑u⁻¹ : 𝔸) f, rescale_mem_restrictedPowerSeries p _ hf,
      evalBDeRhamPlus_dividedPowerSeries_eq p hξ hw
        (by rw [hu, mul_assoc, Units.mul_inv, mul_one]) f⟩

/-- `y ∈ A_cris` if and only if `y = Σ aₙ ξⁿ/n!` in `B_dR^+` for a series `Σ aₙ Xⁿ` over
`W(𝓞_ℂ_[p]♭)` whose coefficients tend to `0` `p`-adically. -/
theorem mem_aCris_iff {y : 𝔹⁺} :
    y ∈ aCris p ↔ ∃ f ∈ restrictedPowerSeries p,
      y = evalBDeRhamPlus p (algebraMap_mem_ker_fontaineThetaInvertP p (fontaineTheta_xi p))
        (dividedPowerSeries p f) := by
  rw [aCris, ← SetLike.mem_coe, RingHom.coe_range,
    range_toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p)]
  rfl

/-- The image of `W(𝓞_ℂ_[p]♭)` in `B_dR^+` lies in `A_cris`. -/
theorem algebraMap_mem_aCris (a : 𝔸) : algebraMap 𝔸 𝔹⁺ a ∈ aCris p := by
  rw [IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺ a]
  exact ⟨algebraMap (finiteDividedPowers p (xi p)) (CrystallineCompletion p (xi p))
      ⟨algebraMap 𝔸 𝔸ₚ a, algebraMap_mem_finiteDividedPowers (xi p) a⟩,
    toBDeRhamPlus_algebraMap (ker_fontaineTheta_eq_span_xi p) _⟩

/-- **`A_cris` is stable under `Gal(ℚ̄_p/ℚ_p)`.** -/
theorem galoisBDeRhamPlus_mem_aCris (σ : Gal(PadicAlgCl p/ℚ_[p])) {y : 𝔹⁺} (hy : y ∈ aCris p) :
    galoisBDeRhamPlus p σ y ∈ aCris p := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨_, toBDeRhamPlus_galoisCrystallineCompletion _ σ x⟩

/-- `p ^ k ∣ (p k)!`. -/
private theorem pow_dvd_factorial_mul (k : ℕ) : p ^ k ∣ (p * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_add, mul_one]
    exact (Nat.mul_dvd_mul ih (Nat.dvd_factorial hp.out.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/-- `1/n = (n - 1)! · (1/n!)` in `W(𝓞_ℂ_[p]♭)[1/p]`, for `n ≠ 0`. -/
private theorem algebraMap_inv_natCast_eq {n : ℕ} (hn : n ≠ 0) :
    algebraMap ℚ_[p] 𝔸ₚ (n : ℚ_[p])⁻¹ =
      (((n - 1).factorial : ℕ) : 𝔸ₚ) * Ring.inverse ((n.factorial : ℕ) : 𝔸ₚ) := by
  apply (isUnit_natCast p hn).mul_left_cancel
  rw [natCast_mul_algebraMap_inv p hn, ← mul_assoc, ← Nat.cast_mul, Nat.mul_factorial_pred hn,
    Ring.mul_inverse_cancel _ (isUnit_natCast_factorial n)]

/-- **`log [ε] ∈ A_cris`** for `ε ∈ 𝓞_ℂ_[p]♭` with `ε♯ = 1`: if `[ε] - 1 = ξ c`, then
`log [ε] = Σ_{n ≥ 1} (-1)^(n+1) (n-1)! cⁿ ξⁿ/n!`, with `p^k ∣ (n-1)!` for `n > p k`. -/
theorem logTeichmuller_mem_aCris {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) :
    logTeichmuller p h ∈ aCris p := by
  have hk : teichmuller p ε - 1 ∈ RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [RingHom.mem_ker, map_sub, map_one, fontaineTheta_teichmuller, h, sub_self]
  rw [ker_fontaineTheta_eq_span_xi, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  rw [mem_aCris_iff]
  refine ⟨PowerSeries.mk fun n =>
    if n = 0 then 0 else (-1) ^ (n + 1) * (((n - 1).factorial : ℕ) : 𝔸) * c ^ n,
    (mem_restrictedPowerSeries p).2 fun k => ⟨p * k + 1, fun n hn => ?_⟩, ?_⟩
  · rw [PowerSeries.coeff_mk, ite_eq_right (by omega)]
    obtain ⟨d, hd⟩ := (pow_dvd_factorial_mul p k).trans
      (Nat.factorial_dvd_factorial (show p * k ≤ n - 1 by omega))
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨(d : 𝔸), ?_⟩ _) _
    rw [hd, Nat.cast_mul, Nat.cast_pow]
  rw [logTeichmuller, logOneAdd]
  refine AdicCompletion.evalPowerSeries_eq_of_coeff_mul_pow_eq _ _ _ _ _ fun n => ?_
  rw [coeff_dividedPowerSeries_mul_pow, logSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  rw [ite_eq_right hn, ite_eq_right hn, ← hc, algebraMap_inv_natCast_eq p hn, dividedPower]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

/-- If `n! = p^v m` with `p ∤ m`, then `v ≤ n`: Legendre's formula
`(p - 1) v_p(n!) = n - s_p(n)`. -/
private theorem le_of_factorial_eq_pow_mul {n v m : ℕ} (hpm : ¬p ∣ m)
    (h : n.factorial = p ^ v * m) : v ≤ n := by
  have hv : multiplicity p n.factorial = v := by
    refine multiplicity_eq_of_dvd_of_not_dvd ⟨m, h⟩ fun hd => hpm ?_
    rw [h, pow_succ] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos v) hd
  have h1 := hp.out.sub_one_mul_multiplicity_factorial (n := n)
  rw [hv] at h1
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : v ≤ (p - 1) * v := Nat.le_mul_of_pos_left v h2
  omega

/-- `pⁿ/n! ∈ ℤ_[p]`: there is `e ∈ ℤ_[p]` with `e · n! = pⁿ`. -/
private theorem exists_mul_factorial_eq_pow (n : ℕ) :
    ∃ e : ℤ_[p], (e : ℚ_[p]) * (n.factorial : ℚ_[p]) = (p : ℚ_[p]) ^ n := by
  obtain ⟨v, m, hpm, hvm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p hp.out.ne_one
  have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
  have hv : v ≤ n := le_of_factorial_eq_pow_mul p hpm hvm
  refine ⟨(p : ℤ_[p]) ^ (n - v) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  have hum : (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hu.val_inv_mul
    rwa [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at this
  rw [hvm]
  push_cast
  calc ((p : ℚ_[p]) ^ (n - v) * (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) *
        ((p : ℚ_[p]) ^ v * (m : ℚ_[p]))
      = (p : ℚ_[p]) ^ (n - v) * (p : ℚ_[p]) ^ v *
          ((((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p])) := by ring
    _ = (p : ℚ_[p]) ^ n := by rw [hum, mul_one, ← pow_add, Nat.sub_add_cancel hv]

/-- If `e · n! = pⁿ` with `e ∈ ℤ_[p]`, then `1/n! = e · p⁻ⁿ` in `W(𝓞_ℂ_[p]♭)[1/p]`. -/
private theorem algebraMap_padicIntToAinf_mul_eq {n : ℕ} {e : ℤ_[p]}
    (he : (e : ℚ_[p]) * (n.factorial : ℚ_[p]) = (p : ℚ_[p]) ^ n) :
    algebraMap 𝔸 𝔸ₚ (padicIntToAinf p e) * algebraMap ℚ_[p] 𝔸ₚ (p : ℚ_[p])⁻¹ ^ n =
      Ring.inverse ((n.factorial : ℕ) : 𝔸ₚ) := by
  have hq : algebraMap ℚ_[p] 𝔸ₚ (e : ℚ_[p]) = algebraMap 𝔸 𝔸ₚ (padicIntToAinf p e) :=
    padicToLocalizationAway_coe p e
  have hinv : (e : ℚ_[p]) * ((p : ℚ_[p])⁻¹) ^ n = ((n.factorial : ℕ) : ℚ_[p])⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [mul_right_comm, he, ← mul_pow, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero),
      one_pow]
  apply (isUnit_natCast_factorial (p := p) n).mul_left_cancel
  rw [Ring.mul_inverse_cancel _ (isUnit_natCast_factorial n), ← hq, ← map_pow, ← map_mul, hinv,
    natCast_mul_algebraMap_inv p (Nat.factorial_ne_zero n)]

/-- **`A_cris ⊆ A_max`**: `Σ aₙ ξⁿ/n! = Σ (pⁿ/n!) aₙ (ξ/p)ⁿ` with `pⁿ/n! ∈ ℤ_p`. -/
theorem aCris_le_aMax : aCris p ≤ aMax p := by
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (mem_aCris_iff p).1 hy
  choose e he using exists_mul_factorial_eq_pow p
  refine Subring.mem_map.2 ⟨PowerSeries.mk fun n => PowerSeries.coeff n f * padicIntToAinf p (e n),
    (mem_restrictedPowerSeries p).2 fun k => ?_, ?_⟩
  · obtain ⟨N, hN⟩ := (mem_restrictedPowerSeries p).1 hf k
    exact ⟨N, fun n hn => by rw [PowerSeries.coeff_mk]; exact Dvd.dvd.mul_right (hN n hn) _⟩
  rw [RingHom.comp_apply]
  refine AdicCompletion.evalPowerSeries_eq_of_coeff_mul_pow_eq _ _ _ _ _ fun n => ?_
  rw [coeff_dividedPowerSeries_mul_pow, PowerSeries.coeff_map, PowerSeries.coeff_mk, xiDivP,
    dividedPower, ← algebraMap_padicIntToAinf_mul_eq p (he n), map_mul]
  ring

/-! ### The period `log [ε]` in `A_cris` -/

/-- **The period `log [ε] ∈ A_cris`** for `ε ∈ 𝓞_ℂ_[p]♭` with `ε♯ = 1`: the element of
`A_cris = CrystallineCompletion p ξ` whose image in `B_dR^+` is `log [ε]`
(`logTeichmuller_mem_aCris`); it is unique since `A_cris → B_dR^+` is injective. -/
def logTeichmullerCrystalline {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) :
    CrystallineCompletion p (xi p) :=
  Classical.choose (logTeichmuller_mem_aCris p h)

/-- The image of the period `log [ε] ∈ A_cris` in `B_dR^+` is `log [ε]`. -/
@[simp]
theorem toBDeRhamPlus_logTeichmullerCrystalline {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) :
    toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) (logTeichmullerCrystalline p h) =
      logTeichmuller p h :=
  Classical.choose_spec (logTeichmuller_mem_aCris p h)

/-- `σ(log [ε]) = log [σ ε]` in `A_cris`, for `ε♯ = 1`. -/
theorem galoisCrystallineCompletion_logTeichmullerCrystalline (σ : Gal(PadicAlgCl p/ℚ_[p]))
    {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1)
    (h' : (PreTilt.map p (integralGalois p σ).toRingHom ε).untilt = 1) :
    galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ
        (logTeichmullerCrystalline p h) =
      logTeichmullerCrystalline p h' :=
  toBDeRhamPlus_injective (ker_fontaineTheta_eq_span_xi p) (by
    rw [toBDeRhamPlus_galoisCrystallineCompletion, toBDeRhamPlus_logTeichmullerCrystalline,
      toBDeRhamPlus_logTeichmullerCrystalline, galoisBDeRhamPlus_logTeichmuller p σ h h'])

end PadicComplexInt
