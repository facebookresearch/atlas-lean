/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/PanBerger.lean`,
`ZInQKernel/Contrib/OneProof/AbstractAcris.lean`, `ZInQKernel/Contrib/OneProof/AbstractBcris.lean`
and `ZInQKernel/Contrib/OneProof/AbstractBst.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.SemistablePeriodRing

/-!
# Fontaine's rings `B_cris` and `B_st` as abstract rings

Let `A_cris = PadicComplexInt.CrystallineCompletion p ξ` be Fontaine's ring (J.-M. Fontaine,
*Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II, §2.3.3 p. 78), with its
action of `Gal(ℚ̄_p/ℚ_p)` (`PadicComplexInt.galoisCrystallineCompletion`), and let
`t = log [ε] ∈ A_cris` (`PadicComplexInt.logTeichmullerCrystalline`). We define the rings

* `B_cris^+ = A_cris[1/p]` (`PadicComplexInt.BCrisPlus`), a localization,
* `B_cris = B_cris^+[1/t]` (`PadicComplexInt.BCris`), a localization (Fontaine, *op. cit.*,
  Exposé II, §2.3.4 pp. 78–79),
* `B_st = B_cris[X]` (`PadicComplexInt.BSt`), a polynomial ring,

with their actions of `Gal(ℚ̄_p/ℚ_p)`: on `B_cris^+` and `B_cris` the actions induced by the
action on `A_cris` (`σ(t) = a t` with `a ∈ ℤ_p` nonzero), and on `B_st` the action on the
coefficients with `σ(X) = X + log [u_σ]`, where `σ(p̃) = p̃ u_σ`
(`PadicComplexInt.BSt.galois_X`; Fontaine, *op. cit.*, §4.3.3 p. 89). We construct injective
Galois-equivariant `ℚ_[p]`-algebra maps to `B_dR`, `X ↦ log [p̃]` on `B_st`, whose images are the
subalgebras `PadicComplexInt.bCrisPlus`, `PadicComplexInt.bCris` and `PadicComplexInt.bSt`
(Fontaine, *op. cit.*, §4.1.2–4.1.3 pp. 83–84 and Théorème 4.2.4 p. 86 for `K = ℚ_p`), and the
resulting equivariant isomorphisms (`PadicComplexInt.BCris.equivBCris`,
`PadicComplexInt.BSt.equivBSt`).

The injectivity of `B_st → B_dR` is the transcendence of `log [p̃]` over `B_cris`
(`PadicComplexInt.transcendental_logPTilde_bCris`).
-/

@[expose] public noncomputable section

open Ideal WittVector Polynomial

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p
local notation "𝔸cris" => CrystallineCompletion p (xi p)

/-! ### `B_cris^+ = A_cris[1/p]` -/

/-- **Fontaine's ring `B_cris^+ = A_cris[1/p]`**: the localization of
`A_cris = CrystallineCompletion p ξ` away from `p`. -/
def BCrisPlus : Type :=
  Localization.Away (p : CrystallineCompletion p (xi p))

namespace BCrisPlus

instance instCommRing : CommRing (BCrisPlus p) :=
  inferInstanceAs (CommRing (Localization.Away (p : 𝔸cris)))

instance instAlgebra : Algebra 𝔸cris (BCrisPlus p) :=
  inferInstanceAs (Algebra 𝔸cris (Localization.Away (p : 𝔸cris)))

instance instIsLocalization : IsLocalization.Away (p : 𝔸cris) (BCrisPlus p) :=
  inferInstanceAs (IsLocalization.Away (p : 𝔸cris) (Localization.Away (p : 𝔸cris)))

/-- The ring map `W(𝓞_ℂ_[p]♭) → A_cris`. -/
def ofWittVector : 𝔸 →+* 𝔸cris :=
  (algebraMap (finiteDividedPowers p (xi p)) 𝔸cris).comp
    ((algebraMap 𝔸 𝔸ₚ).codRestrict (finiteDividedPowers p (xi p))
      (algebraMap_mem_finiteDividedPowers (xi p)))

/-- The ring map `W(𝓞_ℂ_[p]♭)[1/p] → B_cris^+` induced by `W(𝓞_ℂ_[p]♭) → A_cris`. -/
def ofLocalizationAway : 𝔸ₚ →+* BCrisPlus p :=
  Localization.awayLift ((algebraMap 𝔸cris (BCrisPlus p)).comp (ofWittVector p)) p (by
    rw [RingHom.comp_apply, map_natCast, map_natCast]
    have := IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus p) (p : 𝔸cris)
    rwa [map_natCast] at this)

/-- The `ℚ_[p]`-algebra structure of `B_cris^+`, through `ℚ_[p] → W(𝓞_ℂ_[p]♭)[1/p]`. -/
instance instAlgebraPadic : Algebra ℚ_[p] (BCrisPlus p) :=
  ((ofLocalizationAway p).comp (algebraMap ℚ_[p] 𝔸ₚ)).toAlgebra

/-- `W(𝓞_ℂ_[p]♭)[1/p] → B_cris^+` extends `W(𝓞_ℂ_[p]♭) → A_cris`. -/
private theorem ofLocalizationAway_algebraMap (a : 𝔸) :
    ofLocalizationAway p (algebraMap 𝔸 𝔸ₚ a) =
      algebraMap 𝔸cris (BCrisPlus p) (ofWittVector p a) := by
  simp only [ofLocalizationAway, Localization.awayLift, IsLocalization.Away.lift_eq,
    RingHom.comp_apply]

/-- The image of `z ∈ ℤ_[p]` in `B_cris^+` is the image of `z ∈ W(𝓞_ℂ_[p]♭)` in `A_cris`. -/
private theorem algebraMap_padicInt (z : ℤ_[p]) :
    algebraMap ℚ_[p] (BCrisPlus p) (z : ℚ_[p]) =
      algebraMap 𝔸cris (BCrisPlus p) (ofWittVector p (padicIntToAinf p z)) := by
  change ofLocalizationAway p (padicToLocalizationAway p z) = _
  rw [padicToLocalizationAway_coe, ofLocalizationAway_algebraMap]

/-- The action on `A_cris` extends the action on `W(𝓞_ℂ_[p]♭)`. -/
private theorem galoisCrystallineCompletion_ofWittVector (σ : Gal(PadicAlgCl p/ℚ_[p])) (a : 𝔸) :
    galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ (ofWittVector p a) =
      ofWittVector p (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) a) := by
  refine (galoisCrystallineCompletion_algebraMap _ σ _).trans (congrArg _ (Subtype.ext ?_))
  rw [coe_galoisFiniteDividedPowers]
  exact Localization.awayMapNatCast_algebraMap _ _ a

/-- The map `A_cris → B_dR^+` extends the map `W(𝓞_ℂ_[p]♭) → B_dR^+`. -/
private theorem toBDeRhamPlus_ofWittVector (a : 𝔸) :
    toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) (ofWittVector p a) = algebraMap 𝔸 𝔹⁺ a := by
  refine (toBDeRhamPlus_algebraMap _ _).trans ?_
  rw [IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺]
  rfl

/-- The image of `z ∈ ℤ_[p]` in `B_dR^+` is the image of `z ∈ W(𝓞_ℂ_[p]♭)`. -/
private theorem algebraMap_padicInt_bDeRhamPlus (z : ℤ_[p]) :
    algebraMap ℚ_[p] 𝔹⁺ (z : ℚ_[p]) = algebraMap 𝔸 𝔹⁺ (padicIntToAinf p z) := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] 𝔸ₚ 𝔹⁺, IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺]
  exact congrArg _ (padicToLocalizationAway_coe p z)

/-- A ring endomorphism of `B_cris^+` extending the action of `σ` on `A_cris` fixes `ℚ_[p]`. -/
private theorem map_algebraMap_of_galois {σ : Gal(PadicAlgCl p/ℚ_[p])}
    {g : BCrisPlus p →+* BCrisPlus p}
    (hg : ∀ x, g (algebraMap 𝔸cris (BCrisPlus p) x) = algebraMap 𝔸cris (BCrisPlus p)
      (galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ x)) (r : ℚ_[p]) :
    g (algebraMap ℚ_[p] (BCrisPlus p) r) = algebraMap ℚ_[p] (BCrisPlus p) r := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    (j := g.comp (algebraMap ℚ_[p] (BCrisPlus p))) (RingHom.ext fun z => ?_)) r
  simp only [RingHom.comp_apply, PadicInt.algebraMap_apply]
  rw [algebraMap_padicInt, hg, galoisCrystallineCompletion_ofWittVector, map_padicIntToAinf]

/-- A ring map `B_cris^+ → B_dR` extending `A_cris → B_dR^+ → B_dR` is `ℚ_[p]`-linear. -/
private theorem map_algebraMap_of_toBDeRham {g : BCrisPlus p →+* 𝔹}
    (hg : ∀ x, g (algebraMap 𝔸cris (BCrisPlus p) x) =
      algebraMap 𝔹⁺ 𝔹 (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) x)) (r : ℚ_[p]) :
    g (algebraMap ℚ_[p] (BCrisPlus p) r) = algebraMap ℚ_[p] 𝔹 r := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    (j := g.comp (algebraMap ℚ_[p] (BCrisPlus p))) (RingHom.ext fun z => ?_)) r
  simp only [RingHom.comp_apply, PadicInt.algebraMap_apply]
  rw [algebraMap_padicInt, hg, toBDeRhamPlus_ofWittVector,
    IsScalarTower.algebraMap_apply ℚ_[p] 𝔹⁺ 𝔹, algebraMap_padicInt_bDeRhamPlus]

/-- `p` is a unit of `B_dR`. -/
private theorem isUnit_natCast_bDeRham : IsUnit ((p : ℕ) : 𝔹) := by
  rw [← map_natCast (algebraMap ℚ_[p] 𝔹) p]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)).map _

/-- **The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `B_cris^+`**, induced by the action on `A_cris`. -/
def galois (σ : Gal(PadicAlgCl p/ℚ_[p])) : BCrisPlus p →ₐ[ℚ_[p]] BCrisPlus p :=
  { IsLocalization.Away.lift (S := BCrisPlus p) (p : 𝔸cris)
      (g := (algebraMap 𝔸cris (BCrisPlus p)).comp
        (galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ)) (by
        rw [RingHom.comp_apply, map_natCast, map_natCast]
        have := IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus p) (p : 𝔸cris)
        rwa [map_natCast] at this) with
    commutes' := by
      exact map_algebraMap_of_galois p (IsLocalization.Away.lift_eq (S := BCrisPlus p) _ _) }

/-- On `A_cris`, the action on `B_cris^+` is the action on `A_cris`. -/
theorem galois_algebraMap (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : 𝔸cris) :
    galois p σ (algebraMap 𝔸cris (BCrisPlus p) x) =
      algebraMap 𝔸cris (BCrisPlus p) (galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p)
        σ x) := by
  simp only [galois, AlgHom.coe_mk, IsLocalization.Away.lift_eq, RingHom.comp_apply]

/-- **The embedding `B_cris^+ → B_dR`**, induced by the injective map `A_cris → B_dR^+`. -/
def toBDeRham : BCrisPlus p →ₐ[ℚ_[p]] 𝔹 :=
  { IsLocalization.Away.lift (S := BCrisPlus p) (p : 𝔸cris)
      (g := (algebraMap 𝔹⁺ 𝔹).comp (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p))) (by
        rw [RingHom.comp_apply, map_natCast, map_natCast]
        exact isUnit_natCast_bDeRham p) with
    commutes' := by
      exact map_algebraMap_of_toBDeRham p (IsLocalization.Away.lift_eq (S := BCrisPlus p) _ _) }

/-- On `A_cris`, the embedding `B_cris^+ → B_dR` is the map `A_cris → B_dR^+ → B_dR`. -/
theorem toBDeRham_algebraMap (x : 𝔸cris) :
    toBDeRham p (algebraMap 𝔸cris (BCrisPlus p) x) =
      algebraMap 𝔹⁺ 𝔹 (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) x) := by
  simp only [toBDeRham, AlgHom.coe_mk, IsLocalization.Away.lift_eq, RingHom.comp_apply]

/-- **The embedding `B_cris^+ → B_dR` is injective.** -/
theorem toBDeRham_injective : Function.Injective (toBDeRham p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (p : 𝔸cris)) x
  have h : algebraMap 𝔹⁺ 𝔹 (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) a) = 0 := by
    rw [← toBDeRham_algebraMap, ← IsLocalization.mk'_spec (BCrisPlus p) a s, map_mul, hx,
      zero_mul]
  have ha : a = 0 := toBDeRhamPlus_injective _ ((algebraMap_bDeRham_injective p
    (h.trans (map_zero (algebraMap 𝔹⁺ 𝔹)).symm)).trans
      (map_zero (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p))).symm)
  rw [ha, IsLocalization.mk'_zero]

/-- **The embedding `B_cris^+ → B_dR` is Galois equivariant.** -/
theorem toBDeRham_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCrisPlus p) :
    toBDeRham p (galois p σ x) = galoisBDeRham p σ (toBDeRham p x) := by
  have h : (toBDeRham p : BCrisPlus p →+* 𝔹).comp (galois p σ : BCrisPlus p →+* BCrisPlus p) =
      (galoisBDeRham p σ : 𝔹 →+* 𝔹).comp (toBDeRham p : BCrisPlus p →+* 𝔹) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : 𝔸cris)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, RingHom.coe_coe, galois_algebraMap, toBDeRham_algebraMap,
        toBDeRhamPlus_galoisCrystallineCompletion, galoisBDeRham_algebraMap])
  exact RingHom.congr_fun h x

/-- Every element of `B_cris^+` is `c a` with `c ∈ ℚ_[p]` and `a ∈ A_cris`. -/
private theorem exists_eq_algebraMap_mul (x : BCrisPlus p) :
    ∃ (c : ℚ_[p]) (a : 𝔸cris),
      x = algebraMap ℚ_[p] (BCrisPlus p) c * algebraMap 𝔸cris (BCrisPlus p) a := by
  obtain ⟨a, ⟨_, k, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (p : 𝔸cris)) x
  refine ⟨((p : ℚ_[p]) ^ k)⁻¹, a, ?_⟩
  have e : algebraMap 𝔸cris (BCrisPlus p) ((p : 𝔸cris) ^ k) =
      algebraMap ℚ_[p] (BCrisPlus p) ((p : ℚ_[p]) ^ k) := by
    rw [map_pow, map_pow, map_natCast, map_natCast]
  rw [IsLocalization.mk'_eq_iff_eq_mul, e, mul_right_comm, ← map_mul,
    inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)), map_one, one_mul]

/-- **The image of `B_cris^+` in `B_dR` is `PadicComplexInt.bCrisPlus`.** -/
theorem range_toBDeRham : (toBDeRham p).range = bCrisPlus p := by
  refine le_antisymm ?_ (Algebra.adjoin_le ?_)
  · intro z hz
    obtain ⟨x, rfl⟩ := (toBDeRham p).mem_range.mp hz
    obtain ⟨c, a, rfl⟩ := exists_eq_algebraMap_mul p x
    rw [map_mul, AlgHom.commutes, toBDeRham_algebraMap]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
      (algebraMap_mem_bCrisPlus p (RingHom.mem_range_self _ a))
  · rintro _ ⟨y, ⟨a, rfl⟩, rfl⟩
    exact (toBDeRham p).mem_range.mpr ⟨algebraMap 𝔸cris (BCrisPlus p) a, toBDeRham_algebraMap p a⟩

end BCrisPlus

/-! ### `B_cris = B_cris^+[1/t]` -/

/-- **Fontaine's ring `B_cris = B_cris^+[1/t]`**: the localization of `B_cris^+` away from
`t = log [ε] ∈ A_cris` for `ε = (1, ζ_p, ζ_{p²}, …)`. -/
def BCris : Type :=
  Localization.Away (algebraMap (CrystallineCompletion p (xi p)) (BCrisPlus p)
    (logTeichmullerCrystalline p (untilt_epsilon p)))

namespace BCris

instance instCommRing : CommRing (BCris p) :=
  inferInstanceAs (CommRing (Localization.Away (algebraMap 𝔸cris (BCrisPlus p)
    (logTeichmullerCrystalline p (untilt_epsilon p)))))

instance instAlgebra : Algebra (BCrisPlus p) (BCris p) :=
  inferInstanceAs (Algebra (BCrisPlus p) (Localization.Away (algebraMap 𝔸cris (BCrisPlus p)
    (logTeichmullerCrystalline p (untilt_epsilon p)))))

instance instIsLocalization : IsLocalization.Away (algebraMap 𝔸cris (BCrisPlus p)
    (logTeichmullerCrystalline p (untilt_epsilon p))) (BCris p) :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away (algebraMap 𝔸cris (BCrisPlus p)
    (logTeichmullerCrystalline p (untilt_epsilon p)))))

/-- The `A_cris`-algebra structure of `B_cris`, through `B_cris^+`. -/
instance instAlgebraCrystallineCompletion : Algebra 𝔸cris (BCris p) :=
  ((algebraMap (BCrisPlus p) (BCris p)).comp (algebraMap 𝔸cris (BCrisPlus p))).toAlgebra

instance instIsScalarTowerCrystallineCompletion : IsScalarTower 𝔸cris (BCrisPlus p) (BCris p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The `ℚ_[p]`-algebra structure of `B_cris`, through `B_cris^+`. -/
instance instAlgebraPadic : Algebra ℚ_[p] (BCris p) :=
  ((algebraMap (BCrisPlus p) (BCris p)).comp (algebraMap ℚ_[p] (BCrisPlus p))).toAlgebra

instance instIsScalarTowerPadic : IsScalarTower ℚ_[p] (BCrisPlus p) (BCris p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `σ(t) = a t` in `A_cris`, with `a ∈ ℤ_[p]` nonzero. -/
private theorem exists_galois_logTeichmullerCrystalline_eq (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    ∃ a : ℤ_[p], a ≠ 0 ∧ galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ
      (logTeichmullerCrystalline p (untilt_epsilon p)) =
        BCrisPlus.ofWittVector p (padicIntToAinf p a) *
          logTeichmullerCrystalline p (untilt_epsilon p) := by
  have h' : (PreTilt.map p (integralGalois p σ).toRingHom (epsilon p)).untilt = 1 := by
    rw [PreTilt.untilt_map, untilt_epsilon, map_one]
  have hne : PreTilt.map p (integralGalois p σ).toRingHom (epsilon p) ≠ 1 := fun h1 =>
    epsilon_ne_one p (preTiltMap_integralGalois_injective p σ (h1.trans (map_one _).symm))
  obtain ⟨a, ha, hlog⟩ := exists_logTeichmuller_eq_mul_of_ne_one p (untilt_epsilon p)
    (isPrimitiveRoot_untilt_frobeniusEquiv_symm_epsilon p) h' hne
  refine ⟨a, ha, ?_⟩
  rw [galoisCrystallineCompletion_logTeichmullerCrystalline p σ (untilt_epsilon p) h']
  apply toBDeRhamPlus_injective (ker_fontaineTheta_eq_span_xi p)
  rw [map_mul, toBDeRhamPlus_logTeichmullerCrystalline, toBDeRhamPlus_logTeichmullerCrystalline,
    hlog, BCrisPlus.toBDeRhamPlus_ofWittVector, BCrisPlus.algebraMap_padicInt_bDeRhamPlus]

/-- `σ(t)` is a unit of `B_cris`. -/
private theorem isUnit_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    IsUnit (((IsScalarTower.toAlgHom ℚ_[p] (BCrisPlus p) (BCris p)).comp
      (BCrisPlus.galois p σ))
        (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))) := by
  obtain ⟨a, ha, he⟩ := exists_galois_logTeichmullerCrystalline_eq p σ
  rw [AlgHom.comp_apply, BCrisPlus.galois_algebraMap, he, map_mul,
    ← BCrisPlus.algebraMap_padicInt, IsScalarTower.toAlgHom_apply, map_mul,
    ← IsScalarTower.algebraMap_apply]
  exact ((IsUnit.mk0 _ (PadicInt.coe_ne_zero.mpr ha)).map _).mul
    (IsLocalization.Away.algebraMap_isUnit _)

/-- `t` is a unit of `B_dR`. -/
private theorem isUnit_toBDeRham :
    IsUnit (BCrisPlus.toBDeRham p
      (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))) := by
  rw [BCrisPlus.toBDeRham_algebraMap, toBDeRhamPlus_logTeichmullerCrystalline]
  exact IsUnit.mk0 _ ((map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).mpr
    (logTeichmuller_ne_zero p _ (epsilon_ne_one p)))

/-- **The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `B_cris`**, induced by the action on `B_cris^+`:
`σ(t) = a t` with `a ∈ ℤ_p` nonzero is a unit of `B_cris`. -/
def galois (σ : Gal(PadicAlgCl p/ℚ_[p])) : BCris p →ₐ[ℚ_[p]] BCris p :=
  IsLocalization.Away.liftAlgHom (S := BCris p)
    (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))
    (f := (IsScalarTower.toAlgHom ℚ_[p] (BCrisPlus p) (BCris p)).comp (BCrisPlus.galois p σ))
    (by exact isUnit_galois p σ)

/-- On `B_cris^+`, the action on `B_cris` is the action on `B_cris^+`. -/
theorem galois_algebraMap (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCrisPlus p) :
    galois p σ (algebraMap (BCrisPlus p) (BCris p) x) =
      algebraMap (BCrisPlus p) (BCris p) (BCrisPlus.galois p σ x) := by
  rw [galois, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- **The embedding `B_cris → B_dR`**, induced by the embedding of `B_cris^+`. -/
def toBDeRham : BCris p →ₐ[ℚ_[p]] 𝔹 :=
  IsLocalization.Away.liftAlgHom (S := BCris p)
    (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))
    (f := BCrisPlus.toBDeRham p) (by exact isUnit_toBDeRham p)

/-- On `B_cris^+`, the embedding of `B_cris` is the embedding of `B_cris^+`. -/
theorem toBDeRham_algebraMap (x : BCrisPlus p) :
    toBDeRham p (algebraMap (BCrisPlus p) (BCris p) x) = BCrisPlus.toBDeRham p x := by
  rw [toBDeRham, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- On `A_cris`, the embedding of `B_cris` is the map `A_cris → B_dR^+ → B_dR`. -/
private theorem toBDeRham_algebraMap_crystallineCompletion (x : 𝔸cris) :
    toBDeRham p (algebraMap 𝔸cris (BCris p) x) =
      algebraMap 𝔹⁺ 𝔹 (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) x) := by
  rw [IsScalarTower.algebraMap_apply 𝔸cris (BCrisPlus p) (BCris p), toBDeRham_algebraMap,
    BCrisPlus.toBDeRham_algebraMap]

/-- **The embedding `B_cris → B_dR` is injective.** -/
theorem toBDeRham_injective : Function.Injective (toBDeRham p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers
    (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))) x
  have h : BCrisPlus.toBDeRham p y = 0 := by
    rw [← toBDeRham_algebraMap, ← IsLocalization.mk'_spec (BCris p) y s, map_mul, hx, zero_mul]
  rw [(injective_iff_map_eq_zero' _).mp (BCrisPlus.toBDeRham_injective p) y |>.mp h,
    IsLocalization.mk'_zero]

/-- **The embedding `B_cris → B_dR` is Galois equivariant.** -/
theorem toBDeRham_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCris p) :
    toBDeRham p (galois p σ x) = galoisBDeRham p σ (toBDeRham p x) := by
  have h : (toBDeRham p : BCris p →+* 𝔹).comp (galois p σ : BCris p →+* BCris p) =
      (galoisBDeRham p σ : 𝔹 →+* 𝔹).comp (toBDeRham p : BCris p →+* 𝔹) :=
    IsLocalization.ringHom_ext (Submonoid.powers
      (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p))))
      (RingHom.ext fun y => by
        simp only [RingHom.comp_apply, RingHom.coe_coe, galois_algebraMap, toBDeRham_algebraMap,
          BCrisPlus.toBDeRham_galois])
  exact RingHom.congr_fun h x

/-- **The image of `B_cris` in `B_dR` is `PadicComplexInt.bCris`.** -/
theorem range_toBDeRham : (toBDeRham p).range = bCris p := by
  set t := algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p))
  have ht : toBDeRham p (algebraMap (BCrisPlus p) (BCris p) t) =
      algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)) := by
    rw [toBDeRham_algebraMap, BCrisPlus.toBDeRham_algebraMap,
      toBDeRhamPlus_logTeichmullerCrystalline]
  have ht0 : algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).mpr
      (logTeichmuller_ne_zero p _ (epsilon_ne_one p))
  refine le_antisymm ?_ (Algebra.adjoin_le ?_)
  · intro z hz
    obtain ⟨x, rfl⟩ := (toBDeRham p).mem_range.mp hz
    obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers t) x
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hy : toBDeRham p (algebraMap (BCrisPlus p) (BCris p) y) ∈ bCris p := by
      rw [toBDeRham_algebraMap]
      exact bCrisPlus_le_bCris p (BCrisPlus.range_toBDeRham p ▸ AlgHom.mem_range_self _ y)
    have hs : toBDeRham p (algebraMap (BCrisPlus p) (BCris p) s) =
        algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)) ^ n := by
      rw [← hn, map_pow, map_pow, ht]
    have e : toBDeRham p (IsLocalization.mk' (BCris p) y s) =
        toBDeRham p (algebraMap (BCrisPlus p) (BCris p) y) *
          (algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)))⁻¹ ^ n := by
      rw [inv_pow, ← hs, eq_mul_inv_iff_mul_eq₀ (hs ▸ pow_ne_zero n ht0), ← map_mul,
        IsLocalization.mk'_spec]
    rw [e]
    exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (inv_logTeichmuller_epsilon_mem_bCris p) n)
  · rintro _ (⟨y, ⟨a, rfl⟩, rfl⟩ | h)
    · exact (toBDeRham p).mem_range.mpr
        ⟨algebraMap (BCrisPlus p) (BCris p) (algebraMap 𝔸cris (BCrisPlus p) a), by
          rw [toBDeRham_algebraMap, BCrisPlus.toBDeRham_algebraMap]⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      refine (toBDeRham p).mem_range.mpr
        ⟨IsLocalization.Away.invSelf (S := BCris p) t, eq_inv_of_mul_eq_one_left ?_⟩
      rw [← ht, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

/-- **`B_cris` is isomorphic to its image `PadicComplexInt.bCris ⊆ B_dR`**, Galois equivariantly
(`PadicComplexInt.BCris.coe_equivBCris_galois`). -/
def equivBCris : BCris p ≃ₐ[ℚ_[p]] bCris p :=
  (AlgEquiv.ofInjective (toBDeRham p) (toBDeRham_injective p)).trans
    (Subalgebra.equivOfEq _ _ (range_toBDeRham p))

/-- The isomorphism `B_cris ≃ bCris` is the embedding `B_cris → B_dR`. -/
theorem coe_equivBCris (x : BCris p) : (equivBCris p x : 𝔹) = toBDeRham p x :=
  rfl

/-- The isomorphism `B_cris ≃ bCris` is Galois equivariant. -/
theorem coe_equivBCris_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCris p) :
    (equivBCris p (galois p σ x) : 𝔹) = galoisBDeRham p σ (equivBCris p x) :=
  toBDeRham_galois p σ x

end BCris

/-! ### `B_st = B_cris[X]` -/

/-- **Fontaine's ring `B_st = B_cris[X]`**: the polynomial ring over `B_cris`, the variable `X`
standing for `log [p̃]`. -/
abbrev BSt : Type :=
  (BCris p)[X]

namespace BSt

/-- **The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `B_st = B_cris[X]`**: `σ` on the coefficients and
`σ(X) = X + log [u_σ]`, where `σ(p̃) = p̃ u_σ` (`PadicComplexInt.kummerUnit`) and
`log [u_σ] ∈ A_cris ⊆ B_cris`. -/
def galois (σ : Gal(PadicAlgCl p/ℚ_[p])) : BSt p →ₐ[ℚ_[p]] BSt p :=
  eval₂AlgHom ((IsScalarTower.toAlgHom ℚ_[p] (BCris p) (BSt p)).comp (BCris.galois p σ))
    (X + C (algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p (untilt_kummerUnit p σ))))
    fun _ => Commute.all _ _

/-- The action on `B_st` is the action on `B_cris` on the coefficients. -/
theorem galois_C (σ : Gal(PadicAlgCl p/ℚ_[p])) (b : BCris p) :
    galois p σ (C b) = C (BCris.galois p σ b) :=
  eval₂_C _ _

/-- **`σ(X) = X + log [u_σ]`** in `B_st = B_cris[X]`, where `σ(p̃) = p̃ u_σ`. -/
theorem galois_X (σ : Gal(PadicAlgCl p/ℚ_[p])) :
    galois p σ X = X + C (algebraMap 𝔸cris (BCris p)
      (logTeichmullerCrystalline p (untilt_kummerUnit p σ))) :=
  eval₂_X _ _

/-- **The embedding `B_st = B_cris[X] → B_dR`**: the embedding of `B_cris` on the coefficients
and `X ↦ log [p̃]`. -/
def toBDeRham : BSt p →ₐ[ℚ_[p]] 𝔹 :=
  eval₂AlgHom (BCris.toBDeRham p) (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) fun _ => Commute.all _ _

/-- The embedding of `B_st` is the embedding of `B_cris` on the coefficients. -/
theorem toBDeRham_C (b : BCris p) : toBDeRham p (C b) = BCris.toBDeRham p b :=
  eval₂_C _ _

/-- The embedding of `B_st` sends `X` to `log [p̃]`. -/
theorem toBDeRham_X : toBDeRham p X = algebraMap 𝔹⁺ 𝔹 (logPTilde p) :=
  eval₂_X _ _

/-- Through `B_cris ≃ bCris`, the embedding of `B_st` is the evaluation at `log [p̃]` of
polynomials over `bCris`. -/
private theorem toBDeRham_eq_aeval (P : BSt p) :
    toBDeRham p P = aeval (algebraMap 𝔹⁺ 𝔹 (logPTilde p))
      (P.map (BCris.equivBCris p : BCris p →+* bCris p)) := by
  rw [aeval_def, eval₂_map]
  rfl

/-- **The embedding `B_st = B_cris[X] → B_dR`, `X ↦ log [p̃]`, is injective** (Fontaine,
Exposé II, Théorème 4.2.4 p. 86, for `K = ℚ_p`): `log [p̃]` is transcendental over `B_cris`. -/
theorem toBDeRham_injective : Function.Injective (toBDeRham p) := fun P Q h => by
  rw [toBDeRham_eq_aeval, toBDeRham_eq_aeval] at h
  exact Polynomial.map_injective _ (BCris.equivBCris p).injective
    (aeval_logPTilde_bCris_injective p h)

/-- **The embedding `B_st → B_dR` is Galois equivariant**: on `X` this is
`σ(log [p̃]) = log [p̃] + log [u_σ]`. -/
theorem toBDeRham_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BSt p) :
    toBDeRham p (galois p σ x) = galoisBDeRham p σ (toBDeRham p x) := by
  have h : (toBDeRham p : BSt p →+* 𝔹).comp (galois p σ : BSt p →+* BSt p) =
      (galoisBDeRham p σ : 𝔹 →+* 𝔹).comp (toBDeRham p : BSt p →+* 𝔹) := by
    refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · simp only [RingHom.comp_apply, RingHom.coe_coe, galois_C, toBDeRham_C,
        BCris.toBDeRham_galois]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, galois_X, map_add, toBDeRham_X, toBDeRham_C,
        galoisBDeRham_algebraMap_logPTilde]
      rw [BCris.toBDeRham_algebraMap_crystallineCompletion,
        toBDeRhamPlus_logTeichmullerCrystalline]
  exact RingHom.congr_fun h x

/-- **The image of `B_st` in `B_dR` is `PadicComplexInt.bSt = B_cris[log [p̃]]`.** -/
theorem range_toBDeRham : (toBDeRham p).range = bSt p := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨P, rfl⟩ := (toBDeRham p).mem_range.mp hy
    rw [toBDeRham_eq_aeval, ← coe_bCrisPolynomialEquiv]
    exact Subtype.prop _
  · obtain ⟨Q, hQ⟩ := (bCrisPolynomialEquiv p).surjective ⟨y, hy⟩
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (BCris.equivBCris p : BCris p →+* bCris p)
      (BCris.equivBCris p).surjective Q
    exact (toBDeRham p).mem_range.mpr
      ⟨P, (toBDeRham_eq_aeval p P).trans (congrArg Subtype.val hQ)⟩

/-- **`B_st = B_cris[X]` is isomorphic to its image `PadicComplexInt.bSt ⊆ B_dR`**, by
`X ↦ log [p̃]`, Galois equivariantly (`PadicComplexInt.BSt.coe_equivBSt_galois`). -/
def equivBSt : BSt p ≃ₐ[ℚ_[p]] bSt p :=
  (AlgEquiv.ofInjective (toBDeRham p) (toBDeRham_injective p)).trans
    (Subalgebra.equivOfEq _ _ (range_toBDeRham p))

/-- The isomorphism `B_st ≃ bSt` is the embedding `B_st → B_dR`. -/
theorem coe_equivBSt (x : BSt p) : (equivBSt p x : 𝔹) = toBDeRham p x :=
  rfl

/-- The isomorphism `B_st ≃ bSt` sends `X` to `log [p̃]`. -/
theorem coe_equivBSt_X : (equivBSt p X : 𝔹) = algebraMap 𝔹⁺ 𝔹 (logPTilde p) :=
  toBDeRham_X p

/-- The isomorphism `B_st ≃ bSt` is Galois equivariant. -/
theorem coe_equivBSt_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BSt p) :
    (equivBSt p (galois p σ x) : 𝔹) = galoisBDeRham p σ (equivBSt p x) :=
  toBDeRham_galois p σ x

end BSt

end PadicComplexInt
