/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/G9/BdREmb.lean`,
`ZInQKernel/Contrib/G9/I4Layer.lean`, `ZInQKernel/Contrib/OneProof/PanBerger.lean` and
`ZInQKernel/OneProof/H/LPrefix.lean` (https://github.com/Deicyde/diophantine-z-q), compared with
the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRing
public import MathlibExt.NumberTheory.Padics.ComplexInvariants

/-!
# The Galois action on the de Rham period ring of `ℂ_p`

The group `Gal(ℚ̄_p/ℚ_p)` acts on `ℂ_p` by `completionGalois`, the continuous extension of its
action on `ℚ̄_p = PadicAlgCl p`. This action preserves the norm, so it restricts to ring
automorphisms of `𝓞_ℂ_[p]` (`PadicComplexInt.integralGalois`). By functoriality of the tilt, of
Witt vectors, of `θ` and of the completion along `ker θ`, an automorphism of `𝓞_ℂ_[p]` induces
automorphisms of `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p` and `B_dR = BDeRham 𝓞_ℂ_[p] p`
(`BDeRhamPlus.map` and `BDeRham.mapOfRingEquiv`). This gives the action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on
`B_dR^+` and `B_dR` (`PadicComplexInt.galoisBDeRhamPlus`, `PadicComplexInt.galoisBDeRham`), as
in J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II,
§1.5.6–1.5.7 pp. 73–74.
We show that these are actions of `Gal(ℚ̄_p/ℚ_p)` (`PadicComplexInt.galoisBDeRhamPlus_mul`,
`PadicComplexInt.galoisBDeRham_mul` and the corresponding statements for `1`), that they fix
`ℚ_[p]`, that they are compatible with the inclusion `B_dR^+ ⊆ B_dR`, and that Fontaine's map
`θ : B_dR^+ → ℂ_[p]` is equivariant
(`PadicComplexInt.fontaineThetaBDeRhamPlus_galoisBDeRhamPlus`).
-/

@[expose] public noncomputable section

open Ideal WittVector MathlibExt.AlgebraicGeometry.HodgeTateComparison

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- The completed action `completionGalois p σ` of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `ℂ_[p]` preserves the
norm. -/
theorem norm_completionGalois (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    ‖completionGalois p σ x‖ = ‖x‖ := by
  rw [completionGalois_apply_eq_smul, PadicComplex.norm_smul_eq]

end PadicComplex

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-! ### The action on `𝓞_ℂ_[p]` -/

/-- The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `𝓞_ℂ_[p]`: the restriction of the completed action
`completionGalois p σ` on `ℂ_[p]`, which preserves the norm. -/
def integralGalois (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p] where
  toFun x := ⟨completionGalois p σ x, (mem_iff_norm_le_one p _).mpr (by
    rw [PadicComplex.norm_completionGalois]
    exact (mem_iff_norm_le_one p _).mp x.2)⟩
  invFun x := ⟨(completionGalois p σ).symm x, (mem_iff_norm_le_one p _).mpr (by
    rw [← PadicComplex.norm_completionGalois p σ, AlgEquiv.apply_symm_apply]
    exact (mem_iff_norm_le_one p _).mp x.2)⟩
  left_inv x := Subtype.ext ((completionGalois p σ).symm_apply_apply (x : ℂ_[p]))
  right_inv x := Subtype.ext ((completionGalois p σ).apply_symm_apply (x : ℂ_[p]))
  map_mul' x y := Subtype.ext (map_mul (completionGalois p σ) (x : ℂ_[p]) (y : ℂ_[p]))
  map_add' x y := Subtype.ext (map_add (completionGalois p σ) (x : ℂ_[p]) (y : ℂ_[p]))

/-- `integralGalois p σ` is the restriction of `completionGalois p σ`. -/
@[simp]
theorem coe_integralGalois (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : 𝓞_ℂ_[p]) :
    ((integralGalois p σ x : 𝓞_ℂ_[p]) : ℂ_[p]) = completionGalois p σ x :=
  rfl

/-- The map of tilts induced by `integralGalois p σ` is injective. -/
theorem preTiltMap_integralGalois_injective (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Function.Injective (PreTilt.map p (integralGalois p σ).toRingHom) :=
  Function.LeftInverse.injective (g := PreTilt.map p (integralGalois p σ).symm.toRingHom)
    fun x => by
      rw [← RingHom.comp_apply, ← PreTilt.map_comp, RingEquiv.symm_toRingHom_comp_toRingHom,
        PreTilt.map_id, RingHom.id_apply]

/-! ### The action on `B_dR^+` and `B_dR` -/

/-- The map `ℚ_[p] → W(𝓞_ℂ_[p]♭)[1/p]` is `padicToLocalizationAway p`. -/
private theorem algebraMap_padic_localizationAway (r : ℚ_[p]) :
    algebraMap ℚ_[p] 𝔸ₚ r = padicToLocalizationAway p r :=
  rfl

/-- The map of `W(𝓞_ℂ_[p]♭)[1/p]` induced by a ring endomorphism `f` of the tilt fixes the image
of `ℚ_[p]`. -/
theorem awayMapNatCast_algebraMap_padic
    (f : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p) (r : ℚ_[p]) :
    Localization.awayMapNatCast (WittVector.map f) p (algebraMap ℚ_[p] 𝔸ₚ r) =
      algebraMap ℚ_[p] 𝔸ₚ r := by
  have h : (Localization.awayMapNatCast (WittVector.map f) p).comp (algebraMap ℚ_[p] 𝔸ₚ) =
      algebraMap ℚ_[p] 𝔸ₚ :=
    IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) <| RingHom.ext fun z => by
      simp only [RingHom.comp_apply, PadicInt.algebraMap_apply,
        algebraMap_padic_localizationAway, padicToLocalizationAway_coe,
        Localization.awayMapNatCast_algebraMap, map_padicIntToAinf]
  exact RingHom.congr_fun h r

/-- **The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `B_dR^+`**: the map `BDeRhamPlus.map p` induced by the
automorphism `integralGalois p σ` of `𝓞_ℂ_[p]`, as a `ℚ_[p]`-algebra map. -/
def galoisBDeRhamPlus (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : 𝔹⁺ →ₐ[ℚ_[p]] 𝔹⁺ :=
  { BDeRhamPlus.map p (integralGalois p σ).toRingHom with
    commutes' := fun r => by
      change BDeRhamPlus.map p (integralGalois p σ).toRingHom (algebraMap ℚ_[p] 𝔹⁺ r) = _
      rw [IsScalarTower.algebraMap_apply ℚ_[p] 𝔸ₚ 𝔹⁺, BDeRhamPlus.map_algebraMap,
        awayMapNatCast_algebraMap_padic] }

/-- `galoisBDeRhamPlus p σ` is the map induced by `integralGalois p σ`. -/
theorem galoisBDeRhamPlus_toRingHom (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    (galoisBDeRhamPlus p σ : 𝔹⁺ →+* 𝔹⁺) = BDeRhamPlus.map p (integralGalois p σ).toRingHom :=
  rfl

/-- **The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `B_dR`**: the map `BDeRham.mapOfRingEquiv p` induced by
the automorphism `integralGalois p σ` of `𝓞_ℂ_[p]`, as a `ℚ_[p]`-algebra map. -/
def galoisBDeRham (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : 𝔹 →ₐ[ℚ_[p]] 𝔹 :=
  { BDeRham.mapOfRingEquiv p (integralGalois p σ) with
    commutes' := fun r => by
      change BDeRham.mapOfRingEquiv p (integralGalois p σ) (algebraMap ℚ_[p] 𝔹 r) = _
      rw [IsScalarTower.algebraMap_apply ℚ_[p] 𝔹⁺ 𝔹, BDeRham.mapOfRingEquiv_algebraMap]
      exact congrArg (algebraMap 𝔹⁺ 𝔹) ((galoisBDeRhamPlus p σ).commutes r) }

/-- `galoisBDeRham p σ` is the map induced by `integralGalois p σ`. -/
theorem galoisBDeRham_toRingHom (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    (galoisBDeRham p σ : 𝔹 →+* 𝔹) = BDeRham.mapOfRingEquiv p (integralGalois p σ) :=
  rfl

/-- The action on `B_dR` extends the action on `B_dR^+`. -/
@[simp]
theorem galoisBDeRham_algebraMap (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : 𝔹⁺) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 x) = algebraMap 𝔹⁺ 𝔹 (galoisBDeRhamPlus p σ x) :=
  BDeRham.mapOfRingEquiv_algebraMap p _ x

/-- The action on `B_dR^+` extends the map of `W(𝓞_ℂ_[p]♭)[1/p]` induced by `integralGalois p σ`. -/
theorem galoisBDeRhamPlus_algebraMap (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : 𝔸ₚ) :
    galoisBDeRhamPlus p σ (algebraMap 𝔸ₚ 𝔹⁺ x) =
      algebraMap 𝔸ₚ 𝔹⁺ (Localization.awayMapNatCast
        (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom)) p x) :=
  BDeRhamPlus.map_algebraMap p _ x

/-- The action on `B_dR^+` extends the map of `W(𝓞_ℂ_[p]♭)` induced by `integralGalois p σ`. -/
@[simp]
theorem galoisBDeRhamPlus_algebraMap_wittVector (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (w : 𝔸) :
    galoisBDeRhamPlus p σ (algebraMap 𝔸 𝔹⁺ w) =
      algebraMap 𝔸 𝔹⁺ (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) w) := by
  rw [IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺, galoisBDeRhamPlus_algebraMap,
    Localization.awayMapNatCast_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The action on `B_dR` is injective. -/
theorem galoisBDeRham_injective (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Function.Injective (galoisBDeRham p σ) :=
  (galoisBDeRham p σ).toRingHom.injective

/-! ### The action laws -/

/-- The action on `𝓞_ℂ_[p]` is multiplicative: `σ * τ` acts as `τ` followed by `σ`. -/
theorem integralGalois_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    integralGalois p (σ * τ) = (integralGalois p τ).trans (integralGalois p σ) :=
  RingEquiv.ext fun x => Subtype.ext (completionGalois_mul_apply p σ τ x)

/-- The identity of `Gal(ℚ̄_p/ℚ_p)` acts trivially on `𝓞_ℂ_[p]`. -/
@[simp]
theorem integralGalois_one : integralGalois p 1 = RingEquiv.refl _ :=
  RingEquiv.ext fun x => Subtype.ext (completionGalois_one_apply p x)

/-- The action on `B_dR^+` is multiplicative: `σ * τ` acts as `τ` followed by `σ`. -/
theorem galoisBDeRhamPlus_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    galoisBDeRhamPlus p (σ * τ) = (galoisBDeRhamPlus p σ).comp (galoisBDeRhamPlus p τ) :=
  AlgHom.toRingHom_injective <| by
    rw [AlgHom.comp_toRingHom, galoisBDeRhamPlus_toRingHom, galoisBDeRhamPlus_toRingHom,
      galoisBDeRhamPlus_toRingHom, integralGalois_mul]
    exact BDeRhamPlus.map_comp p (integralGalois p σ).toRingHom (integralGalois p τ).toRingHom

/-- The identity of `Gal(ℚ̄_p/ℚ_p)` acts trivially on `B_dR^+`. -/
@[simp]
theorem galoisBDeRhamPlus_one : galoisBDeRhamPlus p 1 = AlgHom.id ℚ_[p] _ :=
  AlgHom.toRingHom_injective <| by
    rw [galoisBDeRhamPlus_toRingHom, integralGalois_one, AlgHom.id_toRingHom]
    exact BDeRhamPlus.map_id p

/-- The action on `B_dR` is multiplicative: `σ * τ` acts as `τ` followed by `σ`. -/
theorem galoisBDeRham_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    galoisBDeRham p (σ * τ) = (galoisBDeRham p σ).comp (galoisBDeRham p τ) :=
  AlgHom.toRingHom_injective <| by
    rw [AlgHom.comp_toRingHom, galoisBDeRham_toRingHom, galoisBDeRham_toRingHom,
      galoisBDeRham_toRingHom, integralGalois_mul, BDeRham.mapOfRingEquiv_trans]

/-- The identity of `Gal(ℚ̄_p/ℚ_p)` acts trivially on `B_dR`. -/
@[simp]
theorem galoisBDeRham_one : galoisBDeRham p 1 = AlgHom.id ℚ_[p] _ :=
  AlgHom.toRingHom_injective <| by
    rw [galoisBDeRham_toRingHom, integralGalois_one, BDeRham.mapOfRingEquiv_refl,
      AlgHom.id_toRingHom]

/-! ### Equivariance of `θ` -/

/-- `θ : B_dR^+ → ℂ_[p]` is the reduction modulo `ker θ`, followed by the isomorphisms
`W(𝓞_ℂ_[p]♭)[1/p] ⧸ ker θ ≃ 𝓞_ℂ_[p][1/p] ≃ ℂ_[p]`. -/
private theorem fontaineThetaBDeRhamPlus_apply (x : 𝔹⁺) :
    fontaineThetaBDeRhamPlus p x =
      localizationAwayEquiv p (RingHom.quotientKerEquivOfSurjective
        (fontaineThetaInvertP_surjective p) (AdicCompletion.evalOneₐ 𝕀 x)) :=
  rfl

/-- The map of adic completions induced by a ring map `f` reduces, modulo the ideals, to the map
of quotients induced by `f`. -/
private theorem evalOneₐ_mapRingHom {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A)
    (J : Ideal B) (f : A →+* B) (h : I.map f ≤ J) (x : AdicCompletion I A) :
    AdicCompletion.evalOneₐ J (AdicCompletion.mapRingHom I J f h x) =
      Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.1 h) (AdicCompletion.evalOneₐ I x) := by
  simp only [AdicCompletion.evalOneₐ, AlgHom.comp_apply, AdicCompletion.evalₐ_mapRingHom]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 x)
  rw [← ha]
  rfl

/-- Modulo `ker θ`, the action on `B_dR^+` is the map of `W(𝓞_ℂ_[p]♭)[1/p] ⧸ ker θ` induced by
`integralGalois p σ`. -/
private theorem evalOneₐ_galoisBDeRhamPlus (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : 𝔹⁺) :
    AdicCompletion.evalOneₐ 𝕀 (galoisBDeRhamPlus p σ x) =
      Ideal.quotientMap 𝕀 (Localization.awayMapNatCast
          (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom)) p)
        (ker_fontaineThetaInvertP_le_comap p _) (AdicCompletion.evalOneₐ 𝕀 x) :=
  evalOneₐ_mapRingHom _ _ _ _ x

/-- The isomorphism `W(𝓞_ℂ_[p]♭)[1/p] ⧸ ker θ ≃ 𝓞_ℂ_[p][1/p]` induced by `θ` intertwines the maps
induced by a ring map `f` of `𝓞_ℂ_[p]`, by naturality of `θ`. -/
private theorem quotientKerEquiv_quotientMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (q : 𝔸ₚ ⧸ 𝕀) :
    RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p)
        (Ideal.quotientMap 𝕀 (Localization.awayMapNatCast (WittVector.map (PreTilt.map p f)) p)
          (ker_fontaineThetaInvertP_le_comap p f) q) =
      Localization.awayMapNatCast f p
        (RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.quotientMap_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, ← RingHom.comp_apply,
    fontaineThetaInvertP_comp_awayMapNatCast, RingHom.comp_apply]

/-- The isomorphism `𝓞_ℂ_[p][1/p] ≃ ℂ_[p]` intertwines the map induced by `integralGalois p σ`
and `completionGalois p σ`. -/
private theorem localizationAwayEquiv_awayMapNatCast (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (u : Localization.Away (p : 𝓞_ℂ_[p])) :
    localizationAwayEquiv p (Localization.awayMapNatCast (integralGalois p σ).toRingHom p u) =
      completionGalois p σ (localizationAwayEquiv p u) := by
  have h : (localizationAwayEquiv p).toRingEquiv.toRingHom.comp
      (Localization.awayMapNatCast (integralGalois p σ).toRingHom p) =
      (completionGalois p σ).toRingEquiv.toRingHom.comp
        (localizationAwayEquiv p).toRingEquiv.toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : 𝓞_ℂ_[p])) <| RingHom.ext fun x => by
      simp
  exact RingHom.congr_fun h u

/-- **Equivariance of `θ`**: `θ (σ x) = σ (θ x)` for `x ∈ B_dR^+`. -/
theorem fontaineThetaBDeRhamPlus_galoisBDeRhamPlus (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : 𝔹⁺) :
    fontaineThetaBDeRhamPlus p (galoisBDeRhamPlus p σ x) =
      completionGalois p σ (fontaineThetaBDeRhamPlus p x) := by
  rw [fontaineThetaBDeRhamPlus_apply, fontaineThetaBDeRhamPlus_apply,
    evalOneₐ_galoisBDeRhamPlus, quotientKerEquiv_quotientMap,
    localizationAwayEquiv_awayMapNatCast]

end PadicComplexInt
