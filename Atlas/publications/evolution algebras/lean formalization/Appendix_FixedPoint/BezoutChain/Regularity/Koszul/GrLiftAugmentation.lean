/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.PolynomialExactness
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExteriorSumDecomposition
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExteriorTransport
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerIdentification
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps

/-!
# The gr-lift augmentation data (`εgr`, `τ`)

This file constructs the augmentation half of `GrLiftIntertwining`
(`GradedLift.lean`): the gr-side augmentation `εgr` and the
semilinear residue comparison `τ`, commuting with the file-5 tower
augmentation.

* (§1) `grlift_augGr`: the gr-side augmentation `mk ∘ zeroEquiv`, as a
  bare `LinearMap` (not via `Submodule.mkQ`, whose `Module`-TC over
  `grRegular` does not close — see `GradedLift.lean`). The quotient
  scalar laws hold by `rfl`. Unconditional.
* (§2) Ideal correspondence (`towerIdeal` maps to the gr-class span under
  any `σ` with `σ Xᵢ = grClassᵢ`) and `grlift_tau`: the `σ`-semilinear
  quotient comparison, built on `Ideal.quotientEquiv`, with computation,
  injectivity, and surjectivity. Unconditional on `[hX]`.
* (§3) `towerAug_collapse`: the file-5 tower augmentation is `mk ∘
  zeroEquiv` at every rung (via `extSplitZero`/`zeroEquiv` naturality).
  unconditional.
* (§4) `augment_e0_zeroEquiv`: a degree-0 bridge transport intertwines the
  two `zeroEquiv`s with `σ` (span induction). Unconditional on the `E0`
  laws.
* (§5) Masters `koszulAugment_data` (on `[hX]`) and
  `koszulAugment_data_of_kerEqBot` (on `[hker]`, via
  `grlift_grEquiv_comp`): the augmentation existential in the exact
  `GrLiftIntertwining` shape.

## References

Project (all read-only):
* `Regularity/Koszul/GradedLift.lean`: `GrLiftIntertwining` (:310),
  `grlift_grClass` (:213), `grlift_grEquivOfKerEqBot` (:362),
  `grlift_grEquiv_comp` (:374).
* `Regularity/Koszul/PolynomialExactness.lean`: `towerIdeal` (:100),
  `towerIdeal_top` (:526), `towerAug` (:475), `towerMap_mkQ` (:280),
  `baseAug` (:381).
* `Regularity/Koszul/GradedSurjection.lean`: `polySurjResidue` (:344).
* `Regularity/Koszul/AssociatedGradedRing.lean`: `grRegular` (:663).
* `Regularity/Koszul/AugmentedConeStep.lean`: `koszulStepAug_apply` (:212).
* `Regularity/Koszul/ExteriorSumDecomposition.lean`: `extSplitZero_apply` (:414).
* `Regularity/Koszul/ExteriorTransport.lean`: `extTransport_span_induction`
  (:143).
* `Regularity/HomologicalDepth/TowerIdentification.lean`: `towerPiSemilinear` (:220).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `LinearAlgebra/ExteriorPower/Basic.lean`: `zeroEquiv`,
  `zeroEquiv_ιMulti`, `zeroEquiv_naturality`.
* `RingTheory/Ideal/Quotient/Operations.lean`: `quotientEquiv`,
  `quotientEquiv_mk`.
* `RingTheory/Ideal/Quotient/Defs.lean`: `mk`, `mk_surjective`,
  `mk_eq_mk`.
* `RingTheory/Ideal/Maps.lean`: `map_span`.

## Status

* §1 (`grlift_augGr` + computation + quotient scalar laws):
  unconditional.
* §2 (ideal correspondence, `grlift_tau` + computation + injective +
  surjective): unconditional on `[hX]`.
* §3 (`towerAug_collapse`): unconditional.
* §4 (`augment_e0_zeroEquiv`): unconditional on the `E0` laws.
* §5 `koszulAugment_data`: conditional-exact on `[hX]` + `E0` laws;
  `koszulAugment_data_of_kerEqBot`: conditional-exact on `[hker]` + `E0`
  laws.

## Residual register

* Full `GrLiftIntertwining` assembly (joining this file's augmentation
  data with the `E`-lane commutation for the same `E`, via
  `extTransport_unique`) stays with the consumer.
* `hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥` closes via the
  `hwit`-chain (`ker_assemble_ker_eq_bot`, parallel lane).
-/


namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GrLiftAugmentation

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PolynomialExactness
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AugmentedConeStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ExteriorSumDecomposition
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ExteriorTransport
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerIdentification

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-! ## §1. The gr-side augmentation -/

/-- Scalar action on the gr-side residue quotient computes on
representatives (definitional: the quotient `SMul` is `mk` of the
product).
-/
theorem augment_quot_smul_gr (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (c z : grRegular P) :
    c • Ideal.Quotient.mk
        (Ideal.span (Set.range (fun i => grlift_grClass P d g hgen i))) z
      = Ideal.Quotient.mk
        (Ideal.span (Set.range (fun i => grlift_grClass P d g hgen i)))
        (c * z) :=
  rfl

/-- `Submodule.mkQ` and `Ideal.Quotient.mk` agree (both are `Quotient.mk`).
-/
theorem augment_mkQ_eq_mk {S : Type*} [CommRing S] (J : Ideal S) (z : S) :
    (Submodule.mkQ (J : Submodule S S)) z = Ideal.Quotient.mk J z :=
  rfl

/-- The gr-side augmentation `εgr = mk ∘ zeroEquiv`, as a bare linear map
(`Submodule.mkQ` over `grRegular` does not elaborate: the `Module`
self-instance unification fails, see `GradedLift.lean`).
-/
noncomputable def grlift_augGr (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ↥(⋀[grRegular P]^0 (Fin d → grRegular P)) →ₗ[grRegular P]
      (grRegular P ⧸ Ideal.span
        (Set.range (fun i => grlift_grClass P d g hgen i))) where
  toFun b := Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv _ _) b)
  map_add' x y := by simp
  map_smul' c x := by
    simp only [map_smul, smul_eq_mul, augment_quot_smul_gr,
      RingHom.id_apply]

/-- Computation rule for the gr-side augmentation.
-/
theorem grlift_augGr_apply (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (b : ↥(⋀[grRegular P]^0 (Fin d → grRegular P))) :
    grlift_augGr P d g hgen b
      = Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv _ _) b) :=
  rfl

/-! ## §2. Ideal correspondence and the residue comparison `τ` -/

/-- Ideal correspondence: under any `σ` sending each variable to the
corresponding gr-class, the top tower ideal maps onto the gr-class span.
-/
theorem augment_ideal_eq (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (σ : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hX : ∀ i, σ (MvPolynomial.X i) = grlift_grClass P d g hgen i) :
    Ideal.span (Set.range (fun i => grlift_grClass P d g hgen i))
      = Ideal.map σ.toRingHom (towerIdeal (grliftK P) d d) := by
  rw [towerIdeal_top, Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, hX i⟩
  · rintro ⟨x, ⟨j, rfl⟩, hx⟩
    exact ⟨j, (hX j).symm.trans hx⟩

/-- The `σ`-semilinear residue comparison `τ`, on `Ideal.quotientEquiv`
(the bare `LinearMap` wrapper avoids `Submodule.mapQ`, whose `Module`
self-instance over `grRegular` fails as in §1).
-/
noncomputable def grlift_tau (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (σ : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hX : ∀ i, σ (MvPolynomial.X i) = grlift_grClass P d g hgen i) :
    (MvPolynomial (Fin d) (grliftK P) ⧸ towerIdeal (grliftK P) d d)
      →ₛₗ[σ.toRingHom]
      (grRegular P ⧸ Ideal.span
        (Set.range (fun i => grlift_grClass P d g hgen i))) where
  toFun := ⇑(Ideal.quotientEquiv (towerIdeal (grliftK P) d d)
    (Ideal.span (Set.range (fun i => grlift_grClass P d g hgen i))) σ
    (augment_ideal_eq P d g hgen σ hX))
  map_add' x y := map_add _ _ _
  map_smul' c x := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (σ (c * s))
      = Ideal.Quotient.mk _ (σ c * σ s)
    rw [map_mul]

/-- Computation rule for `τ`.
-/
theorem grlift_tau_apply (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (σ : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hX : ∀ i, σ (MvPolynomial.X i) = grlift_grClass P d g hgen i)
    (s : MvPolynomial (Fin d) (grliftK P)) :
    grlift_tau P d g hgen σ hX (Ideal.Quotient.mk _ s)
      = Ideal.Quotient.mk _ (σ s) :=
  rfl

/-- `τ` is injective (it is a ring equiv as a function).
-/
theorem grlift_tau_injective (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (σ : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hX : ∀ i, σ (MvPolynomial.X i) = grlift_grClass P d g hgen i) :
    Function.Injective (grlift_tau P d g hgen σ hX) := by
  intro a b hab
  exact (Ideal.quotientEquiv (towerIdeal (grliftK P) d d)
    (Ideal.span (Set.range (fun i => grlift_grClass P d g hgen i))) σ
    (augment_ideal_eq P d g hgen σ hX)).injective hab

/-- `τ` is surjective (it is a ring equiv as a function).
-/
theorem grlift_tau_surjective (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (σ : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hX : ∀ i, σ (MvPolynomial.X i) = grlift_grClass P d g hgen i) :
    Function.Surjective (grlift_tau P d g hgen σ hX) := by
  intro q
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk _ (σ.symm t), by
    rw [grlift_tau_apply, RingEquiv.apply_symm_apply]⟩

/-! ## §3. The tower augmentation collapses to `mk ∘ zeroEquiv` -/

/-- `extSplitZero` preserves `zeroEquiv`-values (it is `map 0 fst`, and
`zeroEquiv` is natural).
-/
theorem augment_zeroEquiv_extSplitZero (d n : ℕ)
    (z : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
      (towerMod (grliftK P) d (n + 1)))) :
    (exteriorPower.zeroEquiv (MvPolynomial (Fin d) (grliftK P))
        (towerMod (grliftK P) d n)) (extSplitZero z)
      = (exteriorPower.zeroEquiv (MvPolynomial (Fin d) (grliftK P))
        (towerMod (grliftK P) d (n + 1))) z := by
  have hnat := exteriorPower.zeroEquiv_naturality
    (LinearMap.fst (MvPolynomial (Fin d) (grliftK P))
      (towerMod (grliftK P) d n) (MvPolynomial (Fin d) (grliftK P)))
  have h := LinearMap.congr_fun hnat z
  rw [LinearMap.comp_apply, ← extSplitZero_apply] at h
  exact h

/-- The tower augmentation at every rung is `mk ∘ zeroEquiv`: the
`towerMap`s collapse (`towerMap_mkQ`) and `extSplitZero` preserves
scalars (§3 helper).
-/
theorem towerAug_collapse (d : ℕ) (n : ℕ) (h : n ≤ d)
    (b : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
      (towerMod (grliftK P) d n))) :
    towerAug (grliftK P) d n h b
      = (Submodule.mkQ (towerIdeal (grliftK P) d n : Submodule _ _))
        ((exteriorPower.zeroEquiv (MvPolynomial (Fin d) (grliftK P))
          (towerMod (grliftK P) d n)) b) := by
  revert h b
  induction n with
  | zero =>
    intro h b
    change baseAug (grliftK P) d b = _
    rfl
  | succ n ih =>
    intro h b
    change koszulStepAug _ _ b = _
    rw [koszulStepAug_apply, ih, towerMap_mkQ,
      augment_zeroEquiv_extSplitZero]

/-! ## §4. Degree-0 transport intertwines the `zeroEquiv`s -/

/-- A degree-0 bridge transport intertwines the two `zeroEquiv`s with `σ`:
by span induction, the `0`/`+`/`•` cases close by the transport laws and
the generator case by `zeroEquiv_ιMulti` on both sides.
-/
theorem augment_e0_zeroEquiv (d : ℕ)
    (σ : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (E0 : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
        (towerMod (grliftK P) d d)) ≃
      ↥(⋀[grRegular P]^0 (Fin d → grRegular P)))
    (hE0 : E0 0 = 0)
    (hadd : ∀ x y, E0 (x + y) = E0 x + E0 y)
    (hsmul : ∀ (c : MvPolynomial (Fin d) (grliftK P)) x,
      E0 (c • x) = (σ c) • E0 x)
    (hι0 : ∀ v : Fin 0 → towerMod (grliftK P) d d,
      E0 (exteriorPower.ιMulti _ _ v) = exteriorPower.ιMulti _ _
        (fun i => (towerPiSemilinear (grliftK P) d (grRegular P) σ) (v i)))
    (b : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
      (towerMod (grliftK P) d d))) :
    (exteriorPower.zeroEquiv (grRegular P) (Fin d → grRegular P)) (E0 b)
      = σ ((exteriorPower.zeroEquiv (MvPolynomial (Fin d) (grliftK P))
        (towerMod (grliftK P) d d)) b) := by
  refine extTransport_span_induction
    (P := fun b => (exteriorPower.zeroEquiv (grRegular P)
      (Fin d → grRegular P)) (E0 b)
      = σ ((exteriorPower.zeroEquiv (MvPolynomial (Fin d) (grliftK P))
        (towerMod (grliftK P) d d)) b)) ?_ ?_ ?_ ?_ b
  · simp [hE0]
  · intro x y hx hy
    simp only [hadd, map_add, hx, hy]
  · intro c x hx
    simp only [hsmul, map_smul, hx, smul_eq_mul, map_mul]
  · intro v
    simp only [hι0 v, exteriorPower.zeroEquiv_ιMulti, map_one]

/-! ## §5. Masters -/

/-- Augmentation data in the exact `GrLiftIntertwining` shape, from the
generator correspondence plus the degree-0 transport laws.

Conditional on exactly `[hX]` + `E0` laws. -/
theorem koszulAugment_data (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (σ : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hX : ∀ i, σ (MvPolynomial.X i) = grlift_grClass P d g hgen i)
    (E0 : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
        (towerMod (grliftK P) d d)) ≃
      ↥(⋀[grRegular P]^0 (Fin d → grRegular P)))
    (hE0 : E0 0 = 0)
    (hadd : ∀ x y, E0 (x + y) = E0 x + E0 y)
    (hsmul : ∀ (c : MvPolynomial (Fin d) (grliftK P)) x,
      E0 (c • x) = (σ c) • E0 x)
    (hι0 : ∀ v : Fin 0 → towerMod (grliftK P) d d,
      E0 (exteriorPower.ιMulti _ _ v) = exteriorPower.ιMulti _ _
        (fun i => (towerPiSemilinear (grliftK P) d (grRegular P) σ) (v i))) :
    ∃ εgr : ↥(⋀[grRegular P]^0 (Fin d → grRegular P)) →ₗ[grRegular P]
        (grRegular P ⧸ Ideal.span
          (Set.range (fun i => grlift_grClass P d g hgen i))),
      ∃ τ : (MvPolynomial (Fin d) (grliftK P) ⧸ towerIdeal (grliftK P) d d)
          →ₛₗ[σ.toRingHom]
          (grRegular P ⧸ Ideal.span
            (Set.range (fun i => grlift_grClass P d g hgen i))),
        (∀ b : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
            (towerMod (grliftK P) d d)),
          τ (towerAug (grliftK P) d d (le_refl d) b) = εgr (E0 b))
        ∧ Function.Injective τ ∧ Function.Surjective τ := by
  refine ⟨grlift_augGr P d g hgen, grlift_tau P d g hgen σ hX, ?_, ?_, ?_⟩
  · intro b
    have hE := augment_e0_zeroEquiv P d σ E0 hE0 hadd hsmul hι0 b
    have hcol := towerAug_collapse P d d (le_refl d) b
    rw [hcol, augment_mkQ_eq_mk, grlift_tau_apply, grlift_augGr_apply, hE]
  · exact grlift_tau_injective P d g hgen σ hX
  · exact grlift_tau_surjective P d g hgen σ hX

/-- Augmentation data over the `ker`-built gr-equivalence: `hX` discharges
by the proved `X ↦ gr-class` computation.

Conditional on exactly `[hker]` + `E0` laws. -/
theorem koszulAugment_data_of_kerEqBot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    (E0 : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
        (towerMod (grliftK P) d d)) ≃
      ↥(⋀[grRegular P]^0 (Fin d → grRegular P)))
    (hE0 : E0 0 = 0)
    (hadd : ∀ x y, E0 (x + y) = E0 x + E0 y)
    (hsmul : ∀ (c : MvPolynomial (Fin d) (grliftK P)) x,
      E0 (c • x)
        = ((grlift_grEquivOfKerEqBot P d g hgen hker) c) • E0 x)
    (hι0 : ∀ v : Fin 0 → towerMod (grliftK P) d d,
      E0 (exteriorPower.ιMulti _ _ v) = exteriorPower.ιMulti _ _
        (fun i => (towerPiSemilinear (grliftK P) d (grRegular P)
          (grlift_grEquivOfKerEqBot P d g hgen hker)) (v i))) :
    ∃ εgr : ↥(⋀[grRegular P]^0 (Fin d → grRegular P)) →ₗ[grRegular P]
        (grRegular P ⧸ Ideal.span
          (Set.range (fun i => grlift_grClass P d g hgen i))),
      ∃ τ : (MvPolynomial (Fin d) (grliftK P) ⧸ towerIdeal (grliftK P) d d)
          →ₛₗ[(grlift_grEquivOfKerEqBot P d g hgen hker).toRingHom]
          (grRegular P ⧸ Ideal.span
            (Set.range (fun i => grlift_grClass P d g hgen i))),
        (∀ b : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
            (towerMod (grliftK P) d d)),
          τ (towerAug (grliftK P) d d (le_refl d) b) = εgr (E0 b))
        ∧ Function.Injective τ ∧ Function.Surjective τ :=
  koszulAugment_data P d g hgen (grlift_grEquivOfKerEqBot P d g hgen hker)
    (grlift_grEquiv_comp P d g hgen hker) E0 hE0 hadd hsmul hι0

#print axioms koszulAugment_data
#print axioms koszulAugment_data_of_kerEqBot
#print axioms grlift_tau_injective
#print axioms grlift_tau_surjective
#print axioms towerAug_collapse
#print axioms augment_e0_zeroEquiv

end GrLiftAugmentation
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
