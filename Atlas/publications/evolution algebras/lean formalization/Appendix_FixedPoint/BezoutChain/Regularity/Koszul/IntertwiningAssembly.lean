/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExteriorTransport
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GrLiftAugmentation
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.PolynomialExactness
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerIdentification
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing

/-!
# Intertwining assembly: full `GrLiftIntertwining` on `[hker]` only

Joins the two proved halves of `GrLiftIntertwining`
(`GradedLift.lean`) at the same explicit transport family:

* (§1) `extTransport_contract_comm_of_laws`: the `∀ E` form of
  `extTransport_contract_comm` (`ExteriorTransport.lean`), reproved
  in-repo (the fit-check): any law-abiding family commutes with the
  Koszul contractions given `hφ`. Same proof (span induction against
  the alternating-sum formula). Unconditional.
* (§2) `assemble_transport_agree`: coherence via `extTransport_unique`
  (`ExteriorTransport.lean`) — any law-abiding family agrees with
  the explicit N3 bridge family `extBridgeEquiv`. This is the provable
  form of the join: the N3-master existential witness's laws are not
  exported, so the assembly instantiates the explicit family everywhere
  instead of identifying the opaque witness. Unconditional.
* (§3) Master `koszulIntertwine_assemble`: full `GrLiftIntertwining`
  over the `ker`-built equiv, conditional-exact on `[hker]` only.
  Takes `E := extBridgeEquiv` family, discharges `hX`/`hφ` via the
  proved `grlift_grEquiv_comp` (`GradedLift.lean`) +
  `extTransport_phi_compat_of_X`, proves commutation via §1, and feeds
  `E 0` + its laws (`extBridgeEquiv_zero/add/smul/ιMulti`,
  `ExteriorTransport.lean`) into the N4 master
  `koszulAugment_data_of_kerEqBot` (`GrLiftAugmentation.lean`).

## References

Project (all read-only):
* `Regularity/Koszul/GradedLift.lean`: `GrLiftIntertwining` (:310),
  `grlift_phiGr` (:224), `grlift_grClass` (:213),
  `grlift_grEquivOfKerEqBot` (:362), `grlift_grEquiv_comp` (:374).
* `Regularity/Koszul/ExteriorTransport.lean`: `ExtTransportBridge` (:128),
  `extTransport_span_induction` (:143), `extTransport_map_sum` (:169),
  `koszulContract_ιMulti_extPow` (:190),
  `extTransport_contract_comm` (:207), `extTransport_unique` (:256),
  `extTransport_phi_compat_of_X` (:347),
  `extBridgeEquiv` (:594) + laws (:609-637),
  `extTransportBridge_proved` (:653).
* `Regularity/Koszul/GrLiftAugmentation.lean`: `koszulAugment_data_of_kerEqBot`
  (:389).
* `Regularity/HomologicalDepth/TowerIdentification.lean`: `towerPiSemilinear` (:220).
* `Regularity/Koszul/PolynomialExactness.lean`: `towerMod` (:440), `towerPhi` (:457).
* `Regularity/Koszul/KoszulComplex.lean`: `koszulContract`,
  `koszulContractOfSequence` (:455).
* `Regularity/Koszul/GradedSurjection.lean`: `polySurjResidue` (:344).

## Status

* §1 `extTransport_contract_comm_of_laws`: unconditional.
* §2 `assemble_transport_agree`: unconditional.
* §3 `koszulIntertwine_assemble`: conditional-exact on `[hker]`.

## Residual register

* `hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥` closes via the
  `hwit`-chain (`ker_assemble_ker_eq_bot`, parallel lane).
* `GrLiftFiltrationConseq` (filtration half of the gr-exact-implies-exact
  lift) stays with the lift consumer (`grlift_r2_exact`,
  `GradedLift.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace IntertwiningAssembly

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ExteriorTransport
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GrLiftAugmentation
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PolynomialExactness
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerIdentification
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-! ## §1. Commutation for any law-abiding family (fit-check, in-repo) -/

/-- The `∀ E` form of `extTransport_contract_comm`: the transported
bijections commute with the Koszul contractions, given the bridge laws
for the same `E` plus functional compatibility
(`φT (e x) = σ (φS x)`). By span induction
(`extTransport_span_induction`): the `0`/`+`/`•` cases close by the
bridge laws, and the generator case is the alternating-sum formula
(`koszulContract_ιMulti_extPow`) on both sides plus `hφ`.

This reproves the fit-check in-repo so the assembly can instantiate the
explicit `extBridgeEquiv` family (whose laws are proved) directly,
instead of depending on the opaque witness of the N3-master
existential.
-/
theorem extTransport_contract_comm_of_laws (κ : Type*) [Field κ] (d : ℕ)
    (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T)
    (φS : (towerMod κ d d) →ₗ[MvPolynomial (Fin d) κ] MvPolynomial (Fin d) κ)
    (φT : (Fin d → T) →ₗ[T] T)
    (E : ∀ k : ℕ,
      ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃
        ↥(⋀[T]^k (Fin d → T)))
    (hE0 : ∀ k, E k 0 = 0)
    (hadd : ∀ k x y, E k (x + y) = E k x + E k y)
    (hsmul : ∀ k (c : MvPolynomial (Fin d) κ) x,
      E k (c • x) = (σ c) • E k x)
    (hι : ∀ k (v : Fin k → towerMod κ d d),
      E k (exteriorPower.ιMulti _ _ v) =
        exteriorPower.ιMulti _ _ fun i => (towerPiSemilinear κ d T σ) (v i))
    (hφ : ∀ x : towerMod κ d d,
      φT ((towerPiSemilinear κ d T σ) x) = σ (φS x)) :
    ∀ k (w : ↥(⋀[MvPolynomial (Fin d) κ]^(k + 1) (towerMod κ d d))),
      E k (koszulContract φS k w) =
        koszulContract φT k (E (k + 1) w) := by
  intro k
  apply extTransport_span_induction
  · rw [map_zero, hE0 k, hE0 (k + 1), map_zero]
  · intro x y hx hy
    rw [map_add, hadd k, hadd (k + 1), map_add, hx, hy]
  · intro r y hy
    rw [map_smul, hsmul k, hsmul (k + 1), map_smul, hy]
  · intro v
    change E k (koszulContract φS k (exteriorPower.ιMulti _ k.succ v)) =
      koszulContract φT k (E k.succ (exteriorPower.ιMulti _ k.succ v))
    rw [koszulContract_ιMulti_extPow φS k v]
    rw [extTransport_map_sum κ d T E k (hE0 k) (hadd k) Finset.univ _]
    simp only [hsmul k, hι k]
    rw [hι k.succ v, koszulContract_ιMulti_extPow φT k _]
    apply Finset.sum_congr rfl
    intro j _
    have hσneg : ∀ m : ℕ,
        σ ((-1 : MvPolynomial (Fin d) κ) ^ m) = (-1 : T) ^ m := by
      intro m
      rw [map_pow]
      congr 1
      simp
    have hcoeff : σ ((-1 : MvPolynomial (Fin d) κ) ^ j.val * φS (v j)) =
        (-1 : T) ^ j.val *
          φT ((fun i => (towerPiSemilinear κ d T σ) (v i)) j) := by
      rw [map_mul, hσneg, ← hφ (v j)]
    have harg : (fun i => (towerPiSemilinear κ d T σ) ((v ∘ Fin.succAbove j) i)) =
        (fun i => (towerPiSemilinear κ d T σ) (v i)) ∘ Fin.succAbove j := rfl
    rw [hcoeff, harg]

/-! ## §2. Coherence: the explicit family is the unique transport -/

/-- Any law-abiding family agrees with the explicit N3 bridge family,
via `extTransport_unique`. This is the provable form of the E/aug join:
both halves of the assembly below instantiate `extBridgeEquiv`, so no
opaque-witness identification is needed.
-/
theorem assemble_transport_agree (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    (E' : ∀ k : ℕ,
      ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^k (towerMod (grliftK P) d d)) ≃
        ↥(⋀[grRegular P]^k (Fin d → grRegular P)))
    (hE0' : ∀ k, E' k 0 = 0)
    (hadd' : ∀ k x y, E' k (x + y) = E' k x + E' k y)
    (hsmul' : ∀ k (c : MvPolynomial (Fin d) (grliftK P)) x,
      E' k (c • x) =
        ((grlift_grEquivOfKerEqBot P d g hgen hker) c) • E' k x)
    (hι' : ∀ k (v : Fin k → towerMod (grliftK P) d d),
      E' k (exteriorPower.ιMulti _ _ v) = exteriorPower.ιMulti _ _
        fun i => (towerPiSemilinear (grliftK P) d (grRegular P)
          (grlift_grEquivOfKerEqBot P d g hgen hker)) (v i)) :
    ∀ k, E' k = extBridgeEquiv (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker) k :=
  extTransport_unique (grliftK P) d (grRegular P)
    (grlift_grEquivOfKerEqBot P d g hgen hker) E'
    (fun k => extBridgeEquiv (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker) k)
    hE0' (extBridgeEquiv_zero (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    hadd' (extBridgeEquiv_add (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    hsmul' (extBridgeEquiv_smul (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    hι' (extBridgeEquiv_ιMulti (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))

/-! ## §3. Master: full intertwining on `[hker]` -/

/-- Full `GrLiftIntertwining` over the `ker`-built gr-equivalence:
`E` is the N3 bridge family (commutation via §1, `hφ` via
`extTransport_phi_compat_of_X` + the proved `grlift_grEquiv_comp`),
and the augmentation data comes from the N4 master fed with `E 0` +
its proved laws.

Conditional on exactly `[hker]`. -/
theorem koszulIntertwine_assemble (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    GrLiftIntertwining P d g hgen
      (grlift_grEquivOfKerEqBot P d g hgen hker) := by
  have hX : ∀ i, (grlift_grEquivOfKerEqBot P d g hgen hker)
      (MvPolynomial.X i) = grlift_grClass P d g hgen i :=
    grlift_grEquiv_comp P d g hgen hker
  have hφ : ∀ x : towerMod (grliftK P) d d,
      koszulContractOfSequence (fun i => grlift_grClass P d g hgen i)
        ((towerPiSemilinear (grliftK P) d (grRegular P)
          (grlift_grEquivOfKerEqBot P d g hgen hker)) x) =
        (grlift_grEquivOfKerEqBot P d g hgen hker)
          (towerPhi (grliftK P) d d x) :=
    extTransport_phi_compat_of_X (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker)
      (fun i => grlift_grClass P d g hgen i) hX
  have hcomm := extTransport_contract_comm_of_laws (grliftK P) d (grRegular P)
    (grlift_grEquivOfKerEqBot P d g hgen hker)
    (towerPhi (grliftK P) d d)
    (koszulContractOfSequence (fun i => grlift_grClass P d g hgen i))
    (fun k => extBridgeEquiv (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker) k)
    (extBridgeEquiv_zero (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    (extBridgeEquiv_add (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    (extBridgeEquiv_smul (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    (extBridgeEquiv_ιMulti (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    hφ
  obtain ⟨εgr, τ, hτ, hτinj, hτsurj⟩ :=
    koszulAugment_data_of_kerEqBot P d g hgen hker
      (extBridgeEquiv (grliftK P) d (grRegular P)
        (grlift_grEquivOfKerEqBot P d g hgen hker) 0)
      (extBridgeEquiv_zero (grliftK P) d (grRegular P)
        (grlift_grEquivOfKerEqBot P d g hgen hker) 0)
      (extBridgeEquiv_add (grliftK P) d (grRegular P)
        (grlift_grEquivOfKerEqBot P d g hgen hker) 0)
      (extBridgeEquiv_smul (grliftK P) d (grRegular P)
        (grlift_grEquivOfKerEqBot P d g hgen hker) 0)
      (extBridgeEquiv_ιMulti (grliftK P) d (grRegular P)
        (grlift_grEquivOfKerEqBot P d g hgen hker) 0)
  refine ⟨fun k => extBridgeEquiv (grliftK P) d (grRegular P)
    (grlift_grEquivOfKerEqBot P d g hgen hker) k,
    extBridgeEquiv_zero (grliftK P) d (grRegular P)
      (grlift_grEquivOfKerEqBot P d g hgen hker),
    ?_, εgr, τ, hτ, hτinj, hτsurj⟩
  intro k w
  exact hcomm k w

#print axioms extTransport_contract_comm_of_laws
#print axioms assemble_transport_agree
#print axioms koszulIntertwine_assemble

end IntertwiningAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
