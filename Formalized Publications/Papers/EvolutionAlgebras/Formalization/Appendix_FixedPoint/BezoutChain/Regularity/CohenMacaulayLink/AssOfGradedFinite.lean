/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerClosure
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower

/-!
# Finiteness of `Ass(gr)` — R0 discharge
This file discharges residual R0 (`SupAssFiniteGr`,
`PositiveDimTower.lean`): the associated primes of the
associated graded ring `gr_𝔪(R)` (as a module over itself) are finite.

## What this file proves

* `supAss_isNoetherianRing_gr`: for Noetherian local `R`, `gr_𝔪(R)`
  is Noetherian. Proof: `𝔪` is finitely generated
  (`Ideal.fg_of_isNoetherianRing`), the finset becomes a `Fin`-family
  (`supAss_family`), the M4b surjection `polySurj` exhibits `gr` as a
  quotient of `MvPolynomial (Fin d) (R ⧸ 𝔪)` (Noetherian by the
  Hilbert basis over the Noetherian quotient), and Noetherianity
  transfers along the surjection.
* `supAssFiniteGr_of_noetherian`: R0 at general Noetherian local `R`,
  from `associatedPrimes.finite` over the Noetherian `gr` above. This
  is the exact `hfin` input of `supTowerPosDim_of_graded` (PosDim
  :341), which already assumes `IsNoetherianRing R`: zero shape gap.
* `supAssFiniteGr_atPrime`: R0 at `R_Q`, unconditional (no hypotheses
  beyond `Q` prime; the `IsNoetherianRing` instance is the proved
  `isNoetherianRing_atPrime`).
* `supTowerPosDim_of_noetherian`: T1:341 with R0 discharged (residual
  `[R1, R2]`).
* `hChiReduceAtAss_of_gradedInputs`: T1:559 with R0 discharged
  (residual per-`Q` `[R1, R2, R3]` + pins + infinite residue fields).

## Status

* All theorems: unconditional (the general ones take the ambient
  `IsNoetherianRing R` that:341 already assumes; the `R_Q` corollary
  takes no hypotheses beyond `Q` prime).
* Overall: R0 closed. No residual hypotheses remain for R0.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only and
grep-verified present (no absence claims made):
* `RingTheory/Ideal/AssociatedPrime/Finiteness.lean`
  (`associatedPrimes.finite`).
* `RingTheory/Noetherian/Basic.lean`
  (`isNoetherianRing_of_surjective`).
* `RingTheory/Noetherian/Defs.lean`
  (`Ideal.fg_of_isNoetherianRing`).
* `RingTheory/Polynomial/Basic.lean`
  (`MvPolynomial.isNoetherianRing` instance).
* `RingTheory/Ideal/Quotient/Noetherian.lean`
  (`Ideal.Quotient.isNoetherianRing` instance).
* `RingTheory/Finiteness/Basic.lean`
  (`Module.Finite.self` instance).
* `Data/Fintype/EquivFin.lean` (`Finset.equivFin`).

Project (read-only):
* `Regularity/HomologicalDepth/PositiveDimTower.lean` (`SupAssFiniteGr`:253,
  `supTowerPosDim_of_graded`:341,
  `hChiReduceAtAss_posDim_of_tower`:559).
* `Regularity/Koszul/GradedSurjection.lean` (`polySurj`:175,
  `polySurj_surjective`:313).
* `Regularity/Koszul/FiltrationStability.lean` (`isNoetherianRing_atPrime`:305).
* `Regularity/Koszul/GradedLift.lean` (`grlift_family`:140,
  `grlift_family_range`:144: the finset-to-family pattern copied here
  as `supAss_family` to keep this file dependency-light).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AssOfGradedFinite

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FiltrationStability
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower

/-- A finset as a `Fin`-family (the `polySurj` input shape). Copies the
proved `grlift_family` pattern so this file stays dependency-light.
-/
noncomputable def supAss_family {R : Type*} (s : Finset R) : Fin s.card → R :=
  fun i => ↑(s.equivFin.symm i)

#print axioms supAss_family

/-- The family hits exactly the finset.
-/
theorem supAss_family_range {R : Type*} (s : Finset R) :
    Set.range (supAss_family s) = ↑s := by
  ext x
  simp only [supAss_family, Set.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    exact ⟨s.equivFin ⟨x, hx⟩,
      congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨x, hx⟩)⟩

#print axioms supAss_family_range

/-- `gr` over the maximal ideal of a Noetherian local ring is
Noetherian: the M4b surjection exhibits it as a quotient of the
Noetherian polynomial ring over `R ⧸ 𝔪`.
-/
theorem supAss_isNoetherianRing_gr {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    IsNoetherianRing (associatedGraded R (IsLocalRing.maximalIdeal R)) := by
  obtain ⟨S, hS⟩ := Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R)
  have hgen : Ideal.span (Set.range (supAss_family S)) =
      IsLocalRing.maximalIdeal R := by
    rw [supAss_family_range]
    exact hS
  have : IsNoetherianRing (MvPolynomial (Fin S.card)
      (R ⧸ IsLocalRing.maximalIdeal R)) := inferInstance
  exact isNoetherianRing_of_surjective _ _
    (polySurj R (IsLocalRing.maximalIdeal R) S.card (supAss_family S) hgen)
    (polySurj_surjective R (IsLocalRing.maximalIdeal R) S.card
      (supAss_family S) hgen)

#print axioms supAss_isNoetherianRing_gr

/-- R0 at general Noetherian local `R`: `Ass(gr_𝔪(R))` is finite. The
exact `hfin` input of `supTowerPosDim_of_graded` (PosDim:341).
-/
theorem supAssFiniteGr_of_noetherian {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : SupAssFiniteGr (R := R) := by
  have hNoeth : IsNoetherianRing (associatedGraded R (IsLocalRing.maximalIdeal R)) :=
    supAss_isNoetherianRing_gr (R := R)
  have hFin : @Module.Finite (associatedGraded R (IsLocalRing.maximalIdeal R))
      (associatedGraded R (IsLocalRing.maximalIdeal R))
      (@CommSemiring.toSemiring
        (associatedGraded R (IsLocalRing.maximalIdeal R))
        (@CommRing.toCommSemiring
          (associatedGraded R (IsLocalRing.maximalIdeal R))
          (instCommRing R (IsLocalRing.maximalIdeal R))))
      (@Semiring.toAddCommMonoid
        (associatedGraded R (IsLocalRing.maximalIdeal R))
        (@CommSemiring.toSemiring
          (associatedGraded R (IsLocalRing.maximalIdeal R))
          (@CommRing.toCommSemiring
            (associatedGraded R (IsLocalRing.maximalIdeal R))
            (instCommRing R (IsLocalRing.maximalIdeal R)))))
      (@Semiring.toModule (associatedGraded R (IsLocalRing.maximalIdeal R))
        (@CommSemiring.toSemiring
          (associatedGraded R (IsLocalRing.maximalIdeal R))
          (@CommRing.toCommSemiring
            (associatedGraded R (IsLocalRing.maximalIdeal R))
            (instCommRing R (IsLocalRing.maximalIdeal R))))) :=
    Module.Finite.self (associatedGraded R (IsLocalRing.maximalIdeal R))
  exact @associatedPrimes.finite
    (associatedGraded R (IsLocalRing.maximalIdeal R))
    (instCommRing R (IsLocalRing.maximalIdeal R))
    (associatedGraded R (IsLocalRing.maximalIdeal R))
    (@Ring.toAddCommGroup (associatedGraded R (IsLocalRing.maximalIdeal R))
      (@CommRing.toRing (associatedGraded R (IsLocalRing.maximalIdeal R))
        (instCommRing R (IsLocalRing.maximalIdeal R))))
    (@Semiring.toModule (associatedGraded R (IsLocalRing.maximalIdeal R))
      (@CommSemiring.toSemiring
        (associatedGraded R (IsLocalRing.maximalIdeal R))
        (@CommRing.toCommSemiring
          (associatedGraded R (IsLocalRing.maximalIdeal R))
          (instCommRing R (IsLocalRing.maximalIdeal R)))))
    hNoeth
    hFin

#print axioms supAssFiniteGr_of_noetherian

/-- R0 at `R_Q`, unconditional: no hypotheses beyond `Q` prime. Feeds
the per-`Q` tower construction behind `hChiReduceAtAss_posDim_of_tower`
(PosDim:559).
-/
theorem supAssFiniteGr_atPrime (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    SupAssFiniteGr (R := Localization.AtPrime Q) := by
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    isNoetherianRing_atPrime Q
  exact supAssFiniteGr_of_noetherian

#print axioms supAssFiniteGr_atPrime

/-- T1:341 with R0 discharged: the reshaped tower from graded
avoidance (R1) and transfer (R2) alone.

Conditional on exactly `[SupJointHomAvoid, SupColonOfGrAvoid]`. -/
theorem supTowerPosDim_of_noetherian {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (havoid : SupJointHomAvoid (R := R))
    (htrans : SupColonOfGrAvoid (R := R)) :
    SupTowerPosDim (R := R) :=
  supTowerPosDim_of_graded hInf supAssFiniteGr_of_noetherian havoid htrans

#print axioms supTowerPosDim_of_noetherian

/-- T1:559 with R0 discharged: the H5 conclusion from per-`Q` pins,
infinite residue fields, graded avoidance (R1), transfer (R2), and
exact drop (R3).

Conditional on exactly per-`Q`
`[SupJointHomAvoid, SupColonOfGrAvoid, SupExactDimDrop]`. -/
theorem hChiReduceAtAss_of_gradedInputs (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hinput : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
            = ((((dimN : ℕ)) : ℕ∞) : WithBot ℕ∞) ∧
          Infinite (Localization.AtPrime Q ⧸
            IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
          SupJointHomAvoid (R := Localization.AtPrime Q) ∧
          SupColonOfGrAvoid (R := Localization.AtPrime Q) ∧
          SupExactDimDrop (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_posDim_of_tower m K J
  intro Q _ hQ
  obtain ⟨dimN, hpin, hInf, havoid, htrans, hexact⟩ := hinput Q hQ
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    isNoetherianRing_atPrime Q
  exact ⟨dimN, hpin,
    supTowerPosDim_of_graded hInf supAssFiniteGr_of_noetherian havoid htrans,
    hexact⟩

#print axioms hChiReduceAtAss_of_gradedInputs

end AssOfGradedFinite
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
