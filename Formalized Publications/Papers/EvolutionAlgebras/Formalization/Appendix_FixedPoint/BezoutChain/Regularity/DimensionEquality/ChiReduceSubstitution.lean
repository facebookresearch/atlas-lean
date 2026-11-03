/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssSubstitution
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.DimEqualsEmbdim
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.InfiniteResidueFields
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.AssOfGradedFinite
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.JointAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerClosure

/-!
# H5/H6 substitution: `HchiReduceAtAss` on the T1 kernel alone (T3) + PosDim route (§4)

Mechanical substitution of the proved unconditional inputs into the R23
kernel-only master (`hChiReduceAtAss_of_gradedExact`, SupColonDimDrop
:560), then firing the T3 assembly into `HdimEqMinAtAss` + allocator.
No new mathematics.

## What this file proves

* `dimPin_atAss_unconditional`: the per-`Q` dimension pin
  `∃ dimN, ringKrullDim R_Q = ↑↑dimN`, unconditional from
  `dimEmbAtAss_unconditional` (RegularDimEmb:210) with
  `dimN := spanFinrank 𝔪_Q`.
* `hChiReduceAtAss_of_t1Kernel`: verbatim `HchiReduceAtAss` (ChiDegree
  :153) on exactly `[per-Q SupT1OfGrAvoid]` (given ambient `Infinite K`):
  R0 from `supAssFiniteGr_atPrime` (:207), R1 from `supJointHomAvoid`
  (:504, the `IsNoetherianRing R_Q` instance is
  `isNoetherianRing_atPrime`), infinite residues from T2
  (`infinite_residue_atAss_of_infinite`), pins from §1.
* `hChiReduceAtAss_of_t1Kernel_algClosed`: the same under the
  ambient `IsAlgClosed K` (which supplies `Infinite K`).
* `hdimEqMinAtAss_of_t1Kernel`: fires
  `hdimEqMinAtAss_of_fullH5_subst` (HdimEqMinSubst:212) →
  verbatim `HdimEqMinAtAss` (UnmixednessAtLengthTwo:309) on `[per-Q kernel]`.
* `alloc_ge2_of_t1Kernel`: fires `alloc_ge2_of_fullH5_subst` (:226) →
  the `d ≥ 2` allocator slice on `[per-Q kernel]`.
* `hdimEqMinAtAss_of_t1Kernel_algClosed` /
  `alloc_ge2_of_t1Kernel_algClosed`: the §3 closers under the
  ambient `IsAlgClosed K`.
* §4 PosDim route on both kernels (`SupT1OfGrAvoid` + `SupDimDropLower`):
  `supTowerPosDim_atAss_of_t1Kernel` (the tower plug at `R_Q`),
  `hChiReduceAtAss_of_bothKernels` (+ `_algClosed`) via the
  master, `hdimEqMinAtAss_of_bothKernels` + `alloc_ge2_of_bothKernels`
  via T3.

## Status

conditional-exact on `[per-Q SupT1OfGrAvoid]` (§§1–3, + `Infinite K` /
`IsAlgClosed K` ambient); conditional-exact on
`[per-Q SupT1OfGrAvoid, per-Q SupDimDropLower]` (§4). No new math:
every step is a literal application, so shapes match by elaboration.

## References

Project (read-only): `ColonDimDrop.lean`
(`hChiReduceAtAss_of_gradedExact`:560, `SupT1OfGrAvoid`:378),
`AssOfGradedFinite.lean` (`supAssFiniteGr_atPrime`:207),
`JointAvoidance.lean` (`supJointHomAvoid`:504),
`DimEqualsEmbdim.lean` (`dimEmbAtAss_unconditional`:210),
`FiltrationStability.lean` (`isNoetherianRing_atPrime`:305, instance),
`MinAtAssSubstitution.lean` (`hdimEqMinAtAss_of_fullH5_subst`:212,
`alloc_ge2_of_fullH5_subst`:226), `InfiniteResidueFields.lean` (T2).
-/


namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ChiReduceSubstitution

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleAllocator
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MinAtAssSubstitution
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimEqualsEmbdim
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulResidueInfinite
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssOfGradedFinite
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonDimDrop
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerClosure

/-! ## §1. The unconditional dimension pin -/

/-- The per-`Q` dimension pin, unconditional: `dim R_Q = spanFinrank 𝔪_Q`
(RegularDimEmb:210) with `dimN := spanFinrank 𝔪_Q`; the `↑↑` vs `↑`
coercion difference closes by `simpa`.
-/
theorem dimPin_atAss_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    ∃ dimN : ℕ, ringKrullDim (Localization.AtPrime Q)
      = ((dimN : ℕ∞) : WithBot ℕ∞) :=
  ⟨(IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank, by
    simpa using dimEmbAtAss_unconditional m K J Q hQ⟩

#print axioms dimPin_atAss_unconditional

/-! ## §2. H5 on the T1 kernel alone -/

/-- Verbatim `HchiReduceAtAss` on exactly `[per-Q SupT1OfGrAvoid]`
(given ambient `Infinite K`): fires the kernel-only R23 master:560
with R0/R1/residues/pins all discharged unconditionally.

Conditional on exactly `[per-Q SupT1OfGrAvoid]`. -/
theorem hChiReduceAtAss_of_t1Kernel (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_of_gradedExact
  intro Q _ hQ
  exact ⟨infinite_residue_atAss_of_infinite m K J Q hQ,
    supAssFiniteGr_atPrime m K Q, supJointHomAvoid, hker Q hQ,
    dimPin_atAss_unconditional m K J Q hQ⟩

#print axioms hChiReduceAtAss_of_t1Kernel

/-- H5 on the kernel under the formalization hypothesis: `IsAlgClosed K`
supplies `Infinite K` (Mathlib instance).

Conditional on exactly `[per-Q SupT1OfGrAvoid]`. -/
theorem hChiReduceAtAss_of_t1Kernel_algClosed (m : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J :=
  hChiReduceAtAss_of_t1Kernel m K J hker

#print axioms hChiReduceAtAss_of_t1Kernel_algClosed

/-! ## §3. T3 assembly: `HdimEqMinAtAss` + allocator on the kernel -/

/-- The T3 firing: verbatim `HdimEqMinAtAss` (UnmixednessAtLengthTwo:309) on
`[per-Q SupT1OfGrAvoid]`, via `hdimEqMinAtAss_of_fullH5_subst` (:212).

Conditional on exactly `[per-Q SupT1OfGrAvoid]`. -/
theorem hdimEqMinAtAss_of_t1Kernel (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q)) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_of_fullH5_subst m K J
    (hChiReduceAtAss_of_t1Kernel m K J hker)

#print axioms hdimEqMinAtAss_of_t1Kernel

/-- Allocator slice on the kernel: the `d ≥ 2` piece of
`HdimEqMasterAlloc` (:180) via `alloc_ge2_of_fullH5_subst` (:226).

Conditional on exactly `[per-Q SupT1OfGrAvoid]`. -/
theorem alloc_ge2_of_t1Kernel (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q)) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  alloc_ge2_of_fullH5_subst m K J
    (hChiReduceAtAss_of_t1Kernel m K J hker)

#print axioms alloc_ge2_of_t1Kernel

/-- The T3 firing under the formalization hypothesis: `IsAlgClosed K`
supplies `Infinite K` (Mathlib instance).

Conditional on exactly `[per-Q SupT1OfGrAvoid]`. -/
theorem hdimEqMinAtAss_of_t1Kernel_algClosed (m : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q)) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_of_t1Kernel m K J hker

#print axioms hdimEqMinAtAss_of_t1Kernel_algClosed

/-- Allocator slice on the kernel under the formalization hypothesis.

Conditional on exactly `[per-Q SupT1OfGrAvoid]`. -/
theorem alloc_ge2_of_t1Kernel_algClosed (m : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q)) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  alloc_ge2_of_t1Kernel m K J hker

#print axioms alloc_ge2_of_t1Kernel_algClosed

/-! ## §4. PosDim route on both kernels (+ coverage) -/

/-- Per-`Q` reshaped tower from the plug
(`supTowerPosDim_of_graded_closed`): R0/R1/T2 discharged
unconditionally, the T1 kernel explicit.

Conditional on exactly `[SupT1OfGrAvoid at Q]`. -/
theorem supTowerPosDim_atAss_of_t1Kernel (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hker : SupT1OfGrAvoid (R := Localization.AtPrime Q)) :
    SupTowerPosDim (R := Localization.AtPrime Q) :=
  supTowerPosDim_of_graded_closed
    (infinite_residue_atAss_of_infinite m K J Q hQ)
    (supAssFiniteGr_atPrime m K Q) supJointHomAvoid hker

#print axioms supTowerPosDim_atAss_of_t1Kernel

/-- Verbatim `HchiReduceAtAss` on exactly
`[per-Q SupT1OfGrAvoid, per-Q SupDimDropLower]`: fires the
PosDim master with R0/R1/residues/pins discharged unconditionally.

Conditional on exactly
`[per-Q SupT1OfGrAvoid, per-Q SupDimDropLower]`. -/
theorem hChiReduceAtAss_of_bothKernels (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q))
    (hlow : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupDimDropLower (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_of_gradedPosDim
  intro Q _ hQ
  exact ⟨infinite_residue_atAss_of_infinite m K J Q hQ,
    supAssFiniteGr_atPrime m K Q, supJointHomAvoid, hker Q hQ,
    hlow Q hQ, dimPin_atAss_unconditional m K J Q hQ⟩

#print axioms hChiReduceAtAss_of_bothKernels

/-- Both-kernel H5 under the formalization hypothesis: `IsAlgClosed K`
supplies `Infinite K` (Mathlib instance).

Conditional on exactly
`[per-Q SupT1OfGrAvoid, per-Q SupDimDropLower]`. -/
theorem hChiReduceAtAss_of_bothKernels_algClosed (m : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q))
    (hlow : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupDimDropLower (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J :=
  hChiReduceAtAss_of_bothKernels m K J hker hlow

#print axioms hChiReduceAtAss_of_bothKernels_algClosed

/-- The T3 firing on both kernels: verbatim `HdimEqMinAtAss`
(UnmixednessAtLengthTwo:309) via `hdimEqMinAtAss_of_fullH5_subst` (:212).

Conditional on exactly
`[per-Q SupT1OfGrAvoid, per-Q SupDimDropLower]`. -/
theorem hdimEqMinAtAss_of_bothKernels (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q))
    (hlow : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupDimDropLower (R := Localization.AtPrime Q)) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_of_fullH5_subst m K J
    (hChiReduceAtAss_of_bothKernels m K J hker hlow)

#print axioms hdimEqMinAtAss_of_bothKernels

/-- Allocator slice on both kernels via `alloc_ge2_of_fullH5_subst`
(:226).

Conditional on exactly
`[per-Q SupT1OfGrAvoid, per-Q SupDimDropLower]`. -/
theorem alloc_ge2_of_bothKernels (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupT1OfGrAvoid (R := Localization.AtPrime Q))
    (hlow : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      SupDimDropLower (R := Localization.AtPrime Q)) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  alloc_ge2_of_fullH5_subst m K J
    (hChiReduceAtAss_of_bothKernels m K J hker hlow)

#print axioms alloc_ge2_of_bothKernels

end ChiReduceSubstitution
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
