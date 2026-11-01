/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.CruxNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoEndToEnd
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelMain
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelCrux
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# G1: `Ge3` attack — the `d ≥ 3` slice of High + uniform `Ge2` joints

Attack on the `Ge3` conjunct (`HnoHomRelHighMinGe3AtAss`,
`WitnessHighAttack.lean`) — the `d ≥ 3` slice of High that the `d = 2`
lanes deliberately exclude — plus uniform-joint corollaries composing
`Ge3` with the `d = 2` slice as an explicit SPEC shim.

## Attack verdict (machine-checked, §§1–4)

`Ge3` is ring-strength within its own slice: every `d ≥ 3` residual is
exactly `Ge3`-kernel strength (the §3 `Ge3` ring, all iffs
unconditional), so no proof of `Ge3` exists below the strength of any
single `Ge3` slice. The scope inversion is legitimate but does not
close the slice: `d ≥ 3` banks strictly more unconditional base (§1)
yet the slice itself stays conditional with an exact single-slice
remainder. The uniform `Ge2` remainder factors exactly as
`D2-shim ∧ Ge3` (§4): any future `d = 2` proof plus any future `Ge3`
proof close every crux form by one `exact`.

* (§1) Uniform low-Hilbert base: `HighAttack` §1 generalized from `d = 2`
  to general `d` (`Hq(0) = 1`, `Hq(1) = d` from minimality alone,
  conditional-form on `[hmin]`), with `Ge3` instances. Strict
  generalization (new shapes); the `d = 2` values are instances.
* (§2) `Ge3`-slice SPECs for all nine crux forms plus the general
  s.o.p.-to-gr residual (10 new Prop addresses, same bodies, gate
  `3 ≤ d` / `3 ≤ embdim`).
* (§3) The `Ge3` ring: `Ge3`-High is iff-linked to every `Ge3` slice
  (11 unconditional iffs via uniform per-triple exactness), plus the
  one-shot 10-tuple slices-joint on `[hge3]`. Answers which crux form
  `Ge3` implies (every `Ge3` slice) and needs (any single one).
* (§4) Uniform joints with the `d = 2` SPEC shim (`HnoHomRelHighD2AtAss`,
  the adjacent `HighAttack` §2 SPEC): the 9-tuple and all nine
  per-form corollaries on `[hd2, hge3]`; shim variants on `[hkerD2]` /
  `[hwitD2]` / gated residual / HS inputs; uniform-to-`Ge3` bridges
  (every uniform crux form restricts to `Ge3`).
* (§5, doc-only) Residual register + attack log.

## Scope coordination (no duplication)

* `WitnessHighAttack.lean` §§2–3: owns the D2/Ge3 SPECs, the
  split, the joint. Consumed only (shim shapes + composition).
* `DimTwoEndToEnd.lean` §§1–4: owns the gated residuals, the
  unconditional s.o.p. discharge, the gated/HS joints. Consumed
  only (the §4 joint-9 lifts compose them; no restatement).
* `CruxNarrowing.lean` §§1–2: owns the narrowing joint + `d`-split.
  consumed only.
* `WitnessKernelMain.lean` §1: owns the uniform crux-ring iffs. Consumed
  only (uniform-to-`Ge3` bridges).
* `HighHomogeneousRelations.lean` §§1–2/10: owns `Low`/pair exactness/the
  Witness bridge. Consumed only (uniform per-triple exactness).
* This file owns: the §1 uniform low-Hilbert base, the §2 `Ge3`-slice
  SPECs, the §3 `Ge3` ring, the §4 uniform joints. Nothing here restates
  a proved shape: every SPEC/thm is a new `Ge3`/uniform-joint address.

## Status

* §1: `CONDITIONAL`-exact on `[hmin]` (helpers conditional-form on `Low`).
* §2: SPECs (Prop addresses).
* §3: `UNCONDITIONAL` (iffs); slices-joint `CONDITIONAL`-exact on `[hge3]`.
* §4: `CONDITIONAL`-exact on the named inputs.
* Overall: `PARTIAL` toward `Ge3` (remainder = any single `Ge3`
  slice, §5) and toward uniform High (remainder = `[d2-shim, ge3]`).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HighDimGe3Attack

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CruxNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimTwoEndToEnd
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelMain
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelCrux
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighRelationsLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. Uniform low-Hilbert base: `Hq(0) = 1`, `Hq(1) = d`

`HighAttack` §1 generalized from `d = 2` to general `d`: from
minimality alone, `Low` kills the degree-1 ker piece, the degree-0
unit chase kills the degree-0 piece, and stars-and-bars pins the
quotient values `Hq(0) = 1`, `Hq(1) = d`. At `d ≥ 3` this is the
unconditional analytic base the `Ge3` attack stands on. -/

/-- `ker ≠ ⊤` from `Low` at general `d`: `X 0` is a linear form outside
`ker` (needs `1 ≤ d`), so `ker` is proper. General-`d` form of
`highAttack_ker_ne_top_of_low`.
-/
theorem highGe3_ker_ne_top_of_low {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : 1 ≤ d)
    (hlow : KwitNoHomRelLow Q d g hgen) :
    RingHom.ker (polySurjResidue Q d g hgen) ≠ ⊤ := by
  intro htop
  have hmem : MvPolynomial.X (⟨0, hd⟩ : Fin d) ∈
      RingHom.ker (polySurjResidue Q d g hgen) := by
    rw [htop]
    exact Submodule.mem_top
  have h0 := hlow _ hmem (MvPolynomial.isHomogeneous_X _ _)
  exact MvPolynomial.X_ne_zero _ h0

/-- The degree-0 ker piece vanishes given `Low` at general `d`:
general-`d` form of `highAttack_kerPiece_zero_eq_bot`.
-/
theorem highGe3_kerPiece_zero_eq_bot {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : 1 ≤ d)
    (hlow : KwitNoHomRelLow Q d g hgen) :
    multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) 0 = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hmem : y.val ∈ RingHom.ker (polySurjResidue Q d g hgen) := by
    unfold multKerPiece at hy
    rwa [Submodule.mem_comap, Submodule.restrictScalars_mem] at hy
  have hhom : y.val.IsHomogeneous 0 :=
    (MvPolynomial.mem_homogeneousSubmodule 0 y.val).mp y.2
  have htd : y.val.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin d)).mpr hhom
  have hcC : y.val = MvPolynomial.C (y.val.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
  by_cases hc0 : y.val.coeff 0 = 0
  · have hval : y.val = 0 := by rw [hcC, hc0, map_zero]
    exact Subtype.ext_iff.mpr hval
  · exfalso
    have hunit : IsUnit y.val := by
      rw [hcC]
      exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hc0)
    have htop : RingHom.ker (polySurjResidue Q d g hgen) = ⊤ :=
      (RingHom.ker (polySurjResidue Q d g hgen)).eq_top_of_isUnit_mem
        hmem hunit
    exact highGe3_ker_ne_top_of_low Q d g hgen hd hlow htop

/-- The degree-1 ker piece vanishes given `Low` at general `d`:
general-`d` form of `highAttack_kerPiece_one_eq_bot`.
-/
theorem highGe3_kerPiece_one_eq_bot {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hlow : KwitNoHomRelLow Q d g hgen) :
    multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) 1 = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hmem : y.val ∈ RingHom.ker (polySurjResidue Q d g hgen) := by
    unfold multKerPiece at hy
    rwa [Submodule.mem_comap, Submodule.restrictScalars_mem] at hy
  have hhom : y.val.IsHomogeneous 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 y.val).mp y.2
  have hval : y.val = 0 := hlow y.val hmem hhom
  exact Subtype.ext_iff.mpr hval

/-- `Hq(0) = 1` at general `d` from minimality: the degree-0 ker piece
is `⊥`, so the quotient piece is the full constants
(stars-and-bars `choose (d-1) (d-1)`).

Conditional on exactly `[hmin]`. -/
theorem highGe3_quotHilbert_zero_eq_one {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : 1 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) 0 = 1 := by
  have hlow := kwitHigh_low_of_minimal Q d g hgen hmin
  have hP0 := highGe3_kerPiece_zero_eq_bot Q d g hgen hd hlow
  have hEq : multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q))
      d (RingHom.ker (polySurjResidue Q d g hgen)) 0 =
      hsAssemble_domainHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) d 0 := by
    unfold multQuotHilbert hsAssemble_domainHilbert
    exact mult_finLength_eq_of_linearEquiv
      ((multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
        (RingHom.ker (polySurjResidue Q d g hgen)) 0).quotEquivOfEqBot hP0)
  rw [hEq]
  have hSB := hsAssemble_domainHilbert_eq_choose
    (IsLocalRing.ResidueField (Localization.AtPrime Q)) d hd 0
  rw [hSB]
  have htop : 0 + d - 1 = d - 1 := by omega
  rw [htop]
  exact Nat.choose_self _

/-- `Hq(1) = d` at general `d` from minimality: the degree-1 ker piece
is `⊥`, so the quotient piece is the full linear forms
(stars-and-bars `choose d (d-1)`).

Conditional on exactly `[hmin]`. -/
theorem highGe3_quotHilbert_one_eq {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : 1 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) 1 = d := by
  have hlow := kwitHigh_low_of_minimal Q d g hgen hmin
  have hP1 := highGe3_kerPiece_one_eq_bot Q d g hgen hlow
  have hEq : multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q))
      d (RingHom.ker (polySurjResidue Q d g hgen)) 1 =
      hsAssemble_domainHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) d 1 := by
    unfold multQuotHilbert hsAssemble_domainHilbert
    exact mult_finLength_eq_of_linearEquiv
      ((multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
        (RingHom.ker (polySurjResidue Q d g hgen)) 1).quotEquivOfEqBot hP1)
  rw [hEq]
  have hSB := hsAssemble_domainHilbert_eq_choose
    (IsLocalRing.ResidueField (Localization.AtPrime Q)) d hd 1
  rw [hSB]
  have htop : 1 + d - 1 = d := by omega
  rw [htop]
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hsub : d' + 1 - 1 = d' := by omega
  rw [hsub]
  exact Nat.choose_succ_self_right d'

/-- `Hq(0) = 1` at `d ≥ 3` from minimality (`Ge3` instance).

Conditional on exactly `[hmin]`. -/
theorem highGe3_quotHilbert_zero_eq_one_ge3 {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd3 : 3 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) 0 = 1 :=
  highGe3_quotHilbert_zero_eq_one Q d g hgen (by omega) hmin

/-- `Hq(1) = d` at `d ≥ 3` from minimality (`Ge3` instance).

Conditional on exactly `[hmin]`. -/
theorem highGe3_quotHilbert_one_eq_ge3 {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd3 : 3 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) 1 = d :=
  highGe3_quotHilbert_one_eq Q d g hgen (by omega) hmin

#print axioms highGe3_ker_ne_top_of_low
#print axioms highGe3_kerPiece_zero_eq_bot
#print axioms highGe3_kerPiece_one_eq_bot
#print axioms highGe3_quotHilbert_zero_eq_one
#print axioms highGe3_quotHilbert_one_eq
#print axioms highGe3_quotHilbert_zero_eq_one_ge3
#print axioms highGe3_quotHilbert_one_eq_ge3

/-! ## §2. `Ge3`-slice SPECs for the crux ring + the general residual

The `d ≥ 3` slices of all nine crux forms (same bodies as the uniform
SPECs, gate `3 ≤ d` / `3 ≤ embdim`), plus the `Ge3` slice of the
general s.o.p.-to-gr residual. The `Ge3`-High slice itself is
`HnoHomRelHighMinGe3AtAss` (`HighAttack` §3, consumed). -/

/-- `ker = ⊥` at minimal `d ≥ 3`: the `Ge3` slice of `HkerMinAtAss`.

Specification (Prop address for the `Ge3` kernel hypothesis). -/
def HkerMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      3 ≤ d → RingHom.ker (polySurjResidue Q d g hgen) = ⊥

/-- `dim gr = d` at minimal `d ≥ 3`: the `Ge3` slice of
`HdimGrMinAtAss`.

Specification (Prop address for the `Ge3` gr-dimension hypothesis). -/
def HdimGrMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      3 ≤ d → ringKrullDim (grRegular Q) = d

/-- Minimal `hle` at `d ≥ 3`: the `Ge3` slice of `HhleMinAtAss`.

Specification (Prop address for the `Ge3` `hle` hypothesis). -/
def HhleMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (_hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      3 ≤ d → d ≤ ringKrullDim (grRegular Q)

/-- R1's lower bound at embdim `≥ 3`: the `Ge3` slice of
`HgrDimLowerMinAtAss` (per-`Q` shape, gate on embdim).

Specification (Prop address for the `Ge3` lower-bound hypothesis). -/
def HgrDimLowerMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    3 ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q)

/-- `dim gr = embdim` at embdim `≥ 3`: the `Ge3` slice of
`HgrDimEqMinAtAss` (per-`Q` shape, gate on embdim).

Specification (Prop address for the `Ge3` gr-equality hypothesis). -/
def HgrDimEqMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    3 ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
    ringKrullDim (grRegular Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank

/-- Witness data at minimal `d ≥ 3`: the `Ge3` slice of `HwitMinAtAss`
(exact `mult_hle_gr_of_witnessHyp` shape, gate `3 ≤ d`).

Specification (Prop address for the `Ge3` witness hypothesis). -/
def HwitMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
    3 ≤ d →
      ∃ (g : Fin d → Localization.AtPrime Q),
        ∃ (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
          ∃ (H : ℕ → ℕ),
            IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1) ∧
            (∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
              (fun n => ((multQuotHilbert
                (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
                (RingHom.ker (polySurjResidue Q d g hgen))
                (n + 1) : ℕ) : ℚ))
                =ᶠ[Filter.atTop] evalFun Pwit ∧
              Pwit.coeff (d - 1) ≠ 0) ∧
            (RingHom.ker (polySurjResidue Q d g hgen) ≠ ⊥ →
              ∃ Jloc : Ideal (Localization.AtPrime Q),
                (∀ Qm ∈ Jloc.minimalPrimes,
                  Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
                (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
                  (Localization.AtPrime Q ⧸ Jloc),
                  ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
                (∀ n, multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
                  (RingHom.ker (polySurjResidue Q d g hgen))
                  (n + 1) + H n = H (n + 1)) ∧
                IsPolyGrowth (fun n => ((multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
                  (RingHom.ker (polySurjResidue Q d g hgen))
                  (n + 1) : ℕ) : ℚ)) (d - 1))

/-- Multiplicity-nonvanishing at minimal `d ≥ 3`: the `Ge3` slice of
`HmultMinAtAss`.

Specification (Prop address for the `Ge3` multiplicity hypothesis). -/
def HmultMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
    3 ≤ d →
      ¬ seqDiff (d - 1) (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0

/-- Exact degree at minimal `d ≥ 3`: the `Ge3` slice of
`HdimEqMinAtAss` (exact KerAssemble-hyp shape).

Specification (Prop address for the `Ge3` dim-equality hypothesis). -/
def HdimEqMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
    3 ≤ d →
      ∀ Qw : ℚ[X], Qw.natDegree ≤ d - 1 →
        (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun Qw →
        Qw.natDegree = d - 1

/-- `∃`-kernel at minimal `d ≥ 3`: the `Ge3` slice of
`HexistsKerMinAtAss`.

Specification (Prop address for the `Ge3` ∃-kernel hypothesis). -/
def HexistsKerMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      3 ≤ d →
      ∃ (g : Fin d → Localization.AtPrime Q),
        ∃ (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
          RingHom.ker (polySurjResidue Q d g hgen) = ⊥

/-- S.o.p.-to-gr residual at minimal `d ≥ 3`: the `Ge3` slice of
`HsopGrLowerMinAtAss` (gated shape, gate `3 ≤ d`).

Specification (Prop address for the `Ge3` s.o.p.-to-gr hypothesis). -/
def HsopGrLowerMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (x : Fin d → Localization.AtPrime Q)
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      (∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
      ringKrullDim
          (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0 →
      3 ≤ d → d ≤ ringKrullDim (grRegular Q)

/-! ## §3. The `Ge3` ring: every `d ≥ 3` slice is `Ge3`-kernel strength

Uniform per-triple exactness (`High ⟺ ker = ⊥` given minimality, at
general `d`) plus the §17 collapse and the gr-side masters link the
`Ge3`-High slice to every §2 slice unconditionally. -/

/-- Per-triple `ker = ⊥` from High at `d ≥ 3`: `Low` is free from
minimality, and the pair closes the kernel (uniform-`d` form of the
D2 §4 sharp exactness).
-/
theorem highGe3_ker_eq_bot_of_high_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (hd3 : 3 ≤ d)
    (hhigh : HilbertWitnessNarrowing.KwitNoHomRelHigh Q d g hgen) :
    RingHom.ker (polySurjResidue Q d g hgen) = ⊥ :=
  kwitHigh_ker_eq_bot_of_low_high Q d g hgen (by omega)
    (kwitHigh_low_of_minimal Q d g hgen (le_of_eq hdmin))
    ((kwitHigh_witness_bridge Q d g hgen).mp hhigh)

/-- Per-triple High from `ker = ⊥` at general `d` (no minimality
needed — the collapse is definitional).
-/
theorem highGe3_high_of_ker_eq_bot_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hker : RingHom.ker (polySurjResidue Q d g hgen) = ⊥) :
    HilbertWitnessNarrowing.KwitNoHomRelHigh Q d g hgen :=
  highNarrow_of_ker_eq_bot Q d g hgen hker

#print axioms highGe3_ker_eq_bot_of_high_atPrime
#print axioms highGe3_high_of_ker_eq_bot_atPrime

/-- Headline hub: `Ge3`-High is exactly `Ge3`-kernel strength.
-/
theorem highGe3_ge3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hge3 Q _ hQ d g hgen hdmin hd3
    exact highGe3_ker_eq_bot_of_high_atPrime Q d g hgen hdmin hd3
      (hge3 Q hQ g hgen hdmin hd3)
  · intro hker Q _ hQ d g hgen hdmin hd3
    exact highGe3_high_of_ker_eq_bot_atPrime Q d g hgen
      (hker Q hQ g hgen hdmin hd3)

#print axioms highGe3_ge3_iff_hkerGe3

/-- `Ge3` gr-dimension is exactly `Ge3`-kernel strength (via the §17
collapse + the unconditional upper bound).
-/
theorem highGe3_hdimGrGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimGrMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hdim Q _ hQ d g hgen hdmin hd3
    have hle : d ≤ ringKrullDim (grRegular Q) :=
      (hdim Q hQ hdmin hd3).ge
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle
  · intro hker Q _ hQ d hdmin hd3
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have hd3' : 3 ≤ d' := by omega
    have hgr := dimGr_eq_of_ker_eq_bot_atPrime Q d' g hgen
      (hker Q hQ g hgen hd' hd3')
    exact hgr.trans (by exact_mod_cast hd'.trans hdmin.symm)

#print axioms highGe3_hdimGrGe3_iff_hkerGe3

/-- `Ge3` `hle` is exactly `Ge3`-kernel strength (the §17 collapse
per triple).
-/
theorem highGe3_hhleGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhleMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hhle Q _ hQ d g hgen hdmin hd3
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp
      (hhle Q hQ g hgen hdmin hd3)
  · intro hker Q _ hQ d g hgen hdmin hd3
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mpr
      (hker Q hQ g hgen hdmin hd3)

#print axioms highGe3_hhleGe3_iff_hkerGe3

/-- `Ge3` lower bound is exactly `Ge3`-kernel strength (forward via
`dim R_Q = d`; backward via the workhorse at the minimal family).
-/
theorem highGe3_lowerGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimLowerMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hlo Q _ hQ d g hgen hdmin hd3
    have hem3 : 3 ≤ (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank := by omega
    have hloQ := hlo Q hQ hem3
    have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen
      (le_of_eq hdmin)
    have hle : d ≤ ringKrullDim (grRegular Q) := hR ▸ hloQ
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle
  · intro hker Q _ hQ hem3
    obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
    have hd3 : 3 ≤ d := by omega
    have hle := mult_hle_gr_of_ker_eq_bot Q d g hgen
      (hker Q hQ g hgen hd hd3)
    have hgr := mult_dim_gr_eq_of_gr_lowerBound Q d g hgen hle
    have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen
      (le_of_eq hd)
    exact le_trans hR.le hgr.ge

#print axioms highGe3_lowerGe3_iff_hkerGe3

/-- `Ge3` gr-equality is exactly `Ge3`-kernel strength.
-/
theorem highGe3_grDimEqGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimEqMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hgr Q _ hQ d g hgen hdmin hd3
    have hem3 : 3 ≤ (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank := by omega
    have he := hgr Q hQ hem3
    have hle : d ≤ ringKrullDim (grRegular Q) := by
      rw [he]
      exact_mod_cast hdmin.le
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle
  · intro hker Q _ hQ hem3
    obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
    have hd3 : 3 ≤ d := by omega
    have hgr := dimGr_eq_of_ker_eq_bot_atPrime Q d g hgen
      (hker Q hQ g hgen hd hd3)
    exact hgr.trans (by exact_mod_cast hd)

#print axioms highGe3_grDimEqGe3_iff_hkerGe3

/-- `Ge3` witness data is exactly `Ge3`-kernel strength (forward via
the §17 narrowing; backward via domain theory with `H := 0`).
-/
theorem highGe3_hwitGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HwitMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hwit Q _ hQ d g hgen hdmin hd3
    obtain ⟨g', hgen', H, hF, hwitQ, hdrop⟩ := hwit Q hQ hdmin hd3
    have hle : d ≤ ringKrullDim (grRegular Q) :=
      mult_hle_gr_of_witnessHyp Q d g' hgen' H (by omega) hF hwitQ hdrop
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle
  · intro hker Q _ hQ d hdmin hd3
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have heq : d = d' := hdmin.trans hd'.symm
    subst heq
    have hkerQ : RingHom.ker (polySurjResidue Q d g hgen) = ⊥ :=
      hker Q hQ g hgen hd' hd3
    refine ⟨g, hgen, (fun _ => 0), ?hF, ?hwit, ?hdrop⟩
    · exact ⟨0, by simp,
        Filter.Eventually.of_forall (fun n => by simp [evalFun])⟩
    · exact HilbertWitnessNarrowing.kwit_hwit_of_hmult Q d g hgen (by omega)
        (HilbertWitnessNarrowing.kwit_hmult_of_ker_eq_bot Q d g hgen (by omega)
          hkerQ)
    · intro hne
      exact absurd hkerQ hne

#print axioms highGe3_hwitGe3_iff_hkerGe3

/-- `Ge3` multiplicity is exactly `Ge3` exact-degree strength (both
via the unconditional gr-side growth bound).
-/
theorem highGe3_hmultGe3_iff_hdimEqGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HmultMinGe3AtAss m K J ↔ HdimEqMinGe3AtAss m K J := by
  constructor
  · intro hmult Q _ hQ d hdmin hd3 Qw hle hag
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have heq : d' = d := hd'.trans hdmin.symm
    have hF : IsPolyGrowth (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        (d - 1) := by
      have hF' := singleDrop_grHilbert_isPolyGrowth m K Q d' g hgen
      rwa [heq] at hF'
    exact hsAssemble_hdimEq_of_not_vanishing hF
      (hmult Q hQ hdmin hd3) Qw hle hag
  · intro hdimEq Q _ hQ d hdmin hd3
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have heq : d' = d := hd'.trans hdmin.symm
    have hF : IsPolyGrowth (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        (d - 1) := by
      have hF' := singleDrop_grHilbert_isPolyGrowth m K Q d' g hgen
      rwa [heq] at hF'
    exact hsAssemble_not_vanishing_of_hdimEq (by omega : 0 < d - 1) hF
      (hdimEq Q hQ hdmin hd3)

#print axioms highGe3_hmultGe3_iff_hdimEqGe3

/-- `Ge3` exact-degree is exactly `Ge3`-kernel strength (forward via
KerAssemble; backward via the gr-side exact-degree master).
-/
theorem highGe3_hdimEqGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hdimEq Q _ hQ d g hgen hdmin hd3
    exact ker_assemble_ker_eq_bot Q d g hgen (by omega)
      (hdimEq Q hQ hdmin hd3)
  · intro hker Q _ hQ d hdmin hd3
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have heq : d = d' := hdmin.trans hd'.symm
    subst heq
    have hgr := dimGr_eq_of_ker_eq_bot_atPrime Q d g hgen
      (hker Q hQ g hgen hd' hd3)
    exact dimToMult_grHdimEq_of_gr_dim_eq Q d g hgen (by omega) hgr

#print axioms highGe3_hdimEqGe3_iff_hkerGe3

/-- `Ge3` multiplicity is exactly `Ge3`-kernel strength (via exact
degree).
-/
theorem highGe3_hmultGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HmultMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J :=
  (highGe3_hmultGe3_iff_hdimEqGe3 m K J).trans
    (highGe3_hdimEqGe3_iff_hkerGe3 m K J)

#print axioms highGe3_hmultGe3_iff_hkerGe3

/-- `Ge3` ∃-kernel is exactly `Ge3`-kernel strength (forward via `hle`
at the witnessed family; backward is the family itself).
-/
theorem highGe3_hexistsGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HexistsKerMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hex Q _ hQ d g hgen hdmin hd3
    obtain ⟨g', hgen', hker'⟩ := hex Q hQ hdmin hd3
    have hle : d ≤ ringKrullDim (grRegular Q) :=
      mult_hle_gr_of_ker_eq_bot Q d g' hgen' hker'
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle
  · intro hker Q _ hQ d hdmin hd3
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have heq : d = d' := hdmin.trans hd'.symm
    subst heq
    exact ⟨g, hgen, hker Q hQ g hgen hd' hd3⟩

#print axioms highGe3_hexistsGe3_iff_hkerGe3

/-- The `Ge3` s.o.p.-to-gr residual is exactly `Ge3`-kernel strength:
it joins the `Ge3` ring (forward via the unconditional §1 s.o.p.;
backward via the minimal family).
-/
theorem highGe3_sopGrLowerGe3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HsopGrLowerMinGe3AtAss m K J ↔ HkerMinGe3AtAss m K J := by
  constructor
  · intro hgr Q _ hQ d g hgen hdmin hd3
    obtain ⟨x, hmem, hdim0⟩ :=
      highD2Close_hsopMin_unconditional m K J Q hQ hdmin
    have hle : d ≤ ringKrullDim (grRegular Q) :=
      hgr Q hQ x hdmin hmem hdim0 hd3
    exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle
  · intro hker Q _ hQ d x hdmin _ _ hd3
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have hd3' : 3 ≤ d' := by omega
    have hle : d' ≤ ringKrullDim (grRegular Q) :=
      mult_hle_gr_of_ker_eq_bot Q d' g hgen
        (hker Q hQ g hgen hd' hd3')
    have heq : d = d' := hdmin.trans hd'.symm
    exact heq ▸ hle

#print axioms highGe3_sopGrLowerGe3_iff_hkerGe3

/-- One-shot `Ge3` slices discharge on `[hge3]`: all ten `d ≥ 3`
forms in one tuple (the nine crux slices + the s.o.p.-to-gr slice).

Conditional on exactly `[hge3]`. -/
theorem highGe3_slices_of_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HkerMinGe3AtAss m K J ∧ HdimGrMinGe3AtAss m K J ∧
      HhleMinGe3AtAss m K J ∧ HgrDimLowerMinGe3AtAss m K J ∧
      HgrDimEqMinGe3AtAss m K J ∧ HwitMinGe3AtAss m K J ∧
      HmultMinGe3AtAss m K J ∧ HdimEqMinGe3AtAss m K J ∧
      HexistsKerMinGe3AtAss m K J ∧ HsopGrLowerMinGe3AtAss m K J := by
  have hker := (highGe3_ge3_iff_hkerGe3 m K J).mp hge3
  refine ⟨hker, (highGe3_hdimGrGe3_iff_hkerGe3 m K J).mpr hker,
    (highGe3_hhleGe3_iff_hkerGe3 m K J).mpr hker,
    (highGe3_lowerGe3_iff_hkerGe3 m K J).mpr hker,
    (highGe3_grDimEqGe3_iff_hkerGe3 m K J).mpr hker,
    (highGe3_hwitGe3_iff_hkerGe3 m K J).mpr hker,
    (highGe3_hmultGe3_iff_hkerGe3 m K J).mpr hker,
    (highGe3_hdimEqGe3_iff_hkerGe3 m K J).mpr hker,
    (highGe3_hexistsGe3_iff_hkerGe3 m K J).mpr hker, ?_⟩
  exact (highGe3_sopGrLowerGe3_iff_hkerGe3 m K J).mpr hker

#print axioms highGe3_slices_of_ge3

/-! ## §4. Uniform joints: `d = 2` shim + `Ge3`, shim variants, bridges

The uniform `Ge2` remainder closes on `[d2-shim, ge3]`; the shim
comes in every stated `d = 2` shape (High SPEC, ker, witness,
gated residual, HS inputs). Conversely every uniform crux form
restricts to `Ge3`. -/

/-- End-to-end uniform 9-tuple on `[hd2, hge3]`: the joint
feeds the narrowed joint.

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_joint9_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J :=
  highNarrow_joint_of_hHigh m K J
    (highAttack_full_of_d2_ge3 m K J hd2 hge3)

#print axioms highGe3_joint9_of_d2_ge3

/-- `HwitMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hwitMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HwitMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).1

#print axioms highGe3_hwitMin_of_d2_ge3

/-- `HkerMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hkerMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HkerMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.1

#print axioms highGe3_hkerMin_of_d2_ge3

/-- `HgrDimLowerMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hlowerMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HgrDimLowerMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.2.1

#print axioms highGe3_hlowerMin_of_d2_ge3

/-- `HhleMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hhleMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HhleMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.2.2.1

#print axioms highGe3_hhleMin_of_d2_ge3

/-- `HdimEqMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hdimEqMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.2.2.2.1

#print axioms highGe3_hdimEqMin_of_d2_ge3

/-- `HmultMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hmultMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HmultMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.2.2.2.2.1

#print axioms highGe3_hmultMin_of_d2_ge3

/-- `HgrDimEqMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hgrDimEqMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HgrDimEqMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.2.2.2.2.2.1

#print axioms highGe3_hgrDimEqMin_of_d2_ge3

/-- `HdimGrMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hdimGrMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimGrMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.2.2.2.2.2.2.1

#print axioms highGe3_hdimGrMin_of_d2_ge3

/-- `HexistsKerMinAtAss` from `[hd2, hge3]` (uniform-joint projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem highGe3_hexistsMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HexistsKerMinAtAss m K J :=
  (highGe3_joint9_of_d2_ge3 m K J hd2 hge3).2.2.2.2.2.2.2.2

#print axioms highGe3_hexistsMin_of_d2_ge3

/-- Full High from `[hkerD2, hge3]`: the joint with the `d = 2`
slice on the ker-shim (via the D2 hub iff).

Conditional on exactly `[hkerD2, hge3]`. -/
theorem highGe3_fullHigh_of_hkerD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hkerD2 : HkerD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highAttack_full_of_d2_ge3 m K J
    (highAttack_highD2_of_hkerD2 m K J hkerD2) hge3

#print axioms highGe3_fullHigh_of_hkerD2_ge3

/-- End-to-end uniform 9-tuple on `[hkerD2, hge3]`.

Conditional on exactly `[hkerD2, hge3]`. -/
theorem highGe3_joint9_of_hkerD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hkerD2 : HkerD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J :=
  highNarrow_joint_of_hHigh m K J
    (highGe3_fullHigh_of_hkerD2_ge3 m K J hkerD2 hge3)

#print axioms highGe3_joint9_of_hkerD2_ge3

/-- Full High from `[hwitD2, hge3]`: the joint with the `d = 2`
slice on the witness-shim (via the D2 ring + hub iff).

Conditional on exactly `[hwitD2, hge3]`. -/
theorem highGe3_fullHigh_of_hwitD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwitD2 : HwitD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highAttack_full_of_d2_ge3 m K J
    (highAttack_highD2_of_hkerD2 m K J
      ((hwitD2_iff_hkerD2 m K J).mp hwitD2)) hge3

#print axioms highGe3_fullHigh_of_hwitD2_ge3

/-- End-to-end uniform 9-tuple on `[hwitD2, hge3]`.

Conditional on exactly `[hwitD2, hge3]`. -/
theorem highGe3_joint9_of_hwitD2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwitD2 : HwitD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J :=
  highNarrow_joint_of_hHigh m K J
    (highGe3_fullHigh_of_hwitD2_ge3 m K J hwitD2 hge3)

#print axioms highGe3_joint9_of_hwitD2_ge3

/-- End-to-end uniform 9-tuple on `[gated residual, ge3]` (the D2Close
§3 joint feeds the narrowed joint).

Conditional on exactly `[hgr, hge3]`. -/
theorem highGe3_joint9_of_sopGrLowerGated_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J :=
  highNarrow_joint_of_hHigh m K J
    (highD2Close_fullHigh_of_sopGrLowerGated_ge3 m K J hgr hge3)

#print axioms highGe3_joint9_of_sopGrLowerGated_ge3

/-- End-to-end uniform 9-tuple on `[HgrExact, HhsDeg, ge3]` (the D2Close
§4 joint feeds the narrowed joint).

Conditional on exactly `[hgrExact, hhsDeg, hge3]`. -/
theorem highGe3_joint9_of_grExact_hsDeg_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hhsDeg : HhsDegLowerD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J :=
  highNarrow_joint_of_hHigh m K J
    (highD2Close_fullHigh_of_grExact_hsDeg_ge3 m K J hgrExact hhsDeg
      hge3)

#print axioms highGe3_joint9_of_grExact_hsDeg_ge3

/-- `Ge3` from uniform `HkerMinAtAss` (via the crux ring + restriction):
every uniform crux proof discharges `Ge3`.

Conditional on exactly `[hker]`. -/
theorem highGe3_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerMinAtAss m K J) :
    HnoHomRelHighMinGe3AtAss m K J :=
  highAttack_ge3_of_ge2 m K J (highNarrow_ge2_of_full m K J
    ((hnoHomRelHighMin_iff_hkerMin m K J).mpr hker))

#print axioms highGe3_of_hkerMin

/-- `Ge3` from uniform `HmultMinAtAss` (via the crux ring + restriction).

Conditional on exactly `[hmult]`. -/
theorem highGe3_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultMinAtAss m K J) :
    HnoHomRelHighMinGe3AtAss m K J :=
  highAttack_ge3_of_ge2 m K J (highNarrow_ge2_of_full m K J
    ((hnoHomRelHighMin_iff_hmultMin m K J).mpr hmult))

#print axioms highGe3_of_hmultMin

/-- `Ge3` from uniform `HdimEqMinAtAss` (via the crux ring + restriction).

Conditional on exactly `[hdimEq]`. -/
theorem highGe3_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : HdimEqMinAtAss m K J) :
    HnoHomRelHighMinGe3AtAss m K J :=
  highAttack_ge3_of_ge2 m K J (highNarrow_ge2_of_full m K J
    ((hnoHomRelHighMin_iff_hdimEqMin m K J).mpr hdimEq))

#print axioms highGe3_of_hdimEqMin

/-! ## §5. Residual register + attack log (doc-only)

minimal non-circular remainders (verbatim):

* `HnoHomRelHighMinGe3AtAss` (`Ge3`): per `Q ∈ Ass(R ⧸ J)` at minimal
  `d ≥ 3`, per minimal family, no nonzero homogeneous `ker` relation of
  degree `≥ 2`. Equivalently (all unconditional iffs, §3):
  `HkerMinGe3AtAss`, `HdimGrMinGe3AtAss`, `HhleMinGe3AtAss`,
  `HgrDimLowerMinGe3AtAss`, `HgrDimEqMinGe3AtAss`, `HwitMinGe3AtAss`,
  `HmultMinGe3AtAss`, `HdimEqMinGe3AtAss`, `HexistsKerMinGe3AtAss`,
  `HsopGrLowerMinGe3AtAss`. Any single `Ge3` slice closes all ten by
  one `exact` (`highGe3_slices_of_ge3`).
* Uniform High: `[HnoHomRelHighD2AtAss, HnoHomRelHighMinGe3AtAss]`
  closes every crux form by one `exact` (§4 9-tuple + projections);
  the `d = 2` shim is also available as `HkerD2AtAss`, `HwitD2AtAss`,
  `HsopGrLowerD2GatedAtAss`, or `[HgrExactD2AtAss, HhsDegLowerD2AtAss]`
  (`HdimGrD2AtAss` / `HhleD2AtAss` shims are one `exact` away via the
  D2 ring and are not restated).

why the remainders are minimal and exact (all machine-checked):

* The §3 hub iff shows `Ge3`-High is exactly `Ge3`-kernel strength;
  the nine spoke iffs + residual iff show every other `d ≥ 3` form is
  the same strength. No proof of `Ge3` exists below the strength of
  any single `Ge3` slice.
* The §4 joints show `[d2, ge3]` is exactly the uniform remainder: the
  split factors `Ge2` unconditionally, and the narrowed joint
  closes all nine crux forms on full High.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth
  fact to prove the §§1/3 masters; the only undischarged inputs are
  the slices / shims themselves.

which crux form does `Ge3` imply / need:

* `Ge3` implies exactly the ten `d ≥ 3` slices (§3 ring, one `exact`
  each) — and with any `d = 2` shim, all nine uniform crux forms (§4).
* `Ge3` needs exactly any single `d ≥ 3` slice (§3 iffs); in
  particular every uniform crux form restricts to `Ge3` (§4 bridges),
  so no uniform proof can land without discharging `Ge3`.

attack log (scope inversion survey):

* Uniform low-Hilbert base (§1): proved — `Hq(0) = 1`, `Hq(1) = d`
  from minimality alone at general `d`. Banks more unconditional base
  at `d ≥ 3` but no eventual behavior (two values), so the slice
  stays conditional — exactly as scoped for analytic items.
* Direct unconditional `Ge3`: not attempted as a claim — the §3 ring
  shows every `Ge3` form is exactly `Ge3`-kernel strength, and no
  proved lemma discharges `ker = ⊥` at `d ≥ 3` (the `d ≤ 1` closures
  do not generalize; transcendence/avoidance arguments need
  initial-form dimension theory or the HS degree theorem, both absent
  from Mathlib v4.34.0 — correctly registered as the remainder
  rather than attempted).
* `t3`-as-stated / `∀`-form / `c = 0` / ungated-residual variants: not
  retried (all settled refutations or false — see lane design note).
* D2 work: not touched except as an explicit SPEC shim in stated
  shapes (C1 owns D2; this file only consumes the shim).

consumers: the §3 iffs let any future `Ge3` proof discharge every
`d ≥ 3` residual by a single `exact`; §4 lets any `[d2, ge3]` pair
discharge every uniform crux form; the §4 bridges let any future
uniform crux proof discharge `Ge3`.
-/

end HighDimGe3Attack
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
