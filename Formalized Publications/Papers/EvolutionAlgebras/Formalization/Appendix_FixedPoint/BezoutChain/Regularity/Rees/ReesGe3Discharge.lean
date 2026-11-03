/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesClose
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighDimGe3Attack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoEndToEnd
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.HomologyTransport
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ReducedMasters
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Rees–Ge3 discharge: rees-9′ joins the Ge3 ring
FiniteDimDischarge attack on rees-9′ (`HdimEqMinGe3AtAss`, the `d ≥ 3` slice of
`HdimEqMinAtAss` — the only surviving Rees residual; the `d = 2` Rees
slice already closed in `ReesClose.lean` §1). Two angles, per the
lane design note: through the Ge3 ring (§§1–2, via the `ReesClose` masters —
the GE3 lane covers the hub through the `HighGe3` joints, overlap is
intended hedging), and through Rees-assembly reversal (§3: which
C-condition is exactly rees-9′?).

## Verdict: partial (unconditional blocked, reversal negative with exact factorization)

* Unconditional is out of reach (the barrier): rees-9′ is
  machine-checked iff-equivalent to the Ge3 hub (`rge3_iff_ge3High`
  below + `highGe3_ge3_iff_hkerGe3`), so closing rees-9′
  unconditionally would close the entire Ge3 crux. The missing
  mathematics is the associated-graded theory of regular local rings
  (`gr(R_Q)` polynomial of Hilbert degree `embdim − 1`), which is
  absent from Mathlib v4.34.0 (no `associatedGraded` API at all) and
  far beyond one lane. No unconditional proof exists below the
  strength of any single Ge3 slice (the Ge3 ring is tight).
* Reversal answers which C-condition is exactly rees-9′: none — every
  Rees C-leg at a Ge3 prime (C1 quasi-iso, C3 `hS`/`hS0`, C4 `hdim`)
  takes `hker` as hypothesis, i.e. all three sit strictly downstream
  of `HkerMinGe3AtAss ⟺ REES-9′` (one `KerAssemble` step upstream).
  The reversal yields no independent condition; its exact
  factorization is the §3 content (each C-leg + per-prime depth fire
  on `[hge3]` alone).
* What this file proves: rees-9′ re-estimated from the `∀`-Qw Hilbert form
  to the narrowest-named Ge3 address `HexistsKerMinGe3AtAss`
  (`∃`-family kernel form — existential, no Hilbert data), all
  `ReesClose` masters + deliveries re-fired on every Ge3 spoke, and a
  one-shot Rees joint on the cheapest legs
  `[HsopGrLowerD2GatedAtAss, HexistsKerMinGe3AtAss]`.

## Contents

* (§1) Bridge `ReesClose.HdimEqMinGe3AtAss ⟺ HighGe3.HdimEqMinGe3AtAss`
  (the two SPECs are the same ∀-statement) + rees-9′ joins the Ge3
  ring: unconditional iffs to all ten spokes.
* (§2) `ReesClose` masters re-fired on alternate Ge3 legs (hub, ker,
  mult, wit, ∃-narrowest) + Rees deliveries (`hkerMin`, `hdepth`,
  general-`k` unmixedness) and a one-shot joint on the cheapest legs.
* (§3) Rees-assembly reversal: C1/C3/C4-hdim legs + per-prime
  `DepthEqDimAt` at Ge3 primes, each conditional-exact on `[hge3]`.
* (§4, doc-only) Residual register + verdict.

## Status

* §1: unconditional (iffs).
* §2: conditional-exact on `[HsopGrLowerD2GatedAtAss, <Ge3-spoke>]`.
* §3: conditional-exact on `[HdimEqMinGe3AtAss]` (rees-9′).
* Overall: partial (remainder = any single Ge3 spoke;
  narrowest named: `HexistsKerMinGe3AtAss`).

## References

Project (read-only): `Regularity/Rees/ReesClose.lean` (§1 SPEC:205,
masters:262/:280/:294, deliveries), `Regularity/Multiplicity/HighDimGe3Attack.lean`
(§2 SPECs, §3 ring:539–:781), `Regularity/Multiplicity/DimTwoEndToEnd.lean`
(gated SPEC:147), `Regularity/Multiplicity/WitnessHighAttack.lean` (hub SPEC:397),
`Regularity/Rees/ReesAssembly.lean` (C1:302, §6 main:335),
`Regularity/Koszul/HomologyTransport.lean` (C3:660/:678),
`Regularity/Multiplicity/ReducedMasters.lean` (C4-hdim:93),
`Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`:309, Min `d`-split:354,
per-prime depth:384).

-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ReesGe3Discharge

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighDimGe3Attack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimTwoEndToEnd
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ReesAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HomologyTransport
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ReducedMasters

/-! ## §1. Bridge: rees-9′ joins the Ge3 ring -/

/-- The two `Ge3` exact-degree SPECs are the same ∀-statement (same
body: `singleDrop_grHilbert` + `evalFun` + `3 ≤ d` gate).
-/
theorem rge3_bridge (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HighDimGe3Attack.HdimEqMinGe3AtAss m K J := by
  unfold ReesClose.HdimEqMinGe3AtAss HighDimGe3Attack.HdimEqMinGe3AtAss
  exact Iff.rfl

/-- Rees-9′ is exactly `Ge3`-kernel strength (via the spoke
`highGe3_hdimEqGe3_iff_hkerGe3`).
-/
theorem rge3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HkerMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans (highGe3_hdimEqGe3_iff_hkerGe3 m K J)

/-- Rees-9′ is exactly the Ge3 hub strength (hence unconditional
closure of rees-9′ would close the Ge3 crux).
-/
theorem rge3_iff_ge3High (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HnoHomRelHighMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_ge3_iff_hkerGe3 m K J).symm)

/-- Rees-9′ is exactly `Ge3`-multiplicity strength.
-/
theorem rge3_iff_hmultGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HmultMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    (highGe3_hmultGe3_iff_hdimEqGe3 m K J).symm

/-- Rees-9′ is exactly `Ge3`-witness strength.
-/
theorem rge3_iff_hwitGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HwitMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_hwitGe3_iff_hkerGe3 m K J).symm)

/-- Rees-9′ is exactly `Ge3` gr-dimension strength.
-/
theorem rge3_iff_hdimGrGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HdimGrMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_hdimGrGe3_iff_hkerGe3 m K J).symm)

/-- Rees-9′ is exactly `Ge3` `hle` strength.
-/
theorem rge3_iff_hhleGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HhleMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_hhleGe3_iff_hkerGe3 m K J).symm)

/-- Rees-9′ is exactly `Ge3` lower-bound strength.
-/
theorem rge3_iff_lowerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HgrDimLowerMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_lowerGe3_iff_hkerGe3 m K J).symm)

/-- Rees-9′ is exactly `Ge3` gr-equality strength.
-/
theorem rge3_iff_grDimEqGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HgrDimEqMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_grDimEqGe3_iff_hkerGe3 m K J).symm)

/-- Rees-9′ is exactly the `Ge3` ∃-kernel strength — the
narrowest-named Ge3 address (existential over families, no Hilbert
data).
-/
theorem rge3_iff_hexistsGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HexistsKerMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_hexistsGe3_iff_hkerGe3 m K J).symm)

/-- Rees-9′ is exactly the `Ge3` s.o.p.-to-gr residual strength.
-/
theorem rge3_iff_sopGrLowerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HsopGrLowerMinGe3AtAss m K J :=
  (rge3_bridge m K J).trans
    ((highGe3_hdimEqGe3_iff_hkerGe3 m K J).trans
      (highGe3_sopGrLowerGe3_iff_hkerGe3 m K J).symm)

/-! ## §2. Rees masters re-fired on alternate Ge3 legs -/

/-- Full `HdimEqMinAtAss` on `[gated-D2, Ge3-ker]`: the `ReesClose`
mod-crux master fed with the ker-spoke conversion.

Conditional on exactly `[hgr, hker]`. -/
theorem rge3_hdimEqMin_of_gated_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hker : HkerMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  ReesClose.rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr
    ((rge3_iff_hkerGe3 m K J).mpr hker)

/-- Full `HdimEqMinAtAss` on `[gated-D2, Ge3-hub]`: the hub leg.

Conditional on exactly `[hgr, hge3]`. -/
theorem rge3_hdimEqMin_of_gated_ge3High (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  ReesClose.rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr
    ((rge3_iff_ge3High m K J).mpr hge3)

/-- Full `HdimEqMinAtAss` on `[gated-D2, Ge3-mult]`.

Conditional on exactly `[hgr, hmult]`. -/
theorem rge3_hdimEqMin_of_gated_hmultGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hmult : HmultMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  ReesClose.rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr
    ((rge3_iff_hmultGe3 m K J).mpr hmult)

/-- Full `HdimEqMinAtAss` on `[gated-D2, Ge3-wit]`.

Conditional on exactly `[hgr, hwit]`. -/
theorem rge3_hdimEqMin_of_gated_hwitGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hwit : HwitMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  ReesClose.rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr
    ((rge3_iff_hwitGe3 m K J).mpr hwit)

/-- Full `HdimEqMinAtAss` on `[gated-D2, Ge3-∃-ker]`: the
narrowest-leg master (existential spoke, no Hilbert data).

Conditional on exactly `[hgr, hexists]`. -/
theorem rge3_hdimEqMin_of_gated_hexistsGe3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hexists : HexistsKerMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  ReesClose.rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J hgr
    ((rge3_iff_hexistsGe3 m K J).mpr hexists)

/-- Universal minimal `hker` on the cheapest legs.

Conditional on exactly `[hgr, hexists]`. -/
theorem rge3_hkerMin_of_gated_hexistsGe3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hexists : HexistsKerMinGe3AtAss m K J) :
    HkerMinAtAss m K J :=
  ReesClose.rees_hkerMin_of_sopGrLowerGated_ge3 m K J hgr
    ((rge3_iff_hexistsGe3 m K J).mpr hexists)

/-- Universal `hdepth` on the cheapest legs.

Conditional on exactly `[hgr, hexists]`. -/
theorem rge3_hdepth_of_gated_hexistsGe3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hexists : HexistsKerMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  ReesClose.rees_hdepth_of_sopGrLowerGated_ge3 m K J hgr
    ((rge3_iff_hexistsGe3 m K J).mpr hexists) Q hQ

/-- General-`k` unmixedness on the cheapest legs. The mod-crux
geometry master on the narrowest Ge3 address.

Conditional on exactly `[hgr, hexists]` (at `J`; general `k`). -/
theorem rge3_hunmixed_of_gated_hexistsGe3 (m : ℕ)
    (K : Type*) [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hexists : HexistsKerMinGe3AtAss m K J) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes :=
  ReesClose.rees_hunmixed_general_of_sopGrLowerGated_ge3 m K q
    hsucc J hJ hgr ((rge3_iff_hexistsGe3 m K J).mpr hexists)

/-- One-shot Rees joint on the cheapest legs: `hdimEqMin`, `hkerMin`,
per-prime depth, and general-`k` unmixedness in one tuple.

Conditional on exactly `[hgr, hexists]`. -/
theorem rge3_reesJoint_of_gated_hexistsGe3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hexists : HexistsKerMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      (∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
        Q ∈ associatedPrimes _ (_ ⧸ J) →
        GradeDepthFragment.DepthEqDimAt m K Q) ∧
      (∀ {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
        (_hsucc : RegularityBridge.SuccessiveSMulRegular q),
        J = Ideal.span (Set.range q) →
        ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
          (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes) := by
  have hge3 : ReesClose.HdimEqMinGe3AtAss m K J :=
    (rge3_iff_hexistsGe3 m K J).mpr hexists
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ReesClose.rees_hdimEqMin_of_sopGrLowerGated_ge3 m K J
      hgr hge3
  · exact ReesClose.rees_hkerMin_of_sopGrLowerGated_ge3 m K J
      hgr hge3
  · intro Q _ hQ
    exact ReesClose.rees_hdepth_of_sopGrLowerGated_ge3 m K J hgr
      hge3 Q hQ
  · intro k q hsucc hJ
    exact ReesClose.rees_hunmixed_general_of_sopGrLowerGated_ge3
      m K q hsucc J hJ hgr hge3

/-! ## §3. Rees-assembly reversal: C-legs fire on `[hge3]` -/

/-- `Ge3`-kernel data from rees-9′ (the one-step conversion every
reversal leg feeds).

Conditional on exactly `[hge3]`. -/
theorem rge3_hkerGe3_of_hge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge3 : ReesClose.HdimEqMinGe3AtAss m K J) :
    HkerMinGe3AtAss m K J :=
  (rge3_iff_hkerGe3 m K J).mp hge3

/-- C1 at a Ge3 prime on `[hge3]`: the retargeted augmentation is a
quasi-iso (the `hker` input comes from the Ge3 ring).

Conditional on exactly `[hge3]`. -/
theorem rge3_c1_of_hge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge3 : ReesClose.HdimEqMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hem3 : 3 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    {d : ℕ} (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    QuasiIso (residuePiShrunk m K Q d g hgen) := by
  have hkerGe3 := rge3_hkerGe3_of_hge3 m K J hge3
  have hker : RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen)
      = ⊥ :=
    hkerGe3 Q hQ g hgen hdmin (by omega)
  exact quasiIso_residuePiShrunk m K Q d g hgen hker

/-- C3-`hS` at a Ge3 prime on `[hge3]`: shift-side exactness below `d`.

Conditional on exactly `[hge3]`. -/
theorem rge3_c3hS_of_hge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge3 : ReesClose.HdimEqMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hem3 : 3 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    {d : ℕ} (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∀ i : ℕ, 1 ≤ i → i < d →
      (SelfDuality.koszulShiftComplex_commRing
        (Localization.AtPrime Q) (Fin d → Localization.AtPrime Q) d
        (KoszulComplex.koszulContractOfSequence g)).ExactAt i := by
  have hkerGe3 := rge3_hkerGe3_of_hge3 m K J hge3
  have hker : RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen)
      = ⊥ :=
    hkerGe3 Q hQ g hgen hdmin (by omega)
  exact shift_hS_of_r2Reduced Q d g hgen hker

/-- C3-`hS0` at a Ge3 prime on `[hge3]`: shift-side exactness at `0`
(`1 ≤ d` from the Ge3 gate).

Conditional on exactly `[hge3]`. -/
theorem rge3_c3hS0_of_hge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge3 : ReesClose.HdimEqMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hem3 : 3 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    {d : ℕ} (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    (SelfDuality.koszulShiftComplex_commRing
      (Localization.AtPrime Q) (Fin d → Localization.AtPrime Q) d
      (KoszulComplex.koszulContractOfSequence g)).ExactAt 0 := by
  have hkerGe3 := rge3_hkerGe3_of_hge3 m K J hge3
  have hker : RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen)
      = ⊥ :=
    hkerGe3 Q hQ g hgen hdmin (by omega)
  exact shift_hS0_of_r2Reduced Q d g hgen hker (by omega)

/-- C4-`hdim` at a Ge3 prime on `[hge3]`: the dimension equation
(`R_Q` side, via the R2 master).

Conditional on exactly `[hge3]`. -/
theorem rge3_c4hdim_of_hge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge3 : ReesClose.HdimEqMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hem3 : 3 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    {d : ℕ} (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ringKrullDim (Localization.AtPrime Q) = d := by
  have hkerGe3 := rge3_hkerGe3_of_hge3 m K J hge3
  have hker : RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen)
      = ⊥ :=
    hkerGe3 Q hQ g hgen hdmin (by omega)
  exact (grlift_r2_exact_reduced_full Q d g hgen hdmin hker).1

/-- Reversal end-to-end: per-prime `DepthEqDimAt` at a Ge3 prime on
`[hge3]` alone (sop data unconditional inside).

Conditional on exactly `[hge3]`. -/
theorem rge3_depthEqDimAt_ge3_of_hge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge3 : ReesClose.HdimEqMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hem3 : 3 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    GradeDepthFragment.DepthEqDimAt m K Q := by
  have hkerGe3 := rge3_hkerGe3_of_hge3 m K J hge3
  refine depthEqDimAt_of_hkerMin_atPrime m K Q
    (fun {d} g hgen hdmin => ?_)
  exact hkerGe3 Q hQ g hgen hdmin (by omega)

/-! ## §4. Residual register + verdict (doc-only)

exact residual of the Rees route, post-discharge (verbatim):

* `HsopGrLowerD2GatedAtAss` (gated `d = 2` s.o.p.-to-gr): closes the
  `d = 2` slice of every §2 master by one `exact`. D2-ring form
  (iff `HkerD2AtAss`, HighD2Close:379).
* `HexistsKerMinGe3AtAss` (§1 `rge3_iff_hexistsGe3`: the narrowest
  Ge3 address — `∃` minimal family with `ker = ⊥`): closes the
  remainder (§2 masters + joint) by one `exact` per theorem. Ge3-ring
  form (iff rees-9′, this file §1).
* Every other Ge3 spoke (`HkerMinGe3AtAss`, hub
  `HnoHomRelHighMinGe3AtAss`, `HmultMinGe3AtAss`, `HwitMinGe3AtAss`,
  `HdimGrMinGe3AtAss`, `HhleMinGe3AtAss`, `HgrDimLowerMinGe3AtAss`,
  `HgrDimEqMinGe3AtAss`, `HsopGrLowerMinGe3AtAss`) is an equivalent
  remainder (§1 iffs) — any single one fires every Rees output via
  the §2 masters.

why unconditional is blocked (evidence, not conjecture):

* `rge3_iff_ge3High` (§1) + `highGe3_ge3_iff_hkerGe3` (HighGe3:539):
  rees-9′ is exactly Ge3-hub strength. Unconditional rees-9′ would
  close the Ge3 crux outright — the GE3 lane's hub target. No proof
  exists below any single-slice strength (Ge3 ring tightness,
  machine-checked).
* The missing mathematics (associated-graded theory of regular local
  rings: `gr(R_Q)` a polynomial ring of Hilbert degree `embdim − 1`)
  is absent from Mathlib v4.34.0 (zero `associatedGraded` API), and
  the `d = 2` Newton pattern does not generalize (at `d ≥ 3` no
  unconditional degree lower bound exists: only `H(0) = 1`,
  `H(1) = d` are unconditional, HighGe3 §1).
* Reversal verdict: no C-condition is rees-9′. C1/C3/C4-`hdim` each
  take `hker` (§3 shows all three fire on `[hge3]` via exactly one
  ring conversion) — all strictly downstream of
  `HkerMinGe3AtAss ⟺ REES-9′`. No independent Rees-side condition
  exists to prove directly.

verdict (audited): Rees fires end-to-end on `[D2-ring, any-Ge3-spoke]`
(§2 joint); the Ge3 remainder is re-estimated to its narrowest address.
no gap-rees-10 (unchanged). The Ge3 spoke remainder is owned by the
crux work (Ge3 hub address); the gated `d = 2` remainder is the
D2 crux form.

consumers: any proof of the two residuals discharges every
Rees output (§2 joint) by single `exact`s; any Ge3-spoke proof
composes with any D2-ring form via the §2 masters.
-/

#print axioms rge3_bridge
#print axioms rge3_iff_hkerGe3
#print axioms rge3_iff_ge3High
#print axioms rge3_iff_hmultGe3
#print axioms rge3_iff_hwitGe3
#print axioms rge3_iff_hdimGrGe3
#print axioms rge3_iff_hhleGe3
#print axioms rge3_iff_lowerGe3
#print axioms rge3_iff_grDimEqGe3
#print axioms rge3_iff_hexistsGe3
#print axioms rge3_iff_sopGrLowerGe3
#print axioms rge3_hdimEqMin_of_gated_hkerGe3
#print axioms rge3_hdimEqMin_of_gated_ge3High
#print axioms rge3_hdimEqMin_of_gated_hmultGe3
#print axioms rge3_hdimEqMin_of_gated_hwitGe3
#print axioms rge3_hdimEqMin_of_gated_hexistsGe3
#print axioms rge3_hkerMin_of_gated_hexistsGe3
#print axioms rge3_hdepth_of_gated_hexistsGe3
#print axioms rge3_hunmixed_of_gated_hexistsGe3
#print axioms rge3_reesJoint_of_gated_hexistsGe3
#print axioms rge3_hkerGe3_of_hge3
#print axioms rge3_c1_of_hge3
#print axioms rge3_c3hS_of_hge3
#print axioms rge3_c3hS0_of_hge3
#print axioms rge3_c4hdim_of_hge3
#print axioms rge3_depthEqDimAt_ge3_of_hge3

end ReesGe3Discharge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
