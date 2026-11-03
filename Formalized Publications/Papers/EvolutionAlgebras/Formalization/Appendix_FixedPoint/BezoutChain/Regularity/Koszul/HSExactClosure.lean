/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.PieceIntegration
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactEmbDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoEndToEnd
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability

/-!
# HS-exact end-to-end closure at embdim 2
Close the `[hgrExact]` / `[hhsDeg]` inputs of the HSIntegrate joints
(`hsIntegrate_hsExactD2_of_grExact`:102 on `[hgrExact]`,
`hsIntegrate_hwitD2_of_grExact_hsDeg`:121 on `[hgrExact, hhsDeg]`)
through the B2 chain, discharging each leg at its cheapest
address. No `hpiece` content anywhere: `hpiece` is closed (HSDegree §5,
L2) and consumed only inside the cited suppliers — never
reproved here.

## What this file proves

* (§1) `hhsDeg` wiring: the unconditional `grExact_hsDegLowerD2`
  (GrExact:365) is fed into HSIntegrate:121 in its exact input
  shape, dropping the `[hhsDeg]` leg: `hsClose_hwitD2_of_grExact` on
  `[hgrExact]` alone.
* (§2) `hgrExact` legs: `HgrExactD2AtAss` on `[HkerD2AtAss]`
  (`hsClose_grExactD2_of_hkerD2`, the GrExact-§3 shape restated as
  this chain's named leg) and on the cheapest `HkerD2` leg — the
  gated s.o.p.-to-gr residual `HsopGrLowerD2GatedAtAss`
  (`hsClose_grExactD2_of_sopGrLowerGated`, via
  `highD2Close_hkerD2_of_sopGrLowerGated`). The gate is load-bearing:
  the ungated `HsopGrLowerD2AtAss` is false as stated (witness
  `J = ⊥`, `Q = ⊥`, `x = 0`), so only the gated form is used.
* (§3) End-to-end HS-route discharge on the single gated remainder:
  per-prime `hsExactD2` via:102
  (`hsClose_hsExactD2_of_sopGrLowerGated`), `HwitD2AtAss` via:121
  (`hsClose_hwitD2_of_sopGrLowerGated`), and the one-shot HS-chain
  bundle `hsClose_hsChainD2_of_sopGrLowerGated`.
* (§4, doc-only) Remainder register: the exact residual is the
  single gated SPEC `[HsopGrLowerD2GatedAtAss]`, iff-equivalent to
  `HkerD2AtAss` (HighD2Close:379–381, joins the D2 ring) — the crux
  itself, not an artifact of this file.

## Status

conditional-exact: `hsClose_hwitD2_of_grExact` on `[hgrExact]`,
`hsClose_grExactD2_of_hkerD2` on `[HkerD2]`,
`hsClose_grExactD2_of_sopGrLowerGated` on `[gated]`,
`hsClose_hsExactD2_of_sopGrLowerGated` on `[gated]`,
`hsClose_hwitD2_of_sopGrLowerGated` on `[gated]`,
`hsClose_hsChainD2_of_sopGrLowerGated` on `[gated]`.
No unconditional close is claimed: `hne ⟺ hmult ⟺ ker = ⊥`
(`kwit_hmult_iff_ker_eq_bot`), so `[gated]` is minimal.

## References

Project (read-only):
* `Regularity/Multiplicity/PieceIntegration.lean` (:102 on `[hgrExact]`,:121 on
  `[hgrExact, hhsDeg]` — the consumption joints).
* `Regularity/Koszul/GradedExactEmbDimTwo.lean` (§3 `grExact_grExactD2_of_hkerD2`
  :230, §5 `grExact_hsExactD2_of_grExact`:264, §6
  `grExact_hsDegLowerD2`:365 — the B2 chain).
* `Regularity/Multiplicity/DimTwoEndToEnd.lean` (gated SPEC
  `HsopGrLowerD2GatedAtAss`:147, cheapest leg
  `highD2Close_hkerD2_of_sopGrLowerGated`:253, exactness iff
  :379–381).
* `Regularity/Multiplicity/WitnessHighAttack.lean` (§4 SPECs `HgrExactD2AtAss`,
  `HhsDegLowerD2AtAss`).
* `Regularity/HomologicalDepth/WitnessKernelDimTwo.lean` (`HkerD2AtAss`, `HwitD2AtAss`).
* `Regularity/Koszul/FiltrationStability.lean` (`isNoetherianRing_atPrime`
  instance for the:102 joint).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HSExactClosure

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PieceIntegration
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedExactEmbDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimTwoEndToEnd
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences

/-! ## §1. `hhsDeg` wiring: `HwitD2` on `[hgrExact]` alone -/

/-- `HwitD2AtAss` from gr-exact data alone: the `[hhsDeg]` leg of
HSIntegrate:121 is discharged by the unconditional
`grExact_hsDegLowerD2` in its exact input shape.

Conditional on exactly `[hgrExact]`. -/
theorem hsClose_hwitD2_of_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J) :
    HwitD2AtAss m K J :=
  hsIntegrate_hwitD2_of_grExact_hsDeg m K J hgrExact
    (grExact_hsDegLowerD2 m K J)

/-! ## §2. `hgrExact` legs: `[HkerD2]` and the cheapest `[gated]` leg -/

/-- `HgrExactD2AtAss` from the `d = 2` crux form `HkerD2AtAss`: the
GrExact-§3 supply restated as this chain's named `HkerD2` leg (the
exact `hsIntegrate` input shape).

Conditional on exactly `[hker]`. -/
theorem hsClose_grExactD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HgrExactD2AtAss m K J :=
  grExact_grExactD2_of_hkerD2 m K J hker

/-- `HgrExactD2AtAss` from the gated s.o.p.-to-gr residual: the
cheapest `HkerD2` leg (`highD2Close_hkerD2_of_sopGrLowerGated`)
feeds the §2 `HkerD2` leg.

Conditional on exactly `[hgr]`. -/
theorem hsClose_grExactD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HgrExactD2AtAss m K J :=
  hsClose_grExactD2_of_hkerD2 m K J
    (highD2Close_hkerD2_of_sopGrLowerGated m K J hgr)

/-! ## §3. End-to-end HS-route discharge on the gated remainder -/

/-- Per-prime HS exact degree 2 from the gated residual: the §2
gr-exact supply feeds HSIntegrate:102 (the `IsNoetherianRing`
joint instance is `isNoetherianRing_atPrime`).

Conditional on exactly `[hgr]`. -/
theorem hsClose_hsExactD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  hsIntegrate_hsExactD2_of_grExact m K J
    (hsClose_grExactD2_of_sopGrLowerGated m K J hgr) Q hQ hemb

/-- `HwitD2AtAss` from the gated residual via the HS route: the §2
gr-exact supply feeds the §1 joint (HSIntegrate:121 with
unconditional `hhsDeg`). The D2-ring route twin is
`highD2Close_hwitD2_of_sopGrLowerGated`; this is the HS-route
end-to-end integration check.

Conditional on exactly `[hgr]`. -/
theorem hsClose_hwitD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HwitD2AtAss m K J :=
  hsClose_hwitD2_of_grExact m K J
    (hsClose_grExactD2_of_sopGrLowerGated m K J hgr)

/-- One-shot HS-chain bundle on the gated residual: all three
HS-chain addresses (`HgrExactD2`, `HhsDegLowerD2`, `HwitD2`) in one
tuple. The `hhsDeg` component is unconditional; the other two ride
the §§1–2 chain.

Conditional on exactly `[hgr]`. -/
theorem hsClose_hsChainD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HgrExactD2AtAss m K J ∧ HhsDegLowerD2AtAss m K J ∧
      HwitD2AtAss m K J := by
  have hgrExact := hsClose_grExactD2_of_sopGrLowerGated m K J hgr
  refine ⟨hgrExact, grExact_hsDegLowerD2 m K J, ?_⟩
  exact hsClose_hwitD2_of_grExact m K J hgrExact

/-! ## §4. Remainder register (doc-only)

Exact residual of this file: the single gated SPEC
`[HsopGrLowerD2GatedAtAss]`. Minimality: the gated residual is
iff-equivalent to `HkerD2AtAss`
(`highD2Close_sopGrLowerD2Gated_iff_hkerD2`, joining the D2 ring),
and `hne ⟺ hmult ⟺ ker = ⊥` (`kwit_hmult_iff_ker_eq_bot`), so no
narrower conditioning of the gr-exact leg exists. This is the crux
itself (`d = 2` slice of the High-at-Ge2 remainder), not an
artifact of this file: `hF` is unconditional (GrExact §1), `hpiece`
is unconditional (HSDegree §5 supply), the HS-degree step is
unconditional (GrExact §6, wired in §1 above).

What fell: the `[hhsDeg]` leg of HSIntegrate:121 (gone —
unconditional supply), the `[hgrExact]` legs of:102/:121
(narrowed to exactly `[gated]`), per-prime `hsExactD2` and
`HwitD2` end-to-end on `[gated]` via the HS route, and the
one-shot HS-chain bundle.

Nothing in this file assumes `hwit`, `hdimEq`, or any growth fact
beyond the cited suppliers; the only undischarged input is the
gated crux form itself (§§2–3).
-/

#print axioms hsClose_hwitD2_of_grExact
#print axioms hsClose_grExactD2_of_hkerD2
#print axioms hsClose_grExactD2_of_sopGrLowerGated
#print axioms hsClose_hsExactD2_of_sopGrLowerGated
#print axioms hsClose_hwitD2_of_sopGrLowerGated
#print axioms hsClose_hsChainD2_of_sopGrLowerGated

end HSExactClosure
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
