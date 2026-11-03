/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FiniteLength

/-!
# Lower-bound attack at `d ≥ 2`: exact remainder + new `gr` machinery (R1)

Attack `HgrDimLowerMinAtAss` (`GradedDimEq.lean`), the
per-Ass-prime lower bound `dim R_Q ≤ dim gr` — the exact remainder behind
`grDimLower_iff_grDimEq` (`GradedDimEq.lean`), with the upper half and
the `d ≤ 1` lower instances already unconditional.

verdict (machine-checked, §§1–2): an unconditional proof of the lower bound
at `d ≥ 2` is OUT of reach — it is exactly goal strength. Given minimal sop
data at `Q`, the lower bound holds iff `ker polySurjResidue = ⊥`
(`grLower_iff_ker_eq_bot_atPrime`), hence at Ass level
`HgrDimLowerMinAtAss ↔ HkerMinAtAss` (`hgrDimLower_iff_hkerMin`). Since
`ker = ⊥` per Ass prime is what the §10 master produces from
`hmult + hdrop` (where `hmult` needs the Hilbert witness predicated on
`dim (S ⧸ ker) = d`, which needs the lower bound — the documented
`hle_gr → dim = d → hwit → hmult → ker = ⊥ → hle_gr` cycle), no proof of
the lower bound exists below the strength of `ker = ⊥` itself. This strand
therefore proves the maximal supporting package: the exact per-prime
remainder (§§1–2) plus two genuinely new associated-graded finiteness
results absent from Mathlib v4.34.0 (§§3–4).

## What this file proves

* (§1) Per-`Q` exact remainder, unconditional: given minimal sop data
  `(d, g, hgen, hd)`, the lower bound `dim R_Q ≤ dim gr` implies
  `ker = ⊥` (`grLower_ker_eq_bot_of_lower_atPrime`, via `dim R_Q = d`
  + the §17 chain collapse) and follows from it
  (`grLower_of_ker_eq_bot_atPrime`), hence the iff
  (`grLower_iff_ker_eq_bot_atPrime`).
* (§2) Ass-level exact remainder, unconditional: `HgrDimLowerMinAtAss`
  from `HkerMinAtAss` (`hgrDimLower_of_hkerMin`, via the minimal sop
  `grlift_sop_exists`), hence the goal-strength iff
  (`hgrDimLower_iff_hkerMin`, forward via GrDimEq §3b
  `hkerMin_of_lower`).
* (§3) `gr` is Noetherian, unconditional: `IsNoetherianRing (grRegular Q)`
  (`grLower_isNoetherianRing_gr`), via the M4b residue surjection out of
  the Noetherian polynomial ring. New: no `IsNoetherianRing gr` fact
  exists anywhere in-tree; enables Krull-hit / Ass / dimension theory
  inside `gr`.
* (§4) `gr` pieces have finite residue-field length, unconditional:
  `IsFiniteLength κ (grPiece R 𝔪 n)` (`grLower_isFiniteLength_grPiece`),
  via the §9 piece-map surjection out of the finite homogeneous piece,
  plus the `finLength = length` characterization
  (`grLower_grHilbert_coe_length`). New: makes `singleDrop_grHilbert`
  provably the true Hilbert function (previously `finLength` without a
  finite-length certificate on `grPiece`).
* (§5, doc-only) Remainder register: the verbatim open lower bound at
  `d ≥ 2`, why it is minimal and exact, and the scoped routes
  (Q4: witness route proved §6, per-prime supply proved §7,
  remainder re-estimated).
* (§6) Witness-route supply adapters, conditional-exact on the named
  crux input (plus unconditional iffs): `HgrDimLowerMinAtAss` from
  `HwitMinAtAss` / `HmultMinAtAss` / `HdimEqMinAtAss` /
  `HnoHomRelHighMinAtAss` — one-line compositions of §2 with the
  `DimensionToMultiplicity` kernel auto-close masters.
* (§7) Per-prime explicit witness supply, conditional-exact on the
  named explicit witness input: `grLower_of_witnessHyp_atPrime` /
  `grLower_of_grWitness_atPrime` — one-`exact` compositions of §1 with
  the Multiplicity §14 masters (per-prime factors of the §6 adapters).

## Scope coordination (no duplication)

* `GradedDimEq.lean`: owns the upper half, the SPEC `HgrDimLowerMinAtAss`,
  `grDimLower_iff_grDimEq`, and the §3b lower→crux auto-close lane
  (notably `hkerMin_of_lower`). This file only consumes the SPEC and
  the §3b forward direction (for the §2 iff).
* `MultiplicityNonvanishing.lean` §17: owns `hle_gr ↔ ker = ⊥`
  (`mult_hle_gr_iff_ker_eq_bot`) and `dim R_Q = d` of minimality
  (`mult_ringKrullDim_atPrime_eq_of_minimal`). This file only consumes them
  to reposition the remainder at `dim R_Q ≤ dim gr` per prime.
* `DimensionToMultiplicity.lean` §5 / `UnmixednessAtLengthTwo`: own the Ass-level
  `hgrDimEq_iff_hkerMin` and `HkerMinAtAss`. The §2 iff is the
  lower-bound-shaped counterpart (direct per-prime proof, not a
  transitivity re-share). §6 only consumes the §6/WitnessHigh kernel
  auto-close masters (`hkerMin_of_hwitMin`, `hkerMin_of_hmultMin`,
  `hkerMin_of_noHomRelHighMin`) and the `HnoHomRelHighMinAtAss` SPEC.
* `SingleDropRegularity.lean` §§8–9: own the residue module structure and the
  piece-map surjection. §4 only consumes them.

## Mathlib survey (`lean-toolchain` pins `v4.34.0`), all read-only

* `isNoetherianRing_of_surjective` —
  `RingTheory/Noetherian/Basic.lean` (consumed in §3).
* `IsNoetherianRing (MvPolynomial (Fin d) κ)` over a field synthesizes by
  `inferInstance` (verified by a `/tmp` probe with imports
  `Noetherian.Basic + FiniteType + MvPolynomial.Basic`; the chain runs
  through `Algebra.FiniteType.isNoetherianRing`,
  `RingTheory/FiniteType.lean`).
* `IsFiniteLength.of_surjective` — `RingTheory/FiniteLength.lean`
  (consumed in §4).

## Status

* §§1–4: unconditional.
* §2 iff: unconditional (iff; both directions unconditional-form).
* §6: adapters conditional-exact on the named crux input; iffs
  unconditional.
* §7: per-prime supply conditional-exact on the named explicit witness
  input.
* Overall: partial toward `HgrDimLowerMinAtAss`
  (remainder = per-Ass-prime `ker = ⊥` / the `d ≥ 2` lower bound itself, §5;
  witness lane §§6–7 reduces it to the shared R-2c′ `HwitMinAtAss`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedLowerBound

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity

/-! ## §1. Per-`Q` exact remainder: lower bound ⟺ `ker = ⊥` -/

/-- Per-`Q` lower bound forces `ker = ⊥` (given minimal sop data):
`dim R_Q = d` (minimality) turns the lower bound into `hle_gr`
(`d ≤ dim gr`), and the §17 chain collapse turns `hle_gr` into
`ker = ⊥`.
-/
theorem grLower_ker_eq_bot_of_lower_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hlo : ringKrullDim (Localization.AtPrime Q) ≤
      ringKrullDim (grRegular Q)) :
    RingHom.ker (polySurjResidue Q d g hgen) = ⊥ := by
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
  have hle : d ≤ ringKrullDim (grRegular Q) := by
    rw [← hR]
    exact hlo
  exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle

/-- Per-`Q` lower bound from `ker = ⊥` (given minimal sop data):
`ker = ⊥` gives `hle_gr` (`S ⧸ ⊥ ≃+* S`), and `dim R_Q = d`
(minimality) turns `hle_gr` into the lower bound.
-/
theorem grLower_of_ker_eq_bot_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hker : RingHom.ker (polySurjResidue Q d g hgen) = ⊥) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) := by
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
  have hle := mult_hle_gr_of_ker_eq_bot Q d g hgen hker
  rw [hR]
  exact hle

/-- Per-`Q` exact remainder: given minimal sop data, the lower bound
`dim R_Q ≤ dim gr` holds iff `ker polySurjResidue = ⊥`. In particular
no unconditional proof of the lower bound at `d ≥ 2` exists below the
strength of `ker = ⊥` itself.
-/
theorem grLower_iff_ker_eq_bot_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank) :
    (ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q)) ↔
      RingHom.ker (polySurjResidue Q d g hgen) = ⊥ :=
  ⟨grLower_ker_eq_bot_of_lower_atPrime Q d g hgen hd,
   grLower_of_ker_eq_bot_atPrime Q d g hgen hd⟩

#print axioms grLower_ker_eq_bot_of_lower_atPrime
#print axioms grLower_of_ker_eq_bot_atPrime
#print axioms grLower_iff_ker_eq_bot_atPrime

/-! ## §2. Ass-level exact remainder -/

/-- `HgrDimLowerMinAtAss` from `HkerMinAtAss`: per-`Q` minimal sop data
(`grlift_sop_exists`) feeds the §1 backward direction.
-/
theorem hgrDimLower_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  exact grLower_of_ker_eq_bot_atPrime Q d g hgen hd (hker Q hQ g hgen hd)

/-- The Ass-level lower bound is exactly goal strength
(`HkerMinAtAss`): the R1 attack closes if and only if the kernel
hypothesis proves per Ass prime. Forward is GrDimEq §3b
(`hkerMin_of_lower`, consumed not restated); backward is §2 above.
-/
theorem hgrDimLower_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimLowerMinAtAss m K J ↔ UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  ⟨hkerMin_of_lower m K J, hgrDimLower_of_hkerMin m K J⟩

#print axioms hgrDimLower_of_hkerMin
#print axioms hgrDimLower_iff_hkerMin

/-! ## §3. `gr` is Noetherian -/

/-- `grRegular Q` is Noetherian: the M4b residue surjection exhibits it
as a surjective image of the Noetherian polynomial ring `κ[t₁..t_d]`
(`d` from the minimal sop). New in-tree; absent from Mathlib v4.34.0
(which has only the Rees algebra).
-/
theorem grLower_isNoetherianRing_gr {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    IsNoetherianRing (grRegular Q) := by
  obtain ⟨d, g, hgen, _⟩ := grlift_sop_exists Q
  exact isNoetherianRing_of_surjective _ _ (polySurjResidue Q d g hgen)
    (polySurjResidue_surjective Q d g hgen)

#print axioms grLower_isNoetherianRing_gr

/-! ## §4. `gr` pieces have finite residue-field length -/

/-- Each graded piece has finite length over the residue field: the §9
piece map surjects from the finite homogeneous piece onto `grPiece`.
new in-tree: certifies `singleDrop_grHilbert` as the true Hilbert
function of `gr`.
-/
theorem grLower_isFiniteLength_grPiece {R : Type*} [CommRing R] [IsLocalRing R]
    (d : ℕ) (g : Fin d → R)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal R) (n : ℕ) :
    IsFiniteLength (IsLocalRing.ResidueField R)
      (grPiece R (IsLocalRing.maximalIdeal R) n) := by
  have hfin :=
    mult_isFiniteLength_homogeneousPiece (IsLocalRing.ResidueField R) d n
  have hsurj :=
    singleDrop_pieceMap_surjective (IsLocalRing.maximalIdeal R) d g hgen n
  exact hfin.of_surjective hsurj

/-- `singleDrop_grHilbert` coerces to the true `Module.length` of the
piece over the residue field.
-/
theorem grLower_grHilbert_coe_length {R : Type*} [CommRing R] [IsLocalRing R]
    (d : ℕ) (g : Fin d → R)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal R) (n : ℕ) :
    ↑(singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n)
      = Module.length (IsLocalRing.ResidueField R)
        (grPiece R (IsLocalRing.maximalIdeal R) n) :=
  coe_finLength (grLower_isFiniteLength_grPiece d g hgen n)

#print axioms grLower_isFiniteLength_grPiece
#print axioms grLower_grHilbert_coe_length

/-! ## §6. Witness route proved: supply adapters (Q4)

One-line compositions of `hgrDimLower_of_hkerMin` (§2) with the
`DimensionToMultiplicity` §6 kernel auto-close masters, so the shared R-2c′
witness remainder (and every other crux conclusion) discharges
`HgrDimLowerMinAtAss` by a single `exact` — the exact dual of the
GrDimEq §3b forward lane (`hwitMin_of_lower` family). The lower bound
is therefore not only `HkerMinAtAss`-strength (§2) but
`HwitMinAtAss`-strength, `HmultMinAtAss`-strength, and
`HdimEqMinAtAss`-strength (iffs below; forward directions consumed
from GrDimEq §3b, not restated).

* `hgrDimLower_of_hwitMin`, `hgrDimLower_of_hmultMin`,
  `hgrDimLower_of_hdimEqMin`, `hgrDimLower_of_noHomRelHighMin`.
* `hgrDimLower_iff_hwitMin`, `hgrDimLower_iff_hmultMin`,
  `hgrDimLower_iff_hdimEqMin`.

Status: adapters conditional-exact on the named crux input; iffs
unconditional.
-/

/-- `HgrDimLowerMinAtAss` from the witness remainder: the §5 witness
route, closed. Per-Ass-prime `ker = ⊥` (`hkerMin_of_hwitMin`) feeds
the §2 backward direction.

Conditional on exactly `[hwit]`. -/
theorem hgrDimLower_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J :=
  hgrDimLower_of_hkerMin m K J (hkerMin_of_hwitMin m K J hwit)

/-- `HgrDimLowerMinAtAss` from multiplicity-nonvanishing (auto-close).

Conditional on exactly `[hmult]`. -/
theorem hgrDimLower_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J :=
  hgrDimLower_of_hkerMin m K J (hkerMin_of_hmultMin m K J hmult)

/-- `HgrDimLowerMinAtAss` from `HdimEqMinAtAss` (auto-close).

Conditional on exactly `[hdimEq]`. -/
theorem hgrDimLower_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J :=
  hgrDimLower_of_hkerMin m K J
    (UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J hdimEq)

/-- `HgrDimLowerMinAtAss` from the high-relations residual: the lower
bound discharges jointly with R-2a′/R-2c′ on the one remainder.

Conditional on exactly `[hHigh]`. -/
theorem hgrDimLower_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J :=
  hgrDimLower_of_hkerMin m K J (hkerMin_of_noHomRelHighMin m K J hHigh)

/-- The lower bound is exactly witness-remainder-strength at Ass primes.
-/
theorem hgrDimLower_iff_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimLowerMinAtAss m K J ↔ UnmixednessAtLengthTwo.HwitMinAtAss m K J :=
  ⟨hwitMin_of_lower m K J, hgrDimLower_of_hwitMin m K J⟩

/-- The lower bound is exactly multiplicity-strength at Ass primes.
-/
theorem hgrDimLower_iff_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimLowerMinAtAss m K J ↔ UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  ⟨hmultMin_of_lower m K J, hgrDimLower_of_hmultMin m K J⟩

/-- The lower bound is exactly `hdimEq`-strength at Ass primes.
-/
theorem hgrDimLower_iff_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimLowerMinAtAss m K J ↔ UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  ⟨hdimEqMin_of_lower m K J, hgrDimLower_of_hdimEqMin m K J⟩

#print axioms hgrDimLower_of_hwitMin
#print axioms hgrDimLower_of_hmultMin
#print axioms hgrDimLower_of_hdimEqMin
#print axioms hgrDimLower_of_noHomRelHighMin
#print axioms hgrDimLower_iff_hwitMin
#print axioms hgrDimLower_iff_hmultMin
#print axioms hgrDimLower_iff_hdimEqMin

/-! ## §7. Per-prime explicit witness supply (Q4)

The §5 next-cheapest item, proved: per-prime lower bounds from explicit
Hilbert-witness data, by one-`exact` composition of §1
(`grLower_of_ker_eq_bot_atPrime`) with the Multiplicity §14 masters.
These are the per-prime factors of the §6 Ass-level adapters (which go
through the `DimensionToMultiplicity` kernel auto-close masters instead).

* `grLower_of_witnessHyp_atPrime`: lower bound from an explicit
  quotient-side witness tuple `(H, hF, hwit, hdrop)` in the exact
  `mult_ker_eq_bot_unconditional_of_witnessHyp` shape.
* `grLower_of_grWitness_atPrime`: lower bound from a `gr`-side witness
  tuple in the exact `mult_ker_eq_bot_of_grWitness` shape (R-2d′ feeds
  R-2c′ feeds the lower bound).

Conditional on exactly the named explicit witness input.
-/

/-- Per-prime lower bound from an explicit Hilbert-witness hypothesis:
the Multiplicity §14 `ker = ⊥` master feeds the §1 backward direction.

Conditional on exactly `[hF, hwit, hdrop]`. -/
theorem grLower_of_witnessHyp_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (H : ℕ → ℕ) (hd2 : 2 ≤ d)
    (hF : NewtonDifferences.IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hwit : ∃ Pwit : Polynomial ℚ, Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((MultiplicityNonvanishing.multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] NewtonDifferences.evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue Q d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime Q),
        (∀ Qm ∈ J.minimalPrimes,
          Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
          (Localization.AtPrime Q ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
        (∀ n, MultiplicityNonvanishing.multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        NewtonDifferences.IsPolyGrowth (fun n => ((MultiplicityNonvanishing.multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) : ℕ) : ℚ))
          (d - 1)) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) :=
  grLower_of_ker_eq_bot_atPrime Q d g hgen hd
    (mult_ker_eq_bot_unconditional_of_witnessHyp Q d g hgen H (by omega) hF
      hwit hdrop)

/-- Per-prime lower bound from a `gr`-side Hilbert witness: the
Multiplicity §14 R-2d′-feeds-R-2c′ master feeds the §1 backward
direction.

Conditional on exactly `[hF, Pwit, hle, hag, hc, hdrop]`. -/
theorem grLower_of_grWitness_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (H : ℕ → ℕ) (e : ℕ) (hd2 : 2 ≤ d) (hdim : e + 1 = d)
    (hF : NewtonDifferences.IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (Pwit : Polynomial ℚ) (hle : Pwit.natDegree ≤ e)
    (hag : (fun n => ((finLength
        (IsLocalRing.ResidueField (Localization.AtPrime Q))
        (grPiece (Localization.AtPrime Q)
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (n + 1)) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] NewtonDifferences.evalFun Pwit)
    (hc : Pwit.coeff e ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue Q d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime Q),
        (∀ Qm ∈ J.minimalPrimes,
          Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
          (Localization.AtPrime Q ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
        (∀ n, MultiplicityNonvanishing.multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        NewtonDifferences.IsPolyGrowth (fun n => ((MultiplicityNonvanishing.multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) : ℕ) : ℚ)) e) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) :=
  grLower_of_ker_eq_bot_atPrime Q d g hgen hd
    (mult_ker_eq_bot_of_grWitness Q d g hgen H e (by omega) hdim hF Pwit hle
      hag hc hdrop)

#print axioms grLower_of_witnessHyp_atPrime
#print axioms grLower_of_grWitness_atPrime

/-! ## §5. Remainder register (doc-only)

Minimal non-circular remainder (verbatim): `HgrDimLowerMinAtAss`, i.e.
`ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q)` per
`Q ∈ Ass(R ⧸ J)` at embedding dimension `d ≥ 2` (`d ≤ 1` is closed in
`GradedDimEq` §4).

Why the remainder is minimal and exact (all machine-checked):

* `grLower_iff_ker_eq_bot_atPrime` (§1) shows the per-`Q` lower bound is
  exactly `ker polySurjResidue = ⊥` given minimal sop data;
  `hgrDimLower_iff_hkerMin` (§2, forward via GrDimEq §3b
  `hkerMin_of_lower`) lifts this to Ass level — so the lower bound
  cannot be proved below the strength of `ker = ⊥` itself (which is
  what the §10 master produces from `hmult + hdrop`, closing the
  documented cycle).
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth /
  polynomiality fact to prove the §§1–4 masters; the only undischarged
  input is the lower bound itself.

Routes to the lower bound (all surveyed, none duplicated):

* Hilbert–Samuel polynomial route: `deg HS + 1 = dim` on both sides with
  `HS(R) = Hilb(gr)`. Needs the full HS degree theorem; Mathlib has
  neither the HS function nor its degree theory. §§3–4 land two of its
  prerequisites (Noetherian `gr`, finite-length `gr` pieces over `κ`).
* Rees-algebra route: `gr ≅ Rees(I)/I·Rees(I)` + `dim Rees = dim R + 1`.
  Needs the quotient identification plus `dim Rees = dim R + 1` (also
  absent: needs catenary-type theory). Priced, not attempted: strictly
  harder than the HS route.
* Witness route (in-tree): proved in §6 (cheapest route).
  `HwitMinAtAss` (the shared R-2c′ remainder) discharges `ker = ⊥`
  per Ass prime (`hkerMin_of_hwitMin`), hence the lower bound by §2
  (`hgrDimLower_of_hwitMin`); likewise `HmultMinAtAss`
  (`hgrDimLower_of_hmultMin`), `HdimEqMinAtAss`
  (`hgrDimLower_of_hdimEqMin`), and `HnoHomRelHighMinAtAss`
  (`hgrDimLower_of_noHomRelHighMin`), with iffs
  `hgrDimLower_iff_hwitMin` / `hgrDimLower_iff_hmultMin` /
  `hgrDimLower_iff_hdimEqMin` (forward via GrDimEq §3b).
  Per-prime explicit-`hwit`-hypothesis form proved in §7:
  `grLower_of_witnessHyp_atPrime` (feeding
  `mult_ker_eq_bot_unconditional_of_witnessHyp` into §1
  `grLower_of_ker_eq_bot_atPrime`) plus the `gr`-side variant
  `grLower_of_grWitness_atPrime`
  (feeding `mult_ker_eq_bot_of_grWitness` into §1).
  repriced remainder: the lower bound now stands or falls with the
  shared R-2c′ remainder `HwitMinAtAss` itself (narrowable to
  `HnoHomRelHighMinAtAss`); no GrLower-side supply work remains on any
  witness lane — the only open lanes are the HS route (full degree
  theorem; §§3–4 prerequisites banked) and the Rees route (strictly
  harder, priced not attempted).

Consumers: `hgrDimLower_of_hkerMin` discharges `HgrDimLowerMinAtAss` on
`[hker]` alone; feeding it into `hgrDimEqMin_of_lower` (GrDimEq §3)
yields `HgrDimEqMinAtAss`, hence `HmultMinAtAss` / `HdimEqMinAtAss` /
rb-1. `grLower_isNoetherianRing_gr` and
`grLower_isFiniteLength_grPiece` are prerequisite-free inputs to any
future Hilbert–Samuel development over `gr`.
-/

end GradedLowerBound
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
