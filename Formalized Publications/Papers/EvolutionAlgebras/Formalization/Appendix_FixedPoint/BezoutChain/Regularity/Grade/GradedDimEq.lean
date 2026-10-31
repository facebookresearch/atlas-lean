/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Associated-graded dimension equality: upper half + exact remainder (S3)

S3 (Hilbert–Samuel import route). The gr-dim crux is the per-Ass-prime
equality `dim gr_I(R) = dim R` (`DimensionToMultiplicity.lean` §4: sole open item
behind `HgrDimEqMinAtAss`, absent from Mathlib v4.34.0). This file builds the
minimal associated-graded dimension theory the crux needs, in per-Ass-prime
form matching `HgrDimEqMinAtAss`:

* (§1) Per-`Q` unconditional `dim R_Q = embdim` (`grDim_atPrime_eq_spanFinrank`,
  regularity + minimal sop data).
* (§2) Per-`Q` unconditional upper bound `dim gr ≤ dim R_Q`
  (`grDim_upper_atPrime`, M4b surjection + §1).
* (§3) The lower bound `dim R_Q ≤ dim gr` per Ass prime as the exact remainder
  (`HgrDimLowerMinAtAss`): lower ⟹ equality (`grDimEq_of_lower_atPrime`),
  lower ⟹ `HgrDimEqMinAtAss` (`hgrDimEqMin_of_lower`), converse
  (`lower_of_hgrDimEqMin`), hence the SPEC-shape iff
  (`grDimLower_iff_grDimEq`).
* (§3b) Supply adapters: lower ⟹ `hwit`/`hmult`/`hdimEq`/`hker`/rb-1
  (one-line §6 consumer-gap closures on `[hlower]`).
* (§4) Per-`Q` unconditional `d ≤ 1` lower instances
  (`grDimLower_embdim_zero/one`, via the closed §5 kernel branches).
* (§5, doc-only) Remainder register: the verbatim open lower bound at `d ≥ 2`
  (Hilbert–Samuel theory), the Rees-algebra route scoped, and why no
  unconditional proof exists below goal strength.

## Mathlib survey (`lean-toolchain` pins `v4.34.0`), all read-only

Read: `Mathlib/RingTheory/ReesAlgebra.lean` (123 lines, the only
associated-graded-adjacent file): `reesAlgebra` def (:39), `mem_reesAlgebra_iff`
(:64), `adjoin_monomial_eq_reesAlgebra` (:93), `reesAlgebra.fg` (:107),
`Algebra.FiniteType` / `IsNoetherianRing` instances (:119–:122). No Hilbert–
Samuel function, no Hilbert–Samuel polynomial, no `dim gr = dim R`, no system
of parameters (`grep -rni "systemOfParameters|HilbertSamuel"` over
`Mathlib/RingTheory/` is empty — re-verified by `IrreducibleCoreDimTheory.lean` §0).

## Scope coordination (no duplication)

* S2 / `DimensionToMultiplicity.lean` (R-2c′ closure, read in full): owns `HgrDimEqMinAtAss`,
  `hgrDimEqMin_of_assocGradedDim`, and the §5 collapse. This file only
  consumes those (explicit reuse, never restated).
* `GradedSurjectionInjective.lean` (M4c-ii growth/SES assembly) and
  `HilbertSerre.lean` (eventual polynomiality `hag_gr`): own the
  Hilbert-function analytic lane. This file proves no growth/polynomiality
  facts.
* `IrreducibleCoreDimTheory.lean`: owns nontriviality/finiteness and the `hle_gr`
  register. This file proves no `hle_gr` facts.
* New here: the `dim gr ≤ dim R_Q` upper half (previously only `dim gr ≤ d`
  against sop data), and the proof that the R-2a′ remainder is exactly the
  lower bound (iff).

## Status

* §§1–2, §3 per-`Q` helpers, §4: unconditional.
* §3 Ass-level forward (`hgrDimEqMin_of_lower`): conditional-exact on `[hlower]`.
* §3b supply adapters: conditional-exact on `[hlower]` (one-line compositions).
* §3 iff: unconditional (iff; backward is unconditional-form).
* Overall: partial toward `HgrDimEqMinAtAss`
  (remainder = `HgrDimLowerMinAtAss` only, §5).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedDimEq

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity

/-! ## §1. Per-`Q` unconditional `dim R_Q = embdim` -/

/-- `dim R_Q = embdim`: minimal sop data (`grlift_sop_exists`) feeds the
regularity equality (`mult_ringKrullDim_atPrime_eq_of_minimal`).
-/
theorem grDim_atPrime_eq_spanFinrank {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank := by
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
  rw [hR]
  exact_mod_cast hd

#print axioms grDim_atPrime_eq_spanFinrank

/-! ## §2. Per-`Q` unconditional upper bound `dim gr ≤ dim R_Q` -/

/-- `dim gr ≤ dim R_Q`: the M4b surjection cannot raise dimension
(`mult_ringKrullDim_gr_le` gives `≤ d` against sop data; §1 identifies
`d` with `dim R_Q`).
-/
theorem grDim_upper_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ringKrullDim (grRegular Q) ≤ ringKrullDim (Localization.AtPrime Q) := by
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have hgr := mult_ringKrullDim_gr_le Q d g hgen
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
  rw [hR]
  exact hgr

#print axioms grDim_upper_atPrime

/-! ## §3. The lower bound is exactly the R-2a′ remainder -/

/-- Per-Ass-prime lower bound `dim R_Q ≤ dim gr`: the minimal remainder
between the proved upper half (§2) and `HgrDimEqMinAtAss`. By
`grDimLower_iff_grDimEq` below this is exactly R-2a′-strength.

Specification (Prop address for the Hilbert–Samuel remainder). -/
def HgrDimLowerMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q)

/-- Per-`Q` equality from the lower bound (upper §2 + antisymmetry).
-/
theorem grDimEq_of_lower_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hlo : ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q)) :
    ringKrullDim (grRegular Q) = ringKrullDim (Localization.AtPrime Q) :=
  le_antisymm (grDim_upper_atPrime Q) hlo

/-- Per-`Q` lower bound from the `HgrDimEqMinAtAss`-shape equality
(`dim R_Q = embdim` is §1, unconditional).
-/
theorem grDimLower_of_grDimEq {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (h : ringKrullDim (grRegular Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) := by
  rw [grDim_atPrime_eq_spanFinrank Q, h]

/-- `HgrDimEqMinAtAss` from the lower-bound remainder: per-`Q` equality
(§2 + antisymmetry) feeds the DimToMult §3 master.

Conditional on exactly `[hlower]`. -/
theorem hgrDimEqMin_of_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : HgrDimLowerMinAtAss m K J) :
    HgrDimEqMinAtAss m K J :=
  hgrDimEqMin_of_assocGradedDim m K J
    (fun Q _ hQ => grDimEq_of_lower_atPrime Q (hlower Q hQ))

/-- Converse: `HgrDimEqMinAtAss` gives the lower bound per Ass prime
(via the per-`Q` helper + §1).
-/
theorem lower_of_hgrDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J :=
  fun Q _ hQ => grDimLower_of_grDimEq Q (hgr Q hQ)

/-- The lower bound is exactly R-2a′-strength at Ass primes.
-/
theorem grDimLower_iff_grDimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimLowerMinAtAss m K J ↔ HgrDimEqMinAtAss m K J :=
  ⟨hgrDimEqMin_of_lower m K J, lower_of_hgrDimEqMin m K J⟩

#print axioms grDimEq_of_lower_atPrime
#print axioms grDimLower_of_grDimEq
#print axioms hgrDimEqMin_of_lower
#print axioms lower_of_hgrDimEqMin
#print axioms grDimLower_iff_grDimEq

/-! ## §3b. Supply adapters: the lower bound feeds every crux conclusion

One-line compositions of `hgrDimEqMin_of_lower` (§3) with the
`DimensionToMultiplicity` §3/§3b/§6 masters, so the Hilbert–Samuel lower bound
auto-closes every crux conclusion by a single `exact` (closing the §6
consumer gap for the `HgrDimLowerMinAtAss` crux form — these adapters
live here, not in §6, because this file imports `DimensionToMultiplicity`).

* `hwitMin_of_lower`, `hmultMin_of_lower`, `hdimEqMin_of_lower`,
  `hkerMin_of_lower`, `hunmixedTwo_of_lower`.

Conditional on exactly `[hlower]` (all §3b).
-/

/-- `HwitMinAtAss` from the lower-bound remainder (via `hgrDimEqMin_of_lower`).

Conditional on exactly `[hlower]`. -/
theorem hwitMin_of_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : HgrDimLowerMinAtAss m K J) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J :=
  hwitMin_of_grDimEq m K J (hgrDimEqMin_of_lower m K J hlower)

/-- `HmultMinAtAss` from the lower-bound remainder (auto-close).

Conditional on exactly `[hlower]`. -/
theorem hmultMin_of_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : HgrDimLowerMinAtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  hmultMin_of_grDimEq m K J (hgrDimEqMin_of_lower m K J hlower)

/-- `HdimEqMinAtAss` from the lower-bound remainder (auto-close).

Conditional on exactly `[hlower]`. -/
theorem hdimEqMin_of_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : HgrDimLowerMinAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  hdimEqMin_of_grDimEq m K J (hgrDimEqMin_of_lower m K J hlower)

/-- `HkerMinAtAss` from the lower-bound remainder (kernel auto-close).

Conditional on exactly `[hlower]`. -/
theorem hkerMin_of_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : HgrDimLowerMinAtAss m K J) :
    UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  hkerMin_of_grDimEq m K J (hgrDimEqMin_of_lower m K J hlower)

/-- Rb-1 from the lower-bound remainder: R-2a′, R-2c′, `HdimEq` discharge
jointly on the one remainder.

Conditional on exactly `[hlower]`. -/
theorem hunmixedTwo_of_lower (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hlower : HgrDimLowerMinAtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  hunmixedTwo_of_grDimEq m K q hsucc J hJ
    (hgrDimEqMin_of_lower m K J hlower)

#print axioms hwitMin_of_lower
#print axioms hmultMin_of_lower
#print axioms hdimEqMin_of_lower
#print axioms hkerMin_of_lower
#print axioms hunmixedTwo_of_lower

/-! ## §4. Per-`Q` unconditional `d ≤ 1` lower instances -/

/-- Per-`Q` unconditional lower bound at embedding dimension `0`
(via the closed kernel branch `hgrDimEq_embdim_zero` + §3 helper).
-/
theorem grDimLower_embdim_zero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (he : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank = 0) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) :=
  grDimLower_of_grDimEq Q (hgrDimEq_embdim_zero m K J Q hQ he)

/-- Per-`Q` unconditional lower bound at embedding dimension `1`
(via the closed kernel branch `hgrDimEq_embdim_one` + §3 helper).
-/
theorem grDimLower_embdim_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (he : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank = 1) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) :=
  grDimLower_of_grDimEq Q (hgrDimEq_embdim_one m K J Q hQ he)

#print axioms grDimLower_embdim_zero
#print axioms grDimLower_embdim_one

/-! ## §5. Remainder register (doc-only)

Minimal non-circular remainder (verbatim): `HgrDimLowerMinAtAss`, i.e.
`ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q)` per
`Q ∈ Ass(R ⧸ J)` — the Hilbert–Samuel lower bound at `d ≥ 2` (`d ≤ 1` is
closed in §4).

Why the remainder is minimal and exact:

* `hgrDimEqMin_of_lower` shows the lower bound suffices for `HgrDimEqMinAtAss`
  (given nothing else — the upper half is §2, unconditional).
* `grDimLower_iff_grDimEq` shows the lower bound is exactly R-2a′-strength,
  and `hgrDimEq_iff_hkerMin` (DimToMult §5) puts R-2a′ at goal strength
  (`ker = ⊥`), so no unconditional proof at `d ≥ 2` exists below the strength
  of `ker = ⊥` itself.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth /
  polynomiality fact to prove the §3 masters; the only undischarged input is
  the Hilbert–Samuel lower bound itself.

Routes to the lower bound (all surveyed, none duplicated):

* Hilbert–Samuel polynomial route: `deg HS + 1 = dim` on both sides with
  `HS(R) = Hilb(gr)`. Needs the full HS degree theorem; Mathlib has neither
  the HS function nor its degree theory (see §0 survey). The S2-side
  `HilbertSerre` eventual polynomiality (`hag_gr`) is one analytic
  prerequisite, owned there.
* Rees-algebra route: `gr ≅ Rees(I)/I·Rees(I)` + `dim Rees = dim R + 1`.
  Needs the quotient identification against the project's `associatedGraded`
  (a `GradedMonoid`-based direct sum — hom constructions into it are
  nontrivial) plus `dim Rees = dim R + 1` (also absent: needs catenary-type
  theory). Priced, not attempted: strictly harder than the HS route.
* Regular-sequence route (`gr` of regular local `≅ κ[X]`): needs regular
  sequences in `gr` (Mathlib `Regular.lean` has dim formulas but no
  associated-graded identification). Circularity risk: `ker = ⊥` is what the
  §10 master produces, not an input.

Consumers (all proved in §3b): `hwitMin_of_lower` / `hmultMin_of_lower` /
`hdimEqMin_of_lower` / `hkerMin_of_lower` / `hunmixedTwo_of_lower`
discharge `HwitMinAtAss` / `HmultMinAtAss` / `HdimEqMinAtAss` /
`HkerMinAtAss` / rb-1 on `[hlower]` alone (one-line compositions of
`hgrDimEqMin_of_lower` with the DimToMult §3/§3b/§6 masters).
-/

end GradedDimEq
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
