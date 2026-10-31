/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# High relations are exactly the dimension lower bound
R2 (no-high-relations attack at minimal `d ≥ 2` per Ass prime).
The target `HnoHomRelHighMinAtAss` (`DimensionToMultiplicity.lean` §7: per-Ass-prime,
per-minimal-family `KwitNoHomRelHigh`) is goal-strength — it is iff-exact
with `HwitMinAtAss` (`hwitMin_iff_noHomRelHighMin`, DimToMult), so no
unconditional proof exists below the strength of the crux itself. This file
proves the maximal partial: the exact reduction of High to the dimension
lower bound, in per-triple and Ass-minimal form, coordinating with the R1
lane (`GradedDimEq.lean`, read-only here — this file only consumes it).

## What this file proves

* (§1) Per-triple exactness given `[hmin, 1 ≤ d]` (HomRelHigh defs):
  `KwitNoHomRelHigh ↔ hle_gr` (`highMin_high_iff_hle_of_minimal`):
  backward is `hle → ker = ⊥` (Multiplicity §17 collapse, needs
  nothing else); forward is `High + Low(hmin, Q1) → ker = ⊥` (§2 pair
  exactness) `→ hle`. Plus `KwitKerIsPrime` from `hle` and from `High`
  (the §4 master's Prime hypothesis evaporates — stepping stone, not a
  gap), and the three Witness-def transfers via the §10 bridge (`Iff.rfl`).
* (§2) `HhleMinAtAss` (SPEC: per-Ass-prime, per-minimal-family `hle_gr`)
  and its unconditional iff with R1's `HgrDimLowerMinAtAss`
  (`hhleMin_iff_lower`, via GrDimEq §1 `dim R_Q = embdim` both ways).
* (§3) Ass-minimal exactness, unconditional (iff):
  `HnoHomRelHighMinAtAss ↔ HhleMinAtAss` (`hnoHomRelHighMin_iff_hhleMin`).
  Backward needs nothing (`hle → ker = ⊥ → High`); forward splits
  `d = 0` (closed `ker = ⊥` via `hsAssemble_ker_eq_bot_zero`) vs `d ≥ 1`
  (§1 with `hmin = le_of_eq hdmin`).
* (§4) R1↔R2 wire: `HnoHomRelHighMinAtAss ↔ HgrDimLowerMinAtAss`
  (`hnoHomRelHighMin_iff_lower`) — the two lanes attack the same
  crux; closing either closes both (and, via DimToMult §3b/§7, `HwitMin`,
  `HmultMin`, `HdimEqMin`, rb-1).
* (§5) rb-1 auto-close on `[HhleMinAtAss]` (`hunmixedTwo_of_hhleMin`).
* (§6, doc-only) Residual register: the precise remainder is R1's lower
  bound only; Prime/NoIrred/UFD-descent are all bypassed for exactness.

## Why this is maximal

* The §3/§4 iffs show the High residual is exactly R1's dimension lower
  bound — nothing strictly between them remains to be proved.
* An unconditional proof of either side is impossible below crux strength
  (DimToMult: High `↔ HwitMinAtAss`; GrDimEq: Lower `↔ HgrDimEq`).
* The UFD descent (HomRelHigh §§3–4) and the DimTheory NoIrred master are
  not superseded as mathematics — they exhibit the irreducible-core
  structure — but for the exactness they are bypassed: `hle ↔ ker = ⊥`
  closes High directly in both directions.

## Scope coordination (no duplication)

* R1 / `GradedDimEq.lean` (read in full): owns `HgrDimLowerMinAtAss`,
  `grDim_atPrime_eq_spanFinrank`, `grDim_upper_atPrime`. Consumed only.
* `DimensionToMultiplicity.lean` §7: owns `HnoHomRelHighMinAtAss`,.
  consumed only. This file is not imported by it (no cycle: new leaf).
* `HighHomogeneousRelations.lean` §§2/7/10, `HilbertWitnessNarrowing.lean` Q1 ,
  `MultiplicityNonvanishing.lean` §17 , `GradedSurjectionInjective.lean` d=0
  : all consumed, never restated.

## Status

* §1 per-triple lemmas + Witness transfers: unconditional
  (conditional-form on `[hmin]` + `1 ≤ d` where stated; the `hle → High`
  direction needs neither).
* §2 `HhleMinAtAss` iff R1-lower: unconditional (iff).
* §3 Ass-min High iff hle-min: unconditional (iff).
* §4 R1↔R2 iff: unconditional (iff).
* §5 rb-1: conditional-exact on `[HhleMinAtAss]`.
* Overall: partial toward `HnoHomRelHighMinAtAss`
  (remainder = `HgrDimLowerMinAtAss` only, §6).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HighRelationsLowerBound

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

/-! ## §1. Per-triple `High ↔ hle_gr` given minimality -/

section PerTriple

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `hle_gr → High`: `hle` forces `ker = ⊥` (the §17 collapse), killing
every homogeneous relation. Needs neither `hmin` nor `1 ≤ d`.
-/
theorem highMin_high_of_hle (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hle : d ≤ ringKrullDim (grRegular P)) :
    KwitNoHomRelHigh P d g hgen := by
  intro y n hym _ _
  have hker := (mult_hle_gr_iff_ker_eq_bot P d g hgen).mp hle
  rw [hker] at hym
  exact (Submodule.mem_bot _).mp hym

/-- `High → hle_gr` given minimality: `Low` from `hmin` (Q1 join) plus
`High` gives `ker = ⊥` (§2 pair exactness, needs `1 ≤ d`), hence `hle`.
-/
theorem highMin_hle_of_high_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hHigh : KwitNoHomRelHigh P d g hgen) :
    d ≤ ringKrullDim (grRegular P) := by
  have hlow := kwitHigh_low_of_minimal P d g hgen hmin
  have hker := kwitHigh_ker_eq_bot_of_low_high P d g hgen hd hlow hHigh
  exact (mult_hle_gr_iff_ker_eq_bot P d g hgen).mpr hker

/-- Per-triple exactness: `High ↔ hle_gr` given `[hmin, 1 ≤ d]`.
-/
theorem highMin_high_iff_hle_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    KwitNoHomRelHigh P d g hgen ↔ d ≤ ringKrullDim (grRegular P) :=
  ⟨highMin_hle_of_high_of_minimal P d g hgen hd hmin,
    highMin_high_of_hle P d g hgen⟩

/-- `KwitKerIsPrime` from `hle_gr`: `hle → ker = ⊥ → Prime`. The §4
master's Prime hypothesis evaporates given `hle`.
-/
theorem highMin_prime_of_hle (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hle : d ≤ ringKrullDim (grRegular P)) :
    KwitKerIsPrime P d g hgen :=
  kwitHigh_prime_of_ker_eq_bot P d g hgen
    ((mult_hle_gr_iff_ker_eq_bot P d g hgen).mp hle)

/-- `KwitKerIsPrime` from `High` given minimality: Prime is implied by the
goal conjunction (stepping stone, strictly weaker).
-/
theorem highMin_prime_of_high_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hHigh : KwitNoHomRelHigh P d g hgen) :
    KwitKerIsPrime P d g hgen :=
  highMin_prime_of_hle P d g hgen
    (highMin_hle_of_high_of_minimal P d g hgen hd hmin hHigh)

/-- Witness-def `hle_gr → High` (via the §10 bridge, `Iff.rfl`).
-/
theorem highMin_wit_high_of_hle (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hle : d ≤ ringKrullDim (grRegular P)) :
    HilbertWitnessNarrowing.KwitNoHomRelHigh P d g hgen :=
  (kwitHigh_witness_bridge P d g hgen).mpr
    (highMin_high_of_hle P d g hgen hle)

/-- Witness-def `High → hle_gr` given minimality (via the §10 bridge).
-/
theorem highMin_wit_hle_of_high_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hHigh : HilbertWitnessNarrowing.KwitNoHomRelHigh P d g hgen) :
    d ≤ ringKrullDim (grRegular P) :=
  highMin_hle_of_high_of_minimal P d g hgen hd hmin
    ((kwitHigh_witness_bridge P d g hgen).mp hHigh)

/-- Witness-def exactness: `High ↔ hle_gr` given `[hmin, 1 ≤ d]`.
-/
theorem highMin_wit_high_iff_hle_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    HilbertWitnessNarrowing.KwitNoHomRelHigh P d g hgen ↔
      d ≤ ringKrullDim (grRegular P) :=
  (kwitHigh_witness_bridge P d g hgen).trans
    (highMin_high_iff_hle_of_minimal P d g hgen hd hmin)

end PerTriple

#print axioms highMin_high_of_hle
#print axioms highMin_hle_of_high_of_minimal
#print axioms highMin_high_iff_hle_of_minimal
#print axioms highMin_prime_of_hle
#print axioms highMin_prime_of_high_of_minimal
#print axioms highMin_wit_high_of_hle
#print axioms highMin_wit_hle_of_high_of_minimal
#print axioms highMin_wit_high_iff_hle_of_minimal

/-! ## §2. Ass-minimal `hle` and its iff with R1's lower bound -/

/-- Per-Ass-prime, per-minimal-family `hle_gr`: the dimension-side address
of the High residual at minimal `d`.

Specification (Prop address for the minimal `hle` hypothesis). -/
def HhleMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (_hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
      d ≤ ringKrullDim (grRegular Q)

/-- `HhleMinAtAss` from R1's lower bound: per family, `dim R_Q ≤ dim gr`
plus §1 (`dim R_Q = embdim`) plus `hdmin` is `hle_gr`.
-/
theorem hhleMin_of_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : HgrDimLowerMinAtAss m K J) :
    HhleMinAtAss m K J := by
  intro Q _ hQ d g _hgen hdmin
  have hlo := hlower Q hQ
  rw [grDim_atPrime_eq_spanFinrank Q] at hlo
  rw [hdmin]
  exact hlo

/-- R1's lower bound from `HhleMinAtAss`: per `Q`, minimal sop data
(`grlift_sop_exists`) carries `hle`, and §1 identifies `d` with `dim R_Q`.
-/
theorem lower_of_hhleMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hhle : HhleMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have hle := hhle Q hQ g hgen hd
  rw [grDim_atPrime_eq_spanFinrank Q, ← hd]
  exact hle

/-- Minimal `hle` is exactly R1's lower bound at Ass primes.
-/
theorem hhleMin_iff_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhleMinAtAss m K J ↔ HgrDimLowerMinAtAss m K J :=
  ⟨lower_of_hhleMin m K J, hhleMin_of_lower m K J⟩

#print axioms hhleMin_of_lower
#print axioms lower_of_hhleMin
#print axioms hhleMin_iff_lower

/-! ## §3. Ass-minimal exactness: `High ↔ hle` -/

/-- `HnoHomRelHighMinAtAss` from minimal `hle`: per family, `hle` needs
nothing else (`hle → ker = ⊥ → High`).
-/
theorem hnoHomRelHighMin_of_hhleMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hhle : HhleMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  exact highMin_wit_high_of_hle Q d g hgen (hhle Q hQ g hgen hdmin)

/-- Minimal `hle` from `HnoHomRelHighMinAtAss`: per family, `d = 0` is the
closed `ker = ⊥` branch (`hsAssemble_ker_eq_bot_zero`); `d ≥ 1` is §1
with `hmin = le_of_eq hdmin`.
-/
theorem hhleMin_of_hnoHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    HhleMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  by_cases hd0 : d = 0
  · subst hd0
    have hker := hsAssemble_ker_eq_bot_zero Q g hgen
    exact (mult_hle_gr_iff_ker_eq_bot Q 0 g hgen).mpr hker
  · have hd1 : 1 ≤ d := by omega
    have hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hdmin
    exact highMin_wit_hle_of_high_of_minimal Q d g hgen hd1 hmin
      (hHigh Q hQ g hgen hdmin)

/-- Ass-minimal exactness: High is exactly minimal `hle` at Ass primes.
-/
theorem hnoHomRelHighMin_iff_hhleMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HhleMinAtAss m K J :=
  ⟨hhleMin_of_hnoHomRelHighMin m K J, hnoHomRelHighMin_of_hhleMin m K J⟩

#print axioms hnoHomRelHighMin_of_hhleMin
#print axioms hhleMin_of_hnoHomRelHighMin
#print axioms hnoHomRelHighMin_iff_hhleMin

/-! ## §4. R1↔R2 wire: High is exactly R1's lower bound -/

/-- R1 closes R2: `HnoHomRelHighMinAtAss` from `HgrDimLowerMinAtAss`.
-/
theorem hnoHomRelHighMin_of_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : HgrDimLowerMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  hnoHomRelHighMin_of_hhleMin m K J (hhleMin_of_lower m K J hlower)

/-- R2 closes R1: `HgrDimLowerMinAtAss` from `HnoHomRelHighMinAtAss`.
-/
theorem lower_of_hnoHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    HgrDimLowerMinAtAss m K J :=
  lower_of_hhleMin m K J (hhleMin_of_hnoHomRelHighMin m K J hHigh)

/-- Headline: the two lanes attack the same crux — R2's High
residual is exactly R1's dimension lower bound.
-/
theorem hnoHomRelHighMin_iff_lower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HgrDimLowerMinAtAss m K J :=
  ⟨lower_of_hnoHomRelHighMin m K J, hnoHomRelHighMin_of_lower m K J⟩

#print axioms hnoHomRelHighMin_of_lower
#print axioms lower_of_hnoHomRelHighMin
#print axioms hnoHomRelHighMin_iff_lower

/-! ## §5. Rb-1 auto-close on minimal `hle` -/

/-- Rb-1 from minimal `hle`: `hle-min → High-min` (§3) feeds the
DimToMult §7 master.

Conditional on exactly `[HhleMinAtAss]`. -/
theorem hunmixedTwo_of_hhleMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hhle : HhleMinAtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  hunmixedTwo_of_noHomRelHighMin m K q hsucc J hJ
    (hnoHomRelHighMin_of_hhleMin m K J hhle)

#print axioms hunmixedTwo_of_hhleMin

/-! ## §6. Residual register (doc-only)

Minimal non-circular remainder (verbatim): `HgrDimLowerMinAtAss`, i.e.
`ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q)` per
`Q ∈ Ass(R ⧸ J)` — R1's Hilbert–Samuel lower bound (this file adds no
remainder of its own: every forward/backward step above is unconditional).

Why the remainder is minimal and exact:

* `hnoHomRelHighMin_iff_lower` (§4) shows R2's High residual is exactly
  R1's lower bound (both directions unconditional); `hhleMin_iff_lower`
  (§2) and `hnoHomRelHighMin_iff_hhleMin` (§3) are the two factored exact
  steps (per-minimal-family `hle_gr` is the middle address).
* No unconditional proof at `d ≥ 2` exists below crux strength:
  `hwitMin_iff_noHomRelHighMin` (DimToMult) puts High at
  `HwitMinAtAss` strength, and `grDimLower_iff_grDimEq` (GrDimEq §3) puts
  the lower bound at `HgrDimEq` strength.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, `KwitKerIsPrime`,
  `KwitNoIrredHigh`, or any growth/polynomiality fact to prove the §1–§4
  masters; the only undischarged input is the lower bound itself.
* `KwitKerIsPrime` is redundant given `hle` (`highMin_prime_of_hle`) and
  implied by `High` given `hmin` (`highMin_prime_of_high_of_minimal`) —
  a stepping stone, not an independent gap. The UFD descent
  (HomRelHigh §§3–4) and `koszulDim_noIrred_of_hle` are bypassed for the
  exactness (the §17 collapse `hle ↔ ker = ⊥` closes High directly in
  both directions), but stand as the discovered irreducible-core
  structure.

Consumers: `hnoHomRelHighMin_of_lower` discharges `HnoHomRelHighMinAtAss`
on R1's `[hlower]` alone; feeding it into `hwitMin_of_noHomRelHighMin` /
`hunmixedTwo_of_noHomRelHighMin` (DimToMult §7) yields `HwitMinAtAss` /
rb-1. Conversely `lower_of_hnoHomRelHighMin` lets any future direct High
attack discharge R1's residual.
-/

end HighRelationsLowerBound
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
