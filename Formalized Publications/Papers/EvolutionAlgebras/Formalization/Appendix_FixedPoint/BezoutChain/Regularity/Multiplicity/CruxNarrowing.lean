/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelMain
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelCrux
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KernelChain
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Crux narrowing to High + the `d`-split attack
Narrow the crux antecedent to `HnoHomRelHighMinAtAss`
(DimToMult §7) and attack the narrowed form.

## What this file proves (no duplication: all compositions are new shapes)

* (§1) Narrowing: every crux form narrows to `HnoHomRelHighMinAtAss` by a
  named one-way arrow — `HkerMin`, `HmultMin`, `HdimEqMin` (via the WitKerCrux iffs), `HgrDimEqMin`
  (via `hwitMin_of_grDimEq`), `HdimGrMin`
  (via `grDimEqMin_of_dimGrMin`), `HexistsKerMin` (via the HwitKerCrux §2
  iff) — plus the three missing iff upgrades (`High ↔ HgrDimEqMin`,
  `High ↔ HdimGrMin`, `High ↔ HexistsKerMin`) and the joint discharge
  `highNarrow_joint_of_hHigh` (all nine crux forms from `[hHigh]` in one
  tuple, mirroring `hwitKerCrux_joint_of_hwitMin`).
* (§2) Attack: the `d`-split. Per-triple `High` is unconditional at
  `d = 0` (`hsAssemble_ker_eq_bot_zero`) and at `d = 1` given `hmin`
  (`ker_chain_ker_eq_bot_one`), both via the direct `ker = ⊥ → High`
  engine (`highNarrow_of_ker_eq_bot`). At Ass level the full `High`
  follows unconditionally from its `d ≥ 2` restriction
  (`HnoHomRelHighMinGe2AtAss`, new SPEC), and the restriction is exact
  (`highNarrow_ge2_iff`).
* (§3, doc-only) Residual register: the precise remainder is `High` at
  minimal `d ≥ 2` only.

## Scope coordination (no duplication)

* `DimensionToMultiplicity.lean` §7: owns `HnoHomRelHighMinAtAss`,
  `hwitMin_of_noHomRelHighMin`, `noHomRelHighMin_of_hwitMin`. Consumed only.
* `WitnessKernelMain.lean` §1: owns the `High ↔ {hker, hmult, hdimEq}` iffs.
  consumed only.
* `WitnessKernelCrux.lean` §2: owns `HexistsKerMinAtAss`,
  `hwitKerCrux_hexists_iff_hker`. Consumed only.
* `GradedSurjectionInjective.lean` (`hsAssemble_ker_eq_bot_zero`),
  `KernelChain.lean` (`ker_chain_ker_eq_bot_one`): the closed `d ≤ 1`
  kernel branches. Consumed only.
* This file is a new leaf: not imported by any other module (no cycle).

## Status

* §1 narrowing arrows + iffs: unconditional; joint discharge:
  conditional-exact on `[hHigh]`.
* §2 per-triple `d ≤ 1` + Ass-level `Ge2` upgrade + iff: unconditional.
* Overall: partial toward `HnoHomRelHighMinAtAss`
  (remainder = `HnoHomRelHighMinGe2AtAss` only, §3).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CruxNarrowing

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighRelationsLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelMain
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelCrux
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelChain
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. Narrowing: every crux form proves on High -/

/-- `HkerMinAtAss` narrows to High (via the crux-ring iff).
-/
theorem highNarrow_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  (hnoHomRelHighMin_iff_hkerMin m K J).mpr hker

/-- `HmultMinAtAss` narrows to High (via the crux-ring iff).
-/
theorem highNarrow_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  (hnoHomRelHighMin_iff_hmultMin m K J).mpr hmult

/-- `HdimEqMinAtAss` narrows to High (via the crux-ring iff).
-/
theorem highNarrow_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : HdimEqMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  (hnoHomRelHighMin_iff_hdimEqMin m K J).mpr hdimEq

/-- `HgrDimEqMinAtAss` narrows to High (via `hwitMin_of_grDimEq`).
-/
theorem highNarrow_of_grDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  noHomRelHighMin_of_hwitMin m K J (hwitMin_of_grDimEq m K J hgr)

/-- `HdimGrMinAtAss` narrows to High (via `grDimEqMin_of_dimGrMin`).
-/
theorem highNarrow_of_dimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimGr : HdimGrMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highNarrow_of_grDimEqMin m K J (grDimEqMin_of_dimGrMin m K J hdimGr)

/-- `HexistsKerMinAtAss` narrows to High (via the §2 ∃↔∀ iff).
-/
theorem highNarrow_of_hexists (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hexists : HexistsKerMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highNarrow_of_hkerMin m K J
    ((hwitKerCrux_hexists_iff_hker m K J).mp hexists)

/-- High is exactly `HgrDimEqMin`-strength.
-/
theorem highNarrow_iff_grDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HgrDimEqMinAtAss m K J :=
  ⟨fun hHigh => grDimEqMin_of_hwitMin m K J
      (hwitMin_of_noHomRelHighMin m K J hHigh),
    highNarrow_of_grDimEqMin m K J⟩

/-- High is exactly `HdimGrMin`-strength.
-/
theorem highNarrow_iff_dimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HdimGrMinAtAss m K J :=
  ⟨fun hHigh => hdimGrMin_of_witnessMin m K J
      (hwitMin_of_noHomRelHighMin m K J hHigh),
    highNarrow_of_dimGrMin m K J⟩

/-- High is exactly `HexistsKerMin`-strength.
-/
theorem highNarrow_iff_hexists (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HexistsKerMinAtAss m K J :=
  ⟨fun hHigh => (hwitKerCrux_hexists_iff_hker m K J).mpr
      (hkerMin_of_hwitMin m K J
        (hwitMin_of_noHomRelHighMin m K J hHigh)),
    highNarrow_of_hexists m K J⟩

/-- Joint discharge on `[hHigh]`: all nine crux forms in one tuple —
`Hwit`, `Hker`, R1's lower bound, minimal `hle`, `HdimEq`, `Hmult`,
`HgrDimEq`, `HdimGr`, `HexistsKer`. Either crux form closes every
residual by a single `exact` (mirror of `hwitKerCrux_joint_of_hwitMin`
with the narrowed antecedent first-class).

Conditional on exactly `[hHigh]`. -/
theorem highNarrow_joint_of_hHigh (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J := by
  have hwit := hwitMin_of_noHomRelHighMin m K J hHigh
  have hker := hkerMin_of_hwitMin m K J hwit
  have hlo := hgrDimLower_of_hkerMin m K J hker
  refine ⟨hwit, hker, hlo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hhleMin_of_lower m K J hlo
  · exact hdimEqMin_of_hwitMin m K J hwit
  · exact hmultMin_of_hwitMin m K J hwit
  · exact grDimEqMin_of_hwitMin m K J hwit
  · exact hdimGrMin_of_witnessMin m K J hwit
  · exact (hwitKerCrux_hexists_iff_hker m K J).mpr hker

#print axioms highNarrow_of_hkerMin
#print axioms highNarrow_of_hmultMin
#print axioms highNarrow_of_hdimEqMin
#print axioms highNarrow_of_grDimEqMin
#print axioms highNarrow_of_dimGrMin
#print axioms highNarrow_of_hexists
#print axioms highNarrow_iff_grDimEqMin
#print axioms highNarrow_iff_dimGrMin
#print axioms highNarrow_iff_hexists
#print axioms highNarrow_joint_of_hHigh

/-! ## §2. Attack: the `d`-split closes `d ≤ 1`, leaving `d ≥ 2` -/

section PerTriple

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Direct engine: `ker = ⊥` kills every homogeneous relation (needs no
minimality, no degree theory — the collapse is definitional).
-/
theorem highNarrow_of_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    KwitNoHomRelHigh P d g hgen := by
  intro y n hym _ _
  rw [hker] at hym
  exact (Submodule.mem_bot _).mp hym

/-- Per-triple High at `d = 0`, unconditionally (the HS-assemble closed
branch).
-/
theorem highNarrow_zero (g : Fin 0 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    KwitNoHomRelHigh P 0 g hgen :=
  highNarrow_of_ker_eq_bot P 0 g hgen
    (hsAssemble_ker_eq_bot_zero P g hgen)

/-- Per-triple High at `d = 1` given `hmin` (the ker-chain closed branch).
-/
theorem highNarrow_one (g : Fin 1 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : 1 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    KwitNoHomRelHigh P 1 g hgen :=
  highNarrow_of_ker_eq_bot P 1 g hgen
    (ker_chain_ker_eq_bot_one P g hgen hmin)

end PerTriple

#print axioms highNarrow_of_ker_eq_bot
#print axioms highNarrow_zero
#print axioms highNarrow_one

/-- Per-Ass-prime high-degree no-relations residual at minimal `d ≥ 2`:
the `d`-split remainder of `HnoHomRelHighMinAtAss` (the `d ≤ 1` cases
are closed by §2 above, so this restriction is exact).

Specification (Prop address for the minimal `d ≥ 2` high-relations hypothesis). -/
def HnoHomRelHighMinGe2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
      2 ≤ d → KwitNoHomRelHigh Q d g hgen

/-- Full High from its `d ≥ 2` restriction: `d = 0` and `d = 1` are the
closed branches above (`hmin` at `d = 1` is minimality itself).
-/
theorem highNarrow_of_ge2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge2 : HnoHomRelHighMinGe2AtAss m K J) :
    HnoHomRelHighMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  cases d with
  | zero => exact highNarrow_zero Q g hgen
  | succ n =>
    cases n with
    | zero => exact highNarrow_one Q g hgen (le_of_eq hdmin)
    | succ k => exact hge2 Q hQ g hgen hdmin (by omega)

/-- The `d ≥ 2` restriction from full High (verbatim restriction).
-/
theorem highNarrow_ge2_of_full (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    HnoHomRelHighMinGe2AtAss m K J := by
  intro Q _ hQ d g hgen hdmin _
  exact hHigh Q hQ g hgen hdmin

/-- The `d ≥ 2` restriction is exact: High holds iff it holds at
minimal `d ≥ 2`.
-/
theorem highNarrow_ge2_iff (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HnoHomRelHighMinGe2AtAss m K J :=
  ⟨highNarrow_ge2_of_full m K J, highNarrow_of_ge2 m K J⟩

#print axioms highNarrow_of_ge2
#print axioms highNarrow_ge2_of_full
#print axioms highNarrow_ge2_iff

/-! ## §3. Residual register (doc-only)

Minimal non-circular remainder (verbatim): `HnoHomRelHighMinGe2AtAss`,
i.e. per `Q ∈ Ass(R ⧸ J)`, per minimal family at `d ≥ 2`, no nonzero
homogeneous `ker` relation of degree `≥ 2`. This file adds no remainder
of its own: every §1 narrowing step and every §2 `d`-split step is
unconditional.

Why the remainder is minimal and exact (all machine-checked):

* `highNarrow_ge2_iff` (§2) shows full High is exactly its `d ≥ 2`
  restriction (both directions unconditional); the `d = 0` / `d = 1`
  branches close on the already-proved kernel theorems
  (`hsAssemble_ker_eq_bot_zero`, `ker_chain_ker_eq_bot_one`), with
  `hmin` at `d = 1` coming from minimality itself (`le_of_eq hdmin`).
* No unconditional proof at `d ≥ 2` exists below crux strength:
  `hwitMin_iff_noHomRelHighMin` (DimToMult) puts High at
  `HwitMinAtAss` strength, and the §1 iffs put every other crux form at
  the same strength.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, `KwitKerIsPrime`,
  `KwitNoIrredHigh`, or any growth/polynomiality fact to prove the §1–§2
  masters; the only undischarged input is the `d ≥ 2` restriction itself.

Consumers: `highNarrow_joint_of_hHigh` discharges all nine crux forms on
`[hHigh]` by a single `exact`; feeding its `HdimEqMinAtAss` component
into `hunmixed_two_forall_of_hdimEqMin` yields rb-1. Conversely the §1
one-way arrows let any future direct attack on any crux form discharge
the narrowed antecedent. The `d ≥ 2` remainder feeds DimToMult §7
(`hwitMin_of_noHomRelHighMin` via `highNarrow_of_ge2`) unchanged.
-/

end CruxNarrowing
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
