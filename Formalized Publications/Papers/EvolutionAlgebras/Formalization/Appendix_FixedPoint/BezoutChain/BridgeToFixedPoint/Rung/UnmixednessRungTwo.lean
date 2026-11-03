/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ConeNoEmbeddedRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# `k = 2` unmixedness at rung-2 diagonal data, via the `HdimEq` route
Residual (2) splits diagonal sufficiency into coefficient
genericity plus `k = 2` unmixedness. This module discharges the
unmixedness half at rung-2 bridge data (`n = 2`, where `bridgeSystem`
is a pair): `HunmixedTwoProp` (rb-1) on `[diagonal, nondegeneracy]`
plus the standing crux, in whichever equivalent form it proves.
Sibling: `BridgeToFixedPoint/RungStepFromUnmixedness.lean` wires the
general `k = 2` case (pair shape, Z2 register, step lemmas, R2 — absorbing
the former `HunmixedTwoDischarge.lean`); this file keeps the rung-2
diagonal instance + embdim narrowing.

What unmixedness needs (read from the masters): `UnmixednessAtLengthTwo` §5 gives
rb-1 conditional-exact on `[HdimEqMinAtAss]`
(`hunmixed_two_forall_of_hdimEqMin`); the supply-chain §6 iff ring
(`DimensionToMultiplicity`) shows `HdimEqMinAtAss` is mutually equivalent to
`HmultMinAtAss`, `HwitMinAtAss`, `HkerMinAtAss`, and R-2a′
(`HgrDimEqMinAtAss`), with §7 adding `HnoHomRelHighMinAtAss` to the
ring. So every corollary below is exact on its named crux input, and
no crux form can land without discharging the rest.

## What is proved here

* `hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin`
  (conditional-exact on `[hdiag, hnondeg, hdimEq]`): rb-1 at the
  rung-2 bridge pair — the §5 master fed with the proved rung-2
  `hsucc` (`hsucc_bridgeSystem_rung2_diagonal`).
* `..._of_hmultMin`, `..._of_hwitMin`, `..._of_grDimEq`,
  `..._of_hkerMin`, `..._of_noHomRelHighMin` (conditional-exact on the
  named crux input): one-`exact` variants via the supply-chain
  forward lanes, so rb-1 at rung 2 follows whatever crux form proves.
* `mem_minimalPrimes_bridgeSystem_rung2_diagonal_of_hdimEqMin`
  (conditional-exact on `[hdiag, hnondeg, hdimEq]`): the per-prime
  minimality form for direct `minimalPrimes` consumers.
* `spanFinrank_maximalIdeal_atPrime_le` (unconditional):
  `spanFinrank 𝔪(R_Q) ≤ m` for `Q` prime in `MvPolynomial (Fin m) K`,
  via regularity (`dim R_Q = embdim`, proved) + `dim R_Q = height Q`
  (Mathlib) + `height ≤ dim R = m` (Mathlib).
* `spanFinrank_atPrime_le_three_rung2` (unconditional): the rung-2
  instance (`embdim ≤ 3`, since `statementIndex 2 + 2 = 3`).
* `HdimEqD23AtAss` (SPEC) + `hdimEqMinAtAss_rung2_of_d23`
  (conditional-exact on `[hd23]`): the `HdimEqMinAtAss` remainder at
  rung 2 narrowed from `∀ d ≥ 2` to the two instances `d ∈ {2, 3}`.
* `hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_d23`,
  `mem_minimalPrimes_bridgeSystem_rung2_diagonal_of_d23`
  (conditional-exact on `[hdiag, hnondeg, hd23]`): rb-1 at rung 2 on
  the narrowed remainder.
* `hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_embdim_le_one`
  (conditional-exact on `[hdiag, hnondeg, hle]`): rb-1 at rung 2 when
  every Ass prime has `embdim ≤ 1` (vacuous-`HdimEq` route, no
  Hilbert input).

## Precise remainder (out of scope)

The standing crux itself narrowed to rung 2 (`HdimEqD23AtAss`: the
`d = 2` and `d = 3` exact-degree instances, each equivalent to its
`Hmult`/`Hwit`/`Hker`/R-2a′/no-hom-rel-high form per the iff ring) —
no new remainder is introduced. The `d = 2`/`d = 3` instances need
R-2a′ (`dim gr(R_Q) = d`) + R-2c′ (dimension-to-multiplicity), both
absent from Mathlib v4.34.0. The coefficient-genericity half of
diagonal sufficiency is a separate SPEC task (the `∀`-forms without
genericity are false: `RungDiagonalGap`, `RungDiagonalCharTwo`).

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `Geometry/UnmixednessAtLengthTwo.lean`: `HdimEqMinAtAss`,
  `hunmixed_two_of_hdimEqMin`, `hunmixed_two_forall_of_hdimEqMin`,
  `hdimEqMin_of_hmultMin` (§5 masters + §7 forward lane).
* `Regularity/Multiplicity/DimensionToMultiplicity.lean`:
  `HgrDimEqMinAtAss`, `hdimEqMin_of_grDimEq`, `hdimEqMin_of_hwitMin`,
  `hdimEqMin_of_hkerMin`, `HnoHomRelHighMinAtAss`,
  `hwitMin_of_noHomRelHighMin` (§6 supply chain + §7).
* `BridgeToFixedPoint/ConeNoEmbeddedRungs.lean`:
  `hsucc_bridgeSystem_rung2_diagonal` (proved rung-2 `hsucc`).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean`:
  `mult_dim_atPrime_eq_spanFinrank` (`dim R_Q = embdim`, regularity).
* `Regularity/Avoid/AvoidanceStep.lean`:
  `ringKrullDim_mvPolynomial_fin` (mirrored for general `Fin m`).
* `BridgeToFixedPoint/Rung/RungDiagonal.lean`: `rungI0`, `IsDiagonal`.
* `BridgeToFixedPoint/FixedPointFromBezout`, `bridgeSystem`, `bridgeForms`,
  `statementIndex`.

Mathlib v4.34.0 (all read-only):

* `associatedPrimes`, `Ideal.minimalPrimes`, `Ideal.span`.
* `IsLocalization.AtPrime.ringKrullDim_eq_height`
  (`RingTheory/Ideal/Height.lean`).
* `Ideal.height_le_ringKrullDim_of_isPrime`
  (`RingTheory/Ideal/Height.lean`).
* `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`
  (`RingTheory/KrullDimension/Polynomial.lean`),
  `ringKrullDim_eq_zero_of_field`
  (`RingTheory/KrullDimension/Field.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace UnmixednessRungTwo

/-- Rb-1 at the rung-2 bridge pair from `[diagonal, nondegeneracy,
HdimEqMinAtAss]`: the §5 master (`hunmixed_two_forall_of_hdimEqMin`)
fed with the proved rung-2 `hsucc`. At `n = 2`, `bridgeSystem` is a
pair (`statementIndex 2 + 1 = 2` by `rfl`-defeq), so this is exactly
the `k = 2` unmixedness the diagonal-sufficiency program needs.

Conditional on exactly `[hdiag, hnondeg, hdimEq]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl := by
  exact UnmixednessAtLengthTwo.hunmixed_two_forall_of_hdimEqMin (statementIndex 2 + 2) K
    (bridgeSystem 2 K c hn)
    (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
      hnondeg)
    _ rfl hdimEq

/-- Rb-1 at the rung-2 bridge pair from multiplicity-nonvanishing
(via `hdimEqMin_of_hmultMin`).

Conditional on exactly `[hdiag, hnondeg, hmult]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hmultMin
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl :=
  hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin _ _ _ hmult)

/-- Rb-1 at the rung-2 bridge pair from the witness remainder
(via `hdimEqMin_of_hwitMin`).

Conditional on exactly `[hdiag, hnondeg, hwit]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hwitMin
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl :=
  hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (DimensionToMultiplicity.hdimEqMin_of_hwitMin _ _ _ hwit)

/-- Rb-1 at the rung-2 bridge pair from R-2a′ (via
`hdimEqMin_of_grDimEq`).

Conditional on exactly `[hdiag, hnondeg, hgr]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_grDimEq
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hgr : DimensionToMultiplicity.HgrDimEqMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl :=
  hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (DimensionToMultiplicity.hdimEqMin_of_grDimEq _ _ _ hgr)

/-- Rb-1 at the rung-2 bridge pair from the kernel conclusion
(via `hdimEqMin_of_hkerMin`, goal-strength).

Conditional on exactly `[hdiag, hnondeg, hker]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hkerMin
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl :=
  hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (DimensionToMultiplicity.hdimEqMin_of_hkerMin _ _ _ hker)

/-- Rb-1 at the rung-2 bridge pair from the high-relations residual
(via `hwitMin_of_noHomRelHighMin` + `hdimEqMin_of_hwitMin`).

Conditional on exactly `[hdiag, hnondeg, hHigh]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_noHomRelHighMin
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hHigh : DimensionToMultiplicity.HnoHomRelHighMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl :=
  hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (DimensionToMultiplicity.hdimEqMin_of_hwitMin _ _ _
      (DimensionToMultiplicity.hwitMin_of_noHomRelHighMin _ _ _ hHigh))

/-- Per-prime minimality at the rung-2 bridge pair from `[diagonal,
nondegeneracy, HdimEqMinAtAss]`: the per-prime §5 master
(`hunmixed_two_of_hdimEqMin`) with the proved rung-2 `hsucc`, for
direct `minimalPrimes` consumers.

Conditional on exactly `[hdiag, hnondeg, hdimEq]`. -/
theorem mem_minimalPrimes_bridgeSystem_rung2_diagonal_of_hdimEqMin
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))))
    (P : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸
      Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    P ∈ (Ideal.span (Set.range (bridgeSystem 2 K c hn))).minimalPrimes := by
  exact UnmixednessAtLengthTwo.hunmixed_two_of_hdimEqMin (statementIndex 2 + 2) K
    (bridgeSystem 2 K c hn)
    (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
      hnondeg)
    _ rfl P hP hdimEq

/-! ## Rung-2 embdim bound + narrowed `d ∈ {2, 3}` remainder (Q2)

At rung 2, `m = statementIndex 2 + 2 = 3`, so every Ass prime has
`embdim = dim R_Q = height Q ≤ dim R = 3`. The `HdimEqMinAtAss`
remainder (`∀ d ≥ 2` at minimal `d`) therefore collapses to the two
instances `d ∈ {2, 3}` (`HdimEqD23AtAss`), and rb-1 follows on that
narrowed input alone. The `embdim ≤ 1` vacuous route is also
instantiated as a no-Hilbert-input corollary. -/

/-- Krull dimension of `K[X₀, …, Xₘ₋₁]` is `m`: the field contributes
`0` (mirrors `AvoidanceStep.ringKrullDim_mvPolynomial_fin` at general
`Fin m`).
-/
theorem ringKrullDim_mvPolynomial_fin_general (m : ℕ) (K : Type*) [Field K] :
    ringKrullDim (MvPolynomial (Fin m) K) = ((m : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

/-- Embedding dimension at a prime is at most the variable count:
`spanFinrank 𝔪(R_Q) = dim R_Q` (regularity,
`mult_dim_atPrime_eq_spanFinrank`) `= height Q`
(`IsLocalization.AtPrime.ringKrullDim_eq_height`) `≤ dim R`
(`Ideal.height_le_ringKrullDim_of_isPrime`) `= m`.
-/
theorem spanFinrank_maximalIdeal_atPrime_le (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank ≤ m := by
  have hreg := MultiplicityNonvanishing.mult_dim_atPrime_eq_spanFinrank Q
  have hloc := IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)
  have hle : Q.height ≤ ringKrullDim (MvPolynomial (Fin m) K) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have hdim := ringKrullDim_mvPolynomial_fin_general m K
  have heq : ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :
      WithBot ℕ∞) = Q.height := hreg.symm.trans hloc
  have hle2 : ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :
      WithBot ℕ∞) ≤ ((m : ℕ) : WithBot ℕ∞) := by
    rw [hdim] at hle
    rw [heq]
    exact hle
  exact_mod_cast hle2

/-- Rung-2 instance: `embdim ≤ 3` (since `statementIndex 2 + 2 = 3`).
-/
theorem spanFinrank_atPrime_le_three_rung2 (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K)) [Q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank ≤ 3 := by
  have h := spanFinrank_maximalIdeal_atPrime_le (statementIndex 2 + 2) K Q
  have h3 : statementIndex 2 + 2 = 3 := rfl
  omega

/-- Rung-2 narrowed `HdimEq` remainder: the exact-degree conclusion only
at the instances `d ∈ {2, 3}` (in verbatim `HdimEqMinAtAss` binder
shape). By the rung-2 embdim bound these are all the `d ≥ 2` minimal
instances.

Specification (Prop address for the narrowed rung-2 hypothesis). -/
def HdimEqD23AtAss (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
    d = 2 ∨ d = 3 →
      ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ d - 1 →
        (fun n => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] NewtonDifferences.evalFun Qw →
        Qw.natDegree = d - 1

/-- Full rung-2 `HdimEqMinAtAss` from the narrowed `d ∈ {2, 3}`
remainder: `2 ≤ d ≤ 3` forces the disjunction (`omega` on the embdim
bound).

Conditional on exactly `[hd23]`. -/
theorem hdimEqMinAtAss_rung2_of_d23 (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K))
    (hd23 : HdimEqD23AtAss K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 2 + 2) K J := by
  intro Q _ hQ d hdmin hd2 Qw hle hag
  have hle3 := spanFinrank_atPrime_le_three_rung2 K Q
  have hd23' : d = 2 ∨ d = 3 := by omega
  exact hd23 Q hQ hdmin hd23' Qw hle hag

/-- Rb-1 at the rung-2 bridge pair from `[diagonal, nondegeneracy,
d23]`: the narrowed remainder feeds the §5 master via
`hdimEqMinAtAss_rung2_of_d23`.

Conditional on exactly `[hdiag, hnondeg, hd23]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_d23
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hd23 : HdimEqD23AtAss K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl :=
  hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (hdimEqMinAtAss_rung2_of_d23 K _ hd23)

/-- Per-prime minimality at the rung-2 bridge pair from `[diagonal,
nondegeneracy, d23]`, for direct `minimalPrimes` consumers.

Conditional on exactly `[hdiag, hnondeg, hd23]`. -/
theorem mem_minimalPrimes_bridgeSystem_rung2_diagonal_of_d23
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hd23 : HdimEqD23AtAss K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))))
    (P : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸
      Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    P ∈ (Ideal.span (Set.range (bridgeSystem 2 K c hn))).minimalPrimes :=
  mem_minimalPrimes_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (hdimEqMinAtAss_rung2_of_d23 K _ hd23) P hP

/-- Rb-1 at the rung-2 bridge pair when every Ass prime has `embdim ≤
1`: the vacuous-`HdimEq` route (`hdimEqMinAtAss_of_embdim_le_one`) —
no Hilbert input at all.

Conditional on exactly `[hdiag, hnondeg, hle]`. -/
theorem hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_embdim_le_one
    (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hle : ∀ (Q : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K))
      [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸
        Ideal.span (Set.range (bridgeSystem 2 K c hn))) →
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank ≤ 1) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn)
      (ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
        hnondeg)
      (Ideal.span (Set.range (bridgeSystem 2 K c hn))) rfl :=
  hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin K c hn hdiag
    hnondeg (ConeNoEmbeddedRungs.hdimEqMinAtAss_of_embdim_le_one _ _ _ hle)

#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hdimEqMin
#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hmultMin
#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hwitMin
#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_grDimEq
#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_hkerMin
#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_noHomRelHighMin
#print axioms mem_minimalPrimes_bridgeSystem_rung2_diagonal_of_hdimEqMin
#print axioms ringKrullDim_mvPolynomial_fin_general
#print axioms spanFinrank_maximalIdeal_atPrime_le
#print axioms spanFinrank_atPrime_le_three_rung2
#print axioms hdimEqMinAtAss_rung2_of_d23
#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_d23
#print axioms mem_minimalPrimes_bridgeSystem_rung2_diagonal_of_d23
#print axioms hunmixedTwoProp_bridgeSystem_rung2_diagonal_of_embdim_le_one

end UnmixednessRungTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
