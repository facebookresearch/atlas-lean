/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ConeNoEmbeddedRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthK
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Rung-`≥ 2` step data from `k = 2` unmixedness
Preparatory wiring: exact-on-unmixedness corollaries consuming Q2's
unmixedness output, so rung `≥ 2` closes automatically when Q2 proves.

Q2's output type is `UnmixednessAtLengthTwo.HunmixedTwoProp` at bridge data (the
`∀ P [P.IsPrime], P ∈ Ass → P ∈ minimalPrimes` shape concluded by every
`UnmixednessRungTwo` corollary); the general-`k` analogue is
`UnmixednessAtLengthK.HunmixedGeProp`. Downstream consumers (`ConeNoEmbeddedRungs` §2,
`AvoidanceApply` avoidance, the `hge2` step binders) take the register
`∀ P ∈ Ass, P ∈ minimalPrimes` shape (no instance binder) or derive
regularity from it. This module is the glue between the two.

## What is proved here

* §1 adapters (unconditional): `hunmixed_forall_of_hunmixedTwoProp`
  (`HunmixedTwoProp` → register `∀`-shape, discharging `[IsPrime]` via
  `AssociatedPrimes.mem_iff`), `hunmixed_forall_of_hunmixedGeProp`
  (general-`k` analogue), `hunmixedTwo_register_of_hunmixedTwoProp`
  (fold to the `AvoidanceApply.UnmixednessAtLengthTwo` Z2 register).
* §2 rung-2 cone end-to-end from Q2's output alone (no `HdimEq`, no
  diagonal/nondegeneracy hypotheses — those live inside Q2's proof):
  `coneNoEmbedded_bridgeForms_rung2_of_hunmixedTwoProp`
  (conditional-exact on `[hU]`, via §2 `coneNoEmbedded_of_hunmixed`),
  `havoid_secForm_bridgeForms_rung2_of_algebraData_of_hunmixedTwoProp`
  (+ algebra data), and the headline
  `hres2_pair_rung2_diagonal_of_algebraData_of_hunmixedTwoProp`
  (full `hsucc ∧ havoid` pair at `n = 2` from
  `[diagonal, nondegeneracy, hU]` + algebra data, mirroring the rung-1
  `hres2_pair_rung1_of_algebraData`).
* §3 `hge2` step-data masters: `isSMulRegular_quot_of_hunmixed_of_minAvoid`
  (unconditional reduction at general Noetherian `R`: regularity from
  `[hunmixed, minAvoid]` via
  `PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes`),
  `hreg_bridge_of_hunmixed_of_minAvoid` (general-`(n, j)` bridge step in
  the verbatim `hge2` binder shape, via `ofList_take_eq_span_image` +
  `span_smul_top`), `hreg_rung2_bridge_of_hunmixedTwoProp_of_minAvoid`
  (the `j.val = 2` step from Q2's output + a span equation),
  `prefixPair` + `span_prefixPair_rung2` (unconditional canonical
  `Fin 2` prefix reindexing + its span equation, gated on `2 ≤ n`),
  and the composed `hreg_rung2_bridge_of_hunmixedTwoProp_canonical`.
* §4 `hreg_rung2slice_of_forall_hunmixed_of_forall_minAvoid`: the
  `j.val = 2` slice of both `hge2narrow` `∀`-forms (diagonal + generic)
  from `∀`-closed `[hunmixed, minAvoid]`.

## Precise remainder (out of scope)

1. Q2's output itself (`HunmixedTwoProp` at bridge data — the standing
   crux in whichever form it proves). Every corollary here fires the
   moment it does; nothing else is assumed on the cone side (§2).
2. `minAvoid` (`x ∉ P` over `minimalPrimes`): genericity/coefficient
   business, stays explicit (§3–§4). Provably independent: the Gap
   witness satisfies diagonality + pointwise nondegeneracy yet kills
   rung-2 regularity.
3. `j.val > 2` steps: need general-`k` unmixedness (`HunmixedGeProp`,
   same crux as Q2 per `UnmixednessAtLengthK` k-uniformity), not Q2's `k = 2`
   output — the §3b master is already stated to consume it (§1
   general-`k` adapter included); only the per-`j` `Fin j.val`
   reindexing span equation remains (finite computation, same pattern
   as `span_prefixPair_rung2`).
4. For the §3c canonical route under a `∀`-closed crux landing: the
   `SuccessiveSMulRegular prefixPair` glue (rung-0/rung-1 data over the
   reindexed pair list — finite `ofFn`-prefix identification).

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `Geometry/UnmixednessAtLengthTwo.lean`: `HunmixedTwoProp` (Q2 output type).
* `Geometry/UnmixednessAtLengthK.lean`: `HunmixedGeProp` (general-`k` type).
* `BridgeToFixedPoint/Rung/UnmixednessRungTwo.lean`: Q2-typed corollaries (read-only shape
  reference; not imported).
* `BridgeToFixedPoint/ConeNoEmbeddedRungs.lean`: `coneNoEmbedded_of_hunmixed`
  (§2 master), `hsucc_bridgeSystem_rung2_diagonal`.
* `BridgeToFixedPoint/R1RegularSection.lean`: `havoid_secForm_of_noEmbedded_of_minAvoid`.
* `BridgeToFixedPoint/ResidualWiring.lean`:
  `secFormAvoidsMinimal_bridgeForms_of_algebraData`.
* `BridgeToFixedPoint/Rung/RungDiagonal.lean`: `hreg_ge1_diagonal_of_ge2narrow`
  (diagonal `hge2` binder, §4 slice target).
* `BridgeToFixedPoint/Rung/RungDiagonalGeneric.lean`: `hreg_ge1_generic_of_ge2narrow`
  (generic `hge2` binder, §4 slice target; genericity unused here).
* `Regularity/Avoid/AvoidanceApply.lean`:
  `ofList_take_eq_span_image`, `UnmixednessAtLengthTwo` register.
* `Regularity/Avoid/PrimeAvoidance.lean`:
  `isSMulRegular_of_forall_notMem_associatedPrimes`.
* `Dimension/RegularSequenceDimDrop.lean`: `span_smul_top`.
* `BridgeToFixedPoint/FixedPointFromBezout.lean`: `shift_add_one`,
  `bridgeSystem` (`mkSystem` by `rfl`-defeq).

Mathlib v4.34.0 (all read-only):

* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `MvPolynomial.isNoetherianRing`
  (`Mathlib/RingTheory/Polynomial/Basic.lean`, instance).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungStepFromUnmixedness

/-! ## §1. Output-to-register adapters (unconditional) -/

/-- Q2's output → register `∀`-shape: `HunmixedTwoProp` (with `[IsPrime]`
instance binders) implies `∀ P ∈ Ass, P ∈ minimalPrimes` (the shape
consumed by `coneNoEmbedded_of_hunmixed`, `avoid_mkSystem_pair`,
`hAss_of_unmixed`, and the `UnmixednessAtLengthTwo` register). The instance is
discharged per-prime via `AssociatedPrimes.mem_iff` (same pattern as
`UnmixednessAtLengthK.hunmixed_ge2_of_hdimEqMin`).
-/
theorem hunmixed_forall_of_hunmixedTwoProp (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes := by
  intro P hP
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact hU P hP

/-- General-`k` analogue: `HunmixedGeProp` → register `∀`-shape (for
`j.val > 2` steps, which need general-`k` unmixedness — same crux as Q2).
-/
theorem hunmixed_forall_of_hunmixedGeProp {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hU : UnmixednessAtLengthK.HunmixedGeProp m K q hsucc J hJ) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes := by
  intro P hP
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact hU P hP

/-- Q2's output folded to the Z2 register `AvoidanceApply.UnmixednessAtLengthTwo`
(definitionally the §1 `∀`-shape).
-/
theorem hunmixedTwo_register_of_hunmixedTwoProp (n : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp (n + 2) K q hsucc J hJ) :
    AvoidanceApply.UnmixednessAtLengthTwo n K J :=
  hunmixed_forall_of_hunmixedTwoProp (n + 2) K q hsucc J hJ hU

#print axioms hunmixed_forall_of_hunmixedTwoProp
#print axioms hunmixed_forall_of_hunmixedGeProp
#print axioms hunmixedTwo_register_of_hunmixedTwoProp

/-! ## §2. Rung-2 cone end-to-end from Q2's output -/

/-- `ConeNoEmbedded` at rung-2 bridge data from Q2's output alone: §2
`coneNoEmbedded_of_hunmixed` fed with the §1 adapter (`bridgeSystem` is
`mkSystem` at bridge data by `rfl`-defeq, as in `ConeNoEmbeddedRungs` §7).
No `HdimEq`, no diagonal/nondegeneracy hypotheses — those live inside
Q2's proof of `hU`.

Conditional on exactly `[hsucc₂, hU]`. -/
theorem coneNoEmbedded_bridgeForms_rung2_of_hunmixedTwoProp (K : Type*)
    [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hsucc₂ : RegularityBridge.SuccessiveSMulRegular (bridgeSystem 2 K c hn))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn) hsucc₂ _ rfl) :
    R1RegularSection.ConeNoEmbedded (statementIndex 2) K (bridgeForms 2 K c hn) :=
  ConeNoEmbeddedRungs.coneNoEmbedded_of_hunmixed (statementIndex 2) K
    (bridgeForms 2 K c hn)
    (hunmixed_forall_of_hunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn) hsucc₂ _ rfl hU)

/-- Rung-2 `havoid` at bridge data from algebra data + Q2's output
(`hF`/`hcut` discharged from algebra data via `ResidualWiring`, as in
`ConeNoEmbeddedRungs` §7).

Conditional on exactly `[hsucc₂, hU]` given algebra data. -/
theorem havoid_secForm_bridgeForms_rung2_of_algebraData_of_hunmixedTwoProp
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (V : Submodule K E) (b : Module.Basis (Fin 2) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hsucc₂ : RegularityBridge.SuccessiveSMulRegular (bridgeSystem 2 K c hn))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn) hsucc₂ _ rfl) :
    ∀ P ∈ associatedPrimes
        (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn))
        (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn)),
      Ideal.Quotient.mk
        (Ideal.span (Set.range (bridgeSystem 2 K c hn)))
        (mkLin (statementIndex 2) K
          (R1RegularSection.secForm (statementIndex 2) K)) ∉ P :=
  R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid (statementIndex 2) K
    (bridgeForms 2 K c hn)
    (coneNoEmbedded_bridgeForms_rung2_of_hunmixedTwoProp K c hn hsucc₂ hU)
    (ResidualWiring.secFormAvoidsMinimal_bridgeForms_of_algebraData K E 2 hn c V b
      hexp hN htower hcomm)

/-- End-to-end `Hres2Inst` pair at rung 2 from consumer algebra data +
`[diagonal, nondegeneracy, Q2-output]`: `hsucc` is the proved
`hsucc_bridgeSystem_rung2_diagonal`; `havoid` is the corollary above.
Mirrors `hres2_pair_rung1_of_algebraData` — rung 2 closes the moment Q2
proves.

Conditional on exactly `[hdiag, hnondeg, hsucc₂, hU]` given algebra data. -/
theorem hres2_pair_rung2_diagonal_of_algebraData_of_hunmixedTwoProp
    (K E : Type*) [Field K]
    [IsAlgClosed K] [NonUnitalNonAssocSemiring E] [Module K E]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (V : Submodule K E) (b : Module.Basis (Fin 2) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hsucc₂ : RegularityBridge.SuccessiveSMulRegular (bridgeSystem 2 K c hn))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 2 + 2) K
      (bridgeSystem 2 K c hn) hsucc₂ _ rfl) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 2 K c hn) ∧
      (∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn))
          (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn)),
        Ideal.Quotient.mk
          (Ideal.span (Set.range (bridgeSystem 2 K c hn)))
          (mkLin (statementIndex 2) K
            (R1RegularSection.secForm (statementIndex 2) K)) ∉ P) := by
  constructor
  · exact ConeNoEmbeddedRungs.hsucc_bridgeSystem_rung2_diagonal K c hn hdiag
      hnondeg
  · exact havoid_secForm_bridgeForms_rung2_of_algebraData_of_hunmixedTwoProp
      K E c hn V b hexp hN htower hcomm hsucc₂ hU

#print axioms coneNoEmbedded_bridgeForms_rung2_of_hunmixedTwoProp
#print axioms havoid_secForm_bridgeForms_rung2_of_algebraData_of_hunmixedTwoProp
#print axioms hres2_pair_rung2_diagonal_of_algebraData_of_hunmixedTwoProp

/-! ## §3. `hge2` step-data masters -/

/-- Regularity from unmixedness + minimal-avoidance (unconditional
reduction at general Noetherian `R`): every `P ∈ Ass(R ⧸ J)` is minimal
(`hunmixed`), hence avoided (`hmin`), hence `x` is regular via
`PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes`.
-/
theorem isSMulRegular_quot_of_hunmixed_of_minAvoid {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) (x : R)
    (hunmixed : ∀ P ∈ associatedPrimes R (R ⧸ J), P ∈ J.minimalPrimes)
    (hmin : ∀ P ∈ J.minimalPrimes, x ∉ P) :
    IsSMulRegular (R ⧸ J) x :=
  PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes x
    (fun P hP => hmin P (hunmixed P hP))

/-- General-`(n, j)` bridge step in the verbatim `hge2` binder shape, from
`[hunmixed, minAvoid]` over the taken-prefix span: `ofList_take` is the
prefix span (`ofList_take_eq_span_image`), `• ⊤` is the span coercion
(`span_smul_top`), and the §3 master closes it. Works at every `j`
(`j.val = 2` fires on Q2's output via §3c; `j.val > 2` on general-`k`
unmixedness via the §1 adapter).

Conditional on exactly `[hunmixed, hmin]`. -/
theorem hreg_bridge_of_hunmixed_of_minAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1))
    (hunmixed : ∀ P ∈ associatedPrimes
      (MvPolynomial (Fin (statementIndex n + 2)) K)
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        Ideal.span (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})),
      P ∈ (Ideal.span
        (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})).minimalPrimes)
    (hmin : ∀ P ∈ (Ideal.span
        (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})).minimalPrimes,
      (bridgeSystem n K c hn) j ∉ P) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  have htake :=
    AvoidanceApply.ofList_take_eq_span_image (bridgeSystem n K c hn) j
  rw [htake, RegularSequenceDimDrop.span_smul_top]
  exact isSMulRegular_quot_of_hunmixed_of_minAvoid _ _ hunmixed hmin

/-- The `j.val = 2` bridge step from Q2's output + a span equation: the
§1 adapter turns `hU` into the register shape, `hJ` transports both
inputs to the taken-prefix span, and the §3b master closes it. Stated at
general `j` (the rung-2 content is `q : Fin 2 → _` + `hJ`).

Conditional on exactly `[hsucc₂, hU, hmin]` given `hJ`. -/
theorem hreg_rung2_bridge_of_hunmixedTwoProp_of_minAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1))
    (q : Fin 2 → MvPolynomial (Fin (statementIndex n + 2)) K)
    (hsucc₂ : RegularityBridge.SuccessiveSMulRegular q)
    (hJ : Ideal.span (Set.range q) =
      Ideal.span (Set.image (bridgeSystem n K c hn) {k | k.val < j.val}))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex n + 2) K q hsucc₂ _ rfl)
    (hmin : ∀ P ∈ (Ideal.span (Set.range q)).minimalPrimes,
      (bridgeSystem n K c hn) j ∉ P) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  have hU' := hunmixed_forall_of_hunmixedTwoProp (statementIndex n + 2) K q
    hsucc₂ _ rfl hU
  rw [hJ] at hU' hmin
  exact hreg_bridge_of_hunmixed_of_minAvoid K n hn c j hU' hmin

/-- Canonical rung-2 prefix pair: the first two `bridgeSystem` equations
reindexed as a `Fin 2` family. Gated on `2 ≤ n` (at `n = 1` the second
index does not exist — and `j.val = 2` is unprovable there anyway). -/
noncomputable def prefixPair (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) (hn2 : 2 ≤ n) :
    Fin 2 → MvPolynomial (Fin (statementIndex n + 2)) K :=
  fun i => bridgeSystem n K c hn ⟨i.val, by
    have hi := i.isLt
    have hs := shift_add_one n hn
    omega⟩

/-- The canonical pair spans the rung-2 taken prefix (unconditional):
`Set.range prefixPair = Set.image bridgeSystem {k | k.val < 2}` by
`Fin 2` case analysis (mirroring `RungRegular`'s `himage`), hence the
span equation closing `hJ` above.
-/
theorem span_prefixPair_rung2 (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 2) :
    Ideal.span (Set.range (prefixPair n K c hn hn2)) =
      Ideal.span (Set.image (bridgeSystem n K c hn) {k | k.val < j.val}) := by
  congr 1
  rw [hj]
  ext y
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨i.val, ?_⟩, ?_, rfl⟩
    · have hi := i.isLt
      have hs := shift_add_one n hn
      omega
    · exact i.isLt
  · rintro ⟨k, hk, rfl⟩
    by_cases hk0 : k.val = 0
    · refine ⟨⟨0, by decide⟩, ?_⟩
      have ek : k = ⟨0, by
          have hs := shift_add_one n hn
          omega⟩ := Fin.ext hk0
      rw [ek]
      rfl
    · have hk1 : k.val = 1 := by omega
      refine ⟨⟨1, by decide⟩, ?_⟩
      have ek : k = ⟨1, by
          have hs := shift_add_one n hn
          omega⟩ := Fin.ext hk1
      rw [ek]
      rfl

/-- The `j.val = 2` bridge step from Q2's output over the canonical pair
+ minimal-avoidance: §3c composed with the §3c span equation — zero
further glue once per-`n` `k = 2` unmixedness proves.

Conditional on exactly `[hsucc₂, hU, hmin]`. -/
theorem hreg_rung2_bridge_of_hunmixedTwoProp_canonical (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 2)
    (hsucc₂ : RegularityBridge.SuccessiveSMulRegular (prefixPair n K c hn hn2))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex n + 2) K
      (prefixPair n K c hn hn2) hsucc₂ _ rfl)
    (hmin : ∀ P ∈
      (Ideal.span (Set.range (prefixPair n K c hn hn2))).minimalPrimes,
      (bridgeSystem n K c hn) j ∉ P) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) :=
  hreg_rung2_bridge_of_hunmixedTwoProp_of_minAvoid K n hn c j
    (prefixPair n K c hn hn2) hsucc₂
    (span_prefixPair_rung2 K n hn hn2 c j hj) hU hmin

#print axioms isSMulRegular_quot_of_hunmixed_of_minAvoid
#print axioms hreg_bridge_of_hunmixed_of_minAvoid
#print axioms hreg_rung2_bridge_of_hunmixedTwoProp_of_minAvoid
#print axioms prefixPair
#print axioms span_prefixPair_rung2
#print axioms hreg_rung2_bridge_of_hunmixedTwoProp_canonical

/-! ## §4. `∀`-closed rung-2 slice of the `hge2narrow` forms -/

/-- The `j.val = 2` slice of both `hge2narrow` `∀`-forms (diagonal
`RungDiagonal.hreg_ge1_diagonal_of_ge2narrow` + generic
`RungDiagonalGeneric.hreg_ge1_generic_of_ge2narrow`, whose genericity is
unused here) from `∀`-closed `[hunmixed, minAvoid]` over taken-prefix
spans: the §3b master pointwise. Each `hunmixed` instance is Q2's output
via the §1 adapter; each `hmin` instance is the genericity residual.

Conditional on exactly `[hunmixed, hmin]`. -/
theorem hreg_rung2slice_of_forall_hunmixed_of_forall_minAvoid (K : Type*)
    [Field K]
    (hunmixed : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c → ∀ j : Fin (statementIndex n + 1),
      j.val = 2 →
        ∀ P ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            Ideal.span (Set.image (bridgeSystem n K c hn)
              {k | k.val < j.val})),
        P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})).minimalPrimes)
    (hmin : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c → ∀ j : Fin (statementIndex n + 1),
      j.val = 2 →
        ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P) :
    ∀ (n : ℕ) (hn : 0 < n), 3 ≤ n →
      ∀ (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c →
      ∀ j : Fin (statementIndex n + 1), j.val = 2 →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
            (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j) := by
  intro n hn hn3 c hdiag j hj
  exact hreg_bridge_of_hunmixed_of_minAvoid K n hn c j
    (hunmixed n hn c hdiag j hj) (hmin n hn c hdiag j hj)

#print axioms hreg_rung2slice_of_forall_hunmixed_of_forall_minAvoid

end RungStepFromUnmixedness
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
