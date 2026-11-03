/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighDimGe3Attack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoJointClose
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Geometry.K2UnmixednessEndgame
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthK
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssRungFeeds
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ConeNoEmbeddedRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring

/-!
# J9: final joint assembly (conditional masters + closure map)

Pure-integration leaf: end-to-end masters for every downstream consumer
(joint-9, rb-1, `hkerMin`, `hmultMin`, `hdimEqMin`, `hdepth`, `hunmixed`,
`heightDrop`, `hsucc`-rungs, `hres2`) on the input set
`[d2-ring, ge3-ring, hdich]`, each taken as an explicit SPEC hypothesis
in its exact stated shape. Sibling outcomes are not
available, so conditional form is required throughout; an
unconditional close of any input is then a mechanical substitution
(see the §10 closure map).

no new math: every proof is one `exact` against a proved master (or a
verbatim replay of the `BabyAuslanderBuchsbaum` per-prime depth argument at the weaker
`HkerMin` input, which the `grlift` family already satisfies).

## Inputs (SPEC shapes)

* `d2`: `WitnessHighAttack.HnoHomRelHighD2AtAss` — the High-side face of
  the D2 ring. Any other D2-ring face converts to it unconditionally
  via the proved ring iffs (see §10).
* `ge3`: `WitnessHighAttack.HnoHomRelHighMinGe3AtAss` — the `Ge3` slice.
* `hdich`: `HdichRung1` (§0 below) — the rung-1 dichotomy disjunct,
  verbatim the `rung1step_of_hdich` binder (`AssRungFeeds`).
* `hass`: `MinAvoidRungs.AssAvoidRung` per rung `j ≥ 2` — the rung-`≥ 2`
  steps. Not in the triple: it is per-instance-`c` step data (the
  universal form is refuted, t3-as-stated), so every `hsucc`/`hres2`
  master carries it as a fourth explicit input, with exact status.

## Layering note

This file lives in `Regularity/` but imports `BridgeToFixedPoint/` masters. This is
a deliberate leaf exception: nothing imports this file, so the import
DAG stays acyclic; the alternative (restating Bridge masters) would
duplicate, not integrate. All `Bridge` use sites are single-`exact`
consumers.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace JointAssembly

/-! ## §0. SPEC inputs: the `hdich` rung-1 shape

`d2`/`ge3` reuse the existing SPEC defs (`WitnessHighAttack`
`HnoHomRelHighD2AtAss` / `HnoHomRelHighMinGe3AtAss`); only the
dichotomy disjunct needs a named address here, so the `hsucc`/`hres2`
masters take it as one hypothesis. -/

/-- Rung-1 dichotomy disjunct (`hdich`, `HassRung` shape): for every
rung-1 index, either `X₀` does not divide the rung-0 bridge form or
the form factors through `X₀` with nonzero cross relation. Verbatim
the `rung1step_of_hdich` / `hsucc_of_hdich_of_hdimEq_of_assAvoid`
binder; `abbrev` (reducible) so it feeds those masters by `exact`.

Specification (Prop address for the rung-1 nondegeneracy hypothesis). -/
abbrev HdichRung1 (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ k : Fin (statementIndex n + 1), k.val = 1 →
    (¬ (MvPolynomial.X
          (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
            Fin (statementIndex n + 1)) :
          MvPolynomial (Fin (statementIndex n + 1)) K) ∣
          bridgeForms n K c hn
            ⟨0, Nat.zero_lt_succ (statementIndex n)⟩) ∨
      (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
        bridgeForms n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ =
          MvPolynomial.X ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ *
            L0 ∧
        MvPolynomial.X (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
          Fin (statementIndex n + 1)) * bridgeForms n K c hn k -
          MvPolynomial.X k * bridgeForms n K c hn
            ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ ≠ 0)

/-! ## §1. Uniform masters on `[d2, ge3]`: joint-9 and crux projections

Each master consumes both inputs: `hd2` supplies the `d = 2` slice of
the `Ge2` joint, `hge3` the `d ≥ 3` slice (`highAttack_full_of_d2_ge3`
needs each slice on its own domain — neither input covers the other's
embdim range). Minimality is by consumption: delete either input and
the cited master no longer applies. -/

/-- End-to-end uniform 9-tuple on `[d2, ge3]`: all nine crux forms in
one tuple (the joint feeds the narrowed joint).

Consumes: `hd2` (§2 slice), `hge3` (§3 slice).

Conditional on exactly `[hd2, hge3]`. -/
theorem final_joint9_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J ∧ UnmixednessAtLengthTwo.HkerMinAtAss m K J ∧
      GradedDimEq.HgrDimLowerMinAtAss m K J ∧
      HighRelationsLowerBound.HhleMinAtAss m K J ∧
      UnmixednessAtLengthTwo.HdimEqMinAtAss m K J ∧
      UnmixednessAtLengthTwo.HmultMinAtAss m K J ∧
      DimensionToMultiplicity.HgrDimEqMinAtAss m K J ∧
      UnmixednessAtLengthTwo.HdimGrMinAtAss m K J ∧
      WitnessKernelCrux.HexistsKerMinAtAss m K J :=
  HighDimGe3Attack.highGe3_joint9_of_d2_ge3 m K J hd2 hge3

#print axioms final_joint9_of_d2_ge3

/-- `HkerMinAtAss` from `[d2, ge3]` (uniform-joint projection).

Consumes: `hd2` + `hge3` (both feed the joint).

Conditional on exactly `[hd2, hge3]`. -/
theorem final_hkerMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J) :
    UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  HighDimGe3Attack.highGe3_hkerMin_of_d2_ge3 m K J hd2 hge3

#print axioms final_hkerMin_of_d2_ge3

/-- `HmultMinAtAss` from `[d2, ge3]` (uniform-joint projection).

Consumes: `hd2` + `hge3` (both feed the joint).

Conditional on exactly `[hd2, hge3]`. -/
theorem final_hmultMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  HighDimGe3Attack.highGe3_hmultMin_of_d2_ge3 m K J hd2 hge3

#print axioms final_hmultMin_of_d2_ge3

/-- `HdimEqMinAtAss` from `[d2, ge3]` (uniform-joint projection; the
hub feeding rb-1, unmixedness, and the rung-`≥ 2` supply chain).

Consumes: `hd2` + `hge3` (both feed the joint).

Conditional on exactly `[hd2, hge3]`. -/
theorem final_hdimEqMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  HighDimGe3Attack.highGe3_hdimEqMin_of_d2_ge3 m K J hd2 hge3

#print axioms final_hdimEqMin_of_d2_ge3

/-! ## §2. Rb-1 on `[d2, ge3]`

The `HdimEqMin` hub feeds the uniform `hunmixedTwo_of_*` consumer;
`hsucc`/`hJ` are the ambient pair data (not conditional inputs). -/

/-- Rb-1 (`HunmixedTwoProp`) from the two slices.

Consumes: `hd2` + `hge3` (via the `HdimEqMin` hub).

Conditional on exactly `[hd2, hge3]` (+ explicit `hsucc`, `hJ`). -/
theorem final_hunmixedTwo_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  DimTwoJointClose.jointClose_hunmixedTwo_of_d2_ge3 m K q hsucc J hJ
    hd2 hge3

#print axioms final_hunmixedTwo_of_d2_ge3

/-! ## §3. `hdepth` on `[d2, ge3]`

`BabyABPair.hdepth_of_hker` needs the over-strong universal
`HkerAtAss` (all families), but its per-prime proof only ever applies
the kernel hypothesis at the `grlift` s.o.p. family — which is minimal
(`grlift_sop_exists` returns `d = spanFinrank`). Hence the same proof
runs on the `[d2, ge3]`-supplied `HkerMinAtAss`. No new math: identical
case split (`d = 0` / `d ≥ 1`), identical suppliers. -/

/-- Per-prime `DepthEqDimAt` from the two slices: the `BabyAuslanderBuchsbaum`
per-prime argument replayed at the minimal kernel input.

Consumes: `hd2` + `hge3` (via the `HkerMin` projection).

Conditional on exactly `[hd2, hge3]`. -/
theorem final_hdepth_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K Q := by
  have hker := final_hkerMin_of_d2_ge3 m K J hd2 hge3
  obtain ⟨d, g, hgen, hd⟩ := GradedLift.grlift_sop_exists Q
  by_cases hd0 : d = 0
  · subst hd0
    exact ReesAssembly.depthEqDimAt_zero_of_sop m K Q g hgen
  · have hd1 : 1 ≤ d := by omega
    exact ReesAssembly.depthEqDimAt_of_r2Reduced m K Q
      (BabyABPair.extBasisULift (Localization.AtPrime Q) d) g hgen hd
      (hker Q hQ g hgen hd) hd1

#print axioms final_hdepth_of_d2_ge3

/-! ## §4. `hunmixed` / `heightDrop` on `[d2, ge3]`

The gated `k ≥ 2` unmixedness shape and the `k = 2` height-drop
residual, both via the §1 hubs. -/

/-- Gated `k ≥ 2` unmixedness from the two slices (the exact
`2 ≤ k → ∀ P ∈ Ass, P ∈ minimalPrimes` shape consumed by
`AvoidanceApply` / rung-`≥ 2` steps).

Consumes: `hd2` + `hge3` (via the `HdimEqMin` hub).

Conditional on exactly `[hd2, hge3]` (+ explicit `hsucc`, `hJ`). -/
theorem final_hunmixed_ge2_of_d2_ge3 {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J) :
    2 ≤ k → ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes :=
  UnmixednessAtLengthK.hunmixed_ge2_of_hdimEqMin m K q hsucc J hJ
    (final_hdimEqMin_of_d2_ge3 m K J hd2 hge3)

#print axioms final_hunmixed_ge2_of_d2_ge3

/-- `k = 2` height-drop residual from the two slices (rb-1 across the
`UnmixednessAtLengthTwo ↔ HeightDrop` equivalence).

Consumes: `hd2` + `hge3` (via the rb-1 master).

Conditional on exactly `[hd2, hge3]` (+ explicit `hsucc`, `hJ`). -/
theorem final_heightDrop_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hd2 : WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J) :
    HeightDrop.HeightDropResidualPair m K q hsucc J hJ :=
  (UnmixednessAtLengthTwo.hunmixed_two_iff_heightDropTwo m K q hsucc J hJ).mp
    (final_hunmixedTwo_of_d2_ge3 m K q hsucc J hJ hd2 hge3)

#print axioms final_heightDrop_of_d2_ge3

/-! ## §5. `hsucc`-rungs: rung 1 from `hdich`, rungs `≥ 2` from `d2`/`ge3`/`hass`

The `MinSubsetAss` master needs `[rung-1 step, ∀-HdimEq,
∀-assAvoid]`: rung 1 is discharged by `hdich` (`rung1step_of_hdich`),
each rung-`≥ 2` `HdimEqMin` by per-stage `[d2, ge3]`, and the
rung-`≥ 2` avoidance stays an explicit fourth input (`hass` = the
steps themselves; the universal form is refuted, so it cannot be
derived from the triple). -/

/-- Full `hsucc` at bridge data from per-rung `[hdich, d2, ge3, hass]`
(no `hmin`, no `hsub` — both discharged inside).

Consumes: `hdich` (rung-1 step only); `hd2`/`hge3` (per-stage
`HdimEqMin` only); `hass` (rung-`≥ 2` avoidance only). Minimal: each
input feeds a disjoint leg.

Conditional on exactly `[hdich, d2∀, ge3∀, hass∀]`. -/
theorem final_hsucc_of_hdich_of_d2_ge3_of_hass (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdich : HdichRung1 n K c hn)
    (hd2 : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      WitnessHighAttack.HnoHomRelHighD2AtAss (statementIndex n + 2) K
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})))
    (hge3 : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      WitnessHighAttack.HnoHomRelHighMinGe3AtAss (statementIndex n + 2) K
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})))
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  AssRungFeeds.hsucc_of_hdich_of_hdimEq_of_assAvoid K n hn c hdich
    (fun j hj => DimTwoJointClose.jointClose_hdimEqMin_of_d2_ge3
      _ _ _ (hd2 j hj) (hge3 j hj)) hass

#print axioms final_hsucc_of_hdich_of_d2_ge3_of_hass

/-- Full `hsucc` at `n = 2` from `hdich` alone: both rung-`≥ 2`
binders (`HdimEq`, `hass`) are vacuous (`statementIndex 2 + 1 = 2`,
so `2 ≤ j.val` is impossible).

Consumes: `hdich` only. Minimal: the single-input close.

Conditional on exactly `[hdich]`. -/
theorem final_hsucc_rung2_of_hdich (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdich : HdichRung1 2 K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 2 K c hn) :=
  final_hsucc_of_hdich_of_d2_ge3_of_hass K 2 hn c hdich
    (fun j hj => by exfalso; have hlt2 : j.val < 2 := j.isLt; omega)
    (fun j hj => by exfalso; have hlt2 : j.val < 2 := j.isLt; omega)
    (fun j hj => by exfalso; have hlt2 : j.val < 2 := j.isLt; omega)

#print axioms final_hsucc_rung2_of_hdich

/-! ## §6. Full-closure master: `Hres2Inst` (the FixedPoint residual)

The theorem turning any complete discharge into the paper results:
`hsucc` per `(n, c)` is the §5 master; `havoid` per `(n, c)` is the
`ConeNoEmbeddedRungs` §5 master on `[hsucc, HdimEqMin-at-full-span]`
(whose `secFormAvoidsMinimal` leg closes from algebra data alone).
`d2`/`ge3` enter in ∀-closed form (consumed at every stage ideal and
every full-span ideal); `hdich`/`hass` universally over `(n, c)` /
rungs. `IsAlgClosed` is the havoid master's explicit requirement. -/

/-- The FixedPoint 2-residual in instance-data form from the complete
discharge: universal `[d2, ge3, hdich, hass]` + algebra data.

Consumes: `hd2`/`hge3` (every `HdimEqMin`: per-rung for `hsucc`,
at-full-span for `havoid`); `hdich` (every rung-1 step); `hass`
(every rung-`≥ 2` avoidance); `hN`/`htower`/`hcomm` (the havoid
minimal-avoidance leg via algebra data).

Conditional on exactly
`[d2∀, ge3∀, hdich∀, hass∀]` given algebra data. -/
theorem final_hres2Inst_of_all (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hd2 : ∀ (m : ℕ) (J : Ideal (MvPolynomial (Fin m) K)),
      WitnessHighAttack.HnoHomRelHighD2AtAss m K J)
    (hge3 : ∀ (m : ℕ) (J : Ideal (MvPolynomial (Fin m) K)),
      WitnessHighAttack.HnoHomRelHighMinGe3AtAss m K J)
    (hdich : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      HdichRung1 n K c hn)
    (hass : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    ResidualWiring.Hres2Inst K E V := by
  intro n hn c b hexp
  have hsucc :=
    final_hsucc_of_hdich_of_d2_ge3_of_hass K n hn c (hdich n hn c)
      (fun j _ => hd2 (statementIndex n + 2)
        (Ideal.span (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
      (fun j _ => hge3 (statementIndex n + 2)
        (Ideal.span (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
      (fun j hj => hass n hn c j hj)
  have hdimEq := DimTwoJointClose.jointClose_hdimEqMin_of_d2_ge3
    _ _ _ (hd2 (statementIndex n + 2)
      (Ideal.span (Set.range (bridgeSystem n K c hn))))
    (hge3 (statementIndex n + 2)
      (Ideal.span (Set.range (bridgeSystem n K c hn))))
  refine ⟨hsucc, ?_⟩
  exact ConeNoEmbeddedRungs.havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin
    K E n hn c V b hexp hN htower hcomm hsucc hdimEq

#print axioms final_hres2Inst_of_all

/-! ## §7. Closure map (doc-only register)

For each of the 3 inputs (+ the fourth), exactly which
masters fire when it closes. A future unconditional close = mechanical
substitution at the listed application sites; no proof step changes.

### When `d2` closes (any D2-ring face, unconditionally)

Ring-face converters (all unconditional, proved): any face reaches
the High-D2 SPEC consumed above —
`hwitD2_iff_hkerD2`, `hdimGrD2_iff_hkerD2`, `hhleD2_iff_hkerD2`
(`WitnessKernelDimTwo` §2 / `HighAttack` §2), `highD2Close` gated iff
(`DimTwoEndToEnd`:379), `jointClose_hmultD2_iff_hkerD2`
(`DimTwoJointClose` §2), `highD2Close_highD2_of_sopGrLowerGated`,
`highAttack_highD2_of_hkerD2`, `jointClose_d2joint_of_grExact`
(collapsed HS leg). Narrowest named face: `PrimeNoIrredD2`
(`HprimeNoIrredD2AtAss`) — convert via the CruxD2 iff chain.
Masters fired (all still need their `ge3` leg): `final_joint9`,
`final_hkerMin`, `final_hmultMin`, `final_hdimEqMin`,
`final_hunmixedTwo`, `final_hdepth`, `final_hunmixed_ge2`,
`final_heightDrop` (each at `hd2 := <closed face converted>`),
plus the per-rung `hd2` legs of `final_hsucc_*` and the ∀-closed
`hd2` leg of `final_hres2Inst_of_all`.

### When `ge3` closes (unconditionally)

No converter needed: `HnoHomRelHighMinGe3AtAss` is consumed verbatim.
Masters fired (all still need their `d2` leg): same eight §1–§4
masters at `hge3 := <closed>`, plus the per-rung `hge3` legs of
`final_hsucc_*` and the ∀-closed `hge3` leg of `final_hres2Inst`.

### When `hdich` closes (per `(n, c)` or universally)

No converter needed: `HdichRung1` is consumed verbatim (reducible).
Masters fired: `final_hsucc_of_hdich_of_d2_ge3_of_hass` at
`hdich := <closed>` (still needs per-rung `d2`/`ge3`/`hass`);
`final_hsucc_rung2_of_hdich` closes unconditionally (its only input);
the ∀-closed `hdich` leg of `final_hres2Inst_of_all`.

### The fourth input: `hass` (rung-`≥ 2` steps)

Per-instance-`c` data, not closable universally (t3-as-stated
refuted). Fires: the `hass` legs of `final_hsucc_*` (general-`n`)
and `final_hres2Inst_of_all`. Reduction available per rung:
`hass ⟺ step` (`MinAvoidRungs.step_span_iff_assAvoidRung`),
`step ⇐ [hunmixed, minAvoid]`
(`RungStepFromUnmixedness.hreg_bridge_of_hunmixed_of_minAvoid`) with
`hunmixed ⇐ [d2, ge3]` (`final_hunmixed_ge2_of_d2_ge3`) — so per
instance, `hass` reduces to rung-wise minimal avoidance.

### Full discharge ⟹ paper results

`[d2∀, ge3∀, hdich∀, hass∀]` + algebra data closes `Hres2Inst`
(`final_hres2Inst_of_all`), the exact residual consumed by the §10
master (`SpineAdapter.fixedPoint_of_idempotent_of_bezout`), hence
`A_FixedPoint.lean`, `IdempotentIff.backward`, and `SolvableCorollary`.
No other conditional input exists downstream of this file. -/

end JointAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
