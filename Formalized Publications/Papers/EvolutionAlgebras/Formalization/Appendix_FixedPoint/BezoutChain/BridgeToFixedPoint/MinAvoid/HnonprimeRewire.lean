/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.A3aHeadlineRefactor
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.RealizedMinAvoid
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungOneClose
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MasterAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge

/-!
# all-`n` hnonprime + M-O1a rewire

Two closers compose into the per-instance
`MinAvoidNonprimeSpec` at every `n`, horth-free:

* `n ≤ 2`: `RealizedMinAvoid.minAvoidNonprimeSpec_of_algebraData_of_le2`
  (B5, vacuous — needs only `[Field K]`).
* `n ≥ 3`: `A3aHeadlineRefactor.minAvoidNonprimeSpec_unhorth_of_algebraData`
  (C4, M-O1d — needs `[IsAlgClosed K]`).

`minAvoidNonprimeSpec_of_algebraData` is the case split, unconditional
given algebra data + `[IsAlgClosed K]`. It feeds:

* Task 1 (R4c/general-`n`): `FirstRegFiring` (companion
  Regularity leaf) discharges the `[hnonprime]`-only FirstReg-fired R4c
  legs to fully unconditional `Hres2Inst`.
* Task 2 (A3/A4 rewire): `hsucc_of_unhorthRung1_of_alloc_of_minAvoid`
  reroutes the M1 consumer shape off the false rung-1 local gates
  (`HdiagRung1`/`HsuppRung1`, false at general `c`) onto the closed M-O1a
  unhorth leg + the master, keeping `[halloc, hmin]`; and
  `hsucc_bridgeSystem_unconditional` fires those too (halloc via the B2
  FirstReg fire, `hmin` via the iff + the all-`n` closer) for a
  fully unconditional general-`n` `hsucc` given algebra data +
  `[IsAlgClosed K]`.

R4b/R4 are not rewired here: both are documented valid but inapplicable
(R4b's R2/R3 inputs are bare-`∀c`, the `hnonprime` form refuted;
R4's route-(a) `hker` is false at `dim ≥ 2`). R4c already is the
rewired R4b (→ + per-instance re-scoping); R4b/R4 stay as
bookkeeping, untouched.

Status: all three conclusions unconditional (resp. `[halloc, hmin]`-gated
for the M1 rewire) given algebra data + `[IsAlgClosed K]`.
`[Infinite K]` (halloc fire) resolves by typeclass from `[IsAlgClosed K]`.

-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HnonprimeRewire

open scoped BigOperators

/-- All-`n` per-instance `MinAvoidNonprimeSpec`, horth-free: `n ≤ 2` by
the B5 vacuous closer, `n ≥ 3` by the C4 M-O1d closer.
-/
theorem minAvoidNonprimeSpec_of_algebraData
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn := by
  by_cases h3 : 3 ≤ n
  · exact A3aHeadlineRefactor.minAvoidNonprimeSpec_unhorth_of_algebraData
      K E n hn h3 c V b hexp hN htower hcomm
  · have hn2 : n ≤ 2 := by omega
    exact RealizedMinAvoid.minAvoidNonprimeSpec_of_algebraData_of_le2
      K E n hn hn2 c V b hexp hN htower hcomm

#print axioms minAvoidNonprimeSpec_of_algebraData

/-- M1 rewire: full `hsucc` from `[per-stage allocator,
`MinAvoidAllSpec`]` with the rung-1 step fed by M-O1a (zero `horth`,
zero local gates) through the master. Drop-in replacement for
the routed M1 consumer shape at general `n`.

Conditional on exactly `[halloc, hmin]` given algebra data +
`[IsAlgClosed K]`. -/
theorem hsucc_of_unhorthRung1_of_alloc_of_minAvoid
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hmin : MinAvoidJoin.MinAvoidAllSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_rung1step_of_alloc_of_minAvoidSpec
    K n hn c
    (RungOneClose.rung1step_unhorth_of_algebraData
      K E V n hn c b hexp hN htower hcomm)
    halloc hmin

#print axioms hsucc_of_unhorthRung1_of_alloc_of_minAvoid

/-- Full `hsucc` at general `n`, horth-free and gate-free: the M1
rewire with `halloc` fired (B2 FirstReg fire) and `hmin` closed (the
iff + the all-`n` closer above).
-/
theorem hsucc_bridgeSystem_unconditional
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  hsucc_of_unhorthRung1_of_alloc_of_minAvoid
    K E n hn c V b hexp hN htower hcomm
    (KoszulHdimEqHallocFirstRegFire.halloc_all_stages_unconditional n K c hn)
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K c hn).mpr
      (minAvoidNonprimeSpec_of_algebraData K E n hn c V b hexp hN htower hcomm))

#print axioms hsucc_bridgeSystem_unconditional

end HnonprimeRewire
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
