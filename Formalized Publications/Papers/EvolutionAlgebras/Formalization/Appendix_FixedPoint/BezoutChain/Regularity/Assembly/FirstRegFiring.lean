/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.GradeKeepsMaximalOutOfAss
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.Hres2PlugCorollary
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.HnonprimeRewire
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
/-!
# R4c-feed FirstReg firing (B4)

The `FirstReg` apex is closed
(`FirstRegAssemble.firstReg_unconditional`), so the
`[FirstReg]`-only R4c feeders fire with `hFR` discharged:

* `hres2Gated_of_nonprimeMin`: the ungated per-basis `(hsucc, havoid)`
  conclusion on `[hnonprime]`-only.
* `hres2Inst_of_nonprimeMin`: the §10-master `hres2` input
  (`Hres2Inst`) on `[hnonprime]`-only.

The per-instance `hnonprime` (`MinAvoidNonprimeSpec`) is preserved
verbatim by design (R4c keeps it as a hypothesis, covering `n < 3`
uniformly; closed for `n ≤ 2` by
`RealizedMinAvoid.minAvoidNonprimeSpec_of_algebraData_of_le2` and
for `n ≥ 3` horth-free by
`A3aHeadlineRefactor.minAvoidNonprimeSpec_unhorth_of_algebraData`).

Conditional on exactly `[hnonprime]` given algebra data +
standing `[IsAlgClosed K]` (universe `uK` diagonal, as the
parent).

-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulFinalR4cFirstRegFire

open scoped BigOperators

universe uK

/-- R4c ungated per-basis `(hsucc, havoid)` on `[hnonprime]`-only:
`hres2Gated_of_fr_of_nonprimeMin` with `hFR` discharged by
`firstReg_unconditional.{uK,uK}`.

Conditional on exactly `[hnonprime]` given algebra data +
standing `[IsAlgClosed K]`. -/
theorem hres2Gated_of_nonprimeMin
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hnonprime : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E)
        = ∑ k, c i j k • (b k : E)),
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E)),
      RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
      (∀ P ∈ associatedPrimes
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
          Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
            (mkLin (statementIndex n) K
              (R1RegularSection.secForm (statementIndex n) K)) ∉ P) :=
  KoszulFinalR4cHdepthFeedC3aDischarge.hres2Gated_of_fr_of_nonprimeMin
    K E V hN htower hcomm
    FirstRegAssemble.firstReg_unconditional.{uK, uK}
    hnonprime

#print axioms hres2Gated_of_nonprimeMin

/-- E3-inherited §10-master `hres2` input (`Hres2Inst`) on
`[hnonprime]`-only: `hres2Inst_of_fr_of_nonprimeMin` with `hFR`
discharged by `firstReg_unconditional.{uK,uK}`.

Conditional on exactly `[hnonprime]` given algebra data +
standing `[IsAlgClosed K]`. -/
theorem hres2Inst_of_nonprimeMin
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hnonprime : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E)
        = ∑ k, c i j k • (b k : E)),
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ResidualWiring.Hres2Inst K E V :=
  KoszulFinalR4cHdepthFeedC3aDischarge.hres2Inst_of_fr_of_nonprimeMin
    K E V hN htower hcomm
    FirstRegAssemble.firstReg_unconditional.{uK, uK}
    hnonprime

#print axioms hres2Inst_of_nonprimeMin

end KoszulFinalR4cFirstRegFire
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# R4c hnonprime firing — unconditional `Hres2Inst`

`KoszulFinalR4cFirstRegFire` left R4c
conditional-exact on per-instance `[hnonprime]` (covering `n < 3`
uniformly by design). That residual is now closed at every `n` by the
companion Bridge leaf
(`HnonprimeRewire.minAvoidNonprimeSpec_of_algebraData`:
B5 `n ≤ 2` + C4 `n ≥ 3`, horth-free), so both FirstReg-fired legs fire
end to end:

* `hres2Gated_unconditional`: the ungated per-basis `(hsucc, havoid)`
  conclusion, hypothesis-free given algebra data + `[IsAlgClosed K]`.
* `hres2Inst_unconditional`: the §10-master `hres2` input
  (`Hres2Inst`), hypothesis-free given algebra data + `[IsAlgClosed K]`.

Status: both conclusions unconditional given algebra data + standing
`[IsAlgClosed K]` (universe `uK` diagonal, as the FirstRegFire parent).

-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FirstRegFiring

open scoped BigOperators

universe uK

/-- R4c ungated per-basis `(hsucc, havoid)` unconditional:
`hres2Gated_of_nonprimeMin` with `hnonprime` discharged by the all-`n`
closer.
-/
theorem hres2Gated_unconditional
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E)),
      RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
      (∀ P ∈ associatedPrimes
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
          Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
            (mkLin (statementIndex n) K
              (R1RegularSection.secForm (statementIndex n) K)) ∉ P) :=
  KoszulFinalR4cFirstRegFire.hres2Gated_of_nonprimeMin
    K E V hN htower hcomm
    (fun n hn c b hexp =>
      HnonprimeRewire.minAvoidNonprimeSpec_of_algebraData
        K E n hn c V b hexp hN htower hcomm)

#print axioms hres2Gated_unconditional

/-- The §10-master `hres2` input (`Hres2Inst`) unconditional:
`hres2Inst_of_nonprimeMin` with `hnonprime` discharged by the all-`n`
closer.
-/
theorem hres2Inst_unconditional
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    ResidualWiring.Hres2Inst K E V :=
  KoszulFinalR4cFirstRegFire.hres2Inst_of_nonprimeMin
    K E V hN htower hcomm
    (fun n hn c b hexp =>
      HnonprimeRewire.minAvoidNonprimeSpec_of_algebraData
        K E n hn c V b hexp hN htower hcomm)

#print axioms hres2Inst_unconditional

end FirstRegFiring
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
