/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SpineAdapter
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.FirstRegFiring
/-!
# Fixed-point backend data bundle

This file holds the Bézout-side justification payload of the projective
fixed-point principle (`EvolutionAlgebras.fixedPoint_of_idempotent`, paper
Theorem `idempotentiff`, backward direction). The paper-shaped wrapper
discharges this payload internally through
`FixedPointBackend.hres2_unconditional`; the residual is not a hypothesis
of the public theorem.

Contents: `HRes2` (the 2-residual: full-family regular sequence
plus specific-form section avoidance, per `(n, c)` realized on `V`),
the bundle `FixedPointData` (exactly `HRes2`), and the detailed principle
`fixedPoint_of_idempotent_of_data` (the former `fixedPoint_of_idempotent`
statement, proved by direct application of the §10 spine-adapter master).
The paper-shaped wrapper lives in `A_FixedPoint.lean`.

## Main results

* `FixedPointData`: the one-hypothesis backend
  bundle.
* `EvolutionAlgebras.fixedPoint_of_idempotent_of_data`: the detailed principle
  (explicit tower/comm/residual hypotheses).
-/

namespace EvolutionAlgebras

variable (K E : Type*) [Field K] [NonUnitalNonAssocSemiring E] [Module K E]

namespace Appendix_FixedPoint.BezoutChain
/-- The 2-residual at `V` (U5 narrowing, ungated): for every
`(n, c)` realized by a basis `(b, hexp)` on `V`, the bridge system is
successively `SMul`-regular and the R1 section form avoids every
associated prime of the cone quotient. This is the
Bézout-chain conclusion in the explicit form used by the detailed
`fixedPoint_of_idempotent_of_data`; `FixedPointBackend.hres2_unconditional`
below discharges it from the algebra data. -/
def HRes2 (V : Submodule K E) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (b : Module.Basis (Fin n) K V)
    (_hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E)),
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
    (∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K
            (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K
            (bridgeSystem n K c hn)),
        Ideal.Quotient.mk
          (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P)

/-- The fixed-point backend bundle at `V`: exactly the 2-residual.
This is the residual payload of the detailed
`fixedPoint_of_idempotent_of_data`; the paper-shaped
`fixedPoint_of_idempotent` discharges it internally through
`FixedPointBackend.hres2_unconditional`. -/
def FixedPointData (V : Submodule K E) : Prop :=
  HRes2 K E V

end Appendix_FixedPoint.BezoutChain
/-- Detailed projective fixed-point principle (former
`fixedPoint_of_idempotent` statement, kept verbatim): on an idempotent
submodule `V` with `N(V) = {0}` over an algebraically closed field, the
squaring map has a projective fixed point. Explicit tower/comm context plus
the 2-residual instance-data form. Proved from the Bézout spine-adapter master
(`Appendix_FixedPoint.BezoutChain.SpineAdapter.fixedPoint_of_idempotent_of_bezout`, §10). The
paper-shaped wrapper is `fixedPoint_of_idempotent` in `A_FixedPoint.lean`. -/
theorem fixedPoint_of_idempotent_of_data (V : Submodule K E) [IsAlgClosed K]
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hres2 : Appendix_FixedPoint.BezoutChain.HRes2 K E V) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x :=
  Appendix_FixedPoint.BezoutChain.SpineAdapter.fixedPoint_of_idempotent_of_bezout
    K E V hfin hV hN hneV htower hcomm hres2

#print axioms fixedPoint_of_idempotent_of_data

end EvolutionAlgebras

/-!
# unconditional `HRes2` — discharging the `hdata` bundle

The §10-master `hres2` input (`ResidualWiring.Hres2Inst`) is unconditional given
consumer algebra data + `[IsAlgClosed K]`
(`FirstRegFiring.hres2Inst_unconditional`, task 1: R4c
fired end to end, `hnonprime` closed at every `n` by
`HnonprimeRewire.minAvoidNonprimeSpec_of_algebraData`).
`ResidualWiring.Hres2Inst` (`ResidualWiring.lean`) is token-identical to
`Appendix_FixedPoint.BezoutChain.HRes2` (`FixedPointBackend.lean`), which is
`Appendix_FixedPoint.BezoutChain.FixedPointData`
(the `hdata` bundle) — so the bundle discharges by `exact` (defeq through the
two definitions, no proof content).

This file is the single discharge point: `fixedPoint_of_idempotent`
(`A_FixedPoint.lean`) feeds this into `fixedPoint_of_idempotent_of_data` and
drops `hdata` from its statement.

Tower/comm context: not invented here — both this file and the §10 master
take `htower`/`hcomm` as explicit `Prop` hypotheses, and every consumer spine
supplies them by the existing `NonUnitalNonAssocAlgebra` parent-projection
chain (`inferInstance`, as already exercised at `A_FixedPoint.lean`).


## Main results

* `FixedPointBackend.hres2_unconditional`: the
  2-residual `Appendix_FixedPoint.BezoutChain.HRes2`, unconditional given algebra data.
* `FixedPointBackend.fixedPointData_unconditional`:
  the same, in bundle (`FixedPointData`) form.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FixedPointBackend

/-- The 2-residual `Appendix_FixedPoint.BezoutChain.HRes2` unconditional: `hres2Inst_unconditional`
(10) through the token-identical `Hres2Inst ≡ HRes2` identification.
-/
theorem hres2_unconditional (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    Appendix_FixedPoint.BezoutChain.HRes2 K E V :=
  FirstRegFiring.hres2Inst_unconditional K E V hN htower hcomm

/-- The `hdata` bundle (`Appendix_FixedPoint.BezoutChain.FixedPointData`) unconditional: exactly
`hres2_unconditional`, since the bundle is defined as `HRes2`.
-/
theorem fixedPointData_unconditional (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    Appendix_FixedPoint.BezoutChain.FixedPointData K E V :=
  FirstRegFiring.hres2Inst_unconditional K E V hN htower hcomm

#print axioms hres2_unconditional
#print axioms fixedPointData_unconditional

end FixedPointBackend
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
