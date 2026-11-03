/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FewFormsCommonZero
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssRungFeeds

/-!
# M-O1a: unhorth rung-1 hsucc step

The rung-1 step of the `hsucc`
ladder, unconditional given realized algebra data + `[IsAlgClosed K]`,
with no `horth`.

## Route

Direct application: the proved-but-unused `hdichRung1_unhorth`
(`FewFormsCommonZero.lean`, concluding the reducible abbrev
`JointAssembly.HdichRung1`, whose body is verbatim the
`rung1step_of_hdich` binder) feeds `AssRungFeeds.rung1step_of_hdich`
(`AssRungFeeds.lean`, conditional-exact on `[hdich]`). No
converter needed.

Namespace note (verdict correction C1): `FewFormsCommonZero.lean`
declares only `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain` (no `FewFormsCommonZero`
namespace), so the feed's true path is
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.hdichRung1_unhorth`, used unqualified below.

Citation fix (design note §M-O1a): `rung1prime0` / `rung1nondvd1` live at
`AssRungFeeds.lean` / (not in `RungRegular.lean`);
`hreg_rung1_of_dichotomy` at `RungRegular.lean` is already consumed
inside `rung1step_of_hdich`. Rung-0 companion (proved, cited not
reproved): `hreg_rung0`, `RungRegular.lean`. The corollary
concludes the span-image `• ⊤` quotient shape (what `rung1step_of_hdich`
gives); rung 0 is ofList-shaped, transportable via
`SuccClosureRungs.step_span_of_step_oflist` if a uniform rungs-≤-1 statement is
wanted downstream.

`[IsAlgClosed K]` is used inside the feed, via the proved
`fewFormsCommonZero` (`FewFormsCommonZero.lean`): `m` homogeneous
positive-degree forms in `N` variables (`m < N`) have a common nonzero
zero. Documented here as `[algClosed]`; no other classical or
choice-like axiom is introduced (see `#print axioms` below).

Status: Leg 1 linked — rung-1 step unconditional given algebra data +
`[IsAlgClosed K]`, no `horth`; pair-hsucc input banked for
`hunmixed_two_of_hdimEqMin` (`UnmixednessAtLengthTwo.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungOneClose

open scoped BigOperators

/-- Rung-1 hsucc step, unconditional given realized algebra data: the
proved `hdichRung1_unhorth` dichotomy (discharged of `hL2` by the proved
`fewFormsCommonZero`) feeds `rung1step_of_hdich` directly, since
`HdichRung1` is reducibly the `hdich` binder. No `horth` needed.
-/
theorem rung1step_unhorth_of_algebraData
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k) :=
  AssRungFeeds.rung1step_of_hdich n K c hn
    (hdichRung1_unhorth
      K E V n hn c b hexp hN htower hcomm)

#print axioms rung1step_unhorth_of_algebraData

end RungOneClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
