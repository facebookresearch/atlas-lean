/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.UngatedHres2Assembly
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SelectedPathDepth
import Appendix_FixedPoint.AssociatedPrimes.FiniteDimDischarge
/-!
# E3: R4c → `Hres2Inst` plug corollary

One-application corollary: the proved R4c-v2 master
(`UngatedHres2Assembly.hres2Gated_of_gatedDepth_of_nonprimeMin`)
concludes exactly the S10-proved ungated shape
(`ResidualWiring.Hres2Inst`), which is the live §10-master `hres2` input
(`SpineAdapter.lean`, fired from the `hfin`/`hneV` basis). Pure repackaging:
the three residual hypotheses are passed through verbatim.

Conditional on exactly `[hdepth_stage, hdepth_full, hnonprime]`
given algebra data (same register as R4c).

## Layering note

Same deliberate leaf exception as `UngatedHres2Assembly`: this file
lives in `Regularity/` but imports `BridgeToFixedPoint/` masters. Nothing imports
this file, so the import DAG stays acyclic.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulFinalE3Plug

open scoped BigOperators

/-- The §10-master `hres2` input (`Hres2Inst`) from the R1b–R3
residuals, via the R4c-v2 master (which concludes it definitionally).

Conditional on exactly `[hdepth_stage, hdepth_full, hnonprime]`
given algebra data. -/
theorem hres2Inst_of_gatedDepth_of_nonprimeMin
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    -- R1b at every stage ideal (H-side; applied inside the instance scope):
    (hdepth_stage : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)),
      ∀ (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ MinAvoidRungs.stageIdeal n K c hn j) →
      ColonTransfer.SupPathDepthSel
        (R := Localization.AtPrime Q) ⊥)
    -- R1b at every full-span ideal:
    (hdepth_full : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ Ideal.span (Set.range (bridgeSystem n K c hn))) →
      ColonTransfer.SupPathDepthSel
        (R := Localization.AtPrime Q) ⊥)
    -- R3, gated on the realizing data (per-instance; not bare ∀c):
    (hnonprime : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E)
        = ∑ k, c i j k • (b k : E)),
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ResidualWiring.Hres2Inst K E V :=
  UngatedHres2Assembly.hres2Gated_of_gatedDepth_of_nonprimeMin
    K E V hN htower hcomm hdepth_stage hdepth_full hnonprime

#print axioms hres2Inst_of_gatedDepth_of_nonprimeMin

end KoszulFinalE3Plug
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# M1: R4c `hdepth` feed from the CM residuals

`C3aGapAll` is closed (`AssociatedPrimes.FiniteDimDischarge`) — `hC3a` binders
below are vestigial; downstream results need only `[FirstReg]`
(see discharge wrappers).

Discharges the R4c-v2 `hdepth_stage` / `hdepth_full` hypotheses
(`UngatedHres2Assembly.hres2Gated_of_gatedDepth_of_nonprimeMin`) with the
Linkage outputs (`KoszulSupHdepthAssemble.hdepth_stage_of_cm_residuals` /
`hdepth_full_of_cm_residuals`), producing the conditional-exact R4c corollary
on `[FirstReg + C3aGapAll, hnonprime]`, plus the E3-inherited corollary via
the E3 plug master (`KoszulFinalE3Plug.hres2Inst_of_gatedDepth_of_nonprimeMin`).

Universe diagonal: the linkage assembly is `uK`-monomorphic, so this leaf is stated at
`universe uK` with `K : Type uK`; R4c's master takes `(K E : Type*)`, so
instantiating R4c's `K` at `uK` is legal (`E` stays `Type*`).

Conditional on exactly `[FirstReg.{uK,uK} + C3aGapAll.{uK}, hnonprime]`
given algebra data + standing `[IsAlgClosed K]`. Feeds only proved lemmas;
nothing new assumed (`hFR` / `hC3a` / `hnonprime` are pass-through hypotheses
in the same register R4c/E3 already carry).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace Hres2PlugCorollary

open scoped BigOperators

universe uK

/-- R4c ungated per-basis `(hsucc, havoid)` with both `hdepth` legs discharged
by the linkage CM-residual outputs. Conclusion is the R4c `:98-108` shape verbatim.

Conditional on exactly `[FirstReg + C3aGapAll, hnonprime]` given algebra
data + standing `[IsAlgClosed K]`. -/
theorem hres2Gated_of_cmResiduals_of_nonprimeMin
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK})
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
  UngatedHres2Assembly.hres2Gated_of_gatedDepth_of_nonprimeMin
    K E V hN htower hcomm
    (KoszulSupHdepthAssemble.hdepth_stage_of_cm_residuals K hFR hC3a)
    (KoszulSupHdepthAssemble.hdepth_full_of_cm_residuals K hFR hC3a)
    hnonprime

#print axioms hres2Gated_of_cmResiduals_of_nonprimeMin

/-- E3 inheritance: the §10-master `hres2` input (`Hres2Inst`) with both
`hdepth` legs discharged by the linkage CM-residual outputs, via the E3 plug master.

Conditional on exactly `[FirstReg + C3aGapAll, hnonprime]` given algebra
data + standing `[IsAlgClosed K]`. -/
theorem hres2Inst_of_cmResiduals_of_nonprimeMin
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK})
    (hnonprime : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E)
        = ∑ k, c i j k • (b k : E)),
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ResidualWiring.Hres2Inst K E V :=
  KoszulFinalE3Plug.hres2Inst_of_gatedDepth_of_nonprimeMin
    K E V hN htower hcomm
    (KoszulSupHdepthAssemble.hdepth_stage_of_cm_residuals K hFR hC3a)
    (KoszulSupHdepthAssemble.hdepth_full_of_cm_residuals K hFR hC3a)
    hnonprime

#print axioms hres2Inst_of_cmResiduals_of_nonprimeMin

end Hres2PlugCorollary
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# R4c-feed C3a discharge pair

## Main results

* `hres2Gated_of_fr_of_nonprimeMin`:
  `hres2Gated_of_cmResiduals_of_nonprimeMin` with the `hC3a` hypothesis
  discharged via the proved `AssociatedPrimes.FiniteDimDischarge.c3aGapAll_of_gapBaseFin`
  (universe `uK`, placed before `hnonprime`), collapsing the hypothesis
  set to `[FirstReg.{uK,uK}]`-only (+ preserved `hnonprime`).
* `hres2Inst_of_fr_of_nonprimeMin`: same discharge for
  `hres2Inst_of_cmResiduals_of_nonprimeMin`.

Both conclusions restated verbatim; the per-instance `hnonprime`
(`MinAvoidNonprimeSpec`) is preserved verbatim (out of scope for this
lane, not discharged). `[Infinite K]` is absent as a binder with
`[IsAlgClosed K]` standing ambient (`Infinite-absent
(IsAlgClosed-ambient, TC unused)` — no argument requires `[Infinite K]`,
so the TC leg is available but unused); the wrappers add none.

`[IsAlgClosed K]` stands ambient in both heads (preserved verbatim);
`[algClosed]`-ambient content is assumed nowhere new in this file.
`hC3a` appears only as the discharged argument position, never assumed.

Import closure: proved `Hres2PlugCorollary`, `AssociatedPrimes.FiniteDimDischarge`
+ mathlib only.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulFinalR4cHdepthFeedC3aDischarge

open scoped BigOperators

universe uK

/-- R4c ungated C3a discharge:
`hres2Gated_of_cmResiduals_of_nonprimeMin` on `[FirstReg.{uK,uK}]`-only
(+ preserved `hnonprime`), `hC3a` discharged via
`c3aGapAll_of_gapBaseFin.{uK}` placed before `hnonprime`.

Hypothesis-set collapse only; the conclusion is restated verbatim. -/
theorem hres2Gated_of_fr_of_nonprimeMin
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
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
              (R1RegularSection.secForm (statementIndex n) K)) ∉ P) := by
  exact Hres2PlugCorollary.hres2Gated_of_cmResiduals_of_nonprimeMin
    K E V hN htower hcomm hFR
    AssociatedPrimes.FiniteDimDischarge.c3aGapAll_of_gapBaseFin.{uK} hnonprime

#print axioms hres2Gated_of_fr_of_nonprimeMin

/-- E3-inherited C3a discharge:
`hres2Inst_of_cmResiduals_of_nonprimeMin` on `[FirstReg.{uK,uK}]`-only
(+ preserved `hnonprime`), `hC3a` discharged via
`c3aGapAll_of_gapBaseFin.{uK}` placed before `hnonprime`.

Hypothesis-set collapse only; the conclusion is restated verbatim. -/
theorem hres2Inst_of_fr_of_nonprimeMin
    (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hnonprime : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E)
        = ∑ k, c i j k • (b k : E)),
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ResidualWiring.Hres2Inst K E V := by
  exact Hres2PlugCorollary.hres2Inst_of_cmResiduals_of_nonprimeMin
    K E V hN htower hcomm hFR
    AssociatedPrimes.FiniteDimDischarge.c3aGapAll_of_gapBaseFin.{uK} hnonprime

#print axioms hres2Inst_of_fr_of_nonprimeMin

end KoszulFinalR4cHdepthFeedC3aDischarge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
