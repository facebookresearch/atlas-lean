/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ConeNoEmbeddedRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungOneClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.Hres2InstanceAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssClosure
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssSubstitution

/-!
# R4c-v2: ungated per-basis Hres2 (repair of r4c-rescoped)

Pure-integration module: the ungated per-basis `(hsucc, havoid)` conclusion
from the R1b–R3 residuals, with the rung-1 step fed horth-free by M-O1a.
This repairs the flawed r4c-rescoped approach (the sketched
`horth : ∀ n hn c b, orth(b)` input is false at `dim ≥ 2`, since every
basis realizes some `c`, so no unrealizability escape exists).

exact scope: this does not conclude `ResidualWiring.Hres2Inst` and does not
plug into the §10 `hres2` binder (`SpineAdapter.lean–:604`) as-is.
Firing §10 needs the natural-basis rework (separate lane).

Composition (template: R4b's own proof body, `:135–:158`):
* Rung-1 step derived in-body from the instance data: M-O1a
  (`RungOneClose.rung1step_unhorth_of_algebraData`), token-identical
  to the `hrung1` slot — zero glue, zero `horth`.
* Remainder = R4b body verbatim with the call replaced by the
  master and `(hnonprime n hn c)` →
  `(hnonprime n hn c b hexp)`; H5 plug
  `Hres2InstanceAssembly.hChiReduceAtAss_of_gatedDepth` reused by import.

Residual register (per realized `(n, c, b, hexp)`; `V hN htower hcomm`
are supplied consumer data): `[hdepth_stage, hdepth_full]` (R1b path depth;
`dim≤1` closed, `dim≥2` = O2) + `[hnonprime]` (R3, gated; closed at `n≤2`,
T3-pinned otherwise) + standing `[IsAlgClosed K]`. No new atoms.

## Layering note

Same deliberate leaf exception as `Hres2InstanceAssembly`: this file
lives in `Regularity/` but imports `BridgeToFixedPoint/` masters. Imported by
`Hres2PlugCorollary` and `KoszulFinalE3Plug` only; the import DAG
stays acyclic (verified closure: `RungOneClose` transitively
imports none of this file or its importers).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace UngatedHres2Assembly

open scoped BigOperators

/-- Ungated per-basis `(hsucc, havoid)` from the R1b–R3 residuals: R1b
`SupPathDepthSel ⊥` at every stage ideal (`hdepth_stage`, feeds the
per-stage allocator) and at every full-span ideal (`hdepth_full`, feeds
`hdimEq`), R3 nonprime residual gated on the realizing data
(`hnonprime`, narrowed to `MinAvoidAllSpec` via the iff), and
the rung-1 step derived in-body from the instance data via M-O1a
(`rung1step_unhorth_of_algebraData`), with no `horth`.

Conditional on exactly `[hdepth_stage, hdepth_full, hnonprime]`
given algebra data. -/
theorem hres2Gated_of_gatedDepth_of_nonprimeMin
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
    -- Ungated per-basis conclusion (horth-free; not Hres2Inst):
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
  intro n hn c b hexp
  -- Rung-1 step, horth-free (M-O1a; token-identical to the hrung1 slot):
  have hrung1 := RungOneClose.rung1step_unhorth_of_algebraData
    K E V n hn c b hexp hN htower hcomm
  -- Remainder = R4b body (Hres2InstanceAssembly.lean–:158) verbatim,
  -- with the call replaced by the master,
  -- (hnonprime n hn c) → (hnonprime n hn c b hexp),
  -- hChiReduceAtAss_of_gatedDepth → Hres2InstanceAssembly.hChiReduceAtAss_of_gatedDepth:
  have hH4s : ∀ j : Fin (statementIndex n + 1),
      ChiDegreeMaster.HchiGrowthAtAss (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) :=
    fun j => MinAtAssSubstitution.hchiGrowthAtAss_of_subst _ _ _
  have hH5s : ∀ j : Fin (statementIndex n + 1),
      ChiDegreeMaster.HchiReduceAtAss (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) :=
    fun j => Hres2InstanceAssembly.hChiReduceAtAss_of_gatedDepth _ _ _
      (hdepth_stage n hn c j)
  have halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) :=
    fun j _ => MinAtAssClosure.alloc_ge2_close_of_h4H5 _ _ _
      (hH4s j) (hH5s j)
  have hsucc :=
    MinAvoidJoin.hsucc_of_rung1step_of_alloc_of_minAvoidSpec
      K n hn c hrung1 halloc
      ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K c hn).mpr
        (hnonprime n hn c b hexp))
  have hdimEq := MinAtAssClosure.hdimEqMinAtAss_close_of_h4H5 _ _ _
    (MinAtAssSubstitution.hchiGrowthAtAss_of_subst _ _ _)
    (Hres2InstanceAssembly.hChiReduceAtAss_of_gatedDepth _ _ _
      (hdepth_full n hn c))
  refine ⟨hsucc, ?_⟩
  exact ConeNoEmbeddedRungs.havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin
    K E n hn c V b hexp hN htower hcomm hsucc hdimEq

#print axioms hres2Gated_of_gatedDepth_of_nonprimeMin

end UngatedHres2Assembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
