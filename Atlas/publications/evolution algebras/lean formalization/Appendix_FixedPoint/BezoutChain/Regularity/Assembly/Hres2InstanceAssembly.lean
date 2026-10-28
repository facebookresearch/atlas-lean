/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ConeNoEmbeddedRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.ChiReduceSubstitution
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssClosure
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssSubstitution
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.InfiniteResidueFields
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TraceRepBridge

/-!
# R4b: per-instance `Hres2Inst` assembly (route-(b) R1 feed; valid but inapplicable)

Pure-integration leaf: the per-instance `ResidualWiring.Hres2Inst K E V` master
from the R1b–R3 residuals. Note (landing correction): the route-(b) R1 feed
(`hChiReduceAtAss_of_gatedDepth` below — per-Q pin + discharged gated
tower + per-Q `SupPathDepthSel ⊥` through) is correctly scoped
and reusable, but the R2/R3 inputs (`hdiag`/`hsupp`/`hnonprime`) are
top-level `∀(n,c)` — and those `∀`-forms are unsatisfiable: `∀c
MinAvoidNonprimeSpec` is REFUTED at `n ≥ 3`
(`minAvoidNonprimeSpec_not_forall`), `∀c HdiagRung1` fails at `c ≡ 1`,
`∀c HsuppRung1` fails at `c ≡ 0`. The R2/R3 outputs are per-instance gated
on realized `(b, hexp)` and cannot feed `∀(n,c)` inputs. So this
assembly is valid but inapplicable, like J9  and route-(a) R4. The
live assembly (R4c, open) re-scopes these inputs inside the
`intro n hn c b hexp` scope.

Composition (template: J9's own proof body, `:364–:379`):
* Per-`J` helper `hChiReduceAtAss_of_gatedDepth`: H5 from per-Q gated
  towers (P1 fed by P3, P2 on P4 residues,
  and the per-Q `SupPathDepthSel ⊥` residual).
* `hsucc` leg: `hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec`
  (`MinAvoidJoin.lean`), fed by R2 rung-1 (`hdiag`/`hsupp`), the
  R1b per-stage allocator (`alloc_ge2_close_of_h4H5` on H4 + the
  helper), and R3 narrowed through `minAvoidAllSpec_iff_nonprimeMin`
  (`PrimeSingleClose.lean`; prime slice closed).
* `havoid` leg: `havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin`
  (`ConeNoEmbeddedRungs.lean`), fed by the `hsucc` leg plus R1b at the
  full-span ideal (`hdimEqMinAtAss_close_of_h4H5` on H4 + helper).

Residual register (per realized `(n, c, b, hexp)`; `V hN htower hcomm`
are supplied consumer data): `[hdepth_stage, hdepth_full, hdiag, hsupp,
hnonprime]` + standing `[IsAlgClosed K]`. No new atoms.

## Layering note

Same deliberate leaf exception as `KoszulFinalR4Assemble`: this file
lives in `Regularity/` but imports `BridgeToFixedPoint/` masters. Nothing imports
this file, so the import DAG stays acyclic.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace Hres2InstanceAssembly

open scoped BigOperators

/-- Per-`J` H5 plug on route (b): `HchiReduceAtAss` from the per-Q gated
tower (P1, fed by the unconditional pin P3 and the
discharged tower P2 on algClosed residues P4) plus the
per-Q path-scoped depth residual (`SupPathDepthSel ⊥`).

Conditional on exactly per-Q `[SupPathDepthSel ⊥]`. -/
theorem hChiReduceAtAss_of_gatedDepth (m : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin m) K))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ColonTransfer.SupPathDepthSel
        (R := Localization.AtPrime Q) ⊥) :
    ChiDegreeMaster.HchiReduceAtAss m K J := by
  apply ColonTransfer.hChiReduceAtAss_of_gatedTowers m K J
  intro Q _ hQ
  obtain ⟨dimN, hpin⟩ :=
    ChiReduceSubstitution.dimPin_atAss_unconditional m K J Q hQ
  exact ⟨dimN, hpin,
    TraceRepBridge.supTowerExactGated_of_quot_of_traceVV
      (InfiniteResidueFields.atPrime_residue_infinite_of_algClosed m K Q),
    hdepth Q hQ⟩

#print axioms hChiReduceAtAss_of_gatedDepth

/-- Per-instance `Hres2Inst` from the R1b–R3 residuals (route-(b) R1 feed;
valid but inapplicable: `∀(n,c)` R2/R3 inputs unsatisfiable, R4c re-scoping
open): R1b `SupPathDepthSel ⊥` at every stage ideal (`hdepth_stage`,
feeds the per-stage allocator) and at every full-span ideal
(`hdepth_full`, feeds `hdimEq`), R2 rung-1 discharge (`hdiag`/`hsupp`),
and the R3 nonprime residual (`hnonprime`, narrowed to
`MinAvoidAllSpec` via the iff). Consumes: `hdepth_stage`/`hdepth_full`
(R1b path depth); `hdiag`/`hsupp` (R2); `hnonprime` (R3); `hN`/`htower`/`hcomm`
(consumer algebra data for the `havoid` minimal-avoidance leg).

Conditional on exactly
`[hdepth_stage, hdepth_full, hdiag, hsupp, hnonprime]` given algebra data. -/
theorem hres2Inst_of_gatedDepth_of_rung1_of_nonprimeMin
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    -- R1b at every stage ideal (feeds halloc):
    (hdepth_stage : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)),
      ∀ (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ MinAvoidRungs.stageIdeal n K c hn j) →
      ColonTransfer.SupPathDepthSel
        (R := Localization.AtPrime Q) ⊥)
    -- R1b at every full-span ideal (feeds hdimEq):
    (hdepth_full : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ Ideal.span (Set.range (bridgeSystem n K c hn))) →
      ColonTransfer.SupPathDepthSel
        (R := Localization.AtPrime Q) ⊥)
    -- R2 (RungOneDiagonalDischarge:150/:163), R3 (MinAvoidJoin:171):
    (hdiag : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (k : Fin (statementIndex n + 1)), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (k : Fin (statementIndex n + 1)), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (hnonprime : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ResidualWiring.Hres2Inst K E V := by
  intro n hn c b hexp
  have hH4s : ∀ j : Fin (statementIndex n + 1),
      ChiDegreeMaster.HchiGrowthAtAss (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) :=
    fun j => MinAtAssSubstitution.hchiGrowthAtAss_of_subst _ _ _
  have hH5s : ∀ j : Fin (statementIndex n + 1),
      ChiDegreeMaster.HchiReduceAtAss (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) :=
    fun j => hChiReduceAtAss_of_gatedDepth _ _ _ (hdepth_stage n hn c j)
  have halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) :=
    fun j _ => MinAtAssClosure.alloc_ge2_close_of_h4H5 _ _ _
      (hH4s j) (hH5s j)
  have hsucc :=
    MinAvoidJoin.hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec
      K n hn c (hdiag n hn c) (hsupp n hn c) halloc
      ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin n K c hn).mpr
        (hnonprime n hn c))
  have hdimEq := MinAtAssClosure.hdimEqMinAtAss_close_of_h4H5 _ _ _
    (MinAtAssSubstitution.hchiGrowthAtAss_of_subst _ _ _)
    (hChiReduceAtAss_of_gatedDepth _ _ _ (hdepth_full n hn c))
  refine ⟨hsucc, ?_⟩
  exact ConeNoEmbeddedRungs.havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin
    K E n hn c V b hexp hN htower hcomm hsucc hdimEq

#print axioms hres2Inst_of_gatedDepth_of_rung1_of_nonprimeMin

end Hres2InstanceAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
