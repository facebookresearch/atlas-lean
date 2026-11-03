/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CountAssembly
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CoordinatizationToolkit
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SecondPointExistence
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ProjectiveFiniteness
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MkSystemSmoothness
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SpuriousMultiplicityOne
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition
import Appendix_FixedPoint.BezoutChain.Dimension.LocalizationDimension
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Appendix_FixedPoint.BezoutChain.Geometry.AffineFinite
import Appendix_FixedPoint.BezoutChain.Geometry.ChartCompat
import Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration
import Appendix_FixedPoint.BezoutChain.Geometry.ConeDimOne
import Appendix_FixedPoint.BezoutChain.Geometry.Counting
import Appendix_FixedPoint.BezoutChain.Geometry.CurveMeetsHyperplane
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity
import Appendix_FixedPoint.BezoutChain.Geometry.MkSystemChart
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeUnmixedBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.EliminationFilter
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemRegular
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.ResultantLemmas
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Order.KrullDimension
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Final discharge hub: maximally-discharged end-to-end theorems

This lane is the import-capable site for the whole project: it imports every
supplier leaf (see the DAG note below) and produces the maximally-discharged
end-to-end theorems — the Bézout count, its smooth-point corollary, and the
bridge chain down to the fixed-point conclusion — with the exact minimal
residual list.

## Master residual lists (exact, nothing else assumed)

At bridge data (`m := statementIndex n`, `G := bridgeSystem n K c hn`,
`ℓ := secForm`), bundled as `FinalResiduals` (§1):

`[hsucc, havoid, hfilter, hinj, hsurj]`.

* `hsucc : SuccessiveSMulRegular bridgeSystem` — the central crux
  (`hunmixed_ge2`): quotient-side successive regularity at rungs `≥ 1`.
  Blocking reason: only rung `0` closes (domain-side
  `MkSystemRegular.mkSystem_isSMulRegular`); rungs `≥ 1` need unmixedness/CM
  input and Mathlib v4.34.0 has no CM/grade/depth API (verified absence).
* `havoid` (R1 Ass-avoidance of `mk(secForm)`) — needs prime avoidance for
  the specific section form (the `(n+2)`-nd rung); `PrimeAvoidance` only yields
  existence of some avoider. Strictly beyond `hsucc`.
* `hfilter` (`Ffun`-filtration of the section) — no `Cf`-construction exists
  for the `stagePiece`/`secIdeal` pieces (`Ffun` is a quotient type while
  `Fsec` is a `sectionQuotient` submodule across a double-quotient vs
  joined-ideal presentation, so the bridge/vanishing lane's `Fsec` closure
  does not transfer). Filtration geometry, open leaf L-FILT.
* `hinj`/`hsurj` (`ChartMaxSpecInj`/`ChartMaxSpecSurj`, `∀`-form over the
  closed `hfin`/`hc`) — the Nullstellensatz transfer through the section
  presentation (cone → chart localization → degree-`0` part →
  projectivization); only the affine feed is in-tree.

Closed in-file from the imports (each with its chain in §2): `hF` (bridge
forms are quadrics), `hG` (hence), `hreg`/`hc` (R1 from `havoid`), `hcut`
(BPF from algebra data `hN`), `hfin` (projective step from algebra data),
`hdim` (polynomial dimension equation), height-`havoid` (Ass lower bound
from `hsucc`), `hZd` (`hcontra` chain), `hmem`/`hsmooth` (from `hF`),
`hloc`/`hmult` (chart+representative transport into closed `dist_mult_one`),
`hfinA` (section-piece vanishing), `hsum`/`hpos` (Artinian + MaxSpec
correspondence), `hbridge` (no-`hlin` bridge), `hH0`/`hSES`/`hSEC`
(SES data), `hSecondOfNotZd` (infinite locus + `hcontra`), `hStatementInst`
(direct `Statement` application).

## End-to-end theorems

* `bezout_at_bridge_discharged` (§3): cone point at bridge data,
  conditional-exact `[hsucc, havoid, hfilter, hinj, hsurj]` (+ algebra data).
* `fixedPoint_of_idempotent_final` (§3): projective fixed point,
  conditional on the `∀`-residuals (+ `hfin hV hN hneV htower hcomm`).
* `bezout_generic_discharged` (§4): count at `(mkSystem, secForm`,
  conditional-exact `[hF, hsucc, havoid, hBPF, hfilter]`.
* `exists_another_generic_discharged` (§4): corollary at `(mkSystem,
  secForm)`, conditional-exact
  `[hF, hsucc, havoid, hBPF, hfilter, hinj, hsurj]` (no `hequiv`: the
  transport+`mult1` route bypasses the `LinearEquiv` residual).

Status: conditional-exact-list.

## §5 closed feed

* `hF_at_ffun` (§5): `Ffun` is the section-piece finrank
  (`∀ d, Ffun … d = finrank (sectionPiece … d)`), unconditional, via the
  piece-level third-isomorphism `LinearEquiv` (`hF_secPieceEquiv`);
  instances at bridge data (`hF_at_ffun_bridge`), at `(mkSystem,
  secForm)` (`hF_at_ffun_mkSystem`), and the `Ffun = Fsec` bridge
  (`hF_ffun_eq_fsec`).

## Import DAG (verified)

This file is new (nothing imports it), so all edges are acyclic by
construction. Never imported: `Appendix_FixedPoint/A_FixedPoint.lean`
(the top-level principle), imported repo-wide solely by `IdempotentIff`
and `SolvableCorollary`
(top level, outside the `Bezout` cone). The `FixedPointFromBezout` cone is
imported read-only as a library (its bridge data + `bezout_quadrics`
statement); no file is modified.

## References

Mathlib v4.34.0 exact names (each grep-verified under
`.lake/packages/mathlib` before use): `MvPolynomial.eval`
(`Algebra/MvPolynomial/Eval.lean`), `IsSMulRegular`
(`Algebra/Regular/SMul.lean`), `Module.finrank`/`Module.Finite`
(`LinearAlgebra/Dimension/Finrank.lean`,
`LinearAlgebra/FiniteDimensional/Defs.lean`), `Module.Basis`
(`LinearAlgebra/Basis/Defs.lean`), `associatedPrimes`
(`RingTheory/Ideal/AssociatedPrime/Basic.lean`), `Ideal`
(`RingTheory/Ideal/Defs.lean`), `Ideal.IsPrime`
(`RingTheory/Ideal/Prime.lean`), `Ideal.Quotient.mk`
(`RingTheory/Ideal/Quotient/Defs.lean`), `Ideal.span`
(`RingTheory/Ideal/Span.lean`), `PrimeSpectrum.height_eq_orderHeight`
(`RingTheory/Ideal/Height.lean`), `PrimeSpectrum`
(`RingTheory/Spectrum/Prime/Defs.lean`), `ringKrullDim`
(`RingTheory/KrullDimension/Basic.lean`), `Ring.KrullDimLE`
(`Order/KrullDimension.lean`), `ℕ∞` (`Data/ENat/Basic.lean`), `WithBot`
(`Order/WithBot.lean`), `Projectivization`
(`LinearAlgebra/Projectivization/Basic.lean`), `Set.Finite.subset`,
`Set.finite_singleton`, `Set.Subsingleton.finite`, `Set.Finite.toFinset`
(`Data/Set/Finite/Basic.lean`), `IsScalarTower`/`SMulCommClass`
(`Algebra/Group/Action/Defs.lean`), `IsHomogeneous`
(`RingTheory/MvPolynomial/Homogeneous.lean`), `Finset` API
(`Algebra/BigOperators/Group/Finset/Basic.lean`+`/Defs.lean`).

Project: `CountAssembly` §1/§3/§6/§9 feeds,
`FixedPointFromBezout.bezout_quadrics` + bridge data, `CoordinatizationToolkit` spine,
`SecondPointWiring.Mult1SpuriousProp`, `ProjectiveFiniteness` §4–§5 `hfin` shapes,
`R1RegularSection` section feeds, `MkSystemSmoothness` point inputs,
`SpuriousMultiplicityOne.mult1_spurious_of_hfin_transport`, `MkSystemSESData`
`Hfun`/`Ffun`/`hH0`/`hSES`/`hSEC`, `MkSystemRegular`
`mkSystem_isHomogeneous_of`, `AssHeightBound`
`le_height_of_span_of_successive`, `PolynomialCatenary`
`mvPolynomial_ringKrullDim`, `LocalizationDimension` monotonicity/transfer,
`AffineFinite` dimAPI route, `ChartCompat` iso + transports,
`MkSystemChart` `dist_mult_one`/`BasePointFree`, `ConeDimOne`
`hcontra_of_havoid`, `CurveMeetsHyperplane` (via `ProjectiveFiniteness` §2),
`ChartFiltration` MaxSpec correspondence + chart finiteness, `HilbertFunctionCount`
section finiteness + `Cfsec` stability/vanishing, `LocalMultiplicity` (via
`hsum_of_hdecomp`), `Counting.infinite_locus_of_not_zeroDim`,
`Statement` (`bezout_quadratic_fsec_final` inputs `hfilter_fsec_of_final`
not needed here — `Ffun` form kept; `hbridge_of_final` closes `hbridge`
with no `hlin`; `exists_another_point_of_smooth_point` direct).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FinalDischargeHub

open scoped BigOperators

/-! ## §1 The exact minimal residual bundle at bridge data -/

/-- The exact minimal residual bundle at bridge data
(`m := statementIndex n`, `G := bridgeSystem n K c hn`,
`ℓ := R1RegularSection.secForm m K`): `[hsucc, havoid, hfilter, hinj, hsurj]`.

* `hsucc`: central crux (`hunmixed_ge2`), quotient-side successive
  regularity at rungs `≥ 1` (only rung `0` closes domain-side; no CM API).
* `havoid`: R1 Ass-avoidance for the specific `secForm` (`(n+2)`-nd rung).
* `hfilter`: `Ffun`-filtration of the section (no `Cf`-construction for
  `stagePiece`/`secIdeal` pieces; the `Fsec` closure does not transfer).
* `hinj`/`hsurj`: MaxSpec correspondence (`∀`-form over the closed
  `hfin`/`hc`; Nullstellensatz transfer through the section presentation). -/
def FinalResiduals (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn)
    ∧ (∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
        Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P)
    ∧ (∃ (B : ℕ) (Cf : ℕ → Submodule K
          (sectionQuotient (statementIndex n) K (bridgeSystem n K c hn)
            (R1RegularSection.secForm (statementIndex n) K))),
        Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
        (∀ d, d ≤ B →
          Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
            + MkSystemSESData.Ffun (statementIndex n) K
              (bridgeSystem n K c hn)
              (mkLin (statementIndex n) K
                (R1RegularSection.secForm (statementIndex n) K)) d) ∧
        ∀ d, B < d → MkSystemSESData.Ffun (statementIndex n) K
          (bridgeSystem n K c hn)
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) d = 0)
    ∧ (∀ (hfin : (vanishingLocus (statementIndex n) K
          (bridgeSystem n K c hn)).Finite)
        (hc : ChartNonvanishing (statementIndex n) K
          (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K)),
        ChartMaxSpecInj (statementIndex n) K (bridgeSystem n K c hn)
          (R1RegularSection.secForm (statementIndex n) K) hfin hc)
    ∧ ∀ (hfin : (vanishingLocus (statementIndex n) K
          (bridgeSystem n K c hn)).Finite)
        (hc : ChartNonvanishing (statementIndex n) K
          (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K)),
        ChartMaxSpecSurj (statementIndex n) K (bridgeSystem n K c hn)
          (R1RegularSection.secForm (statementIndex n) K) hfin hc

/-! ## §2 Closed feeds -/

/-- `hcut` at bridge data from algebra data: the shifted-family BPF proof
moved across the `rfl` mirror links (`familyForms`/`statementIndex`). -/
theorem hcut_of_algebraData (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    R1RegularSection.cutsOutOrigin (statementIndex n) K
      (bridgeForms n K c0 hn) := by
  have hB := basePointFree_shiftedFamily_of_algebraData n K c0 hn E V b
    hexp hN htower hcomm
  exact hB

/-- `hdim` closed: the `≤` half is the polynomial dimension equation. -/
theorem hdim_closed (n : ℕ) (K : Type*) [Field K] :
    ringKrullDim (MvPolynomial (Fin (n + 2)) K)
      ≤ ((n + 2 : ℕ) : WithBot ℕ∞) :=
  le_of_eq (mvPolynomial_ringKrullDim K (n + 2))

/-- Height-`havoid` (the `ConeDimOne` shape) from `hsucc`: the global Ass
lower bound, moved across `PrimeSpectrum.height_eq_orderHeight`. -/
theorem hHeightAvoid_of_hsucc (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular G) :
    ∀ P : Ideal (MvPolynomial (Fin (n + 2)) K), ∀ hP : P.IsPrime,
      Ideal.span (Set.range G) ≤ P →
        ((n + 1 : ℕ) : ℕ∞) ≤ Order.height (⟨P, hP⟩ : PrimeSpectrum _) := by
  intro P hP hJP
  have := hP
  have h := AssHeightBound.le_height_of_span_of_successive G hsucc P hJP
  have e := PrimeSpectrum.height_eq_orderHeight
    (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial (Fin (n + 2)) K))
  rw [← e]
  exact h

/-- `hZd` from `[hG, hsucc, hfin]` via the `hcontra` chain (generic `G`). -/
theorem hZd_of_hfin_hsucc (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular G)
    (hfin : (vanishingLocus n K G).Finite) :
    IsZeroDimensional n K G :=
  hcontra_of_havoid n K G (fun _ => 2) hG (hdim_closed n K)
    (hHeightAvoid_of_hsucc n K G hsucc) hfin

/-- `hloc` (local multiplicity `1` at the distinguished representative)
from `[hF, hc]`: chart transport (closed iso) + representative transport +
closed `dist_mult_one`. Proof-term gaps close by proof irrelevance. -/
theorem hloc_closed (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (ℓ : Fin (m + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
      (_ : p ∈ vanishingLocus m K (mkSystem m K F))
      (v : Fin (m + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin m K ℓ) ≠ 0) :
    localMultiplicity m K (mkSystem m K F) ℓ (distinguishedPoint m K).rep
      (fun i => mem_vanishingLocus_mkSystem m K F hF
        (distinguishedPoint m K).rep (distinguishedPoint m K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint m K)) i)
      (hc (distinguishedPoint m K) (mem_vanishingLocus_mkSystem m K F hF)
        (distinguishedPoint m K).rep (distinguishedPoint m K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint m K))) = 1 := by
  have hmem0 : distinguishedPoint m K ∈
      vanishingLocus m K (mkSystem m K F) :=
    mem_vanishingLocus_mkSystem m K F hF
  have htr : localMultiplicity m K (mkSystem m K F) ℓ
        (distinguishedPoint m K).rep
        (fun i => hmem0 _ _ (Projectivization.mk_rep _) i)
        (hc _ hmem0 _ _ (Projectivization.mk_rep _))
      = localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) :=
    CountAssembly.mult_transport_dist_of_iso m K F ℓ hF
      (fun i => hmem0 _ _ (Projectivization.mk_rep _) i)
      (hc _ hmem0 _ _ (Projectivization.mk_rep _))
      (fun i => hmem0 _ _ (Projectivization.mk_rep _) i)
      (hℓdist_at_rep K m)
      (chartIso_chartCompatIso m K (mkSystem m K F) ℓ (distEll m K)
        (distinguishedPoint m K).rep
        (fun i => hmem0 _ _ (Projectivization.mk_rep _) i)
        (hc _ hmem0 _ _ (Projectivization.mk_rep _))
        (hℓdist_at_rep K m))
  exact htr.trans (dist_mult_one m K F hF)

/-- `hmult` at the distinguished point from `[hfin, hF, hc]`: the
`SpuriousMultiplicityOne` transport wiring with `hchart` closed by the chart iso
and `hrep` closed from `hF`. -/
theorem hmult_closed (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (ℓ : Fin (m + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
      (_ : p ∈ vanishingLocus m K (mkSystem m K F))
      (v : Fin (m + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin m K ℓ) ≠ 0)
    (hfin : (vanishingLocus m K (mkSystem m K F)).Finite) :
    localPointMultiplicity m K (mkSystem m K F) ℓ hc
      (distinguishedPoint m K) = 1 := by
  apply mult1_spurious_of_hfin_transport K m F hF ℓ hc hfin
  · exact CountAssembly.hchart_of_iso m K F ℓ _ _ _ _
      (chartIso_chartCompatIso m K (mkSystem m K F) ℓ (distEll m K)
        (distinguishedPoint m K).rep _ _ _)
  · exact localMultiplicity_rep_eq_zRep m K F hF _ _

/-- `hfinA` (chart finiteness) from `[hG, hreg, hZd]`: section-piece
vanishing (`Fsec` vanishing above the `Cfsec` stability bound) fed into
the chart-finiteness descent. No `hlin`. -/
theorem hfinA_closed (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    Module.Finite K (chartRing n K G ℓ) := by
  have := section_finite_of_artinian n K G ℓ hreg hZd
  obtain ⟨B, hstab⟩ := cfsec_stab_section n K G ℓ hreg hZd
  have hvan : ∀ d, B < d →
      Module.finrank K ↥(sectionPiece n K G ℓ d) = 0 :=
    fsec_vanishing_of_stabAbove n K G ℓ B hstab
      (fun d _ => hdisj_full_of_quadrics n K G ℓ hG d)
  exact chart_finite_of_sectionPiece_vanishing n K G ℓ B hG hreg hvan

/-- `hsum` from `[hfin, hc, hinj, hsurj, hG, hreg, hZd]` (`hfinA` closed
in-line): the Artinian decomposition (`chartLocFinite`/`chartDecomp`)
fed with the MaxSpec correspondence. -/
theorem hsum_closed (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hinj : ChartMaxSpecInj n K G ℓ hfin hc)
    (hsurj : ChartMaxSpecSurj n K G ℓ hfin hc)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    ∑ p ∈ hfin.toFinset, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) := by
  have hfinA := hfinA_closed n K G ℓ hG hreg hZd
  exact CountAssembly.hsum_of_hdecomp n K G ℓ hfin hc
    (fun p => chartLocFinite_of_chartFinite n K G ℓ hfin hc hfinA p)
    (chartDecomp_of n K G ℓ hfin hc hfinA
      (chartHbij_of_bijective n K G ℓ hfin hc hinj hsurj)
      (chartHloc_of_bijective n K G ℓ hfin hc hinj hsurj))

/-- `_hpos` from `[hfin, hc, hG, hreg, hZd]` (`hfinA` closed in-line). -/
theorem hpos_closed (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    ∀ p ∈ hfin.toFinset, 1 ≤ localPointMultiplicity n K G ℓ hc p :=
  CountAssembly.hpos_of_hfinLoc n K G ℓ hfin hc
    (fun p => chartLocFinite_of_chartFinite n K G ℓ hfin hc
      (hfinA_closed n K G ℓ hG hreg hZd) p)

/-- The `¬hZd`-branch second point from `[hG, hsucc]`: the locus is
infinite (`hcontra` chain), hence not contained in the singleton. -/
theorem hSecondOfNotZd_closed (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular G) :
    ¬ IsZeroDimensional n K G →
      ∃ q : Projectivization K (Fin (n + 2) → K),
        q ∈ vanishingLocus n K G ∧ q ≠ distinguishedPoint n K := by
  intro hNotZd
  have hcontra := hcontra_of_havoid n K G (fun _ => 2) hG (hdim_closed n K)
    (hHeightAvoid_of_hsucc n K G hsucc)
  have hInf := infinite_locus_of_not_zeroDim n K G hNotZd hcontra
  by_contra hcon
  have hcon' : ∀ q ∈ vanishingLocus n K G, q = distinguishedPoint n K := by
    intro q hq
    by_contra hne
    exact hcon ⟨q, hq, hne⟩
  have hsub : (vanishingLocus n K G).Subsingleton := fun q hq r hr =>
    (hcon' q hq).trans (hcon' r hr).symm
  have hfin' := hsub.finite
  exact hInf hfin'

/-! ## §2b The `LocalizationDimension` alternative route, closed
The three by-name dimension inputs of `AffineFinite.hdim_of_hsucc_of_dimAPI`
are all proved, so the affine-quotient dimension bound (hence affine
finiteness) follows from `hsucc` on the chart family alone. -/

/-! ## §3 End-to-end at bridge data -/

/-- Bézout cone point at bridge data with everything but `FinalResiduals`
discharged: `ℓ := secForm`, `H/F := Hfun/Ffun`, `hH0`/`hSES`/`hSEC` from
SES data, `hc`/`hreg` from R1, `hcut`/`hfin` from algebra data, `hZd` from
the `hcontra` chain, `hsum`/`hpos` from Artinian + MaxSpec, `hbridge`
with no `hlin`, `hloc` from transport, `hStatementInst` direct,
`hSecondOfNotZd` from the infinite locus.

Exact residual list: `[hsucc, havoid, hfilter, hinj, hsurj]` (bundled as
`FinalResiduals`) plus the algebra data `(V, b, hexp, hN, htower,
hcomm)`, which are the theorem's own inputs. -/
theorem bezout_at_bridge_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hres : FinalResiduals n K c hn) :
    ∃ (X : Fin n → K) (z : K),
      (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0 := by
  obtain ⟨hsucc, havoid, hfilter, hinj, hsurj⟩ := hres
  have hF : ∀ i, ((bridgeForms n K c hn) i).IsHomogeneous 2 :=
    bridgeForms_homogeneous n K c hn
  have hG : ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2 :=
    bridgeSystem_homogeneous n K c hn
  have hreg := R1RegularSection.secForm_isSMulRegular_of_avoid (statementIndex n) K
    (bridgeForms n K c hn) havoid
  have hcut := hcut_of_algebraData n K c hn E V b hexp hN htower hcomm
  have hc := CountAssembly.hc_secForm_of (statementIndex n) K
    (bridgeForms n K c hn) hF havoid hcut
  have hfin := hfin_bridgeSystem_of_algebraData n K c hn E V b hexp hN
    htower hcomm
  have hZd := hZd_of_hfin_hsucc (statementIndex n) K
    (bridgeSystem n K c hn) hG hsucc hfin
  have hsum := hsum_closed (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hfin hc (hinj hfin hc)
    (hsurj hfin hc) hG hreg hZd
  have hbridge := hbridge_of_final (statementIndex n) K
    (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K)
    hG hreg hZd
  have hpos := hpos_closed (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hfin hc hG hreg hZd
  have hloc := hloc_closed (statementIndex n) K (bridgeForms n K c hn) hF
    (R1RegularSection.secForm (statementIndex n) K) hc
  refine bezout_quadrics K hn c (R1RegularSection.secForm (statementIndex n) K)
    hc hreg
    (MkSystemSESData.Hfun (statementIndex n) K (bridgeSystem n K c hn))
    (MkSystemSESData.Ffun (statementIndex n) K (bridgeSystem n K c hn)
      (mkLin (statementIndex n) K (R1RegularSection.secForm (statementIndex n) K)))
    ?_ ?_ ?_ hfilter hfin hsum hbridge hpos hloc ?_ ?_
  · intro d
    exact MkSystemSESData.hH0_quadrics (statementIndex n) K
      (bridgeSystem n K c hn) d
  · exact MkSystemSESData.hSES_quadrics (statementIndex n) K
      (bridgeSystem n K c hn) hG hsucc
  · exact MkSystemSESData.hSEC_section (statementIndex n) K
      (bridgeSystem n K c hn) hG
      (mkLin (statementIndex n) K (R1RegularSection.secForm (statementIndex n) K))
      (MkSystemSESData.mkLin_homogeneous_of (statementIndex n) K
        (R1RegularSection.secForm (statementIndex n) K))
      (CountAssembly.hsec_of_hreg (statementIndex n) K
        (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K)
        hreg)
  · intro _hG' ℓ' hc' _hreg' _hZd' _hmem' _hsmooth' _hmult' H' F' _hH0' _hSES'
      _hSEC' _hfilter' hfin' _hsum' _hbridge' _hpos'
    exact exists_another_point_of_smooth_point (statementIndex n) K
      (bridgeSystem n K c hn) _hG' ℓ' hc' _hreg' _hZd' _hmem' _hsmooth'
      _hmult' H' F' _hH0' _hSES' _hSEC' _hfilter' hfin' _hsum' _hbridge'
      _hpos'
  · exact hSecondOfNotZd_closed (statementIndex n) K
      (bridgeSystem n K c hn) hG hsucc

/-- Projective fixed point from idempotence, maximally discharged: algebra
data from the `CoordinatizationToolkit` spine, the cone point from
`bezout_at_bridge_discharged`, dehomogenization (`z ≠ 0` via `hN`,
`sq_expand`) replayed on the `CoordinatizationToolkit` spine.

conditional on the `∀`-residuals (one `FinalResiduals` per `(n, c)`)
plus the fixed-point inputs `hfin hV hN hneV htower hcomm`. The
conclusion matches `fixedPoint_of_idempotent` up to the documented
spine/`∃`-mem sugar. -/
theorem fixedPoint_of_idempotent_final (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [Module K E] [IsAlgClosed K]
    (V : Submodule K E)
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hres : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      FinalResiduals n K c hn) :
    ∃ x ∈ V, x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  obtain ⟨n, hn, hb⟩ := CoordinatizationToolkit.exists_pos_fin_basis K E V hfin hneV
  obtain ⟨b⟩ := hb
  obtain ⟨c, hexp⟩ := CoordinatizationToolkit.exists_structure_constants K E b hV
  obtain ⟨X, z, hsol, hXne⟩ := bezout_at_bridge_discharged n K c hn E V b
    hexp hN htower hcomm (hres n hn c)
  have hF : ∀ k, CoordinatizationToolkit.sqCoords K c k X = z * X k := by
    intro k
    have h := hsol k
    have h' : CoordinatizationToolkit.sqCoords K c k X - z * X k = 0 := h
    exact sub_eq_zero.mp h'
  have hz : z ≠ 0 := by
    intro hz0
    have hF0 : ∀ k, CoordinatizationToolkit.sqCoords K c k X = 0 := by
      intro k
      have h := hsol k
      have h' : CoordinatizationToolkit.sqCoords K c k X - z * X k = 0 := h
      rw [hz0, zero_mul, sub_zero] at h'
      exact h'
    have hsq0 : CoordinatizationToolkit.coordVec K E b X * CoordinatizationToolkit.coordVec K E b X
        = 0 := by
      rw [CoordinatizationToolkit.sq_expand K E b c hexp X htower hcomm]
      simp [hF0]
    have hzero : CoordinatizationToolkit.coordVec K E b X = 0 :=
      CoordinatizationToolkit.eq_zero_of_mem_sq_eq_zero K E V hN
        (CoordinatizationToolkit.coordVec_mem K E b X) hsq0
    exact hXne (CoordinatizationToolkit.coordVec_eq_zero K E b X hzero)
  refine ⟨CoordinatizationToolkit.coordVec K E b X, CoordinatizationToolkit.coordVec_mem K E b X,
    ?_, z,
    hz, ?_⟩
  · intro hzero
    exact hXne (CoordinatizationToolkit.coordVec_eq_zero K E b X hzero)
  · rw [CoordinatizationToolkit.sq_expand K E b c hexp X htower hcomm]
    unfold CoordinatizationToolkit.coordVec
    have hdist : ∀ (s : Finset (Fin n)) (f : Fin n → E),
        Finset.sum s (fun k => z • f k) = z • Finset.sum s (fun k => f k) := by
      intro s f
      induction s using Finset.induction with
      | empty => simp
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, smul_add]
    simp only [← hdist]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF k, mul_smul]

/-! ## §4 Generic `(n, F)` end-to-end corollaries -/

/-- Bézout count at `(mkSystem, secForm)` with `hZd` discharged via the
`hcontra` chain (`hfin` from `hBPF`).

Exact residual list: `[hF, hsucc, havoid, hBPF, hfilter]`. -/
theorem bezout_generic_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hBPF : BasePointFree n K F)
    (hfilter : ∃ (B : ℕ) (Cf : ℕ → Submodule K
        (sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K (mkSystem n K F)
            (mkLin n K (R1RegularSection.secForm n K)) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K (mkSystem n K F)
        (mkLin n K (R1RegularSection.secForm n K)) d = 0) :
    totalDegree n K (mkSystem n K F) (R1RegularSection.secForm n K)
      = 2 ^ (n + 1) := by
  have hG : ∀ i, ((mkSystem n K F) i).IsHomogeneous 2 :=
    fun i => MkSystemRegular.mkSystem_isHomogeneous_of n K F hF i
  have hfin := vanishingLocus_finite_mkSystem_of_bpf n K F hF hBPF
  have hZd := hZd_of_hfin_hsucc n K (mkSystem n K F) hG hsucc hfin
  exact CountAssembly.bezout_hsec_discharged n K F hF hsucc havoid hZd
    hfilter

/-- Smooth-point corollary at `(mkSystem, secForm)` with `hZd`/`hmem`/
`hsmooth`/`hmult`/`hfin`/`hfinA`/`hsum`/`hbridge`/`hpos` discharged; the
`hequiv` `LinearEquiv` residual is bypassed via the transport+`mult1`
route, so it does not appear.

Exact residual list:
`[hF, hsucc, havoid, hBPF, hfilter, hinj, hsurj]`. -/
theorem exists_another_generic_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hBPF : BasePointFree n K F)
    (hfilter : ∃ (B : ℕ) (Cf : ℕ → Submodule K
        (sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K (mkSystem n K F)
            (mkLin n K (R1RegularSection.secForm n K)) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K (mkSystem n K F)
        (mkLin n K (R1RegularSection.secForm n K)) d = 0)
    (hinj : ∀ (hfin : (vanishingLocus n K (mkSystem n K F)).Finite)
      (hc : ChartNonvanishing n K (mkSystem n K F)
        (R1RegularSection.secForm n K)),
      ChartMaxSpecInj n K (mkSystem n K F) (R1RegularSection.secForm n K)
        hfin hc)
    (hsurj : ∀ (hfin : (vanishingLocus n K (mkSystem n K F)).Finite)
      (hc : ChartNonvanishing n K (mkSystem n K F)
        (R1RegularSection.secForm n K)),
      ChartMaxSpecSurj n K (mkSystem n K F) (R1RegularSection.secForm n K)
        hfin hc) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K (mkSystem n K F)
        ∧ q ≠ distinguishedPoint n K := by
  have hG : ∀ i, ((mkSystem n K F) i).IsHomogeneous 2 :=
    fun i => MkSystemRegular.mkSystem_isHomogeneous_of n K F hF i
  have hreg := R1RegularSection.secForm_isSMulRegular_of_avoid n K F havoid
  have hcut : R1RegularSection.cutsOutOrigin n K F := hBPF
  have hc := CountAssembly.hc_secForm_of n K F hF havoid hcut
  have hfin := vanishingLocus_finite_mkSystem_of_bpf n K F hF hBPF
  have hZd := hZd_of_hfin_hsucc n K (mkSystem n K F) hG hsucc hfin
  have hmem := mem_vanishingLocus_mkSystem n K F hF
  have hsmooth := isSmoothPoint_mkSystem n K F hF
  have hmult := hmult_closed n K F hF (R1RegularSection.secForm n K) hc hfin
  have hsum := hsum_closed n K (mkSystem n K F) (R1RegularSection.secForm n K)
    hfin hc (hinj hfin hc) (hsurj hfin hc) hG hreg hZd
  have hbridge := hbridge_of_final n K (mkSystem n K F)
    (R1RegularSection.secForm n K) hG hreg hZd
  have hpos := hpos_closed n K (mkSystem n K F) (R1RegularSection.secForm n K)
    hfin hc hG hreg hZd
  refine exists_another_point_of_smooth_point n K (mkSystem n K F) hG
    (R1RegularSection.secForm n K) hc hreg hZd hmem hsmooth hmult
    (MkSystemSESData.Hfun n K (mkSystem n K F))
    (MkSystemSESData.Ffun n K (mkSystem n K F)
      (mkLin n K (R1RegularSection.secForm n K)))
    ?_ ?_ ?_ hfilter hfin hsum hbridge hpos
  · intro d
    exact MkSystemSESData.hH0_quadrics n K (mkSystem n K F) d
  · exact MkSystemSESData.hSES_quadrics n K (mkSystem n K F) hG hsucc
  · exact MkSystemSESData.hSEC_section n K (mkSystem n K F) hG
      (mkLin n K (R1RegularSection.secForm n K))
      (MkSystemSESData.mkLin_homogeneous_of n K (R1RegularSection.secForm n K))
      (CountAssembly.hsec_of_hreg n K (mkSystem n K F)
        (R1RegularSection.secForm n K) hreg)

end FinalDischargeHub
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FinalDischargeHub

open scoped BigOperators

/-! ## §5 hF-at-Ffun: `Ffun` is the section-piece finrank (unconditional)

This section closes the `hF`-at-`Ffun` residual in its exact stated form:
`∀ d, Ffun … d = finrank (sectionPiece … d)`, for arbitrary `G`/`ℓ`
(`hF_at_ffun`), hence at bridge data (`hF_at_ffun_bridge`) and at
`(mkSystem, secForm)` (`hF_at_ffun_mkSystem`), plus the `Ffun = Fsec`
bridge (`hF_ffun_eq_fsec`).

Method: piece-level third-isomorphism identification. The homogeneous-piece
forward map (`hF_homogToCone` + `secProj`, both `K`-linear) has kernel
exactly `pieceSub secIdeal` — forward by ideal absorption, reverse by
lifting the cone screw (`mk_surjective`) — so `Submodule.liftQ` gives a
`LinearEquiv` (`hF_secPieceEquiv`) between the joined-ideal quotient piece
`stagePiece secIdeal` (whose finrank is `Ffun`) and the double-quotient
submodule `sectionPiece`. Finrank equality is `LinearEquiv.finrank_eq`.
This instantiates the `stepCokerEquiv` third-iso pattern at the section
step; no homogeneous-division hypothesis is needed because the kernel
characterization is pure ideal theory on already-homogeneous lifts.

Status: unconditional (no `hsucc`/`havoid`/`hreg`/`hG`/`hZd` assumed).

## References

Mathlib v4.34.0 exact names (each grep-verified under
`.lake/packages/mathlib` before use, and already exercised in-tree):
`Submodule.liftQ`, `Submodule.ker_liftQ_eq_bot`, `Submodule.mkQ`
(`LinearAlgebra/Quotient/Basic.lean`), `Submodule.mem_sup`,
`Submodule.mem_bot`, `Submodule.coe_add`, `Submodule.coe_smul`
(`Algebra/Module/Submodule/Lattice.lean`), `LinearMap.mem_ker`
(`Algebra/Module/Submodule/Ker.lean`), `LinearEquiv.ofBijective`
(`Algebra/Module/Submodule/Equiv.lean`), `LinearEquiv.finrank_eq`
(`LinearAlgebra/Dimension/Finrank.lean`), `Ideal.mem_span_singleton'`,
`Ideal.subset_span` (`RingTheory/Ideal/Span.lean`),
`Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.mk_surjective`
(`RingTheory/Ideal/Quotient/Defs.lean`), `Ideal.Quotient.mk_algebraMap`
(`RingTheory/Ideal/Quotient/Operations.lean`), `Algebra.smul_def`
(`Algebra/Algebra/Defs.lean`), `MvPolynomial.mem_homogeneousSubmodule`
(`RingTheory/MvPolynomial/Homogeneous.lean`).

Project: `MkSystemSESData.stageIdeal`/`secIdeal`/`pieceSub`/`stagePiece`/
`Ffun`/`mem_pieceSub`, `ChartFiltration.sectionPiece`, `HilbertFunctionCount.conePiece`/
`secProj` (all imported above; no new imports).
-/

/-- The full prefix ideal is the range span (all `Fin (n+1)` indices satisfy
`j.val < n + 1`).

## References

* Core `Set.mem_image`, `Set.mem_range`, `Fin.isLt`. -/
theorem hF_stageIdeal_full (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    MkSystemSESData.stageIdeal n K G (n + 1) = Ideal.span (Set.range G) := by
  unfold MkSystemSESData.stageIdeal
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.isLt, rfl⟩

/-- The section ideal is the cone ideal plus the section generator.

## References

* `MkSystemSESData.secIdeal` (definition unfolding) + `hF_stageIdeal_full`. -/
theorem hF_secIdeal_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    MkSystemSESData.secIdeal n K G (mkLin n K ℓ)
      = Ideal.span (Set.range G) ⊔ Ideal.span {mkLin n K ℓ} := by
  unfold MkSystemSESData.secIdeal
  rw [hF_stageIdeal_full n K G]

/-- Homogeneous piece to cone piece (`K`-linear): send `x` to the cone class
of `x.val` (verbatim the `conePiece_finite` forward map).

## References

* `Ideal.Quotient.mk` (`RingTheory/Ideal/Quotient/Defs.lean`),
  `Algebra.smul_def`, `Ideal.Quotient.mk_algebraMap` (smul case, as in
  `HilbertFunctionCount.conePiece_finite`). -/
noncomputable def hF_homogToCone (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (d : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) →ₗ[K]
      ↥(conePiece n K G d) :=
  { toFun := fun x =>
      ⟨Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val, x.val, x.property, rfl⟩
    map_add' := fun x y => Subtype.ext
      (map_add (Ideal.Quotient.mk (Ideal.span (Set.range G))) x.val y.val)
    map_smul' := fun r x => by
      apply Subtype.ext
      change Ideal.Quotient.mk (Ideal.span (Set.range G)) (r • x.val)
        = r • Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val
      rw [Algebra.smul_def (R := K) (A := MvPolynomial (Fin (n + 2)) K),
        map_mul, Ideal.Quotient.mk_algebraMap K _ _,
        Algebra.smul_def (R := K) (A := coneQuotient n K G)] }

/-- Homogeneous piece to section piece (`K`-linear): `secProj` after
`hF_homogToCone`. Composition reuses both proved linearities, so no new
smul computation is needed.

## References

* `HilbertFunctionCount.secProj` (the section projection). -/
noncomputable def hF_secHomogMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) →ₗ[K]
      ↥(sectionPiece n K G ℓ d) :=
  (secProj n K G ℓ d).comp (hF_homogToCone n K G d)

/-- Value of the forward map (definitional). -/
theorem hF_secHomogMap_val (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (x : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d)) :
    (hF_secHomogMap n K G ℓ d x).val
      = Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
            Set (coneQuotient n K G)))
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val) := rfl

/-- Forward kernel inclusion: `pieceSub secIdeal` dies under the forward map
(ideal absorption: the `J`-part dies in the cone, the `span{ℓ}`-part dies
in the section since `ℓ̄` maps to `0`).

## References

* `MkSystemSESData.mem_pieceSub`, `Submodule.mem_sup`,
  `Ideal.mem_span_singleton'`, `Ideal.Quotient.eq_zero_iff_mem`,
  `Ideal.subset_span`. -/
theorem hF_ker_contains (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    MkSystemSESData.pieceSub n K (MkSystemSESData.secIdeal n K G (mkLin n K ℓ)) d
      ≤ LinearMap.ker (hF_secHomogMap n K G ℓ d) := by
  intro x hx
  rw [LinearMap.mem_ker]
  have hxmem : (x.val : MvPolynomial (Fin (n + 2)) K)
      ∈ MkSystemSESData.secIdeal n K G (mkLin n K ℓ) :=
    (MkSystemSESData.mem_pieceSub n K _ d x).mp hx
  rw [hF_secIdeal_eq n K G ℓ] at hxmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb
  have ha0 : Ideal.Quotient.mk (Ideal.span (Set.range G)) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hℓ0 : Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply Subtype.ext
  change (hF_secHomogMap n K G ℓ d x).val = 0
  rw [hF_secHomogMap_val]
  have hxeq : (x.val : MvPolynomial (Fin (n + 2)) K) = a + b := hab.symm
  rw [hxeq, map_add, map_add]
  have hbval : Ideal.Quotient.mk (Ideal.span (Set.range G)) b
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) r
        * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) := by
    conv_lhs => rw [← hr]
    rw [map_mul]
  rw [hbval, map_mul, hℓ0, mul_zero, ha0, map_zero, zero_add]

/-- Reverse kernel inclusion: a homogeneous lift mapping to `0` in the
section lies in `secIdeal` (lift the cone screw `c` with `mk_surjective`,
so `p - r * ℓ ∈ span range` and `p = (p - r * ℓ) + r * ℓ`).

## References

* `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_span_singleton'`,
  `Ideal.Quotient.mk_surjective`, `Submodule.mem_sup`. -/
theorem hF_ker_reverse (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    LinearMap.ker (hF_secHomogMap n K G ℓ d)
      ≤ MkSystemSESData.pieceSub n K
        (MkSystemSESData.secIdeal n K G (mkLin n K ℓ)) d := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hval0 : Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val) = 0 := by
    have h0 : (hF_secHomogMap n K G ℓ d x).val = 0 := congrArg Subtype.val hx
    rwa [hF_secHomogMap_val] at h0
  have hmem : Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val
      ∈ Ideal.span ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hval0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range G)) c
  have hc2 : Ideal.Quotient.mk (Ideal.span (Set.range G)) (r * mkLin n K ℓ)
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val := by
    rw [map_mul, hr]
    exact hc
  have hdiff : (x.val : MvPolynomial (Fin (n + 2)) K) - r * mkLin n K ℓ
      ∈ Ideal.span (Set.range G) := by
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range G))
        ((x.val : MvPolynomial (Fin (n + 2)) K) - r * mkLin n K ℓ) = 0 := by
      rw [map_sub, hc2, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  rw [MkSystemSESData.mem_pieceSub, hF_secIdeal_eq n K G ℓ]
  refine Submodule.mem_sup.mpr ⟨x.val - r * mkLin n K ℓ, hdiff, r * mkLin n K ℓ,
    Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩, sub_add_cancel _ _⟩

/-- The lifted map on the joined-ideal quotient piece, via `Submodule.liftQ`.

## References

* `Submodule.liftQ` (`LinearAlgebra/Quotient/Basic.lean`). -/
noncomputable def hF_secPieceLift (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    MkSystemSESData.stagePiece n K
        (MkSystemSESData.secIdeal n K G (mkLin n K ℓ)) d →ₗ[K]
      ↥(sectionPiece n K G ℓ d) :=
  (MkSystemSESData.pieceSub n K
    (MkSystemSESData.secIdeal n K G (mkLin n K ℓ)) d).liftQ
    (hF_secHomogMap n K G ℓ d) (hF_ker_contains n K G ℓ d)

/-- Surjectivity: every section-piece element has a homogeneous lift `p`,
so it is hit by `mkQ ⟨p, _⟩`.

## References

* `MvPolynomial.mem_homogeneousSubmodule`, `Submodule.liftQ` (`rfl`
  computation on `mkQ`). -/
theorem hF_secPieceLift_surj (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Function.Surjective (hF_secPieceLift n K G ℓ d) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := y.property
  have hpmem : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d :=
    (MvPolynomial.mem_homogeneousSubmodule d p).mpr hp
  refine ⟨(MkSystemSESData.pieceSub n K
    (MkSystemSESData.secIdeal n K G (mkLin n K ℓ)) d).mkQ ⟨p, hpmem⟩, ?_⟩
  have hlift : hF_secPieceLift n K G ℓ d
      ((MkSystemSESData.pieceSub n K
        (MkSystemSESData.secIdeal n K G (mkLin n K ℓ)) d).mkQ ⟨p, hpmem⟩)
      = hF_secHomogMap n K G ℓ d ⟨p, hpmem⟩ := rfl
  rw [hlift]
  apply Subtype.ext
  exact hpy

/-- Injectivity: `ker liftQ = ⊥` from the reverse inclusion.

## References

* `Submodule.ker_liftQ_eq_bot`, `Submodule.mem_bot`, `LinearMap.mem_ker`. -/
theorem hF_secPieceLift_inj (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Function.Injective (hF_secPieceLift n K G ℓ d) := by
  have hker : LinearMap.ker (hF_secPieceLift n K G ℓ d) = ⊥ := by
    unfold hF_secPieceLift
    rw [Submodule.ker_liftQ_eq_bot _ _ _ (hF_ker_reverse n K G ℓ d)]
  intro u v huv
  have h0 : u - v ∈ LinearMap.ker (hF_secPieceLift n K G ℓ d) := by
    rw [LinearMap.mem_ker, map_sub, huv, sub_self]
  rw [hker] at h0
  have hzero : u - v = 0 := (Submodule.mem_bot K).mp h0
  exact sub_eq_zero.mp hzero

/-- Piece-level third-isomorphism equiv: the joined-ideal quotient piece
(`Ffun` side) is the double-quotient submodule (`sectionPiece` side).

## References

* `LinearEquiv.ofBijective`. -/
noncomputable def hF_secPieceEquiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    MkSystemSESData.stagePiece n K
        (MkSystemSESData.secIdeal n K G (mkLin n K ℓ)) d ≃ₗ[K]
      ↥(sectionPiece n K G ℓ d) :=
  LinearEquiv.ofBijective (hF_secPieceLift n K G ℓ d)
    ⟨hF_secPieceLift_inj n K G ℓ d, hF_secPieceLift_surj n K G ℓ d⟩

/-- hF-at-Ffun (exact residual, unconditional): `Ffun` is the section-piece
finrank, for arbitrary `G`/`ℓ`. No regularity/homogeneity/dimension input.

## References

* `MkSystemSESData.Ffun` (definition), `LinearEquiv.finrank_eq`. -/
theorem hF_at_ffun (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    ∀ d, MkSystemSESData.Ffun n K G (mkLin n K ℓ) d
      = Module.finrank K ↥(sectionPiece n K G ℓ d) := by
  intro d
  unfold MkSystemSESData.Ffun
  exact LinearEquiv.finrank_eq (hF_secPieceEquiv n K G ℓ d)

/-- hF-at-Ffun at bridge data (`statementIndex`/`bridgeSystem`/`secForm`). -/
theorem hF_at_ffun_bridge (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ d, MkSystemSESData.Ffun (statementIndex n) K (bridgeSystem n K c hn)
        (mkLin (statementIndex n) K (R1RegularSection.secForm (statementIndex n) K)) d
      = Module.finrank K ↥(sectionPiece (statementIndex n) K
        (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K) d) :=
  hF_at_ffun (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K)

/-- hF-at-Ffun at `(mkSystem, secForm)`. -/
theorem hF_at_ffun_mkSystem (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) :
    ∀ d, MkSystemSESData.Ffun n K (mkSystem n K F)
        (mkLin n K (R1RegularSection.secForm n K)) d
      = Module.finrank K ↥(sectionPiece n K
        (mkSystem n K F) (R1RegularSection.secForm n K) d) :=
  hF_at_ffun n K (mkSystem n K F) (R1RegularSection.secForm n K)

/-- `Ffun = Fsec` bridge (pointwise): the SES `Ffun` coincides with the
geometric `Fsec` witness (`Fsec` is `sectionPiece` finrank by definition),
so `Fsec` vanishing/filtration transfers to `Ffun`.

## References

* `HilbertFunctionCount.Fsec` (definition: `rfl` after `hF_at_ffun`). -/
theorem hF_ffun_eq_fsec (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    ∀ d, MkSystemSESData.Ffun n K G (mkLin n K ℓ) d = Fsec n K G ℓ d := by
  intro d
  rw [hF_at_ffun n K G ℓ d]
  rfl

end FinalDischargeHub
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FinalDischargeHub

open scoped BigOperators

/-! ## §6 k=2 discharge: step hsucc/havoid via T3-shape + hinj/hsurj closure (proof)

This section threads the `k = 2` pair-unmixed conclusion (exact
`Geometry/K2UnmixednessEndgame.unmixed_pair_of_depthEq` conclusion spelling,
`Geometry/K2UnmixednessEndgame.lean`: `P ∈ J.minimalPrimes`, taken as an explicit
hypothesis since U1 proves `cond-[hker]` in parallel and cannot be
imported) through the conclusion-exact interface
(`GradeDepthFragment.unmixed_of_grade_of_depthEq`, `GradeDepthFragment.lean`) into the
per-step pair (`ResultantLemmas.hsuccStep_mkSystem_of_hunmixed`,
`ResultantLemmas.lean`, hlow-discharged form) to yield step
`hsucc` for 2-element families, plus the havoid reduction
(`AvoidanceApply.avoid_of_hunmixed_ge2`, `AvoidanceApply.lean`), plus
hinj/hsurj closure via the ChartFiltration ∀-forms
(`chartMaxSpecInj_forall`, `ChartFiltration.lean`, unconditional;
`chartMaxSpecSurj_forall`, `ChartFiltration.lean`, conditional on
`[IsAlgClosed K, hfinA, hG]` with `hfinA` closed in-file via `hfinA_closed`
from `[hG, hreg, hZd]`).

`hlow` is closed upstream (`ResultantLemmas.hlow_general` wiring
`HeightLowerBound.hlow_uncond`, `HeightLowerBound.lean`), so the `k = 2`
step lemmas below take no `hlow` hypothesis (stronger than the
interface, which retains `hlow` for stability; the form is used).
`hdepth` (`GradeDepthFragment.DepthEqDimAt`, `GradeDepthFragment.lean`) is upstream of T3
(T3 discharges the pair conclusion from `hdepth`) and is not a binder here.
`hfilter` stays an explicit hypothesis (parallel lane owns it).

New masters `bezout_at_bridge_hinj_hsurj_closed` and
`fixedPoint_of_idempotent_hinj_hsurj_closed` close hinj/hsurj via the above
forms, leaving `[hsucc, havoid, hfilter]` (+ algebra/fixed-point inputs).
Full reduction of `hsucc`/`havoid` for `bridgeSystem` (length `n`) to the
`k = 2` step outputs is not claimed: `k > 2` steps remain open, and the
step family `h` (length `k ≤ n`) is distinct from `bridgeSystem` (length
`n + 1` in `Bezout` indexing).

Imports added this lane (verified acyclic: nothing imports this file, so all
new edges terminate here): `Regularity.Avoid.AvoidanceApply`,
`Regularity.Grade.GradeDepthFragment`, `Regularity.Avoid.ResultantLemmas`.
`Geometry.K2UnmixednessEndgame` is
deliberately not imported (parallel U1 development); its conclusion spelling
is reproduced verbatim as an explicit hypothesis binder.

Status: `hsuccStep_k2_of_pair_unmixed` conditional-exact on
`[hunmixed_pair]` + ctx `[hreg, hZd, hk]` (`hlow` closed);
`avoid_k2_of_pair_unmixed` conditional-exact on `[hunmixed_pair]` + ctx
`[hreg, hZd, hk]` (`hsucc` derived, `hlow` closed);
`hinj_bridge_closed` unconditional; `hsurj_bridge_of_regCtx` conditional on
`[hreg, hZd]` (`hG` closed at bridge); masters conditional-exact on
`[hsucc, havoid, hfilter]` (hinj/hsurj closed). Overall lane: partial
(`k > 2` open, `hfilter` explicit, full-`G` `hsucc`/`havoid` still explicit).

## References

* `Geometry/K2UnmixednessEndgame.lean` (`unmixed_pair_of_depthEq` conclusion
  `P ∈ J.minimalPrimes`, reproduced as `hunmixed_pair`).
* `GradeDepthFragment.lean` (`unmixed_of_grade_of_depthEq` conclusion shape,
  identical `P ∈ J.minimalPrimes`; `GradeDepthFragment.lean` `DepthEqDimAt`
  upstream of T3).
* `ResultantLemmas.lean` (`hsuccStep_mkSystem_of_hunmixed` threading
  interface) and (`..._uncond_hlow`, `hlow` discharged via
  `hlow_general`); `AvoidanceApply.lean` (`hsucc_of_step_outputs`
  repackaging) and (`avoid_of_hunmixed_ge2` reduction).
* `ChartFiltration.lean` (`chartMaxSpecInj_forall`) and
  (`chartMaxSpecSurj_forall`); in-file `hfinA_closed` (§2).
* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`) for the
  membership-to-instance adaptation (as at `ResultantLemmas.lean`).

Residual register (verbatim): closed this lane: [hinj (∀-form,
unconditional)]; [hsurj (∀-form, conditional on `[hreg, hZd]`
via + `hfinA_closed`, `hG` closed at bridge)]; [hlow
(step-independent catenary, closed upstream via `hlow_general` wiring
`hlow_uncond`)]; [k=2 step hsucc (from `hunmixed_pair` + ctx)];
[k=2 step avoidance (from `hunmixed_pair` + ctx, `hsucc`)]. Open: [hunmixed-conclusion for
`k > 2` (general-`k` baby-AB,
open)]; [hfilter (`Ffun`-filtration, parallel lane, stays explicit)];
[hsucc for `bridgeSystem`/`mkSystem` full family (quotient-side rungs `≥ 1`,
still explicit)]; [havoid for `secForm` (specific-form Ass-avoidance, still
explicit)]; [hdepth (deep-core (iii), upstream of T3, not a binder here)].
context: [hreg (per-step `IsSMulRegular` outputs)], [hZd
(`IsZeroDimensional`)], [hk (`2 ≤ n` for `k = 2` steps)].
-/

/-- hsuccStep for `k = 2` from the T3 pair-unmixed conclusion (exact
conclusion spelling with `J := Ideal.span (Set.range h)`): per-step
`IsSMulRegular` outputs repackage to `SuccessiveSMulRegular h`, and every
`Ass` prime of the step quotient has proper `comboLin` pullback. `hlow` is
not a hypothesis (closed upstream via `hlow_general`); the form of
the interface is used.

Conditional on exactly `[hunmixed_pair]` + ctx `[hreg, hZd, hk]`.

## References

* `ResultantLemmas.hsuccStep_mkSystem_of_hunmixed_uncond_hlow`
  (`ResultantLemmas.lean`, discharging `hlow` in).
* `GradeDepthFragment.unmixed_of_grade_of_depthEq` (`GradeDepthFragment.lean`) for the
  `hunmixed` conclusion shape; `BabyABPair.unmixed_pair_of_depthEq`
  (`Geometry/K2UnmixednessEndgame.lean`) for the `k = 2` source spelling. -/
theorem hsuccStep_k2_of_pair_unmixed (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (h : Fin 2 → MvPolynomial (Fin (n + 2)) K)
    (hk : 2 ≤ n)
    (hreg : ∀ j : Fin 2, IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn h)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))
      (h j))
    (hunmixed_pair : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range h)) →
      P ∈ (Ideal.span (Set.range h)).minimalPrimes) :
    RegularityBridge.SuccessiveSMulRegular h ∧
      ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)),
        P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
            (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)))) →
        Submodule.comap (comboLin K (mkSystem n K F))
          (Submodule.restrictScalars K
            (P : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ :=
  hsuccStep_mkSystem_of_hunmixed_uncond_hlow n K F hZd 2 hk h hreg
    hunmixed_pair

/-- Step avoidance for `k = 2` from the T3 pair-unmixed conclusion (exact
conclusion spelling with `J` param + `hJ`, as): no `Ass`
prime of the step quotient contains `span G`. `hsucc` for `q` is derived
from `hreg` (unconditional repackaging); `hlow` is supplied by
`hlow_general` (closed upstream).

Conditional on exactly `[hunmixed_pair]` + ctx `[hreg, hZd, hk]`.

## References

* `AvoidanceApply.avoid_of_hunmixed_ge2` (`AvoidanceApply.lean`).
* `AvoidanceApply.hsucc_of_step_outputs` (`AvoidanceApply.lean`).
* `ResultantLemmas.hlow_general` (`ResultantLemmas.lean`).
* `BabyABPair.unmixed_pair_of_depthEq` (`Geometry/K2UnmixednessEndgame.lean`) for the
  `hunmixed_pair` spelling; `AssociatedPrimes.mem_iff` for the
  membership-to-instance adaptation. -/
theorem avoid_k2_of_pair_unmixed (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (q : Fin 2 → MvPolynomial (Fin (n + 2)) K)
    (hk : 2 ≤ n)
    (hreg : ∀ j : Fin 2, IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn q)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))
      (q j))
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hunmixed_pair : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ J) →
      P ∈ J.minimalPrimes) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range G) ≤ P) := by
  have hsuccStep := AvoidanceApply.hsucc_of_step_outputs q hreg
  have hunmixed_mem : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes := by
    intro P hPm
    exact @hunmixed_pair P (AssociatedPrimes.mem_iff.mp hPm).isPrime hPm
  exact AvoidanceApply.avoid_of_hunmixed_ge2 n K G hZd 2 hk q hsuccStep J hJ
    (hlow_general n K G) (fun _ => hunmixed_mem)

/-- `hinj` ∀-form at bridge data, closed unconditionally.


## References

* `chartMaxSpecInj_forall` (`ChartFiltration.lean`). -/
theorem hinj_bridge_closed (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ (hfin : (vanishingLocus (statementIndex n) K
          (bridgeSystem n K c hn)).Finite)
        (hc : ChartNonvanishing (statementIndex n) K
          (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K)),
        ChartMaxSpecInj (statementIndex n) K (bridgeSystem n K c hn)
          (R1RegularSection.secForm (statementIndex n) K) hfin hc :=
  chartMaxSpecInj_forall (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K)

/-- `hsurj` ∀-form at bridge data from R1/zero-dim context: fed with
`hfinA_closed` (`hG` closed at bridge via `bridgeSystem_homogeneous`).

Conditional on exactly `[hreg, hZd]`.

## References

* `chartMaxSpecSurj_forall` (`ChartFiltration.lean`).
* In-file `hfinA_closed` (§2); `bridgeSystem_homogeneous`
  (`FixedPointFromBezout.lean`). -/
theorem hsurj_bridge_of_regCtx (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hreg : IsSMulRegular (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
      (Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
        (mkLin (statementIndex n) K (R1RegularSection.secForm (statementIndex n) K))))
    (hZd : IsZeroDimensional (statementIndex n) K (bridgeSystem n K c hn)) :
    ∀ (hfin : (vanishingLocus (statementIndex n) K
          (bridgeSystem n K c hn)).Finite)
        (hc : ChartNonvanishing (statementIndex n) K
          (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K)),
        ChartMaxSpecSurj (statementIndex n) K (bridgeSystem n K c hn)
          (R1RegularSection.secForm (statementIndex n) K) hfin hc := by
  have hG : ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2 :=
    bridgeSystem_homogeneous n K c hn
  have hfinA := hfinA_closed (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hG hreg hZd
  exact chartMaxSpecSurj_forall (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hfinA hG

/-- Bézout cone point at bridge data with hinj/hsurj closed: `hinj` via
`hinj_bridge_closed` (unconditional), `hsurj` via `hsurj_bridge_of_regCtx`
with `hreg` from `havoid` and `hZd` from the `hcontra` chain, then the §3
master.

Exact residual list: `[hsucc, havoid, hfilter]` (+ algebra data).

Conditional on exactly `[hsucc, havoid, hfilter]`.

## References

* §3 `bezout_at_bridge_discharged`; §6 `hinj_bridge_closed`,
  `hsurj_bridge_of_regCtx`; §2 `hZd_of_hfin_hsucc`.
* `R1RegularSection.secForm_isSMulRegular_of_avoid` (`R1RegularSection.lean`);
  `hfin_bridgeSystem_of_algebraData` (`ProjectiveFiniteness.lean`). -/
theorem bezout_at_bridge_hinj_hsurj_closed (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn))
    (havoid : ∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
        Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P)
    (hfilter : ∃ (B : ℕ) (Cf : ℕ → Submodule K
          (sectionQuotient (statementIndex n) K (bridgeSystem n K c hn)
            (R1RegularSection.secForm (statementIndex n) K))),
        Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
        (∀ d, d ≤ B →
          Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
            + MkSystemSESData.Ffun (statementIndex n) K
              (bridgeSystem n K c hn)
              (mkLin (statementIndex n) K
                (R1RegularSection.secForm (statementIndex n) K)) d) ∧
        ∀ d, B < d → MkSystemSESData.Ffun (statementIndex n) K
          (bridgeSystem n K c hn)
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) d = 0) :
    ∃ (X : Fin n → K) (z : K),
      (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0 := by
  have hG : ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2 :=
    bridgeSystem_homogeneous n K c hn
  have hreg := R1RegularSection.secForm_isSMulRegular_of_avoid (statementIndex n) K
    (bridgeForms n K c hn) havoid
  have hfin := hfin_bridgeSystem_of_algebraData n K c hn E V b hexp hN
    htower hcomm
  have hZd := hZd_of_hfin_hsucc (statementIndex n) K
    (bridgeSystem n K c hn) hG hsucc hfin
  have hinj := hinj_bridge_closed n K c hn
  have hsurj := hsurj_bridge_of_regCtx n K c hn hreg hZd
  exact bezout_at_bridge_discharged n K c hn E V b hexp hN htower hcomm
    ⟨hsucc, havoid, hfilter, hinj, hsurj⟩

/-- Projective fixed point from idempotence with hinj/hsurj closed: the
`CoordinatizationToolkit` spine supplies algebra data for the spine `(n, c)`, the §6
Bezout master supplies the cone point from the 3-residual bundle at that
`(n, c)`, and dehomogenization replays on the spine.

conditional on the 3-residual ∀-form (one `(hsucc, havoid, hfilter)` per
`(n, c)`) plus the fixed-point inputs `hfin hV hN hneV htower hcomm`.

Conditional on exactly `[hsucc, havoid, hfilter]` (∀-form).

## References

* §6 `bezout_at_bridge_hinj_hsurj_closed`; `CoordinatizationToolkit` spine
  (`exists_pos_fin_basis`, `exists_structure_constants`, `sqCoords`,
  `coordVec`, `sq_expand`, `eq_zero_of_mem_sq_eq_zero`,
  `coordVec_eq_zero`, `coordVec_mem`). -/
theorem fixedPoint_of_idempotent_hinj_hsurj_closed (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [Module K E] [IsAlgClosed K]
    (V : Submodule K E)
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hres3 : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
      (∀ P ∈ associatedPrimes
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
          Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
            (mkLin (statementIndex n) K
              (R1RegularSection.secForm (statementIndex n) K)) ∉ P) ∧
      (∃ (B : ℕ) (Cf : ℕ → Submodule K
            (sectionQuotient (statementIndex n) K (bridgeSystem n K c hn)
              (R1RegularSection.secForm (statementIndex n) K))),
          Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
          (∀ d, d ≤ B →
            Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
              + MkSystemSESData.Ffun (statementIndex n) K
                (bridgeSystem n K c hn)
                (mkLin (statementIndex n) K
                  (R1RegularSection.secForm (statementIndex n) K)) d) ∧
          ∀ d, B < d → MkSystemSESData.Ffun (statementIndex n) K
            (bridgeSystem n K c hn)
            (mkLin (statementIndex n) K
              (R1RegularSection.secForm (statementIndex n) K)) d = 0)) :
    ∃ x ∈ V, x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  obtain ⟨n, hn, hb⟩ := CoordinatizationToolkit.exists_pos_fin_basis K E V hfin hneV
  obtain ⟨b⟩ := hb
  obtain ⟨c, hexp⟩ := CoordinatizationToolkit.exists_structure_constants K E b hV
  obtain ⟨hsucc, havoid, hfilter⟩ := hres3 n hn c
  obtain ⟨X, z, hsol, hXne⟩ := bezout_at_bridge_hinj_hsurj_closed n K c hn E V b
    hexp hN htower hcomm hsucc havoid hfilter
  have hF : ∀ k, CoordinatizationToolkit.sqCoords K c k X = z * X k := by
    intro k
    have h := hsol k
    have h' : CoordinatizationToolkit.sqCoords K c k X - z * X k = 0 := h
    exact sub_eq_zero.mp h'
  have hz : z ≠ 0 := by
    intro hz0
    have hF0 : ∀ k, CoordinatizationToolkit.sqCoords K c k X = 0 := by
      intro k
      have h := hsol k
      have h' : CoordinatizationToolkit.sqCoords K c k X - z * X k = 0 := h
      rw [hz0, zero_mul, sub_zero] at h'
      exact h'
    have hsq0 : CoordinatizationToolkit.coordVec K E b X * CoordinatizationToolkit.coordVec K E b X
        = 0 := by
      rw [CoordinatizationToolkit.sq_expand K E b c hexp X htower hcomm]
      simp [hF0]
    have hzero : CoordinatizationToolkit.coordVec K E b X = 0 :=
      CoordinatizationToolkit.eq_zero_of_mem_sq_eq_zero K E V hN
        (CoordinatizationToolkit.coordVec_mem K E b X) hsq0
    exact hXne (CoordinatizationToolkit.coordVec_eq_zero K E b X hzero)
  refine ⟨CoordinatizationToolkit.coordVec K E b X, CoordinatizationToolkit.coordVec_mem K E b X,
    ?_, z,
    hz, ?_⟩
  · intro hzero
    exact hXne (CoordinatizationToolkit.coordVec_eq_zero K E b X hzero)
  · rw [CoordinatizationToolkit.sq_expand K E b c hexp X htower hcomm]
    unfold CoordinatizationToolkit.coordVec
    have hdist : ∀ (s : Finset (Fin n)) (f : Fin n → E),
        Finset.sum s (fun k => z • f k) = z • Finset.sum s (fun k => f k) := by
      intro s f
      induction s using Finset.induction with
      | empty => simp
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, smul_add]
    simp only [← hdist]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF k, mul_smul]

#print axioms hsuccStep_k2_of_pair_unmixed
#print axioms avoid_k2_of_pair_unmixed
#print axioms hinj_bridge_closed
#print axioms hsurj_bridge_of_regCtx
#print axioms bezout_at_bridge_hinj_hsurj_closed
#print axioms fixedPoint_of_idempotent_hinj_hsurj_closed

end FinalDischargeHub
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FinalDischargeHub

open scoped BigOperators

/-! ## §7 hfilter discharge at bridge data (proof)

This section closes the `FinalResiduals` `hfilter` conjunct (`Ffun`-form)
at bridge data by applying the §5 third-isomorphism bridge
(`hF_ffun_eq_fsec`, unconditional) into the Regularity master
(`hfilter_ffun_of_final`, `EliminationFilter.lean`, conditional-exact
`[hFbridge]`). The geometric inputs are the closed feeds: `hreg` from
`havoid` (`secForm_isSMulRegular_of_avoid`), `hZd` from `[hsucc, hfin]`
(`hZd_of_hfin_hsucc` with `hfin` from algebra data), `hG` from
`bridgeSystem_homogeneous`.

New masters `bezout_at_bridge_hfilter_closed` and
`fixedPoint_of_idempotent_hfilter_closed` restate the §6 masters
 with `hfilter` discharged, leaving
`[hsucc-full, havoid-secForm]` (+ ctx). No existing declaration is
modified.

Import added this lane (verified acyclic: no file under
`Bezout/Regularity`, `Bezout/Geometry`, or `Bezout/Core` imports
`Appendix_FixedPoint.BezoutChain.Bridge`, and nothing imports this file, so the new edge terminates
here): `Regularity.Koszul.EliminationFilter`.

Status: `hfilter_bridge_closed` conditional-exact on
`[hsucc-full, havoid-secForm]` + ctx `[algebra data]`; both new masters
conditional-exact on `[hsucc-full, havoid-secForm]` (+ inputs).

## References

* `Appendix_FixedPoint.BezoutChain.hfilter_ffun_of_final` (`EliminationFilter.lean`).
* In-file `hF_ffun_eq_fsec` (§5), `hZd_of_hfin_hsucc` (§2),
  `bezout_at_bridge_hinj_hsurj_closed` (§6), `bezout_at_bridge_discharged`
  (§3), `fixedPoint_of_idempotent_hinj_hsurj_closed` (§6).
* `R1RegularSection.secForm_isSMulRegular_of_avoid` (`R1RegularSection.lean`);
  `hfin_bridgeSystem_of_algebraData` (`ProjectiveFiniteness.lean`);
  `bridgeSystem_homogeneous` (`FixedPointFromBezout.lean`).

Residual register (verbatim): closed this lane: [hfilter (`Ffun`-filtration
at bridge data, via `EliminationFilter.lean` + §5 bridge, conditional on
`[hsucc-full, havoid-secForm]` + ctx `[algebra data]`)]. Open: [hsucc for
`bridgeSystem` full family (quotient-side rungs `≥ 1`, still explicit)];
[havoid for `secForm` (specific-form Ass-avoidance, still explicit)].
context: [algebra data (`V b hexp hN htower hcomm`) for `hfin`;
fixed-point inputs (`hfin hV hN hneV htower hcomm`) for the spine].
-/

/-- `hfilter` (`Ffun`-form) at bridge data from `[hsucc-full,
havoid-secForm]` + algebra-data ctx: `hreg` from `havoid`, `hZd` from
`[hsucc, hfin]`, `hG` closed at bridge, `hFbridge` closed by §5, fed into
`hfilter_ffun_of_final`.

Conditional on exactly `[hsucc-full, havoid-secForm]` + ctx
`[algebra data]`.

## References

* `Appendix_FixedPoint.BezoutChain.hfilter_ffun_of_final` (`EliminationFilter.lean`).
* In-file `hF_ffun_eq_fsec` (§5), `hZd_of_hfin_hsucc` (§2).
* `R1RegularSection.secForm_isSMulRegular_of_avoid` (`R1RegularSection.lean`);
  `hfin_bridgeSystem_of_algebraData` (`ProjectiveFiniteness.lean`);
  `bridgeSystem_homogeneous` (`FixedPointFromBezout.lean`). -/
theorem hfilter_bridge_closed (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn))
    (havoid : ∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
        Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P) :
    ∃ (B : ℕ) (Cf : ℕ → Submodule K
          (sectionQuotient (statementIndex n) K (bridgeSystem n K c hn)
            (R1RegularSection.secForm (statementIndex n) K))),
        Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
        (∀ d, d ≤ B →
          Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
            + MkSystemSESData.Ffun (statementIndex n) K
              (bridgeSystem n K c hn)
              (mkLin (statementIndex n) K
                (R1RegularSection.secForm (statementIndex n) K)) d) ∧
        ∀ d, B < d → MkSystemSESData.Ffun (statementIndex n) K
          (bridgeSystem n K c hn)
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) d = 0 := by
  have hG : ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2 :=
    bridgeSystem_homogeneous n K c hn
  have hreg := R1RegularSection.secForm_isSMulRegular_of_avoid (statementIndex n) K
    (bridgeForms n K c hn) havoid
  have hfin := hfin_bridgeSystem_of_algebraData n K c hn E V b hexp hN
    htower hcomm
  have hZd := hZd_of_hfin_hsucc (statementIndex n) K
    (bridgeSystem n K c hn) hG hsucc hfin
  exact hfilter_ffun_of_final (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hreg hZd hG
    (hF_ffun_eq_fsec (statementIndex n) K (bridgeSystem n K c hn)
      (R1RegularSection.secForm (statementIndex n) K))

/-- Bézout cone point at bridge data with `hfilter` closed (§7 restatement
of the §6 master): `hfilter_bridge_closed` supplies the `hfilter` input
from `[hsucc, havoid]`, then the §6 master.

Exact residual list: `[hsucc-full, havoid-secForm]` (+ algebra data).

Conditional on exactly `[hsucc-full, havoid-secForm]`.

## References

* §7 `hfilter_bridge_closed`; §6 `bezout_at_bridge_hinj_hsurj_closed`. -/
theorem bezout_at_bridge_hfilter_closed (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn))
    (havoid : ∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
        Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P) :
    ∃ (X : Fin n → K) (z : K),
      (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0 := by
  have hfilter := hfilter_bridge_closed n K c hn E V b hexp hN htower hcomm
    hsucc havoid
  exact bezout_at_bridge_hinj_hsurj_closed n K c hn E V b hexp hN htower
    hcomm hsucc havoid hfilter

/-- Projective fixed point from idempotence with `hfilter` closed (§7
restatement of the §6 master): the `CoordinatizationToolkit` spine supplies algebra
data for the spine `(n, c)`, the §7 Bézout master supplies the cone point
from the 2-residual bundle at that `(n, c)`, and dehomogenization replays
on the spine.

conditional on the 2-residual ∀-form (one `(hsucc, havoid)` per `(n, c)`)
plus the fixed-point inputs `hfin hV hN hneV htower hcomm`.

Conditional on exactly `[hsucc-full, havoid-secForm]` (∀-form).

## References

* §7 `bezout_at_bridge_hfilter_closed`; `CoordinatizationToolkit` spine
  (`exists_pos_fin_basis`, `exists_structure_constants`, `sqCoords`,
  `coordVec`, `sq_expand`, `eq_zero_of_mem_sq_eq_zero`,
  `coordVec_eq_zero`, `coordVec_mem`). -/
theorem fixedPoint_of_idempotent_hfilter_closed (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [Module K E] [IsAlgClosed K]
    (V : Submodule K E)
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hres2 : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
      (∀ P ∈ associatedPrimes
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
          Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
            (mkLin (statementIndex n) K
              (R1RegularSection.secForm (statementIndex n) K)) ∉ P)) :
    ∃ x ∈ V, x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  obtain ⟨n, hn, hb⟩ := CoordinatizationToolkit.exists_pos_fin_basis K E V hfin hneV
  obtain ⟨b⟩ := hb
  obtain ⟨c, hexp⟩ := CoordinatizationToolkit.exists_structure_constants K E b hV
  obtain ⟨hsucc, havoid⟩ := hres2 n hn c
  obtain ⟨X, z, hsol, hXne⟩ := bezout_at_bridge_hfilter_closed n K c hn E V b
    hexp hN htower hcomm hsucc havoid
  have hF : ∀ k, CoordinatizationToolkit.sqCoords K c k X = z * X k := by
    intro k
    have h := hsol k
    have h' : CoordinatizationToolkit.sqCoords K c k X - z * X k = 0 := h
    exact sub_eq_zero.mp h'
  have hz : z ≠ 0 := by
    intro hz0
    have hF0 : ∀ k, CoordinatizationToolkit.sqCoords K c k X = 0 := by
      intro k
      have h := hsol k
      have h' : CoordinatizationToolkit.sqCoords K c k X - z * X k = 0 := h
      rw [hz0, zero_mul, sub_zero] at h'
      exact h'
    have hsq0 : CoordinatizationToolkit.coordVec K E b X * CoordinatizationToolkit.coordVec K E b X
        = 0 := by
      rw [CoordinatizationToolkit.sq_expand K E b c hexp X htower hcomm]
      simp [hF0]
    have hzero : CoordinatizationToolkit.coordVec K E b X = 0 :=
      CoordinatizationToolkit.eq_zero_of_mem_sq_eq_zero K E V hN
        (CoordinatizationToolkit.coordVec_mem K E b X) hsq0
    exact hXne (CoordinatizationToolkit.coordVec_eq_zero K E b X hzero)
  refine ⟨CoordinatizationToolkit.coordVec K E b X, CoordinatizationToolkit.coordVec_mem K E b X,
    ?_, z,
    hz, ?_⟩
  · intro hzero
    exact hXne (CoordinatizationToolkit.coordVec_eq_zero K E b X hzero)
  · rw [CoordinatizationToolkit.sq_expand K E b c hexp X htower hcomm]
    unfold CoordinatizationToolkit.coordVec
    have hdist : ∀ (s : Finset (Fin n)) (f : Fin n → E),
        Finset.sum s (fun k => z • f k) = z • Finset.sum s (fun k => f k) := by
      intro s f
      induction s using Finset.induction with
      | empty => simp
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, smul_add]
    simp only [← hdist]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF k, mul_smul]

#print axioms hfilter_bridge_closed
#print axioms bezout_at_bridge_hfilter_closed
#print axioms fixedPoint_of_idempotent_hfilter_closed

end FinalDischargeHub
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FinalDischargeHub

open scoped BigOperators

/-! ## §8 general-k discharge: step hsucc/havoid + R2 via (proof)

This section lifts the §6 `k = 2` step outputs to general `k` via the
hbaby-closed general-`k` corollaries
(`GradeUnmixedBridge.heightDrop_of_chain_depth` / `unmixed_of_chain_depth`,
`Regularity/Grade/GradeUnmixedBridge.lean`), following the pattern.

Does general-`k` hsuccStep exist? Yes in `hunmixed`-conditional form:
`hsuccStep_mkSystem_of_hunmixed` (`ResultantLemmas.lean`, general `k`
with `(hk : k ≤ n)`) and its `hlow`-discharged form are already
general-`k` — no new rung induction is needed for the step (the per-step
`hreg` outputs are supplied as context, repackaged). What is new
here is discharging the `hunmixed` input itself from `hdepth` via the
hbaby-closed,
yielding general-`k` step hsucc/havoid conditional-exact on
`[hdepth-general-k-shape]` (+ ctx `[hreg, hZd, hk]`), plus the narrowed
full-family (R2 existence via change-of-basis) conditional-exact on
`[hdepth_all]` (+ ctx `[hF/hG, hZd]`).

Chain per `(k, q, J)`: `hreg` → `hsucc` (unconditional) →
`hunmixed` (hbaby-closed from chain + `hdepth`) → step
pair (`hlow` closed) / avoidance (`hlow`
via).
R2 feeds the same `hunmixed` discharge into the `hunmixed_ge2` binders of.

Full fixed-`G` `hsucc`/`havoid` (the exact open shapes/:1387/
: `hsucc : SuccessiveSMulRegular bridgeSystem` for the fixed
length-`n` family + `havoid : mk(secForm) ∉ P` for the specific section form
on the cone quotient) do not follow from the step lemmas: the step `hsucc`
conclusion repackages the supplied `hreg` (for fixed `G`, `hreg` is the open
`hsucc`), and step avoidance (`¬ span G ≤ P` on step quotients `R ⧸ J`,
`k ≤ n`) is a different quotient/element than secForm avoidance on the cone
quotient `R ⧸ span G`. Closing fixed-`G` needs (i) rung induction
constructing `hreg` rung-by-rung for the fixed family (existence-form R2
above is the exact narrow: some recombined full-length family is regular,
not the fixed one), and (ii) specific-form prime avoidance for `secForm`
beyond `PrimeAvoidance` existence. Both are scoped remainder, left explicit.

Import swapped this lane (verified acyclic: `Regularity/GradeUnmixedBridge`
imports only `Regularity/*` + `Dimension/*` + Mathlib, never `Bridge`):
`Regularity.Grade.GradeUnmixedBridge` (for) replaces
`Regularity.Unmixed.BabyAuslanderBuchsbaum` — the BabyAuslanderBuchsbaum bridges are now
consumed only inside the
hbaby-closed corollaries. No other import edit.

Status: `heightDrop_general_of_depthEq` + `unmixed_general_of_depthEq`
conditional-exact on `[hdepth]`; `hsuccStep_mkSystem_of_depthEq` +
`avoid_general_of_depthEq` conditional-exact on `[hdepth-general-k-shape]` +
ctx `[hreg, hZd, hk]` (`hlow` closed); `exists_regular_quadrics_of_depthEq` +
`exists_regular_quadrics_mkSystem_of_depthEq` conditional-exact on
`[hdepth_all]` + ctx `[hG/hF, hZd]`. Overall lane: partial (fixed-`G`
`hsucc`/`havoid` at stay explicit).

## References

* `Regularity/Grade/GradeUnmixedBridge.lean` (`heightDrop_of_chain_depth`
  / `unmixed_of_chain_depth`, hbaby-closed one-liners cond `[hdepth]`);
  `Geometry/K2UnmixednessEndgame.lean` (`heightDrop_pair_of_depthEq` /
  `unmixed_pair_of_depthEq`, `k = 2` pattern, same one-liners at `k := 2`).
* `GradeDepthFragment.lean` (`DepthEqDimAt`)
  (`gradeDropChain_of_successive`, chain closed; is consumed
  inside the closed corollaries).
* `ResultantLemmas.lean` (`hsuccStep_mkSystem_of_hunmixed`, general-`k`
  T4-form) (`..._uncond_hlow`) (`hlow_general`)
  (`exists_regular_quadrics_of_unmixed`)
  (`exists_regular_quadrics_mkSystem_of_hunmixed_ge2`).
* `AvoidanceApply.lean` (`hsucc_of_step_outputs`)
  (`avoid_of_hunmixed_ge2`); `RegularityBridge.lean`
  (`SuccessiveSMulRegular`).
* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`) for the
  membership-to-instance adaptation (as at `ResultantLemmas.lean`).

Residual register (verbatim): closed this lane: [hunmixed general-`k`
conclusion (via hbaby-closed from chain, conditional on
`[hdepth-general-k-shape]`)]; [general-`k` hsuccStep pair conclusion (from `hdepth` + ctx, `hlow`
closed)]; [general-`k` step avoidance
(from `hdepth` + ctx, `hsucc`, `hlow` closed)]; [R2
narrowed full-family existence (general `G` + `mkSystem`, via
from `[hdepth_all]` + ctx)]. Open (priced remainder): [hsucc for fixed
`bridgeSystem`/`mkSystem` full family (
shapes; needs rung induction constructing `hreg` for the fixed family —
existence-form R2 above does not imply it)]; [havoid for specific `secForm`
on the cone quotient (shapes; needs
specific-form prime avoidance beyond existence)]; [hdepth (deep-core (iii),
now the sole conditional input, `hdepth-general-k-shape` per step /
`hdepth_all` ∀-form for R2)]. Context: [hreg (per-step `IsSMulRegular`
outputs)], [hZd (`IsZeroDimensional`)], [hk (`k ≤ n`)], [hF/hG
(homogeneity for R2)].
-/

/-- General-`k` height-drop from `DepthEqDimAt`: one-line application of
the hbaby-closed `GradeUnmixedBridge.heightDrop_of_chain_depth` ,
fed with the closed chain  and the explicit `hdepth` hypothesis.
Generalizes `BabyABPair.heightDrop_pair_of_depthEq`
(`Geometry/K2UnmixednessEndgame.lean`).

Conditional on exactly `[hdepth]`.

## References

* `GradeUnmixedBridge.heightDrop_of_chain_depth`
  (`Regularity/Grade/GradeUnmixedBridge.lean`).
* `GradeDepthFragment.gradeDropChain_of_successive` (`GradeDepthFragment.lean`). -/
theorem heightDrop_general_of_depthEq {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ :=
  GradeUnmixedBridge.heightDrop_of_chain_depth m K q hsucc J hJ
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc) hdepth

/-- General-`k` per-prime minimality over `J` from `DepthEqDimAt`:
one-line application of the hbaby-closed
`GradeUnmixedBridge.unmixed_of_chain_depth`. Generalizes
`BabyABPair.unmixed_pair_of_depthEq` (`Geometry/K2UnmixednessEndgame.lean`).

Conditional on exactly `[hdepth]`.

## References

* `GradeUnmixedBridge.unmixed_of_chain_depth`
  (`Regularity/Grade/GradeUnmixedBridge.lean`).
* `GradeDepthFragment.gradeDropChain_of_successive` (`GradeDepthFragment.lean`). -/
theorem unmixed_general_of_depthEq {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    P ∈ J.minimalPrimes :=
  GradeUnmixedBridge.unmixed_of_chain_depth m K q hsucc J hJ P hP
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc)
    hdepth

/-- General-`k` hsuccStep at `mkSystem` from `hdepth` (exact hdepth
shape with `J := Ideal.span (Set.range h)`): per-step `IsSMulRegular`
outputs repackage to `SuccessiveSMulRegular h` (via), `hunmixed` is
derived via `unmixed_general_of_depthEq` (hbaby-closed), and every
`Ass` prime of the step quotient has
proper `comboLin` pullback (via, `hlow` closed upstream). Follows
the pattern with `hunmixed` discharged.

Conditional on exactly `[hdepth-general-k-shape]` + ctx
`[hreg, hZd, hk]`.

## References

* `ResultantLemmas.hsuccStep_mkSystem_of_hunmixed_uncond_hlow`
  (`ResultantLemmas.lean`).
* `AvoidanceApply.hsucc_of_step_outputs` (`AvoidanceApply.lean`).
* `unmixed_general_of_depthEq` above (hbaby-closed). -/
theorem hsuccStep_mkSystem_of_depthEq (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (k : ℕ) (hk : k ≤ n)
    (h : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hreg : ∀ j : Fin k, IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn h)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))
      (h j))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin (n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range h)) →
      GradeDepthFragment.DepthEqDimAt (n + 2) K Q) :
    RegularityBridge.SuccessiveSMulRegular h ∧
      ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)),
        P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
            (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)))) →
        Submodule.comap (comboLin K (mkSystem n K F))
          (Submodule.restrictScalars K
            (P : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ := by
  have hsucc := AvoidanceApply.hsucc_of_step_outputs h hreg
  have hunmixed : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range h)) →
      P ∈ (Ideal.span (Set.range h)).minimalPrimes := by
    intro P hPI hP
    exact unmixed_general_of_depthEq (n + 2) K h hsucc _ rfl P hP hdepth
  exact hsuccStep_mkSystem_of_hunmixed_uncond_hlow n K F hZd k hk h hreg
    hunmixed

/-- General-`k` step avoidance from `hdepth` (exact hdepth shape with
`J` param + `hJ`, as): no `Ass` prime of the step quotient
contains `span G`. `hsucc` for `q` is derived from `hreg`;
`hunmixed` via `unmixed_general_of_depthEq`; `hlow`.

Conditional on exactly `[hdepth-general-k-shape]` + ctx
`[hreg, hZd, hk]`.

## References

* `AvoidanceApply.avoid_of_hunmixed_ge2` (`AvoidanceApply.lean`).
* `AvoidanceApply.hsucc_of_step_outputs` (`AvoidanceApply.lean`).
* `ResultantLemmas.hlow_general` (`ResultantLemmas.lean`).
* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`). -/
theorem avoid_general_of_depthEq (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (k : ℕ) (hk : k ≤ n)
    (q : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hreg : ∀ j : Fin k, IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn q)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))
      (q j))
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin (n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ J) →
      GradeDepthFragment.DepthEqDimAt (n + 2) K Q) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range G) ≤ P) := by
  have hsucc := AvoidanceApply.hsucc_of_step_outputs q hreg
  have hunmixed_mem : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes := by
    intro P hP
    have := (AssociatedPrimes.mem_iff.mp hP).isPrime
    exact unmixed_general_of_depthEq (n + 2) K q hsucc J hJ P hP hdepth
  exact AvoidanceApply.avoid_of_hunmixed_ge2 n K G hZd k hk q hsucc J hJ
    (hlow_general n K G) (fun _ => hunmixed_mem)

/-- R2 for general `G` from `hdepth_all` (narrowed full-family existence):
some recombined full-length family is regular and spans the same ideal.
Discharges the `hunmixed_ge2` binder via
`unmixed_general_of_depthEq` per `(k, q, J)`.

Conditional on exactly `[hdepth_all]` + ctx `[hG, hZd]`.

## References

* `exists_regular_quadrics_of_unmixed` (`ResultantLemmas.lean`).
* `unmixed_general_of_depthEq` above (hbaby-closed).
* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`). -/
theorem exists_regular_quadrics_of_depthEq (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hZd : IsZeroDimensional n K G)
    (hdepth_all : ∀ (k : ℕ), 2 ≤ k →
      ∀ (q : Fin k → MvPolynomial (Fin (n + 2)) K)
      (J : Ideal (MvPolynomial (Fin (n + 2)) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ (Q : Ideal (MvPolynomial (Fin (n + 2)) K)) [Q.IsPrime],
        Q ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K ⧸ J) →
        GradeDepthFragment.DepthEqDimAt (n + 2) K Q) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUnit M ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • G j) ∧
      Ideal.span (Set.range fun k => ∑ j, M k j • G j)
        = Ideal.span (Set.range G) := by
  apply exists_regular_quadrics_of_unmixed n K G hG hZd
  intro k hk2 q hsucc J hJ P hP
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact unmixed_general_of_depthEq (n + 2) K q hsucc J hJ P hP
    (hdepth_all k hk2 q J hJ)

/-- R2 at `mkSystem` from `hdepth_all` (narrowed full-family existence):
some recombined full-length family is regular and spans the same ideal as
`mkSystem`. Discharges the `hunmixed_ge2` binder via
`unmixed_general_of_depthEq` per `(k, q, J)`.

Conditional on exactly `[hdepth_all]` + ctx `[hF, hZd]`.

## References

* `exists_regular_quadrics_mkSystem_of_hunmixed_ge2`
  (`ResultantLemmas.lean`).
* `unmixed_general_of_depthEq` above (hbaby-closed).
* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`). -/
theorem exists_regular_quadrics_mkSystem_of_depthEq (n : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hdepth_all : ∀ (k : ℕ), 2 ≤ k →
      ∀ (q : Fin k → MvPolynomial (Fin (n + 2)) K)
      (J : Ideal (MvPolynomial (Fin (n + 2)) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ (Q : Ideal (MvPolynomial (Fin (n + 2)) K)) [Q.IsPrime],
        Q ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K ⧸ J) →
        GradeDepthFragment.DepthEqDimAt (n + 2) K Q) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUnit M ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • mkSystem n K F j) ∧
      Ideal.span (Set.range fun k => ∑ j, M k j • mkSystem n K F j)
        = Ideal.span (Set.range (mkSystem n K F)) := by
  apply exists_regular_quadrics_mkSystem_of_hunmixed_ge2 n K F hF hZd
  intro k hk2 q hsucc J hJ P hP
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact unmixed_general_of_depthEq (n + 2) K q hsucc J hJ P hP
    (hdepth_all k hk2 q J hJ)

#print axioms heightDrop_general_of_depthEq
#print axioms unmixed_general_of_depthEq
#print axioms hsuccStep_mkSystem_of_depthEq
#print axioms avoid_general_of_depthEq
#print axioms exists_regular_quadrics_of_depthEq
#print axioms exists_regular_quadrics_mkSystem_of_depthEq

end FinalDischargeHub
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FinalDischargeHub

open scoped BigOperators

/-! ## §9 fixed-family rung induction: skeleton + rung 0, remainder scoped (proof)

Goal: `SuccessiveSMulRegular (bridgeSystem n K c hn)`
(full shape) conditional-exact on
`[hdepth-general-k-shape]` + ctx, by rung induction using the §8 step lemmas.

Verdict: partial. Rung 0 closes unconditionally (proved below); the
rung-induction skeleton proves conditional-exact on `[rungAvoid at rungs ≥ 1]`
(per-rung fixed-element avoidance); rungs `≥ 1` do not follow from `hdepth`
(or from `∀J`-`HkerAtAss`), for two structural reasons (no spiral: both are
terminal for this route, scoped below).

Rung table (`R = MvPolynomial (Fin (statementIndex n + 2)) K`,
`q = bridgeSystem n K c hn`, `Jᵢ = span (image q {j | j.val < i.val})`):

* Rung 0 (`i.val = 0`): closed unconditional — `Jᵢ = ⊥`, domain-side t1
  (`Triangular.mkSystem_isSMulRegular`) lifted by
  `AvoidanceApply.isSMulRegular_quot_bot_of_regular`.
  Established: `mkSystem_rung_zero` (general `mkSystem`), `bridgeSystem_rung_zero`.
* Rung `i ≥ 1`: needs the fixed element `q i ∉ P` for every
  `P ∈ Ass(R ⧸ Jᵢ • ⊤)`, then `regular_of_avoid` closes the rung. The
  skeleton (`successive_of_rungAvoid`, general; the sharpened bridge master
  `bridgeSystem_successive_of_rungAvoid_pos` with rung 0 discharged in-file)
  proves this conditional-exact on `[rungAvoid at rungs ≥ 1]`.
* Why `hdepth` cannot supply `rungAvoid`: `hdepth` (via) yields
  unmixedness, hence only span-level avoidance `¬ span G ≤ P`
  (`avoid_general_of_depthEq`). For a fixed next element,
  `¬ span G ≤ P` does not imply `q i ∉ P` (some other combo may be the
  avoider). The R2 `key` induction bridges span-avoidance
  to regularity only by selecting a new element (`exists_avoiding_coeff` +
  `regular_of_avoid`); the fixed family has no selection step.
* Why the step lemma cannot supply the next rung: `hsuccStep_*`  concludes
  `SuccessiveSMulRegular h` by repackaging the
  input `hreg` about the same `h` (`hsucc_of_step_outputs`; the
  equation `ofList_take_eq_span_image`, makes `hreg ↔ hsucc` for one
  family). For the fixed family, `hreg` for prefix `k+1` already contains the
  open rung — "rung from step lemma + previous rungs" begs the question.
  Existence-form R2 produces some recombined family, not
  the fixed one.
* `HkerAtAss`-shape (`Geometry/K2UnmixednessEndgame.lean`, upstream of `hdepth`): considered by
  design; not
  threaded — the skeleton needs no
  unmixedness input at all (avoidance implies regularity directly), and
  `∀J`-`hker` would still terminate at span-avoidance (same gap). No `hker`
  hypothesis is introduced or closed here.
* Triangular scoped routes (not proved): rung 1 via t2a (cond `[x₀ ∤ F₀]`)
  / t2b (cond `[x₀ ∣ F₀ + minor ≠ 0]`) — `c`-specific hypotheses about
  `bridgeForms`; rungs `≥ 2` t3-obstructed (no division algorithm after the
  non-monic quotient; `TriangularRegularity.lean` (t3) verdict).

No import edit (all feeds — `TriangularRegularity`, `RegularSequenceDimDrop`,
`AvoidanceApply`, `ResultantLemmas` — already in the transitive closure via
the §1–§8 imports). No existing declaration modified.

Status: `mkSystem_rung_zero` + `bridgeSystem_rung_zero` unconditional;
`successive_of_rungAvoid` conditional-exact on `[rungAvoid]`;
`bridgeSystem_successive_of_rungAvoid_pos` conditional-exact on
`[rungAvoid at rungs ≥ 1]` (full shape). Overall lane: partial.

## References

* `RegularityBridge.SuccessiveSMulRegular` (`RegularityBridge.lean`).
* `regular_of_avoid` (`ResultantLemmas.lean`); `exists_avoiding_coeff`
 R2 `key` induction; `hsuccStep_*`; R2 existence; §8.
* `AvoidanceApply.hsucc_of_step_outputs` , `ofList_take_eq_span_image`
  , `isSMulRegular_quot_bot_of_regular` ,
  `hsucc_mkSystem_singleton` (rung-0 proof pattern mirrored).
* `Triangular.mkSystem_isSMulRegular` (t1, `TriangularRegularity.lean`); t2a/t2b
  dichotomy + (t3) verdict (`TriangularRegularity.lean`, header).
* `RegularSequenceDimDrop.span_smul_top` (`RegularSequenceDimDrop.lean`).
* `mkSystem` (`Statement/Definitions.lean`); `bridgeSystem`
  (`FixedPointFromBezout.lean`).
* `BabyABPair.HkerAtAss` (`Geometry/K2UnmixednessEndgame.lean`), `hdepth_of_hker`
   — cited, not imported.

Residual register (verbatim): closed this lane: [rung 0 of the fixed
`bridgeSystem`/`mkSystem` family (unconditional, domain-side t1 + quot-bot
lift)]; [rung-induction skeleton (general `successive_of_rungAvoid`,
conditional-exact on `[rungAvoid]`); sharpened bridge master (full
shape, conditional-exact on `[rungAvoid at rungs ≥ 1]`, rung 0 discharged
in-file)]. Open (priced remainder): [rungAvoid for fixed `bridgeSystem`
rungs `≥ 1` (`q i ∉ P` per `P ∈ Ass` of the rung quotient; strictly stronger
than span-avoidance — does not follow from `hdepth`/`∀J`-`hker`; rung 1
scoped via t2a/t2b on `c`-specific dvd/minor hyps, rungs `≥ 2`
t3-obstructed)]; [hsucc full shape stays conditional on the above (replaces
the bare `hsucc` residual with the strictly narrower `rungAvoid ≥ 1`)];
[havoid for specific `secForm` (unchanged)]. Not introduced: [`HkerAtAss`
(unneeded by the skeleton; insufficient for the gap — see above)].
-/

/-- Rung 0 of a fixed `mkSystem` family is regular, unconditional: the prior
span is empty (`⊥`), the generator is nonzero by the `-z·xᵢ` monomial (t1),
hence regular on the domain, lifted across `R ⧸ ⊥`. Mirrors the
`hsucc_mkSystem_singleton` proof (`AvoidanceApply.lean`).


## References

* `Triangular.mkSystem_isSMulRegular` (t1, `TriangularRegularity.lean`).
* `AvoidanceApply.isSMulRegular_quot_bot_of_regular`
  (`AvoidanceApply.lean`).
* `RegularSequenceDimDrop.span_smul_top` (`RegularSequenceDimDrop.lean`). -/
theorem mkSystem_rung_zero (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) :
    IsSMulRegular
      (MvPolynomial (Fin (m + 2)) K ⧸
        (Ideal.span (Set.image (mkSystem m K F)
          { j | j.val < (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).val }) •
          (⊤ : Submodule (MvPolynomial (Fin (m + 2)) K)
            (MvPolynomial (Fin (m + 2)) K))))
      (mkSystem m K F ⟨0, Nat.zero_lt_succ m⟩) := by
  have hset : Set.image (mkSystem m K F)
      { j : Fin (m + 1) | j.val < (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).val }
      = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨j, hj, rfl⟩
    simp only [Set.mem_ofPred_eq] at hj
    have _hv : ((⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).val) = 0 := rfl
    omega
  rw [hset, Ideal.span_empty]
  have e : ((⊥ : Ideal (MvPolynomial (Fin (m + 2)) K)) •
      (⊤ : Submodule (MvPolynomial (Fin (m + 2)) K)
        (MvPolynomial (Fin (m + 2)) K)) : Submodule _ _) =
      ((⊥ : Ideal _) : Submodule _ _) := by
    rw [← Ideal.span_empty]
    exact RegularSequenceDimDrop.span_smul_top _
  rw [e]
  exact AvoidanceApply.isSMulRegular_quot_bot_of_regular m K _
    (Triangular.mkSystem_isSMulRegular m K F ⟨0, Nat.zero_lt_succ m⟩)

/-- Rung 0 of the fixed bridge family is regular, unconditional: definitional
instance of `mkSystem_rung_zero` (`bridgeSystem` is `mkSystem` at
`bridgeForms`, `FixedPointFromBezout.lean`).
-/
theorem bridgeSystem_rung_zero (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          { j | j.val < (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
            Fin (statementIndex n + 1)).val }) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      (bridgeSystem n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩) :=
  mkSystem_rung_zero (statementIndex n) K (bridgeForms n K c hn)

/-- Rung-induction skeleton (general family): per-rung fixed-element avoidance
(`q i` outside every `Ass` prime of its rung quotient) yields
`SuccessiveSMulRegular`, rung by rung via `regular_of_avoid`. No unmixedness,
no selection, no `IsAlgClosed`.

Conditional on exactly `[rungAvoid]`.

## References

* `regular_of_avoid` (`ResultantLemmas.lean`).
* `RegularityBridge.SuccessiveSMulRegular` (`RegularityBridge.lean`). -/
theorem successive_of_rungAvoid (m : ℕ) (K : Type*) [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (havoid : ∀ (i : Fin k) (P : Ideal (MvPolynomial (Fin m) K)),
      P ∈ associatedPrimes (MvPolynomial (Fin m) K)
        (MvPolynomial (Fin m) K ⧸
          (Ideal.span (Set.image q { j | j.val < i.val }) •
            (⊤ : Submodule (MvPolynomial (Fin m) K)
              (MvPolynomial (Fin m) K)))) →
      q i ∉ P) :
    RegularityBridge.SuccessiveSMulRegular q := by
  intro i
  exact regular_of_avoid _ _ (q i) (fun P hP => havoid i P hP)

/-- Full `hsucc` at bridge data (shape) with rung 0 discharged in-file:
successive regularity of the fixed `bridgeSystem` family from per-rung
avoidance at rungs `≥ 1` only (`0 < i.val`; rung 0 closes by
`bridgeSystem_rung_zero`).

Conditional on exactly `[rungAvoid at rungs ≥ 1]`.

## References

* `successive_of_rungAvoid` above (skeleton); `bridgeSystem_rung_zero` above.
* `regular_of_avoid` (`ResultantLemmas.lean`). -/
theorem bridgeSystem_successive_of_rungAvoid_pos (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (havoid : ∀ (i : Fin (statementIndex n + 1)), 0 < i.val →
      ∀ (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)),
        P ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            (Ideal.span (Set.image (bridgeSystem n K c hn)
              { j | j.val < i.val }) •
              (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
                (MvPolynomial (Fin (statementIndex n + 2)) K)))) →
        (bridgeSystem n K c hn) i ∉ P) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) := by
  intro i
  by_cases hi : i.val = 0
  · have hi0 : i = ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ := Fin.ext hi
    rw [hi0]
    exact bridgeSystem_rung_zero n K c hn
  · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
    exact regular_of_avoid _ _ _ (fun P hP => havoid i hpos P hP)

#print axioms mkSystem_rung_zero
#print axioms bridgeSystem_rung_zero
#print axioms successive_of_rungAvoid
#print axioms bridgeSystem_successive_of_rungAvoid_pos

end FinalDischargeHub
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
