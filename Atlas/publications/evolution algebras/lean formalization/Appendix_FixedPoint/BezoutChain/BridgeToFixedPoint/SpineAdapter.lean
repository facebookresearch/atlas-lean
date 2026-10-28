/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Section_2_Preliminaries.A_Preliminaries
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CountAssembly
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CoordinatizationSemiring
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ProjectiveFiniteness
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Appendix_FixedPoint.BezoutChain.Geometry.AffineFinite
import Appendix_FixedPoint.BezoutChain.Geometry.MkSystemChart
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.EliminationFilter
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Spine adapter: Semiring-spine fixed point from the Bezout master

The Bézout formalization proves the projective fixed-point conclusion on the Ring
spine (`FinalDischargeHub.fixedPoint_of_idempotent_hfilter_closed`,
`FinalDischargeHub.lean`: `[NonUnitalNonAssocRing E]` + tower/comm +
2-residual `∀`-form). The library principle
(`EvolutionAlgebras.fixedPoint_of_idempotent`, `A_FixedPoint.lean`) is stated
on the minimal Semiring spine (`[NonUnitalNonAssocSemiring E]`, inputs `hfin
hV hN hneV`, conclusion `∃ x: E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam: K,...`).
This file adapts the former to the latter: it replays the §3/§6/§7 chain on
the Semiring spine the adapter master
(`SpineAdapter.fixedPoint_of_idempotent_of_bezout`, §10) with the principle's exact
spine, inputs (plus documented tower/comm context), and conclusion shape.

Why the replay works. The only `E`-touching feeds of the Bezout chain are
`hcut`/`hfin` from algebra data; every other input is `E`-free by signature
(`bezout_quadrics` takes only `(K) [Field K] {n} [IsAlgClosed K] (hn) (c)`
plus polynomial data — `#check`-verified, no `E`; `FinalResiduals`
(`FinalDischargeHub.lean`) is `E`-free). The `hcut`/`hfin` feeds go through
spine-generic machines taking only `[AddCommMonoid E] [Mul E] [SMul K E]`
(`bpf_of_hN_affine`, `AffineFinite.lean`; `h_expand_shift_affine`;
`h_inj_shift_affine`; `basePointFree_familyForms_affine`),
instantiated here with the `CoordinatizationSemiring` mirrors (Semiring spine,
`CoordinatizationSemiring.lean`) instead of the Ring mirrors. `sqCoords` converts
across mirrors by `rfl`-defeq; tower/comm ride as explicit `Prop` hypotheses
(the documented integration-time shape, `FixedPointFromBezout.lean`).

Sections: §1 Semiring `BasePointFree` at the shifted family (replay of
`ProjectiveFiniteness.lean`); §2 Semiring `hcut` (replay of
`FinalDischargeHub.lean`); §3 Semiring affine finiteness (replay of
`AffineFinite.lean`); §4 Semiring Shape-1 `hfin` (replay of
`ProjectiveFiniteness.lean`); §5 Semiring bridge `hfin` (replay of
`ProjectiveFiniteness.lean`); §6 Semiring discharged cone point (replay of
`FinalDischargeHub.lean`); §7 Semiring hinj/hsurj-closed cone point (replay
of `FinalDischargeHub.lean`); §8 Semiring `hfilter` closure (replay of
`FinalDischargeHub.lean`); §9 Semiring hfilter-closed cone point (replay of
`FinalDischargeHub.lean`); §10 adapter master (replay of
`FinalDischargeHub.lean` on the `CoordinatizationSemiring` spine, with the
target conclusion shape).

Where the hker-chain enters. `hsucc-full-G` stays an explicit residual: its
attack route runs `HkerAtAss` (`Geometry/K2UnmixednessEndgame.lean`) → `hdepth_of_hker`
(`:248-258`) → unmixedness → per-step outputs (`FinalDischargeHub`
§8, `:1645+`), but fixed-`G` `hsucc` does not follow from the step lemmas
(`FinalDischargeHub.lean`: needs rung induction constructing `hreg`
for the fixed family, plus specific-form prime avoidance for `secForm`
beyond `PrimeAvoidance` existence). `havoid-secForm` likewise stays explicit
(specific-form Ass-avoidance). Both are priced remainder, kept verbatim.

Integration note: (i) the principle statement
grew `[htower hcomm hres2]` (both consumers provide tower/comm: the bundle
spine via `NonUnitalNonAssocAlgebra` instance projections (`inferInstance`);
the Ring spine holds them as instances); (ii) the principle body
became the §10 master application; (iii) this file's `A_FixedPoint` import edge
is dropped (else an import cycle: `A_FixedPoint` imports the adapter). The edge
was used only for the statement-shape witness, so the drop was mechanical.

Acyclicity (post-integration): `A_FixedPoint` imports the adapter + `A_Preliminaries` +
Mathlib; no Bézout module imports `A_FixedPoint` (the adapter's edge was the
only one); nothing imports the two consumers (`IdempotentIff`,
`SolvableCorollary`), so the `A_FixedPoint` → adapter edge cannot cycle.

Status: `fixedPoint_of_idempotent_of_bezout` conditional-exact on
`[hsucc-full-G, havoid-secForm]` (instance-data `hres2`: per `(n, c)`
realized by `(b, hexp)` on `V`, U5 narrowing) + fixed-point inputs
`[hfin hV hN hneV]` + tower/comm context `[htower hcomm]`.

Residual register (verbatim): closed this lane: [Ring-vs-Semiring spine
mismatch (full §3/§6/§7 replay on the Semiring spine via spine-generic
machines + `CoordinatizationSemiring` mirrors)]; [∃-mem sugar (master conclusion
is the principle's exact `∃ x : E, x ∈ V ∧...` shape)]; [tower/comm packaging
(explicit `Prop` hypotheses, the documented integration-time shape)]. Open
(priced remainder): [hsucc for fixed `bridgeSystem` full family
(quotient-side rungs `≥ 1`; hker-chain position: `HkerAtAss` →
`hdepth_of_hker` → step outputs does not imply fixed-`G`, needs rung
induction)]; [havoid for specific `secForm` on the cone quotient (needs
specific-form prime avoidance beyond existence)]. Closed at integration:
[`A_FixedPoint.lean` wiring (statement-grower +
import-edge drop)]. Context: [fixed-point inputs (`hfin hV hN
hneV`)]; [htower (`IsScalarTower K E E`)]; [hcomm (`SMulCommClass K E E`)].
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SpineAdapter

open scoped BigOperators

/-! ## §1 `BasePointFree` at the shifted family from Semiring algebra data -/

/-- `BasePointFree` at the shifted `mkSystem` family from Semiring-spine
fixed-point algebra data: replay of
`ProjectiveFiniteness.basePointFree_shiftedFamily_of_algebraData`
(`ProjectiveFiniteness.lean`) with the `CoordinatizationSemiring` mirrors. The
`sqCoords` binder converts by `rfl`-defeq
(`CoordinatizationSemiring.sqCoords` = `sqCoords_affine`, same body
`∑ i, ∑ j, c i j k * X i * X j`); `hN` feeds `h_nil` directly (no
`absNilpotent_affine` mirror, which is Ring-spined:
`ProjectiveFiniteness.lean`); `(0 : K) • e = 0` is `zero_smul`.

`(V, b, hexp, hN, htower, hcomm)`.

## References

* `BridgeToFixedPoint.ProjectiveFiniteness`,
  `Appendix_FixedPoint.BezoutChain.basePointFree_shiftedFamily_of_algebraData`
  (`ProjectiveFiniteness.lean`) (replayed proof).
* `BridgeToFixedPoint.CoordinatizationSemiring`,
  `Appendix_FixedPoint.BezoutChain.CoordinatizationSemiring.sq_expand`
  (`CoordinatizationSemiring.lean`), `coordVec_eq_zero` ,
  `coordVec_mem` , `eq_zero_of_mem_sq_eq_zero`.
* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.bpf_of_hN_affine` ,
  `Appendix_FixedPoint.BezoutChain.h_expand_shift_affine` ,
  `Appendix_FixedPoint.BezoutChain.h_inj_shift_affine` ,
  `Appendix_FixedPoint.BezoutChain.basePointFree_of_coordBPF_of_evalBridge` ,
  `Appendix_FixedPoint.BezoutChain.eval_mkQuadForm_affine`.
* `Mathlib/Algebra/GroupWithZero/Action/Defs.lean`, `zero_smul`. -/
theorem basePointFree_shiftedFamily_of_algebraData_semiring
    (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    BasePointFree (statementIndex_affine n) K
      (familyForms_affine (statementIndex_affine n) K
        (shiftConsts_affine n K c0 hn)) := by
  have := htower
  have := hcomm
  have h_expand : ∀ X : Fin n → K,
      CoordinatizationSemiring.coordVec K E b X * CoordinatizationSemiring.coordVec K E b X
        = ∑ k, (sqCoords_affine K c0 k X) • (b k : E) :=
    fun X => CoordinatizationSemiring.sq_expand K E b c0 hexp X
  have h_inj : ∀ X : Fin n → K,
      CoordinatizationSemiring.coordVec K E b X = 0 → X = 0 :=
    fun X h => CoordinatizationSemiring.coordVec_eq_zero K E b X h
  have hcoord : ∀ X' : Fin (statementIndex_affine n + 1) → K,
      (∀ k, sqCoords_affine K (shiftConsts_affine n K c0 hn) k X' = 0)
        → X' = 0 :=
    bpf_of_hN_affine (shiftConsts_affine n K c0 hn)
      (fun X' => CoordinatizationSemiring.coordVec K E b
        (reindexVec_affine K (shiftEquiv_affine n hn) X'))
      (fun k => ((b (shiftEquiv_affine n hn k)) : E)) (fun x => x ∈ V)
      (fun X' => CoordinatizationSemiring.coordVec_mem K E b _)
      (fun X' => h_expand_shift_affine (shiftEquiv_affine n hn) c0
        (CoordinatizationSemiring.coordVec K E b) (fun k => (b k : E)) h_expand X')
      (fun e => zero_smul K e)
      (fun hx hxx => CoordinatizationSemiring.eq_zero_of_mem_sq_eq_zero K E V hN hx hxx)
      (fun X' h0 => h_inj_shift_affine (shiftEquiv_affine n hn)
        (CoordinatizationSemiring.coordVec K E b) h_inj X' h0)
  exact basePointFree_of_coordBPF_of_evalBridge _ K _
    (fun k X' => sqCoords_affine K (shiftConsts_affine n K c0 hn) k X')
    hcoord (fun k X' => eval_mkQuadForm_affine _ K _ k X')

/-! ## §2 `hcut` at bridge data from Semiring algebra data -/

/-- `hcut` at bridge data from Semiring-spine algebra data: replay of
`FinalDischargeHub.hcut_of_algebraData` (`FinalDischargeHub.lean`) — the
Semiring §1 BPF moved across the `rfl` mirror links. The defeq is
`E`-independent.
-/
theorem hcut_of_algebraData_semiring (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    R1RegularSection.cutsOutOrigin (statementIndex n) K
      (bridgeForms n K c0 hn) := by
  have hB := basePointFree_shiftedFamily_of_algebraData_semiring n K c0 hn E V b
    hexp hN htower hcomm
  exact hB

/-! ## §3 Affine finiteness at the shifted family from Semiring data -/

/-- Affine finiteness at the shifted `mkSystem` family from Semiring-spine
algebra data: replay of
`AffineFinite.affineZero_finite_shiftedFamily_of_algebraData`
(`AffineFinite.lean`) with the `CoordinatizationSemiring` mirrors and the real
`hN` (no `absNilpotent_affine` transfer needed).

Conditional on exactly `[hCurveMeet]` given consumer algebra data
`(V, b, hexp, hN, htower, hcomm)` + `[IsAlgClosed K]`.

## References

* `Geometry.AffineFinite`,
  `Appendix_FixedPoint.BezoutChain.affineZero_finite_shiftedFamily_of_algebraData`
  (replayed proof), `Appendix_FixedPoint.BezoutChain.meetsInfinity_familyForms_affine_of_curveMeet`
  , `Appendix_FixedPoint.BezoutChain.affineZero_finite_of_meetsInfinity_of_coordBPF`
  , `Appendix_FixedPoint.BezoutChain.eval_mkQuadForm_affine`.
* This file, §1 (binder pattern). -/
theorem affineZero_finite_shiftedFamily_of_algebraData_semiring
    (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hCurveMeet : ∀ (F : Fin (statementIndex_affine n + 1) →
        MvPolynomial (Fin (statementIndex_affine n + 1)) K),
      (∀ i, (F i).IsHomogeneous 2)
        → MeetsInfinity_curve_affine (statementIndex_affine n) K F) :
    (affineZero (statementIndex_affine n) K
      (familyForms_affine (statementIndex_affine n) K
        (shiftConsts_affine n K c0 hn))).Finite := by
  have hPDT : MeetsInfinity (statementIndex_affine n) K
      (familyForms_affine (statementIndex_affine n) K
        (shiftConsts_affine n K c0 hn)) :=
    meetsInfinity_familyForms_affine_of_curveMeet _ K _ hCurveMeet
  have := htower
  have := hcomm
  have h_expand : ∀ X : Fin n → K,
      CoordinatizationSemiring.coordVec K E b X * CoordinatizationSemiring.coordVec K E b X
        = ∑ k, (sqCoords_affine K c0 k X) • (b k : E) :=
    fun X => CoordinatizationSemiring.sq_expand K E b c0 hexp X
  have h_inj : ∀ X : Fin n → K,
      CoordinatizationSemiring.coordVec K E b X = 0 → X = 0 :=
    fun X h => CoordinatizationSemiring.coordVec_eq_zero K E b X h
  have hcoord : ∀ X' : Fin (statementIndex_affine n + 1) → K,
      (∀ k, sqCoords_affine K (shiftConsts_affine n K c0 hn) k X' = 0)
        → X' = 0 := by
    have hcore := bpf_of_hN_affine (shiftConsts_affine n K c0 hn)
      (fun X' => CoordinatizationSemiring.coordVec K E b
        (reindexVec_affine K (shiftEquiv_affine n hn) X'))
      (fun k => ((b (shiftEquiv_affine n hn k)) : E)) (fun x => x ∈ V)
      (fun X' => CoordinatizationSemiring.coordVec_mem K E b _)
      (fun X' => h_expand_shift_affine (shiftEquiv_affine n hn) c0
        (CoordinatizationSemiring.coordVec K E b) (fun k => (b k : E)) h_expand X')
      (fun e => zero_smul K e)
      (fun hx hxx => CoordinatizationSemiring.eq_zero_of_mem_sq_eq_zero K E V hN hx hxx)
      (fun X' h0 => h_inj_shift_affine (shiftEquiv_affine n hn)
        (CoordinatizationSemiring.coordVec K E b) h_inj X' h0)
    exact hcore
  have hbridge : ∀ (k : Fin (statementIndex_affine n + 1))
      (X' : Fin (statementIndex_affine n + 1) → K),
      MvPolynomial.eval X'
          ((familyForms_affine (statementIndex_affine n) K
            (shiftConsts_affine n K c0 hn)) k)
        = sqCoords_affine K (shiftConsts_affine n K c0 hn) k X' :=
    fun k X' => eval_mkQuadForm_affine _ K _ k X'
  exact affineZero_finite_of_meetsInfinity_of_coordBPF (statementIndex_affine n) K
    (familyForms_affine (statementIndex_affine n) K
      (shiftConsts_affine n K c0 hn)) hPDT
    (fun k X' => sqCoords_affine K (shiftConsts_affine n K c0 hn) k X')
    hcoord hbridge

/-! ## §4 Shape-1 `hfin` at the shifted family from Semiring data -/

/-- Shape 1 — projective finiteness at the shifted `mkSystem` family from
Semiring-spine algebra data: replay of
`ProjectiveFiniteness.vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData`
(`ProjectiveFiniteness.lean`) via the Semiring §1/§3 feeds. The projective
step and `hCurveMeet` discharge are `E`-free, reused by name.

Conditional on exactly `[V b hexp hN htower hcomm]` plus the
`[IsAlgClosed K]` instance.

## References

* `BridgeToFixedPoint.ProjectiveFiniteness`, the Ring-spine Shape 1 (`ProjectiveFiniteness.lean`)
  (replayed proof), `Appendix_FixedPoint.BezoutChain.meetsInfinity_curve_affine_of_isHomogeneous`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.locus_finite_of_bpf_affine`
  (`MkSystemChart.lean`).
* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.shiftedFamily_homogeneous`.
* This file, §1 (`basePointFree_shiftedFamily_of_algebraData_semiring`) and
  §3 (`affineZero_finite_shiftedFamily_of_algebraData_semiring`). -/
theorem vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData_semiring
    (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    (vanishingLocus (statementIndex_affine n) K
      (mkSystem (statementIndex_affine n) K
        (familyForms_affine (statementIndex_affine n) K
          (shiftConsts_affine n K c0 hn)))).Finite := by
  have hCurveMeet : ∀ (F : Fin (statementIndex_affine n + 1) →
        MvPolynomial (Fin (statementIndex_affine n + 1)) K),
      (∀ i, (F i).IsHomogeneous 2)
        → MeetsInfinity_curve_affine (statementIndex_affine n) K F :=
    fun F hF => meetsInfinity_curve_affine_of_isHomogeneous _ K F hF
  have hAff := affineZero_finite_shiftedFamily_of_algebraData_semiring
    n K c0 hn E V b hexp hN htower hcomm hCurveMeet
  exact locus_finite_of_bpf_affine _ K _
    (shiftedFamily_homogeneous n K c0 hn)
    (basePointFree_shiftedFamily_of_algebraData_semiring n K c0 hn E V b hexp hN
      htower hcomm)
    hAff

/-! ## §5 Bridge `hfin` from Semiring algebra data -/

/-- Bridge `hfin` (exact consumer shape) from Semiring-spine algebra data:
replay of `ProjectiveFiniteness.hfin_bridgeSystem_of_algebraData`
(`ProjectiveFiniteness.lean`) — the Semiring §4 feed moved across the `rfl`
`bridgeSystem` identification (E-independent).

Conditional on exactly `[V b hexp hN htower hcomm]` plus the
`[IsAlgClosed K]` instance. -/
theorem hfin_bridgeSystem_of_algebraData_semiring
    (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    (vanishingLocus (statementIndex n) K
      (bridgeSystem n K c0 hn)).Finite := by
  have h := vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData_semiring
    n K c0 hn E V b hexp hN htower hcomm
  exact h

/-! ## §6 Discharged cone point at bridge data on the Semiring spine -/

/-- Bezout cone point at bridge data with everything but `FinalResiduals`
discharged, on the Semiring spine: replay of
`FinalDischargeHub.bezout_at_bridge_discharged` (`FinalDischargeHub.lean`)
with the Semiring §2 `hcut` / §5 `hfin` feeds. All other inputs
(`hG`/`hreg`/`hc`/`hZd`/`hsum`/`hbridge`/`hpos`/`hloc`/SES data/Statement
instantiation/`hSecondOfNotZd`) are `E`-free, reused by name.

Exact residual list: `[hsucc, havoid, hfilter, hinj, hsurj]` (bundled as
`FinalDischargeHub.FinalResiduals`) + algebra data.

Conditional on exactly
`[hsucc, havoid, hfilter, hinj, hsurj]` (+ algebra data). -/
theorem bezout_at_bridge_discharged_semiring (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hres : FinalDischargeHub.FinalResiduals n K c hn) :
    ∃ (X : Fin n → K) (z : K),
      (∀ k, homogQuadric K c k X z = 0) ∧ X ≠ 0 := by
  obtain ⟨hsucc, havoid, hfilter, hinj, hsurj⟩ := hres
  have hF : ∀ i, ((bridgeForms n K c hn) i).IsHomogeneous 2 :=
    bridgeForms_homogeneous n K c hn
  have hG : ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2 :=
    bridgeSystem_homogeneous n K c hn
  have hreg := R1RegularSection.secForm_isSMulRegular_of_avoid (statementIndex n) K
    (bridgeForms n K c hn) havoid
  have hcut := hcut_of_algebraData_semiring n K c hn E V b hexp hN htower hcomm
  have hc := CountAssembly.hc_secForm_of (statementIndex n) K
    (bridgeForms n K c hn) hF havoid hcut
  have hfin := hfin_bridgeSystem_of_algebraData_semiring n K c hn E V b hexp hN
    htower hcomm
  have hZd := FinalDischargeHub.hZd_of_hfin_hsucc (statementIndex n) K
    (bridgeSystem n K c hn) hG hsucc hfin
  have hsum := FinalDischargeHub.hsum_closed (statementIndex n) K
    (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hfin hc (hinj hfin hc)
    (hsurj hfin hc) hG hreg hZd
  have hbridge := hbridge_of_final (statementIndex n) K
    (bridgeSystem n K c hn) (R1RegularSection.secForm (statementIndex n) K)
    hG hreg hZd
  have hpos := FinalDischargeHub.hpos_closed (statementIndex n) K
    (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hfin hc hG hreg hZd
  have hloc := FinalDischargeHub.hloc_closed (statementIndex n) K
    (bridgeForms n K c hn) hF
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
  · exact FinalDischargeHub.hSecondOfNotZd_closed (statementIndex n) K
      (bridgeSystem n K c hn) hG hsucc

/-! ## §7 Cone point with hinj/hsurj closed, on the Semiring spine -/

/-- Bezout cone point at bridge data with hinj/hsurj closed, on the Semiring
spine: replay of `FinalDischargeHub.bezout_at_bridge_hinj_hsurj_closed`
(`FinalDischargeHub.lean`) with the Semiring §5 `hfin` / §6 master feeds.
`hinj`/`hsurj` closures are `E`-free, reused by name.

Exact residual list: `[hsucc, havoid, hfilter]` (+ algebra data).

Conditional on exactly `[hsucc, havoid, hfilter]`. -/
theorem bezout_at_bridge_hinj_hsurj_closed_semiring (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
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
  have hfin := hfin_bridgeSystem_of_algebraData_semiring n K c hn E V b hexp hN
    htower hcomm
  have hZd := FinalDischargeHub.hZd_of_hfin_hsucc (statementIndex n) K
    (bridgeSystem n K c hn) hG hsucc hfin
  have hinj := FinalDischargeHub.hinj_bridge_closed n K c hn
  have hsurj := FinalDischargeHub.hsurj_bridge_of_regCtx n K c hn hreg hZd
  exact bezout_at_bridge_discharged_semiring n K c hn E V b hexp hN htower hcomm
    ⟨hsucc, havoid, hfilter, hinj, hsurj⟩

/-! ## §8 `hfilter` closure at bridge data on the Semiring spine -/

/-- `hfilter` (`Ffun`-form) at bridge data from `[hsucc-full, havoid-secForm]`
on the Semiring spine: replay of `FinalDischargeHub.hfilter_bridge_closed`
(`FinalDischargeHub.lean`) with the Semiring §5 `hfin` feed. The
Koszul-`hfilter` landing and the `Ffun`/`Fsec` bridge are `E`-free, reused
by name.

Conditional on exactly `[hsucc-full, havoid-secForm]` (+ algebra data). -/
theorem hfilter_bridge_closed_semiring (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
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
  have hfin := hfin_bridgeSystem_of_algebraData_semiring n K c hn E V b hexp hN
    htower hcomm
  have hZd := FinalDischargeHub.hZd_of_hfin_hsucc (statementIndex n) K
    (bridgeSystem n K c hn) hG hsucc hfin
  exact hfilter_ffun_of_final (statementIndex n) K (bridgeSystem n K c hn)
    (R1RegularSection.secForm (statementIndex n) K) hreg hZd hG
    (FinalDischargeHub.hF_ffun_eq_fsec (statementIndex n) K
      (bridgeSystem n K c hn)
      (R1RegularSection.secForm (statementIndex n) K))

/-! ## §9 Cone point with `hfilter` closed, on the Semiring spine -/

/-- Bezout cone point at bridge data with `hfilter` closed, on the Semiring
spine: replay of `FinalDischargeHub.bezout_at_bridge_hfilter_closed`
(`FinalDischargeHub.lean`) — the Semiring §8 `hfilter` feed plus the
Semiring §7 master.

Exact residual list: `[hsucc-full, havoid-secForm]` (+ algebra data).

Conditional on exactly `[hsucc-full, havoid-secForm]`. -/
theorem bezout_at_bridge_hfilter_closed_semiring (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
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
  have hfilter := hfilter_bridge_closed_semiring n K c hn E V b hexp hN htower
    hcomm hsucc havoid
  exact bezout_at_bridge_hinj_hsurj_closed_semiring n K c hn E V b hexp hN
    htower hcomm hsucc havoid hfilter

/-! ## §10 Adapter master: target-shape fixed point from Bezout -/

/-- Projective fixed point from idempotence on the principle's exact spine:
replay of `FinalDischargeHub.fixedPoint_of_idempotent_hfilter_closed`
(`FinalDischargeHub.lean`) with the `CoordinatizationSemiring` coordinatization
spine and the Semiring §9 cone point. Spine, fixed-point inputs, and
conclusion match `EvolutionAlgebras.fixedPoint_of_idempotent`
(`A_FixedPoint.lean`) exactly; the extras are the tower/comm context
(the documented integration-time shape) and the 2-residual
instance-data `hres2`.

conditional on the 2-residual instance-data form (one
`(hsucc, havoid)` per `(n, c)` realized by `(b, hexp)` on `V`;
the U5 shape, ungated)
plus the fixed-point inputs `hfin hV hN hneV` and tower/comm context.

note: `hfin`/`hneV` are load-bearing (basis via
`exists_pos_fin_basis`).

Conditional on exactly `[hsucc-full, havoid-secForm]` (instance-data).

## References

* `BridgeToFixedPoint.FinalDischargeHub`,
  `Appendix_FixedPoint.BezoutChain.FinalDischargeHub.fixedPoint_of_idempotent_hfilter_closed`
  (`FinalDischargeHub.lean`) (replayed dehomogenization).
* `EvolutionAlgebras.fixedPoint_of_idempotent` (`A_FixedPoint.lean`)
  (target statement matched).
* This file, §9 (`bezout_at_bridge_hfilter_closed_semiring`). -/
theorem fixedPoint_of_idempotent_of_bezout (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E] [IsAlgClosed K]
    (V : Submodule K E)
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hres2 : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (b : Module.Basis (Fin n) K V)
      (_hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E)),
      RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
      (∀ P ∈ associatedPrimes
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
            (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
          Ideal.Quotient.mk (Ideal.span (Set.range (bridgeSystem n K c hn)))
            (mkLin (statementIndex n) K
              (R1RegularSection.secForm (statementIndex n) K)) ∉ P)) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  have := htower
  have := hcomm
  -- (i) basis from hfin/hneV (P5); hfin/hneV now load-bearing.
  obtain ⟨n, hn, ⟨b⟩⟩ :=
    CoordinatizationSemiring.exists_pos_fin_basis K E V hfin hneV
  obtain ⟨c, hexp⟩ := CoordinatizationSemiring.exists_structure_constants K E b hV
  -- (ii) ungated hres2 application — no horth argument exists (§8 pattern,
  -- Hres2InstN3.lean: `obtain ⟨hsucc, havoid⟩ := hres2n3 c b hexp …`).
  obtain ⟨hsucc, havoid⟩ := hres2 n hn c b hexp
  obtain ⟨X, z, hsol, hXne⟩ := bezout_at_bridge_hfilter_closed_semiring n K c hn
    E V b hexp hN htower hcomm hsucc havoid
  have hF : ∀ k, CoordinatizationSemiring.sqCoords K c k X = z * X k := by
    intro k
    have h := hsol k
    have h' : CoordinatizationSemiring.sqCoords K c k X - z * X k = 0 := h
    exact sub_eq_zero.mp h'
  have hz : z ≠ 0 := by
    intro hz0
    have hF0 : ∀ k, CoordinatizationSemiring.sqCoords K c k X = 0 := by
      intro k
      have h := hsol k
      have h' : CoordinatizationSemiring.sqCoords K c k X - z * X k = 0 := h
      rw [hz0, zero_mul, sub_zero] at h'
      exact h'
    have hsq0 : CoordinatizationSemiring.coordVec K E b X *
        CoordinatizationSemiring.coordVec K E b X = 0 := by
      rw [CoordinatizationSemiring.sq_expand K E b c hexp X]
      simp [hF0]
    have hzero : CoordinatizationSemiring.coordVec K E b X = 0 :=
      CoordinatizationSemiring.eq_zero_of_mem_sq_eq_zero K E V hN
        (CoordinatizationSemiring.coordVec_mem K E b X) hsq0
    exact hXne (CoordinatizationSemiring.coordVec_eq_zero K E b X hzero)
  refine ⟨CoordinatizationSemiring.coordVec K E b X,
    CoordinatizationSemiring.coordVec_mem K E b X, ?_, z, hz, ?_⟩
  · intro hzero
    exact hXne (CoordinatizationSemiring.coordVec_eq_zero K E b X hzero)
  · rw [CoordinatizationSemiring.sq_expand K E b c hexp X]
    unfold CoordinatizationSemiring.coordVec
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

/-! ## Integration record

`EvolutionAlgebras.fixedPoint_of_idempotent` (`A_FixedPoint.lean`) applies
the §10 master directly, so the shape match is machine-checked at the use
site; the `A_FixedPoint` import edge is dropped (this module is imported
*by* `A_FixedPoint`, so the edge would cycle). -/

#print axioms hfilter_bridge_closed_semiring
#print axioms bezout_at_bridge_hfilter_closed_semiring
#print axioms fixedPoint_of_idempotent_of_bezout

end SpineAdapter
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
