/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SesClosure
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster

/-!
# Colon-from-superficial transfer + exact-dimension master rework
Target: close the two G2 residuals from `TowerClosure.lean` §5
(the colon-from-superficial transfer, ~100 lines; the master exact-dim rework,
~100–150 lines), modulo explicit hypotheses for the sibling T1 lane
(superficial/order-one existence — output unavailable, taken as an explicit
hypothesis, never as a dependency).

## What this file proves

* (§1) Colon-from-superficial transfer: `SupT1Data` (the T1 conclusion shape:
  regularity in the exact `SupStepData` form + the Valabrega–Valla order-one
  trace equation) implies the true gate `SupColonStabFor`
  (`supColon_of_t1Data`, via the ideal-form regularity bridge
  `supT1_reg_mem_of_mul_mem`). The `DVR π²` witness of SupSesClose §1 is
  regular but violates the order-one equation at every rank, so the trace
  input is load-bearing, not a restatement of the conclusion.
* (§2) Exact-dimension rework: `SupTowerExact` (the reshaped tower — at each
  exact pin `d ≥ 1` provides `y` with selection + T1 data + the exact-dim
  drop to `d - 1`) fires the restated growth master
  (`sup_chi_exactDim_growth`: dim-zero case via the proved
  `supDimZeroBase_unconditional`, dim `≥ 1` via tower + §1 transfer + SES
  assembly + shift + lift) and the restated nonvanishing master
  (`sup_tower_nonvanishing_exact`: dim-zero case via the proved seed
  `sup_dimZero_seed`, dim `≥ 1` via tower + transfer + SES + shift + lift),
  hence the verbatim `HchiReduceAtAss` conclusion
  (`hChiReduceAtAss_of_exactTowers`).
* (§3) Depth-gated reshape: `SupTowerExactGated` (canonical address,
  unified up from QuotTowerFire §3 — one definition, not a dup) +
  the two §3 bridges (`supTowerExactGated_of_tower`,
  `supSelectColon_of_towerExactGated`) + tower reachability
  (`SupTowerStep`, `SupTowerReach`) + path-scoped
  depth (`SupPathDepth`, the carefully-scoped replacement for the
  false ∀`J'` depth hypothesis) + the three gated masters
  (`sup_chi_exactDim_growth_gated`,
  `sup_tower_nonvanishing_exact_gated`,
  `hChiReduceAtAss_of_gatedTowers`) firing on the gated tower.
* (C0) Statement repair: unselected path depth is false in `dim ≥ 2`
  (cmap design note §0), so `SupTowerStepSel`/`SupTowerReachSel`/
  `SupPathDepthSel` (tower-selected steps only) replace the
  unselected reachability in the three gated masters' premises; the
  forgetful lemmas keep the dim-`≤ 1` discharge feeding them.

## Why exact pins (the rework rationale)

At a dim-zero `J` with a `≤`-pin `e ≥ 1`, the nonvanishing conclusion is
false (`χ` eventually constant), so the `≤`-pin induction of
`sup_tower_nonvanishing` cannot case-split its way out: the dim-zero branch
is unprovable. Exact pins (`ringKrullDim = d`) internalize the split the
G2 note asks for: the induction goes on the exact pin value, the
`0` branch is dim-zero (growth via `supDimZeroBase_unconditional`,
nonvanishing via the positivity seed), and the `d + 1` branch is
positive-dimensional (the tower fires, exactness maintained by the
tower-supplied exact drop). No `KrullDimLE 0` case-split is needed inside:
a `d + 1` pin already excludes dim-zero, and properness follows from any
exact pin (`sup_exactDim_ne_top`). The exact drop (dimension falls by
exactly one) is false for general non-catenary rings, so it stays an
explicit tower component — discharged by T1 only for the specific `R_Q`.

## Status

unconditional (from explicit T1 data): `supT1_reg_mem_of_mul_mem`,
`supColon_of_t1Data`, `sup_exactDim_ne_top`, `sup_krullDimLE_of_exactPin`,
`supSelectColon_of_towerExact`, `supTowerExactGated_of_tower`,
`supSelectColon_of_towerExactGated`.
SPEC: `SupT1Data`, `SupTowerExact`, `SupTowerExactGated`,
`SupTowerStep`, `SupTowerReach`, `SupPathDepth`, `SupTowerStepSel`,
`SupTowerReachSel`, `SupPathDepthSel`.
conditional-exact on `[SupTowerExact]`: `sup_chi_exactDim_growth`,
`sup_tower_nonvanishing_exact`, `hChiReduceAtAss_of_exactTowers`.
conditional-gated on `[SupTowerExactGated, SupPathDepthSel]`:
`sup_chi_exactDim_growth_gated`, `sup_tower_nonvanishing_exact_gated`,
`hChiReduceAtAss_of_gatedTowers`.

## Residual register (verbatim)

closed this lane: [colon-from-superficial transfer `supColon_of_t1Data`],
[exact-dim growth master], [exact-dim nonvanishing master], [verbatim
`HchiReduceAtAss` modulo `SupTowerExact`], [gated-tower canonical
address + path-scoped gated masters (§3)].
open (exact): [`SupTowerExact` over each `R_Q` — per positive-dim `J'`
with exact pin: T1 superficial/order-one existence (homogeneous avoidance
on the project's `associatedGraded`) + the exact-dim drop along the step;
the closer lane fires `hChiReduceAtAss_of_exactTowers` on it;
gated alternative: `SupPathDepthSel ⊥` over each `R_Q` (CM induction
along the selected tower path — no CM API in tree) fired via
`hChiReduceAtAss_of_gatedTowers`].

## Import DAG

New leaf module (no importers): `Regularity/NewtonDifferences` (`seqDiff`,
`IsPolyGrowth`), `Regularity/HilbertSerre`
(`hsIsPolyGrowth_comp_add_succ`), `Regularity/SuperficialReduction`
(`SupSelectData`, `supChi`, `IsSupSes`, `supTotal_growth_lift`,
`sup_lengthFin_supChi`, `supChi_bot`), `Regularity/SesClosure`
(`SupColonStabFor`, `supSes_of_colonStab`,
`supDimZeroBase_unconditional`, `sup_nonvanishing_shift`,
`sup_nonvanishing_lift`, `sup_dimZero_seed`),
`Regularity/ChiDegreeMaster` (`HchiReduceAtAss`, `chiFunQ`), narrow
Mathlib (`=ᶠ`, `associatedPrimes`, `ringKrullDim`, colon, quotient,
`IsSMulRegular`). No cycle risk (leaf).

## References

* `Regularity/HomologicalDepth/SesClosure.lean`: `SupColonStabFor` (:290),
  `supSes_of_colonStab` (:309), `supDimZeroBase_unconditional` (:536),
  `sup_nonvanishing_lift` (:649), `sup_dimZero_seed` (:670),
  `sup_tower_nonvanishing` (:689), `hChiReduceAtAss_of_towers` (:757).
* `Regularity/Multiplicity/ChiDegreeMaster.lean`: `chiFunQ` (:121),
  `HchiReduceAtAss` (:153).
* `Regularity/Multiplicity/SuperficialReduction.lean`: `SupSelectData` (:165),
  `supTotal_growth_lift` (:310), `sup_lengthFin_supChi` (:432),
  `supChi_bot` (:455).
* `Regularity/HomologicalDepth/TowerClosure.lean`: `SupTowerPosDim` (:330).
* `Regularity/Multiplicity/HilbertSerre.lean`:
  `hsIsPolyGrowth_comp_add_succ` (:1606).
* `Regularity/Avoid/MacaulayTwo.lean` (precedent: regularity elimination on
  an ideal quotient).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ColonTransfer

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SesClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster

/-! ## §1. T1-shape superficial data + colon transfer -/

/-- T1-shape superficial datum (T1 conclusion, taken as an explicit
hypothesis — sibling output unavailable): `y` is regular mod `J'` (the
exact `SupStepData` regularity shape) and order-one: every element of
`𝔪 ^ (n + 2) ⊔ J'` divisible by `y` has a quotient in
`𝔪 ^ (n + 1) ⊔ J'`, eventually. This is the Valabrega–Valla trace form of
order-one superficiality: the initial form `y*` has order one, so no
unexpected divisibility occurs past some rank. Existence (T1 lane) comes
from homogeneous prime avoidance on the project's `associatedGraded` —
Mathlib v4.34.0 has zero superficial-element API (grep `superficial`
returns only a prose comment in `Topology/Semicontinuity/Defs.lean`) and
zero `associatedGraded` API (grep returns nothing), so that existence
proof is all new; only the transfer below is proved here.

Specification address (the exact T1 conclusion shape). -/
def SupT1Data {R : Type*} [CommRing R] [IsLocalRing R] (J' : Ideal R)
    (y : R) : Prop :=
  IsSMulRegular (R ⧸ J') y ∧
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ z : R,
      z ∈ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' →
      z ∈ Ideal.span {y} →
      ∃ a : R, a ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' ∧ a * y = z

#print axioms SupT1Data

/-- Regularity elimination in ideal form: `x * y ∈ J'` forces `x ∈ J'`.
Direct wrapper over Mathlib's
`mem_of_isSMulRegular_quotient_of_smul_mem` (the `•` is `*` by
`smul_eq_mul`, up to commutativity). Precedent: `MacaulayTwo.lean`
applies the same lemma to an ideal quotient.
-/
theorem supT1_reg_mem_of_mul_mem {R : Type*} [CommRing R] (J' : Ideal R)
    (y : R) (hreg : IsSMulRegular (R ⧸ J') y) {x : R}
    (h : x * y ∈ J') : x ∈ J' := by
  have hsmul : y • x ∈ ((J' : Ideal R) : Submodule R R) := by
    rw [smul_eq_mul, mul_comm]
    exact h
  exact mem_of_isSMulRegular_quotient_of_smul_mem hreg hsmul

#print axioms supT1_reg_mem_of_mul_mem

/-- Colon-from-superficial transfer: T1-shape data gives the true gate
`SupColonStabFor`. The `⊇` direction is `y ∈ 𝔪` (adic multiplication
proves one level deeper); the `⊆` direction is the order-one datum (the
quotient lies in `𝔪 ^ (n + 1) ⊔ J'`) corrected by regularity
(`(x - a) * y = 0` forces `x - a ∈ J'`). This is the ~100-line transfer
scoped in `SesClosure.lean` §5 and `TowerClosure.lean` §5.
-/
theorem supColon_of_t1Data {R : Type*} [CommRing R] [IsLocalRing R]
    (J' : Ideal R) (y : R)
    (hym : y ∈ IsLocalRing.maximalIdeal R)
    (hT1 : SupT1Data (R := R) J' y) :
    SupColonStabFor (R := R) J' y := by
  obtain ⟨hreg, c, hc⟩ := hT1
  have hpow2 : ∀ n : ℕ, IsLocalRing.maximalIdeal R ^ (n + 1)
      * IsLocalRing.maximalIdeal R
      = IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro n
    rw [mul_comm, ← pow_succ']
  refine ⟨c, fun n hn => ?_⟩
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_colon_singleton] at hx
    have hxB : x * y ∈ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' := by
      rw [smul_eq_mul] at hx
      exact hx
    have hxspan : x * y ∈ Ideal.span {y} :=
      Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩
    obtain ⟨a, haA, hay⟩ := hc n hn (x * y) hxB hxspan
    have h0 : (x - a) * y = 0 := by
      rw [sub_mul, hay, sub_self]
    have hdiff : x - a ∈ J' := by
      apply supT1_reg_mem_of_mul_mem J' y hreg
      rw [h0]
      exact Ideal.zero_mem J'
    have hJ'A : J' ≤ IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' :=
      le_sup_right
    have hxA : x ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' := by
      have heq : x = a + (x - a) := by ring
      rw [heq]
      exact add_mem haA (hJ'A hdiff)
    exact hxA
  · intro hx
    have hxI : x ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' := hx
    rw [Submodule.mem_colon_singleton]
    have hmul : (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J')
        * Ideal.span {y}
        ≤ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' := by
      rw [Ideal.sup_mul]
      apply sup_le
      · calc IsLocalRing.maximalIdeal R ^ (n + 1) * Ideal.span {y}
              ≤ IsLocalRing.maximalIdeal R ^ (n + 1)
                * IsLocalRing.maximalIdeal R :=
              mul_le_mul_of_nonneg_left
                (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hym))
                bot_le
          _ = IsLocalRing.maximalIdeal R ^ (n + 2) := hpow2 n
          _ ≤ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' := le_sup_left
      · calc J' * Ideal.span {y} ≤ J' := Ideal.mul_le_left
          _ ≤ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' := le_sup_right
    have hxB : x * y ∈ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' :=
      hmul (Ideal.mul_mem_mul hxI (Ideal.mem_span_singleton_self y))
    rw [smul_eq_mul]
    exact hxB

#print axioms supColon_of_t1Data

/-! ## §2. Exact-dimension tower + master rework -/

/-- Reshaped exact-dimension tower (T2 residual address): at each
exact pin `d ≥ 1` over a proper ideal, provides `y` with s.o.p. selection
(`SupSelectData`), T1 superficial data (`SupT1Data`), and the exact-dim
drop (the successor quotient has exact pin `d - 1`). This subsumes the
`SupTowerPosDim` reshape (an exact pin `d ≥ 1` already excludes dim-zero
ideals, where the old tower was refuted) and internalizes the G2
case-split: the masters induct on the exact pin, so no `KrullDimLE 0`
split is needed inside. The exact drop is false for general
non-catenary rings, hence stays explicit — T1 discharges it only for the
specific `R_Q`.

Specification (the exact reshaped residual). -/
def SupTowerExact {R : Type*} [CommRing R] [IsLocalRing R] : Prop :=
  ∀ J' : Ideal R, ∀ d : ℕ, J' ≠ ⊤ → 1 ≤ d →
    ringKrullDim (R ⧸ J') = ((d : ℕ∞) : WithBot ℕ∞) →
    ∃ y : R, SupSelectData (R := R) J' y ∧ SupT1Data (R := R) J' y ∧
      ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
        = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)

#print axioms SupTowerExact

/-- An exact pin forces properness: over `J' = ⊤` the quotient is
trivial, so `ringKrullDim = ⊥` (via `ringKrullDim_eq_bot_iff_subsingleton`
+ `Ideal.Quotient.nontrivial_iff`), contradicting the pin `↑↑d ≠ ⊥`.
-/
theorem sup_exactDim_ne_top {R : Type*} [CommRing R] (J' : Ideal R)
    (d : ℕ)
    (hpin : ringKrullDim (R ⧸ J') = ((d : ℕ∞) : WithBot ℕ∞)) :
    J' ≠ ⊤ := by
  intro hcon
  rw [hcon] at hpin
  have hsub : Subsingleton (R ⧸ (⊤ : Ideal R)) := by
    rw [← not_nontrivial_iff_subsingleton, Ideal.Quotient.nontrivial_iff]
    exact not_not_intro rfl
  have hbot : ringKrullDim (R ⧸ (⊤ : Ideal R)) = ⊥ :=
    ringKrullDim_eq_bot_iff_subsingleton.mpr hsub
  rw [hbot] at hpin
  exact WithBot.coe_ne_bot hpin.symm

#print axioms sup_exactDim_ne_top

/-- An exact pin gives the `≤`-bound (for the dim-zero base case input).
-/
theorem sup_krullDimLE_of_exactPin {R : Type*} [CommRing R]
    (J' : Ideal R) (d : ℕ)
    (hpin : ringKrullDim (R ⧸ J') = ((d : ℕ∞) : WithBot ℕ∞)) :
    Ring.KrullDimLE d (R ⧸ J') := by
  rw [Ring.krullDimLE_iff, hpin]
  exact le_rfl

#print axioms sup_krullDimLE_of_exactPin

/-- The exact tower delivers the old (selection ∧ colon) shape at each
positive-dim step: §1 transfer applied to the tower's T1 component.
Bridge for colon-consumers posed in the pre-reshape form.
-/
theorem supSelectColon_of_towerExact {R : Type*} [CommRing R]
    [IsLocalRing R] (htower : SupTowerExact (R := R))
    (J' : Ideal R) (d : ℕ) (hne : J' ≠ ⊤) (hd : 1 ≤ d)
    (hpin : ringKrullDim (R ⧸ J') = ((d : ℕ∞) : WithBot ℕ∞)) :
    ∃ y : R, SupSelectData (R := R) J' y ∧
      SupColonStabFor (R := R) J' y := by
  obtain ⟨y, hsel, hT1, _hpin1⟩ := htower J' d hne hd hpin
  exact ⟨y, hsel, supColon_of_t1Data J' y hsel.1 hT1⟩

#print axioms supSelectColon_of_towerExact

/-- Exact-dimension growth master (rework of `sup_chi_degree_le_dim_gated`):
`deg χ_J ≤ e` from the exact pin `ringKrullDim = e`. HilbertFunctionCount on `e`:
the dim-zero case is the proved `supDimZeroBase_unconditional` (via the
`≤`-bound); the dim-`≥ 1` case fires the exact tower, converts T1 data to
colon data (§1 transfer), assembles the SES equation, applies the
induction hypothesis at the exact-drop pin, shifts, and lifts.

Conditional on exactly `[SupTowerExact]`. -/
theorem sup_chi_exactDim_growth {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (e : ℕ) (J : Ideal R)
    (hpin : ringKrullDim (R ⧸ J) = ((e : ℕ∞) : WithBot ℕ∞))
    (htower : SupTowerExact (R := R)) :
    IsPolyGrowth (fun n => ((supChi (R := R) J n : ℕ) : ℚ)) e := by
  revert J hpin
  induction e with
  | zero =>
    intro J hpin
    have hJ : Ring.KrullDimLE 0 (R ⧸ J) :=
      sup_krullDimLE_of_exactPin J 0 hpin
    exact supDimZeroBase_unconditional J hJ
  | succ e ih =>
    intro J hpin
    have hne : J ≠ ⊤ := sup_exactDim_ne_top J (e + 1) hpin
    obtain ⟨y, hsel, hT1, hpin1⟩ :=
      htower J (e + 1) hne (Nat.le_add_left 1 e) hpin
    have hcol : SupColonStabFor (R := R) J y :=
      supColon_of_t1Data J y hsel.1 hT1
    have hses : IsSupSes (supChi (R := R) J)
        (supChi (R := R) (J ⊔ Ideal.span {y})) :=
      supSes_of_colonStab J y hsel.1 hcol (sup_lengthFin_supChi J)
        (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
    have hsub : e + 1 - 1 = e := Nat.add_sub_cancel e 1
    rw [hsub] at hpin1
    have hIH : IsPolyGrowth
        (fun n => ((supChi (R := R) (J ⊔ Ideal.span {y}) n : ℕ) : ℚ)) e :=
      ih (J ⊔ Ideal.span {y}) hpin1
    have hshift : IsPolyGrowth
        (fun n => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) e :=
      hsIsPolyGrowth_comp_add_succ hIH
    exact supTotal_growth_lift (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) e hses hshift

#print axioms sup_chi_exactDim_growth

/-- Exact-dimension nonvanishing master (rework of `sup_tower_nonvanishing`):
the `e`-th difference of `χ` does not vanish, from the exact pin.
HilbertFunctionCount on `e`: the dim-zero case is the proved positivity seed
`sup_dimZero_seed` (properness from the pin); the dim-`≥ 1` case fires
the exact tower, converts T1 data to colon data (§1 transfer), assembles
the SES equation, and lifts nonvanishing from the exact-drop pin.

Conditional on exactly `[SupTowerExact]`. -/
theorem sup_tower_nonvanishing_exact {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (e : ℕ) (J : Ideal R)
    (hpin : ringKrullDim (R ⧸ J) = ((e : ℕ∞) : WithBot ℕ∞))
    (htower : SupTowerExact (R := R)) :
    ¬ seqDiff e (fun n => ((supChi (R := R) J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  revert J hpin
  induction e with
  | zero =>
    intro J hpin
    rw [seqDiff_zero]
    exact sup_dimZero_seed J (sup_exactDim_ne_top J 0 hpin)
  | succ e ih =>
    intro J hpin
    have hne : J ≠ ⊤ := sup_exactDim_ne_top J (e + 1) hpin
    obtain ⟨y, hsel, hT1, hpin1⟩ :=
      htower J (e + 1) hne (Nat.le_add_left 1 e) hpin
    have hcol : SupColonStabFor (R := R) J y :=
      supColon_of_t1Data J y hsel.1 hT1
    have hsub : e + 1 - 1 = e := Nat.add_sub_cancel e 1
    rw [hsub] at hpin1
    have hIH := ih (J ⊔ Ideal.span {y}) hpin1
    have hshift : ¬ seqDiff e
        (fun n : ℕ => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 :=
      sup_nonvanishing_shift _ e hIH
    have hses : IsSupSes (supChi (R := R) J)
        (supChi (R := R) (J ⊔ Ideal.span {y})) :=
      supSes_of_colonStab J y hsel.1 hcol (sup_lengthFin_supChi J)
        (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
    exact sup_nonvanishing_lift (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) e hses hshift

#print axioms sup_tower_nonvanishing_exact

/-- The exact-tower conclusion, verbatim `HchiReduceAtAss` (ChiDegree
:153): at every `Q ∈ Ass(R ⧸ J)`, the `dimN`-th difference of `χ` does
not vanish, with `dimN` pinned to `ringKrullDim(R_Q)`. The bridge
`chiFunQ = cast ∘ supChi ⊥` is `supChi_bot`; the pin transports over
`⧸ ⊥` by `RingEquiv.quotientBot`; nonvanishing is the exact-dim tower.
This is the input the closer lane fires into
`hdimEqMinAtAss_of_chi_specs` once `SupTowerExact` over each `R_Q` proves.

Conditional on exactly `[htower]` (per-`Q` dimension pin +
exact tower over `R_Q`). -/
theorem hChiReduceAtAss_of_exactTowers (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        SupTowerExact (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J := by
  intro Q _ hQ
  obtain ⟨dimN, hpin, htow⟩ := htower Q hQ
  refine ⟨dimN, hpin, ?_⟩
  have hlink : chiFunQ m K Q = fun n : ℕ =>
      ((supChi (R := Localization.AtPrime Q) ⊥ n : ℕ) : ℚ) := by
    funext n
    change ((HilbertSamuelDegree.hsSamuel (R := Localization.AtPrime Q) n :
      ℕ) : ℚ) = _
    rw [← supChi_bot]
  rw [hlink]
  have hpinBot : ringKrullDim
      (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
      = ((dimN : ℕ∞) : WithBot ℕ∞) := by
    have heq : ringKrullDim
        (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
        = ringKrullDim (Localization.AtPrime Q) :=
      RingEquiv.ringKrullDim (RingEquiv.quotientBot _)
    rw [heq, hpin]
  exact sup_tower_nonvanishing_exact dimN ⊥ hpinBot htow

#print axioms hChiReduceAtAss_of_exactTowers

/-! ## §3. Depth-gated tower + path-scoped gated masters -/

/-- Depth-gated reshape of `SupTowerExact` (§2): verbatim binders plus a
per-firing depth premise (`𝔪 ∉ Ass(R ⧸ J')`). Canonical address for the
gated tower (moved up from `QuotientTowerFire` §3 so the T2 masters
and the T1 chain share one definition — a second copy there made
downstream `open`s ambiguous and broke RepFire elaboration).
`supTowerExactGated_of_quot` (QuotTowerFire) and
`supTowerExactGated_of_quotRep` (RepFire) target this statement.

Specification (the reshaped residual address). -/
def SupTowerExactGated (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ J' : Ideal R, ∀ d : ℕ, J' ≠ ⊤ → 1 ≤ d →
    ringKrullDim (R ⧸ J') = ((d : ℕ∞) : WithBot ℕ∞) →
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J') →
    ∃ y : R, SupSelectData (R := R) J' y ∧ SupT1Data (R := R) J' y ∧
      ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
        = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)

#print axioms SupTowerExactGated

/-- One tower step: `J'` extends `J` by adjoining a single generator.

Specification (reachability infrastructure for the gated masters). -/
def SupTowerStep {R : Type*} [CommRing R] (J J' : Ideal R) : Prop :=
  ∃ y : R, J' = J ⊔ Ideal.span {y}

#print axioms SupTowerStep

/-- Tower reachability: the reflexive-transitive closure of
`SupTowerStep` from `J`. The gated masters induct over reachable
ideals, so the depth premise only ever fires on-path.

Specification (reachability infrastructure for the gated masters). -/
inductive SupTowerReach {R : Type*} [CommRing R] (J : Ideal R) :
    Ideal R → Prop
  | base : SupTowerReach J J
  | step {J' J'' : Ideal R} : SupTowerReach J J' → SupTowerStep J' J'' →
      SupTowerReach J J''

/-- Path depth: `depth ≥ 1` (`𝔪 ∉ Ass`) at every positive-dimensional
ideal reachable from `J`. This is the carefully-scoped replacement for
the ∀`J'` depth hypothesis (false in `dim ≥ 2`, QuotAvoid §5): the
gated masters only need depth along the actual tower path, and the
dim-zero reachable ideals are excluded (over a dim-zero local ring
`𝔪 ∈ Ass` in general, so unqualified path depth would be
un-dischargeable).

Specification (the path-scoped depth residual). -/
def SupPathDepth {R : Type*} [CommRing R] [IsLocalRing R]
    (J : Ideal R) : Prop :=
  ∀ J' : Ideal R, SupTowerReach (R := R) J J' →
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')

#print axioms SupPathDepth

/-- C0-selected tower step (T2-C0 statement repair, cmap design note §0): `J'`
extends `J` by adjoining a single generator `y` that is tower-selected
at the source `J` — s.o.p. selection (`SupSelectData`) plus T1
superficial data (`SupT1Data`), the exact per-firing output shape of
`SupTowerExactGated`. Data are indexed by the source ideal (the design note's
`J'`, cf. the `SupTowerExact` binders where the source is called `J'`):
the gated masters obtain `hsel`/`hT1` at the source from the tower and
extend `SupTowerReachSel` by that same `y`, so the repair is faithful.
The unselected `SupTowerStep` (any generator) made `SupPathDepth ⊥`
false in `dim ≥ 2` (the `(x₁²,x₁x₂)` witness); the witness is
Sel-unreachable (`x₁x₂` is a zerodivisor mod `(x₁²)`, so T1 fails at
step 2).

Specification (the C0 repaired reachability infrastructure). -/
def SupTowerStepSel {R : Type*} [CommRing R] [IsLocalRing R]
    (J J' : Ideal R) : Prop :=
  ∃ y : R, J' = J ⊔ Ideal.span {y} ∧ SupSelectData (R := R) J y ∧
    SupT1Data (R := R) J y

#print axioms SupTowerStepSel

/-- Selected tower reachability: the reflexive-transitive closure of
`SupTowerStepSel` from `J`. C0 mirror of `SupTowerReach`.

Specification (the C0 repaired reachability infrastructure). -/
inductive SupTowerReachSel {R : Type*} [CommRing R] [IsLocalRing R]
    (J : Ideal R) : Ideal R → Prop
  | base : SupTowerReachSel J J
  | step {J' J'' : Ideal R} : SupTowerReachSel J J' →
      SupTowerStepSel J' J'' → SupTowerReachSel J J''

/-- Selected path depth: `depth ≥ 1` (`𝔪 ∉ Ass`) at every
positive-dimensional ideal Sel-reachable from `J`. C0 restatement of
`SupPathDepth` — the target of the CM induction (C1–C3), replacing the
false unselected statement.

Specification (the C0 repaired path-scoped depth residual). -/
def SupPathDepthSel {R : Type*} [CommRing R] [IsLocalRing R]
    (J : Ideal R) : Prop :=
  ∀ J' : Ideal R, SupTowerReachSel (R := R) J J' →
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')

#print axioms SupPathDepthSel

/-- Forgetful: a selected step is a step (selection data discarded).
-/
theorem supTowerStep_forget_sel {R : Type*} [CommRing R] [IsLocalRing R]
    {J J' : Ideal R} (h : SupTowerStepSel (R := R) J J') :
    SupTowerStep (R := R) J J' := by
  obtain ⟨y, heq, _, _⟩ := h
  exact ⟨y, heq⟩

#print axioms supTowerStep_forget_sel

/-- Forgetful: Sel-reachability implies unselected reachability.
-/
theorem supTowerReach_forget_sel {R : Type*} [CommRing R] [IsLocalRing R]
    {J J' : Ideal R} (h : SupTowerReachSel (R := R) J J') :
    SupTowerReach (R := R) J J' := by
  induction h with
  | base => exact SupTowerReach.base
  | step _ hstep ih => exact ih.step (supTowerStep_forget_sel hstep)

#print axioms supTowerReach_forget_sel

/-- Forgetful: unselected path depth implies selected path depth. The
dim-`≤ 1` unconditional discharge (`KoszulSupPathDepthDim1`, posed for
`SupPathDepth`) therefore still feeds the re-pointed gated masters.
-/
theorem supPathDepthSel_of_supPathDepth {R : Type*} [CommRing R]
    [IsLocalRing R] {J : Ideal R} (h : SupPathDepth (R := R) J) :
    SupPathDepthSel (R := R) J :=
  fun J' hreach hpos => h J' (supTowerReach_forget_sel hreach) hpos

#print axioms supPathDepthSel_of_supPathDepth

/-- The ungated tower implies the gated tower (the depth premise is
simply discarded).
-/
theorem supTowerExactGated_of_tower {R : Type*} [CommRing R]
    [IsLocalRing R] (htower : SupTowerExact (R := R)) :
    SupTowerExactGated (R := R) :=
  fun J' d hne hd hpin _ => htower J' d hne hd hpin

#print axioms supTowerExactGated_of_tower

/-- The gated tower delivers the old (selection ∧ colon) shape at each
firing: §1 transfer applied to the tower's T1 component. Gated mirror of
`supSelectColon_of_towerExact`.
-/
theorem supSelectColon_of_towerExactGated {R : Type*} [CommRing R]
    [IsLocalRing R] (htowerG : SupTowerExactGated (R := R))
    (J' : Ideal R) (d : ℕ) (hne : J' ≠ ⊤) (hd : 1 ≤ d)
    (hpin : ringKrullDim (R ⧸ J') = ((d : ℕ∞) : WithBot ℕ∞))
    (hdepth : IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')) :
    ∃ y : R, SupSelectData (R := R) J' y ∧
      SupColonStabFor (R := R) J' y := by
  obtain ⟨y, hsel, hT1, _hpin1⟩ := htowerG J' d hne hd hpin hdepth
  exact ⟨y, hsel, supColon_of_t1Data J' y hsel.1 hT1⟩

#print axioms supSelectColon_of_towerExactGated

/-- Exact-dimension growth master, gated form: `deg χ_J ≤ e` from the
exact pin + the gated tower + path depth at `J₀`. HilbertFunctionCount on `e`
generalizing over reachable ideals (reachability extends by the
tower-chosen `y` at each step); positivity comes from the pin inline
(the `supPosDim_of_pin_succ` argument, TowerPosDim:391 — inlined so
this file needs no new import edge), depth from `hpath`. Otherwise
step-for-step the §2 proof.

Gated conditional on `[SupTowerExactGated, SupPathDepthSel]`. -/
theorem sup_chi_exactDim_growth_gated {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (e : ℕ) (J₀ : Ideal R)
    (htower : SupTowerExactGated (R := R))
    (hpath : SupPathDepthSel (R := R) J₀)
    (J : Ideal R) (hreach : SupTowerReachSel (R := R) J₀ J)
    (hpin : ringKrullDim (R ⧸ J) = ((e : ℕ∞) : WithBot ℕ∞)) :
    IsPolyGrowth (fun n => ((supChi (R := R) J n : ℕ) : ℚ)) e := by
  revert J hreach hpin
  induction e with
  | zero =>
    intro J _ hpin
    have hJ : Ring.KrullDimLE 0 (R ⧸ J) :=
      sup_krullDimLE_of_exactPin J 0 hpin
    exact supDimZeroBase_unconditional J hJ
  | succ e ih =>
    intro J hreach hpin
    have hne : J ≠ ⊤ := sup_exactDim_ne_top J (e + 1) hpin
    have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J) := by
      rw [Ring.krullDimLE_iff, hpin]
      intro hle
      have hN : e + 1 ≤ 0 := by exact_mod_cast hle
      omega
    obtain ⟨y, hsel, hT1, hpin1⟩ :=
      htower J (e + 1) hne (Nat.le_add_left 1 e) hpin
        (hpath J hreach hpos)
    have hcol : SupColonStabFor (R := R) J y :=
      supColon_of_t1Data J y hsel.1 hT1
    have hses : IsSupSes (supChi (R := R) J)
        (supChi (R := R) (J ⊔ Ideal.span {y})) :=
      supSes_of_colonStab J y hsel.1 hcol (sup_lengthFin_supChi J)
        (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
    have hsub : e + 1 - 1 = e := Nat.add_sub_cancel e 1
    rw [hsub] at hpin1
    have hreach1 : SupTowerReachSel (R := R) J₀ (J ⊔ Ideal.span {y}) :=
      hreach.step ⟨y, rfl, hsel, hT1⟩
    have hIH : IsPolyGrowth
        (fun n => ((supChi (R := R) (J ⊔ Ideal.span {y}) n : ℕ) : ℚ)) e :=
      ih (J ⊔ Ideal.span {y}) hreach1 hpin1
    have hshift : IsPolyGrowth
        (fun n => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) e :=
      hsIsPolyGrowth_comp_add_succ hIH
    exact supTotal_growth_lift (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) e hses hshift

#print axioms sup_chi_exactDim_growth_gated

/-- Exact-dimension nonvanishing master, gated form: the `e`-th
difference of `χ` does not vanish, from the exact pin + the gated
tower + path depth at `J₀`. Same induction pattern as
`sup_chi_exactDim_growth_gated` (§3); otherwise step-for-step the §2
nonvanishing proof.

Gated conditional on `[SupTowerExactGated, SupPathDepthSel]`. -/
theorem sup_tower_nonvanishing_exact_gated {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (e : ℕ) (J₀ : Ideal R)
    (htower : SupTowerExactGated (R := R))
    (hpath : SupPathDepthSel (R := R) J₀)
    (J : Ideal R) (hreach : SupTowerReachSel (R := R) J₀ J)
    (hpin : ringKrullDim (R ⧸ J) = ((e : ℕ∞) : WithBot ℕ∞)) :
    ¬ seqDiff e (fun n => ((supChi (R := R) J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  revert J hreach hpin
  induction e with
  | zero =>
    intro J _ hpin
    rw [seqDiff_zero]
    exact sup_dimZero_seed J (sup_exactDim_ne_top J 0 hpin)
  | succ e ih =>
    intro J hreach hpin
    have hne : J ≠ ⊤ := sup_exactDim_ne_top J (e + 1) hpin
    have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J) := by
      rw [Ring.krullDimLE_iff, hpin]
      intro hle
      have hN : e + 1 ≤ 0 := by exact_mod_cast hle
      omega
    obtain ⟨y, hsel, hT1, hpin1⟩ :=
      htower J (e + 1) hne (Nat.le_add_left 1 e) hpin
        (hpath J hreach hpos)
    have hcol : SupColonStabFor (R := R) J y :=
      supColon_of_t1Data J y hsel.1 hT1
    have hsub : e + 1 - 1 = e := Nat.add_sub_cancel e 1
    rw [hsub] at hpin1
    have hreach1 : SupTowerReachSel (R := R) J₀ (J ⊔ Ideal.span {y}) :=
      hreach.step ⟨y, rfl, hsel, hT1⟩
    have hIH := ih (J ⊔ Ideal.span {y}) hreach1 hpin1
    have hshift : ¬ seqDiff e
        (fun n : ℕ => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 :=
      sup_nonvanishing_shift _ e hIH
    have hses : IsSupSes (supChi (R := R) J)
        (supChi (R := R) (J ⊔ Ideal.span {y})) :=
      supSes_of_colonStab J y hsel.1 hcol (sup_lengthFin_supChi J)
        (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
    exact sup_nonvanishing_lift (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) e hses hshift

#print axioms sup_tower_nonvanishing_exact_gated

/-- The gated-tower conclusion, verbatim `HchiReduceAtAss` (ChiDegree
:153): the `hChiReduceAtAss_of_exactTowers` (§2) plug re-fired on the
gated tower + path depth at `⊥` over each `R_Q`. The per-`Q` depth
premise is path-scoped (`SupPathDepthSel ⊥`), not ∀`J'` — the ∀`J'`
form is false in `dim ≥ 2` (QuotAvoid §5), while the selected-path
form is the exact residual for the CM-induction closer (C0 repair:
unselected path depth is likewise false in `dim ≥ 2`).

Gated conditional on per-`Q` `[SupTowerExactGated,
SupPathDepthSel ⊥]` (+ per-`Q` dimension pin). -/
theorem hChiReduceAtAss_of_gatedTowers (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        SupTowerExactGated (R := Localization.AtPrime Q) ∧
        SupPathDepthSel (R := Localization.AtPrime Q) ⊥) :
    HchiReduceAtAss m K J := by
  intro Q _ hQ
  obtain ⟨dimN, hpin, htow, hpath⟩ := htower Q hQ
  refine ⟨dimN, hpin, ?_⟩
  have hlink : chiFunQ m K Q = fun n : ℕ =>
      ((supChi (R := Localization.AtPrime Q) ⊥ n : ℕ) : ℚ) := by
    funext n
    change ((HilbertSamuelDegree.hsSamuel (R := Localization.AtPrime Q) n :
      ℕ) : ℚ) = _
    rw [← supChi_bot]
  rw [hlink]
  have hpinBot : ringKrullDim
      (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
      = ((dimN : ℕ∞) : WithBot ℕ∞) := by
    have heq : ringKrullDim
        (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
        = ringKrullDim (Localization.AtPrime Q) :=
      RingEquiv.ringKrullDim (RingEquiv.quotientBot _)
    rw [heq, hpin]
  exact sup_tower_nonvanishing_exact_gated dimN ⊥ htow hpath ⊥
    SupTowerReachSel.base hpinBot

#print axioms hChiReduceAtAss_of_gatedTowers

end ColonTransfer
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
