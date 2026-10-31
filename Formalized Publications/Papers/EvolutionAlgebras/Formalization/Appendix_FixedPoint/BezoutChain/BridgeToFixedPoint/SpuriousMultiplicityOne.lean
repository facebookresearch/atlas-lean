/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ProjectiveFiniteness
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.ChartCompat
import Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity
import Appendix_FixedPoint.BezoutChain.Geometry.MkSystemChart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Weight
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Spurious-point multiplicity one (mult1 lane)

Target (verbatim shape of `MkSecondPoint`'s `h_mult1_spurious` binder):
`localPointMultiplicity m K (mkSystem m K F) ℓ hc (distinguishedPoint m K) = 1`
for all `m F hF ℓ hc` (`m_{P∞} = 1` via Nakayama).

## Approach-1 recon verdict (revised against current API): the pieces compose modulo local `hloc`

* `MkSystemSmoothness.distinguished_inputs_mkSystem` concludes the canonical
  `localPointMultiplicity` (third conjunct), via `Counting.smooth_implies_mult_one`
  (`Counting.lean` lines 579–603), whose `hloc` is the local
  `localMultiplicity … p.rep … = 1` (discharged by `LocalMultiplicity.hlocLocal` /
  `hlocBundle` modulo the regular-local input). The target needs exactly this
  canonical `localPointMultiplicity` (local length at `p.rep`, `0` off the locus).
* The residual gap is therefore the local `hloc` at `(ℓ, p.rep)` for all `ℓ` —
  not a global/local mismatch (the old global `finrank K chartRing = 1` shape
  is retained in `Definitions` but no longer on this path). The transport below
  (`mult1_spurious_of_hfin_transport`) discharges it from `dist_mult_one`
  via `hchart`/`hrep`.
* What does compose: `LocalMultiplicity.hlocalLocal` (needs locus finiteness `hfin`)
  identifies the target with `localMultiplicity` at `p.rep`, and
  `LinearEquiv.finrank_eq` turns a local `hequiv : locRingAt ≃ₗ[K] K` into the
  value `1`. This reduction is proved below as `mult1_spurious_of_hequiv`,
  conditional on exactly `hfin` + `hequiv` (stated at `p.rep` with
  membership-derived proofs). The `IsSmoothPoint` input of `hlocLocal` is
  bypassed (that hypothesis is unused there); smoothness is not re-proved.

The residual `hequiv` is equivalent to the conclusion (either direction is a
few lines given nontriviality), so this conditional is documented as a
reduction, not a closure: the target is blocked on `hequiv`.

## Approach-2 status: Nakayama proved, local computation blocked

* Mathlib v4.34.0 has Nakayama: `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`
  (`Mathlib/RingTheory/Finiteness/Nakayama.lean`) plus the Jacobson-form
  variants in `Mathlib/RingTheory/Nakayama.lean`. No elementary proof needed.
* The sketch's Fact (`fact:nakayama`) in directly usable local-ring form is
  proved below (`nakayama_maximalIdeal_eq_bot_of_le_smul`): over a local ring,
  an FG submodule with `N ≤ maximalIdeal • N` is `⊥`.
* What remains (the gap to exact): the `m = m² + I` computation
  (`uᵢ = fᵢ(u) - qᵢ`, `fᵢ(u) ∈ m²`) in `chartRing`/`locRingAt` vocabulary.
  This needs the affine-chart identification of the degree-0 chart plus named
  coordinate generators and their maximal-ideal membership — none of which
  exists: Mathlib has no dehomogenization API (grep-verified: zero hits for
  `dehomogen` in `Mathlib/`), and `LocalMultiplicity` gap G3 documents the missing
  Jacobian-criterion link (only cotangent/submersive/presentation API
  in-tree). This is multi-file chart-geometry work, out of scope for this lane.

## Second-prize note (`IsAlgClosed`)

No `IsAlgClosed`-conditional variant is claimed: the sketch's mult1 proof is
characteristic-free and never uses algebraic closedness, so such a hypothesis
would not discharge any step — the gap (`hequiv`, above) is orthogonal to it.
Gap-to-exact for the verbatim target is exactly the `hequiv` discharge.

## DAG safety

This file imports only `Statement.Definitions`, `Geometry.LocalMultiplicity`,
`Geometry.MkSystemChart`, and narrow Mathlib modules. It never imports
`Statement.Statement`, `Geometry.Counting`, `BridgeToFixedPoint.MkSystemSmoothness`, or
`Geometry.ProjectiveLocus`; the three sibling shapes it needs (homogeneous
scaling, `mkSystem` homogeneity, spurious-point membership) are mirrored
under `_local` names with by-name citations, per the `LocalMultiplicity` precedent
(`jacShapeAt`).

## Wiring update: `hequiv` closed at the distinguished chart

`MkSystemChart.dist_mult_one` (imported; DAG-safe — nothing imports this
file, and the `MkSystemChart` closure is `ChartFiltration`/`LocalMultiplicity`/
`Definitions` + Mathlib) discharges `hequiv` unconditionally at
`(distEll, zRep)`. `mult1_spurious_of_hfin_transport` wires it into the
verbatim target: status conditional-exact `[hfin, hchart, hrep]`, where
`hfin` is the `AffineFinite`-shape locus finiteness (further ⇐
`[BasePointFree, KrullDimLE 0]` via `locus_finite_of_bpf_affine` +
`affineZero_finite_of_krullDimLE_zero`, quoted by name, not chased) and
`hchart`/`hrep` are the chart/rep transport equations. Exact-`[hfin]` is
unreachable without them: the closed `hequiv` sits at fixed
`(distEll, zRep)` while the target quantifies over all `ℓ` at `p.rep`
(`rep` is `Quotient.out`, not `zRep`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E] [Module K E]

/-- Homogeneous scaling of evaluation (local mirror of
`ProjectiveLocus.eval_smul_of_isHomogeneous`, cited by name, never imported):
`eval (a • v) φ = a ^ d * eval v φ`. Proof mirrors the sibling's `as_sum` +
per-monomial computation.

## References

* `Geometry.ProjectiveLocus`, `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous`
  (mirrored).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.weight_apply`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `Finset.mul_sum`,
  `map_sum`. -/
theorem eval_smul_of_isHomogeneous_local {σ : Type*} {φ : MvPolynomial σ K}
    {d : ℕ} (hφ : φ.IsHomogeneous d) (a : K) (v : σ → K) :
    MvPolynomial.eval (a • v) φ = a ^ d * MvPolynomial.eval v φ := by
  rw [φ.as_sum]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hsup : φ.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hwt : Finsupp.weight (1 : σ → ℕ) e = d := hφ hsup
  rw [Finsupp.weight_apply] at hwt
  have hsum : e.sum (fun _ c => c) = d := by
    simpa using hwt
  simp only [MvPolynomial.eval_monomial]
  have hterm : e.prod (fun n en => ((a • v) n) ^ en)
      = a ^ d * e.prod (fun n en => (v n) ^ en) := by
    have h1 : ∀ n en, ((a • v) n) ^ en = a ^ en * (v n) ^ en := fun n en => by
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    simp_rw [h1]
    unfold Finsupp.prod
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hnat : e.support.sum (fun n => e n) = d := by
      have h2 := hsum
      unfold Finsupp.sum at h2
      simpa using h2
    rw [hnat]
  rw [hterm, mul_left_comm]

/-- `mkSystem` preserves quadratic homogeneity (local mirror of
`Statement.mkSystem_homogeneous`, cited by name, never imported).

## References

* `Statement.Statement`, `Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous` (mirrored).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.rename_isHomogeneous/sub/mul`,
  `MvPolynomial.isHomogeneous_X`. -/
theorem mkSystem_homogeneous_local (m : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    ∀ i, ((mkSystem m K F) i).IsHomogeneous 2 := by
  intro i
  simp only [mkSystem]
  exact ((hF i).rename_isHomogeneous).sub
    (by simpa using
      (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-- The `mkSystem` equations vanish at `zRep` (local mirror of
`MkSystemSmoothness.hmem_eval_mkSystem`, cited by name, never imported): the
renamed-`Fᵢ` piece by homogeneity (positive degree, hence `0` at the origin),
the `-z·xᵢ` piece since `x = 0` there.

## References

* `BridgeToFixedPoint.MkSystemSmoothness`, `Appendix_FixedPoint.BezoutChain.hmem_eval_mkSystem`
  (mirrored).
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.eval_rename`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.castSucc_ne_last`. -/
theorem hmem_eval_mkSystem_local (m : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (m + 1)) :
    MvPolynomial.eval (zRep m K) ((mkSystem m K F) i) = 0 := by
  have hdecomp : ((mkSystem m K F) i)
      = MvPolynomial.rename Fin.castSucc (F i)
        - MvPolynomial.X (Fin.last (m + 1)) * MvPolynomial.X (Fin.castSucc i) :=
    rfl
  have hcomp : (zRep m K) ∘ Fin.castSucc = (0 : Fin (m + 1) → K) := by
    funext x
    simp only [Function.comp_apply, Pi.zero_apply]
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last x) _
  have hF0 : MvPolynomial.eval (0 : Fin (m + 1) → K) (F i) = 0 := by
    have h := eval_smul_of_isHomogeneous_local K (hF i) (0 : K)
      (0 : Fin (m + 1) → K)
    rw [zero_smul] at h
    rw [h]
    simp
  have h1 : MvPolynomial.eval (zRep m K)
      (MvPolynomial.rename Fin.castSucc (F i)) = 0 := by
    rw [MvPolynomial.eval_rename, hcomp]
    exact hF0
  have hz : zRep m K (Fin.castSucc i) = 0 :=
    Pi.single_eq_of_ne (Fin.castSucc_ne_last i) _
  have h2 : MvPolynomial.eval (zRep m K)
      (MvPolynomial.X (Fin.last (m + 1)) * MvPolynomial.X (Fin.castSucc i))
      = 0 := by
    rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, hz, mul_zero]
  rw [hdecomp, map_sub, h1, h2, sub_zero]

/-- The spurious point lies on the `mkSystem` locus (local mirror of
`MkSystemSmoothness.mem_vanishingLocus_mkSystem`, cited by name, never imported):
lifts the `zRep` evaluation via homogeneity scaling along the projective
fibre.

## References

* `BridgeToFixedPoint.MkSystemSmoothness`,
  `Appendix_FixedPoint.BezoutChain.mem_vanishingLocus_mkSystem` (mirrored).
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`. -/
theorem spurious_mem_mkSystem (m : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    distinguishedPoint m K ∈ vanishingLocus m K (mkSystem m K F) := by
  have hGhom := mkSystem_homogeneous_local K m F hF
  have h0 := hmem_eval_mkSystem_local K m F hF
  intro v hv hmk i
  have hrep : Projectivization.mk K (zRep m K) (zRep_ne_zero m K)
      = distinguishedPoint m K := rfl
  rw [← hrep] at hmk
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' K v (zRep m K) hv (zRep_ne_zero m K)).mp hmk
  have hscale := eval_smul_of_isHomogeneous_local K (hGhom i) a (zRep m K)
  rw [ha] at hscale
  rw [hscale, h0 i, mul_zero]

/-- Conditional mult1 reduction: the verbatim target follows from locus
finiteness plus the local `K`-identification at `p.rep`. Proved by
`LocalMultiplicity.hlocalLocal` (bridge to `localMultiplicity`) plus the finrank
computation; the residual `hequiv` is the documented G3 gap (equivalent to
the conclusion — see the module docstring — so this is a reduction, not a
closure).

## References

* `Geometry.LocalMultiplicity`, `Appendix_FixedPoint.BezoutChain.hlocalLocal`,
  `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`,
  `Module.finrank_self`. -/
theorem mult1_spurious_of_hequiv (m : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (ℓ : Fin (m + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
      (_ : p ∈ vanishingLocus m K (mkSystem m K F))
      (v : Fin (m + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin m K ℓ) ≠ 0)
    (hfin : (vanishingLocus m K (mkSystem m K F)).Finite)
    (hequiv : locRingAt m K (mkSystem m K F) ℓ (distinguishedPoint m K).rep
      (fun i => spurious_mem_mkSystem K m F hF _ _
        (Projectivization.mk_rep (distinguishedPoint m K)) i)
      (hc _ (spurious_mem_mkSystem K m F hF) _ _
        (Projectivization.mk_rep (distinguishedPoint m K))) ≃ₗ[K] K) :
    localPointMultiplicity m K (mkSystem m K F) ℓ hc
      (distinguishedPoint m K) = 1 := by
  have hmem : distinguishedPoint m K ∈ vanishingLocus m K (mkSystem m K F) :=
    spurious_mem_mkSystem K m F hF
  have hloc := hlocalLocal m K (mkSystem m K F) ℓ hfin hc
    (distinguishedPoint m K)
    ((mem_locLocusFinset m K (mkSystem m K F) hfin _).mpr hmem)
  rw [hloc]
  exact (LinearEquiv.finrank_eq hequiv).trans (Module.finrank_self K)

/-- Nakayama's lemma in local-ring form (the sketch's `fact:nakayama`, proved
from the in-tree general form): over a commutative local ring, a finitely
generated submodule absorbed by the maximal ideal is `⊥`. The in-tree lemma
yields `r` with `r - 1 ∈ maximalIdeal` killing `N`; such an `r` is a unit
(`1 = r - (r - 1)` cannot lie in the maximal ideal), hence `N = ⊥`.

## References

* `Mathlib/RingTheory/Finiteness/Nakayama.lean`,
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`.
* `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`,
  `IsLocalRing.notMem_maximalIdeal`. -/
theorem nakayama_maximalIdeal_eq_bot_of_le_smul (R : Type*) [CommRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hN : N.FG)
    (hle : N ≤ IsLocalRing.maximalIdeal R • N) : N = ⊥ := by
  obtain ⟨r, hr, hr'⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (IsLocalRing.maximalIdeal R) N hN hle
  have hunit : IsUnit r := by
    by_contra hnu
    have hmem : r ∈ IsLocalRing.maximalIdeal R := by
      by_contra hcon
      exact hnu (IsLocalRing.notMem_maximalIdeal.mp hcon)
    have h1mem : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have h := sub_mem hmem hr
      simp at h
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1mem
  rw [Submodule.eq_bot_iff]
  intro n hn
  have h0 : r • n = 0 := hr' n hn
  obtain ⟨u, hu⟩ := hunit
  have h0' : ((u : Rˣ) : R) • n = 0 := by
    rw [hu]
    exact h0
  have h1 : (((u⁻¹ : Rˣ)) : R) * (((u : Rˣ)) : R) = 1 := u.inv_mul
  calc n = (1 : R) • n := (one_smul _ _).symm
    _ = (((u⁻¹ : Rˣ) : R) * (((u : Rˣ)) : R)) • n := by rw [h1]
    _ = (((u⁻¹ : Rˣ)) : R) • ((((u : Rˣ)) : R) • n) := mul_smul _ _ _
    _ = 0 := by rw [h0', smul_zero]

/-- The distinguished point's canonical representative lies in the
distinguished chart: `eval p.rep (mkLin distEll) ≠ 0`. From `mk_rep`,
`p.rep` is a scalar multiple `a • zRep` (`mk_eq_mk_iff'`), the scalar is
nonzero (else `p.rep = 0`, contra `rep_nonzero`), and the distinguished
chart form reads off the last coordinate (`eval_mkLin_distEll`), which is
that nonzero scalar.

## References

* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.eval_mkLin_distEll`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`, `Projectivization.mk_rep`,
  `Projectivization.rep_nonzero`.
* Core `Pi.single_eq_same`, `Pi.smul_apply`, `smul_eq_mul`, `zero_smul`. -/
theorem hℓdist_at_rep (m : ℕ) :
    MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K (distEll m K)) ≠ 0 := by
  have hmk : Projectivization.mk K (distinguishedPoint m K).rep
        (distinguishedPoint m K).rep_nonzero
      = Projectivization.mk K (zRep m K) (zRep_ne_zero m K) :=
    Projectivization.mk_rep (distinguishedPoint m K)
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' K (distinguishedPoint m K).rep
      (zRep m K) _ _).mp hmk
  have hane : a ≠ 0 := by
    intro h0
    have hrep0 : (distinguishedPoint m K).rep = 0 := by
      rw [← ha, h0, zero_smul]
    exact (distinguishedPoint m K).rep_nonzero hrep0
  have h1 : zRep m K (Fin.last (m + 1)) = 1 := Pi.single_eq_same _ _
  rw [eval_mkLin_distEll, ← ha, Pi.smul_apply, smul_eq_mul, h1, mul_one]
  exact hane

/-- Wiring: the verbatim mult1 target follows from locus finiteness plus
the two transport equations into the closed `dist_mult_one` — `hchart`
(changes the chart `ℓ ↦ distEll` at `p.rep`) and `hrep` (changes the
representative `p.rep ↦ zRep` in the distinguished chart). Proof: the
`hlocalLocal` bridge to `localMultiplicity` at `p.rep`, then the two
rewrites (proof-term mismatches absorbed by proof irrelevance in `exact`),
then the closed `dist_mult_one`.

Conditional on exactly `[hfin, hchart, hrep]` given `[hF, hc]`.
* `hfin` is the `AffineFinite`-shape residual
  (`(vanishingLocus m K (mkSystem m K F)).Finite`), further ⇐
  `[BasePointFree m K F, Ring.KrullDimLE 0 (affine quotient)]` via
  `MkSystemChart.locus_finite_of_bpf_affine` +
  `AffineFinite.affineZero_finite_of_krullDimLE_zero` (quoted by name;
  `hdim`/`hBPF` are not trivially available in-repo, so listed, not chased).
* `hchart` is the `Counting.mult_chart_independent` `hloceq` shape at this
  point (chart-independence of `localMultiplicity`; no in-repo discharge —
  needs a localization iso between different chart rings).
* `hrep` is representative-independence in the distinguished chart
  (`p.rep = a • zRep` scaling; no in-repo discharge — needs
  scale-invariance of `chartEval` on `chartRing`).

## References

* `Geometry.LocalMultiplicity`, `Appendix_FixedPoint.BezoutChain.hlocalLocal`,
  `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.dist_mult_one`,
  `Appendix_FixedPoint.BezoutChain.distEll`,
  `Appendix_FixedPoint.BezoutChain.hvGdist`, `Appendix_FixedPoint.BezoutChain.hℓdist`.
* This module, `Appendix_FixedPoint.BezoutChain.spurious_mem_mkSystem`,
  `Appendix_FixedPoint.BezoutChain.hℓdist_at_rep`.
* `Geometry.Counting`, `Appendix_FixedPoint.BezoutChain.mult_chart_independent` (`hloceq` shape). -/
theorem mult1_spurious_of_hfin_transport (m : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (ℓ : Fin (m + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
      (_ : p ∈ vanishingLocus m K (mkSystem m K F))
      (v : Fin (m + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin m K ℓ) ≠ 0)
    (hfin : (vanishingLocus m K (mkSystem m K F)).Finite)
    (hchart : localMultiplicity m K (mkSystem m K F) ℓ
        (distinguishedPoint m K).rep
        (fun i => spurious_mem_mkSystem K m F hF _ _
          (Projectivization.mk_rep (distinguishedPoint m K)) i)
        (hc _ (spurious_mem_mkSystem K m F hF) _ _
          (Projectivization.mk_rep (distinguishedPoint m K)))
      = localMultiplicity m K (mkSystem m K F) (distEll m K)
        (distinguishedPoint m K).rep
        (fun i => spurious_mem_mkSystem K m F hF _ _
          (Projectivization.mk_rep (distinguishedPoint m K)) i)
        (hℓdist_at_rep K m))
    (hrep : localMultiplicity m K (mkSystem m K F) (distEll m K)
        (distinguishedPoint m K).rep
        (fun i => spurious_mem_mkSystem K m F hF _ _
          (Projectivization.mk_rep (distinguishedPoint m K)) i)
        (hℓdist_at_rep K m)
      = localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K)) :
    localPointMultiplicity m K (mkSystem m K F) ℓ hc
      (distinguishedPoint m K) = 1 := by
  have hmem : distinguishedPoint m K ∈ vanishingLocus m K (mkSystem m K F) :=
    spurious_mem_mkSystem K m F hF
  have hp : distinguishedPoint m K ∈ locLocusFinset m K (mkSystem m K F) hfin :=
    (mem_locLocusFinset m K (mkSystem m K F) hfin _).mpr hmem
  have hloc := hlocalLocal m K (mkSystem m K F) ℓ hfin hc
    (distinguishedPoint m K) hp
  rw [hloc]
  exact hchart.trans (hrep.trans (dist_mult_one m K F hF))

/-! ## Final wire: `hchart` + `hrep` discharged (hmult-final-wire lane)

`ChartCompat.chartIso_chartCompatIso` (closed chain: `chartIso_g` fraction map
→ `chartIso_gHom` → prime-compl-to-units → `chartIso_F`/`chartIso_G` inverse
pair → `chartIso_ringEquiv` → `chartIso_algEquiv` → linear equiv) inhabits
`ChartCompatIso`, and the imported `MkSystemChart.dist_mult_one` (unconditional
`hequiv` at `(distEll, zRep)`) closes the base case. This section wires both
into the verbatim mult1 target.

DAG check (direct import, no mirrors): this file newly imports
`Geometry.ChartCompat`, whose closure is `Statement.Definitions` /
`Geometry.MkSystemChart` (+ `ChartFiltration` / `LocalMultiplicity`) + Mathlib — none
of which imports this file (the sole importer of this file is
`BridgeToFixedPoint.FinalDischargeHub`, downstream of both). No cycle; no verbatim mirrors
needed.

Conditional on exactly `[hfin]`. -/

/-- The exact `hchart` transport equation at `p.rep`, closed by the chart iso:
`hchart_distEll_of_iso` fed with `chartIso_chartCompatIso` (which takes a
single `hvG` for both charts, hence the shared `hvG₁` here).

## References

* `Geometry.ChartCompat`, `Appendix_FixedPoint.BezoutChain.hchart_distEll_of_iso`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartCompatIso`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.distEll`. -/
theorem hchart_distEll_closed (m : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (ℓ : Fin (m + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓ₁ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K ℓ) ≠ 0)
    (hℓ₂ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K (distEll m K)) ≠ 0) :
    localMultiplicity m K (mkSystem m K F) ℓ (distinguishedPoint m K).rep
        hvG₁ hℓ₁
      = localMultiplicity m K (mkSystem m K F) (distEll m K)
        (distinguishedPoint m K).rep hvG₁ hℓ₂ :=
  hchart_distEll_of_iso m K F ℓ hvG₁ hℓ₁ hvG₁ hℓ₂
    (chartIso_chartCompatIso m K (mkSystem m K F) ℓ (distEll m K)
      (distinguishedPoint m K).rep hvG₁ hℓ₁ hℓ₂)

/-- Final mult1: the verbatim target from locus finiteness alone. The
`mult1_spurious_of_hfin_transport` wiring with `hchart` closed by
`hchart_distEll_closed` (chart iso) and `hrep` closed by
`localMultiplicity_rep_eq_zRep` (from `hF`); the base case is the closed
`MkSystemChart.dist_mult_one`.

Conditional on exactly `[hfin]` given `[hc]`, where `hfin` is the `AffineFinite`-shape
locus finiteness (further ⇐ `[BasePointFree, KrullDimLE 0]` via
`locus_finite_of_bpf_affine` + `affineZero_finite_of_krullDimLE_zero`, quoted
by name, not chased — see `mult1_spurious_of_hfin_transport`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.mult1_spurious_of_hfin_transport`,
  `Appendix_FixedPoint.BezoutChain.hchart_distEll_closed`.
* `Geometry.ChartCompat`, `Appendix_FixedPoint.BezoutChain.localMultiplicity_rep_eq_zRep`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.dist_mult_one` (via the transport). -/
theorem mult1_spurious_of_hfin (m : ℕ)
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
  · exact hchart_distEll_closed K m F ℓ _ _ _
  · exact localMultiplicity_rep_eq_zRep m K F hF _ _

/-! ## Final close: `hfin` discharged (mult1-final lane)

`ProjectiveFiniteness.vanishingLocus_finite_mkSystem_of_bpf` (generic
hfin closure: `locus_finite_of_bpf_affine` over
`affineZero_finite_of_meetsInfinity` with hPDT closed by
`meetsInfinity_of_isHomogeneous`) discharges the `hfin` hypothesis of
`mult1_spurious_of_hfin`, closing the verbatim mult1 target end-to-end.

DAG check (direct import, no mirrors): this file newly imports
`BridgeToFixedPoint.ProjectiveFiniteness`, whose closure is
`BridgeToFixedPoint.FixedPointFromBezout`
(`BridgeToFixedPoint.ProjectiveToConeExtraction` / `BridgeToFixedPoint.MkSystemSmoothness` /
`Statement.Definitions`) /
`Geometry.AffineFinite` / `Geometry.CurveMeetsHyperplane` /
`Geometry.MkSystemChart` + Mathlib — none of which imports this file (the
sole importer of this file is `BridgeToFixedPoint.FinalDischargeHub`, downstream of
both). No cycle; no verbatim mirrors needed.

Conditional on exactly `[hF, hBPF]` plus the `[IsAlgClosed K]`
instance. -/

/-- End-to-end mult1 from `[hF, hBPF, hc]` plus `[IsAlgClosed K]`: the
`mult1_spurious_of_hfin` wiring with `hfin` discharged by the generic
hfin closure (`vanishingLocus_finite_mkSystem_of_bpf`).

Conditional on exactly `[hF, hBPF, hc]` plus the `[IsAlgClosed K]`
instance (`hF` the quadratic-homogeneity input, `hBPF` the tex `(bpf)`
input; both are theorem inputs, not in-repo obligations).

## References

* This module, `Appendix_FixedPoint.BezoutChain.mult1_spurious_of_hfin` (hfin-conditional wire).
* `BridgeToFixedPoint.ProjectiveFiniteness`,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus_finite_mkSystem_of_bpf` (generic hfin, §5).
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.BasePointFree` (residual shape). -/
theorem mult1_spurious_of_bpf (m : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    [IsAlgClosed K]
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hBPF : BasePointFree m K F)
    (ℓ : Fin (m + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (m + 2) → K))
      (_ : p ∈ vanishingLocus m K (mkSystem m K F))
      (v : Fin (m + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin m K ℓ) ≠ 0) :
    localPointMultiplicity m K (mkSystem m K F) ℓ hc
      (distinguishedPoint m K) = 1 :=
  mult1_spurious_of_hfin K m F hF ℓ hc
    (vanishingLocus_finite_mkSystem_of_bpf m K F hF hBPF)

/-! ## Axiom audit (within `propext` / `Classical.choice` /
`Quot.sound`). -/

#print axioms eval_smul_of_isHomogeneous_local
#print axioms mkSystem_homogeneous_local
#print axioms hmem_eval_mkSystem_local
#print axioms spurious_mem_mkSystem
#print axioms mult1_spurious_of_hequiv
#print axioms nakayama_maximalIdeal_eq_bot_of_le_smul
#print axioms hℓdist_at_rep
#print axioms mult1_spurious_of_hfin_transport
#print axioms hchart_distEll_closed
#print axioms mult1_spurious_of_hfin
#print axioms mult1_spurious_of_bpf

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
