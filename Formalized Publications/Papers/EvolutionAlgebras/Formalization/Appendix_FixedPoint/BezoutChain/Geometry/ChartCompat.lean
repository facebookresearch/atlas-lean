/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.MkSystemChart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Cross-chart compatibility of the local multiplicity (chart-compat lane)

This module discharges the two transport equations that
`BridgeToFixedPoint.SpuriousMultiplicityOne.mult1_spurious_of_hfin_transport` is conditional on
(exact shapes quoted from `SpuriousMultiplicityOne.lean` lines 388–405):

* `hchart`: `localMultiplicity m K (mkSystem m K F) ℓ p.rep …`
  `= localMultiplicity m K (mkSystem m K F) (distEll m K) p.rep …`
  (change of chart `ℓ ↦ distEll` at `p.rep`; the `Counting.mult_chart_independent`
  `hloceq` shape at this point).
* `hrep`: `localMultiplicity m K (mkSystem m K F) (distEll m K) p.rep …`
  `= localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K) …`
  (change of representative `p.rep ↦ zRep` in the distinguished chart).

## Deliverables

* (2) `hrep` — proved conditional-exact-`[hF]` (the quadric homogeneity input):
  `chartEval` is scale-invariant (`chartEval_smul`: evaluation at `a • v`
  agrees with evaluation at `v` as ring homs, since numerator and denominator
  scale by the same `a ^ d` and the `IsLocalization.lift` spec equation is
  preserved — no `a ≠ 0` input is needed, the nonvanishing `hℓw` is taken as
  a hypothesis), hence the point ideals agree (`pointIdeal_smul`), hence the
  local lengths agree (`localMultiplicity_smul`). The `dif`-free transport
  through propositionally-equal ideals is `finrank_loc_of_ideal_eq`
  (`subst` + `rfl`, closing by definitional proof irrelevance of the maximality
  instances). The exact `hrep` shape is `localMultiplicity_rep_eq_zRep`, with
  the scaling `p.rep = a • zRep` derived in-file from `mk_rep` /
  `mk_eq_mk_iff'` (no nonzero-scalar input needed anywhere).
* (1) `hchart` — proved unconditional: the exact residual `ChartCompatIso`
  (the `K`-linear iso of the two chart-local rings at `v`) is inhabited by
  the hand-built fraction-map construction below (`chartIso_chartCompatIso`),
  so `hloceq_forall_of_iso` closes the full `Counting.mult_chart_independent`
  `hloceq` binder and `hchart_distEll_of_iso` the exact `hchart` shape with no
  hypotheses beyond the chart data. Status: closed.
  (`localMultiplicity_chart_independent_of_iso`, via `LinearEquiv.finrank_eq`,
  is the consumption step.)

## How the `hchart` residual is discharged

The two local rings are localizations of *different* base rings (the degree-0
parts `(S_{ℓ₁})₀`, `(S_{ℓ₂})₀` of different ambient localizations), so no
Mathlib `IsLocalization` comparison lemma applies directly: the iso is built
by hand as a fraction map (`s/ℓ₁^d ↦ (s/ℓ₂^d)/(ℓ₁^d/ℓ₂^d)` on homogeneous
lifts) with well-definedness (`chartIso_gAux_wellDefined`), ring-hom
(`chartIso_gHom`), prime-complement-to-units
(`chartIso_primeCompl_to_units`, lifting to `chartIso_F`/`chartIso_G` via
`IsLocalization.lift`), and two-sided-inverse (`chartIso_fg_id` /
`chartIso_gf_id` via the roundtrip `chartIso_roundtrip`) arguments, all
through the `Localization.mk'` API — a multi-hundred-line construction, now
proved unconditionally in the `Chart-iso construction` sections below. The
scalar behavior (`chartIso_gHom_algebraMap`, `chartIso_F_commutes`) promotes
the ring iso to the `K`-linear iso (`chartIso_algEquiv`,
`chartIso_toLinearEquiv`) inhabiting `ChartCompatIso`.

## DAG safety

Imports only clean `Statement.Definitions` + `Geometry.MkSystemChart` (whose closure
is `ChartFiltration`/`LocalMultiplicity`/`Definitions` + Mathlib) plus narrow Mathlib
modules. Never imports `Statement.Statement`, `Geometry.Counting`,
`BridgeToFixedPoint.SpuriousMultiplicityOne`, or any other downstream file; the two sibling shapes
needed (homogeneous scaling, `mkLin` homogeneity) are mirrored under `_compat`
names with by-name citations, per the `LocalMultiplicity` precedent (`jacShapeAt`).
The `Chart-iso construction` sections add no imports. No other file imports
this one (fresh leaf).

## References

Mathlib v4.34.0 exact paths/names (each grep-verified in-tree) are cited per
declaration below.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hvG : ∀ i, MvPolynomial.eval v (G i) = 0` — locus-membership equations at
  the representative `v` (`hvGw` is the same shape at the distinguished rep).
* `hℓ`/`hℓw`/`hℓdist : MvPolynomial.eval v (mkLin …) ≠ 0` — chart nonvanishing
  at `v` (taken as a hypothesis; no `a ≠ 0` input is ever needed).
* `hF : ∀ i, (F i).IsHomogeneous 2` — quadratic input forms (mkSystem section).
* `hphom : p.IsHomogeneous d` with `hpeq : mk p = s` — homogeneous-lift data
  feeding the hand-built fraction maps.
* Instance: `[Field K]` throughout.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Local mirrors (by-name citations, never imported) -/

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
theorem eval_smul_compat {σ : Type*} {K : Type*} [Field K]
    {φ : MvPolynomial σ K} {d : ℕ} (hφ : φ.IsHomogeneous d) (a : K)
    (v : σ → K) :
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

/-- The chart linear form is homogeneous of degree `1` (local mirror of
`ChartFiltration.mkLin_isHomogeneous`, cited by name, never imported).

## References

* `Geometry.ChartFiltration`, `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous` (mirrored).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.sum`, `MvPolynomial.isHomogeneous_C_mul_X`. -/
theorem mkLin_isHomogeneous_compat (n : ℕ) (K : Type*) [Field K]
    (ℓ : Fin (n + 2) → K) : (mkLin n K ℓ).IsHomogeneous 1 := by
  unfold mkLin
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
    MvPolynomial.isHomogeneous_C_mul_X _ _

/-! ## Scale-invariance of chart evaluation (the `hrep` discharge) -/

/-- Scale-invariance of `chartLocEval` on a presented fraction: for
`s / ℓ^d` with `s` admitting a homogeneous degree-`d` lift `p`, evaluation
at `a • v` agrees with evaluation at `v`. Both the numerator and the
denominator scale by `a ^ d` (via `eval_smul_compat`, using `p`'s lift for
the numerator and `(mkLin ℓ ^ d).IsHomogeneous d` for the denominator), so
the `IsLocalization.lift` spec equation `g s = g ℓ^d * V` is preserved.
No `a ≠ 0` input is needed: the nonvanishing `hℓw` is a hypothesis (the
`a = 0` case is vacuous for it).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartLocEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.
* This module, `Appendix_FixedPoint.BezoutChain.eval_smul_compat`,
  `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous_compat`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.pow`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift_mk`
  (used via definitional unfolding in `rfl`, per the `coneEval_C` precedent).
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_pow`. -/
theorem chartLocEval_smul_mk (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K) (a : K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hvGw : ∀ i, MvPolynomial.eval (a • v) (G i) = 0)
    (hℓw : MvPolynomial.eval (a • v) (mkLin n K ℓ) ≠ 0)
    (d : ℕ) (s : coneQuotient n K G) (p : MvPolynomial (Fin (n + 2)) K)
    (hphom : p.IsHomogeneous d)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range G)) p = s)
    (y : Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G))
      (mkLin n K ℓ)))
    (hy : (y : coneQuotient n K G)
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d) :
    chartLocEval n K G ℓ (a • v) hvGw hℓw (Localization.mk s y)
      = chartLocEval n K G ℓ v hvG hℓ (Localization.mk s y) := by
  set V := chartLocEval n K G ℓ v hvG hℓ (Localization.mk s y) with hVdef
  unfold chartLocEval
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  have hV : coneEval n K G v hvG s
      = coneEval n K G v hvG (y : coneQuotient n K G) * V := by
    rw [hVdef]
    unfold chartLocEval
    rw [Localization.mk_eq_mk'_apply]
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mp rfl
  have hws : coneEval n K G (a • v) hvGw s
      = a ^ d * coneEval n K G v hvG s := by
    have cw : coneEval n K G (a • v) hvGw s
        = MvPolynomial.eval (a • v) p := by
      rw [← hpeq]
      rfl
    have cv : coneEval n K G v hvG s = MvPolynomial.eval v p := by
      rw [← hpeq]
      rfl
    rw [cw, cv, eval_smul_compat hphom a v]
  have hpowmk : (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ)) ^ d
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) ((mkLin n K ℓ) ^ d) := by
    rw [map_pow]
  have hhom : ((mkLin n K ℓ) ^ d).IsHomogeneous d := by
    have h1 := (mkLin_isHomogeneous_compat n K ℓ).pow d
    rwa [one_mul] at h1
  have hwℓ : coneEval n K G (a • v) hvGw (y : coneQuotient n K G)
      = a ^ d * coneEval n K G v hvG (y : coneQuotient n K G) := by
    rw [hy]
    have cw : coneEval n K G (a • v) hvGw
          ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d)
        = MvPolynomial.eval (a • v) ((mkLin n K ℓ) ^ d) := by
      rw [hpowmk]
      rfl
    have cv : coneEval n K G v hvG
          ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d)
        = MvPolynomial.eval v ((mkLin n K ℓ) ^ d) := by
      rw [hpowmk]
      rfl
    rw [cw, cv, eval_smul_compat hhom a v]
  rw [hws, hwℓ, hV]
  ring

/-- Scale-invariance of `chartEval` as ring homs: evaluation at `a • v`
is evaluation at `v`. Every chart element carries its balanced presentation
(`s / ℓ^d` with homogeneous degree-`d` lift), on which
`chartLocEval_smul_mk` applies.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartRing`.
* This module, `Appendix_FixedPoint.BezoutChain.chartLocEval_smul_mk`.
* `Mathlib/Algebra/Ring/Hom/Defs.lean`, `RingHom.ext`,
  `RingHom.comp_apply`. -/
theorem chartEval_smul (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K) (a : K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hvGw : ∀ i, MvPolynomial.eval (a • v) (G i) = 0)
    (hℓw : MvPolynomial.eval (a • v) (mkLin n K ℓ) ≠ 0) :
    chartEval n K G ℓ (a • v) hvGw hℓw
      = chartEval n K G ℓ v hvG hℓ := by
  apply RingHom.ext
  intro x
  obtain ⟨val, d, s, ⟨p, hphom, hpeq⟩, e⟩ := x
  unfold chartEval
  rw [RingHom.comp_apply, RingHom.comp_apply]
  change chartLocEval n K G ℓ (a • v) hvGw hℓw val
    = chartLocEval n K G ℓ v hvG hℓ val
  rw [e]
  exact chartLocEval_smul_mk n K G ℓ v a hvG hℓ hvGw hℓw d s p hphom hpeq
    _ rfl

/-- Scale-invariance of the point ideal: kernels of the equal evaluations.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.pointIdeal`.
* This module, `Appendix_FixedPoint.BezoutChain.chartEval_smul`. -/
theorem pointIdeal_smul (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K) (a : K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hvGw : ∀ i, MvPolynomial.eval (a • v) (G i) = 0)
    (hℓw : MvPolynomial.eval (a • v) (mkLin n K ℓ) ≠ 0) :
    pointIdeal n K G ℓ (a • v) hvGw hℓw
      = pointIdeal n K G ℓ v hvG hℓ := by
  unfold pointIdeal
  rw [chartEval_smul n K G ℓ v a hvG hℓ hvGw hℓw]

/-- `finrank` of the point-localization depends only on the point ideal:
propositionally-equal maximal ideals give equal local lengths. The `subst`
leaves only maximality-instance arguments differing, which are definitionally
equal by proof irrelevance, so `rfl` closes the goal. (A direct `rw` on the
ideals fails: the `primeCompl` instances mention the ideal only in their
types, so the rewrite motive is not type-correct.)

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing` (the `CommRing` / `Algebra K`
  instances flowing to the localization).
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.primeCompl`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `Module.finrank`. -/
theorem finrank_loc_of_ideal_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (I₁ I₂ : Ideal (chartRing n K G ℓ)) [I₁.IsMaximal] [I₂.IsMaximal]
    (h : I₁ = I₂) :
    Module.finrank K (Localization I₁.primeCompl)
      = Module.finrank K (Localization I₂.primeCompl) := by
  subst h
  rfl

/-- Scale-invariance of the local multiplicity: the local length at `a • v`
equals the local length at `v` (the point ideals agree by `pointIdeal_smul`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.localMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.pointIdeal_smul`,
  `Appendix_FixedPoint.BezoutChain.finrank_loc_of_ideal_eq`. -/
theorem localMultiplicity_smul (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K) (a : K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hvGw : ∀ i, MvPolynomial.eval (a • v) (G i) = 0)
    (hℓw : MvPolynomial.eval (a • v) (mkLin n K ℓ) ≠ 0) :
    localMultiplicity n K G ℓ (a • v) hvGw hℓw
      = localMultiplicity n K G ℓ v hvG hℓ := by
  unfold localMultiplicity locRingAt
  exact finrank_loc_of_ideal_eq n K G ℓ _ _
    (pointIdeal_smul n K G ℓ v a hvG hℓ hvGw hℓw)

/-- The exact `hrep` shape (`SpuriousMultiplicityOne.lean` lines 399–405): in the
distinguished chart, the local multiplicity at `p.rep` equals the one at
`zRep`. The scaling `p.rep = a • zRep` is derived in-file from `mk_rep` /
`mk_eq_mk_iff'` (the scalar-needs-no-nonzero argument of
`chartLocEval_smul_mk`); the `∀`-generalization over the representative
makes the `subst` go through (a direct `rw` on `p.rep` fails since the
equation proofs mention it only in their types).

GRADE (`hrep` result): conditional-exact-`[hF]`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.localMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`,
  `Appendix_FixedPoint.BezoutChain.distinguishedPoint`, `Appendix_FixedPoint.BezoutChain.zRep`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.distEll`,
  `Appendix_FixedPoint.BezoutChain.hvGdist`,
  `Appendix_FixedPoint.BezoutChain.hℓdist`.
* This module, `Appendix_FixedPoint.BezoutChain.localMultiplicity_smul`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_rep`, `Projectivization.mk_eq_mk_iff'`. -/
theorem localMultiplicity_rep_eq_zRep (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hvGw : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓw : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K (distEll m K)) ≠ 0) :
    localMultiplicity m K (mkSystem m K F) (distEll m K)
        (distinguishedPoint m K).rep hvGw hℓw
      = localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) := by
  have hmk : Projectivization.mk K (distinguishedPoint m K).rep
        (distinguishedPoint m K).rep_nonzero
      = Projectivization.mk K (zRep m K) (zRep_ne_zero m K) :=
    Projectivization.mk_rep (distinguishedPoint m K)
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' K (distinguishedPoint m K).rep
      (zRep m K) _ _).mp hmk
  have hgen : ∀ (w : Fin (m + 2) → K)
      (hv : ∀ i, MvPolynomial.eval w ((mkSystem m K F) i) = 0)
      (hℓ : MvPolynomial.eval w (mkLin m K (distEll m K)) ≠ 0)
      (_ : w = a • zRep m K),
      localMultiplicity m K (mkSystem m K F) (distEll m K) w hv hℓ
        = localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
          (hvGdist m K F hF) (hℓdist m K) := by
    intro w hv hℓ e
    subst e
    exact localMultiplicity_smul m K (mkSystem m K F) (distEll m K)
      (zRep m K) a (hvGdist m K F hF) (hℓdist m K) hv hℓ
  exact hgen _ hvGw hℓw ha.symm

/-! ## Chart-independence step (the `hchart` reduction) -/

/-- Exact residual for `hchart` (the `Counting.mult_chart_independent` `hloceq`
content): the `K`-linear iso of the two chart-local rings at `v`. Both rings
are stalks of the same projective point, but they localize *different* base
rings, so the iso is a manual fraction-map construction through the
`Localization.mk'` API (see the module docstring); it is recorded here as an
explicit hypothesis with its consumption step proved below. -/
def ChartCompatIso (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) : Prop :=
  Nonempty (locRingAt n K G ℓ₁ v hvG₁ hℓ₁
    ≃ₗ[K] locRingAt n K G ℓ₂ v hvG₂ hℓ₂)

/-- Consumption step: a `K`-linear iso of the two chart-local rings makes the
local multiplicities agree (the `hloceq` equation at `v`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.localMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.locRingAt`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`,
  `LinearEquiv.finrank_eq`. -/
theorem localMultiplicity_chart_independent_of_iso (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (e : locRingAt n K G ℓ₁ v hvG₁ hℓ₁
      ≃ₗ[K] locRingAt n K G ℓ₂ v hvG₂ hℓ₂) :
    localMultiplicity n K G ℓ₁ v hvG₁ hℓ₁
      = localMultiplicity n K G ℓ₂ v hvG₂ hℓ₂ :=
  LinearEquiv.finrank_eq e

/-- The `hloceq` equation from the named residual.

## References

* This module, `Appendix_FixedPoint.BezoutChain.ChartCompatIso`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity_chart_independent_of_iso`. -/
theorem hloceq_of_chartCompatIso (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (hiso : ChartCompatIso n K G ℓ₁ ℓ₂ v hvG₁ hℓ₁ hvG₂ hℓ₂) :
    localMultiplicity n K G ℓ₁ v hvG₁ hℓ₁
      = localMultiplicity n K G ℓ₂ v hvG₂ hℓ₂ := by
  obtain ⟨e⟩ := hiso
  exact localMultiplicity_chart_independent_of_iso n K G ℓ₁ ℓ₂ v
    hvG₁ hℓ₁ hvG₂ hℓ₂ e

/-- The full `Counting.mult_chart_independent` `hloceq` binder shape from the
pointwise residual.

## References

* `Geometry.Counting`, `Appendix_FixedPoint.BezoutChain.mult_chart_independent` (`hloceq` shape).
* This module, `Appendix_FixedPoint.BezoutChain.ChartCompatIso`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity_chart_independent_of_iso`. -/
theorem hloceq_forall_of_iso (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K)
    (hiso : ∀ (v : Fin (n + 2) → K)
      (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
      (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0),
      ChartCompatIso n K G ℓ₁ ℓ₂ v hvG₁ hℓ₁ hvG₂ hℓ₂) :
    ∀ (v : Fin (n + 2) → K)
      (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
      (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0),
      localMultiplicity n K G ℓ₁ v hvG₁ hℓ₁
        = localMultiplicity n K G ℓ₂ v hvG₂ hℓ₂ := by
  intro v hvG₁ hℓ₁ hvG₂ hℓ₂
  obtain ⟨e⟩ := hiso v hvG₁ hℓ₁ hvG₂ hℓ₂
  exact localMultiplicity_chart_independent_of_iso n K G ℓ₁ ℓ₂ v
    hvG₁ hℓ₁ hvG₂ hℓ₂ e

/-- The exact `hchart` shape (`SpuriousMultiplicityOne.lean` lines 388–398): changing
the chart `ℓ ↦ distEll` at `p.rep`, from the named residual.

GRADE (`hchart` result): conditional-exact-`[ChartCompatIso]`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.localMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`,
  `Appendix_FixedPoint.BezoutChain.distinguishedPoint`, `Appendix_FixedPoint.BezoutChain.mkLin`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.distEll`.
* This module, `Appendix_FixedPoint.BezoutChain.ChartCompatIso`,
  `Appendix_FixedPoint.BezoutChain.hloceq_of_chartCompatIso`. -/
theorem hchart_distEll_of_iso (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (ℓ : Fin (m + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓ₁ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K ℓ) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓ₂ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K (distEll m K)) ≠ 0)
    (hiso : ChartCompatIso m K (mkSystem m K F) ℓ (distEll m K)
      (distinguishedPoint m K).rep hvG₁ hℓ₁ hvG₂ hℓ₂) :
    localMultiplicity m K (mkSystem m K F) ℓ (distinguishedPoint m K).rep
        hvG₁ hℓ₁
      = localMultiplicity m K (mkSystem m K F) (distEll m K)
        (distinguishedPoint m K).rep hvG₂ hℓ₂ :=
  hloceq_of_chartCompatIso m K (mkSystem m K F) ℓ (distEll m K) _ hvG₁ hℓ₁
    hvG₂ hℓ₂ hiso

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Chart-iso construction: transport helpers

Balanced presentations `s/ℓ^d` (a cone numerator plus a homogeneous degree-`d`
lift) are re-based from chart `ℓ₁` to chart `ℓ₂`: `chartIso_liftToChart`
re-presents a cone fraction in the target chart, `chartIso_chartDenom` is the
cross-chart denominator `ℓ₁^d/ℓ₂^d`, and `chartIso_gAux` is the auxiliary
fraction map `s/ℓ₁^d ↦ (s/ℓ₂^d)/(ℓ₁^d/ℓ₂^d)` on presentation data, with its
well-definedness (`chartIso_gAux_wellDefined`) and the chosen-presentation
machinery (`chartIso_chosen*`, `chartIso_g`) promoting it to chart elements. -/

/-- Re-base a balanced cone fraction in any chart: from a cone numerator `s`
with a homogeneous degree-`d` lift `p`, build the chart element `s/ℓ^d`.
The balanced presentation is carried verbatim, so the value equation is
`rfl` (see `chartIso_lift_val`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`,
  `Appendix_FixedPoint.BezoutChain.coneQuotient`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
noncomputable def chartIso_liftToChart (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (s : coneQuotient n K G) (p : MvPolynomial (Fin (n + 2)) K)
    (hphom : p.IsHomogeneous d)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range G)) p = s) :
    chartRing n K G ℓ :=
  ⟨Localization.mk s ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
      (mkLin n K ℓ)) ^ d,
      (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩,
    d, s, ⟨p, hphom, hpeq⟩, rfl⟩

/-- Powers of the chart linear form are homogeneous of the matching degree:
`(mkLin ℓ ^ d).IsHomogeneous d`, from the degree-`1` fact by `.pow` (with
`1 * d = d` normalized).

## References

* This module, `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous_compat`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.pow`. -/
theorem chartIso_mkLin_pow_hom (n : ℕ) (K : Type*) [Field K]
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    ((mkLin n K ℓ) ^ d).IsHomogeneous d := by
  have h1 : (mkLin n K ℓ).IsHomogeneous 1 :=
    mkLin_isHomogeneous_compat n K ℓ
  have h2 := h1.pow d
  rwa [one_mul] at h2

/-- The cross-chart denominator `ℓ₁^d/ℓ₂^d` as a chart-`ℓ₂` element: the
`chartIso_liftToChart` lift of the cone element `ℓ̄₁^d` with the homogeneous
lift `(mkLin ℓ₁)^d` (whose quotient image is `ℓ̄₁^d` by `map_pow`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_mkLin_pow_hom`.
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_pow`. -/
noncomputable def chartIso_chartDenom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (d : ℕ) :
    chartRing n K G ℓ₂ :=
  chartIso_liftToChart n K G ℓ₂ d
    ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^ d)
    ((mkLin n K ℓ₁) ^ d)
    (chartIso_mkLin_pow_hom n K ℓ₁ d)
    (by rw [map_pow])

/-- The cross-chart denominator evaluates nonzero at `v` when both charts
do: unfolding `chartEval`/`chartLocEval` and applying the
`IsLocalization.lift` spec equation, a zero value would force
`(eval v (mkLin ℓ₁))^d = 0`, contradicting `hℓ₁` via `pow_ne_zero`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartLocEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_pow`. -/
theorem chartIso_chartDenom_eval_ne_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (d : ℕ) :
    chartEval n K G ℓ₂ v hvG hℓ₂
      (chartIso_chartDenom n K G ℓ₁ ℓ₂ d) ≠ 0 := by
  unfold chartIso_chartDenom chartIso_liftToChart chartEval
  rw [RingHom.comp_apply]
  change chartLocEval n K G ℓ₂ v hvG hℓ₂
      (Localization.mk ((Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ₁)) ^ d) _) ≠ 0
  intro h0
  unfold chartLocEval at h0
  rw [Localization.mk_eq_mk'_apply] at h0
  have heq :
      coneEval n K G v hvG
        ((Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₁)) ^ d)
      = coneEval n K G v hvG
        ((Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₂)) ^ d) * 0 :=
    (IsLocalization.lift_mk'_spec _ _ _ _).mp h0
  rw [mul_zero] at heq
  have hnum :
      coneEval n K G v hvG
        ((Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₁)) ^ d)
      = (MvPolynomial.eval v (mkLin n K ℓ₁)) ^ d := by
    rw [map_pow]
    congr 1
  rw [hnum] at heq
  exact pow_ne_zero d hℓ₁ heq

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The cross-chart denominator lies in the target prime complement at `v`:
membership in `primeCompl` unfolds to nonvanishing of `chartEval`
(`mem_primeCompl_iff` + `RingHom.mem_ker`), which is
`chartIso_chartDenom_eval_ne_zero`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.pointIdeal`,
  `Appendix_FixedPoint.BezoutChain.chartEval`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom_eval_ne_zero`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.mem_primeCompl_iff`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `RingHom.mem_ker`. -/
theorem chartIso_denom_mem_primeCompl (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (d : ℕ) :
    chartIso_chartDenom n K G ℓ₁ ℓ₂ d ∈
      (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl := by
  rw [Ideal.mem_primeCompl_iff]
  unfold pointIdeal
  intro hmem
  rw [RingHom.mem_ker] at hmem
  exact chartIso_chartDenom_eval_ne_zero n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁ d
    hmem

/-- The auxiliary fraction map on presentation data: `s/ℓ₁^d ↦ (s/ℓ₂^d)/(ℓ₁^d/ℓ₂^d)`.
The numerator is the `chartIso_liftToChart` re-basing of the balanced
presentation `(s, p)` in the target chart, and the denominator is the
cross-chart `chartIso_chartDenom` (legitimate in the stalk by
`chartIso_denom_mem_primeCompl`). Well-definedness across presentations is
`chartIso_gAux_wellDefined`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_denom_mem_primeCompl`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk`. -/
noncomputable def chartIso_gAux (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (d : ℕ) (s : coneQuotient n K G)
    (p : MvPolynomial (Fin (n + 2)) K)
    (hphom : p.IsHomogeneous d)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range G)) p = s) :
    locRingAt n K G ℓ₂ v hvG hℓ₂ :=
  Localization.mk (chartIso_liftToChart n K G ℓ₂ d s p hphom hpeq)
    ⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ d,
      chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁ d⟩

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Well-definedness of the auxiliary fraction map across presentations:
equal `ℓ₁`-fractions map to equal stalk fractions. The source equality
unfolds (via `IsLocalization.eq`) to a witness `c = ℓ₁^k` with a cone
identity; multiplying through by the cross-chart denominator at `k`
(`IsLocalization.eq_iff_exists`) reduces the target equality to that cone
identity plus a `ring` rearrangement of the `ℓ₂`-powers.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.eq`,
  `IsLocalization.eq_iff_exists`, `IsLocalization.mk'_eq_iff_eq`;
  `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_mul`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
theorem chartIso_gAux_wellDefined (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (d₁ d₂ : ℕ) (s₁ s₂ : coneQuotient n K G)
    (p₁ p₂ : MvPolynomial (Fin (n + 2)) K)
    (hphom₁ : p₁.IsHomogeneous d₁)
    (hpeq₁ : Ideal.Quotient.mk (Ideal.span (Set.range G)) p₁ = s₁)
    (hphom₂ : p₂.IsHomogeneous d₂)
    (hpeq₂ : Ideal.Quotient.mk (Ideal.span (Set.range G)) p₂ = s₂)
    (heq : Localization.mk s₁
        (⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₁)) ^ d₁,
          (Submonoid.mem_powers_iff _ _).mpr ⟨d₁, rfl⟩⟩ :
          Submonoid.powers (Ideal.Quotient.mk
            (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
            coneQuotient n K G))
      = Localization.mk s₂
        (⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₁)) ^ d₂,
          (Submonoid.mem_powers_iff _ _).mpr ⟨d₂, rfl⟩⟩ :
          Submonoid.powers (Ideal.Quotient.mk
            (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
            coneQuotient n K G))) :
    chartIso_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ d₁ s₁ p₁ hphom₁ hpeq₁
      = chartIso_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ d₂ s₂ p₂
        hphom₂ hpeq₂ := by
  rw [Localization.mk_eq_mk'_apply,
    Localization.mk_eq_mk'_apply] at heq
  obtain ⟨c, hc⟩ := (IsLocalization.eq).mp heq
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
  rw [← hk] at hc
  dsimp at hc
  unfold chartIso_gAux
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply]
  rw [IsLocalization.mk'_eq_iff_eq]
  apply (IsLocalization.eq_iff_exists
    (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl _).mpr
  refine ⟨⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ k,
    chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁
      k⟩, ?_⟩
  apply Subtype.ext
  simp only [Subalgebra.coe_mul]
  unfold chartIso_chartDenom chartIso_liftToChart
  dsimp
  rw [Localization.mk_mul, Localization.mk_mul,
    Localization.mk_mul, Localization.mk_mul]
  rw [hc]
  congr 1
  apply Subtype.ext
  dsimp
  ring

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The chosen degree of a chart element's balanced presentation
(`Classical.choose` on the `chartRing` membership data).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`. -/
noncomputable def chartIso_chosenD (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c : chartRing n K G ℓ₁) : ℕ :=
  Classical.choose c.2

/-- The chosen cone numerator of a chart element's balanced presentation
(`Classical.choose` on the `chartRing` membership data).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`,
  `Appendix_FixedPoint.BezoutChain.coneQuotient`. -/
noncomputable def chartIso_chosenS (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c : chartRing n K G ℓ₁) :
    coneQuotient n K G :=
  Classical.choose (Classical.choose_spec c.2)

/-- The chosen homogeneous lift of a chart element's balanced presentation
(`Classical.choose` on the `chartRing` membership data).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`. -/
noncomputable def chartIso_chosenP (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c : chartRing n K G ℓ₁) :
    MvPolynomial (Fin (n + 2)) K :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec c.2)).1

/-- The chosen lift is homogeneous of the chosen degree (projection of the
`Classical.choose_spec` data for `chartIso_chosenD`/`chartIso_chosenP`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`. -/
theorem chartIso_chosenHom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c : chartRing n K G ℓ₁) :
    (chartIso_chosenP n K G ℓ₁ c).IsHomogeneous
      (chartIso_chosenD n K G ℓ₁ c) := by
  have h1 := Classical.choose_spec c.2
  have h2 := Classical.choose_spec h1
  have hp := h2.1
  have h3 := Classical.choose_spec hp
  unfold chartIso_chosenD chartIso_chosenP
  exact h3.1

/-- The chosen lift lies over the chosen numerator (`mk p = s`; projection
of the `Classical.choose_spec` data for `chartIso_chosenS` /
`chartIso_chosenP`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`. -/
theorem chartIso_chosenEq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c : chartRing n K G ℓ₁) :
    Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartIso_chosenP n K G ℓ₁ c)
      = chartIso_chosenS n K G ℓ₁ c := by
  have h1 := Classical.choose_spec c.2
  have h2 := Classical.choose_spec h1
  have hp := h2.1
  have h3 := Classical.choose_spec hp
  unfold chartIso_chosenS chartIso_chosenP
  exact h3.2

/-- The chosen presentation equation: a chart element's value is the
fraction `s/ℓ^d` of its chosen data (projection of the
`Classical.choose_spec` data; the bridge from chart elements back to
fractions, consumed by `chartIso_g_eq_gAux` and the `add`/`mul`
presentation lemmas).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
theorem chartIso_chosenE (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c : chartRing n K G ℓ₁) :
    (c : Localization (Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
        coneQuotient n K G)))
      = Localization.mk (chartIso_chosenS n K G ℓ₁ c)
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c),
          (Submonoid.mem_powers_iff _ _).mpr
            ⟨chartIso_chosenD n K G ℓ₁ c, rfl⟩⟩ := by
  have h1 := Classical.choose_spec c.2
  have h2 := Classical.choose_spec h1
  unfold chartIso_chosenD chartIso_chosenS
  exact h2.2

/-- The chart transport map via chosen presentations: apply `chartIso_gAux`
to the `chartIso_chosen*` data of a chart-`ℓ₁` element, landing in the
stalk at `v` in chart `ℓ₂`. Independence of the chosen presentation is
`chartIso_g_eq_gAux` (via `chartIso_gAux_wellDefined`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`,
  `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenEq`. -/
noncomputable def chartIso_g (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (c : chartRing n K G ℓ₁) : locRingAt n K G ℓ₂ v hvG hℓ₂ :=
  chartIso_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
    (chartIso_chosenD n K G ℓ₁ c)
    (chartIso_chosenS n K G ℓ₁ c)
    (chartIso_chosenP n K G ℓ₁ c)
    (chartIso_chosenHom n K G ℓ₁ c)
    (chartIso_chosenEq n K G ℓ₁ c)

/-- The transport map agrees with `chartIso_gAux` on any presentation: the
given presentation equation `e` and the chosen one (`chartIso_chosenE`)
exhibit the same fraction, so `chartIso_gAux_wellDefined` applies. This is
the workhorse for the `map_zero`/`map_one`/`map_add`/`map_mul` proofs, each
of which supplies the canonical presentation.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_g`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gAux_wellDefined`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenE`. -/
theorem chartIso_g_eq_gAux (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (c : chartRing n K G ℓ₁)
    (d : ℕ) (s : coneQuotient n K G)
    (p : MvPolynomial (Fin (n + 2)) K)
    (hphom : p.IsHomogeneous d)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range G)) p = s)
    (e : (c : Localization (Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
          coneQuotient n K G)))
        = Localization.mk s ⟨(Ideal.Quotient.mk
          (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^ d,
          (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩) :
    chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ c
      = chartIso_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ d s p
        hphom hpeq := by
  unfold chartIso_g
  apply chartIso_gAux_wellDefined
  exact (chartIso_chosenE n K G ℓ₁ c).symm.trans e

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The transport map preserves zero: `0` presents as `C 0/ℓ^0`
(`MvPolynomial.C_0`, `IsLocalization.mk'_zero`), and its transport is
`0/(ℓ₁^0/ℓ₂^0) = 0` by the same `mk'_zero` collapse at both levels.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_g`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_eq_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gAux`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.mk'_zero`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`. -/
theorem chartIso_g_map_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ 0 = 0 := by
  have e0 : ((0 : chartRing n K G ℓ₁) :
      Localization (Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
          coneQuotient n K G)))
      = Localization.mk
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (MvPolynomial.C (0 : K)))
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₁)) ^ 0,
          (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩ := by
    change (0 : Localization (Submonoid.powers _)) = _
    have hcone : Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.C (0 : K)) = 0 := by
      rw [MvPolynomial.C_0, map_zero]
    rw [hcone]
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_zero]
  rw [chartIso_g_eq_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ 0 0 _ _
    (MvPolynomial.isHomogeneous_C _ _) rfl e0]
  have hnum0 : chartIso_liftToChart n K G ℓ₂ 0
      (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.C (0 : K)))
      (MvPolynomial.C (0 : K))
      (MvPolynomial.isHomogeneous_C _ _) rfl = 0 := by
    apply Subtype.ext
    change Localization.mk _ _ = (0 : chartRing n K G ℓ₂).val
    have hcone : Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.C (0 : K)) = 0 := by
      rw [MvPolynomial.C_0, map_zero]
    rw [hcone]
    change Localization.mk (0 : coneQuotient n K G) _ = 0
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_zero]
  unfold chartIso_gAux
  rw [hnum0]
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_zero]

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The transport map preserves one: `1` presents as `C 1/ℓ^0`
(`MvPolynomial.C_1`, `Localization.mk_one` with the degree-`0` denominator
identified with `1`), the lifted numerator is `1`, the cross-chart
denominator at degree `0` is `1`, and the stalk fraction `1/1` is `1`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_g`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_eq_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gAux`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk_one`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`. -/
theorem chartIso_g_map_one (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ 1 = 1 := by
  have e1 : ((1 : chartRing n K G ℓ₁) :
      Localization (Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
          coneQuotient n K G)))
      = Localization.mk
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (MvPolynomial.C (1 : K)))
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₁)) ^ 0,
          (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩ := by
    change (1 : Localization (Submonoid.powers _)) = _
    have hcone : Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.C (1 : K)) = 1 := by
      rw [MvPolynomial.C_1, map_one]
    rw [hcone]
    have h1mem : (1 : coneQuotient n K G) ∈ Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₁)) :=
      (Submonoid.mem_powers_iff _ _).mpr ⟨0, by rw [pow_zero]⟩
    have hden : (⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ₁)) ^ 0,
        (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩ :
        Submonoid.powers _) = ⟨1, h1mem⟩ := by
      apply Subtype.ext
      change _ ^ (0 : ℕ) = 1
      rw [pow_zero]
    rw [hden]
    have h11 : (⟨1, h1mem⟩ :
        Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
          coneQuotient n K G)) = 1 := by
      apply Subtype.ext
      rfl
    rw [h11, Localization.mk_one]
  rw [chartIso_g_eq_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ 1 0 _ _
    (MvPolynomial.isHomogeneous_C _ _) rfl e1]
  have hnum1 : chartIso_liftToChart n K G ℓ₂ 0
      (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.C (1 : K)))
      (MvPolynomial.C (1 : K))
      (MvPolynomial.isHomogeneous_C _ _) rfl = 1 := by
    apply Subtype.ext
    change Localization.mk _ _ = (1 : chartRing n K G ℓ₂).val
    have hcone : Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.C (1 : K)) = 1 := by
      rw [MvPolynomial.C_1, map_one]
    rw [hcone]
    change Localization.mk (1 : coneQuotient n K G) _ = 1
    have h1mem : (1 : coneQuotient n K G) ∈ Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₂)) :=
      (Submonoid.mem_powers_iff _ _).mpr ⟨0, by rw [pow_zero]⟩
    have hden : (⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ₂)) ^ 0,
        (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩ :
        Submonoid.powers _) = ⟨1, h1mem⟩ := by
      apply Subtype.ext
      change _ ^ (0 : ℕ) = 1
      rw [pow_zero]
    rw [hden]
    have h11 : (⟨1, h1mem⟩ :
        Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range G)) (mkLin n K ℓ₂) :
          coneQuotient n K G)) = 1 := by
      apply Subtype.ext
      rfl
    rw [h11, Localization.mk_one]
  have hden1 : chartIso_chartDenom n K G ℓ₁ ℓ₂ 0 = 1 := by
    apply Subtype.ext
    unfold chartIso_chartDenom chartIso_liftToChart
    dsimp
    change Localization.mk _ _ = (1 : chartRing n K G ℓ₂).val
    have hpow1 : ((Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ₁)) ^ (0 : ℕ)) = 1 := pow_zero _
    rw [hpow1]
    change Localization.mk (1 : coneQuotient n K G) _ = 1
    have h1mem : (1 : coneQuotient n K G) ∈ Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ₂)) :=
      (Submonoid.mem_powers_iff _ _).mpr ⟨0, by rw [pow_zero]⟩
    have hden : (⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ₂)) ^ 0,
        (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩ :
        Submonoid.powers _) = ⟨1, h1mem⟩ := by
      apply Subtype.ext
      change _ ^ (0 : ℕ) = 1
      rw [pow_zero]
    rw [hden]
    have h11 : (⟨1, h1mem⟩ :
        Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range G)) (mkLin n K ℓ₂) :
          coneQuotient n K G)) = 1 := by
      apply Subtype.ext
      rfl
    rw [h11, Localization.mk_one]
  unfold chartIso_gAux
  rw [hnum1]
  have hy1 : (⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ 0,
      chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁
        0⟩ : (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl)
      = 1 := by
    apply Subtype.ext
    change chartIso_chartDenom n K G ℓ₁ ℓ₂ 0 = 1
    exact hden1
  rw [hy1, Localization.mk_one]

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Chart-iso construction: additivity of the transport map

The `chartRing` addition law (`add_mem'`: cross-multiplied sum numerator) is
mirrored on chosen presentations (`chartIso_addHom`, `chartIso_addHpeq`,
`chartIso_add_presentation`), and `chartIso_g_map_add` carries the sum
presentation across the transport map, descending the resulting fraction
identity to a `ring` identity in the cone. -/

/-- Computation rule for the lift: the value of a `chartIso_liftToChart`
element is its presented fraction `s/ℓ^d` (`rfl`, by definition).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk`. -/
theorem chartIso_lift_val (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (s : coneQuotient n K G) (p : MvPolynomial (Fin (n + 2)) K)
    (hphom : p.IsHomogeneous d)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range G)) p = s) :
    ((chartIso_liftToChart n K G ℓ d s p hphom hpeq : chartRing n K G ℓ) :
      Localization (Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :
          coneQuotient n K G)))
      = Localization.mk s ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ)) ^ d,
        (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩ := rfl

/-- Homogeneity of the cross-multiplied sum numerator (mirrors `chartRing`
`add_mem'`): `ℓ^d₁·p₂ + ℓ^d₂·p₁` is homogeneous of degree `d₁ + d₂`, since
each summand is (`(hlin.pow _).mul` with the degree equation closed by
`omega`), and homogeneous sums stay homogeneous (`.add`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenHom`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.sum`, `MvPolynomial.IsHomogeneous.mul`,
  `MvPolynomial.IsHomogeneous.add`, `MvPolynomial.IsHomogeneous.pow`,
  `MvPolynomial.isHomogeneous_C_mul_X`. -/
theorem chartIso_addHom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c₁ c₂ : chartRing n K G ℓ₁) :
    ((mkLin n K ℓ₁) ^ (chartIso_chosenD n K G ℓ₁ c₁) *
        (chartIso_chosenP n K G ℓ₁ c₂) +
      (mkLin n K ℓ₁) ^ (chartIso_chosenD n K G ℓ₁ c₂) *
        (chartIso_chosenP n K G ℓ₁ c₁)).IsHomogeneous
      (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂) := by
  have hlin : (mkLin n K ℓ₁).IsHomogeneous 1 := by
    unfold mkLin
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _
  have e1 : 1 * (chartIso_chosenD n K G ℓ₁ c₁) + (chartIso_chosenD n K G ℓ₁ c₂)
      = (chartIso_chosenD n K G ℓ₁ c₁) + (chartIso_chosenD n K G ℓ₁ c₂) := by
    omega
  have e2 : 1 * (chartIso_chosenD n K G ℓ₁ c₂) + (chartIso_chosenD n K G ℓ₁ c₁)
      = (chartIso_chosenD n K G ℓ₁ c₁) + (chartIso_chosenD n K G ℓ₁ c₂) := by
    omega
  have h1 : ((mkLin n K ℓ₁) ^ (chartIso_chosenD n K G ℓ₁ c₁) *
      (chartIso_chosenP n K G ℓ₁ c₂)).IsHomogeneous
      ((chartIso_chosenD n K G ℓ₁ c₁) + (chartIso_chosenD n K G ℓ₁ c₂)) := by
    rw [← e1]
    exact (hlin.pow _).mul (chartIso_chosenHom n K G ℓ₁ c₂)
  have h2 : ((mkLin n K ℓ₁) ^ (chartIso_chosenD n K G ℓ₁ c₂) *
      (chartIso_chosenP n K G ℓ₁ c₁)).IsHomogeneous
      ((chartIso_chosenD n K G ℓ₁ c₁) + (chartIso_chosenD n K G ℓ₁ c₂)) := by
    rw [← e2]
    exact (hlin.pow _).mul (chartIso_chosenHom n K G ℓ₁ c₁)
  exact h1.add h2

/-- The sum numerator lies over the cross-multiplied cone sum (mirrors
`chartRing` `add_mem'`): pushing `ℓ^d₁·p₂ + ℓ^d₂·p₁` through the quotient
`mk` distributes (`map_add`/`map_mul`/`map_pow`) to
`ℓ̄^d₁·s₂ + ℓ̄^d₂·s₁` via the chosen lift equations (`chartIso_chosenEq`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenEq`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`.
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_add`, `map_mul`, `map_pow`. -/
theorem chartIso_addHpeq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c₁ c₂ : chartRing n K G ℓ₁) :
    Ideal.Quotient.mk (Ideal.span (Set.range G))
        ((mkLin n K ℓ₁) ^ (chartIso_chosenD n K G ℓ₁ c₁) *
          (chartIso_chosenP n K G ℓ₁ c₂) +
        (mkLin n K ℓ₁) ^ (chartIso_chosenD n K G ℓ₁ c₂) *
          (chartIso_chosenP n K G ℓ₁ c₁))
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₁) *
          (chartIso_chosenS n K G ℓ₁ c₂) +
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₂) *
          (chartIso_chosenS n K G ℓ₁ c₁) := by
  rw [map_add, map_mul, map_mul, map_pow, map_pow,
    chartIso_chosenEq n K G ℓ₁ c₁, chartIso_chosenEq n K G ℓ₁ c₂]

/-- Presentation of a sum of chart elements (mirrors `chartRing`
`add_mem'`): `(c₁ + c₂).val` is the cross-multiplied fraction over
`ℓ^(d₁+d₂)`, from the two chosen presentations (`chartIso_chosenE`) via
`Localization.add_mk`, with the denominator powers merged by `pow_add`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenE`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean` (`Submonoid.powers`
  membership), via `Submonoid.mem_powers_iff`. -/
theorem chartIso_add_presentation (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c₁ c₂ : chartRing n K G ℓ₁) :
    ((c₁ + c₂ : chartRing n K G ℓ₁) : Localization (Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
        coneQuotient n K G)))
      = Localization.mk
        ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₁) *
          (chartIso_chosenS n K G ℓ₁ c₂) +
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₂) *
          (chartIso_chosenS n K G ℓ₁ c₁))
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂),
          (Submonoid.mem_powers_iff _ _).mpr
            ⟨chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂,
              rfl⟩⟩ := by
  have e₁ := chartIso_chosenE n K G ℓ₁ c₁
  have e₂ := chartIso_chosenE n K G ℓ₁ c₂
  have hpow : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₁) *
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₂) =
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂) :=
    (pow_add _ _ _).symm
  rw [Subalgebra.coe_add, e₁, e₂, Localization.add_mk]
  congr 1
  exact Subtype.ext hpow

set_option maxHeartbeats 1000000 in
-- `rw [Localization.mk_mul]`/`add_mk` matching over fraction goals carrying
-- nested `chartIso_chosen*` data exceeds the default 200k heartbeats
-- (expensive `isDefEq` per `*`-node); wall-time stays ~1s.
/-- The transport map preserves addition: the sum presentation
(`chartIso_add_presentation` + `Localization.add_mk`) is carried across by
`chartIso_g_eq_gAux`, and the resulting fraction identity in `locRingAt` is
discharged by two `IsLocalization.mk'_eq_iff_eq` steps down to a `ring`
identity in the cone (after one `pow_add` rewrite of the `ℓ₁`-power).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_g`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_eq_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_addHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_addHpeq`,
  `Appendix_FixedPoint.BezoutChain.chartIso_add_presentation`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.mk'_eq_iff_eq`;
  `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_mul`. -/
theorem chartIso_g_map_add (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (c₁ c₂ : chartRing n K G ℓ₁) :
    chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ (c₁ + c₂)
      = chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ c₁
        + chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ c₂ := by
  have e₁₂ := chartIso_add_presentation n K G ℓ₁ c₁ c₂
  rw [chartIso_g_eq_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ (c₁ + c₂)
    _ _ _ (chartIso_addHom n K G ℓ₁ c₁ c₂)
    (chartIso_addHpeq n K G ℓ₁ c₁ c₂) e₁₂]
  unfold chartIso_g chartIso_gAux
  rw [Localization.add_mk, Localization.mk_eq_mk'_apply,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq]
  congr 1
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Submonoid.coe_mul]
  unfold chartIso_chartDenom chartIso_liftToChart
  dsimp only
  rw [Localization.mk_mul, Localization.mk_mul, Localization.mk_mul,
    Localization.mk_mul, Localization.add_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply,
    IsLocalization.mk'_eq_iff_eq]
  congr 1
  simp only [Submonoid.coe_mul]
  have hK : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂)
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₁) *
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₂) :=
    pow_add _ _ _
  rw [hK]
  ring

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Chart-iso construction: multiplicativity and the bundled hom

The `chartRing` multiplication law (`mul_mem'`) is mirrored on chosen
presentations (`chartIso_mulHom`, `chartIso_mulHpeq`,
`chartIso_mul_presentation`), `chartIso_g_map_mul` carries products across,
and `chartIso_gHom` bundles the transport map as a ring hom into the target
stalk. -/

/-- Homogeneity of the product numerator (mirrors `chartRing` `mul_mem'`):
`p₁·p₂` is homogeneous of degree `d₁ + d₂` by `.mul` of the chosen
homogeneity proofs.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenHom`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.mul`. -/
theorem chartIso_mulHom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c₁ c₂ : chartRing n K G ℓ₁) :
    ((chartIso_chosenP n K G ℓ₁ c₁) *
      (chartIso_chosenP n K G ℓ₁ c₂)).IsHomogeneous
      (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂) :=
  (chartIso_chosenHom n K G ℓ₁ c₁).mul (chartIso_chosenHom n K G ℓ₁ c₂)

/-- The product numerator lies over the product of cone numerators
(mirrors `chartRing` `mul_mem'`): `mk (p₁·p₂) = s₁·s₂` by `map_mul` plus
the two chosen lift equations (`chartIso_chosenEq`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenEq`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`.
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_mul`. -/
theorem chartIso_mulHpeq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c₁ c₂ : chartRing n K G ℓ₁) :
    Ideal.Quotient.mk (Ideal.span (Set.range G))
        ((chartIso_chosenP n K G ℓ₁ c₁) * (chartIso_chosenP n K G ℓ₁ c₂))
      = (chartIso_chosenS n K G ℓ₁ c₁) * (chartIso_chosenS n K G ℓ₁ c₂) := by
  rw [map_mul, chartIso_chosenEq n K G ℓ₁ c₁, chartIso_chosenEq n K G ℓ₁ c₂]

/-- Presentation of a product of chart elements (mirrors `chartRing`
`mul_mem'`): `(c₁·c₂).val` is the fraction `(s₁·s₂)/ℓ^(d₁+d₂)`, from the
two chosen presentations (`chartIso_chosenE`) via `Localization.mk_mul`,
with the denominator powers merged by `pow_add`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenE`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk_mul`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean` (`Submonoid.powers`
  membership), via `Submonoid.mem_powers_iff`. -/
theorem chartIso_mul_presentation (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (c₁ c₂ : chartRing n K G ℓ₁) :
    ((c₁ * c₂ : chartRing n K G ℓ₁) : Localization (Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
        coneQuotient n K G)))
      = Localization.mk
        ((chartIso_chosenS n K G ℓ₁ c₁) * (chartIso_chosenS n K G ℓ₁ c₂))
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂),
          (Submonoid.mem_powers_iff _ _).mpr
            ⟨chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂,
              rfl⟩⟩ := by
  have e₁ := chartIso_chosenE n K G ℓ₁ c₁
  have e₂ := chartIso_chosenE n K G ℓ₁ c₂
  have hpow : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₁) *
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₂) =
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂) :=
    (pow_add _ _ _).symm
  rw [Subalgebra.coe_mul, e₁, e₂, Localization.mk_mul]
  congr 1
  exact Subtype.ext hpow

set_option maxHeartbeats 1000000 in
-- `rw [Localization.mk_mul]` matching over fraction goals carrying nested
-- `chartIso_chosen*` data exceeds the default 200k heartbeats (expensive
-- `isDefEq` per `*`-node); wall-time stays ~1s.
/-- The transport map preserves multiplication (same two-step
`IsLocalization.mk'_eq_iff_eq` descent as `chartIso_g_map_add`): the
product presentation (`chartIso_mul_presentation`) is carried across by
`chartIso_g_eq_gAux`, and the stalk fraction identity descends to a `ring`
identity in the cone (after one `pow_add` rewrite of the `ℓ₁`-power).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_g`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_eq_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_mulHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_mulHpeq`,
  `Appendix_FixedPoint.BezoutChain.chartIso_mul_presentation`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_mul`; `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.mk'_eq_iff_eq`. -/
theorem chartIso_g_map_mul (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (c₁ c₂ : chartRing n K G ℓ₁) :
    chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ (c₁ * c₂)
      = chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ c₁
        * chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ c₂ := by
  have e₁₂ := chartIso_mul_presentation n K G ℓ₁ c₁ c₂
  rw [chartIso_g_eq_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ (c₁ * c₂)
    _ _ _ (chartIso_mulHom n K G ℓ₁ c₁ c₂)
    (chartIso_mulHpeq n K G ℓ₁ c₁ c₂) e₁₂]
  unfold chartIso_g chartIso_gAux
  rw [Localization.mk_mul, Localization.mk_eq_mk'_apply,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq]
  congr 1
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Submonoid.coe_mul]
  unfold chartIso_chartDenom chartIso_liftToChart
  dsimp only
  rw [Localization.mk_mul, Localization.mk_mul, Localization.mk_mul,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply,
    IsLocalization.mk'_eq_iff_eq]
  congr 1
  simp only [Submonoid.coe_mul]
  have hK : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
        (chartIso_chosenD n K G ℓ₁ c₁ + chartIso_chosenD n K G ℓ₁ c₂)
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₁) *
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^
          (chartIso_chosenD n K G ℓ₁ c₂) :=
    pow_add _ _ _
  rw [hK]
  ring

/-- The bundled chart-transport ring hom: `chartIso_g` with the four
preservation laws (`chartIso_g_map_one`, `chartIso_g_map_mul`,
`chartIso_g_map_zero`, `chartIso_g_map_add`), as a ring hom from
chart-`ℓ₁` elements to the stalk at `v` in chart `ℓ₂`. Promoted to the
stalk-to-stalk maps `chartIso_F`/`chartIso_G` via `IsLocalization.lift`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`,
  `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_g`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_map_zero`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_map_one`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_map_add`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_map_mul`. -/
noncomputable def chartIso_gHom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    chartRing n K G ℓ₁ →+* locRingAt n K G ℓ₂ v hvG hℓ₂ where
  toFun := chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
  map_one' := chartIso_g_map_one n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
  map_mul' := chartIso_g_map_mul n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
  map_zero' := chartIso_g_map_zero n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
  map_add' := chartIso_g_map_add n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Chart-iso construction: the prime complement maps to units

The hypothesis needed to lift `chartIso_gHom` through `IsLocalization.lift`:
a prime-complement element has nonzero cone numerator
(`chartIso_coneEval_ne_zero_of_mem_primeCompl`), so its lift lies in the
target prime complement (`chartIso_lift_mem_primeCompl`), and a fraction with
prime-complement numerator is a unit
(`chartIso_mk_unit_of_mem_primeCompl`), giving
`chartIso_primeCompl_to_units`. -/

/-- The numerator of a prime-complement element evaluates nonzero at `v`:
`chartEval` is nonzero on it (by `mem_primeCompl_iff`), and the
`IsLocalization.lift` spec equation transfers that to `coneEval` (a zero
cone numerator would force `chartEval = coneEval · * V = 0`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartLocEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval`, `Appendix_FixedPoint.BezoutChain.pointIdeal`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chosenE`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.mem_primeCompl_iff`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `RingHom.mem_ker`. -/
theorem chartIso_coneEval_ne_zero_of_mem_primeCompl (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (y : (pointIdeal n K G ℓ₁ v hvG hℓ₁).primeCompl) :
    coneEval n K G v hvG
        (chartIso_chosenS n K G ℓ₁ (y : chartRing n K G ℓ₁)) ≠ 0 := by
  have hy : chartEval n K G ℓ₁ v hvG hℓ₁ (y : chartRing n K G ℓ₁) ≠ 0 := by
    intro h0
    have hmem := Ideal.mem_primeCompl_iff.mp y.2
    unfold pointIdeal at hmem
    exact hmem (RingHom.mem_ker.mpr h0)
  have e := chartIso_chosenE n K G ℓ₁ (y : chartRing n K G ℓ₁)
  have h1 : chartEval n K G ℓ₁ v hvG hℓ₁ (y : chartRing n K G ℓ₁)
      = chartLocEval n K G ℓ₁ v hvG hℓ₁ ((y : chartRing n K G ℓ₁).val) := rfl
  intro hcon
  have hV0 : chartEval n K G ℓ₁ v hvG hℓ₁ (y : chartRing n K G ℓ₁) = 0 := by
    rw [h1, e]
    unfold chartLocEval
    rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
    rw [hcon, mul_zero]
  exact hy hV0

/-- The lifted numerator of a prime-complement element lies in the target
prime complement: its `chartEval` is nonzero since `coneEval` of the shared
numerator is (`chartIso_coneEval_ne_zero_of_mem_primeCompl`), via the
`IsLocalization.lift` spec equation in the target chart.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartLocEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval`, `Appendix_FixedPoint.BezoutChain.pointIdeal`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_coneEval_ne_zero_of_mem_primeCompl`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenEq`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.mem_primeCompl_iff`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `RingHom.mem_ker`. -/
theorem chartIso_lift_mem_primeCompl (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (y : (pointIdeal n K G ℓ₁ v hvG hℓ₁).primeCompl) :
    chartIso_liftToChart n K G ℓ₂ (chartIso_chosenD n K G ℓ₁ (y : chartRing n K G ℓ₁))
        (chartIso_chosenS n K G ℓ₁ (y : chartRing n K G ℓ₁))
        (chartIso_chosenP n K G ℓ₁ (y : chartRing n K G ℓ₁))
        (chartIso_chosenHom n K G ℓ₁ (y : chartRing n K G ℓ₁))
        (chartIso_chosenEq n K G ℓ₁ (y : chartRing n K G ℓ₁))
      ∈ (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl := by
  have hcone := chartIso_coneEval_ne_zero_of_mem_primeCompl n K G ℓ₁ v hvG hℓ₁ y
  rw [Ideal.mem_primeCompl_iff]
  unfold pointIdeal
  intro hmem
  rw [RingHom.mem_ker] at hmem
  have h1 : chartEval n K G ℓ₂ v hvG hℓ₂
        (chartIso_liftToChart n K G ℓ₂ (chartIso_chosenD n K G ℓ₁ ↑y)
          (chartIso_chosenS n K G ℓ₁ ↑y) (chartIso_chosenP n K G ℓ₁ ↑y)
          (chartIso_chosenHom n K G ℓ₁ ↑y) (chartIso_chosenEq n K G ℓ₁ ↑y))
        = chartLocEval n K G ℓ₂ v hvG hℓ₂
          (Localization.mk (chartIso_chosenS n K G ℓ₁ ↑y)
            ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)) ^
              (chartIso_chosenD n K G ℓ₁ ↑y),
              (Submonoid.mem_powers_iff _ _).mpr
                ⟨chartIso_chosenD n K G ℓ₁ ↑y, rfl⟩⟩) := rfl
  rw [h1] at hmem
  unfold chartLocEval at hmem
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec] at hmem
  apply hcone
  rw [hmem, mul_zero]

/-- A fraction with prime-complement numerator is a unit: the swapped
fraction is the two-sided inverse (both products collapse by `mk_mul` to a
`mul_comm` identity via `IsLocalization.mk'_eq_iff_eq`, against
`Localization.mk_one`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.locRingAt`,
  `Appendix_FixedPoint.BezoutChain.chartRing`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_mul`, `Localization.mk_one`;
  `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.mk'_eq_iff_eq`. -/
theorem chartIso_mk_unit_of_mem_primeCompl (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (a : chartRing n K G ℓ₂) (ha : a ∈ (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl)
    (b : (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl) :
    IsUnit (Localization.mk a b :
      locRingAt n K G ℓ₂ v hvG hℓ₂) := by
  have hmul : ∀ (x : chartRing n K G ℓ₂)
      (hx : x ∈ (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl)
      (z : (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl),
      Localization.mk x z * Localization.mk (z : chartRing n K G ℓ₂) ⟨x, hx⟩
        = 1 := by
    intro x hx z
    rw [Localization.mk_mul]
    conv_rhs => rw [← Localization.mk_one]
    rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply,
      IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [Submonoid.coe_mul, Submonoid.coe_one, mul_one, one_mul]
    exact mul_comm _ _
  have hinv : Localization.mk (b : chartRing n K G ℓ₂) ⟨a, ha⟩ *
      Localization.mk a b = 1 := by
    rw [mul_comm]
    exact hmul a ha b
  refine ⟨Units.mk (Localization.mk a b)
    (Localization.mk (b : chartRing n K G ℓ₂) ⟨a, ha⟩)
    (hmul a ha b) hinv, rfl⟩

/-- The transport hom sends the prime complement to units: on a
prime-complement element `y`, `chartIso_gHom y` is definitionally the
fraction `(lift s)/(chartDenom d)`, whose numerator lies in the target
prime complement (`chartIso_lift_mem_primeCompl`), hence is a unit by
`chartIso_mk_unit_of_mem_primeCompl`. This is the exact hypothesis
`IsLocalization.lift` needs for `chartIso_F`/`chartIso_G`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.pointIdeal`,
  `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_gHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_denom_mem_primeCompl`,
  `Appendix_FixedPoint.BezoutChain.chartIso_lift_mem_primeCompl`,
  `Appendix_FixedPoint.BezoutChain.chartIso_mk_unit_of_mem_primeCompl`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk`. -/
theorem chartIso_primeCompl_to_units (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (y : (pointIdeal n K G ℓ₁ v hvG hℓ₁).primeCompl) :
    IsUnit (chartIso_gHom n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
      (y : chartRing n K G ℓ₁)) := by
  have hmem := chartIso_lift_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ y
  have e : (chartIso_gHom n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂)
        (y : chartRing n K G ℓ₁)
      = Localization.mk
        (chartIso_liftToChart n K G ℓ₂ (chartIso_chosenD n K G ℓ₁ ↑y)
          (chartIso_chosenS n K G ℓ₁ ↑y) (chartIso_chosenP n K G ℓ₁ ↑y)
          (chartIso_chosenHom n K G ℓ₁ ↑y) (chartIso_chosenEq n K G ℓ₁ ↑y))
        ⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ (chartIso_chosenD n K G ℓ₁ ↑y),
          chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁
            (chartIso_chosenD n K G ℓ₁ ↑y)⟩ := rfl
  rw [e]
  exact chartIso_mk_unit_of_mem_primeCompl n K G ℓ₂ v hvG hℓ₂ _ hmem _

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Chart-iso construction: the lifted homs

`IsLocalization.lift` promotes the transport hom to stalk maps in both
directions (`chartIso_F`, `chartIso_G`), with their values on chart elements
(`chartIso_F_algebraMap`, `chartIso_G_algebraMap`) and the
scalar-preservation law (`chartIso_gHom_algebraMap`, `chartIso_F_commutes`)
needed for the final `K`-linear promotion. -/

/-- The degree-`0` cross-chart denominator is one: both the `ℓ₁`-power
(`pow_zero`) and the `ℓ₂`-power denominator (identified with `1` as a
`Submonoid.powers` element) collapse, so the fraction is
`Localization.mk 1 1 = 1` (`Localization.mk_one`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk_one`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
theorem chartIso_denom_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) :
    chartIso_chartDenom n K G ℓ₁ ℓ₂ 0 = 1 := by
  apply Subtype.ext
  unfold chartIso_chartDenom chartIso_liftToChart
  dsimp only
  have hpow1 : ((Ideal.Quotient.mk (Ideal.span (Set.range G))
      (mkLin n K ℓ₁)) ^ (0 : ℕ)) = 1 := pow_zero _
  rw [hpow1]
  change Localization.mk (1 : coneQuotient n K G) _ = 1
  have h1mem : (1 : coneQuotient n K G) ∈ Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ₂)) :=
    (Submonoid.mem_powers_iff _ _).mpr ⟨0, by rw [pow_zero]⟩
  have hden : (⟨(Ideal.Quotient.mk (Ideal.span (Set.range G))
      (mkLin n K ℓ₂)) ^ 0,
      (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩ :
      Submonoid.powers _) = ⟨1, h1mem⟩ := by
    apply Subtype.ext
    change _ ^ (0 : ℕ) = 1
    rw [pow_zero]
  rw [hden]
  have h11 : (⟨1, h1mem⟩ :
      Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range G)) (mkLin n K ℓ₂) :
        coneQuotient n K G)) = 1 := by
    apply Subtype.ext
    rfl
  rw [h11, Localization.mk_one]

/-- The lifted forward hom: `IsLocalization.lift` of `chartIso_gHom`,
promoting the chart-to-stalk transport to a stalk-to-stalk map
(`locRingAt ℓ₁ → locRingAt ℓ₂`), licensed by
`chartIso_primeCompl_to_units`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_gHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_primeCompl_to_units`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift`. -/
noncomputable def chartIso_F (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    locRingAt n K G ℓ₁ v hvG hℓ₁ →+* locRingAt n K G ℓ₂ v hvG hℓ₂ :=
  IsLocalization.lift (fun y =>
    chartIso_primeCompl_to_units n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ y)

/-- The lifted backward hom: `IsLocalization.lift` of the swapped
transport `chartIso_gHom ℓ₂ ℓ₁`, promoting it to a stalk-to-stalk map
(`locRingAt ℓ₂ → locRingAt ℓ₁`), licensed by the swapped
`chartIso_primeCompl_to_units`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_gHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_primeCompl_to_units`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift`. -/
noncomputable def chartIso_G (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    locRingAt n K G ℓ₂ v hvG hℓ₂ →+* locRingAt n K G ℓ₁ v hvG hℓ₁ :=
  IsLocalization.lift (fun y =>
    chartIso_primeCompl_to_units n K G ℓ₂ ℓ₁ v hvG hℓ₂ hℓ₁ y)

/-- `chartIso_F` on chart elements is `chartIso_gHom`: the lift agrees
with the underlying hom on `algebraMap`-images, by
`IsLocalization.lift_eq`. Consumed by `chartIso_gf_id` (via
`IsLocalization.ringHom_ext`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_F`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gHom`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift_eq`. -/
theorem chartIso_F_algebraMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (x : chartRing n K G ℓ₁) :
    chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
        (algebraMap (chartRing n K G ℓ₁) (locRingAt n K G ℓ₁ v hvG hℓ₁) x)
      = chartIso_gHom n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ x := by
  unfold chartIso_F
  exact IsLocalization.lift_eq _ _

/-- `chartIso_G` on chart elements is the backward `chartIso_gHom`: the
lift agrees with the underlying hom on `algebraMap`-images, by
`IsLocalization.lift_eq`. Consumed by `chartIso_fg_id` (via
`IsLocalization.ringHom_ext`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_G`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gHom`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift_eq`. -/
theorem chartIso_G_algebraMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (x : chartRing n K G ℓ₂) :
    chartIso_G n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
        (algebraMap (chartRing n K G ℓ₂) (locRingAt n K G ℓ₂ v hvG hℓ₂) x)
      = chartIso_gHom n K G ℓ₂ ℓ₁ v hvG hℓ₂ hℓ₁ x := by
  unfold chartIso_G
  exact IsLocalization.lift_eq _ _

/-- The transport hom preserves scalars: `algebraMap r` presents as
`C r / ℓ̄^0` (via `MvPolynomial.algebraMap_eq` and
`Ideal.Quotient.mk_algebraMap`), whose transport is
`algebraMap r / 1 = algebraMap r` (the denominator is `1` by
`chartIso_denom_zero`; `Localization.mk_one_eq_algebraMap` closes).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing`,
  `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_gHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_eq_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_lift_val`,
  `Appendix_FixedPoint.BezoutChain.chartIso_denom_zero`,
  `Appendix_FixedPoint.BezoutChain.chartIso_denom_mem_primeCompl`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_algebraMap`, `Localization.mk_one_eq_algebraMap`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`. -/
theorem chartIso_gHom_algebraMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (r : K) :
    chartIso_gHom n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
        (algebraMap K (chartRing n K G ℓ₁) r)
      = algebraMap K (locRingAt n K G ℓ₂ v hvG hℓ₂) r := by
  have homC : (MvPolynomial.C r : MvPolynomial (Fin (n + 2)) K).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C _ _
  have hC : (MvPolynomial.C r : MvPolynomial (Fin (n + 2)) K)
      = algebraMap K (MvPolynomial (Fin (n + 2)) K) r := by
    rw [MvPolynomial.algebraMap_eq]
  have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C r)
      = algebraMap K (coneQuotient n K G) r := by
    rw [hC]
    exact Ideal.Quotient.mk_algebraMap K _ _
  have e : ((algebraMap K (chartRing n K G ℓ₁) r) : Localization
        (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
          coneQuotient n K G)))
      = Localization.mk (algebraMap K (coneQuotient n K G) r)
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)) ^ 0,
          (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩ := by
    have hbase : Localization.mk (algebraMap K (coneQuotient n K G) r) (1 :
          Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
            coneQuotient n K G))
        = algebraMap K (Localization (Submonoid.powers
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
            coneQuotient n K G))) r :=
      Localization.mk_algebraMap r
    change algebraMap K (Localization (Submonoid.powers
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁) :
          coneQuotient n K G))) r = _
    rw [← hbase]
    congr 1
  have hLift : chartIso_liftToChart n K G ℓ₂ 0
        (algebraMap K (coneQuotient n K G) r) (MvPolynomial.C r) homC hmap
      = algebraMap K (chartRing n K G ℓ₂) r := by
    apply Subtype.ext
    rw [chartIso_lift_val]
    have hbase : Localization.mk (algebraMap K (coneQuotient n K G) r) (1 :
          Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂) :
            coneQuotient n K G))
        = algebraMap K (Localization (Submonoid.powers
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂) :
            coneQuotient n K G))) r :=
      Localization.mk_algebraMap r
    change Localization.mk (algebraMap K (coneQuotient n K G) r)
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)) ^ 0, _⟩
        = algebraMap K (Localization (Submonoid.powers
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂) :
            coneQuotient n K G))) r
    rw [← hbase]
    congr 1
  have hD0 := chartIso_denom_zero n K G ℓ₁ ℓ₂
  have e2 : chartIso_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ 0
        (algebraMap K (coneQuotient n K G) r) (MvPolynomial.C r) homC hmap
      = Localization.mk (algebraMap K (chartRing n K G ℓ₂) r) 1 := by
    unfold chartIso_gAux
    rw [hLift]
    have hy1 : (⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ 0,
        chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁ 0⟩ :
        (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl) = 1 :=
      Subtype.ext hD0
    rw [hy1]
  change chartIso_g n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
      (algebraMap K (chartRing n K G ℓ₁) r) = _
  rw [chartIso_g_eq_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ _
    0 _ _ homC hmap e, e2]
  exact Localization.mk_one_eq_algebraMap _

/-- `chartIso_F` preserves scalars (via `chartIso_gHom_algebraMap` and the
`IsLocalization.lift` spec equation): writing `algebraMap r` as
`mk (algebraMap r) 1` (`Localization.mk_algebraMap`), the lift spec plus
scalar-preservation of `chartIso_gHom` and `map_one` give the result. This
is the side condition for `AlgEquiv.ofRingEquiv` in `chartIso_algEquiv`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_F`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gHom_algebraMap`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_map_one`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_algebraMap`, `Localization.mk_eq_mk'_apply`,
  `IsLocalization.lift_mk'_spec`. -/
theorem chartIso_F_commutes (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (r : K) :
    chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
        (algebraMap K (locRingAt n K G ℓ₁ v hvG hℓ₁) r)
      = algebraMap K (locRingAt n K G ℓ₂ v hvG hℓ₂) r := by
  have h1 : algebraMap K (locRingAt n K G ℓ₁ v hvG hℓ₁) r
      = Localization.mk (algebraMap K (chartRing n K G ℓ₁) r) 1 :=
    (Localization.mk_algebraMap r).symm
  rw [h1]
  unfold chartIso_F
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  rw [chartIso_gHom_algebraMap]
  have hone : chartIso_gHom n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ 1 = 1 :=
    chartIso_g_map_one n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
  exact (one_mul _).symm.trans
    (congrArg (fun x : locRingAt n K G ℓ₂ v hvG hℓ₂ =>
      x * algebraMap K (locRingAt n K G ℓ₂ v hvG hℓ₂) r) hone.symm)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Chart-iso construction: roundtrip, inverses, and the iso

The forward-backward roundtrip on chart generators (`chartIso_roundtrip`, via
`chartIso_lift_recover` and `chartIso_lift_self_one`) feeds
`IsLocalization.ringHom_ext` to give the two-sided inverse laws
(`chartIso_fg_id`, `chartIso_gf_id`); these bundle as the ring iso
(`chartIso_ringEquiv`), promoted to the `K`-algebra iso (`chartIso_algEquiv`)
and the `K`-linear iso (`chartIso_toLinearEquiv`) inhabiting
`ChartCompatIso` (`chartIso_chartCompatIso`), closing `hchart`. -/

/-- The lift of the target chart's own power is one: the fraction
`ℓ̄₂^d/ℓ̄₂^d` collapses by `IsLocalization.mk'_self` (after unfolding the
lift value via `chartIso_lift_val`). Consumed by `chartIso_roundtrip` for
the denominator side.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_lift_val`,
  `Appendix_FixedPoint.BezoutChain.chartIso_mkLin_pow_hom`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.mk'_self`. -/
theorem chartIso_lift_self_one (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₂ : Fin (n + 2) → K) (d : ℕ)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range G))
        ((mkLin n K ℓ₂) ^ d)
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)) ^ d) :
    chartIso_liftToChart n K G ℓ₂ d
        ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)) ^ d)
        ((mkLin n K ℓ₂) ^ d)
        (chartIso_mkLin_pow_hom n K ℓ₂ d) hpeq = 1 := by
  apply Subtype.ext
  rw [chartIso_lift_val, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_self _ _

/-- Lifting the chosen presentation of a chart element recovers the
element: `chartIso_liftToChart` of the `chartIso_chosen*` data is `x`
itself, since the lift value (`chartIso_lift_val`) is exactly the chosen
presentation equation (`chartIso_chosenE`). Consumed by
`chartIso_roundtrip` for the numerator side.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_lift_val`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenS`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenP`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenEq`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenE`. -/
theorem chartIso_lift_recover (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₂ : Fin (n + 2) → K) (x : chartRing n K G ℓ₂) :
    chartIso_liftToChart n K G ℓ₂ (chartIso_chosenD n K G ℓ₂ x)
        (chartIso_chosenS n K G ℓ₂ x) (chartIso_chosenP n K G ℓ₂ x)
        (chartIso_chosenHom n K G ℓ₂ x) (chartIso_chosenEq n K G ℓ₂ x) = x := by
  apply Subtype.ext
  rw [chartIso_lift_val]
  exact (chartIso_chosenE n K G ℓ₂ x).symm

set_option maxHeartbeats 1000000 in
-- `rw` matching over fraction goals carrying nested `chartIso_chosen*` data
-- exceeds the default 200k heartbeats (expensive `isDefEq` per node);
-- wall-time stays ~1s.
/-- Roundtrip on chart generators: `F (gHom x) = algebraMap x`. The
`IsLocalization.lift` spec equation reduces this to a fraction identity:
both `gHom` applications unfold via `chartIso_g_eq_gAux` (with `rfl`
presentations), the numerator side collapses by `chartIso_lift_recover`,
the denominator side by `chartIso_lift_self_one`, and `Localization.mk_mul`
finishes against `algebraMap x = mk x 1`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_F`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gHom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_g_eq_gAux`,
  `Appendix_FixedPoint.BezoutChain.chartIso_liftToChart`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chartDenom`,
  `Appendix_FixedPoint.BezoutChain.chartIso_denom_mem_primeCompl`,
  `Appendix_FixedPoint.BezoutChain.chartIso_lift_recover`,
  `Appendix_FixedPoint.BezoutChain.chartIso_lift_self_one`,
  `Appendix_FixedPoint.BezoutChain.chartIso_chosenD`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`;
  `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_mul`.
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_pow`. -/
theorem chartIso_roundtrip (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (x : chartRing n K G ℓ₂) :
    chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
        (chartIso_gHom n K G ℓ₂ ℓ₁ v hvG hℓ₂ hℓ₁ x)
      = algebraMap (chartRing n K G ℓ₂) (locRingAt n K G ℓ₂ v hvG hℓ₂) x := by
  have eN : (chartIso_gHom n K G ℓ₂ ℓ₁ v hvG hℓ₂ hℓ₁) x
      = Localization.mk
        (chartIso_liftToChart n K G ℓ₁ (chartIso_chosenD n K G ℓ₂ x)
          (chartIso_chosenS n K G ℓ₂ x) (chartIso_chosenP n K G ℓ₂ x)
          (chartIso_chosenHom n K G ℓ₂ x) (chartIso_chosenEq n K G ℓ₂ x))
        ⟨chartIso_chartDenom n K G ℓ₂ ℓ₁ (chartIso_chosenD n K G ℓ₂ x),
          chartIso_denom_mem_primeCompl n K G ℓ₂ ℓ₁ v hvG hℓ₁ hℓ₂
            (chartIso_chosenD n K G ℓ₂ x)⟩ := rfl
  rw [eN]
  unfold chartIso_F
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  have hpeqD : Ideal.Quotient.mk (Ideal.span (Set.range G))
        ((mkLin n K ℓ₂) ^ (chartIso_chosenD n K G ℓ₂ x))
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)) ^
        (chartIso_chosenD n K G ℓ₂ x) := by
    rw [map_pow]
  have hN : (chartIso_gHom n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂)
        (chartIso_liftToChart n K G ℓ₁ (chartIso_chosenD n K G ℓ₂ x)
          (chartIso_chosenS n K G ℓ₂ x) (chartIso_chosenP n K G ℓ₂ x)
          (chartIso_chosenHom n K G ℓ₂ x) (chartIso_chosenEq n K G ℓ₂ x))
      = Localization.mk
        (chartIso_liftToChart n K G ℓ₂ (chartIso_chosenD n K G ℓ₂ x)
          (chartIso_chosenS n K G ℓ₂ x) (chartIso_chosenP n K G ℓ₂ x)
          (chartIso_chosenHom n K G ℓ₂ x) (chartIso_chosenEq n K G ℓ₂ x))
        ⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ (chartIso_chosenD n K G ℓ₂ x),
          chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁
            (chartIso_chosenD n K G ℓ₂ x)⟩ :=
    chartIso_g_eq_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ _
      (chartIso_chosenD n K G ℓ₂ x) (chartIso_chosenS n K G ℓ₂ x)
      (chartIso_chosenP n K G ℓ₂ x) (chartIso_chosenHom n K G ℓ₂ x)
      (chartIso_chosenEq n K G ℓ₂ x) rfl
  have hD : (chartIso_gHom n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂)
        (chartIso_chartDenom n K G ℓ₂ ℓ₁ (chartIso_chosenD n K G ℓ₂ x))
      = Localization.mk
        (chartIso_liftToChart n K G ℓ₂ (chartIso_chosenD n K G ℓ₂ x)
          ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)) ^
            (chartIso_chosenD n K G ℓ₂ x))
          ((mkLin n K ℓ₂) ^ (chartIso_chosenD n K G ℓ₂ x))
          (chartIso_mkLin_pow_hom n K ℓ₂ (chartIso_chosenD n K G ℓ₂ x))
          hpeqD)
        ⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ (chartIso_chosenD n K G ℓ₂ x),
          chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁
            (chartIso_chosenD n K G ℓ₂ x)⟩ :=
    chartIso_g_eq_gAux n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ _
      (chartIso_chosenD n K G ℓ₂ x)
      ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)) ^
        (chartIso_chosenD n K G ℓ₂ x))
      ((mkLin n K ℓ₂) ^ (chartIso_chosenD n K G ℓ₂ x))
      (chartIso_mkLin_pow_hom n K ℓ₂ (chartIso_chosenD n K G ℓ₂ x))
      hpeqD rfl
  rw [hN, hD]
  have hx := chartIso_lift_recover n K G ℓ₂ x
  have h1x := chartIso_lift_self_one n K G ℓ₂
    (chartIso_chosenD n K G ℓ₂ x) hpeqD
  rw [hx, h1x]
  have halg : algebraMap (chartRing n K G ℓ₂) (locRingAt n K G ℓ₂ v hvG hℓ₂) x
      = Localization.mk x 1 := rfl
  rw [halg, Localization.mk_mul]
  have hnx : (1 : chartRing n K G ℓ₂) * x = x := one_mul x
  have hE1 : ((⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ (chartIso_chosenD n K G ℓ₂ x),
        chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁
          (chartIso_chosenD n K G ℓ₂ x)⟩ :
        (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl) * 1)
      = ⟨chartIso_chartDenom n K G ℓ₁ ℓ₂ (chartIso_chosenD n K G ℓ₂ x),
        chartIso_denom_mem_primeCompl n K G ℓ₁ ℓ₂ v hvG hℓ₂ hℓ₁
          (chartIso_chosenD n K G ℓ₂ x)⟩ :=
    mul_one _
  rw [hnx, hE1]

/-- Forward-backward composite is the identity on the `ℓ₂`-stalk:
`IsLocalization.ringHom_ext` reduces to agreement on chart elements, where
`chartIso_G_algebraMap` exhibits `G x` as a `gHom`-value and
`chartIso_roundtrip` closes the roundtrip. (The `right_inv` field of
`chartIso_ringEquiv`.)

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_F`,
  `Appendix_FixedPoint.BezoutChain.chartIso_G`,
  `Appendix_FixedPoint.BezoutChain.chartIso_G_algebraMap`,
  `Appendix_FixedPoint.BezoutChain.chartIso_roundtrip`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.ringHom_ext`.
* `Mathlib/Algebra/Ring/Hom/Defs.lean`, `RingHom.ext`. -/
theorem chartIso_fg_id (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    (chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂).comp
        (chartIso_G n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂)
      = RingHom.id (locRingAt n K G ℓ₂ v hvG hℓ₂) := by
  refine IsLocalization.ringHom_ext
    (M := (pointIdeal n K G ℓ₂ v hvG hℓ₂).primeCompl) ?_
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [chartIso_G_algebraMap, chartIso_roundtrip]

/-- Backward-forward composite is the identity on the `ℓ₁`-stalk: the
mirror of `chartIso_fg_id` with the charts swapped —
`IsLocalization.ringHom_ext` plus `chartIso_F_algebraMap` plus the swapped
`chartIso_roundtrip`. (The `left_inv` field of `chartIso_ringEquiv`.)

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_F`,
  `Appendix_FixedPoint.BezoutChain.chartIso_G`,
  `Appendix_FixedPoint.BezoutChain.chartIso_F_algebraMap`,
  `Appendix_FixedPoint.BezoutChain.chartIso_roundtrip`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.ringHom_ext`.
* `Mathlib/Algebra/Ring/Hom/Defs.lean`, `RingHom.ext`. -/
theorem chartIso_gf_id (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    (chartIso_G n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂).comp
        (chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂)
      = RingHom.id (locRingAt n K G ℓ₁ v hvG hℓ₁) := by
  refine IsLocalization.ringHom_ext
    (M := (pointIdeal n K G ℓ₁ v hvG hℓ₁).primeCompl) ?_
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [chartIso_F_algebraMap]
  exact chartIso_roundtrip n K G ℓ₂ ℓ₁ v hvG hℓ₂ hℓ₁ x

/-- The chart-compatibility ring isomorphism between the two stalks at
`v`: forward `chartIso_F`, backward `chartIso_G`, with the two-sided
inverse laws `chartIso_gf_id` (`left_inv`) and `chartIso_fg_id`
(`right_inv`), pointwise via `RingHom.congr_fun`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_F`,
  `Appendix_FixedPoint.BezoutChain.chartIso_G`,
  `Appendix_FixedPoint.BezoutChain.chartIso_fg_id`,
  `Appendix_FixedPoint.BezoutChain.chartIso_gf_id`. -/
noncomputable def chartIso_ringEquiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    locRingAt n K G ℓ₁ v hvG hℓ₁ ≃+* locRingAt n K G ℓ₂ v hvG hℓ₂ where
  toFun := chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
  invFun := chartIso_G n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂
  map_add' := (chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂).map_add
  map_mul' := (chartIso_F n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂).map_mul
  left_inv x := RingHom.congr_fun
    (chartIso_gf_id n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂) x
  right_inv x := RingHom.congr_fun
    (chartIso_fg_id n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂) x

/-- The `K`-algebra isomorphism: `AlgEquiv.ofRingEquiv` promotes
`chartIso_ringEquiv`, with scalar-preservation discharged by
`chartIso_F_commutes`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.locRingAt`.
* This module, `Appendix_FixedPoint.BezoutChain.chartIso_ringEquiv`,
  `Appendix_FixedPoint.BezoutChain.chartIso_F_commutes`.
* `Mathlib/Algebra/Algebra/Equiv.lean`, `AlgEquiv.ofRingEquiv`. -/
noncomputable def chartIso_algEquiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    locRingAt n K G ℓ₁ v hvG hℓ₁ ≃ₐ[K] locRingAt n K G ℓ₂ v hvG hℓ₂ :=
  AlgEquiv.ofRingEquiv
    (f := chartIso_ringEquiv n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂)
    (fun r => chartIso_F_commutes n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂ r)

/-- The `K`-linear isomorphism discharging `ChartCompatIso`: the linear
face (`AlgEquiv.toLinearEquiv`) of `chartIso_algEquiv`, in exactly the
`locRingAt ℓ₁ ≃ₗ[K] locRingAt ℓ₂` shape the residual requires.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartIso_algEquiv`,
  `Appendix_FixedPoint.BezoutChain.ChartCompatIso`.
* `Mathlib/Algebra/Algebra/Equiv.lean`, `AlgEquiv.toLinearEquiv`. -/
noncomputable def chartIso_toLinearEquiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    locRingAt n K G ℓ₁ v hvG hℓ₁ ≃ₗ[K] locRingAt n K G ℓ₂ v hvG hℓ₂ :=
  (chartIso_algEquiv n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂).toLinearEquiv

/-- The `ChartCompatIso` residual is inhabited: the two chart-local rings
at `v` are `K`-linearly isomorphic, witnessed by
`chartIso_toLinearEquiv`. This closes the `hchart` conditional —
`hloceq_forall_of_iso` and `hchart_distEll_of_iso` are now unconditional.

GRADE (`hchart` result): closed (was conditional-exact-`[ChartCompatIso]`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.ChartCompatIso`,
  `Appendix_FixedPoint.BezoutChain.chartIso_toLinearEquiv`,
  `Appendix_FixedPoint.BezoutChain.hloceq_forall_of_iso`,
  `Appendix_FixedPoint.BezoutChain.hchart_distEll_of_iso`. -/
theorem chartIso_chartCompatIso (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) :
    ChartCompatIso n K G ℓ₁ ℓ₂ v hvG hℓ₁ hvG hℓ₂ :=
  ⟨chartIso_toLinearEquiv n K G ℓ₁ ℓ₂ v hvG hℓ₁ hℓ₂⟩

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
