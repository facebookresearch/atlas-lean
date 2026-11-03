/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Statement of Bézout's theorem (quadratic case) — main theorems

Minimal formal statement of the Bézout input our fixed-point argument needs.

## Mathematical content

Setup: `n + 1` homogeneous quadratic polynomials `G₀, …, Gₙ` in `n + 2`
variables `(x₀, …, xₙ, z)` over an algebraically closed field `K`, cutting out
the projective locus `Z = V(G₀, …, Gₙ)` in `ℙⁿ⁺¹ = ℙ K (Fin (n+2) → K)`.
Our instance is `Gᵢ = Fᵢ(x) − z·xᵢ` (see `mkSystem`), where the `Fᵢ` are the
quadratic structure forms in the `x` variables.

Needed conclusion (`bezout_quadratic`): if `Z` is zero-dimensional, its total
degree counted with multiplicity equals `2 ^ (n + 1)`. Corollary used
downstream (`exists_another_point_of_smooth_point`): if `Z` contains the point
`[0 : ⋯ : 0 : 1]` with multiplicity `1` (smooth point), then `Z` contains
another `K`-point, since `2 ^ (n + 1) ≥ 2`.

## Definitions used

`Projectivization` (`ℙ K V`), `MvPolynomial`, `MvPolynomial.IsHomogeneous`,
and `IsAlgClosed` all exist in Mathlib v4.34.0 and are used directly.
What does not exist is any degree-of-variety / dimension-of-variety /
intersection-multiplicity API for loci in `Projectivization`. Those notions
(`IsZeroDimensional`, `totalDegree`, `localPointMultiplicity`, `IsSmoothPoint`;
the preliminary global-length `pointMultiplicity` survives only as a
backward-compat alias)
therefore live in `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions` with
real bodies
built from general-purpose Mathlib API (quotients, Krull dimension, finrank,
Jacobian rank); see that module for the per-definition references. They take
the scheme data `G` (and the explicit section data `ℓ`, whose regularity R1
is proved in parallel) rather than the locus set. Both theorems below
are proved conditionally; see the per-theorem status comment below
(followed by the bridge-lane closings).

## Consumer note

The consumer (fixed-point / idempotent argument) applies
`exists_another_point_of_smooth_point` to `mkSystem n K F`: it supplies the
system `G`, homogeneity (`mkSystem_homogeneous`), the section data `ℓ` with
its R1-nonvanishing `hc`, zero-dimensionality of the locus, membership +
smoothness + multiplicity `1` at `distinguishedPoint` (`[0 : ⋯ : 0 : 1]`),
plus the conditional inputs (`H F hH0 hSES hSEC hfilter hfin hsum hbridge
_hpos`; see the theorem docstring), and receives a second `K`-point of the
locus, distinct from `distinguishedPoint`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Homogeneity of the system -/

/-- Our system is homogeneous quadratic whenever the input forms are:
each `Gᵢ = Fᵢ(x) − z·xᵢ` is homogeneous of degree `2`. The proof is the
routine combination of "`rename` preserves homogeneity" with "`z·xᵢ` is the
product of two linear forms". -/
theorem mkSystem_homogeneous (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    ∀ i, ((mkSystem n K F) i).IsHomogeneous 2 := by
  intro i
  simp only [mkSystem]
  exact ((hF i).rename_isHomogeneous).sub
    (by simpa using
      (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-! ## Bézout's theorem and the second-point corollary -/

/-- Bézout's theorem, quadratic case (conditional closure):
`n + 1` homogeneous quadratics in `n + 2` variables over an algebraically
closed field cut out a locus whose total degree with multiplicity is
`2 ^ (n + 1)` — provided the locus is zero-dimensional and the section linear
form `ℓ` is regular on the cone (hypothesis `_hreg`). This is the
`∏ deg Gᵢ = 2 ^ (n+1)` instance of the general `deg Z = ∏ deg Gᵢ`. The
regularity hypothesis is essential: a non-regular section can be
infinite-dimensional, in which case `totalDegree` (a `finrank`, `0` by
convention when infinite) need not equal `2 ^ (n + 1)`.

Conditional on the six numerical inputs below (exact list): `H`, `F`,
`hH0`, `hSES`, `hSEC`, `hfilter` — verbatim shapes from
`HilbertFunctionCount.length_section_eq_two_pow` (`Geometry/HilbertFunctionCount.lean`, applied
directly since its conclusion is already `totalDegree … = 2 ^ (n + 1)`; no
unfold needed). Suppliers: `hH0` ⇐ `hilbertSeries_poly`;
`hSES` ⇐ R2 (`exists_regular_quadrics`) via `graded_piece_ses`;
`hSEC` ⇐ `_hreg` via `graded_piece_ses` (R1 application);
`hfilter` ⇐ filtration geometry. The pre-existing `_hG`, `_hreg`, `_hZd`
are retained for interface stability (currently unused: the closure is
purely numerical). Conclusion exact. -/
theorem bezout_quadratic (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (_hG : ∀ i, (G i).IsHomogeneous 2)
    (ℓ : Fin (n + 2) → K)
    (_hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (_hZd : IsZeroDimensional n K G)
    (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ)
    (hH0 : ∀ d, H 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d)
    (hSEC : ∀ d,
      F d + (if 1 ≤ d then H (n + 1) (d - 1) else 0) = H (n + 1) d)
    (hfilter : ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d) + F d) ∧
      ∀ d, B < d → F d = 0) :
    totalDegree n K G ℓ = 2 ^ (n + 1) :=
  length_section_eq_two_pow n K G ℓ H F hH0 hSES hSEC hfilter

/-- Corollary used downstream (conditional closure): if the
locus contains the distinguished point `[0 : ⋯ : 0 : 1]` as a smooth point of
multiplicity `1`, then it contains another `K`-point. Intended proof: by
`bezout_quadratic` the total degree is `2 ^ (n + 1) ≥ 2`, while the
distinguished point accounts for exactly `1`, so some further point of the
locus must exist. The counting argument uses `totalDegree = 2 ^ (n + 1)`, so
it needs the same regularity hypothesis `hreg` on the section form `ℓ`: a
non-regular section can be infinite-dimensional, in which case `totalDegree`
(a `finrank`, `0` by convention when infinite) need not equal `2 ^ (n + 1)`.

Conditional on eleven added inputs (exact list): the six count
inputs (`H F hH0 hSES hSEC hfilter`, threaded into `bezout_quadratic` for
the total) plus `hc`, `hfin`, `hsum`, `hbridge`, `_hpos` — verbatim C5
shapes from `Counting.exists_another_point_of_counting_data`
(`Geometry/Counting.lean`), whose proof is mirrored below (it cannot be
imported: `Counting → ResultantLemmas → Statement.Statement` would be an import
cycle, and `Counting` transitively depends on this module).
`locusFinset` there is `hfin.toFinset` by definition and is used directly
here. Suppliers: `hc` is the ∀-p R1-nonvanishing
required by the local form (from R1); `hfin` ⇐ `finite_locus`
modulo `hcover` (L-COVER); `hsum` ⇐ `sum_mult_eq_chart_length` modulo
`hlocal`/`hadd` (L-LOCAL/L-ADD); `hbridge` ⇐ `chart_bridge` modulo `hlin`
(L-HLIN); `_hpos` ⇐ `mult_pos_of_mem` modulo L-POS (retained for interface
stability although the singleton-collapse proof subsumes it). `hmult` is
taken directly (cf. `smooth_implies_mult_one` for its local-`hloc`
discharge route, via `LocalMultiplicity.hlocLocal`); `mult_chart_independent` is
not needed (single chart). The pre-existing `_hsmooth` is retained for
interface stability. All multiplicity hypotheses are now in local form.
Conclusion exact.

Local-form resolution (verified under the preliminary global-length form):
`hmult` pins the local length at `distinguishedPoint.rep` (`= 1`)
while `hbridge` + `bezout_quadratic` pin the global chart length
(`= 2 ^ (n + 1) ≥ 2`) — jointly consistent (a single local factor of
length `1` inside a global length `≥ 2`), so the conditional is no longer
vacuous on its face. Genuine applicability now rests on the counting-route
discharges (`hsum`/`hbridge`/`_hpos` via L-LOCAL/L-ADD/L-HLIN/L-POS;
`hmult` via T6/L-SMOOTH-VAL).

## References (proof mirrors `Counting.exists_another_point_of_counting_data`)

* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.toFinset`,
  `Set.Finite.mem_toFinset`.
* `Mathlib/Data/Finset/Insert.lean`, `Finset.eq_singleton_iff_unique_mem`,
  `Finset.mem_singleton`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_singleton` (via `to_additive` from `prod_singleton`).
* `Mathlib/Algebra/Order/Monoid/Unbundled/Pow.lean`, `pow_le_pow_right'`. -/
theorem exists_another_point_of_smooth_point (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hmem : distinguishedPoint n K ∈ vanishingLocus n K G)
    (_hsmooth : IsSmoothPoint n K G (distinguishedPoint n K))
    (hmult : localPointMultiplicity n K G ℓ hc (distinguishedPoint n K) = 1)
    (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ)
    (hH0 : ∀ d, H 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d)
    (hSEC : ∀ d,
      F d + (if 1 ≤ d then H (n + 1) (d - 1) else 0) = H (n + 1) d)
    (hfilter : ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d) + F d) ∧
      ∀ d, B < d → F d = 0)
    (hfin : (vanishingLocus n K G).Finite)
    (hsum : ∑ p ∈ hfin.toFinset, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ))
    (hbridge : Module.finrank K (chartRing n K G ℓ) = totalDegree n K G ℓ)
    (_hpos : ∀ p ∈ hfin.toFinset, 1 ≤ localPointMultiplicity n K G ℓ hc p) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K G ∧ q ≠ distinguishedPoint n K := by
  have hdist : distinguishedPoint n K ∈ hfin.toFinset :=
    hfin.mem_toFinset.mpr hmem
  have htotal : totalDegree n K G ℓ = 2 ^ (n + 1) :=
    bezout_quadratic n K G hG ℓ hreg hZd H F hH0 hSES hSEC hfilter
  have h2 : 2 ≤ ∑ p ∈ hfin.toFinset, localPointMultiplicity n K G ℓ hc p := by
    rw [hsum, hbridge, htotal]
    calc (2 : ℕ) = 2 ^ 1 := by simp
      _ ≤ 2 ^ (n + 1) := pow_le_pow_right' (by norm_num) (by omega)
  by_contra hcon
  have hcollapse : ∀ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K G → q = distinguishedPoint n K := by
    intro q hqmem
    by_contra hne
    exact hcon ⟨q, hqmem, hne⟩
  have hsub : hfin.toFinset ⊆ {distinguishedPoint n K} := by
    intro p hp
    have hpmem : p ∈ vanishingLocus n K G := hfin.mem_toFinset.mp hp
    exact Finset.mem_singleton.mpr (hcollapse p hpmem)
  have heq : hfin.toFinset = {distinguishedPoint n K} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hdist, fun p hp => Finset.mem_singleton.mp (hsub hp)⟩
  rw [heq, Finset.sum_singleton, hmult] at h2
  exact absurd h2 (by norm_num)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/- Status of the three results above:
1. `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`: proved —
   the routine homogeneous-degree computation "`rename` preserves
   `IsHomogeneous 2` and `X z * X xᵢ` is homogeneous of degree `1 + 1 = 2`"
   (via `MvPolynomial.IsHomogeneous.rename_isHomogeneous/sub/mul`,
   `MvPolynomial.isHomogeneous_X`).
2. `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.bezout_quadratic`: closed conditionally on
   `H F hH0 hSES hSEC hfilter` (verbatim `length_section_eq_two_pow` inputs,
   applied directly); see the theorem docstring for status + suppliers.
3. `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point`: closed
   conditionally on `hc H F hH0 hSES hSEC hfilter hfin hsum hbridge _hpos`
   (C5 mirror of `Counting.exists_another_point_of_counting_data`, in
   local form); see the theorem docstring for status + suppliers + the
   local-form resolution note.
-/

/-! ## BridgeToFixedPoint/vanishing close lane (bridge lane)

hbridge closure = the `hlin` routing for this file (task 1). The corollary's
`hbridge` slot (`hbridge ⇐ chart_bridge` modulo `hlin`, L-HLIN) needs only the
finrank equation, so finrank rewire is chosen (same reason as in `Counting`:
shorter than `Classical.choice` from
`Elimination.chart_bridge_equiv_of_final`): `hbridge_of_final` below closes
it unconditionally on exactly `[hG, hreg, hZd]`, via `chart_bridge_of_final`
at the `stab_align` bound (`totalDegree` unfolds to the section finrank by
`rfl`). This also supersedes the `BridgeToFixedPoint.CountAssembly.hbridge_of_hlin`
route (cited by name) for equation consumers.

hfilter closure (task 2 — this file). `hfilter_fsec_of_final` instantiates
both theorems' `hfilter` at `F := Fsec`: `hstab` by `cfsec_stab_section`,
`hvan` by `fsec_vanishing_of_stabAbove` with `hdisjAbove` from
`hdisj_full_of_quadrics` (lattice bridge + `CfsecDisjointData` closure),
assembled by `cfsec_hfilter` — unconditional on exactly `[hreg, hZd, hG]`.

End-to-end narrowings: `bezout_quadratic_fsec_final` (conditional-exact
`[H, hH0, hSES, hSEC-at-Fsec]`, the numerical leaves L-R2/L-R1/L-FILT-num)
and `exists_another_point_fsec_final` (conditional-exact
`[hc, hmult, H, hH0, hSES, hSEC-at-Fsec, hfin, hsum, hpos]`).

No `Counting` import (would cycle: `Counting → ResultantLemmas → Statement`);
the bridge chain is inlined from `HilbertFunctionCount`/`Elimination` lemmas.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The `hfilter` input at `F := Fsec` from Statement's own hypotheses
(`hstab` by `cfsec_stab_section`; `hvan` by `fsec_vanishing_of_stabAbove`
with `hdisjAbove` from `hdisj_full_of_quadrics`; assembled by
`cfsec_hfilter`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_stab_section`,
  `Appendix_FixedPoint.BezoutChain.fsec_vanishing_of_stabAbove`,
  `Appendix_FixedPoint.BezoutChain.hdisj_full_of_quadrics`,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`,
  `Appendix_FixedPoint.BezoutChain.Fsec`. -/
theorem hfilter_fsec_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K G ℓ d) ∧
      ∀ d, B < d → Fsec n K G ℓ d = 0 := by
  have hfinSec := section_finite_of_artinian n K G ℓ hreg hZd
  obtain ⟨B, hstab⟩ := cfsec_stab_section n K G ℓ hreg hZd
  have hvan : ∀ d, B < d → Fsec n K G ℓ d = 0 :=
    fsec_vanishing_of_stabAbove n K G ℓ B hstab
      (fun d _ => hdisj_full_of_quadrics n K G ℓ hG d)
  exact cfsec_hfilter n K G ℓ B
    (fun d _ => hdisj_full_of_quadrics n K G ℓ hG d) hstab hvan

/-- The `hbridge` slot (`finrank chart = totalDegree`) from Statement's own
hypotheses, with no `hlin`: `chart_bridge_of_final` at the `stab_align`
bound (`Cfsec` section side via the SES step + `hS0_of_hG`; chart side via
`chartStab_of_hvan` with `hvan` closed as in `hfilter_fsec_of_final`).
`totalDegree` unfolds to the section finrank by `rfl`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge_of_final`,
  `Appendix_FixedPoint.BezoutChain.chartStab_of_hvan`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.stab_align`,
  `Appendix_FixedPoint.BezoutChain.cfsec_zero`, `Appendix_FixedPoint.BezoutChain.cfsec_succ`,
  `Appendix_FixedPoint.BezoutChain.hS0_of_hG`,
  `Appendix_FixedPoint.BezoutChain.cfsec_stab_section`,
  `Appendix_FixedPoint.BezoutChain.fsec_vanishing_of_stabAbove`,
  `Appendix_FixedPoint.BezoutChain.hdisj_full_of_quadrics`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.totalDegree`.
* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `Submodule.finrank_sup_add_finrank_inf_eq`.
* `Mathlib/Order/Disjoint.lean`, `disjoint_iff_inf_le`.
* `Mathlib/LinearAlgebra/Dimension/Finite.lean`, `finrank_bot`. -/
theorem hbridge_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    Module.finrank K (chartRing n K G ℓ) = totalDegree n K G ℓ := by
  have hfinSec := section_finite_of_artinian n K G ℓ hreg hZd
  obtain ⟨B, hstabS⟩ := cfsec_stab_section n K G ℓ hreg hZd
  have hvanS : ∀ d, B < d → Fsec n K G ℓ d = 0 :=
    fsec_vanishing_of_stabAbove n K G ℓ B hstabS
      (fun d _ => hdisj_full_of_quadrics n K G ℓ hG d)
  obtain ⟨D, hstabC⟩ := chartStab_of_hvan n K G ℓ B hG hreg
    (fun d hd => hvanS d hd)
  obtain ⟨B', hC', hS'⟩ := stab_align n K G ℓ B D hstabS hstabC
  have hCstep : ∀ d, d ≤ B' → Module.finrank K ↥(Cfsec n K G ℓ (d + 1))
      = Module.finrank K ↥(Cfsec n K G ℓ d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d) := by
    intro d hd
    have hstep := Submodule.finrank_sup_add_finrank_inf_eq
      (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d)
    have hinf : Cfsec n K G ℓ d ⊓ sectionPiece n K G ℓ d = ⊥ :=
      le_antisymm (disjoint_iff_inf_le.mp
        (hdisj_full_of_quadrics n K G ℓ hG d)) bot_le
    rw [hinf, finrank_bot, add_zero] at hstep
    rw [cfsec_succ]
    exact hstep
  exact chart_bridge_of_final n K G ℓ B' hreg hG hC'
    (Cfsec n K G ℓ) (cfsec_zero n K G ℓ) hS' hCstep
    (hS0_of_hG n K G ℓ hG)

/-- `bezout_quadratic` at `F := Fsec` with `hfilter` closed.
Conditional on exactly `[H, hH0, hSES, hSEC-at-Fsec]` (numerical leaves).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.bezout_quadratic`,
  `Appendix_FixedPoint.BezoutChain.hfilter_fsec_of_final` (this module). -/
theorem bezout_quadratic_fsec_final (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (H : ℕ → ℕ → ℕ)
    (hH0 : ∀ d, H 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d)
    (hSEC : ∀ d,
      Fsec n K G ℓ d + (if 1 ≤ d then H (n + 1) (d - 1) else 0)
        = H (n + 1) d) :
    totalDegree n K G ℓ = 2 ^ (n + 1) :=
  bezout_quadratic n K G hG ℓ hreg hZd H (Fsec n K G ℓ) hH0 hSES hSEC
    (hfilter_fsec_of_final n K G ℓ hreg hZd hG)

/-- `exists_another_point_of_smooth_point` at `F := Fsec` with `hfilter` and
`hbridge` closed (no `hlin`).
Conditional on exactly
`[hc, hmult, H, hH0, hSES, hSEC-at-Fsec, hfin, hsum, hpos]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point`,
  `Appendix_FixedPoint.BezoutChain.hfilter_fsec_of_final`,
  `Appendix_FixedPoint.BezoutChain.hbridge_of_final` (this module). -/
theorem exists_another_point_fsec_final (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hmem : distinguishedPoint n K ∈ vanishingLocus n K G)
    (hsmooth : IsSmoothPoint n K G (distinguishedPoint n K))
    (hmult : localPointMultiplicity n K G ℓ hc (distinguishedPoint n K) = 1)
    (H : ℕ → ℕ → ℕ)
    (hH0 : ∀ d, H 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d)
    (hSEC : ∀ d,
      Fsec n K G ℓ d + (if 1 ≤ d then H (n + 1) (d - 1) else 0)
        = H (n + 1) d)
    (hfin : (vanishingLocus n K G).Finite)
    (hsum : ∑ p ∈ hfin.toFinset, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ))
    (hpos : ∀ p ∈ hfin.toFinset, 1 ≤ localPointMultiplicity n K G ℓ hc p) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K G ∧ q ≠ distinguishedPoint n K :=
  exists_another_point_of_smooth_point n K G hG ℓ hc hreg hZd hmem hsmooth hmult
    H (Fsec n K G ℓ) hH0 hSES hSEC
    (hfilter_fsec_of_final n K G ℓ hreg hZd hG) hfin hsum
    (hbridge_of_final n K G ℓ hG hreg hZd) hpos

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
