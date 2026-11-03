/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MacaulayTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeUnmixedBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KernelChain
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Geometry.K2UnmixednessEndgame
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# `hunmixed_two`: per-prefix minimality at length 2, on the minimal-`d` residual

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `q : Fin 2 → R` carrying
successive SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`), and
`J = Ideal.span (Set.range q)`, this file is the formal address of rb-1
(the central crux): every `P ∈ Ass(R ⧸ J)` is minimal over `J`.

* `HunmixedTwoProp` — the unconditional goal statement (SPEC address).
* `hunmixed_two_of_hdimEqMin` — minimality over `J`, conditional-exact on
  `[HdimEqMinAtAss]`.
* `hunmixed_two_forall_of_hdimEqMin` — the `∀`-closed (consumer) shape.
* `height_le_two_of_hdimEqMin` — the `P.height ≤ 2` form, via the Krull
  direction (`HeightDrop.heightDrop_of_mem_minimalPrimes`).
* `hunmixed_two_iff_heightDropTwo` — `UnmixednessAtLengthTwo ↔ HeightDropResidualPair`
  (the `HeightDrop.heightDrop_iff_forall_mem_minimalPrimes` equivalence).

## Why minimal-`d` forms (read before extending this file)

The `Geometry/K2UnmixednessEndgame` endgame chains through universal hypotheses:
`HkerAtAss` (kernel triviality for every spanning family at every `d`) and
`HdimEqAtAss` (exact `gr`-Hilbert degree `d - 1` for every `d ≥ 2`).
Mathematical analysis (not formalized here): both universals are
over-strong to the point of falsehood.

* `HdimEqAtAss` demands exact degree `d - 1` simultaneously for all
  `d ≥ 2`. For `d` exceeding the embedding dimension `e` of `R_Q`, the
  true Hilbert polynomial (degree `e - 1`, eventually agreeing by
  Hilbert–Serre) is a degree-`≤ d - 1` competitor of degree `≠ d - 1`
  (e.g. `e = 0`: `Qw = 0` at `d = 2` demands `0 = 1`).
* `HkerAtAss` quantifies over all families: padding any spanning family
  with a zero generator preserves `hgen` but puts the corresponding
  variable in `ker polySurjResidue` (e.g. `e = 0`: `g = 0 : Fin 1 → R_Q`
  spans `⊥ = 𝔪` with `X₀ ∈ ker`).

Hence the universal chain can never ground: its hypotheses are
unprovable. The fix (this file): the only instances the Koszul chain
actually consumes are at minimal `d` (`d = spanFinrank 𝔪`):
`grlift_sop_exists` provides minimal sop data, and
`depthEqDimAt_of_r2Reduced` already threads the minimality equation `hd`.
The minimal forms `HkerMinAtAss` / `HdimEqMinAtAss` below are the true
statements at those instances, and the `d`-split re-runs with the
`d = 1` branch closed by minimality itself
(`ker_chain_hmin_one_of_sop` from `[hd, 1 ≤ d]` — no `hne` needed).

Contrast: the universal `HminOneAtAss` (`1 ≤ spanFinrank 𝔪` per Ass prime)
is true — it quantifies over no families — and is closed here
(`hminOneAtAss_uncond`) from the newly proved `hne` chain, discharging
the `KernelChain.lean` residual register item.

## What is proved here

* §1 `hne` chain (unconditional, first principles): `pair_J_ne_bot`
  (`J ≠ ⊥` from `MacaulayTwo.pair_fst_ne_zero`),
  `assPrime_ne_bot_of_J_ne_bot` (`Q ≠ ⊥` via
  `LocalUnmixed.assPrime_contains_span`), and
  `maximalIdeal_atPrime_ne_bot_of_ne_bot` (`𝔪(R_Q) ≠ ⊥`: a nonzero
  `t ∈ Q` maps into `𝔪` by `to_map_mem_maximal_iff` and stays nonzero
  by `IsLocalization.injective` over `primeCompl_le_nonZeroDivisors`).
  Assembled as `hne_pair_ass`, closing `hminOneAtAss_uncond`.
* §2 SPEC: `HkerMinAtAss`, `HdimEqMinAtAss` (minimal-`d` residuals) plus
  the specialization comparisons from the universal forms.
* §3 `hkerMinAtAss_of_hdimEqMin` (conditional-exact on `[hdimEqMin]`):
  the minimal `d`-split (`d = 0` via `hsAssemble_ker_eq_bot_zero`,
  `d = 1` via `ker_chain_ker_eq_bot_one` + `ker_chain_hmin_one_of_sop`,
  `d ≥ 2` via `ker_assemble_ker_eq_bot`).
* §4 `hdepth_of_hkerMin` (conditional-exact on `[hkerMin]`): per-prime
  `DepthEqDimAt` from minimal sop data (`grlift_sop_exists`,
  `depthEqDimAt_zero_of_sop`, `depthEqDimAt_of_r2Reduced` with the
  reused `BabyABPair.extBasisULift`).
* §5 masters (conditional-exact on `[hdimEqMin]`): `hunmixed_two_*`
  via the hbaby-closed `GradeUnmixedBridge.unmixed_of_chain_depth`
  fed with `GradeDepthFragment.gradeDropChain_of_successive`.
* §6 `hdimEqMinAtAss_d_one`: the `d = 1` exact-degree instance,
  unconditional (`d - 1 = 0` forces the conclusion by `omega`).
* §7 R1 reduction (unconditional bound + conditional-exact master):
  `singleDrop_grHilbert_isPolyGrowth` (gr-side `IsPolyGrowth` bound `d - 1`,
  via degree-bounded Hilbert–Serre + the R-2d′ bridge) and
  `hdimEqMin_of_hmultMin` (`HdimEqMinAtAss` from `HmultMinAtAss`).
* §8 R-2a′ (`dim gr(R_Q) = d` at minimal `d`, partial):
  `HdimGrMinAtAss` (SPEC) with `d = 0` / `d = 1` closed unconditionally
  (`hdimGrMinAtAss_d_zero/one`, via the closed kernel branches), the
  goal-strength iff `hdimGrMin_iff_hkerMin` (R-2a′ ↔ `HkerMinAtAss`),
  and masters `hdimGrMin_of_witnessMin` (conditional-exact on `[hwit]`,
  shared with R-2c′ — no new remainder) and `hdimGrMin_of_hgrdimMin`
  (conditional-exact on `[hgr]`, the §13 route).

## Precise narrowed remainder (out of scope)

`HmultMinAtAss` alone (`d = 1` closed unconditionally by
`hdimEqMinAtAss_d_one`, §6 — `d - 1 = 0` forces the conclusion): for
each `Q ∈ Ass(R ⧸ J)`, at minimal `d = spanFinrank 𝔪 ≥ 2`, the `(d-1)`-st
Newton difference of the `gr` Hilbert function does not vanish. By
`hsAssemble_hdimEq_of_not_vanishing` plus the unconditional §7 growth
bound, this is exactly equivalent to `HdimEqMinAtAss` (forward:
`hdimEqMin_of_hmultMin`; backward:
`hsAssemble_not_vanishing_of_hdimEq`). This is true (nonzero multiplicity
at `embdim`) and is the genuine crux: it needs R-2a′
(`dim gr(R_Q) = d` at minimal `d`, i.e. `dim gr = dim R_Q` for Noetherian
local rings, since `dim R_Q = embdim` is proved via regularity) plus R-2c′
(dimension-to-multiplicity: a `d`-dimensional graded quotient has Hilbert
polynomial of degree `d - 1` with nonzero leading coefficient), both absent
from Mathlib v4.34.0. Nothing else is assumed.

R-2a′ status (§8): `d = 0` and `d = 1` are closed unconditionally; at
`d ≥ 2`, R-2a′ is goal-strength (`hdimGrMin_iff_hkerMin`: equivalent to
`HkerMinAtAss`) and closes on the R-2c′ witness remainder alone
(`hdimGrMin_of_witnessMin` on `[HwitMinAtAss]`, via the §17 narrowing —
no independent R-2a′ remainder), or on `[HgrdimMinAtAss]`
(`hdimGrMin_of_hgrdimMin`, the §13 route). The outstanding work is R-2c′
proper (witness existence + dim-to-mult wiring to `singleDrop_grHilbert`).

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):
* `Regularity/Avoid/MacaulayTwo.lean`: `MacaulayTwo.pair_fst_ne_zero`.
* `Dimension/LocalUnmixed.lean`: `LocalUnmixed.assPrime_contains_span`.
* `Regularity/Grade/GradeDepthFragment.lean`: `gradeDropChain_of_successive`.
* `Regularity/Grade/GradeUnmixedBridge.lean`: `unmixed_of_chain_depth`.
* `Regularity/Unmixed/HeightDrop.lean`: `heightDrop_of_mem_minimalPrimes`,
  `heightDrop_iff_forall_mem_minimalPrimes`.
* `Regularity/Koszul/GradedLift.lean`: `grlift_sop_exists`.
* `Regularity/Rees/ReesAssembly.lean`:
  `depthEqDimAt_of_r2Reduced`, `depthEqDimAt_zero_of_sop`.
* `Regularity/Multiplicity/GradedSurjectionInjective.lean`: `hsAssemble_ker_eq_bot_zero`.
* `Regularity/Koszul/KernelChain.lean`:
  `ker_chain_ker_eq_bot_one`, `ker_chain_hmin_one_of_sop`,
  `ker_chain_one_le_spanFinrank_of_ne_bot` (+ residual register).
* `Regularity/Multiplicity/KernelAssembly.lean`: `ker_assemble_ker_eq_bot`.
* `Regularity/Multiplicity/HilbertSerre.lean` (§7):
  `hsQuotHilbert_isPolyGrowth` (degree-bounded Hilbert–Serre).
* `Regularity/Multiplicity/KernelAssembly.lean` (§1): `ker_assemble_ker_homogeneous`,
  `ker_assemble_grHilbert_eq_hsQuot` (R-2d′ bridge to `gr`-side).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean` (§10):
  `hsAssemble_hdimEq_of_not_vanishing`,
  `hsAssemble_not_vanishing_of_hdimEq` (`hdimEq ↔ hmult`).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean` (§13/§16/§17):
  `mult_dim_gr_eq_of_gr_lowerBound`, `mult_hle_gr_of_ker_eq_bot`,
  `mult_hle_gr_iff_ker_eq_bot`, `mult_hle_gr_of_witnessHyp`,
  `mult_dim_gr_eq_of_assocGradedDim` (R-2a′ collapse + narrowing).
* `Regularity/Koszul/AssociatedGradedRing.lean`: `grRegular`.
* `Geometry/K2UnmixednessEndgame.lean`: `HkerAtAss`, `HdimEqAtAss`, `HminOneAtAss`,
  `hminOneAtAss_of_ne_bot`, `extBasisULift` (all `BabyABPair`).

Mathlib v4.34.0 (all read-only):
* `IsLocalization.AtPrime.to_map_mem_maximal_iff`
  (`RingTheory/Localization/AtPrime/Basic.lean`).
* `IsLocalization.injective` (`RingTheory/Localization/Defs.lean`).
* `Ideal.primeCompl_le_nonZeroDivisors`
  (`RingTheory/Ideal/Operations.lean`).
* `Submodule.ne_bot_iff` (`Algebra/Module/Submodule/Lattice.lean`).

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hsucc : RegularityBridge.SuccessiveSMulRegular q` — successive SMul-regularity
  data on the pair `q : Fin 2 → R`.
* `hJ : J = Ideal.span (Set.range q)` — the spanned-ideal identification.
* `hQ : Q ∈ associatedPrimes _ (_ ⧸ J)` — Ass-membership of the prime.
* `hdimEqMin`/`hkerMin` (minimal-`d` residuals, plus `hwit`/`hgr` routes) —
  the routine conditional inputs of the masters (GRADE stays per-decl).
* Instances: `[Field K]` throughout; `[Q.IsPrime]` on Ass primes;
  `[IsDomain R]` in the §1 `hne` chain.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace UnmixednessAtLengthTwo

/-! ## §1. The `hne` chain: `𝔪(R_Q) ≠ ⊥` per Ass prime (unconditional) -/

/-- `J ≠ ⊥` for a successive pair: the first generator is nonzero
(`MacaulayTwo.pair_fst_ne_zero`) and lies in `J`. Discharges the
`J ≠ ⊥` third of the `KernelChain.lean` register.
-/
theorem pair_J_ne_bot (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q)) :
    J ≠ ⊥ := by
  have hf0 : q ⟨0, by omega⟩ ≠ 0 := MacaulayTwo.pair_fst_ne_zero hsucc
  intro hJbot
  have hfJ : q ⟨0, by omega⟩ ∈ J :=
    hJ ▸ Ideal.subset_span (Set.mem_range_self _)
  rw [hJbot] at hfJ
  exact hf0 (Ideal.mem_bot.mp hfJ)

/-- Associated primes over a nonzero ideal are nonzero: `J ≤ Q`
(`LocalUnmixed.assPrime_contains_span`) pushes `Q = ⊥` down to `J`.
-/
theorem assPrime_ne_bot_of_J_ne_bot {R : Type*} [CommRing R]
    (J : Ideal R) (hJ : J ≠ ⊥)
    (Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ associatedPrimes R (R ⧸ J)) :
    Q ≠ ⊥ := by
  intro hQbot
  have hle : J ≤ Q := LocalUnmixed.assPrime_contains_span J Q hQ
  rw [hQbot] at hle
  exact hJ (le_bot_iff.mp hle)

/-- The maximal ideal of `R_Q` is nonzero for `Q ≠ ⊥` over a domain: a
nonzero `t ∈ Q` maps into `𝔪` (`to_map_mem_maximal_iff`) and stays
nonzero (`IsLocalization.injective` over
`primeCompl_le_nonZeroDivisors`). Discharges the
`(Q ≠ ⊥ → 𝔪(R_Q) ≠ ⊥)` third of the `KernelChain.lean` register
(the `J ≤ Q` third is `LocalUnmixed.assPrime_contains_span`).
-/
theorem maximalIdeal_atPrime_ne_bot_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    (Q : Ideal R) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥ := by
  obtain ⟨t, htQ, ht0⟩ := (Submodule.ne_bot_iff Q).mp hQ
  have hmem : algebraMap R (Localization.AtPrime Q) t ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q t).mpr
      htQ
  have hne : algebraMap R (Localization.AtPrime Q) t ≠ 0 := by
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime Q)) :=
      IsLocalization.injective (Localization.AtPrime Q)
        Q.primeCompl_le_nonZeroDivisors
    have h0 : algebraMap R (Localization.AtPrime Q) t ≠
        algebraMap R (Localization.AtPrime Q) 0 :=
      fun h => ht0 (hinj h)
    simpa using h0
  intro hbot
  rw [hbot] at hmem
  exact hne (Ideal.mem_bot.mp hmem)

/-- Universal `hne` over `Ass(R ⧸ J)` for a successive pair: assembly of
the three register thirds.
-/
theorem hne_pair_ass (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥ :=
  maximalIdeal_atPrime_ne_bot_of_ne_bot Q
    (assPrime_ne_bot_of_J_ne_bot J (pair_J_ne_bot m K q hsucc J hJ) Q hQ)

/-- Universal `HminOneAtAss` closed for a successive pair: the
`KernelChain.lean` register item, discharged by feeding
`hne_pair_ass` into `BabyABPair.hminOneAtAss_of_ne_bot`.
-/
theorem hminOneAtAss_uncond (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q)) :
    BabyABPair.HminOneAtAss m K J :=
  BabyABPair.hminOneAtAss_of_ne_bot m K J (hne_pair_ass m K q hsucc J hJ)

#print axioms pair_J_ne_bot
#print axioms assPrime_ne_bot_of_J_ne_bot
#print axioms maximalIdeal_atPrime_ne_bot_of_ne_bot
#print axioms hne_pair_ass
#print axioms hminOneAtAss_uncond

/-! ## §2. Minimal-`d` residuals (SPEC) -/

/-- Universal `hker` over `Ass(R ⧸ J)` at minimal `d` only: for every
associated prime `Q` and every spanning family with `d = spanFinrank 𝔪`,
the poly-surjection kernel is trivial. This is the true statement the
Koszul chain consumes (cf. the module docstring on why the universal
`BabyABPair.HkerAtAss` is over-strong).

Specification (Prop address for the minimal kernel hypothesis). -/
def HkerMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
      RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen) = ⊥

/-- Universal `hdimEq` over `Ass(R ⧸ J)` at minimal `d ≥ 2` only: in the
exact `ker_assemble_ker_eq_bot` hyp shape
(`KernelAssembly.lean`), with the minimality side condition
`d = spanFinrank 𝔪`. This is the true exact-degree statement (exact
degree `embdim - 1`) and the sole remainder of §5.

Specification (Prop address for the minimal dim-equality hypothesis). -/
def HdimEqMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
    2 ≤ d →
      ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ d - 1 →
        (fun n => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] NewtonDifferences.evalFun Qw →
        Qw.natDegree = d - 1

/-- The universal `HkerAtAss` specializes to the minimal form (dropping
the minimality argument). Documents that `HkerMinAtAss` is weaker.
-/
theorem hkerMin_of_hker (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hker : BabyABPair.HkerAtAss m K J) :
    HkerMinAtAss m K J :=
  fun Q _ hQ _d g hgen _ => hker Q hQ g hgen

/-- The universal `HdimEqAtAss` specializes to the minimal form.
Documents that `HdimEqMinAtAss` is weaker (and, unlike the universal,
true — see the module docstring).
-/
theorem hdimEqMin_of_hdimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hdimEq : BabyABPair.HdimEqAtAss m K J) :
    HdimEqMinAtAss m K J :=
  fun Q _ hQ _d _ hd2 => hdimEq Q hQ hd2

#print axioms hkerMin_of_hker
#print axioms hdimEqMin_of_hdimEq

/-! ## §3. Minimal `d`-split: `HkerMinAtAss` from `HdimEqMinAtAss` -/

/-- Minimal `d`-split discharge of `HkerMinAtAss`: `d = 0` closed via
`hsAssemble_ker_eq_bot_zero` , `d = 1` closed via
`ker_chain_ker_eq_bot_one`  with `hmin` supplied by minimality
itself (`ker_chain_hmin_one_of_sop` from `[hd, 1 ≤ d]` — no `hne`
needed), `d ≥ 2` via `ker_assemble_ker_eq_bot`  on `[hdimEq]`
in exact M3-conclusion shape.

Conditional on exactly `[hdimEq]`. -/
theorem hkerMinAtAss_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : HdimEqMinAtAss m K J) :
    HkerMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  cases d with
  | zero =>
    exact GradedSurjectionInjective.hsAssemble_ker_eq_bot_zero Q g hgen
  | succ n =>
    cases n with
    | zero =>
      exact KernelChain.ker_chain_ker_eq_bot_one Q g hgen
        (KernelChain.ker_chain_hmin_one_of_sop Q _ g hgen hdmin (by omega))
    | succ k =>
      have hd2 : 2 ≤ k + 2 := by omega
      exact KernelAssembly.ker_assemble_ker_eq_bot Q (k + 2) g hgen
        hd2 (hdimEq Q hQ hdmin hd2)

#print axioms hkerMinAtAss_of_hdimEqMin

/-! ## §4. `DepthEqDimAt` from minimal `hker` -/

/-- Per-prime `DepthEqDimAt` from minimal local `hker`: sop data from
`grlift_sop_exists` (minimal by construction), then `d = 0` via
`depthEqDimAt_zero_of_sop` and `d ≥ 1` via `depthEqDimAt_of_r2Reduced`
with `BabyABPair.extBasisULift` (`1 ≤ d` by `omega` from the case
split). The minimality equation `hd` feeds both the R2Reduced master
and the minimal `hker`.

Conditional on exactly `[hkerQ]`. -/
theorem depthEqDimAt_of_hkerMin_atPrime (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hkerQ : ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
      RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen) = ⊥) :
    GradeDepthFragment.DepthEqDimAt m K Q := by
  obtain ⟨d, g, hgen, hd⟩ := GradedLift.grlift_sop_exists Q
  by_cases hd0 : d = 0
  · subst hd0
    exact ReesAssembly.depthEqDimAt_zero_of_sop m K Q g hgen
  · have hd1 : 1 ≤ d := by omega
    exact ReesAssembly.depthEqDimAt_of_r2Reduced m K Q
      (BabyABPair.extBasisULift (Localization.AtPrime Q) d) g hgen hd
      (hkerQ g hgen hd) hd1

/-- Universal `hdepth` from `HkerMinAtAss`: specialization of the per-prime
discharge to each `Q ∈ Ass(R ⧸ J)`.

Conditional on exactly `[hker]`. -/
theorem hdepth_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  depthEqDimAt_of_hkerMin_atPrime m K Q (hker Q hQ)

#print axioms depthEqDimAt_of_hkerMin_atPrime
#print axioms hdepth_of_hkerMin

/-! ## §5. Masters: `hunmixed_two` on `[hdimEqMin]` -/

/-- Rb-1 goal statement (SPEC address): every `P ∈ Ass(R ⧸ J)` for a
successive-regular pair is minimal over `J`. -/
def HunmixedTwoProp (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (_hJ : J = Ideal.span (Set.range q)) : Prop :=
  ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    P ∈ associatedPrimes _ (_ ⧸ J) → P ∈ J.minimalPrimes

/-- Per-prime minimality over `J` from `HdimEqMinAtAss`: one-line
application of the hbaby-closed `GradeUnmixedBridge.unmixed_of_chain_depth`
 at `k := 2`, fed with the closed chain
(`GradeDepthFragment.gradeDropChain_of_successive`) and `hdepth_of_hkerMin` on the
§3 discharge.

Conditional on exactly `[hdimEq]`. -/
theorem hunmixed_two_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdimEq : HdimEqMinAtAss m K J) :
    P ∈ J.minimalPrimes :=
  GradeUnmixedBridge.unmixed_of_chain_depth m K q hsucc J hJ P hP
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc)
    (hdepth_of_hkerMin m K J (hkerMinAtAss_of_hdimEqMin m K J hdimEq))

/-- `∀`-closed (consumer) shape: `HunmixedTwoProp` from `HdimEqMinAtAss`.

Conditional on exactly `[hdimEq]`. -/
theorem hunmixed_two_forall_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdimEq : HdimEqMinAtAss m K J) :
    HunmixedTwoProp m K q hsucc J hJ :=
  fun P _ hP => hunmixed_two_of_hdimEqMin m K q hsucc J hJ P hP hdimEq

/-- Height `≤ 2` form from `HdimEqMinAtAss`: the Krull direction
(`HeightDrop.heightDrop_of_mem_minimalPrimes`) applied to the per-prime
minimality above.

Conditional on exactly `[hdimEq]`. -/
theorem height_le_two_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdimEq : HdimEqMinAtAss m K J) :
    P.height ≤ ((2 : ℕ) : ℕ∞) :=
  HeightDrop.heightDrop_of_mem_minimalPrimes m K q J hJ P
    (hunmixed_two_of_hdimEqMin m K q hsucc J hJ P hP hdimEq)

/-- `HunmixedTwoProp` is the `k = 2` height-drop residual: the
`HeightDrop.heightDrop_iff_forall_mem_minimalPrimes` equivalence.
-/
theorem hunmixed_two_iff_heightDropTwo (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q)) :
    HunmixedTwoProp m K q hsucc J hJ ↔
      HeightDrop.HeightDropResidualPair m K q hsucc J hJ := by
  unfold HunmixedTwoProp HeightDrop.HeightDropResidualPair
  exact (HeightDrop.heightDrop_iff_forall_mem_minimalPrimes m K q hsucc J hJ).symm

#print axioms hunmixed_two_of_hdimEqMin
#print axioms hunmixed_two_forall_of_hdimEqMin
#print axioms height_le_two_of_hdimEqMin
#print axioms hunmixed_two_iff_heightDropTwo

/-! ## §6. `hdimEq` at `d = 1` (unconditional) -/

/-- Universal `hdimEq` over `Ass(R ⧸ J)` at `d = 1`, unconditional: with
`d - 1 = 0`, the degree bound `Qw.natDegree ≤ 0` already forces the
conclusion `Qw.natDegree = 0` (`omega` alone) — the eventual-equality
hypothesis is unused and no Hilbert theory enters. Stated in the exact
`HdimEqMinAtAss` binder shape at `d = 1`, so the R1 register is `d ≥ 2`
only (no in-tree consumer: the `d = 1` kernel branch closes via
`ker_chain_ker_eq_bot_one`, §3).
-/
theorem hdimEqMinAtAss_d_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ 1 - 1 →
      (fun n => ((SingleDropRegularity.singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] NewtonDifferences.evalFun Qw →
      Qw.natDegree = 1 - 1 := by
  intro Q _ _ Qw hle _
  omega

#print axioms hdimEqMinAtAss_d_one

/-! ## §7. Degree-bounded `gr` growth + `HdimEqMinAtAss` from multiplicity -/

/-- `gr`-side degree-bounded growth: the `gr` Hilbert function at `P` has
`IsPolyGrowth` bound `d - 1` for any ambient `d` with spanning data, via
the degree-bounded Hilbert–Serre theorem (`hsQuotHilbert_isPolyGrowth`)
transported along the R-2d′ bridge
(`ker_assemble_grHilbert_eq_hsQuot`, with `ker` homogeneous by
`ker_assemble_ker_homogeneous`).
-/
theorem singleDrop_grHilbert_isPolyGrowth (m : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    NewtonDifferences.IsPolyGrowth (fun n => ((SingleDropRegularity.singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ)) (d - 1) := by
  obtain ⟨Pgr, hdeg, hPgr⟩ := HilbertSerre.hsQuotHilbert_isPolyGrowth
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d
    (RingHom.ker (GradedSurjection.polySurjResidue P d g hgen))
    (KernelAssembly.ker_assemble_ker_homogeneous P d g hgen)
  refine ⟨Pgr, hdeg, ?_⟩
  have hfun : (fun n => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      = (fun n => ((HilbertSerre.hsQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (GradedSurjection.polySurjResidue P d g hgen)) n : ℕ) : ℚ)) := by
    funext n
    rw [KernelAssembly.ker_assemble_grHilbert_eq_hsQuot P d g hgen n]
  rw [hfun]
  exact hPgr

/-- Multiplicity-nonvanishing at minimal `d ≥ 2`: the `(d-1)`-st Newton
difference of the `gr` Hilbert function does not vanish. By
`hsAssemble_hdimEq_of_not_vanishing` + the unconditional degree-bounded
growth above, this is exactly equivalent to `HdimEqMinAtAss` (forward:
`hdimEqMin_of_hmultMin`; backward: `hsAssemble_not_vanishing_of_hdimEq`).
This is the sole remainder of §5: R-2c′ is closed (`DimensionToMultiplicity`,
exact on `HgrDimEqMinAtAss`); live remainder is R-2a′ (`dim gr = d`, §8).

Specification (Prop address for the minimal multiplicity hypothesis). -/
def HmultMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
    2 ≤ d →
      ¬ NewtonDifferences.seqDiff (d - 1) (fun n => ((SingleDropRegularity.singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0

/-- `HdimEqMinAtAss` from multiplicity-nonvanishing: per-`Q` minimal spanning
data (`grlift_sop_exists`) feeds the unconditional gr-side growth bound into
`hsAssemble_hdimEq_of_not_vanishing`.

Conditional on exactly `[hmult]`. -/
theorem hdimEqMin_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultMinAtAss m K J) :
    HdimEqMinAtAss m K J := by
  intro Q _ hQ d hdmin hd2 Qw hle hag
  obtain ⟨d', g, hgen, hd'⟩ := GradedLift.grlift_sop_exists Q
  have heq : d' = d := hd'.trans hdmin.symm
  have hF : NewtonDifferences.IsPolyGrowth
      (fun n => ((SingleDropRegularity.singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ)) (d - 1) := by
    have hF' := singleDrop_grHilbert_isPolyGrowth m K Q d' g hgen
    rwa [heq] at hF'
  exact GradedSurjectionInjective.hsAssemble_hdimEq_of_not_vanishing hF
    (hmult Q hQ hdmin hd2) Qw hle hag

#print axioms singleDrop_grHilbert_isPolyGrowth
#print axioms hdimEqMin_of_hmultMin

/-! ## §8. R-2a′: `dim gr(R_Q) = d` at minimal `d` (partial)

R-2a′ is the first half of the `HmultMinAtAss` crux split: for each
`Q ∈ Ass(R ⧸ J)`, at minimal `d = spanFinrank 𝔪(R_Q)`, the Krull dimension
of the associated graded ring `grRegular Q` equals `d`.

Status proved here:

* `HdimGrMinAtAss` (SPEC): the precise Prop address.
* `hdimGrMinAtAss_d_zero` / `hdimGrMinAtAss_d_one` (unconditional): the
  `d = 0` / `d = 1` instances, via the already-closed kernel branches
  (`hsAssemble_ker_eq_bot_zero`, `ker_chain_ker_eq_bot_one` on
  `ker_chain_hmin_one_of_sop`) fed into the workhorse
  `dimGr_eq_of_ker_eq_bot_atPrime` (`ker = ⊥ → dim gr = d`, from the §17
  collapse direction plus the unconditional upper bound).
* `hdimGrMin_iff_hkerMin` (unconditional iff): R-2a′ holds iff
  `HkerMinAtAss` holds — R-2a′ is goal-strength (proving it outright is
  proving the §3 kernel conclusion), so no unconditional proof at `d ≥ 2`
  exists below the strength of `ker = ⊥` itself.
* `hdimGrMin_of_witnessMin` (conditional-exact on `[hwit]`): the master —
  `d ≤ 1` unconditional, `d ≥ 2` via `mult_hle_gr_of_witnessHyp` (§17
  narrowing). R-2a′ adds no new remainder beyond R-2c′ (`HwitMinAtAss`).
* `hdimGrMin_of_hgrdimMin` (conditional-exact on `[hgr]`): the §13 route —
  same `d`-split with `d ≥ 2` via `mult_dim_gr_eq_of_assocGradedDim`
  (`hmin` discharged by the minimality equation).

Precise remainder: `HwitMinAtAss` (the R-2c′ Hilbert-witness side data at
minimal `d ≥ 2`, in exact `mult_hle_gr_of_witnessHyp` shape) — shared with
R-2c′, plus R-2c′ proper (the witness existence + dim-to-mult wiring to
`singleDrop_grHilbert`, out of scope for this section).
-/

/-- R-2a′ SPEC: `dim gr(R_Q) = d` at minimal `d = spanFinrank 𝔪(R_Q)` for
every `Q ∈ Ass(R ⧸ J)`.

Specification (Prop address for the minimal gr-dimension hypothesis). -/
def HdimGrMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ringKrullDim (AssociatedGradedRing.grRegular Q) = d

/-- Workhorse: `ker = ⊥` gives `dim gr = d` (either `d`), via the collapse
direction (`mult_hle_gr_of_ker_eq_bot`) plus the unconditional upper bound
(`mult_dim_gr_eq_of_gr_lowerBound`).
-/
theorem dimGr_eq_of_ker_eq_bot_atPrime {m : ℕ} {K : Type*} [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hker : RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen) = ⊥) :
    ringKrullDim (AssociatedGradedRing.grRegular Q) = d :=
  MultiplicityNonvanishing.mult_dim_gr_eq_of_gr_lowerBound Q d g hgen
    (MultiplicityNonvanishing.mult_hle_gr_of_ker_eq_bot Q d g hgen hker)

/-- R-2a′ at `d = 0`, unconditional: minimal sop data
(`grlift_sop_exists`, transported to `Fin 0` by the minimality equation)
feeds `hsAssemble_ker_eq_bot_zero` into the workhorse.
-/
theorem hdimGrMinAtAss_d_zero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      d = 0 → ringKrullDim (AssociatedGradedRing.grRegular Q) = d := by
  intro Q _ _ d hdmin hd0
  subst hd0
  obtain ⟨d', g, hgen, hd'⟩ := GradedLift.grlift_sop_exists Q
  have heq : d' = 0 := hd'.trans hdmin.symm
  subst heq
  exact dimGr_eq_of_ker_eq_bot_atPrime Q 0 g hgen
    (GradedSurjectionInjective.hsAssemble_ker_eq_bot_zero Q g hgen)

/-- R-2a′ at `d = 1`, unconditional: minimal sop data (transported to
`Fin 1`) feeds `ker_chain_ker_eq_bot_one` — with `hmin` supplied by
minimality itself (`ker_chain_hmin_one_of_sop`, no `hne` needed) — into
the workhorse.
-/
theorem hdimGrMinAtAss_d_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      d = 1 → ringKrullDim (AssociatedGradedRing.grRegular Q) = d := by
  intro Q _ _ d hdmin hd1
  subst hd1
  obtain ⟨d', g, hgen, hd'⟩ := GradedLift.grlift_sop_exists Q
  have heq : d' = 1 := hd'.trans hdmin.symm
  subst heq
  exact dimGr_eq_of_ker_eq_bot_atPrime Q 1 g hgen
    (KernelChain.ker_chain_ker_eq_bot_one Q g hgen
      (KernelChain.ker_chain_hmin_one_of_sop Q 1 g hgen hd' (by omega)))

/-- R-2a′ holds iff `HkerMinAtAss` holds (both directions unconditional):
forward via the §17 collapse (`mult_hle_gr_iff_ker_eq_bot`), backward via
minimal sop data into the workhorse. R-2a′ is goal-strength.
-/
theorem hdimGrMin_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimGrMinAtAss m K J ↔ HkerMinAtAss m K J := by
  constructor
  · intro hdim Q _ hQ d g hgen hdmin
    have hgr : ringKrullDim (AssociatedGradedRing.grRegular Q) = d := hdim Q hQ hdmin
    have hle : d ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) := by
      rw [hgr]
    exact (MultiplicityNonvanishing.mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle
  · intro hker Q _ hQ d hdmin
    obtain ⟨d', g, hgen, hd'⟩ := GradedLift.grlift_sop_exists Q
    have heq : d' = d := hd'.trans hdmin.symm
    subst heq
    exact dimGr_eq_of_ker_eq_bot_atPrime Q _ g hgen (hker Q hQ g hgen hdmin)

/-- R-2c′ remainder at minimal `d ≥ 2`, `∃`-closed over the spanning family:
some minimal spanning family admits Hilbert-witness side data
(`H`, `IsPolyGrowth`, `hwit`, `hdrop`) in the exact
`mult_hle_gr_of_witnessHyp` shape. By the §17 narrowing this single
remainder also closes R-2a′ (`hdimGrMin_of_witnessMin`).

Specification (Prop address for the minimal Hilbert-witness hypothesis). -/
def HwitMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
    2 ≤ d →
      ∃ (g : Fin d → Localization.AtPrime Q),
        ∃ (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
          ∃ (H : ℕ → ℕ),
            NewtonDifferences.IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1) ∧
            (∃ Pwit : Polynomial ℚ, Pwit.natDegree ≤ d - 1 ∧
              (fun n => ((MultiplicityNonvanishing.multQuotHilbert
                (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
                (RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen))
                (n + 1) : ℕ) : ℚ))
                =ᶠ[Filter.atTop] NewtonDifferences.evalFun Pwit ∧
              Pwit.coeff (d - 1) ≠ 0) ∧
            (RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen) ≠ ⊥ →
              ∃ Jloc : Ideal (Localization.AtPrime Q),
                (∀ Qm ∈ Jloc.minimalPrimes,
                  Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
                (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
                  (Localization.AtPrime Q ⧸ Jloc),
                  ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
                (∀ n, MultiplicityNonvanishing.multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
                  (RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen))
                  (n + 1) + H n = H (n + 1)) ∧
                NewtonDifferences.IsPolyGrowth (fun n => ((MultiplicityNonvanishing.multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
                  (RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen))
                  (n + 1) : ℕ) : ℚ)) (d - 1))

/-- R-2a′ master from the shared witness remainder: `d = 0` and `d = 1`
closed unconditionally (`hdimGrMinAtAss_d_zero/one`); `d ≥ 2` via
`mult_hle_gr_of_witnessHyp` (§17 narrowing) plus the unconditional upper
bound. R-2a′ adds no new remainder beyond R-2c′.

Conditional on exactly `[hwit]`. -/
theorem hdimGrMin_of_witnessMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitMinAtAss m K J) :
    HdimGrMinAtAss m K J := by
  intro Q _ hQ d hdmin
  cases d with
  | zero =>
    exact hdimGrMinAtAss_d_zero m K J Q hQ hdmin rfl
  | succ n =>
    cases n with
    | zero =>
      exact hdimGrMinAtAss_d_one m K J Q hQ hdmin rfl
    | succ k =>
      have hd2 : 2 ≤ k + 2 := by omega
      obtain ⟨g, hgen, H, hF, hwitQ, hdrop⟩ := hwit Q hQ hdmin hd2
      have hd_pos : 1 < k + 2 := by omega
      have hle := MultiplicityNonvanishing.mult_hle_gr_of_witnessHyp Q (k + 2) g hgen
        H hd_pos hF hwitQ hdrop
      exact MultiplicityNonvanishing.mult_dim_gr_eq_of_gr_lowerBound Q (k + 2) g hgen hle

/-- R-2a′ §13 remainder at Ass primes: `dim gr = dim R_Q` per `Q ∈ Ass`
(absent from Mathlib: associated-graded dimension theory). With minimality
(`dim R_Q = embdim`, proved via regularity) this gives R-2a′.

Specification (Prop address for the minimal gr-dimension-equality hypothesis). -/
def HgrdimMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ringKrullDim (AssociatedGradedRing.grRegular Q) =
      ringKrullDim (Localization.AtPrime Q)

/-- R-2a′ from the §13 remainder: `d ≤ 1` unconditional; `d ≥ 2` via
`mult_dim_gr_eq_of_assocGradedDim` on minimal sop data (`hmin` discharged
by the minimality equation).

Conditional on exactly `[hgr]`. -/
theorem hdimGrMin_of_hgrdimMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrdimMinAtAss m K J) :
    HdimGrMinAtAss m K J := by
  intro Q _ hQ d hdmin
  cases d with
  | zero =>
    exact hdimGrMinAtAss_d_zero m K J Q hQ hdmin rfl
  | succ n =>
    cases n with
    | zero =>
      exact hdimGrMinAtAss_d_one m K J Q hQ hdmin rfl
    | succ k =>
      obtain ⟨d', g, hgen, hd'⟩ := GradedLift.grlift_sop_exists Q
      have heq : d' = k + 2 := hd'.trans hdmin.symm
      subst heq
      exact MultiplicityNonvanishing.mult_dim_gr_eq_of_assocGradedDim Q (k + 2) g hgen
        (le_of_eq hd') (hgr Q hQ)

#print axioms dimGr_eq_of_ker_eq_bot_atPrime
#print axioms hdimGrMinAtAss_d_zero
#print axioms hdimGrMinAtAss_d_one
#print axioms hdimGrMin_iff_hkerMin
#print axioms hdimGrMin_of_witnessMin
#print axioms hdimGrMin_of_hgrdimMin

end UnmixednessAtLengthTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
