/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack

/-!
# I1: `hpiece` unconditional-bridge integration

Wiring only: the L2 `hpiece` discharge (`hpiece_discharge`,
`HilbertSamuelDegree.lean` §5, unconditional) is integrated through every
consumer of the HSDegree-§3 `[hpiece]` hypothesis. No new analytic
content; every restatement below is a real proved corollary.

## Consumer audit (evidence)

Repo-wide `grep -rln "hpiece|hsBridge_"` over `Formalization/` hits
exactly five files; of these only two consume the HSDegree-§3
`[hpiece]` hypothesis:

* `HilbertSamuelDegree.lean` itself: §5 already proves unconditional twins
  for all three §3 masters (`hsBridge_cumulative_unconditional`:717,
  `hsBridge_hs_eq_cumsum_unconditional`:726,
  `hsBridge_hs_exact_of_gr_exact_unconditional`:737). Nothing left
  to restate here; §1 below cites them, it does not duplicate them.
* `WitnessHighAttack.lean` §4: the `HhpieceD2AtAss` SPEC (:561) plus
  two adapter theorems taking `[hpiece]`
  (`highAttack_hsExactD2_of_hpiece_grExact`:595 on
  `[hpiece, hgrExact]`, `highAttack_hwitD2_of_hpiece_grExact_hsDeg`
  :630 on `[hpiece, hgrExact, hhsDeg]`). Both call sites (:608,:642)
  feed `hsBridge_hs_exact_of_gr_exact`. Discharged in §§1–2 below.
* `GradedSurjectionInjective.lean`: no `hpiece`/`hsBridge_` mentions and it
  does not import `HilbertSamuelDegree` (the import arrow points the other
  way: HSDegree imports HSAssemble). Its §4–§6 `R_P` masters
  (`hsAssemble_ker_eq_bot`, `..._of_dim`, `..._of_mult`,
  `..._of_principal`) consume gr-side data only. No `[hpiece]` legs;
  nothing to restate.
* `SingleDropRegularity.lean`: no `hpiece`/`hsBridge_` mentions and it
  does not import `HilbertSamuelDegree` (again the arrow is reversed:
  HSDegree §3 consumes SingleDrop's `hSES`/`hcomp`/growth masters as
  gr-side suppliers). No `[hpiece]` legs, direct or transitive;
  nothing to restate.
* `HilbertSerre.lean`, `HilbertWitnessNarrowing.lean`,
  `Geometry/HilbertFunctionCount.lean`: the `hpiece` hits there are unrelated
  local binders (different statements); none mentions `hsBridge_` or
  imports HSDegree-§3 shapes. No legs.

So the complete `[hpiece]`-leg set is: the three §3 masters (twins
already proved in §5) + the two HighAttack §4 joints (restated here).
No consumer file is edited.

## Status

* `hsIntegrate_hpieceD2AtAss`: unconditional.
* `hsIntegrate_hsExactD2_of_grExact`: conditional-exact on
  `[hgrExact]` only (the `[hpiece]` leg discharged).
* `hsIntegrate_hwitD2_of_grExact_hsDeg`: conditional-exact on
  `[hgrExact, hhsDeg]` only (the `[hpiece]` leg discharged).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace PieceIntegration

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences

/-! ## §1. The `HhpieceD2AtAss` SPEC holds unconditionally

Per-prime `hpiece` is exactly `hpiece_discharge` at the maximal ideal:
`hpiece_discharge (I) (n)` states `finLength R (grPiece R I n) =
singleDrop_grHilbert I n` for ANY ideal `I` over any `CommRing R`,
which is the body of `HhpieceD2AtAss` with `I := 𝔪_Q`. -/

/-- The L2-style `hpiece` address at embdim 2, discharged
unconditionally via the §5 supplier.
-/
theorem hsIntegrate_hpieceD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhpieceD2AtAss m K J := by
  intro Q _ hQ hemb i
  exact hpiece_discharge _ i

/-! ## §2. HighAttack §4 joints restated on the remaining legs only

Each joint below applies the original adapter to the discharged
§1 proof, dropping the `[hpiece]` hypothesis. Conclusions are
byte-identical to the originals. -/

/-- Per-prime HS exact degree 2 from gr-exact data alone (the
`[hpiece]` leg of `highAttack_hsExactD2_of_hpiece_grExact`
discharged via §1).

Conditional on exactly `[hgrExact]`. -/
theorem hsIntegrate_hsExactD2_of_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    [IsNoetherianRing (Localization.AtPrime Q)] :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  highAttack_hsExactD2_of_hpiece_grExact m K J
    (hsIntegrate_hpieceD2AtAss m K J) hgrExact Q hQ hemb

/-- `HwitD2AtAss` from gr-exact data plus the HS-degree residual (the
`[hpiece]` leg of `highAttack_hwitD2_of_hpiece_grExact_hsDeg`
discharged via §1).

Conditional on exactly `[hgrExact, hhsDeg]`. -/
theorem hsIntegrate_hwitD2_of_grExact_hsDeg (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hhsDeg : HhsDegLowerD2AtAss m K J) :
    HwitD2AtAss m K J :=
  highAttack_hwitD2_of_hpiece_grExact_hsDeg m K J
    (hsIntegrate_hpieceD2AtAss m K J) hgrExact hhsDeg

#print axioms hsIntegrate_hpieceD2AtAss
#print axioms hsIntegrate_hsExactD2_of_grExact
#print axioms hsIntegrate_hwitD2_of_grExact_hsDeg

/-! ## §3. Residual register: HS-chain masters, post-integration (doc-only)

unconditional (no hypotheses beyond ambient instances):

* `hsBridge_step` (§3 adic SES step — was already unconditional).
* `hsBridge_cumulative_unconditional` (§5:717).
* `hsBridge_hs_eq_cumsum_unconditional` (§5:726).
* `hpiece_discharge` / `hpiece_maximal` (§5:700/:709).
* `hsIntegrate_hpieceD2AtAss` (§1 above: the HighAttack SPEC).
* All of `GradedSurjectionInjective` §§1–14 masters and `SingleDropRegularity`
  §§1–12 masters to the extent previously graded (gr-side,
  `hpiece`-free throughout — verified by grep + import direction,
  not restated).

conditional-exact, `[hpiece]`-free remainders:

* `hsBridge_hs_exact_of_gr_exact_unconditional` (§5:737) on gr-side
  exact-degree data `[hF, hne]` only.
* `hsIntegrate_hsExactD2_of_grExact` (§2 above) on `[hgrExact]` only.
* `hsIntegrate_hwitD2_of_grExact_hsDeg` (§2 above) on
  `[hgrExact, hhsDeg]` only.

exact remainder (HS chain contributes no further closable piece):

* Gr-side exact-degree data (`[hF, hne]` / `HgrExactD2AtAss`:
  `IsPolyGrowth... 1` + first-difference nonvanishing) — the graded
  exact-degree lower bound, still open (needs homogeneous minimal
  primes / graded Noether normalization / finite-graded Hilbert
  comparison; HSDegree §4 register).
* `HhsDegLowerD2AtAss` (HS exact degree 2 forces the gr lower bound)
  — the open HS degree-theory step named in HighAttack §4.
* The `[hpiece]` hypothesis itself is extinct as a remainder: every
  former consumer now routes through an unconditional proof. No live
  theorem in the tree takes HSDegree-§3 `hpiece` as a hypothesis
  anymore (the §3 originals keep it only as superseded conditional
  forms alongside their §5 twins).
-/

end PieceIntegration
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
