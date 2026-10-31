/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Mathlib.Data.ENat.Monoid
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Height-drop residual for successive-regular families (grade/Koszul core)

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `q : Fin k → R` carrying
successive SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`), and
`J = Ideal.span (Set.range q)`, the exact step-(iv) residual
(`Regularity/Unmixed/CohenMacaulayFragment.lean`, roadblock ledger) is the upper height bound

> every `P ∈ associatedPrimes R (R ⧸ J)` satisfies `P.height ≤ k`

(here `k = 2`; the statement is uniform in `k`, and that uniformity is the
`k ≥ 3` core: one height-drop per prefix length). This file first reports the
route analysis, then records the proved content and the exact residual:

* §1 route report with API mapping (all `grep` run in
  `.lake/packages/mathlib`, `lean-toolchain` pins `v4.34.0`).
* §2 proved content: the general-`k` reduction
  (`localized_dim_zero_of_height_le`, generalizing
  `CohenMacaulayFragment.u2_dim_zero_of_height_le_two`), its minimality corollary
  (`minimal_of_height_le`), the `j = 0` / `j = 1` prefix instances
  (`assHeight_le_zero_of_successive_zero`,
  `assHeight_le_one_of_successive_singleton`), and the conditional assembly
  (`unmixed_of_heightDrop`) pinning the exact interface the residual must
  supply.
* §3 blocked verdict: the exact minimal missing statement
  (`HeightDropResidualAt`, with the `k = 2` alias `HeightDropResidualPair`)
  plus grep evidence. No placeholder proofs are used anywhere in this file.
* §4 Q+1 attempt: PrimeAvoidance-powered rung selection
  (`exists_nextRung_regular_of_avoid`, `exists_nextRung_mem_maximal_of_avoid`),
  the Krull-direction conditional (`heightDrop_of_mem_minimalPrimes`), and the
  weakest-hypothesis equivalence (`heightDrop_iff_forall_mem_minimalPrimes`:
  the residual is unmixedness-at-`k`). The unconditional `k = 2` close stays
  blocked (see §4 ledger): the selection feed's per-prime input has no source
  without minimality, and `GradeDepthFragment` cannot be imported (import cycle —
  `GradeDepthFragment.lean` imports this file).

## §1 route report

Target: `P.height ≤ 2` for `P ∈ Ass(R ⧸ J)`, `J` spanned by a length-2
successive-regular family (general-`k` form `P.height ≤ k` preferred).

Route R1 — grade/Koszul ladder. Missing. The natural content is
quotient-of-CM-by-regular + CM-implies-unmixed at the specific successive
quotients (equivalently grade-`2` forces height `2` for Ass primes), but:

* `Mathlib/RingTheory/Depth/` holds exactly one file, `Rees.lean`, whose only
  content is the Rees theorem (`ModuleCat.exists_isRegular_tfae`): regular
  sequences exist, no grade/depth-to-CM ladder.
* Koszul: `grep -rn "Koszul\|koszul" Mathlib/` has zero commutative-algebra
  hits (only the Levi-Civita formula in differential geometry, a limit remark
  in `Algebra/Homology/LocalCohomology.lean`, and the todo at
  `RingTheory/Regular/RegularSequence.lean`:
  "todo: Koszul regular sequences, `H_1`-regular sequences, quasi-regular
  sequences, depth").
* Status: `grep -rln "def grade" Mathlib/RingTheory/` is empty (only
  `GradedAlgebra` false positives).
* CM/unmixed: `grep -rn "CohenMacaulay" Mathlib/` ⟹ `0`; the only `Unmixed`
  hits are the unrelated `ComplexEmbedding.IsUnmixed` (see SPEC in
  `Regularity/Unmixed/CohenMacaulayFragment.lean`).

Route R2 — single-step dimension drop. Verified shape, insufficient.
`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`
(`Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean`):
`{r : R} (hr : r ∈ R⁰) ⊢ ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R`.
Already consumed by U2 step (iii) through the DVR drop
(`CohenMacaulayFragment.ringKrullDim_quotient_span_le_zero_of_dvr`). Its exact-equality
upgrades in `Mathlib/RingTheory/KrullDimension/Regular.lean` were all
inspected and all run the wrong way for an Ass upper bound:

* `ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors` (:130): needs a
  maximal-height prime containing `r`; yields global dimension equations.
* `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
  (:174): needs `[IsLocalRing R]` + maximal-ideal membership; yields
  `dim (R ⧸ span {x}) + 1 = dim R`.
* `supportDim_add_length_eq_supportDim_of_isRegular` /
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`: needs local
  Noetherian + `IsRegular` list; already consumed in-tree through
  `LocalUnmixed`/`RegularSequenceDimDrop` into `AssHeightBound.height_eq_add_of_span`
  (`↑height P = dim (R_P ⧸ J_P) + k`).
* `Ideal.height_le_ringKrullDim_quotient_add_one`
  (`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`):
  `p.height ≤ ringKrullDim (R ⧸ span {r}) + 1` for `r ∈ p` — upper-bound
  shaped but in the wrong ring (global quotient by one generator, no Ass
  input, no localization at `P` with the full ideal `J`).

Every one of these reproduces the circular equation `height = dim + k`
(which `AssHeightBound` already has); none converts Ass-membership into an
upper bound without already knowing minimality.

Route R3 — DVR-dimension induction lifting steps (i)–(iii). Blocked at
transfer. Steps (i)–(iii) land `R_Q` a DVR of dimension one plus
`dim (R_Q ⧸ span {q̄₁}) ≤ 0`; moving that zero to `R_P ⧸ J_P` needs a
quotient-localization iso or dim-monotonicity bridge, and
`grep -rn ringKrullDim Mathlib/RingTheory/Localization/` is empty (see
`CohenMacaulayFragment` ledger); the only nearby iso
(`IsLocalization.AtPrime.equivQuotientMapOfIsMaximal`) needs `P` maximal
above `p` (residue-field case — inapplicable since `J_P` maximal is the
goal); `ringKrullDim_le_of_surjective` (`KrullDimension/Basic.lean`) runs
`R_P ⧸ J_P → R_Q ⧸ J_Q`, i.e. against the needed bound.

Route R4 — catenary-upper. Absent. In-tree only the easy/sum half
`height_add_ringKrullDim_quotient_le`
(`Dimension/PolynomialCatenary.lean`):
`(P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) ≤ ringKrullDim R`.
That bounds `height P ≤ m - s` (`s` the normalization index); reaching
`≤ 2` would need `s ≥ m - 2` (a normalization-index lower bound for Ass
primes — unavailable) and the full equality is absent. Mathlib catenary:
`grep -rni "catenary" Mathlib/` ⟹ zero hits (case-insensitive). Accordingly,
no upper half is assumed below.

Route R5 — regular-element height drop in `R ⧸ (q₀)`. False in general.
`Dimension/LocalUnmixed.lean` module docstring records the verified-by-hand
counterexample (`k[a,b,c] ⧸ (ab, ac)` localized, regular `x = a + b`,
embedded Ass prime of height `2 ≠ 1`); the `k = 1` UFD argument
(`mem_minimalPrimes_of_successive_singleton`) cannot reapply after the first
quotient. Needs CM-ness of `R ⧸ (q₀)` — back to R1.

## §3 blocked verdict (see below)

All five routes bottom out at absent grade/Koszul/CM API (R1, R5), the
circular equation (R2), the missing transfer bridge (R3), or absent
catenary-upper plus a missing normalization lower bound (R4). The exact
minimal missing statement is `HeightDropResidualAt` (general `k`; the
`k = 2` alias `HeightDropResidualPair` is the U2 step-(iv) residual).
This report and the interface it specifies are recorded as the outcome for
the residual itself; everything provable around it is proved in §2. The Q+1
attempt (§4)
reduces the residual further to its weakest explicit hypothesis (an
equivalence with unmixedness-at-`k`) the PrimeAvoidance selection feed;
the unconditional close remains blocked per the §4 ledger.

## References

Project (read-only; never edited here):

* `Regularity/Unmixed/CohenMacaulayFragment.lean` (bare `BezoutChain` namespace):
  U1 + steps (i)–(iii)
  proved (`hasUniqueIrreducible_atPrime_height_one`, `u1_dvr_at_height_one`,
  `exists_height_one_minimal_le_of_successive_pair`,
  `dvr_at_height_one_le_of_successive_pair`,
  `ringKrullDim_quotient_span_le_zero_of_dvr`,
  `dim_dvr_quotient_le_zero_of_successive_pair`), height reduction
  (`u2_dim_zero_of_height_le_two`), roadblock ledger.
* `Regularity/Unmixed/Unmixedness.lean` (bare `Bezout` namespace):
  `mem_minimalPrimes_of_successive_zero`,
  `mem_minimalPrimes_of_successive_singleton`,
  `mem_minimalPrimes_of_localized_quotient_dim_zero` (consumed by
  `minimal_of_height_le`).
* `Regularity/Avoid/AssHeightBound.lean` (`AssHeightBound` namespace):
  `height_eq_add_of_span`, `le_height_of_span_of_successive`,
  `le_height_of_mem_associatedPrimes_of_successive` (used for orientation),
  `height_le_of_mem_minimalPrimes` (consumed by the `j = 0, 1` instances).
* `Dimension/LocalUnmixed.lean` (`LocalUnmixed` namespace):
  `assPrime_contains_span`, plus the `k[a,b,c] ⧸ (ab, ac)` counterexample
  (route R5 evidence — know what fails in general).
* `Regularity/Avoid/RegularityBridge.lean` (`RegularityBridge` namespace):
  `RegularityBridge.SuccessiveSMulRegular`.

Mathlib (all grep-verified, see §1):

* `RingTheory/KrullDimension/NonZeroDivisors.lean`
  (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`).
* `RingTheory/KrullDimension/Regular.lean,174`
  (exact-equality upgrades; insufficient per R2).
* `RingTheory/KrullDimension/Basic.lean`
  (`ringKrullDim_nonneg_of_nontrivial`)
  (`ringKrullDim_le_of_surjective`, wrong direction per R3).
* `RingTheory/Ideal/KrullsHeightTheorem.lean`
  (`Ideal.height_le_ringKrullDim_quotient_add_one`, wrong ring per R2).
* `RingTheory/Depth/Rees.lean` (only `ModuleCat.exists_isRegular_tfae`).
* `RingTheory/Regular/RegularSequence.lean` (Koszul todo).
* `Data/ENat/Monoid.lean`
  (`ENat.WithBot.add_le_add_natCast_right_iff`, cancellation below).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HeightDrop

/-- Exact residual at general prefix length `k`: every associated prime of
`R ⧸ J` (`J` spanned by a length-`k` successive-regular family) has height at
most `k`. This is the grade/Koszul core — the `k = 2` case is the U2
step-(iv) residual (`HeightDropResidualPair`), and the uniform-`k` form is
the `k ≥ 3` core (one height-drop per prefix length). Each prefix of a
successive family restricts to a successive family on the same pattern as
`CohenMacaulayFragment.singleton_successive_of_successive_pair`, so one statement per
prefix length is the right address. -/
def HeightDropResidualAt {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (_hJ : J = Ideal.span (Set.range q)) : Prop :=
  ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    P ∈ associatedPrimes _ (_ ⧸ J) → P.height ≤ (k : ℕ∞)

/-- The `k = 2` case: the exact U2 step-(iv) residual. By
`u2_dim_zero_of_height_le_two` + `unmixed_two_of_u2` (`CohenMacaulayFragment`), this single
inequality closes `k = 2` unmixedness. -/
def HeightDropResidualPair (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) : Prop :=
  HeightDropResidualAt m K q hsucc J hJ

/-- General-`k` height reduction, proved: the height upper bound implies the
localized dimension-zero equation. Generalizes
`CohenMacaulayFragment.u2_dim_zero_of_height_le_two` (same proof, `2` replaced by `k`):
the in-tree equation `AssHeightBound.height_eq_add_of_span`
(`↑height P = dim (R_P ⧸ J_P) + k`) plus the hypothesis cancel through
`ENat.WithBot.add_le_add_natCast_right_iff`; the lower bound on `dim` is
free (`ringKrullDim_nonneg_of_nontrivial`, since `J_P` sits below the
maximal ideal). -/
theorem localized_dim_zero_of_height_le {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hle : P.height ≤ (k : ℕ∞)) :
    ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) = 0 := by
  have hJP : Ideal.span (Set.range q) ≤ P := by
    rw [← hJ]
    exact LocalUnmixed.assPrime_contains_span J P hP
  have hH := AssHeightBound.height_eq_add_of_span q hsucc P hJP
  have hle0 : ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) ≤ 0 := by
    have hle' : ringKrullDim (Localization.AtPrime P ⧸
        Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
          (Localization.AtPrime P) ∘ q))) + ((k : ℕ) : WithBot ℕ∞) ≤
        0 + ((k : ℕ) : WithBot ℕ∞) := by
      rw [zero_add]
      have h1 : ((P.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast hle
      rw [hH] at h1
      exact h1
    exact ENat.WithBot.add_le_add_natCast_right_iff.mp hle'
  have hJPne : Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
      (Localization.AtPrime P) ∘ q)) ≠ ⊤ := by
    intro hcon
    have hmem : ∀ i, algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) (q i) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      intro i
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime P) P]
      exact hJP (Ideal.subset_span (Set.mem_range_self i))
    have hleM : Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
    rw [hcon] at hleM
    exact Ideal.IsMaximal.ne_top inferInstance (top_le_iff.mp hleM)
  have hge0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) :=
    @ringKrullDim_nonneg_of_nontrivial _ _
      (Ideal.Quotient.nontrivial_iff.mpr hJPne)
  exact le_antisymm hle0 hge0

/-- General-`k` minimality from the height bound, proved: the residual implies
hunmixedness at that prefix length, via
`mem_minimalPrimes_of_localized_quotient_dim_zero`
(`Regularity/Unmixed/Unmixedness.lean`). -/
theorem minimal_of_height_le {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hle : P.height ≤ (k : ℕ∞)) :
    P ∈ J.minimalPrimes :=
  mem_minimalPrimes_of_localized_quotient_dim_zero m k K q hsucc J hJ P hP
    (localized_dim_zero_of_height_le m K q hsucc J hJ P hP hle)

/-- Prefix length `j = 0`, proved: associated primes sit at height `0`.
Chains the proved `k = 0` minimality
(`mem_minimalPrimes_of_successive_zero`) with the Krull upper bound
(`AssHeightBound.height_le_of_mem_minimalPrimes`). -/
theorem assHeight_le_zero_of_successive_zero (m : ℕ) (K : Type*) [Field K]
    (q : Fin 0 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P.height ≤ 0 := by
  have hmin := mem_minimalPrimes_of_successive_zero m K q hsucc J hJ P hP
  have hle := AssHeightBound.height_le_of_mem_minimalPrimes q J hJ P hmin
  simpa using hle

/-- Prefix length `j = 1`, proved: associated primes sit at height `≤ 1`.
Chains the proved `k = 1` UFD minimality
(`mem_minimalPrimes_of_successive_singleton`) with the Krull upper bound.
This is the last prefix length whose height-drop goes through with Mathlib
v4.34.0; `j = 2` is the residual (route R5: the UFD argument cannot
reapply in `R ⧸ (q₀)`). -/
theorem assHeight_le_one_of_successive_singleton (m : ℕ) (K : Type*) [Field K]
    (q : Fin 1 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P.height ≤ 1 := by
  have hmin := mem_minimalPrimes_of_successive_singleton m K q hsucc J hJ P hP
  have hle := AssHeightBound.height_le_of_mem_minimalPrimes q J hJ P hmin
  simpa using hle

/-- Conditional assembly, proved: the residual at length `k` implies
hunmixedness at that length. Trivial as a proof; its value is
architectural — it pins the exact interface the grade/Koszul core must
supply so each prefix length has a formal address. -/
theorem unmixed_of_heightDrop {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdrop : HeightDropResidualAt m K q hsucc J hJ) :
    P ∈ J.minimalPrimes :=
  minimal_of_height_le m K q hsucc J hJ P hP (hdrop P hP)

/-!
# §4 Q+1 attempt ledger (PrimeAvoidance feed + weakest-hypothesis pin)

Goal: attempt the general-`k` residual with
`Regularity/Avoid/PrimeAvoidance.lean` (`exists_isSMulRegular_mem_of_forall_not_le_ass`,
`exists_mem_maximal_notMem`) and `Regularity/Grade/GradeDepthFragment.lean`
(`grade_quotIter_add_eq_grade`).

(1) PrimeAvoidance feed — proved below as `exists_nextRung_regular_of_avoid`
(global selection over `R ⧸ J`) and `exists_nextRung_mem_maximal_of_avoid`
(local maximal-ideal selection). Both are thin consumes (no rebuild) of
`PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass`; the global form
discharges `Module.Finite R (R ⧸ J)` via `Module.Finite.of_surjective` +
`Submodule.mkQ_surjective` (both already used in-tree at
`GradeDepthFragment.lean`, Mathlib v4.34.0).

(2) GradeDepthFragment equation — not imported, by necessity: `GradeDepthFragment.lean`
reads `import EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop`,
so importing
`GradeDepthFragment` here is an import cycle. The rung feed goes through the in-file
reduction instead (`localized_dim_zero_of_height_le` → `minimal_of_height_le`
→ `unmixed_of_heightDrop`), wired to the selection output by the equivalence
below.

(3) `k = 2` endgame — reduced, still blocked. Via
`heightDrop_iff_forall_mem_minimalPrimes`, the `k = 2` close is equivalent to
minimality of every `P ∈ Ass(R ⧸ J)` over the 2-generated `J`, i.e. to
`dim (R_P ⧸ J_P) = 0` (`mem_minimalPrimes_of_localized_quotient_dim_zero`).
The selection feed cannot supply this: its per-prime input
(`∀ P ∈ Ass, ¬ I ≤ P`) has no in-tree source without minimality already in
hand (circular), and the route-R5 counterexample (`LocalUnmixed`: regular
`x = a + b` on `k[a,b,c] ⧸ (ab, ac)` localized, embedded Ass prime of height
`2 ≠ 1`) witnesses that no general rung-selection + Krull argument can close
the gap — any proof must use CM-ness of `R ⧸ (q₀)`, i.e. precisely the
missing minimality. No counterexample to the residual itself was found
(the statement remains true for successive-regular families); the block is a
missing-input block, not a refutation.

Outcome grade: conditional (exact hypothesis list — minimality over `J`,
`∃`-free) for the residual implication in both directions;
blocked-with-evidence for the unconditional `k = 2` close.

Update (local rungs 0–1 closed; see `VariableInductionCM.lean` §4 ledger):
`varHeightDropResidualList_nil/singleton` +
`varUnmixedOneResidual_of_ne_zero` close the local length-0/1 height bounds
unconditionally (domain core + generic UFD replay, no transfer), so the
global↔local `k ≤ 1` correspondence is complete on both sides
(`assHeight_le_zero/one_of_successive_*` here). Remaining crux unified:
global `k = 2` (`HeightDropResidualPair`) and local length-2 per-prefix
minimality both reduce to unmixedness-at-length-2 for successive-regular
pairs (global: over `R`; local: over `R_P`) — same Macaulay content, i.e.
CM-ness of the first quotient. Both stay blocked per the ledger above;
narrowest next step unchanged (length-2 minimality; Koszul/AB forbidden,
from-scratch Macaulay-`k = 2` has no in-tree content).
-/

/-- Krull-direction conditional, proved (Q+1): minimality over
`J = span (Set.range q)` implies the height bound — with no regularity input
(`AssHeightBound.height_le_of_mem_minimalPrimes` is Krull's height theorem
for the finset `Finset.univ.image q`, card `≤ k`) and no Ass-membership input
(Ass plays no role in this direction; it is consumed only by the converse
`minimal_of_height_le`). This is the weakest explicit hypothesis for the
residual: one prime, one minimality fact, nothing else.

## References

* `AssHeightBound.height_le_of_mem_minimalPrimes`
  (`Regularity/Avoid/AssHeightBound.lean`, via
  `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`). -/
theorem heightDrop_of_mem_minimalPrimes {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hmin : P ∈ J.minimalPrimes) :
    P.height ≤ (k : ℕ∞) :=
  AssHeightBound.height_le_of_mem_minimalPrimes q J hJ P hmin

/-- Weakest-hypothesis equivalence, proved (Q+1): the residual at length `k`
is unmixedness-at-`k` (every `Ass` prime minimal over `J`). Forward is the
proved conditional assembly (`unmixed_of_heightDrop`); backward is the Krull
conditional above. Hence any close of the residual (CM step, depth =
dim, maximal-sequence argument) has exactly one formal address: minimality
of `Ass` primes over `J` — equivalently `dim (R_P ⧸ J_P) = 0` via
`mem_minimalPrimes_of_localized_quotient_dim_zero`. -/
theorem heightDrop_iff_forall_mem_minimalPrimes {k : ℕ} (m : ℕ) (K : Type*)
    [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q)) :
    HeightDropResidualAt m K q hsucc J hJ ↔
      (∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
        P ∈ associatedPrimes _ (_ ⧸ J) → P ∈ J.minimalPrimes) := by
  constructor
  · intro hdrop P _ hP
    exact unmixed_of_heightDrop m K q hsucc J hJ P hP hdrop
  · intro hmin P _ hmem
    exact heightDrop_of_mem_minimalPrimes m K q J hJ P (hmin P hmem)

/-- PrimeAvoidance-powered rung selection over `R ⧸ J`, proved (Q+1, step 1): if
the ideal `I` lies in no associated prime of `R ⧸ J`, some element of `I` is
SMul-regular on `R ⧸ J` — the "next rung" is regular on the current quotient.
Thin consume of `PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass`
(the per-prime input is the exact hypothesis future height control must
supply; see the §4 ledger for why it has no source yet without minimality).

## References

* `PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass`
  (`Regularity/Avoid/PrimeAvoidance.lean`, via `associatedPrimes.finite` +
  `biUnion_associatedPrimes_eq_compl_regular`).
* `Module.Finite.of_surjective`, `Submodule.mkQ_surjective` (Mathlib v4.34.0;
  already used in-tree at `GradeDepthFragment.lean`). -/
theorem exists_nextRung_regular_of_avoid (m : ℕ) (K : Type*) [Field K]
    (J I : Ideal (MvPolynomial (Fin m) K))
    (hle : ∀ P ∈ associatedPrimes _ (_ ⧸ J), ¬ I ≤ P) :
    ∃ x ∈ I, IsSMulRegular (_ ⧸ J) x := by
  have hfin : Module.Finite (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J) :=
    Module.Finite.of_surjective (Submodule.mkQ (J : Submodule _ _))
      (Submodule.mkQ_surjective _)
  exact PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass I hle

/-- PrimeAvoidance-powered selection inside the maximal ideal, proved (Q+1,
step 1, local form): in a Noetherian local ring, if the maximal ideal lies in
no associated prime of `M`, some element of the maximal ideal is SMul-regular
on `M` while avoiding every associated prime. This is the exact shape the
localization rung (`S = Localization.AtPrime P`,
`M = S ⧸ J_P`) consumes once Ass-control supplies `hle`.

## References

* `PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass`
  (`Regularity/Avoid/PrimeAvoidance.lean`). -/
theorem exists_nextRung_mem_maximal_of_avoid {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hle : ∀ P ∈ associatedPrimes S M, ¬ IsLocalRing.maximalIdeal S ≤ P) :
    ∃ x ∈ IsLocalRing.maximalIdeal S, IsSMulRegular M x :=
  PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass _ hle

end HeightDrop
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
