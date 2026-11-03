/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeUnmixedBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Order.WithBot

/-!
# `hunmixed_ge`: unmixedness at length `k`, conditional on the shared residual

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `q : Fin k → R` carrying
successive SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`), and
`J = Ideal.span (Set.range q)`, this file discharges the R3-register item
`k > 2` (`hunmixed_ge2`): every `P ∈ Ass(R ⧸ J)` is minimal over `J`.

## Result: `k > 2` adds no new remainder beyond `k = 2`

The entire `UnmixednessAtLengthTwo` chain is already general-`k`:

* `GradeUnmixedBridge.unmixed_of_chain_depth` is stated at `{k : ℕ}` implicit.
* `GradeDepthFragment.gradeDropChain_of_successive` is stated at `{k : ℕ}` implicit.
* `UnmixednessAtLengthTwo.hdepth_of_hkerMin` / `hkerMinAtAss_of_hdimEqMin` (the
  `HdimEqMinAtAss → DepthEqDimAt` leg) mention no `k` at all: they are about
  `gr`-Hilbert theory at minimal embedding dimension `d` of each `R_Q`.
* `HeightDrop.heightDrop_of_mem_minimalPrimes` /
  `heightDrop_iff_forall_mem_minimalPrimes` are stated at `{k : ℕ}` implicit.

Hence the `k = 2` masters (`UnmixednessAtLengthTwo.lean` §5) re-run verbatim at general
`k`, conditional-exact on the same single residual `HdimEqMinAtAss` (§2–§3).
The `k > 2` rung is therefore exactly as hard as the `k = 2` rung — one
shared crux, not a per-`k` ladder.

## What is proved here

* §1 SPEC: `HunmixedGeProp` (general-`k` goal statement).
* §2 masters (conditional-exact on `[hdimEq : HdimEqMinAtAss m K J]`):
  `hunmixed_of_hdimEqMin` (per-prime), `hunmixed_forall_of_hdimEqMin`
  (`∀`-closed consumer shape), `height_le_of_hdimEqMin` (`P.height ≤ k`
  via the general-`k` Krull direction), `hunmixed_iff_heightDrop`
  (equivalence with `HeightDropResidualAt`).
* §3 gated shapes: `hunmixed_ge2_of_hdimEqMin` (the fixed-`k`
  `2 ≤ k → ∀ P ∈ Ass, P ∈ minimalPrimes` shape consumed by
  `AvoidanceApply.hAss_of_hunmixed_ge2`), `hunmixed_ge2_all_of_hdimEqMin_all`
  (the `∀ k, 2 ≤ k → ∀ q hsucc J hJ, …` shape consumed by
  `ResultantLemmas.exists_regular_quadrics_of_unmixed`).
* §4 avoidance wiring: `avoid_of_hdimEqMin` — general-`k` avoidance
  conditional on `[HdimEqMinAtAss]` only (`hlow` discharged by the
  unconditional `hlow_uncond`; `hunmixed` by §2).

## Precise narrowed remainder (out of scope; shared with `k = 2`)

`HdimEqMinAtAss` alone — see `UnmixednessAtLengthTwo.lean` §§7–8 + `DimensionToMultiplicity`:
`d = 1` is unconditional (`hdimEqMinAtAss_d_one`); at `d ≥ 2` the R-2c′
dimension-to-multiplicity leg is closed (`DimensionToMultiplicity`, exact on
`HgrDimEqMinAtAss`), leaving the R-2a′ remainder `dim gr(R_Q) = embdim`
per Ass prime (`HdimGrMinAtAss`, §8 partial: `d = 0/1` closed,
`d ≥ 2` on `HwitMinAtAss`). No Cohen–Macaulay / unmixedness input exists
in Mathlib v4.34.0 (re-verified `grep`: only the unrelated infinite-place
`IsUnmixed`). Nothing else is assumed.

## R3 register update (this lane)

* `k = 0`: closed (`Unmixedness.mem_minimalPrimes_of_successive_zero`).
* `k = 1`: closed (`Unmixedness.mem_minimalPrimes_of_successive_singleton`).
* `k = 2`: open as `AvoidanceApply.UnmixednessAtLengthTwo` register; conditional-exact
  on `[HdimEqMinAtAss]` via `UnmixednessAtLengthTwo.hunmixed_two_forall_of_hdimEqMin`.
* `k > 2`: open as `hunmixed_ge2`; conditional-exact on the same
  `[HdimEqMinAtAss]` via §2–§3 below (this file). No new residual.

## Standing context (routine binders, not residuals)

Per-declaration GRADE lines track only non-standing residuals. The following
recur verbatim across declarations and are documented once here: `q` /
`hsucc` (successive-regular family data), `J` / `hJ` (span ideal),
`P` / `hP` (Ass prime under study), and instance binders (`[Field K]`,
`[P.IsPrime]`, `[IsAlgClosed K]` where taken); §4 additionally takes the
standing inputs `hZd` and `hJ` named at `avoid_of_hdimEqMin`.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):
* `Geometry/UnmixednessAtLengthTwo.lean`: `HdimEqMinAtAss`, `hkerMinAtAss_of_hdimEqMin`,
  `hdepth_of_hkerMin` (all general-`k`-agnostic; consumed read-only).
* `Regularity/Grade/GradeUnmixedBridge.lean`: `unmixed_of_chain_depth`.
* `Regularity/Grade/GradeDepthFragment.lean`: `gradeDropChain_of_successive`.
* `Regularity/Unmixed/HeightDrop.lean`: `heightDrop_of_mem_minimalPrimes`,
  `heightDrop_iff_forall_mem_minimalPrimes` (both general-`k`).
* `Regularity/Avoid/AvoidanceApply.lean`: `avoid_of_unmixed_hlow`,
  `hAss_of_hunmixed_ge2` (gated-shape consumers).
* `Regularity/Avoid/ResultantLemmas.lean`:
  `exists_regular_quadrics_of_unmixed` (`∀`-closed gated-shape consumer).
* `Dimension/HeightLowerBound.lean`: `hlow_uncond` (unconditional).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace UnmixednessAtLengthK

/-! ## §1. SPEC: general-`k` goal statement -/

/-- General-`k` unmixedness goal (SPEC address): every `P ∈ Ass(R ⧸ J)` for a
successive-regular family is minimal over `J`. -/
def HunmixedGeProp {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (_hJ : J = Ideal.span (Set.range q)) : Prop :=
  ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    P ∈ associatedPrimes _ (_ ⧸ J) → P ∈ J.minimalPrimes

/-! ## §2. Masters: general-`k` unmixedness on `[HdimEqMinAtAss]` -/

/-- Per-prime minimality over `J` from `HdimEqMinAtAss`: one-line application
of the hbaby-closed `GradeUnmixedBridge.unmixed_of_chain_depth` (general-`k`),
fed with the closed chain (`GradeDepthFragment.gradeDropChain_of_successive`,
general-`k`) and `UnmixednessAtLengthTwo.hdepth_of_hkerMin` on the §3 discharge (both
`k`-agnostic).

Conditional on exactly `[hdimEq]`. -/
theorem hunmixed_of_hdimEqMin {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    P ∈ J.minimalPrimes :=
  GradeUnmixedBridge.unmixed_of_chain_depth m K q hsucc J hJ P hP
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc)
    (UnmixednessAtLengthTwo.hdepth_of_hkerMin m K J
      (UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J hdimEq))

/-- `∀`-closed (consumer) shape: `HunmixedGeProp` from `HdimEqMinAtAss`.

Conditional on exactly `[hdimEq]`. -/
theorem hunmixed_forall_of_hdimEqMin {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    HunmixedGeProp m K q hsucc J hJ :=
  fun P _ hP => hunmixed_of_hdimEqMin m K q hsucc J hJ P hP hdimEq

/-- Height `≤ k` form from `HdimEqMinAtAss`: the general-`k` Krull direction
(`HeightDrop.heightDrop_of_mem_minimalPrimes`) applied to the per-prime
minimality above.

Conditional on exactly `[hdimEq]`. -/
theorem height_le_of_hdimEqMin {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    P.height ≤ ((k : ℕ) : ℕ∞) :=
  HeightDrop.heightDrop_of_mem_minimalPrimes m K q J hJ P
    (hunmixed_of_hdimEqMin m K q hsucc J hJ P hP hdimEq)

/-- `HunmixedGeProp` is the general-`k` height-drop residual: the
`HeightDrop.heightDrop_iff_forall_mem_minimalPrimes` equivalence.
-/
theorem hunmixed_iff_heightDrop {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q)) :
    HunmixedGeProp m K q hsucc J hJ ↔
      HeightDrop.HeightDropResidualAt m K q hsucc J hJ := by
  unfold HunmixedGeProp HeightDrop.HeightDropResidualAt
  exact (HeightDrop.heightDrop_iff_forall_mem_minimalPrimes m K q hsucc J hJ).symm

#print axioms hunmixed_of_hdimEqMin
#print axioms hunmixed_forall_of_hdimEqMin
#print axioms height_le_of_hdimEqMin
#print axioms hunmixed_iff_heightDrop

/-! ## §3. Gated shapes (`k ≥ 2` consumers) -/

/-- Fixed-`k` gated shape from `HdimEqMinAtAss`: the exact
`2 ≤ k → ∀ P ∈ Ass, P ∈ minimalPrimes` hypothesis consumed by
`AvoidanceApply.hAss_of_hunmixed_ge2` (the `2 ≤ k` gate is discharged by the
caller; the proof itself is `k`-uniform).

Conditional on exactly `[hdimEq]`. -/
theorem hunmixed_ge2_of_hdimEqMin {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    2 ≤ k → ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes := by
  intro _ P hP
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact hunmixed_of_hdimEqMin m K q hsucc J hJ P hP hdimEq

/-- `∀`-closed gated shape from ∀-closed `HdimEqMinAtAss`: the exact
`∀ k, 2 ≤ k → ∀ q hsucc J hJ, ∀ P ∈ Ass, P ∈ minimalPrimes` hypothesis
consumed by `ResultantLemmas.exists_regular_quadrics_of_unmixed`.

Conditional on exactly `[hdimEq]`. -/
theorem hunmixed_ge2_all_of_hdimEqMin_all (m : ℕ) (K : Type*) [Field K]
    (hdimEq : ∀ (k : ℕ) (q : Fin k → MvPolynomial (Fin m) K)
      (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
      (J : Ideal (MvPolynomial (Fin m) K))
      (_hJ : J = Ideal.span (Set.range q)),
      UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    ∀ (k : ℕ), 2 ≤ k →
      ∀ (q : Fin k → MvPolynomial (Fin m) K)
      (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
      (J : Ideal (MvPolynomial (Fin m) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
        (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes := by
  intro k _ q hsucc J hJ P hP
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact hunmixed_of_hdimEqMin m K q hsucc J hJ P hP (hdimEq k q hsucc J hJ)

#print axioms hunmixed_ge2_of_hdimEqMin
#print axioms hunmixed_ge2_all_of_hdimEqMin_all

/-! ## §4. Avoidance wiring: general-`k` avoidance on `[HdimEqMinAtAss]` only -/

/-- General-`k` avoidance conditional on `[HdimEqMinAtAss]` only (residual
register): `hunmixed` via §2 (`hunmixed_forall_of_hdimEqMin`), `hlow` via
the unconditional `hlow_uncond` (containment hypothesis dropped —
`hlow_uncond` needs none). Standing inputs (not residuals): `[IsAlgClosed K]`,
`hZd`, `hJ`. This is the `k > 2` analogue of
`AvoidanceApply.avoid_mkSystem_pair_of_hunmixedTwo`, with the register
discharged down to the shared residual.

Conditional on exactly `[hdimEq]`. -/
theorem avoid_of_hdimEqMin (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (k : ℕ) (hk : k ≤ n)
    (q : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (n + 2) K J) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range G) ≤ P) := by
  refine AvoidanceApply.avoid_of_unmixed_hlow n K G hZd k hk q hsucc J hJ
    ?hunmixed (fun P _ _ => hlow_uncond n K P)
  intro P hP
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact hunmixed_of_hdimEqMin (n + 2) K q hsucc J hJ P hP hdimEq

#print axioms avoid_of_hdimEqMin

end UnmixednessAtLengthK
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
