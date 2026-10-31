/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerreGrTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.DimEqualsEmbdim
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity

/-!
# Minimal-generator existence per associated prime
Close `GAP-GR-MINEXIST` (`HilbertSerreGrTransfer.lean` §5 residual): for
`Q ∈ Ass(R ⧸ J)`, produce minimal-generator data matching the H4 inputs of
`chiGrowth_of_grClose_atAss` (`{d} g hgen hdmin (hd : 1 ≤ d)`), and settle the
`d = 0` case per `Q`.

## Results

* (§1) `grMinExist_atPrime` / `grMinExist_atAss`: `∃ d g`,
  `span (range g) = 𝔪(R_Q) ∧ d = spanFinrank 𝔪` — unconditional, via the
  proved `grlift_sop_exists` (which is itself the FG route:
  `Submodule.FG.exists_span_finset_card_eq_spanFinrank` over
  `Ideal.fg_of_isNoetherianRing`, per `SystemOfParameters`). No Nakayama lifting is
  rebuilt: the `𝔪/𝔪²`-basis identification is the proved
  `grlift_sop_cotangent_dim`, and existence needs only FG + minimality.
* (§2) `grMinExist_cumsum_isPolyGrowth_zero`: a cumsum of an eventually-zero
  sequence has growth `≤ 0` (eventually constant) — unconditional.
* (§3) `grMinExist_chi_zero_of_mingens`: from `d = 0` mingens data,
  `IsPolyGrowth (chiFunQ m K Q) 0` — unconditional, via the proved
  `grClose_rational_zero` (polynomial gr series ⟹ `H` eventually zero) plus
  §2 and the unconditional cumsum bridge. Note `1 ≤ d` is false in general
  per `Q` (e.g. `J = ⊥`, `Q = ⊥` gives `d = 0`), so the `d = 0` growth form
  — not a positivity proof — is the correct settlement.
* (§4) `grMinExist_hchiGrowth_unconditional`: `HchiGrowthAtAss m K J`
  unconditional — case split on `d = 0` (§3 + Track-R pin at `dimN = 0`)
  vs `1 ≤ d` (`chiGrowth_of_grClose_atAss`).

## Status

unconditional: `grMinExist_atPrime`, `grMinExist_atAss`,
`grMinExist_cumsum_isPolyGrowth_zero`, `grMinExist_chi_zero_of_mingens`,
`grMinExist_hchiGrowth_unconditional`.

## Residual register

closed this lane: [gap-gr-minexist in full — mingens existence per
`Q ∈ Ass(R ⧸ J)` with `d = spanFinrank 𝔪`]; [the `d = 0` case per `Q`];
[the H4 conditional — `HchiGrowthAtAss` is now unconditional].
open (exact, outside this file's scope): [H2 `HchiReduceAtAss`, Track-R
`HregDimAtAss` — the other two SPECs consumed by
`hdimEqMinAtAss_of_chi_specs`]. No Mathlib-absence claim is made or estimated.

## References

Project (read-only):
* `Regularity/Koszul/GradedLift.lean` (`grlift_sop_exists`, `grlift_sop_cotangent_dim`).
* `Regularity/Koszul/SystemOfParameters.lean` (the FG route behind the sop).
* `Regularity/Multiplicity/HilbertSerreGrTransfer.lean` (`grClose_rational_zero`,
  `chiGrowth_of_grClose_atAss`).
* `Regularity/Multiplicity/HilbertSamuelDegree.lean` (`hsCumsum`,
  `hsBridge_hs_eq_cumsum_unconditional`).
* `Regularity/Multiplicity/NewtonDifferences.lean` (`IsPolyGrowth`, `evalFun`).
* `Regularity/Multiplicity/ChiDegreeMaster.lean` (`chiFunQ`, `HchiGrowthAtAss`).
* `Regularity/Grade/DimEqualsEmbdim.lean` (`dimEmbAtAss_unconditional`).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/PowerSeries/Basic.lean`: `PowerSeries.coeff_mk`,
  `Polynomial.coeff_coe`.
* `Algebra/Polynomial/Degree/Operations.lean`:
  `Polynomial.coeff_eq_zero_of_natDegree_lt`.
* `Algebra/Polynomial/Degree/Defs.lean`: `Polynomial.natDegree_C`.
* `Algebra/Polynomial/Eval/Defs.lean`: `Polynomial.eval_C`.
* `Algebra/BigOperators/Group/Finset/Basic.lean`: `Finset.sum_subset`.
* `Data/Finset/Range.lean`: `Finset.range_subset_range`.
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.
-/

open scoped PowerSeries

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinimalGeneratorExists

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerreGrTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimEqualsEmbdim
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity

/-! ## §1. Minimal-generator existence (gap-gr-minexist) -/

/-- Minimal-generator family for the maximal ideal at any prime: `d`
generators spanning `𝔪(R_Q)` with `d = spanFinrank 𝔪`. This is the proved
`grlift_sop_exists` (the FG route via `SystemOfParameters`); the `Ass` gate is added
in `grMinExist_atAss`.
-/
theorem grMinExist_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ∃ d : ℕ, ∃ g : Fin d → Localization.AtPrime Q,
      Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
  grlift_sop_exists Q

#print axioms grMinExist_atPrime

/-- Gap-gr-minexist, closed: minimal-generator data per
`Q ∈ Ass(R ⧸ J)`, in the exact H4 input shape (`{d} g hgen hdmin` of
`chiGrowth_of_grClose_atAss`). The `Ass` gate matches consumer SPECs
(irrelevant to truth — §1 holds at every prime).
-/
theorem grMinExist_atAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    ∃ d : ℕ, ∃ g : Fin d → Localization.AtPrime Q,
      Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
  grlift_sop_exists Q

#print axioms grMinExist_atAss

/-! ## §2. Cumsum of an eventually-zero sequence is eventually constant -/

/-- A cumsum of an eventually-zero sequence has growth `≤ 0`: for
`n ≥ N` the tail of the range sum vanishes (`Finset.sum_subset`), so the
cumsum is eventually the constant `hsCumsum H N = evalFun (C _)`.
-/
theorem grMinExist_cumsum_isPolyGrowth_zero {H : ℕ → ℚ} {N : ℕ}
    (hH : ∀ n ≥ N, H n = 0) :
    IsPolyGrowth (hsCumsum H) 0 := by
  refine ⟨Polynomial.C (hsCumsum H N), le_of_eq (Polynomial.natDegree_C _), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  change hsCumsum H n = (Polynomial.C (hsCumsum H N)).eval (n : ℚ)
  rw [Polynomial.eval_C]
  change (∑ i ∈ Finset.range (n + 1), H i) = ∑ i ∈ Finset.range (N + 1), H i
  symm
  exact Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    (fun i _ hni => hH i (by
      simp only [Finset.mem_range, not_lt] at hni
      omega))

#print axioms grMinExist_cumsum_isPolyGrowth_zero

/-! ## §3. The `d = 0` growth form -/

/-- The `d = 0` case per `Q`: from mingens data with `d = 0`, `χ` has
growth `≤ 0`. Proof: `grClose_rational_zero` makes the gr Hilbert series a
polynomial series, so `H` vanishes past `f.natDegree` (coefficient
extraction via `coeff_mk` / `coeff_coe`); §2 gives the cumsum growth `≤ 0`;
the unconditional cumsum bridge rewrites it to `chiFunQ`.
-/
theorem grMinExist_chi_zero_of_mingens (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd0 : d = 0) :
    IsPolyGrowth (chiFunQ m K Q) 0 := by
  obtain ⟨f, hf⟩ := grClose_rational_zero Q d g hgen hd0
  have hH : ∀ n ≥ f.natDegree + 1,
      ((singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        n : ℕ) : ℚ) = 0 := by
    intro n hn
    have hcoeff : (PowerSeries.coeff n) (PowerSeries.mk (fun n =>
          ((singleDrop_grHilbert
            (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ)))
        = (PowerSeries.coeff n) (↑f : ℚ⟦X⟧) := by rw [hf]
    rw [PowerSeries.coeff_mk, Polynomial.coeff_coe] at hcoeff
    rw [hcoeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hpoly := grMinExist_cumsum_isPolyGrowth_zero (H := fun n =>
    ((singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      n : ℕ) : ℚ)) hH
  have hbridge :=
    hsBridge_hs_eq_cumsum_unconditional (R := Localization.AtPrime Q)
  have hfun : (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
      = chiFunQ m K Q := rfl
  rw [← hfun, hbridge]
  exact hpoly

#print axioms grMinExist_chi_zero_of_mingens

/-! ## §4. The unconditional H1 pin -/

/-- The H1 pin, unconditional: `HchiGrowthAtAss` from §§1–3. Case split on
the mingens dimension: at `d = 0`, §3 gives χ-growth `≤ 0` with the Track-R
pin rewritten to `dimN = 0`; at `1 ≤ d`, `chiGrowth_of_grClose_atAss` fires
directly. This discharges the H4 conditional downstream consumers read.
-/
theorem grMinExist_hchiGrowth_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HchiGrowthAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, g, hgen, hdmin⟩ := grMinExist_atAss m K J Q hQ
  by_cases hd0 : d = 0
  · have hR := dimEmbAtAss_unconditional m K J Q hQ
    rw [← hdmin, hd0] at hR
    exact ⟨0, hR, grMinExist_chi_zero_of_mingens m K Q d g hgen hd0⟩
  · have hd : 1 ≤ d := Nat.pos_of_ne_zero hd0
    exact chiGrowth_of_grClose_atAss m K J Q hQ g hgen hdmin hd

#print axioms grMinExist_hchiGrowth_unconditional

end MinimalGeneratorExists
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
