/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceStep
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.TriangularRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.List.OfFn
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Conditional avoidance from explicit unmixedness + catenary inputs

The avoidance chain is complete except for two named hard inputs, each documented
with a `## Obstruction` section in its home file:

* `AssHeightBound` proves minimal-prime height `= k`
  (`height_eq_of_mem_minimalPrimes`) but the `hAss` upper bound on all of
  `Ass(R ⧸ J)` needs explicit unmixedness: every associated prime is minimal.
* `HeightLowerBound` proves the maximal case, the dim-zero case, and the
  conditional assembly (`height_lower_bound_of_catenary_lower_bound`), but the
  general `hHt` needs the explicit catenary lower bound `hlow`.

Following the established explicit-hypothesis pattern (precedent:
`Elimination.chart_bridge`'s stand-in `hlin` — explicit, documented),
this file assembles the conditional avoidance theorem, so the only
gaps are named explicit hypotheses (`hunmixed`, `hlow`):

* `hAss_of_unmixed`: `hunmixed` + `height_eq_of_mem_minimalPrimes` give `hAss`
  in the core's exact binder shape.
* `hHt_of_hlow`: `hlow` (the exact hypothesis shape
  `height_lower_bound_of_catenary_lower_bound` consumes) + that conditional
  lemma give `hHt` in the core's exact binder shape.
* `avoid_of_unmixed_hlow`: `(hk : k ≤ n)` + regular data + `hunmixed` + `hlow`
  give `¬ span G ≤ P` for all `P ∈ Ass(R ⧸ J)`, via
  `noAssPrime_contains_span_of_height_bounds`.
* `span_le_of_comap_comboLin_eq_top`: the `comap`-to-`span` bridge the R2
  plug-in needs (contrapositive feeds `exists_regular_quadrics`' `havoid`).

On "properness in A4's exact form": verified by reading
`AssHeightBound.lean` lines 88-200 — none of its lemmas
(`height_eq_add_of_span`, `le_height_of_span_of_successive`,
`le_height_of_mem_associatedPrimes_of_successive`,
`height_le_of_mem_minimalPrimes`, `height_eq_of_mem_minimalPrimes`) takes a
standalone properness hypothesis. The regular data is exactly
`RegularityBridge.SuccessiveSMulRegular q` plus the span equation
`hJ : J = Ideal.span (Set.range q)`; per-prime properness/primality comes from
`[P.IsPrime]` instances derived from `Ass` membership via
`AssociatedPrimes.mem_iff`. No extra hypothesis is invented here.

## Plug-in map

R2 (`ResultantLemmas.exists_regular_quadrics`): exact instantiation recipe.
At induction step `k` (the `key` induction chooses rows `0..n`, so each
avoidance call has current generator count `k ≤ n`, i.e. `hk : k ≤ n` holds;
`k = 0` is already unconditional via `noAssPrime_contains_span_zero`):

* `k`:= number of combinations chosen so far,
* `J`:= `Ideal.span (Set.range q)` with `q j = comboLin K G (r j)` the chosen
  rows (`RegularityBridge.span_range_eq_ofList_ofFn` identifies this with the
  `Ideal.ofList` span used in the induction step),
* `G`:= the same system `G`,
* `hunmixed` specializes to
  `∀ P ∈ associatedPrimes R (R ⧸ J_step), P ∈ J_step.minimalPrimes`,
* `hlow` specializes at the same `G` (it is step-independent),
* `hsucc` for the chosen rows comes from the step's `IsSMulRegular` outputs
  (proof obligation at each step, not closed here),
* then `avoid_of_unmixed_hlow` yields `¬ Ideal.span (Set.range G) ≤ P`, and the
  contrapositive of `span_le_of_comap_comboLin_eq_top` turns this into the
  required
  `Submodule.comap (comboLin K G) (Submodule.restrictScalars K ↥P) ≠ ⊤`.

R1 (`ResultantLemmas.exists_regular_chartForm`): precise gap, no instantiation.
R1's `havoid` is over `S = coneQuotient n K G`:
```
(havoid: ∀ P ∈ associatedPrimes (coneQuotient n K G) (coneQuotient n K G),
  Submodule.comap (coeffToCone n K G)
    (Submodule.restrictScalars K
      (P: Submodule (coneQuotient n K G) (coneQuotient n K G))) ≠ ⊤)
```
Our theorem lives over `R = MvPolynomial (Fin (n + 2)) K` and concludes
`¬ Ideal.span (Set.range G) ≤ P` for `P ∈ Ass(R ⧸ J)`. The missing bridge has
two halves, neither attempted here: (i) transport of `Ass(R ⧸ J)`-avoidance
across the quotient map `R → S` (associated primes of `S` as a module over
itself correspond to primes of `R` containing `span G`, not to `Ass(R ⧸ J)`
for intermediate `J`); (ii) an `S`-side height contradiction in the shape of
`coeffToCone`-pullback properness, which is about linear forms in `S`, not
spans in `R`.

## mkSystem narrowing (R2-at-`mkSystem`, conditional on `hunmixed`-at-`k ≥ 2` only)

The second half of this file narrows the R2 consumer to `G = mkSystem n K F`,
so that induction steps `k = 0, 1` discharge via proved inputs while `k ≥ 2`
stays an explicit conditional hypothesis:

* `ofList_take_eq_span_image` + `hsucc_of_step_outputs` (L-HSUCC glue): the
  R2-step `IsSMulRegular` outputs (quotients by `Ideal.ofList` of taken prefix
  lists) repackaged into `RegularityBridge.SuccessiveSMulRegular` (quotients by spans
  of previous values), via `Fin.ofFn_take_eq_take_ofFn`.
* `hAss_of_hunmixed_ge2` + `avoid_of_hunmixed_ge2`: the avoidance chain with
  `hunmixed` gated on `2 ≤ k` — `k = 0` via the proved domain case
  (`Unmixedness.mem_minimalPrimes_of_successive_zero`), `k = 1` via the proved
  UFD-colon case (`Unmixedness.mem_minimalPrimes_of_successive_singleton`),
  `k ≥ 2` via the explicit hypothesis.
* `comap_ne_top_of_step`: the per-step `≠ ⊤` the R2 induction consumes
  (spans bridge + the above), taking `hsucc` from the step outputs.
* `isSMulRegular_quot_bot_of_regular` + `hsucc_mkSystem_singleton` +
  `comap_ne_top_zero_of_t1`: step `k = 0` discharged via the domain step
  (`Triangular.mkSystem_ne_zero`, t1-style `Gᵢ ≠ 0`) — no `hZd`, no `hlow`,
  no unmixedness needed at `J = ⊥`.
* `isSMulRegular_mkSystem_mod_of_not_dvd` (t2a carried back across
  `Triangular.lastVarRingEquiv`) + `hsucc_mkSystem_pair_of_dichotomy` +
  `avoid_mkSystem_pair`: the t2a/t2b dichotomy shapes imported/applied at the
  `mkSystem` instantiation, supplying `hsucc` for the generator pair; the
  `k = 2` avoidance stays conditional on explicit `hunmixed₂` (+ `hlow`).
  Step 3+ (t3) is explicitly out of scope (see `TriangularRegularity.lean` (t3)
  verdict, applied as-is, not generalized).

Remaining hypotheses at `k ≥ 2` (see also the final R2 theorem in
`ResultantLemmas.lean`): `hunmixed_ge2` (minimality over `J` for `2 ≤ k`)
and the step-independent catenary `hlow`. Frozen contracts
(`unmixed_of_successive_regular_*`) are consumed read-only, never
restated; `hlow` stays an explicit hypothesis.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `AvoidanceStep.lean`, `noAssPrime_contains_span_of_height_bounds`,
  `noAssPrime_contains_span_zero`.
* `AssHeightBound.lean`, `height_eq_of_mem_minimalPrimes` (plus the
  `## Obstruction` unmixedness input quoted by `hunmixed`).
* `HeightLowerBound.lean`, `height_lower_bound_of_catenary_lower_bound` (plus
  the `## Obstruction` catenary input quoted by `hlow`).
* `ResultantLemmas.lean`, `exists_regular_chartForm`, `exists_regular_quadrics`.
* `Definitions.lean`, `comboLin`, `comboLin_apply`.
* `RegularityBridge.lean`, `SuccessiveSMulRegular`, `span_range_eq_ofList_ofFn`.
* `Regularity/Unmixed/Unmixedness.lean`, `mem_minimalPrimes_of_successive_zero`,
  `mem_minimalPrimes_of_successive_singleton` (`k ≤ 1` inputs, applied).
* `Regularity/Avoid/TriangularRegularity.lean`, `mkSystem_ne_zero`,
  `mkSystem_isSMulRegular`, `triG_isSMulRegular_mod_of_not_dvd`,
  `mkSystem_isSMulRegular_mod_of_dvd`, `lastVarRingEquiv`,
  `lastVarRingEquiv_apply`, `lastVarEquiv_mkSystem` (t1/t2a/t2b, applied).
* `Dimension/RegularSequenceDimDrop.lean`, `span_smul_top` (ideal/submodule bridge).
* `Definitions.lean`, `IsZeroDimensional`.
* `Elimination.lean`, `chart_bridge` (precedent for the explicit-hypothesis
  escape hatch).

Mathlib:

* `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`, `associatedPrimes`,
  `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`.
* `Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean`, `Ideal.minimalPrimes`.
* `Mathlib/RingTheory/Ideal/Height.lean`, `Ideal.height`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `ringKrullDim`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`.
* `Mathlib/Algebra/Module/Submodule/Map.lean`, `Submodule.mem_comap`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single_of_mem`.
* `Mathlib/Algebra/Group/Pi/Basic.lean` (via `ResultantLemmas` usage),
  `Pi.single_eq_of_ne`, `Pi.single_eq_same`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AvoidanceApply

/-- `hAss` from explicit unmixedness: if every `P ∈ Ass(R ⧸ J)` is minimal over
`J = span (Set.range q)`, then `height_eq_of_mem_minimalPrimes` gives
`P.height ≤ k` in exactly the consumption shape of
`AvoidanceStep.noAssPrime_contains_span_of_height_bounds`.

## References

* `AssHeightBound.height_eq_of_mem_minimalPrimes`.
* `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`. -/
theorem hAss_of_unmixed {R : Type*} [CommRing R] [IsNoetherianRing R]
    {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal R) (hJ : J = Ideal.span (Set.range q))
    (hunmixed : ∀ P ∈ associatedPrimes R (R ⧸ J), P ∈ J.minimalPrimes) :
    ∀ P ∈ associatedPrimes R (R ⧸ J), P.height ≤ (k : ℕ∞) := by
  intro P hP
  have hprime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact le_of_eq (@AssHeightBound.height_eq_of_mem_minimalPrimes _ _ _ _ q hsucc
    J hJ P hprime (hunmixed P hP))

/-- `hHt` from the explicit catenary lower bound: `hlow` is the exact
hypothesis shape `height_lower_bound_of_catenary_lower_bound` consumes, so the
conclusion is `hHt` in exactly the consumption shape of
`AvoidanceStep.noAssPrime_contains_span_of_height_bounds`.

## References

* `HeightLowerBound.height_lower_bound_of_catenary_lower_bound`. -/
theorem hHt_of_hlow (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range G) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P)) :
    ∀ P : Ideal (MvPolynomial (Fin (n + 2)) K), P.IsPrime →
      Ideal.span (Set.range G) ≤ P → ((n : ℕ∞) + 1) ≤ P.height := by
  intro P hprime hle
  exact @height_lower_bound_of_catenary_lower_bound n K _ _ G hZd P hprime hle
    (@hlow P hprime hle)

/-- Conditional avoidance: with `k ≤ n`, successive-regular data for
`J = span (Set.range q)`, explicit unmixedness, and the explicit catenary lower
bound, no associated prime of `R ⧸ J` contains `span G`. The only gaps are the
named explicit hypotheses `hunmixed` and `hlow`.

## References

* `AvoidanceStep.noAssPrime_contains_span_of_height_bounds`.
* `hAss_of_unmixed`, `hHt_of_hlow` above. -/
theorem avoid_of_unmixed_hlow (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (k : ℕ) (hk : k ≤ n)
    (q : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hunmixed : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes)
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range G) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P)) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range G) ≤ P) :=
  noAssPrime_contains_span_of_height_bounds n K G k hk J
    (hAss_of_unmixed q hsucc J hJ hunmixed)
    (hHt_of_hlow n K G hZd hlow)

/-- The `comap`-to-`span` bridge for the R2 plug-in: if the coefficient pullback
of `P` along `comboLin K G` is everything, then every `G i` lies in `P` (take
the `Pi.single i 1` coefficient vectors), hence `span G ≤ P`. Contrapositive:
`¬ span G ≤ P` (e.g. from `avoid_of_unmixed_hlow`) gives the `≠ ⊤` that
`ResultantLemmas.exists_regular_quadrics`' `havoid` demands.

## References

* `Definitions.comboLin_apply`.
* `Mathlib/Algebra/Module/Submodule/Map.lean`, `Submodule.mem_comap`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single_of_mem`.
* `Pi.single_eq_of_ne`, `Pi.single_eq_same` (as used in `ResultantLemmas`).
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`. -/
theorem span_le_of_comap_comboLin_eq_top (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K))
    (htop : Submodule.comap (comboLin K G)
      (Submodule.restrictScalars K
        (P : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))) = ⊤) :
    Ideal.span (Set.range G) ≤ P := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  have hmem : (Pi.single i (1 : K) : Fin (n + 1) → K) ∈ Submodule.comap (comboLin K G)
      (Submodule.restrictScalars K
        (P : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Submodule.mem_comap] at hmem
  have h0 : ∀ l ∈ (Finset.univ : Finset (Fin (n + 1))), l ≠ i →
      (((Pi.single i (1 : K) : Fin (n + 1) → K)) l • G l) = 0 := by
    intro l _ hli
    rw [Pi.single_eq_of_ne hli, zero_smul]
  have heq : comboLin K G (Pi.single i (1 : K)) = G i := by
    rw [comboLin_apply,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i) h0,
      Pi.single_eq_same, one_smul]
  rw [heq] at hmem
  exact hmem

/-! ## General-G R2 plug-in (L-R2, tasks 2–3)

The R2 plug-in for general `G` (no `mkSystem` narrowing): step `k = 0` from
`hZd` alone (`comap_ne_top_zero_general`, via
`noAssPrime_contains_span_zero` + the span bridge — no `hlow`, no
unmixedness), steps `k ≥ 1` with ungated unmixedness
(`comap_ne_top_of_step_unmixed`, the literal recipe `hAss_of_unmixed` +
`hHt_of_hlow` → `avoid_of_unmixed_hlow` → contrapositive of
`span_le_of_comap_comboLin_eq_top`). Both conclude the exact `≠ ⊤` shape
that `ResultantLemmas.exists_regular_quadrics`' `havoid` demands; the
general conditional R2 theorem consuming them is
`Appendix_FixedPoint.BezoutChain.exists_regular_quadrics_of_unmixed_hlow`
(`Regularity/Avoid/ResultantLemmas.lean`). -/

/-- Step `k = 0` pullback properness for general `G` (no `mkSystem`
narrowing): with the empty generator family (`J = ⊥`),
`noAssPrime_contains_span_zero` gives `¬ span G ≤ P` from `hZd` alone, and
the contrapositive of `span_le_of_comap_comboLin_eq_top` turns this into
the `≠ ⊤` that `ResultantLemmas.exists_regular_quadrics`' `havoid`
demands. No `hlow`, no unmixedness.

## References

* `noAssPrime_contains_span_zero` (`AvoidanceStep.lean`, domain + `hZd`).
* `span_le_of_comap_comboLin_eq_top` above (contrapositive).
* `RegularSequenceDimDrop.span_smul_top`, `RegularityBridge.span_range_eq_ofList_ofFn`. -/
theorem comap_ne_top_zero_general (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (h : Fin 0 → MvPolynomial (Fin (n + 2)) K)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hP : P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))) :
    Submodule.comap (comboLin K G)
      (Submodule.restrictScalars K
        (P : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ := by
  have eJ : (Ideal.ofList (List.ofFn h) •
      (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K)) : Submodule (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K)) = ↑(Ideal.ofList (List.ofFn h)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn h]
    exact RegularSequenceDimDrop.span_smul_top _
  rw [eJ] at hP
  have hJ : Ideal.ofList (List.ofFn h) = Ideal.span (Set.range h) :=
    (RegularityBridge.span_range_eq_ofList_ofFn h).symm
  have hno := noAssPrime_contains_span_zero n K G hZd h _ hJ P hP
  exact fun htop => hno (span_le_of_comap_comboLin_eq_top n K G P htop)

/-- The per-step `≠ ⊤` for general `G` with ungated unmixedness: the literal
L-R2 plug-in recipe (`hAss_of_unmixed` + `hHt_of_hlow` →
`avoid_of_unmixed_hlow` → contrapositive of
`span_le_of_comap_comboLin_eq_top`). At step `k` (`hk : k ≤ n`) with
successive-regular data `hsucc` for the chosen family `h`, explicit
`hunmixed` (every `P ∈ Ass(R ⧸ J)` minimal over `J`) and the
step-independent catenary `hlow` yield the `≠ ⊤` that
`ResultantLemmas.exists_regular_quadrics`' `havoid` demands. (The gated
variant `comap_ne_top_of_step` in the `mkSystem` section below discharges
`k ≤ 1` unconditionally and is what the narrowed R2 inductions consume;
this ungated form serves consumers with full unmixedness.)

## References

* `avoid_of_unmixed_hlow` above (`hAss_of_unmixed` + `hHt_of_hlow` inside).
* `span_le_of_comap_comboLin_eq_top` above (contrapositive).
* `RegularSequenceDimDrop.span_smul_top`, `RegularityBridge.span_range_eq_ofList_ofFn`. -/
theorem comap_ne_top_of_step_unmixed (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (k : ℕ) (hk : k ≤ n)
    (h : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular h)
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range G) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hunmixed : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.ofList (List.ofFn h)),
      P ∈ (Ideal.ofList (List.ofFn h)).minimalPrimes)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hPmem : P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))) :
    Submodule.comap (comboLin K G)
      (Submodule.restrictScalars K
        (P : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ := by
  have eJ : (Ideal.ofList (List.ofFn h) •
      (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K)) : Submodule (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K)) = ↑(Ideal.ofList (List.ofFn h)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn h]
    exact RegularSequenceDimDrop.span_smul_top _
  rw [eJ] at hPmem
  have hJ : Ideal.ofList (List.ofFn h) = Ideal.span (Set.range h) :=
    (RegularityBridge.span_range_eq_ofList_ofFn h).symm
  have hno := avoid_of_unmixed_hlow n K G hZd k hk h hsucc
    _ hJ hunmixed hlow P hPmem
  exact fun htop => hno (span_le_of_comap_comboLin_eq_top n K G P htop)

/-! ## mkSystem narrowing: `k ≤ 1` discharged, `k ≥ 2` explicit -/

/-- L-HSUCC glue (1/2): an `ofList` span of a taken prefix list is the span of
the values below the index. Via `Fin.ofFn_take_eq_take_ofFn` the prefix list
becomes an `ofFn`, hence a range, and `Fin.castLE` identifies that range with
the initial image.

## References

* `Fin.ofFn_take_eq_take_ofFn` (`Mathlib/Data/Fin/Tuple/Take.lean`).
* `RegularityBridge.span_range_eq_ofList_ofFn`.
* `Fin.take_apply`, `Fin.val_castLE`, `Fin.ext`
  (`Mathlib/Data/Fin/Tuple/Take.lean`, core `Fin` API). -/
theorem ofList_take_eq_span_image {R : Type*} [CommRing R] {k : ℕ}
    (h : Fin k → R) (i : Fin k) :
    Ideal.ofList ((List.ofFn h).take (i.val)) =
      Ideal.span (Set.image h {j | j.val < i.val}) := by
  have hm : i.val ≤ k := le_of_lt i.isLt
  rw [← Fin.ofFn_take_eq_take_ofFn hm h, ← RegularityBridge.span_range_eq_ofList_ofFn]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i', rfl⟩
    exact ⟨Fin.castLE hm i', by rw [Fin.val_castLE]; exact i'.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨j.val, hj⟩, ?_⟩
    have e : Fin.castLE hm ⟨j.val, hj⟩ = j := by apply Fin.ext; simp
    change h (Fin.castLE hm ⟨j.val, hj⟩) = h j
    rw [e]

/-- L-HSUCC glue (2/2): per-step `IsSMulRegular` outputs (quotients by
`ofList` of taken prefix lists) repackaged into `SuccessiveSMulRegular` for
the chosen family. This closes the repackaging leaf for every step at once;
the R2 induction feeds its `hreg` here.

## References

* `ofList_take_eq_span_image` above.
* `RegularityBridge.SuccessiveSMulRegular`. -/
theorem hsucc_of_step_outputs {R : Type*} [CommRing R] {k : ℕ}
    (h : Fin k → R)
    (hreg : ∀ j : Fin k, IsSMulRegular
      (R ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn h)) •
        (⊤ : Submodule R R)))
      (h j)) :
    RegularityBridge.SuccessiveSMulRegular h := by
  intro i
  have e : Ideal.ofList (List.take (i.val) (List.ofFn h)) =
      Ideal.span (Set.image h {j | j.val < i.val}) :=
    ofList_take_eq_span_image h i
  have hi := hreg i
  rw [e] at hi
  exact hi

/-- `hAss` with `hunmixed` gated on `2 ≤ k`: `k = 0` via the proved domain
case, `k = 1` via the proved UFD-colon case (`Unmixedness.lean`, applied
here), `k ≥ 2` via the explicit hypothesis (kept, never dropped).

## References

* `mem_minimalPrimes_of_successive_zero`,
  `mem_minimalPrimes_of_successive_singleton` (`Unmixedness.lean`).
* `AssHeightBound.height_eq_of_mem_minimalPrimes`.
* `hAss_of_unmixed` above (ungated shape). -/
theorem hAss_of_hunmixed_ge2 (m : ℕ) (K : Type*) [Field K]
    (k : ℕ) (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (hunmixed_ge2 : 2 ≤ k → ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P.height ≤ (k : ℕ∞) := by
  intro P hP
  have hprime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  by_cases h2 : 2 ≤ k
  · exact le_of_eq (@AssHeightBound.height_eq_of_mem_minimalPrimes _ _ _ _ q hsucc
      J hJ P hprime (hunmixed_ge2 h2 P hP))
  · have hk2 : k < 2 := by omega
    interval_cases k
    · exact le_of_eq (@AssHeightBound.height_eq_of_mem_minimalPrimes _ _ _ _ q hsucc
        J hJ P hprime
        (mem_minimalPrimes_of_successive_zero _ _ _ hsucc _ hJ _ hP))
    · exact le_of_eq (@AssHeightBound.height_eq_of_mem_minimalPrimes _ _ _ _ q hsucc
        J hJ P hprime
        (mem_minimalPrimes_of_successive_singleton _ _ _ hsucc _ hJ _ hP))

/-- Conditional avoidance with `hunmixed` gated on `2 ≤ k`: steps `k = 0, 1`
use only proved inputs (+ the step-independent `hlow`); the only unmixedness
demand left is the explicit `hunmixed_ge2`.

## References

* `AvoidanceStep.noAssPrime_contains_span_of_height_bounds`.
* `hAss_of_hunmixed_ge2`, `hHt_of_hlow` above. -/
theorem avoid_of_hunmixed_ge2 (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (k : ℕ) (hk : k ≤ n)
    (q : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range G) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hunmixed_ge2 : 2 ≤ k → ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range G) ≤ P) :=
  noAssPrime_contains_span_of_height_bounds n K G k hk J
    (hAss_of_hunmixed_ge2 (n + 2) K k q hsucc J hJ hunmixed_ge2)
    (hHt_of_hlow n K G hZd hlow)

/-- The per-step `≠ ⊤` the R2 induction consumes: `hsucc` (from
`hsucc_of_step_outputs`), `hlow`, and `hunmixed` gated on `2 ≤ k`, turned
through the narrowed avoidance plus the `comap`-to-`span` bridge. The
`• ⊤`-submodule quotient of the induction step is identified with the ideal
quotient via `RegularSequenceDimDrop.span_smul_top`.

## References

* `RegularSequenceDimDrop.span_smul_top`, `RegularityBridge.span_range_eq_ofList_ofFn`.
* `avoid_of_hunmixed_ge2`, `span_le_of_comap_comboLin_eq_top` above. -/
theorem comap_ne_top_of_step (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (k : ℕ) (hk : k ≤ n)
    (h : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular h)
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range G) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hunmixed : 2 ≤ k → ∀ (q : Fin k → MvPolynomial (Fin (n + 2)) K)
      (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
      (J : Ideal (MvPolynomial (Fin (n + 2)) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hPmem : P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))) :
    Submodule.comap (comboLin K G)
      (Submodule.restrictScalars K
        (P : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ := by
  have eJ : (Ideal.ofList (List.ofFn h) •
      (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K)) : Submodule (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K)) = ↑(Ideal.ofList (List.ofFn h)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn h]
    exact RegularSequenceDimDrop.span_smul_top _
  rw [eJ] at hPmem
  have hJ : Ideal.ofList (List.ofFn h) = Ideal.span (Set.range h) :=
    (RegularityBridge.span_range_eq_ofList_ofFn h).symm
  have hP : P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.ofList (List.ofFn h)) := hPmem
  have hno := avoid_of_hunmixed_ge2 n K G hZd k hk h hsucc
    _ hJ hlow (fun h2 => hunmixed h2 h hsucc _ hJ) P hP
  exact fun htop => hno (span_le_of_comap_comboLin_eq_top n K G P htop)

/-- Regularity lifts across `R ⧸ ⊥`: a regular element of the domain stays
regular on the quotient by the bottom submodule. Used to turn the t1 input
(`Triangular.mkSystem_isSMulRegular`) into `hsucc` shape.

## References

* `isSMulRegular_iff_right_eq_zero_of_smul`
  (`Mathlib/Algebra/GroupWithZero/Action/Regular.lean`).
* `quot_mk_smul` (`AvoidanceStep.lean`), `Ideal.Quotient.mk_surjective`,
  `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_bot`. -/
theorem isSMulRegular_quot_bot_of_regular (n : ℕ) (K : Type*) [Field K]
    (x : MvPolynomial (Fin (n + 2)) K)
    (hx : IsSMulRegular (MvPolynomial (Fin (n + 2)) K) x) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸
      ((⊥ : Ideal (MvPolynomial (Fin (n + 2)) K)) : Submodule _ _)) x := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [← quot_mk_smul] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hm
  have key : x • H = x • (0 : MvPolynomial (Fin (n + 2)) K) := by
    rw [hm, smul_zero]
  have hH : H = 0 := hx key
  rw [hH]
  exact map_zero _

/-- `hsucc` for a generator singleton, from t1: `G i0 ≠ 0` makes it regular
on the domain, hence on `R ⧸ ⊥`.

## References

* `Triangular.mkSystem_isSMulRegular` (t1, regularity form).
* `isSMulRegular_quot_bot_of_regular` above.
* `RegularSequenceDimDrop.span_smul_top`, `Ideal.span_empty`. -/
theorem hsucc_mkSystem_singleton (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (q : Fin 1 → MvPolynomial (Fin (n + 2)) K)
    (i0 : Fin (n + 1))
    (hq0 : q 0 = mkSystem n K F i0) :
    RegularityBridge.SuccessiveSMulRegular q := by
  intro i
  have ei : i = 0 := Subsingleton.elim i 0
  subst ei
  have hset : Set.image q {j : Fin 1 | j.val < (0 : Fin 1).val} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨j, hj, rfl⟩
    simp only [Set.mem_ofPred_eq] at hj
    have hv : ((0 : Fin 1).val) = 0 := rfl
    rw [hv] at hj
    omega
  rw [hset, Ideal.span_empty]
  have e : ((⊥ : Ideal (MvPolynomial (Fin (n + 2)) K)) •
      (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K)) : Submodule _ _) =
      ((⊥ : Ideal _) : Submodule _ _) := by
    rw [← Ideal.span_empty]
    exact RegularSequenceDimDrop.span_smul_top _
  rw [e, hq0]
  exact isSMulRegular_quot_bot_of_regular n K _
    (Triangular.mkSystem_isSMulRegular n K F i0)

/-- Step `k = 0` pullback properness from the domain step (t1-style `Gᵢ ≠ 0`):
every `P ∈ Ass(R ⧸ ⊥)` is `⊥` (the domain argument), and the coefficient
pullback of `⊥` is the kernel of `comboLin`, which is proper since
`G i0 ≠ 0`. No `hZd`, no `hlow`, no unmixedness.

## References

* `eq_bot_of_mem_associatedPrimes_quot_bot` (`AvoidanceStep.lean`, domain).
* `Triangular.mkSystem_ne_zero` (t1).
* `Definitions.comboLin_apply`; `Finset.sum_eq_single_of_mem`,
  `Pi.single_eq_of_ne`, `Pi.single_eq_same` (as in
  `span_le_of_comap_comboLin_eq_top`).
* `RegularSequenceDimDrop.span_smul_top`, `RegularityBridge.span_range_eq_ofList_ofFn`,
  `Ideal.span_empty`. -/
theorem comap_ne_top_zero_of_t1 (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (h : Fin 0 → MvPolynomial (Fin (n + 2)) K)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hP : P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))) :
    Submodule.comap (comboLin K (mkSystem n K F))
      (Submodule.restrictScalars K
        (P : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ := by
  have hrange : Set.range h = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -⟩ := hx
    exact i.elim0
  have e : (Ideal.ofList (List.ofFn h) •
      (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K)) : Submodule _ _) =
      ((⊥ : Ideal _) : Submodule _ _) := by
    have h1 : Ideal.ofList (List.ofFn h) = Ideal.span (∅ : Set _) := by
      rw [← RegularityBridge.span_range_eq_ofList_ofFn h, hrange]
    rw [h1, RegularSequenceDimDrop.span_smul_top, Ideal.span_empty]
  rw [e] at hP
  have hPB : P = ⊥ := eq_bot_of_mem_associatedPrimes_quot_bot n K ⊥ rfl P hP
  subst hPB
  intro htop
  have hmem : (Pi.single ⟨0, Nat.zero_lt_succ n⟩ (1 : K)) ∈
      Submodule.comap (comboLin K (mkSystem n K F))
        (Submodule.restrictScalars K
          ((⊥ : Ideal (MvPolynomial (Fin (n + 2)) K)) : Submodule _ _)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Submodule.mem_comap] at hmem
  have hmem0 : comboLin K (mkSystem n K F)
      (Pi.single ⟨0, Nat.zero_lt_succ n⟩ (1 : K)) ∈
      (⊥ : Ideal (MvPolynomial (Fin (n + 2)) K)) := hmem
  rw [Ideal.mem_bot] at hmem0
  have h0 : ∀ l ∈ (Finset.univ : Finset (Fin (n + 1))),
      l ≠ ⟨0, Nat.zero_lt_succ n⟩ →
      (((Pi.single ⟨0, Nat.zero_lt_succ n⟩ (1 : K) : Fin (n + 1) → K)) l •
        mkSystem n K F l) = 0 := by
    intro l _ hli
    rw [Pi.single_eq_of_ne hli, zero_smul]
  have heq : comboLin K (mkSystem n K F)
      (Pi.single ⟨0, Nat.zero_lt_succ n⟩ (1 : K))
      = mkSystem n K F ⟨0, Nat.zero_lt_succ n⟩ := by
    rw [comboLin_apply,
      Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0,
      Pi.single_eq_same, one_smul]
  rw [heq] at hmem0
  exact Triangular.mkSystem_ne_zero n K F _ hmem0

/-- (t2a, carried back) Transport of `Triangular.triG_isSMulRegular_mod_of_not_dvd`
across `Triangular.lastVarRingEquiv`: if `X i0` is prime, `X i0 ∤ F i0`,
`X i1 ≠ 0` and `X i0 ∤ X i1`, then `G i1` is regular mod `(G i0)` on the
`MvPolynomial` side. This is the t2a half of the dichotomy at the `mkSystem`
instantiation (the t2b half is `Triangular.mkSystem_isSMulRegular_mod_of_dvd`);
the transport mirrors `Triangular.isSMulRegular_mvPolynomial_mod_of_dvd`.

## References

* `Triangular.triG_isSMulRegular_mod_of_not_dvd`, `Triangular.lastVarRingEquiv`,
  `Triangular.lastVarRingEquiv_apply`, `Triangular.lastVarEquiv_mkSystem`.
* `isSMulRegular_iff_right_eq_zero_of_smul`,
  `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`,
  `Ideal.mem_span_singleton` (as in the mirrored proof). -/
theorem isSMulRegular_mkSystem_mod_of_not_dvd (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i0 i1 : Fin (n + 1))
    (hprime0 : Prime (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K))
    (hndvd0 : ¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣ F i0)
    (ha1 : (MvPolynomial.X i1 : MvPolynomial (Fin (n + 1)) K) ≠ 0)
    (hndvd1 : ¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣
      MvPolynomial.X i1) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span {mkSystem n K F i0})
      (Ideal.Quotient.mk (Ideal.span {mkSystem n K F i0})
        (mkSystem n K F i1)) := by
  have h0 : Triangular.lastVarRingEquiv n K (mkSystem n K F i0) =
      Triangular.triG (F i0) (MvPolynomial.X i0) := by
    rw [Triangular.lastVarRingEquiv_apply]
    exact Triangular.lastVarEquiv_mkSystem n K F i0
  have h1 : Triangular.lastVarRingEquiv n K (mkSystem n K F i1) =
      Triangular.triG (F i1) (MvPolynomial.X i1) := by
    rw [Triangular.lastVarRingEquiv_apply]
    exact Triangular.lastVarEquiv_mkSystem n K F i1
  have hreg : IsSMulRegular
      (Polynomial (MvPolynomial (Fin (n + 1)) K) ⧸
        Ideal.span {Triangular.triG (F i0) (MvPolynomial.X i0)})
      (Ideal.Quotient.mk
        (Ideal.span {Triangular.triG (F i0) (MvPolynomial.X i0)})
        (Triangular.triG (F i1) (MvPolynomial.X i1))) :=
    Triangular.triG_isSMulRegular_mod_of_not_dvd hprime0 hndvd0 ha1 hndvd1
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg ⊢
  intro m hm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  have hwx : Triangular.lastVarRingEquiv n K (mkSystem n K F i1 * x) =
      Triangular.triG (F i1) (MvPolynomial.X i1) *
        Triangular.lastVarRingEquiv n K x := by rw [map_mul, h1]
  have hw0 : Triangular.lastVarRingEquiv n K (mkSystem n K F i0 * w) =
      Triangular.triG (F i0) (MvPolynomial.X i0) *
        Triangular.lastVarRingEquiv n K w := by rw [map_mul, h0]
  have hmemS : Triangular.triG (F i1) (MvPolynomial.X i1) *
      Triangular.lastVarRingEquiv n K x ∈
      Ideal.span {Triangular.triG (F i0) (MvPolynomial.X i0)} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨Triangular.lastVarRingEquiv n K w, ?_⟩
    rw [← hwx, ← hw0, hw]
  have hsmul : Ideal.Quotient.mk
      (Ideal.span {Triangular.triG (F i0) (MvPolynomial.X i0)})
      (Triangular.triG (F i1) (MvPolynomial.X i1)) •
      Ideal.Quotient.mk
        (Ideal.span {Triangular.triG (F i0) (MvPolynomial.X i0)})
        (Triangular.lastVarRingEquiv n K x) = 0 := by
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hmemS
  have hx0 := hreg _ hsmul
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx0
  obtain ⟨v, hv⟩ := hx0
  have hcancel : Triangular.lastVarRingEquiv n K
      ((Triangular.lastVarRingEquiv n K).symm v) = v :=
    (Triangular.lastVarRingEquiv n K).toEquiv.apply_symm_apply v
  have key : Triangular.lastVarRingEquiv n K
      (mkSystem n K F i0 * (Triangular.lastVarRingEquiv n K).symm v) =
      Triangular.lastVarRingEquiv n K x := by
    rw [map_mul, h0, hcancel, hv]
  have hx : mkSystem n K F i0 * (Triangular.lastVarRingEquiv n K).symm v = x :=
    (Triangular.lastVarRingEquiv n K).toEquiv.injective key
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨(Triangular.lastVarRingEquiv n K).symm v, hx.symm⟩

/-- `hsucc` for the generator pair, from the t2a/t2b dichotomy at the
`mkSystem` instantiation: `G i0` is regular on `R ⧸ ⊥` (t1 transport) and
`G i1` is regular mod `(G i0)` (t2a carried back above, or t2b
`Triangular.mkSystem_isSMulRegular_mod_of_dvd`). Step 3+ (t3) is explicitly
out of scope: no claim about further generators is made here.

## References

* `Triangular.mkSystem_isSMulRegular` (t1, first component).
* `isSMulRegular_mkSystem_mod_of_not_dvd` above (t2a),
  `Triangular.mkSystem_isSMulRegular_mod_of_dvd` (t2b).
* `isSMulRegular_quot_bot_of_regular`, `RegularSequenceDimDrop.span_smul_top`,
  `Ideal.span_empty`, `Set.image_singleton`. -/
theorem hsucc_mkSystem_pair_of_dichotomy (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (q : Fin 2 → MvPolynomial (Fin (n + 2)) K)
    (i0 i1 : Fin (n + 1))
    (hq0 : q ⟨0, by omega⟩ = mkSystem n K F i0)
    (hq1 : q ⟨1, by omega⟩ = mkSystem n K F i1)
    (hprime0 : Prime (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K))
    (hndvd1 : ¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣
      MvPolynomial.X i1)
    (hdich : (¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣ F i0 ∧
        (MvPolynomial.X i1 : MvPolynomial (Fin (n + 1)) K) ≠ 0) ∨
      (∃ L0 : MvPolynomial (Fin (n + 1)) K,
        F i0 = MvPolynomial.X i0 * L0 ∧
        MvPolynomial.X i0 * F i1 - MvPolynomial.X i1 * F i0 ≠ 0)) :
    RegularityBridge.SuccessiveSMulRegular q := by
  intro i
  have h01 : i.val = 0 ∨ i.val = 1 := by have h := i.isLt; omega
  rcases h01 with h0 | h1
  · have ei : i = ⟨0, by omega⟩ := Fin.ext h0
    have hq0' : q i = mkSystem n K F i0 := by rw [ei]; exact hq0
    have hset : Set.image q {j : Fin 2 | j.val < i.val} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨j, hj, rfl⟩
      simp only [Set.mem_ofPred_eq] at hj
      omega
    rw [hset, Ideal.span_empty]
    have e : ((⊥ : Ideal (MvPolynomial (Fin (n + 2)) K)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K)) : Submodule _ _) =
        ((⊥ : Ideal _) : Submodule _ _) := by
      rw [← Ideal.span_empty]
      exact RegularSequenceDimDrop.span_smul_top _
    rw [e, hq0']
    exact isSMulRegular_quot_bot_of_regular n K _
      (Triangular.mkSystem_isSMulRegular n K F i0)
  · have ei : i = ⟨1, by omega⟩ := Fin.ext h1
    have hq1' : q i = mkSystem n K F i1 := by rw [ei]; exact hq1
    have hv0 : ((⟨0, by omega⟩ : Fin 2).val) = 0 := rfl
    have him : Set.image q {j : Fin 2 | j.val < i.val} =
        {mkSystem n K F i0} := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hjv : j.val = 0 := by omega
        have ej : j = ⟨0, by omega⟩ := Fin.ext hjv
        rw [ej]
        exact hq0
      · intro hy
        refine ⟨⟨0, by omega⟩, ?_, hq0.trans hy.symm⟩
        rw [hv0]
        omega
    rw [him, RegularSequenceDimDrop.span_smul_top, hq1']
    rcases hdich with ⟨hndvd0, ha1⟩ | ⟨L0, hF0, hM⟩
    · exact isSMulRegular_mkSystem_mod_of_not_dvd n K F i0 i1 hprime0 hndvd0
        ha1 hndvd1
    · exact Triangular.mkSystem_isSMulRegular_mod_of_dvd n K F i0 i1 L0 hF0 hM
        hprime0 hndvd1

/-- `k = 2` avoidance at the generator pair: `hsucc` from the t2a/t2b
dichotomy, `hunmixed₂` explicit. This pins exactly which hypotheses remain
for `k = 2` (the first explicit step): dichotomy data + `hlow` +
`hunmixed₂` (+ `2 ≤ n`, `hZd`).

## References

* `avoid_of_unmixed_hlow` (with `k := 2`).
* `hsucc_mkSystem_pair_of_dichotomy` above. -/
theorem avoid_mkSystem_pair (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (q : Fin 2 → MvPolynomial (Fin (n + 2)) K)
    (i0 i1 : Fin (n + 1))
    (hq0 : q ⟨0, by omega⟩ = mkSystem n K F i0)
    (hq1 : q ⟨1, by omega⟩ = mkSystem n K F i1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hk : 2 ≤ n)
    (hprime0 : Prime (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K))
    (hndvd1 : ¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣
      MvPolynomial.X i1)
    (hdich : (¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣ F i0 ∧
        (MvPolynomial.X i1 : MvPolynomial (Fin (n + 1)) K) ≠ 0) ∨
      (∃ L0 : MvPolynomial (Fin (n + 1)) K,
        F i0 = MvPolynomial.X i0 * L0 ∧
        MvPolynomial.X i0 * F i1 - MvPolynomial.X i1 * F i0 ≠ 0))
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range (mkSystem n K F)) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hunmixed2 : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range (mkSystem n K F)) ≤ P) :=
  avoid_of_unmixed_hlow n K (mkSystem n K F) hZd 2 hk q
    (hsucc_mkSystem_pair_of_dichotomy n K F q i0 i1 hq0 hq1 hprime0 hndvd1
      hdich)
    J hJ hunmixed2 hlow

/-! ## Z2 register: `UnmixednessAtLengthTwo`, the first-open rung blocker

The Z2 rung-avoider investigation proved no proof by design; its auditable
output is this register. Rung status for pair-quotient unmixedness (every
`P ∈ Ass(R ⧸ J)` minimal over `J`):

* `k = 0`: closed — the domain case (`isSMulRegular_quot_bot_of_regular`,
 , + `hsucc_mkSystem_singleton`).
* `k = 1`: closed — nonzero `x` in a UFD-domain
  (`VariableInductionCM.varUnmixedOneResidual_of_ne_zero`,
  `Regularity/CohenMacaulayLink/VariableInductionCM.lean`).
* `k = 2`: open — `UnmixednessAtLengthTwo` below, the blocker. Its first consumer is
  `avoid_mkSystem_pair` (`k = 2` dichotomy avoidance), restated here
  as `avoid_mkSystem_pair_of_hunmixedTwo` conditional-exact on the register.
  (`hlow` discharges via `ResultantLemmas.hlow_general`,
  `Regularity/Avoid/ResultantLemmas.lean`, unconditional — retained explicit
  for interface stability.)
* `k > 2`: open — `hunmixed_ge2` (gated `2 ≤ k`).

Why Mathlib v4.34.0 cannot supply it (all re-verified against the
pinned toolchain): `CohenMacaulay` 0 hits; `Catenary` 0 hits; the only
`Unmixed` hits are infinite-place ramification
(`NumberTheory/NumberField/InfinitePlace/`, unrelated to
unmixedness-of-quotients). No CM / unmixedness / catenary input exists to
discharge the register.

Status: `UnmixednessAtLengthTwo` is a recorded residual (`def`, no proof claim);
`avoid_mkSystem_pair_of_hunmixedTwo` conditional-exact on `[UnmixednessAtLengthTwo]`.

## References

* `avoid_mkSystem_pair`  for the consumed ∀-shape.
* `Regularity/CohenMacaulayLink/VariableInductionCM.lean` (`k = 1` closure).
* `Regularity/Avoid/ResultantLemmas.lean` (`hlow_general`, unconditional).
* `BridgeToFixedPoint/FinalDischargeHub.lean` (`hunmixed_pair` span/J
  bridges, conditional on `[hker]` — the alternate conditional route;
  absorbs the former `FinalWire.lean`).
* `BridgeToFixedPoint/FinalDischargeHub.lean` (`successive_of_rungAvoid` — the rung
  skeleton whose fixed-element rungs `≥ 1` stay open beyond this register).

Residual register (verbatim): closed this lane: [Z2 rung-avoider
investigation as an auditable register (`UnmixednessAtLengthTwo` + shape-exact
consumer restatement)]. Open: [`UnmixednessAtLengthTwo` at `k = 2` (needs CM/unmixed
theory absent from Mathlib v4.34.0)]; [`hunmixed_ge2` at `k > 2` (same
critical path)].
-/

/-- Z2 register: unmixedness at the pair step — every associated
prime of `R ⧸ J` is minimal over `J`, in the exact ∀-shape consumed by
`avoid_mkSystem_pair`. A `def` (no proof claim); the first-open
rung blocker (`k = 0` / `k = 1` closed, see the section header).

Status: recorded residual (no proof claim). -/
def UnmixednessAtLengthTwo (n : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) : Prop :=
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
    (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes

/-- `k = 2` avoidance at the generator pair, conditional-exact on the Z2
register: `avoid_mkSystem_pair`  with its `hunmixed2` hypothesis
folded to `UnmixednessAtLengthTwo` (definitionally the same ∀-shape). Proves the
register is exactly what the first explicit step consumes.

Conditional on exactly `[UnmixednessAtLengthTwo]`.

## References

* `avoid_mkSystem_pair`. -/
theorem avoid_mkSystem_pair_of_hunmixedTwo (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (q : Fin 2 → MvPolynomial (Fin (n + 2)) K)
    (i0 i1 : Fin (n + 1))
    (hq0 : q ⟨0, by omega⟩ = mkSystem n K F i0)
    (hq1 : q ⟨1, by omega⟩ = mkSystem n K F i1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q))
    (hk : 2 ≤ n)
    (hprime0 : Prime (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K))
    (hndvd1 : ¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣
      MvPolynomial.X i1)
    (hdich : (¬ (MvPolynomial.X i0 : MvPolynomial (Fin (n + 1)) K) ∣ F i0 ∧
        (MvPolynomial.X i1 : MvPolynomial (Fin (n + 1)) K) ≠ 0) ∨
      (∃ L0 : MvPolynomial (Fin (n + 1)) K,
        F i0 = MvPolynomial.X i0 * L0 ∧
        MvPolynomial.X i0 * F i1 - MvPolynomial.X i1 * F i0 ≠ 0))
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range (mkSystem n K F)) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hU : UnmixednessAtLengthTwo n K J) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range (mkSystem n K F)) ≤ P) :=
  avoid_mkSystem_pair n K F hZd q i0 i1 hq0 hq1 J hJ hk hprime0 hndvd1 hdich
    hlow hU

#print axioms UnmixednessAtLengthTwo
#print axioms avoid_mkSystem_pair_of_hunmixedTwo

end AvoidanceApply
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
