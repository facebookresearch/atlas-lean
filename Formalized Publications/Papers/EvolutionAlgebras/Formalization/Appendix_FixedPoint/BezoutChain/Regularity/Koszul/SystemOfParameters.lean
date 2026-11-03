/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# System of parameters for the regular local ring `R_P` (Koszul-plan step A1)

Step A1 of the scoped Koszul/AB plan (A1–A6): extract a system of parameters
for the regular local ring `R_P = Localization.AtPrime P` — a generating set
of the maximal ideal with exactly `d = ringKrullDim R_P` elements. All inputs
are free per probe (see the `GradeDepthFragment` G-(iii)(a) ledger: `IsRegularRing K`
via Dedekind, `MvPolynomial.isRegularRing_of_isRegularRing`, and
`IsRegularRing.isRegularLocalRing_localization` are all automatic).

* General regular-local engine (§1): `exists_finset_span_maximalIdeal` (a
  `Finset` spanning the maximal ideal, `card = spanFinrank`, hence
  `(card : WithBot ℕ∞) = ringKrullDim R` by regularity) and
  `exists_list_ofList_maximalIdeal` (the same data as a `List`, via
  `Ideal.ofList`).
* `R_P` specialization (§2): `exists_finset_span_maximalIdeal_atPrime` and
  `exists_list_ofList_maximalIdeal_atPrime` for
  `P : Ideal (MvPolynomial (Fin m) K)` prime over a field, plus the
  `inferInstance` checks that `IsRegularLocalRing (Localization.AtPrime P)`
  and `UniqueFactorizationMonoid (Localization.AtPrime P)` are automatic.

Shape for step A2 (Koszul complex on the sop): A2 consumes
`exists_list_ofList_maximalIdeal_atPrime` with `d := rs.length`, giving
`Ideal.ofList rs = maximalIdeal R_P` (the `List` form `IsRegular` and the
`KoszulFrag` cone data consume) together with both the pure-`ℕ` equation
`rs.length = spanFinrank` and the dimension equation
`(rs.length : WithBot ℕ∞) = ringKrullDim R_P`.

## References

Project (read-only):
* `Regularity/Grade/GradeDepthFragment.lean` G-(iii)(a) ledger (`IsRegularRing K` via
  Dedekind at `RegularLocalRing/Defs.lean`, `MvPolynomial` regularity,
  automatic `IsRegularLocalRing (Localization.AtPrime P)`).
* `Regularity/Koszul/AugmentedConeStep.lean` (`AugmentedConeStep`) + Mathlib's
  `List`-based `IsRegular` API that fixes the A2 input shape.

Mathlib (`lean-toolchain` pins `v4.34.0`):
* `IsRegularLocalRing` class (`RingTheory/RegularLocalRing/Defs.lean`)
  and `isRegularLocalRing_iff`.
* `IsRegularRing.isRegularLocalRing_localization` (`Defs.lean`,
  `attribute [instance low]`).
* `MvPolynomial.isRegularRing_of_isRegularRing` (`Polynomial.lean`).
* `Submodule.FG.exists_span_finset_card_eq_spanFinrank`
  (`Algebra/Module/SpanRank.lean`).
* `Ideal.fg_of_isNoetherianRing` (`RingTheory/Noetherian/Defs.lean`).
* `Ideal.ofList` (`RingTheory/Regular/RegularSequence.lean`).
* `ringKrullDim` (`RingTheory/KrullDimension/Basic.lean`).
* `Ideal.span` abbrev (`RingTheory/Ideal/Span.lean`).
* `Finset.length_toList` (`Data/Finset/Card.lean`),
  `Finset.mem_toList` (`Data/Finset/Dedup.lean`).
* `UniqueFactorizationMonoid (Localization S)` instance
  (`GroupTheory/MonoidLocalization/UniqueFactorization.lean`).
* `MvPolynomial.uniqueFactorizationMonoid` instance
  (`RingTheory/Polynomial/UniqueFactorization.lean`).

## Status

* `exists_finset_span_maximalIdeal`: unconditional.
* `exists_list_ofList_maximalIdeal`: unconditional.
* `exists_finset_span_maximalIdeal_atPrime`: unconditional.
* `exists_list_ofList_maximalIdeal_atPrime`: unconditional.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SystemOfParameters

/-! ## §1 General regular-local engine -/

/-- System of parameters as a `Finset`: the maximal ideal of a regular local
ring is spanned by `spanFinrank` elements, hence by `dim` elements.


## References

* `Submodule.FG.exists_span_finset_card_eq_spanFinrank`,
  `Ideal.fg_of_isNoetherianRing`, `isRegularLocalRing_iff` (addresses above). -/
theorem exists_finset_span_maximalIdeal (R : Type*) [CommRing R]
    [IsRegularLocalRing R] :
    ∃ s : Finset R, Ideal.span (↑s : Set R) = IsLocalRing.maximalIdeal R ∧
      s.card = (IsLocalRing.maximalIdeal R).spanFinrank ∧
      (s.card : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R))
  have hreg := (isRegularLocalRing_iff R).mp inferInstance
  refine ⟨s, hspan, hcard, ?_⟩
  rw [hcard]
  exact hreg

/-- System of parameters as a `List`: the A2 input shape. `Ideal.ofList rs`
is the maximal ideal, with `rs.length = spanFinrank` (pure `ℕ`, for `Fin`- or
induction-based Koszul indexing with `d := rs.length`) and
`(rs.length : WithBot ℕ∞) = ringKrullDim R` (the dimension equation).


## References

* `exists_finset_span_maximalIdeal` (this file), `Ideal.ofList`,
  `Finset.length_toList`, `Finset.mem_toList` (addresses above). -/
theorem exists_list_ofList_maximalIdeal (R : Type*) [CommRing R]
    [IsRegularLocalRing R] :
    ∃ rs : List R, Ideal.ofList rs = IsLocalRing.maximalIdeal R ∧
      rs.length = (IsLocalRing.maximalIdeal R).spanFinrank ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨s, hspan, hcard, hdim⟩ := exists_finset_span_maximalIdeal R
  refine ⟨s.toList, ?_, ?_, ?_⟩
  · have hset : { r | r ∈ s.toList } = (↑s : Set R) :=
      Set.ext fun _ => Finset.mem_toList
    change Ideal.span { r | r ∈ s.toList } = _
    rw [hset]
    exact hspan
  · rw [Finset.length_toList]
    exact hcard
  · rw [Finset.length_toList]
    exact hdim

/-! ## §2 The `R_P` specialization -/

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Probe-confirmed (GradeDepthFragment G-(iii)(a) ledger): the regular-local instance
for `R_P` is automatic. -/
example : IsRegularLocalRing (Localization.AtPrime P) := inferInstance

/-- Probe-confirmed: the UFD instance for `R_P` is automatic
(`MvPolynomial.uniqueFactorizationMonoid` + the general localization-UFD
instance). -/
example : UniqueFactorizationMonoid (Localization.AtPrime P) := inferInstance

/-- System of parameters for `R_P` as a `Finset`.

regular-local instance is automatic).

## References

* `exists_finset_span_maximalIdeal` (§1); the instance chain is
  `IsRegularRing K` (Dedekind) → `MvPolynomial.isRegularRing_of_isRegularRing`
  → `IsRegularRing.isRegularLocalRing_localization` (addresses above). -/
theorem exists_finset_span_maximalIdeal_atPrime :
    ∃ s : Finset (Localization.AtPrime P),
      Ideal.span (↑s : Set (Localization.AtPrime P)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
        s.card = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank ∧
        (s.card : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime P) :=
  exists_finset_span_maximalIdeal (Localization.AtPrime P)

/-- System of parameters for `R_P` as a `List`: the exact A2 input shape
(`d := rs.length`).

regular-local instance is automatic).

## References

* `exists_list_ofList_maximalIdeal` (§1). -/
theorem exists_list_ofList_maximalIdeal_atPrime :
    ∃ rs : List (Localization.AtPrime P),
      Ideal.ofList rs = IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
        rs.length =
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank ∧
        (rs.length : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime P) :=
  exists_list_ofList_maximalIdeal (Localization.AtPrime P)

#print axioms exists_finset_span_maximalIdeal
#print axioms exists_list_ofList_maximalIdeal
#print axioms exists_finset_span_maximalIdeal_atPrime
#print axioms exists_list_ofList_maximalIdeal_atPrime

end SystemOfParameters
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
