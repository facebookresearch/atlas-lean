/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParameters
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.VariableInductionCM

/-!
# C1 block of the CM-link design note: `R_Q` is Cohen–Macaulay (partial)

Proves the C1 block: `R_Q =
Localization.AtPrime Q` is Cohen–Macaulay, i.e. `IsCM` below (verbatim copy
of the design note §2 predicate, reusing proved `GradeDepthFragment.grade`).

## Status: partial (exact residual stated)

* Unconditional, dim ≤ 1: `isCM_atPrime_of_dim_le_one` (via the dim-0 and
  dim-1 cases). The dim-0 case uses the empty regular sequence; the dim-1
  case uses `VariableInductionCM.exists_isSMulRegular_mem_maximal` (in a domain of
  positive dimension, `𝔪` carries a regular element) plus
  `singleton_isRegular_of_mem_maximal`, closed by the proved capstone
  `VariableInductionCM.grade_eq_dim_of_maximal_regular`.
* Conditional, full C1: `isCM_atPrime_of_regularSopExists` proves `IsCM R_Q`
  from the explicit residual `RegularSopExists` (a length-`dim` regular
  sequence spanning `𝔪_Q`).
* Residual (route-K (i), Serre direction, design note F8 sketch): `RegularSopExists`
  in dimension ≥ 2 — the SystemOfParameters minimal generators
  (`mingens_span_dim_atPrime`, from
  `SystemOfParameters.exists_list_ofList_maximalIdeal_atPrime`) form a regular
  sequence. This is large-scale Serre-level content (`IsRegularLocalRing`
  is defined as embdim = dim with zero homological content); it is not
  closed here. Restructure-(b) (regular-quotient induction consuming C3)
  was not pursued: it needs C3, violating the C1 ∥ C2/C3 independence this
  lane was dealt, and no valid `C3 → C1` induction could be reconstructed
  from the one-line sketch.

## What this file proves

* `IsCM` — verbatim design note-§2 predicate (see header note on the def).
* `isCM_atPrime_iff_depthEqDimAt` — C1 closes the SPEC address `DepthEqDimAt`
  (GradeDepthFragment:957) by unfolding (`Iff.rfl`).
* `isCM_atPrime_of_dim_eq_zero`, `isCM_atPrime_of_dim_eq_one`,
  `isCM_atPrime_of_dim_le_one` — unconditional dim-≤-1 close.
* `mingens_span_dim_atPrime` — SystemOfParameters mingens repackage (span + dim
  equation; the regularity conjunct is exactly the residual).
* `RegularSopExists` — the exact sketch residual (route-K (i)).
* `isCM_atPrime_of_regularSopExists` — conditional full C1 on the residual.

## Circularity

This file (and its project imports `GradeDepthFragment`, `SystemOfParameters`,
`VariableInductionCM`)
uses no graded machinery and no crux-ring members: a verification grep for
the forbidden identifiers is empty here, and the three imports are verified
free of those strings. In particular the only `DepthEqDimAt` derivations
elsewhere in the tree (Rees/Ge3 legs, conditional on crux hypotheses) are
not used.

## Status

`isCM_atPrime_of_dim_eq_zero/one/le_one`, `mingens_span_dim_atPrime`,
`isCM_atPrime_iff_depthEqDimAt`: unconditional.
`isCM_atPrime_of_regularSopExists`: conditional-exact on `[RegularSopExists]`.
`RegularSopExists`: residual (route-K (i) sketch).

## References

`GradeDepthFragment.grade` (:292), `grade_le_ringKrullDim` (:417),
`mem_gradeSet_of_isRegular`/`le_grade_of_mem_gradeSet` (:325/:332),
`DepthEqDimAt` (:957). `SystemOfParameters.exists_list_ofList_maximalIdeal_atPrime`
(:185; Finset form:168; graded-construction-free) and the TC probe (:151);
`dimEmbAtAss_unconditional` (RegularDimEmb:210) is the Ass-gated twin of
the dim equation used here in List form.
`VariableInductionCM.grade_eq_dim_of_maximal_regular` (:758),
`singleton_isRegular_of_mem_maximal` (:354),
`exists_isSMulRegular_mem_maximal` (:376), `empty_isRegular` (:346).
Instance automation mirrors `supPathDepth_atPrime_of_dimLE1`
(PathDepthDim1:179).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CMQuotientPartial

open RingTheory.Sequence

/-- Cohen–Macaulay (local): grade w.r.t. 𝔪 equals Krull dimension.
Coercion dance matches proved `DepthEqDimAt` (GradeDepthFragment:957).

verbatim copy of the §2 predicate for the C1 lane. Header note: the assembly owns
the canonical `IsCM`; this copy is definitionally equal to it (same
`GradeDepthFragment.grade` equation) and is to be unified with the canonical
predicate by defeq when the C1–C3 assembly proves — no transport lemma is
needed beyond `Iff.rfl`-style unfolding. -/
def IsCM (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  ((GradeDepthFragment.grade R R (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞)
    = ringKrullDim R

/-- TC probe (PathDepthDim1:179 pattern): the local-ring instance for `R_Q`
is automatic. -/
example (m : ℕ) (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin m) K))
    [Q.IsPrime] : IsLocalRing (Localization.AtPrime Q) := inferInstance

/-- TC probe: the Noetherian instance for `R_Q` (localization preserves
Noetherian) is automatic. -/
example (m : ℕ) (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin m) K))
    [Q.IsPrime] : IsNoetherianRing (Localization.AtPrime Q) := inferInstance

/-- TC probe: `R_Q` is nontrivial (via `IsLocalRing`). -/
example (m : ℕ) (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin m) K))
    [Q.IsPrime] : Nontrivial (Localization.AtPrime Q) := inferInstance

/-- TC probe (SystemOfParameters:151 pattern): the regular-local instance for `R_Q`
is automatic. -/
example (m : ℕ) (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin m) K))
    [Q.IsPrime] : IsRegularLocalRing (Localization.AtPrime Q) := inferInstance

/-- C1 closes the SPEC address `DepthEqDimAt` (GradeDepthFragment:957) by unfolding:
the two predicates are the same `grade`/`dim` equation.
-/
theorem isCM_atPrime_iff_depthEqDimAt (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    IsCM (Localization.AtPrime Q) ↔ GradeDepthFragment.DepthEqDimAt m K Q := Iff.rfl

#print axioms isCM_atPrime_iff_depthEqDimAt

/-- Dim-0 case, unconditional: the empty sequence is regular
(`VariableInductionCM.empty_isRegular`) and maximal, closed by the proved capstone
`VariableInductionCM.grade_eq_dim_of_maximal_regular`. -/
theorem isCM_atPrime_of_dim_eq_zero (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hdim : ringKrullDim (Localization.AtPrime Q) = 0) :
    IsCM (Localization.AtPrime Q) := by
  have hmem : ∀ r ∈ ([] : List (Localization.AtPrime Q)),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    fun r hr => (List.not_mem_nil hr).elim
  have hreg : IsRegular (Localization.AtPrime Q) [] :=
    VariableInductionCM.empty_isRegular
  have hdimcast : ((((List.length ([] : List (Localization.AtPrime Q)) : ℕ)) : ℕ∞) :
      WithBot ℕ∞) = ringKrullDim (Localization.AtPrime Q) := by
    simp only [List.length_nil]
    rw [hdim, WithBot.coe_natCast]
    exact Nat.cast_zero
  exact VariableInductionCM.grade_eq_dim_of_maximal_regular hmem hreg hdimcast

#print axioms isCM_atPrime_of_dim_eq_zero

/-- Dim-1 case, unconditional: the domain supplies a regular element in `𝔪`
(`VariableInductionCM.exists_isSMulRegular_mem_maximal`), which is a length-1
regular sequence (`singleton_isRegular_of_mem_maximal`), closed by the
proved capstone. -/
theorem isCM_atPrime_of_dim_eq_one (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hdim : ringKrullDim (Localization.AtPrime Q) = 1) :
    IsCM (Localization.AtPrime Q) := by
  have hdomI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_of_local_atPrime (P := Q) inferInstance
  have hdimne : ringKrullDim (Localization.AtPrime Q) ≠ 0 := by
    rw [hdim]
    simp
  obtain ⟨x, hxm, hxreg⟩ :=
    @VariableInductionCM.exists_isSMulRegular_mem_maximal _ _ hdomI _ hdimne
  have hreg : IsRegular (Localization.AtPrime Q) [x] :=
    VariableInductionCM.singleton_isRegular_of_mem_maximal hxm hxreg
  have hmem : ∀ r ∈ [x], r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hxm
  have hdimcast : ((((List.length [x] : ℕ)) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime Q) := by
    simp only [List.length_singleton]
    rw [hdim, WithBot.coe_natCast]
    exact Nat.cast_one
  exact VariableInductionCM.grade_eq_dim_of_maximal_regular hmem hreg hdimcast

#print axioms isCM_atPrime_of_dim_eq_one

/-- Dim-≤-1 close, unconditional: `R_Q` is nontrivial so its dimension is
`↑d` for `d : ℕ∞`; `d ≤ 1` forces `d = 0 ∨ d = 1`, dispatching to the two
cases above. -/
theorem isCM_atPrime_of_dim_le_one (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hdim : ringKrullDim (Localization.AtPrime Q) ≤ 1) :
    IsCM (Localization.AtPrime Q) := by
  have hne : ringKrullDim (Localization.AtPrime Q) ≠ ⊥ := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact (Module.supportDim_ne_bot_iff_nontrivial _ _).mpr inferInstance
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd, ← WithBot.coe_one, WithBot.coe_le_coe] at hdim
  have hd01 : d = 0 ∨ d = 1 := by
    have htop : d ≠ ⊤ := by
      rintro rfl
      simp at hdim
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← Nat.cast_one, ENat.natCast_le_natCast] at hdim
    interval_cases n
    · left; simp
    · right; simp
  rcases hd01 with rfl | rfl
  · have hdim0 : ringKrullDim (Localization.AtPrime Q) = 0 := by
      rw [← hd]
      exact WithBot.coe_zero
    exact isCM_atPrime_of_dim_eq_zero m K Q hdim0
  · have hdim1 : ringKrullDim (Localization.AtPrime Q) = 1 := by
      rw [← hd]
      exact WithBot.coe_one
    exact isCM_atPrime_of_dim_eq_one m K Q hdim1

#print axioms isCM_atPrime_of_dim_le_one

/-- SystemOfParameters mingens repackage (design note §3 C1 inputs): a `List` spanning
`𝔪_Q` whose length is the Krull dimension. This is
`SystemOfParameters.exists_list_ofList_maximalIdeal_atPrime` (:185; Finset form
:168) with the middle `spanFinrank` equation dropped; the dim equation is
the List-form twin of `dimEmbAtAss_unconditional` (RegularDimEmb:210).
The missing conjunct — regularity of the list — is exactly `RegularSopExists`.
-/
theorem mingens_span_dim_atPrime (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ∃ rs : List (Localization.AtPrime Q),
      Ideal.ofList rs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧
        (rs.length : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime Q) := by
  obtain ⟨rs, hspan, _, hdim⟩ :=
    SystemOfParameters.exists_list_ofList_maximalIdeal_atPrime Q
  exact ⟨rs, hspan, hdim⟩

#print axioms mingens_span_dim_atPrime

/-- Residual (route-K (i), Serre direction; design note F8 sketch): a
length-`dim` regular sequence spanning `𝔪_Q`. `mingens_span_dim_atPrime`
provides the span + dim equation; the `IsRegular` conjunct is the
large-scale Serre content (minimal generators of `𝔪_Q` form a regular
sequence) and is not closed here. -/
def RegularSopExists (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] : Prop :=
  ∃ rs : List (Localization.AtPrime Q),
    Ideal.ofList rs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime Q) ∧
        IsRegular (Localization.AtPrime Q) rs

/-- Full C1 conditional on the residual: a length-`dim` regular sequence in
`𝔪_Q` is a maximal `GradeSet` witness, closed by the proved capstone
`VariableInductionCM.grade_eq_dim_of_maximal_regular`.

Conditional on exactly `[RegularSopExists]`. -/
theorem isCM_atPrime_of_regularSopExists (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hsop : RegularSopExists m K Q) :
    IsCM (Localization.AtPrime Q) := by
  obtain ⟨rs, hspan, hlen, hreg⟩ := hsop
  have hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    intro r hr
    have hsr : r ∈ Ideal.ofList rs := Ideal.subset_span hr
    rw [hspan] at hsr
    exact hsr
  have hdimcast : ((((rs.length : ℕ)) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime Q) := by
    rw [← hlen]
    exact WithBot.coe_natCast rs.length
  exact VariableInductionCM.grade_eq_dim_of_maximal_regular hmem hreg hdimcast

#print axioms isCM_atPrime_of_regularSopExists

end CMQuotientPartial
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
