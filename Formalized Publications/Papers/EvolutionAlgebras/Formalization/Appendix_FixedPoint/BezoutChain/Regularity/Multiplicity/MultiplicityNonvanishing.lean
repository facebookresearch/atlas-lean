/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective

/-!
# Multiplicity-nonvanishing for the quotient Hilbert function (R2)

R2 milestone file: the `hmult` input that `GradedSurjectionInjective` §10
(`hsAssemble_ker_eq_bot_of_mult`) consumes, for the concrete quotient Hilbert
function of `S ⧸ ker` where `S = κ[t₁..t_d]` and `ker` is the kernel of the
M4b graded surjection. Proving `hmult` needs `dim (S ⧸ ker) = d` (via
`quotKerEquiv` transfer) plus `dim gr = dim R = d` plus Hilbert-polynomial
leading-coefficient theory; proves clean verified milestones toward
that goal (see remaining below for the precise residuals).

## Sections

* (§1) The concrete quotient Hilbert function `multQuotHilbert` (homogeneous
  pieces modulo the kernel piece, measured by `finLength`), with finiteness
  (`Module.Finite` via FG, hence `IsFiniteLength`) and the SES split
  `domain = kerPiece + quot` (`mult_hilbert_add`) plus the comparison
  `quot ≤ domain` (`mult_quot_le_domain`).
* (§2) Krull-dimension API: `dim κ[t₁..t_d] = d` (`mult_ringKrullDim_poly`),
  `dim (S ⧸ ker) ≤ d` (`mult_ringKrullDim_quot_le`), the `quotKerEquiv` dim
  transfer `dim (S ⧸ ker) = dim gr` (`mult_quotKerEquiv_dim`), and the
  conditional equality `mult_dim_quot_eq_of_dim_gr`.
* (§3) Length transfer along equivalences (`mult_finLength_eq_of_linearEquiv`,
  via `LinearEquiv.length_eq`).
* (§4) Leading-coefficient bridges: a witnessing polynomial with nonzero top
  coefficient forces `hmult` (`mult_hmult_of_coeff_ne_zero`), hence so does an
  exact-degree nonzero witness (`mult_hmult_of_exactDegree`).
* (§5) The results in exact §10 shape: `mult_hmult` for the concrete
  shifted quotient Hilbert function, `mult_hdimEq_for_quotHilbert` recovering
  `hdimEq`, and `mult_ker_eq_bot_of_hilbertWitness` discharging the `hmult`
  hypothesis of `hsAssemble_ker_eq_bot_of_mult` (exact-shape consumption
  verified by typechecking the application).
* (§6) remaining: milestones proved + precise residuals (doc-only; snapshot
  — see §11 for the update).
* (§7) Dimension upper bounds: `dim R_P ≤ d` (Krull hit +
  `spanFinrank`), `dim gr ≤ d` (surjection), and the reverse conditional
  `dim gr = d` from `dim (S ⧸ ker) = d`.
* (§8) Regularity of `R_P` (`IsRegularRing` of a field, hence
  `dim R_P = min #gens`); the conditional equality on minimality of `g`;
  and the machine-checked refutation of R-2b-as-stated (zero-padding).
* (§9) Domain nonvanishing: the top difference of the binomial basis is
  constant `1`, hence unconditional domain `hmult`/`hdimEq` masters, hence
  R-2c for `ker = ⊥`.
* (§10) Quotient-length transfer along linear equivs (the ungraded
  mechanism behind R-2d).
* (§11) remaining: update — proved halves + refined residuals
  (doc-only).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/KrullDimension/Basic.lean`: `ringKrullDim`,
  `ringKrullDim_quotient_le`, `RingEquiv.ringKrullDim`.
* `RingTheory/KrullDimension/Field.lean`: `ringKrullDim_eq_zero_of_field`.
* `RingTheory/KrullDimension/Polynomial.lean`:
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.
* `RingTheory/MvPolynomial/Homogeneous.lean`: `homogeneousSubmodule`,
  `homogeneousSubmodule_fg`.
* `RingTheory/KrullDimension/Basic.lean` (also): `ringKrullDim_le_of_surjective`.
* `RingTheory/Ideal/KrullsHeightTheorem.lean`:
  `ringKrullDim_le_spanFinrank_maximalIdeal`.
* `Algebra/Module/SpanRank.lean`: `spanFinrank`,
  `spanFinrank_span_le_ncard_of_finite`, `spanFinrank_bot`.
* `RingTheory/RegularLocalRing/Defs.lean`: `IsRegularRing`,
  `IsRegularLocalRing`, `isRegularRing_iff`, `isRegularLocalRing_iff`.
* `RingTheory/RegularLocalRing/Polynomial.lean`:
  `MvPolynomial.isRegularRing_of_isRegularRing`.
* `RingTheory/Localization/Basic.lean`: `Field.localization_map_bijective`.
* `RingTheory/Localization/AtPrime/Basic.lean`:
  `IsLocalization.AtPrime.map_eq_maximalIdeal`.
* `RingTheory/Noetherian/Basic.lean`: `isNoetherianRing_of_ringEquiv`.
* `LinearAlgebra/Quotient/Basic.lean`: `Submodule.mapQ`, `mapQ_apply`,
  `Submodule.quotEquivOfEqBot`, `Submodule.mkQ_surjective`.
* `Algebra/Module/Equiv/Basic.lean`: `LinearEquiv.ofLinearMap`.
* `RingTheory/Finiteness/Basic.lean`: `Module.Finite.of_fg`.
* `RingTheory/FiniteLength.lean`: `IsFiniteLength`.
* `RingTheory/Length.lean`: `LinearEquiv.length_eq`.
* `Algebra/Module/Submodule/RestrictScalars.lean`: `restrictScalars`.
* `Algebra/Polynomial/Degree/Defs.lean`: `Polynomial.coeff_natDegree`,
  `Polynomial.leadingCoeff_ne_zero`.
* `Data/Nat/Factorial/Basic.lean`: `Nat.factorial_ne_zero`.
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.

Project (read-only):
* `Regularity/Multiplicity/NewtonDifferences.lean` (M4c-ii part 1: `seqDiff`, `IsPolyGrowth`,
  `evalFun`, `seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun`).
* `Regularity/Koszul/LengthFramework.lean` (M4c-i: `finLength`,
  `finLength_add_of_submodule`, `isFiniteLength_of_isNoetherian_isArtinian`,
  `isFiniteLength_quotient`).
* `Regularity/Koszul/GradedSurjection.lean` (M4b: `polySurjResidue`,
  `polySurjResidue_quotKerEquiv`).
* `Regularity/Koszul/AssociatedGradedRing.lean` (step A4(i): `grRegular`).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean` (§9–§10: `hsAssemble_domainHilbert`,
  `hsAssemble_hdimEq_of_not_vanishing`, `hsAssemble_ker_eq_bot_of_mult`;
  §13: `hsAssemble_domainHilbert_eq_choose`, `hsAssemble_hF`).
* `Regularity/Multiplicity/NewtonDifferences.lean` (also: `seqDiff_comp_add`,
  `seqDiff_chooseFun_succ`, `chooseFun`, `isPolyGrowth_comp_add`).

## Status

* §1–§4: unconditional.
* §5 (`mult_hmult`, `mult_hdimEq_for_quotHilbert`,
  `mult_ker_eq_bot_of_hilbertWitness`): conditional-explicit on the Hilbert
  witness `(Pwit, hle, hag, hc)` (residual R-2c) plus, for the kernel
  corollary, the §10 residuals `hF`, `hdrop`, `hd_pos`, `hdim`.
* §7–§10: unconditional, except `mult_ringKrullDim_atPrime_eq_of_minimal`
  and `mult_r2b_universal_false` which are unconditional proofs of
  conditional-form statements (minimality hypothesis / spanning-family
  hypothesis respectively).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MultiplicityNonvanishing

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective

/-! ## §1. The concrete quotient Hilbert function -/

/-- The degree-`n` piece of `ker`: homogeneous degree-`n` polynomials lying in
`ker`, as a `κ`-submodule of the homogeneous piece (restriction of scalars
along `κ → S`). -/
noncomputable def multKerPiece (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) :
    Submodule κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) :=
  Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin d) κ n).subtype
    (ker.restrictScalars κ)

/-- The concrete quotient Hilbert function: `κ`-lengths of the homogeneous
pieces of `S = κ[t₁..t_d]` modulo the kernel piece. At
`κ = IsLocalRing.ResidueField R_P` and `ker = RingHom.ker polySurjResidue`
this is the `Hq` whose `hmult` (§5) feeds `hsAssemble_ker_eq_bot_of_mult`. -/
noncomputable def multQuotHilbert (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) : ℕ :=
  finLength κ (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸
    multKerPiece κ d ker n)

/-- Homogeneous pieces over a field are finite-dimensional (FG + field).
-/
theorem mult_finite_homogeneousPiece (κ : Type*) [Field κ] (d n : ℕ) :
    Module.Finite κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin d) κ n)

/-- Homogeneous pieces over a field have finite length (Noetherian + Artinian
instances from finite-dimensionality).
-/
theorem mult_isFiniteLength_homogeneousPiece (κ : Type*) [Field κ] (d n : ℕ) :
    IsFiniteLength κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) := by
  have _hfin := mult_finite_homogeneousPiece κ d n
  exact isFiniteLength_of_isNoetherian_isArtinian

/-- Quotient pieces have finite length (stability under quotients).
-/
theorem mult_isFiniteLength_quotPiece (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) :
    IsFiniteLength κ (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸
      multKerPiece κ d ker n) :=
  isFiniteLength_quotient (mult_isFiniteLength_homogeneousPiece κ d n) _

/-- SES split of the domain Hilbert function: each homogeneous piece length is
the kernel-piece length plus the quotient-piece length.
-/
theorem mult_hilbert_add (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) :
    hsAssemble_domainHilbert κ d n = finLength κ ↥(multKerPiece κ d ker n) +
      multQuotHilbert κ d ker n := by
  unfold hsAssemble_domainHilbert multQuotHilbert
  exact finLength_add_of_submodule
    (mult_isFiniteLength_homogeneousPiece κ d n) (multKerPiece κ d ker n)

/-- The quotient Hilbert function is pointwise bounded by the domain one.
-/
theorem mult_quot_le_domain (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) :
    multQuotHilbert κ d ker n ≤ hsAssemble_domainHilbert κ d n := by
  have h := mult_hilbert_add κ d ker n
  omega

/-! ## §2. Krull-dimension API -/

/-- The Krull dimension of `κ[t₁..t_d]` over a field is `d` (Mathlib's
Noetherian polynomial formula + `dim κ = 0`).
-/
theorem mult_ringKrullDim_poly (κ : Type*) [Field κ] (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) κ) = d := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, Nat.card_fin, zero_add]

/-- The Krull dimension of a quotient of `κ[t₁..t_d]` is at most `d`.
-/
theorem mult_ringKrullDim_quot_le (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) :
    ringKrullDim (MvPolynomial (Fin d) κ ⧸ ker) ≤ d := by
  have h1 : ringKrullDim (MvPolynomial (Fin d) κ ⧸ ker)
      ≤ ringKrullDim (MvPolynomial (Fin d) κ) :=
    ringKrullDim_quotient_le ker
  rw [mult_ringKrullDim_poly κ d] at h1
  exact h1

/-- The `quotKerEquiv` dimension transfer: `dim (S ⧸ ker) = dim gr`, since the
first-isomorphism form is a ring equiv.
-/
theorem mult_quotKerEquiv_dim {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) =
      ringKrullDim (grRegular P) :=
  RingEquiv.ringKrullDim (polySurjResidue_quotKerEquiv P d g hgen)

/-- Conditional dimension equality: `dim gr = d` gives `dim (S ⧸ ker) = d`
(residual R-2a discharges `hgr`; see §6).
-/
theorem mult_dim_quot_eq_of_dim_gr {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hgr : ringKrullDim (grRegular P) = d) :
    ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) = d := by
  rw [mult_quotKerEquiv_dim P d g hgen, hgr]

/-! ## §3. Length transfer along equivalences -/

/-- `finLength` is invariant under linear equivs (via `LinearEquiv.length_eq`):
the abstract transfer behind the graded `quotKerEquiv` length comparison
(residual R-2d states the graded form; see §6).
-/
theorem mult_finLength_eq_of_linearEquiv {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) : finLength R M = finLength R N := by
  unfold finLength
  rw [e.length_eq]

/-! ## §4. Leading-coefficient bridges to nonvanishing -/

/-- A witnessing polynomial with nonzero top coefficient forces `hmult`: the
`e`-th difference is eventually the constant `e! * coeff`, which is nonzero.
-/
theorem mult_hmult_of_coeff_ne_zero {F : ℕ → ℚ} {e : ℕ} (P : ℚ[X])
    (hle : P.natDegree ≤ e) (hag : F =ᶠ[Filter.atTop] evalFun P)
    (hc : P.coeff e ≠ 0) :
    ¬ seqDiff e F =ᶠ[Filter.atTop] 0 := by
  have hconst := seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun P e hag hle
  intro hvan
  have h00 : (fun _ : ℕ => (Nat.factorial e : ℚ) * P.coeff e)
      =ᶠ[Filter.atTop] (0 : ℕ → ℚ) :=
    hconst.symm.trans hvan
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h00
  have hNN := hN N le_rfl
  simp only [Pi.zero_apply] at hNN
  have hfact : (Nat.factorial e : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero e)
  rcases mul_eq_zero.mp hNN with h | h
  · exact absurd h hfact
  · exact absurd h hc

/-- An exact-degree nonzero witness forces `hmult` (top coefficient =
leading coefficient ≠ 0).
-/
theorem mult_hmult_of_exactDegree {F : ℕ → ℚ} {e : ℕ} (P : ℚ[X])
    (hdeg : P.natDegree = e) (hne : P ≠ 0)
    (hag : F =ᶠ[Filter.atTop] evalFun P) :
    ¬ seqDiff e F =ᶠ[Filter.atTop] 0 := by
  apply mult_hmult_of_coeff_ne_zero P (le_of_eq hdeg) hag
  have hlc : P.coeff e = P.leadingCoeff := by
    rw [← hdeg, Polynomial.coeff_natDegree]
  rw [hlc]
  exact Polynomial.leadingCoeff_ne_zero.mpr hne

/-! ## §5. The `hmult` results in exact §10 shape -/

/-- `hmult` for the concrete shifted quotient Hilbert function
(`Hq (n + 1)` cast to `ℚ`), conditional on the Hilbert witness
`(P, hle, hag, hc)` (residual R-2c; see §6). This is the exact proposition
`hsAssemble_ker_eq_bot_of_mult` takes as its `hmult` hypothesis.

Explicitly conditional on `(P, hle, hag, hc)`. -/
theorem mult_hmult (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) (e : ℕ) (P : ℚ[X])
    (hle : P.natDegree ≤ e)
    (hag : (fun n => ((multQuotHilbert κ d ker (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun P)
    (hc : P.coeff e ≠ 0) :
    ¬ seqDiff e (fun n => ((multQuotHilbert κ d ker (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
  mult_hmult_of_coeff_ne_zero P hle hag hc

/-- `hdimEq` for the concrete quotient Hilbert function, recovered from
`hmult` via §10 (`hsAssemble_hdimEq_of_not_vanishing`).

Explicitly conditional on `(hFq, P, hle, hag, hc)`. -/
theorem mult_hdimEq_for_quotHilbert (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) (e : ℕ)
    (hFq : IsPolyGrowth
      (fun n => ((multQuotHilbert κ d ker (n + 1) : ℕ) : ℚ)) e)
    (P : ℚ[X]) (hle : P.natDegree ≤ e)
    (hag : (fun n => ((multQuotHilbert κ d ker (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun P)
    (hc : P.coeff e ≠ 0) :
    ∀ Q : ℚ[X], Q.natDegree ≤ e →
      (fun n => ((multQuotHilbert κ d ker (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q → Q.natDegree = e :=
  hsAssemble_hdimEq_of_not_vanishing hFq
    (mult_hmult κ d ker e P hle hag hc)

/-- The §10 kernel master with `Hq` instantiated to the concrete quotient
Hilbert function and `hmult` discharged by `mult_hmult`: the exact-shape
consumption is verified by typechecking this application.

Explicitly conditional on `(Pwit, hle, hag, hc)` (residual R-2c) plus
the §10 residuals `hF`, `hdrop`, `hd_pos`, `hdim`. -/
theorem mult_ker_eq_bot_of_hilbertWitness {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H : ℕ → ℕ) (e : ℕ)
    (hd_pos : 1 < d) (hdim : e + 1 = d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (Pwit : ℚ[X]) (hle : Pwit.natDegree ≤ e)
    (hag : (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pwit)
    (hc : Pwit.coeff e ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
          d (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ)) e) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ :=
  hsAssemble_ker_eq_bot_of_mult P d g hgen H
    (multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen))) e hd_pos hdim hF
    (mult_hmult (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) e Pwit hle hag hc)
    hdrop

/-! ## §6. Remaining (status; superseded by §11)

Milestones proved (all verified 0 errors 0 warnings):

* M-R2a (concrete Hilbert function): `multKerPiece` + `multQuotHilbert` with
  `Module.Finite`/`IsFiniteLength` (FG + field ⇒ Noetherian + Artinian), the
  SES split `mult_hilbert_add`, and the comparison `mult_quot_le_domain.
* M-R2b (dimension API): `mult_ringKrullDim_poly` (`dim κ[t] = d`),
  `mult_ringKrullDim_quot_le` (`dim (S ⧸ ker) ≤ d`), `mult_quotKerEquiv_dim`
  (`dim (S ⧸ ker) = dim gr` via the M4b ring equiv), and the conditional
  equality `mult_dim_quot_eq_of_dim_gr`.
* M-R2c (length transfer): `mult_finLength_eq_of_linearEquiv` (the abstract
  transfer; the graded per-degree form is R-2d).
* M-R2d (leading-coefficient theory): `mult_hmult_of_coeff_ne_zero` and
  `mult_hmult_of_exactDegree` (Newton bridges from a Hilbert witness to
  nonvanishing).
* M-R2e (results): `mult_hmult` in the exact §10 shape,
  `mult_hdimEq_for_quotHilbert`, and `mult_ker_eq_bot_of_hilbertWitness`
  (typechecked application of `hsAssemble_ker_eq_bot_of_mult`).

Precise residuals (the remainder of R2):

1. **R-2a (`dim gr = d`).** Needs associated-graded dimension theory
   (`dim gr_I(R) = dim R` for Noetherian local `R`) plus `dim R_P = d`,
   all absent from Mathlib. Discharges `hgr` in `mult_dim_quot_eq_of_dim_gr`.
   Estimate: ~150 lines plus new dim API.
2. **R-2b (`dim R_P = d`).** The regular-local dimension equals the minimal
   number of generators of `𝔪` (regularity ⇒ `dim = embdim`; `R_P` is regular
   since `P` is a prime of a polynomial ring over a field). Absent from
   Mathlib. Estimate: ~100 lines.
3. **R-2c (Hilbert witness from dimension).** From `dim (S ⧸ ker) = d`,
   produce `(Pwit, hle, hag, hc)`: the shifted quotient Hilbert function
   eventually agrees with a degree-`≤ e` rational polynomial with nonzero
   `e`-coefficient (`e = d - 1`). Needs Hilbert-polynomial existence
   (characteristic-free, hence not Mathlib's `HilbertPoly`) plus
   multiplicity-positivity from dimension. This is the analytic core of R2.
   Estimate: ~250+ lines.
4. **R-2d (graded length transfer).** Per-degree identification of
   `multQuotHilbert n` with `gr`-piece lengths along `quotKerEquiv`: needs
   the quotient grading on `S ⧸ ker` (ker-homogeneity is §11 of
   `GradedSurjectionInjective`) plus graded-ness of `quotKerEquiv`. Would let R-2c
   run on `gr`-side Hilbert theory instead. Estimate: ~100 lines.
-/

#print axioms mult_hilbert_add
#print axioms mult_ringKrullDim_poly
#print axioms mult_quotKerEquiv_dim
#print axioms mult_finLength_eq_of_linearEquiv
#print axioms mult_hmult_of_coeff_ne_zero
#print axioms mult_hmult
#print axioms mult_ker_eq_bot_of_hilbertWitness

/-! ## §7. Dimension upper bounds (R-2a/R-2b upper halves)

The easy halves of the two dimension residuals, both unconditional:
`dim R_P ≤ d` (Krull's Hauptidealsatz via `spanFinrank`: the height of `𝔪`
is at most the size of any spanning family) and `dim gr ≤ d` (a surjective
image cannot have larger dimension than the source, applied to the M4b
surjection). The reverse conditional `dim gr = d` from `dim (S ⧸ ker) = d`
pairs with `mult_dim_quot_eq_of_dim_gr`, so R-2a is now exactly the lower
bound `dim gr ≥ d` (equivalently `dim (S ⧸ ker) ≥ d`).
-/

/-- The minimal number of generators of `𝔪(R_P)` is at most `d`: `hgen`
exhibits `d` generators and `spanFinrank` is the minimum.
-/
theorem mult_spanFinrank_maximalIdeal_atPrime_le {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank ≤ d := by
  rw [← hgen]
  refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
    (Set.finite_range g)) ?_
  have h1 : Set.range g = g '' Set.univ := by rw [Set.image_univ]
  rw [h1]
  refine le_trans (Set.ncard_image_le Set.finite_univ) ?_
  rw [Set.ncard_univ, Nat.card_fin]

/-- `dim R_P ≤ d` (Krull's Hauptidealsatz: height is at most the number of
generators).
-/
theorem mult_ringKrullDim_atPrime_le {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ringKrullDim (Localization.AtPrime P) ≤ d := by
  have h1 := ringKrullDim_le_spanFinrank_maximalIdeal (Localization.AtPrime P)
  have h2 := mult_spanFinrank_maximalIdeal_atPrime_le P d g hgen
  refine le_trans h1 ?_
  exact_mod_cast h2

/-- `dim gr ≤ d`: the M4b surjection cannot raise dimension.
-/
theorem mult_ringKrullDim_gr_le {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ringKrullDim (grRegular P) ≤ d := by
  have hle := ringKrullDim_le_of_surjective (polySurjResidue P d g hgen)
    (polySurjResidue_surjective P d g hgen)
  rw [mult_ringKrullDim_poly _ d] at hle
  exact hle

/-- Reverse conditional: `dim (S ⧸ ker) = d` gives `dim gr = d`
(residual R-2a is now exactly the lower bound; see §11).
-/
theorem mult_dim_gr_eq_of_dim_quot {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hquot : ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) = d) :
    ringKrullDim (grRegular P) = d := by
  rw [← mult_quotKerEquiv_dim P d g hgen]
  exact hquot

/-! ## §8. Regularity of `R_P` and the re-scoped R-2b

R-2b-as-stated (`dim R_P = d` for every spanning family `g`) is false:
zero-padding any spanning family preserves spanning while changing `d`
(`mult_r2b_universal_false`). The correct residual is the minimality
hypothesis `hmin` in `mult_ringKrullDim_atPrime_eq_of_minimal` (to be
discharged by file 6's construction of `g`, e.g. lifting a residue-field
basis of `𝔪/𝔪²`).

The equality `dim R_P = min #gens` itself is Mathlib regularity theory:
fields are regular rings (every localization of a field is equivalent to
the field, hence a regular local ring with both sides `0`), polynomial
rings over a regular ring are regular
(`MvPolynomial.isRegularRing_of_isRegularRing`), and a regular local ring
satisfies `dim = spanFinrank 𝔪` by definition. No circularity:
this is dim-equals-embdim only, not CM-ness or unmixedness.

conditional-form statements with unconditional proofs). -/

/-- Fields are regular rings: every localization of a field is (equivalent
to) the field itself, hence a regular local ring with both sides `0`.
-/
instance mult_isRegularRing_of_field (K : Type*) [Field K] : IsRegularRing K := by
  rw [isRegularRing_iff]
  intro p hp
  have hpbot : p = ⊥ := Ideal.eq_bot_of_prime p
  have h0 : (0 : K) ∉ p.primeCompl := by
    intro hmem
    exact hmem (Ideal.zero_mem p)
  have hbij : Function.Bijective (algebraMap K (Localization.AtPrime p)) :=
    Field.localization_map_bijective (M := p.primeCompl) h0
  let e : K ≃+* Localization.AtPrime p :=
    RingEquiv.ofBijective (algebraMap K (Localization.AtPrime p)) hbij
  have _hE : IsNoetherianRing (Localization.AtPrime p) :=
    isNoetherianRing_of_ringEquiv K e
  rw [isRegularLocalRing_iff]
  have hmap : Ideal.map (algebraMap K (Localization.AtPrime p)) p =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p) = ⊥ := by
    rw [← hmap]
    subst hpbot
    exact Ideal.map_bot
  rw [hmax, Submodule.spanFinrank_bot]
  have hdim : ringKrullDim (Localization.AtPrime p) = 0 := by
    have h := RingEquiv.ringKrullDim e.symm
    rw [ringKrullDim_eq_zero_of_field] at h
    exact h
  exact hdim.symm

/-- `dim R_P = min #gens 𝔪(R_P)`: `R_P` is a regular local ring (Mathlib:
polynomial rings over the regular ring `K` are regular).
-/
theorem mult_dim_atPrime_eq_spanFinrank {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    ringKrullDim (Localization.AtPrime P)
      = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank :=
  (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := Localization.AtPrime P)).symm

/-- Conditional equality: minimality of `g` (`d ≤ min #gens`) gives
`dim R_P = d`.
-/
theorem mult_ringKrullDim_atPrime_eq_of_minimal {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    ringKrullDim (Localization.AtPrime P) = d := by
  refine le_antisymm (mult_ringKrullDim_atPrime_le P d g hgen) ?_
  rw [mult_dim_atPrime_eq_spanFinrank P]
  exact_mod_cast hmin

/-- Padding a spanning family with `0` preserves spanning.
-/
theorem mult_padded_span {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d₀ : ℕ)
    (g₀ : Fin d₀ → Localization.AtPrime P)
    (hgen₀ : Ideal.span (Set.range g₀) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    Ideal.span (Set.range (Fin.cons (0 : Localization.AtPrime P) g₀)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  rw [Fin.range_cons, Ideal.span_insert_zero, hgen₀]

/-- The padded family has `d₀ + 1 ≠ dim` generators: dimension is bounded
by the unpadded count.
-/
theorem mult_dim_atPrime_ne_of_redundant {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d₀ : ℕ)
    (g₀ : Fin d₀ → Localization.AtPrime P)
    (hgen₀ : Ideal.span (Set.range g₀) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ringKrullDim (Localization.AtPrime P) ≠ d₀ + 1 := by
  intro hcon
  have hle := mult_ringKrullDim_atPrime_le P d₀ g₀ hgen₀
  rw [hcon] at hle
  have hcontra : d₀ + 1 ≤ d₀ := by exact_mod_cast hle
  omega

/-- R-2b-as-stated is false: given any spanning family, the zero-padded
family spans `𝔪` with `d₀ + 1` generators while `dim R_P ≤ d₀`.
-/
theorem mult_r2b_universal_false {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d₀ : ℕ)
    (g₀ : Fin d₀ → Localization.AtPrime P)
    (hgen₀ : Ideal.span (Set.range g₀) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ∃ (d : ℕ) (g : Fin d → Localization.AtPrime P),
      Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)
        ∧ ringKrullDim (Localization.AtPrime P) ≠ d :=
  ⟨d₀ + 1, Fin.cons 0 g₀, mult_padded_span P d₀ g₀ hgen₀,
    mult_dim_atPrime_ne_of_redundant P d₀ g₀ hgen₀⟩

/-! ## §9. Domain nonvanishing (Newton half of R-2c)

The `k`-th difference of the binomial basis `C(·, k)` is the constant-`1`
sequence (Pascal induction via `seqDiff_chooseFun_succ`), hence the shifted
domain Hilbert function — which §13 identifies pointwise with a shifted
binomial sequence — has nonvanishing top difference. This yields
unconditional domain `hmult`/`hdimEq` masters plus R-2c for `ker = ⊥`
(where the quotient Hilbert function is the domain one, via
`Submodule.quotEquivOfEqBot`). The remainder of R-2c is purely the
Hilbert-polynomial half: nontrivial quotients of dimension `d` inherit a
Hilbert witness (needs Hilbert-polynomial existence, absent from Mathlib).
-/

/-- The `k`-th difference of the binomial basis `C(·, k)` is constant `1`.
-/
theorem mult_seqDiff_chooseFun_self {R : Type*} [CommRing R] (k : ℕ) :
    seqDiff k (chooseFun (R := R) k) = 1 := by
  induction k with
  | zero =>
    have h1 : chooseFun (R := R) 0 = fun _ => (1 : R) := by
      funext n
      change ((Nat.choose n 0 : ℕ) : R) = 1
      rw [Nat.choose_zero_right, Nat.cast_one]
    rw [h1]
    exact seqDiff_zero _
  | succ k ih =>
    rw [seqDiff_succ', ← seqDiff_one, seqDiff_chooseFun_succ]
    exact ih

/-- The top difference of the shifted domain Hilbert function is constant
`1` (via the §13 stars-bars identity and shift-invariance of `seqDiff`).
-/
theorem mult_seqDiff_domainHilbert_shifted (κ : Type*) [Field κ] (d : ℕ)
    (hd : 1 ≤ d) :
    seqDiff (d - 1) (fun n => ((hsAssemble_domainHilbert κ d (n + 1) : ℕ) : ℚ))
      = 1 := by
  have hfun : (fun n => ((hsAssemble_domainHilbert κ d (n + 1) : ℕ) : ℚ))
      = fun n => chooseFun (R := ℚ) (d - 1) (n + d) := by
    funext n
    have hSB := hsAssemble_domainHilbert_eq_choose κ d hd (n + 1)
    have hN : (n + 1) + d - 1 = n + d := by omega
    rw [hN] at hSB
    change ((hsAssemble_domainHilbert κ d (n + 1) : ℕ) : ℚ) =
      ((Nat.choose (n + d) (d - 1) : ℕ) : ℚ)
    rw [hSB]
  rw [hfun, seqDiff_comp_add, mult_seqDiff_chooseFun_self]
  rfl

/-- Unconditional domain `hmult`: the shifted domain Hilbert function has
nonvanishing top difference.
-/
theorem mult_domainHmult (κ : Type*) [Field κ] (d : ℕ) (hd : 1 ≤ d) :
    ¬ seqDiff (d - 1) (fun n => ((hsAssemble_domainHilbert κ d (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  rw [mult_seqDiff_domainHilbert_shifted κ d hd]
  intro hvan
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hvan
  have hNN := hN N le_rfl
  simp only [Pi.one_apply, Pi.zero_apply] at hNN
  exact one_ne_zero hNN

/-- Unconditional domain `hdimEq` in §10 shape (via
`isPolyGrowth_comp_add` shifting `hsAssemble_hF`).
-/
theorem mult_domainHdimEq (κ : Type*) [Field κ] (d : ℕ) (hd : 1 ≤ d) :
    ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((hsAssemble_domainHilbert κ d (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q → Q.natDegree = d - 1 :=
  hsAssemble_hdimEq_of_not_vanishing
    (isPolyGrowth_comp_add (hsAssemble_hF κ d hd) 1)
    (mult_domainHmult κ d hd)

/-- The kernel piece of `⊥` is `⊥`.
-/
theorem mult_kerPiece_bot (κ : Type*) [Field κ] (d n : ℕ) :
    multKerPiece κ d ⊥ n = ⊥ := by
  unfold multKerPiece
  simp

/-- At `ker = ⊥` the quotient Hilbert function is the domain one.
-/
theorem mult_quotHilbert_eq_domain_of_ker_eq_bot (κ : Type*) [Field κ]
    (d n : ℕ) :
    multQuotHilbert κ d ⊥ n = hsAssemble_domainHilbert κ d n := by
  unfold multQuotHilbert hsAssemble_domainHilbert
  exact mult_finLength_eq_of_linearEquiv
    ((multKerPiece κ d ⊥ n).quotEquivOfEqBot (mult_kerPiece_bot κ d n))

/-- R-2c for `ker = ⊥`: unconditional quotient `hmult` at trivial kernel.
-/
theorem mult_hmult_of_ker_eq_bot (κ : Type*) [Field κ] (d : ℕ) (hd : 1 ≤ d) :
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert κ d ⊥ (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have heq : (fun n => ((multQuotHilbert κ d ⊥ (n + 1) : ℕ) : ℚ))
      = fun n => ((hsAssemble_domainHilbert κ d (n + 1) : ℕ) : ℚ) := by
    funext n
    rw [mult_quotHilbert_eq_domain_of_ker_eq_bot]
  rw [heq]
  exact mult_domainHmult κ d hd

/-- R-2c for `ker = ⊥`: unconditional quotient `hdimEq` at trivial kernel.
-/
theorem mult_hdimEq_of_ker_eq_bot (κ : Type*) [Field κ] (d : ℕ) (hd : 1 ≤ d) :
    ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((multQuotHilbert κ d ⊥ (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q → Q.natDegree = d - 1 := by
  have heq : (fun n => ((multQuotHilbert κ d ⊥ (n + 1) : ℕ) : ℚ))
      = fun n => ((hsAssemble_domainHilbert κ d (n + 1) : ℕ) : ℚ) := by
    funext n
    rw [mult_quotHilbert_eq_domain_of_ker_eq_bot]
  have hFq : IsPolyGrowth (fun n => ((multQuotHilbert κ d ⊥ (n + 1) : ℕ) : ℚ))
      (d - 1) := by
    rw [heq]
    exact isPolyGrowth_comp_add (hsAssemble_hF κ d hd) 1
  have h := hsAssemble_hdimEq_of_not_vanishing hFq
    (mult_hmult_of_ker_eq_bot κ d hd)
  intro Q hdQ hQag
  exact h Q hdQ hQag

/-! ## §10. Quotient-length transfer along linear equivs (R-2d mechanism)

The ungraded transfer mechanism behind R-2d: a linear equiv `e : M ≃ N`
induces a quotient equiv `M ⧸ P ≃ N ⧸ P.map e` (both directions via
`Submodule.mapQ`, inverses by quotient induction), hence equal
`finLength`s. What remains for R-2d proper (§11) is producing the
per-degree equivs from the graded `quotKerEquiv` (needs the quotient
grading on `S ⧸ ker` plus gradedness of `quotKerEquiv`, both absent).
-/

/-- A linear equiv induces a quotient equiv along `P ↦ P.map e`.
-/
noncomputable def mult_quotCongrOfLinearEquiv {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (P : Submodule R M) :
    (M ⧸ P) ≃ₗ[R] (N ⧸ P.map e.toLinearMap) := by
  refine LinearEquiv.ofLinearMap
    (Submodule.mapQ P (P.map e.toLinearMap) e.toLinearMap
      (Submodule.le_comap_map e.toLinearMap P))
    (Submodule.mapQ (P.map e.toLinearMap) P e.symm.toLinearMap ?h2) ?h3 ?h4
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    simpa using hy
  · rw [LinearMap.ext_iff]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (P.map e.toLinearMap) x
    simp
  · rw [LinearMap.ext_iff]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P x
    simp

/-- `finLength` of quotients transfers along linear equivs carrying `P`.
-/
theorem mult_finLength_quot_congr_of_linearEquiv {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (P : Submodule R M) :
    finLength R (M ⧸ P) = finLength R (N ⧸ P.map e.toLinearMap) :=
  mult_finLength_eq_of_linearEquiv (mult_quotCongrOfLinearEquiv e P)

/-! ## §11. Remaining (update)

Supersedes §6. Milestones proved (all verified 0 errors
0 warnings):

* M-R2f (dimension upper bounds, §7): `mult_spanFinrank_maximalIdeal_atPrime_le`
  (`min #gens 𝔪 ≤ d`), `mult_ringKrullDim_atPrime_le` (`dim R_P ≤ d` via
  Krull hit), `mult_ringKrullDim_gr_le` (`dim gr ≤ d` via the M4b
  surjection), `mult_dim_gr_eq_of_dim_quot` (reverse conditional).
* M-R2g (regularity + re-scope, §8): `mult_isRegularRing_of_field`
  (fields are regular rings), `mult_dim_atPrime_eq_spanFinrank`
  (`dim R_P = min #gens`), `mult_ringKrullDim_atPrime_eq_of_minimal`
  (equality on minimality of `g`), and `mult_r2b_universal_false`
  (R-2b-as-stated is false: zero-padding refutation).
* M-R2h (domain nonvanishing, §9): `mult_seqDiff_chooseFun_self` (top
  difference of the binomial basis is `1`),
  `mult_seqDiff_domainHilbert_shifted`, the unconditional masters
  `mult_domainHmult` / `mult_domainHdimEq`, and R-2c for `ker = ⊥`
  (`mult_quotHilbert_eq_domain_of_ker_eq_bot`,
  `mult_hmult_of_ker_eq_bot`, `mult_hdimEq_of_ker_eq_bot`).
* M-R2i (transfer mechanism, §10): `mult_quotCongrOfLinearEquiv` +
  `mult_finLength_quot_congr_of_linearEquiv`.

Precise residuals (the remainder of R2):

1. **R-2a′ (`dim gr ≥ d`).** Only the lower bound remains (upper bound
   proved; both conditionals proved). Needs associated-graded dimension
   theory (`dim gr_I(R) = dim R` for Noetherian local `R`), absent from
   Mathlib, plus minimality of `g` (file 6). Estimate: ~150 lines plus
   new dim API.
2. **R-2b′ (minimality of `g`).** R-2b-as-stated is false
   (`mult_r2b_universal_false`); the true residual is the minimality
   hypothesis `d ≤ spanFinrank 𝔪` in
   `mult_ringKrullDim_atPrime_eq_of_minimal`, to be discharged by file 6's
   construction of `g` (e.g. lifting a residue-field basis of `𝔪/𝔪²`).
   No new ring theory needed.
3. **R-2c′ (Hilbert witness for nontrivial quotients).** The Newton half
   is proved (§9: domain case + `ker = ⊥` case). What remains is the
   Hilbert-polynomial half: from `dim (S ⧸ ker) = d`, produce the witness
   `(Pwit, hle, hag, hc)` for a possibly-nontrivial quotient. Needs
   Hilbert-polynomial existence (characteristic-free) plus
   multiplicity-positivity from dimension, both absent from Mathlib. This
   is the analytic core of R2. Estimate: ~250+ lines.
4. **R-2d′ (graded per-degree equivs).** The ungraded transfer mechanism
   is proved (§10). What remains is producing per-degree linear equivs
   from `quotKerEquiv`: the quotient grading on `S ⧸ ker`
   (ker-homogeneity is §11 of `GradedSurjectionInjective`) plus gradedness of
   `quotKerEquiv`. Estimate: ~100 lines.
-/

#print axioms mult_ringKrullDim_atPrime_le
#print axioms mult_ringKrullDim_gr_le
#print axioms mult_dim_atPrime_eq_spanFinrank
#print axioms mult_ringKrullDim_atPrime_eq_of_minimal
#print axioms mult_r2b_universal_false
#print axioms mult_seqDiff_chooseFun_self
#print axioms mult_domainHmult
#print axioms mult_domainHdimEq
#print axioms mult_quotHilbert_eq_domain_of_ker_eq_bot
#print axioms mult_hmult_of_ker_eq_bot
#print axioms mult_finLength_quot_congr_of_linearEquiv

/-! ## §12. Graded per-degree equivs (R-2d′ closed)

The quotient grading on `S ⧸ ker` plus gradedness of `quotKerEquiv`, yielding
per-degree `(R ⧸ I)`-linear equivs between the quotient Hilbert pieces and the
`gr` pieces, hence identification of `multQuotHilbert` with `gr`-piece lengths.

* Residue action (§12a): `I` annihilates each `grPiece` (`mult_grPiece_annihilated`),
  so the `R`-action descends to `R ⧸ I` (`multGrPieceQuotientModule`).
* Degree map (§12b): `polySurj` restricts to a degree-`n` linear map
  (`multDegMap`) from the homogeneous piece to `grPiece n`, via §11
  (`hsAssemble_polySurj_of_homogeneous`); scalar compatibility through
  `coeffHom`/`of_smul_eq` inside the `map_smul'` proof.
* Kernel + surjectivity (§12c): the kernel is the kernel piece
  (`multDegMap_ker_eq`) and every class has a homogeneous preimage
  (`mult_polySurj_homogeneous_preimage`, via `preimage_of` + homogeneous
  decomposition), hence `multDegMap_surjective`.
* Equiv + length (§12d): per-degree linear equiv (`multDegQuotEquiv`), the
  `R_P` transport (`multQuotKerTransport`), and the Hilbert-function
  identification (`mult_quotHilbert_eq_grPieceLength` via the generic
  `mult_lengthTransfer_of_equivs`).
* Quotient grading (§12e): `S ⧸ ker` is spanned by homogeneous classes
  (`mult_quotient_spanned_by_homogeneous`) and they are independent
  (`mult_quotient_homogeneous_independent`, exactly ker-homogeneity).
* Masters (§12f): `hmult`/`hdimEq` with the witness stated `gr`-side
  (`mult_hmult_grSide`, `mult_hdimEq_grSide`).
-/

section R2dResidueAction

variable (R : Type*) [CommRing R] (I : Ideal R)

/-- `I` annihilates each graded piece: for `c ∈ I` and `y : grPiece n`,
`c • y = 0`, since `c * r ∈ I * I^n = I^(n+1)`.
-/
theorem mult_grPiece_annihilated (n : ℕ) (c : R) (hc : c ∈ I) (y : grPiece R I n) :
    c • y = 0 := by
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I n y
  rw [grPiece_mk_smul, grPiece_mk_eq_zero_iff]
  have hmem : c * (r : R) ∈ I ^ 1 * I ^ n :=
    Ideal.mul_mem_mul (by rwa [pow_one]) r.2
  have hpow : I ^ (n + 1) = I ^ 1 * I ^ n := by
    rw [show n + 1 = 1 + n from by omega, pow_add]
  rw [hpow]
  have hcoe : ((c • r : ↥(I ^ n)) : R) = c * (r : R) := rfl
  rw [hcoe]
  exact hmem

/-- Representatives of the same residue class act identically on graded pieces.
-/
theorem mult_grPiece_smul_congr (n : ℕ) (a b : R)
    (h : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b) (y : grPiece R I n) :
    a • y = b • y := by
  have hmem : a - b ∈ I := (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp h
  have hann := mult_grPiece_annihilated R I n (a - b) hmem y
  rw [sub_smul, sub_eq_zero] at hann
  exact hann

/-- The residue-ring action on graded pieces: `I` annihilates each piece, so the
`R`-action descends to `R ⧸ I` (via `Quotient.out` representatives).
-/
noncomputable instance multGrPieceQuotientModule (n : ℕ) :
    Module (R ⧸ I) (grPiece R I n) where
  smul q y := (Quotient.out q : R) • y
  one_smul y := by
    change (Quotient.out (1 : R ⧸ I) : R) • y = y
    have h : (Quotient.out (1 : R ⧸ I) : R) • y = (1 : R) • y :=
      mult_grPiece_smul_congr R I n _ _
        (by rw [Ideal.Quotient.mk_out]; exact (map_one _).symm) y
    rwa [one_smul] at h
  mul_smul a b y := by
    change (Quotient.out (a * b) : R) • y
      = (Quotient.out a : R) • (Quotient.out b : R) • y
    have h : Ideal.Quotient.mk I (Quotient.out (a * b)) =
        Ideal.Quotient.mk I (Quotient.out a * Quotient.out b) := by
      rw [Ideal.Quotient.mk_out, map_mul, Ideal.Quotient.mk_out,
        Ideal.Quotient.mk_out]
    have h2 := mult_grPiece_smul_congr R I n _ _ h y
    have h3 : (Quotient.out a * Quotient.out b : R) • y =
        (Quotient.out a : R) • (Quotient.out b : R) • y := mul_smul _ _ _
    rwa [h3] at h2
  smul_zero a := by
    change (Quotient.out a : R) • (0 : grPiece R I n) = 0
    exact smul_zero _
  smul_add a y₁ y₂ := by
    change (Quotient.out a : R) • (y₁ + y₂)
      = (Quotient.out a : R) • y₁ + (Quotient.out a : R) • y₂
    exact smul_add _ _ _
  add_smul a b y := by
    change (Quotient.out (a + b) : R) • y
      = (Quotient.out a : R) • y + (Quotient.out b : R) • y
    have h : Ideal.Quotient.mk I (Quotient.out (a + b)) =
        Ideal.Quotient.mk I (Quotient.out a + Quotient.out b) := by
      rw [Ideal.Quotient.mk_out, map_add, Ideal.Quotient.mk_out,
        Ideal.Quotient.mk_out]
    have h2 := mult_grPiece_smul_congr R I n _ _ h y
    have h3 : (Quotient.out a + Quotient.out b : R) • y =
        (Quotient.out a : R) • y + (Quotient.out b : R) • y := add_smul _ _ _
    rwa [h3] at h2
  zero_smul y := by
    change (Quotient.out (0 : R ⧸ I) : R) • y = 0
    have h : (Quotient.out (0 : R ⧸ I) : R) • y = (0 : R) • y :=
      mult_grPiece_smul_congr R I n _ _
        (by rw [Ideal.Quotient.mk_out]; exact (map_zero _).symm) y
    rwa [zero_smul] at h

/-- `DirectSum.of` is injective in each degree (by evaluation at that degree).
-/
theorem mult_of_injective (n : ℕ) :
    Function.Injective ⇑(DirectSum.of (grPiece R I) n) := by
  intro a b h
  have h2 := congrArg (fun s : DirectSum ℕ (grPiece R I) => s n) h
  rwa [DirectSum.of_eq_same, DirectSum.of_eq_same] at h2

end R2dResidueAction

section R2dDegMap

variable (R : Type*) [CommRing R] (I : Ideal R) (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = I)

/-- The underlying function of the degree map: the chosen homogeneous image
under `polySurj` (§11 `hsAssemble_polySurj_of_homogeneous`).
-/
noncomputable def multDegMapFun (n : ℕ)
    (x : ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)) :
    grPiece R I n :=
  Classical.choose (hsAssemble_polySurj_of_homogeneous I d g hgen
    ((MvPolynomial.mem_homogeneousSubmodule n x.1).mp x.2))

/-- The chosen image maps back to `polySurj` of the representative.
-/
theorem multDegMapFun_spec (n : ℕ)
    (x : ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)) :
    polySurj R I d g hgen x.1 =
      DirectSum.of (grPiece R I) n (multDegMapFun R I d g hgen n x) :=
  Classical.choose_spec (hsAssemble_polySurj_of_homogeneous I d g hgen
    ((MvPolynomial.mem_homogeneousSubmodule n x.1).mp x.2))

/-- The degree-`n` piece of `polySurj`, as an `(R ⧸ I)`-linear map from the
homogeneous piece to `grPiece n`.
-/
noncomputable def multDegMap (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n →ₗ[R ⧸ I]
      grPiece R I n where
  toFun := multDegMapFun R I d g hgen n
  map_add' x y := by
    apply mult_of_injective R I n
    have h1 : (x + y : ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)).1 =
        x.1 + y.1 := rfl
    rw [map_add, ← multDegMapFun_spec, ← multDegMapFun_spec,
      ← multDegMapFun_spec, h1]
    exact map_add _ _ _
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply mult_of_injective R I n
    have h1 : (((Ideal.Quotient.mk I r) • x :
        ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)).1) =
        (Ideal.Quotient.mk I r) • (x : MvPolynomial (Fin d) (R ⧸ I)) := rfl
    have hcon : (Quotient.out (Ideal.Quotient.mk I r) : R) •
          (multDegMapFun R I d g hgen n x) =
        r • multDegMapFun R I d g hgen n x :=
      mult_grPiece_smul_congr R I n _ _ (Ideal.Quotient.mk_out _) _
    rw [← multDegMapFun_spec, h1, MvPolynomial.smul_eq_C_mul, map_mul,
      polySurj_C, multDegMapFun_spec, coeffHom_mk]
    have hsmul := (of_smul_eq R I n r (multDegMapFun R I d g hgen n x)).symm
    have hcong := congrArg ⇑(DirectSum.of (grPiece R I) n) hcon.symm
    exact hsmul.trans hcong

/-- The degree map applies as the chosen function (definitional unfolding).
-/
theorem multDegMap_apply (n : ℕ)
    (x : ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)) :
    multDegMap R I d g hgen n x = multDegMapFun R I d g hgen n x := rfl

/-- The kernel of the degree map is the kernel piece (stated in comap form;
see `multDegMap_ker_eq_multKerPiece` for the `R_P` form with `multKerPiece`).
-/
theorem multDegMap_ker_eq (n : ℕ) :
    LinearMap.ker (multDegMap R I d g hgen n) =
      Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n).subtype
        ((RingHom.ker (polySurj R I d g hgen)).restrictScalars (R ⧸ I)) := by
  ext x
  have hsub : (MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n).subtype x =
      x.1 := rfl
  simp only [LinearMap.mem_ker, Submodule.mem_comap, hsub,
    Submodule.restrictScalars_mem, RingHom.mem_ker]
  constructor
  · intro hx
    rw [multDegMap_apply] at hx
    have h := multDegMapFun_spec R I d g hgen n x
    rw [hx, map_zero] at h
    exact h
  · intro hx
    apply mult_of_injective R I n
    rw [multDegMap_apply]
    have h := multDegMapFun_spec R I d g hgen n x
    rw [← h, hx]
    exact (map_zero _).symm

end R2dDegMap

section R2dSurj

variable (R : Type*) [CommRing R] (I : Ideal R) (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = I)

/-- Every graded class has a homogeneous preimage under `polySurj`: take any
preimage (`preimage_of`) and keep its degree-`n` homogeneous component (the
other components map into other degrees, hence vanish on evaluation at `n`).
-/
theorem mult_polySurj_homogeneous_preimage (n : ℕ) (z : grPiece R I n) :
    ∃ q : MvPolynomial (Fin d) (R ⧸ I), q.IsHomogeneous n ∧
      polySurj R I d g hgen q = DirectSum.of (grPiece R I) n z := by
  obtain ⟨p, hp⟩ := preimage_of R I d g hgen n z
  refine ⟨MvPolynomial.homogeneousComponent n p,
    MvPolynomial.homogeneousComponent_isHomogeneous n p, ?_⟩
  have hsplit := MvPolynomial.sum_homogeneousComponent p
  have hmap : polySurj R I d g hgen p =
      ∑ i ∈ Finset.range (p.totalDegree + 1),
        polySurj R I d g hgen
          ((MvPolynomial.homogeneousComponent i) p) := by
    conv_lhs => rw [← hsplit]
    rw [map_sum]
  have hmono : ∀ i : ℕ, ∃ y : grPiece R I i,
      polySurj R I d g hgen ((MvPolynomial.homogeneousComponent i) p) =
        DirectSum.of (grPiece R I) i y := fun i =>
    hsAssemble_polySurj_of_homogeneous I d g hgen
      (MvPolynomial.homogeneousComponent_isHomogeneous i p)
  obtain ⟨y, hy⟩ := Classical.axiomOfChoice hmono
  have hsum : ∑ i ∈ Finset.range (p.totalDegree + 1),
      DirectSum.of (grPiece R I) i (y i) =
      DirectSum.of (grPiece R I) n z := by
    have h0 : ∑ i ∈ Finset.range (p.totalDegree + 1),
        polySurj R I d g hgen
          ((MvPolynomial.homogeneousComponent i) p) =
        DirectSum.of (grPiece R I) n z := by
      rw [← hmap]
      exact hp
    simp only [hy] at h0
    exact h0
  have heval := congrArg (fun s : DirectSum ℕ (grPiece R I) => s n) hsum
  rw [DFinsupp.finsetSum_apply, DirectSum.of_eq_same] at heval
  by_cases hn : n < p.totalDegree + 1
  · rw [Finset.sum_eq_single n
      (fun j _ hji => DirectSum.of_eq_of_ne j n (y j) (Ne.symm hji))
      (fun hi' => absurd (Finset.mem_range.mpr hn) hi')] at heval
    rw [DirectSum.of_eq_same] at heval
    rw [hy n, heval]
  · have hz : z = 0 := by
      have h0 : ∑ i ∈ Finset.range (p.totalDegree + 1),
          DirectSum.of (grPiece R I) i (y i) n = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjn : j ≠ n := by
          intro hcon
          subst hcon
          exact hn (Finset.mem_range.mp hj)
        exact DirectSum.of_eq_of_ne j n (y j) (Ne.symm hjn)
      rw [h0] at heval
      exact heval.symm
    have hzc : MvPolynomial.homogeneousComponent n p = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero n p (by omega)
    rw [hzc, map_zero, hz]
    exact (map_zero _).symm

/-- The degree map is surjective.
-/
theorem multDegMap_surjective (n : ℕ) :
    Function.Surjective (multDegMap R I d g hgen n) := by
  intro z
  obtain ⟨q, hqhom, hq⟩ := mult_polySurj_homogeneous_preimage R I d g hgen n z
  have hmem : q ∈ MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n :=
    (MvPolynomial.mem_homogeneousSubmodule n q).mpr hqhom
  refine ⟨⟨q, hmem⟩, ?_⟩
  apply mult_of_injective R I n
  rw [multDegMap_apply]
  have h := multDegMapFun_spec R I d g hgen n ⟨q, hmem⟩
  rw [← h]
  exact hq

/-- The per-degree linear equiv: the homogeneous piece modulo the kernel piece
is the graded piece. The type is inferred (stating the `⧸`-quotient over the
nested ring `R ⧸ I` directly trips `HasQuotient` synthesis; inheriting it by
instantiation from `quotKerEquivOfSurjective` avoids the issue).
-/
noncomputable def multDegQuotEquiv (n : ℕ) :=
  @LinearMap.quotKerEquivOfSurjective (R ⧸ I)
    ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n) (grPiece R I n) _ _ _ _ _
    (multDegMap R I d g hgen n) (multDegMap_surjective R I d g hgen n)

end R2dSurj

section R2dTransfer

variable {κ : Type*} [Field κ] {d n : ℕ}

/-- Generic length transfer along per-degree equivs (variable-`κ` form): two
per-degree equivs identify the quotient Hilbert function with a length
function. All quotient synthesis happens over the variable ring `κ`, then
`R_P` instances instantiate this lemma (avoiding quotient synthesis over the
nested ring `R ⧸ 𝔪`).
-/
theorem mult_lengthTransfer_of_equivs (ker : Ideal (MvPolynomial (Fin d) κ))
    (P2 : Submodule κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n))
    (G : Type*) [AddCommGroup G] [Module κ G]
    (e₁ : (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸
      multKerPiece κ d ker n) ≃ₗ[κ]
      (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸ P2))
    (e₂ : (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸ P2) ≃ₗ[κ] G) :
    multQuotHilbert κ d ker n = finLength κ G := by
  unfold multQuotHilbert
  have L1 := mult_finLength_eq_of_linearEquiv e₁
  have L2 := mult_finLength_eq_of_linearEquiv e₂
  exact L1.trans L2

end R2dTransfer

section R2dLocal

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The kernel of the degree map is `multKerPiece` in the `R_P` setting
(`polySurjResidue`/`ResidueField` unfold to `polySurj`/`R ⧸ 𝔪`).
-/
theorem multDegMap_ker_eq_multKerPiece (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (n : ℕ) :
    LinearMap.ker (multDegMap (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n) =
      multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n := by
  rw [multDegMap_ker_eq]
  rfl

/-- The residue field acts on graded pieces in the `R_P` setting (restated
with `ResidueField` for syntactic typeclass matching).
-/
noncomputable instance multGrPieceResidueModule (n : ℕ) :
    Module (IsLocalRing.ResidueField (Localization.AtPrime P))
      (grPiece (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n) :=
  multGrPieceQuotientModule (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n

/-- Transport between the two quotient presentations in the `R_P` setting:
modulo `multKerPiece` vs modulo `ker (multDegMap..)` (equal by
`multDegMap_ker_eq_multKerPiece`). Type inferred.
-/
noncomputable def multQuotKerTransport (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (n : ℕ) :=
  @Submodule.quotEquivOfEq (IsLocalRing.ResidueField (Localization.AtPrime P))
    ↥(MvPolynomial.homogeneousSubmodule (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime P)) n) _ _ _
    (multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) n)
    (LinearMap.ker (multDegMap (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n))
    (multDegMap_ker_eq_multKerPiece P d g hgen n).symm

/-- The quotient Hilbert function is the `gr`-piece length function
(R-2d′ length transfer).
-/
theorem mult_quotHilbert_eq_grPieceLength (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (n : ℕ) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n =
      finLength (IsLocalRing.ResidueField (Localization.AtPrime P))
        (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n) :=
  mult_lengthTransfer_of_equivs
    (RingHom.ker (polySurjResidue P d g hgen))
    (LinearMap.ker (multDegMap (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n))
    (grPiece (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n)
    (multQuotKerTransport P d g hgen n)
    (multDegQuotEquiv (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n)

end R2dLocal

section R2dQuotGrading

variable (R : Type*) [CommRing R] (I : Ideal R) (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = I)

/-- Every class in `S ⧸ ker` is a finite sum of homogeneous classes
(quotient grading: spanning).
-/
theorem mult_quotient_spanned_by_homogeneous
    (q : MvPolynomial (Fin d) (R ⧸ I) ⧸ RingHom.ker (polySurj R I d g hgen)) :
    ∃ (N : ℕ) (x : ℕ → MvPolynomial (Fin d) (R ⧸ I)),
      (∀ i, (x i).IsHomogeneous i) ∧
        q = ∑ i ∈ Finset.range N, Ideal.Quotient.mk _ (x i) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨p.totalDegree + 1, fun i => MvPolynomial.homogeneousComponent i p,
    fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
  rw [map_sum]

/-- Homogeneous classes in the quotient are independent: a vanishing finite sum
of homogeneous classes (one per degree) vanishes degree by degree. This is
exactly ker-homogeneity (`hsAssemble_ker_homogeneousComponent_mem`).
-/
theorem mult_quotient_homogeneous_independent (N : ℕ)
    (x : ℕ → MvPolynomial (Fin d) (R ⧸ I))
    (hx : ∀ i, (x i).IsHomogeneous i)
    (hsum : ∑ i ∈ Finset.range N,
      Ideal.Quotient.mk (RingHom.ker (polySurj R I d g hgen)) (x i) = 0) :
    ∀ j, j < N →
      Ideal.Quotient.mk (RingHom.ker (polySurj R I d g hgen)) (x j) = 0 := by
  intro j hj
  have hsum0 : Ideal.Quotient.mk (RingHom.ker (polySurj R I d g hgen))
      (∑ i ∈ Finset.range N, x i) = 0 := by
    rw [map_sum]
    exact hsum
  have hker : (∑ i ∈ Finset.range N, x i) ∈
      RingHom.ker (polySurj R I d g hgen) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hsum0
  have hcomp := hsAssemble_ker_homogeneousComponent_mem I d g hgen _ hker j
  have hsingle : MvPolynomial.homogeneousComponent j
      (∑ i ∈ Finset.range N, x i) = x j := by
    rw [map_sum, Finset.sum_eq_single j
      (fun i _ hij => by
        have h := MvPolynomial.homogeneousComponent_of_mem (m := j)
          ((MvPolynomial.mem_homogeneousSubmodule i (x i)).mpr (hx i))
        rw [ite_eq_right (Ne.symm hij)] at h
        exact h)
      (fun hj' => absurd (Finset.mem_range.mpr hj) hj')]
    have hjj := MvPolynomial.homogeneousComponent_of_mem (m := j)
      ((MvPolynomial.mem_homogeneousSubmodule j (x j)).mpr (hx j))
    rw [ite_eq_left rfl] at hjj
    exact hjj
  rw [hsingle] at hcomp
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hcomp

end R2dQuotGrading

section R2dMasters

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `hmult` with the Hilbert witness stated on the `gr` side (via R-2d′ length
transfer): the nonvanishing conclusion is about the quotient Hilbert function.
-/
theorem mult_hmult_grSide (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (e : ℕ) (Pwit : ℚ[X])
    (hle : Pwit.natDegree ≤ e)
    (hag : (fun n => ((finLength
        (IsLocalRing.ResidueField (Localization.AtPrime P))
        (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n + 1)) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pwit)
    (hc : Pwit.coeff e ≠ 0) :
    ¬ seqDiff e (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hfun : (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ)) =
      (fun n => ((finLength (IsLocalRing.ResidueField (Localization.AtPrime P))
        (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n + 1)) : ℕ) : ℚ)) := by
    funext n
    rw [mult_quotHilbert_eq_grPieceLength P d g hgen]
  rw [hfun]
  exact mult_hmult_of_coeff_ne_zero Pwit hle hag hc

/-- `hdimEq` with the Hilbert witness stated on the `gr` side.
-/
theorem mult_hdimEq_grSide (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (e : ℕ)
    (hFq : IsPolyGrowth (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ)) e)
    (Pwit : ℚ[X])
    (hle : Pwit.natDegree ≤ e)
    (hag : (fun n => ((finLength
        (IsLocalRing.ResidueField (Localization.AtPrime P))
        (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n + 1)) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pwit)
    (hc : Pwit.coeff e ≠ 0) :
    ∀ Q : ℚ[X], Q.natDegree ≤ e →
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q → Q.natDegree = e :=
  hsAssemble_hdimEq_of_not_vanishing hFq
    (mult_hmult_grSide P d g hgen e Pwit hle hag hc)

end R2dMasters

/-! ## §13. Associated-graded dimension (R-2a′ partial)

R-2a′ (`dim gr = d`) needs associated-graded dimension theory
(`dim gr_I(R) = dim R` for Noetherian local `R`), absent from Mathlib. This
section proves what is provable now and isolates the exact missing theorem:

* `mult_isNoetherianRing_grRegular`: `grRegular P` is Noetherian (surjective
  image of the Noetherian polynomial ring) — a needed input for any future
  dimension theory.
* `mult_dim_gr_eq_of_assocGradedDim`: the missing dimension equality
  `dim gr = dim R_P` as an explicit hypothesis plus minimality of `g` gives
  `dim gr = d`.
* `mult_dim_quot_eq_of_assocGradedDim`: same, transported to `dim (S ⧸ ker)`.

The R-2a′ remainder is exactly `hgrdim` below: for Noetherian local `R`,
`dim gr_I(R) = dim R`. Its proof (via Hilbert–Samuel or systems of
parameters) is a major project requiring theory absent from Mathlib.

Status: partial (conditional on `hgrdim`). -/

section R2aPartial

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `grRegular P` is Noetherian: surjective image of the Noetherian polynomial
ring over the residue field.
-/
theorem mult_isNoetherianRing_grRegular (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsNoetherianRing (grRegular P) :=
  isNoetherianRing_of_surjective _ _ (polySurjResidue P d g hgen)
    (polySurjResidue_surjective P d g hgen)

/-- R-2a′ reduced to its missing core: associated-graded dimension equality
(`hgrdim`, absent from Mathlib) plus minimality of `g` gives `dim gr = d`.

Explicitly conditional on `hgrdim`. -/
theorem mult_dim_gr_eq_of_assocGradedDim (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hgrdim : ringKrullDim (grRegular P) =
      ringKrullDim (Localization.AtPrime P)) :
    ringKrullDim (grRegular P) = d := by
  rw [hgrdim]
  exact mult_ringKrullDim_atPrime_eq_of_minimal P d g hgen hmin

/-- R-2a′ transported to the quotient side: `dim (S ⧸ ker) = d`.

Explicitly conditional on `hgrdim`. -/
theorem mult_dim_quot_eq_of_assocGradedDim (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hgrdim : ringKrullDim (grRegular P) =
      ringKrullDim (Localization.AtPrime P)) :
    ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) = d :=
  mult_dim_quot_eq_of_dim_gr P d g hgen
    (mult_dim_gr_eq_of_assocGradedDim P d g hgen hmin hgrdim)

end R2aPartial

/-! ## §14. Hilbert witnesses (R-2c′ partial)

R-2c′ (Hilbert witness from `dim`) needs Hilbert–Serre theory (eventual
polynomiality of Hilbert functions of graded quotients with degree `dim - 1`
and positive leading coefficient), absent from Mathlib. This section proves
what is provable now:

* `mult_ker_eq_bot_of_grWitness`: R-2d′ feeds R-2c′ — a `gr`-side Hilbert
  witness yields `ker = ⊥` (reduces the witness problem to the `gr` side).
* `mult_hmult_unconditional_of_witnessHyp`: the residual isolated as an
  explicit existence hypothesis, yielding unconditional `hmult`.
* `mult_ker_eq_bot_unconditional_of_witnessHyp`: same, yielding `ker = ⊥`.

The R-2c′ remainder is exactly `hwit` below: from `dim (S ⧸ ker) = d`
produce `(Pwit, hle, hag, hc)` with `e = d - 1`.

Status: partial (conditional on `hwit`). -/

section R2cPartial

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- R-2d′ feeds R-2c′: a `gr`-side Hilbert witness yields `ker = ⊥`.

Explicitly conditional on the `gr`-side witness. -/
theorem mult_ker_eq_bot_of_grWitness (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H : ℕ → ℕ) (e : ℕ)
    (hd_pos : 1 < d) (hdim : e + 1 = d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (Pwit : ℚ[X]) (hle : Pwit.natDegree ≤ e)
    (hag : (fun n => ((finLength
        (IsLocalRing.ResidueField (Localization.AtPrime P))
        (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n + 1)) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pwit)
    (hc : Pwit.coeff e ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
          d (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ)) e) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  have hfun : (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ)) =
      (fun n => ((finLength (IsLocalRing.ResidueField (Localization.AtPrime P))
        (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n + 1)) : ℕ) : ℚ)) := by
    funext n
    rw [mult_quotHilbert_eq_grPieceLength P d g hgen]
  have hagQ : (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pwit := by
    rw [hfun]
    exact hag
  exact mult_ker_eq_bot_of_hilbertWitness P d g hgen H e hd_pos hdim hF Pwit
    hle hagQ hc hdrop

/-- R-2c′ isolated as an explicit existence hypothesis, yielding
unconditional `hmult` (with `e = d - 1`).

Explicitly conditional on `hwit`. -/
theorem mult_hmult_unconditional_of_witnessHyp (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0) :
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  obtain ⟨Pwit, hle, hag, hc⟩ := hwit
  exact mult_hmult (IsLocalRing.ResidueField (Localization.AtPrime P)) d
    (RingHom.ker (polySurjResidue P d g hgen)) (d - 1) Pwit hle hag hc

/-- R-2c′ isolated as an explicit existence hypothesis, yielding `ker = ⊥`.

Explicitly conditional on `hwit` (plus the §10 residuals). -/
theorem mult_ker_eq_bot_unconditional_of_witnessHyp (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H : ℕ → ℕ) (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
          d (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
          (d - 1)) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  obtain ⟨Pwit, hle, hag, hc⟩ := hwit
  have hdim : d - 1 + 1 = d := by omega
  exact mult_ker_eq_bot_of_hilbertWitness P d g hgen H (d - 1) hd_pos hdim hF
    Pwit hle hag hc hdrop

end R2cPartial

/-! ## §15. Register update (r2-residuals lane)

Status after (all verified 0 errors 0 warnings):

* R-2d′ closed (§12): quotient grading on `S ⧸ ker` (spanning
  `mult_quotient_spanned_by_homogeneous` + independence
  `mult_quotient_homogeneous_independent`), per-degree linear equivs
  (`multDegQuotEquiv`, `multQuotKerTransport`), length transfer
  (`mult_quotHilbert_eq_grPieceLength` via `mult_lengthTransfer_of_equivs`),
  and `gr`-side masters (`mult_hmult_grSide`, `mult_hdimEq_grSide`).
  Supporting: residue action (`multGrPieceQuotientModule`,
  `multGrPieceResidueModule`), degree map (`multDegMap`,
  `multDegMap_ker_eq`, `mult_polySurj_homogeneous_preimage`,
  `multDegMap_surjective`, `multDegMap_ker_eq_multKerPiece`).
* R-2a′ partial (§13): `mult_isNoetherianRing_grRegular` proved;
  `mult_dim_gr_eq_of_assocGradedDim` /
  `mult_dim_quot_eq_of_assocGradedDim` isolate the exact remainder
  (`hgrdim`: `dim gr_I(R) = dim R` for Noetherian local `R`).
* R-2c′ partial (§14): `mult_ker_eq_bot_of_grWitness` wires R-2d′ into
  R-2c′; `mult_hmult_unconditional_of_witnessHyp` /
  `mult_ker_eq_bot_unconditional_of_witnessHyp` isolate the exact remainder
  (`hwit`: Hilbert witness from `dim`).

Status: as marked per theorem. -/

#print axioms mult_quotHilbert_eq_grPieceLength
#print axioms mult_quotient_homogeneous_independent
#print axioms mult_hmult_grSide
#print axioms mult_isNoetherianRing_grRegular
#print axioms mult_dim_quot_eq_of_assocGradedDim
#print axioms mult_ker_eq_bot_of_grWitness
#print axioms mult_ker_eq_bot_unconditional_of_witnessHyp

/-! ## §16. Minimal remainder for R-2a′ (`d ≤ dim gr`)

The §13 hypothesis `hgrdim` (`dim gr = dim R_P`) is stronger than needed:
`dim gr ≤ d` is already unconditional (`mult_ringKrullDim_gr_le`), so the
single lower bound `hle_gr : d ≤ dim gr` alone yields `dim gr = d` (no `hmin`
needed). Given `hmin`, the new remainder is exactly equivalent to `hgrdim`
(`mult_hgrdim_of_gr_lowerBound` / `mult_gr_lowerBound_of_hgrdim`), so the
R-2a′ remainder is now minimal: one inequality instead of an equality of two
Krull dimensions.

The lower bound itself is the true core: producing a length-`d` prime chain
in `gr` needs Hilbert–Samuel / systems-of-parameters dimension theory, which
is absent from Mathlib (no catenary, system-of-parameters, Hilbert–Samuel, or
associated-graded files under `Mathlib/RingTheory/` at the pinned toolchain).
No unconditional proof is attempted here.

* `mult_dim_gr_eq_of_gr_lowerBound`: `d ≤ dim gr → dim gr = d`.
* `mult_dim_quot_eq_of_gr_lowerBound`: transported to `dim (S ⧸ ker) = d`.
* `mult_hgrdim_of_gr_lowerBound`: `hmin` + `hle_gr` recovers §13 `hgrdim`.
* `mult_gr_lowerBound_of_hgrdim`: `hmin` + `hgrdim` gives `hle_gr` (exactness).
-/

section R2aMinimal

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- R-2a′ from its minimal core: the lower bound `d ≤ dim gr` alone gives
`dim gr = d` (upper bound is `mult_ringKrullDim_gr_le`).
-/
theorem mult_dim_gr_eq_of_gr_lowerBound (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hle_gr : d ≤ ringKrullDim (grRegular P)) :
    ringKrullDim (grRegular P) = d :=
  le_antisymm (mult_ringKrullDim_gr_le P d g hgen) hle_gr

/-- Minimal-core form transported to the quotient side: `dim (S ⧸ ker) = d`.
-/
theorem mult_dim_quot_eq_of_gr_lowerBound (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hle_gr : d ≤ ringKrullDim (grRegular P)) :
    ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) = d :=
  mult_dim_quot_eq_of_dim_gr P d g hgen
    (mult_dim_gr_eq_of_gr_lowerBound P d g hgen hle_gr)

/-- The §13 `hgrdim` equality recovered from `hmin` plus the minimal lower
bound (so the §13 masters discharge on the weaker hypothesis).
-/
theorem mult_hgrdim_of_gr_lowerBound (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hle_gr : d ≤ ringKrullDim (grRegular P)) :
    ringKrullDim (grRegular P) =
      ringKrullDim (Localization.AtPrime P) := by
  rw [mult_dim_gr_eq_of_gr_lowerBound P d g hgen hle_gr,
    mult_ringKrullDim_atPrime_eq_of_minimal P d g hgen hmin]

/-- Exactness converse: `hmin` plus §13 `hgrdim` yields the minimal lower
bound, so `hle_gr` and `hgrdim` are equivalent given `hmin`.
-/
theorem mult_gr_lowerBound_of_hgrdim (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hgrdim : ringKrullDim (grRegular P) =
      ringKrullDim (Localization.AtPrime P)) :
    d ≤ ringKrullDim (grRegular P) := by
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal P d g hgen hmin
  rw [hgrdim, hR]

end R2aMinimal

#print axioms mult_dim_gr_eq_of_gr_lowerBound
#print axioms mult_dim_quot_eq_of_gr_lowerBound
#print axioms mult_hgrdim_of_gr_lowerBound
#print axioms mult_gr_lowerBound_of_hgrdim

/-! ## §17. `hle_gr` is equivalent to `ker = ⊥` (circularity collapse)

The §16 remainder `hle_gr : d ≤ dim gr` is not independent of the R-2c′ goal
`ker = ⊥`: the two are equivalent, by unconditional proofs in both directions.

* `mult_hle_gr_iff_quot_lowerBound`: `hle_gr` is the quotient-side lower bound
  `d ≤ dim (S ⧸ ker)` (via `mult_quotKerEquiv_dim`).
* `mult_ker_eq_bot_of_quot_lowerBound`: full dimension of a polynomial
  quotient forces a trivial kernel. Given `d ≤ dim (S ⧸ ker)`,
  `Order.le_krullDim_iff` yields a length-`d` prime chain upstairs; comap along
  the surjective quotient map pushes it to a length-`d` chain in `S` starting
  above `ker`. If the chain starts at `⊥`, then `ker = ⊥`; else prepending `⊥`
  gives a length-`d+1` chain in `S`, contradicting `dim S = d`.
* `mult_hle_gr_of_ker_eq_bot`: `ker = ⊥` gives `hle_gr` (via `S ⧸ ⊥ ≃+* S`).
* `mult_hle_gr_iff_ker_eq_bot`: the collapse (`hle_gr ↔ ker = ⊥`).

circularity (exact dependency chain): closing `hle_gr` unconditionally would
close `ker = ⊥` unconditionally (by `mult_ker_eq_bot_of_quot_lowerBound`), and
`ker = ⊥` is exactly what the §10 master `hsAssemble_ker_eq_bot_of_mult`
produces from `hmult` + `hdrop`, where `hmult` needs the Hilbert witness `hwit`
(§14), which is predicated on `dim (S ⧸ ker) = d`, which needs `hle_gr`. The
cycle is `hle_gr → dim = d → hwit → hmult → ker = ⊥ → hle_gr`. No proof of
`hle_gr` avoiding this cycle exists below the strength of `ker = ⊥` itself:
any route through algebraic independence of the `d` gr-classes, `hdimEq`, or
`ker = ⊥` is circular. This section assumes none of them.

narrowing: the collapse reduces two residuals to one. `hle_gr` (R-2a′
remainder) follows from the R-2c′ remainder `hwit`:
* `mult_hle_gr_of_witnessHyp`: conditional-exact on `[hwit, hF, hdrop, hd_pos]`.
* `mult_dim_quot_eq_of_witnessHyp` / `mult_dim_gr_eq_of_witnessHyp`: both R-2a
  equalities from the same single remainder.

Minimal non-circular remainder (verbatim): `hwit`, i.e.
`∃ Pwit: ℚ[X], Pwit.natDegree ≤ d - 1 ∧ Hq =ᶠ[atTop] evalFun Pwit ∧
Pwit.coeff (d - 1) ≠ 0` for the shifted quotient Hilbert function `Hq`
(see `mult_ker_eq_bot_unconditional_of_witnessHyp`), plus the §10 side data
`hF`, `hdrop`, `hd_pos`. Nothing strictly weaker than `ker = ⊥` implies
`hle_gr` (any `ker ≠ ⊥` is consistent with the hypotheses but refuted only by
the full chain argument landing `ker = ⊥`).

conditional-exact on `[hwit, hF, hdrop, hd_pos]` for the witness corollaries;
partial overall (`hwit` open). -/

section HleCollapse

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Transport: `hle_gr` is the quotient-side lower bound `d ≤ dim (S ⧸ ker)`.
-/
theorem mult_hle_gr_iff_quot_lowerBound (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    (d ≤ ringKrullDim (grRegular P)) ↔
      d ≤ ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) := by
  rw [mult_quotKerEquiv_dim P d g hgen]

/-- Full dimension of a polynomial quotient forces a trivial kernel: from
`d ≤ dim (S ⧸ ker)` a length-`d` prime chain upstairs pushes forward along the
surjective quotient map to a length-`d` chain in `S` starting above `ker`;
either it starts at `⊥` (so `ker = ⊥`) or prepending `⊥` contradicts
`dim S = d`.
-/
theorem mult_ker_eq_bot_of_quot_lowerBound (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ))
    (hle : d ≤ ringKrullDim (MvPolynomial (Fin d) κ ⧸ ker)) :
    ker = ⊥ := by
  have hle' :
      d ≤ Order.krullDim (PrimeSpectrum (MvPolynomial (Fin d) κ ⧸ ker)) := hle
  obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hle'
  have hsurj : Function.Surjective (Ideal.Quotient.mk ker) :=
    Ideal.Quotient.mk_surjective
  set F : PrimeSpectrum (MvPolynomial (Fin d) κ ⧸ ker) →
      PrimeSpectrum (MvPolynomial (Fin d) κ) :=
    fun x =>
      ⟨Ideal.comap (Ideal.Quotient.mk ker) x.asIdeal, inferInstance⟩
  have hstrict : StrictMono F := by
    intro x y hxy
    have hleI : x.asIdeal ≤ y.asIdeal := le_of_lt hxy
    have hleC : Ideal.comap (Ideal.Quotient.mk ker) x.asIdeal ≤
        Ideal.comap (Ideal.Quotient.mk ker) y.asIdeal :=
      Ideal.comap_mono hleI
    have hinj : Function.Injective
        (Ideal.comap (Ideal.Quotient.mk ker) :
          Ideal (MvPolynomial (Fin d) κ ⧸ ker) →
          Ideal (MvPolynomial (Fin d) κ)) :=
      Ideal.comap_injective_of_surjective (Ideal.Quotient.mk ker) hsurj
    have hneC : Ideal.comap (Ideal.Quotient.mk ker) x.asIdeal ≠
        Ideal.comap (Ideal.Quotient.mk ker) y.asIdeal := by
      intro hcon
      have hconI : x.asIdeal = y.asIdeal := hinj hcon
      have hltI : x.asIdeal < y.asIdeal := hxy
      exact absurd hconI (ne_of_lt hltI)
    change Ideal.comap (Ideal.Quotient.mk ker) x.asIdeal <
      Ideal.comap (Ideal.Quotient.mk ker) y.asIdeal
    exact lt_of_le_of_ne hleC hneC
  set l' : LTSeries (PrimeSpectrum (MvPolynomial (Fin d) κ)) :=
    l.map F hstrict with hl'
  have hlen' : l'.length = d := by
    rw [hl', LTSeries.map_length]
    exact hlen
  have hheadI : (l'.head).asIdeal =
      Ideal.comap (Ideal.Quotient.mk ker) (l.head).asIdeal := rfl
  have hker_le :
      ker ≤ Ideal.comap (Ideal.Quotient.mk ker) (l.head).asIdeal := by
    intro x hx
    rw [Ideal.mem_comap]
    have h0 : Ideal.Quotient.mk ker x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    rw [h0]
    exact (l.head).asIdeal.zero_mem
  by_cases hq0 : (l'.head).asIdeal = ⊥
  · apply eq_bot_iff.mpr
    calc ker ≤ Ideal.comap (Ideal.Quotient.mk ker) (l.head).asIdeal := hker_le
      _ = (l'.head).asIdeal := hheadI.symm
      _ = ⊥ := hq0
  · have hbot :
        (⟨⊥, inferInstance⟩ : PrimeSpectrum (MvPolynomial (Fin d) κ)) <
          l'.head := by
      change (⊥ : Ideal (MvPolynomial (Fin d) κ)) < (l'.head).asIdeal
      exact bot_lt_iff_ne_bot.mpr hq0
    set q := l'.cons _ hbot with hq
    have hqlen : q.length = d + 1 := by
      rw [hq, RelSeries.cons_length, hlen']
    have hleS := Order.LTSeries.length_le_krullDim q
    have hdim : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin d) κ)) = d :=
      mult_ringKrullDim_poly κ d
    rw [hqlen, hdim] at hleS
    have hcontra : d + 1 ≤ d := by exact_mod_cast hleS
    omega

/-- `ker = ⊥` gives `hle_gr` (`S ⧸ ⊥ ≃+* S` has dimension `d`).
-/
theorem mult_hle_gr_of_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    d ≤ ringKrullDim (grRegular P) := by
  have hdim : ringKrullDim (grRegular P) = d := by
    rw [← mult_quotKerEquiv_dim P d g hgen, hker,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      mult_ringKrullDim_poly]
  rw [hdim]

/-- Collapse: `hle_gr` holds iff `ker = ⊥` (both directions unconditional).
-/
theorem mult_hle_gr_iff_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    (d ≤ ringKrullDim (grRegular P)) ↔
      RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  constructor
  · intro hle
    have hleQ : d ≤ ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) :=
      (mult_hle_gr_iff_quot_lowerBound P d g hgen).mp hle
    exact mult_ker_eq_bot_of_quot_lowerBound _ d _ hleQ
  · exact mult_hle_gr_of_ker_eq_bot P d g hgen

/-- Narrowing: the R-2a′ remainder `hle_gr` follows from the R-2c′ remainder
`hwit` (via `mult_ker_eq_bot_unconditional_of_witnessHyp`).

Conditional on exactly `[hwit, hF, hdrop, hd_pos]`. -/
theorem mult_hle_gr_of_witnessHyp (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H : ℕ → ℕ) (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
          d (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
          (d - 1)) :
    d ≤ ringKrullDim (grRegular P) := by
  have hker := mult_ker_eq_bot_unconditional_of_witnessHyp P d g hgen H hd_pos
    hF hwit hdrop
  exact mult_hle_gr_of_ker_eq_bot P d g hgen hker

/-- Full R-2a on the quotient side from the single remainder `hwit`.

Conditional on exactly `[hwit, hF, hdrop, hd_pos]`. -/
theorem mult_dim_quot_eq_of_witnessHyp (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H : ℕ → ℕ) (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
          d (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
          (d - 1)) :
    ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) = d := by
  have hker := mult_ker_eq_bot_unconditional_of_witnessHyp P d g hgen H hd_pos
    hF hwit hdrop
  rw [hker, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    mult_ringKrullDim_poly]

/-- Full R-2a on the `gr` side from the single remainder `hwit`.

Conditional on exactly `[hwit, hF, hdrop, hd_pos]`. -/
theorem mult_dim_gr_eq_of_witnessHyp (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H : ℕ → ℕ) (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
          d (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
          (d - 1)) :
    ringKrullDim (grRegular P) = d :=
  mult_dim_gr_eq_of_gr_lowerBound P d g hgen
    (mult_hle_gr_of_witnessHyp P d g hgen H hd_pos hF hwit hdrop)

end HleCollapse

#print axioms mult_hle_gr_iff_quot_lowerBound
#print axioms mult_ker_eq_bot_of_quot_lowerBound
#print axioms mult_hle_gr_of_ker_eq_bot
#print axioms mult_hle_gr_iff_ker_eq_bot
#print axioms mult_hle_gr_of_witnessHyp
#print axioms mult_dim_quot_eq_of_witnessHyp
#print axioms mult_dim_gr_eq_of_witnessHyp

end MultiplicityNonvanishing
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
