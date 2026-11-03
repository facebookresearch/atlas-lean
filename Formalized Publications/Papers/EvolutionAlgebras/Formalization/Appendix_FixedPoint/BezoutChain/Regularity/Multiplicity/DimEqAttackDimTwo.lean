/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.CruxLowerFaceDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactEmbDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactnessDischarge
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo

/-!
# DimEq-analytic attack at embdim 2
Bank + attack on `HdimEqD2AtAss`, the single analytic remainder of the
GX discharge (the exact-degree property of `H_gr` at embdim
exactly 2: every degree-`≤ 1` polynomial approximant has degree exactly
`1`). This lane owns DIMequality (`hdimEq`); the sibling D2H lane owns
the leading-coefficient angle (`hle`) — different SPECs, shared Hilbert
bank. D2H shapes enter below only as SPEC hypotheses (§4 coordination
bridge), never as dependencies on sibling output.

## What this file proves

* (§1) bank-a — quotient-Hilbert pins transported to `H_gr`: `H(0) = 1`
  and `H(1) = 2` for `singleDrop_grHilbert` itself (per-family
  conditional-form on `[hmin]` via the R-2d′ length bridge +
  HighAttack §1, per-prime form via the grlift family), plus the `d = 2`
  domain values identifying the pins as full stars-and-bars values.
* (§2) bank-b — cumsum exactness at `d = 2`: the unconditional bridge
  pins `hsSamuel 0 = 1` and `hsSamuel 1 = 3` (per-family and per-prime).
* (§3) bank-c — the Newton-core iff web at `e = 1`: the exact-degree
  piece is exactly eventual non-constancy of the sequence (pure
  sequence/polynomial calculus, no `hF` input), instantiated to `H_gr`
  per prime, plus the `hne ⟺ piece` conditional-form on `[hF]`.
* (§4) attack — `HdimEqD2AtAss` via the bank: the sequence-only
  non-stabilization SPEC `HgrNonstabD2AtAss` (no polynomials, no family,
  no `ker`, no multiplicity — strictly narrower vocabulary than the
  slice) is unconditionally iff the slice, and closes `HgrExactD2`,
  `HkerD2`, `HmultD2`, and per-prime `hsExactD2` by single `exact`s;
  the D2H-angle compatibility bridge (`HhleD2` closes the slice); the
  HS-face iff (per-prime `hsExact` degree 2 ⟺ the slice piece,
  extending the §3 iff); and the genuine-failure witnesses showing
  the §1 pins are consistent with both stabilization and growth.
* (§5, doc-only) Remainder register + verdict.

## Status

unconditional: `dimEqAttack_grHilbert_zero_eq_one`,
`dimEqAttack_grHilbert_one_eq_two`, `dimEqAttack_grHilbert01_of_embdim`,
`dimEqAttack_domainHilbert_d2_zero`, `dimEqAttack_domainHilbert_d2_one`,
`dimEqAttack_hsSamuel_zero_eq_one`, `dimEqAttack_hsSamuel_one_eq_three`,
`dimEqAttack_hsSamuel01_of_embdim`,
`dimEqAttack_dimEq_piece_iff_nonstab`, `dimEqAttack_grPiece_iff_nonstab`,
`dimEqAttack_hdimEqD2_iff_nonstab`,
`dimEqAttack_hsExact_iff_dimEq_piece`,
`dimEqAttack_pins_consistent_with_stabilization`,
`dimEqAttack_pins_consistent_with_growth`.
conditional-exact on `[hF]` (conditional-form): `dimEqAttack_hne_iff_piece`.
conditional-exact on `[HgrNonstabD2AtAss]`: `dimEqAttack_hdimEqD2_of_nonstab`,
`dimEqAttack_grExactD2_of_nonstab`, `dimEqAttack_hkerD2_of_nonstab`,
`dimEqAttack_hmultD2_of_nonstab`, `dimEqAttack_hsExactD2_of_nonstab`.
conditional-exact on `[HdimEqD2AtAss]`: `dimEqAttack_nonstab_of_hdimEqD2`.
conditional-exact on `[HhleD2AtAss]` (D2H-SPEC shape):
`dimEqAttack_hdimEqD2_of_hleD2`.
Overall: partial, remainder exactly `HgrNonstabD2AtAss` (§5).
The non-stabilization SPEC is the weakest sufficient condition (it is the
slice itself in sequence-only vocabulary), so no strictly weaker analytic
remainder exists in this vocabulary — the §4 witnesses pin down exactly
why: finite initial data never determines the tail.

## References

Project (read-only):
* `Regularity/Koszul/GradedExactnessDischarge.lean` (the `HdimEqD2AtAss` SPEC §1 +
  Newton-core reversal + §2 masters, all consumed, never reproved).
* `Regularity/Koszul/GradedExactEmbDimTwo.lean` (§1 `hF`, §6 cumsum converse,
  `grExact_hsExactD2_of_grExact`:264).
* `Regularity/Multiplicity/WitnessHighAttack.lean` (§1 ker-piece/quotient values,
  §4 `HgrExactD2AtAss` SPEC).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean` (`hsAssemble_hdimEq_of_not_vanishing`,
  `hsAssemble_not_vanishing_of_hdimEq`, `hsAssemble_domainHilbert_eq_choose`).
* `Regularity/Multiplicity/HilbertSamuelDegree.lean` (`hsCumsum`, `hsSamuel`,
  `hsBridge_hs_eq_cumsum_unconditional`,
  `hsBridge_hs_exact_of_gr_exact_unconditional`).
* `Regularity/Multiplicity/KernelAssembly.lean` (R-2d′ bridge:
  `ker_assemble_grHilbert_eq_hsQuot`, `ker_assemble_hsQuot_eq_multQuot`).
* `Regularity/Koszul/GradedLift.lean` (`grlift_sop_exists`).
* `Regularity/HomologicalDepth/WitnessKernelDimTwo.lean` (`HkerD2AtAss`, `HhleD2AtAss`,
  `hhleD2_iff_hkerD2`).
* `Regularity/Multiplicity/CruxLowerFaceDimTwo.lean` (`HmultD2AtAss` SPEC).
* `Regularity/Multiplicity/NewtonDifferences.lean` (`seqDiff`, `evalFun`, `IsPolyGrowth`).
* `Regularity/Multiplicity/SingleDropRegularity.lean` (`singleDrop_grHilbert`).
* `Regularity/Koszul/FiltrationStability.lean`: imported for the
  `IsNoetherianRing (AtPrime)` instance only.
* `Regularity/Koszul/LengthFramework.lean` (read for the length↔finrank bridge;
  consumed transitively via `hsAssemble_domainHilbert_eq_choose`).

-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace DimEqAttackDimTwo

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CruxLowerFaceDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedExactEmbDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedExactnessDischarge
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo

/-! ## §1. Bank-a: quotient-Hilbert pins transported to `H_gr` -/

/-- `H_gr(0) = 1` at `d = 2` from minimality: the R-2d′ length bridge
identifies `singleDrop_grHilbert` with `multQuotHilbert` pointwise, and
HighAttack §1 pins the quotient value (`Low` + unit chase kill the
degree-0 ker piece; stars-and-bars gives `choose 1 1`).
-/
theorem dimEqAttack_grHilbert_zero_eq_one {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      0 = 1 := by
  rw [ker_assemble_grHilbert_eq_hsQuot Q 2 g hgen 0,
    ker_assemble_hsQuot_eq_multQuot]
  exact highAttack_quotHilbert_zero_eq_one Q g hgen hmin

/-- `H_gr(1) = 2` at `d = 2` from minimality: same bridge; `Low` kills
the degree-1 ker piece and stars-and-bars gives `choose 2 1`.
-/
theorem dimEqAttack_grHilbert_one_eq_two {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      1 = 2 := by
  rw [ker_assemble_grHilbert_eq_hsQuot Q 2 g hgen 1,
    ker_assemble_hsQuot_eq_multQuot]
  exact highAttack_quotHilbert_one_eq_two Q g hgen hmin

/-- Per-prime `H_gr` pins at embdim 2: the grlift family identifies
`d` with `2`, minimality is the embdim equation.
-/
theorem dimEqAttack_grHilbert01_of_embdim (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        0 = 1 ∧
      singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        1 = 2 := by
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hemb
  exact ⟨dimEqAttack_grHilbert_zero_eq_one Q g hgen hmin,
    dimEqAttack_grHilbert_one_eq_two Q g hgen hmin⟩

/-- The `d = 2` domain value at 0: the §1 pins are the full
stars-and-bars values (`choose 1 1`), i.e. the ker pieces contribute
nothing at degree 0.
-/
theorem dimEqAttack_domainHilbert_d2_zero (κ : Type*) [Field κ] :
    hsAssemble_domainHilbert κ 2 0 = 1 := by
  have hSB := hsAssemble_domainHilbert_eq_choose κ 2 (by omega) 0
  rw [hSB]
  decide

/-- The `d = 2` domain value at 1 (`choose 2 1`).
-/
theorem dimEqAttack_domainHilbert_d2_one (κ : Type*) [Field κ] :
    hsAssemble_domainHilbert κ 2 1 = 2 := by
  have hSB := hsAssemble_domainHilbert_eq_choose κ 2 (by omega) 1
  rw [hSB]
  decide

/-! ## §2. Bank-b: cumsum exactness at `d = 2` -/

/-- `hsSamuel 0 = 1` at `d = 2`: the unconditional bridge identifies
`hsSamuel` with the cumsum of `H_gr`, and the cumsum at 0 is `H(0)`.
-/
theorem dimEqAttack_hsSamuel_zero_eq_one {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    hsSamuel (R := Localization.AtPrime Q) 0 = 1 := by
  have hbridge := hsBridge_hs_eq_cumsum_unconditional
    (R := Localization.AtPrime Q)
  have hcongr := congrFun hbridge 0
  have hsum : hsCumsum (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      0 = 1 := by
    unfold hsCumsum
    have e1 : 0 + 1 = 1 := by omega
    rw [e1, Finset.sum_range_one,
      dimEqAttack_grHilbert_zero_eq_one Q g hgen hmin, Nat.cast_one]
  rw [hsum] at hcongr
  change ((hsSamuel (R := Localization.AtPrime Q) 0 : ℕ) : ℚ) = 1 at hcongr
  exact_mod_cast hcongr

/-- `hsSamuel 1 = 3` at `d = 2`: the cumsum at 1 is `H(0) + H(1)`.
-/
theorem dimEqAttack_hsSamuel_one_eq_three {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    hsSamuel (R := Localization.AtPrime Q) 1 = 3 := by
  have hbridge := hsBridge_hs_eq_cumsum_unconditional
    (R := Localization.AtPrime Q)
  have hcongr := congrFun hbridge 1
  have hsum : hsCumsum (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      1 = 3 := by
    unfold hsCumsum
    have e2 : 1 + 1 = 2 := by omega
    rw [e2, Finset.sum_range_succ,
      Finset.sum_range_one,
      dimEqAttack_grHilbert_zero_eq_one Q g hgen hmin,
      dimEqAttack_grHilbert_one_eq_two Q g hgen hmin]
    norm_num
  rw [hsum] at hcongr
  change ((hsSamuel (R := Localization.AtPrime Q) 1 : ℕ) : ℚ) = 3 at hcongr
  exact_mod_cast hcongr

/-- Per-prime `hsSamuel` pins at embdim 2.
-/
theorem dimEqAttack_hsSamuel01_of_embdim (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    hsSamuel (R := Localization.AtPrime Q) 0 = 1 ∧
      hsSamuel (R := Localization.AtPrime Q) 1 = 3 := by
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hemb
  exact ⟨dimEqAttack_hsSamuel_zero_eq_one Q g hgen hmin,
    dimEqAttack_hsSamuel_one_eq_three Q g hgen hmin⟩

/-! ## §3. Bank-c: the Newton-core iff web at `e = 1` -/

/-- The exact-degree piece at `e = 1` is exactly eventual
non-constancy of the sequence — pure sequence/polynomial calculus, no
`hF` input. Forward: a constant tail `=ᶠ c` is agreed with by `C c`
(degree 0), against the piece forcing degree 1. Backward: an
approximant of degree `≤ 1` has degree 0 or 1; degree 0 makes its
evaluation sequence constant, against non-stabilization.
-/
theorem dimEqAttack_dimEq_piece_iff_nonstab {F : ℕ → ℚ} :
    ((∀ Qw : ℚ[X], Qw.natDegree ≤ 2 - 1 →
      F =ᶠ[Filter.atTop] evalFun Qw → Qw.natDegree = 2 - 1)
      ↔ ∀ c : ℚ, ¬ F =ᶠ[Filter.atTop] fun _ => c) := by
  constructor
  · intro hdim c hcon
    have hev : evalFun (Polynomial.C c) = fun _ => c := by
      funext n
      change (Polynomial.C c).eval (n : ℚ) = c
      exact Polynomial.eval_C
    have hag : F =ᶠ[Filter.atTop] evalFun (Polynomial.C c) := by
      rw [hev]
      exact hcon
    have hdeg := hdim (Polynomial.C c)
      (by rw [Polynomial.natDegree_C]; omega) hag
    rw [Polynomial.natDegree_C] at hdeg
    omega
  · intro hnonstab Qw hle hag
    by_cases h1 : Qw.natDegree = 1
    · omega
    · have h0 : Qw.natDegree = 0 := by omega
      have heval : evalFun Qw = fun _ => Qw.eval 0 := by
        funext n
        change Qw.eval (n : ℚ) = Qw.eval 0
        have hQw := Polynomial.eq_C_of_natDegree_eq_zero h0
        rw [hQw]
        simp only [Polynomial.eval_C]
      exfalso
      exact hnonstab (Qw.eval 0) (by rw [heval] at hag; exact hag)

/-- The §3 centerpiece at `H_gr`, per prime: the `d = 2` exact-degree
piece is exactly non-stabilization of `H_gr`. No growth input.
-/
theorem dimEqAttack_grPiece_iff_nonstab {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ((∀ Qw : ℚ[X], Qw.natDegree ≤ 2 - 1 →
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Qw → Qw.natDegree = 2 - 1)
      ↔ ∀ c : ℚ, ¬ (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] fun _ => c) :=
  dimEqAttack_dimEq_piece_iff_nonstab

/-- `hne ⟺ piece` at `H_gr`, conditional-form on `[hF]`: the two
HSAssemble §10 directions instantiated at `e := 1`.

Conditional on exactly `[hF]` (conditional-form). -/
theorem dimEqAttack_hne_iff_piece {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hF : IsPolyGrowth (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      1) :
    ((¬ seqDiff 1 (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0)
      ↔ (∀ Qw : ℚ[X], Qw.natDegree ≤ 2 - 1 →
        (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun Qw → Qw.natDegree = 2 - 1)) := by
  constructor
  · intro hne
    exact hsAssemble_hdimEq_of_not_vanishing hF hne
  · intro hdim
    exact hsAssemble_not_vanishing_of_hdimEq (e := 1) (by omega) hF hdim

/-! ## §4. Attack: `HdimEqD2AtAss` via the bank -/

/-- Eventual non-stabilization of `H_gr` at embdim exactly 2: per
`Q ∈ Ass(R ⧸ J)` at embdim 2, `H_gr` agrees with no constant sequence.
Sequence-only vocabulary — no polynomials, no family, no `ker`, no
multiplicity, no s.o.p.: strictly narrower vocabulary than every other
D2-ring form including the slice itself. This is the exact surviving
remainder of this file, and (§3) the weakest sufficient condition.

Specification (Prop address for the non-stabilization hypothesis). -/
def HgrNonstabD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ∀ c : ℚ, ¬ (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] fun _ => c

/-- The slice on `[HgrNonstabD2AtAss]`: the §3 centerpiece, universally
quantified. The attack's main closure leg.

Conditional on exactly `[hnonstab]`. -/
theorem dimEqAttack_hdimEqD2_of_nonstab (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hnonstab : HgrNonstabD2AtAss m K J) :
    HdimEqD2AtAss m K J := by
  intro Q _ hQ hemb Qw hle hag
  exact (dimEqAttack_grPiece_iff_nonstab Q).mpr
    (hnonstab Q hQ hemb) Qw hle hag

/-- Non-stabilization on `[HdimEqD2AtAss]`: the §3 converse,
universally quantified.

Conditional on exactly `[hslice]`. -/
theorem dimEqAttack_nonstab_of_hdimEqD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hslice : HdimEqD2AtAss m K J) :
    HgrNonstabD2AtAss m K J := by
  intro Q _ hQ hemb c hcon
  exact (dimEqAttack_grPiece_iff_nonstab Q).mp
    (hslice Q hQ hemb) c hcon

/-- The slice is non-stabilization: `HgrNonstabD2AtAss` joins the D2
ring (via the GX iff) in the narrowest vocabulary in tree.
-/
theorem dimEqAttack_hdimEqD2_iff_nonstab (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqD2AtAss m K J ↔ HgrNonstabD2AtAss m K J :=
  ⟨dimEqAttack_nonstab_of_hdimEqD2 m K J,
    dimEqAttack_hdimEqD2_of_nonstab m K J⟩

/-- `HgrExactD2AtAss` on `[HgrNonstabD2AtAss]`: the slice (§4 above)
feeds the GX §2 master.

Conditional on exactly `[hnonstab]`. -/
theorem dimEqAttack_grExactD2_of_nonstab (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hnonstab : HgrNonstabD2AtAss m K J) :
    HgrExactD2AtAss m K J :=
  grExactDischarge_grExactD2_of_hdimEqD2 m K J
    (dimEqAttack_hdimEqD2_of_nonstab m K J hnonstab)

/-- `HkerD2AtAss` on `[HgrNonstabD2AtAss]`: via the independent
KerAssemble + GrLower track (GX §2).

Conditional on exactly `[hnonstab]`. -/
theorem dimEqAttack_hkerD2_of_nonstab (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hnonstab : HgrNonstabD2AtAss m K J) :
    HkerD2AtAss m K J :=
  grExactDischarge_hkerD2_of_hdimEqD2 m K J
    (dimEqAttack_hdimEqD2_of_nonstab m K J hnonstab)

/-- `HmultD2AtAss` on `[HgrNonstabD2AtAss]`: the CruxD2 shape.

Conditional on exactly `[hnonstab]`. -/
theorem dimEqAttack_hmultD2_of_nonstab (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hnonstab : HgrNonstabD2AtAss m K J) :
    HmultD2AtAss m K J :=
  grExactDischarge_hmultD2_of_hdimEqD2 m K J
    (dimEqAttack_hdimEqD2_of_nonstab m K J hnonstab)

/-- Per-prime HS exact degree 2 on `[HgrNonstabD2AtAss]`: non-stabilization
closes gr-exactness, which feeds the GrExact §5 master.

Conditional on exactly `[hnonstab]`. -/
theorem dimEqAttack_hsExactD2_of_nonstab (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hnonstab : HgrNonstabD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  grExact_hsExactD2_of_grExact m K J
    (dimEqAttack_grExactD2_of_nonstab m K J hnonstab) Q hQ hemb

/-- D2H-angle compatibility: the leading-coefficient SPEC `HhleD2AtAss`
closes the slice (hle ⟺ ker by the D2 ring, ker closes gr-exactness by
GrExact §3, gr-exactness closes the slice by GX §2). If the sibling
D2H lane proves `hle`, dimEq falls by this single `exact` — cited here
only as a SPEC shape, never depending on sibling output.

Conditional on exactly `[hhle]` (D2H-SPEC shape). -/
theorem dimEqAttack_hdimEqD2_of_hleD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hhle : HhleD2AtAss m K J) :
    HdimEqD2AtAss m K J :=
  grExactDischarge_hdimEqD2_of_grExactD2 m K J
    (grExact_grExactD2_of_hkerD2 m K J
      ((hhleD2_iff_hkerD2 m K J).mp hhle))

/-- Per-prime HS exact degree 2 ⟺ the slice piece at embdim 2.
Forward: HS exactness recovers gr-side nonvanishing (cumsum converse)
which with unconditional `hF` gives the exact-degree reading.
Backward: the piece forces nonvanishing (§3 converse direction with
`hF`), which with `hF` gives HS exactness (unconditional bridge).
Extends the GX §3 iff (hsExact ⟺ grExact-piece) to the slice face.
-/
theorem dimEqAttack_hsExact_iff_dimEq_piece (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ((∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S)
      ↔ (∀ Qw : ℚ[X], Qw.natDegree ≤ 2 - 1 →
        (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun Qw → Qw.natDegree = 2 - 1)) := by
  constructor
  · intro hHS
    have hF := grExact_hF_d2 m K J Q hQ hemb
    have hne := grExact_hne_of_hsExactD2 Q hHS
    exact hsAssemble_hdimEq_of_not_vanishing hF hne
  · intro hdim
    have hF := grExact_hF_d2 m K J Q hQ hemb
    have hne : ¬ seqDiff 1 (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0 :=
      hsAssemble_not_vanishing_of_hdimEq (e := 1) (by omega) hF hdim
    exact hsBridge_hs_exact_of_gr_exact_unconditional hF hne

/-- Genuine-failure witness, stabilization side: the §1 pins `H(0) = 1`,
`H(1) = 2` are consistent with an eventually constant tail — so no
unconditional close of the slice from finite initial data exists, and
the §4 remainder is genuinely a tail condition.
-/
theorem dimEqAttack_pins_consistent_with_stabilization :
    ∃ F : ℕ → ℚ, F 0 = 1 ∧ F 1 = 2 ∧
      ∃ c : ℚ, F =ᶠ[Filter.atTop] fun _ => c := by
  refine ⟨fun n => if n = 0 then 1 else 2, rfl, rfl, 2, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hne : n ≠ 0 := by omega
  simp [hne]

/-- Genuine-failure witness, growth side: the same pins are consistent
with a never-stabilizing tail — so the pins carry no information about
the slice either way.
-/
theorem dimEqAttack_pins_consistent_with_growth :
    ∃ G : ℕ → ℚ, G 0 = 1 ∧ G 1 = 2 ∧
      ∀ c : ℚ, ¬ G =ᶠ[Filter.atTop] fun _ => c := by
  refine ⟨fun n => (n : ℚ) + 1, by simp, by norm_num, ?_⟩
  intro c hcon
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcon
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  simp only at h1 h2
  rw [Nat.cast_add, Nat.cast_one] at h2
  linarith

/-! ## §5. Remainder register + verdict (doc-only)

exact residual of the dimEq leg, post-attack (verbatim):

* `HgrNonstabD2AtAss` (§4 SPEC: per `Q ∈ Ass(R ⧸ J)` at embdim exactly 2,
  `H_gr` agrees with no constant sequence): closes `HdimEqD2AtAss` (§4
  main leg), hence `HgrExactD2AtAss`, `HkerD2AtAss`, `HmultD2AtAss` (§4
  consumers), and per-prime `hsExactD2` (§4) by single `exact`s.
  Crux-ring form (iff the slice, §4; hence iff every D2-ring form via
  the GX iff + ReesClose).

why the residual is the narrowest possible (all machine-checked):

* Vocabulary: unlike every other D2-ring form (the slice quantifies
  over `ℚ[X]` approximants; `HkerD2` quantifies over all minimal
  families + `ker`; `HmultD2` uses multiplicity data; gated forms use
  s.o.p./Noether data), the SPEC mentions only `H_gr` and rational
  constants: no polynomials, no family, no `ker`, no multiplicity, no
  s.o.p. It is the narrowest phrasing of `d = 2` strength in tree.
* Minimality: the §3 iff shows the SPEC is exactly the slice in
  sequence-only vocabulary — i.e. it is the weakest sufficient
  condition. Any analytic condition implying the slice (given the
  unconditional bank) implies non-stabilization, so no strictly weaker
  analytic remainder exists in this vocabulary.
* Non-circularity: nothing assumes `hwit`, `hmult`, `hdimEq`,
  `ker = ⊥`, gated data, `hle`, or any growth fact beyond the cited
  unconditional suppliers (`hF`, the R-2d′ bridge, the cumsum bridge,
  HighAttack §1) to prove the §§1–4 masters; the only undischarged
  inputs are the SPEC itself (and the D2H-SPEC shape in the
  coordination bridge, which is not consumed elsewhere).

why unconditional is OUT of scope (not attempted): the slice is
`ker = ⊥` strength (GX §2 iff + ReesClose), and
unconditional `d = 2` below `ker = ⊥` is settled OUT of reach.
The §4 witnesses make the obstruction concrete at the analytic level:
the bank's finite pins `H(0) = 1`, `H(1) = 2` (and likewise any finite
prefix) are consistent with both stabilization and growth, so the tail
is genuinely undetermined by all unconditional data banked here. A
direct proof would need regular-local-ring theory absent from Mathlib
v4.34.0 (`R_Q` regular of dimension 2 implies `gr(R_Q)` polynomial).

verdict (audited): partial. `HdimEqD2AtAss` is not closed
unconditionally; it is scoped to exactly the §4 SPEC, the narrowest
(and weakest-sufficient) analytic remainder in tree, with the
quotient-Hilbert → `H_gr` → cumsum bank (§§1–2), the Newton-core iff
web (§3), the D2H compatibility bridge, and the HS-face iff proved.

consumers: any proof of the SPEC discharges the slice,
`HgrExactD2`, `HkerD2`, `HmultD2`, and per-prime `hsExactD2` by single
`exact`s; any future D2H landing of `HhleD2AtAss` discharges the slice
via `dimEqAttack_hdimEqD2_of_hleD2`; any future per-prime attack (HS or
gr face) composes via §§3–4.
-/

#print axioms dimEqAttack_grHilbert_zero_eq_one
#print axioms dimEqAttack_grHilbert_one_eq_two
#print axioms dimEqAttack_grHilbert01_of_embdim
#print axioms dimEqAttack_domainHilbert_d2_zero
#print axioms dimEqAttack_domainHilbert_d2_one
#print axioms dimEqAttack_hsSamuel_zero_eq_one
#print axioms dimEqAttack_hsSamuel_one_eq_three
#print axioms dimEqAttack_hsSamuel01_of_embdim
#print axioms dimEqAttack_dimEq_piece_iff_nonstab
#print axioms dimEqAttack_grPiece_iff_nonstab
#print axioms dimEqAttack_hne_iff_piece
#print axioms dimEqAttack_hdimEqD2_of_nonstab
#print axioms dimEqAttack_nonstab_of_hdimEqD2
#print axioms dimEqAttack_hdimEqD2_iff_nonstab
#print axioms dimEqAttack_grExactD2_of_nonstab
#print axioms dimEqAttack_hkerD2_of_nonstab
#print axioms dimEqAttack_hmultD2_of_nonstab
#print axioms dimEqAttack_hsExactD2_of_nonstab
#print axioms dimEqAttack_hdimEqD2_of_hleD2
#print axioms dimEqAttack_hsExact_iff_dimEq_piece
#print axioms dimEqAttack_pins_consistent_with_stabilization
#print axioms dimEqAttack_pins_consistent_with_growth

end DimEqAttackDimTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
