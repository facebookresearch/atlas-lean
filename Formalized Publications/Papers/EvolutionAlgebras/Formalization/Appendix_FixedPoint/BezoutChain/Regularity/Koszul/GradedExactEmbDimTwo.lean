/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack

/-!
# Gr-side HS exact closure at embdim 2
FiniteDimDischarge the gr-side remainder of Hilbert–Samuel exactness at embdim
exactly 2, building on the closed `hpiece` (HSDegree §5, L2: never
reproved, only consumed). The HSDegree-§3 master
`hsBridge_hs_exact_of_gr_exact_unconditional` is conditional-exact on
gr-side data `[hF, hne]` alone; this file closes each input in the exact
shapes HighAttack §4 (`HgrExactD2AtAss`, `HhsDegLowerD2AtAss`,
`HhpieceD2AtAss`) and HSAssemble consumers need.

## What this file proves

* (§1) `hF` unconditional, per-family (`grExact_hF_of_family`) and
  per-prime at embdim 2 (`grExact_hF_d2`): Hilbert–Serre
  `hsQuotHilbert_isPolyGrowth` transported along the R-2d′ bridge
  `ker_assemble_grHilbert_eq_hsQuot`. This closes the
  `singleDrop_grHilbert_isPolyGrowth` gap cited (but never proved) in
  HSDegree §3 and WitKerCrux.
* (§2) `hne` conditional-exact: on the narrowest analytic remainder
  `hmult` (`grExact_hne_of_hmult`, via `kwit_not_vanishing_unshifted` +
  the R-2d′ bridge), and on `ker = ⊥` (`grExact_hne_of_ker_eq_bot`,
  via `kwit_hmult_of_ker_eq_bot`). Exactness: `hmult ⟺ ker = ⊥` by
  `kwit_hmult_iff_ker_eq_bot`, so no narrower conditioning exists.
* (§3) `HgrExactD2AtAss` conditional-exact on `[HkerD2AtAss]`
  (`grExact_grExactD2_of_hkerD2`): the grlift sop family identifies
  `d` with `2`, `hF` is §1, `hne` is §2.
* (§4) `HhpieceD2AtAss` unconditional (`grExact_hhpieceD2`): one-line
  `hpiece_maximal` application in the HighAttack-§4 shape.
* (§5) HS exact degree 2 per prime: conditional-exact on `[hgrExact]`
  alone (`grExact_hsExactD2_of_grExact`, upgrading
  `highAttack_hsExactD2_of_hpiece_grExact` by dropping `hpiece`), and
  end-to-end conditional-exact on `[HkerD2AtAss]`
  (`grExact_hsExactD2_of_hkerD2`).
* (§6) `HhsDegLowerD2AtAss` unconditional (`grExact_hsDegLowerD2`):
  HS exact degree 2 recovers gr-side nonvanishing (cumsum converse
  `grExact_hne_of_hsExactD2`, pure Newton calculus), which with §1
  growth gives the exact-degree reading
  (`hsAssemble_hdimEq_of_not_vanishing`); the KerAssemble track turns
  it into `ker = ⊥` on the grlift family, and the §17 collapse into
  `hle`. Plus the HS-route integration check `HkerD2 → HwitD2`
  (`grExact_hwitD2_of_hkerD2_viaHS`).
* (§7, doc-only) Remainder register: the exact residual is `[HkerD2]`
  (equivalently `[hmult]` per family) — the crux itself, not an
  artifact of this file.

## Status

unconditional: `grExact_hF_of_family`, `grExact_hF_d2`,
`grExact_hhpieceD2`, `grExact_seqDiff_two_hsCumsum`,
`grExact_hne_of_hsExactD2`, `grExact_hsDegLowerD2`.
conditional-exact: `grExact_hne_of_hmult` on `[hmult]`,
`grExact_hne_of_ker_eq_bot` on `[hker]`,
`grExact_grExactD2_of_hkerD2` on `[HkerD2]`,
`grExact_hsExactD2_of_grExact` on `[hgrExact]`,
`grExact_hsExactD2_of_hkerD2` on `[HkerD2]`,
`grExact_hwitD2_of_hkerD2_viaHS` on `[HkerD2]`.

## References

Project (read-only):
* `Regularity/Multiplicity/HilbertSamuelDegree.lean` (§3 bridge masters, §5 `hpiece`
  discharge: `hpiece_maximal`, `hsBridge_hs_eq_cumsum_unconditional`,
  `hsBridge_hs_exact_of_gr_exact_unconditional`).
* `Regularity/Multiplicity/HilbertSerre.lean` (`hsQuotHilbert_isPolyGrowth`).
* `Regularity/Multiplicity/KernelAssembly.lean` (`ker_assemble_grHilbert_eq_hsQuot`,
  `ker_assemble_hsQuot_eq_multQuot`, `ker_assemble_ker_homogeneous`,
  `ker_assemble_ker_eq_bot`).
* `Regularity/HomologicalDepth/HilbertWitnessNarrowing.lean` (`kwit_hmult_of_ker_eq_bot`,
  `kwit_not_vanishing_unshifted`, `kwit_hmult_iff_ker_eq_bot`).
* `Regularity/Koszul/GradedLift.lean` (`grlift_sop_exists`).
* `Regularity/Koszul/FiltrationStability.lean`
  (`isNoetherianRing_atPrime` instance).
* `Regularity/Multiplicity/WitnessHighAttack.lean` (§4 SPECs + masters).
* `Regularity/HomologicalDepth/WitnessKernelDimTwo.lean` (`HkerD2AtAss`, `HwitD2AtAss`).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedExactEmbDimTwo

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack

/-! ## §1. `hF`: gr-side growth upper bound, unconditional -/

/-- Gr-side growth upper bound, per-family form: `H_gr` has `IsPolyGrowth`
bound `d - 1` for any spanning family (Hilbert–Serre
`hsQuotHilbert_isPolyGrowth` transported along the R-2d′ bridge
`ker_assemble_grHilbert_eq_hsQuot`). This closes the
`singleDrop_grHilbert_isPolyGrowth` gap cited (but never proved) in
HSDegree §3 and WitKerCrux.
-/
theorem grExact_hF_of_family {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    IsPolyGrowth (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      (d - 1) := by
  have hQ := hsQuotHilbert_isPolyGrowth
    (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
    (RingHom.ker (polySurjResidue Q d g hgen))
    (ker_assemble_ker_homogeneous Q d g hgen)
  have hfun : (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      = (fun n => ((hsQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
        (RingHom.ker (polySurjResidue Q d g hgen)) n : ℕ) : ℚ)) := by
    funext n
    rw [ker_assemble_grHilbert_eq_hsQuot Q d g hgen n]
  rw [hfun]
  exact hQ

/-- Gr-side growth upper bound at embdim exactly 2, per-prime form: the
grlift sop family identifies `d` with `2`.
-/
theorem grExact_hF_d2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    IsPolyGrowth (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      1 := by
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  exact grExact_hF_of_family Q 2 g hgen

/-! ## §2. `hne`: gr-side nonvanishing, conditional-exact -/

/-- Gr-side nonvanishing from the R-2c′ analytic remainder `hmult`
(shifted `multQuotHilbert` nonvanishing): unshift
(`kwit_not_vanishing_unshifted`) then transport along the R-2d′ bridge.
This is the narrowest analytic conditioning for `hne`
(`hmult ⟺ ker = ⊥` by `kwit_hmult_iff_ker_eq_bot`).

Conditional on exactly `[hmult]`. -/
theorem grExact_hne_of_hmult {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmult : ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) :
    ¬ seqDiff (d - 1) (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hfunG : (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      = (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
        (RingHom.ker (polySurjResidue Q d g hgen)) n : ℕ) : ℚ)) := by
    funext n
    rw [ker_assemble_grHilbert_eq_hsQuot Q d g hgen n,
      ker_assemble_hsQuot_eq_multQuot]
  rw [hfunG]
  exact kwit_not_vanishing_unshifted
    (F := fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
      (RingHom.ker (polySurjResidue Q d g hgen)) n : ℕ) : ℚ))
    (e := d - 1) hmult

/-- Gr-side nonvanishing from `ker = ⊥` (domain case
`kwit_hmult_of_ker_eq_bot`, unshifted + bridged).

Conditional on exactly `[hker]`. -/
theorem grExact_hne_of_ker_eq_bot {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : 1 ≤ d)
    (hker : RingHom.ker (polySurjResidue Q d g hgen) = ⊥) :
    ¬ seqDiff (d - 1) (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
  grExact_hne_of_hmult Q d g hgen
    (kwit_hmult_of_ker_eq_bot Q d g hgen hd hker)

/-! ## §3. `HgrExactD2AtAss` from the crux form -/

/-- `HgrExactD2AtAss` from the `d = 2` crux form `HkerD2AtAss`: per `Q`
the grlift sop family identifies `d` with `2`; `hF` is §1, `hne` is §2
from `ker = ⊥` on that family.

Conditional on exactly `[hker]`. -/
theorem grExact_grExactD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HgrExactD2AtAss m K J := by
  intro Q _ hQ hemb
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hkerQ : RingHom.ker (polySurjResidue Q 2 g hgen) = ⊥ :=
    hker Q hQ g hgen hemb
  refine ⟨?hF, ?hne⟩
  · exact grExact_hF_of_family Q 2 g hgen
  · exact grExact_hne_of_ker_eq_bot Q 2 g hgen (by omega) hkerQ

/-! ## §4. `HhpieceD2AtAss`, unconditional -/

/-- The `hpiece` cross-ring identification at embdim 2, discharged
unconditionally (`hpiece_maximal`, L2): the exact HighAttack-§4
`HhpieceD2AtAss` shape.
-/
theorem grExact_hhpieceD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhpieceD2AtAss m K J := by
  intro Q _ _hQ _hemb i
  exact hpiece_maximal i

/-! ## §5. HS exact degree 2 per prime -/

/-- Per-prime HS exact degree 2 from gr-exact data alone (`hpiece`
discharged): the `hsBridge` master with L2 supply. This upgrades
`highAttack_hsExactD2_of_hpiece_grExact` by dropping `hpiece`.

Conditional on exactly `[hgrExact]`. -/
theorem grExact_hsExactD2_of_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S := by
  obtain ⟨hF, hne⟩ := hgrExact Q hQ hemb
  exact hsBridge_hs_exact_of_gr_exact_unconditional hF hne

/-- HS exact degree 2 end-to-end from the crux form: `HkerD2 → HgrExactD2`
(§3) feeds the §5 master.

Conditional on exactly `[hker]`. -/
theorem grExact_hsExactD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  grExact_hsExactD2_of_grExact m K J
    (grExact_grExactD2_of_hkerD2 m K J hker) Q hQ hemb

/-! ## §6. `HhsDegLowerD2AtAss`, unconditional, + HS-route integration -/

/-- The second difference of a cumsum is the shifted first difference:
`Δ²χ = (ΔH) ∘ succ` (same rewrite chain as `hsCumsum_nonvanishing`).
-/
theorem grExact_seqDiff_two_hsCumsum (H : ℕ → ℚ) :
    seqDiff (1 + 1) (hsCumsum H) = fun n => seqDiff 1 H (n + 1) := by
  rw [seqDiff_succ', ← seqDiff_one, hsCumsum_seqDiff, seqDiff_comp_add]

/-- Cumsum converse at degree 2: HS exact degree 2 (identified with the
cumsum of `H_gr` by the unconditional bridge) recovers gr-side
nonvanishing. If `ΔH_gr =ᶠ 0`, then `Δ²HS =ᶠ 0` by the shift argument —
but `Δ²HS =ᶠ 2! * S.coeff 2 ≠ 0` since `natDegree S = 2`. Pure Newton
calculus, no dimension input.
-/
theorem grExact_hne_of_hsExactD2 {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hHS : ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S) :
    ¬ seqDiff 1 (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  obtain ⟨S, hSdeg, hSag⟩ := hHS
  have hbridge : (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
      = hsCumsum (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ)) :=
    hsBridge_hs_eq_cumsum_unconditional
  intro hvan
  have hvan2 : seqDiff (1 + 1)
        (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] (0 : ℕ → ℚ) := by
    have hSeq2 := grExact_seqDiff_two_hsCumsum (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
    rw [hbridge, hSeq2]
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hvan
    refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
    exact hN (m + 1) (by omega)
  have hconst : seqDiff (1 + 1)
        (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop]
        fun _ => (Nat.factorial (1 + 1) : ℚ) * S.coeff (1 + 1) :=
    seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun S (1 + 1) hSag
      (le_of_eq hSdeg)
  have hcontra : (fun _ => (Nat.factorial (1 + 1) : ℚ) * S.coeff (1 + 1))
      =ᶠ[Filter.atTop] (0 : ℕ → ℚ) := hconst.symm.trans hvan2
  have hcoeff : S.coeff (1 + 1) ≠ 0 := by
    have hSne : S ≠ 0 := by
      rintro rfl
      rw [Polynomial.natDegree_zero] at hSdeg
      omega
    have hlc : S.coeff (1 + 1) = S.leadingCoeff := by
      rw [← hSdeg, Polynomial.coeff_natDegree]
    rw [hlc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hSne
  have hfact : (Nat.factorial (1 + 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcontra
  have hNN := hN N le_rfl
  simp only [Pi.zero_apply] at hNN
  exact (mul_ne_zero hfact hcoeff) hNN

/-- The HS-degree-to-dimension residual at embdim 2, closed
unconditionally: HS exact degree 2 recovers gr-side nonvanishing (§6,
cumsum converse), which with §1 growth gives the exact-degree reading
(`hsAssemble_hdimEq_of_not_vanishing`); the KerAssemble track turns it
into `ker = ⊥` on the grlift family, and the §17 collapse into `hle`.
-/
theorem grExact_hsDegLowerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhsDegLowerD2AtAss m K J := by
  intro Q _ _hQ hemb hHS
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hF := grExact_hF_of_family Q 2 g hgen
  have hne := grExact_hne_of_hsExactD2 Q hHS
  have hdimEq := hsAssemble_hdimEq_of_not_vanishing hF hne
  have hker := ker_assemble_ker_eq_bot Q 2 g hgen le_rfl hdimEq
  exact mult_hle_gr_of_ker_eq_bot Q 2 g hgen hker

/-- `HwitD2AtAss` from `HkerD2AtAss` via the HS route (integration check):
`hpiece` (§4, unconditional) + `HgrExactD2` (§3, on `[hker]`) +
`HhsDegLowerD2` (§6, unconditional) feed the HighAttack-§4 master. This is
the HS-exact-closure end-to-end: every gr-side input the HS route needs is
now supplied.

Conditional on exactly `[hker]`. -/
theorem grExact_hwitD2_of_hkerD2_viaHS (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HwitD2AtAss m K J :=
  highAttack_hwitD2_of_hpiece_grExact_hsDeg m K J
    (grExact_hhpieceD2 m K J)
    (grExact_grExactD2_of_hkerD2 m K J hker)
    (grExact_hsDegLowerD2 m K J)

/-! ## §7. Remainder register (doc-only)

Exact residual of this file: `[HkerD2AtAss]` (equivalently, per family,
the analytic remainder `[hmult]` — the two are iff-equivalent by
`kwit_hmult_iff_ker_eq_bot`, so the §3/§5 conditioning is minimal). This
is the crux itself (`d = 2` slice of the High-at-Ge2 remainder), not an
artifact of this file: `hF` is unconditional (§1), `hpiece` is
unconditional (§4, L2 supply), the HS-degree step is
unconditional (§6), and `hne` is pinned to exactly `hmult` (§2).

What fell: `singleDrop_grHilbert_isPolyGrowth` (the §1 transport — cited
but never proved in HSDegree §3 / WitKerCrux), `HhpieceD2AtAss`,
`HhsDegLowerD2AtAss`, per-prime `hsExactD2` on `[hgrExact]` alone, and
the HS-route `HkerD2 → HwitD2` integration.

Nothing in this file assumes `hwit`, `hdimEq`, or any growth fact beyond
§1 to prove the §6 master; the only undischarged inputs are the crux
forms themselves (§§2–3, §5b).
-/

#print axioms grExact_hF_of_family
#print axioms grExact_hF_d2
#print axioms grExact_hne_of_hmult
#print axioms grExact_hne_of_ker_eq_bot
#print axioms grExact_grExactD2_of_hkerD2
#print axioms grExact_hhpieceD2
#print axioms grExact_hsExactD2_of_grExact
#print axioms grExact_hsExactD2_of_hkerD2
#print axioms grExact_seqDiff_two_hsCumsum
#print axioms grExact_hne_of_hsExactD2
#print axioms grExact_hsDegLowerD2
#print axioms grExact_hwitD2_of_hkerD2_viaHS

end GradedExactEmbDimTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
