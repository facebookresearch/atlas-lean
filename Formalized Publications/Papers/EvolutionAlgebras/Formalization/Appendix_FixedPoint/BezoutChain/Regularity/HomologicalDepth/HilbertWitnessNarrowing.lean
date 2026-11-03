/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly

/-!
# Hilbert-witness narrowing: `hwit` is top-difference nonvanishing (M4 prime mover)

Closes-or-narrows `hwit`, the R-2c′ remainder isolating the
`hle_gr → hdimEq → ker` chain (`mult_hmult_unconditional_of_witnessHyp`,
`mult_ker_eq_bot_unconditional_of_witnessHyp`, §17 witness corollaries):
`hwit` asks for `∃ Pwit : ℚ[X]` with `natDegree ≤ d - 1`, eventual agreement
with the shifted quotient Hilbert function `Hq`, and `coeff (d - 1) ≠ 0`.
Three of the four conjuncts land here unconditionally (given `1 ≤ d`):
Hilbert–Serre existence plus the domain comparison (`quot ≤ domain`) bounds
the degree via polynomial domination, and the shift is exact. The remaining
leading-coefficient content is exactly top-difference nonvanishing (`hmult`),
in both directions. Nothing here assumes `ker = ⊥`, `hle_gr`, `hdimEq`, or
any dimension equality.

## §0. Step-0 inventory of M4's remaining obligations (verified by reading)

* `hF` (domain growth bound): closed. `hsAssemble_hF` §13
  (`GradedSurjectionInjective.lean`, via `hsAssemble_hF_of_starsBars`:649 and
  `hsAssemble_domainHilbert_eq_choose`:1307) proves
  `IsPolyGrowth (domainHilbert κ d) (d - 1)` from `1 ≤ d` alone —
  unconditional (conditional-form on application data). Artinian form
  `hsAssemble_hF_one`:1395. Consumed below (`kwit_deg_le_of_quot_agreement`)
  and by SingleDrop §7 / Multiplicity §9.
* `hdrop` (the drop shape): rescoped Route-B, closed on the new track.
  The original fixed-`Hq` shift-1 `hdrop` (HSAssemble §6) is abandoned
  (its `hses + hFq` kill `hdimEq` for the same `Hq`, and the shift-1 SES
  only matches degree-1 `y`). Route-B (R3′) replaces it with the per-`(y, t)` shift-`t`
  step: `singleDrop_hSES` (§3), `singleDrop_hcomp_concrete` (§9b),
  `singleDrop_hdom` (§10) — all unconditional — packaged as
  `ker_assemble_hstep` (`KernelAssembly.lean`, unconditional) with
  `hag_gr` discharged by Hilbert–Serre (`ker_assemble_hag_gr`:196,
  unconditional). The old-`hdrop` masters (`hsAssemble_ker_eq_bot_of_mult`,
  Multiplicity §14/§17) remain valid conditional statements but are no
  longer on the critical path: `ker_assemble_ker_eq_bot` (:283) needs only
  `hdimEq`. This file feeds `hdimEq` from `hmult` (§4).
* `hd_pos` (`1 < d`): application data, not a proof obligation. Binds the
  §6 masters (`GradedSurjectionInjective.lean`), the `_of_dim` masters (:505),
  the `_of_mult` masters (:747), the `_of_principal` masters (:1047), and
  the Multiplicity witness masters (`MultiplicityNonvanishing.lean, 1928`).
  R4 (§14) closes `d = 0` separately (`hsAssemble_ker_eq_bot_zero`:1419,
  unconditional). KerAssemble uses `2 ≤ d` instead (:287). This file takes
  `1 ≤ d` (weak witness) / `2 ≤ d` (kernel master) the same way.

## Sections

* (§1) Generic Newton/poly bridges (unconditional): domination forces a
  degree bound (`kwit_deg_le_of_le_domain`), nonvanishing forces a nonzero
  top coefficient (`kwit_coeff_ne_of_not_vanishing`), shifted nonvanishing
  gives unshifted nonvanishing (`kwit_not_vanishing_unshifted`).
* (§2) The weak witness (unconditional given `1 ≤ d`): Hilbert–Serre
  existence plus the §1 degree bound give `IsPolyGrowth` of the quotient
  Hilbert function, unshifted (`kwit_isPolyGrowth_quot`) and shifted
  (`kwit_hFq` — exactly `hwit` minus the leading coefficient).
* (§3) The narrowing (unconditional conditional-form): `hwit → hmult`
  (`kwit_hmult_of_hwit`), `hmult → hwit` (`kwit_hwit_of_hmult`), and the
  iff (`kwit_hwit_iff_hmult`).
* (§4) Masters (conditional-exact on `[hmult]`): the `gr`-side witness
  triple (`kwit_grWitness_of_hmult`), `hdimEq` in exact KerAssemble shape
  (`kwit_hdimEq_gr_of_hmult`), `ker = ⊥` needing nothing else
  (`kwit_ker_eq_bot_of_hmult`), the Multiplicity-track `hle_gr`
  (`kwit_hle_gr_of_hmult`), and the exactness collapse
  (`kwit_hmult_of_ker_eq_bot`, `kwit_hmult_iff_ker_eq_bot`).
* (§5) Residual register (doc-only): `hmult` is the exact minimal remainder.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Order/Filter/AtTopBot/Basic.lean`: `eventually_atTop`
  (used as `Filter.eventually_atTop.mp/mpr`).

Project (read-only):
* `Regularity/Multiplicity/NewtonDifferences.lean` (`seqDiff`:123, `evalFun`:329,
  `IsPolyGrowth`:465, `seqDiff_comp_add`:228,
  `seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun`:433).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean` (`hsAssemble_domainHilbert`:642,
  `hsAssemble_hF_of_starsBars`:649, `isPolyGrowth_comp_add`:619,
  `hsAssemble_domainHilbert_eq_choose`:1307, `hsAssemble_hF`:1323).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean` (`multQuotHilbert`:175,
  `mult_quot_le_domain`:220, `mult_hmult`:338,
  `mult_r2b_universal_false`:647, `mult_hmult_of_ker_eq_bot`:757,
  `mult_hmult_unconditional_of_witnessHyp`:1571,
  `mult_ker_eq_bot_unconditional_of_witnessHyp`:1591,
  `mult_hle_gr_iff_ker_eq_bot`:1905, `mult_hle_gr_of_witnessHyp`:1924).
* `Regularity/Multiplicity/HilbertSerre.lean` (`hsQuotHilbert_eventuallyEq`:1428,
  `hsQuotHilbert_hag_gr`:1570).
* `Regularity/Multiplicity/SingleDropRegularity.lean` (`singleDrop_grHilbert`:1094,
  `singleDrop_hdom`:1556, `singleDrop_hdimEq_of_grWitness`:1777).
* `Regularity/Multiplicity/KernelAssembly.lean` (`ker_assemble_ker_homogeneous`:94,
  `ker_assemble_hsQuot_eq_multQuot`:107,
  `ker_assemble_grHilbert_eq_hsQuot`:174, `ker_assemble_ker_eq_bot`:283).

## Status

* §1: unconditional.
* §2: unconditional (conditional-form on `1 ≤ d`, application data).
* §3: unconditional (conditional-form on the stated hypotheses).
* §4: conditional-exact on `[hmult]` (`kwit_grWitness_of_hmult`,
  `kwit_hdimEq_gr_of_hmult`, `kwit_ker_eq_bot_of_hmult`,
  `kwit_hmult_iff_ker_eq_bot`); conditional-exact on
  `[hmult, hF, hdrop, hd_pos]` (`kwit_hle_gr_of_hmult`).
* Overall: partial (`hmult` open — the exact minimal remainder).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HilbertWitnessNarrowing

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly

/-! ## §1. Generic Newton/poly bridges -/

/-- Domination forces a degree bound: a polynomial eventually agreeing with
a pointwise-smaller sequence has degree at most the growth degree of the
bigger one (via `singleDrop_hdom` at `e + 2`, so `(e + 2) - 2 = e`).
-/
theorem kwit_deg_le_of_le_domain {Fq Fd : ℕ → ℕ} {e : ℕ} (Pw : ℚ[X])
    (hag : (fun n => ((Fq n : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Pw)
    (hle : ∀ n, Fq n ≤ Fd n)
    (hdom : IsPolyGrowth (fun n => ((Fd n : ℕ) : ℚ)) e) :
    Pw.natDegree ≤ e := by
  obtain ⟨Pdom, hDle, hDag⟩ := hdom
  have hQle : Pdom.natDegree ≤ (e + 2) - 2 := by omega
  have hP : ∀ᶠ (n : ℕ) in Filter.atTop, 0 ≤ Pw.eval (n : ℚ) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hag
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hnn : (0 : ℚ) ≤ ((Fq n : ℕ) : ℚ) := Nat.cast_nonneg _
    have hn' : ((Fq n : ℕ) : ℚ) = evalFun Pw n := hN n hn
    rw [hn'] at hnn
    exact hnn
  have hleE : ∀ᶠ (n : ℕ) in Filter.atTop,
      Pw.eval (n : ℚ) ≤ Pdom.eval (n : ℚ) := by
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hag
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hDag
    refine Filter.eventually_atTop.mpr ⟨max N1 N2, fun n hn => ?_⟩
    have hn1 : ((Fq n : ℕ) : ℚ) = evalFun Pw n :=
      hN1 n (le_trans (Nat.le_max_left _ _) hn)
    have hn2 : ((Fd n : ℕ) : ℚ) = evalFun Pdom n :=
      hN2 n (le_trans (Nat.le_max_right _ _) hn)
    have hpt : ((Fq n : ℕ) : ℚ) ≤ ((Fd n : ℕ) : ℚ) :=
      Nat.cast_le.mpr (hle n)
    rw [hn1, hn2] at hpt
    exact hpt
  have hbound := singleDrop_hdom (e + 2) Pw Pdom hP hleE hQle
  omega

/-- Nonvanishing forces a nonzero top coefficient: the converse of
`mult_hmult_of_coeff_ne_zero` — the `e`-th difference is eventually the
constant `e! * coeff`, so vanishing would follow from `coeff = 0`.
-/
theorem kwit_coeff_ne_of_not_vanishing {F : ℕ → ℚ} {e : ℕ} (P : ℚ[X])
    (hle : P.natDegree ≤ e) (hag : F =ᶠ[Filter.atTop] evalFun P)
    (hmult : ¬ seqDiff e F =ᶠ[Filter.atTop] 0) :
    P.coeff e ≠ 0 := by
  intro hzero
  apply hmult
  have hconst := seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun P e hag hle
  rw [hzero, mul_zero] at hconst
  exact hconst

/-- Shifted nonvanishing gives unshifted nonvanishing: differences commute
with the shift (`seqDiff_comp_add`), so an eventually-zero unshifted
difference would shift to an eventually-zero shifted one.
-/
theorem kwit_not_vanishing_unshifted {F : ℕ → ℚ} {e : ℕ}
    (hmult : ¬ seqDiff e (fun n => F (n + 1)) =ᶠ[Filter.atTop] 0) :
    ¬ seqDiff e F =ᶠ[Filter.atTop] 0 := by
  intro hvan
  apply hmult
  have hshift : seqDiff e (fun n => F (n + 1))
      = fun m => seqDiff e F (m + 1) :=
    seqDiff_comp_add F 1 e
  rw [hshift]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hvan
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
  exact hN (m + 1) (by omega)

/-! ## §2. The weak witness: existence plus degree bound, unconditionally -/

section WeakWitness

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The degree-bound half of `hwit`, unconditionally: any polynomial
eventually agreeing with the (unshifted) quotient Hilbert function has
degree `≤ d - 1` (quotient `≤` domain pointwise, domain has growth
`d - 1` by `hsAssemble_hF`).
-/
theorem kwit_deg_le_of_quot_agreement (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d) (Pw : ℚ[X])
    (hag : (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pw) :
    Pw.natDegree ≤ d - 1 :=
  kwit_deg_le_of_le_domain (Fq := fun n => multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) n)
    (Fd := fun n => hsAssemble_domainHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d n)
    (e := d - 1) Pw hag
    (fun n => mult_quot_le_domain
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) n)
    (hsAssemble_hF (IsLocalRing.ResidueField (Localization.AtPrime P)) d hd)

/-- Hilbert–Serre existence plus the §1 degree bound: the unshifted
quotient Hilbert function has polynomial growth `≤ d - 1`.
-/
theorem kwit_isPolyGrowth_quot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d) :
    IsPolyGrowth (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ)) (d - 1) := by
  obtain ⟨Pgr, hPgr⟩ := hsQuotHilbert_hag_gr
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d
    (RingHom.ker (polySurjResidue P d g hgen))
    (ker_assemble_ker_homogeneous P d g hgen)
  have hfun : (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ))
      = (fun n => ((hsQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ)) := by
    funext n
    rw [ker_assemble_hsQuot_eq_multQuot]
  have hag : (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr := by
    rw [hfun]
    exact hPgr
  exact ⟨Pgr, kwit_deg_le_of_quot_agreement P d g hgen hd Pgr hag, hag⟩

/-- The shifted weak witness: exactly `hwit` minus the leading
coefficient (`isPolyGrowth_comp_add` shifts `kwit_isPolyGrowth_quot`).
-/
theorem kwit_hFq (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d) :
    IsPolyGrowth (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      (d - 1) := by
  obtain ⟨Pwit, hle, hag⟩ :=
    isPolyGrowth_comp_add (kwit_isPolyGrowth_quot P d g hgen hd) 1
  exact ⟨Pwit, hle, hag⟩

end WeakWitness

/-! ## §3. The narrowing: `hwit` is top-difference nonvanishing -/

section Narrowing

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `hwit → hmult`: a Hilbert witness forces nonvanishing
(`mult_hmult`).
-/
theorem kwit_hmult_of_hwit (d : ℕ)
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

/-- `hmult → hwit`: nonvanishing plus the unconditional weak witness
(`kwit_hFq`) recovers the leading coefficient
(`kwit_coeff_ne_of_not_vanishing`).
-/
theorem kwit_hwit_of_hmult (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmult : ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) :
    ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0 := by
  obtain ⟨Pwit, hle, hag⟩ := kwit_hFq P d g hgen hd
  exact ⟨Pwit, hle, hag, kwit_coeff_ne_of_not_vanishing Pwit hle hag hmult⟩

/-- The narrowing as an iff: `hwit ↔ hmult` given `1 ≤ d`.
-/
theorem kwit_hwit_iff_hmult (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d) :
    (∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0) ↔
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
  ⟨kwit_hmult_of_hwit P d g hgen, kwit_hwit_of_hmult P d g hgen hd⟩

end Narrowing

/-! ## §4. Masters: the chain from `hmult` alone -/

section Masters

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The `gr`-side witness triple from `hmult`, in the exact shape
`singleDrop_hdimEq_of_grWitness` consumes: Hilbert–Serre existence plus
the §1 degree bound on the unshifted quotient function, transported to
`singleDrop_grHilbert` along the R-2d′ bridge, with the leading
coefficient from shifted nonvanishing via `kwit_not_vanishing_unshifted`.

Conditional on exactly `[hmult]` (+ `1 ≤ d`). -/
theorem kwit_grWitness_of_hmult (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmult : ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) :
    ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0 := by
  obtain ⟨Pgr, hPgr⟩ := hsQuotHilbert_hag_gr
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d
    (RingHom.ker (polySurjResidue P d g hgen))
    (ker_assemble_ker_homogeneous P d g hgen)
  have hfunQ : (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ))
      = (fun n => ((hsQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ)) := by
    funext n
    rw [ker_assemble_hsQuot_eq_multQuot]
  have hagQ : (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr := by
    rw [hfunQ]
    exact hPgr
  have hle := kwit_deg_le_of_quot_agreement P d g hgen hd Pgr hagQ
  have hfunG : (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      = (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ)) := by
    funext n
    rw [ker_assemble_grHilbert_eq_hsQuot P d g hgen n,
      ker_assemble_hsQuot_eq_multQuot]
  have hagW : (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr := by
    rw [hfunG]
    exact hagQ
  have hmultU : ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
    kwit_not_vanishing_unshifted (F := fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ))
      (e := d - 1) hmult
  have hc := kwit_coeff_ne_of_not_vanishing Pgr hle hagQ hmultU
  exact ⟨Pgr, hle, hagW, hc⟩

/-- `hdimEq` in exact KerAssemble-hyp shape from `hmult` alone (the prime
mover feed: no `hle_gr`, no `hub`, no dimension input).

Conditional on exactly `[hmult]` (+ `1 ≤ d`). -/
theorem kwit_hdimEq_gr_of_hmult (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmult : ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) :
    ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1 := by
  obtain ⟨Pwit, hle, hagW, hc⟩ := kwit_grWitness_of_hmult P d g hgen hd hmult
  exact singleDrop_hdimEq_of_grWitness P d Pwit hle hagW hc

/-- `ker = ⊥` from `hmult` alone: the KerAssemble track needs no `hF`,
no `hdrop`, no dimension input — `hmult` supplies `hdimEq`, the R3′ drop
does the rest.

Conditional on exactly `[hmult]` (+ `2 ≤ d`). -/
theorem kwit_ker_eq_bot_of_hmult (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmult : ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  have hdimEq := kwit_hdimEq_gr_of_hmult P d g hgen (by omega) hmult
  exact ker_assemble_ker_eq_bot P d g hgen hd hdimEq

/-- The Multiplicity-track narrowing: `hle_gr` from `hmult` (via §17's
`mult_hle_gr_of_witnessHyp`), replacing the `hwit` existential with the
single analytic remainder.

Conditional on exactly `[hmult, hF, hdrop, hd_pos]`. -/
theorem kwit_hle_gr_of_hmult (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H : ℕ → ℕ) (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hmult : ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0)
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
  have hwit := kwit_hwit_of_hmult P d g hgen (by omega) hmult
  exact mult_hle_gr_of_witnessHyp P d g hgen H hd_pos hF hwit hdrop

/-- Exactness converse: `ker = ⊥` gives `hmult` (quotient is domain,
`mult_hmult_of_ker_eq_bot`).
-/
theorem kwit_hmult_of_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  rw [hker]
  exact mult_hmult_of_ker_eq_bot
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d hd

/-- Collapse: `hmult` holds iff `ker = ⊥` — the remainder is exact
(nothing strictly weaker than the goal implies it, nothing stronger is
needed for it).
-/
theorem kwit_hmult_iff_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d) :
    (¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) ↔
      RingHom.ker (polySurjResidue P d g hgen) = ⊥ :=
  ⟨kwit_ker_eq_bot_of_hmult P d g hgen hd,
    kwit_hmult_of_ker_eq_bot P d g hgen (by omega)⟩

end Masters

/-! ## §5. Residual register (doc-only)

Minimal non-circular remainder (verbatim): `hmult`, i.e.
`¬ seqDiff (d - 1) (fun n => ((multQuotHilbert κ d ker (n + 1): ℕ): ℚ))
=ᶠ[atTop] 0` for `κ = IsLocalRing.ResidueField R_P` and
`ker = RingHom.ker (polySurjResidue P d g hgen)`.

Why `hmult` cannot be closed here (all machine-checked or cited):

* An unconditional proof is impossible in the current context: for a
  zero-padded spanning family the quotient has dimension `< d`, so the
  top difference vanishes. The padding obstruction is machine-checked at
  the dimension level by `mult_r2b_universal_false`
  (`MultiplicityNonvanishing.lean`): R-2b-as-stated is false, and the true
  residual carries the minimality hypothesis
  `hmin : d ≤ spanFinrank 𝔪` (`mult_ringKrullDim_atPrime_eq_of_minimal`
  :603, to be discharged by file 6's construction of `g`).
* Given `hmin`, closing `hmult` needs Hilbert–Samuel dimension theory
  (dimension `d` forces a nonzero degree-`d - 1` leading coefficient),
  which is absent from Mathlib at the pinned toolchain (no catenary,
  system-of-parameters, Hilbert–Samuel, or associated-graded dimension
  files under `Mathlib/RingTheory/`).
* The remainder is exact, not just sufficient: `kwit_hmult_iff_ker_eq_bot`
  shows `hmult ↔ ker = ⊥` (given `2 ≤ d`), so no weakening below the
  goal's own strength can discharge it, and no circular hypothesis
  (`ker = ⊥`, `hle_gr`, `hdimEq`, dimension equalities) was assumed
  anywhere in §§1–4.

Consumers: `kwit_hdimEq_gr_of_hmult` discharges the `hdimEq` hypothesis of
`ker_assemble_ker_eq_bot` on `[hmult]`; `kwit_ker_eq_bot_of_hmult`
discharges the `hker⊥` hypothesis of `grlift_r2_exact` on `[hmult]`;
`kwit_hle_gr_of_hmult` narrows the §17 Multiplicity-track corollaries to
`[hmult, hF, hdrop, hd_pos]`.
-/

#print axioms kwit_deg_le_of_le_domain
#print axioms kwit_coeff_ne_of_not_vanishing
#print axioms kwit_not_vanishing_unshifted
#print axioms kwit_deg_le_of_quot_agreement
#print axioms kwit_isPolyGrowth_quot
#print axioms kwit_hFq
#print axioms kwit_hmult_of_hwit
#print axioms kwit_hwit_of_hmult
#print axioms kwit_hwit_iff_hmult
#print axioms kwit_grWitness_of_hmult
#print axioms kwit_hdimEq_gr_of_hmult
#print axioms kwit_ker_eq_bot_of_hmult
#print axioms kwit_hle_gr_of_hmult
#print axioms kwit_hmult_of_ker_eq_bot
#print axioms kwit_hmult_iff_ker_eq_bot

end HilbertWitnessNarrowing
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HilbertWitnessNarrowing

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework

/-! ## §6. `hmult` from minimality (crux lane)

Proves `hmult` (top-difference nonvanishing of the shifted quotient
Hilbert function) from the minimality hypothesis
`hmin : d ≤ spanFinrank 𝔪`, narrowed to the exact homogeneous-relations
residual `KwitNoHomRel`. The universal form (no `hmin`) is false:
zero-padding raises the demanded difference order `d - 1` above the
true growth degree (cf. `mult_r2b_universal_false` at the dimension
level), so `hmin` is essential everywhere below — it is used via the
dimension equation `dim R_P = d`.

* Minimality infrastructure (unconditional conditional-form):
  `kwit_spanFinrank_eq_of_minimal` (`d = spanFinrank 𝔪` from spanning
  plus `hmin`).
* Length lower bound (conditional-exact on `[hmin]`):
  `kwit_quotHilbert_ne_zero_of_minimal` — no quotient Hilbert value
  vanishes. Vanishing at any degree would kill a graded piece, forcing
  `𝔪ⁿ = 𝔪ⁿ⁺¹`, hence `𝔪ⁿ = ⊥` by Nakayama, hence every prime maximal,
  hence `dim R_P = 0`, contradicting `dim R_P = d ≥ 1`. The vanishing
  transfers from the mult-side quotient to `grPiece` along the R-2d′
  equivs (`multQuotKerTransport`, `multDegQuotEquiv`) via
  `kwit_subsingleton_of_surjective`.
* Dimension one (conditional-exact on `[hmin]`):
  `kwit_hmult_of_minimal_one` — `hmult` for `d = 1`, since the `0`-th
  difference is the function itself.
* Master (conditional-exact on `[hmin, KwitNoHomRel]`):
  `kwit_hmult_of_minimal` — homogeneous chase: every `p ∈ ker` is a sum
  of homogeneous components in `ker`; the degree-0 component would be a
  unit killing `Hq 0` (ruled out by the lower bound, where `hmin` is
  essential); components of degree `≥ 1` vanish by the residual. Hence
  `ker = ⊥`, hence `hmult`.
* Exactness: `kwit_hmult_iff_noHomRel_of_minimal` — given `hmin`
  (+ `2 ≤ d`), `hmult ↔ KwitNoHomRel`, so the residual is minimal, not
  just sufficient. This subsumes the §5 `hmult` register on `[hmin]`.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/Finiteness/Nakayama.lean`:
  `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`.
* `RingTheory/KrullDimension/Basic.lean`: `Ring.KrullDimLE.mk₀`.
* `RingTheory/KrullDimension/Zero.lean`:
  `ringKrullDimZero_iff_ringKrullDim_eq_zero`.
* `RingTheory/Length.lean,94`:
  `Module.length_eq_zero_iff`, `Module.length_ne_top_iff`.
* `RingTheory/Ideal/Prime.lean`: `IsPrime.mem_of_pow_mem`.
* `RingTheory/MvPolynomial/Homogeneous.lean,537,560`:
  `totalDegree_zero_iff_isHomogeneous`,
  `homogeneousComponent_isHomogeneous`, `sum_homogeneousComponent`.
* `Algebra/MvPolynomial/Degrees.lean`:
  `totalDegree_eq_zero_iff_eq_C`.
* `RingTheory/Ideal/Operations.lean,289`:
  `Ideal.smul_eq_mul`, `Ideal.mul_le_right`.
* `RingTheory/LocalRing/MaximalIdeal/Basic.lean,36`:
  `mem_maximalIdeal`, `maximalIdeal.isMaximal`.

Project (read-only):
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean` (`mult_isFiniteLength_quotPiece`
  :199, `mult_spanFinrank_maximalIdeal_atPrime_le`:477,
  `mult_ringKrullDim_atPrime_eq_of_minimal`:603, `multDegQuotEquiv`
  :1192, `multQuotKerTransport`:1262).
* `Regularity/Multiplicity/NewtonDifferences.lean` (`seqDiff_zero`:129).
* `Regularity/Koszul/LengthFramework.lean` (`coe_finLength`:218,
  `finLength_zero_of_subsingleton`:274).
* `Regularity/Koszul/AssociatedGradedRing.lean` (`grPiece_mk_eq_zero_iff`:125).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean`
  (`hsAssemble_ker_homogeneousComponent_mem`:950).

## Status

* `kwit_subsingleton_of_surjective`,
  `kwit_spanFinrank_eq_of_minimal`: unconditional (conditional-form on
  the stated hypotheses).
* `kwit_quotHilbert_ne_zero_of_minimal`, `kwit_hmult_of_minimal_one`:
  conditional-exact on `[hmin]`.
* `kwit_hmult_of_minimal`: conditional-exact on `[hmin, KwitNoHomRel]`.
* `kwit_hmult_iff_noHomRel_of_minimal`: unconditional
  (conditional-form on `hmin` + `2 ≤ d`).
* Overall: partial (`KwitNoHomRel` open — the exact minimal
  remainder given `hmin`).
-/

/-- Subsingleton transfers along surjective maps (explicit hypothesis form,
so the domain/codomain unification happens at default transparency).
-/
theorem kwit_subsingleton_of_surjective {α β : Type*} (hα : Subsingleton α)
    {f : α → β} (hf : Function.Surjective f) : Subsingleton β := by
  have := hα
  exact ⟨fun b₁ b₂ => by
    obtain ⟨a₁, rfl⟩ := hf b₁
    obtain ⟨a₂, rfl⟩ := hf b₂
    rw [Subsingleton.elim a₁ a₂]⟩

section Minimal

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Minimality plus spanning forces `d = spanFinrank 𝔪`.
-/
theorem kwit_spanFinrank_eq_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank :=
  le_antisymm hmin (mult_spanFinrank_maximalIdeal_atPrime_le P d g hgen)

/-- Every quotient Hilbert value is nonzero from minimality: vanishing at
any degree would kill a graded piece, forcing `𝔪ⁿ = 𝔪ⁿ⁺¹`, hence
`𝔪ⁿ = ⊥` by Nakayama, hence every prime is maximal, hence
`dim R_P = 0`, contradicting `dim R_P = d ≥ 1`.

Conditional on exactly `[hmin]` (+ `1 ≤ d`). -/
theorem kwit_quotHilbert_ne_zero_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hd : 1 ≤ d) (n : ℕ) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) n ≠ 0 := by
  intro h0
  have hfinQ := mult_isFiniteLength_quotPiece
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d
    (RingHom.ker (polySurjResidue P d g hgen)) n
  unfold multQuotHilbert at h0
  have hlen0 : Module.length (IsLocalRing.ResidueField (Localization.AtPrime P))
      (↥(MvPolynomial.homogeneousSubmodule (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) n) ⧸
        multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) n) = 0 := by
    have hco := coe_finLength hfinQ
    rw [← hco, h0]
    simp
  have hsubQ : Subsingleton _ := Module.length_eq_zero_iff.mp hlen0
  have e1 := multQuotKerTransport P d g hgen n
  have e2 := multDegQuotEquiv (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n
  have hsub1 := kwit_subsingleton_of_surjective hsubQ e1.surjective
  have hsubG : Subsingleton (grPiece (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n) :=
    kwit_subsingleton_of_surjective hsub1 e2.surjective
  have hle_pow : (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n + 1) := by
    intro r hr
    have hz : (Submodule.Quotient.mk (⟨r, hr⟩ :
        ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n)) :
        grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n) = 0 :=
      hsubG.elim _ _
    rw [grPiece_mk_eq_zero_iff] at hz
    exact hz
  have hge : (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n + 1) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n := by
    rw [pow_succ']
    exact Ideal.mul_le_right
  have heq : (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n =
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n + 1) :=
    le_antisymm hle_pow hge
  have hFG : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n).FG :=
    IsNoetherian.noetherian _
  have hin : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) •
        ((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n) := by
    have hsmul : (IsLocalRing.maximalIdeal (Localization.AtPrime P)) •
          ((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n + 1) := by
      rw [Ideal.smul_eq_mul, ← pow_succ']
    rw [hsmul]
    exact le_of_eq heq
  obtain ⟨r, hr, hrkill⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      ((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n) hFG hin
  have hrU : IsUnit r := by
    by_contra hcon
    have hmem : r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon)
    have h1 : (1 : Localization.AtPrime P) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      have hsub :=
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)).sub_mem hmem hr
      rwa [sub_sub_cancel] at hsub
    have hne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊤ := by
      intro htop
      have h1' : (1 : Localization.AtPrime P) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
        rw [htop]
        exact Submodule.mem_top
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1'
      exact h1' isUnit_one
    exact hne
      ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).eq_top_of_isUnit_mem
        h1 isUnit_one)
  obtain ⟨u, rfl⟩ := hrU
  have hNbot : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n :
      Ideal (Localization.AtPrime P)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have h0x : ((u : (Localization.AtPrime P)ˣ) :
        Localization.AtPrime P) • x = 0 :=
      hrkill x hx
    have hmul : ((((u⁻¹ : (Localization.AtPrime P)ˣ) :
        Localization.AtPrime P)) * (u : Localization.AtPrime P)) = 1 := by
      simp
    calc x = (((((u⁻¹ : (Localization.AtPrime P)ˣ) :
          Localization.AtPrime P)) * (u : Localization.AtPrime P))) • x := by
            simp [hmul]
      _ = ((((u⁻¹ : (Localization.AtPrime P)ˣ) :
          Localization.AtPrime P))) •
          ((u : Localization.AtPrime P) • x) := by rw [mul_smul]
      _ = ((((u⁻¹ : (Localization.AtPrime P)ˣ) :
          Localization.AtPrime P))) • 0 := by rw [h0x]
      _ = 0 := by simp
  have hpow : ∀ k : ℕ, ∀ y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P),
      y ^ k ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ k := by
    intro k
    induction k with
    | zero =>
      intro y _
      simp
    | succ k ih =>
      intro y hy
      simp only [pow_succ]
      exact Ideal.mul_mem_mul (ih y hy) hy
  have hprime_max : ∀ I : Ideal (Localization.AtPrime P),
      I.IsPrime → I.IsMaximal := by
    intro I hI
    have hle : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ I := by
      intro x hx
      have hxp : x ^ n ∈ I := by
        have hmem : x ^ n ∈
            (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n :=
          hpow n x hx
        rw [hNbot] at hmem
        have hx0 : x ^ n = 0 := (Submodule.mem_bot _).mp hmem
        rw [hx0]
        exact Submodule.zero_mem I
      exact hI.mem_of_pow_mem n hxp
    have heqI : IsLocalRing.maximalIdeal (Localization.AtPrime P) = I :=
      (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le hI.ne_top hle
    rw [← heqI]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hdim0 : ringKrullDim (Localization.AtPrime P) = 0 := by
    rw [← ringKrullDimZero_iff_ringKrullDim_eq_zero]
    exact Ring.KrullDimLE.mk₀ hprime_max
  have hdimd : ringKrullDim (Localization.AtPrime P) = d :=
    mult_ringKrullDim_atPrime_eq_of_minimal P d g hgen hmin
  have hcontra : (d : WithBot ℕ∞) = 0 := by rw [← hdimd, hdim0]
  have h1d : (1 : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast hd
  rw [hcontra] at h1d
  exact one_ne_zero (le_antisymm h1d zero_le_one)

end Minimal

section Master

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `hmult` from minimality in dimension one: the `0`-th difference is the
function itself, which never vanishes by `kwit_quotHilbert_ne_zero_of_minimal`.

Conditional on exactly `[hmin]`. -/
theorem kwit_hmult_of_minimal_one
    (g : Fin 1 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : 1 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    ¬ seqDiff (1 - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) 1
      (RingHom.ker (polySurjResidue P 1 g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have h11 : (1 : ℕ) - 1 = 0 := rfl
  rw [h11, seqDiff_zero]
  intro hvan
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hvan
  have hNN := hN N le_rfl
  simp only [Pi.zero_apply] at hNN
  have hNe := kwit_quotHilbert_ne_zero_of_minimal P 1 g hgen hmin
    (le_refl 1) (N + 1)
  exact hNe (Nat.cast_eq_zero.mp hNN)

/-- Residual: `ker` contains no nonzero homogeneous relation of degree
`≥ 1`. Given `hmin` this is exact for `hmult` (see
`kwit_hmult_iff_noHomRel_of_minimal`): degree-0 relations are units, so
any nonzero one would force `ker = ⊤` and kill `Hq 0`, contradicting
`kwit_quotHilbert_ne_zero_of_minimal`; the linear case is the exact
content minimality should discharge (degree-1 independence of the
`[gᵢ]`), and degrees `≥ 2` are the higher homogeneous relations. -/
def KwitNoHomRel (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  ∀ (y : MvPolynomial (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime P))) (n : ℕ),
    y ∈ RingHom.ker (polySurjResidue P d g hgen) →
      MvPolynomial.IsHomogeneous y n → 1 ≤ n → y = 0

/-- Master: `hmult` from minimality plus the exact homogeneous-relations
residual. Homogeneous chase: every `p ∈ ker` is a sum of homogeneous
components in `ker` (`hsAssemble_ker_homogeneousComponent_mem`); the
degree-0 component would be a unit killing `Hq 0` (impossible by
`kwit_quotHilbert_ne_zero_of_minimal`, where `hmin` is essential), and
components of degree `≥ 1` vanish by the residual. Hence `ker = ⊥`,
hence `hmult` (`kwit_hmult_of_ker_eq_bot`).

Conditional on exactly `[hmin, KwitNoHomRel]` (+ `2 ≤ d`). -/
theorem kwit_hmult_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hNoHom : KwitNoHomRel P d g hgen) :
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
    apply eq_bot_iff.mpr
    intro p hpmem
    have hcomp : ∀ i ∈ Finset.range (p.totalDegree + 1),
        (MvPolynomial.homogeneousComponent i) p = 0 := by
      intro i _
      by_cases hi0 : i = 0
      · subst hi0
        by_contra hne
        have hc_hom := MvPolynomial.homogeneousComponent_isHomogeneous 0 p
        have hcmem := hsAssemble_ker_homogeneousComponent_mem
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen p hpmem 0
        have htd : ((MvPolynomial.homogeneousComponent 0) p).totalDegree = 0 :=
          (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin d)).mpr hc_hom
        have hcC : (MvPolynomial.homogeneousComponent 0) p =
            MvPolynomial.C (((MvPolynomial.homogeneousComponent 0) p).coeff 0) :=
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
        have hcoeff : (((MvPolynomial.homogeneousComponent 0) p).coeff 0) ≠ 0 := by
          intro hz
          exact hne (by rw [hcC, hz, map_zero])
        have hunit : IsUnit ((MvPolynomial.homogeneousComponent 0) p) := by
          rw [hcC]
          exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hcoeff)
        have htop : RingHom.ker (polySurjResidue P d g hgen) = ⊤ :=
          (RingHom.ker (polySurjResidue P d g hgen)).eq_top_of_isUnit_mem
            hcmem hunit
        have hQ0 : multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P)) d
            (RingHom.ker (polySurjResidue P d g hgen)) 0 = 0 := by
          have hpiece : multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime P)) d
              (RingHom.ker (polySurjResidue P d g hgen)) 0 = ⊤ := by
            unfold multKerPiece
            rw [htop]
            simp
          unfold multQuotHilbert
          rw [hpiece]
          have : Subsingleton (↥(MvPolynomial.homogeneousSubmodule (Fin d)
              (IsLocalRing.ResidueField (Localization.AtPrime P)) 0) ⧸
              (⊤ : Submodule (IsLocalRing.ResidueField (Localization.AtPrime P))
                ↥(MvPolynomial.homogeneousSubmodule (Fin d)
                  (IsLocalRing.ResidueField (Localization.AtPrime P)) 0))) :=
            ⟨fun a b => by
              obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
              obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
              have ha : (Submodule.Quotient.mk a' : _ ⧸
                  (⊤ : Submodule (IsLocalRing.ResidueField (Localization.AtPrime P)) _)) = 0 := by
                rw [Submodule.Quotient.mk_eq_zero]
                exact Submodule.mem_top
              have hb : (Submodule.Quotient.mk b' : _ ⧸
                  (⊤ : Submodule (IsLocalRing.ResidueField (Localization.AtPrime P)) _)) = 0 := by
                rw [Submodule.Quotient.mk_eq_zero]
                exact Submodule.mem_top
              rw [ha, hb]⟩
          exact finLength_zero_of_subsingleton
        exact kwit_quotHilbert_ne_zero_of_minimal P d g hgen hmin (by omega) 0 hQ0
      · have hcmem := hsAssemble_ker_homogeneousComponent_mem
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen p hpmem i
        have hc_hom := MvPolynomial.homogeneousComponent_isHomogeneous i p
        exact hNoHom _ i hcmem hc_hom (by omega)
    have hsum : p = ∑ i ∈ Finset.range (p.totalDegree + 1),
        (MvPolynomial.homogeneousComponent i) p :=
      (MvPolynomial.sum_homogeneousComponent p).symm
    rw [hsum, Finset.sum_eq_zero hcomp]
    exact Submodule.zero_mem _
  exact kwit_hmult_of_ker_eq_bot P d g hgen (by omega) hker

/-- Exactness: given `hmin` (+ `2 ≤ d`), `hmult` holds iff the residual
holds — the remainder is minimal, not just sufficient.
-/
theorem kwit_hmult_iff_noHomRel_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    (¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) ↔
      KwitNoHomRel P d g hgen := by
  constructor
  · intro hmult y n hym _ _
    have hker := kwit_ker_eq_bot_of_hmult P d g hgen hd hmult
    rw [hker] at hym
    exact (Submodule.mem_bot _).mp hym
  · intro hNoHom
    exact kwit_hmult_of_minimal P d g hgen hd hmin hNoHom

end Master

#print axioms kwit_subsingleton_of_surjective
#print axioms kwit_spanFinrank_eq_of_minimal
#print axioms kwit_quotHilbert_ne_zero_of_minimal
#print axioms kwit_hmult_of_minimal_one
#print axioms kwit_hmult_of_minimal
#print axioms kwit_hmult_iff_noHomRel_of_minimal

end HilbertWitnessNarrowing
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HilbertWitnessNarrowing

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework

/-! ## §7. Degree-1 homogeneous relations discharged (crux lane, part 1)

Closes the degree-1 half of `KwitNoHomRel` from the minimality hypothesis
`hmin : d ≤ spanFinrank 𝔪`, and restates the §6 master on the high-degree
residual `KwitNoHomRelHigh` (degrees `≥ 2` only). Degrees `≥ 2` are not
attempted here (parallel lane).

* Linear-algebra helper (unconditional):
  `kwit_linearIndependent_of_span_eq_top_of_card_le_finrank` — over a field,
  a spanning family with `card ≤ finrank` is independent. Proved directly
  (redundant-vector argument: a nontrivial relation exhibits a spanning
  subfamily of size `card - 1`, forcing `finrank ≤ card - 1`), avoiding the
  `OrzechProperty` import (which is outside the transitive import closure).
* Degree-1 discharge (conditional-exact on `[hmin]`):
  `kwit_noHomRel_degree_one_of_minimal` — a homogeneous `y ∈ ker` of degree
  `1` is `0`. Route: `y = ∑ cᵢ Xᵢ` (`homogeneousSubmodule_one_eq_span_X`);
  lift `cᵢ` to `rᵢ : R`; `polySurj y = 0` forces `∑ rᵢ [gᵢ] = 0` in `gr¹`
  (`of_injective`); hence `(∑ rᵢ gᵢ) ∈ 𝔪²` (`grPiece_mk_eq_zero_iff`), hence
  `∑ rᵢ [gᵢ] = 0` in the cotangent space (`toCotangent_eq_zero`), hence
  `∑ cᵢ [gᵢ] = 0` (`algebraMap_smul`); minimality makes the `[gᵢ]` a basis
  (`spanFinrank = finrank` + spanning-transfer), so all `cᵢ = 0`, so `y = 0`.
* Restatement (conditional-exact on `[hmin, KwitNoHomRelHigh]`):
  `KwitNoHomRelHigh` (new def, degrees `≥ 2`),
  `kwit_noHomRel_of_high_of_minimal` (full `KwitNoHomRel` from `High`),
  `kwit_hmult_of_minimal_high` (master), and
  `kwit_hmult_iff_noHomRelHigh_of_minimal` (exactness `hmult ↔ High`).
  This subsumes the §6 `KwitNoHomRel` register on `[hmin]`.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/MvPolynomial/Homogeneous.lean`:
  `homogeneousSubmodule_one_eq_span_X`.
* `Algebra/Module/SpanRankOperations.lean`:
  `spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`.
* `RingTheory/Ideal/Cotangent.lean`:
  `CotangentSpace.span_image_eq_top_iff`;: `toCotangent_eq_zero`.
* `LinearAlgebra/Span/Basic.lean`:
  `span_range_subtype_eq_top_iff`.
* `LinearAlgebra/Finsupp/LinearCombination.lean`:
  `mem_span_range_iff_exists_fun`.
* `LinearAlgebra/Dimension/Constructions.lean`:
  `finrank_le_of_span_eq_top`.
* `LinearAlgebra/LinearIndependent/Defs.lean`:
  `Fintype.linearIndependent_iff`.
* `Data/Fintype/Card.lean`: `Fintype.card_subtype_lt`.
* `Algebra/MvPolynomial/Basic.lean`: `smul_eq_C_mul`.
* `Algebra/DirectSum/Basic.lean`: `of_injective`.
* `Algebra/Algebra/Tower.lean`: `IsScalarTower.algebraMap_smul`.
* `RingTheory/Ideal/Quotient/Operations.lean`:
  `Quotient.algebraMap_eq`.
* `RingTheory/Ideal/Quotient/Defs.lean`: `mk_surjective`.
* `Algebra/BigOperators/Group/Finset/Basic.lean`:
  `mul_prod_erase` (additive form `add_sum_erase`).

Project (read-only):
* `Regularity/HomologicalDepth/HilbertWitnessNarrowing.lean` §6 (`kwit_spanFinrank_eq_of_minimal`,
  `kwit_hmult_of_minimal`, `kwit_ker_eq_bot_of_hmult`).
* `Regularity/Koszul/GradedSurjection.lean` (`polySurj_C`, `polySurj_X`, `coeffHom_mk`,
  `of_smul_eq`, `genClass`, `gen_mem_pow_one`).
* `Regularity/Koszul/AssociatedGradedRing.lean` (`grPiece_mk_smul`, `grPiece_mk_eq_zero_iff`,
  `grPiece_mkQ_eq_mk`, `grSub`).
* `Regularity/Koszul/GradedLift.lean,179` (`grlift_sop_cotangent_dim`,
  `grlift_sop_minimal`).

## Status

* `kwit_linearIndependent_of_span_eq_top_of_card_le_finrank`: unconditional.
* `kwit_noHomRel_degree_one_of_minimal`: conditional-exact on `[hmin]`.
* `kwit_noHomRel_of_high_of_minimal`: conditional-exact on
  `[hmin, KwitNoHomRelHigh]`.
* `kwit_hmult_of_minimal_high`: conditional-exact on
  `[hmin, KwitNoHomRelHigh]` (+ `2 ≤ d`).
* `kwit_hmult_iff_noHomRelHigh_of_minimal`: unconditional
  (conditional-form on `hmin` + `2 ≤ d`).
* Overall: partial (`KwitNoHomRelHigh` open — the exact minimal
  remainder given `hmin`, with degree 1 discharged).
-/

/-- Over a field, a spanning family with `card ≤ finrank` is independent.
Proved by the redundant-vector argument (a nontrivial relation yields a
spanning subfamily of size `card - 1`, contradicting `card ≤ finrank`),
so no `OrzechProperty` import is needed.
-/
theorem kwit_linearIndependent_of_span_eq_top_of_card_le_finrank
    {κ V : Type*} [Field κ] {ι : Type*} [Fintype ι]
    [AddCommGroup V] [Module κ V]
    {w : ι → V} (hspan : Submodule.span κ (Set.range w) = ⊤)
    (hle : Fintype.card ι ≤ Module.finrank κ V) :
    LinearIndependent κ w := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hne
  set ι' : Type _ := { i : ι // i ≠ j } with hιdef
  set v' : ι' → V := fun x => w x.val with hvdef
  have hcard_lt : Fintype.card ι' < Fintype.card ι := by
    have hnp : ¬ (j ≠ j) := by simp
    exact Fintype.card_subtype_lt (p := fun i => i ≠ j) hnp
  have hwj_mem : w j ∈ Submodule.span κ (Set.range v') := by
    have hsplit : c j • w j + ∑ x ∈ Finset.univ.erase j, c x • w x = 0 := by
      have h := Finset.add_sum_erase Finset.univ (fun i => c i • w i) (Finset.mem_univ j)
      have huniv : (∑ x ∈ Finset.univ, c x • w x) = 0 := hc
      rwa [huniv] at h
    have hneg : c j • w j = -∑ x ∈ Finset.univ.erase j, c x • w x :=
      eq_neg_of_add_eq_zero_left hsplit
    have h1 : w j = (c j)⁻¹ • (c j • w j) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hwj_eq : w j = ∑ x ∈ Finset.univ.erase j, (-((c j)⁻¹ * c x)) • w x := by
      rw [h1, hneg, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [smul_smul, ← neg_smul]
    rw [hwj_eq]
    apply Submodule.sum_smul_mem
    intro x hx
    have hxne : x ≠ j := Finset.ne_of_mem_erase hx
    have hmem : w x ∈ Set.range v' := ⟨⟨x, hxne⟩, rfl⟩
    exact Submodule.subset_span hmem
  have hle_span : Submodule.span κ (Set.range w) ≤ Submodule.span κ (Set.range v') := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    by_cases hi : i = j
    · subst hi
      exact hwj_mem
    · have hmem : w i ∈ Set.range v' := ⟨⟨i, hi⟩, rfl⟩
      exact Submodule.subset_span hmem
  have hspan' : Submodule.span κ (Set.range v') = ⊤ := by
    apply le_antisymm le_top
    rw [← hspan]
    exact hle_span
  have hfin_le : Module.finrank κ V ≤ Fintype.card ι' :=
    finrank_le_of_span_eq_top hspan'
  have hlt : Module.finrank κ V < Module.finrank κ V :=
    lt_of_lt_of_le (lt_of_le_of_lt hfin_le hcard_lt) hle
  exact lt_irrefl _ hlt

/-- Degree-1 homogeneous relations vanish from minimality: a homogeneous
`y ∈ ker (polySurjResidue...)` of degree `1` is `0`. Minimality makes the
`[gᵢ]` a cotangent basis, so the linear relation from `y` forces all
coefficients to `0`.

Conditional on exactly `[hmin]`. -/
theorem kwit_noHomRel_degree_one_of_minimal {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank)
    (y : MvPolynomial (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hyker : y ∈ RingHom.ker (polySurjResidue P d g hgen))
    (yhom : MvPolynomial.IsHomogeneous y 1) :
    y = 0 := by
  have hdeq := kwit_spanFinrank_eq_of_minimal P d g hgen hmin
  have hfin : d = Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime P))
      (IsLocalRing.CotangentSpace (Localization.AtPrime P)) := by
    rw [hdeq]
    exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace _
  have hgmem : ∀ i, g i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := fun i => by
    have hmem : g i ∈ Ideal.span (Set.range g) :=
      Submodule.subset_span (Set.mem_range_self i)
    rwa [hgen] at hmem
  set v : Fin d → ↥(IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    fun i => ⟨g i, hgmem i⟩ with hvdef
  have hspanM : Submodule.span (Localization.AtPrime P) (Set.range v) = ⊤ := by
    have h := (Submodule.span_range_subtype_eq_top_iff
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) hgmem).mpr hgen
    convert h using 2
  set w : Fin d → IsLocalRing.CotangentSpace (Localization.AtPrime P) :=
    fun i => (IsLocalRing.maximalIdeal (Localization.AtPrime P)).toCotangent (v i) with hwdef
  have hspanC : Submodule.span (IsLocalRing.ResidueField (Localization.AtPrime P))
      (Set.range w) = ⊤ := by
    have himg : Set.range w =
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)).toCotangent '' Set.range v := by
      ext y
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [himg]
    exact (IsLocalRing.CotangentSpace.span_image_eq_top_iff).mpr hspanM
  have hcard : Fintype.card (Fin d) ≤ Module.finrank
      (IsLocalRing.ResidueField (Localization.AtPrime P))
      (IsLocalRing.CotangentSpace (Localization.AtPrime P)) := by
    rw [Fintype.card_fin]
    exact hfin ▸ le_rfl
  have hLI : LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime P)) w :=
    kwit_linearIndependent_of_span_eq_top_of_card_le_finrank hspanC hcard
  have hyMem : y ∈ MvPolynomial.homogeneousSubmodule (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime P)) 1 := yhom
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X] at hyMem
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun
    (IsLocalRing.ResidueField (Localization.AtPrime P)) |>.mp hyMem
  have hpoly0 : polySurjResidue P d g hgen y = 0 :=
    RingHom.mem_ker.mp hyker
  rw [← hc] at hpoly0
  have hsurj : ∀ i, ∃ r : Localization.AtPrime P,
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P)) r :
        IsLocalRing.ResidueField (Localization.AtPrime P)) = c i := fun i =>
    Ideal.Quotient.mk_surjective (c i)
  choose r hr using hsurj
  have hsum_gr : ∑ i, r i • genClass (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g i hgen = 0 := by
    have hsum : polySurjResidue P d g hgen (∑ i, c i • MvPolynomial.X i) =
        DirectSum.of (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P))) 1
          (∑ i, r i • genClass (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g i hgen) := by
      rw [map_sum _ _ Finset.univ, map_sum _ _ Finset.univ]
      apply Finset.sum_congr rfl
      intro i _
      have hsmul : c i • MvPolynomial.X i = MvPolynomial.C (c i) * MvPolynomial.X i := by
        rw [MvPolynomial.smul_eq_C_mul]
      rw [hsmul, map_mul]
      have hC : polySurjResidue P d g hgen (MvPolynomial.C (c i)) =
          coeffHom (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) (c i) :=
        polySurj_C (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) d g hgen (c i)
      have hX : polySurjResidue P d g hgen (MvPolynomial.X i) =
          DirectSum.of (grPiece (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal _)) 1
            (genClass (Localization.AtPrime P)
              (IsLocalRing.maximalIdeal _) d g i hgen) :=
        polySurj_X (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) d g hgen i
      rw [hC, hX]
      have hcoeff : coeffHom (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal _) (c i) =
          DirectSum.of (grPiece (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal _)) 0
            (grMk0 (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) (r i)) := by
        rw [← hr i]
        exact coeffHom_mk (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) (r i)
      rw [hcoeff]
      exact (of_smul_eq (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1 (r i) _).symm
    rw [hsum] at hpoly0
    have h0 : DirectSum.of (grPiece (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))) 1
        (0 : grPiece (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1) = 0 :=
      map_zero _
    have heq : DirectSum.of (grPiece (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal _)) 1
        (∑ i, r i • genClass (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal _) d g i hgen) =
        DirectSum.of (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal _)) 1 0 :=
      hpoly0.trans h0.symm
    exact DirectSum.of_injective _ heq
  have hsumR : ∑ i, r i • w i = 0 := by
    have hgen_eq : ∀ i, genClass (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal _) d g i hgen =
        Submodule.Quotient.mk
          (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
            ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) := fun i => rfl
    have hsmul : ∀ i, r i • genClass (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal _) d g i hgen =
        Submodule.Quotient.mk (r i • (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
          ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1))) := fun i => by
      rw [hgen_eq i]
      exact grPiece_mk_smul (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1 (r i) _
    have hsum_mk : (∑ i, r i • genClass (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal _) d g i hgen :
        grPiece (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1) =
        Submodule.Quotient.mk (∑ i, r i • (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
          ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1))) := by
      simp_rw [hsmul]
      have h1 : ∀ i, (Submodule.Quotient.mk (r i • (⟨g i, gen_mem_pow_one
          (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
          ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1))) :
          grPiece (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1) =
          (grSub (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1).mkQ _ := fun i =>
        (grPiece_mkQ_eq_mk (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1 _).symm
      simp_rw [h1]
      rw [← map_sum _ _ Finset.univ]
      rw [grPiece_mkQ_eq_mk]
    have hsum0' : (Submodule.Quotient.mk (∑ i, r i • (⟨g i, gen_mem_pow_one
        (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
        ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1))) :
        grPiece (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) 1) = 0 := by
      rw [← hsum_mk]
      exact hsum_gr
    have hmem1 : ((∑ i, r i • (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
        ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
        ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
        Localization.AtPrime P) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 2 := by
      have h := (grPiece_mk_eq_zero_iff (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal _) 1 _).mp hsum0'
      simpa using h
    have hcoe : ((∑ i, r i • v i :
        ↥(IsLocalRing.maximalIdeal (Localization.AtPrime P))) :
        Localization.AtPrime P) =
        ((∑ i, r i • (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
          ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
          ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
          Localization.AtPrime P) := by
      have hterm : ∀ i, ((r i • v i :
          ↥(IsLocalRing.maximalIdeal (Localization.AtPrime P))) :
          Localization.AtPrime P) =
          ((r i • (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
            ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
            ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
            Localization.AtPrime P) := fun i => rfl
      have h1 : ((∑ i, r i • v i :
          ↥(IsLocalRing.maximalIdeal (Localization.AtPrime P))) :
          Localization.AtPrime P) =
          ∑ i, ((r i • v i : ↥(IsLocalRing.maximalIdeal (Localization.AtPrime P))) :
            Localization.AtPrime P) :=
        map_sum (IsLocalRing.maximalIdeal (Localization.AtPrime P)).subtype _ _
      have h2 : ((∑ i, r i • (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
          ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
          ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
          Localization.AtPrime P) =
          ∑ i, ((r i • (⟨g i, gen_mem_pow_one (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal _) d g i hgen⟩ :
            ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
            ↥((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)) :
            Localization.AtPrime P) :=
        map_sum (((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 1)).subtype _ _
      rw [h1, h2]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    have hmem2 : ((∑ i, r i • v i :
        ↥(IsLocalRing.maximalIdeal (Localization.AtPrime P))) :
        Localization.AtPrime P) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 2 := by
      rw [hcoe]
      exact hmem1
    have hcot0 : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).toCotangent
        (∑ i, r i • v i) = 0 := by
      rw [Ideal.toCotangent_eq_zero]
      exact hmem2
    have hlin : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).toCotangent
        (∑ i, r i • v i) =
        ∑ i, r i • (IsLocalRing.maximalIdeal (Localization.AtPrime P)).toCotangent (v i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul _ _ _
    rw [hlin] at hcot0
    convert hcot0 using 2
  have hsumC : ∑ i, c i • w i = 0 := by
    have hterm : ∀ i, c i • w i = r i • w i := fun i => by
      have h1 : (algebraMap (Localization.AtPrime P)
          (IsLocalRing.ResidueField (Localization.AtPrime P)) (r i)) • w i =
          r i • w i :=
        IsScalarTower.algebraMap_smul
          (IsLocalRing.ResidueField (Localization.AtPrime P)) (r i) (w i)
      have h2 : algebraMap (Localization.AtPrime P)
          (IsLocalRing.ResidueField (Localization.AtPrime P)) (r i) = c i := by
        rw [← hr i]
        rfl
      rw [h2] at h1
      exact h1
    calc ∑ i, c i • w i = ∑ i, r i • w i :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = 0 := hsumR
  have hc0 : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp hLI c hsumC
  have hsum0 : (∑ i, c i • MvPolynomial.X i :
      MvPolynomial (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime P))) = 0 := by
    simp [hc0]
  rw [hc] at hsum0
  exact hsum0

section HighRestate

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Residual: `ker` contains no nonzero homogeneous relation of degree
`≥ 2`. The degree-1 half is discharged by
`kwit_noHomRel_degree_one_of_minimal`; this is the exact remainder. -/
def KwitNoHomRelHigh (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  ∀ (y : MvPolynomial (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime P))) (n : ℕ),
    y ∈ RingHom.ker (polySurjResidue P d g hgen) →
      MvPolynomial.IsHomogeneous y n → 2 ≤ n → y = 0

/-- Full `KwitNoHomRel` from the high-degree residual plus minimality:
degree `1` is discharged by `kwit_noHomRel_degree_one_of_minimal`.

Conditional on exactly `[hmin, KwitNoHomRelHigh]`. -/
theorem kwit_noHomRel_of_high_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hHigh : KwitNoHomRelHigh P d g hgen) :
    KwitNoHomRel P d g hgen := by
  intro y n hyker yhom hn1
  by_cases hn2 : 2 ≤ n
  · exact hHigh y n hyker yhom hn2
  · have hn_eq : n = 1 := by omega
    subst hn_eq
    exact kwit_noHomRel_degree_one_of_minimal P d g hgen hmin y hyker yhom

/-- Master: `hmult` from minimality plus the high-degree residual only.

Conditional on exactly `[hmin, KwitNoHomRelHigh]` (+ `2 ≤ d`). -/
theorem kwit_hmult_of_minimal_high (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hHigh : KwitNoHomRelHigh P d g hgen) :
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hNoHom := kwit_noHomRel_of_high_of_minimal P d g hgen hmin hHigh
  exact kwit_hmult_of_minimal P d g hgen hd hmin hNoHom

/-- Exactness: given `hmin` (+ `2 ≤ d`), `hmult` holds iff the high-degree
residual holds.
-/
theorem kwit_hmult_iff_noHomRelHigh_of_minimal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    (¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) ↔
      KwitNoHomRelHigh P d g hgen := by
  constructor
  · intro hmult y n hym _ _
    have hker := kwit_ker_eq_bot_of_hmult P d g hgen hd hmult
    rw [hker] at hym
    exact (Submodule.mem_bot _).mp hym
  · intro hHigh
    exact kwit_hmult_of_minimal_high P d g hgen hd hmin hHigh

end HighRestate

#print axioms kwit_linearIndependent_of_span_eq_top_of_card_le_finrank
#print axioms kwit_noHomRel_degree_one_of_minimal
#print axioms kwit_noHomRel_of_high_of_minimal
#print axioms kwit_hmult_of_minimal_high
#print axioms kwit_hmult_iff_noHomRelHigh_of_minimal

end HilbertWitnessNarrowing
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
