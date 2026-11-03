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

/-!
# Kernel assembly: `ker polySurjResidue = ⊥` from dim-equality (M4c-ii close)

Assembles the M4c-ii kernel equality from the three closed lanes:

* (§1) `hag_gr` for `H_gr` (unconditional): `hsQuotHilbert_hag_gr`
  (Hilbert–Serre eventual polynomiality for the homogeneous quotient
  `κ[X]/ker`) transported along the R-2d′ bridge
  (`mult_quotHilbert_eq_grPieceLength`: the quotient Hilbert function is
  the `gr`-piece length function). The two quotient Hilbert functions
  (`hsQuotHilbert`, `multQuotHilbert`) agree definitionally
  (`ker_assemble_hsQuot_eq_multQuot`), and `ker` is homogeneous by
  `hsAssemble_ker_homogeneousComponent_mem`. The SingleDrop and
  multiplicity residue actions on `grPiece` agree pointwise
  (`ker_assemble_smul_agree`), so the two module instances are equal
  (`ker_assemble_module_eq`) and lengths transfer across them.
* (§2) the concrete `hstep` (unconditional): per-`(y, t)` SES equation
  plus pointwise comparison from the two closed SingleDrop pieces
  (`singleDrop_hSES`, `singleDrop_hcomp_concrete`), packaged as
  `ker_assemble_hstep`; the third closed piece (`singleDrop_hdom`)
  joins them in `ker_assemble_deg_le_of_ker_ne_bot` via
  `singleDrop_deg_le_of_step`.
* (§3) the master `ker_assemble_ker_eq_bot`: `hag_gr` (§1) fed into
  `singleDrop_ker_eq_bot_of_hag`, leaving `hdimEq` as the sole residue.

## Status

* `ker_assemble_ker_homogeneous`, `ker_assemble_hsQuot_eq_multQuot`,
  `ker_assemble_smul_agree`, `ker_assemble_module_eq`,
  `ker_assemble_grHilbert_eq_hsQuot`, `ker_assemble_hag_gr`,
  `ker_assemble_hstep`: unconditional.
* `ker_assemble_deg_le_of_ker_ne_bot`: conditional-explicit on `hag_gr`.
* `ker_assemble_ker_eq_bot`: conditional-exact on `[hdimEq]`.

## References

Project (read-only):
* `Regularity/Multiplicity/SingleDropRegularity.lean` (§7 masters
  `singleDrop_deg_le_of_step`, `singleDrop_ker_eq_bot_of_hag`; closed
  pieces `singleDrop_hSES`, `singleDrop_hcomp_concrete`,
  `singleDrop_hdom`).
* `Regularity/Multiplicity/HilbertSerre.lean` (`hsQuotHilbert_hag_gr`).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean`
  (`mult_quotHilbert_eq_grPieceLength`).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean`
  (`hsAssemble_ker_homogeneousComponent_mem`,
  `hsAssemble_exists_homogeneous_mem_ker`).
* `Regularity/Koszul/GradedLift.lean` (consumer: `grlift_r2_exact` takes
  `hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KernelAssembly

open scoped Polynomial

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre

section KerAssemble

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-! ## §1. `hag_gr` for `H_gr` via Hilbert–Serre and the R-2d′ bridge -/

/-- `ker polySurjResidue` is homogeneous: kernel homogeneous components
(`hsAssemble_ker_homogeneousComponent_mem`) in `hsIsHomogeneous` shape.
-/
theorem ker_assemble_ker_homogeneous (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    hsIsHomogeneous (RingHom.ker (polySurjResidue P d g hgen)) := by
  intro f hf n
  exact hsAssemble_ker_homogeneousComponent_mem
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen f hf n

/-- The Hilbert–Serre and multiplicity quotient Hilbert functions agree
(both are `κ`-lengths of homogeneous pieces modulo the comap piece).
-/
theorem ker_assemble_hsQuot_eq_multQuot (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) :
    hsQuotHilbert κ d J n = multQuotHilbert κ d J n := rfl

/-- The two residue actions on `grPiece` agree: the SingleDrop
`Quotient.liftOn` action (`singleDrop_grPiece_smulFun`) equals the
multiplicity `Quotient.out` action (`multGrPieceQuotientModule`).
-/
theorem ker_assemble_smul_agree (n : ℕ)
    (q : (Localization.AtPrime P)
      ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (x : grPiece (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n) :
    singleDrop_grPiece_smulFun (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        n q x
      = (Quotient.out q : Localization.AtPrime P) • x := by
  refine Quotient.inductionOn' q (fun r => ?_)
  change singleDrop_grPiece_smulFun
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P)) r) x
    = (Quotient.out
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P)) r) :
      Localization.AtPrime P) • x
  rw [singleDrop_grPiece_smul_mk]
  have hout : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (Quotient.out (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) r))
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P)) r :=
    Ideal.Quotient.mk_out _
  have hcongr := mult_grPiece_smul_congr (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n _ _ hout x
  exact hcongr.symm

/-- The two residue module structures on `grPiece` are equal: the
SingleDrop `Quotient.liftOn` instance agrees with the multiplicity
`Quotient.out` instance by `ker_assemble_smul_agree` (proof fields by
proof irrelevance).
-/
theorem ker_assemble_module_eq (n : ℕ) :
    singleDrop_grPiece_module (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        n =
      (multGrPieceResidueModule P n : Module
        ((Localization.AtPrime P)
          ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n)) := by
  have hsmul : singleDrop_grPiece_smulFun
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n =
        fun (q : (Localization.AtPrime P)
            ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P))
          (x : grPiece (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n) =>
          (Quotient.out q : Localization.AtPrime P) • x := by
    funext q x
    exact ker_assemble_smul_agree P n q x
  unfold singleDrop_grPiece_module multGrPieceResidueModule
    multGrPieceQuotientModule
  simp only [hsmul]

/-- The `gr` Hilbert function is the Hilbert–Serre quotient Hilbert
function of `ker` (R-2d′ length transfer:
`mult_quotHilbert_eq_grPieceLength`, across the two residue module
instances via `ker_assemble_module_eq`).
-/
theorem ker_assemble_grHilbert_eq_hsQuot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (n : ℕ) :
    singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n =
      hsQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P)) d
        (RingHom.ker (polySurjResidue P d g hgen)) n := by
  have hbridge := mult_quotHilbert_eq_grPieceLength P d g hgen n
  have hq := ker_assemble_hsQuot_eq_multQuot
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d
    (RingHom.ker (polySurjResidue P d g hgen)) n
  rw [hq, hbridge]
  unfold singleDrop_grHilbert
  rw [ker_assemble_module_eq P n]
  congr 1

/-- `hag_gr` for `H_gr` in the exact §7 shape: Hilbert–Serre
(`hsQuotHilbert_hag_gr` on the homogeneous `ker`) transported along
the R-2d′ bridge.
-/
theorem ker_assemble_hag_gr (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ∃ Pgr : ℚ[X], (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr := by
  obtain ⟨Pgr, hPgr⟩ := hsQuotHilbert_hag_gr
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d
    (RingHom.ker (polySurjResidue P d g hgen))
    (ker_assemble_ker_homogeneous P d g hgen)
  refine ⟨Pgr, ?_⟩
  have hfun : (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ)) =
      (fun n => ((hsQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
        d (RingHom.ker (polySurjResidue P d g hgen)) n : ℕ) : ℚ)) := by
    funext n
    rw [ker_assemble_grHilbert_eq_hsQuot P d g hgen n]
  rw [hfun]
  exact hPgr

/-! ## §2. Concrete `hstep` from the three closed pieces -/

/-- The concrete per-`(y, t)` step: the SES equation
(`singleDrop_hSES`) plus the pointwise comparison
(`singleDrop_hcomp_concrete`).
-/
theorem ker_assemble_hstep (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (y : MvPolynomial (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime P))) (t : ℕ)
    (hym : y ∈ RingHom.ker (polySurjResidue P d g hgen)) (hyne : y ≠ 0)
    (hyhom : y.IsHomogeneous t) :
    (∀ n, t ≤ n →
      singleDrop_quotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
          d t y hyhom n
        + hsAssemble_domainHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
        = hsAssemble_domainHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d n)
    ∧ (∀ n, singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n
        ≤ singleDrop_quotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P))
          d t y hyhom n) := by
  constructor
  · intro n hn
    exact singleDrop_hSES (IsLocalRing.ResidueField (Localization.AtPrime P))
      d t y hyhom hyne n hn
  · intro n
    exact singleDrop_hcomp_concrete (R := Localization.AtPrime P)
      d g hgen t y hyhom n hym

/-- The drop with `hstep`/`hdom` discharged: `ker ≠ ⊥` supplies the
homogeneous `y`, `ker_assemble_hstep` supplies SES+comparison, and
`singleDrop_hdom` supplies domination.

Explicitly conditional on `hag_gr` only. -/
theorem ker_assemble_deg_le_of_ker_ne_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d) (Pgr : ℚ[X])
    (hag_gr : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr)
    (hker : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥) :
    Pgr.natDegree ≤ d - 2 := by
  obtain ⟨t, y, hym, hyne, hyhom⟩ :=
    hsAssemble_exists_homogeneous_mem_ker _ d g hgen hker
  obtain ⟨hSES, hcomp⟩ := ker_assemble_hstep P d g hgen y t hym hyne hyhom
  exact singleDrop_deg_le_of_step P d g hgen hd y t hym hyne hyhom
    (singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime P)))
    (singleDrop_quotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
      d t y hyhom)
    hSES hcomp Pgr hag_gr (singleDrop_hdom d)

/-! ## §3. The master: `ker = ⊥` conditional only on `hdimEq` -/

/-- The M4c-ii close: `hag_gr` (§1, unconditional) fed into
`singleDrop_ker_eq_bot_of_hag`, leaving `hdimEq` as the sole residue.
Discharges the `hker⊥` hypothesis of `grlift_r2_exact`.

Conditional on exactly `[hdimEq]`. -/
theorem ker_assemble_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  obtain ⟨Pgr, hag_gr⟩ := ker_assemble_hag_gr P d g hgen
  exact singleDrop_ker_eq_bot_of_hag P d g hgen hd Pgr hag_gr hdimEq

end KerAssemble

#print axioms ker_assemble_ker_homogeneous
#print axioms ker_assemble_hsQuot_eq_multQuot
#print axioms ker_assemble_smul_agree
#print axioms ker_assemble_module_eq
#print axioms ker_assemble_grHilbert_eq_hsQuot
#print axioms ker_assemble_hag_gr
#print axioms ker_assemble_hstep
#print axioms ker_assemble_deg_le_of_ker_ne_bot
#print axioms ker_assemble_ker_eq_bot

end KernelAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
