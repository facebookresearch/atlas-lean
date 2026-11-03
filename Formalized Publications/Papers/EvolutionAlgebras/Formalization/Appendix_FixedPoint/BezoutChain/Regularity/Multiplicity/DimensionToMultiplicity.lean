/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Dimension-to-multiplicity (R-2c′ closed)

R-2c′ is the dimension-to-multiplicity implication: a `d`-dimensional
graded quotient has Hilbert polynomial of degree `d - 1` with nonzero
leading coefficient. In-tree it appears as the `hwit` existential —
quot-side (`MultiplicityNonvanishing.lean` §14: witness for the shifted
`multQuotHilbert`) and `gr`-side (`SingleDropRegularity.lean` §12: witness
for the unshifted `singleDrop_grHilbert`) — predicated on a dimension
equality. This file closes both forms (conditional-form on the
dimension equality, application data):

* (§1) Quot-side: `dim (S ⧸ ker) = d` forces `ker = ⊥`
  (`dimToMult_ker_eq_bot_of_quot_dim_eq`, via the §17 chain argument),
  hence quot-side `hmult` (`dimToMult_quotHmult_of_dim_eq`, domain
  theory) and the §14 `hwit` existential
  (`dimToMult_quotHwit_of_dim_eq`, via the Witness narrowing).
* (§2) `gr`-side: `dim gr = d` gives the §12 witness triple
  (`dimToMult_grWitness_of_gr_dim_eq`), `gr`-side `hmult` in the exact
  `HmultMinAtAss` per-prime shape (`dimToMult_grHmult_of_gr_dim_eq`),
  and `hdimEq` in exact KerAssemble shape
  (`dimToMult_grHdimEq_of_gr_dim_eq`).
* (§3) Ass-level masters: `HgrDimEqMinAtAss` (SPEC: per-Ass-prime
  `dim gr = embdim`, i.e. R-2a′ at Ass primes) feeds `HmultMinAtAss`
  (`hmultMin_of_grDimEq`), `HdimEqMinAtAss` (`hdimEqMin_of_grDimEq`),
  and rb-1 itself (`hunmixedTwo_of_grDimEq`).
* (§4, doc-only) Precise remainder: `HgrDimEqMinAtAss` from the pure
  associated-graded equality `dim gr = dim R_Q`
  (`hgrDimEqMin_of_assocGradedDim`), so the sole open item is
  `dim gr_I(R) = dim R` per Ass prime — absent from Mathlib v4.34.0.
* (§5) Collapse of the remainder: `HgrDimEqMinAtAss ↔ HdimGrMinAtAss`
  (SPEC-shape iff, unconditional, via the §3 direction lemmas), the
  goal-strength iff with `HkerMinAtAss` (`hgrDimEq_iff_hkerMin`), and
  per-`Q` unconditional `d = 0` / `d = 1` instances
  (`hgrDimEq_embdim_zero/one`). Together with the §3 converse lane
  (`grDimEqMin_of_hwitMin`, `hwitMin_iff_grDimEqMin`), R-2a′ at `d ≥ 2`
  adds no remainder beyond the shared R-2c′ witness `HwitMinAtAss`.
* (§7) Witness skeleton + high-relations route: unconditional
  `(g, hgen, H, hF, weak-hwit)` skeleton at minimal `d ≥ 2`, the full
  `HwitMinAtAss` tuple conditional-exact on `HnoHomRelHighMinAtAss`
  (no homogeneous `ker` relation of degree `≥ 2`), the exactness iff,
  rb-1 jointly, and one-line §6 adapters (`grDimEq`/`hmult`/`hdimEq`/
  `hker` from `hHigh`).
* (§6) Supply-chain wiring: exact-on-crux corollaries so `HdimEqMinAtAss`
  at `d ≥ 2` (hence rb-1) closes automatically once any crux form proves
  (forward `hmultMin`/`hdimEqMin` of `hwitMin`/`dimGrMin`/`hkerMin`,
  backward lanes, iff ring, kernel/rb-1/per-`(Q,d)` auto-close).

Why this is non-circular (cf. the Multiplicity §17 circularity note):
the §17 cycle `hle_gr → dim = d → hwit → hmult → ker = ⊥ → hle_gr`
says no proof of `hle_gr` exists below the strength of `ker = ⊥`.
The route here goes `dim = d → ker = ⊥` directly (the unconditional
§17 chain argument `mult_ker_eq_bot_of_quot_lowerBound`), i.e. at full
goal strength, then `ker = ⊥ → hmult → hwit` by domain theory. Nothing
assumes `hwit`, `hmult`, `hdimEq`, or `ker = ⊥` to prove them; the only
undischarged input is the R-2a′ dimension equality itself.

## References

Project (read-only):
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean`
  (`mult_ker_eq_bot_of_quot_lowerBound`:1819,
  `mult_quotKerEquiv_dim`:253, `mult_hmult_of_coeff_ne_zero`:298,
  `mult_ringKrullDim_atPrime_eq_of_minimal`:603).
* `Regularity/HomologicalDepth/HilbertWitnessNarrowing.lean` (`kwit_hmult_of_ker_eq_bot`:512,
  `kwit_hwit_of_hmult`:328, `kwit_grWitness_of_hmult`:380).
* `Regularity/Multiplicity/SingleDropRegularity.lean`
  (`singleDrop_hdimEq_of_grWitness`:1784).
* `Regularity/Koszul/GradedLift.lean` (`grlift_sop_exists`:156).
* `Geometry/UnmixednessAtLengthTwo.lean` (`HmultMinAtAss`:538,
  `HdimEqMinAtAss`:286, `hdimEqMin_of_hmultMin`:554,
  `hunmixed_two_of_hdimEqMin`:412, `HunmixedTwoProp`:397).

## Status

* §1–§2: unconditional (conditional-form on `hdim`/`hgr` + `1 ≤ d`).
* §3: conditional-exact on `[hgr]` (`HgrDimEqMinAtAss`).
* `hgrDimEqMin_of_assocGradedDim`: conditional-exact on the pure
  associated-graded equality per Ass prime.
* §5: unconditional (shape iff, goal-strength iff, `d ≤ 1` instances).
* §7: unconditional (skeleton, exactness iff); conditional-exact on
  `[hHigh]` (full witness, rb-1).
* §6: conditional-exact on the named crux input (one-line compositions);
  iffs unconditional.
* Overall: R-2c′ closed; partial toward `HmultMinAtAss`
  (remainder = `HwitMinAtAss` only, §5); §6 wires every residual so the
  crux discharge propagates automatically.
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace DimensionToMultiplicity

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing

/-! ## §1. Quot-side R-2c′: `dim (S ⧸ ker) = d` gives the witness -/

section QuotSide

/-- Full dimension of a polynomial quotient forces a trivial kernel,
equality form (thin wrapper over the §17 chain argument).
-/
theorem dimToMult_ker_eq_bot_of_quot_dim_eq (κ : Type*) [Field κ]
    (d : ℕ) (ker : Ideal (MvPolynomial (Fin d) κ))
    (hdim : ringKrullDim (MvPolynomial (Fin d) κ ⧸ ker) = d) :
    ker = ⊥ :=
  mult_ker_eq_bot_of_quot_lowerBound κ d ker hdim.ge

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Quot-side `hmult` (shifted `multQuotHilbert`) from the quotient
dimension equality: `dim = d` forces `ker = ⊥`, and the quotient is
then the domain.
-/
theorem dimToMult_quotHmult_of_dim_eq (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hdim : ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) = d) :
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hker := dimToMult_ker_eq_bot_of_quot_dim_eq
    (IsLocalRing.ResidueField (Localization.AtPrime P)) d _ hdim
  exact kwit_hmult_of_ker_eq_bot P d g hgen hd hker

/-- Quot-side R-2c′ in the exact Multiplicity §14 `hwit` shape: the
`dim = d` hypothesis yields `(Pwit, hle, hag, hc)` for the shifted
quotient Hilbert function.
-/
theorem dimToMult_quotHwit_of_dim_eq (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hdim : ringKrullDim (MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) = d) :
    ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d
          (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0 :=
  kwit_hwit_of_hmult P d g hgen hd
    (dimToMult_quotHmult_of_dim_eq P d g hgen hd hdim)

end QuotSide

/-! ## §2. `gr`-side R-2c′: `dim gr = d` gives the witness -/

section GrSide

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `gr`-side R-2c′ in the exact SingleDrop §12 `hwit` shape: `dim gr`
transports to the quotient side (R-2d′ dimension bridge), forces
`ker = ⊥`, and the Witness prime mover supplies the triple for the
unshifted `singleDrop_grHilbert`.
-/
theorem dimToMult_grWitness_of_gr_dim_eq (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hgr : ringKrullDim (grRegular P) = d) :
    ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0 := by
  have hdim : ringKrullDim (MvPolynomial (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
      RingHom.ker (polySurjResidue P d g hgen)) = d := by
    rw [mult_quotKerEquiv_dim P d g hgen, hgr]
  have hmult := dimToMult_quotHmult_of_dim_eq P d g hgen hd hdim
  exact kwit_grWitness_of_hmult P d g hgen hd hmult

/-- `gr`-side `hmult` from `dim gr = d`, in the exact `HmultMinAtAss`
per-prime shape (unshifted `singleDrop_grHilbert`).
-/
theorem dimToMult_grHmult_of_gr_dim_eq (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hgr : ringKrullDim (grRegular P) = d) :
    ¬ seqDiff (d - 1) (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  obtain ⟨Pwit, hle, hagW, hc⟩ :=
    dimToMult_grWitness_of_gr_dim_eq P d g hgen hd hgr
  exact mult_hmult_of_coeff_ne_zero Pwit hle hagW hc

/-- `gr`-side `hdimEq` from `dim gr = d`, in exact KerAssemble-hyp
shape (the SingleDrop §12 chained master with `hwit` discharged).
-/
theorem dimToMult_grHdimEq_of_gr_dim_eq (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hgr : ringKrullDim (grRegular P) = d) :
    ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1 := by
  obtain ⟨Pwit, hle, hagW, hc⟩ :=
    dimToMult_grWitness_of_gr_dim_eq P d g hgen hd hgr
  exact singleDrop_hdimEq_of_grWitness P d Pwit hle hagW hc

end GrSide

#print axioms dimToMult_ker_eq_bot_of_quot_dim_eq
#print axioms dimToMult_quotHmult_of_dim_eq
#print axioms dimToMult_quotHwit_of_dim_eq
#print axioms dimToMult_grWitness_of_gr_dim_eq
#print axioms dimToMult_grHmult_of_gr_dim_eq
#print axioms dimToMult_grHdimEq_of_gr_dim_eq

/-! ## §3. Ass-level masters: R-2a′ remainder feeds the crux -/

section AssMasters

/-- Per-Ass-prime `dim gr = embdim` (R-2a′ at Ass primes): the sole
remainder between R-2c′ (closed in §§1–2) and `HmultMinAtAss`. By
`hgrDimEqMin_of_assocGradedDim` below this is exactly the pure
associated-graded equality `dim gr = dim R_Q` per Ass prime
(`dim R_Q = embdim` is proved via regularity).

Specification (Prop address for the R-2a′ remainder). -/
def HgrDimEqMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ringKrullDim (grRegular Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank

/-- `HmultMinAtAss` from the R-2a′ remainder: per-`Q` minimal spanning
data (`grlift_sop_exists`) identifies `d` with `embdim`, and the §2
`gr`-side nonvanishing applies.

Conditional on exactly `[hgr]`. -/
theorem hmultMin_of_grDimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J := by
  intro Q _ hQ d hdmin hd2
  obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
  have heq : d = d' := hdmin.trans hd'.symm
  subst heq
  have hdimGr : ringKrullDim (grRegular Q) = d :=
    (hgr Q hQ).trans (by exact_mod_cast hd'.symm)
  exact dimToMult_grHmult_of_gr_dim_eq Q d g hgen (by omega) hdimGr

/-- `HdimEqMinAtAss` from the R-2a′ remainder (via
`hdimEqMin_of_hmultMin`).

Conditional on exactly `[hgr]`. -/
theorem hdimEqMin_of_grDimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin m K J
    (hmultMin_of_grDimEq m K J hgr)

/-- Rb-1 from the R-2a′ remainder: the §5 master fed with the §2-fed
`HdimEqMinAtAss`.

Conditional on exactly `[hgr]`. -/
theorem hunmixedTwo_of_grDimEq (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hgr : HgrDimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  fun P _ hP => UnmixednessAtLengthTwo.hunmixed_two_of_hdimEqMin m K q hsucc J hJ
    P hP (hdimEqMin_of_grDimEq m K J hgr)

/-- The R-2a′ remainder from the pure associated-graded equality
`dim gr = dim R_Q` per Ass prime: `dim R_Q = embdim` is proved
(`mult_ringKrullDim_atPrime_eq_of_minimal`, with `hmin` from the
minimal sop equation itself).

Conditional on exactly `[hgrdim]`. -/
theorem hgrDimEqMin_of_assocGradedDim (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrdim : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ringKrullDim (grRegular Q) =
        ringKrullDim (Localization.AtPrime Q)) :
    HgrDimEqMinAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hd
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen hmin
  rw [hgrdim Q hQ, hR]
  exact_mod_cast hd

/-! ## §3b. Witness closure: `HwitMinAtAss` iff R-2a′ at Ass primes

The `UnmixednessAtLengthTwo.hdimGrMin_of_witnessMin` master (:764) closes R-2a′ on
the R-2c′ witness remainder `HwitMinAtAss`. Here we land the converse:
`HwitMinAtAss` follows from the R-2a′ remainder `HgrDimEqMinAtAss`
(`hwitMin_of_grDimEq`), so the witness side data is exactly R-2a′
strength (`hwitMin_iff_grDimEqMin`) and hence goal-strength
(`hwitMin_iff_hkerMin`, via `hdimGrMin_iff_hkerMin`).

Proof idea for the forward direction: per-`Q` minimal spanning data
identifies `d` with `embdim`; `dim gr = d` transports to the quotient
side (R-2d′ bridge), forces `ker = ⊥` (§17 chain), hence `hwit` by
domain theory. `H := 0` supplies `hF` (zero is polynomial growth of
every degree) and `hdrop` is vacuous on `ker = ⊥`.
-/

/-- R-2a′ in `HgrDimEqMinAtAss` form from the `HdimGrMinAtAss` form
(instantiate the minimality equation by `rfl`).
-/
theorem grDimEqMin_of_dimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdim : UnmixednessAtLengthTwo.HdimGrMinAtAss m K J) :
    HgrDimEqMinAtAss m K J := by
  intro Q _ hQ
  exact hdim Q hQ rfl

/-- R-2a′ in `HdimGrMinAtAss` form from the `HgrDimEqMinAtAss` form
(rewrite the minimality equation).
-/
theorem dimGrMin_of_grDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HdimGrMinAtAss m K J := by
  intro Q _ hQ d hdmin
  exact (hgr Q hQ).trans (by exact_mod_cast hdmin.symm)

/-- `HwitMinAtAss` from the R-2a′ remainder: per-`Q` minimal spanning
data identifies `d` with `embdim`; `dim gr = d` transports to the
quotient side, forces `ker = ⊥`, hence `hwit` by domain theory.
`H := 0` supplies `hF`; `hdrop` is vacuous on `ker = ⊥`.

Conditional on exactly `[hgr]`. -/
theorem hwitMin_of_grDimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J := by
  intro Q _ hQ d hdmin hd2
  obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
  have heq : d = d' := hdmin.trans hd'.symm
  subst heq
  have hdimGr : ringKrullDim (grRegular Q) = d :=
    (hgr Q hQ).trans (by exact_mod_cast hd'.symm)
  have hdimQuot : ringKrullDim (MvPolynomial (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime Q)) ⧸
      RingHom.ker (polySurjResidue Q d g hgen)) = d := by
    rw [mult_quotKerEquiv_dim Q d g hgen, hdimGr]
  have hker : RingHom.ker (polySurjResidue Q d g hgen) = ⊥ :=
    mult_ker_eq_bot_of_quot_lowerBound _ d _ hdimQuot.ge
  refine ⟨g, hgen, (fun _ => 0), ?hF, ?hwit, ?hdrop⟩
  · refine ⟨0, by simp, Filter.Eventually.of_forall (fun n => by simp [evalFun])⟩
  · exact kwit_hwit_of_hmult Q d g hgen (by omega)
      (kwit_hmult_of_ker_eq_bot Q d g hgen (by omega) hker)
  · intro hne
    exact absurd hker hne

/-- The R-2a′ remainder from the witness remainder (via
`hdimGrMin_of_witnessMin`).
-/
theorem grDimEqMin_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    HgrDimEqMinAtAss m K J :=
  grDimEqMin_of_dimGrMin m K J
    (UnmixednessAtLengthTwo.hdimGrMin_of_witnessMin m K J hwit)

/-- `HwitMinAtAss` iff R-2a′ at Ass primes: the R-2c′ witness side data
is exactly R-2a′ strength (forward here, backward
`hdimGrMin_of_witnessMin`).
-/
theorem hwitMin_iff_grDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J ↔ HgrDimEqMinAtAss m K J :=
  ⟨grDimEqMin_of_hwitMin m K J, hwitMin_of_grDimEq m K J⟩

/-- `HwitMinAtAss` iff `HkerMinAtAss`: the witness remainder is
goal-strength (via `hdimGrMin_iff_hkerMin`).
-/
theorem hwitMin_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J ↔ UnmixednessAtLengthTwo.HkerMinAtAss m K J := by
  have h1 : UnmixednessAtLengthTwo.HwitMinAtAss m K J ↔
      UnmixednessAtLengthTwo.HdimGrMinAtAss m K J :=
    ⟨UnmixednessAtLengthTwo.hdimGrMin_of_witnessMin m K J,
     fun hdim => hwitMin_of_grDimEq m K J
       (grDimEqMin_of_dimGrMin m K J hdim)⟩
  exact h1.trans (UnmixednessAtLengthTwo.hdimGrMin_iff_hkerMin m K J)

end AssMasters

#print axioms hmultMin_of_grDimEq
#print axioms hdimEqMin_of_grDimEq
#print axioms hunmixedTwo_of_grDimEq
#print axioms hgrDimEqMin_of_assocGradedDim
#print axioms grDimEqMin_of_dimGrMin
#print axioms dimGrMin_of_grDimEqMin
#print axioms hwitMin_of_grDimEq
#print axioms grDimEqMin_of_hwitMin
#print axioms hwitMin_iff_grDimEqMin
#print axioms hwitMin_iff_hkerMin

/-! ## §4. Precise remainder register (doc-only)

R-2c′ is closed (§§1–2, conditional-form on the dimension equality).
Toward `HmultMinAtAss` / `HdimEqMinAtAss` / rb-1 (§3), the minimal
non-circular remainder (verbatim) is `HgrDimEqMinAtAss`, i.e.
`ringKrullDim (grRegular Q) = spanFinrank 𝔪(R_Q)` per
`Q ∈ Ass(R ⧸ J)` — the R-2a′ lane result — narrowed by
`hgrDimEqMin_of_assocGradedDim` to the pure associated-graded
dimension equality `dim gr_I(R) = dim R` per Ass prime (Hilbert–Samuel
/ systems-of-parameters theory, absent from Mathlib v4.34.0: no
catenary, system-of-parameters, Hilbert–Samuel, or associated-graded
dimension files under `Mathlib/RingTheory/`).

Exactness: the remainder is not just sufficient. By
`mult_hle_gr_iff_ker_eq_bot` (Multiplicity §17) the R-2a′ lower bound
is `ker = ⊥`-strength, and by `kwit_hmult_iff_ker_eq_bot` (Witness §4)
so is `hmult`; no weakening below goal strength can discharge them,
and no circular hypothesis was assumed anywhere in §§1–3.
-/

/-! ## §5. Collapse of the remainder to `HwitMinAtAss`

Complements the §3 converse lane (`grDimEqMin_of_dimGrMin`,
`dimGrMin_of_grDimEqMin`, `hwitMin_of_grDimEq`, `grDimEqMin_of_hwitMin`,
`hwitMin_iff_grDimEqMin`, `hwitMin_iff_hkerMin`): the SPEC-shape iff in
explicit form, goal-strength in `HgrDimEqMinAtAss` shape, and the per-`Q`
unconditional `d ≤ 1` instances.

* `hgrDimEq_iff_hdimGrMin`: `HgrDimEqMinAtAss ↔ HdimGrMinAtAss`
  (unconditional iff, via the §3 direction lemmas) — the two R-2a′ SPEC
  shapes coincide.
* `hgrDimEq_iff_hkerMin`: `HgrDimEqMinAtAss ↔ HkerMinAtAss`
  (unconditional iff) — goal-strength in `HgrDimEqMinAtAss` shape: no
  unconditional proof at `d ≥ 2` exists below the strength of `ker = ⊥`
  itself, so the conditional form on `[hwit]` (`grDimEqMin_of_hwitMin`)
  is maximal.
* `hgrDimEq_embdim_zero/one`: per-`Q` unconditional instances when the
  embedding dimension is `0` / `1` (via the closed kernel branches).

`HwitMinAtAss` (shared with R-2c′).
-/

section AssCollapse

/-- The two R-2a′ SPEC shapes coincide (via the §3 direction lemmas).
-/
theorem hgrDimEq_iff_hdimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimEqMinAtAss m K J ↔ UnmixednessAtLengthTwo.HdimGrMinAtAss m K J :=
  ⟨dimGrMin_of_grDimEqMin m K J, grDimEqMin_of_dimGrMin m K J⟩

/-- Goal-strength in `HgrDimEqMinAtAss` shape: R-2a′ holds iff
`HkerMinAtAss` holds (via the shape iff + `hdimGrMin_iff_hkerMin`).
-/
theorem hgrDimEq_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimEqMinAtAss m K J ↔ UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  (hgrDimEq_iff_hdimGrMin m K J).trans
    (UnmixednessAtLengthTwo.hdimGrMin_iff_hkerMin m K J)

/-- Per-`Q` unconditional instance at embedding dimension `0`.
-/
theorem hgrDimEq_embdim_zero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (he : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank = 0) :
    ringKrullDim (grRegular Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
  UnmixednessAtLengthTwo.hdimGrMinAtAss_d_zero m K J Q hQ rfl he

/-- Per-`Q` unconditional instance at embedding dimension `1`.
-/
theorem hgrDimEq_embdim_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (he : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank = 1) :
    ringKrullDim (grRegular Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
  UnmixednessAtLengthTwo.hdimGrMinAtAss_d_one m K J Q hQ rfl he

end AssCollapse

#print axioms hgrDimEq_iff_hdimGrMin
#print axioms hgrDimEq_iff_hkerMin
#print axioms hgrDimEq_embdim_zero
#print axioms hgrDimEq_embdim_one

/-! ## §6. Supply-chain wiring: `HdimEqMinAtAss` at `d ≥ 2` closes on the crux

Preparatory wiring so `HdimEqMinAtAss` at `d ≥ 2` (hence rb-1) closes
automatically — by a single `exact` — once any crux form proves (R-2c′
closed §§1–2 conditional-on-crux; live R-2a′). All forward corollaries consume the `hwitMin` /
`grDimEq` masters (§3/§3b) plus `UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin`; the
backward lanes close the equivalence ring via `hkerMinAtAss_of_hdimEqMin` +
`hdimGrMin_iff_hkerMin`, so every residual below is mutually equivalent and
no crux form can land without discharging the rest.

* Forward (crux → `hmult`/`hdimEq`): `hmultMin_of_hwitMin`,
  `hmultMin_of_dimGrMin`, `hmultMin_of_hkerMin`, `hdimEqMin_of_hwitMin`,
  `hdimEqMin_of_dimGrMin`, `hdimEqMin_of_hkerMin`.
* Backward (`hmult`/`hdimEq` → crux): `grDimEqMin_of_hdimEqMin`,
  `grDimEqMin_of_hmultMin`, `hmultMin_of_hdimEqMin`,
  `hwitMin_of_hdimEqMin`, `hwitMin_of_hmultMin`.
* Iff ring: `hmultMin_iff_grDimEqMin`, `hdimEqMin_iff_grDimEqMin`,
  `hdimEqMin_iff_hmultMin`, `hwitMin_iff_hmultMin`, `hdimEqMin_iff_hkerMin`.
* Kernel auto-close: `hkerMin_of_grDimEq`, `hkerMin_of_hwitMin`,
  `hkerMin_of_hmultMin`.
* Rb-1 auto-close: `hunmixedTwo_of_hmultMin`, `hunmixedTwo_of_hwitMin`,
  `hunmixedTwo_of_hdimEqMin` (thin alias over
  `hunmixed_two_forall_of_hdimEqMin` for a uniform `hunmixedTwo_of_*` family).
* Per-`(Q, d)` `d ≥ 2` instances in exact hypothesis shape:
  `hmult_d_ge_two_of_hwitMin`, `hdimEq_d_ge_two_of_hwitMin`,
  `hdimEq_d_ge_two_of_grDimEq`, `hdimEq_d_ge_two_of_hmultMin`.

Status: forward/backward/kernel/rb-1/per-prime conditional-exact on the named
crux input (one-line compositions of §§1–5 + `UnmixednessAtLengthTwo` masters); iffs
unconditional.
-/

section SupplyChain

/-- `HmultMinAtAss` from the witness remainder (via `grDimEqMin_of_hwitMin`).

Conditional on exactly `[hwit]`. -/
theorem hmultMin_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  hmultMin_of_grDimEq m K J (grDimEqMin_of_hwitMin m K J hwit)

/-- `HmultMinAtAss` from R-2a′ in `HdimGrMinAtAss` shape.

Conditional on exactly `[hdim]`. -/
theorem hmultMin_of_dimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdim : UnmixednessAtLengthTwo.HdimGrMinAtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  hmultMin_of_grDimEq m K J (grDimEqMin_of_dimGrMin m K J hdim)

/-- `HmultMinAtAss` from the kernel conclusion (via goal-strength).

Conditional on exactly `[hker]`. -/
theorem hmultMin_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  hmultMin_of_dimGrMin m K J
    ((UnmixednessAtLengthTwo.hdimGrMin_iff_hkerMin m K J).mpr hker)

/-- `HdimEqMinAtAss` from the witness remainder: the auto-close corollary —
once `HwitMinAtAss` proves, `HdimEqMinAtAss` at `d ≥ 2` follows by one `exact`.

Conditional on exactly `[hwit]`. -/
theorem hdimEqMin_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  hdimEqMin_of_grDimEq m K J (grDimEqMin_of_hwitMin m K J hwit)

/-- `HdimEqMinAtAss` from R-2a′ in `HdimGrMinAtAss` shape.

Conditional on exactly `[hdim]`. -/
theorem hdimEqMin_of_dimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdim : UnmixednessAtLengthTwo.HdimGrMinAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  hdimEqMin_of_grDimEq m K J (grDimEqMin_of_dimGrMin m K J hdim)

/-- `HdimEqMinAtAss` from the kernel conclusion (via goal-strength).

Conditional on exactly `[hker]`. -/
theorem hdimEqMin_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  hdimEqMin_of_dimGrMin m K J
    ((UnmixednessAtLengthTwo.hdimGrMin_iff_hkerMin m K J).mpr hker)

/-- R-2a′ from `HdimEqMinAtAss`: `hdimEq → hker` (§3) `→ hdimGr`
(goal-strength) `→ grDimEq` (shape lemma). Closes the equivalence ring.

Conditional on exactly `[hdimEq]`. -/
theorem grDimEqMin_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    HgrDimEqMinAtAss m K J :=
  grDimEqMin_of_dimGrMin m K J
    ((UnmixednessAtLengthTwo.hdimGrMin_iff_hkerMin m K J).mpr
      (UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J hdimEq))

/-- R-2a′ from `HmultMinAtAss` (via `hdimEqMin_of_hmultMin`).

Conditional on exactly `[hmult]`. -/
theorem grDimEqMin_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss m K J) :
    HgrDimEqMinAtAss m K J :=
  grDimEqMin_of_hdimEqMin m K J
    (UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin m K J hmult)

/-- `HmultMinAtAss` from `HdimEqMinAtAss` (backward lane of the iff ring).

Conditional on exactly `[hdimEq]`. -/
theorem hmultMin_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  hmultMin_of_grDimEq m K J (grDimEqMin_of_hdimEqMin m K J hdimEq)

/-- `HwitMinAtAss` from `HdimEqMinAtAss` (backward lane of the iff ring).

Conditional on exactly `[hdimEq]`. -/
theorem hwitMin_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J :=
  hwitMin_of_grDimEq m K J (grDimEqMin_of_hdimEqMin m K J hdimEq)

/-- `HwitMinAtAss` from `HmultMinAtAss` (backward lane of the iff ring).

Conditional on exactly `[hmult]`. -/
theorem hwitMin_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss m K J) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J :=
  hwitMin_of_grDimEq m K J (grDimEqMin_of_hmultMin m K J hmult)

/-- `HmultMinAtAss` iff R-2a′ at Ass primes.
-/
theorem hmultMin_iff_grDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J ↔ HgrDimEqMinAtAss m K J :=
  ⟨grDimEqMin_of_hmultMin m K J, hmultMin_of_grDimEq m K J⟩

/-- `HdimEqMinAtAss` iff R-2a′ at Ass primes.
-/
theorem hdimEqMin_iff_grDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J ↔ HgrDimEqMinAtAss m K J :=
  ⟨grDimEqMin_of_hdimEqMin m K J, hdimEqMin_of_grDimEq m K J⟩

/-- `HdimEqMinAtAss` iff `HmultMinAtAss` (the `hsAssemble` equivalence,
Ass-level).
-/
theorem hdimEqMin_iff_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J ↔ UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  ⟨hmultMin_of_hdimEqMin m K J,
   UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin m K J⟩

/-- `HwitMinAtAss` iff `HmultMinAtAss`.
-/
theorem hwitMin_iff_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J ↔ UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  ⟨hmultMin_of_hwitMin m K J, hwitMin_of_hmultMin m K J⟩

/-- `HdimEqMinAtAss` iff `HkerMinAtAss` (goal-strength, both directions).
-/
theorem hdimEqMin_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J ↔ UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  ⟨UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J, hdimEqMin_of_hkerMin m K J⟩

/-- `HkerMinAtAss` from R-2a′ (kernel auto-close).

Conditional on exactly `[hgr]`. -/
theorem hkerMin_of_grDimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J
    (hdimEqMin_of_grDimEq m K J hgr)

/-- `HkerMinAtAss` from the witness remainder (kernel auto-close).

Conditional on exactly `[hwit]`. -/
theorem hkerMin_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J
    (hdimEqMin_of_hwitMin m K J hwit)

/-- `HkerMinAtAss` from multiplicity-nonvanishing (kernel auto-close).

Conditional on exactly `[hmult]`. -/
theorem hkerMin_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss m K J) :
    UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J
    (UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin m K J hmult)

/-- Rb-1 from multiplicity-nonvanishing: the §5 master fed with
`hdimEqMin_of_hmultMin`.

Conditional on exactly `[hmult]`. -/
theorem hunmixedTwo_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  UnmixednessAtLengthTwo.hunmixed_two_forall_of_hdimEqMin m K q hsucc J hJ
    (UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin m K J hmult)

/-- Rb-1 from the witness remainder: once `HwitMinAtAss` proves, rb-1 follows
by one `exact`.

Conditional on exactly `[hwit]`. -/
theorem hunmixedTwo_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  hunmixedTwo_of_grDimEq m K q hsucc J hJ
    (grDimEqMin_of_hwitMin m K J hwit)

/-- Rb-1 from `HdimEqMinAtAss` (thin alias over
`hunmixed_two_forall_of_hdimEqMin` for a uniform `hunmixedTwo_of_*` family).

Conditional on exactly `[hdimEq]`. -/
theorem hunmixedTwo_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  UnmixednessAtLengthTwo.hunmixed_two_forall_of_hdimEqMin m K q hsucc J hJ hdimEq

/-- Per-`(Q, d)` `hmult` conclusion at `d ≥ 2` from Ass-level witness data,
in exact `HmultMinAtAss` shape.

Conditional on exactly `[hwit]`. -/
theorem hmult_d_ge_two_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hd2 : 2 ≤ d) :
    ¬ seqDiff (d - 1) (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
  hmultMin_of_hwitMin m K J hwit Q hQ hdmin hd2

/-- Per-`(Q, d)` `hdimEq` conclusion at `d ≥ 2` from Ass-level witness data,
in exact KerAssemble-hyp shape.

Conditional on exactly `[hwit]`. -/
theorem hdimEq_d_ge_two_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hd2 : 2 ≤ d)
    (Qw : ℚ[X]) (hle : Qw.natDegree ≤ d - 1)
    (hag : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Qw) :
    Qw.natDegree = d - 1 :=
  hdimEqMin_of_hwitMin m K J hwit Q hQ hdmin hd2 Qw hle hag

/-- Per-`(Q, d)` `hdimEq` conclusion at `d ≥ 2` from the R-2a′ remainder, in
exact KerAssemble-hyp shape.

Conditional on exactly `[hgr]`. -/
theorem hdimEq_d_ge_two_of_grDimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hd2 : 2 ≤ d)
    (Qw : ℚ[X]) (hle : Qw.natDegree ≤ d - 1)
    (hag : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Qw) :
    Qw.natDegree = d - 1 :=
  hdimEqMin_of_grDimEq m K J hgr Q hQ hdmin hd2 Qw hle hag

/-- Per-`(Q, d)` `hdimEq` conclusion at `d ≥ 2` from multiplicity-nonvanishing,
in exact KerAssemble-hyp shape.

Conditional on exactly `[hmult]`. -/
theorem hdimEq_d_ge_two_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hd2 : 2 ≤ d)
    (Qw : ℚ[X]) (hle : Qw.natDegree ≤ d - 1)
    (hag : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Qw) :
    Qw.natDegree = d - 1 :=
  UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin m K J hmult Q hQ hdmin hd2 Qw hle hag

end SupplyChain

#print axioms hmultMin_of_hwitMin
#print axioms hmultMin_of_dimGrMin
#print axioms hmultMin_of_hkerMin
#print axioms hdimEqMin_of_hwitMin
#print axioms hdimEqMin_of_dimGrMin
#print axioms hdimEqMin_of_hkerMin
#print axioms grDimEqMin_of_hdimEqMin
#print axioms grDimEqMin_of_hmultMin
#print axioms hmultMin_of_hdimEqMin
#print axioms hwitMin_of_hdimEqMin
#print axioms hwitMin_of_hmultMin
#print axioms hmultMin_iff_grDimEqMin
#print axioms hdimEqMin_iff_grDimEqMin
#print axioms hdimEqMin_iff_hmultMin
#print axioms hwitMin_iff_hmultMin
#print axioms hdimEqMin_iff_hkerMin
#print axioms hkerMin_of_grDimEq
#print axioms hkerMin_of_hwitMin
#print axioms hkerMin_of_hmultMin
#print axioms hunmixedTwo_of_hmultMin
#print axioms hunmixedTwo_of_hwitMin
#print axioms hunmixedTwo_of_hdimEqMin
#print axioms hmult_d_ge_two_of_hwitMin
#print axioms hdimEq_d_ge_two_of_hwitMin
#print axioms hdimEq_d_ge_two_of_grDimEq
#print axioms hdimEq_d_ge_two_of_hmultMin

/-! ## §7. Witness skeleton + high-relations route (S2)

Maximal unconditional partial toward `HwitMinAtAss` (the joint R-2a′ + R-2c′ +
`HdimEq` witness at minimal `d ≥ 2`), plus the conditional-exact full witness
on the high-degree homogeneous-relations residual.

* `HnoHomRelHighMinAtAss` (SPEC): per-Ass-prime, per-minimal-family
  `KwitNoHomRelHigh` — no nonzero homogeneous `ker` relation of degree `≥ 2`
  (degree `0` dies by the `Hq 0 ≠ 0` lower bound, degree `1` by minimality).
* `hwitMin_skeleton_of_minimal` (unconditional): the witness minus its two
  hard conjuncts — minimal sop data `(g, hgen)`, `H := 0` with `hF`, and the
  weak witness `hFq` (Hilbert–Serre existence + domain degree bound).
  Remainder: `coeff (d - 1) ≠ 0` and the `hdrop` drop data.
* `hwitMin_of_noHomRelHighMin` (conditional-exact on `[hHigh]`): the full
  `HwitMinAtAss` tuple — `hmult` from the High residual, `hwit` by narrowing,
  `hdrop` vacuous on `ker = ⊥`.
* `noHomRelHighMin_of_hwitMin` + `hwitMin_iff_noHomRelHighMin`
  (unconditional iff): the High residual is exact, not just sufficient.
* `grDimEqMin_of_noHomRelHighMin`, `hmultMin_of_noHomRelHighMin`,
  `hdimEqMin_of_noHomRelHighMin`, `hkerMin_of_noHomRelHighMin`
  (conditional-exact on `[hHigh]`): one-line §6 supply adapters, so the
  High residual auto-closes every crux conclusion by a single `exact`.
* `hunmixedTwo_of_noHomRelHighMin` (conditional-exact on `[hHigh]`): rb-1
  jointly — R-2a′, R-2c′, `HdimEq` all discharge on the one residual.

Status: as marked per theorem; partial overall
(`HnoHomRelHighMinAtAss` open — the exact minimal remainder).
-/

section WitnessHigh

/-- Per-Ass-prime high-degree no-relations residual at minimal `d`: every
minimal spanning family admits no nonzero homogeneous `ker` relation of
degree `≥ 2`.

Specification (Prop address for the minimal high-relations hypothesis). -/
def HnoHomRelHighMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank),
      KwitNoHomRelHigh Q d g hgen

/-- Unconditional witness skeleton at minimal `d ≥ 2`: minimal sop data
`(g, hgen)`, `H := 0` with `hF`, and the weak witness `hFq`. The two hard
conjuncts (`coeff ≠ 0`, `hdrop` drop data) are the precise remainder.
-/
theorem hwitMin_skeleton_of_minimal (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hd2 : 2 ≤ d) :
    ∃ (g : Fin d → Localization.AtPrime Q),
      ∃ (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
        ∃ (H : ℕ → ℕ),
          IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1) ∧
          IsPolyGrowth (fun n => ((multQuotHilbert
            (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
            (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) : ℕ) : ℚ))
            (d - 1) := by
  obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
  have heq : d = d' := hdmin.trans hd'.symm
  subst heq
  refine ⟨g, hgen, (fun _ => 0), ?hF, kwit_hFq Q d g hgen (by omega)⟩
  · refine ⟨0, by simp, Filter.Eventually.of_forall (fun n => by simp [evalFun])⟩

/-- `HwitMinAtAss` from the high-relations residual: per-`Q` minimal spanning
data identifies `d` with `embdim`; High gives `hmult`, narrowing gives
`hwit`, and `hdrop` is vacuous on `ker = ⊥`.

Conditional on exactly `[hHigh]`. -/
theorem hwitMin_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J := by
  intro Q _ hQ d hdmin hd2
  obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
  have heq : d = d' := hdmin.trans hd'.symm
  subst heq
  have hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hd'
  have hmult := kwit_hmult_of_minimal_high Q d g hgen hd2 hmin
    (hHigh Q hQ g hgen hd')
  have hker : RingHom.ker (polySurjResidue Q d g hgen) = ⊥ :=
    kwit_ker_eq_bot_of_hmult Q d g hgen hd2 hmult
  refine ⟨g, hgen, (fun _ => 0), ?hF, ?hwit, ?hdrop⟩
  · refine ⟨0, by simp, Filter.Eventually.of_forall (fun n => by simp [evalFun])⟩
  · exact kwit_hwit_of_hmult Q d g hgen (by omega) hmult
  · intro hne
    exact absurd hker hne

/-- High residual from the witness (via `hwitMin_iff_hkerMin`): the witness
gives `ker = ⊥` for every minimal family, killing every homogeneous relation.
-/
theorem noHomRelHighMin_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin y n hym _ _
  have hker : RingHom.ker (polySurjResidue Q d g hgen) = ⊥ :=
    (hwitMin_iff_hkerMin m K J).mp hwit Q hQ g hgen hdmin
  rw [hker] at hym
  exact (Submodule.mem_bot _).mp hym

/-- `HwitMinAtAss ↔ High-min`: the high-relations remainder is exact.
-/
theorem hwitMin_iff_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HwitMinAtAss m K J ↔ HnoHomRelHighMinAtAss m K J :=
  ⟨noHomRelHighMin_of_hwitMin m K J, hwitMin_of_noHomRelHighMin m K J⟩

/-- R-2a′ from the high-relations residual (via `hwitMin_of_noHomRelHighMin`).

Conditional on exactly `[hHigh]`. -/
theorem grDimEqMin_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    HgrDimEqMinAtAss m K J :=
  grDimEqMin_of_hwitMin m K J (hwitMin_of_noHomRelHighMin m K J hHigh)

/-- `HmultMinAtAss` from the high-relations residual (auto-close).

Conditional on exactly `[hHigh]`. -/
theorem hmultMin_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    UnmixednessAtLengthTwo.HmultMinAtAss m K J :=
  hmultMin_of_hwitMin m K J (hwitMin_of_noHomRelHighMin m K J hHigh)

/-- `HdimEqMinAtAss` from the high-relations residual (auto-close).

Conditional on exactly `[hHigh]`. -/
theorem hdimEqMin_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  hdimEqMin_of_hwitMin m K J (hwitMin_of_noHomRelHighMin m K J hHigh)

/-- `HkerMinAtAss` from the high-relations residual (kernel auto-close).

Conditional on exactly `[hHigh]`. -/
theorem hkerMin_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  hkerMin_of_hwitMin m K J (hwitMin_of_noHomRelHighMin m K J hHigh)

/-- Rb-1 from the high-relations residual: R-2a′, R-2c′, `HdimEq` discharge
jointly on the one remainder.

Conditional on exactly `[hHigh]`. -/
theorem hunmixedTwo_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    UnmixednessAtLengthTwo.HunmixedTwoProp m K q hsucc J hJ :=
  hunmixedTwo_of_grDimEq m K q hsucc J hJ
    (grDimEqMin_of_hwitMin m K J (hwitMin_of_noHomRelHighMin m K J hHigh))

end WitnessHigh

#print axioms hwitMin_skeleton_of_minimal
#print axioms hwitMin_of_noHomRelHighMin
#print axioms noHomRelHighMin_of_hwitMin
#print axioms hwitMin_iff_noHomRelHighMin
#print axioms grDimEqMin_of_noHomRelHighMin
#print axioms hmultMin_of_noHomRelHighMin
#print axioms hdimEqMin_of_noHomRelHighMin
#print axioms hkerMin_of_noHomRelHighMin
#print axioms hunmixedTwo_of_noHomRelHighMin

end DimensionToMultiplicity
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
