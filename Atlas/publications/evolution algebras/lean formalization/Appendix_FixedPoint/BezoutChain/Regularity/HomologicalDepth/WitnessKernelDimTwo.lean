/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# P1: crux antecedent at `d = 2` — direct attack (smallest open case)

Direct attack on the crux antecedent `HwitMinAtAss` at `d = 2` (embdim
exactly 2), the smallest open case (`d = 0` via
`hsAssemble_ker_eq_bot_zero`, `d = 1` via `ker_chain_ker_eq_bot_one`).

verdict (machine-checked, §§1–4): an unconditional proof of the `d = 2`
antecedent is OUT of reach below `ker = ⊥` strength along every uniform
route — the `d = 2` restriction inherits the full iff-ring (§2: witness
⟺ ker ⟺ dim ⟺ hle at embdim 2, all unconditional). The `d = 1` closure
does not generalize (one-variable monomial classification
`ker_chain_fin1_homog_eq` has no two-variable analogue in-tree), and the
`d = 2`-specific analytic routes (bounded quotient Hilbert function +
eventual polynomiality; UFD structure of `κ[X, Y]`) each need theory
absent from Mathlib v4.34.0 or hypotheses exactly as strong as the goal
(§5). This file therefore proves the maximal supporting package:

* (§1) `d = 2` SPECs (new Prop addresses): `HwitD2AtAss` (witness tuple
  at embdim 2, in exact `mult_hle_gr_of_witnessHyp` shape with `d := 2`),
  `HkerD2AtAss` (`ker = ⊥` per minimal family at embdim 2),
  `HdimGrD2AtAss` (`dim gr = 2` at embdim 2), `HhleD2AtAss` (`hle` at
  embdim 2).
* (§2) The `d = 2` ring, unconditional (iffs): every `d = 2` residual is
  explicitly iff-linked — `hwitD2_iff_hkerD2`, `hdimGrD2_iff_hkerD2`,
  `hhleD2_iff_hkerD2` — plus the projections showing each `d = 2` form
  is weaker than its uniform parent (`hwitD2_of_hwitMin`,
  `hkerD2_of_hkerMin`, `hdimGrD2_of_hdimGrMin`, `hhleD2_of_hhleMin`).
* (§3) Per-prime `d = 2` conditional forms: `ker = ⊥`, `hmult`, and
  `dim gr = spanFinrank` at embdim 2 from explicit/`HwitD2AtAss` witness
  data, plus the lower bound at embdim 2 — the `d = 2` analogues of the
  GrDimEq §4 instances (`grDimLower_embdim_zero/one`,
  `hgrDimEq_embdim_zero/one`), conditional-exact on the `d = 2` witness.
* (§4) Unconditional `d = 2` base from minimality alone: `Low` at `d = 2`
  (`witKerD2_low_of_minimal`), pointwise nonvanishing
  (`witKerD2_quotHilbert_ne_zero`), and the sharp per-triple exactness
  `High ⟺ ker = ⊥` given `hmin` (`witKerD2_ker_iff_high_of_minimal`)
  and `High ⟺ hle` (`witKerD2_hle_iff_high_of_minimal`) — the only
  thing between minimality and `ker = ⊥` at `d = 2` is `High`
  (degree-`≥ 2` relations).
* (§5, doc-only) Precise remainder register: the verbatim open `d = 2`
  item, why it is minimal and exact, and the scoped `d = 2`-specific
  routes (a future `d = 2`-only proof would not be circular: it would
  not imply `d ≥ 3`, escaping the uniformity-based goal-strength
  verdicts).

## Scope coordination (no duplication)

* `DimensionToMultiplicity.lean` / `WitnessKernelMain.lean` / `WitnessKernelCrux.lean`:
  own the uniform (`d ≥ 2`) implication and iff-ring. Consumed only
  (idea-level; this file re-proves nothing uniform).
* `MultiplicityNonvanishing.lean` §§14/16/17: own the per-triple engine
  (`mult_ker_eq_bot_unconditional_of_witnessHyp`,
  `mult_hmult_unconditional_of_witnessHyp`,
  `mult_hle_gr_of_witnessHyp`, `mult_hle_gr_iff_ker_eq_bot`,
  `mult_dim_gr_eq_of_gr_lowerBound`,
  `mult_ringKrullDim_atPrime_eq_of_minimal`). Consumed only.
* `GradedDimEq.lean` §3/§4: owns `grDimLower_of_grDimEq` and the
  `d ≤ 1` instances. Consumed only (§3 mirrors the §4 shape at `d = 2`).
* `HighRelationsLowerBound.lean` §2: owns `HhleMinAtAss`. Consumed only
  (projection target).
* `HilbertWitnessNarrowing.lean`: owns the domain-theory masters
  (`kwit_hwit_of_hmult`, `kwit_hmult_of_ker_eq_bot`) and pointwise
  nonvanishing (`kwit_quotHilbert_ne_zero_of_minimal`). Consumed only
  (fully qualified — `KwitNoHomRelHigh` would clash with the
  HomRelHigh def).
* `HighHomogeneousRelations.lean` §§2/7: own `Low`/`High` and pair exactness.
  consumed only.
* `Geometry/UnmixednessAtLengthTwo.lean`: owns the uniform SPECs. Consumed only
  (projection sources).

## Status

* §1: SPEC (new Prop addresses).
* §2: iffs unconditional; projections unconditional.
* §3: conditional-exact on the named `d = 2` witness input.
* §4: unconditional (conditional-form on `[hmin]` where stated; the
  `ker → High` direction needs nothing).
* Overall: partial toward the `d = 2` crux antecedent
  (remainder = the `d = 2` witness tuple / `High` at `d = 2`, §5).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace WitnessKernelDimTwo

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighRelationsLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. `d = 2` SPECs -/

/-- Witness antecedent at embdim exactly 2: per `Q ∈ Ass(R ⧸ J)` with
`spanFinrank 𝔪(R_Q) = 2`, some minimal spanning family admits
`(H, hF, hwit, hdrop)` in the exact
`mult_hle_gr_of_witnessHyp` shape with `d := 2` (so `e = 2 - 1`).

Specification (Prop address for the `d = 2` Hilbert-witness hypothesis). -/
def HwitD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ∃ (g : Fin 2 → Localization.AtPrime Q),
        ∃ (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
          ∃ (H : ℕ → ℕ),
            IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (2 - 1) ∧
            (∃ Pwit : ℚ[X], Pwit.natDegree ≤ 2 - 1 ∧
              (fun n => ((multQuotHilbert
                (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
                (RingHom.ker (polySurjResidue Q 2 g hgen))
                (n + 1) : ℕ) : ℚ))
                =ᶠ[Filter.atTop] evalFun Pwit ∧
              Pwit.coeff (2 - 1) ≠ 0) ∧
            (RingHom.ker (polySurjResidue Q 2 g hgen) ≠ ⊥ →
              ∃ Jloc : Ideal (Localization.AtPrime Q),
                (∀ Qm ∈ Jloc.minimalPrimes,
                  Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
                (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
                  (Localization.AtPrime Q ⧸ Jloc),
                  ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
                (∀ n, multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
                  (RingHom.ker (polySurjResidue Q 2 g hgen))
                  (n + 1) + H n = H (n + 1)) ∧
                IsPolyGrowth (fun n => ((multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
                  (RingHom.ker (polySurjResidue Q 2 g hgen))
                  (n + 1) : ℕ) : ℚ)) (2 - 1))

/-- `ker = ⊥` per minimal family at embdim exactly 2 (the `d = 2`
restriction of `HkerMinAtAss`).

Specification (Prop address for the `d = 2` kernel hypothesis). -/
def HkerD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (g : Fin 2 → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      RingHom.ker (polySurjResidue Q 2 g hgen) = ⊥

/-- `dim gr = 2` at embdim exactly 2 (the `d = 2` restriction of
`HdimGrMinAtAss`).

Specification (Prop address for the `d = 2` gr-dimension hypothesis). -/
def HdimGrD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ringKrullDim (grRegular Q) = 2

/-- `hle` per minimal family at embdim exactly 2 (the `d = 2`
restriction of `HhleMinAtAss`).

Specification (Prop address for the `d = 2` lower-bound hypothesis). -/
def HhleD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (g : Fin 2 → Localization.AtPrime Q)
      (_hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      2 ≤ ringKrullDim (grRegular Q)

/-! ## §2. The `d = 2` ring: witness ⟺ ker ⟺ dim ⟺ hle -/

/-- `HkerD2AtAss` from the `d = 2` witness: the witnessed family feeds
the §17 narrowing (`hle`), and the §17 collapse upgrades `hle` to
`ker = ⊥` for every minimal family.

Conditional on exactly `[hwit]`. -/
theorem hkerD2_of_hwitD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨g', hgen', H, hF, hwitQ, hdrop⟩ := hwit Q hQ hemb
  have hle : 2 ≤ ringKrullDim (grRegular Q) :=
    mult_hle_gr_of_witnessHyp Q 2 g' hgen' H (by omega) hF hwitQ hdrop
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

/-- `HwitD2AtAss` from `HkerD2AtAss`: per-`Q` minimal spanning data
(`grlift_sop_exists`) identifies the sop `d` with `2`; `ker = ⊥` on
that family yields `hwit` by domain theory
(`kwit_hwit_of_hmult` + `kwit_hmult_of_ker_eq_bot`). `H := 0` supplies
`hF`; `hdrop` is vacuous on `ker = ⊥`.

Conditional on exactly `[hker]`. -/
theorem hwitD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HwitD2AtAss m K J := by
  intro Q _ hQ hemb
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hkerQ : RingHom.ker (polySurjResidue Q 2 g hgen) = ⊥ :=
    hker Q hQ g hgen hemb
  refine ⟨g, hgen, (fun _ => 0), ?hF, ?hwit, ?hdrop⟩
  · exact ⟨0, by simp, Filter.Eventually.of_forall (fun n => by simp [evalFun])⟩
  · exact HilbertWitnessNarrowing.kwit_hwit_of_hmult Q 2 g hgen (by omega)
      (HilbertWitnessNarrowing.kwit_hmult_of_ker_eq_bot Q 2 g hgen (by omega) hkerQ)
  · intro hne
    exact absurd hkerQ hne

/-- The `d = 2` witness is exactly `ker = ⊥` strength at embdim 2.
-/
theorem hwitD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HwitD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨hkerD2_of_hwitD2 m K J, hwitD2_of_hkerD2 m K J⟩

/-- `HkerD2AtAss` from `dim gr = 2`: the equality is `hle`, and the
§17 collapse closes the kernel per family.

Conditional on exactly `[hdim]`. -/
theorem hkerD2_of_hdimGrD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdim : HdimGrD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  have hdimGr := hdim Q hQ hemb
  have hle : 2 ≤ ringKrullDim (grRegular Q) := by rw [hdimGr]
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

/-- `dim gr = 2` from `HkerD2AtAss`: per-`Q` minimal spanning data
carries `ker = ⊥`, hence `hle`, hence the equality by the
unconditional upper bound.

Conditional on exactly `[hker]`. -/
theorem hdimGrD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HdimGrD2AtAss m K J := by
  intro Q _ hQ hemb
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hle : 2 ≤ ringKrullDim (grRegular Q) :=
    mult_hle_gr_of_ker_eq_bot Q 2 g hgen (hker Q hQ g hgen hemb)
  exact mult_dim_gr_eq_of_gr_lowerBound Q 2 g hgen hle

/-- `dim gr = 2` is exactly `ker = ⊥` strength at embdim 2.
-/
theorem hdimGrD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimGrD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨hkerD2_of_hdimGrD2 m K J, hdimGrD2_of_hkerD2 m K J⟩

/-- `HhleD2AtAss` from `HkerD2AtAss` (via `S ⧸ ⊥ ≃+* S`).

Conditional on exactly `[hker]`. -/
theorem hhleD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HhleD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  exact mult_hle_gr_of_ker_eq_bot Q 2 g hgen (hker Q hQ g hgen hemb)

/-- `HkerD2AtAss` from `HhleD2AtAss` (the §17 chain collapse).

Conditional on exactly `[hhle]`. -/
theorem hkerD2_of_hhleD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hhle : HhleD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp (hhle Q hQ g hgen hemb)

/-- Minimal `hle` at `d = 2` is exactly `ker = ⊥` strength.
-/
theorem hhleD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhleD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨hkerD2_of_hhleD2 m K J, hhleD2_of_hkerD2 m K J⟩

/-- The uniform witness projects to the `d = 2` witness (instantiate
`d := 2`).
-/
theorem hwitD2_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitMinAtAss m K J) :
    HwitD2AtAss m K J := by
  intro Q _ hQ hemb
  exact hwit Q hQ hemb (le_refl 2)

/-- The uniform kernel hypothesis projects to embdim 2.
-/
theorem hkerD2_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerMinAtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  exact hker Q hQ g hgen hemb

/-- The uniform `dim gr` hypothesis projects to embdim 2.
-/
theorem hdimGrD2_of_hdimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdim : HdimGrMinAtAss m K J) :
    HdimGrD2AtAss m K J := by
  intro Q _ hQ hemb
  exact hdim Q hQ hemb

/-- The uniform minimal `hle` projects to embdim 2.
-/
theorem hhleD2_of_hhleMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hhle : HhleMinAtAss m K J) :
    HhleD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  exact hhle Q hQ g hgen hemb

#print axioms hkerD2_of_hwitD2
#print axioms hwitD2_of_hkerD2
#print axioms hwitD2_iff_hkerD2
#print axioms hkerD2_of_hdimGrD2
#print axioms hdimGrD2_of_hkerD2
#print axioms hdimGrD2_iff_hkerD2
#print axioms hhleD2_of_hkerD2
#print axioms hkerD2_of_hhleD2
#print axioms hhleD2_iff_hkerD2
#print axioms hwitD2_of_hwitMin
#print axioms hkerD2_of_hkerMin
#print axioms hdimGrD2_of_hdimGrMin
#print axioms hhleD2_of_hhleMin

/-! ## §3. Per-prime `d = 2` conditional forms -/

/-- Per-prime `ker = ⊥` at `d = 2` from an explicit witness tuple in
exact `HwitD2AtAss`-tuple shape (the Multiplicity §14 master at
`d := 2`).

Conditional on exactly `[hF, hwit, hdrop]`. -/
theorem witKerD2_ker_of_witData_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (H : ℕ → ℕ)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (2 - 1))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ 2 - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
          (RingHom.ker (polySurjResidue Q 2 g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (2 - 1) ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue Q 2 g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime Q),
        (∀ Qm ∈ J.minimalPrimes,
          Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
          (Localization.AtPrime Q ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q))
          2 (RingHom.ker (polySurjResidue Q 2 g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
          (RingHom.ker (polySurjResidue Q 2 g hgen)) (n + 1) : ℕ) : ℚ))
          (2 - 1)) :
    RingHom.ker (polySurjResidue Q 2 g hgen) = ⊥ :=
  mult_ker_eq_bot_unconditional_of_witnessHyp Q 2 g hgen H (by omega) hF
    hwit hdrop

/-- Per-prime `hmult` at `d = 2` (first-difference nonvanishing of the
shifted quotient Hilbert function) from the `hwit` conjunct alone.

Conditional on exactly `[hwit]`. -/
theorem witKerD2_hmult_of_witData_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ 2 - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
          (RingHom.ker (polySurjResidue Q 2 g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (2 - 1) ≠ 0) :
    ¬ seqDiff (2 - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
        (RingHom.ker (polySurjResidue Q 2 g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
  mult_hmult_unconditional_of_witnessHyp Q 2 g hgen hwit

/-- `dim gr = spanFinrank` at embdim 2 from `HwitD2AtAss`: the `d = 2`
analogue of the GrDimEq §4 instances `hgrDimEq_embdim_zero/one`.

Conditional on exactly `[hwit]`. -/
theorem witKerD2_grDimEq_embdim_two_of_hwitD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ringKrullDim (grRegular Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank := by
  obtain ⟨g, hgen, H, hF, hwitQ, hdrop⟩ := hwit Q hQ hemb
  have hle : 2 ≤ ringKrullDim (grRegular Q) :=
    mult_hle_gr_of_witnessHyp Q 2 g hgen H (by omega) hF hwitQ hdrop
  have hdim := mult_dim_gr_eq_of_gr_lowerBound Q 2 g hgen hle
  rw [hdim]
  exact_mod_cast hemb

/-- Lower bound at embdim 2 from `HwitD2AtAss`: the `d = 2` analogue of
the GrDimEq §4 instances `grDimLower_embdim_zero/one`.

Conditional on exactly `[hwit]`. -/
theorem witKerD2_lower_embdim_two_of_hwitD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) :=
  grDimLower_of_grDimEq Q
    (witKerD2_grDimEq_embdim_two_of_hwitD2 m K J hwit Q hQ hemb)

#print axioms witKerD2_ker_of_witData_atPrime
#print axioms witKerD2_hmult_of_witData_atPrime
#print axioms witKerD2_grDimEq_embdim_two_of_hwitD2
#print axioms witKerD2_lower_embdim_two_of_hwitD2

/-! ## §4. Unconditional `d = 2` base from minimality alone -/

/-- `Low` at `d = 2` from minimality (Q1 at `d := 2`): no nonzero
linear relation in `ker`.

Conditional on exactly `[hmin]`. -/
theorem witKerD2_low_of_minimal {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    KwitNoHomRelLow Q 2 g hgen :=
  kwitHigh_low_of_minimal Q 2 g hgen hmin

/-- Every quotient Hilbert value is nonzero at `d = 2` from minimality
(Nakayama chase at `d := 2`).

Conditional on exactly `[hmin]`. -/
theorem witKerD2_quotHilbert_ne_zero {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) (n : ℕ) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) n ≠ 0 :=
  HilbertWitnessNarrowing.kwit_quotHilbert_ne_zero_of_minimal Q 2 g hgen hmin
    (by omega) n

/-- `High` at `d = 2` from `ker = ⊥`: a trivial kernel contains no
nonzero relation of any degree. Needs nothing (no `hmin`).
-/
theorem witKerD2_high_of_ker {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hker : RingHom.ker (polySurjResidue Q 2 g hgen) = ⊥) :
    KwitNoHomRelHigh Q 2 g hgen := by
  intro y n hym _ _
  rw [hker] at hym
  exact (Submodule.mem_bot _).mp hym

/-- Sharp per-triple exactness at `d = 2`: given `hmin`, `High` holds
iff `ker = ⊥`. Forward is pair exactness (§2) with `Low` discharged by
minimality; backward is `witKerD2_high_of_ker`. The only thing between
minimality and `ker = ⊥` at `d = 2` is `High`.
-/
theorem witKerD2_ker_iff_high_of_minimal {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    KwitNoHomRelHigh Q 2 g hgen ↔
      RingHom.ker (polySurjResidue Q 2 g hgen) = ⊥ := by
  constructor
  · intro hhigh
    exact kwitHigh_ker_eq_bot_of_low_high Q 2 g hgen (by omega)
      (kwitHigh_low_of_minimal Q 2 g hgen hmin) hhigh
  · exact witKerD2_high_of_ker Q g hgen

/-- `High ⟺ hle` at `d = 2` given `hmin` (via the sharp exactness plus
the §17 collapse).
-/
theorem witKerD2_hle_iff_high_of_minimal {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    KwitNoHomRelHigh Q 2 g hgen ↔ 2 ≤ ringKrullDim (grRegular Q) :=
  (witKerD2_ker_iff_high_of_minimal Q g hgen hmin).trans
    (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).symm

#print axioms witKerD2_low_of_minimal
#print axioms witKerD2_quotHilbert_ne_zero
#print axioms witKerD2_high_of_ker
#print axioms witKerD2_ker_iff_high_of_minimal
#print axioms witKerD2_hle_iff_high_of_minimal

/-! ## §5. Remainder register (doc-only)

Minimal non-circular remainder (verbatim): `HwitD2AtAss`, i.e. per
`Q ∈ Ass(R ⧸ J)` at embdim exactly 2, some minimal spanning family
`(g, hgen)` admits `(H, hF, hwit, hdrop)` in the exact
`mult_hle_gr_of_witnessHyp` shape with `d := 2` (so `e = 2 - 1`).
Equivalently (all unconditional iffs, §2 + §4): `HkerD2AtAss`,
`HdimGrD2AtAss`, `HhleD2AtAss`, or per-triple `KwitNoHomRelHigh` at
`d = 2` given `hmin`.

Why the remainder is minimal and exact (all machine-checked):

* The §2 hub iffs (`hwitD2_iff_hkerD2`, `hdimGrD2_iff_hkerD2`,
  `hhleD2_iff_hkerD2`) show every `d = 2` residual is exactly `ker = ⊥`
  strength at embdim 2 — no unconditional proof of any of them exists
  below the strength of `ker = ⊥` itself at `d = 2` (which is what the
  §10 master produces from `hmult + hdrop`, closing the documented
  `hle → dim = 2 → hwit → hmult → ker = ⊥ → hle` cycle at `d = 2`).
* §4 shows the `d = 2` kernel is exactly `High` given `hmin`
  (`witKerD2_ker_iff_high_of_minimal`): `Low` is free from minimality,
  so degree-`≥ 2` relations are the precise per-triple remainder.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth /
  polynomiality fact to prove the §§2–4 masters; the only undischarged
  input is the witness data itself.

Why the `d = 1` closure does not generalize: `ker_chain_ker_eq_bot_one`
rests on the one-variable monomial classification
(`ker_chain_fin1_homog_eq`: every homogeneous `N`-form in one variable
is `c·X^N`), which forces a nonzero homogeneous kernel element to kill
all large quotient pieces. In two variables the degree-`N` piece has
dimension `N + 1` with no such classification in-tree.

`d = 2`-specific routes (all surveyed, none duplicated; a `d = 2`-only
proof would not be circular since it would not imply `d ≥ 3`):

* Bounded-quotient route: a nonzero homogeneous `f ∈ ker` of degree `i`
  forces `Hq(N) ≤ i` for `N ≥ i` (multiples `f·S_{N-i}` fill all but
  `i` dimensions). With eventual polynomiality of `Hq` (Hilbert–Serre
  at `d = 2`, absent from Mathlib) this gives `seqDiff 1 Hq =ᶠ 0`,
  i.e. `¬hmult` — but closing `ker = ⊥` needs `hmult`
  unconditionally, which is `ker = ⊥` strength itself
  (`kwit_ker_eq_bot_of_hmult` + `kwit_hmult_of_ker_eq_bot`). Blocked on
  `hmult`-without-`High`.
* UFD route: in `κ[X, Y]` a nonzero homogeneous prime is principal or
  maximal; `Low` rules out maximal and linear principals. But `ker`
  prime needs `gr` a domain (`KwitKerIsPrime`), which is what the §10
  master produces, not an input. Circular.
* Direct chain route: exhibit a length-2 prime chain in `gr`. Needs
  prime lifting above `ker` in `κ[X, Y]` (minimal primes over `ker`
  plus strict growth), i.e. catenary-type theory absent from Mathlib
  v4.34.0. Priced, not attempted.
* Next-cheapest analytic item (not attempted): pin `Hq(0) = 1` and
  `Hq(1) = 2` at `d = 2` from `Low` + the domain choose formula
  (`hsAssemble_domainHilbert_eq_choose`); two values do not yield
  eventual behavior, so this does not advance the crux.

Consumers: the §2 iffs let any future `d = 2` proof discharge every
`d = 2` residual by a single `exact`; the §3 per-prime forms supply
`ker = ⊥` / `dim gr = 2` / the lower bound at embdim 2 directly from
witness data; §4 supplies the unconditional `d = 2` base.
-/

end WitnessKernelDimTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

