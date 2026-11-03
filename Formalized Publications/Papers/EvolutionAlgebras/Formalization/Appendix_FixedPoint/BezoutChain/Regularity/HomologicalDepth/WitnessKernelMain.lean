/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Q1: `HwitMin → ker = ⊥` main attack — crux-ring completion

Status of the target crux implication at the outset: the Ass-level form
`HwitMinAtAss → HkerMinAtAss` is already proved
(`hkerMin_of_hwitMin`, `DimensionToMultiplicity.lean`, via `hdimEqMin_of_hwitMin`
+ `hkerMinAtAss_of_hdimEqMin`), and every other crux conclusion auto-closes
on `[hwit]` / `[hHigh]` / `[hlower]` by one `exact` (DimToMult §§6–7, GrLower
§6, HighHleMin §§3–4, GrDimEq §3b). An unconditional proof of any crux form
is OUT of reach: each is iff-exact with `HkerMinAtAss` (goal strength), and
discharging `ker = ⊥` outright needs associated-graded dimension theory
(`dim gr = dim R` per Ass prime) absent from Mathlib v4.34.0. This file
therefore proves the maximal supporting package:

* (§1) Crux-ring completion, unconditional (iffs): every residual is now
  explicitly iff-linked to the `HkerMinAtAss` hub —
  `hmultMin_iff_hkerMin`, `hhleMin_iff_hkerMin`,
  `hnoHomRelHighMin_iff_hkerMin` — plus the witness-spoke iffs
  `hwitMin_iff_hdimEqMin`, `hwitMin_iff_hdimGrMin`,
  `hmultMin_iff_hdimGrMin`, `hdimEqMin_iff_hdimGrMin`,
  `hhleMin_iff_hwitMin`, `hnoHomRelHighMin_iff_hmultMin`,
  `hnoHomRelHighMin_iff_hdimEqMin`. Any future crux proof now propagates to
  every residual by a single `exact` with no transitivity chase.
* (§2) Per-prime crux forms, unconditional (conditional-form on the named
  witness input): the `HwitMin → ker = ⊥` implication in exact per-prime
  shape — the lower bound from explicit witness data
  (`witKerCrux_lower_of_witData_atPrime`, the GrLower §5 "one `exact`" item),
  `dim gr = d` at `(Q, d)` from Ass-level witness data
  (`witKerCrux_dimGr_of_hwitMin_atPrime`), and the per-`Q` lower bound from
  Ass-level witness data (`witKerCrux_lower_of_hwitMin_atPrime`, `d ≤ 1`
  via the closed embdim instances). (`ker = ⊥` at the witnessed family is
  the sibling `WitnessKernelCrux` lane's `hwitKerCrux_hexists_of_hwitMin`,
  not restated here.)
* (§3, doc-only) Precise remainder register: the verbatim open item, why it
  is minimal and exact, and the scoped routes.

## Scope coordination (no duplication)

* `DimensionToMultiplicity.lean` §§3/3b/5/6/7: owns the `hwit`/`grDimEq`/`hker`
  masters and the supply-chain adapters. Consumed only.
* `GradedLowerBound.lean` §§1–2/6: owns the per-prime lower-bound remainder
  and the witness-route adapters. Consumed only.
* `HighRelationsLowerBound.lean` §§2–4: owns the `High ↔ hle ↔ lower` iffs.
  consumed only.
* `GradedDimEq.lean`: owns the upper half, the lower-bound SPEC, and the
  `d ≤ 1` instances. Consumed only.
* `MultiplicityNonvanishing.lean` §17: owns the witness-hyp masters
  (`mult_ker_eq_bot_unconditional_of_witnessHyp`,
  `mult_hle_gr_of_witnessHyp`). Consumed only.
* `Geometry/UnmixednessAtLengthTwo.lean`: owns the Ass-level SPECs. Consumed only.
* `WitnessKernelCrux.lean` (parallel Q1 lane, read-only, not
  imported): owns the joint one-shot discharge tuples and the ∃-ker
  factorization (`HexistsKerMinAtAss`). This file owns the iff-ring
  completion (§1) and the per-prime lower/`dim gr` forms (§2); neither
  file restates the other's shapes.

## Status

* §1: unconditional (iffs; one-line compositions/transitivities of proved
  masters).
* §2: unconditional (conditional-form on the named witness input).
* Overall: partial toward the crux antecedent `HwitMinAtAss`
  (remainder = the witness tuple itself at `d ≥ 2`, §3).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace WitnessKernelMain

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighRelationsLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. Crux-ring completion: every residual iff the `HkerMinAtAss` hub -/

/-- `HmultMinAtAss` is exactly goal strength (both directions proved in
DimToMult §6).
-/
theorem hmultMin_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HmultMinAtAss m K J ↔ HkerMinAtAss m K J :=
  ⟨hkerMin_of_hmultMin m K J, hmultMin_of_hkerMin m K J⟩

/-- Minimal `hle` is exactly goal strength (via `hhle ↔ lower ↔ hker`).
-/
theorem hhleMin_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhleMinAtAss m K J ↔ HkerMinAtAss m K J :=
  (hhleMin_iff_lower m K J).trans (hgrDimLower_iff_hkerMin m K J)

/-- The high-relations residual is exactly goal strength
(via `High ↔ lower ↔ hker`).
-/
theorem hnoHomRelHighMin_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HkerMinAtAss m K J :=
  (hnoHomRelHighMin_iff_lower m K J).trans (hgrDimLower_iff_hkerMin m K J)

/-- `HwitMinAtAss` iff `HdimEqMinAtAss` (both directions proved in
DimToMult §6).
-/
theorem hwitMin_iff_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HwitMinAtAss m K J ↔ HdimEqMinAtAss m K J :=
  ⟨hdimEqMin_of_hwitMin m K J, hwitMin_of_hdimEqMin m K J⟩

/-- `HwitMinAtAss` iff R-2a′ in `HdimGrMinAtAss` shape (forward is the
`hdimGrMin_of_witnessMin` master; backward via the §3 direction lemmas).
-/
theorem hwitMin_iff_hdimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HwitMinAtAss m K J ↔ HdimGrMinAtAss m K J :=
  ⟨hdimGrMin_of_witnessMin m K J, fun hdim =>
    hwitMin_of_grDimEq m K J (grDimEqMin_of_dimGrMin m K J hdim)⟩

/-- `HmultMinAtAss` iff R-2a′ in `HdimGrMinAtAss` shape.
-/
theorem hmultMin_iff_hdimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HmultMinAtAss m K J ↔ HdimGrMinAtAss m K J :=
  (hmultMin_iff_grDimEqMin m K J).trans
    (hgrDimEq_iff_hdimGrMin m K J)

/-- `HdimEqMinAtAss` iff R-2a′ in `HdimGrMinAtAss` shape.
-/
theorem hdimEqMin_iff_hdimGrMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMinAtAss m K J ↔ HdimGrMinAtAss m K J :=
  (hdimEqMin_iff_grDimEqMin m K J).trans
    (hgrDimEq_iff_hdimGrMin m K J)

/-- Minimal `hle` is exactly witness-remainder-strength
(via `hhle ↔ lower ↔ hwit`).
-/
theorem hhleMin_iff_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhleMinAtAss m K J ↔ HwitMinAtAss m K J :=
  (hhleMin_iff_lower m K J).trans (hgrDimLower_iff_hwitMin m K J)

/-- The high-relations residual is exactly multiplicity-strength
(via `High ↔ hwit ↔ hmult`).
-/
theorem hnoHomRelHighMin_iff_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HmultMinAtAss m K J :=
  (hwitMin_iff_noHomRelHighMin m K J).symm.trans
    (hwitMin_iff_hmultMin m K J)

/-- The high-relations residual is exactly `hdimEq`-strength
(via `High ↔ hwit ↔ hdimEq`).
-/
theorem hnoHomRelHighMin_iff_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinAtAss m K J ↔ HdimEqMinAtAss m K J :=
  (hwitMin_iff_noHomRelHighMin m K J).symm.trans
    (hwitMin_iff_hdimEqMin m K J)

#print axioms hmultMin_iff_hkerMin
#print axioms hhleMin_iff_hkerMin
#print axioms hnoHomRelHighMin_iff_hkerMin
#print axioms hwitMin_iff_hdimEqMin
#print axioms hwitMin_iff_hdimGrMin
#print axioms hmultMin_iff_hdimGrMin
#print axioms hdimEqMin_iff_hdimGrMin
#print axioms hhleMin_iff_hwitMin
#print axioms hnoHomRelHighMin_iff_hmultMin
#print axioms hnoHomRelHighMin_iff_hdimEqMin

/-! ## §2. Per-prime crux forms: `HwitMin → ker = ⊥` in exact shape -/

/-- Per-prime lower bound from explicit witness data: the GrLower §5
"one `exact`" item — the §17 master feeds the §1 backward direction.
-/
theorem witKerCrux_lower_of_witData_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (H : ℕ → ℕ) (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hwit : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
      (fun n => ((multQuotHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0)
    (hdrop : RingHom.ker (polySurjResidue Q d g hgen) ≠ ⊥ →
      ∃ Jloc : Ideal (Localization.AtPrime Q),
        (∀ Qm ∈ Jloc.minimalPrimes,
          Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
          (Localization.AtPrime Q ⧸ Jloc),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
        (∀ n, multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q))
          d (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) + H n =
          H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen)) (n + 1) : ℕ) : ℚ))
          (d - 1)) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) :=
  grLower_of_ker_eq_bot_atPrime Q d g hgen hd
    (mult_ker_eq_bot_unconditional_of_witnessHyp Q d g hgen H hd_pos hF
      hwit hdrop)

/-- `dim gr = d` at `(Q, d)` from Ass-level witness data: the witnessed
family feeds the §17 narrowing plus the unconditional upper bound.
-/
theorem witKerCrux_dimGr_of_hwitMin_atPrime (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank)
    (hd2 : 2 ≤ d) :
    ringKrullDim (grRegular Q) = d := by
  obtain ⟨g, hgen, H, hF, hwitQ, hdrop⟩ := hwit Q hQ hdmin hd2
  have hle := mult_hle_gr_of_witnessHyp Q d g hgen H (by omega) hF hwitQ hdrop
  exact mult_dim_gr_eq_of_gr_lowerBound Q d g hgen hle

/-- Per-`Q` lower bound from Ass-level witness data: `d ≥ 2` via the
witnessed family's `hle` plus `dim R_Q = d` (minimality); `d ≤ 1` via the
closed embdim instances. The per-prime unpacking of
`hgrDimLower_of_hwitMin`.
-/
theorem witKerCrux_lower_of_hwitMin_atPrime (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (grRegular Q) := by
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  by_cases hd2 : 2 ≤ d
  · obtain ⟨g', hgen', H, hF, hwitQ, hdrop⟩ := hwit Q hQ hd hd2
    have hle : d ≤ ringKrullDim (grRegular Q) :=
      mult_hle_gr_of_witnessHyp Q d g' hgen' H (by omega) hF hwitQ hdrop
    have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
    rw [hR]
    exact hle
  · have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with rfl | rfl
    · exact grDimLower_embdim_zero m K J Q hQ hd.symm
    · exact grDimLower_embdim_one m K J Q hQ hd.symm

#print axioms witKerCrux_lower_of_witData_atPrime
#print axioms witKerCrux_dimGr_of_hwitMin_atPrime
#print axioms witKerCrux_lower_of_hwitMin_atPrime

/-! ## §3. Remainder register (doc-only)

Minimal non-circular remainder (verbatim): `HwitMinAtAss`, i.e. per
`Q ∈ Ass(R ⧸ J)` at minimal `d = spanFinrank 𝔪(R_Q)` with `2 ≤ d`, some
minimal spanning family `(g, hgen)` admits `(H, hF, hwit, hdrop)` in the
exact `mult_hle_gr_of_witnessHyp` shape (the R-2c′ Hilbert-witness side
data). Equivalently (all unconditional iffs, §1 + the consumed rings):
`HkerMinAtAss`, `HmultMinAtAss`, `HdimEqMinAtAss`, `HdimGrMinAtAss`,
`HgrDimEqMinAtAss`, `HgrDimLowerMinAtAss`, `HhleMinAtAss`, or
`HnoHomRelHighMinAtAss`.

Why the remainder is minimal and exact (all machine-checked):

* The §1 hub iffs (`hmultMin_iff_hkerMin`, `hhleMin_iff_hkerMin`,
  `hnoHomRelHighMin_iff_hkerMin`) plus the consumed spokes
  (`hwitMin_iff_hkerMin`, `hdimEqMin_iff_hkerMin`,
  `hgrDimEq_iff_hkerMin`, `hdimGrMin_iff_hkerMin`,
  `hgrDimLower_iff_hkerMin`) show every residual is exactly `ker = ⊥`
  strength — no unconditional proof of any of them exists below the
  strength of `ker = ⊥` itself (which is what the §10 master produces
  from `hmult + hdrop`, closing the documented
  `hle_gr → dim = d → hwit → hmult → ker = ⊥ → hle_gr` cycle).
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth /
  polynomiality fact to prove the §§1–2 masters; the only undischarged
  input is the witness data itself.
* §2 shows the witness data discharges the lower bound (from explicit
  data or Ass-level input) and `dim gr = d` at `(Q, d)` by direct
  per-prime compositions, complementing the sibling lane's `ker = ⊥` /
  `hle_gr` per-triple forms — the implication direction is fully explicit
  and no supply-chain gap remains on it.

Routes to the remainder (all surveyed, none duplicated):

* Hilbert–Samuel degree route: `deg HS + 1 = dim` on both sides with
  `HS(R) = Hilb(gr)`. Needs the full HS degree theorem; Mathlib has
  neither the HS function nor its degree theory. Prerequisites proved:
  Noetherian `gr` (`grLower_isNoetherianRing_gr`), finite-length `gr`
  pieces (`grLower_isFiniteLength_grPiece`), degree-bounded growth
  (`singleDrop_grHilbert_isPolyGrowth`, `kwit_hFq`).
* Rees-algebra route: `gr ≅ Rees(I)/I·Rees(I)` + `dim Rees = dim R + 1`.
  Needs the quotient identification plus `dim Rees = dim R + 1` (absent:
  needs catenary-type theory). Priced, not attempted: strictly harder
  than the HS route.
* Regularity route: `R_Q` is a regular local ring (localization of a
  polynomial ring), and `gr` of a regular local ring is a polynomial
  ring in `embdim` variables — this is the mathematical reason the crux
  is true. Formally needs regular-local-ring theory plus the
  associated-graded identification, both absent from Mathlib v4.34.0.
* Direct `d = 2` attack: no degree reason forces `ker = ⊥` at `d ≥ 2`
  (the `d ≤ 1` closures use `hsAssemble_ker_eq_bot_zero` /
  `ker_chain_ker_eq_bot_one`, which do not generalize); any attack at
  `d ≥ 2` is goal-strength by the §1 ring.

Consumers: the §1 iffs let any future crux proof discharge every residual
by a single `exact`; the §2 per-prime forms supply `dim gr = d` and the
lower bound at `(Q, d)` directly from witness data.
-/

end WitnessKernelMain
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
