/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KernelChain
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Unified crux `HwitMinAtAss → ker = ⊥`: one-shot discharge + ∃-ker factorization
Q1 main attack on the unified crux: the witness-to-kernel implication
closing R1 + R2 + §6 in one (R-2c′ is already closed-on-crux, R-2a′ is the sole
live attack).

verdict (machine-checked, §§1–2): the implication is closed, and the live
remainder is the antecedent itself.
* Per-triple, the implication from an explicit witness tuple
  `(g, hgen, H, hF, hwit, hdrop)` to `ker = ⊥` for that family is
  `mult_ker_eq_bot_unconditional_of_witnessHyp` (Multiplicity §14, consumed).
* At Ass level, `HwitMinAtAss → HkerMinAtAss` is `hkerMin_of_hwitMin`
  (DimToMult §6, consumed): the ∃-closed witness data yields `dim gr = d`
  (g-independent), hence `ker = ⊥` for every minimal family via the §17
  collapse.
* No unconditional proof of the antecedent at `d ≥ 2` exists below the
  strength of `ker = ⊥` itself (`hwitMin_iff_hkerMin`, DimToMult §3b):
  `hwit`'s `coeff (d-1) ≠ 0` needs `dim (S ⧸ ker) = d`, which needs `hle_gr`,
  which is `ker = ⊥` (§17 collapse); `hdrop`'s drop equation needs genuine
  drop theory (`H := 0` fails it: it would force `multQuotHilbert = 0`).

## What this file proves (no duplication: all compositions are new shapes)

* (§1) Joint one-shot discharge, conditional-exact on the named crux input:
  `hwitKerCrux_joint_of_hwitMin` (R1 lower + R2 High + §6 `hdimEq`/`hmult` +
  `HgrDimEq` + `Hker` from `[hwit]` in one tuple) and the symmetric
  `hwitKerCrux_joint_of_hkerMin` (same tuple with `Hwit` first, from `[hker]`).
  Either crux form closes every residual by a single `exact`.
* (§2) ∃-ker factorization (new intermediate SPEC + 4 theorems): the Ass-level
  implication factors through `HexistsKerMinAtAss` (∃-closed over the spanning
  family, mirroring `HkerMinAtAss` binders). `hwitKerCrux_hexists_of_hwitMin`
  (conditional-exact on `[hwit]`, `d`-split: `d ≤ 1` unconditional via the
  closed kernel branches, `d ≥ 2` direct from the witness family — no
  dimension detour) isolates the ∃ conclusion; `hwitKerCrux_hker_of_hexists`
  (unconditional upgrade: ∃ `ker = ⊥` → `hle_gr` → `dim gr = d` → ∀
  `ker = ⊥`) shows the ∃→∀ upgrade goes exactly through `dim gr`;
  `hwitKerCrux_hexists_iff_hker` (unconditional iff) closes the triangle.
  Engine: `hwitKerCrux_tuple_gives_all` (per-triple tuple → `ker = ⊥` ∧
  `hle_gr` ∧ `dim gr = d`, in exact `HwitMinAtAss`-tuple shape).
* (§3, doc-only) Precise remainder register: the antecedent `HwitMinAtAss`
  itself (equivalently any crux form), why each conjunct is goal-strength,
  and the scoped routes.

## Scope coordination (no duplication)

* `DimensionToMultiplicity.lean` §§3b/6/7: owns `hkerMin_of_hwitMin`,
  `hdimEqMin_of_hwitMin`, `hmultMin_of_hwitMin`, `grDimEqMin_of_hwitMin`,
  `hwitMin_iff_hkerMin`. Consumed only (never restated).
* `GradedLowerBound.lean` §2: owns `hgrDimLower_of_hkerMin`. Consumed only.
* `HighRelationsLowerBound.lean` §4: owns `hnoHomRelHighMin_of_lower`. Consumed only.
* `GradedDimEq.lean` §3: owns `HgrDimLowerMinAtAss`. Consumed only.
* `MultiplicityNonvanishing.lean` §§14/16/17: owns the per-triple engine pieces.
  consumed only.
* This file is a new leaf: not imported by any other module (no cycle).

## Status

* §1 joint discharge: conditional-exact on the named crux input.
* §2 engine + ∃→∀ upgrade + iff direction: unconditional; ∃ from witness:
  conditional-exact on `[hwit]`.
* Overall: partial toward the crux antecedent
  (remainder = `HwitMinAtAss` itself at `d ≥ 2`, §3).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace WitnessKernelCrux

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelChain
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighRelationsLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. Joint one-shot discharge: any crux form closes R1 + R2 + §6 -/

/-- One-shot discharge on `[hwit]`: R1's lower bound, R2's High residual, §6's
`hdimEq`/`hmult`, `HgrDimEq`, and `Hker` — every residual in one tuple.

Conditional on exactly `[hwit]`. -/
theorem hwitKerCrux_joint_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitMinAtAss m K J) :
    HkerMinAtAss m K J ∧ HgrDimLowerMinAtAss m K J ∧
      HnoHomRelHighMinAtAss m K J ∧ HdimEqMinAtAss m K J ∧
      HmultMinAtAss m K J ∧ HgrDimEqMinAtAss m K J := by
  have hker := hkerMin_of_hwitMin m K J hwit
  have hlo := hgrDimLower_of_hkerMin m K J hker
  refine ⟨hker, hlo, ?_, ?_, ?_, ?_⟩
  · exact hnoHomRelHighMin_of_lower m K J hlo
  · exact hdimEqMin_of_hwitMin m K J hwit
  · exact hmultMin_of_hwitMin m K J hwit
  · exact grDimEqMin_of_hwitMin m K J hwit

/-- Symmetric one-shot discharge on `[hker]`: same tuple with `Hwit` first
(via `hwitMin_iff_hkerMin`, then §1 above).

Conditional on exactly `[hker]`. -/
theorem hwitKerCrux_joint_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerMinAtAss m K J) :
    HwitMinAtAss m K J ∧ HgrDimLowerMinAtAss m K J ∧
      HnoHomRelHighMinAtAss m K J ∧ HdimEqMinAtAss m K J ∧
      HmultMinAtAss m K J ∧ HgrDimEqMinAtAss m K J := by
  have hwit := (hwitMin_iff_hkerMin m K J).mpr hker
  obtain ⟨_, hlo, hhigh, hdimEq, hmult, hgr⟩ :=
    hwitKerCrux_joint_of_hwitMin m K J hwit
  exact ⟨hwit, hlo, hhigh, hdimEq, hmult, hgr⟩

#print axioms hwitKerCrux_joint_of_hwitMin
#print axioms hwitKerCrux_joint_of_hkerMin

/-! ## §2. ∃-ker factorization: the implication via an ∃-closed middle -/

/-- Per-triple engine in exact `HwitMinAtAss`-tuple shape: an explicit witness
tuple yields `ker = ⊥` for that family (§14 master), hence `hle_gr` (§17
forward collapse), hence `dim gr = d` (§16 upper bound).
-/
theorem hwitKerCrux_tuple_gives_all {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (H : ℕ → ℕ) (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hwitQ : ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
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
        (∀ n, multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen))
          (n + 1) + H n = H (n + 1)) ∧
        IsPolyGrowth (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
          (RingHom.ker (polySurjResidue Q d g hgen))
          (n + 1) : ℕ) : ℚ)) (d - 1)) :
    RingHom.ker (polySurjResidue Q d g hgen) = ⊥ ∧
      d ≤ ringKrullDim (grRegular Q) ∧
      ringKrullDim (grRegular Q) = d := by
  have hker := mult_ker_eq_bot_unconditional_of_witnessHyp Q d g hgen H
    hd_pos hF hwitQ hdrop
  have hle := mult_hle_gr_of_ker_eq_bot Q d g hgen hker
  exact ⟨hker, hle, mult_dim_gr_eq_of_gr_lowerBound Q d g hgen hle⟩

/-- ∃-closed kernel form at minimal `d`: for every Ass prime and minimal `d`,
some spanning family has trivial kernel. Weaker (by binder shape) than
`HkerMinAtAss`; the §2 iff shows it is equivalent — the ∃→∀ upgrade goes
exactly through `dim gr`.

Specification (Prop address for the ∃-closed kernel hypothesis). -/
def HexistsKerMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ},
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ∃ (g : Fin d → Localization.AtPrime Q),
        ∃ (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
          RingHom.ker (polySurjResidue Q d g hgen) = ⊥

/-- ∃-ker from the witness remainder, `d`-split: `d = 0` via
`hsAssemble_ker_eq_bot_zero` on the minimal sop family, `d = 1` via
`ker_chain_ker_eq_bot_one` (with `hmin` from minimality itself), `d ≥ 2`
direct from the witness family (no dimension detour — the detour is only
needed for the ∀ upgrade below).

Conditional on exactly `[hwit]` (`d ≤ 1` unconditional). -/
theorem hwitKerCrux_hexists_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitMinAtAss m K J) :
    HexistsKerMinAtAss m K J := by
  intro Q _ hQ d hdmin
  cases d with
  | zero =>
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have heq : d' = 0 := hd'.trans hdmin.symm
    subst heq
    exact ⟨g, hgen, hsAssemble_ker_eq_bot_zero Q g hgen⟩
  | succ n =>
    cases n with
    | zero =>
      obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
      have heq : d' = 1 := hd'.trans hdmin.symm
      subst heq
      exact ⟨g, hgen, ker_chain_ker_eq_bot_one Q g hgen
        (ker_chain_hmin_one_of_sop Q _ g hgen hd' (by omega))⟩
    | succ k =>
      have hd2 : 2 ≤ k + 2 := by omega
      obtain ⟨g, hgen, H, hF, hwitQ, hdrop⟩ := hwit Q hQ hdmin hd2
      have hd_pos : 1 < k + 2 := by omega
      exact ⟨g, hgen,
        (hwitKerCrux_tuple_gives_all Q (k + 2) g hgen H hd_pos hF hwitQ
          hdrop).1⟩

/-- ∀-ker from ∃-ker: the witness family's `ker = ⊥` gives `hle_gr` (§17
forward), hence `dim gr = d` (§16 upper), hence `ker = ⊥` for every minimal
family (§17 backward collapse). The ∃→∀ upgrade is exactly `dim gr`.
-/
theorem hwitKerCrux_hker_of_hexists (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hexists : HexistsKerMinAtAss m K J) :
    HkerMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  obtain ⟨g0, hgen0, hker0⟩ := hexists Q hQ hdmin
  have hle : d ≤ ringKrullDim (grRegular Q) :=
    mult_hle_gr_of_ker_eq_bot Q d g0 hgen0 hker0
  have hgr : ringKrullDim (grRegular Q) = d :=
    mult_dim_gr_eq_of_gr_lowerBound Q d g0 hgen0 hle
  have hle' : d ≤ ringKrullDim (grRegular Q) := by rw [hgr]
  exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle'

/-- ∃-ker is exactly ∀-ker at Ass primes: forward is the `dim gr` upgrade
above; backward instantiates the ∀ form on the minimal sop family.
-/
theorem hwitKerCrux_hexists_iff_hker (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HexistsKerMinAtAss m K J ↔ HkerMinAtAss m K J := by
  constructor
  · exact hwitKerCrux_hker_of_hexists m K J
  · intro hker Q _ hQ d hdmin
    obtain ⟨d', g, hgen, hd'⟩ := grlift_sop_exists Q
    have heq : d' = d := hd'.trans hdmin.symm
    subst heq
    exact ⟨g, hgen, hker Q hQ g hgen hd'⟩

#print axioms hwitKerCrux_tuple_gives_all
#print axioms hwitKerCrux_hexists_of_hwitMin
#print axioms hwitKerCrux_hker_of_hexists
#print axioms hwitKerCrux_hexists_iff_hker

/-! ## §3. Remainder register (doc-only)

Minimal non-circular remainder (verbatim): `HwitMinAtAss` itself — i.e. per
`Q ∈ Ass(R ⧸ J)` at minimal `d ≥ 2`, a spanning family `(g, hgen)` with
`H`, `IsPolyGrowth H (d-1)`, `hwit` (eventual polynomiality of
`multQuotHilbert` of degree `≤ d - 1` with `coeff (d - 1) ≠ 0`), and `hdrop`
(drop data under `ker ≠ ⊥`). Equivalently (all unconditional iffs): `HkerMin`,
`HdimGrMin`, `HgrDimEqMin`, `HgrDimLowerMin` (R1), `HnoHomRelHighMin` (R2),
`HmultMin`, `HdimEqMin`, or `HexistsKerMin` (§2).

Why the remainder is minimal and exact (all machine-checked):

* `hwitKerCrux_hexists_iff_hker` (§2) + `hwitMin_iff_hkerMin` (DimToMult §3b)
  + `hnoHomRelHighMin_iff_lower` (HighHleMin §4) + `hgrDimLower_iff_hkerMin`
  (GrLower §2): every crux form is exactly `ker = ⊥` strength — no proof of
  any of them exists below the strength of `ker = ⊥` itself.
* Per-conjunct goal-strength: `hwit`'s `coeff (d-1) ≠ 0` is `hmult`, which
  needs `dim (S ⧸ ker) = d` (R-2c′), which needs `hle_gr` (R-2a′), which is
  `ker = ⊥` (§17 collapse) — the documented cycle. `hdrop`'s drop equation
  `multQuotHilbert (n+1) + H n = H (n+1)` with `IsPolyGrowth H (d-1)` asks for
  the degree drop under `ker ≠ ⊥` (with `H := 0` it would force
  `multQuotHilbert = 0`, false in general), so the §7 skeleton's `H := 0`
  cannot be extended to `hdrop` without drop theory.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth /
  polynomiality fact to prove the §§1–2 masters; the only undischarged input
  is the named crux hypothesis itself.

Routes to the antecedent (all surveyed, none duplicated):

* Hilbert–Samuel degree route: `deg HS + 1 = dim` on both sides with
  `HS(R) = Hilb(gr)` gives `dim gr = d`, hence `hwit` by domain theory
  (`hwitMin_of_grDimEq`). Needs the full HS degree theorem; Mathlib has
  neither the HS function nor its degree theory. Prerequisites already in place:
  Noetherian `gr` + finite-length pieces (GrLower §§3–4), `IsPolyGrowth` of
  `gr` Hilbert (UnmixednessAtLengthTwo §7).
* Rees-algebra route: `gr ≅ Rees(I)/I·Rees(I)` + `dim Rees = dim R + 1`.
  Needs the quotient identification plus `dim Rees = dim R + 1` (also absent:
  needs catenary-type theory). Priced, not attempted: strictly harder.
* Direct High attack: a nonzero homogeneous relation of degree `≥ 2`
  contradicts minimality + domain structure. Needs `KwitKerIsPrime` +
  `KwitNoIrredHigh` (HomRelHigh §§3–4, DimTheory: prime needs nzd(`gr`),
  NoIrredHigh needs `hle_gr`) — scoped, circular at current strength.

Consumers: `hwitKerCrux_joint_of_hwitMin` / `hwitKerCrux_joint_of_hkerMin`
discharge every residual on either crux form by a single `exact`; feeding the
`HdimEqMinAtAss` component into `hunmixed_two_forall_of_hdimEqMin` yields rb-1.
`hwitKerCrux_hexists_of_hwitMin` + `hwitKerCrux_hker_of_hexists` factor the
Ass-level implication through the ∃ middle, documenting that the ∀ strength
comes exactly from `dim gr`.
-/

end WitnessKernelCrux
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
