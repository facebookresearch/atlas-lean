/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MacaulayScoped
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.BabyAuslanderBuchsbaum
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Grade-unmixedness bridge: chain + depth + baby-AB imply unmixedness

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `q : Fin k → R` carrying
successive SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`), and
`J = Ideal.span (Set.range q)`, this file assembles the end-to-end bridge
from the three residual inputs to per-prefix unmixedness:

* (L1) `GradeDepthFragment.GradeDropChain`: every prime carries local grade `≥ k`.
* (L2) `GradeDepthFragment.DepthEqDimAt` at every `P ∈ Ass(R ⧸ J)`: local grade
  equals local Krull dimension.
* (L4) `BabyAuslanderBuchsbaum` (this file): the Auslander–Buchsbaum + Koszul content as one
  inequality per `Ass` prime —
  `grade S S m ≤ k + grade S M_P m`, where `S = Localization.AtPrime P`,
  `m` is its maximal ideal, and `M_P = LocalizedModule.AtPrime P (R ⧸ J)`.
  Justification: the Koszul complex of the length-`k` regular sequence
  generating `J_P` bounds `pd(M_P) ≤ k`, and Auslander–Buchsbaum reads
  `depth S ≤ pd(M_P) + depth M_P`. Both are absent from Mathlib v4.34.0,
  so (L4) is the named residual; sibling lanes prove it.

Every other step is proved here:

* `grade_localized_quotient_eq_zero`: `grade S M_P m = 0` for
  `P ∈ Ass(R ⧸ J)` — the proved local (ii): `Ass` localizes
  (`mem_associatedPrimes_atPrime_of_mem_associatedPrimes`) and grade at an
  associated prime is zero (`grade_eq_zero_of_mem_associatedPrimes`).
* `height_eq_of_chain_depth_babyAB`: `P.height = k` for `P ∈ Ass(R ⧸ J)`,
  from (L1) + (L2) + (L4). Lower: (L1) gives `k ≤ grade S`;
  upper: (L4) + depth-zero gives `grade S ≤ k`; hence `grade S = k`;
  (L2) turns this into `dim S = k`, and `dim S = height P`
  (`IsLocalization.AtPrime.ringKrullDim_eq_height`).
* `heightDrop_of_chain_depth_babyAB`: `HeightDrop.HeightDropResidualAt`.
* `unmixed_of_chain_depth_babyAB`: per-prime minimality over `J` — ports
  the `GradeDepthFragment.unmixed_of_grade_of_depthEq` assembly shape, with `BabyAuslanderBuchsbaum`
  in place of `GradeUnmixedBridge`.
* `scoped_of_chain_depth_babyAB`: `MacaulayScoped.ScopedMacaulayAt` (the
  `2 ≤ k` gate is inside the statement).

The `q` / `hsucc` / `hJ` binders enter the equality proof only through the
residual hypotheses that pin them; the proof itself is grade/dimension
arithmetic at `P`.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/Regularity/`):

* `GradeDepthFragment.lean`: `grade`, `GradeDropChain`, `DepthEqDimAt`,
  `grade_eq_zero_of_mem_associatedPrimes`, `unmixed_of_grade_of_depthEq`
  (assembly shape ported here).
* `HeightDrop.lean`: `HeightDropResidualAt`, `minimal_of_height_le`.
* `MacaulayScoped.lean`: `ScopedMacaulayAt`, `scoped_iff_heightDrop`.

Mathlib v4.34.0:

* `mem_associatedPrimes_atPrime_of_mem_associatedPrimes`
  (`RingTheory/Ideal/AssociatedPrime/Localization.lean`).
* `IsLocalization.AtPrime.ringKrullDim_eq_height`
  (`RingTheory/Ideal/Height.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradeUnmixedBridge

/-- Baby Auslander–Buchsbaum (L4 residual): at each `P ∈ Ass(R ⧸ J)`, the
depth of the local ring `S = Localization.AtPrime P` is at most `k` plus
the depth of the localized quotient `M_P`. The Koszul resolution of `M_P`
by the length-`k` regular sequence has projective dimension `≤ k`, and
Auslander–Buchsbaum reads `depth S ≤ pd + depth M_P`; both inputs are
absent from Mathlib, so this inequality is taken as the named residual.
Proved by sibling lanes — never here. -/
def BabyAuslanderBuchsbaum {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (_hJ : J = Ideal.span (Set.range q)) : Prop :=
  ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    P ∈ associatedPrimes _ (_ ⧸ J) →
      GradeDepthFragment.grade (Localization.AtPrime P) (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      ≤ (k : ℕ∞) + GradeDepthFragment.grade (Localization.AtPrime P)
        (LocalizedModule.AtPrime P (_ ⧸ J))
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))

/-- Depth-zero of the localized quotient at an `Ass` prime (proved): the
maximal ideal of `S` is associated to `M_P` (localization of `Ass`), and
grade at an associated prime is zero. -/
theorem grade_localized_quotient_eq_zero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.grade (Localization.AtPrime P)
      (LocalizedModule.AtPrime P (_ ⧸ J))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = 0 :=
  GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes
    (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hP)

/-- Height equality at an `Ass` prime from (L1) + (L2) + (L4): the chain
pins `k ≤ grade S`, baby-AB with depth-zero pins `grade S ≤ k`, depth-eq-dim
turns `grade S = k` into `dim S = k`, and `dim S = height P`. -/
theorem height_eq_of_chain_depth_babyAB {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hchain : GradeDepthFragment.GradeDropChain m K q hsucc)
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q)
    (hbaby : BabyAuslanderBuchsbaum m K q hsucc J hJ) :
    P.height = (k : ℕ∞) := by
  have hdepth0 : GradeDepthFragment.grade (Localization.AtPrime P)
      (LocalizedModule.AtPrime P (_ ⧸ J))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = 0 :=
    grade_localized_quotient_eq_zero m K J P hP
  have hJP : Ideal.span (Set.range q) ≤ P :=
    hJ ▸ LocalUnmixed.assPrime_contains_span J P hP
  have hgrade_ge : (k : ℕ∞) ≤ GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    hchain P hJP
  have hgrade_le : GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      ≤ (k : ℕ∞) := by
    have h := hbaby P hP
    rwa [hdepth0, add_zero] at h
  have hgrade_eq : GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      = (k : ℕ∞) :=
    le_antisymm hgrade_le hgrade_ge
  have hde : ((GradeDepthFragment.grade (Localization.AtPrime P) (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim (Localization.AtPrime P) :=
    hdepth P hP
  have hH : ringKrullDim (Localization.AtPrime P)
      = ((P.height : ℕ∞) : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
  have hW : ((P.height : ℕ∞) : WithBot ℕ∞) = (((k : ℕ∞)) : WithBot ℕ∞) := by
    calc ((P.height : ℕ∞) : WithBot ℕ∞)
        = ringKrullDim (Localization.AtPrime P) := hH.symm
      _ = ((GradeDepthFragment.grade (Localization.AtPrime P) (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) :
          WithBot ℕ∞) := hde.symm
      _ = (((k : ℕ∞)) : WithBot ℕ∞) := by rw [hgrade_eq]
  exact WithBot.coe_eq_coe.mp hW

/-- Height-drop residual from (L1) + (L2) + (L4): every `Ass` prime has
height `≤ k` (in fact `= k`). -/
theorem heightDrop_of_chain_depth_babyAB {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (hchain : GradeDepthFragment.GradeDropChain m K q hsucc)
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q)
    (hbaby : BabyAuslanderBuchsbaum m K q hsucc J hJ) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ := by
  change ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    P ∈ associatedPrimes _ (_ ⧸ J) → P.height ≤ (k : ℕ∞)
  intro P _ hP
  exact (height_eq_of_chain_depth_babyAB m K q hsucc J hJ P hP hchain hdepth
    hbaby).le

/-- Per-prime minimality over `J` from (L1) + (L2) + (L4): ports the
`GradeDepthFragment.unmixed_of_grade_of_depthEq` assembly with `BabyAuslanderBuchsbaum` supplying
the bridge content. -/
theorem unmixed_of_chain_depth_babyAB {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hchain : GradeDepthFragment.GradeDropChain m K q hsucc)
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q)
    (hbaby : BabyAuslanderBuchsbaum m K q hsucc J hJ) :
    P ∈ J.minimalPrimes := by
  have hdrop : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → Q.height ≤ (k : ℕ∞) :=
    heightDrop_of_chain_depth_babyAB m K q hsucc J hJ hchain hdepth hbaby
  exact HeightDrop.minimal_of_height_le m K q hsucc J hJ P hP (hdrop P hP)

/-- Scoped Macaulay unmixedness from (L1) + (L2) + (L4): per-prefix
minimality at lengths `≥ 2` (the gate is inside `ScopedMacaulayAt`). -/
theorem scoped_of_chain_depth_babyAB {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (hchain : GradeDepthFragment.GradeDropChain m K q hsucc)
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q)
    (hbaby : BabyAuslanderBuchsbaum m K q hsucc J hJ) :
    MacaulayScoped.ScopedMacaulayAt k K q hsucc J hJ :=
  (MacaulayScoped.scoped_iff_heightDrop k m K q hsucc J hJ).mpr
    (fun _ => heightDrop_of_chain_depth_babyAB m K q hsucc J hJ hchain hdepth
      hbaby)

end GradeUnmixedBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradeUnmixedBridge

open _root_.EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BabyAuslanderBuchsbaum


/-- L4 `BabyAuslanderBuchsbaum` inequality from the proved length-`k` Auslander–Buchsbaum
equation: `babyAB_quot` gives `pd + grade(spanQuot) = grade(S)` at
`S = Localization.AtPrime P`, `pd = k` (`pd_spanQuot_eq_length` plus
`List.length_ofFn`), and `grade_congr_of_linearEquiv` across
`locQuotEquivOfFn` identifies `grade(spanQuot)` with `grade(M_P)`;
the resulting equality implies the `≤` goal.
-/
theorem babyAB_of_babyAB_quot {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q)) :
    BabyAuslanderBuchsbaum m K q hsucc J hJ := by
  intro P _ hP
  have hJP : Ideal.span (Set.range q) ≤ P :=
    hJ ▸ LocalUnmixed.assPrime_contains_span J P hP
  obtain ⟨hreg, hmem⟩ :=
    localized_isRegular_ofFn P q hsucc hJP
  have hIlt : IsLocalRing.maximalIdeal (Localization.AtPrime P) •
      (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) < ⊤ :=
    lt_top_iff_ne_top.mpr (Ne.symm
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)))
  have hAB :=
    babyAB_quot
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) _ hmem hIlt hreg
  have hpd :=
    pd_spanQuot_eq_length
      (R' := Localization.AtPrime P) _ hreg
  have hcongr :=
    grade_congr_of_linearEquiv
      (
        locQuotEquivOfFn P q J hJ)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P))
  rw [hpd, ← hcongr, List.length_ofFn] at hAB
  have hEq : GradeDepthFragment.grade (Localization.AtPrime P) (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      = (k : ℕ∞) + GradeDepthFragment.grade (Localization.AtPrime P)
        (LocalizedModule.AtPrime P (_ ⧸ J))
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) := by
    apply WithBot.coe_eq_coe.mp
    rw [← hAB, WithBot.coe_add, WithBot.coe_natCast]
  exact hEq.le

end GradeUnmixedBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradeUnmixedBridge

/-- Height-drop residual from (L1) + (L2): `hbaby` discharged
by `babyAB_of_babyAB_quot` (unconditional L4).

Conditional on exactly [hchain, hdepth]. -/
theorem heightDrop_of_chain_depth {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (hchain : GradeDepthFragment.GradeDropChain m K q hsucc)
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ :=
  heightDrop_of_chain_depth_babyAB m K q hsucc J hJ hchain hdepth
    (babyAB_of_babyAB_quot m K q hsucc J hJ)

/-- Per-prime minimality over `J` from (L1) + (L2): `hbaby` discharged
by `babyAB_of_babyAB_quot` (unconditional L4).

Conditional on exactly [hchain, hdepth]. -/
theorem unmixed_of_chain_depth {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hchain : GradeDepthFragment.GradeDropChain m K q hsucc)
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    P ∈ J.minimalPrimes :=
  unmixed_of_chain_depth_babyAB m K q hsucc J hJ P hP hchain hdepth
    (babyAB_of_babyAB_quot m K q hsucc J hJ)

end GradeUnmixedBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
