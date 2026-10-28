/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.BabyAuslanderBuchsbaum
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeUnmixedBridge
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Height-drop residual ⟺ DepthEqDimAt-at-Ass package (C0-sharp)


## Main results

* `depthEqDimAt_of_residual`: the reverse direction — the height-drop
  residual (`P.height ≤ k` for `P ∈ Ass(R ⧸ J)`) implies
  `GradeDepthFragment.DepthEqDimAt` at each `Ass` prime. This is the only real
  proof in the file (~30 lines): it mirrors the proved template
  `GradeUnmixedBridge.height_eq_of_chain_depth_babyAB`, with the
  residual supplying the upper bound instead of L2. Inputs are all
  proved: `GradeDepthFragment.gradeDropChain_of_successive` (L1 lower bound),
  `GradeUnmixedBridge.babyAB_of_babyAB_quot` (L4, unconditional
  general-`k` BabyAuslanderBuchsbaum) + `grade_localized_quotient_eq_zero` (depth-zero
  at `Ass`) for the upper bound, and `GradeDepthFragment.grade_le_ringKrullDim`
  (grade ≤ dim).
* `DepthEqDimAtAss`: the sharp address — `DepthEqDimAt` at every
  `P ∈ Ass(R ⧸ J)`, with the same binder shape as
  `HeightDrop.HeightDropResidualAt` (unused `hsucc`/`hJ` kept).
* `residual_iff_depthEqDimAtAss`: the packaged biconditional. Forward
  cites the proved `BabyAuslanderBuchsbaum.gradeUnmixedBridge_general` (which ignores
  its chain input) fed by `gradeDropChain_of_successive`; reverse is
  `depthEqDimAt_of_residual` under the binder.
* `residualPair_iff_depthEqDimAtAss`: the `k = 2` alias, definitional
  since `HeightDropResidualPair` is `def`'d as `HeightDropResidualAt`.

## Placement

This leaf sits strictly downstream of every import (`GradeDepthFragment`,
`HeightDrop`, `BabyAuslanderBuchsbaum`, `GradeUnmixedBridge`, `LocalUnmixed`), so no
import cycle is possible. It is deliberately not inside
`HeightDrop.lean`: the package needs `GradeDepthFragment` content and
`GradeDepthFragment.lean` imports `HeightDrop`.

`DepthEqDimAt` appears here only proved (reverse side) or packaged as
one side of a proved biconditional (forward side) — never assumed.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HeightDropSharp

/-- Reverse direction (C0-sharp, the only real proof): the height-drop
residual implies `DepthEqDimAt` at each `Ass` prime. The chain lower
bound (`k ≤ grade`) plus baby-AB with depth-zero (`grade ≤ k`) pins
`grade S = k`; `grade_le_ringKrullDim` gives `↑grade ≤ dim S`, and the
residual closes `dim S ≤ ↑grade` through
`ringKrullDim_eq_height`. -/
theorem depthEqDimAt_of_residual {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hres : HeightDrop.HeightDropResidualAt m K q hsucc J hJ)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K P := by
  have hJP : Ideal.span (Set.range q) ≤ P :=
    hJ ▸ LocalUnmixed.assPrime_contains_span J P hP
  have hchain : GradeDepthFragment.GradeDropChain m K q hsucc :=
    GradeDepthFragment.gradeDropChain_of_successive m K q hsucc
  have hgrade_ge : (k : ℕ∞) ≤ GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    hchain P hJP
  have hdepth0 : GradeDepthFragment.grade (Localization.AtPrime P)
      (LocalizedModule.AtPrime P (_ ⧸ J))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = 0 :=
    GradeUnmixedBridge.grade_localized_quotient_eq_zero m K J P hP
  have hbaby : GradeUnmixedBridge.BabyAuslanderBuchsbaum m K q hsucc J hJ :=
    GradeUnmixedBridge.babyAB_of_babyAB_quot m K q hsucc J hJ
  have hgrade_le : GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      ≤ (k : ℕ∞) := by
    have h := hbaby P hP
    rwa [hdepth0, add_zero] at h
  have hgrade_eq : GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      = (k : ℕ∞) :=
    le_antisymm hgrade_le hgrade_ge
  have hle : ((GradeDepthFragment.grade (Localization.AtPrime P) (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) : WithBot ℕ∞)
      ≤ ringKrullDim (Localization.AtPrime P) :=
    GradeDepthFragment.grade_le_ringKrullDim _
  unfold GradeDepthFragment.DepthEqDimAt
  refine le_antisymm hle ?_
  rw [hgrade_eq,
    IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  exact WithBot.coe_le_coe.mpr (hres P hP)

#print axioms depthEqDimAt_of_residual

/-- Sharp address: `DepthEqDimAt` at every `P ∈ Ass(R ⧸ J)`. Binder
shape mirrors `HeightDrop.HeightDropResidualAt` exactly, including the
underscore-prefixed unused `hsucc`/`hJ`, so the iff sides align. -/
def DepthEqDimAtAss {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (_hJ : J = Ideal.span (Set.range q)) : Prop :=
  ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    P ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K P

/-- The C0-sharp package: the height-drop residual holds iff
`DepthEqDimAt` holds at every `Ass` prime. Forward cites the proved
`BabyAuslanderBuchsbaum.gradeUnmixedBridge_general` (chain input ignored there, fed
here by `gradeDropChain_of_successive`); reverse is
`depthEqDimAt_of_residual` under the binder. -/
theorem residual_iff_depthEqDimAtAss {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ ↔
      DepthEqDimAtAss m K q hsucc J hJ := by
  constructor
  · intro hres P _ hP
    exact depthEqDimAt_of_residual m K q hsucc J hJ hres P hP
  · intro hdepth
    exact BabyAuslanderBuchsbaum.gradeUnmixedBridge_general m K q hsucc J hJ
      (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc) hdepth

#print axioms residual_iff_depthEqDimAtAss

/-- The `k = 2` alias of the C0-sharp package: `HeightDropResidualPair`
is definitionally `HeightDropResidualAt`, so this is the general iff
at `k = 2`. -/
theorem residualPair_iff_depthEqDimAtAss (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) :
    HeightDrop.HeightDropResidualPair m K q hsucc J hJ ↔
      DepthEqDimAtAss m K q hsucc J hJ :=
  residual_iff_depthEqDimAtAss m K q hsucc J hJ

#print axioms residualPair_iff_depthEqDimAtAss

end HeightDropSharp
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
