/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AdelicFinitePrefixLimits

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (B : EffectiveBoundary A X) (N₀ N : MetrizedLine A X L)

def withPrefix : CauchySequence (L := L) B :=
  ⟨fun n ↦ if n = 0 then N₀ else N, by
    intro ε hε
    refine ⟨1, ?_⟩
    intro m n hm hn v p z hz
    have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
    change |Real.log (norm (if m = 0 then N₀ else N) v p z) -
      Real.log (norm (if n = 0 then N₀ else N) v p z)| ≤ _
    rw [ite_eq_right hm0, ite_eq_right hn0, sub_self, abs_zero]
    exact mul_nonneg (le_of_lt hε) (B.nonnegative v p)⟩

theorem prefix_equivalent : Equivalent B (withPrefix B N₀ N) (constantSequence B N) := by
  intro ε hε
  refine ⟨1, ?_⟩
  intro n hn v p z hz
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  change |Real.log (norm (if n = 0 then N₀ else N) v p z) - Real.log (norm N v p z)| ≤ _
  rw [ite_eq_right hn0, sub_self, abs_zero]
  exact mul_nonneg (le_of_lt hε) (B.nonnegative v p)

/-- An arbitrary first metric has no effect on any completed norm, even at zero gauge. -/
example (v : A.places) (p : Point (A := A) (X := X) v)
    (z : Vector (A := A) (X := X) (L := L) v p) :
    fibreNorm B (Quotient.mk _ (withPrefix B N₀ N)) v p z = norm N v p z := by
  have h : Quotient.mk _ (withPrefix B N₀ N) = constantClass B N :=
    Quotient.sound (prefix_equivalent B N₀ N)
  rw [h, fibreNorm_constant]

/-- Completed scalar normalization agrees with the original norm at the concrete scalar three. -/
example (v : A.places) (p : Point (A := A) (X := X) v)
    (z : Vector (A := A) (X := X) (L := L) v p) :
    fibreNorm B (constantClass B N) v p
      ((3 : MathlibExt.AlgebraicGeometry.ValuedLineFibres.CompletedResidue
        (A.completion v) (placeScheme A X v) p) • z) =
        ‖(3 : MathlibExt.AlgebraicGeometry.ValuedLineFibres.CompletedResidue
          (A.completion v) (placeScheme A X v) p)‖ *
          norm N v p z := by
  rw [fibreNorm_constant]
  exact ((N.metric v).fibreNorm p).homogeneous _ _

end MathlibExtTest.AlgebraicGeometry.AdelicFinitePrefixLimits
