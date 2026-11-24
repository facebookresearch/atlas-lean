/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.StableMapCompositionStacks
import Mathlib.RingTheory.Polynomial.Basic

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.StableMapCompositionFamilies
open MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials
open MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies

set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace StableMapCompositionDifferentialsTest

-- A constant projected genus-zero unmarked family has no stable target model.
example {V Y S T : Scheme.{0}} {q : V ⟶ S} {b : T ⟶ S}
    (F : Family q 0 0 T b) (h : V ⟶ Y) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ T) (constant : IsFiberConstant F h p) : ¬ IsStabilizable F h 0 := by
  intro stable
  rcases stable Ω p with bad | bad
  · norm_num at bad
  · exact bad constant

-- Genus two admits stabilization even when all target maps are constant and no markings remain.
example {V Y S T : Scheme.{0}} {q : V ⟶ S} {n : ℕ} {b : T ⟶ S}
    (F : Family q n 2 T b) (h : V ⟶ Y) : IsStabilizable F h 0 := by
  intro Ω _ _ p
  exact Or.inl (by norm_num)

def line : Over (Spec (.of ℚ)) := Over.mk (Spec.algebraMap ℚ (Polynomial ℚ))
def zeroPoint : Spec (.of ℚ) ⟶ line.left := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))

theorem zeroPoint_over : zeroPoint ≫ line.hom = 𝟙 (Spec (.of ℚ)) := by
  have h : CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom 0) = 𝟙 _ := by ext x; simp
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ))) = _
  rw [← Spec.map_comp, h, Spec.map_id]

def motion : PointDeformation (q := line.hom) (b := 𝟙 _) zeroPoint zeroPoint_over where
  map := Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom ℚ ℚ) (TrivSqZeroExt.inr 1)))
  over := by
    have h : CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)) ≫
        CommRingCat.ofHom (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom ℚ ℚ)
          (TrivSqZeroExt.inr 1)) = CommRingCat.ofHom (TrivSqZeroExt.inlHom ℚ ℚ) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom ℚ ℚ)
        (TrivSqZeroExt.inr 1)) (Polynomial.C x) = TrivSqZeroExt.inl x
      simp
    change Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom ℚ ℚ)
      (TrivSqZeroExt.inr 1))) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ))) = _
    rw [← Spec.map_comp, h, Category.comp_id]
    rfl
  reduction_map := by
    have h : CommRingCat.ofHom (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom ℚ ℚ)
          (TrivSqZeroExt.inr 1)) ≫ CommRingCat.ofHom
        (TrivSqZeroExt.fstHom (R := ℚ) (M := ℚ) (S := ℚ)).toRingHom =
      CommRingCat.ofHom (Polynomial.evalRingHom 0) := by
      ext x <;> simp
    rw [reduction, ← Spec.map_comp, h]
    rfl

-- The actual dual-number point moves in the source, while its square has no first-order motion.
example : (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom ℚ ℚ)
    (TrivSqZeroExt.inr 1 : DualNumbers ℚ)) Polynomial.X ≠ 0 := by
  have h : (TrivSqZeroExt.inr 1 : DualNumbers ℚ) ≠ 0 := by
    intro hz
    have h' := congrArg TrivSqZeroExt.snd hz
    norm_num at h'
  simpa using h

example : (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom ℚ ℚ)
    (TrivSqZeroExt.inr 1 : DualNumbers ℚ)) (Polynomial.X ^ 2) = 0 := by
  simp [pow_two]

end StableMapCompositionDifferentialsTest
