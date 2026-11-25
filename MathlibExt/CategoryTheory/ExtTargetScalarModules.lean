/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Target-scalar modules on actual Ext groups

The scalar action is native Ext postcomposition with the degree-zero
class of the original target endomorphism. The module identities follow
from the native additive Ext composition and its associativity.
This is the action used when the target is the actual structure sheaf.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.ExtTargetScalarModules

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe w u v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (R : Type*) [Ring R] {X Y : C} (a : R →+* End Y) (n : ℕ)

/-- Actual target scalar postcomposition in the native Ext group. -/
def targetScalar (r : R) (e : Ext.{w} X Y n) : Ext.{w} X Y n :=
  e.comp (Ext.mk₀ (a r).asHom) (Nat.add_zero n)

/-- A target endomorphism-ring action induces this fixed module action on Ext. -/
@[instance_reducible] def targetModule : Module R (Ext.{w} X Y n) := by
  letI : SMul R (Ext.{w} X Y n) := ⟨targetScalar R a n⟩
  exact {
    smul := targetScalar R a n
    one_smul := by
      intro e
      change targetScalar R a n 1 e = e
      simp only [targetScalar, map_one, End.one_asHom, Ext.comp_mk₀_id]
    mul_smul := by
      intro r s e
      change targetScalar R a n (r * s) e =
        targetScalar R a n r (targetScalar R a n s e)
      simp only [targetScalar, map_mul, End.mul_asHom]
      rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
    smul_add := by
      intro r e f
      change targetScalar R a n r (e + f) =
        targetScalar R a n r e + targetScalar R a n r f
      exact Ext.add_comp _ _ _ _
    add_smul := by
      intro r s e
      change targetScalar R a n (r + s) e = targetScalar R a n r e + targetScalar R a n s e
      simp only [targetScalar, map_add, End.add_asHom, Ext.mk₀_add, Ext.comp_add]
    zero_smul := by
      intro e
      change targetScalar R a n 0 e = 0
      simp only [targetScalar, map_zero, End.zero_asHom, Ext.mk₀_zero, Ext.comp_zero]
    smul_zero := by
      intro r
      change targetScalar R a n r 0 = 0
      simp only [targetScalar, Ext.zero_comp] }

/-- The induced scalar action is exactly native target postcomposition. -/
theorem targetModule_smul (r : R) (e : Ext.{w} X Y n) :
    letI := targetModule (X := X) R a n
    r • e = e.comp (Ext.mk₀ (a r).asHom) (Nat.add_zero n) := rfl

end MathlibExt.CategoryTheory.ExtTargetScalarModules
