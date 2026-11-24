/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The scalar-stable projector-morphism pattern is adapted from AxiomMath/Stacks,
revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/CategoryTheory/Graded/TwistedKaroubi.lean (instLinear),
licensed under Apache 2.0. Modification notice: specialize the construction
to Mathlib's ordinary Karoubi envelope and retain its existing additive
group structure. All module and composition laws are proved here.
-/

module
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Linear.Basic
/-!
# Linear structure on Mathlib's Karoubi envelope

The scalar multiple of a projector-compatible morphism remains projector-
compatible. This gives the actual module on Karoubi morphisms and proves
that composition is linear in both arguments. This completed adapter is used
by rational Chow-projector realization; no new idempotent-completion theorem
is requested.
-/

@[expose] public noncomputable section
namespace MathlibExt.CategoryTheory.LinearKaroubi
open _root_.CategoryTheory _root_.CategoryTheory.Idempotents
universe u v w
variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

instance homSMul (M N : Karoubi C) : SMul R (M ⟶ N) where
  smul r f := ⟨r • f.f, by rw [Linear.smul_comp, Linear.comp_smul, f.comm]⟩

instance homModule (M N : Karoubi C) : Module R (M ⟶ N) where
  one_smul f := by ext; exact one_smul R f.f
  mul_smul r s f := by ext; exact mul_smul r s f.f
  zero_smul f := by ext; exact zero_smul R f.f
  smul_zero r := by ext; exact smul_zero r
  smul_add r f g := by ext; exact smul_add r f.f g.f
  add_smul r s f := by ext; exact add_smul r s f.f

instance linearKaroubi : Linear R (Karoubi C) where
  homModule M N := homModule M N
  smul_comp M N O r f g := by ext; exact Linear.smul_comp M.X N.X O.X r f.f g.f
  comp_smul M N O f r g := by ext; exact Linear.comp_smul M.X N.X O.X f.f r g.f

end MathlibExt.CategoryTheory.LinearKaroubi
