/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
public import MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals
public import Mathlib.Data.ZMod.Basic

/-! # Rational-function empty sections, divisor effectivity and actual Cartier trace images -/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.DivisorialFrobenius

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RationalFunctionModules
open MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals

/-- A rational-function sheaf has zero empty-open sections; a constant field presheaf would fail. -/
example (X : Scheme.{0}) [IrreducibleSpace X] (s : Γ(rationalFunctions X, ⊥)) : s = 0 :=
  TopCat.Presheaf.section_ext
    ⟨(rationalFunctions X).presheaf, (rationalFunctions X).isSheaf⟩
    ⊥ s 0 (by intro x hx; exact False.elim hx)

/-- The actual O(D) order bound contains one precisely for an effective local divisor. -/
example {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    (D : IntegerWeil V) (U : V.X.left.Opens) [Nonempty U] :
    (rationalFunctionsEquiv U).symm 1 ∈ DivisorialModuleSheaves.sections V D U ↔
      ∀ p : PrimePoint V, p.val ∈ U → 0 ≤ D p := by
  rw [DivisorialModuleSheaves.mem_sections]
  have : Nonempty (⊤ : V.X.left.Opens) := ⟨⟨genericPoint V.X.left, by trivial⟩⟩
  have hord (p : PrimePoint V) : V.X.left.ord (1 : FunctionField V) p.val = 0 := by
    simpa only [map_one] using
      V.X.left.ord_of_isUnit (U := ⊤) (f := (1 : Γ(V.X.left,⊤))) isUnit_one
        (x := p.val) (by trivial)
  simp only [LinearEquiv.apply_symm_apply, one_ne_zero, false_or, hord, neg_nonpos]

private def identityTrace : CartierTrace (ZMod 2) 2 1 where
  toAddMonoidHom := AddMonoidHom.id _
  scalar := by decide

private def zeroTrace : CartierTrace (ZMod 2) 2 1 where
  toAddMonoidHom := 0
  scalar := by simp

/-- A genuine nonzero trace has full image in the field case. -/
example : imageIdeal identityTrace = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  exact ⟨1, rfl⟩

/-- A non-splitting zero trace is allowed and has zero image, not a silently assumed splitting. -/
example : imageIdeal zeroTrace = ⊥ := by
  ext a
  simp [imageIdeal, zeroTrace, eq_comm]

end MathlibExtTest.AlgebraicGeometry.DivisorialFrobenius
