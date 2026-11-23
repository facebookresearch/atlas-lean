/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Module.Torsion.TateModuleComparison

/-!
Tests for the comparison of the Tau Ceti Tate-module carrier with the root `TateModule`: the
equivalence is the identity on components, transports the `ℤ_p`-actions into each other (checked
against the root carrier's own description of natural-number scalars), and is natural.
-/

namespace MathlibExtTest.Algebra.Module.Torsion.TateModuleComparison

open MathlibExt.Algebra.Module MathlibExt.Algebra.Module.Torsion.TateModule

variable {p : ℕ} {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The equivalence and its inverse are mutually inverse. -/
example (x : Torsion.TateModule p A) : equivRoot.symm (equivRoot x) = x := by simp
example (y : _root_.TateModule p A) : equivRoot (equivRoot.symm y) = y := by simp

/-- Components are preserved, so the root projections read off the Tau Ceti ones. -/
example (x : Torsion.TateModule p A) (n : ℕ) :
    _root_.TateModule.proj p A n (equivRoot x) = (proj n x : A) :=
  root_proj_equivRoot x n

/-- Addition is preserved componentwise. -/
example (x y : Torsion.TateModule p A) (n : ℕ) :
    ((equivRoot (x + y) : _root_.TateModule p A) : ℕ → A) n = (proj n x : A) + (proj n y : A) := by
  simp

section Padic

variable [Fact p.Prime]

/-- A natural-number scalar acts on each component of the transported point by repeated addition,
computed on the root side by `TateModule.natCast_padicInt_smul_apply`. -/
example (c : ℕ) (x : Torsion.TateModule p A) (n : ℕ) :
    (proj n ((c : ℤ_[p]) • x) : A) = (c : ℤ) • (proj n x : A) := by
  have h := congrArg (fun y : _root_.TateModule p A ↦ (y : ℕ → A) n)
    (linearEquivRoot.map_smul (c : ℤ_[p]) x)
  rw [_root_.TateModule.natCast_padicInt_smul_apply] at h
  exact h

/-- The `ℤ_p`-linear comparison transports scalar multiplication. -/
example (a : ℤ_[p]) (x : Torsion.TateModule p A) :
    linearEquivRoot (a • x) = a • linearEquivRoot x :=
  map_smul linearEquivRoot a x

/-- The comparison commutes with the maps induced by an additive homomorphism. -/
example (f : A →+ B) (x : Torsion.TateModule p A) (n : ℕ) :
    ((linearEquivRoot (mapLinearMap (p := p) f x) : _root_.TateModule p B) : ℕ → B) n =
      f (proj n x) :=
  linearEquivRoot_mapLinearMap f x n

end Padic

end MathlibExtTest.Algebra.Module.Torsion.TateModuleComparison

#print axioms MathlibExt.Algebra.Module.Torsion.TateModule.linearEquivRoot
#print axioms MathlibExt.Algebra.Module.Torsion.TateModule.equivRoot_map
