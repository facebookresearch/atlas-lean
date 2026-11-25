/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.DegreeAdjoint
public import MathlibExt.Algebra.Category.RightLieModuleCat.Basic

/-!
# Right-adjoint Chevalley–Eilenberg coefficients

Negating the adjoint representation in each exterior degree gives a right
Lie-module object. Its action is the alternating right-adjoint formula, on
the same coefficient carrier as the corresponding left representation.
-/

@[expose] public section

noncomputable section

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {S : Type w} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)

/-- The right-adjoint coefficient object, from the native left object. -/
def rightAdjointCoefficients (n : ℕ) : RightLieModuleCat.{max u v} R S :=
  RightLieModuleCat.fromLeft (LieModuleCat.restrictObj ι (degreeAdjointModule R L n))

@[simp]
theorem rightAdjointCoefficients_action (n : ℕ) (s : S) (a : ⋀[R]^n L) :
    (rightAdjointCoefficients R L ι n).action s a = rightDegreeAdjointAction R L ι n s a := by
  let M := LieModuleCat.restrictObj ι (degreeAdjointModule R L n)
  have h₁ := RightLieModuleCat.fromLeft_action M s (show M from a)
  have h₂ := LieModuleCat.restrictObj_lie ι (degreeAdjointModule R L n) s (show M from a)
  have h₃ := degreeAdjointModule_lie R L n (ι s) (show degreeAdjointModule R L n from a)
  exact h₁.trans (congrArg Neg.neg (h₂.trans h₃))

/-- The right-L coefficient object retains the alternating formula. -/
theorem rightAdjointCoefficients_pure (n : ℕ) (s : S) (v : Fin n → L) :
    (rightAdjointCoefficients R L ι n).action s (exteriorPower.ιMulti R n v) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅v i, ι s⁆) := by
  rw [rightAdjointCoefficients_action]
  exact rightDegreeAdjointAction_pure R L ι n s v

end ChevalleyEilenberg
