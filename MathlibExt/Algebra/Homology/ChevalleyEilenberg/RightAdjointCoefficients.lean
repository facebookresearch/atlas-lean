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
# Right Lie-module coefficients from exterior adjoint actions

Let L and S be Lie algebras over a commutative ring R, and let ι : S →ₗ⁅R⁆ L. Restrict the
adjoint action of L on ⋀[R]^n L along ι and negate it to obtain a right S-Lie-module
structure.

On a decomposable exterior word v₀ ∧ … ∧ v_(n−1), the right action of s is the sum of words
obtained by replacing v_i with ⁅v_i, ι(s)⁆. All terms in this action sum have positive
coefficient; the reversed bracket incorporates the negation of the left adjoint action.
-/

@[expose] public section

noncomputable section

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {S : Type w} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let S be another R-Lie algebra and ι : S →ₗ⁅R⁆ L. For n : ℕ,
rightAdjointCoefficients R L ι n is the right S-Lie-module with carrier ⋀[R]^n L, obtained by
restricting the degree adjoint representation along ι and negating its action. It lies in
RightLieModuleCat.{max u v} R S. -/
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

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let S be an R-Lie algebra, ι : S →ₗ⁅R⁆ L, n : ℕ, s : S and v : Fin n → L. The right
action of s on exteriorPower.ιMulti R n v equals ∑ i : Fin n, exteriorPower.ιMulti R n
(Function.update v i ⁅v_i, ι(s)⁆). The other entries retain their order, and every summand has
coefficient +1. -/
theorem rightAdjointCoefficients_pure (n : ℕ) (s : S) (v : Fin n → L) :
    (rightAdjointCoefficients R L ι n).action s (exteriorPower.ιMulti R n v) =
      ∑ i : Fin n, exteriorPower.ιMulti R n (Function.update v i ⁅v i, ι s⁆) := by
  rw [rightAdjointCoefficients_action]
  exact rightDegreeAdjointAction_pure R L ι n s v

end ChevalleyEilenberg
