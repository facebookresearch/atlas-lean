/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOverTrivialFibration

noncomputable section

open CategoryTheory HomotopicalAlgebra CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

universe u

#check SSet.HomotopyRelOver.ofTrivialFibration
#print axioms SSet.HomotopyRelOver.ofTrivialFibration

namespace SSet

variable {K E B : SSet.{u}} (S : K.Subcomplex)
variable (p : E ⟶ B) (hp : trivialFibrations SSet.{u} p) (f₀ f₁ : K ⟶ E)
variable (hS : S.ι ≫ f₀ = S.ι ≫ f₁) (hP : f₀ ≫ p = f₁ ≫ p)

-- The domain, total space, base and relative subcomplex are arbitrary.
example : HomotopyRelOver p f₀ f₁ S :=
  HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP

-- The result interoperates with the canonical relative homotopy consumer.
example : HomotopyRel f₀ f₁ S :=
  (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).toHomotopyRel

example :
    SSet.ι₀ ≫ (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).h = f₀ ∧
      SSet.ι₁ ≫ (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).h = f₁ :=
  ⟨(HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).h₀,
    (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).h₁⟩

-- This is an equality of maps on the entire cylinder, not a pointwise premise.
example :
    (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).h ≫ p =
      fst K (Δ[1] : SSet.{u}) ≫ (f₀ ≫ p) :=
  (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).over_eq

-- All simplex degrees and all interval simplices preserve the actual subcomplex.
example (n : SimplexCategoryᵒᵖ) (x : K.obj n) (hx : x ∈ S.obj n)
    (t : (Δ[1] : SSet.{u}).obj n) :
    (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).h.app n (x, t) =
      f₀.app n x :=
  (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).stationary hx t

-- The constructed result works directly with the existing fiberwise symmetry API.
example : HomotopyRelOver p f₁ f₀ S := by
  let _ : Fibration p := (mem_trivialFibrations_iff p).mp hp |>.1
  exact (HomotopyRelOver.ofTrivialFibration S p hp f₀ f₁ hS hP).symm

end SSet

end
