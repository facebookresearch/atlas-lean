/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DivisorDynamics

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.DivisorDynamics

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.NumericalCurveCones

universe u

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

-- Iterates: `f^0 = 𝟙` and `f^{n+1} = f^n ≫ f`.
example (f : X ⟶ X) : iterateMap f 0 = 𝟙 X := rfl

example (f : X ⟶ X) (n : ℕ) : iterateMap f (n + 1) = iterateMap f n ≫ f := rfl

-- The empty tensor product is the structure sheaf.
example {d : ℕ} (L : Fin d → X.left.Modules) :
    selectedTensor L ∅ = structureModule X.left := by
  simp [selectedTensor]

-- The truncated Euler sum of degree zero is `h⁰`.
example (M : X.left.Modules) :
    truncatedEuler X 0 M = Module.finrank k (cohomology X.hom M 0) := by
  simp [truncatedEuler]

-- The zero class is an effective combination of curves, hence in the Mori cone.
example : (0 : N1 X) ∈ effectiveCombinations X :=
  ⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, by simp⟩

example : (0 : N1 X) ∈ moriCone X :=
  subset_closure ⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, by simp⟩

variable [IsProper X.hom]

-- `d = 0`: the intersection number of no line bundles is `χ(𝒪_X)`.
example (hd : topologicalKrullDim X.left ≤ (0 : ℕ)) (L : Fin 0 → LineBundle X.left) :
    mixedIntersection X 0 hd L = truncatedEuler X 0 (structureModule X.left) := by
  simp [mixedIntersection, selectedTensor]

-- `d = 1`: the intersection number of one line bundle is `χ(L) - χ(𝒪_X)`, its degree.
example (hd : topologicalKrullDim X.left ≤ (1 : ℕ)) (L : Fin 1 → LineBundle X.left) :
    mixedIntersection X 1 hd L =
      truncatedEuler X 1 (selectedTensor (fun i ↦ (L i).val) {0}) -
        truncatedEuler X 1 (structureModule X.left) := by
  have h : (Finset.univ : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  rw [mixedIntersection, h, Finset.sum_pair (by simp)]
  simp [selectedTensor]
  ring

-- The first two terms of the growth sequence: `deg₁ f` and `√(deg₁ (f ∘ f))`.
example (d : ℕ) (hd : topologicalKrullDim X.left = d) (hd₀ : 0 < d) (H : LineBundle X.left)
    (f : X ⟶ X) :
    degreeGrowth d hd hd₀ H f 0 = max 0 (firstDegree d hd hd₀ H (𝟙 X ≫ f) : ℝ) := by
  simp [degreeGrowth, iterateMap]

example (d : ℕ) (hd : topologicalKrullDim X.left = d) (hd₀ : 0 < d) (H : LineBundle X.left)
    (f : X ⟶ X) :
    degreeGrowth d hd hd₀ H f 1 =
      Real.sqrt (max 0 (firstDegree d hd hd₀ H ((𝟙 X ≫ f) ≫ f) : ℝ)) := by
  norm_num [degreeGrowth, iterateMap, Real.sqrt_eq_rpow]

end MathlibExt.AlgebraicGeometry.DivisorDynamics
