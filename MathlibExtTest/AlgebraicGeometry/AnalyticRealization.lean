/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AnalyticRealization

@[expose] public section

/-!
# Tests for the normalized analytic realization

The two input classes provide the charted-space and manifold instances on the
complex points, the regular-function map is determined by evaluation, constants
become constant holomorphic functions, and the module pullback and pushforward
along the realization are adjoint. The holomorphic modules form an abelian
category, as the derived-category statements built on them require.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Manifold ContDiff
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.AnalyticRealization

namespace MathlibExtTest.AlgebraicGeometry.AnalyticRealization

variable (X : ComplexScheme) (d : ℕ)

/-! ### Instances from the input classes -/

example [AnalyticManifold X d] : ChartedSpace (CoordinateSpace d) (space X) :=
  inferInstance

example [AnalyticManifold X d] :
    IsManifold 𝓘(ℂ, CoordinateSpace d) ∞ (space X) :=
  inferInstance

/-- The normalization leaves no choice of regular-function map. -/
example [AnalyticManifold X d] (a b : RegularFunctions X d) : a = b :=
  Subsingleton.elim a b

/-! ### Points and analytic opens -/

example (p : space X) : pointMap X p = ComplexPoints.schemePoint p := by
  simp

example (U : X.left.Opens) (p : space X) :
    p ∈ analyticOpen X U ↔ ComplexPoints.Mem p U := by
  simp

example : analyticOpen X ⊤ = ⊤ := by
  ext p
  simpa using ComplexPoints.mem_top p

variable [AnalyticManifold X d] [RegularFunctions X d]

/-! ### The regular-function map -/

/-- The holomorphic function attached to a regular function takes the values
of that regular function. -/
example (U : X.left.Opens) (g : Γ(X.left, U)) (p : analyticOpen X U) :
    (show C^∞⟮𝓘(ℂ, CoordinateSpace d), analyticOpen X U; 𝓘(ℂ), ℂ⟯ from
      RegularFunctions.regularMap.app (op U) g) p =
      ComplexPoints.eval g p.1 (mem_analyticOpen.mp p.2) :=
  RegularFunctions.regularMap_eval U g p

/-- Constants become constant holomorphic functions. -/
example (U : X.left.Opens) (c : ℂ) (p : analyticOpen X U) :
    (show C^∞⟮𝓘(ℂ, CoordinateSpace d), analyticOpen X U; 𝓘(ℂ), ℂ⟯ from
      RegularFunctions.regularMap.app (op U)
        (ComplexPoints.constHom (y := X.hom) U c)) p = c := by
  rw [RegularFunctions.regularMap_eval]
  exact ComplexPoints.eval_constHom c p.1 _

/-- The map of ringed spaces lies over the point map. -/
example : (ringedMap X d).hom.base = pointMap X := rfl

/-! ### Modules -/

example : Abelian (AnalyticModules X d) := inferInstance

example : AnalyticModules X d := SheafOfModules.unit (holomorphicRingSheaf X d)

example :
    (SheafOfModules.pushforward.{0} (F := Opens.map (pointMap X))
      (ringMap X d)).IsRightAdjoint :=
  inferInstance

example : pullback X d ⊣ pushforward X d := pullbackPushforwardAdjunction X d

example : (pullback X d).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction X d).isLeftAdjoint

/-- The pushforward of a holomorphic module has the same sections over a scheme
open as the module over its analytic open. -/
example (M : AnalyticModules X d) (U : X.left.Opens) :
    ((pushforward X d).obj M).val.obj (op U) =
      (ModuleCat.restrictScalars ((ringMap X d).hom.app (op U)).hom).obj
        (M.val.obj (op (analyticOpen X U))) :=
  rfl

end MathlibExtTest.AlgebraicGeometry.AnalyticRealization
