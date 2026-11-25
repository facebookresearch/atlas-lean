/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Actual local tensor and power maps for metrized line fibres

Local tensor sections are the native pure tensors followed by the
specific module-sheafification unit. Power sections use this actual map
recursively, including the exponent-zero structure-section unit.

Fibre power maps retain the actual line-sheaf power and every original
local section evaluation, as well as all completed-field homogeneous
scalars. These normalizations determine the one-dimensional power map;
its construction is separate from rational model approximation.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 2.1 and A.5.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.MetrizedFibrePowerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries
open scoped TensorProduct

variable {X : Scheme.{0}} (L M : X.Modules)

/-- The original local tensor section, through the actual sheafification unit. -/
def tensorSectionAt (U : X.Opens) (s : Γ(L,U)) (t : Γ(M,U)) :
    Γ(CurvePositivity.moduleTensor X L M,U) := by
  let P := PresheafOfModulesOfCommRing.{0} X.sheaf.obj
  let T := ((curriedTensor P).obj L.val).obj M.val
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app T).app
    (op U) (s ⊗ₜ[X.presheaf.obj (op U)] t)

/-- The actual local power-section map, including the empty tensor. -/
def powerSectionAt (U : X.Opens) (s : Γ(L,U)) :
    (n : ℕ) → Γ(CurvePositivity.power L n,U)
  | 0 => (1 : X.presheaf.obj (op U))
  | n+1 => tensorSectionAt (CurvePositivity.power L n) L U (powerSectionAt U s n) s

variable (K : Type) [NormedField K] (Y : Over (Spec (.of K))) (F : Y.left.Modules)

/-- Fibre power data is fixed on every genuine local section and scalar. -/
structure PowerFibre (n : ℕ) where
  map : ∀ p : ValuedLineFibres.Point K Y,
    ValuedLineFibres.Fibre K Y F p →
      ValuedLineFibres.Fibre K Y (CurvePositivity.power F n) p
  homogeneous : ∀ (p : ValuedLineFibres.Point K Y)
    (a : ValuedLineFibres.CompletedResidue K Y p) (v : ValuedLineFibres.Fibre K Y F p),
    map p (a • v) = a ^ n • map p v
  section_normalized : ∀ (U : Y.left.Opens) (s : Γ(F,U))
    (p : ValuedLineFibres.Point K Y) (hp : p.schemePoint ∈ U),
    map p (ValuedLineFibres.evaluateSection K Y F s p hp) =
      ValuedLineFibres.evaluateSection K Y (CurvePositivity.power F n)
        (powerSectionAt F U s n) p hp
  nonzero : 0 < n → ∀ p v, v ≠ 0 → map p v ≠ 0

end MathlibExt.AlgebraicGeometry.MetrizedFibrePowerModels
