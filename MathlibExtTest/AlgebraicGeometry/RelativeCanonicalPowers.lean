/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers

/-! # Biduality fidelity and direction of the canonical open-extension map -/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.RelativeCanonicalPowers

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
open MathlibExt.AlgebraicGeometry.ModuleInternalHom

/-- The normalized biduality map cannot collapse a nonzero actual unit section. -/
example (X : Scheme.{0}) (E : Biduality (structureModule X)) (U : X.Opens) :
    Function.Injective (E.map.app U) := by
  intro s t h
  let b : Γ(dual (structureModule X), U) :=
    𝟙 ((restrFun X.presheaf U).obj (structureModule X).val)
  have hs := E.normalized U s b
  have ht := E.normalized U t b
  have hv := congrArg (fun z =>
    localHomValue X (dual (structureModule X)) (structureModule X) U z b) h
  rw [hs, ht] at hv
  exact hv

/-- In the globally invertible case, the open-extension constructor has the expected inverse
direction even though its body uses only the open adjunction and target Hartogs unit. -/
example {X : Scheme.{0}} (U : X.Opens) {A M N : X.Modules}
    (e : A ⟶ M) [IsIso e] (β : A ⟶ N)
    (hE : IsIso ((Scheme.Modules.pullback U.ι).map e))
    (hN : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app N)) :
    (extendAcrossOpen U e β hE hN).val = inv e ≫ β := by
  symm
  apply (extendAcrossOpen U e β hE hN).property.2
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end MathlibExtTest.AlgebraicGeometry.RelativeCanonicalPowers
