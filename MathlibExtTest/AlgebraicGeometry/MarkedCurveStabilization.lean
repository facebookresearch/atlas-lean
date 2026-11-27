/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.MarkedCurveStabilization
import MathlibExt.AlgebraicGeometry.StableCurveStackModels

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

namespace MarkedCurveStabilizationTest

universe u

/-- The standard node is nodal at every point, closed or not: it is its own chart. -/
example (k : Type u) [Field k] : IsNodal (nodeCurve k) := fun x ↦
  ⟨(nodeCurve k).left, 𝟙 _, x, 𝟙 _, inferInstance, inferInstance, rfl, rfl⟩

/-- Nodality is tested at points that need not be closed. -/
example {k : Type u} [Field k] (C : Over (Spec (.of k))) (h : IsNodal C) (x : C.left) :
    ∃ (V : Scheme.{u}) (a : V ⟶ C.left) (v : V), Etale a ∧ a v = x := by
  obtain ⟨V, a, v, _, ha, _, hv, _⟩ := h x
  exact ⟨V, a, v, ha, hv⟩

/-- A relative marking gives a section of the geometric fibre over the field. -/
example {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {Ω : Type u} [Field Ω] (p : Spec (.of Ω) ⟶ S) :
    fiberMark f s hs p ≫ (fiberCurve f p).hom = 𝟙 _ := by
  simp [fiberMark, fiberCurve]

/-- The fibre point lies over the marking. -/
example {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {Ω : Type u} [Field Ω] (p : Spec (.of Ω) ⟶ S) :
    fiberMark f s hs p ≫ pullback.fst f p = p ≫ s :=
  pullback.lift_fst _ _ _

/-- The identity is a marked automorphism. -/
example {k : Type u} [Field k] (C : Over (Spec (.of k))) (n : ℕ)
    (p : Fin n → (Spec (.of k) ⟶ C.left)) : MarkedAut C n p :=
  ⟨Iso.refl C, fun _ ↦ by simp⟩

open MathlibExt.AlgebraicGeometry.StableCurveStackModels in
/-- Pure dimension requires a cycle atlas, so it cannot hold vacuously. -/
example {k : Type} [Field k]
    (X : AlgebraicGeometry.StackCycleGeometry.Stack (Spec (.of k))) (d : ℤ)
    (h : HasDimension X d) :
    Nonempty (AlgebraicGeometry.StackCycleGeometry.CycleAtlas X) :=
  h.1

/-- A genus-preserving contraction makes the canonical structure-sheaf map `𝒪_Y ⟶ f_* 𝒪_X` an
isomorphism (not merely gives some abstract isomorphism). -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) (h : IsGenusPreservingContraction f) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :
      MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.structureModule Y ⟶
        (Scheme.Modules.pushforward f).obj
          (MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.structureModule X)) :=
  h.2.2.1

end MarkedCurveStabilizationTest
