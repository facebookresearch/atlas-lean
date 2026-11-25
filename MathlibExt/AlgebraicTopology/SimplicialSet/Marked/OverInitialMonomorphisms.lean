/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InitialMonomorphisms
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Native marked slice initial inclusions and original mono-right sections

The actual slice forgetful functor preserves the original initial object,
so its initial inclusions have the original marked monomorphisms as
underlying maps. Right lifting supplies an actual same-base section of
each mono-right map, retaining the strict original factorization equation.
No marked model or fibrancy premise is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked

/-- Every actual marked slice has the original initial-mono property. -/
theorem over_initialMonoClass (B : Marked.{u}) : InitialMonoClass (Over B) := by
  let _ : HasColimitsOfSize.{u, u} (Over B) :=
    CostructuredArrow.hasColimitsOfSize (G := 𝟭 Marked.{u}) (X := B)
  let _ : InitialMonoClass Marked.{u} := initialMonoClass
  let F : Over B ⥤ Marked.{u} := Over.forget B
  let _ : PreservesColimitsOfSize.{0, 0} F := inferInstance
  let _ : PreservesColimit (Functor.empty (Over B)) F :=
    (inferInstance : PreservesColimitsOfShape (Discrete PEmpty) F).preservesColimit
  let hI : IsInitial (⊥_ (Over B)).left := initialIsInitial.isInitialObj F _
  apply InitialMonoClass.of_initial
  intro X
  let _ : Mono (initial.to X).left := hI.mono_from _
  exact Over.mono_of_mono_left _

/-- A marked slice mono-right map has a genuine original same-base section. -/
theorem overMonoRight_exists_section {B : Marked.{u}} {X Y : Over B} (p : X ⟶ Y)
    (hp : (monomorphisms (Over B)).rlp p) : ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  let _ : HasColimitsOfSize.{u, u} (Over B) :=
    CostructuredArrow.hasColimitsOfSize (G := 𝟭 Marked.{u}) (X := B)
  let _ : InitialMonoClass (Over B) := over_initialMonoClass B
  let i : (⊥_ (Over B)) ⟶ Y := initial.to Y
  let _ : HasLiftingProperty i p := hp i inferInstance
  let sq : CommSq (initial.to X) i p (𝟙 Y) := ⟨initialIsInitial.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

end SSet.Marked
