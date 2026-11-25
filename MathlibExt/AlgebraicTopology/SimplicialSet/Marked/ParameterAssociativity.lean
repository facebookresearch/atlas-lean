/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPushoutProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Actual associativity of native marked parameter corners

The two scalar parameters and original marked source form the same
native three-coordinate product. The canonical Leibniz associator,
original max-product comparison and actual pushout-point isomorphisms
compare the two complete corner maps. All original markings and scalar
corner maps are retained. This is a carrier-level comparison without
marked-model or lifting hypotheses.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] cartesianMonoidalCategory monoidalClosed
/-- The original marked product symmetry supplies the local native Leibniz associator. -/
local instance parameterCornerBraided : BraidedCategory Marked.{u} := .ofCartesianMonoidalCategory

/-- The two complete original parameter corners are the same scalar-corner action through the actual native
  Leibniz associator. -/
def parameterPushoutProductAssociativityIso {A D K L : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (b : K ⟶ L) (f : X ⟶ Y) :
    Arrow.mk (parameterPushoutProduct a (parameterPushoutProduct b f)) ≅
      Arrow.mk (parameterPushoutProduct (Arrow.mk a □ Arrow.mk b).hom f) := by
  let am := Arrow.mk (maximal.map a)
  let bm := Arrow.mk (maximal.map b)
  let fm := Arrow.mk f
  let e₁ := parameterPushoutProductCanonicalIso a (parameterPushoutProduct b f)
  let e₂ := (MonoidalCategory.Arrow.pushoutProduct.obj am).mapIso (parameterPushoutProductCanonicalIso b f)
  let e₃ := (MonoidalCategory.Arrow.PushoutProduct.associator am bm fm).symm
  let e₄ := (MonoidalCategory.Arrow.pushoutProduct.flip.obj fm).mapIso (maximalPushoutProductIso a b).symm
  let e₅ := (parameterPushoutProductCanonicalIso (Arrow.mk a □ Arrow.mk b).hom f).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

end SSet.Marked

namespace SSet.Marked

attribute [local instance] cartesianMonoidalCategory monoidalClosed
/-- The same marked product symmetry is retained locally for the target-component characteristic. -/
local instance parameterCornerCharacteristicBraided : BraidedCategory Marked.{u} := .ofCartesianMonoidalCategory

/-- The complete parameter-corner comparison uses the same original three-coordinate product multiplication
  on its target. -/
theorem parameterPushoutProductAssociativityIso_hom_right {A D K L : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (b : K ⟶ L) (f : X ⟶ Y) :
    (parameterPushoutProductAssociativityIso a b f).hom.right =
      (prodAssociator (max D) (max L) Y).inv ≫
        prodMap (maxProductIso D L).hom (𝟙 Y) := by
  apply Hom.ext
  rfl

end SSet.Marked
