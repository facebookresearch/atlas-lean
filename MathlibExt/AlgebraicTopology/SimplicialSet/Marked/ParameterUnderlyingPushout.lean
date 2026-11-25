/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterSquareMonomorphisms

/-!
# The actual underlying parameter pushout-product

Forgetting the supplied markings preserves the actual pushout square.
The original whole simplicial map is therefore the pushout-product of
the same parameter and source maps, through the canonical pushout-point
comparison. Native simplicial monomorphism pushout-products prove that
these original marked maps are monic; no adhesive marked-category or
marked-model hypothesis is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- The actual marked pushout keeps the original simplicial pushout square and whole comparison map. -/
def parameterUnderlyingPushout {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) : (curriedTensor SSet.{u}).flip.PushoutObjObj f.hom a :=
  underlyingParameterSquare (parameterPushout a f)

/-- The underlying native marked parameter map is literally this whole simplicial comparison. -/
@[simp]
theorem parameterUnderlyingPushout_ι {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) :
    (parameterUnderlyingPushout a f).ι = (parameterPushoutProduct a f).hom := rfl

/-- The actual underlying pushout point is canonically compared with the same original simplicial pushout-product. -/
def parameterUnderlyingPushoutIso {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) :
    Arrow.mk (parameterPushoutProduct a f).hom ≅ (Arrow.mk a □ Arrow.mk f.hom) :=
  underlyingParameterSquareIso (parameterPushout a f)

/-- Monic original parameter and source maps give a genuine marked parameter pushout-product monomorphism. -/
theorem parameterPushoutProduct_mono {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) [Mono a] [Mono f] : Mono (parameterPushoutProduct a f) :=
  parameterSquare_mono (parameterPushout a f)

end SSet.Marked
