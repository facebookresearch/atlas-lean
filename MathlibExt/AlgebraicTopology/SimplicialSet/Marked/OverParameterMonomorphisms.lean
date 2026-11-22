/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterLeibniz
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterSquareMonomorphisms

/-!
# Original marked parameter monomorphisms over any base

The supplied original marked slice retains its exact underlying parameter
pushout square. Native simplicial monicity transfers through that original
square and the faithful slice forgetful functor. Thus both parameter
boundaries and horns keep their actual marked monomorphism assertions;
no Kan or quasicategory base, right properness or marked-model premise is
required.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- Monic original parameter and slice source maps give a monic whole marked slice pushout-product. -/
theorem overParameterPushoutProduct_mono {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) [Mono a] [Mono f] : Mono (overParameterPushoutProduct a f) := by
  let _ : Mono f.left := Over.mono_left_of_mono f
  let _ : Mono (overParameterPushoutProduct a f).left :=
    parameterSquare_mono (overParameterUnderlyingPushout a f)
  exact Over.mono_of_mono_left _

/-- Every original boundary parameter retains its whole marked slice monomorphism. -/
theorem overParameterBoundary_mono {Z : Marked.{u}} {X Y : Over Z}
    (f : X ⟶ Y) [Mono f] (n : ℕ) :
    Mono (overParameterPushoutProduct (boundary.{u} n).ι f) :=
  overParameterPushoutProduct_mono _ f

/-- Every original horn parameter retains the same native marked slice monomorphism. -/
theorem overParameterHorn_mono {Z : Marked.{u}} {X Y : Over Z}
    (f : X ⟶ Y) [Mono f] (n : ℕ) (i : Fin (n + 1)) :
    Mono (overParameterPushoutProduct (horn.{u} n i).ι f) :=
  overParameterPushoutProduct_mono _ f

end SSet.Marked
