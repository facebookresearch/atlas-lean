/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Subfunctor.PreimagePullback

/-!
# Tests for native subfunctor preimage pullbacks
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subfunctor.PreimagePullbackTest

variable {C : Type u} [Category.{v} C]
variable {F F' : C ⥤ Type w}

/-- Arbitrary original unions are retained literally by preimage. -/
example {ι : Type*} (G : ι → Subfunctor F) (p : F' ⟶ F) :
    (⨆ i, G i).preimage p = ⨆ i, (G i).preimage p :=
  Subfunctor.preimage_iSup G p

/-- The supplied native square retains its literal four maps. -/
example (G : Subfunctor F) (p : F' ⟶ F) :
    IsPullback (G.preimage p).ι (G.fromPreimage p) p G.ι :=
  G.preimage_isPullback p

/-- A monic ambient map gives both monicity and the expected total-point bound. -/
theorem monic_preimage_bounds (G : Subfunctor F) (p : F' ⟶ F) [Mono p] :
    Mono (G.fromPreimage p) ∧
      Cardinal.mk (G.preimage p).toFunctor.Elements ≤
        Cardinal.mk G.toFunctor.Elements :=
  ⟨inferInstance, G.mk_elements_preimage_le p⟩

/-- The pullback square keeps its original commuting equation. -/
example (G : Subfunctor F) (p : F' ⟶ F) :
    (G.preimage p).ι ≫ p = G.fromPreimage p ≫ G.ι :=
  (G.preimage_isPullback p).w

/-- The literal image seed has no more total points than its source. -/
example (G : Subfunctor F) {F'' : C ⥤ Type w} (p : F ⟶ F'') :
    Cardinal.mk (G.image p).toFunctor.Elements ≤
      Cardinal.mk G.toFunctor.Elements :=
  G.mk_elements_image_le p

end CategoryTheory.Subfunctor.PreimagePullbackTest
