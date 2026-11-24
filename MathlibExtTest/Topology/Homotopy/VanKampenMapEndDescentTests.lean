/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Topology.Homotopy.VanKampenMapEndDescent
import MathlibExt.CategoryTheory.Groupoid.FullOfMapEnd

noncomputable section

open CategoryTheory
open MathlibExt.Topology.Homotopy.VanKampenWanted

universe u v

#check @Functor.full_of_surjective_mapEnd
#print axioms Functor.full_of_surjective_mapEnd
#check @SingleObj.map_eq_conjugate_of_eq_mapEnd
#print axioms SingleObj.map_eq_conjugate_of_eq_mapEnd
#check @SingleObj.comp_objectAdjustment_eq
#print axioms SingleObj.comp_objectAdjustment_eq
#check @exists_globalFunctor_of_overlap_mapEnd_eq
#print axioms exists_globalFunctor_of_overlap_mapEnd_eq

-- The original outside End map and the second region's actual functor survive.
example {D : Type u} [TopologicalSpace D] {U V : Set D}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {G : Type v} [Group G]
    (F_U : FundamentalGroupoid U ⥤ SingleObj G)
    (F_V : FundamentalGroupoid V ⥤ SingleObj G)
    (b : FundamentalGroupoid ↥(U ∩ V))
    (β : ∀ c : FundamentalGroupoid ↥(U ∩ V), b ⟶ c)
    (hEnd : ∀ e : End b,
      (F_U.map ((FundamentalGroupoid.map (inclusionInterLeft U V)).map e.asHom) : G) =
        (F_V.map ((FundamentalGroupoid.map (inclusionInterRight U V)).map e.asHom) : G)) :
    ∃ F : FundamentalGroupoid D ⥤ SingleObj G,
      FundamentalGroupoid.map (inclusionSub V) ⋙ F = F_V ∧
        ∀ p : U, p.val ∉ V → ∀ e : End (FundamentalGroupoid.mk p),
          (F.map ((FundamentalGroupoid.map (inclusionSub U)).map e.asHom) : G) =
            (F_U.map e.asHom : G) :=
  exists_globalFunctor_of_overlap_mapEnd_eq hU hV hcover F_U F_V b β hEnd

end
