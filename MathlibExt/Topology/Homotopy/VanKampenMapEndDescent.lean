/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.VanKampen
public import MathlibExt.CategoryTheory.SingleObj.Descent

/-!
# Computed based descent through an actual open-cover diagram

The original overlap End equality determines the connector weights. The
existing object adjustment makes the overlap restrictions strictly equal,
so the actual van Kampen universal property constructs a global functor.
At every original first-region point outside the second region, its entire
based End map is unchanged. No global functor or restriction witness is
supplied.
-/

noncomputable section

open CategoryTheory

universe u v

namespace MathlibExt.Topology.Homotopy.VanKampenWanted

/-- Original overlap End compatibility gives actual global descent,
preserving every original outside End map and the second-region functor. -/
public theorem exists_globalFunctor_of_overlap_mapEnd_eq
    {D : Type u} [TopologicalSpace D] {U V : Set D}
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
            (F_U.map e.asHom : G) := by
  let I_L := FundamentalGroupoid.map (inclusionInterLeft U V)
  let I_R := FundamentalGroupoid.map (inclusionInterRight U V)
  let F_L := I_L ⋙ F_U
  let F_R := I_R ⋙ F_V
  let w (c : FundamentalGroupoid ↥(U ∩ V)) : G :=
    (F_L.map (β c) : G) * (F_R.map (β c) : G)⁻¹
  have hI : Function.Injective I_L.obj := by
    intro c d h
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    have hpoint := congrArg FundamentalGroupoid.as h
    exact congrArg (fun p : U => p.val) hpoint
  have hformula : ∀ {c d : FundamentalGroupoid ↥(U ∩ V)} (f : c ⟶ d),
      (F_U.map (I_L.map f) : G) = w d * (F_R.map f : G) * (w c)⁻¹ := by
    intro c d f
    exact SingleObj.map_eq_conjugate_of_eq_mapEnd F_L F_R b β hEnd f
  let F_U' := SingleObj.objectAdjustment I_L F_U w
  have hcompat : I_L ⋙ F_U' = I_R ⋙ F_V :=
    SingleObj.comp_objectAdjustment_eq I_L F_U F_R w hI hformula
  obtain ⟨F, hfirst, hsecond⟩ :=
    (seifert_vanKampen_fundamentalGroupoid_universalProperty hU hV hcover
      F_U' F_V hcompat).2.exists
  refine ⟨F, hsecond, ?_⟩
  intro p hp e
  have hout : FundamentalGroupoid.mk p ∉ Set.range I_L.obj := by
    rintro ⟨c, hc⟩
    have hpoint := congrArg (fun d : FundamentalGroupoid U => d.as.val) hc
    change c.as.val = p.val at hpoint
    exact hp (hpoint ▸ c.as.property.2)
  have hglobal := congrArg
    (fun K : FundamentalGroupoid U ⥤ SingleObj G => (K.map e.asHom : G)) hfirst
  change (F.map ((FundamentalGroupoid.map (inclusionSub U)).map e.asHom) : G) =
    (F_U'.map e.asHom : G) at hglobal
  exact hglobal.trans
    (SingleObj.objectAdjustment_map_of_not_mem_range I_L F_U w e.asHom hout hout)

end MathlibExt.Topology.Homotopy.VanKampenWanted

end
