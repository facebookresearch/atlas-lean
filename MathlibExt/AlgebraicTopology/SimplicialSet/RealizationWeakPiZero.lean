/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnitPiZero
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne

/-!
# Realization weak equivalences preserve original simplicial components

The original component map is bijective at every value universe. No Kan,
nonempty, connectedness, basepoint or model-category input is required for
its endpoints. The proof uses the genuine realization–singular image map,
both all-object unit component bijections, and the whole naturality square.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory

namespace SSet

/-- A realization weak equivalence preserves the original simplicial components,
at every universe and without any Kan or inhabitedness assumption. -/
theorem realizationWeakEquivalences.bijective_mapπ₀
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : realizationWeakEquivalences f) :
    Function.Bijective (mapπ₀ f) := by
  let R := SSet.toTop.{u} ⋙ TopCat.toSSet.{u}
  have hRf : KanComplex.W (R.map f) := by
    change KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))
    exact (mem_realizationWeakEquivalences_iff f).1 hf
  have hR := KanComplex.W.bijective_mapπ₀ hRf
  have hX := bijective_mapπ₀_sSetTopAdj_unit_app X
  have hY := bijective_mapπ₀_sSetTopAdj_unit_app Y
  have hnat : mapπ₀ (sSetTopAdj.unit.app Y) ∘ mapπ₀ f =
      mapπ₀ (R.map f) ∘ mapπ₀ (sSetTopAdj.unit.app X) := by
    funext x
    simpa only [R, Functor.id_map, Functor.comp_map, mapπ₀_comp_apply,
      Function.comp_apply] using
      congrArg (fun g => mapπ₀ g x) (sSetTopAdj.{u}.unit.naturality f)
  have hcomp : Function.Bijective
      (mapπ₀ (sSetTopAdj.unit.app Y) ∘ mapπ₀ f) := by
    rw [hnat]
    exact hR.comp hX
  exact Function.Bijective.of_comp_left hcomp hY.1

end SSet
