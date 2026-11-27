/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticMeromorphicCoordinates

/-!
# Punctured parameter unit

The pole-chart parameter restricts to a unit on the punctured chart.

Source: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1;
Beauville--Laszlo, *Un lemme de descente*.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates

/-- Let $p$ be a prime, $E$ a field, $d : D → X$ a morphism of analytic adic spaces over $E$ and
$U$ a puncture of $d$ (an open embedding with isomorphic stalks onto the complement of the image
of $d$), and assume that $d$ has a Cartier atlas (`CartierAtlas`: it is a closed embedding with
surjective stalk maps, covered by pole charts). Then for every pole chart $Q$ of $d$
(`PoleChart`), its parameter $t$ restricts to a unit on the punctured chart of $Q$. -/
public theorem punctured_parameter_unit
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (A : CartierAtlas p E d U) (Q : PoleChart p E d U) :
    IsUnit (sectionMap p E Q.puncture.map Q.parameter) := by
  have _ := A
  let Xt := Q.space.left.obj.space
  let Pt := Q.puncture.space.left.obj.space
  let Dt := Q.divisor.left.obj.space
  let fL := Q.puncture.map.left.hom.val
  let gL := Q.divisorMap.left.hom.val
  have hcompl : Set.range ⇑fL.base = (Set.range ⇑gL.base)ᶜ :=
    Q.puncture.complement
  let V0 : TopologicalSpace.Opens Xt :=
    ⟨Set.range ⇑fL.base, Q.puncture.open_embedding.isOpen_range⟩
  have hV0_coe : (V0 : Set Xt) = Set.range ⇑fL.base := rfl
  have hpre : ⇑gL.base ⁻¹' (V0 : Set Xt) = ∅ := by
    rw [hV0_coe, hcompl]
    apply Set.eq_empty_of_forall_notMem
    intro y hy
    exact hy (Set.mem_range_self y)
  have hmap : (TopologicalSpace.Opens.map gL.base).obj V0 = ⊥ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.map_coe]
    change ⇑gL.base ⁻¹' (V0 : Set Xt) = _
    rw [hpre]
    rfl
  have hterm := Dt.toSheafedSpace.sheaf.isTerminalOfEmpty
  have hsub_empty : Subsingleton ↑(Dt.presheaf.obj (op ⊥)) :=
    CommRingCat.subsingleton_of_isTerminal hterm
  have hsub_mid :
      Subsingleton ↑(Dt.presheaf.obj (op ((TopologicalSpace.Opens.map gL.base).obj V0))) := by
    rw [hmap]
    exact hsub_empty
  have hker : RingHom.ker (gL.c.app (op V0)).hom = ⊤ :=
    @RingHom.ker_eq_top_of_subsingleton _ _ _ _ _ _ _ hsub_mid _
  have hideal := Q.ideal V0
  have hspan :
      Ideal.span
        ({Xt.presheaf.map (homOfLE (show V0 ≤ ⊤ from le_top)).op Q.parameter} : Set _) = ⊤ := by
    rw [← hideal]
    exact hker
  have ht0_unit : IsUnit (Xt.presheaf.map (homOfLE (show V0 ≤ ⊤ from le_top)).op Q.parameter) :=
    Ideal.span_singleton_eq_top.mp hspan
  have hgerm_V0 :
      ∀ (y : Xt) (hy : y ∈ V0), IsUnit (Xt.presheaf.germ ⊤ y (by trivial) Q.parameter) := by
    intro y hy
    have hgerm_t0 :
        IsUnit
          (Xt.presheaf.germ V0 y hy
            (Xt.presheaf.map (homOfLE (show V0 ≤ ⊤ from le_top)).op Q.parameter)) :=
      IsUnit.map _ ht0_unit
    have hgerm_eq :
        Xt.presheaf.germ V0 y hy
            (Xt.presheaf.map (homOfLE (show V0 ≤ ⊤ from le_top)).op Q.parameter) =
        Xt.presheaf.germ ⊤ y (by trivial) Q.parameter :=
      Xt.presheaf.germ_res_apply (homOfLE (show V0 ≤ ⊤ from le_top)) y hy Q.parameter
    rw [hgerm_eq] at hgerm_t0
    exact hgerm_t0
  apply RingedSpace.isUnit_of_isUnit_germ _ _ _
  intro x hx
  have hyV0 : (fL.base x : Xt) ∈ V0 := Set.mem_range_self x
  have hgerm_t := hgerm_V0 (fL.base x) hyV0
  have hstalk := LocallyRingedSpace.stalkMap_germ_apply fL ⊤ x (by trivial) Q.parameter
  have hunit_stalk :
      IsUnit (fL.stalkMap x (Xt.presheaf.germ ⊤ (fL.base x) (by trivial) Q.parameter)) :=
    IsUnit.map _ hgerm_t
  rw [hstalk] at hunit_stalk
  exact hunit_stalk

end WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization
