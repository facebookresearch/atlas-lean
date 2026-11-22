/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreUniversalMapping
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedAdjunction
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoReplacement

/-!
# The constructed original-local core adjunction

The existing Quillen-derived-adjunction constructor applies to the actual
constant/evaluation pair and the internally chosen original Smith model.
It takes no scalar Q/R convention or universal-property conclusion as input.
The original groupoidal/core Ho Hom functions retain the actual baseline unit
and the ordinary evaluation adjunct. Mapping-space presentation independence
is the natural weak comparison proved separately in CoreUniversalMapping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra Opposite
open SimplicialPresheaf.InjectiveKan
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf.CoreDerivedAdjunction

/-- The fixed scalar localization at the actual Kan–Quillen weak class. -/
abbrev scalarHo : SSet.{u} ⥤ SSet.realizationWeakEquivalences.{u}.Localization :=
  SSet.realizationWeakEquivalences.Q

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

/-- The exact weak class of the same internally chosen original Smith model. -/
abbrev localWeakClass (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  (originalLocalSmithData S).model.categoryWithWeakEquivalences.weakEquivalences

/-- The original-local localization, with its unchanged original object functions. -/
abbrev localHo (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    SimplicialPresheaf.{u} D ⥤ (localWeakClass S).Localization :=
  (localWeakClass S).Q

/-- Construct the total derived adjunction by the existing actual Quillen constructor. -/
def derivedAdjunctionData (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    QuillenDerivedAdjunctionData (ConstantEvaluation.adjunction hz) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let _ : (ConstantEvaluation.adjunction hz).IsQuillenAdjunction :=
    ConstantEvaluation.isQuillenAdjunction S hz
  exact quillenDerivedAdjunctionData (ConstantEvaluation.adjunction hz)

/-- The same constructed total-derived functors satisfy the actual adjunction. -/
def adjunction (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D} (hz : IsTerminal z) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    (derivedAdjunctionData S hz).leftDerived ⊣ (derivedAdjunctionData S hz).rightDerived := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  exact (derivedAdjunctionData S hz).adjunction

private theorem baselineUnit_localWeak (S : I → Arrow (SimplicialPresheaf.{u} D))
    (K : SSet.{u}) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    WeakEquivalence ((BaselineConstantCoreComparison.unit (D := D)).app K) := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  apply (weakEquivalence_iff _).mpr
  change d.model.categoryWithWeakEquivalences.weakEquivalences _
  rw [d.weakEquivalences_eq]
  exact BaselineConstantCoreComparison.unit_originalLocalWeak S K

/-- The actual original-local Ho functions from the groupoidal source to the zero core. -/
def homEquiv (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D} (hz : IsTerminal z)
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C) :
    ((localHo S).obj ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) ⟶
      (localHo S).obj C) ≃ (scalarHo.obj K ⟶ scalarHo.obj (C.obj (op z))) := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let _ : (ConstantEvaluation.adjunction hz).IsQuillenAdjunction :=
    ConstantEvaluation.isQuillenAdjunction S hz
  let _ : IsFibrant C := (d.isFibrant_iff C).mpr hC
  let η := (BaselineConstantCoreComparison.unit (D := D)).app K
  let _ : WeakEquivalence η := baselineUnit_localWeak S K
  exact (QuillenOrdinaryHoReplacement.replacementPrecompEquiv η C).trans
    (QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C)

/-- The forward Ho adjunct retains the baseline unit's zero component and the original map. -/
theorem homEquiv_map (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C)
    (f : (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K ⟶ C) :
    homEquiv S hz K C hC ((localHo S).map f) =
      scalarHo.map (((BaselineConstantCoreComparison.unit (D := D)).app K).app (op z) ≫
        f.app (op z)) := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let _ : (ConstantEvaluation.adjunction hz).IsQuillenAdjunction :=
    ConstantEvaluation.isQuillenAdjunction S hz
  let _ : IsFibrant C := (d.isFibrant_iff C).mpr hC
  let η := (BaselineConstantCoreComparison.unit (D := D)).app K
  let _ : WeakEquivalence η := baselineUnit_localWeak S K
  let H := (weakEquivalences (SimplicialPresheaf.{u} D)).Q
  let V := (weakEquivalences SSet.{u}).Q
  change QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C
    (H.map η ≫ H.map f) = V.map (η.app (op z) ≫ f.app (op z))
  exact (congrArg (QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C)
    (H.map_comp η f).symm).trans
      ((QuillenOrdinaryHoHom.homEquiv_map (ConstantEvaluation.adjunction hz) K C
        (η ≫ f)).trans
          (congrArg V.map (ConstantEvaluation.adjunction_homEquiv hz K C (η ≫ f))))

/-- The full Ho function is natural under actual strict maps of local-fibrant targets. -/
theorem homEquiv_target (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) {C C' : SimplicialPresheaf.{u} D}
    (hC : isOriginalLocalFibrant S C) (hC' : isOriginalLocalFibrant S C')
    (f : (localHo S).obj ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) ⟶
      (localHo S).obj C) (g : C ⟶ C') :
    homEquiv S hz K C' hC' (f ≫ (localHo S).map g) =
      homEquiv S hz K C hC f ≫ scalarHo.map (g.app (op z)) := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let _ : (ConstantEvaluation.adjunction hz).IsQuillenAdjunction :=
    ConstantEvaluation.isQuillenAdjunction S hz
  let _ : IsFibrant C := (d.isFibrant_iff C).mpr hC
  let _ : IsFibrant C' := (d.isFibrant_iff C').mpr hC'
  let η := (BaselineConstantCoreComparison.unit (D := D)).app K
  let _ : WeakEquivalence η := baselineUnit_localWeak S K
  let H := (weakEquivalences (SimplicialPresheaf.{u} D)).Q
  let V := (weakEquivalences SSet.{u}).Q
  let f' : H.obj ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) ⟶
      H.obj C := f
  change QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C'
      (H.map η ≫ (f' ≫ H.map g)) =
    QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C (H.map η ≫ f') ≫
      V.map ((ConstantEvaluation.evaluation z).map g)
  exact (congrArg (QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C')
    (Category.assoc (H.map η) f' (H.map g)).symm).trans
      (QuillenOrdinaryHoHom.homEquiv_naturality_right (ConstantEvaluation.adjunction hz)
        K (H.map η ≫ f') g)

/-- Coefficient naturality retains the original baseline and scalar functor actions. -/
theorem homEquiv_source (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) {K L : SSet.{u}} (k : K ⟶ L) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C)
    (f : (localHo S).obj ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj L) ⟶
      (localHo S).obj C) :
    homEquiv S hz K C hC
      ((localHo S).map ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k) ≫ f) =
      scalarHo.map k ≫ homEquiv S hz L C hC f := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let _ : (ConstantEvaluation.adjunction hz).IsQuillenAdjunction :=
    ConstantEvaluation.isQuillenAdjunction S hz
  let _ : IsFibrant C := (d.isFibrant_iff C).mpr hC
  let ηK := (BaselineConstantCoreComparison.unit (D := D)).app K
  let ηL := (BaselineConstantCoreComparison.unit (D := D)).app L
  let _ : WeakEquivalence ηK := baselineUnit_localWeak S K
  let _ : WeakEquivalence ηL := baselineUnit_localWeak S L
  let H := (weakEquivalences (SimplicialPresheaf.{u} D)).Q
  let V := (weakEquivalences SSet.{u}).Q
  let f' : H.obj ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj L) ⟶
      H.obj C := f
  change QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C
      (H.map ηK ≫
        (H.map ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k) ≫ f')) =
    V.map k ≫ QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) L C
      (H.map ηL ≫ f')
  have hn : H.map ηK ≫
      H.map ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k) =
      H.map (ConstantEvaluation.constant.map k) ≫ H.map ηL :=
    (H.map_comp ηK _).symm.trans
      ((H.congr_map ((BaselineConstantCoreComparison.unit (D := D)).naturality k).symm).trans
        (H.map_comp _ ηL))
  have hc : H.map ηK ≫
      (H.map ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k) ≫ f') =
      H.map (ConstantEvaluation.constant.map k) ≫ (H.map ηL ≫ f') :=
    (Category.assoc (H.map ηK) _ f').symm.trans
      ((congrArg (fun h => h ≫ f') hn).trans
        (Category.assoc (H.map (ConstantEvaluation.constant.map k)) (H.map ηL) f'))
  exact (congrArg (QuillenOrdinaryHoHom.homEquiv (ConstantEvaluation.adjunction hz) K C) hc).trans
    (QuillenOrdinaryHoHom.homEquiv_naturality_left (ConstantEvaluation.adjunction hz)
      C k (H.map ηL ≫ f'))

end SimplicialPresheaf.CoreDerivedAdjunction
