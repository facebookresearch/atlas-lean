/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreBifunctor
import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseCore
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Full functor cores from original Kan sources

The entire evaluation map from a Kan source times its full functor core has
Kan domain, so it factors through the literal target core. Its actual curry
is inverse to the canonical core restriction of internal postcomposition.
Both inclusions and every original source and target map are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FunctorCore.KanSource

/-- Every entire image of an original Kan source lies in the target's literal core. -/
theorem range_le_core {X Y : SSet.{u}} [KanComplex X] (f : X ⟶ Y) :
    Subcomplex.range f ≤ core Y := by
  rw [← Subcomplex.image_top]
  apply (Subcomplex.image_le_iff (⊤ : X.Subcomplex) f (core Y)).mpr
  simpa only [core_eq_top_of_kanComplex] using core_le_preimage f

private def intoCore {X Y : SSet.{u}} [KanComplex X] (f : X ⟶ Y) :
    X ⟶ (core Y : SSet.{u}) :=
  Subcomplex.lift f (range_le_core f)

private theorem intoCore_ι {X Y : SSet.{u}} [KanComplex X] (f : X ⟶ Y) :
    intoCore f ≫ (core Y).ι = f := Subcomplex.lift_ι _ _

private def forward (K Q : SSet.{u}) [KanComplex K] [Quasicategory Q] :
    (core ((ihom K).obj Q) : SSet.{u}) ⟶ (ihom K).obj (core Q : SSet.{u}) := by
  letI : KanComplex (core ((ihom K).obj Q) : SSet.{u}) := FunctorCore.isKan K Q
  letI : IsFibrant (K ⨯ (core ((ihom K).obj Q) : SSet.{u})) :=
    isFibrant_of_fibration
      (prod.snd : K ⨯ (core ((ihom K).obj Q) : SSet.{u}) ⟶ (core ((ihom K).obj Q) : SSet.{u}))
  let e : K ⊗ (core ((ihom K).obj Q) : SSet.{u}) ≅ K ⨯ (core ((ihom K).obj Q) : SSet.{u}) :=
    (CartesianMonoidalCategory.tensorLeftIsoProd K).app (core ((ihom K).obj Q) : SSet.{u})
  letI : KanComplex (K ⊗ (core ((ihom K).obj Q) : SSet.{u})) := isFibrant_of_fibration e.hom
  let ev : K ⊗ (core ((ihom K).obj Q) : SSet.{u}) ⟶ Q := FunctorCore.evaluation K Q
  exact curry (intoCore ev)

private def backward (K Q : SSet.{u}) [Quasicategory Q] :
    (ihom K).obj (core Q : SSet.{u}) ⟶ (core ((ihom K).obj Q) : SSet.{u}) := by
  letI : KanComplex ((ihom K).obj (core Q : SSet.{u})) := by infer_instance
  exact intoCore ((ihom K).map (core Q).ι)

private theorem forward_ι (K Q : SSet.{u}) [KanComplex K] [Quasicategory Q] :
    forward K Q ≫ (ihom K).map (core Q).ι = (core ((ihom K).obj Q)).ι := by
  apply uncurry_injective
  dsimp only [forward]
  rw [uncurry_natural_right, uncurry_curry]
  simp only [intoCore, Subcomplex.lift_ι, uncurry_eq, FunctorCore.evaluation]

private theorem backward_ι (K Q : SSet.{u}) [Quasicategory Q] :
    backward K Q ≫ (core ((ihom K).obj Q)).ι = (ihom K).map (core Q).ι :=
  intoCore_ι _

/-- The full functor core from a Kan source is the whole internal Hom into the native target core. -/
def iso (K Q : SSet.{u}) [KanComplex K] [Quasicategory Q] :
    (core ((ihom K).obj Q) : SSet.{u}) ≅ (ihom K).obj (core Q : SSet.{u}) where
  hom := forward K Q
  inv := backward K Q
  hom_inv_id := by
    apply (cancel_mono (core ((ihom K).obj Q)).ι).mp
    rw [Category.assoc, backward_ι, forward_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono ((ihom K).map (core Q).ι)).mp
    rw [Category.assoc, forward_ι, backward_ι, Category.id_comp]

/-- The forward comparison retains the SAME full original function-core inclusion. -/
@[reassoc]
theorem iso_hom_ι (K Q : SSet.{u}) [KanComplex K] [Quasicategory Q] :
    (iso K Q).hom ≫ (ihom K).map (core Q).ι = (core ((ihom K).obj Q)).ι :=
  forward_ι K Q

/-- The inverse comparison retains the SAME full original internal postcomposition. -/
@[reassoc]
theorem iso_inv_ι (K Q : SSet.{u}) [KanComplex K] [Quasicategory Q] :
    (iso K Q).inv ≫ (core ((ihom K).obj Q)).ι = (ihom K).map (core Q).ι :=
  backward_ι K Q

/-- Every actual target map retains the entire function-core and native-core actions. -/
theorem natural_target (K : SSet.{u}) [KanComplex K] {Q Q' : SSet.{u}}
    [Quasicategory Q] [Quasicategory Q'] (f : Q ⟶ Q') :
    (FunctorCore.functor K).map f ≫ (iso K Q').hom =
      (iso K Q).hom ≫ (ihom K).map (core.map f) := by
  apply (cancel_mono ((ihom K).map (core Q').ι)).mp
  rw [Category.assoc, iso_hom_ι, FunctorCore.map_inclusion]
  rw [Category.assoc, ← Functor.map_comp, core.map_ι, Functor.map_comp, ← Category.assoc, iso_hom_ι]

/-- Every actual Kan-source map retains the original contravariant precomposition. -/
theorem natural_source {K L : SSet.{u}} [KanComplex K] [KanComplex L]
    (a : K ⟶ L) (Q : SSet.{u}) [Quasicategory Q] :
    (FunctorCore.sourceMap a).app Q ≫ (iso K Q).hom =
      (iso L Q).hom ≫ (pre a).app (core Q : SSet.{u}) := by
  apply (cancel_mono ((ihom K).map (core Q).ι)).mp
  rw [Category.assoc, iso_hom_ι, FunctorCore.sourceMap_inclusion]
  rw [Category.assoc, ← (pre a).naturality (core Q).ι, ← Category.assoc, iso_hom_ι]

end SSet.FunctorCore.KanSource
