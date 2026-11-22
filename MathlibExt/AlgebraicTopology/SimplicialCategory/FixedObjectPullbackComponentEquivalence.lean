/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectComponentUnitMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.ModelCategory.ProperCospanGluing
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# The SAME paired original equivalence is invertible in the full Hom-fibration pullback

Every full original Hom square is the actual scalar pullback square.
Precomposition by the unchanged paired coefficient acts weakly on both
original projections and the base, using the genuine original component
isomorphisms. The canonical weak pullback comparison makes its SAME full
precomposition map weak. Both original component inverse identities are
then constructed, without assuming the desired paired equivalence.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.PullbackComponentEquivalence
open ComponentCategory EnrichedHomPrecomposition
variable {O : Type u} {P A B D : FixedObjects O}
variable {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ D} {g : B ⟶ D}

/-- Both actual original projection equivalences give weakness of the SAME entire precomposition pullback map at every
original Hom. -/
theorem pre_weak (sq : IsPullback fst snd f g) (hp : FixedObjectModel.fibrations O f)
    (x y z : O) (q : 𝟙_ SSet.{u} ⟶ hom P x y)
    (hA : IsIso (arrowOf A.val (SSet.unitHomEquiv _ (q ≫ homMap fst x y))))
    (hB : IsIso (arrowOf B.val (SSet.unitHomEquiv _ (q ≫ homMap snd x y)))) :
    SSet.realizationWeakEquivalences (pre (vertex P z) q) := by
  let m : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let : CategoryWithWeakEquivalences SSet.{u} := m.categoryWithWeakEquivalences
  let : CategoryWithFibrations SSet.{u} := m.categoryWithFibrations
  let qA := q ≫ homMap fst x y
  let qB := q ≫ homMap snd x y
  let qD := qA ≫ homMap f x y
  let s := pre (vertex A z) qA
  let r := pre (vertex B z) qB
  let h := pre (vertex D z) qD
  have hc : homMap fst x y ≫ homMap f x y = homMap snd x y ≫ homMap g x y :=
    (homMap_comp fst f x y).symm.trans
      ((congrArg (fun F => homMap F x y) sq.w).trans (homMap_comp snd g x y))
  have hq : qD = qB ≫ homMap g x y :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => q ≫ k) hc).trans (Category.assoc _ _ _).symm)
  have hs : homMap f y z ≫ h = s ≫ homMap f x z :=
    (pre_homMap_natural f x y z qA).symm
  have hr : homMap g y z ≫ h = r ≫ homMap g x z :=
    (congrArg (fun k => homMap g y z ≫ pre (vertex D z) k) hq).trans
      (pre_homMap_natural g x y z qB).symm
  have ha : pre (vertex P z) q ≫ homMap fst x z = homMap fst y z ≫ s :=
    pre_homMap_natural fst x y z q
  have hb : pre (vertex P z) q ≫ homMap snd x z = homMap snd y z ≫ r :=
    pre_homMap_natural snd x y z q
  have ws : SSet.realizationWeakEquivalences s := pre_weak_of_isIso (vertex A z) qA hA
  have wr : SSet.realizationWeakEquivalences r := pre_weak_of_isIso (vertex B z) qB hB
  have hD : IsIso (arrowOf D.val (SSet.unitHomEquiv _ qD)) := homMap_unit_isIso f x y qA hA
  have wh : SSet.realizationWeakEquivalences h := pre_weak_of_isIso (vertex D z) qD hD
  let _ : Fibration ((evaluation y z).map f) := by
    change Fibration (homMap f y z)
    exact (FixedObjectModel.fibrations_iff f).mp hp y z
  let _ : Fibration ((evaluation x z).map f) := by
    change Fibration (homMap f x z)
    exact (FixedObjectModel.fibrations_iff f).mp hp x z
  let hsW : WeakEquivalence s := (weakEquivalence_iff s).mpr ws
  let hrW : WeakEquivalence r := (weakEquivalence_iff r).mpr wr
  let hhW : WeakEquivalence h := (weakEquivalence_iff h).mpr wh
  exact (weakEquivalence_iff _).mp
    (@IsRightProper.weakEquivalence_map_of_isPullbacks_of_fst SSet.{u} inferInstance m
      SSet.modelCategoryQuillen.instIsRightProper
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (sq.map (evaluation y z)) (sq.map (evaluation x z))
      (pre (vertex P z) q) s r h hs hr ha.symm hb.symm
      (inferInstance : Fibration ((evaluation y z).map f))
      (inferInstance : Fibration ((evaluation x z).map f)) hsW hrW hhW)


/-- The SAME actual paired original coefficient is component-invertible in the entire original pullback, with both
original inverse identities proved. -/
theorem unit_isIso (sq : IsPullback fst snd f g) (hp : FixedObjectModel.fibrations O f)
    (x y : O) (q : 𝟙_ SSet.{u} ⟶ hom P x y)
    (hA : IsIso (arrowOf A.val (SSet.unitHomEquiv _ (q ≫ homMap fst x y))))
    (hB : IsIso (arrowOf B.val (SSet.unitHomEquiv _ (q ≫ homMap snd x y)))) :
    IsIso (arrowOf P.val (SSet.unitHomEquiv _ q)) :=
  isIso_of_pre_weak q (pre_weak sq hp x y x q hA hB) (pre_weak sq hp x y y q hA hB)

end CategoryTheory.SimplicialEnrichment.FixedObjects.PullbackComponentEquivalence
