/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSkeletalPullback

/-!
# Consumers of the actual BK skeletal pullback

The clients retain the original outer reindexing, both literal pullback
coordinates, and both inverse coordinates through the public module boundary.
No regularity or transition-equivalence assumption is supplied.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u})
    (c : ComposableArrows J 1) (x : (D.obj c.left).obj (op ⦋0⦌)) :
    (SSet.bkHocolimToNerve D).app (op ⦋0⦌)
      (((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map
        (SimplexCategory.δ (0 : Fin 2)).op).app (op ⦋0⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D 1
          ⟨c, PUnit.unit⟩).app (op ⦋0⦌) x)) =
      (nerve J).map (SimplexCategory.δ (0 : Fin 2)).op c :=
  SSet.bkHocolimToNerve_outerMap_wbarIncl D (SimplexCategory.δ (0 : Fin 2)) ⟨c, PUnit.unit⟩ x

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u}) (n : ℕ) :
    IsPullback (SSet.bkSkeletalFiltration D n).ι (SSet.bkSkeletalProjection D n)
        (SSet.bkHocolimToNerve D) ((nerve J).skeleton (n + 1)).ι ∧
      (SSet.bkSkeletalRestrictionIso D n).hom ≫
        pullback.fst (SSet.toTop.map (SSet.bkHocolimToNerve D))
          (SSet.toTop.map ((nerve J).skeleton (n + 1)).ι) =
        SSet.toTop.map (SSet.bkSkeletalFiltration D n).ι ∧
      (SSet.bkSkeletalRestrictionIso D n).hom ≫
        pullback.snd (SSet.toTop.map (SSet.bkHocolimToNerve D))
          (SSet.toTop.map ((nerve J).skeleton (n + 1)).ι) =
        SSet.toTop.map (SSet.bkSkeletalProjection D n) :=
  ⟨SSet.bkSkeletalProjection_isPullback D n, SSet.bkSkeletalRestrictionIso_hom_fst D n,
    SSet.bkSkeletalRestrictionIso_hom_snd D n⟩

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u}) (n : ℕ) :
    (SSet.bkSkeletalRestrictionIso D n).inv ≫ SSet.toTop.map (SSet.bkSkeletalFiltration D n).ι =
      pullback.fst (SSet.toTop.map (SSet.bkHocolimToNerve D))
        (SSet.toTop.map ((nerve J).skeleton (n + 1)).ι) ∧
      (SSet.bkSkeletalRestrictionIso D n).inv ≫ SSet.toTop.map (SSet.bkSkeletalProjection D n) =
      pullback.snd (SSet.toTop.map (SSet.bkHocolimToNerve D))
        (SSet.toTop.map ((nerve J).skeleton (n + 1)).ι) :=
  ⟨SSet.bkSkeletalRestrictionIso_inv_fst D n, SSet.bkSkeletalRestrictionIso_inv_snd D n⟩

#print axioms SSet.bkSkeletalFiltration_eq_preimage
#print axioms SSet.bkHocolimToNerve_outerMap_wbarIncl
#print axioms SSet.bkSkeletalProjection_realized_isPullback
#print axioms SSet.bkSkeletalRestrictionIso
