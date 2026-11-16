/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.UniversalRootWeightLines

/-!
# The native line comparison of actual reindexed root families

All three stages are the original DF inverse image, root comparison
and identity-etale restriction. The final arrow is the actual root
family isomorphism. These whole module maps fix every coefficient,
including roots whose sections vanish.

Source: Borne–Vistoli arXiv:1001.0466v2, Sections4.3/6.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RootNativeFamilyComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.Opposite _root_.AlgebraicGeometry
open DeligneFaltingsSheaves DenominatorRootStacks EtaleMonoidInverseImage UniversalRootWeightLines
open RootWeightEvaluations

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) {T U : Over X} (q : T ⟶ U)
  (r : RootReindexing I D j q) (E : rootsAt I D j U) (F : rootsAt I D j T)
  (k : F ⟶ r.functor.obj E)
  (g : (pulledMonoids U B).obj.obj (op (identityEtale U.left)))
  (h : (pulledMonoids T B).obj.obj (op (identityEtale T.left)))

def inverseGenerator := generator q.left (pulledMonoids U B) (identityEtale U.left) g

def imageGenerator := (monoidOverComparison B q).hom.hom.app
  (op ((etaleBaseChange q.left).obj (identityEtale U.left))) (inverseGenerator (B := B) q g)

def GeneratorNormalization : Prop :=
  (pulledMonoids T B).obj.map (unitDiagonal q.left).op (imageGenerator (B := B) q g) = h

/-- This is an actual module isomorphism, not a condition only on the section. -/
def comparison (N : GeneratorNormalization (B := B) q g h) :
    (Scheme.Modules.pullback q.left).obj ((E.of.extended.chart (identityEtale U.left)).module g) ≅
      (F.of.extended.chart (identityEtale T.left)).module h :=
  diagonalPullbackIso q.left ((E.of.extended.chart (identityEtale U.left)).module g) ≪≫
    (Scheme.Modules.pullback (unitDiagonal q.left).left).mapIso
      (((I T.left U.left q.left (pulledMonoids U B)).object E.of.extended).comparison (identityEtale U.left) g) ≪≫
    (Scheme.Modules.pullback (unitDiagonal q.left).left).mapIso
      (nativeRootLineIso I D j q r E ((etaleBaseChange q.left).obj (identityEtale U.left))
        (inverseGenerator (B := B) q g)) ≪≫
    nativeReindexLineIso (r.functor.obj E).of.extended (unitDiagonal q.left)
      (imageGenerator (B := B) q g) h N ≪≫
    (k.iso.hom.hom.comparison (identityEtale T.left) h).symm

end MathlibExt.AlgebraicGeometry.RootNativeFamilyComparisons
