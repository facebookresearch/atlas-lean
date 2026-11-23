/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.K0.ComponentProduct

noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra
open CategoryTheory.SInverseS CategoryTheory.SInverseS.ComponentTranslation
open AlgebraicKTheory

universe u v w

namespace ProjectiveComponentProductTests

#check grothendieckDiscreteSpace_discrete
#print axioms grothendieckDiscreteSpace_discrete
#check nativeProductHomotopyEquiv
#print axioms nativeProductHomotopyEquiv
#check nativeProductLeftHomotopyRel
#print axioms nativeProductLeftHomotopyRel
#check nativeProductRightHomotopyRel
#print axioms nativeProductRightHomotopyRel
#check nativeProductForward_class
#print axioms nativeProductForward_class
#check nativeProductInverse_class
#print axioms nativeProductInverse_class
#check nativeZeroPathComponentHomeomorph
#print axioms nativeZeroPathComponentHomeomorph
#check nativeZeroInclusion_realization
#print axioms nativeZeroInclusion_realization
#check RingK0.projectiveProductHomotopyEquiv
#print axioms RingK0.projectiveProductHomotopyEquiv
#check RingK0.projectiveProductLeftHomotopyRel
#print axioms RingK0.projectiveProductLeftHomotopyRel
#check RingK0.projectiveProductRightHomotopyRel
#print axioms RingK0.projectiveProductRightHomotopyRel
#check RingK0.projectiveProductForward_class
#print axioms RingK0.projectiveProductForward_class
#check RingK0.projectiveProductInverse_class
#print axioms RingK0.projectiveProductInverse_class
#check RingK0.projectiveProductForward_every_class
#print axioms RingK0.projectiveProductForward_every_class
#check RingK0.projectiveProductForward_pair_class
#print axioms RingK0.projectiveProductForward_pair_class
#check RingK0.projectivePathProductHomotopyEquiv
#print axioms RingK0.projectivePathProductHomotopyEquiv
#check RingK0.projectivePathProductLeftHomotopyRel
#print axioms RingK0.projectivePathProductLeftHomotopyRel
#check RingK0.projectivePathProductRightHomotopyRel
#print axioms RingK0.projectivePathProductRightHomotopyRel
#check RingK0.projectivePathProductForward_every_class
#print axioms RingK0.projectivePathProductForward_every_class

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example : (nativeProductForward.{u, v, w} (C := C)) (nativeOriginalPoint.{u, v, w} (C := C)) = (nativeProductPoint.{u, v, w} (C := C)) :=
  (nativeProductForward_point.{u, v, w} (C := C))

example : (nativeProductInverse.{u, v, w} (C := C)) (nativeProductPoint.{u, v, w} (C := C)) = (nativeOriginalPoint.{u, v, w} (C := C)) :=
  (nativeProductInverse_point.{u, v, w} (C := C))

example (t : unitInterval) : (nativeProductLeftHomotopyRel.{u, v, w} (C := C)) (t, nativeOriginalPoint.{u, v, w} (C := C)) =
    (nativeOriginalPoint.{u, v, w} (C := C)) := (nativeProductLeftHomotopyRel.{u, v, w} (C := C)).eq_snd t (by simp)

example (t : unitInterval) : (nativeProductRightHomotopyRel.{u, v, w} (C := C)) (t, nativeProductPoint.{u, v, w} (C := C)) =
    (nativeProductPoint.{u, v, w} (C := C)) := by
  let := (nativeProductSpace.{u, v, w} (C := C)).str
  exact (nativeProductRightHomotopyRel.{u, v, w} (C := C)).eq_snd t (by simp)

example (g : GrothendieckAddGroup (Skeleton C)) (z : nativeZeroSpace.{u, v, w} (C := C)) :
    (nativeProductInverse.{u, v, w} (C := C)) (g, z) = (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι)
        (componentInverse g ((nativeZeroRealizationIso.{u, v, w} (C := C)).hom z))) := (nativeProductInverse_class.{u, v, w} (C := C)) g z

example (z : nativeZeroSpace.{u, v, w} (C := C)) :
    ((nativeZeroPathComponentHomeomorph.{u, v, w} (C := C)) z : nativeOriginalSpace.{u, v, w} (C := C)) = (nativeZeroInclusion.{u, v, w} (C := C)) z :=
  (nativeZeroPathComponentHomeomorph_apply.{u, v, w} (C := C)) z

end Generic

section Projective

variable (R : Type u) [Ring R]

example (a : RingK0 R)
    (z : componentSpace ((RingK0.projectiveGrothendieckEquiv.{u, v} R).symm a)) :
    (RingK0.projectiveProductForward.{u, v, w} R ((nativeOriginalRealizationIso.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap
        (componentProperty ((RingK0.projectiveGrothendieckEquiv.{u, v} R).symm a)).ι) z))).1 = a :=
  RingK0.projectiveProductForward_every_class.{u, v, w} R a z

example (a : RingK0 R) (z : RingK0.projectiveZeroSpace.{u, v, w} R) :
    RingK0.projectiveProductInverse.{u, v, w} R (a, z) = (nativeOriginalRealizationIso.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap
        (componentProperty ((RingK0.projectiveGrothendieckEquiv.{u, v} R).symm a)).ι)
          (componentInverse ((RingK0.projectiveGrothendieckEquiv.{u, v} R).symm a)
            ((nativeZeroRealizationIso.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).hom z))) := RingK0.projectiveProductInverse_class.{u, v, w} R a z

example (X : Pair (FGProjectiveCat.{max u v} R)) (z : componentSpace X.difference) :
    RingK0.projectiveProductForward.{u, v, w} R ((nativeOriginalRealizationIso.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty X.difference).ι) z)) =
        (RingK0.projectiveGrothendieckEquiv.{u, v} R X.difference,
          (nativeZeroRealizationIso.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).inv (componentForward X.difference z)) :=
  RingK0.projectiveProductForward_class.{u, v, w} R X.difference z

example : RingK0.projectiveProductForward.{u, v, w} R (RingK0.projectiveOriginalPoint.{u, v, w} R) =
    RingK0.projectiveProductPoint.{u, v, w} R := RingK0.projectiveProductForward_point.{u, v, w} R

example : RingK0.projectiveProductInverse.{u, v, w} R (RingK0.projectiveProductPoint.{u, v, w} R) =
    RingK0.projectiveOriginalPoint.{u, v, w} R := RingK0.projectiveProductInverse_point.{u, v, w} R

example (t : unitInterval) :
    RingK0.projectiveProductLeftHomotopyRel.{u, v, w} R (t, RingK0.projectiveOriginalPoint.{u, v, w} R) =
      RingK0.projectiveOriginalPoint.{u, v, w} R :=
  (RingK0.projectiveProductLeftHomotopyRel.{u, v, w} R).eq_snd t (by simp)

example (t : unitInterval) :
    RingK0.projectiveProductRightHomotopyRel.{u, v, w} R (t, RingK0.projectiveProductPoint.{u, v, w} R) =
      RingK0.projectiveProductPoint.{u, v, w} R := by
  let := (RingK0.projectiveProductSpace.{u, v, w} R).str
  exact (RingK0.projectiveProductRightHomotopyRel.{u, v, w} R).eq_snd t (by simp)

example (a : RingK0 R)
    (z : componentSpace ((RingK0.projectiveGrothendieckEquiv.{u, v} R).symm a)) :
    (RingK0.projectivePathProductForward.{u, v, w} R ((nativeOriginalRealizationIso.{max u v + 1, max u v, w} (C := FGProjectiveCat.{max u v} R)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap
        (componentProperty ((RingK0.projectiveGrothendieckEquiv.{u, v} R).symm a)).ι) z))).1 = a :=
  RingK0.projectivePathProductForward_every_class.{u, v, w} R a z

example (t : unitInterval) :
    RingK0.projectivePathProductLeftHomotopyRel.{u, v, w} R (t, RingK0.projectiveOriginalPoint.{u, v, w} R) =
      RingK0.projectiveOriginalPoint.{u, v, w} R :=
  (RingK0.projectivePathProductLeftHomotopyRel.{u, v, w} R).eq_snd t (by simp)

example (t : unitInterval) :
    RingK0.projectivePathProductRightHomotopyRel.{u, v, w} R (t, RingK0.projectivePathProductPoint.{u, v, w} R) =
      RingK0.projectivePathProductPoint.{u, v, w} R := by
  let := (RingK0.projectivePathProductSpace.{u, v, w} R).str
  exact (RingK0.projectivePathProductRightHomotopyRel.{u, v, w} R).eq_snd t (by simp)

end Projective

end ProjectiveComponentProductTests
