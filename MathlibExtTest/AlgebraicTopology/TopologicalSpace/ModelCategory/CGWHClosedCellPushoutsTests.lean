/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellPushouts

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology

universe u v

namespace CGWHClosedCellPushoutsTests

section Generic

variable {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
variable (hi : IsClosedEmbedding
  (ConcreteCategory.hom (CGWH.cgwhToTop.map i)))

example : PreservesColimit (span i f)
    CGWH.cgwhToCompactlyGenerated :=
  CGWH.preservesPushout_of_isClosedEmbedding i f hi

example : IsClosedEmbedding
    (ConcreteCategory.hom
      (CGWH.cgwhToCompactlyGenerated.map (pushout.inr i f))) :=
  CGWH.isClosedEmbedding_pushout_inr i f hi

example : PreservesColimit (span f i)
    CGWH.cgwhToCompactlyGenerated := by
  let _ : PreservesColimit (span i f)
      CGWH.cgwhToCompactlyGenerated :=
    CGWH.preservesPushout_of_isClosedEmbedding i f hi
  exact preservesPushout_symmetry CGWH.cgwhToCompactlyGenerated i f

end Generic

section ArbitrarySquare

variable {A B X Y : CGWH.{u, v}}
variable (g₁ : A ⟶ X) (m : A ⟶ B) (s : X ⟶ Y) (g₂ : B ⟶ Y)
variable (sq : IsPushout g₁ m s g₂)
variable (hm : IsClosedEmbedding
  (ConcreteCategory.hom (CGWH.cgwhToTop.map m)))

example : IsPushout
    (CGWH.cgwhToCompactlyGenerated.map g₁)
    (CGWH.cgwhToCompactlyGenerated.map m)
    (CGWH.cgwhToCompactlyGenerated.map s)
    (CGWH.cgwhToCompactlyGenerated.map g₂) := by
  let _ : PreservesColimit (span m g₁)
      CGWH.cgwhToCompactlyGenerated :=
    CGWH.preservesPushout_of_isClosedEmbedding m g₁ hm
  let _ : PreservesColimit (span g₁ m)
      CGWH.cgwhToCompactlyGenerated :=
    preservesPushout_symmetry CGWH.cgwhToCompactlyGenerated m g₁
  exact sq.map CGWH.cgwhToCompactlyGenerated

end ArbitrarySquare

section NoGlobalPreservation

#guard_msgs (error, substring := true) in
#synth PreservesColimitsOfSize.{v, v}
  CGWH.cgwhToCompactlyGenerated.{u, v}

#guard_msgs (error, substring := true) in
#synth PreservesColimitsOfShape WalkingSpan
  CGWH.cgwhToCompactlyGenerated.{u, v}

#guard_msgs (error, substring := true) in
#check CGWH.modelCategory

#guard_msgs (error, substring := true) in
#check CGWH.cofibrantGenerationData

end NoGlobalPreservation

section UniverseMatrix

#check CGWH.preservesPushout_of_isClosedEmbedding.{0, 0}
#check CGWH.isClosedEmbedding_pushout_inr.{0, 0}

#check CGWH.preservesPushout_of_isClosedEmbedding.{1, 1}
#check CGWH.isClosedEmbedding_pushout_inr.{1, 1}

#check CGWH.preservesPushout_of_isClosedEmbedding.{0, 1}
#check CGWH.isClosedEmbedding_pushout_inr.{0, 1}

#check CGWH.preservesPushout_of_isClosedEmbedding.{1, 0}
#check CGWH.isClosedEmbedding_pushout_inr.{1, 0}

end UniverseMatrix

#check CGWH.preservesPushout_of_isClosedEmbedding
#check CGWH.isClosedEmbedding_pushout_inr

#print axioms CGWH.preservesPushout_of_isClosedEmbedding
#print axioms CGWH.isClosedEmbedding_pushout_inr

end CGWHClosedCellPushoutsTests
