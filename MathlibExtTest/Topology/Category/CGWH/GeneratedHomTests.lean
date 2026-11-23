/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.GeneratedHom

/-!
# Tests for generated mapping carriers in CGWH

The tests pin independent universes, both inverse laws, pointwise behavior,
and the absence of stronger separation hypotheses on the source.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Topology

namespace MathlibExtTest.Topology.Category.CGWH.GeneratedHomTests

variable (A B : CGWH.{u, v})

example : ContinuousMapGeneratedBy
      CompactlyGenerated.compactHausProbes.{u} A B ≃ C(A, B) :=
  CGWH.generatedMapEquivContinuousMap A B

example (f : ContinuousMapGeneratedBy
    CompactlyGenerated.compactHausProbes.{u} A B) (a : A) :
    CGWH.generatedMapEquivContinuousMap A B f a = f a :=
  CGWH.generatedMapEquivContinuousMap_apply A B f a

example (f : ContinuousMapGeneratedBy
    CompactlyGenerated.compactHausProbes.{u} A B) :
    (CGWH.generatedMapEquivContinuousMap A B).symm
        (CGWH.generatedMapEquivContinuousMap A B f) = f :=
  (CGWH.generatedMapEquivContinuousMap A B).symm_apply_apply f

example (f : C(A, B)) :
    CGWH.generatedMapEquivContinuousMap A B
        ((CGWH.generatedMapEquivContinuousMap A B).symm f) = f :=
  (CGWH.generatedMapEquivContinuousMap A B).apply_symm_apply f

example (f g : ContinuousMapGeneratedBy
    CompactlyGenerated.compactHausProbes.{u} A B)
    (h : ∀ a, f a = g a) : f = g := by
  ext a
  exact h a

section UniverseMatrix

#check CGWH.generatedMapEquivContinuousMap.{0, 0}
#check CGWH.generatedMapEquivContinuousMap_apply.{0, 0}
#check CGWH.generatedMapEquivContinuousMap.{1, 1}
#check CGWH.generatedMapEquivContinuousMap_apply.{1, 1}
#check CGWH.generatedMapEquivContinuousMap.{0, 1}
#check CGWH.generatedMapEquivContinuousMap_apply.{0, 1}
#check CGWH.generatedMapEquivContinuousMap.{1, 0}
#check CGWH.generatedMapEquivContinuousMap_apply.{1, 0}
#check CGWH.generatedMapEquivContinuousMap.{u, v}
#check CGWH.generatedMapEquivContinuousMap_apply.{u, v}

end UniverseMatrix

section NegativeBoundaries

example : True := by
  fail_if_success let _ : T2Space A := inferInstance
  fail_if_success let _ : LocallyCompactSpace A := inferInstance
  trivial

end NegativeBoundaries

#print axioms CGWH.generatedMapEquivContinuousMap
#print axioms CGWH.generatedMapEquivContinuousMap_apply

end MathlibExtTest.Topology.Category.CGWH.GeneratedHomTests
