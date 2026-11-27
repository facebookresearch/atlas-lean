/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
import MathlibExt.Topology.Maps.CollapsedAxes
set_option autoImplicit false
namespace MathlibExtTest.Topology.CollapsedAxes
open _root_.Topology
variable {B Q : Type*} [TopologicalSpace B] [TopologicalSpace Q]
example (q : B → Q) (A S : Set B)
    (hkernel : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hA : IsClosed A) (hS : IsClosed S) :
    IsClosed (q ⁻¹' (q '' S)) :=
  isClosed_saturation_of_single_collapsed_class q A S hkernel hA hS
example (q : B → Q) (hq : IsQuotientMap q) (A S : Set B)
    (hkernel : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hA : IsClosed A) (hS : IsClosed S) : IsClosed (q '' S) :=
  isClosedMap_of_quotient_single_collapsed_class q hq A hkernel hA S hS

example {A B QA QB : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace QA] [TopologicalSpace QB]
    (f : A → B) (qA : A → QA) (qB : B → QB) (g : QA → QB)
    (hA : IsQuotientMap qA) (hB : IsQuotientMap qB)
    (CA : Set A) (CB : Set B)
    (hKernelA : ∀ a b, qA a = qA b ↔ a = b ∨ (a ∈ CA ∧ b ∈ CA))
    (hKernelB : ∀ a b, qB a = qB b ↔ a = b ∨ (a ∈ CB ∧ b ∈ CB))
    (hClosedB : IsClosed CB) (hReflect : f ⁻¹' CB = CA)
    (hSquare : ∀ a, g (qA a) = qB (f a))
    (hf : IsClosedEmbedding f) (hg : Continuous g) : IsClosedEmbedding g :=
  isClosedEmbedding_of_single_class_quotients f qA qB g hA hB CA CB
    hKernelA hKernelB hClosedB hReflect hSquare hf hg

#print axioms isClosed_saturation_of_single_collapsed_class
#print axioms isClosedMap_of_quotient_single_collapsed_class
#print axioms isClosedEmbedding_of_single_class_quotients

end MathlibExtTest.Topology.CollapsedAxes
