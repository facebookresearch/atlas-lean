/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import Mathlib.Topology.Maps.Basic

/-!
# Closed maps and embeddings after collapsing one closed class

The full kernel relation determines each saturation. Quotient topology then
makes the projection closed, and a reflected collapsed class allows an original
closed embedding to descend to a closed embedding. These results apply to the
actual wedge collapsed by a smash quotient.
-/

@[expose] public section
set_option autoImplicit false
namespace Topology
variable {B Q : Type*} [TopologicalSpace B] [TopologicalSpace Q]
omit [TopologicalSpace Q] in
/-- A complete quotient kernel collapsing one closed set has closed saturations of closed sets. -/
theorem isClosed_saturation_of_single_collapsed_class
    (q : B → Q) (A S : Set B)
    (hkernel : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hA : IsClosed A) (hS : IsClosed S) :
    IsClosed (q ⁻¹' (q '' S)) := by
  classical
  by_cases hmeet : ∃ z, z ∈ S ∧ z ∈ A
  · have heq : q ⁻¹' (q '' S) = S ∪ A := by
      ext x
      constructor
      · rintro ⟨z, hz, hzx⟩
        rcases (hkernel z x).mp hzx with h | ⟨hzA, hxA⟩
        · exact Or.inl (h ▸ hz)
        · exact Or.inr hxA
      · rintro (hxS | hxA)
        · exact ⟨x, hxS, rfl⟩
        · obtain ⟨z, hzS, hzA⟩ := hmeet
          exact ⟨z, hzS, (hkernel z x).mpr (Or.inr ⟨hzA, hxA⟩)⟩
    rw [heq]
    exact hS.union hA
  · have heq : q ⁻¹' (q '' S) = S := by
      ext x
      constructor
      · rintro ⟨z, hz, hzx⟩
        rcases (hkernel z x).mp hzx with h | ⟨hzA, hxA⟩
        · exact h ▸ hz
        · exact (hmeet ⟨z, hz, hzA⟩).elim
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact hS
/-- The actual quotient with that complete kernel maps every closed set to a closed set. -/
theorem isClosedMap_of_quotient_single_collapsed_class
    (q : B → Q) (hq : IsQuotientMap q) (A : Set B)
    (hkernel : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hA : IsClosed A) : IsClosedMap q := by
  intro S hS
  exact hq.isCoinducing.isClosed_preimage.mp
    (isClosed_saturation_of_single_collapsed_class q A S hkernel hA hS)


variable {A B QA QB : Type*}
  [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace QA] [TopologicalSpace QB]

/-- A continuous map descended from an actual closed embedding remains a
closed embedding when both complete quotient kernels collapse one class,
the target class is closed and the original embedding reflects that class. -/
theorem isClosedEmbedding_of_single_class_quotients
    (f : A → B) (qA : A → QA) (qB : B → QB) (g : QA → QB)
    (hA : IsQuotientMap qA) (hB : IsQuotientMap qB)
    (CA : Set A) (CB : Set B)
    (hKernelA : ∀ a b, qA a = qA b ↔ a = b ∨ (a ∈ CA ∧ b ∈ CA))
    (hKernelB : ∀ a b, qB a = qB b ↔ a = b ∨ (a ∈ CB ∧ b ∈ CB))
    (hClosedB : IsClosed CB) (hReflect : f ⁻¹' CB = CA)
    (hSquare : ∀ a, g (qA a) = qB (f a))
    (hf : IsClosedEmbedding f) (hg : Continuous g) :
    IsClosedEmbedding g := by
  have hInjective : Function.Injective g := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := hA.surjective x
    obtain ⟨b, rfl⟩ := hA.surjective y
    have hq : qB (f a) = qB (f b) :=
      (hSquare a).symm.trans (hxy.trans (hSquare b))
    rcases (hKernelB (f a) (f b)).mp hq with heq | ⟨ha, hb⟩
    · exact congrArg qA (hf.injective heq)
    · have ha' : a ∈ CA := by
        rw [← hReflect]
        exact ha
      have hb' : b ∈ CA := by
        rw [← hReflect]
        exact hb
      exact (hKernelA a b).mpr (Or.inr ⟨ha', hb'⟩)
  have hClosedQ : IsClosedMap qB :=
    isClosedMap_of_quotient_single_collapsed_class qB hB CB hKernelB hClosedB
  have hClosedG : IsClosedMap g := by
    intro T hT
    have hPre : IsClosed (qA ⁻¹' T) := hT.preimage hA.continuous
    have hImage : IsClosed (qB '' (f '' (qA ⁻¹' T))) :=
      hClosedQ _ (hf.isClosedMap _ hPre)
    have hFullImage : g '' T = qB '' (f '' (qA ⁻¹' T)) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨a, ha⟩ := hA.surjective x
        refine ⟨f a, ⟨a, ?_, rfl⟩, ?_⟩
        · change qA a ∈ T
          rw [ha]
          exact hx
        · exact (hSquare a).symm.trans (congrArg g ha)
      · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨qA a, ha, hSquare a⟩
    rw [hFullImage]
    exact hImage
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap hg hInjective hClosedG


end Topology
