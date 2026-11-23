/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianClosed

/-! # Pointwise computation for the original internal-Hom adjunction -/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
public section

namespace CGWH

/-- Native uncurrying evaluates the original generated mapping object at
the original first Cartesian coordinate. No ordinary product inverse is
used in this pointwise characteristic. -/
theorem internalHom_uncurry_apply
    {A K B : CGWH.{u, v}} (f : K ⟶ internalHom A B)
    (z : (A ⊗ K : CGWH.{u, v})) :
    MonoidalClosed.uncurry f z =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B)
        (f (CartesianMonoidalCategory.snd A K z)) :
          ContinuousMapGeneratedBy
            CompactlyGenerated.compactHausProbes.{u} A B)
        (CartesianMonoidalCategory.fst A K z) := by
  have h₁ : CartesianMonoidalCategory.fst A (internalHom A B) ((A ◁ f) z) =
      CartesianMonoidalCategory.fst A K z :=
    ConcreteCategory.congr_hom (CartesianMonoidalCategory.whiskerLeft_fst A f) z
  have h₂ : CartesianMonoidalCategory.snd A (internalHom A B) ((A ◁ f) z) =
      f (CartesianMonoidalCategory.snd A K z) :=
    ConcreteCategory.congr_hom (CartesianMonoidalCategory.whiskerLeft_snd A f) z
  have h := internalHom_ev_apply A B ((A ◁ f) z)
  rw [h₁, h₂] at h
  exact (ConcreteCategory.congr_hom (MonoidalClosed.uncurry_eq f) z).trans h

end CGWH
