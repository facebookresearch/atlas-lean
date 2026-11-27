/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero

/-! Public use of the native degree-zero class under only Category,
HasZeroMorphisms and individual homology assumptions. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace MathlibExtTest.ChainComplexHomologyZero

section WeakCategory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (K : ChainComplex C ℕ) [K.HasHomology 0]

example : ChainComplex.homologyZeroClass K =
    K.pOpcycles 0 ≫ K.isoHomologyι₀.inv := rfl

example : K.d 1 0 ≫ ChainComplex.homologyZeroClass K = 0 :=
  ChainComplex.d_comp_homologyZeroClass K

example : IsColimit (ChainComplex.homologyZeroCofork K) :=
  ChainComplex.homologyZeroCoforkIsColimit K

/-- A native universal map exists without a chosen cokernel or a zero object. -/
example {Z : C} (f : K.X 0 ⟶ Z) (hf : K.d 1 0 ≫ f = 0) :
    ∃ g : K.homology 0 ⟶ Z, ChainComplex.homologyZeroClass K ≫ g = f := by
  let g := CokernelCofork.IsColimit.desc'
    (ChainComplex.homologyZeroCoforkIsColimit K) f hf
  exact ⟨g.val, g.property⟩

/-- The zero-boundary case still requires no global cokernel or zero object. -/
example (h : K.d 1 0 = 0) : IsIso (ChainComplex.homologyZeroClass K) :=
  CokernelCofork.IsColimit.isIso_π (ChainComplex.homologyZeroCofork K)
    (ChainComplex.homologyZeroCoforkIsColimit K) h

variable {K} {L : ChainComplex C ℕ} [L.HasHomology 0]

example (φ : K ⟶ L) :
    ChainComplex.homologyZeroClass K ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ ChainComplex.homologyZeroClass L :=
  ChainComplex.homologyZeroClass_naturality φ

section Cokernels

variable [HasCokernel (K.d 1 0)] [HasCokernel (L.d 1 0)]

example : ChainComplex.homologyZeroClass K ≫
    (ChainComplex.homologyZeroIsoCokernel K).hom = cokernel.π (K.d 1 0) :=
  ChainComplex.homologyZeroIsoCokernel_class K

example (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ 0 ≫ (ChainComplex.homologyZeroIsoCokernel L).hom =
      (ChainComplex.homologyZeroIsoCokernel K).hom ≫
        cokernel.map (K.d 1 0) (L.d 1 0) (φ.f 1) (φ.f 0) (φ.comm 1 0).symm :=
  ChainComplex.homologyZeroIsoCokernel_naturality φ

end Cokernels
end WeakCategory

end MathlibExtTest.ChainComplexHomologyZero
