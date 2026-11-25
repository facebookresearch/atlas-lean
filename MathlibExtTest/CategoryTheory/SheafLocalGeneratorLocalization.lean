/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.SheafLocalGeneratorLocalization

/-!
# Tests for local theta-line generators and their localization

A local generator restricts to a local generator and generates the kernel ideal on its own object.
Zero is never a local generator on a nonzero ring, even when the kernel vanishes there, because
multiplication by a local generator must be injective. Local generators are denominators of the
localization, so their images become units there.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.CategoryTheory.SheafKernelCompletion
open MathlibExt.CategoryTheory.SheafLocalGeneratorLocalization

namespace MathlibExtTest.SheafLocalGeneratorLocalization

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (A H R : Sheaf J CommRingCat.{1}) (θ : A ⟶ H) (a : A ⟶ R)

/-- A local generator generates the kernel ideal on its own object. -/
example (U : Cᵒᵖ) (t : A.obj.obj U) (ht : IsLocalGenerator A H θ U t) :
    Ideal.span {t} = kernelIdeal A H θ U := by
  simpa using (ht U (𝟙 U)).1

/-- Local generators restrict to local generators. -/
example {U V : Cᵒᵖ} (f : U ⟶ V) (t : A.obj.obj U) (ht : IsLocalGenerator A H θ U t) :
    IsLocalGenerator A H θ V ((A.obj.map f).hom t) :=
  localGenerator_restrict A H θ f t ht

/-- Zero is not a local generator on a nonzero ring, whatever the kernel. -/
example (U : Cᵒᵖ) [Nontrivial (A.obj.obj U)] : ¬ IsLocalGenerator A H θ U 0 := by
  intro h
  have hinj := (h U (𝟙 U)).2
  have h01 : (0 : A.obj.obj U) ≠ 1 := zero_ne_one
  apply h01
  apply hinj
  simp

/-- The image of a local generator is a denominator of the localization. -/
example (U : Cᵒᵖ) (t : A.obj.obj U) (ht : IsLocalGenerator A H θ U t) :
    (a.hom.app U).hom t ∈ denominators A H R θ a U :=
  Submonoid.subset_closure ⟨t, ht, rfl⟩

end MathlibExtTest.SheafLocalGeneratorLocalization
