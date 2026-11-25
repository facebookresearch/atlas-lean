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

public import MathlibExt.CategoryTheory.ExactCategory.KernelCokernel
public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty

/-!
# An admissible kernel pulled back along an admissible epi

Pulling back the kernel map of an admissible exact sequence along an
admissible epimorphism gives the kernel of the composite epimorphism. This
identifies the resulting admissible exact sequence with its given maps and
its original quotient object.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private noncomputable def kernelCompIsLimitOfPullback
    {X Z Q P Y : C} {i : X ⟶ Z} {q : Z ⟶ Q} {p : Y ⟶ Z}
    {fst : P ⟶ X} {snd : P ⟶ Y}
    (wi : i ≫ q = 0) (hi : IsLimit (KernelFork.ofι i wi))
    (hpb : IsPullback fst snd i p) :
    IsLimit (KernelFork.ofι snd (show snd ≫ (p ≫ q) = 0 by
      rw [← Category.assoc, ← hpb.w, Category.assoc, wi, comp_zero])) := by
  let l {T : C} (t : T ⟶ Y) (ht : t ≫ (p ≫ q) = 0) : T ⟶ X :=
    hi.lift (KernelFork.ofι (t ≫ p) (by
      simpa only [Category.assoc] using ht))
  have hl {T : C} (t : T ⟶ Y) (ht : t ≫ (p ≫ q) = 0) :
      l t ht ≫ i = t ≫ p := by
    exact Fork.IsLimit.lift_ι hi
  refine KernelFork.IsLimit.ofι snd _
    (fun {T} t ht => hpb.lift (l t ht) t (hl t ht)) ?_ ?_
  · intro T t ht
    exact hpb.lift_snd _ _ _
  · intro T t ht m hm
    apply hpb.hom_ext
    · apply Fork.IsLimit.hom_ext hi
      change (m ≫ fst) ≫ i =
        (hpb.lift (l t ht) t (hl t ht) ≫ fst) ≫ i
      rw [hpb.lift_fst, hl t ht, Category.assoc, hpb.w, ← Category.assoc, hm]
    · rw [hpb.lift_snd, hm]

/-- The pullback of the first map of an admissible exact sequence along an
admissible epi is an admissible exact kernel sequence of the composite epi. -/
theorem isAdmissibleExact_pullbackKernelSequence
    {S : ShortComplex C} {P Y : C}
    {fst : P ⟶ S.X₁} {snd : P ⟶ Y} {p : Y ⟶ S.X₂}
    (hS : IsAdmissibleExact S) (hp : IsAdmissibleEpi p)
    (hpb : IsPullback fst snd S.f p) :
    IsAdmissibleExact (ShortComplex.mk snd (p ≫ S.g) (by
      rw [← Category.assoc, ← hpb.w, Category.assoc, S.zero, comp_zero])) := by
  let T : ShortComplex C := ShortComplex.mk snd (p ≫ S.g) (by
    rw [← Category.assoc, ← hpb.w, Category.assoc, S.zero, comp_zero])
  have hTg : IsAdmissibleEpi T.g := by
    change IsAdmissibleEpi (p ≫ S.g)
    exact admissibleEpi_comp.comp_mem p S.g hp (isAdmissibleEpi_g hS)
  have hTk : IsLimit (KernelFork.ofι T.f T.zero) :=
    kernelCompIsLimitOfPullback S.zero
      (isLimit_kernelFork_of_isAdmissibleExact hS) hpb
  exact isAdmissibleExact_of_isAdmissibleEpi_isLimit (S := T) hTg hTk

end CategoryTheory.ExactCategory
