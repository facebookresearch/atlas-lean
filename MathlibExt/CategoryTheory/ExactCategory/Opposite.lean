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

public import MathlibExt.CategoryTheory.ExactCategory.Split
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The opposite exact structure

The opposite of an exact category is exact. Admissibility is tested by
reversing the short complex into the original category. The construction is
a named value, so a choice of exact structure remains explicit.
-/

public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem oppositeAdmissibleMono_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    admissibleMonosOf Cᵒᵖ (fun S => IsAdmissibleExact S.unop) f ↔
      IsAdmissibleEpi f.unop := by
  constructor
  · rintro ⟨Z, g, w, hS⟩
    exact ⟨Z.unop, g.unop, by rw [← unop_comp, w, unop_zero], hS⟩
  · rintro ⟨Z, g, w, hS⟩
    exact ⟨op Z, g.op, by
      simpa only [op_comp, Quiver.Hom.op_unop, op_zero] using
        congrArg Quiver.Hom.op w, hS⟩

private theorem oppositeAdmissibleEpi_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    admissibleEpisOf Cᵒᵖ (fun S => IsAdmissibleExact S.unop) f ↔
      IsAdmissibleMono f.unop := by
  constructor
  · rintro ⟨Z, g, w, hS⟩
    exact ⟨Z.unop, g.unop, by rw [← unop_comp, w, unop_zero], hS⟩
  · rintro ⟨Z, g, w, hS⟩
    exact ⟨op Z, g.op, by
      simpa only [op_comp, Quiver.Hom.op_unop, op_zero] using
        congrArg Quiver.Hom.op w, hS⟩

/-- The exact structure on the opposite category, with admissible rows
precisely the reversals of the original admissible rows. -/
@[instance_reducible]
noncomputable def oppositeExactCategory : ExactCategory Cᵒᵖ where
  IsAdmissibleExact S := IsAdmissibleExact S.unop
  shortExact_of_isAdmissibleExact := by
    intro S hS
    exact ShortComplex.shortExact_of_iso (ShortComplex.unopOp S)
      (shortExact_of_isAdmissibleExact hS).op
  isLimit_kernelFork := by
    intro S hS
    refine ⟨?_⟩
    exact CokernelCofork.IsColimit.ofπOp S.f.unop S.unop.zero
      (isColimit_cokernelCofork_of_isAdmissibleExact hS)
  isColimit_cokernelCofork := by
    intro S hS
    refine ⟨?_⟩
    exact KernelFork.IsLimit.ofιOp S.g.unop S.unop.zero
      (isLimit_kernelFork_of_isAdmissibleExact hS)
  isAdmissibleExact_of_iso := by
    intro S T e hS
    exact isAdmissibleExact_of_iso
      (Iso.unop ((ShortComplex.unopFunctor C).mapIso e.symm)) hS
  isAdmissibleExact_split X Y :=
    isAdmissibleExact_of_splitting
      (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).unop
  admissibleMono_comp :=
    { comp_mem := by
        intro X Y Z f g hf hg
        apply (oppositeAdmissibleMono_iff C (f ≫ g)).mpr
        change IsAdmissibleEpi (g.unop ≫ f.unop)
        change admissibleEpisOf C IsAdmissibleExact (g.unop ≫ f.unop)
        exact admissibleEpi_comp.comp_mem g.unop f.unop
          ((oppositeAdmissibleMono_iff C g).mp hg)
          ((oppositeAdmissibleMono_iff C f).mp hf) }
  admissibleEpi_comp :=
    { comp_mem := by
        intro X Y Z f g hf hg
        apply (oppositeAdmissibleEpi_iff C (f ≫ g)).mpr
        change IsAdmissibleMono (g.unop ≫ f.unop)
        change admissibleMonosOf C IsAdmissibleExact (g.unop ≫ f.unop)
        exact admissibleMono_comp.comp_mem g.unop f.unop
          ((oppositeAdmissibleEpi_iff C g).mp hg)
          ((oppositeAdmissibleEpi_iff C f).mp hf) }
  admissibleMono_pushout := by
    intro X Y i hi X' f
    obtain ⟨P, fst, snd, hpb, hfst⟩ :=
      admissibleEpi_pullback Y.unop X.unop i.unop
        ((oppositeAdmissibleMono_iff C i).mp hi) X'.unop f.unop
    exact ⟨op P, fst.op, snd.op, hpb.op.flip,
      (oppositeAdmissibleMono_iff C fst.op).mpr hfst⟩
  admissibleEpi_pullback := by
    intro Y Z p hp Z' g
    obtain ⟨P, inl, inr, hpo, hinl⟩ :=
      admissibleMono_pushout Z.unop Y.unop p.unop
        ((oppositeAdmissibleEpi_iff C p).mp hp) Z'.unop g.unop
    exact ⟨op P, inl.op, inr.op, hpo.op.flip,
      (oppositeAdmissibleEpi_iff C inl.op).mpr hinl⟩

/-- Membership in the named opposite exact structure is admissibility of
the reversed short complex in the original category. -/
theorem oppositeExactCategory_isAdmissibleExact_iff (S : ShortComplex Cᵒᵖ) :
    @IsAdmissibleExact Cᵒᵖ _ _ _ _ (oppositeExactCategory C) S ↔
      IsAdmissibleExact S.unop :=
  Iff.rfl

/-- Reversing an admissible exact row gives an admissible exact row in the
named opposite exact structure. -/
theorem isAdmissibleExact_op {S : ShortComplex C} (hS : IsAdmissibleExact S) :
    @IsAdmissibleExact Cᵒᵖ _ _ _ _ (oppositeExactCategory C) S.op :=
  (oppositeExactCategory_isAdmissibleExact_iff C S.op).mpr
    (isAdmissibleExact_of_iso (ShortComplex.opUnop S).symm hS)

end CategoryTheory.ExactCategory
