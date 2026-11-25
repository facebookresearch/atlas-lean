/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Finsupp
import all MathlibExt.CategoryTheory.ExactCategory.AdmissibleMonoCokernelComposition
import MathlibExt.CategoryTheory.ExactCategory.FullSubcategory

/-! A flag of nonzero finite-dimensional rational vector spaces with its actual quotients. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

noncomputable section

namespace ExactCategoryFullSubcategoryCompositionClients

private def finiteModules : ObjectProperty (ModuleCat ℚ) := fun V => Module.Finite ℚ V

private instance : finiteModules.IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hX
  let : Module.Finite ℚ X := hX
  exact Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)

private instance : finiteModules.ContainsZero where
  exists_zero := by
    let V : ModuleCat ℚ := 0
    let : Subsingleton V := ModuleCat.subsingleton_of_isZero (isZero_zero _)
    exact ⟨V, isZero_zero _, inferInstanceAs (Module.Finite ℚ V)⟩

private instance : finiteModules.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    let : Module.Finite ℚ S.X₁ := h₁
    let : Module.Finite ℚ S.X₃ := h₃
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      hS.moduleCat_surjective_g

private abbrev FiniteSpace := finiteModules.FullSubcategory

@[instance_reducible]
private def finiteExact : ExactCategory FiniteSpace := ofFullSubcategory finiteModules

attribute [local instance] finiteExact

private def line : FiniteSpace := ⟨ModuleCat.of ℚ ℚ, inferInstanceAs (Module.Finite ℚ ℚ)⟩
private abbrev plane : FiniteSpace := line ⊞ line
private abbrev space : FiniteSpace := plane ⊞ line

private abbrev first : line ⟶ plane := biprod.inl
private abbrev second : plane ⟶ space := biprod.inl

private theorem line_id_ne_zero : 𝟙 line ≠ (0 : line ⟶ line) := by
  intro h
  have impossible : (1 : ℚ) = 0 :=
    congrArg (fun f : line ⟶ line => f.hom.hom (1 : ℚ)) h
  exact one_ne_zero impossible

private theorem first_ne_zero : first ≠ 0 := by
  intro h
  apply line_id_ne_zero
  simpa using congrArg (fun f => f ≫ (biprod.fst : plane ⟶ line)) h

private theorem second_ne_zero : second ≠ 0 := by
  intro h
  apply first_ne_zero
  simpa using congrArg (fun f => first ≫ f ≫ (biprod.fst : space ⟶ plane)) h

private def firstRow : AdmissibleMonoCokernelPresentation first where
  cokernel := line
  π := biprod.snd
  zero := by simp
  exact := isAdmissibleExact_split line line

private def secondRow : AdmissibleMonoCokernelPresentation second where
  cokernel := line
  π := biprod.snd
  zero := by simp
  exact := isAdmissibleExact_split plane line

private def compositeRow := firstRow.composite secondRow

-- Kill the first coordinate of the flag, keeping the second and third coordinates.
private def quotientCoordinates : space ⟶ plane :=
  biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd

private def coordinateDesc :
    {d : compositeRow.cokernel ⟶ plane // compositeRow.π ≫ d = quotientCoordinates} :=
  CokernelCofork.IsColimit.desc' compositeRow.cokernelIsColimit quotientCoordinates (by
    apply biprod.hom_ext
    · simp [quotientCoordinates, Category.assoc]
    · simp [quotientCoordinates, Category.assoc])

private theorem composite_keeps_last_coordinate :
    biprod.inr ≫ compositeRow.π ≫ coordinateDesc.val = (biprod.inr : line ⟶ plane) := by
  rw [coordinateDesc.property]
  apply biprod.hom_ext <;> simp [quotientCoordinates, Category.assoc]

private theorem composite_cokernel_extension :
    IsAdmissibleExact (firstRow.compositeCokernelSequence secondRow) :=
  firstRow.compositeCokernelSequence_exact secondRow

private def doubleLine : line ⟶ line := 𝟙 line + 𝟙 line

private def cobase : firstRow.CobaseChange doubleLine :=
  (firstRow.cobaseChange_nonempty doubleLine).some

private def cobaseQuotient : cobase.obj ⟶ line :=
  (firstRow.cobaseChangePresentation cobase).π

-- Push out the first inclusion along doubling. The returned projection kills
-- the new first summand and sends the old second summand to the original line.
private theorem cobase_retains_quotient :
    (firstRow.cobaseChangePresentation cobase).cokernel = line ∧
      cobase.inl ≫ cobaseQuotient = 0 ∧
      (biprod.inr : line ⟶ plane) ≫ cobase.inr ≫ cobaseQuotient = 𝟙 line := by
  refine ⟨firstRow.cobaseChangePresentation_cokernel cobase,
    (firstRow.cobaseChangePresentation cobase).zero, ?_⟩
  have projection : cobaseQuotient =
      pushoutQuotientMap doubleLine first firstRow.π cobase.inl cobase.inr
        firstRow.zero cobase.square := rfl
  exact (congrArg (fun q : cobase.obj ⟶ line => (biprod.inr : line ⟶ plane) ≫ cobase.inr ≫ q)
    projection).trans ((congrArg (fun q : plane ⟶ firstRow.cokernel =>
      (biprod.inr : line ⟶ plane) ≫ q)
      (pushoutQuotientMap_y doubleLine first firstRow.π cobase.inl cobase.inr
        firstRow.zero cobase.square)).trans biprod.inr_snd)

end ExactCategoryFullSubcategoryCompositionClients
