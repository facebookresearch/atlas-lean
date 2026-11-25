/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtalePositiveExt

/-! # Actual maps of small étale sections-resolution classes -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (X : Scheme.{u})
variable {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}

private abbrev sectionComplex (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (injectiveResolution Q).cocomplex

private def sectionShortMap (τ : Q ⟶ Q') (n : ℕ) :
    positiveShort.{u, w} X Q n ⟶ positiveShort.{u, w} X Q' n :=
  (HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
    n (n + 1) (n + 2)).map
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc τ (injectiveResolution Q') (injectiveResolution Q)))

private def transportedSectionCycle (τ : Q ⟶ Q') (n : ℕ)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker) :
    (positiveShort.{u, w} X Q' n).g.hom.ker :=
  ⟨(sectionShortMap.{u, w} X τ n).τ₂ z.val, by
    have hz : (positiveShort.{u, w} X Q n).g z.val = 0 := z.property
    exact (ConcreteCategory.congr_hom (sectionShortMap.{u, w} X τ n).comm₂₃ z.val).trans
      ((congrArg (sectionShortMap.{u, w} X τ n).τ₃ hz).trans
        ((sectionShortMap.{u, w} X τ n).τ₃.hom.map_zero))⟩

private theorem categorical_section_cycle_map (τ : Q ⟶ Q') (n : ℕ)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker) :
    ShortComplex.cyclesMap (sectionShortMap.{u, w} X τ n)
      ((positiveShort.{u, w} X Q n).abCyclesIso.inv z) =
        (positiveShort.{u, w} X Q' n).abCyclesIso.inv
          (transportedSectionCycle.{u, w} X τ n z) := by
  apply (AddCommGrpCat.mono_iff_injective
    (positiveShort.{u, w} X Q' n).iCycles).mp inferInstance
  have h := ConcreteCategory.congr_hom
    (ShortComplex.cyclesMap_i (sectionShortMap.{u, w} X τ n))
      ((positiveShort.{u, w} X Q n).abCyclesIso.inv z)
  exact h.trans ((congrArg (sectionShortMap.{u, w} X τ n).τ₂
    ((positiveShort.{u, w} X Q n).abCyclesIso_inv_apply_iCycles z)).trans
      ((positiveShort.{u, w} X Q' n).abCyclesIso_inv_apply_iCycles
        (transportedSectionCycle.{u, w} X τ n z)).symm)

private theorem transported_section_cycle_class (τ : Q ⟶ Q') (n : ℕ)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker) :
    positiveCycleClass.{u, w} X Q' n (transportedSectionCycle.{u, w} X τ n z) =
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived (n + 1)).map τ
        (positiveCycleClass.{u, w} X Q n z) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let φ := InjectiveResolution.desc τ (injectiveResolution Q') (injectiveResolution Q)
  let ψ := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  let B := HomologicalComplex.homologyFunctorIso' AddCommGrpCat (ComplexShape.up ℕ)
    n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))
  let c := (positiveShort.{u, w} X Q n).homologyπ
    ((positiveShort.{u, w} X Q n).abCyclesIso.inv z)
  have hπ : (positiveShort.{u, w} X Q' n).homologyπ
      ((positiveShort.{u, w} X Q' n).abCyclesIso.inv
        (transportedSectionCycle.{u, w} X τ n z)) =
      ShortComplex.homologyMap (sectionShortMap.{u, w} X τ n) c := by
    rw [← categorical_section_cycle_map.{u, w} X τ n z]
    exact (ConcreteCategory.congr_hom
      (ShortComplex.homologyπ_naturality (sectionShortMap.{u, w} X τ n))
        ((positiveShort.{u, w} X Q n).abCyclesIso.inv z)).symm
  have hB := ConcreteCategory.congr_hom (B.inv.naturality ψ) c
  change ((injectiveResolution Q').isoRightDerivedObj Γ (n + 1)).inv
      ((B.app (sectionComplex.{u, w} X Q')).inv _) =
    (Γ.rightDerived (n + 1)).map τ
      (((injectiveResolution Q).isoRightDerivedObj Γ (n + 1)).inv
        ((B.app (sectionComplex.{u, w} X Q)).inv c))
  rw [hπ]
  calc
    _ = ((injectiveResolution Q').isoRightDerivedObj Γ (n + 1)).inv
        (HomologicalComplex.homologyMap ψ (n + 1)
          ((B.app (sectionComplex.{u, w} X Q)).inv c)) :=
      congrArg (fun x => ((injectiveResolution Q').isoRightDerivedObj Γ (n + 1)).inv x) hB
    _ = _ := (ConcreteCategory.congr_hom
      (InjectiveResolution.isoRightDerivedObj_inv_naturality τ
        (injectiveResolution Q) (injectiveResolution Q') φ
        (InjectiveResolution.desc_commutes_zero τ (injectiveResolution Q')
          (injectiveResolution Q)) Γ (n + 1))
            ((B.app (sectionComplex.{u, w} X Q)).inv c)).symm

/-- Internally chosen resolution descent transports every original cycle
and its actual class. -/
theorem sections_resolution_class_map_naturality (τ : Q ⟶ Q') (n : ℕ)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker) :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
    let φ := InjectiveResolution.desc τ (injectiveResolution Q') (injectiveResolution Q)
    ∃ zτ : (positiveShort.{u, w} X Q' n).g.hom.ker,
      zτ.val = Γ.map (φ.f (n + 1)) z.val ∧
      positiveCycleClass.{u, w} X Q' n zτ =
        (Γ.rightDerived (n + 1)).map τ (positiveCycleClass.{u, w} X Q n z) := by
  intro Γ φ
  exact ⟨transportedSectionCycle.{u, w} X τ n z, rfl,
    transported_section_cycle_class.{u, w} X τ n z⟩

end AlgebraicGeometry.Scheme.DerivedSections
