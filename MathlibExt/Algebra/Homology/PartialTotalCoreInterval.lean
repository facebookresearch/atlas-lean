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

public import MathlibExt.Algebra.Homology.PartialTotalSpectralObject

/-!
# Core intervals of the partial-total filtration

This file identifies each interval selected by the increasing page-one core
with the corresponding uniform partial-total filtration step, first for
natural chain complexes and then after extension to integer cochain degree.

No mapping-cone homology, spectral page, or convergence statement is made.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- At filtration degree zero, the core interval `-1 ⟶ 0` is isomorphic to
the zero-stage partial-total step. -/
noncomputable def partialTotalE₁StepIsoZero (q : ℕ) :
    CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalEIntFiltration.map
          (homOfLE ((core).le₁₂ (0, q)))) ≅
      CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalStepShortComplex 0).f :=
  CategoryTheory.ComposableArrows.isoMk₁
    ((B.isZero_partialTotalE₁LowerZero q).iso
      (isZero_zero (ChainComplex C ℕ)))
    (B.partialTotalE₁UpperIso 0 q)
    ((B.isZero_partialTotalE₁LowerZero q).eq_of_src _ _)

/-- At filtration degree `m+1`, the core interval is isomorphic to the
successor partial-total step. -/
noncomputable def partialTotalE₁StepIsoSucc (m q : ℕ) :
    CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalEIntFiltration.map
          (homOfLE ((core).le₁₂ (m + 1, q)))) ≅
      CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalStepShortComplex (m + 1)).f := by
  refine CategoryTheory.ComposableArrows.isoMk₁
    (B.partialTotalE₁LowerSuccIso m q)
    (B.partialTotalE₁UpperIso (m + 1) q) ?_
  change B.partialTotalEIntFiltration.map
      (homOfLE ((core).le₁₂ (m + 1, q))) ≫
        (B.partialTotalE₁UpperIso (m + 1) q).hom =
    (B.partialTotalE₁LowerSuccIso m q).hom ≫
      B.partialTotalMap (Nat.le_succ m)
  apply (cancel_epi (B.partialTotalE₁LowerSuccIso m q).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc,
    partialTotalStepShortComplex_f_succ] using
      B.partialTotalE₁IntervalMap_succ m q

/-- Uniform chain-level comparison between the interval selected by the
increasing core and the `p`th partial-total step. -/
noncomputable def partialTotalE₁StepIso :
    (p q : ℕ) →
      CategoryTheory.ComposableArrows.mk₁
          (B.partialTotalEIntFiltration.map
            (homOfLE ((core).le₁₂ (p, q)))) ≅
        CategoryTheory.ComposableArrows.mk₁
          (B.partialTotalStepShortComplex p).f
  | 0, q => B.partialTotalE₁StepIsoZero q
  | m + 1, q => B.partialTotalE₁StepIsoSucc m q

/-- The upper component of the page-one interval coordinate is the
canonical finite-stage coordinate, up to the endpoint identification built
into the increasing core. -/
theorem partialTotalE₁StepIso_app_one_heq (p q : ℕ) :
    HEq ((B.partialTotalE₁StepIso p q).app 1)
      (B.partialTotalEIntFiltrationObjIso p) := by
  cases p with
  | zero =>
      have hidx : (core).i₂ (0, q) = (((0 : ℕ) : ℤ) : EInt) := by
        simp
      have hUpperIso :
          B.partialTotalE₁UpperIso 0 q =
            eqToIso (congrArg B.partialTotalEIntFiltration.obj hidx) ≪≫
              B.partialTotalEIntFiltrationObjIso 0 := by
        rfl
      have hEqToIso :
          (eqToIso
            (congrArg B.partialTotalEIntFiltration.obj hidx)).hom =
              𝟙 (B.partialTotalEIntFiltration.obj
                (((0 : ℕ) : ℤ) : EInt)) := by
        cases hidx
        rfl
      apply heq_of_eq
      change B.partialTotalE₁UpperIso 0 q =
        B.partialTotalEIntFiltrationObjIso 0
      rw [hUpperIso]
      apply Iso.ext
      rw [Iso.trans_hom, hEqToIso]
      exact Category.id_comp _
  | succ m =>
      have hidx : (core).i₂ (m + 1, q) =
          ((((m + 1 : ℕ) : ℕ) : ℤ) : EInt) := by
        simp
      have hUpperIso :
          B.partialTotalE₁UpperIso (m + 1) q =
            eqToIso (congrArg B.partialTotalEIntFiltration.obj hidx) ≪≫
              B.partialTotalEIntFiltrationObjIso (m + 1) := by
        rfl
      have hEqToIso :
          (eqToIso
            (congrArg B.partialTotalEIntFiltration.obj hidx)).hom =
              𝟙 (B.partialTotalEIntFiltration.obj
                ((((m + 1 : ℕ) : ℕ) : ℤ) : EInt)) := by
        cases hidx
        rfl
      apply heq_of_eq
      change B.partialTotalE₁UpperIso (m + 1) q =
        B.partialTotalEIntFiltrationObjIso (m + 1)
      rw [hUpperIso]
      apply Iso.ext
      rw [Iso.trans_hom, hEqToIso]
      exact Category.id_comp _

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- Uniform cochain-level comparison between the interval selected by the
increasing core and the cochain extension of the `p`th filtration step. -/
noncomputable def partialTotalE₁CochainStepIso
    (B' : HomologicalComplex₂ D (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p q : ℕ) :
    CategoryTheory.ComposableArrows.mk₁ (C := CochainComplex D ℤ)
        (B'.partialTotalCochainFiltration.map
          (homOfLE ((core).le₁₂ (p, q)))) ≅
      CategoryTheory.ComposableArrows.mk₁ (C := CochainComplex D ℤ)
        (B'.partialTotalStepCochainShortComplex p).f :=
  let F := ComplexShape.embeddingDownNat.extendFunctor D
  (F.mapComposableArrowsObjMk₁Iso
      (B'.partialTotalEIntFiltration.map
        (homOfLE ((core).le₁₂ (p, q))))).symm ≪≫
    (F.mapComposableArrows 1).mapIso (B'.partialTotalE₁StepIso p q) ≪≫
    F.mapComposableArrowsObjMk₁Iso
      (B'.partialTotalStepShortComplex p).f

end Abelian

end HomologicalComplex₂

end
