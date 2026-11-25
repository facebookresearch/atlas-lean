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

public import MathlibExt.Algebra.Homology.TensorHomologyDesc
public import MathlibExt.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Functor comparison for the original tensor homology product

Canonical mapped-cycle and mapped-homology comparisons retain the original
cycle inclusions and homology projections. A proved cycle-product square
then descends through the original homology cokernels on both categories.
The tensor comparison is the strong monoidal functor's original `μ` map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ShortComplex

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [F.IsEquivalence]

/-- The inverse of the original mapped-homology projection comparison. -/
@[reassoc]
theorem map_homologyπ_comp_mapHomologyIso_inv (S : ShortComplex C) :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  apply (cancel_epi (S.mapCyclesIso F).hom).mp
  rw [← Category.assoc, ← S.homologyπ_comp_mapHomologyIso_hom F]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

variable {F}
variable {S : ShortComplex C} {T : ShortComplex D}

/-- The canonical comparison of original source cycles with actual target
cycles through a genuine mapped-source short-complex isomorphism. -/
def functorCyclesComparisonIso (e : S.map F ≅ T) : F.obj S.cycles ≅ T.cycles :=
  (S.mapCyclesIso F).symm ≪≫ (cyclesFunctor D).mapIso e

/-- The canonical comparison of original source homology with actual target
homology through the original homology functor. -/
def functorHomologyComparisonIso (e : S.map F ≅ T) : F.obj S.homology ≅ T.homology :=
  (S.mapHomologyIso F).symm ≪≫ (homologyFunctor D).mapIso e

/-- An unchanged mapped short complex retains its original cycle comparison. -/
@[simp]
theorem functorCyclesComparisonIso_refl (S : ShortComplex C) :
    functorCyclesComparisonIso (F := F) (Iso.refl (S.map F)) = (S.mapCyclesIso F).symm := by
  dsimp only [functorCyclesComparisonIso]
  rw [Functor.mapIso_refl]
  change (S.mapCyclesIso F).symm ≪≫ Iso.refl (S.map F).cycles = (S.mapCyclesIso F).symm
  exact Iso.trans_refl _

/-- An unchanged mapped short complex retains its original homology comparison. -/
@[simp]
theorem functorHomologyComparisonIso_refl (S : ShortComplex C) :
    functorHomologyComparisonIso (F := F) (Iso.refl (S.map F)) = (S.mapHomologyIso F).symm := by
  dsimp only [functorHomologyComparisonIso]
  rw [Functor.mapIso_refl]
  change (S.mapHomologyIso F).symm ≪≫ Iso.refl (S.map F).homology = (S.mapHomologyIso F).symm
  exact Iso.trans_refl _

/-- The canonical cycle comparison preserves the original mapped inclusion. -/
@[reassoc]
theorem functorCyclesComparisonIso_hom_iCycles (e : S.map F ≅ T) :
    (functorCyclesComparisonIso e).hom ≫ T.iCycles =
      F.map S.iCycles ≫ e.hom.τ₂ := by
  dsimp only [functorCyclesComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, cyclesFunctor]
  rw [Category.assoc, cyclesMap_i]
  rw [← S.mapCyclesIso_hom_iCycles F]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The canonical cycle and homology comparisons preserve the original
source and target homology projections. -/
@[reassoc]
theorem functorHomologyComparisonIso_projection (e : S.map F ≅ T) :
    F.map S.homologyπ ≫ (functorHomologyComparisonIso e).hom =
      (functorCyclesComparisonIso e).hom ≫ T.homologyπ := by
  dsimp only [functorHomologyComparisonIso, functorCyclesComparisonIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homologyFunctor, cyclesFunctor]
  rw [← Category.assoc, map_homologyπ_comp_mapHomologyIso_inv F S]
  simp only [Category.assoc]
  rw [homologyπ_naturality]

variable (F)

/-- The original mapped homology projection factors through the actual
mapped-short-complex projection and its canonical comparison isomorphisms. -/
theorem map_homologyπ_eq_comparison (S : ShortComplex C) :
    F.map S.homologyπ =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom := by
  apply (cancel_epi (S.mapCyclesIso F).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (S.homologyπ_comp_mapHomologyIso_hom F).symm

variable [MonoidalCategory D] [MonoidalPreadditive D]
variable [∀ A : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]

/-- Tensoring the original mapped homology projections is epi because the
actual mapped short-complex projections are preserved cokernel projections. -/
theorem epi_tensor_map_homologyπ (S₁ S₂ : ShortComplex C) :
    Epi (F.map S₁.homologyπ ⊗ₘ F.map S₂.homologyπ) := by
  let c₁ : CokernelCofork (S₁.map F).toCycles :=
    CokernelCofork.ofπ (S₁.map F).homologyπ (S₁.map F).toCycles_comp_homologyπ
  let c₂ : CokernelCofork (S₂.map F).toCycles :=
    CokernelCofork.ofπ (S₂.map F).homologyπ (S₂.map F).toCycles_comp_homologyπ
  let _ : Epi ((S₁.map F).homologyπ ⊗ₘ (S₂.map F).homologyπ) :=
    CokernelCofork.epi_tensor_π c₁ (S₁.map F).homologyIsCokernel
      c₂ (S₂.map F).homologyIsCokernel
  rw [map_homologyπ_eq_comparison F S₁, map_homologyπ_eq_comparison F S₂,
    ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
  infer_instance

end CategoryTheory.ShortComplex

namespace HomologicalComplex

universe w₁ w₂ w₃

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [F.IsEquivalence]

/-- The canonical source-to-target cycle comparison in the actual complex
cycle objects at the chosen degree. -/
def functorCyclesComparisonIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (L : HomologicalComplex D c) (j : ι)
    (e : (K.sc j).map F ≅ L.sc j) : F.obj (K.cycles j) ≅ L.cycles j :=
  ShortComplex.functorCyclesComparisonIso e

/-- The canonical source-to-target homology comparison in the original
complex homology objects, using the native short-complex homology functor. -/
def functorHomologyComparisonIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (L : HomologicalComplex D c) (j : ι)
    (e : (K.sc j).map F ≅ L.sc j) : F.obj (K.homology j) ≅ L.homology j :=
  ShortComplex.functorHomologyComparisonIso e

/-- The actual complex cycle and homology comparisons retain both native
homology projections. -/
@[reassoc]
theorem functorHomologyComparisonIso_projection {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (L : HomologicalComplex D c) (j : ι)
    (e : (K.sc j).map F ≅ L.sc j) :
    F.map (K.homologyπ j) ≫ (functorHomologyComparisonIso F K L j e).hom =
      (functorCyclesComparisonIso F K L j e).hom ≫ L.homologyπ j :=
  ShortComplex.functorHomologyComparisonIso_projection e

variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [MonoidalCategory D] [MonoidalPreadditive D]
variable [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]
variable [∀ A : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]
variable [F.Monoidal]
variable {ι₁ : Type w₁} {ι₂ : Type w₂} {ι₃ : Type w₃}
variable {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} {c₃ : ComplexShape ι₃}
variable (K₁ : HomologicalComplex C c₁) (K₂ : HomologicalComplex C c₂)
  (K₃ : HomologicalComplex C c₃)
variable (L₁ : HomologicalComplex D c₁) (L₂ : HomologicalComplex D c₂)
  (L₃ : HomologicalComplex D c₃)
variable (i₁ j₁ : ι₁) (h₁ : c₁.prev j₁ = i₁)
  (i₂ j₂ : ι₂) (h₂ : c₂.prev j₂ = i₂) (j₃ : ι₃)

variable (e₁ : (K₁.sc j₁).map F ≅ L₁.sc j₁)
  (e₂ : (K₂.sc j₂).map F ≅ L₂.sc j₂)
  (e₃ : (K₃.sc j₃).map F ≅ L₃.sc j₃)
variable (k : K₁.cycles j₁ ⊗ K₂.cycles j₂ ⟶ K₃.cycles j₃)
  (l : L₁.cycles j₁ ⊗ L₂.cycles j₂ ⟶ L₃.cycles j₃)
variable
  (hk : coprod.desc (K₁.toCycles i₁ j₁ ▷ K₂.cycles j₂)
    (K₁.cycles j₁ ◁ K₂.toCycles i₂ j₂) ≫ (k ≫ K₃.homologyπ j₃) = 0)
  (hl : coprod.desc (L₁.toCycles i₁ j₁ ▷ L₂.cycles j₂)
    (L₁.cycles j₁ ◁ L₂.toCycles i₂ j₂) ≫ (l ≫ L₃.homologyπ j₃) = 0)
  (hcycles :
    ((functorCyclesComparisonIso F K₁ L₁ j₁ e₁).hom ⊗ₘ
      (functorCyclesComparisonIso F K₂ L₂ j₂ e₂).hom) ≫ l =
    Functor.LaxMonoidal.μ F (K₁.cycles j₁) (K₂.cycles j₂) ≫ F.map k ≫
      (functorCyclesComparisonIso F K₃ L₃ j₃ e₃).hom)

include hcycles in
/-- A proved cross-category square on actual cycles descends through the
original homology cokernels. The target tensor descent is its independent
original construction, and `F.μ` is the original strong monoidal comparison. -/
theorem tensorHomologyDesc_functorComparison :
    ((functorHomologyComparisonIso F K₁ L₁ j₁ e₁).hom ⊗ₘ
      (functorHomologyComparisonIso F K₂ L₂ j₂ e₂).hom) ≫
        tensorHomologyDesc L₁ i₁ j₁ h₁ L₂ i₂ j₂ h₂ (l ≫ L₃.homologyπ j₃) hl =
      Functor.LaxMonoidal.μ F (K₁.homology j₁) (K₂.homology j₂) ≫
        F.map (tensorHomologyDesc K₁ i₁ j₁ h₁ K₂ i₂ j₂ h₂
          (k ≫ K₃.homologyπ j₃) hk) ≫
            (functorHomologyComparisonIso F K₃ L₃ j₃ e₃).hom := by
  let _ : Epi (F.map (K₁.homologyπ j₁) ⊗ₘ F.map (K₂.homologyπ j₂)) :=
    ShortComplex.epi_tensor_map_homologyπ F (K₁.sc j₁) (K₂.sc j₂)
  apply (cancel_epi (F.map (K₁.homologyπ j₁) ⊗ₘ F.map (K₂.homologyπ j₂))).mp
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    functorHomologyComparisonIso_projection,
    functorHomologyComparisonIso_projection,
    ← tensorHom_comp_tensorHom_assoc, tensor_homologyπ_comp_tensorHomologyDesc]
  rw [← Category.assoc, hcycles]
  simp only [Category.assoc]
  rw [← functorHomologyComparisonIso_projection]
  rw [← Category.assoc (F.map k) (F.map (K₃.homologyπ j₃))
    (functorHomologyComparisonIso F K₃ L₃ j₃ e₃).hom, ← F.map_comp,
    Functor.LaxMonoidal.μ_natural_assoc]
  rw [← Category.assoc
    (F.map (K₁.homologyπ j₁ ⊗ₘ K₂.homologyπ j₂))
    (F.map (tensorHomologyDesc K₁ i₁ j₁ h₁ K₂ i₂ j₂ h₂
      (k ≫ K₃.homologyπ j₃) hk))
    (functorHomologyComparisonIso F K₃ L₃ j₃ e₃).hom,
    ← F.map_comp, tensor_homologyπ_comp_tensorHomologyDesc]

end HomologicalComplex
