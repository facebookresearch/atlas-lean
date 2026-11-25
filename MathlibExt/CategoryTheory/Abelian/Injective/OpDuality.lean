/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Opposites of single complexes and resolutions

Single-object complexes commute with opposites. Opposites of injective
resolutions are projective resolutions and conversely. The unop functor
commutes with biproducts and is exact.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory Limits

open scoped ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- `single₀` commutes with `op` (candidate for upstream). -/
noncomputable def single₀OpIso (X : C) :
    ((CochainComplex.single₀ C).obj X).op ≅
      (ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X) := by
  refine HomologicalComplex.Hom.isoOfComponents ?f ?hf
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp only [HomologicalComplex.op_X, CochainComplex.single₀_obj_zero,
        ChainComplex.single₀_obj_zero]
      exact Iso.refl _
    · simp only [HomologicalComplex.op_X]
      have hX1 : ((CochainComplex.single₀ C).obj X).X n = (0 : C) := by
        simp [CochainComplex.single₀, HomologicalComplex.single, hn]
      have hX2 : ((ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X)).X n = (0 : Cᵒᵖ) := by
        simp [ChainComplex.single₀, HomologicalComplex.single, hn]
      rw [hX1, hX2]
      exact (IsZero.op (isZero_zero C)).iso (isZero_zero Cᵒᵖ)
  · intro n m hnm
    have e1 : (((CochainComplex.single₀ C).obj X).op).d n m = 0 := rfl
    have e2 : ((ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X)).d n m = 0 := rfl
    rw [e1, e2, zero_comp, comp_zero]

/-- The `single₀`/`op` iso is the identity in degree 0. -/
theorem single₀OpIso_hom_f_zero (X : C) :
    (single₀OpIso X).hom.f 0 = 𝟙 _ := rfl

/-- The opposite of an injective resolution is a projective resolution of the
opposite object (candidate for upstream). -/
noncomputable def injectiveResolutionOpProj {X : C} (I : InjectiveResolution X) :
    ProjectiveResolution (Opposite.op X) where
  complex := I.cocomplex.op
  projective := fun n => by
    rw [HomologicalComplex.op_X]
    have h := I.injective n
    infer_instance
  π := (HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map I.ι.op ≫
    (single₀OpIso X).hom
  quasiIso := by
    have h1 : QuasiIso ((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map I.ι.op) :=
      (HomologicalComplex.quasiIso_opFunctor_map_iff _).mpr I.quasiIso
    have h2 : QuasiIso (single₀OpIso X).hom := by
      have : IsIso (single₀OpIso X).hom := (single₀OpIso X).isIso_hom
      exact quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := h1) (hφ' := h2)

/-- `single₀` commutes with `unop` (dual of `single₀OpIso`).

Informal sketch: degreewise, at `0` both sides are `X` (`unop (op X) = X`
definitionally); elsewhere both sides are zero. Differentials vanish on both
sides since `single₀` has zero differentials. -/
noncomputable def single₀UnopIso (X : C) :
    (CochainComplex.single₀ C).obj X ≅
      ((ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X)).unop := by
  refine HomologicalComplex.Hom.isoOfComponents ?f ?hf
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp only [HomologicalComplex.unop_X, CochainComplex.single₀_obj_zero,
        ChainComplex.single₀_obj_zero]
      exact Iso.refl _
    · simp only [HomologicalComplex.unop_X]
      have hX1 : ((CochainComplex.single₀ C).obj X).X n = (0 : C) := by
        simp [CochainComplex.single₀, HomologicalComplex.single, hn]
      have hX2 : ((ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X)).X n = (0 : Cᵒᵖ) := by
        simp [ChainComplex.single₀, HomologicalComplex.single, hn]
      rw [hX1, hX2]
      exact (isZero_zero C).iso (IsZero.unop (isZero_zero Cᵒᵖ))
  · intro n m hnm
    have e1 : ((CochainComplex.single₀ C).obj X).d n m = 0 := rfl
    have e2 : (((ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X)).unop).d n m = 0 := rfl
    rw [e1, e2, zero_comp, comp_zero]

/-- The `single₀`/`unop` iso is the identity in degree 0. -/
theorem single₀UnopIso_hom_f_zero (X : C) :
    (single₀UnopIso X).hom.f 0 = 𝟙 _ := rfl

/-- The unopposite of a projective resolution in `Cᵒᵖ` is an injective
resolution (dual of `injectiveResolutionOpProj`).

Informal sketch: unop the complex (projectives dualize to injectives via the
Mathlib instance); the augmentation is `single₀UnopIso` followed by the unop'd
`π` (a quasi-iso since `unopFunctor` preserves quasi-isos). Stated over a
general `Y : Cᵒᵖ` (rather than `op X`) with the same baked instances as the
horseshoe endpoint ascriptions, so horseshoe-middle applications match
syntactically. -/
noncomputable def projectiveResolutionUnopInj {Y : Cᵒᵖ}
    (P : @ProjectiveResolution Cᵒᵖ Category.opposite
      (@Abelian.hasZeroObject Cᵒᵖ Category.opposite inferInstance)
      (@Preadditive.preadditiveHasZeroMorphisms Cᵒᵖ Category.opposite
        (@Abelian.toPreadditive Cᵒᵖ Category.opposite inferInstance))
      Y) :
    InjectiveResolution Y.unop where
  cocomplex := P.complex.unop
  injective := fun n => by
    rw [HomologicalComplex.unop_X]
    have h := P.projective n
    infer_instance
  ι := (single₀UnopIso Y.unop).hom ≫
    (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map P.π.op
  quasiIso := by
    have h1 : QuasiIso ((HomologicalComplex.unopFunctor C
      (ComplexShape.down ℕ)).map P.π.op) :=
      (HomologicalComplex.quasiIso_unopFunctor_map_iff _).mpr P.quasiIso
    have h2 : QuasiIso (single₀UnopIso (C := C) Y.unop).hom := by
      have hIso : IsIso (single₀UnopIso (C := C) Y.unop).hom :=
        (single₀UnopIso Y.unop).isIso_hom
      exact quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := h2) (hφ' := h1)

/-- `unopFunctor` preserves zero morphisms (it acts componentwise by `unop`). -/
theorem unopFunctor_preservesZeroMorphisms :
    (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- `unopFunctor` preserves finite limits (it is an equivalence). -/
theorem unopFunctor_preservesFiniteLimits :
    PreservesFiniteLimits
      (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)) := by
  have : PreservesLimitsOfSize.{0, 0}
      (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)) := inferInstance
  exact PreservesLimitsOfSize.preservesFiniteLimits _

/-- `unopFunctor` preserves finite colimits (it is an equivalence). -/
theorem unopFunctor_preservesFiniteColimits :
    PreservesFiniteColimits
      (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)) := by
  have : PreservesColimitsOfSize.{0, 0}
      (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)) := inferInstance
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- `unop` distributes over binary biproducts.

Informal sketch: both sides are biproducts of `unop A`, `unop B`; the maps
come from unop-ing the structure maps, and the roundtrips are `biprod.hom_ext`
plus `unop_comp`. -/
noncomputable def unopBiprodIso {A B : Cᵒᵖ} :
    (A ⊞ B).unop ≅ A.unop ⊞ B.unop where
  hom := biprod.lift (biprod.inl : A ⟶ A ⊞ B).unop (biprod.inr : B ⟶ A ⊞ B).unop
  inv := biprod.desc (biprod.fst : A ⊞ B ⟶ A).unop (biprod.snd : A ⊞ B ⟶ B).unop
  hom_inv_id := by
    show biprod.lift _ _ ≫ biprod.desc _ _ = 𝟙 _
    rw [biprod.lift_desc, ← unop_comp, ← unop_comp, ← unop_add, biprod.total,
      unop_id]
  inv_hom_id := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst]
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_desc, ← unop_comp, biprod.inl_fst,
          unop_id, ← Category.assoc, Category.comp_id, biprod.inl_fst]
      · rw [← Category.assoc, biprod.inr_desc, ← unop_comp, biprod.inl_snd,
          unop_zero, ← Category.assoc, Category.comp_id, biprod.inr_fst]
    · rw [Category.assoc, biprod.lift_snd]
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_desc, ← unop_comp, biprod.inr_fst,
          unop_zero, ← Category.assoc, Category.comp_id, biprod.inl_snd]
      · rw [← Category.assoc, biprod.inr_desc, ← unop_comp, biprod.inr_snd,
          unop_id, ← Category.assoc, Category.comp_id, biprod.inr_snd]

end CategoryTheory
