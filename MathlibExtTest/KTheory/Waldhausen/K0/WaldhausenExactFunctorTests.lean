/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.LinearAlgebra.Dimension.RankNullity
import MathlibExt.KTheory.Waldhausen.K0.WaldhausenExactFunctor

/-! # Waldhausen K₀ of evaluation on a pair of finite-dimensional vector spaces

Evaluation is exact for the mono/iso structures. The two evaluations induce
different coefficient homomorphisms, as detected by rank on the pair `(ℚ, 0)`.
-/

open CategoryTheory Limits ZeroObject WaldhausenKTheory

namespace MathlibExtTest.WaldhausenK0Functor

private abbrev Vect := FGModuleCat.{0} ℚ
private abbrev Pair := Discrete (Fin 2) ⥤ Vect

@[instance_reducible]
private noncomputable def monoStructure (C : Type*) [Category* C] [Abelian C]
    [HasPushouts C] : WaldhausenCategoryWithoutGluing C where
  cofibrations := MorphismProperty.monomorphisms C
  weakEquivalences := MorphismProperty.isomorphisms C
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration _ f := mono_of_source_iso_zero f (Iso.refl (0 : C))
  cofibration_pushout i hi _ f := by
    have : Mono i := hi
    exact ⟨pushout f i, pushout.inl f i, pushout.inr f i, IsPushout.of_hasPushout f i,
      Abelian.mono_pushout_of_mono_g f i⟩

private noncomputable local instance : WaldhausenCategoryWithoutGluing Vect := monoStructure Vect
private noncomputable local instance : WaldhausenCategoryWithoutGluing Pair := monoStructure Pair

private abbrev eval (i : Fin 2) : Pair ⥤ Vect := (evaluation _ _).obj ⟨i⟩

private theorem evalExact (i : Fin 2) : (eval i).IsWaldhausenExact where
  map_isZero h := (eval i).map_isZero h
  map_cofibration f h := (NatTrans.mono_iff_mono_app f).mp h ⟨i⟩
  map_weakEquivalence f h := by
    have : IsIso f := h
    change IsIso ((eval i).map f)
    infer_instance
  map_pushout _ _ _ _ _ h := (eval i).map_isPushout h

private noncomputable def lineAndZero : Pair :=
  Discrete.functor fun i => if i = 0 then FGModuleCat.of ℚ ℚ else 0

-- The following rank argument uses the same cofiber-as-cokernel calculation
-- as `MathlibExtTest/KTheory/Waldhausen/K0/BasicTests.lean`.
private noncomputable def dimension : Skeleton Vect → ℤ :=
  Quotient.lift (fun X : Vect => (Module.finrank ℚ X : ℤ)) fun _ _ ⟨e⟩ =>
    congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv e).finrank_eq

private theorem dimension_weak {X Y : Vect} (f : X ⟶ Y) (h : IsWeakEquivalence f) :
    dimension (toSkeleton X) = dimension (toSkeleton Y) := by
  have : IsIso f := h
  exact congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv (asIso f)).finrank_eq

private theorem dimension_cofiber {X Y Z : Vect} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : IsCofibrationSequence f g) :
    dimension (toSkeleton Y) = dimension (toSkeleton X) + dimension (toSkeleton Z) := by
  obtain ⟨hf, toZero, fromZero, push⟩ := h
  have : Mono f := hf
  let F := forget₂ Vect (ModuleCat.{0} ℚ)
  have hp := F.map_isPushout push
  have zh : IsZero (F.obj (0 : Vect)) := F.map_isZero (isZero_zero _)
  have hfg : F.map f ≫ F.map g = 0 := by
    rw [← hp.w, zh.eq_of_src (F.map fromZero) 0, comp_zero]
  have hc : IsColimit (CokernelCofork.ofπ (F.map g) hfg) := by
    let commute {W : ModuleCat ℚ} (k : F.obj Y ⟶ W) (hk : F.map f ≫ k = 0) :
        F.map toZero ≫ 0 = F.map f ≫ k := by rw [hk, comp_zero]
    refine CokernelCofork.IsColimit.ofπ _ _ (fun k hk => hp.desc 0 k (commute k hk))
      (fun k hk => hp.inr_desc _ _ (commute k hk)) ?_
    intro W k hk m hm
    exact hp.hom_ext (zh.eq_of_src _ _) (hm.trans (hp.inr_desc _ _ (commute k hk)).symm)
  let e := hc.coconePointUniqueUpToIso (ModuleCat.cokernelIsColimit (F.map f))
  have hquot : Module.finrank ℚ Z = Module.finrank ℚ (Y ⧸ (F.map f).hom.range) :=
    e.toLinearEquiv.finrank_eq
  have hinj : Function.Injective (F.map f).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hrange : Module.finrank ℚ (F.map f).hom.range = Module.finrank ℚ X :=
    (LinearEquiv.ofInjective _ hinj).finrank_eq.symm
  have hfinite : Module.Finite ℚ (F.obj Y) := (inferInstance : Module.Finite ℚ Y)
  have hr := (F.map f).hom.range.finrank_quotient_add_finrank
  change Module.finrank ℚ (Y ⧸ (F.map f).hom.range) + _ = Module.finrank ℚ Y at hr
  rw [← hquot, hrange, add_comm] at hr
  change (Module.finrank ℚ Y : ℤ) = (Module.finrank ℚ X : ℤ) + (Module.finrank ℚ Z : ℤ)
  exact_mod_cast hr.symm

private noncomputable def evaluationRank (i : Fin 2) : K0 Pair →+ ℤ :=
  (K0.lift dimension dimension_weak dimension_cofiber).comp
    (K0.mapOfWaldhausenExact (eval i) (evalExact i))

example : evaluationRank 0 (K0.mk lineAndZero) = 1 := by
  rw [evaluationRank, K0.lift_comp_mapOfWaldhausenExact, K0.lift_mk]
  simp only [Function.comp_apply, Functor.mapSkeleton_obj_toSkeleton]
  change dimension (toSkeleton (FGModuleCat.of ℚ ℚ)) = 1
  change (Module.finrank ℚ ℚ : ℤ) = 1
  simp

example : evaluationRank 1 (K0.mk lineAndZero) = 0 := by
  simp only [evaluationRank, AddMonoidHom.comp_apply, K0.mapOfWaldhausenExact_mk]
  change K0.lift dimension dimension_weak dimension_cofiber (K0.mk (0 : Vect)) = 0
  simp only [K0.mk_zero, map_zero]

/-- The actual split cofiber of the identity of the diagram, evaluated at its nonzero slot. -/
example : IsCofibrationSequence ((eval 0).map (𝟙 lineAndZero))
    ((eval 0).map (0 : lineAndZero ⟶ (0 : Pair))) := by
  apply (evalExact 0).map_cofibrationSequence
  refine ⟨?_, 0, 𝟙 (0 : Pair), IsPushout.id_vert (0 : lineAndZero ⟶ (0 : Pair))⟩
  change Mono (𝟙 lineAndZero)
  infer_instance

end MathlibExtTest.WaldhausenK0Functor
