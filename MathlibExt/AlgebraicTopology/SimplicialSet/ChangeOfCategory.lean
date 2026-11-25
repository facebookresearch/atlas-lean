/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua, Avocado -/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.AlgebraicTopology.SimplicialSet.PairChains

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [HasCoproducts.{w} C]
variable {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{w} D]

/-- A colimit-preserving functor commutes with copowers by a type. -/
noncomputable def mapSigmaConstIso (F : Functor C D)
    [PreservesColimitsOfSize.{w, w} F] (R : C) :
    sigmaConst.{w}.obj R ⋙ F ≅ sigmaConst.{w}.obj (F.obj R) :=
  NatIso.ofComponents
    (fun X ↦ (asIso (sigmaComparison F (fun _ : X ↦ R))).symm)
    (fun {X Y} f ↦ by
      rw [← cancel_epi (asIso (sigmaComparison F (fun _ : X ↦ R))).hom]
      ext x
      change
        Sigma.ι (fun _ : X ↦ F.obj R) x ≫
              sigmaComparison F (fun _ : X ↦ R) ≫
              F.map (Sigma.map' (ConcreteCategory.hom f) (fun _ ↦ 𝟙 R)) ≫
              CategoryTheory.inv (sigmaComparison F (fun _ : Y ↦ R)) =
          Sigma.ι (fun _ : X ↦ F.obj R) x ≫
              sigmaComparison F (fun _ : X ↦ R) ≫
              CategoryTheory.inv (sigmaComparison F (fun _ : X ↦ R)) ≫
              Sigma.map'
                (f := fun _ : Y ↦ F.obj R) (g := fun _ : X ↦ F.obj R)
                (ConcreteCategory.hom f) (fun _ ↦ 𝟙 (F.obj R))
      rw [ι_comp_sigmaComparison_assoc, ← F.map_comp_assoc,
        Sigma.ι_comp_map', Category.id_comp,
        map_ι_comp_inv_sigmaComparison]
      simp)

variable [HasZeroMorphisms C] [HasCokernels C]
variable [HasZeroMorphisms D] [HasCokernels D]

/-- A zero-preserving functor that preserves cokernels commutes with the
cokernel functor on arrows. -/
noncomputable def mapCokerIso (F : Functor C D)
    [F.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F] :
    coker (C := C) ⋙ F ≅ F.mapArrow ⋙ coker (C := D) :=
  NatIso.ofComponents
    (fun f ↦ PreservesCokernel.iso F f.hom)
    (fun {f g} p ↦ by
      exact (preserves_cokernel_iso_comp_cokernel_map
        F f.hom g.hom p.left p.right p.w.symm).symm)

end CategoryTheory.Functor

namespace SSet

open AlgebraicTopology

variable {C : Type u₁} [Category.{v₁} C] [HasCoproducts.{w} C]
  [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{w} D]
  [Preadditive D]

/-- Simplicial chains commute with an additive functor that preserves the
required coproducts. -/
noncomputable def mapChainComplexFunctorIso (F : Functor C D)
    [F.Additive] [PreservesColimitsOfSize.{w, w} F] (R : C) :
    (chainComplexFunctor C).obj R ⋙
        F.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      (chainComplexFunctor D).obj (F.obj R) :=
  eqToIso (by
    dsimp [chainComplexFunctor, Functor.postcompose₂]
    rw [Functor.assoc, map_alternatingFaceMapComplex]
    rfl) ≪≫
    Functor.isoWhiskerRight
      ((SimplicialObject.whiskering (Type w) D).mapIso
        (CategoryTheory.Functor.mapSigmaConstIso F R))
      (alternatingFaceMapComplex D)

end SSet

namespace SSetPair

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  [HasCoproducts.{w} C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasCoproducts.{w} D]

/-- Relative simplicial chains commute with an additive functor that preserves
the required coproducts and cokernels. -/
noncomputable def mapRelativeChainComplexFunctorIso (F : Functor C D)
    [F.Additive] [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape WalkingParallelPair
      (F.mapHomologicalComplex (ComplexShape.down ℕ))] (R : C) :
    (relativeChainComplexFunctor (C := C)).obj R ⋙
        F.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      (relativeChainComplexFunctor (C := D)).obj (F.obj R) :=
  Functor.isoWhiskerLeft
      (SSetPair.forget ⋙ ((SSet.chainComplexFunctor C).obj R).mapArrow)
      (CategoryTheory.Functor.mapCokerIso
        (F.mapHomologicalComplex (ComplexShape.down ℕ))) ≪≫
    eqToIso (by rfl) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft SSetPair.forget
        ((Functor.mapArrowFunctor SSet.{w} (ChainComplex D ℕ)).mapIso
          (SSet.mapChainComplexFunctorIso F R)))
      (coker (C := ChainComplex D ℕ))
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem mapRelativeChainComplexFunctorIso_hom_app_comp_π
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape WalkingParallelPair
      (F.mapHomologicalComplex (ComplexShape.down ℕ))]
    (R : C) (X : SSetPair.{w}) :
    (SSet.mapChainComplexFunctorIso F R).hom.app X.fst ≫
        cokernel.π (((SSet.chainComplexFunctor D).obj (F.obj R)).map X.hom) =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (cokernel.π (((SSet.chainComplexFunctor C).obj R).map X.hom)) ≫
        (mapRelativeChainComplexFunctorIso F R).hom.app X := by
  dsimp [mapRelativeChainComplexFunctorIso,
    CategoryTheory.Functor.mapCokerIso]
  change _ =
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (cokernel.π (((SSet.chainComplexFunctor C).obj R).map X.hom)) ≫
      (PreservesCokernel.iso
        (F.mapHomologicalComplex (ComplexShape.down ℕ))
        (((SSet.chainComplexFunctor C).obj R).map X.hom)).hom ≫ _
  erw [← Category.assoc, PreservesCokernel.π_iso_hom]
  simp only [Category.id_comp]
  erw [cokernel.π_desc]
  rfl

end SSetPair

namespace AlgebraicTopology

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero simplicial homology commutes with an exact functor and the
canonical coproduct description of connected components. -/
theorem ssetHomologyZeroMapFunctorIso_hom_of_exactFunctor
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasCoproducts.{w} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasCoproducts.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{w, w} F]
    [F.PreservesHomology] (A : C) (X : SSet.{w}) :
    let K := X.chainComplex A
    let e := (SSet.mapChainComplexFunctorIso F A).app X
    let c := (HomologicalComplex.mapHomologyFunctorIso 0 F).inv.app K ≫
      HomologicalComplex.homologyMap e.hom 0
    c ≫ (X.homology₀Iso (F.obj A)).hom =
      F.map (X.homology₀Iso A).hom ≫
        (F.mapSigmaConstIso A).hom.app (SSet.π₀ X) := by
  dsimp only
  let K := X.chainComplex A
  let KF : ChainComplex D ℕ :=
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let e : KF ≅ X.chainComplex (F.obj A) :=
    (SSet.mapChainComplexFunctorIso F A).app X
  let η : KF.homology 0 ≅ F.obj (K.homology 0) :=
    (HomologicalComplex.mapHomologyFunctorIso 0 F).app K
  change (η.inv ≫ HomologicalComplex.homologyMap e.hom 0) ≫
      (X.homology₀Iso (F.obj A)).hom =
    F.map (X.homology₀Iso A).hom ≫
      (F.mapSigmaConstIso A).hom.app (SSet.π₀ X)
  have hπ : ((K.sc 0).mapCyclesIso F).hom ≫ F.map (K.homologyπ 0) =
      KF.homologyπ 0 ≫ η.hom := by
    change ((K.sc 0).mapCyclesIso F).hom ≫ F.map ((K.sc 0).homologyπ) =
      ((K.sc 0).map F).homologyπ ≫ ((K.sc 0).mapHomologyIso F).hom
    rw [(K.sc 0).homologyData.left.mapHomologyIso_eq F]
    rw [(K.sc 0).homologyData.left.mapCyclesIso_eq F]
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [Category.assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
    rw [cancel_epi]
    rw [ShortComplex.LeftHomologyData.map_π]
    rw [← F.map_comp, ← F.map_comp,
      ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  let KD := X.chainComplex (F.obj A)
  let eK := K.cycles₀Iso
  let eKF := KF.cycles₀Iso
  let eKD := KD.cycles₀Iso
  have heMap : HomologicalComplex.cyclesMap e.hom 0 ≫ eKD.hom =
      eKF.hom ≫ e.hom.f 0 := by
    have h := HomologicalComplex.cyclesMap_i e.hom 0
    change HomologicalComplex.cyclesMap e.hom 0 ≫ eKD.hom =
      eKF.hom ≫ e.hom.f 0 at h
    exact h
  have he : eKF.inv ≫ HomologicalComplex.cyclesMap e.hom 0 =
      e.hom.f 0 ≫ eKD.inv := by
    apply (cancel_mono eKD.hom).mp
    rw [Category.assoc, heMap]
    simp
  have hMapCycles : ((K.sc 0).mapCyclesIso F).hom ≫ F.map eK.hom =
      eKF.hom := by
    have h := ShortComplex.mapCyclesIso_hom_iCycles (S := K.sc 0) F
    change ((K.sc 0).mapCyclesIso F).hom ≫ F.map eK.hom = eKF.hom at h
    exact h
  have hF : eKF.inv ≫ ((K.sc 0).mapCyclesIso F).hom =
      F.map eK.inv := by
    apply (cancel_mono (F.map eK.hom)).mp
    rw [Category.assoc, hMapCycles]
    change eKF.inv ≫ eKF.hom = F.map eK.inv ≫ F.map eK.hom
    simp only [Iso.inv_hom_id, Iso.inv_hom_id_map]
    change 𝟙 (F.obj (K.X 0)) = 𝟙 (F.obj (K.X 0))
    rfl
  apply (cancel_epi η.hom).mp
  rw [← Category.assoc, η.hom_inv_id_assoc]
  apply (cancel_epi (KF.homologyπ 0)).mp
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc]
  rw [← hπ]
  simp only [Category.assoc]
  apply (cancel_epi eKF.inv).mp
  rw [← Category.assoc, he]
  slice_rhs 1 2 => rw [hF]
  simp only [Category.assoc]
  let s0 := (F.mapSigmaConstIso A).app
    (X.obj (Opposite.op (SimplexCategory.mk 0)))
  let sπ := (F.mapSigmaConstIso A).app (SSet.π₀ X)
  have he0 : e.hom.f 0 = s0.hom := by
    simp [e, s0, SSet.mapChainComplexFunctorIso]
  rw [he0]
  apply (cancel_epi s0.inv).mp
  apply Sigma.hom_ext
  intro x
  have hDinv : X.ιChainComplex (R := F.obj A) x ≫ eKD.inv =
      KD.liftCycles (X.ιChainComplex (R := F.obj A) x) 0 (by simp) (by simp) := by
    have h := HomologicalComplex.liftCycles_i KD
      (X.ιChainComplex (R := F.obj A) x) 0 (by simp) (by simp)
    change KD.liftCycles (X.ιChainComplex (R := F.obj A) x) 0
      (by simp) (by simp) ≫ eKD.hom = X.ιChainComplex (R := F.obj A) x at h
    calc
      X.ιChainComplex (R := F.obj A) x ≫ eKD.inv =
          (KD.liftCycles (X.ιChainComplex (R := F.obj A) x) 0
            (by simp) (by simp) ≫ eKD.hom) ≫ eKD.inv := by rw [h]
      _ = _ := by simp
  have hKinv : X.ιChainComplex (R := A) x ≫ eK.inv =
      K.liftCycles (X.ιChainComplex (R := A) x) 0 (by simp) (by simp) := by
    have h := HomologicalComplex.liftCycles_i K
      (X.ιChainComplex (R := A) x) 0 (by simp) (by simp)
    change K.liftCycles (X.ιChainComplex (R := A) x) 0
      (by simp) (by simp) ≫ eK.hom = X.ιChainComplex (R := A) x at h
    calc
      X.ιChainComplex (R := A) x ≫ eK.inv =
          (K.liftCycles (X.ιChainComplex (R := A) x) 0
            (by simp) (by simp) ≫ eK.hom) ≫ eK.inv := by rw [h]
      _ = _ := by simp
  have hι : Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk 0)) =>
        F.obj A) x ≫ s0.inv =
      F.map (X.ιChainComplex (R := A) x) := by
    change Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk 0)) =>
        F.obj A) x ≫ sigmaComparison F (fun _ => A) =
      F.map (Sigma.ι (fun _ => A) x)
    rw [Limits.ι_comp_sigmaComparison]
  have hclass : X.ιChainComplex (R := A) x ≫ eK.inv ≫
      K.homologyπ 0 ≫ (X.homology₀Iso A).hom =
        Sigma.ι (fun _ : SSet.π₀ X => A) (SSet.π₀.mk x) := by
    slice_lhs 1 2 => rw [hKinv]
    simpa only [K, Category.assoc] using
      (SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X A x)
  calc
    Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk 0)) => F.obj A) x ≫
          s0.inv ≫ s0.hom ≫ eKD.inv ≫ KD.homologyπ 0 ≫
            (X.homology₀Iso (F.obj A)).hom =
        Sigma.ι (fun _ : SSet.π₀ X => F.obj A) (SSet.π₀.mk x) := by
      rw [s0.inv_hom_id_assoc]
      change X.ιChainComplex (R := F.obj A) x ≫ eKD.inv ≫
          KD.homologyπ 0 ≫ (X.homology₀Iso (F.obj A)).hom = _
      slice_lhs 1 2 => rw [hDinv]
      simpa only [KD, Category.assoc] using
        (SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X (F.obj A) x)
    _ = F.map (Sigma.ι (fun _ : SSet.π₀ X => A) (SSet.π₀.mk x)) ≫ sπ.hom := by
      symm
      exact map_ι_comp_inv_sigmaComparison F (fun _ : SSet.π₀ X => A)
        (SSet.π₀.mk x)
    _ = Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk 0)) => F.obj A) x ≫
          s0.inv ≫ F.map eK.inv ≫ F.map (K.homologyπ 0) ≫
            F.map (X.homology₀Iso A).hom ≫ sπ.hom := by
      slice_rhs 1 2 => rw [hι]
      simp only [← F.map_comp, Category.assoc]
      rw [hclass]

end AlgebraicTopology
