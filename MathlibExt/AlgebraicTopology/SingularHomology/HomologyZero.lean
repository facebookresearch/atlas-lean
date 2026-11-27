/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import MathlibExt.Topology.Category.TopCat.ZerothHomotopy

/-!
# Naturality of the degree-zero augmentation and of the canonical H₀ identification

This module proves naturality of the canonical augmentation from degree-zero
homology to the coefficient object, and functoriality/naturality of the
canonical H₀ identification with a coproduct of copies of the coefficient
object indexed by connected components.

For a simplicial map `f : X ⟶ Y`, the induced map on `H₀` commutes with the
augmentations `H₀ → R`. The proof first cancels the epimorphism `homologyπ`
from cycles to homology, uses naturality of `homologyπ` to reduce to a statement
about the induced map on cycles, and then checks equality on the coproduct
generators given by vertices. Each generator evaluation is the identity by the
existing vertex lemma.

The singular version follows by transport through the singular simplicial set
functor: singular homology and its augmentation are defined as the simplicial
ones of `toSSet`, so the simplicial naturality applied to `toSSet.map f`
gives the topological statement.

We reuse the functorial action of `ZerothHomotopy` on continuous maps and its
compatibility with `SSet.π₀` via `zerothHomotopyEquiv` from the extracted
`MathlibExt.Topology.Category.TopCat.ZerothHomotopy` core, and add the
coproduct functor and naturality of the canonical H₀ isomorphisms
`X.homology₀Iso R` and `X.singularHomology₀Iso R`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits AlgebraicTopology Simplicial

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]

namespace TopCat

variable (R : C)

/-- The coproduct functor `X ↦ ∐_{ZerothHomotopy X} R`. -/
noncomputable def zerothHomotopyCoproductFunctor : TopCat.{w} ⥤ C :=
  zerothHomotopyFunctor ⋙ sigmaConst.obj R

@[simp]
theorem zerothHomotopyCoproductFunctor_obj (X : TopCat.{w}) :
    (zerothHomotopyCoproductFunctor (R := R)).obj X = ∐ (fun _ : ZerothHomotopy X => R) :=
  rfl

@[simp]
theorem zerothHomotopyCoproductFunctor_map {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (zerothHomotopyCoproductFunctor (R := R)).map f =
      (sigmaConst.obj R).map (↾(zerothHomotopyMap f)) :=
  rfl

end TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

namespace SSet

variable {X Y : SSet.{w}} (f : X ⟶ Y) (R : C)

@[reassoc (attr := simp)]
theorem homologyMap_comp_homology₀ε :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  have h_epi : Epi ((X.chainComplex R).homologyπ 0) := inferInstance
  apply (cancel_epi ((X.chainComplex R).homologyπ 0)).mp
  have hπ_nat :
      (X.chainComplex R).homologyπ 0 ≫ SSet.homologyMap f R 0 =
        HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
          (Y.chainComplex R).homologyπ 0 :=
    HomologicalComplex.homologyπ_naturality (SSet.chainComplexMap f R) 0
  suffices h_cyc :
      HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
        (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R =
        (X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R by
    calc (X.chainComplex R).homologyπ 0 ≫ SSet.homologyMap f R 0 ≫ Y.homology₀ε R
        = (HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
            (Y.chainComplex R).homologyπ 0) ≫ Y.homology₀ε R := by
          rw [← Category.assoc, hπ_nat]
      _ = HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
            (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R := by
          rw [Category.assoc]
      _ = (X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R := h_cyc
  let eX : (X.chainComplex R).cycles 0 ≅ (X.chainComplex R).X 0 :=
    (X.chainComplex R).cycles₀Iso
  let eY : (Y.chainComplex R).cycles 0 ≅ (Y.chainComplex R).X 0 :=
    (Y.chainComplex R).cycles₀Iso
  have h_cyc_eq :
      HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
        (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R =
        (X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R := by
    have h_inv_eq :
        eX.inv ≫
          (HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
            (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R) =
        eX.inv ≫ ((X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R) := by
      apply SSet.chainComplex_hom_ext
      intro x
      have h_X_ι_lift :
          (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
            eX.hom = X.ιChainComplex x :=
        HomologicalComplex.liftCycles_i _ _ 0 (by simp) (by simp)
      have h_X_inv :
          X.ιChainComplex (R := R) x ≫ eX.inv =
            (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
        calc X.ιChainComplex x ≫ eX.inv
            = ((X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
                eX.hom) ≫ eX.inv := by rw [h_X_ι_lift]
          _ = (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
                (eX.hom ≫ eX.inv) := by rw [Category.assoc]
          _ = _ := by rw [eX.hom_inv_id, Category.comp_id]
      have h_chain_eq :
          X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0 =
            Y.ιChainComplex (f.app _ x) :=
        SSet.ι_chainComplexMap_f X Y f R x
      have h_Y1 :
          (Y.chainComplex R).liftCycles
              (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) ≫
            eY.hom =
            X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0 :=
        HomologicalComplex.liftCycles_i _ _ 0 (by simp) (by simp)
      have h_Y2 :
          (Y.chainComplex R).liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) ≫
            eY.hom =
            Y.ιChainComplex (f.app _ x) :=
        HomologicalComplex.liftCycles_i _ _ 0 (by simp) (by simp)
      have h_Y12 :
          (Y.chainComplex R).liftCycles
                (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) ≫
              eY.hom =
            (Y.chainComplex R).liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) ≫
              eY.hom := by
        rw [h_Y1, h_Y2, h_chain_eq]
      have h_lift_Y_eq :
          (Y.chainComplex R).liftCycles
              (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) =
            (Y.chainComplex R).liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
        exact (cancel_mono eY.hom).mp h_Y12
      have h_left :
          X.ιChainComplex x ≫ eX.inv ≫
            (HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
              (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R) = 𝟙 R := by
        calc X.ιChainComplex x ≫ eX.inv ≫
              (HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
                (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R)
            = (X.ιChainComplex x ≫ eX.inv ≫
                HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0) ≫
                (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R := by
              simp only [Category.assoc]
          _ = ((X.ιChainComplex x ≫ eX.inv) ≫
                HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0) ≫
                (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R := by
              simp only [← Category.assoc]
          _ = ((X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
                HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0) ≫
                (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R := by
              rw [h_X_inv]
          _ = (Y.chainComplex R).liftCycles
                (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) ≫
                (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R := by
              rw [HomologicalComplex.liftCycles_comp_cyclesMap]
          _ = (Y.chainComplex R).liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) ≫
                (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R := by
              rw [h_lift_Y_eq]
          _ = 𝟙 R := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε Y R (f.app _ x)
      have h_right :
          X.ιChainComplex x ≫ eX.inv ≫
            ((X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R) = 𝟙 R := by
        calc X.ιChainComplex x ≫ eX.inv ≫
              ((X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R)
            = (X.ιChainComplex x ≫ eX.inv ≫ (X.chainComplex R).homologyπ 0) ≫
                X.homology₀ε R := by simp only [Category.assoc]
          _ = ((X.ιChainComplex x ≫ eX.inv) ≫ (X.chainComplex R).homologyπ 0) ≫
                X.homology₀ε R := by simp only [← Category.assoc]
          _ = ((X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
                (X.chainComplex R).homologyπ 0) ≫ X.homology₀ε R := by rw [h_X_inv]
          _ = (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
                (X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R := by
              simp only [Category.assoc]
          _ = 𝟙 R := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε X R x
      rw [h_left, h_right]
    calc HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
          (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R
        = (eX.hom ≫ eX.inv) ≫
            (HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
              (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R) := by
          rw [eX.hom_inv_id, Category.id_comp]
      _ = eX.hom ≫
            (eX.inv ≫
              (HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
                (Y.chainComplex R).homologyπ 0 ≫ Y.homology₀ε R)) := by
          rw [Category.assoc]
      _ = eX.hom ≫ (eX.inv ≫ ((X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R)) := by
          rw [h_inv_eq]
      _ = (eX.hom ≫ eX.inv) ≫ ((X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R) := by
          rw [← Category.assoc]
      _ = (X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R := by
          rw [eX.hom_inv_id, Category.id_comp]
  exact h_cyc_eq

private theorem homologyMap_comp_homology₀Iso_hom_aux :
    SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom =
      (X.homology₀Iso R).hom ≫ Sigma.map' (SSet.mapπ₀ f) (fun _ => 𝟙 R) := by
  apply (cancel_epi ((X.chainComplex R).homologyπ 0)).mp
  have hπ_nat := HomologicalComplex.homologyπ_naturality (SSet.chainComplexMap f R) 0
  calc (X.chainComplex R).homologyπ 0 ≫ SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom
      = (HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
          (Y.chainComplex R).homologyπ 0) ≫ (Y.homology₀Iso R).hom := by
        rw [← Category.assoc, hπ_nat]
    _ = HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0 ≫
          (Y.chainComplex R).homologyπ 0 ≫ (Y.homology₀Iso R).hom := by
        rw [Category.assoc]
    _ = (X.chainComplex R).homologyπ 0 ≫ (X.homology₀Iso R).hom ≫
          Sigma.map' (SSet.mapπ₀ f) (fun _ => 𝟙 R) := by
        let eX : (X.chainComplex R).cycles 0 ≅ (X.chainComplex R).X 0 :=
          (X.chainComplex R).cycles₀Iso
        let eY : (Y.chainComplex R).cycles 0 ≅ (Y.chainComplex R).X 0 :=
          (Y.chainComplex R).cycles₀Iso
        apply (cancel_epi eX.inv).mp
        apply SSet.chainComplex_hom_ext
        intro x
        have h_X_inv :
            X.ιChainComplex (R := R) x ≫ eX.inv =
              (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
          have h :
              (X.chainComplex R).liftCycles
                    (X.ιChainComplex x) 0 (by simp) (by simp) ≫ eX.hom =
                X.ιChainComplex x :=
            HomologicalComplex.liftCycles_i _ _ 0 (by simp) (by simp)
          calc X.ιChainComplex x ≫ eX.inv
              = ((X.chainComplex R).liftCycles _ 0 (by simp) (by simp) ≫ eX.hom) ≫ eX.inv := by
                rw [h]
            _ = _ ≫ (eX.hom ≫ eX.inv) := by rw [Category.assoc]
            _ = _ := by rw [eX.hom_inv_id, Category.comp_id]
        have h_lift_Y_eq :
            (Y.chainComplex R).liftCycles
                (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0)
                  0 (by simp) (by simp) =
              (Y.chainComplex R).liftCycles
                (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
          have h1 :
              (Y.chainComplex R).liftCycles
                    (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0)
                      0 (by simp) (by simp) ≫ eY.hom =
                X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0 :=
            HomologicalComplex.liftCycles_i _ _ 0 (by simp) (by simp)
          have h2 :
              (Y.chainComplex R).liftCycles
                    (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) ≫ eY.hom =
                Y.ιChainComplex (f.app _ x) :=
            HomologicalComplex.liftCycles_i _ _ 0 (by simp) (by simp)
          have :
              (Y.chainComplex R).liftCycles
                    (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0)
                      0 (by simp) (by simp) ≫ eY.hom =
                (Y.chainComplex R).liftCycles
                    (Y.ιChainComplex (f.app _ x))
                      0 (by simp) (by simp) ≫ eY.hom := by
            rw [h1, h2, SSet.ι_chainComplexMap_f]
          exact (cancel_mono eY.hom).mp this
        simp only [← Category.assoc, h_X_inv]
        rw [HomologicalComplex.liftCycles_comp_cyclesMap]
        rw [h_lift_Y_eq]
        simp only [Category.assoc]
        rw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom Y R (f.app _ x)]
        rw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom_assoc X R x]
        simp only [Sigma.ι_comp_map', Category.id_comp, SSet.mapπ₀_mk]

@[reassoc]
theorem homologyMap_comp_homology₀Iso_hom :
    SSet.homologyMap f R 0 ≫ (Y.homology₀Iso R).hom =
      (X.homology₀Iso R).hom ≫ (sigmaConst.obj R).map (SSet.π₀Functor.map f) := by
  have h := homologyMap_comp_homology₀Iso_hom_aux f R
  convert h
  rfl

/-- The canonical degree-zero homology isomorphism is natural in the coefficient object. -/
@[reassoc]
theorem homology₀Iso_hom_naturality_coefficient
    (X : SSet.{w}) {R S : C} (a : R ⟶ S) :
    HomologicalComplex.homologyMap (((SSet.chainComplexFunctor C).map a).app X) 0 ≫
        (X.homology₀Iso S).hom =
      (X.homology₀Iso R).hom ≫ Limits.Sigma.map (fun _ : SSet.π₀ X => a) := by
  let φ := ((SSet.chainComplexFunctor C).map a).app X
  apply (cancel_epi ((X.chainComplex R).homologyπ 0)).mp
  have hπ_nat := HomologicalComplex.homologyπ_naturality φ 0
  rw [← Category.assoc, hπ_nat, Category.assoc]
  let eR : (X.chainComplex R).cycles 0 ≅ (X.chainComplex R).X 0 :=
    (X.chainComplex R).cycles₀Iso
  let eS : (X.chainComplex S).cycles 0 ≅ (X.chainComplex S).X 0 :=
    (X.chainComplex S).cycles₀Iso
  apply (cancel_epi eR.inv).mp
  apply SSet.chainComplex_hom_ext
  intro x
  have h_R_inv :
      X.ιChainComplex (R := R) x ≫ eR.inv =
        (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    have h :
        (X.chainComplex R).liftCycles
              (X.ιChainComplex x) 0 (by simp) (by simp) ≫ eR.hom =
          X.ιChainComplex x :=
      HomologicalComplex.liftCycles_i _ _ 0 (by simp) (by simp)
    calc
      X.ιChainComplex x ≫ eR.inv =
          ((X.chainComplex R).liftCycles _ 0 (by simp) (by simp) ≫ eR.hom) ≫ eR.inv := by
            rw [h]
      _ = _ ≫ (eR.hom ≫ eR.inv) := by rw [Category.assoc]
      _ = _ := by rw [eR.hom_inv_id, Category.comp_id]
  simp only [← Category.assoc, h_R_inv]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap]
  have hcoeff :
      X.ιChainComplex (R := R) x ≫ φ.f 0 =
        a ≫ X.ιChainComplex (R := S) x := by
    change Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk 0)) => (R : C)) x ≫
        Limits.Sigma.map (fun _ : X.obj (Opposite.op (SimplexCategory.mk 0)) => a) =
      a ≫ Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk 0)) => (S : C)) x
    rw [Limits.Sigma.ι_map]
  have h_lift_S_eq :
      (X.chainComplex S).liftCycles
          (X.ιChainComplex (R := R) x ≫ φ.f 0) 0 (by simp) (by simp) =
        a ≫ (X.chainComplex S).liftCycles
          (X.ιChainComplex (R := S) x) 0 (by simp) (by simp) := by
    apply (cancel_mono eS.hom).mp
    change (X.chainComplex S).liftCycles
          (X.ιChainComplex (R := R) x ≫ φ.f 0) 0 (by simp) (by simp) ≫
          (X.chainComplex S).iCycles 0 =
        (a ≫ (X.chainComplex S).liftCycles
          (X.ιChainComplex (R := S) x) 0 (by simp) (by simp)) ≫
          (X.chainComplex S).iCycles 0
    rw [HomologicalComplex.liftCycles_i]
    rw [Category.assoc, HomologicalComplex.liftCycles_i]
    exact hcoeff
  rw [h_lift_S_eq]
  simp only [Category.assoc]
  rw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom]
  rw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom_assoc]
  rw [Limits.Sigma.ι_map]

end SSet

namespace TopCat

variable {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C)

@[reassoc (attr := simp)]
theorem singularHomologyMap_comp_singularHomology₀ε :
    ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map f ≫
      Y.singularHomology₀ε R = X.singularHomology₀ε R := by
  have h : SSet.homologyMap (TopCat.toSSet.map f) R 0 ≫
      (TopCat.toSSet.obj Y).homology₀ε R =
      (TopCat.toSSet.obj X).homology₀ε R :=
    SSet.homologyMap_comp_homology₀ε (TopCat.toSSet.map f) R
  convert h <;> rfl

/-- A map between path-connected spaces induces an isomorphism on singular
homology in degree zero. -/
theorem isIso_singularHomologyMap_zero_of_pathConnected
    [PathConnectedSpace X] [PathConnectedSpace Y] :
    IsIso (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map f) := by
  let hY : IsIso (Y.singularHomology₀ε R) := by infer_instance
  let hX : IsIso (X.singularHomology₀ε R) := by infer_instance
  exact @IsIso.of_isIso_fac_right C _ _ _ _ _ _ _ hY hX
    (singularHomologyMap_comp_singularHomology₀ε f R)

private theorem singularHomologyMap_comp_singularHomology₀Iso_hom_aux :
    SSet.homologyMap (TopCat.toSSet.map f) R 0 ≫
      (((TopCat.toSSet.obj Y).homology₀Iso R).hom ≫
        Sigma.map' (C := C)
          (f := fun _ : ZerothHomotopy Y => R)
          (g := fun _ : SSet.π₀ (TopCat.toSSet.obj Y) => R)
          (TopCat.zerothHomotopyEquiv (X := Y)).symm (fun _ => 𝟙 R)) =
      (((TopCat.toSSet.obj X).homology₀Iso R).hom ≫
        Sigma.map' (C := C)
          (f := fun _ : ZerothHomotopy X => R)
          (g := fun _ : SSet.π₀ (TopCat.toSSet.obj X) => R)
          (TopCat.zerothHomotopyEquiv (X := X)).symm (fun _ => 𝟙 R)) ≫
        Sigma.map' (C := C)
          (f := fun _ : ZerothHomotopy Y => R)
          (g := fun _ : ZerothHomotopy X => R)
          (TopCat.zerothHomotopyMap f) (fun _ => 𝟙 R) := by
  have hS := SSet.homologyMap_comp_homology₀Iso_hom_aux (TopCat.toSSet.map f) R
  have h_square :
      Sigma.map' (C := C)
        (f := fun _ : SSet.π₀ (TopCat.toSSet.obj Y) => R)
        (g := fun _ : SSet.π₀ (TopCat.toSSet.obj X) => R)
        (SSet.mapπ₀ (TopCat.toSSet.map f)) (fun _ => 𝟙 R) ≫
      Sigma.map' (C := C)
        (f := fun _ : ZerothHomotopy Y => R)
        (g := fun _ : SSet.π₀ (TopCat.toSSet.obj Y) => R)
        (TopCat.zerothHomotopyEquiv (X := Y)).symm (fun _ => 𝟙 R) =
      Sigma.map' (C := C)
        (f := fun _ : ZerothHomotopy X => R)
        (g := fun _ : SSet.π₀ (TopCat.toSSet.obj X) => R)
        (TopCat.zerothHomotopyEquiv (X := X)).symm (fun _ => 𝟙 R) ≫
      Sigma.map' (C := C)
        (f := fun _ : ZerothHomotopy Y => R)
        (g := fun _ : ZerothHomotopy X => R)
        (TopCat.zerothHomotopyMap f) (fun _ => 𝟙 R) := by
    apply Sigma.hom_ext
    intro q
    simp only [← Category.assoc, Sigma.ι_comp_map', Category.id_comp]
    rw [TopCat.zerothHomotopyEquiv_symm_naturality f q]
  rw [← Category.assoc, hS, Category.assoc, h_square, ← Category.assoc]

@[reassoc]
theorem singularHomologyMap_comp_singularHomology₀Iso_hom :
    ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map f ≫
      (Y.singularHomology₀Iso R).hom =
      (X.singularHomology₀Iso R).hom ≫
        (zerothHomotopyCoproductFunctor R).map f := by
  have h := singularHomologyMap_comp_singularHomology₀Iso_hom_aux f R
  convert h; rfl

/-- The canonical singular degree-zero homology isomorphism is natural in the coefficient object. -/
@[reassoc]
theorem singularHomology₀Iso_hom_naturality_coefficient
    (X : TopCat.{w}) {R S : C} (a : R ⟶ S) :
    ((AlgebraicTopology.singularHomologyFunctor C 0).map a).app X ≫
        (X.singularHomology₀Iso S).hom =
      (X.singularHomology₀Iso R).hom ≫
        Limits.Sigma.map (fun _ : ZerothHomotopy X => a) := by
  change HomologicalComplex.homologyMap
      (((SSet.chainComplexFunctor C).map a).app (TopCat.toSSet.obj X)) 0 ≫
      (((TopCat.toSSet.obj X).homology₀Iso S).hom ≫
        Sigma.map' (TopCat.zerothHomotopyEquiv (X := X)).symm (fun _ => 𝟙 S)) =
    (((TopCat.toSSet.obj X).homology₀Iso R).hom ≫
        Sigma.map' (TopCat.zerothHomotopyEquiv (X := X)).symm (fun _ => 𝟙 R)) ≫
      Limits.Sigma.map (fun _ : ZerothHomotopy X => a)
  rw [← Category.assoc, SSet.homology₀Iso_hom_naturality_coefficient,
    Category.assoc]
  have h_square :
      Limits.Sigma.map (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => a) ≫
          Sigma.map' (TopCat.zerothHomotopyEquiv (X := X)).symm (fun _ => 𝟙 S) =
        Sigma.map' (TopCat.zerothHomotopyEquiv (X := X)).symm (fun _ => 𝟙 R) ≫
          Limits.Sigma.map (fun _ : ZerothHomotopy X => a) := by
    apply Sigma.hom_ext
    intro q
    simp
  simpa only [Category.assoc] using congrArg
    (fun k => ((TopCat.toSSet.obj X).homology₀Iso R).hom ≫ k) h_square

/-- The singular degree-zero augmentation is natural in the coefficient object. -/
@[reassoc (attr := simp)]
theorem singularHomology₀ε_naturality_coefficient
    (X : TopCat.{w}) {R S : C} (a : R ⟶ S) :
    ((AlgebraicTopology.singularHomologyFunctor C 0).map a).app X ≫
        X.singularHomology₀ε S =
      X.singularHomology₀ε R ≫ a := by
  have h_fold :
      Limits.Sigma.map (fun _ : ZerothHomotopy X => a) ≫
          Sigma.desc (fun _ => 𝟙 S) =
        Sigma.desc (fun _ => 𝟙 R) ≫ a := by
    apply Sigma.hom_ext
    intro q
    simp
  calc
    ((AlgebraicTopology.singularHomologyFunctor C 0).map a).app X ≫
          X.singularHomology₀ε S =
        ((AlgebraicTopology.singularHomologyFunctor C 0).map a).app X ≫
          (X.singularHomology₀Iso S).hom ≫ Sigma.desc (fun _ => 𝟙 S) := by
            rw [X.singularHomology₀Iso_sigma_desc_id]
    _ = (((AlgebraicTopology.singularHomologyFunctor C 0).map a).app X ≫
          (X.singularHomology₀Iso S).hom) ≫ Sigma.desc (fun _ => 𝟙 S) := by
            rw [Category.assoc]
    _ = ((X.singularHomology₀Iso R).hom ≫
          Limits.Sigma.map (fun _ : ZerothHomotopy X => a)) ≫
          Sigma.desc (fun _ => 𝟙 S) := by
            rw [singularHomology₀Iso_hom_naturality_coefficient]
    _ = (X.singularHomology₀Iso R).hom ≫
          (Limits.Sigma.map (fun _ : ZerothHomotopy X => a) ≫
            Sigma.desc (fun _ => 𝟙 S)) := by
            rw [Category.assoc]
    _ = (X.singularHomology₀Iso R).hom ≫
          (Sigma.desc (fun _ => 𝟙 R) ≫ a) := by rw [h_fold]
    _ = ((X.singularHomology₀Iso R).hom ≫ Sigma.desc (fun _ => 𝟙 R)) ≫ a := by
          rw [← Category.assoc]
    _ = X.singularHomology₀ε R ≫ a := by
          rw [X.singularHomology₀Iso_sigma_desc_id]

/-- Packages the objectwise canonical singular degree-zero homology isomorphisms
into a natural isomorphism from the degree-zero singular-homology functor at
coefficient `R` to the zeroth-homotopy-indexed coproduct functor, natural in
the space variable; coefficient naturality is supplied by the neighboring
theorem rather than this `NatIso`. -/
noncomputable def singularHomology₀NatIso (R : C) :
    (AlgebraicTopology.singularHomologyFunctor C 0).obj R ≅
      zerothHomotopyCoproductFunctor R :=
  NatIso.ofComponents (fun X => X.singularHomology₀Iso R)
    (fun f => singularHomologyMap_comp_singularHomology₀Iso_hom f R)

@[simp]
theorem singularHomology₀NatIso_app (X : TopCat.{w}) (R : C) :
    (singularHomology₀NatIso (R := R)).app X = X.singularHomology₀Iso R :=
  rfl

end TopCat

namespace AlgebraicTopology

section PointHomologyClass

variable (R : C)

/-- The degree-zero point class. -/
noncomputable def pointHomologyClass (X : TopCat.{w}) (x : X) :
    R ⟶ ((singularHomologyFunctor C 0).obj R).obj X :=
  Sigma.ι (fun _ : ZerothHomotopy X => R) (ZerothHomotopy.mk x) ≫
    (X.singularHomology₀Iso R).inv

/-- Point classes are natural: the class of a point pushes forward to
the class of its image. -/
theorem pointHomologyClass_naturality (X Y : TopCat.{w}) (f : X ⟶ Y) (x : X) :
    pointHomologyClass R X x ≫ ((singularHomologyFunctor C 0).obj R).map f =
      pointHomologyClass R Y (f x) := by
  have key : (X.singularHomology₀Iso R).inv ≫
        (((singularHomologyFunctor C 0).obj R).map f ≫
          (Y.singularHomology₀Iso R).hom) =
      (TopCat.zerothHomotopyCoproductFunctor R).map f := by
    rw [TopCat.singularHomologyMap_comp_singularHomology₀Iso_hom]
    exact Iso.inv_hom_id_assoc _ _
  apply (cancel_mono (Y.singularHomology₀Iso R).hom).mp
  unfold pointHomologyClass
  simp only [Category.assoc]
  rw [key, Iso.inv_hom_id, Category.comp_id,
    TopCat.zerothHomotopyCoproductFunctor_map]
  simp only [sigmaConst_obj_map, Sigma.ι_comp_map', Category.id_comp]
  congr 1

end PointHomologyClass

end AlgebraicTopology
