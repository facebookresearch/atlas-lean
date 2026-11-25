/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.AdjunctionBarRelativeProjectivity
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.Abel

/-!
# Restricted contraction of the adjunction Bar

The extra degeneracy of the restricted free Bar gives a homotopy equivalence from its alternating
chain complex to the coefficient object concentrated in degree zero. Its augmentation is the
restricted counit and its degree-zero section is the unit. The homotopy components determine
positive splitting operators with the stated signs. An additive right adjoint identifies the
restriction of the original alternating complex with this complex.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe uC vC uD vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {U : D ⥤ C}

/-- The restricted augmented Bar, including its counit endpoint. -/
abbrev restrictedFreeBarAugmented (adj : F ⊣ U) (M : D) : SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj D C U).obj (adj.freeBarAugmented M)

/-- The restricted extra degeneracy has the unit as its zero section. -/
theorem freeBarExtra_s'_eq_unit (adj : F ⊣ U) (M : D) :
    (adj.freeBarExtra M).s' = adj.unit.app (U.obj M) := by
  let X : C := U.obj (F.obj (U.obj M))
  let v : X ⟶ X := (adj.freeBarForgetIso M).inv.app (Opposite.op (SimplexCategory.mk 0))
  have hv : v = 𝟙 X := by
    have h := Iso.inv_hom_id_app (adj.freeBarForgetIso M) (Opposite.op (SimplexCategory.mk 0))
    rw [freeBarForgetIso_hom_app_mk] at h
    change v ≫ 𝟙 X = 𝟙 X at h
    exact (Category.comp_id v).symm.trans h
  change (𝟙 (U.obj M)) ≫ (Monad.resolutionExtra ((Monad.comparison adj).obj M)).s' ≫ v = _
  rw [Category.id_comp, Monad.resolutionExtra_s']
  change adj.unit.app (U.obj M) ≫ v = adj.unit.app (U.obj M)
  let u : U.obj M ⟶ X := adj.unit.app (U.obj M)
  change u ≫ v = u
  exact (congrArg (fun a : X ⟶ X => u ≫ a) hv).trans (Category.comp_id u)

section Contraction

variable [Preadditive C] [HasZeroObject C]

/-- The alternating-chain complex of the restricted Bar. -/
abbrev restrictedFreeBarChain (adj : F ⊣ U) (M : D) : ChainComplex C ℕ :=
  (alternatingFaceMapComplex C).obj (adj.freeBar M ⋙ U)

/-- The extra-degeneracy operator on the restricted chain objects. -/
abbrev restrictedFreeBarSplitOperator (adj : F ⊣ U) (M : D) (n : ℕ) :
    (restrictedFreeBarChain adj M).X n ⟶ (restrictedFreeBarChain adj M).X (n + 1) :=
  (adj.freeBarExtra M).s n

/-- Extra degeneracy constructs the restricted augmentation equivalence. -/
def restrictedFreeBarHomotopyEquiv (adj : F ⊣ U) (M : D) :
    HomotopyEquiv (restrictedFreeBarChain adj M) ((ChainComplex.single₀ C).obj (U.obj M)) :=
  (adj.freeBarExtra M).homotopyEquiv

/-- Its forward map is the augmentation of the whole U-whiskered object. -/
theorem restrictedFreeBarHomotopyEquiv_hom (adj : F ⊣ U) (M : D) :
    (adj.restrictedFreeBarHomotopyEquiv M).hom =
      AlternatingFaceMapComplex.ε.app (adj.restrictedFreeBarAugmented M) := rfl

/-- Degree zero retains the counit after `U`. -/
theorem restrictedFreeBarHomotopyEquiv_hom_zero (adj : F ⊣ U) (M : D) :
    (adj.restrictedFreeBarHomotopyEquiv M).hom.f 0 = U.map (adj.counit.app M) := by
  rw [restrictedFreeBarHomotopyEquiv_hom, AlternatingFaceMapComplex.ε_app_f_zero,
    SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk, freeBarAugmented_hom_zero]
  rfl

/-- The augmentation has zero components in every positive chain degree. -/
theorem restrictedFreeBarHomotopyEquiv_hom_succ (adj : F ⊣ U) (M : D) (n : ℕ) :
    (adj.restrictedFreeBarHomotopyEquiv M).hom.f (n + 1) = 0 := rfl

/-- The backward map retains the unit at the point in degree zero. -/
theorem restrictedFreeBarHomotopyEquiv_inv_zero (adj : F ⊣ U) (M : D) :
    (adj.restrictedFreeBarHomotopyEquiv M).inv.f 0 = adj.unit.app (U.obj M) := by
  let t : U.obj M ⟶ (restrictedFreeBarChain adj M).X 0 := (adj.freeBarExtra M).s'
  have ht : t = adj.unit.app (U.obj M) := freeBarExtra_s'_eq_unit adj M
  change ((ChainComplex.fromSingle₀Equiv (restrictedFreeBarChain adj M) (U.obj M)).symm t).f 0 = _
  exact ((ChainComplex.fromSingle₀Equiv (restrictedFreeBarChain adj M) (U.obj M)).apply_symm_apply t).trans ht

/-- The homotopy has the negative extra-degeneracy component. -/
theorem restrictedFreeBarHomotopyEquiv_homotopy_succ (adj : F ⊣ U) (M : D) (n : ℕ) :
    (adj.restrictedFreeBarHomotopyEquiv M).homotopyHomInvId.hom n (n + 1) =
      -(adj.restrictedFreeBarSplitOperator M n) := by
  simp only [restrictedFreeBarHomotopyEquiv,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, Pi.single_eq_same]
  rfl

omit [Preadditive C] [HasZeroObject C] in
/-- The unit is a section of the mapped counit, as the augmentation split requires. -/
theorem restrictedFreeBar_unit_counit (adj : F ⊣ U) (M : D) :
    adj.unit.app (U.obj M) ≫ U.map (adj.counit.app M) = 𝟙 _ :=
  adj.right_triangle_components M

/-- Degree-zero splitness uses the positive extra-degeneracy operator and augmentation. -/
theorem restrictedFreeBar_split_zero (adj : F ⊣ U) (M : D) :
    let a : (restrictedFreeBarChain adj M).X 0 ⟶ U.obj M := U.map (adj.counit.app M)
    let t : U.obj M ⟶ (restrictedFreeBarChain adj M).X 0 := adj.unit.app (U.obj M)
    a ≫ t + adj.restrictedFreeBarSplitOperator M 0 ≫ (restrictedFreeBarChain adj M).d 1 0 = 𝟙 _ := by
  let K := restrictedFreeBarChain adj M
  let a : K.X 0 ⟶ U.obj M := U.map (adj.counit.app M)
  let t : U.obj M ⟶ K.X 0 := adj.unit.app (U.obj M)
  have h := (adj.restrictedFreeBarHomotopyEquiv M).homotopyHomInvId.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    restrictedFreeBarHomotopyEquiv_hom_zero, restrictedFreeBarHomotopyEquiv_inv_zero,
    restrictedFreeBarHomotopyEquiv_homotopy_succ, zero_add] at h
  change a ≫ t = (-adj.restrictedFreeBarSplitOperator M 0) ≫ K.d 1 0 + 𝟙 (K.X 0) at h
  rw [Preadditive.neg_comp] at h
  have hh := congrArg
    (fun z : K.X 0 ⟶ K.X 0 => z + adj.restrictedFreeBarSplitOperator M 0 ≫ K.d 1 0) h
  abel_nf at hh ⊢
  exact hh

/-- The homotopy gives the splitting equation in every positive degree. -/
theorem restrictedFreeBar_split_succ (adj : F ⊣ U) (M : D) (n : ℕ) :
    adj.restrictedFreeBarSplitOperator M (n + 1) ≫ (restrictedFreeBarChain adj M).d (n + 2) (n + 1) +
      (restrictedFreeBarChain adj M).d (n + 1) n ≫ adj.restrictedFreeBarSplitOperator M n = 𝟙 _ := by
  let K := restrictedFreeBarChain adj M
  have h := (adj.restrictedFreeBarHomotopyEquiv M).homotopyHomInvId.comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    restrictedFreeBarHomotopyEquiv_hom_succ, zero_comp,
    restrictedFreeBarHomotopyEquiv_homotopy_succ] at h
  change 0 = K.d (n + 1) n ≫ (-adj.restrictedFreeBarSplitOperator M n) +
    (-adj.restrictedFreeBarSplitOperator M (n + 1)) ≫ K.d (n + 2) (n + 1) + 𝟙 (K.X (n + 1)) at h
  rw [Preadditive.comp_neg, Preadditive.neg_comp] at h
  have hh := congrArg
    (fun z : K.X (n + 1) ⟶ K.X (n + 1) =>
      adj.restrictedFreeBarSplitOperator M (n + 1) ≫ K.d (n + 2) (n + 1) +
        K.d (n + 1) n ≫ adj.restrictedFreeBarSplitOperator M n + z) h
  abel_nf at hh
  exact hh

/-- The coefficient map gives the alternating-chain map after restriction. -/
def restrictedFreeBarChainMap (adj : F ⊣ U) {M N : D} (f : M ⟶ N) :
    restrictedFreeBarChain adj M ⟶ restrictedFreeBarChain adj N :=
  (alternatingFaceMapComplex C).map
    (Functor.whiskerRight ((adj.freeBarFunctor).map f) U)

/-- The restricted augmentation is natural in every coefficient map. -/
@[reassoc]
theorem restrictedFreeBar_augmentation_naturality (adj : F ⊣ U) {M N : D} (f : M ⟶ N) :
    adj.restrictedFreeBarChainMap f ≫ (adj.restrictedFreeBarHomotopyEquiv N).hom =
      (adj.restrictedFreeBarHomotopyEquiv M).hom ≫ (ChainComplex.single₀ C).map (U.map f) := by
  let a := (SimplicialObject.Augmented.whiskeringObj D C U).map
    ((adj.freeBarAugmentedFunctor).map f)
  exact AlternatingFaceMapComplex.ε.naturality a

end Contraction

section AdditiveWhiskering

variable [Preadditive C] [Preadditive D] [U.Additive]

/-- Additive whiskering relates the D-chain to the restricted C-chain. -/
def restrictedFreeBarChainIso (adj : F ⊣ U) (M : D) :
    (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex D).obj (adj.freeBar M)) ≅
      (alternatingFaceMapComplex C).obj (adj.freeBar M ⋙ U) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso U).app (adj.freeBar M)

/-- The comparison has identity components on chain objects. -/
theorem restrictedFreeBarChainIso_hom_f (adj : F ⊣ U) (M : D) (n : ℕ) :
    (adj.restrictedFreeBarChainIso M).hom.f n = 𝟙 _ := rfl

end AdditiveWhiskering

section Homology

variable [Abelian C]

/-- In an Abelian target, the restricted augmentation is a quasi-isomorphism. -/
theorem restrictedFreeBar_augmentation_quasiIso (adj : F ⊣ U) (M : D) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (adj.restrictedFreeBarAugmented M)) :=
  (adj.restrictedFreeBarHomotopyEquiv M).quasiIso_hom

end Homology

end CategoryTheory.Adjunction
