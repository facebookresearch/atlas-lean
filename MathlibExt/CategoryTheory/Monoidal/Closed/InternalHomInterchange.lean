/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Full natural internal currying, coordinate interchange, and point evaluation

The complete original reusable closed-category namespaces live here.
Their actual functions, proofs, declared universes and public Names are
retained. Simplicial-set specializations import this general Source.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

section
universe u v u₁ v₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped MonoidalClosed

namespace CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The full original internal currying map commutes with every original target map. -/
theorem originalIhomCurry_naturality (I J : C) {X Y : C} (f : X ⟶ Y) :
    (ihom (I ⊗ J)).map f ≫ ihomCurry I J Y =
      ihomCurry I J X ≫ (ihom J).map ((ihom I).map f) := by
  apply uncurry_injective
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_natural_right]
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc]
  exact (congrArg (fun h => (α_ I J ((ihom (I ⊗ J)).obj X)).inv ≫ h)
    ((ihom.ev (I ⊗ J)).naturality f)).trans
      (Category.assoc (α_ I J ((ihom (I ⊗ J)).obj X)).inv
        ((ihom.ev (I ⊗ J)).app X) f).symm

/-- Both original currying and uncurrying maps form the full original internal natural Iso. -/
def originalIhomCurryingNatIso (I J : C) :
    ihom (I ⊗ J) ≅ ihom I ⋙ ihom J :=
  NatIso.ofComponents (fun X => ihomCurryIso I J X)
    (fun f => originalIhomCurry_naturality I J f)

/-- The entire forward natural component is the SAME original internal currying function. -/
theorem originalIhomCurryingNatIso_hom_app (I J X : C) :
    (originalIhomCurryingNatIso I J).hom.app X = ihomCurry I J X := rfl

/-- The entire inverse natural component is the SAME original internal uncurrying function. -/
theorem originalIhomCurryingNatIso_inv_app (I J X : C) :
    (originalIhomCurryingNatIso I J).inv.app X = ihomUncurry I J X := rfl

/-- Every entire inverse original internal map retains the full target-map naturality. -/
theorem originalIhomCurryingNatIso_inv_naturality (I J : C) {X Y : C} (f : X ⟶ Y) :
    (ihom J).map ((ihom I).map f) ≫ (originalIhomCurryingNatIso I J).inv.app Y =
      (originalIhomCurryingNatIso I J).inv.app X ≫ (ihom (I ⊗ J)).map f :=
  (originalIhomCurryingNatIso I J).inv.naturality f

private theorem originalDoubleUncurryPostCurrying (K M : C) {A X : C}
    (f : A ⟶ (ihom (K ⊗ M)).obj X) :
    uncurry (A := K) (uncurry (A := M) (f ≫ ihomCurry K M X)) =
      (α_ K M A).inv ≫ uncurry f := by
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc]
  rw [uncurry_eq]

section Braided

variable [BraidedCategory C]

/-- The complete original two-coordinate swap is built from the SAME whole original closed maps. -/
def originalSelfInterchangeNatIso (K : C) : ihom K ⋙ ihom K ≅ ihom K ⋙ ihom K :=
  (originalIhomCurryingNatIso K K).symm ≪≫
    (MonoidalClosed.internalHom (C := C)).mapIso (β_ K K).symm.op ≪≫
      originalIhomCurryingNatIso K K

/-- The full forward coordinate map keeps both original internal maps and original inverse
braiding. -/
theorem originalSelfInterchangeNatIso_hom_app (K X : C) :
    (originalSelfInterchangeNatIso K).hom.app X =
      ihomUncurry K K X ≫ (pre (β_ K K).inv).app X ≫ ihomCurry K K X := rfl

/-- The full inverse coordinate map keeps both original internal maps and original forward
braiding. -/
theorem originalSelfInterchangeNatIso_inv_app (K X : C) :
    (originalSelfInterchangeNatIso K).inv.app X =
      ihomUncurry K K X ≫ (pre (β_ K K).hom).app X ≫ ihomCurry K K X :=
  Category.assoc (ihomUncurry K K X) ((pre (β_ K K).hom).app X) (ihomCurry K K X)

/-- Every entire original target map keeps the full forward two-coordinate naturality. -/
theorem originalSelfInterchangeNatIso_hom_naturality (K : C) {X Y : C} (f : X ⟶ Y) :
    (ihom K).map ((ihom K).map f) ≫ (originalSelfInterchangeNatIso K).hom.app Y =
      (originalSelfInterchangeNatIso K).hom.app X ≫ (ihom K).map ((ihom K).map f) :=
  (originalSelfInterchangeNatIso K).hom.naturality f

/-- Every entire original target map keeps the full inverse two-coordinate naturality. -/
theorem originalSelfInterchangeNatIso_inv_naturality (K : C) {X Y : C} (f : X ⟶ Y) :
    (ihom K).map ((ihom K).map f) ≫ (originalSelfInterchangeNatIso K).inv.app Y =
      (originalSelfInterchangeNatIso K).inv.app X ≫ (ihom K).map ((ihom K).map f) :=
  (originalSelfInterchangeNatIso K).inv.naturality f

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- The SAME actual ambient symmetric braiding identifies both entire coordinate functions. -/
theorem originalSelfInterchangeNatIso_hom_eq_inv (K : C) :
    (originalSelfInterchangeNatIso K).hom = (originalSelfInterchangeNatIso K).inv := by
  apply NatTrans.ext
  funext X
  rw [originalSelfInterchangeNatIso_hom_app, originalSelfInterchangeNatIso_inv_app,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding K K]

/-- Swapping the SAME original coordinates twice is the whole original functor identity. -/
theorem originalSelfInterchangeNatIso_involution (K : C) :
    (originalSelfInterchangeNatIso K).hom ≫ (originalSelfInterchangeNatIso K).hom = 𝟙 _ :=
  (congrArg (fun h => (originalSelfInterchangeNatIso K).hom ≫ h)
    (originalSelfInterchangeNatIso_hom_eq_inv K)).trans
      (originalSelfInterchangeNatIso K).hom_inv_id

end Symmetric

section Braided

variable [BraidedCategory C]

/-- Twice uncurrying retains the literal original coordinate permutation and both evaluations. -/
theorem originalSelfInterchangeNatIso_hom_double_uncurry (K X : C) :
    uncurry (uncurry ((originalSelfInterchangeNatIso K).hom.app X)) =
      (α_ K K ((ihom K).obj ((ihom K).obj X))).inv ≫
        (β_ K K).inv ▷ ((ihom K).obj ((ihom K).obj X)) ≫
          (α_ K K ((ihom K).obj ((ihom K).obj X))).hom ≫
            K ◁ (ihom.ev K).app ((ihom K).obj X) ≫ (ihom.ev K).app X := by
  let a := ihomUncurry K K X
  let b := (pre (β_ K K).inv).app X
  let c := ihomCurry K K X
  have hFirst := originalDoubleUncurryPostCurrying K K (a ≫ b)
  have hPre := uncurry_pre_app X a (β_ K K).inv
  have hOriginal := uncurry_ihomUncurry K K X
  exact (congrArg (fun f => uncurry (uncurry f))
      (originalSelfInterchangeNatIso_hom_app K X)).trans
    ((congrArg (fun f => uncurry (uncurry f)) (Category.assoc a b c).symm).trans
      (hFirst.trans (congrArg
        (fun f => (α_ K K ((ihom K).obj ((ihom K).obj X))).inv ≫ f)
          (hPre.trans (congrArg
            (fun f => (β_ K K).inv ▷ ((ihom K).obj ((ihom K).obj X)) ≫ f) hOriginal)))))

end Braided

end CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry

end

section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped MonoidalClosed

namespace CategoryTheory.MonoidalClosed.OriginalPointEvaluationClauseGeometry

universe u₁ v₁
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The entire original pre-composition clause remains equal after the full unit evaluation. -/
theorem originalPreCompositionEvaluation_whole {A B : C}
    (f : (𝟙_ C) ⟶ A) (g : A ⟶ B) :
    (pre g ≫ pre f) ≫ unitNatIso.inv = pre (f ≫ g) ≫ unitNatIso.inv :=
  congrArg (fun e => e ≫ unitNatIso.inv) (pre_map f g).symm

/-- Every original component retains the complete original pre-composition value clause. -/
theorem originalPreCompositionEvaluation_app {A B : C}
    (f : (𝟙_ C) ⟶ A) (g : A ⟶ B) (X : C) :
    (pre g).app X ≫ (pre f).app X ≫ (unitIsoSelf (X := X)).hom =
      (pre (f ≫ g)).app X ≫ (unitIsoSelf (X := X)).hom :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun e => e.app X) (originalPreCompositionEvaluation_whole f g))

end CategoryTheory.MonoidalClosed.OriginalPointEvaluationClauseGeometry

end

section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped MonoidalClosed

namespace CategoryTheory.MonoidalClosed.OriginalDoubleLoopCoordinateGeometry

universe u₁ v₁
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
open CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry


/-- Every entire original internal square retains the whole defining coordinate map after
twice uncurrying, before the actual simplicial specialization. -/
theorem originalWholeSquareTwist_uncurry (K X : C) (r : K ⊗ K ⟶ K ⊗ K)
    {A : C} (g : A ⟶ (ihom K).obj ((ihom K).obj X)) :
    uncurry (uncurry (g ≫ ihomUncurry K K X ≫ (pre r).app X ≫ ihomCurry K K X)) =
      (α_ K K A).inv ≫ r ▷ A ≫ (α_ K K A).hom ≫ uncurry (uncurry g) := by
  let a := ihomUncurry K K X
  let b := (pre r).app X
  let c := ihomCurry K K X
  have hc : a ≫ c = 𝟙 _ :=
    congr_app (originalIhomCurryingNatIso K K).inv_hom_id X
  have hG : g = (g ≫ a) ≫ c := by
    exact (show (g ≫ a) ≫ c = g by rw [Category.assoc, hc, Category.comp_id]).symm
  have hD : uncurry (uncurry g) = (α_ K K A).inv ≫ uncurry (g ≫ a) :=
    (congrArg (fun t => uncurry (uncurry t)) hG).trans
      (originalDoubleUncurryPostCurrying K K (g ≫ a))
  have hSwap : g ≫ a ≫ b ≫ c = ((g ≫ a) ≫ b) ≫ c := by
    simp only [Category.assoc]
  change uncurry (uncurry (g ≫ a ≫ b ≫ c)) = _
  rw [hSwap, originalDoubleUncurryPostCurrying, uncurry_pre_app, hD]
  simp only [Iso.hom_inv_id_assoc]

universe u₂ v₂
variable {C₂ : Type u₂} [Category.{v₂} C₂]

/-- The entire original composition retains its whole projection equation before specializing
the complete original carrier and map functions. -/
theorem originalWholeCompositeProjection {A B D E : C₂}
    (f : A ⟶ B) (g : B ⟶ D) (e : D ⟶ E) (b : B ⟶ E) (j : A ⟶ E)
    (hg : g ≫ e = b) (hf : f ≫ b = j) : (f ≫ g) ≫ e = j :=
  (Category.assoc f g e).trans ((congrArg (fun a => f ≫ a) hg).trans hf)

/-- The complete restricted fiber square retains every original inclusion and both complete
coordinate maps before the exact simplicial specialization. -/
theorem originalWholeFiberSquareProjection {A B D E P : C₂}
    (f : A ⟶ B) (b : B ⟶ D) (a : A ⟶ E) (m : E ⟶ D)
    (v : D ⟶ P) (w : E ⟶ P) (j : A ⟶ P) (s : P ⟶ P)
    (hf : f ≫ b = a ≫ m) (hm : m ≫ v = w ≫ s) (hj : a ≫ w = j) :
    f ≫ (b ≫ v) = j ≫ s := by
  rw [← Category.assoc, hf, Category.assoc, hm, ← Category.assoc, hj]

/-- The entire mapped projection square retains its whole value function and associativity
before the exact original sequence specialization. -/
theorem originalWholeMappedProjectionPostcomp {A B D E P Q : C₂}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (f : A ⟶ P) (g : P ⟶ E) (p : E ⟶ Q)
    (h : a ≫ b ≫ c = f ≫ g) : a ≫ b ≫ c ≫ p = f ≫ (g ≫ p) :=
  (congrArg (fun t => a ≫ t) (Category.assoc b c p)).symm.trans
    ((Category.assoc a (b ≫ c) p).symm.trans
      ((congrArg (fun t => t ≫ p) h).trans (Category.assoc f g p)))

variable [BraidedCategory C]

/-- The full forward original square swap has its literal original inverse braiding. -/
theorem originalWholeSquareSwap_hom_uncurry (K X : C) {A : C}
    (g : A ⟶ (ihom K).obj ((ihom K).obj X)) :
    uncurry (uncurry (g ≫ (originalSelfInterchangeNatIso K).hom.app X)) =
      (α_ K K A).inv ≫ (β_ K K).inv ▷ A ≫ (α_ K K A).hom ≫ uncurry (uncurry g) := by
  rw [originalSelfInterchangeNatIso_hom_app]
  exact originalWholeSquareTwist_uncurry K X (β_ K K).inv g

/-- The full inverse original square swap has its literal original forward braiding. -/
theorem originalWholeSquareSwap_inv_uncurry (K X : C) {A : C}
    (g : A ⟶ (ihom K).obj ((ihom K).obj X)) :
    uncurry (uncurry (g ≫ (originalSelfInterchangeNatIso K).inv.app X)) =
      (α_ K K A).inv ≫ (β_ K K).hom ▷ A ≫ (α_ K K A).hom ≫ uncurry (uncurry g) := by
  rw [originalSelfInterchangeNatIso_inv_app]
  exact originalWholeSquareTwist_uncurry K X (β_ K K).hom g

end CategoryTheory.MonoidalClosed.OriginalDoubleLoopCoordinateGeometry

end

section ScalarOperatorInterchange

universe uC vC
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.MonoidalClosed

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- The scalar and operator internal Hom coordinates are exchanged by the
original currying maps and the actual inverse braiding of their coefficients. -/
def scalarOperatorInterchangeNatIso (M K : C) :
    ihom K ⋙ ihom M ≅ ihom M ⋙ ihom K :=
  (MonoidalClosed.OriginalLoopInterchangeGeometry.originalIhomCurryingNatIso K M).symm ≪≫
    (MonoidalClosed.internalHom (C := C)).mapIso (β_ K M).symm.op ≪≫
      MonoidalClosed.OriginalLoopInterchangeGeometry.originalIhomCurryingNatIso M K

/-- The scalar/operator interchange retains the full original closed maps. -/
theorem scalarOperatorInterchangeNatIso_hom_app (M K X : C) :
    (scalarOperatorInterchangeNatIso M K).hom.app X =
      MonoidalClosed.ihomUncurry K M X ≫ (MonoidalClosed.pre (β_ K M).inv).app X ≫
        MonoidalClosed.ihomCurry M K X := rfl

/-- The inverse comparison retains the original forward coefficient braiding. -/
theorem scalarOperatorInterchangeNatIso_inv_app (M K X : C) :
    (scalarOperatorInterchangeNatIso M K).inv.app X =
      MonoidalClosed.ihomUncurry M K X ≫ (MonoidalClosed.pre (β_ K M).hom).app X ≫
        MonoidalClosed.ihomCurry K M X :=
  Category.assoc (MonoidalClosed.ihomUncurry M K X)
    ((MonoidalClosed.pre (β_ K M).hom).app X) (MonoidalClosed.ihomCurry K M X)

/-- Every original target arrow commutes with the entire forward coordinate map. -/
theorem scalarOperatorInterchangeNatIso_hom_naturality (M K : C) {X Y : C} (f : X ⟶ Y) :
    (ihom M).map ((ihom K).map f) ≫ (scalarOperatorInterchangeNatIso M K).hom.app Y =
      (scalarOperatorInterchangeNatIso M K).hom.app X ≫ (ihom K).map ((ihom M).map f) :=
  (scalarOperatorInterchangeNatIso M K).hom.naturality f

/-- Every original target arrow commutes with the entire inverse coordinate map. -/
theorem scalarOperatorInterchangeNatIso_inv_naturality (M K : C) {X Y : C} (f : X ⟶ Y) :
    (ihom K).map ((ihom M).map f) ≫ (scalarOperatorInterchangeNatIso M K).inv.app Y =
      (scalarOperatorInterchangeNatIso M K).inv.app X ≫ (ihom M).map ((ihom K).map f) :=
  (scalarOperatorInterchangeNatIso M K).inv.naturality f

/-- Equal scalar and operator coefficients recover the original self-interchange. -/
theorem scalarOperatorInterchangeNatIso_self (K : C) :
    scalarOperatorInterchangeNatIso K K =
      MonoidalClosed.OriginalLoopInterchangeGeometry.originalSelfInterchangeNatIso K := rfl

/-- Twice uncurrying the scalar/operator comparison preserves the entire
coefficient permutation and both actual evaluation maps. -/
theorem scalarOperatorInterchange_uncurry (M K X : C) {A : C}
    (g : A ⟶ (ihom M).obj ((ihom K).obj X)) :
    MonoidalClosed.uncurry (A := M) (MonoidalClosed.uncurry (A := K)
        (g ≫ (scalarOperatorInterchangeNatIso M K).hom.app X)) =
      (α_ M K A).inv ≫ (β_ K M).inv ▷ A ≫ (α_ K M A).hom ≫
        MonoidalClosed.uncurry (A := K) (MonoidalClosed.uncurry (A := M) g) := by
  let a := MonoidalClosed.ihomUncurry K M X
  let b := (MonoidalClosed.pre (β_ K M).inv).app X
  let c := MonoidalClosed.ihomCurry K M X
  have hc : a ≫ c = 𝟙 _ :=
    congr_app
      (MonoidalClosed.OriginalLoopInterchangeGeometry.originalIhomCurryingNatIso K M).inv_hom_id X
  have hG : g = (g ≫ a) ≫ c := by
    exact (show (g ≫ a) ≫ c = g by rw [Category.assoc, hc, Category.comp_id]).symm
  have hD : MonoidalClosed.uncurry (A := K) (MonoidalClosed.uncurry (A := M) g) =
      (α_ K M A).inv ≫ MonoidalClosed.uncurry (g ≫ a) :=
    (congrArg (fun t => MonoidalClosed.uncurry (A := K)
      (MonoidalClosed.uncurry (A := M) t)) hG).trans
        (OriginalLoopInterchangeGeometry.originalDoubleUncurryPostCurrying K M (g ≫ a))
  rw [scalarOperatorInterchangeNatIso_hom_app]
  change MonoidalClosed.uncurry (A := M) (MonoidalClosed.uncurry (A := K)
      (g ≫ a ≫ b ≫ MonoidalClosed.ihomCurry M K X)) = _
  have hSwap : g ≫ a ≫ b ≫ MonoidalClosed.ihomCurry M K X =
      ((g ≫ a) ≫ b) ≫ MonoidalClosed.ihomCurry M K X := by
    simp only [Category.assoc]
  rw
      [hSwap, OriginalLoopInterchangeGeometry.originalDoubleUncurryPostCurrying,
        MonoidalClosed.uncurry_pre_app, hD]
  simp only [Iso.hom_inv_id_assoc]

end CategoryTheory.MonoidalClosed

end ScalarOperatorInterchange

section ScalarOperatorTensorEvaluation

universe uC vC
open CategoryTheory MonoidalCategory BraidedCategory

namespace CategoryTheory.MonoidalClosed

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]

private theorem tensorSwapCoefficient (M K A H : C) (u : K ⟶ H) :
    M ◁ (u ▷ A) ≫ M ◁ (β_ A H).inv ≫ (α_ M A H).inv =
      (α_ M K A).inv ≫ (β_ K M).inv ▷ A ≫ (α_ K M A).hom ≫
        u ▷ (M ⊗ A) ≫ (β_ (M ⊗ A) H).inv := by
  have hb : (β_ K M).inv ≫ u ▷ M ≫ (β_ M H).inv = M ◁ u := by
    have h := braiding_inv_naturality_right M u
    calc
      _ = (M ◁ u ≫ (β_ H M).inv) ≫ (β_ M H).inv := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ (β_ M H).inv) h.symm)
      _ = _ := by
        rw [← SymmetricCategory.braiding_swap_eq_inv_braiding H M]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hb' : ((β_ K M).inv ≫ u ▷ M) ≫ (β_ M H).inv = M ◁ u :=
    (Category.assoc _ _ _).trans hb
  rw [braiding_tensor_left_inv]
  rw [← associator_naturality_left_assoc u M A, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, hb']
  rw [← associator_inv_naturality_middle_assoc M u A, Iso.inv_hom_id_assoc]

/-- The tensor evaluation identity retains the full coefficient permutation.
Symmetry is used to cancel the two inverse braidings. -/
theorem scalarOperatorInterchange_tensorSwapEvaluation (M K A H X : C) (u : K ⟶ H) (e : M ⊗ A ⟶ X) :
    M ◁ (u ▷ A ≫ (β_ A H).inv) ≫ (α_ M A H).inv ≫ e ▷ H =
      (α_ M K A).inv ≫ (β_ K M).inv ▷ A ≫ (α_ K M A).hom ≫
        K ◁ e ≫ u ▷ X ≫ (β_ X H).inv := by
  calc
    _ = (M ◁ (u ▷ A) ≫ M ◁ (β_ A H).inv ≫ (α_ M A H).inv) ≫ e ▷ H := by
      simp only [whiskerLeft_comp, Category.assoc]
    _ = ((α_ M K A).inv ≫ (β_ K M).inv ▷ A ≫ (α_ K M A).hom ≫
        u ▷ (M ⊗ A) ≫ (β_ (M ⊗ A) H).inv) ≫ e ▷ H :=
      congrArg (fun q => q ≫ e ▷ H) (tensorSwapCoefficient M K A H u)
    _ = _ := by
      simp only [Category.assoc]
      rw [← braiding_inv_naturality_right H e, whisker_exchange_assoc u e]

end CategoryTheory.MonoidalClosed

end ScalarOperatorTensorEvaluation
