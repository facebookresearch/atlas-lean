/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceCoefficientAction
public import MathlibExt.Topology.Category.PointedCGWH.Points

/-!
# Composition from the original continuous orthogonal source laws

The original source associative equation supplies the ordered coefficient
composition. Mapped weighted coend generators and the actual unit separator
determine the entire operator action while retaining every spectrum value
and both whole sphere coefficients.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceCompositionCompatibility

/-- The original orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on orthogonal indices. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed CGWH enriched ordinary structure on orthogonal indices. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry on orthogonal indices. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

attribute [local instance] Enriched.prodCategory

/-- All original arrow coefficients determine maps on the whole tensor-preserved operator coend. -/
theorem coefficientHom_hom_ext (M T : PointedCGWH.{u, v}) (n k : OrthogonalIndex)
    {f g : M ⊗ OrthogonalOperatorIndex.hom.{u, v} n k ⟶ T}
    (h : ∀ (a : OrthogonalIndex) (p : a + n ⟶ k),
      (M ◁ coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} n k a p) ≫ f =
      (M ◁ coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} n k a p) ≫ g) : f = g := by
  apply Enriched.weightedCoend.Mapped.hom_ext
    (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k)
    orthogonalSphereFunctor.{u, v} (tensorLeft M)
  intro a
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let i : H ⊗ A ⟶ OrthogonalOperatorIndex.hom.{u, v} n k :=
    OrthogonalOperatorIndex.ι.{u, v} n k a
  let ff : M ⊗ (H ⊗ A) ⟶ T := (M ◁ i) ≫ f
  let gg : M ⊗ (H ⊗ A) ⟶ T := (M ◁ i) ≫ g
  change ff = gg
  apply MonoidalClosed.curry_injective
  apply PointedCGWH.tensorLeftPoint_hom_ext
  intro p
  apply MonoidalClosed.uncurry_injective
  let j : A ⟶ H ⊗ A := (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)
  let q : a + n ⟶ k := (eHomEquiv PointedCGWH.{u, v}).symm p
  have hp : eHomEquiv PointedCGWH.{u, v} q = p := Equiv.apply_symm_apply _ p
  let c : A ⟶ OrthogonalOperatorIndex.hom.{u, v} n k :=
    coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} n k a q
  have hCoefficient : c = ((λ_ A).inv ≫ (eHomEquiv PointedCGWH.{u, v} q ⊗ₘ 𝟙 A)) ≫ i :=
    rfl
  have hj : ((λ_ A).inv ≫ (eHomEquiv PointedCGWH.{u, v} q ⊗ₘ 𝟙 A)) = j :=
    congrArg (fun z : 𝟙_ PointedCGWH.{u, v} ⟶ H => (λ_ A).inv ≫ (z ⊗ₘ 𝟙 A)) hp
  have hc : c = j ≫ i := hCoefficient.trans (congrArg (fun z => z ≫ i) hj)
  have hPrefix : M ◁ c = (M ◁ j) ≫ M ◁ i :=
    (congrArg (fun z => M ◁ z) hc).trans (whiskerLeft_comp M j i)
  have hFirst : (M ◁ j) ≫ ff = (M ◁ c) ≫ f :=
    (Category.assoc (M ◁ j) (M ◁ i) f).symm.trans
      (congrArg (fun z => z ≫ f) hPrefix.symm)
  have hLast : (M ◁ j) ≫ gg = (M ◁ c) ≫ g :=
    (Category.assoc (M ◁ j) (M ◁ i) g).symm.trans
      (congrArg (fun z => z ≫ g) hPrefix.symm)
  have hLeft : MonoidalClosed.uncurry (j ≫ MonoidalClosed.curry ff) = (M ◁ j) ≫ ff :=
    (MonoidalClosed.uncurry_natural_left j (MonoidalClosed.curry ff)).trans
      (congrArg (fun z => (M ◁ j) ≫ z) (MonoidalClosed.uncurry_curry ff))
  have hRight : MonoidalClosed.uncurry (j ≫ MonoidalClosed.curry gg) = (M ◁ j) ≫ gg :=
    (MonoidalClosed.uncurry_natural_left j (MonoidalClosed.curry gg)).trans
      (congrArg (fun z => (M ◁ j) ≫ z) (MonoidalClosed.uncurry_curry gg))
  exact hLeft.trans ((hFirst.trans ((h a q).trans hLast.symm)).trans hRight.symm)

/-- Two independent original coefficient arrows determine maps on both entire operator Homs. -/
theorem coefficient_pair_hom_ext (M T : PointedCGWH.{u, v}) (n k l : OrthogonalIndex)
    {f g : M ⊗ (OrthogonalOperatorIndex.hom.{u, v} n k ⊗
      OrthogonalOperatorIndex.hom.{u, v} k l) ⟶ T}
    (h : ∀ (a b : OrthogonalIndex) (p : a + n ⟶ k) (q : b + k ⟶ l),
      (M ◁ (coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} n k a p ⊗ₘ
          coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
            orthogonalSphereFunctor.{u, v} k l b q)) ≫ f =
      (M ◁ (coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} n k a p ⊗ₘ
          coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
            orthogonalSphereFunctor.{u, v} k l b q)) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply coefficientHom_hom_ext (OrthogonalOperatorIndex.hom.{u, v} n k)
    ((ihom M).obj T) k l
  intro b q
  apply (cancel_epi
    (β_ (PointedCGWH.orthogonalSphere.{u, v} b) (OrthogonalOperatorIndex.hom.{u, v} n k)).hom).1
  apply coefficientHom_hom_ext (PointedCGWH.orthogonalSphere.{u, v} b)
    ((ihom M).obj T) n k
  intro a p
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let B := PointedCGWH.orthogonalSphere.{u, v} b
  let H := OrthogonalOperatorIndex.hom.{u, v} n k
  let K := OrthogonalOperatorIndex.hom.{u, v} k l
  let cp : A ⟶ H := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} n k a p
  let cq : B ⟶ K := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} k l b q
  have hNat : (B ◁ cp) ≫ (β_ B H).hom ≫ (H ◁ cq) =
      (β_ B A).hom ≫ (cp ⊗ₘ cq) := by
    rw [braiding_naturality_right_assoc, ← tensorHom_def]
  have hPair : (cp ⊗ₘ cq) ≫ MonoidalClosed.curry f =
      (cp ⊗ₘ cq) ≫ MonoidalClosed.curry g := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
    exact h a b p q
  change (B ◁ cp) ≫ (β_ B H).hom ≫ (H ◁ cq) ≫ MonoidalClosed.curry f =
    (B ◁ cp) ≫ (β_ B H).hom ≫ (H ◁ cq) ≫ MonoidalClosed.curry g
  calc
    _ = (β_ B A).hom ≫ (cp ⊗ₘ cq) ≫ MonoidalClosed.curry f := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ MonoidalClosed.curry f) hNat
    _ = (β_ B A).hom ≫ (cp ⊗ₘ cq) ≫ MonoidalClosed.curry g :=
      congrArg (fun z => (β_ B A).hom ≫ z) hPair
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ MonoidalClosed.curry g) hNat.symm

variable
  (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))
  (ha : ∀ n a b : OrthogonalIndex,
    (α_ (X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
      (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ▷
          PointedCGWH.orthogonalSphere.{u, v} b) ≫
        Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (n + a) b =
    (X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.mu a b) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (a + b) ≫
          X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv)

include ha

/-- The original external source associativity composes every whole pair of labeled
coefficients. -/
theorem coefficient_action_comp (n k l a b : OrthogonalIndex)
    (f : a + n ⟶ k) (g : b + k ⟶ l) :
    (α_ (X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
      (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      ((Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ≫
          X.toEnrichedFunctor.toOrdinaryFunctor.map f) ▷ PointedCGWH.orthogonalSphere.{u, v} b) ≫
      Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t k b ≫
          X.toEnrichedFunctor.toOrdinaryFunctor.map g =
    (X.toEnrichedFunctor.obj n ◁
      ((β_ (PointedCGWH.orthogonalSphere.{u, v} a)
        (PointedCGWH.orthogonalSphere.{u, v} b)).hom ≫
          orthogonalSphereMonoidalData.{u, v}.mu b a)) ≫
      Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (b + a) ≫
          X.toEnrichedFunctor.toOrdinaryFunctor.map ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
  let M := X.toEnrichedFunctor.obj n
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let B := PointedCGWH.orthogonalSphere.{u, v} b
  let N := X.toEnrichedFunctor.obj (a + n)
  let Y := X.toEnrichedFunctor.obj k
  let Z := X.toEnrichedFunctor.obj (b + (a + n))
  let T := X.toEnrichedFunctor.obj (b + k)
  let cA : M ⊗ A ⟶ N := Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let cB : Y ⊗ B ⟶ T := Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t k b
  let cBA : N ⊗ B ⟶ Z := Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (a + n) b
  let cAll : M ⊗ PointedCGWH.orthogonalSphere.{u, v} (b + a) ⟶
      X.toEnrichedFunctor.obj ((b + a) + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (b + a)
  let r : N ⟶ Y := X.toEnrichedFunctor.toOrdinaryFunctor.map f
  let s : T ⟶ X.toEnrichedFunctor.obj l := X.toEnrichedFunctor.toOrdinaryFunctor.map g
  let fo : Z ⟶ T := X.toEnrichedFunctor.toOrdinaryFunctor.map (b ◁ f)
  let ao : X.toEnrichedFunctor.obj ((b + a) + n) ⟶ Z :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ b a n).hom
  let m : A ⊗ B ⟶ PointedCGWH.orthogonalSphere.{u, v} (b + a) :=
    (β_ A B).hom ≫ orthogonalSphereMonoidalData.{u, v}.mu b a
  let label : (b + a) + n ⟶ l := (α_ b a n).hom ≫ (b ◁ f) ≫ g
  have hMove : (r ▷ B) ≫ cB = cBA ≫ fo := by
    have h := CanonicalSourceCoefficientCompatibility.coefficient_twoInputs X t f (𝟙 b)
    have hid : orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (𝟙 b) = 𝟙 B :=
      orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map_id b
    have ht : r ⊗ₘ orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (𝟙 b) = r ▷ B :=
      (congrArg (fun z : B ⟶ B => r ⊗ₘ z) hid).trans (tensorHom_id r B)
    have hi : X.toEnrichedFunctor.toOrdinaryFunctor.map (𝟙 b ⊗ₘ f) = fo :=
      congrArg X.toEnrichedFunctor.toOrdinaryFunctor.map (id_tensorHom b f)
    calc
      _ = (r ⊗ₘ orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (𝟙 b)) ≫ cB :=
        congrArg (fun z => z ≫ cB) ht.symm
      _ = cBA ≫ X.toEnrichedFunctor.toOrdinaryFunctor.map (𝟙 b ⊗ₘ f) := h
      _ = cBA ≫ fo := congrArg (fun z => cBA ≫ z) hi
  have hAssoc : (α_ M A B).inv ≫ (cA ▷ B) ≫ cBA = (M ◁ m) ≫ cAll ≫ ao :=
    CanonicalSourceCoefficientCompatibility.coefficient_assoc X t ha n a b
  have hLabel : ao ≫ fo ≫ s = X.toEnrichedFunctor.toOrdinaryFunctor.map label := by
    dsimp only [ao, fo, s]
    simp only [label, Functor.map_comp]
  change (α_ M A B).inv ≫ ((cA ≫ r) ▷ B) ≫ cB ≫ s =
    (M ◁ m) ≫ cAll ≫ X.toEnrichedFunctor.toOrdinaryFunctor.map label
  calc
    _ = (α_ M A B).inv ≫ (cA ▷ B) ≫ (r ▷ B) ≫ cB ≫ s := by
      rw [comp_whiskerRight]
      simp only [Category.assoc]
    _ = (α_ M A B).inv ≫ (cA ▷ B) ≫ cBA ≫ fo ≫ s := by
      simpa only [Category.assoc] using
        congrArg (fun z => (α_ M A B).inv ≫ (cA ▷ B) ≫ z ≫ s) hMove
    _ = (M ◁ m) ≫ cAll ≫ ao ≫ fo ≫ s := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ fo ≫ s) hAssoc
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z => (M ◁ m) ≫ cAll ≫ z) hLabel

/-- Both complete coefficient inclusions compose through the actual original reverse action. -/
theorem reverseOperatorAction_coefficient_comp (n k l a b : OrthogonalIndex)
    (f : a + n ⟶ k) (g : b + k ⟶ l) :
    (X.toEnrichedFunctor.obj n ◁
      ((coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} n k a f ⊗ₘ
          coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
            orthogonalSphereFunctor.{u, v} k l b g) ≫
        eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l))) ≫
      reverseOperatorAction.{u, v} X t n l =
    (α_ (X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
      (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (((X.toEnrichedFunctor.obj n ◁
        coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} n k a f) ≫
            reverseOperatorAction.{u, v} X t n k) ▷ PointedCGWH.orthogonalSphere.{u, v} b) ≫
      (X.toEnrichedFunctor.obj k ◁
        coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} k l b g) ≫ reverseOperatorAction.{u, v} X t k l := by
  let M := X.toEnrichedFunctor.obj n
  let Y := X.toEnrichedFunctor.obj k
  let Z := X.toEnrichedFunctor.obj l
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let B := PointedCGWH.orthogonalSphere.{u, v} b
  let C := PointedCGWH.orthogonalSphere.{u, v} (b + a)
  let H := OrthogonalOperatorIndex.hom.{u, v} n k
  let K := OrthogonalOperatorIndex.hom.{u, v} k l
  let P := OrthogonalOperatorIndex.hom.{u, v} n l
  let cp : A ⟶ H := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} n k a f
  let cq : B ⟶ K := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} k l b g
  let label : (b + a) + n ⟶ l := (α_ b a n).hom ≫ (b ◁ f) ≫ g
  let cr : C ⟶ P := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} n l (b + a) label
  let comp : H ⊗ K ⟶ P :=
    eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l)
  let m : A ⊗ B ⟶ C := (β_ A B).hom ≫ orthogonalSphereMonoidalData.{u, v}.mu b a
  let rnk : M ⊗ H ⟶ Y := reverseOperatorAction.{u, v} X t n k
  let rkl : Y ⊗ K ⟶ Z := reverseOperatorAction.{u, v} X t k l
  let rnl : M ⊗ P ⟶ Z := reverseOperatorAction.{u, v} X t n l
  let ca : M ⊗ A ⟶ X.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let cb : Y ⊗ B ⟶ X.toEnrichedFunctor.obj (b + k) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t k b
  let cc : M ⊗ C ⟶ X.toEnrichedFunctor.obj ((b + a) + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (b + a)
  let ra : X.toEnrichedFunctor.obj (a + n) ⟶ Y := X.toEnrichedFunctor.toOrdinaryFunctor.map f
  let rb : X.toEnrichedFunctor.obj (b + k) ⟶ Z := X.toEnrichedFunctor.toOrdinaryFunctor.map g
  let rc : X.toEnrichedFunctor.obj ((b + a) + n) ⟶ Z :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map label
  have hComp : (cp ⊗ₘ cq) ≫ comp = m ≫ cr :=
    (congrArg (fun z => (cp ⊗ₘ cq) ≫ z) (OrthogonalOperatorIndex.comp_eq.{u, v} n k l)).trans
      (coefficientHom_comp OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k l a b f g)
  have hA : (M ◁ cp) ≫ rnk = ca ≫ ra :=
    CanonicalSourceCoefficientAction.coefficientHom_action X t n k a f
  have hB : (Y ◁ cq) ≫ rkl = cb ≫ rb :=
    CanonicalSourceCoefficientAction.coefficientHom_action X t k l b g
  have hC : (M ◁ cr) ≫ rnl = cc ≫ rc :=
    CanonicalSourceCoefficientAction.coefficientHom_action X t n l (b + a) label
  have hSource : (α_ M A B).inv ≫ ((ca ≫ ra) ▷ B) ≫ cb ≫ rb =
      (M ◁ m) ≫ cc ≫ rc := coefficient_action_comp X t ha n k l a b f g
  have hRight : (α_ M A B).inv ≫ (((M ◁ cp) ≫ rnk) ▷ B) ≫ (Y ◁ cq) ≫ rkl =
      (α_ M A B).inv ≫ ((ca ≫ ra) ▷ B) ≫ cb ≫ rb := by
    calc
      _ = (α_ M A B).inv ≫ ((ca ≫ ra) ▷ B) ≫ (Y ◁ cq) ≫ rkl :=
        congrArg (fun z => (α_ M A B).inv ≫ (z ▷ B) ≫ (Y ◁ cq) ≫ rkl) hA
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun z => (α_ M A B).inv ≫ ((ca ≫ ra) ▷ B) ≫ z) hB
  change (M ◁ ((cp ⊗ₘ cq) ≫ comp)) ≫ rnl =
    (α_ M A B).inv ≫ (((M ◁ cp) ≫ rnk) ▷ B) ≫ (Y ◁ cq) ≫ rkl
  calc
    _ = (M ◁ (m ≫ cr)) ≫ rnl := congrArg (fun z => (M ◁ z) ≫ rnl) hComp
    _ = (M ◁ m) ≫ (M ◁ cr) ≫ rnl := by
      rw [whiskerLeft_comp, Category.assoc]
    _ = (M ◁ m) ≫ cc ≫ rc := congrArg (fun z => (M ◁ m) ≫ z) hC
    _ = (α_ M A B).inv ≫ ((ca ≫ ra) ▷ B) ≫ cb ≫ rb := hSource.symm
    _ = _ := hRight.symm

/-- The entire original operator composition acts by the two entire reverse actions. -/
theorem reverseOperatorAction_comp (n k l : OrthogonalIndex) :
    (X.toEnrichedFunctor.obj n ◁
      eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l)) ≫
      reverseOperatorAction.{u, v} X t n l =
    (α_ (X.toEnrichedFunctor.obj n) (OrthogonalOperatorIndex.hom.{u, v} n k)
      (OrthogonalOperatorIndex.hom.{u, v} k l)).inv ≫
      (reverseOperatorAction.{u, v} X t n k ▷ OrthogonalOperatorIndex.hom.{u, v} k l) ≫
        reverseOperatorAction.{u, v} X t k l := by
  apply coefficient_pair_hom_ext (X.toEnrichedFunctor.obj n) (X.toEnrichedFunctor.obj l) n k l
  intro a b f g
  let M := X.toEnrichedFunctor.obj n
  let Y := X.toEnrichedFunctor.obj k
  let Z := X.toEnrichedFunctor.obj l
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let B := PointedCGWH.orthogonalSphere.{u, v} b
  let H := OrthogonalOperatorIndex.hom.{u, v} n k
  let K := OrthogonalOperatorIndex.hom.{u, v} k l
  let P := OrthogonalOperatorIndex.hom.{u, v} n l
  let cp : A ⟶ H := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} n k a f
  let cq : B ⟶ K := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} k l b g
  let comp : H ⊗ K ⟶ P :=
    eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l)
  let rnk : M ⊗ H ⟶ Y := reverseOperatorAction.{u, v} X t n k
  let rkl : Y ⊗ K ⟶ Z := reverseOperatorAction.{u, v} X t k l
  let rnl : M ⊗ P ⟶ Z := reverseOperatorAction.{u, v} X t n l
  have hAssoc : (M ◁ (cp ⊗ₘ cq)) ≫ (α_ M H K).inv =
      (α_ M A B).inv ≫ ((M ◁ cp) ⊗ₘ cq) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 M) cp cq
  have hSplit : ((M ◁ cp) ⊗ₘ cq) ≫ (rnk ▷ K) =
      (((M ◁ cp) ≫ rnk) ▷ B) ≫ (Y ◁ cq) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, tensorHom_def]
  have hRight : (M ◁ (cp ⊗ₘ cq)) ≫ (α_ M H K).inv ≫ (rnk ▷ K) ≫ rkl =
      (α_ M A B).inv ≫ (((M ◁ cp) ≫ rnk) ▷ B) ≫ (Y ◁ cq) ≫ rkl := by
    calc
      _ = (α_ M A B).inv ≫ ((M ◁ cp) ⊗ₘ cq) ≫ (rnk ▷ K) ≫ rkl := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ (rnk ▷ K) ≫ rkl) hAssoc
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun z => (α_ M A B).inv ≫ z ≫ rkl) hSplit
  have hSource : (M ◁ ((cp ⊗ₘ cq) ≫ comp)) ≫ rnl =
      (α_ M A B).inv ≫ (((M ◁ cp) ≫ rnk) ▷ B) ≫ (Y ◁ cq) ≫ rkl :=
    reverseOperatorAction_coefficient_comp X t ha n k l a b f g
  change (M ◁ (cp ⊗ₘ cq)) ≫ ((M ◁ comp) ≫ rnl) =
    (M ◁ (cp ⊗ₘ cq)) ≫ ((α_ M H K).inv ≫ (rnk ▷ K) ≫ rkl)
  calc
    _ = (M ◁ ((cp ⊗ₘ cq) ≫ comp)) ≫ rnl := by
      simp only [whiskerLeft_comp, Category.assoc]
    _ = (α_ M A B).inv ≫ (((M ◁ cp) ≫ rnk) ▷ B) ≫ (Y ◁ cq) ≫ rkl := hSource
    _ = _ := by simpa only [Category.assoc] using hRight.symm

/-- Currying the same whole actions gives the actual enriched composition equation. -/
theorem reverseOperatorMapField_comp (n k l : OrthogonalIndex) :
    eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l) ≫
        reverseOperatorMapField.{u, v} X t n l =
    (reverseOperatorMapField.{u, v} X t n k ⊗ₘ reverseOperatorMapField.{u, v} X t k l) ≫
      eComp PointedCGWH.{u, v} (X.toEnrichedFunctor.obj n) (X.toEnrichedFunctor.obj k)
        (X.toEnrichedFunctor.obj l) := by
  let M := X.toEnrichedFunctor.obj n
  let Y := X.toEnrichedFunctor.obj k
  let Z := X.toEnrichedFunctor.obj l
  let H := OrthogonalOperatorIndex.hom.{u, v} n k
  let K := OrthogonalOperatorIndex.hom.{u, v} k l
  let P := OrthogonalOperatorIndex.hom.{u, v} n l
  let comp : H ⊗ K ⟶ P :=
    eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l)
  let fnk : H ⟶ (ihom M).obj Y := reverseOperatorMapField.{u, v} X t n k
  let fkl : K ⟶ (ihom Y).obj Z := reverseOperatorMapField.{u, v} X t k l
  let fnl : P ⟶ (ihom M).obj Z := reverseOperatorMapField.{u, v} X t n l
  let rnk : M ⊗ H ⟶ Y := reverseOperatorAction.{u, v} X t n k
  let rkl : Y ⊗ K ⟶ Z := reverseOperatorAction.{u, v} X t k l
  let rnl : M ⊗ P ⟶ Z := reverseOperatorAction.{u, v} X t n l
  have hnk : MonoidalClosed.uncurry fnk = rnk :=
    Reconstruction.uncurry_enrichedMapField OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit n k
  have hkl : MonoidalClosed.uncurry fkl = rkl :=
    Reconstruction.uncurry_enrichedMapField OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit k l
  have hnl : MonoidalClosed.uncurry fnl = rnl :=
    Reconstruction.uncurry_enrichedMapField OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit n l
  have hLeft : MonoidalClosed.uncurry (comp ≫ fnl) = (M ◁ comp) ≫ rnl :=
    (MonoidalClosed.uncurry_natural_left comp fnl).trans
      (congrArg (fun z => (M ◁ comp) ≫ z) hnl)
  have hRight : MonoidalClosed.uncurry ((fnk ⊗ₘ fkl) ≫ eComp PointedCGWH.{u, v} M Y Z) =
      (α_ M H K).inv ≫ (rnk ▷ K) ≫ rkl := by
    simpa only [hnk, hkl] using MonoidalClosed.uncurry_eComp fnk fkl
  apply MonoidalClosed.uncurry_injective
  exact hLeft.trans ((reverseOperatorAction_comp X t ha n k l).trans hRight.symm)

omit ha

/-- Every original canonical diagram has the same entire reverse composition action. -/
theorem original_reverseOperatorAction_comp
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (n k l : OrthogonalIndex) :
    (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj n ◁
      eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l)) ≫
      reverseOperatorAction.{u, v} ((restrictionFunctor.{u, v}).obj F)
        (sphereTransformation.{u, v} F) n l =
    (α_ (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj n)
      (OrthogonalOperatorIndex.hom.{u, v} n k) (OrthogonalOperatorIndex.hom.{u, v} k l)).inv ≫
      (reverseOperatorAction.{u, v} ((restrictionFunctor.{u, v}).obj F)
        (sphereTransformation.{u, v} F) n k ▷ OrthogonalOperatorIndex.hom.{u, v} k l) ≫
      reverseOperatorAction.{u, v} ((restrictionFunctor.{u, v}).obj F)
        (sphereTransformation.{u, v} F) k l :=
  reverseOperatorAction_comp ((restrictionFunctor.{u, v}).obj F) (sphereTransformation.{u, v} F)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc F) n k l

/-- Original canonical restrictions retain the actual full reverse enriched composition equation. -/
theorem original_reverseOperatorMapField_comp
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (n k l : OrthogonalIndex) :
    eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) (OrthogonalOperatorIndex.ofIndex.{u, v} l) ≫
        reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F)
          (sphereTransformation.{u, v} F) n l =
    (reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F)
      (sphereTransformation.{u, v} F) n k ⊗ₘ
        reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F)
          (sphereTransformation.{u, v} F) k l) ≫
      eComp PointedCGWH.{u, v} (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))
        (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k))
        (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} l)) :=
  reverseOperatorMapField_comp ((restrictionFunctor.{u, v}).obj F) (sphereTransformation.{u, v} F)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc F) n k l

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceCompositionCompatibility
