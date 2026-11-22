/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornTensorAction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Native pointed coproduct actions for arbitrary horn tensors

The actual native pointed coproduct and preservation by fixed-left smash assemble
the original component actions. The coefficient objects are arbitrary. Both
endpoints and the full source-fixing equation retain the selected constraints.
For an empty family the endpoint composites are identities; the interval action
itself is the canonical map from its tensor domain, not an identity of the target.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace PointedCGWH

private def coproductIntervalAction {J : Type v} (I : PointedCGWH.{u, v})
    (B : J → PointedCGWH.{u, v}) (H : ∀ a, I ⊗ B a ⟶ B a) :
    I ⊗ (∐ B) ⟶ ∐ B :=
  (isColimitOfHasCoproductOfPreservesColimit (tensorLeft I) B).desc
    (Cofan.mk _ (fun a => H a ≫ Limits.Sigma.ι B a))

private theorem coproductIntervalAction_ι {J : Type v} (I : PointedCGWH.{u, v})
    (B : J → PointedCGWH.{u, v}) (H : ∀ a, I ⊗ B a ⟶ B a) (a : J) :
    (I ◁ Limits.Sigma.ι B a) ≫ coproductIntervalAction I B H = H a ≫ Limits.Sigma.ι B a := by
  exact (isColimitOfHasCoproductOfPreservesColimit (tensorLeft I) B).fac
    (Cofan.mk _ (fun a => H a ≫ Limits.Sigma.ι B a)) (Discrete.mk a)

private theorem coproductIntervalAction_endpoint {J : Type v}
    (I : PointedCGWH.{u, v}) (B : J → PointedCGWH.{u, v})
    (H : ∀ a, I ⊗ B a ⟶ B a) (e : 𝟙_ PointedCGWH.{u, v} ⟶ I)
    (f : ∀ a, B a ⟶ B a)
    (he : ∀ a, (λ_ (B a)).inv ≫ (e ▷ B a) ≫ H a = f a) :
    (λ_ (∐ B)).inv ≫ (e ▷ (∐ B)) ≫ coproductIntervalAction I B H = Limits.Sigma.map f := by
  apply Limits.Sigma.hom_ext
  intro a
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  rw [coproductIntervalAction_ι]
  simpa only [Category.assoc, Limits.Sigma.ι_map] using
    congrArg (fun g : B a ⟶ B a => g ≫ Limits.Sigma.ι B a) (he a)

private theorem coproductIntervalAction_fix {J : Type v}
    (I : PointedCGWH.{u, v}) (A B : J → PointedCGWH.{u, v})
    (H : ∀ a, I ⊗ B a ⟶ B a) (j : ∀ a, A a ⟶ B a)
    (c : I ⟶ 𝟙_ PointedCGWH.{u, v})
    (hfix : ∀ a, (I ◁ j a) ≫ H a = (c ▷ A a) ≫ (λ_ (A a)).hom ≫ j a) :
    (I ◁ Limits.Sigma.map j) ≫ coproductIntervalAction I B H =
      (c ▷ (∐ A)) ≫ (λ_ (∐ A)).hom ≫ Limits.Sigma.map j := by
  apply (isColimitOfHasCoproductOfPreservesColimit (tensorLeft I) A).hom_ext
  rintro ⟨a⟩
  change (I ◁ Limits.Sigma.ι A a) ≫ (I ◁ Limits.Sigma.map j) ≫ coproductIntervalAction I B H =
    (I ◁ Limits.Sigma.ι A a) ≫ (c ▷ (∐ A)) ≫ (λ_ (∐ A)).hom ≫ Limits.Sigma.map j
  calc
    _ = (I ◁ j a) ≫ (I ◁ Limits.Sigma.ι B a) ≫ coproductIntervalAction I B H := by
      rw [← whiskerLeft_comp_assoc, Limits.Sigma.ι_map, whiskerLeft_comp_assoc]
    _ = (I ◁ j a) ≫ H a ≫ Limits.Sigma.ι B a := by
      rw [coproductIntervalAction_ι]
    _ = (c ▷ A a) ≫ (λ_ (A a)).hom ≫ j a ≫ Limits.Sigma.ι B a := by
      simpa only [Category.assoc] using
        congrArg (fun g : I ⊗ A a ⟶ B a => g ≫ Limits.Sigma.ι B a) (hfix a)
    _ = _ := by
      rw [whisker_exchange_assoc, leftUnitor_naturality_assoc, Limits.Sigma.ι_map]

variable (J : Type v) (n : J → ℕ) (i : ∀ a, Fin (n a + 2))
  (K : J → PointedCGWH.{u, v})

/-- The actual native coproduct of freely pointed horn tensors. -/
def freePointHornTensorCoproductSource : PointedCGWH.{u, v} :=
  ∐ fun a => (Under.costar CGWH.point.{u, v}).obj
    (SSet.toCGWHOfFinite (SSet.horn.{v} (n a + 1) (i a))) ⊗ K a

/-- The actual native coproduct of freely pointed simplex tensors. -/
def freePointHornTensorCoproductTarget : PointedCGWH.{u, v} :=
  ∐ fun a => (Under.costar CGWH.point.{u, v}).obj
    (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a

/-- The actual coproduct of the original tensor horn inclusions. -/
def freePointHornTensorCoproductInclusion :
    freePointHornTensorCoproductSource J n i K ⟶ freePointHornTensorCoproductTarget J n K :=
  Limits.Sigma.map (fun a =>
    (Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
      𝟙 (K a))

/-- The coproduct of the original tensor retractions, with its original source and target. -/
def freePointHornTensorCoproductRetraction :
    freePointHornTensorCoproductTarget J n K ⟶ freePointHornTensorCoproductSource J n i K :=
  Limits.Sigma.map (fun a => freePointHornRetraction (n a) (i a) ⊗ₘ 𝟙 (K a))

/-- Assemble the complete component action through the preserved native coproduct. -/
def freePointHornTensorCoproductIntervalAction :
    (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval ⊗
        freePointHornTensorCoproductTarget J n K ⟶ freePointHornTensorCoproductTarget J n K :=
  (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft ((Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval))
    (fun a => (Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a)).desc
        (Cofan.mk _ (fun a => freePointHornTensorIntervalAction (n a) (i a) (K a) ≫
          Limits.Sigma.ι (fun a => (Under.costar CGWH.point.{u, v}).obj
            (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a) a))

/-- The action retains its full original component formula on each actual coproduct injection. -/
theorem freePointHornTensorCoproductIntervalAction_ι (a : J) :
    ((Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval ◁
      Limits.Sigma.ι (fun a => (Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a) a) ≫
      freePointHornTensorCoproductIntervalAction J n i K =
        freePointHornTensorIntervalAction (n a) (i a) (K a) ≫
          Limits.Sigma.ι (fun a => (Under.costar CGWH.point.{u, v}).obj
            (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a) a :=
  coproductIntervalAction_ι _ _ _ a

/-- The actual coproduct retraction is a strict left inverse of the actual attaching map. -/
theorem freePointHornTensorCoproduct_inclusion_ret :
    freePointHornTensorCoproductInclusion J n i K ≫
      freePointHornTensorCoproductRetraction J n i K = 𝟙 _ := by
  unfold freePointHornTensorCoproductInclusion freePointHornTensorCoproductRetraction
  unfold freePointHornTensorCoproductSource freePointHornTensorCoproductTarget
  erw [Limits.Sigma.map_comp_map]
  simp only [freePointHornTensor_inclusion_ret, Limits.Sigma.map_id]

/-- At zero, the complete coproduct action has the identity endpoint. -/
theorem freePointHornTensorCoproductIntervalAction_zero :
    (λ_ (freePointHornTensorCoproductTarget J n K)).inv ≫
      (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫
        freePointHornTensorCoproductIntervalAction J n i K = 𝟙 _ := by
  rw [tensorHom_id]
  change (λ_ _).inv ≫ (freePointIntervalEndpoint 0 ▷ _) ≫
    coproductIntervalAction _ _ (fun a => freePointHornTensorIntervalAction (n a) (i a) (K a)) =
      𝟙 _
  rw [coproductIntervalAction_endpoint _ _ _ _ (fun _ => 𝟙 _)
    (fun a => by simpa only [tensorHom_id] using
      freePointHornTensorIntervalAction_zero (n a) (i a) (K a))]
  exact Limits.Sigma.map_id

/-- At one, the full endpoint is the original coproduct retraction followed by inclusion. -/
theorem freePointHornTensorCoproductIntervalAction_one :
    (λ_ (freePointHornTensorCoproductTarget J n K)).inv ≫
      (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫
        freePointHornTensorCoproductIntervalAction J n i K =
      freePointHornTensorCoproductRetraction J n i K ≫
        freePointHornTensorCoproductInclusion J n i K := by
  rw [tensorHom_id]
  change (λ_ _).inv ≫ (freePointIntervalEndpoint 1 ▷ _) ≫
    coproductIntervalAction _ _ (fun a => freePointHornTensorIntervalAction (n a) (i a) (K a)) = _
  rw [coproductIntervalAction_endpoint _ _ _ _
    (fun a => (freePointHornRetraction (n a) (i a) ⊗ₘ 𝟙 (K a)) ≫
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)))
    (fun a => by simpa only [tensorHom_id] using
      freePointHornTensorIntervalAction_one (n a) (i a) (K a))]
  exact (Limits.Sigma.map_comp_map _ _).symm

/-- The complete native coproduct action fixes the entire original source for all time. -/
theorem freePointHornTensorCoproductIntervalAction_fix :
    (𝟙 _ ⊗ₘ freePointHornTensorCoproductInclusion J n i K) ≫
      freePointHornTensorCoproductIntervalAction J n i K =
        (freePointIntervalCollapse ⊗ₘ 𝟙 _) ≫
          (λ_ (freePointHornTensorCoproductSource J n i K)).hom ≫
            freePointHornTensorCoproductInclusion J n i K := by
  rw [id_tensorHom, tensorHom_id]
  change (_ ◁ Limits.Sigma.map _) ≫ coproductIntervalAction _ _ _ =
    (freePointIntervalCollapse ▷ _) ≫ (λ_ _).hom ≫ Limits.Sigma.map _
  exact coproductIntervalAction_fix _ _ _ _ _ _
    (fun a => by simpa only [id_tensorHom, tensorHom_id] using
      freePointHornTensorIntervalAction_fix (n a) (i a) (K a))

/-- For the empty family, the actual retraction is also right inverse on the selected target. -/
theorem freePointHornTensorCoproduct_ret_inclusion_empty [IsEmpty J] :
    freePointHornTensorCoproductRetraction J n i K ≫
      freePointHornTensorCoproductInclusion J n i K = 𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro a
  exact isEmptyElim a

/-- The empty-family action is the unique map from its preserved empty-coproduct tensor domain. -/
theorem freePointHornTensorCoproductIntervalAction_empty [IsEmpty J]
    (H : (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval ⊗
      freePointHornTensorCoproductTarget J n K ⟶ freePointHornTensorCoproductTarget J n K) :
    H = freePointHornTensorCoproductIntervalAction J n i K := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft ((Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval))
    (fun a => (Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a)).hom_ext
  rintro ⟨a⟩
  exact isEmptyElim a

end PointedCGWH
