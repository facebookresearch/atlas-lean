/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Op
public import
  MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedExtraDegeneracyRev
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Basic
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.IntervalPrism
public import Mathlib.Topology.Homotopy.Equiv

import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Topology.Homeomorph.Lemmas
import MathlibExt.Topology.Convenient.QuotientProduct

/-!
# Realized simplicial homotopies and extra degeneracies

This file realizes simplicial homotopies continuously, proves realization
invariant under simplex-coordinate reversal, and packages left- and
right-handed augmented extra degeneracies as homotopy equivalences.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial Topology MonoidalCategory

open scoped Simplicial

universe u

namespace TopCat.SimplicialRealization.DegreePrismCore
private noncomputable def homotopyCell
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ)
    (j : Fin (n + 1)) :
    X.obj (op ⦋n⦌) ⊗ SimplexCategory.toTop.obj ⦋n + 1⦌ ⟶
      simplicialRealization.obj Y :=
  (H.h j ⊗ₘ 𝟙 _) ≫ ι Y ⦋n + 1⦌

private theorem homotopyCell_face
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ)
    (j : Fin (n + 1)) {m : ℕ} (α : ⦋m⦌ ⟶ ⦋n + 1⦌) :
    (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ SimplexCategory.toTop.map α) ≫
        homotopyCell H n j =
      ((H.h j ≫ Y.map α.op) ⊗ₘ
          𝟙 (SimplexCategory.toTop.obj ⦋m⦌)) ≫
        ι Y ⦋m⦌ := by
  calc
    (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ SimplexCategory.toTop.map α) ≫
          homotopyCell H n j =
        ((𝟙 _ ⊗ₘ SimplexCategory.toTop.map α) ≫
          (H.h j ⊗ₘ 𝟙 _)) ≫ ι Y ⦋n + 1⦌ := by
      simp only [homotopyCell, Category.assoc]
    _ = (H.h j ⊗ₘ SimplexCategory.toTop.map α) ≫
          ι Y ⦋n + 1⦌ := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      rw [Category.id_comp, Category.comp_id]
    _ = (H.h j ⊗ₘ 𝟙 _) ≫
          ((𝟙 _ ⊗ₘ SimplexCategory.toTop.map α) ≫
            ι Y ⦋n + 1⦌) := by
      rw [← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom]
      rw [Category.comp_id, Category.id_comp]
    _ = (H.h j ⊗ₘ 𝟙 _) ≫
          ((Y.map α.op ⊗ₘ 𝟙 _) ≫ ι Y ⦋m⦌) := by
      rw [ι_condition]
    _ = ((H.h j ≫ Y.map α.op) ⊗ₘ 𝟙 _) ≫
          ι Y ⦋m⦌ := by
      rw [← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom]
      rw [Category.comp_id]

private theorem homotopyCell_adjacent
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) {n : ℕ} (j : Fin (n + 1)) :
    (𝟙 (X.obj (op ⦋n + 1⦌)) ⊗ₘ
        SimplexCategory.toTop.map (SimplexCategory.δ j.castSucc.succ)) ≫
        homotopyCell H (n + 1) j.castSucc =
      (𝟙 (X.obj (op ⦋n + 1⦌)) ⊗ₘ
        SimplexCategory.toTop.map (SimplexCategory.δ j.castSucc.succ)) ≫
        homotopyCell H (n + 1) j.succ := by
  rw [homotopyCell_face, homotopyCell_face]
  change ((H.h j.castSucc ≫ Y.δ j.castSucc.succ) ⊗ₘ 𝟙 _) ≫ _ =
    ((H.h j.succ ≫ Y.δ j.castSucc.succ) ⊗ₘ 𝟙 _) ≫ _
  rw [H.h_succ_comp_δ_castSucc_succ j]

private theorem homotopyCell_zero
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
        SimplexCategory.toTop.map
          (SimplexCategory.δ (Fin.last (n + 1)))) ≫
        homotopyCell H n (Fin.last n) =
      (f.app (op ⦋n⦌) ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj ⦋n⦌)) ≫ ι Y ⦋n⦌ := by
  rw [homotopyCell_face]
  change ((H.h (Fin.last n) ≫ Y.δ (Fin.last (n + 1))) ⊗ₘ 𝟙 _) ≫ _ = _
  rw [H.h_last_comp_δ_last]

private theorem homotopyCell_one
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
        SimplexCategory.toTop.map (SimplexCategory.δ 0)) ≫
        homotopyCell H n 0 =
      (g.app (op ⦋n⦌) ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj ⦋n⦌)) ≫ ι Y ⦋n⦌ := by
  rw [homotopyCell_face]
  change ((H.h 0 ≫ Y.δ 0) ⊗ₘ 𝟙 _) ≫ _ = _
  rw [H.h_zero_comp_δ_zero]

private theorem homotopyCell_compatible
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    ∀ i : Fin n,
      (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
          SimplexCategory.toTop.map
            (SimplexCategory.δ i.castSucc.succ)) ≫
          homotopyCell H n i.castSucc =
        (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
          SimplexCategory.toTop.map
            (SimplexCategory.δ i.castSucc.succ)) ≫
          homotopyCell H n i.succ := by
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ n => exact fun i => homotopyCell_adjacent H i

private noncomputable def degreePrism
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    X.obj (op ⦋n⦌) ⊗
        (SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u}) ⟶
      simplicialRealization.obj Y :=
  TopCat.IntervalPrism.desc n (homotopyCell H n)
    (homotopyCell_compatible H n)

private theorem degreePrism_cell
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ)
    (i : Fin (n + 1)) :
    (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ TopCat.IntervalPrism.cell.{u} n i) ≫
        degreePrism H n =
      homotopyCell H n i :=
  TopCat.IntervalPrism.cell_desc n (homotopyCell H n)
    (homotopyCell_compatible H n) i

private theorem degreePrism_zero
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
        (TopCat.ι₀ : SimplexCategory.toTop.obj ⦋n⦌ ⟶
          SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u})) ≫
        degreePrism H n =
      (f.app (op ⦋n⦌) ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj ⦋n⦌)) ≫ ι Y ⦋n⦌ := by
  rw [degreePrism, TopCat.IntervalPrism.zero_desc]
  exact homotopyCell_zero H n

private theorem degreePrism_one
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
        (TopCat.ι₁ : SimplexCategory.toTop.obj ⦋n⦌ ⟶
          SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u})) ≫
        degreePrism H n =
      (g.app (op ⦋n⦌) ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj ⦋n⦌)) ≫ ι Y ⦋n⦌ := by
  rw [degreePrism, TopCat.IntervalPrism.one_desc]
  exact homotopyCell_one H n
end TopCat.SimplicialRealization.DegreePrismCore
namespace TopCat.DegreePrismNaturality

open TopCat.SimplicialRealization.DegreePrismCore

private abbrev prismD (n : ℕ) : TopCat.{u} :=
  SimplexCategory.toTop.{u}.obj ⦋n⦌

private abbrev degreeNaturality
    {X Y : SimplicialObject TopCat.{u}}
    (degree : ∀ n : ℕ,
      X _⦋n⦌ ⊗ (prismD.{u} n ⊗ TopCat.I.{u}) ⟶
        simplicialRealization.obj Y)
    {m n : SimplexCategory} (α : m ⟶ n) : Prop :=
  (X.map α.op ⊗ₘ 𝟙 (prismD.{u} m.len ⊗ TopCat.I.{u})) ≫
      degree m.len =
    (𝟙 (X.obj (op n)) ⊗ₘ
      (SimplexCategory.toTop.map α ⊗ₘ 𝟙 TopCat.I.{u})) ≫
      degree n.len

private theorem tensor_cell_left
    {X : SimplicialObject TopCat.{u}}
    {m n : SimplexCategory} (α : m ⟶ n)
    (p : ℕ) (j : Fin (p + 1)) :
    (𝟙 (X.obj (op n)) ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫
        (X.map α.op ⊗ₘ 𝟙 (prismD.{u} p ⊗ TopCat.I.{u})) =
      (X.map α.op ⊗ₘ 𝟙 (prismD.{u} (p + 1))) ≫
        (𝟙 (X.obj (op m)) ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

private theorem tensor_cell_delta_le
    (A : TopCat.{u}) (p : ℕ) (i : Fin (p + 2))
    (j : Fin (p + 1)) (hij : i ≤ j.castSucc) :
    (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫
        (𝟙 A ⊗ₘ (SimplexCategory.toTop.map
          (SimplexCategory.δ i) ⊗ₘ 𝟙 TopCat.I.{u})) =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.map
        (SimplexCategory.δ i.castSucc)) ≫
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} (p + 1) j.succ) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  change 𝟙 A ⊗ₘ (TopCat.IntervalPrism.cell.{u} p j ≫
      (SimplexCategory.toTop.map (SimplexCategory.δ i) ▷ TopCat.I)) =
    𝟙 A ⊗ₘ (SimplexCategory.toTop.map
      (SimplexCategory.δ i.castSucc) ≫ TopCat.IntervalPrism.cell.{u} (p + 1) j.succ)
  rw [TopCat.IntervalPrism.Internal.cell_δ_of_le p i j hij]

private theorem tensor_cell_delta_gt
    (A : TopCat.{u}) (p : ℕ) (i : Fin (p + 2))
    (j : Fin (p + 1)) (hji : j.castSucc < i) :
    (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫
        (𝟙 A ⊗ₘ (SimplexCategory.toTop.map
          (SimplexCategory.δ i) ⊗ₘ 𝟙 TopCat.I.{u})) =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.map
        (SimplexCategory.δ i.succ)) ≫
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} (p + 1) j.castSucc) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  change 𝟙 A ⊗ₘ (TopCat.IntervalPrism.cell.{u} p j ≫
      (SimplexCategory.toTop.map (SimplexCategory.δ i) ▷ TopCat.I)) =
    𝟙 A ⊗ₘ (SimplexCategory.toTop.map
      (SimplexCategory.δ i.succ) ≫ TopCat.IntervalPrism.cell.{u} (p + 1) j.castSucc)
  rw [TopCat.IntervalPrism.Internal.cell_δ_of_gt p i j hji]

private theorem tensor_cell_sigma_le
    (A : TopCat.{u}) (p : ℕ) (i j : Fin (p + 1)) (hij : i ≤ j) :
    (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} (p + 1) j.succ) ≫
        (𝟙 A ⊗ₘ (SimplexCategory.toTop.map
          (SimplexCategory.σ i) ⊗ₘ 𝟙 TopCat.I.{u})) =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.map
        (SimplexCategory.σ i.castSucc)) ≫
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  change 𝟙 A ⊗ₘ (TopCat.IntervalPrism.cell.{u} (p + 1) j.succ ≫
      (SimplexCategory.toTop.map (SimplexCategory.σ i) ▷ TopCat.I)) =
    𝟙 A ⊗ₘ (SimplexCategory.toTop.map
      (SimplexCategory.σ i.castSucc) ≫ TopCat.IntervalPrism.cell.{u} p j)
  rw [TopCat.IntervalPrism.Internal.cell_σ_of_le p i j hij]

private theorem tensor_cell_sigma_ge
    (A : TopCat.{u}) (p : ℕ) (i j : Fin (p + 1)) (hji : j ≤ i) :
    (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} (p + 1) j.castSucc) ≫
        (𝟙 A ⊗ₘ (SimplexCategory.toTop.map
          (SimplexCategory.σ i) ⊗ₘ 𝟙 TopCat.I.{u})) =
      (𝟙 A ⊗ₘ SimplexCategory.toTop.map
        (SimplexCategory.σ i.succ)) ≫
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  change 𝟙 A ⊗ₘ (TopCat.IntervalPrism.cell.{u} (p + 1) j.castSucc ≫
      (SimplexCategory.toTop.map (SimplexCategory.σ i) ▷ TopCat.I)) =
    𝟙 A ⊗ₘ (SimplexCategory.toTop.map
      (SimplexCategory.σ i.succ) ≫ TopCat.IntervalPrism.cell.{u} p j)
  rw [TopCat.IntervalPrism.Internal.cell_σ_of_ge p i j hji]

private theorem delta_naturality
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g)
    (degree : ∀ n : ℕ,
      X _⦋n⦌ ⊗ (prismD.{u} n ⊗ TopCat.I.{u}) ⟶
        simplicialRealization.obj Y)
    (hdegree : ∀ (n : ℕ) (j : Fin (n + 1)),
      (𝟙 (X _⦋n⦌) ⊗ₘ TopCat.IntervalPrism.cell.{u} n j) ≫ degree n =
        homotopyCell H n j)
    (hcellExt : ∀ {A Z : TopCat.{u}} (p : ℕ)
      {r s : A ⊗ (prismD.{u} p ⊗ TopCat.I.{u}) ⟶ Z},
      (∀ j : Fin (p + 1),
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫ r =
          (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫ s) → r = s)
    {p : ℕ} (i : Fin (p + 2)) :
    degreeNaturality degree (SimplexCategory.δ i) := by
  apply hcellExt p
  intro j
  rw [← Category.assoc, tensor_cell_left, Category.assoc, hdegree]
  by_cases hij : i ≤ j.castSucc
  · rw [← Category.assoc,
      tensor_cell_delta_le (X _⦋p + 1⦌) p i j hij,
      Category.assoc, hdegree]
    rw [homotopyCell_face]
    unfold homotopyCell
    rw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
    have hH := H.h_succ_comp_δ_castSucc_of_lt i j hij
    change H.h j.succ ≫ Y.map (SimplexCategory.δ i.castSucc).op =
      X.map (SimplexCategory.δ i).op ≫ H.h j at hH
    rw [← hH]
  · have hji : j.castSucc < i := by omega
    rw [← Category.assoc,
      tensor_cell_delta_gt (X _⦋p + 1⦌) p i j hji,
      Category.assoc, hdegree]
    rw [homotopyCell_face]
    unfold homotopyCell
    rw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
    have hH := H.h_castSucc_comp_δ_succ_of_lt i j hji
    change H.h j.castSucc ≫ Y.map (SimplexCategory.δ i.succ).op =
      X.map (SimplexCategory.δ i).op ≫ H.h j at hH
    rw [← hH]

private theorem sigma_naturality
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g)
    (degree : ∀ n : ℕ,
      X _⦋n⦌ ⊗ (prismD.{u} n ⊗ TopCat.I.{u}) ⟶
        simplicialRealization.obj Y)
    (hdegree : ∀ (n : ℕ) (j : Fin (n + 1)),
      (𝟙 (X _⦋n⦌) ⊗ₘ TopCat.IntervalPrism.cell.{u} n j) ≫ degree n =
        homotopyCell H n j)
    (hcellExt : ∀ {A Z : TopCat.{u}} (p : ℕ)
      {r s : A ⊗ (prismD.{u} p ⊗ TopCat.I.{u}) ⟶ Z},
      (∀ j : Fin (p + 1),
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫ r =
          (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫ s) → r = s)
    {p : ℕ} (i : Fin (p + 1)) :
    degreeNaturality degree (SimplexCategory.σ i) := by
  apply hcellExt (p + 1)
  intro j
  rw [← Category.assoc, tensor_cell_left, Category.assoc, hdegree]
  by_cases hji : j ≤ i.castSucc
  · have hjlast : j ≠ Fin.last (p + 1) :=
      Fin.ne_last_of_lt (hji.trans_lt i.castSucc_lt_last)
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last hjlast
    have hji' : j ≤ i := Fin.castSucc_le_castSucc_iff.mp hji
    rw [← Category.assoc,
      tensor_cell_sigma_ge (X _⦋p⦌) p i j hji',
      Category.assoc, hdegree]
    rw [homotopyCell_face]
    unfold homotopyCell
    rw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
    have hH := H.h_comp_σ_succ_of_lt i j hji'
    change H.h j ≫ Y.map (SimplexCategory.σ i.succ).op =
      X.map (SimplexCategory.σ i).op ≫ H.h j.castSucc at hH
    rw [← hH]
  · have hij : i.castSucc < j := lt_of_not_ge hji
    have hjzero : j ≠ 0 := Fin.ne_zero_of_lt hij
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hjzero
    have hij' : i ≤ j := Fin.castSucc_lt_succ_iff.mp hij
    rw [← Category.assoc,
      tensor_cell_sigma_le (X _⦋p⦌) p i j hij',
      Category.assoc, hdegree]
    rw [homotopyCell_face]
    unfold homotopyCell
    rw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
    have hH := H.h_comp_σ_castSucc_of_le i j hij'
    change H.h j ≫ Y.map (SimplexCategory.σ i.castSucc).op =
      X.map (SimplexCategory.σ i).op ≫ H.h j.succ at hH
    rw [← hH]

private theorem degree_naturality
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g)
    (degree : ∀ n : ℕ,
      X _⦋n⦌ ⊗ (prismD.{u} n ⊗ TopCat.I.{u}) ⟶
        simplicialRealization.obj Y)
    (hdegree : ∀ (n : ℕ) (j : Fin (n + 1)),
      (𝟙 (X _⦋n⦌) ⊗ₘ TopCat.IntervalPrism.cell.{u} n j) ≫ degree n =
        homotopyCell H n j)
    (hcellExt : ∀ {A Z : TopCat.{u}} (p : ℕ)
      {r s : A ⊗ (prismD.{u} p ⊗ TopCat.I.{u}) ⟶ Z},
      (∀ j : Fin (p + 1),
        (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫ r =
          (𝟙 A ⊗ₘ TopCat.IntervalPrism.cell.{u} p j) ≫ s) → r = s)
    {m n : SimplexCategory} (α : m ⟶ n) :
    degreeNaturality degree α := by
  let W : MorphismProperty SimplexCategory :=
    fun _ _ β ↦ degreeNaturality degree β
  let hmul : W.IsMultiplicative :=
    { id_mem := fun q ↦ by
        induction q using SimplexCategory.rec
        rename_i p
        dsimp only [W, degreeNaturality]
        change (X.map (𝟙 (op ⦋p⦌)) ⊗ₘ
              𝟙 (prismD.{u} p ⊗ TopCat.I.{u})) ≫ degree p =
          (𝟙 (X _⦋p⦌) ⊗ₘ
              (SimplexCategory.toTop.map (𝟙 ⦋p⦌) ⊗ₘ
                𝟙 TopCat.I.{u})) ≫ degree p
        rw [X.map_id]
        rw [SimplexCategory.toTop.map_id]
        simp
      comp_mem := fun {A B C} a b ha hb ↦ by
        dsimp only [W, degreeNaturality] at ha hb ⊢
        rw [Functor.map_comp, op_comp, Functor.map_comp]
        calc
          ((X.map b.op ≫ X.map a.op) ⊗ₘ
                𝟙 (prismD.{u} A.len ⊗ TopCat.I.{u})) ≫
              degree A.len =
            (X.map b.op ⊗ₘ
                𝟙 (prismD.{u} A.len ⊗ TopCat.I.{u})) ≫
              ((X.map a.op ⊗ₘ
                  𝟙 (prismD.{u} A.len ⊗ TopCat.I.{u})) ≫
                degree A.len) := by
            rw [← Category.assoc,
              MonoidalCategory.tensorHom_comp_tensorHom]
            simp
          _ = (X.map b.op ⊗ₘ
                𝟙 (prismD.{u} A.len ⊗ TopCat.I.{u})) ≫
              ((𝟙 (X.obj (op B)) ⊗ₘ
                  (SimplexCategory.toTop.map a ⊗ₘ 𝟙 TopCat.I.{u})) ≫
                degree B.len) := by rw [ha]
          _ = (𝟙 (X.obj (op C)) ⊗ₘ
                (SimplexCategory.toTop.map a ⊗ₘ 𝟙 TopCat.I.{u})) ≫
              ((X.map b.op ⊗ₘ
                  𝟙 (prismD.{u} B.len ⊗ TopCat.I.{u})) ≫
                degree B.len) := by
            rw [← Category.assoc, ← Category.assoc,
              MonoidalCategory.tensorHom_comp_tensorHom,
              MonoidalCategory.tensorHom_comp_tensorHom]
            simp
          _ = (𝟙 (X.obj (op C)) ⊗ₘ
                (SimplexCategory.toTop.map a ⊗ₘ 𝟙 TopCat.I.{u})) ≫
              ((𝟙 (X.obj (op C)) ⊗ₘ
                  (SimplexCategory.toTop.map b ⊗ₘ 𝟙 TopCat.I.{u})) ≫
                degree C.len) := by rw [hb]
          _ = (𝟙 (X.obj (op C)) ⊗ₘ
                ((SimplexCategory.toTop.map a ≫
                    SimplexCategory.toTop.map b) ⊗ₘ 𝟙 TopCat.I.{u})) ≫
              degree C.len := by
            rw [← Category.assoc,
              MonoidalCategory.tensorHom_comp_tensorHom,
              MonoidalCategory.tensorHom_comp_tensorHom]
            simp }
  have hW : W = ⊤ := @SimplexCategory.morphismProperty_eq_top W hmul
    (fun i ↦ delta_naturality H degree hdegree hcellExt i)
    (fun i ↦ sigma_naturality H degree hdegree hcellExt i)
  change W α
  rw [hW]
  trivial

end TopCat.DegreePrismNaturality

namespace TopCat.DegreePrismComplete

open TopCat.SimplicialRealization.DegreePrismCore

private theorem degreePrism_naturality
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g)
    {m n : SimplexCategory} (α : m ⟶ n) :
    (X.map α.op ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj m ⊗ TopCat.I.{u})) ≫
      TopCat.SimplicialRealization.DegreePrismCore.degreePrism H m.len =
    (𝟙 (X.obj (op n)) ⊗ₘ
        (SimplexCategory.toTop.map α ⊗ₘ 𝟙 TopCat.I.{u})) ≫
      TopCat.SimplicialRealization.DegreePrismCore.degreePrism H n.len := by
  exact TopCat.DegreePrismNaturality.degree_naturality H
    (TopCat.SimplicialRealization.DegreePrismCore.degreePrism H)
    (TopCat.SimplicialRealization.DegreePrismCore.degreePrism_cell H)
    (fun p _ _ h => TopCat.IntervalPrism.Internal.cell_hom_ext p h) α

end TopCat.DegreePrismComplete

namespace TopCat.SimplicialRealization

private abbrev presentationFamily
    (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) : TopCat.{u} :=
  X.obj (op n) ⊗ SimplexCategory.toTop.obj n
private noncomputable def degreeAssoc
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory) :
    (X.obj (op n) ⊗ SimplexCategory.toTop.{u}.obj n) ⊗
        TopCat.I.{u} ⟶
      TopCat.simplicialRealization.obj Y :=
  (α_ (X.obj (op n)) (SimplexCategory.toTop.obj n) TopCat.I).hom ≫
    TopCat.SimplicialRealization.DegreePrismCore.degreePrism H n.len

private noncomputable def sigmaPrism
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    TopCat.of (Σ n : SimplexCategory,
      (presentationFamily X n ⊗ TopCat.I.{u} : TopCat.{u})) ⟶
      TopCat.simplicialRealization.obj Y :=
  TopCat.ofHom
    { toFun := fun z => degreeAssoc H z.1 z.2
      continuous_toFun := continuous_sigma fun n =>
        (degreeAssoc H n).hom.continuous }

private noncomputable def tensorRawProdHom (A B : TopCat.{u}) :
    A ⊗ B ⟶ TopCat.of (A × B) :=
  TopCat.ofHom
    { toFun := fun z => (z.1, z.2)
      continuous_toFun :=
        (CartesianMonoidalCategory.fst A B).hom.continuous.prodMk
          (CartesianMonoidalCategory.snd A B).hom.continuous }

private noncomputable def sigmaProdDistribHom
    (X : SimplicialObject TopCat.{u}) :
    (TopCat.of (Σ n : SimplexCategory,
      ↑(presentationFamily X n))) ⊗ TopCat.I.{u} ⟶
      TopCat.of (Σ n : SimplexCategory,
        (presentationFamily X n ⊗ TopCat.I.{u} : TopCat.{u})) :=
  (tensorRawProdHom
      (TopCat.of (Σ n : SimplexCategory,
        ↑(presentationFamily X n))) TopCat.I) ≫
    TopCat.ofHom
      { toFun := Homeomorph.sigmaProdDistrib
          (X := fun n : SimplexCategory =>
            ↑(presentationFamily X n))
          (Y := ↑TopCat.I.{u})
        continuous_toFun := (Homeomorph.sigmaProdDistrib
          (X := fun n : SimplexCategory =>
            ↑(presentationFamily X n))
          (Y := ↑TopCat.I.{u})).continuous }

private noncomputable def presentationPrism
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    presentation X ⊗ TopCat.I.{u} ⟶
      TopCat.simplicialRealization.obj Y :=
  ((TopCat.sigmaIsoSigma (presentationFamily X)).hom ⊗ₘ 𝟙 TopCat.I) ≫
    sigmaProdDistribHom X ≫ sigmaPrism H

private theorem presentationPrism_ι
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory) :
    (Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I) ≫
        presentationPrism H =
      degreeAssoc H n := by
  simp only [presentationPrism, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
    TopCat.sigmaIsoSigma_hom_ι]
  apply TopCat.ext
  rintro ⟨x, t⟩
  change sigmaPrism H
      ((Homeomorph.sigmaProdDistrib
        (X := fun n : SimplexCategory =>
          ↑(presentationFamily X n))
        (Y := ↑TopCat.I.{u})) (⟨n, x⟩, t)) =
    degreeAssoc H n (x, t)
  rw [Homeomorph.sigmaProdDistrib_apply]
  rfl

private noncomputable def timeInclusion (A : TopCat.{u}) (t : TopCat.I.{u}) :
    A ⟶ A ⊗ TopCat.I.{u} :=
  CartesianMonoidalCategory.lift (𝟙 A) (TopCat.const t)

private theorem timeInclusion_natural {A B : TopCat.{u}}
    (h : A ⟶ B) (t : TopCat.I.{u}) :
    h ≫ timeInclusion B t =
      timeInclusion A t ≫ (h ⊗ₘ 𝟙 TopCat.I) := by
  apply TopCat.ext
  intro x
  rfl

private noncomputable def degreeAt
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory)
    (t : TopCat.I.{u}) :
    X.obj (op n) ⊗ SimplexCategory.toTop.{u}.obj n ⟶
      TopCat.simplicialRealization.obj Y :=
  timeInclusion
      (X.obj (op n) ⊗ SimplexCategory.toTop.{u}.obj n) t ≫
    degreeAssoc H n

private theorem degreeAt_condition
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g)
    {m n : SimplexCategory} (α : m ⟶ n) (t : TopCat.I.{u}) :
    (X.map α.op ⊗ₘ 𝟙 (SimplexCategory.toTop.{u}.obj m)) ≫
        degreeAt (X := X) (Y := Y) (f := f) (g := g) H m t =
      (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.{u}.map α) ≫
        degreeAt (X := X) (Y := Y) (f := f) (g := g) H n t := by
  simp only [degreeAt, degreeAssoc]
  slice_lhs 1 2 => rw [timeInclusion_natural]
  slice_rhs 1 2 => rw [timeInclusion_natural]
  slice_lhs 2 3 => rw [MonoidalCategory.associator_naturality]
  slice_rhs 2 3 => rw [MonoidalCategory.associator_naturality]
  simp only [MonoidalCategory.id_tensorHom_id]
  slice_lhs 3 4 =>
    rw [TopCat.DegreePrismComplete.degreePrism_naturality H α]
  simp only [Category.assoc]

private noncomputable def degreeAtPresentation
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory)
    (t : TopCat.I.{u}) :
    presentationFamily X n ⟶
      TopCat.simplicialRealization.obj Y :=
  timeInclusion (presentationFamily X n) t ≫ degreeAssoc H n

private theorem degreeAtPresentation_condition
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g)
    {m n : SimplexCategory} (α : m ⟶ n) (t : TopCat.I.{u}) :
    (X.map α.op ⊗ₘ 𝟙 (SimplexCategory.toTop.{u}.obj m)) ≫
        degreeAtPresentation H m t =
      (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.{u}.map α) ≫
        degreeAtPresentation H n t := by
  exact degreeAt_condition H α t

private noncomputable def realizationAt
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (t : TopCat.I.{u}) :
    TopCat.simplicialRealization.obj X ⟶
      TopCat.simplicialRealization.obj Y :=
  TopCat.SimplicialRealization.desc
    (fun n ↦ degreeAtPresentation H n t)
    (by
      intro m n α
      exact degreeAtPresentation_condition H α t)

@[reassoc]
private theorem iota_realizationAt
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (t : TopCat.I.{u})
    (n : SimplexCategory) :
    TopCat.SimplicialRealization.ι X n ≫ realizationAt H t =
      degreeAtPresentation H n t :=
  TopCat.SimplicialRealization.ι_desc _ _ n
private theorem presentationSlice
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (t : TopCat.I.{u}) :
    timeInclusion (presentation X) t ≫ presentationPrism H =
      presentationQuotient X ≫ realizationAt H t := by
  apply Limits.Sigma.hom_ext
  intro n
  have hleft :
      Limits.Sigma.ι (presentationFamily X) n ≫
          (timeInclusion (presentation X) t ≫ presentationPrism H) =
        degreeAtPresentation H n t := by
    calc
      _ = (Limits.Sigma.ι (presentationFamily X) n ≫
            timeInclusion (presentation X) t) ≫ presentationPrism H :=
        (Category.assoc _ _ _).symm
      _ = (timeInclusion (presentationFamily X n) t ≫
            (Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I)) ≫
          presentationPrism H := by
        rw [timeInclusion_natural]
      _ = timeInclusion (presentationFamily X n) t ≫
          ((Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I) ≫
            presentationPrism H) := Category.assoc _ _ _
      _ = timeInclusion (presentationFamily X n) t ≫ degreeAssoc H n := by
        rw [presentationPrism_ι]
      _ = degreeAtPresentation H n t := rfl
  have hright :
      Limits.Sigma.ι (presentationFamily X) n ≫
          (presentationQuotient X ≫ realizationAt H t) =
        degreeAtPresentation H n t := by
    have hq :
        (Limits.Sigma.ι (presentationFamily X) n ≫
            presentationQuotient X) ≫ realizationAt H t =
          TopCat.SimplicialRealization.ι X n ≫
            realizationAt H t :=
      congrArg (fun k => k ≫ realizationAt H t)
        (presentationQuotient_ι X n)
    have hq' :
        Limits.Sigma.ι (presentationFamily X) n ≫
            (presentationQuotient X ≫ realizationAt H t) =
          TopCat.SimplicialRealization.ι X n ≫
            realizationAt H t :=
      (Category.assoc _ _ _).symm.trans hq
    exact hq'.trans
      (iota_realizationAt (X := X) (Y := Y) (f := f) (g := g) H t n)
  exact hleft.trans hright.symm
private theorem presentationQuotient_tensor_interval_isQuotientMap
    (X : SimplicialObject TopCat.{u}) :
    IsQuotientMap
      (presentationQuotient X ⊗ₘ 𝟙 TopCat.I.{u}) := by
  change IsQuotientMap
    (Prod.map (presentationQuotient X)
      (id : TopCat.I.{u} → TopCat.I.{u}))
  exact (presentationQuotient_isQuotientMap X).prodMap_left

private theorem presentationPrism_factors
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    Function.FactorsThrough (presentationPrism H)
      (presentationQuotient X ⊗ₘ 𝟙 TopCat.I.{u}) := by
  rintro ⟨x, t⟩ ⟨y, s⟩ h
  have ht : t = s := congrArg Prod.snd h
  subst s
  have hx : presentationQuotient X x = presentationQuotient X y :=
    congrArg Prod.fst h
  calc
    presentationPrism H (x, t) =
        realizationAt H t (presentationQuotient X x) :=
      ConcreteCategory.congr_hom (presentationSlice H t) x
    _ = realizationAt H t (presentationQuotient X y) := congrArg _ hx
    _ = presentationPrism H (y, t) :=
      (ConcreteCategory.congr_hom (presentationSlice H t) y).symm

private noncomputable def realizationHomotopyMap
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    TopCat.simplicialRealization.obj X ⊗
        TopCat.I.{u} ⟶
      TopCat.simplicialRealization.obj Y :=
  TopCat.ofHom
    ((presentationQuotient_tensor_interval_isQuotientMap X).lift
      (presentationPrism H).hom (presentationPrism_factors H))

private theorem realizationHomotopyMap_fac
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    (presentationQuotient X ⊗ₘ 𝟙 TopCat.I.{u}) ≫
        realizationHomotopyMap H = presentationPrism H := by
  apply TopCat.ext
  intro z
  exact ContinuousMap.congr_fun
    ((presentationQuotient_tensor_interval_isQuotientMap X).lift_comp
      (presentationPrism H).hom (presentationPrism_factors H)) z

private theorem realizationHomotopyMap_iota
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory) :
    (TopCat.SimplicialRealization.ι X n ⊗ₘ
        𝟙 TopCat.I.{u}) ≫ realizationHomotopyMap H =
      degreeAssoc H n := by
  have hgen :
      (Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I.{u}) ≫
          (presentationQuotient X ⊗ₘ 𝟙 TopCat.I.{u}) =
        TopCat.SimplicialRealization.ι X n ⊗ₘ
          𝟙 TopCat.I.{u} := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
      presentationQuotient_ι]
  have hpre :
      (TopCat.SimplicialRealization.ι X n ⊗ₘ
          𝟙 TopCat.I) ≫ realizationHomotopyMap H =
        (Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I) ≫
          presentationPrism H := by
    calc
      _ = ((Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I) ≫
            (presentationQuotient X ⊗ₘ 𝟙 TopCat.I)) ≫
          realizationHomotopyMap H :=
        (congrArg (fun k => k ≫ realizationHomotopyMap H) hgen).symm
      _ = (Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I) ≫
          ((presentationQuotient X ⊗ₘ 𝟙 TopCat.I) ≫
            realizationHomotopyMap H) := Category.assoc _ _ _
      _ = (Limits.Sigma.ι (presentationFamily X) n ⊗ₘ 𝟙 TopCat.I) ≫
          presentationPrism H := by rw [realizationHomotopyMap_fac]
  exact hpre.trans
    (presentationPrism_ι (X := X) (Y := Y) (f := f) (g := g) H n)

private theorem realizationHomotopyMap_iota_degreePrism
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n : SimplexCategory) :
    (TopCat.SimplicialRealization.ι X n ⊗ₘ
        𝟙 TopCat.I.{u}) ≫ realizationHomotopyMap H =
      (α_ (X.obj (op n)) (SimplexCategory.toTop.obj n) TopCat.I).hom ≫
        TopCat.SimplicialRealization.DegreePrismCore.degreePrism H n.len := by
  exact realizationHomotopyMap_iota H n
private theorem realizationHomotopyMap_zero
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    TopCat.ι₀ ≫ realizationHomotopyMap H =
      TopCat.simplicialRealization.map f := by
  apply TopCat.SimplicialRealization.hom_ext
  intro n
  obtain ⟨n⟩ := n
  calc
    TopCat.SimplicialRealization.ι X ⦋n⦌ ≫
          TopCat.ι₀ ≫ realizationHomotopyMap H =
        TopCat.ι₀ ≫
          (TopCat.SimplicialRealization.ι X ⦋n⦌ ▷
            TopCat.I.{u}) ≫ realizationHomotopyMap H := by
      simp only [TopCat.ι₀_comp_assoc]
    _ = TopCat.ι₀ ≫
        (TopCat.SimplicialRealization.ι X ⦋n⦌ ⊗ₘ
          𝟙 TopCat.I.{u}) ≫ realizationHomotopyMap H := by
      rw [MonoidalCategory.tensorHom_id]
    _ = TopCat.ι₀ ≫
        (MonoidalCategory.associator
          (X.obj (op ⦋n⦌))
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I.{u}).hom ≫
          TopCat.SimplicialRealization.DegreePrismCore.degreePrism H n := by
      rw [realizationHomotopyMap_iota_degreePrism]
    _ = (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
          (TopCat.ι₀ : SimplexCategory.toTop.obj ⦋n⦌ ⟶
            SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u})) ≫
        TopCat.SimplicialRealization.DegreePrismCore.degreePrism H n := rfl
    _ = (f.app (op ⦋n⦌) ⊗ₘ
          𝟙 (SimplexCategory.toTop.obj ⦋n⦌)) ≫
        TopCat.SimplicialRealization.ι Y ⦋n⦌ :=
      TopCat.SimplicialRealization.DegreePrismCore.degreePrism_zero H n
    _ = TopCat.SimplicialRealization.ι X ⦋n⦌ ≫
        TopCat.simplicialRealization.map f :=
      (TopCat.SimplicialRealization.ι_map f ⦋n⦌).symm

private theorem realizationHomotopyMap_one
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    TopCat.ι₁ ≫ realizationHomotopyMap H =
      TopCat.simplicialRealization.map g := by
  apply TopCat.SimplicialRealization.hom_ext
  intro n
  obtain ⟨n⟩ := n
  calc
    TopCat.SimplicialRealization.ι X ⦋n⦌ ≫
          TopCat.ι₁ ≫ realizationHomotopyMap H =
        TopCat.ι₁ ≫
          (TopCat.SimplicialRealization.ι X ⦋n⦌ ▷
            TopCat.I.{u}) ≫ realizationHomotopyMap H := by
      simp only [TopCat.ι₁_comp_assoc]
    _ = TopCat.ι₁ ≫
        (TopCat.SimplicialRealization.ι X ⦋n⦌ ⊗ₘ
          𝟙 TopCat.I.{u}) ≫ realizationHomotopyMap H := by
      rw [MonoidalCategory.tensorHom_id]
    _ = TopCat.ι₁ ≫
        (MonoidalCategory.associator
          (X.obj (op ⦋n⦌))
          (SimplexCategory.toTop.obj ⦋n⦌) TopCat.I.{u}).hom ≫
          TopCat.SimplicialRealization.DegreePrismCore.degreePrism H n := by
      rw [realizationHomotopyMap_iota_degreePrism]
    _ = (𝟙 (X.obj (op ⦋n⦌)) ⊗ₘ
          (TopCat.ι₁ : SimplexCategory.toTop.obj ⦋n⦌ ⟶
            SimplexCategory.toTop.obj ⦋n⦌ ⊗ TopCat.I.{u})) ≫
        TopCat.SimplicialRealization.DegreePrismCore.degreePrism H n := rfl
    _ = (g.app (op ⦋n⦌) ⊗ₘ
          𝟙 (SimplexCategory.toTop.obj ⦋n⦌)) ≫
        TopCat.SimplicialRealization.ι Y ⦋n⦌ :=
      TopCat.SimplicialRealization.DegreePrismCore.degreePrism_one H n
    _ = TopCat.SimplicialRealization.ι X ⦋n⦌ ≫
        TopCat.simplicialRealization.map g :=
      (TopCat.SimplicialRealization.ι_map g ⦋n⦌).symm

private noncomputable def packageCylinder
    {P Y : TopCat.{u}} {f₀ f₁ : P ⟶ Y}
    (h : P ⊗ TopCat.I.{u} ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f₀) (h₁ : TopCat.ι₁ ≫ h = f₁) :
    ContinuousMap.Homotopy f₀.hom f₁.hom where
  toFun p := h (p.2, TopCat.I.homeomorph.symm p.1)
  continuous_toFun :=
    h.hom.continuous.comp
      (continuous_snd.prodMk
        (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
  map_zero_left x := by
    change (TopCat.ι₀ ≫ h) x = _
    rw [h₀]
  map_one_left x := by
    change (TopCat.ι₁ ≫ h) x = _
    rw [h₁]

noncomputable opaque realizationHomotopy
    {X Y : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) :
    ContinuousMap.Homotopy
      (TopCat.simplicialRealization.map f).hom
      (TopCat.simplicialRealization.map g).hom := by
  refine
    { toFun := fun p ↦ realizationHomotopyMap H
        (p.2, TopCat.I.homeomorph.symm p.1)
      continuous_toFun :=
        (realizationHomotopyMap H).hom.continuous.comp
          (continuous_snd.prodMk
            (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    change (TopCat.ι₀ ≫ realizationHomotopyMap H) x = _
    rw [realizationHomotopyMap_zero]
  · intro x
    change (TopCat.ι₁ ≫ realizationHomotopyMap H) x = _
    rw [realizationHomotopyMap_one]
end TopCat.SimplicialRealization

namespace TopCat.SimplicialRealization

private noncomputable def simplexRev (n : SimplexCategory) :
    SimplexCategory.toTop.{u}.obj n ⟶ SimplexCategory.toTop.obj n :=
  TopCat.ofHom
    { toFun := fun s ↦ ULift.up
        (Convexity.StdSimplex.map
          (Fin.rev : Fin (n.len + 1) → Fin (n.len + 1)) s.down)
      continuous_toFun := by fun_prop }

private theorem simplexRev_naturality {m n : SimplexCategory}
    (α : m ⟶ n) :
    SimplexCategory.toTop.{u}.map α ≫ simplexRev n =
      simplexRev m ≫
        SimplexCategory.toTop.map (SimplexCategory.rev.map α) := by
  apply TopCat.ext
  intro s
  apply ULift.down_injective
  change (s.down.map α).map Fin.rev =
    (s.down.map Fin.rev).map (SimplexCategory.rev.map α)
  rw [← Convexity.StdSimplex.map_comp,
    ← Convexity.StdSimplex.map_comp]
  congr 1
  funext i
  change (α.toOrderHom i).rev =
    (SimplexCategory.rev.map α).toOrderHom i.rev
  rw [SimplexCategory.rev_map_apply, Fin.rev_rev]

private theorem simplexRev_sq (n : SimplexCategory) :
    simplexRev.{u} n ≫ simplexRev n = 𝟙 _ := by
  apply TopCat.ext
  intro s
  apply ULift.down_injective
  change (s.down.map Fin.rev).map Fin.rev = s.down
  rw [← Convexity.StdSimplex.map_comp]
  have hrev :
      (Fin.rev ∘ Fin.rev : Fin (n.len + 1) → Fin (n.len + 1)) = id :=
    funext Fin.rev_rev
  rw [hrev, s.down.map_id]

private noncomputable def opGenerator
    (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) :
    (SimplicialObject.opFunctor.obj X).obj (op n) ⊗
        SimplexCategory.toTop.obj n ⟶
      TopCat.simplicialRealization.obj X :=
  (SimplicialObject.opObjIso.hom ⊗ₘ simplexRev n) ≫ ι X n

private theorem opGenerator_condition
    (X : SimplicialObject TopCat.{u}) {m n : SimplexCategory}
    (α : m ⟶ n) :
    ((SimplicialObject.opFunctor.obj X).map α.op ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj m)) ≫ opGenerator X m =
      (𝟙 ((SimplicialObject.opFunctor.obj X).obj (op n)) ⊗ₘ
        SimplexCategory.toTop.map α) ≫ opGenerator X n := by
  unfold opGenerator
  simp only [SimplicialObject.opFunctor_obj_map]
  change
    (X.map (SimplexCategory.rev.map α).op ⊗ₘ simplexRev m) ≫ ι X m =
      (𝟙 (X.obj (op n)) ⊗ₘ
        (SimplexCategory.toTop.map α ≫ simplexRev n)) ≫ ι X n
  calc
    _ = (𝟙 (X.obj (op n)) ⊗ₘ simplexRev m) ≫
        (X.map (SimplexCategory.rev.map α).op ⊗ₘ 𝟙 _) ≫ ι X m := by
      rw [← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    _ = (𝟙 (X.obj (op n)) ⊗ₘ simplexRev m) ≫
        (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.map
          (SimplexCategory.rev.map α)) ≫ ι X n := by
      have hι :
          (X.map (SimplexCategory.rev.map α).op ⊗ₘ
              𝟙 (SimplexCategory.toTop.obj m)) ≫ ι X m =
            (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.map
              (SimplexCategory.rev.map α)) ≫ ι X n := by
        simpa using ι_condition X (SimplexCategory.rev.map α)
      rw [hι]
    _ = (𝟙 (X.obj (op n)) ⊗ₘ
        (simplexRev m ≫ SimplexCategory.toTop.map
          (SimplexCategory.rev.map α))) ≫ ι X n := by
      rw [← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    _ = _ := by rw [← simplexRev_naturality α]

private noncomputable def opHom (X : SimplicialObject TopCat.{u}) :
    TopCat.simplicialRealization.obj (SimplicialObject.opFunctor.obj X) ⟶
      TopCat.simplicialRealization.obj X :=
  desc (opGenerator X) (by
    intro m n α
    exact opGenerator_condition X α)

@[reassoc]
private theorem ι_opHom (X : SimplicialObject TopCat.{u})
    (n : SimplexCategory) :
    ι (SimplicialObject.opFunctor.obj X) n ≫ opHom X =
      opGenerator X n :=
  ι_desc _ _ n

private noncomputable def opInv (X : SimplicialObject TopCat.{u}) :
    TopCat.simplicialRealization.obj X ⟶
      TopCat.simplicialRealization.obj (SimplicialObject.opFunctor.obj X) :=
  TopCat.simplicialRealization.map
      (SimplicialObject.opFunctorCompOpFunctorIso.inv.app X) ≫
    opHom (SimplicialObject.opFunctor.obj X)

private theorem opHom_opInv (X : SimplicialObject TopCat.{u}) :
    opHom X ≫ opInv X = 𝟙 _ := by
  apply hom_ext
  intro n
  simp only [opInv, Category.comp_id]
  rw [← Category.assoc, ι_opHom]
  unfold opGenerator
  slice_lhs 2 3 => rw [ι_map]
  slice_lhs 3 4 =>
    change ι (SimplicialObject.opFunctor.obj
      (SimplicialObject.opFunctor.obj X)) n ≫
        opHom (SimplicialObject.opFunctor.obj X)
    rw [ι_opHom]
  unfold opGenerator
  rw [SimplicialObject.opFunctorCompOpFunctorIso_inv_app_app]
  rw [← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [simplexRev_sq]
  simp

private theorem opInv_opHom (X : SimplicialObject TopCat.{u}) :
    opInv X ≫ opHom X = 𝟙 _ := by
  apply hom_ext
  intro n
  simp only [opInv, Category.comp_id]
  rw [Category.assoc, ← Category.assoc, ι_map]
  slice_lhs 2 3 =>
    change ι (SimplicialObject.opFunctor.obj
      (SimplicialObject.opFunctor.obj X)) n ≫
        opHom (SimplicialObject.opFunctor.obj X)
    rw [ι_opHom]
  unfold opGenerator
  slice_lhs 3 4 => rw [ι_opHom]
  unfold opGenerator
  rw [SimplicialObject.opFunctorCompOpFunctorIso_inv_app_app]
  rw [← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.comp_id]
  rw [← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Iso.inv_hom_id]
  rw [simplexRev_sq]
  simp

/-- Realization is invariant under the covariant simplicial reversal. -/
@[no_expose]
noncomputable def opIso (X : SimplicialObject TopCat.{u}) :
    TopCat.simplicialRealization.obj (SimplicialObject.opFunctor.obj X) ≅
      TopCat.simplicialRealization.obj X where
  hom := opHom X
  inv := opInv X
  hom_inv_id := opHom_opInv X
  inv_hom_id := opInv_opHom X

/-- Generator formula for reversal: reverse the standard-simplex coordinate
and use the degreewise `opObjIso` on the simplicial-space coordinate. -/
theorem opIso_ι_apply (X : SimplicialObject TopCat.{u})
    (n : SimplexCategory)
    (x : (SimplicialObject.opFunctor.obj X).obj (op n) ×
      SimplexCategory.toTop.{u}.obj n) :
    (ι (SimplicialObject.opFunctor.obj X) n ≫ (opIso X).hom) x =
      ι X n
        ((SimplicialObject.opObjIso (X := X) (n := op n)).hom.hom x.1,
          ULift.up (Convexity.StdSimplex.map
            (Fin.rev : Fin (n.len + 1) → Fin (n.len + 1)) x.2.down)) := by
  change (ι (SimplicialObject.opFunctor.obj X) n ≫ opHom X) x = _
  rw [ι_opHom]
  rfl

/-- Naturality of realization reversal. -/
theorem opIso_naturality {X Y : SimplicialObject TopCat.{u}} (f : X ⟶ Y) :
    TopCat.simplicialRealization.map (SimplicialObject.opFunctor.map f) ≫
        (opIso Y).hom =
      (opIso X).hom ≫ TopCat.simplicialRealization.map f := by
  change TopCat.simplicialRealization.map
      (SimplicialObject.opFunctor.map f) ≫ opHom Y =
    opHom X ≫ TopCat.simplicialRealization.map f
  apply hom_ext
  intro n
  slice_lhs 1 2 => rw [ι_map]
  slice_lhs 2 3 => rw [ι_opHom]
  slice_rhs 1 2 => rw [ι_opHom]
  unfold opGenerator
  slice_rhs 2 3 => rw [ι_map]
  simp only [SimplicialObject.opFunctor_map_app]
  rw [← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc, Category.id_comp]
  slice_rhs 1 2 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- Applying realization reversal twice is the realization of the canonical
double-reversal comparison. -/
theorem opIso_double (X : SimplicialObject TopCat.{u}) :
    (opIso (SimplicialObject.opFunctor.obj X)).hom ≫ (opIso X).hom =
      TopCat.simplicialRealization.map
        (SimplicialObject.opFunctorCompOpFunctorIso.hom.app X) := by
  change opHom (SimplicialObject.opFunctor.obj X) ≫ opHom X =
    TopCat.simplicialRealization.map
      (SimplicialObject.opFunctorCompOpFunctorIso.hom.app X)
  apply hom_ext
  intro n
  slice_lhs 1 2 => rw [ι_opHom]
  unfold opGenerator
  slice_lhs 2 3 => rw [ι_opHom]
  unfold opGenerator
  slice_rhs 1 2 => rw [ι_map]
  rw [SimplicialObject.opFunctorCompOpFunctorIso_hom_app_app]
  rw [← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [simplexRev_sq]
  simp

/-- Reversal of a constant simplicial space is invisible under the canonical
constant-realization isomorphism. -/
theorem opIso_constIso (Q : TopCat.{u}) :
    TopCat.simplicialRealization.map
        ((SimplicialObject.constCompOpFunctorIso (C := TopCat.{u})).hom.app Q) ≫
        (constIso Q).hom =
      (opIso ((SimplicialObject.const TopCat).obj Q)).hom ≫
        (constIso Q).hom := by
  change TopCat.simplicialRealization.map
      ((SimplicialObject.constCompOpFunctorIso (C := TopCat.{u})).hom.app Q) ≫
      (constIso Q).hom =
    opHom ((SimplicialObject.const TopCat).obj Q) ≫ (constIso Q).hom
  apply hom_ext
  intro n
  slice_lhs 1 2 => rw [ι_map]
  slice_lhs 2 3 => rw [ι_constIso_hom]
  slice_rhs 1 2 =>
    change ι (SimplicialObject.opFunctor.obj
      ((SimplicialObject.const TopCat).obj Q)) n ≫
        opHom ((SimplicialObject.const TopCat).obj Q)
    rw [ι_opHom]
  unfold opGenerator
  slice_rhs 2 3 => rw [ι_constIso_hom]
  rw [SimplicialObject.constCompOpFunctorIso_hom_app_app]
  change (𝟙 Q ⊗ₘ 𝟙 (SimplexCategory.toTop.obj n)) ≫
      CartesianMonoidalCategory.fst Q (SimplexCategory.toTop.obj n) =
    CartesianMonoidalCategory.fst Q (SimplexCategory.toTop.obj n) ≫ 𝟙 Q
  simp

end TopCat.SimplicialRealization

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

/-- The augmentation of an augmented simplicial space with a left extra
degeneracy is a homotopy equivalence after realization. -/
noncomputable def realizationHomotopyEquiv
    {X : SimplicialObject.Augmented TopCat.{u}} (ed : X.ExtraDegeneracy) :
    ContinuousMap.HomotopyEquiv
      (TopCat.simplicialRealization.obj X.left) X.right where
  toFun := (TopCat.simplicialRealization.map X.hom ≫
    (TopCat.SimplicialRealization.constIso X.right).hom).hom
  invFun := ((TopCat.SimplicialRealization.constIso X.right).inv ≫
    TopCat.simplicialRealization.map ed.section_).hom
  left_inv := by
    let p := TopCat.simplicialRealization.map X.hom ≫
      (TopCat.SimplicialRealization.constIso X.right).hom
    let s := (TopCat.SimplicialRealization.constIso X.right).inv ≫
      TopCat.simplicialRealization.map ed.section_
    have hps : p ≫ s =
        TopCat.simplicialRealization.map (X.hom ≫ ed.section_) := by
      dsimp only [p, s]
      rw [Category.assoc, Iso.hom_inv_id_assoc,
        ← TopCat.simplicialRealization.map_comp]
    have h₀ : s.hom.comp p.hom =
        (TopCat.simplicialRealization.map
          (X.hom ≫ ed.section_)).hom := by
      ext x
      exact ConcreteCategory.congr_hom hps x
    have h₁ : ContinuousMap.id
          (TopCat.simplicialRealization.obj X.left) =
        (TopCat.simplicialRealization.map (𝟙 X.left)).hom := by
      rw [TopCat.simplicialRealization.map_id]
      rfl
    exact ⟨(TopCat.SimplicialRealization.realizationHomotopy ed.homotopy).cast
      h₀.symm h₁.symm⟩
  right_inv := by
    let p := TopCat.simplicialRealization.map X.hom ≫
      (TopCat.SimplicialRealization.constIso X.right).hom
    let s := (TopCat.SimplicialRealization.constIso X.right).inv ≫
      TopCat.simplicialRealization.map ed.section_
    have hsp : s ≫ p = 𝟙 X.right := by
      dsimp only [p, s]
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        rw [← TopCat.simplicialRealization.map_comp,
          ed.section_comp_hom, TopCat.simplicialRealization.map_id]
      simp
    have hc : p.hom.comp s.hom = ContinuousMap.id X.right := by
      ext x
      exact ConcreteCategory.congr_hom hsp x
    rw [hc]

@[simp]
theorem realizationHomotopyEquiv_toFun
    {X : SimplicialObject.Augmented TopCat.{u}} (ed : X.ExtraDegeneracy) :
    ed.realizationHomotopyEquiv.toFun =
      (TopCat.simplicialRealization.map X.hom ≫
        (TopCat.SimplicialRealization.constIso X.right).hom).hom :=
  rfl

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

namespace CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy

/-- A right extra degeneracy gives the same realized augmentation homotopy
equivalence, transported through simplex-coordinate reversal. -/
noncomputable def realizationHomotopyEquiv
    {X : SimplicialObject.Augmented TopCat.{u}}
    (ed : X.RightExtraDegeneracy) :
    ContinuousMap.HomotopyEquiv
      (TopCat.simplicialRealization.obj X.left) X.right := by
  let L := ed.toExtraDegeneracyRev
  let eL := L.realizationHomotopyEquiv
  let r : ContinuousMap.HomotopyEquiv
      (TopCat.simplicialRealization.obj X.left)
      (TopCat.simplicialRealization.obj
        (SimplicialObject.opFunctor.obj X.left)) :=
    (TopCat.homeoOfIso
      (TopCat.SimplicialRealization.opIso X.left)).symm.toHomotopyEquiv
  let e : ContinuousMap.HomotopyEquiv
      (TopCat.simplicialRealization.obj X.left) X.right := r.trans eL
  let p := TopCat.simplicialRealization.map X.hom ≫
    (TopCat.SimplicialRealization.constIso X.right).hom
  let q : SimplicialObject.opFunctor.obj X.left ⟶
      (SimplicialObject.const TopCat).obj X.right :=
    SimplicialObject.opFunctor.map X.hom ≫
      (SimplicialObject.constCompOpFunctorIso
        (C := TopCat.{u})).hom.app X.right
  have hrev : (SimplicialObject.Augmented.rev X).hom = q :=
    SimplicialObject.Augmented.rev_hom X
  have hcat :
      (TopCat.SimplicialRealization.opIso X.left).inv ≫
          TopCat.simplicialRealization.map q ≫
          (TopCat.SimplicialRealization.constIso X.right).hom =
        p := by
    apply (cancel_epi (TopCat.SimplicialRealization.opIso X.left).hom).mp
    dsimp only [p]
    rw [Iso.hom_inv_id_assoc]
    dsimp only [q]
    rw [TopCat.simplicialRealization.map_comp]
    simp only [Category.assoc]
    rw [TopCat.SimplicialRealization.opIso_constIso]
    rw [← Category.assoc,
      TopCat.SimplicialRealization.opIso_naturality]
    rw [Category.assoc]
  have hto : e.toFun = p.hom := by
    change ((TopCat.SimplicialRealization.opIso X.left).inv ≫
      TopCat.simplicialRealization.map
        (SimplicialObject.Augmented.rev X).hom ≫
      (TopCat.SimplicialRealization.constIso X.right).hom).hom = p.hom
    rw [hrev]
    exact congrArg TopCat.Hom.hom hcat
  exact
    { toFun := p.hom
      invFun := e.invFun
      left_inv := by simpa only [← hto] using e.left_inv
      right_inv := by simpa only [← hto] using e.right_inv }

@[simp]
theorem realizationHomotopyEquiv_toFun
    {X : SimplicialObject.Augmented TopCat.{u}}
    (ed : X.RightExtraDegeneracy) :
    ed.realizationHomotopyEquiv.toFun =
      (TopCat.simplicialRealization.map X.hom ≫
        (TopCat.SimplicialRealization.constIso X.right).hom).hom := by
  unfold realizationHomotopyEquiv
  rfl

end CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy

end
