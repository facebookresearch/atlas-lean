/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne

/-!
# Simplicial homotopies from a constant-source edge

Let C be any category, B an object and X simplicial. A map z : B → X₀ determines a map
const(B) → X whose degree-n component is z followed by X applied to the opposite of the
collapse [n] → [0].

For maps f,g : const(B) → X and an edge e : B → X₁ with e ≫ d₁ = f₀ and e ≫ d₀ = g₀, define
h_{n,i} = e ≫ X(κ_i.op), where κ_i : [n+1] → [1] is zero on vertices r ≤ i and one on r > i.
The cut identities give all simplicial homotopy face and degeneracy equations. In particular
h_{n,0} ≫ d₀ = g_n and h_{n,n} ≫ d_{n+1} = f_n. Object and morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.ConstantSourcePrism

variable {C : Type u} [Category.{v} C] {B : C} {X : SimplicialObject C}

private abbrev collapse (n : ℕ) : ⦋n⦌ ⟶ ⦋0⦌ := SimplexCategory.const _ _ 0

/-- Constant-source simplicial map determined in degree zero.

For z : B → X₀ in an arbitrary category C, define const(B) → X with degree-n component z
followed by X applied contravariantly to the unique simplex map [n] → [0]. -/
def fromZero (z : B ⟶ X.obj (op ⦋0⦌)) : (SimplicialObject.const C).obj B ⟶ X where
  app Δ := z ≫ X.map (SimplexCategory.isTerminalZero.from Δ.unop).op
  naturality {Δ Δ'} θ := by
    simp only [Functor.const_obj_map, Category.id_comp, Category.assoc, ← X.map_comp]
    have h : (SimplexCategory.isTerminalZero.from Δ.unop).op ≫ θ =
        (SimplexCategory.isTerminalZero.from Δ'.unop).op := by
      apply Quiver.Hom.unop_inj
      exact SimplexCategory.isTerminalZero.hom_ext _ _
    exact (Category.id_comp _).trans
      (congrArg (fun f => z ≫ X.map f) h).symm

/-- Degree-zero component of a constant-source simplicial map.

For z : B → X₀, the map fromZero z has degree-zero component z itself, since the collapse [0]
→ [0] is identity. -/
@[simp]
theorem fromZero_zero (z : B ⟶ X.obj (op ⦋0⦌)) : (fromZero z).app (op ⦋0⦌) = z := by
  have h : SimplexCategory.isTerminalZero.from ⦋0⦌ = 𝟙 ⦋0⦌ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  simp only [fromZero, h, op_id, X.map_id, Category.comp_id]

private abbrev cut {n : ℕ} (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.toMk₁ i.castSucc.succ

private theorem first_face (n : ℕ) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ cut (0 : Fin (n + 1)) =
      collapse n ≫ SimplexCategory.δ (0 : Fin 2) := by
  rw [cut, SimplexCategory.δ_comp_toMk₁_of_lt _ _ (by simp), Fin.pred_succ]
  ext j : 3
  simp [SimplexCategory.toMk₁, collapse, SimplexCategory.const, SimplexCategory.δ]

private theorem last_face (n : ℕ) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ cut (Fin.last n) =
      collapse n ≫ SimplexCategory.δ (1 : Fin 2) := by
  rw [cut, SimplexCategory.δ_comp_toMk₁_of_le _ _ (by simp)]
  ext j : 3
  change (if j.val < n + 1 then (0 : Fin 2) else 1) = 0
  rw [if_pos j.isLt]

private theorem early_face {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    SimplexCategory.δ i.castSucc ≫ cut j.succ = cut j := by
  have h : i.castSucc.castSucc < j.succ.castSucc.succ := by
    simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hij ⊢
    omega
  simp only [cut]
  rw [SimplexCategory.δ_comp_toMk₁_of_lt j.succ.castSucc.succ i.castSucc h]
  congr 1
  all_goals apply Fin.ext
  all_goals simp only [Fin.val_pred, Fin.val_succ, Fin.val_castSucc]
  all_goals omega

private theorem middle_face {n : ℕ} (j : Fin (n + 1)) :
    SimplexCategory.δ j.castSucc.succ ≫ cut j.succ =
      SimplexCategory.δ j.castSucc.succ ≫ cut j.castSucc := by
  rw [cut, cut,
    SimplexCategory.δ_comp_toMk₁_of_lt _ _ (by simp),
    SimplexCategory.δ_comp_toMk₁_of_le _ _ (by simp), Fin.pred_succ]
  congr 1
  all_goals apply Fin.ext
  all_goals rfl

private theorem late_face {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    SimplexCategory.δ i.succ ≫ cut j.castSucc = cut j := by
  have h : j.castSucc.castSucc.succ ≤ i.succ.castSucc := by
    simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hji ⊢
    omega
  rw [cut, SimplexCategory.δ_comp_toMk₁_of_le _ _ h]
  congr 1
  all_goals apply Fin.ext
  all_goals rfl

private theorem early_degeneracy {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    SimplexCategory.σ i.castSucc ≫ cut j = cut j.succ := by
  have h : i.castSucc.castSucc < j.castSucc.succ := by
    simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hij ⊢
    omega
  simpa only [cut, Fin.succ_castSucc] using
    SimplexCategory.σ_comp_toMk₁_of_lt j.castSucc.succ i.castSucc h

private theorem late_degeneracy {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    SimplexCategory.σ i.succ ≫ cut j = cut j.castSucc := by
  have h : j.castSucc.succ ≤ i.succ.castSucc := by
    simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at hji ⊢
    omega
  rw [cut, SimplexCategory.σ_comp_toMk₁_of_le _ _ h]
  congr 1
  all_goals apply Fin.ext
  all_goals rfl

variable (f g : (SimplicialObject.const C).obj B ⟶ X)
  (e : B ⟶ X.obj (op ⦋1⦌))
  (hf : e ≫ X.δ (1 : Fin 2) = f.app (op ⦋0⦌))
  (hg : e ≫ X.δ (0 : Fin 2) = g.app (op ⦋0⦌))

/-- Simplicial homotopy constructed from an edge with specified endpoints.

For f,g : const(B) → X and e : B → X₁ satisfying e ≫ d₁ = f₀ and e ≫ d₀ = g₀, define h_{n,i} =
e ≫ X(κ_i.op) for i ∈ Fin(n+1), with κ_i the cut at i+1. These components satisfy every face
and degeneracy law of a homotopy from f to g, including h_{n,0} ≫ d₀ = g_n and h_{n,n} ≫
d_{n+1} = f_n. -/
def homotopy : SimplicialObject.Homotopy f g where
  h i := e ≫ X.map (SimplexCategory.toMk₁ i.castSucc.succ).op
  h_zero_comp_δ_zero n := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ, SimplicialObject.const, Functor.const]
    try simp only [Category.id_comp]
    change (e ≫ X.map (cut (0 : Fin (n + 1))).op) ≫
      X.map (SimplexCategory.δ (0 : Fin (n + 2))).op = _
    rw [Category.assoc, ← X.map_comp, ← op_comp, first_face,
      op_comp, X.map_comp, ← Category.assoc]
    change (e ≫ X.δ (0 : Fin 2)) ≫ X.map (collapse n).op = _
    rw [hg]
    have h := (g.naturality (collapse n).op).symm
    change g.app (op ⦋0⦌) ≫ X.map (collapse n).op = 𝟙 B ≫ g.app (op ⦋n⦌) at h
    exact h.trans (Category.id_comp _)
  h_last_comp_δ_last n := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ, SimplicialObject.const, Functor.const]
    try simp only [Category.id_comp]
    change (e ≫ X.map (cut (Fin.last n)).op) ≫
      X.map (SimplexCategory.δ (Fin.last (n + 1))).op = _
    rw [Category.assoc, ← X.map_comp, ← op_comp, last_face,
      op_comp, X.map_comp, ← Category.assoc]
    change (e ≫ X.δ (1 : Fin 2)) ≫ X.map (collapse n).op = _
    rw [hf]
    have h := (f.naturality (collapse n).op).symm
    change f.app (op ⦋0⦌) ≫ X.map (collapse n).op = 𝟙 B ≫ f.app (op ⦋n⦌) at h
    exact h.trans (Category.id_comp _)
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ, SimplicialObject.const, Functor.const]
    try simp only [Category.id_comp]
    rw [Category.assoc, ← X.map_comp, ← op_comp, early_face i j hij]
    all_goals simp only [Functor.const_obj_map, Category.id_comp]
  h_succ_comp_δ_castSucc_succ j := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ, SimplicialObject.const, Functor.const]
    try simp only [Category.id_comp]
    simp only [Category.assoc, ← X.map_comp, ← op_comp]
    all_goals rw [middle_face]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ, SimplicialObject.const, Functor.const]
    try simp only [Category.id_comp]
    rw [Category.assoc, ← X.map_comp, ← op_comp, late_face i j hji]
    all_goals simp only [Functor.const_obj_map, Category.id_comp]
  h_comp_σ_castSucc_of_le i j hij := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ, SimplicialObject.const, Functor.const]
    try simp only [Category.id_comp]
    rw [Category.assoc, ← X.map_comp, ← op_comp, early_degeneracy i j hij]
    all_goals simp only [Functor.const_obj_map, Category.id_comp]
  h_comp_σ_succ_of_lt i j hji := by
    dsimp only [SimplicialObject.δ, SimplicialObject.σ, SimplicialObject.const, Functor.const]
    try simp only [Category.id_comp]
    rw [Category.assoc, ← X.map_comp, ← op_comp, late_degeneracy i j hji]
    all_goals simp only [Functor.const_obj_map, Category.id_comp]

end CategoryTheory.SimplicialObject.ConstantSourcePrism

end
