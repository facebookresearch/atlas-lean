/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Unit insertion along ordinal maps

An increasing edge selects its original target edge; a constant edge inserts
one. This coordinate operation needs only a type with one. Its degeneracy
composition law is independent of coefficients, tensor products or rings.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory

universe w

/-- Read the target label on increasing edges, inserting one on constant edges. -/
def pullbackEdges {A : Type w} [One A] {X Y : SimplexCategory}
    (f : X ⟶ Y) (a : Fin Y.len → A) : Fin X.len → A := fun i =>
  if h : f.toOrderHom i.castSucc < f.toOrderHom i.succ then
    a ⟨(f.toOrderHom i.castSucc).val,
      lt_of_lt_of_le (Fin.lt_def.mp h) (f.toOrderHom i.succ).is_le⟩
  else 1

/-- Identity ordinal maps retain every edge label. -/
@[simp]
theorem pullbackEdges_id {A : Type w} [One A] (X : SimplexCategory)
    (a : Fin X.len → A) : pullbackEdges (𝟙 X) a = a := by
  funext i
  change (if _ : i.castSucc < i.succ then a i else 1) = a i
  rw [dite_eq_left (show i.castSucc < i.succ from Fin.castSucc_lt_succ)]

private theorem predAbove_edge_left {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.predAbove (i.succAbove j).castSucc = j.castSucc := by
  rw [← Fin.castSucc_succAbove_castSucc, Fin.predAbove_succAbove]

private theorem predAbove_edge_right {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.predAbove (i.succAbove j).succ = j.succ := by
  apply Fin.succAbove_right_injective (p := i.succ)
  rw [Fin.succ_succAbove_predAbove (by
    exact fun h => Fin.succAbove_ne i j (Fin.succ_injective (n + 1) h)),
    Fin.succ_succAbove_succ]

/-- Precomposing any ordinal map by a degeneracy inserts one in that edge. -/
theorem pullbackEdges_σ_comp {A : Type w} [One A] {X Y : SimplexCategory}
    (f : X ⟶ Y) (i : Fin (X.len + 1)) (a : Fin Y.len → A) :
    pullbackEdges (σ i ≫ f) a = Fin.insertNth i 1 (pullbackEdges f a) := by
  rw [Fin.eq_insertNth_iff]
  constructor
  · have hleft : (σ i ≫ f).toOrderHom i.castSucc = f.toOrderHom i := by
      change f.toOrderHom (i.predAbove i.castSucc) = f.toOrderHom i
      rw [Fin.predAbove_castSucc_self]
    have hright : (σ i ≫ f).toOrderHom i.succ = f.toOrderHom i := by
      change f.toOrderHom (i.predAbove i.succ) = f.toOrderHom i
      rw [Fin.predAbove_succ_self]
    simp only [pullbackEdges, hleft, hright, lt_self_iff_false]
    exact dite_eq_right (fun h : False => h)
  · funext j
    change pullbackEdges (σ i ≫ f) a (i.succAbove j) = pullbackEdges f a j
    have hleft : (σ i ≫ f).toOrderHom (i.succAbove j).castSucc =
        f.toOrderHom j.castSucc := by
      change f.toOrderHom (i.predAbove (i.succAbove j).castSucc) = f.toOrderHom j.castSucc
      rw [predAbove_edge_left]
    have hright : (σ i ≫ f).toOrderHom (i.succAbove j).succ = f.toOrderHom j.succ := by
      change f.toOrderHom (i.predAbove (i.succAbove j).succ) = f.toOrderHom j.succ
      rw [predAbove_edge_right]
    simp only [pullbackEdges, hleft, hright]

end SimplexCategory
