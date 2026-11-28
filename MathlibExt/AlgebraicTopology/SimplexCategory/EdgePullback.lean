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
# Edge coordinates along order-preserving ordinal maps

Let f : X → Y be a morphism of finite nonempty ordinals and let a label the edges of Y by a
type with a distinguished element 1. On an edge i of X, the coordinate operation reads a at
the left endpoint f(i) when f(i) < f(i + 1), and assigns 1 when the endpoints have the same
image.

The identity ordinal map preserves the labels. Precomposing f with the degeneracy that repeats
vertex i inserts the label 1 in edge coordinate i, preserving the other coordinates.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory

universe w

/-- Let A be a type with an element 1, let f : X ⟶ Y be a simplex-category morphism and let a :
Fin Y.len → A label the target edges. For i : Fin X.len, pullbackEdges f a i is a(f(i)) if
f(i) < f(i + 1), and is 1 otherwise. Here i and i + 1 are the endpoints i.castSucc and i.succ,
and the strict inequality ensures that f(i) is a valid target edge index. -/
def pullbackEdges {A : Type w} [One A] {X Y : SimplexCategory}
    (f : X ⟶ Y) (a : Fin Y.len → A) : Fin X.len → A := fun i =>
  if h : f.toOrderHom i.castSucc < f.toOrderHom i.succ then
    a ⟨(f.toOrderHom i.castSucc).val,
      lt_of_lt_of_le (Fin.lt_def.mp h) (f.toOrderHom i.succ).is_le⟩
  else 1

/-- For a type A with an element 1, a simplex-category object X and edge labels a : Fin X.len → A,
one has pullbackEdges (𝟙 X) a = a. Every consecutive pair of vertices remains strictly
increasing under the identity. -/
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

/-- For a type A with an element 1, f : X ⟶ Y in the simplex category, i : Fin (X.len + 1) and a :
Fin Y.len → A, one has pullbackEdges (σ i ≫ f) a = Fin.insertNth i 1 (pullbackEdges f a). Thus
the repeated-vertex edge has label 1 and every other edge keeps the corresponding coordinate
for f. -/
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
