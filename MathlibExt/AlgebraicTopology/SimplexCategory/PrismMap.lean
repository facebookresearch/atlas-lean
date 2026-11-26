/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne

/-!
# Simplex maps with a duplicated prism vertex

Let e : [n] → [m] be monotone and i a vertex of [n]. Define Φ(e,i) : [n+1] → [m+1] by Φ(r) =
e(r) for r ≤ i and Φ(r) = e(r−1)+1 for r > i. Thus the two copies of i map to the two copies
of e(i), with the left and right ordinal embeddings respected.

These maps satisfy Φ(id,i) = id and Φ(e,i) ≫ Φ(f,e(i)) = Φ(e ≫ f,i). They preserve
epimorphisms. If κ_i : [n+1] → [1] is zero on vertices r ≤ i and one on vertices r > i, then
Φ(e,i) ≫ κ_{e(i)} = κ_i.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory.PrismMap

variable {n m l : ℕ}

/-- Monotone simplex map across a duplicated vertex.

For e : [n] → [m] and i ∈ Fin(n+1), define Φ(e,i) : [n+1] → [m+1] with value e(r) when r ≤ i
and e(r−1)+1 when r > i. The source vertex i and target vertex e(i) are each duplicated. -/
def map (e : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋m + 1⦌ := by
  let value (r : Fin (n + 2)) : Fin (m + 2) :=
    if h : r ≤ i.castSucc then
      (e.toOrderHom (r.castLT (by
        change r.val < n + 1
        have hi := i.isLt
        have hr : r.val ≤ i.val := h
        omega))).castSucc
    else
      (e.toOrderHom (r.pred (by
        intro hr
        subst r
        exact h (Fin.zero_le _)))).succ
  have hvalue : Monotone value := by
    intro r s hrs
    by_cases hr : r ≤ i.castSucc
    · by_cases hs : s ≤ i.castSucc
      · dsimp only [value]
        rw [dif_pos hr, dif_pos hs]
        apply Fin.castSucc_le_castSucc_iff.mpr
        apply e.toOrderHom.monotone
        exact hrs
      · have hs0 : s ≠ 0 := by
          intro h
          subst s
          exact hs (Fin.zero_le _)
        dsimp only [value]
        rw [dif_pos hr, dif_neg hs]
        have h : e.toOrderHom (r.castLT (by
            change r.val < n + 1
            have hi := i.isLt
            have hr' : r.val ≤ i.val := hr
            omega)) ≤ e.toOrderHom (s.pred hs0) := by
          apply e.toOrderHom.monotone
          have hri : r.val ≤ i.val := hr
          have hsi : ¬ s.val ≤ i.val := hs
          simp only [Fin.le_def, Fin.val_castLT, Fin.val_pred]
          omega
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at h ⊢
        omega
    · have hs : ¬ s ≤ i.castSucc := by
        intro hs
        exact hr (hrs.trans hs)
      dsimp only [value]
      rw [dif_neg hr, dif_neg hs]
      apply Fin.succ_le_succ_iff.mpr
      apply e.toOrderHom.monotone
      simp only [Fin.le_def, Fin.val_pred]
      exact Nat.sub_le_sub_right (Fin.le_iff_val_le_val.mp hrs) 1
  exact SimplexCategory.Hom.mk { toFun := value, monotone' := hvalue }

/-- Left-embedding formula for a simplex prism map.

For r,i ∈ Fin(n+1) with r ≤ i, Φ(e,i) sends r.castSucc to e(r).castSucc. These embeddings keep
the vertex values unchanged in the enlarged ordinals. -/
@[simp]
theorem map_left (e : ⦋n⦌ ⟶ ⦋m⦌) (i r : Fin (n + 1)) (hr : r ≤ i) :
    (map e i).toOrderHom r.castSucc = (e.toOrderHom r).castSucc := by
  have h : r.castSucc ≤ i.castSucc := Fin.castSucc_le_castSucc_iff.mpr hr
  let r' : Fin (n + 1) := r.castSucc.castLT (by
    change r.val < n + 1
    exact r.isLt)
  have hv : (map e i).toOrderHom r.castSucc = (e.toOrderHom r').castSucc := by
    unfold map
    dsimp only [SimplexCategory.Hom.toOrderHom, SimplexCategory.Hom.mk, DFunLike.coe, OrderHom.instFunLike]
    split_ifs with hh
    · apply congrArg (fun a => (e.toOrderHom a).castSucc)
      exact Fin.ext rfl
    · exact False.elim (hh h)
  have hr' : r' = r := Fin.ext rfl
  exact hv.trans (congrArg (fun a => (e.toOrderHom a).castSucc) hr')

/-- Right-embedding formula for a simplex prism map.

For i,r ∈ Fin(n+1) with i ≤ r, Φ(e,i) sends r.succ to e(r).succ. Both vertex values are
increased by one in the enlarged ordinals. -/
@[simp]
theorem map_right (e : ⦋n⦌ ⟶ ⦋m⦌) (i r : Fin (n + 1)) (hr : i ≤ r) :
    (map e i).toOrderHom r.succ = (e.toOrderHom r).succ := by
  have h : ¬ r.succ ≤ i.castSucc := by
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    have hri : i.val ≤ r.val := hr
    omega
  have hv : (map e i).toOrderHom r.succ = (e.toOrderHom r).succ := by
    unfold map
    dsimp only [SimplexCategory.Hom.toOrderHom, SimplexCategory.Hom.mk, DFunLike.coe, OrderHom.instFunLike]
    split_ifs with hh
    · exact False.elim (h hh)
    · apply congrArg (fun a => (e.toOrderHom a).succ)
      exact Fin.pred_succ _
  exact hv

/-- Identity law for the duplicated-vertex simplex map.

For any vertex i of [n], duplicating i under the identity simplex map gives the identity map
of [n+1]. -/
theorem map_id (i : Fin (n + 1)) : map (𝟙 ⦋n⦌) i = 𝟙 ⦋n + 1⦌ := by
  ext r : 3
  by_cases hr : r ≤ i.castSucc
  · have hlast : r ≠ Fin.last (n + 1) := by
      intro h
      subst r
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hr
      omega
    obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    rw [map_left _ _ _ (Fin.castSucc_le_castSucc_iff.mp hr)]
    rfl
  · have hzero : r ≠ 0 := by intro h; subst r; simp at hr
    obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hzero
    rw [map_right _ _ _ (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hr; omega)]
    rfl

/-- Composition law for duplicated-vertex simplex maps.

For e : [n] → [m], f : [m] → [l] and i a vertex of [n], Φ(e,i) ≫ Φ(f,e(i)) = Φ(e ≫ f,i). The
second duplicated vertex is the image e(i). -/
theorem map_comp (e : ⦋n⦌ ⟶ ⦋m⦌) (f : ⦋m⦌ ⟶ ⦋l⦌) (i : Fin (n + 1)) :
    map e i ≫ map f (e.toOrderHom i) = map (e ≫ f) i := by
  ext r : 3
  by_cases hr : r ≤ i.castSucc
  · have hlast : r ≠ Fin.last (n + 1) := by
      intro h
      subst r
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hr
      omega
    obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    have hri : r ≤ i := Fin.castSucc_le_castSucc_iff.mp hr
    have hre : e.toOrderHom r ≤ e.toOrderHom i := e.toOrderHom.monotone hri
    change (map f (e.toOrderHom i)).toOrderHom ((map e i).toOrderHom r.castSucc) = _
    rw [map_left e i r hri, map_left f _ _ hre, map_left (e ≫ f) i r hri]
    rfl
  · have hzero : r ≠ 0 := by intro h; subst r; simp at hr
    obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hzero
    have hir : i ≤ r := by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hr; omega
    have hei : e.toOrderHom i ≤ e.toOrderHom r := e.toOrderHom.monotone hir
    change (map f (e.toOrderHom i)).toOrderHom ((map e i).toOrderHom r.succ) = _
    rw [map_right e i r hir, map_right f _ _ hei, map_right (e ≫ f) i r hir]
    rfl

/-- Epimorphism preserved by duplicating a simplex vertex.

If e : [n] → [m] is an epimorphism, then Φ(e,i) : [n+1] → [m+1] is an epimorphism for every i.
Surjectivity on each side of the duplicated vertex supplies all target vertices. -/
theorem map_epi (e : ⦋n⦌ ⟶ ⦋m⦌) [Epi e] (i : Fin (n + 1)) : Epi (map e i) := by
  rw [SimplexCategory.epi_iff_surjective]
  have he : Function.Surjective e.toOrderHom := SimplexCategory.epi_iff_surjective.mp inferInstance
  intro z
  by_cases hz : z ≤ (e.toOrderHom i).castSucc
  · have hlast : z ≠ Fin.last (m + 1) := by
      intro h
      subst z
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hz
      omega
    let w := z.castPred hlast
    have hw : w ≤ e.toOrderHom i := by
      simpa only [w, Fin.le_def, Fin.coe_castPred, Fin.val_castSucc] using hz
    by_cases hwi : w = e.toOrderHom i
    · refine ⟨i.castSucc, ?_⟩
      rw [map_left e i i le_rfl, ← hwi]
      exact Fin.castSucc_castPred z hlast
    · obtain ⟨r, hr⟩ := he w
      have hri : r ≤ i := by
        by_contra h
        have hmon : e.toOrderHom i ≤ e.toOrderHom r := e.toOrderHom.monotone (le_of_not_ge h)
        rw [hr] at hmon
        exact hwi (le_antisymm hw hmon)
      refine ⟨r.castSucc, ?_⟩
      rw [map_left e i r hri, hr]
      exact Fin.castSucc_castPred z hlast
  · have hgt : (e.toOrderHom i).castSucc < z := lt_of_not_ge hz
    have hzero : z ≠ 0 := Fin.ne_zero_of_lt hgt
    let w := z.pred hzero
    have hw : e.toOrderHom i ≤ w := by
      simp only [w, Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_pred] at hgt ⊢
      omega
    by_cases hwi : w = e.toOrderHom i
    · refine ⟨i.succ, ?_⟩
      rw [map_right e i i le_rfl, ← hwi]
      exact Fin.succ_pred z hzero
    · obtain ⟨r, hr⟩ := he w
      have hir : i ≤ r := by
        by_contra h
        have hmon : e.toOrderHom r ≤ e.toOrderHom i := e.toOrderHom.monotone (le_of_not_ge h)
        rw [hr] at hmon
        exact hwi (le_antisymm hmon hw)
      refine ⟨r.succ, ?_⟩
      rw [map_right e i r hir, hr]
      exact Fin.succ_pred z hzero

/-- Cut compatibility of a duplicated-vertex simplex map.

For e : [n] → [m] and vertex i, let κ_i : [n+1] → [1] be the cut with values zero for r ≤ i
and one for r > i. Then Φ(e,i) ≫ κ_{e(i)} = κ_i, preserving the chosen prism interval cut. -/
theorem map_cut (e : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    map e i ≫ SimplexCategory.toMk₁ (e.toOrderHom i).castSucc.succ =
      SimplexCategory.toMk₁ i.castSucc.succ := by
  ext r : 3
  by_cases hr : r ≤ i.castSucc
  · have hlast : r ≠ Fin.last (n + 1) := by
      intro h
      subst r
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hr
      omega
    obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    have hri : r ≤ i := Fin.castSucc_le_castSucc_iff.mp hr
    have hre : e.toOrderHom r ≤ e.toOrderHom i := e.toOrderHom.monotone hri
    change SimplexCategory.toMk₁ (e.toOrderHom i).castSucc.succ ((map e i).toOrderHom r.castSucc) = _
    rw [map_left e i r hri]
    have hleft := SimplexCategory.toMk₁_of_castSucc_lt
      (n := m + 1) (e.toOrderHom i).castSucc.succ (e.toOrderHom r).castSucc (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hre))
    have hright := SimplexCategory.toMk₁_of_castSucc_lt
      (n := n + 1) i.castSucc.succ r.castSucc (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hri))
    exact hleft.trans hright.symm
  · have hzero : r ≠ 0 := by intro h; subst r; simp at hr
    obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hzero
    have hir : i ≤ r := by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hr; omega
    have hei : e.toOrderHom i ≤ e.toOrderHom r := e.toOrderHom.monotone hir
    change SimplexCategory.toMk₁ (e.toOrderHom i).castSucc.succ ((map e i).toOrderHom r.succ) = _
    rw [map_right e i r hir]
    have hleft := SimplexCategory.toMk₁_of_le_castSucc
      (n := m + 1) (e.toOrderHom i).castSucc.succ (e.toOrderHom r).succ (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
        exact Nat.add_le_add_right (Fin.le_iff_val_le_val.mp hei) 1)
    have hright := SimplexCategory.toMk₁_of_le_castSucc
      (n := n + 1) i.castSucc.succ r.succ (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
        exact Nat.add_le_add_right (Fin.le_iff_val_le_val.mp hir) 1)
    exact hleft.trans hright.symm

end SimplexCategory.PrismMap

end
