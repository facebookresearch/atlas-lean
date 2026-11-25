/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.GaloisConnection.Defs

/-!
# The actual contravariant interval representation

Extend a simplex operator by a new top element and take its finite-order
left adjoint. This constructs the interval action on levels, preserving
the two distinct endpoints. The adjunction proves the actual identity
and composition equations and recovers the original simplex operator.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory.IntervalRepresentation

variable {Δ Δ' Δ'' : SimplexCategory}

/-- The original operator extended by the new, distinct top level. -/
def extendTop (f : Δ ⟶ Δ') : Fin (Δ.len + 2) →o Fin (Δ'.len + 2) where
  toFun k := if h : k = Fin.last (Δ.len + 1) then Fin.last (Δ'.len + 1)
    else (f.toOrderHom (k.castPred h)).castSucc
  monotone' := by
    intro k l hkl
    by_cases hl : l = Fin.last (Δ.len + 1)
    · simp only [hl, dite_true]
      exact Fin.le_last _
    · have hk : k ≠ Fin.last (Δ.len + 1) := by
        intro hk
        have h0 := hkl
        rw [hk] at h0
        exact hl (le_antisymm (Fin.le_last l) h0)
      simp only [dite_eq_right hk, dite_eq_right hl]
      exact Fin.castSucc_le_castSucc_iff.mpr (f.toOrderHom.monotone hkl)

/-- Each original level has its original operator image. -/
theorem extendTop_castSucc (f : Δ ⟶ Δ') (k : Fin (Δ.len + 1)) :
    extendTop f k.castSucc = (f.toOrderHom k).castSucc := by
  simp [extendTop]

/-- The added top level is preserved literally. -/
theorem extendTop_last (f : Δ ⟶ Δ') :
    extendTop f (Fin.last (Δ.len + 1)) = Fin.last (Δ'.len + 1) := by
  simp [extendTop]

/-- Original identity operators remain the entire extended identity. -/
theorem extendTop_id : extendTop (𝟙 Δ) = OrderHom.id := by
  apply OrderHom.ext
  funext k
  by_cases hk : k = Fin.last (Δ.len + 1)
  · simp [hk, extendTop_last]
  · simp [extendTop, hk]

/-- Original operator composition remains the entire extended composition. -/
theorem extendTop_comp (f : Δ ⟶ Δ') (g : Δ' ⟶ Δ'') :
    extendTop (f ≫ g) = (extendTop g).comp (extendTop f) := by
  apply OrderHom.ext
  funext k
  by_cases hk : k = Fin.last (Δ.len + 1)
  · simp [hk, extendTop_last]
  · obtain ⟨k', rfl⟩ := k.eq_castSucc_of_ne_last hk
    change extendTop (f ≫ g) k'.castSucc = extendTop g (extendTop f k'.castSucc)
    rw [extendTop_castSucc, extendTop_castSucc, extendTop_castSucc]
    rfl

/-- The finite upper set whose first point is the interval image. -/
def candidates (f : Δ ⟶ Δ') (j : Fin (Δ'.len + 2)) : Finset (Fin (Δ.len + 2)) :=
  Finset.univ.filter fun k => j ≤ extendTop f k

/-- The preserved top makes every such upper set nonempty. -/
theorem candidates_nonempty (f : Δ ⟶ Δ') (j : Fin (Δ'.len + 2)) :
    (candidates f j).Nonempty := by
  refine ⟨Fin.last (Δ.len + 1), ?_⟩
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and, extendTop_last]
  exact Fin.le_last j

/-- The actual first original level above the requested target level. -/
def left (f : Δ ⟶ Δ') (j : Fin (Δ'.len + 2)) : Fin (Δ.len + 2) :=
  (candidates f j).min' (candidates_nonempty f j)

/-- The interval image is the actual finite-order left adjoint of the extended operator. -/
theorem left_gc (f : Δ ⟶ Δ') : GaloisConnection (left f) (extendTop f) := by
  intro j k
  constructor
  · intro h
    have hm : j ≤ extendTop f (left f j) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ (candidates_nonempty f j))).2
    exact hm.trans ((extendTop f).monotone h)
  · intro h
    change (candidates f j).min' (candidates_nonempty f j) ≤ k
    exact Finset.min'_le (candidates f j) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- The interval image is an actual simplex operator. -/
def map (f : Δ ⟶ Δ') : ⦋Δ'.len + 1⦌ ⟶ ⦋Δ.len + 1⦌ :=
  mkHom ⟨left f, (left_gc f).monotone_l⟩

/-- The bottom endpoint remains the original bottom endpoint. -/
theorem map_zero (f : Δ ⟶ Δ') : (map f).toOrderHom 0 = 0 := by
  apply le_antisymm
  · exact (left_gc f 0 0).mpr (Fin.zero_le _)
  · exact Fin.zero_le _

/-- The top endpoint remains the original, distinct top endpoint. -/
theorem map_last (f : Δ ⟶ Δ') :
    (map f).toOrderHom (Fin.last (Δ'.len + 1)) = Fin.last (Δ.len + 1) := by
  by_contra h
  have hm : Fin.last (Δ'.len + 1) ≤
      extendTop f ((map f).toOrderHom (Fin.last (Δ'.len + 1))) :=
    (left_gc f).le_u_l _
  obtain ⟨k, hk⟩ := ((map f).toOrderHom (Fin.last (Δ'.len + 1))).eq_castSucc_of_ne_last h
  rw [← hk, extendTop_castSucc] at hm
  exact (Fin.castSucc_lt_last _).not_ge hm

/-- Identity simplex operators act by the entire interval identity. -/
theorem map_id : map (𝟙 Δ) = 𝟙 ⦋Δ.len + 1⦌ := by
  apply Hom.ext
  apply OrderHom.ext
  funext j
  apply (left_gc (𝟙 Δ)).l_unique (GaloisConnection.id)
  intro k
  exact congrArg (fun h : Fin (Δ.len + 2) →o Fin (Δ.len + 2) => h k) extendTop_id

/-- The interval action reverses the actual original composition. -/
theorem map_comp (f : Δ ⟶ Δ') (g : Δ' ⟶ Δ'') :
    map (f ≫ g) = map g ≫ map f := by
  apply Hom.ext
  apply OrderHom.ext
  funext j
  apply (left_gc (f ≫ g)).l_unique ((left_gc g).compose (left_gc f))
  intro k
  exact congrArg (fun h : Fin (Δ.len + 2) →o Fin (Δ''.len + 2) => h k) (extendTop_comp f g)

/-- The actual contravariant interval functor, with both endpoint maps proved. -/
def functor : SimplexCategoryᵒᵖ ⥤ SimplexCategory where
  obj Δ := ⦋Δ.unop.len + 1⦌
  map f := map f.unop
  map_id _ := map_id
  map_comp f g := map_comp g.unop f.unop

/-- The actual interval action recovers each original operator. -/
theorem map_injective : Function.Injective (map (Δ := Δ) (Δ' := Δ')) := by
  intro f g h
  apply Hom.ext
  apply OrderHom.ext
  funext k
  have he : extendTop f k.castSucc = extendTop g k.castSucc :=
    (left_gc f).u_unique (left_gc g) (fun j => congrArg (fun q => q.toOrderHom j) h)
  rw [extendTop_castSucc, extendTop_castSucc] at he
  exact Fin.castSucc_injective _ he

instance : functor.Faithful where
  map_injective := by
    intro Δ Δ' f g h
    exact Quiver.Hom.unop_inj (map_injective h)

private theorem gc_predAbove_succAbove {n : ℕ} (i : Fin (n + 1)) :
    GaloisConnection i.predAbove i.castSucc.succAbove := by
  intro j k
  simp only [Fin.succAbove, Fin.predAbove, Fin.le_def, Fin.lt_def, Fin.val_castSucc,
    apply_dite Fin.val, Fin.val_pred, Fin.coe_castPred, dite_eq_ite,
    apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

private theorem gc_succAbove_predAbove {n : ℕ} (i : Fin (n + 1)) :
    GaloisConnection i.succ.succAbove i.predAbove := by
  intro j k
  simp only [Fin.succAbove, Fin.predAbove, Fin.le_def, Fin.lt_def, Fin.val_castSucc,
    apply_dite Fin.val, Fin.val_pred, Fin.coe_castPred, dite_eq_ite,
    apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- Extending an original face skips the same level before the distinct new top. -/
theorem extendTop_delta {n : ℕ} (i : Fin (n + 2)) :
    extendTop (δ i) = (Fin.succAboveOrderEmb i.castSucc).toOrderHom := by
  apply OrderHom.ext
  funext k
  by_cases hk : k = Fin.last (n + 1)
  · subst k
    rw [extendTop_last]
    change Fin.last (n + 2) = i.castSucc.succAbove (Fin.last (n + 1))
    rw [Fin.succAbove_castSucc_of_le _ _ (Fin.le_last i)]
    rfl
  · obtain ⟨k', rfl⟩ := k.eq_castSucc_of_ne_last hk
    rw [extendTop_castSucc]
    exact Fin.castSucc_succAbove_castSucc.symm

/-- Extending an original degeneracy coalesces the same adjacent levels. -/
theorem extendTop_sigma {n : ℕ} (i : Fin (n + 1)) :
    extendTop (σ i) = i.castSucc.predAboveOrderHom := by
  apply OrderHom.ext
  funext k
  by_cases hk : k = Fin.last (n + 2)
  · subst k
    rw [extendTop_last]
    exact Fin.predAbove_right_last.symm
  · obtain ⟨k', rfl⟩ := k.eq_castSucc_of_ne_last hk
    rw [extendTop_castSucc]
    exact (Fin.castSucc_predAbove_castSucc i k').symm

/-- An original face acts on levels by the corresponding degeneracy. -/
theorem map_delta {n : ℕ} (i : Fin (n + 2)) : map (δ i) = σ i := by
  apply Hom.ext
  apply OrderHom.ext
  funext j
  apply (left_gc (δ i)).l_unique (gc_predAbove_succAbove i)
  intro k
  exact congrArg (fun q : Fin (n + 2) →o Fin (n + 3) => q k) (extendTop_delta i)

/-- An original degeneracy acts on levels by the face omitting its new interior gap. -/
theorem map_sigma {n : ℕ} (i : Fin (n + 1)) : map (σ i) = δ i.castSucc.succ := by
  apply Hom.ext
  apply OrderHom.ext
  funext j
  apply (left_gc (σ i)).l_unique (gc_succAbove_predAbove i.castSucc)
  intro k
  exact congrArg (fun q : Fin (n + 3) →o Fin (n + 2) => q k) (extendTop_sigma i)

end SimplexCategory.IntervalRepresentation
