/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatActionSubgroups
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiberCentralCoordinate
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperWeylGeneration

/-! # Right-action base reachability and transitivity

Reusable right-action reachability for the Tits Bruhat fiber `X F n`.
The fiber coordinate `X.fst` is moved on the right by `SL` multiplication;
right permutations realize this action and central permutations adjust the
central fiber. Every `SL` element is reached from the base point `X_one`
by a right-action permutation, and every fiber point is reached by a
right-action followed by a central permutation.
-/

@[expose] public section

universe u

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoTitsBruhatFiber

namespace MatsumotoTitsBruhatFiber

/-- Subgroup of `SL (Fin n) F` realized by right-action permutations:
`s` belongs iff some `g ∈ rightActionSubgroup F n` satisfies
`∀ x, X.fst (g x) = X.fst x * s`. Right multiplication is
anti-multiplicative, so witnesses compose in reversed order. -/
def rightActionFstSubgroup (F : Type u) [Field F] (n : ℕ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := { s |
    ∃ g ∈ rightActionSubgroup (F := F) (n := n),
      ∀ x : X F n, X.fst (g x) = X.fst x * s }
  one_mem' := by
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro x
    simp
  mul_mem' := by
    intro s t hs ht
    obtain ⟨gs, hgs_mem, hgs⟩ := hs
    obtain ⟨gt, hgt_mem, hgt⟩ := ht
    refine ⟨gt * gs, Subgroup.mul_mem _ hgt_mem hgs_mem, ?_⟩
    intro x
    have h1 : X.fst ((gt * gs) x) = X.fst (gt (gs x)) := by
      simp [Equiv.Perm.mul_apply]
    rw [h1, hgt (gs x), hgs x, mul_assoc]
  inv_mem' := by
    intro s hs
    obtain ⟨gs, hgs_mem, hgs⟩ := hs
    refine ⟨gs⁻¹, Subgroup.inv_mem _ hgs_mem, ?_⟩
    intro x
    have h : ∀ y : X F n, X.fst (gs y) = X.fst y * s := hgs
    have h1 := h (gs⁻¹ x)
    have h2 : X.fst x = X.fst (gs⁻¹ x) * s := by
      have h_eq : gs (gs⁻¹ x) = x := Equiv.apply_symm_apply gs x
      calc X.fst x = X.fst (gs (gs⁻¹ x)) := by rw [h_eq]
        _ = X.fst (gs⁻¹ x) * s := h1
    calc X.fst (gs⁻¹ x) = X.fst (gs⁻¹ x) * s * s⁻¹ := by simp
      _ = X.fst x * s⁻¹ := by rw [← h2]

theorem rightActionFstSubgroup_mem_iff (F : Type u) [Field F] {n : ℕ}
    {s : Matrix.SpecialLinearGroup (Fin n) F} :
    s ∈ rightActionFstSubgroup (F := F) (n := n) ↔
      ∃ g ∈ rightActionSubgroup (F := F) (n := n),
        ∀ x : X F n, X.fst (g x) = X.fst x * s :=
  Iff.rfl

-- Upper elementary generators belong via `rightUpperPerm`.
theorem UpperElementary_toSLHom_mem_rightActionFstSubgroup (F : Type u) [Field F]
    {n : ℕ} (u : upperElementarySubgroup (Fin n) F) :
    UpperElementary.toSLHom (R := F) u ∈ rightActionFstSubgroup (F := F) (n := n) := by
  refine ⟨rightUpperPerm (F := F) u,
    rightUpperPerm_mem_rightActionSubgroup F u, ?_⟩
  intro x
  simp [rightUpperPerm_apply]

-- Adjacent Weyl with `-1` belongs via `rightWeylPerm`.
theorem weylSLUnit_neg_one_mem_rightActionFstSubgroup (F : Type u) [Field F]
    {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
    Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (-1 : Fˣ) ∈
      rightActionFstSubgroup (F := F) (n := n) := by
  refine ⟨rightWeylPerm (F := F) hij,
    rightWeylPerm_mem_rightActionSubgroup F hij, ?_⟩
  intro x
  simp [rightWeylPerm_fst]

-- Adjacent Weyl with `1` belongs as inverse of the `-1` generator.
theorem weylSLUnit_one_mem_rightActionFstSubgroup (F : Type u) [Field F]
    {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
    Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (1 : Fˣ) ∈
      rightActionFstSubgroup (F := F) (n := n) := by
  have h_neg :
      Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (-1 : Fˣ) ∈
        rightActionFstSubgroup (F := F) (n := n) :=
    weylSLUnit_neg_one_mem_rightActionFstSubgroup (F := F) hij
  have h_inv_mem :
      (Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (-1 : Fˣ))⁻¹ ∈
        rightActionFstSubgroup (F := F) (n := n) :=
    (rightActionFstSubgroup (F := F) (n := n)).inv_mem h_neg
  have h_eq :
      (Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (-1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (1 : Fˣ) := by
    have h_inv :
        (Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (-1 : Fˣ))⁻¹ =
          Matrix.GeneralLinearGroup.weylSLUnit (R := F) i j hij.ne (-(-1 : Fˣ)) :=
      Matrix.GeneralLinearGroup.weylSLUnit_inv (R := F) i j hij.ne (-1 : Fˣ)
    have h_neg_neg : (-(-1 : Fˣ) : Fˣ) = (1 : Fˣ) := by
      apply Units.ext
      simp
    rw [h_inv, h_neg_neg]
  rw [← h_eq]
  exact h_inv_mem

theorem upperWeylGenerators_subset_rightActionFstSubgroup (F : Type u) [Field F]
    (n : ℕ) :
    Matrix.GeneralLinearGroup.upperWeylGenerators (Fin n) (R := F) ⊆
      (rightActionFstSubgroup (F := F) (n := n) : Set _) := by
  intro s hs
  simp only [Matrix.GeneralLinearGroup.upperWeylGenerators, Set.mem_union,
    Set.mem_range] at hs
  rcases hs with ⟨u, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exact UpperElementary_toSLHom_mem_rightActionFstSubgroup (F := F) u
  · exact weylSLUnit_one_mem_rightActionFstSubgroup (F := F) hij

theorem upperWeylSubgroup_le_rightActionFstSubgroup (F : Type u) [Field F]
    (n : ℕ) :
    Matrix.GeneralLinearGroup.upperWeylSubgroup (Fin n) (R := F) ≤
      rightActionFstSubgroup (F := F) (n := n) := by
  unfold Matrix.GeneralLinearGroup.upperWeylSubgroup
  rw [Subgroup.closure_le]
  exact upperWeylGenerators_subset_rightActionFstSubgroup (F := F) n

theorem rightActionFstSubgroup_eq_top (F : Type u) [Field F] {n : ℕ}
    (hn : 2 ≤ n) :
    rightActionFstSubgroup (F := F) (n := n) = ⊤ := by
  have hNontrivial : Nontrivial (Fin n) := (Fin.nontrivial_iff_two_le.mpr hn)
  have h_top :
      Matrix.GeneralLinearGroup.upperWeylSubgroup (Fin n) (R := F) = ⊤ :=
    @Matrix.GeneralLinearGroup.upperWeylSubgroup_eq_top (Fin n) _ _ _ F _ hNontrivial
  have h_le :
      Matrix.GeneralLinearGroup.upperWeylSubgroup (Fin n) (R := F) ≤
        rightActionFstSubgroup (F := F) (n := n) :=
    upperWeylSubgroup_le_rightActionFstSubgroup (F := F) n
  rw [h_top] at h_le
  exact top_le_iff.mp h_le

theorem rightAction_reaches_base (F : Type u) [Field F] {n : ℕ}
    (hn : 2 ≤ n) (s : Matrix.SpecialLinearGroup (Fin n) F) :
    ∃ g : Equiv.Perm (X F n),
      g ∈ rightActionSubgroup (F := F) (n := n) ∧
        X.fst (g (X_one F n)) = s := by
  have h_mem : s ∈ rightActionFstSubgroup (F := F) (n := n) := by
    rw [rightActionFstSubgroup_eq_top (F := F) hn]
    exact Subgroup.mem_top s
  obtain ⟨g, hg_mem, hg⟩ := h_mem
  refine ⟨g, hg_mem, ?_⟩
  have h := hg (X_one F n)
  simp only [X_one_fst, one_mul] at h
  exact h

theorem rightAction_central_transitive (F : Type u) [Field F] {n : ℕ}
    (hn : 2 ≤ n) (x : X F n) :
    ∃ (g : Equiv.Perm (X F n)) (_ : g ∈ rightActionSubgroup (F := F) (n := n))
      (c : Multiplicative (MilnorK F 2)),
      (centralPerm (F := F) (n := n) c * g) (X_one F n) = x := by
  obtain ⟨g, hg_mem, hg_fst⟩ :=
    rightAction_reaches_base (F := F) hn (X.fst x)
  have hFst : X.fst (g (X_one F n)) = X.fst x := hg_fst
  obtain ⟨c, hc⟩ := central_fiber_exists (x := g (X_one F n)) (y := x) hFst
  refine ⟨g, hg_mem, c, ?_⟩
  have h_perm :
      (centralPerm (F := F) (n := n) c * g) (X_one F n) =
        central (F := F) (n := n) c (g (X_one F n)) := by
    simp [Equiv.Perm.mul_apply, centralPerm_apply]
  rw [h_perm, hc]

end MatsumotoTitsBruhatFiber

end
