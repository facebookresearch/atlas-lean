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

public import MathlibExt.KTheory.Milnor.ClassicalK2Laws
public import MathlibExt.GroupTheory.CentralExtension
public import MathlibExt.GroupTheory.NormalizedCocycleExtension
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# The Matsumoto diagonal extension

The product-one diagonal torus over a field carries an extension by Milnor `K₂`,
defined by a bilinear symbol cocycle. Explicit lifts of two-coordinate diagonal
elements satisfy the torus relations.
-/

@[expose] public section

open Finset

namespace MatsumotoDiagonalExtension

variable (F : Type*) [Field F] (n : ℕ)

def diagProdHom : (Fin n → Fˣ) →* Fˣ where
  toFun u := ∏ i : Fin n, u i
  map_one' := by simp
  map_mul' u v := by simp [Finset.prod_mul_distrib]

def diagSubgroup : Subgroup (Fin n → Fˣ) :=
  (diagProdHom F n).ker

abbrev Diag := ↥(diagSubgroup F n)

instance : Group (Diag F n) := Subgroup.toGroup _

theorem Diag.coe_one_val (i : Fin n) : ((1 : Diag F n) : Fin n → Fˣ) i = 1 := rfl

theorem Diag.prod_eq_one (u : Diag F n) : ∏ i : Fin n, (u : Fin n → Fˣ) i = 1 := by
  have h : (u : Fin n → Fˣ) ∈ (diagSubgroup F n) := u.property
  simp only [diagSubgroup, diagProdHom, MonoidHom.mem_ker] at h
  exact h

theorem Diag.val_mul_val (u v : Diag F n) (i : Fin n) :
    ((u * v : Diag F n) : Fin n → Fˣ) i = (u : Fin n → Fˣ) i * (v : Fin n → Fˣ) i := rfl

theorem Diag.val_inv_val (u : Diag F n) (i : Fin n) :
    ((u⁻¹ : Diag F n) : Fin n → Fˣ) i = ((u : Fin n → Fˣ) i)⁻¹ := rfl

theorem Diag.mul_comm (u v : Diag F n) : u * v = v * u := by
  apply Subtype.ext
  funext i
  change (u : Fin n → Fˣ) i * (v : Fin n → Fˣ) i =
      (v : Fin n → Fˣ) i * (u : Fin n → Fˣ) i
  exact _root_.mul_comm _ _

def alphaAdd (u v : Diag F n) : MilnorK F 2 :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i),
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)

def alpha (u v : Diag F n) : Multiplicative (MilnorK F 2) :=
  Multiplicative.ofAdd (alphaAdd F n u v)

theorem alphaAdd_one_left (v : Diag F n) : alphaAdd F n (1 : Diag F n) v = 0 := by
  unfold alphaAdd
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp [MilnorK.k2Symbol_one_left]

theorem alphaAdd_one_right (u : Diag F n) : alphaAdd F n u (1 : Diag F n) = 0 := by
  unfold alphaAdd
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp [MilnorK.k2Symbol_one_right]

theorem alpha_one_left (v : Diag F n) : alpha F n (1 : Diag F n) v = 1 := by
  unfold alpha
  rw [alphaAdd_one_left]
  rfl

theorem alpha_one_right (u : Diag F n) : alpha F n u (1 : Diag F n) = 1 := by
  unfold alpha
  rw [alphaAdd_one_right]
  rfl

theorem alphaAdd_mul_left (u₁ u₂ v : Diag F n) :
    alphaAdd F n (u₁ * u₂) v = alphaAdd F n u₁ v + alphaAdd F n u₂ v := by
  unfold alphaAdd
  have h : ∀ i : Fin n, (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u₁ * u₂ : Diag F n).val i) ((v : Fin n → Fˣ) j)) =
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u₁ : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u₂ : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) := by
    intro i
    have h1 : ((u₁ * u₂ : Diag F n).val i) = (u₁ : Fin n → Fˣ) i * (u₂ : Fin n → Fˣ) i := rfl
    calc ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
      MilnorK.k2Symbol F ((u₁ * u₂ : Diag F n).val i) ((v : Fin n → Fˣ) j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          (MilnorK.k2Symbol F ((u₁ : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j) + MilnorK.k2Symbol F ((u₂ :
          Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [h1, MilnorK.k2Symbol_mul_left]
        _ = _ := by rw [Finset.sum_add_distrib]
  calc ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u₁ * u₂ : Diag F n).val i) ((v : Fin n → Fˣ) j)
      = ∑ i : Fin n, ((∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u₁ : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
          (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            MilnorK.k2Symbol F ((u₂ : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j))) := by
          apply Finset.sum_congr rfl; intro i _; exact h i
      _ = (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u₁ : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            MilnorK.k2Symbol F ((u₂ : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) := by
          rw [Finset.sum_add_distrib]

theorem alphaAdd_mul_right (u v₁ v₂ : Diag F n) :
    alphaAdd F n u (v₁ * v₂) = alphaAdd F n u v₁ + alphaAdd F n u v₂ := by
  unfold alphaAdd
  have h : ∀ i : Fin n, (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₁ * v₂ : Diag F n).val j)) =
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₁ : Fin n → Fˣ) j)) +
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₂ : Fin n → Fˣ) j)) := by
    intro i
    calc ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₁ * v₂ : Diag F n).val j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          (MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₁ : Fin n → Fˣ) j) + MilnorK.k2Symbol F ((u :
          Fin n → Fˣ) i) ((v₂ : Fin n → Fˣ) j)) := by
          apply Finset.sum_congr rfl
          intro j _
          have hj : ((v₁ * v₂ : Diag F n).val j) = (v₁ : Fin n → Fˣ) j * (v₂ : Fin n → Fˣ) j := rfl
          rw [hj, MilnorK.k2Symbol_mul_right]
        _ = _ := by rw [Finset.sum_add_distrib]
  calc ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₁ * v₂ : Diag F n).val j)
      = ∑ i : Fin n, ((∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₁ : Fin n → Fˣ) j)) +
          (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v₂ : Fin n → Fˣ) j))) := by
          apply Finset.sum_congr rfl; intro i _; exact h i
      _ = _ := by rw [Finset.sum_add_distrib]

theorem alpha_mul_left (u₁ u₂ v : Diag F n) :
    alpha F n (u₁ * u₂) v = alpha F n u₁ v * alpha F n u₂ v := by
  unfold alpha
  rw [alphaAdd_mul_left, ofAdd_add]

theorem alpha_mul_right (u v₁ v₂ : Diag F n) :
    alpha F n u (v₁ * v₂) = alpha F n u v₁ * alpha F n u v₂ := by
  unfold alpha
  rw [alphaAdd_mul_right, ofAdd_add]

theorem alphaAdd_cocycle (u v w : Diag F n) :
    alphaAdd F n u v + alphaAdd F n (u * v) w = alphaAdd F n u (v * w) + alphaAdd F n v w := by
  have h1 : alphaAdd F n (u * v) w = alphaAdd F n u w + alphaAdd F n v w := alphaAdd_mul_left F n u
    v w
  have h2 : alphaAdd F n u (v * w) = alphaAdd F n u v + alphaAdd F n u w := alphaAdd_mul_right F n u
    v w
  calc alphaAdd F n u v + alphaAdd F n (u * v) w
      = alphaAdd F n u v + (alphaAdd F n u w + alphaAdd F n v w) := by rw [h1]
    _ = alphaAdd F n u v + alphaAdd F n u w + alphaAdd F n v w := by abel
    _ = (alphaAdd F n u v + alphaAdd F n u w) + alphaAdd F n v w := by abel
    _ = alphaAdd F n u (v * w) + alphaAdd F n v w := by rw [← h2]

theorem alpha_cocycle (u v w : Diag F n) :
    alpha F n u v * alpha F n (u * v) w = alpha F n u (v * w) * alpha F n v w := by
  unfold alpha
  have h := alphaAdd_cocycle F n u v w
  calc Multiplicative.ofAdd (alphaAdd F n u v) * Multiplicative.ofAdd (alphaAdd F n (u * v) w)
      = Multiplicative.ofAdd (alphaAdd F n u v + alphaAdd F n (u * v) w) := by
          rw [← ofAdd_add]
    _ = Multiplicative.ofAdd (alphaAdd F n u (v * w) + alphaAdd F n v w) := by rw [h]
    _ = Multiplicative.ofAdd (alphaAdd F n u (v * w)) * Multiplicative.ofAdd (alphaAdd F n v w) :=
      by
          rw [ofAdd_add]

abbrev matsumotoDiagonalCocycle : NormalizedCocycleExtension.NormalizedCocycle (Diag F n)
  (Multiplicative (MilnorK F 2)) where
  cocycle := alpha F n
  one_left := alpha_one_left F n
  one_right := alpha_one_right F n
  cocycle_assoc := alpha_cocycle F n

abbrev H (F : Type*) [Field F] (n : ℕ) := NormalizedCocycleExtension.Extension
  (matsumotoDiagonalCocycle (F := F) (n := n))

abbrev H.diag (h : H F n) : Diag F n := h.base

@[ext]
theorem H.ext {x y : H F n} (h1 : x.diag = y.diag) (h2 : x.coeff = y.coeff) : x = y :=
  NormalizedCocycleExtension.Extension.ext h1 h2

@[simp]
theorem H.mul_diag (x y : H F n) : (x * y).diag = x.diag * y.diag := rfl

@[simp]
theorem H.mul_coeff (x y : H F n) : (x * y).coeff = x.coeff * y.coeff * alpha F n x.diag y.diag :=
  rfl

@[simp]
theorem H.one_diag : (1 : H F n).diag = 1 := rfl

@[simp]
theorem H.one_coeff : (1 : H F n).coeff = 1 := rfl

@[simp]
theorem H.inv_diag (x : H F n) : (x⁻¹ : H F n).diag = x.diag⁻¹ := rfl

theorem H.inv_coeff (x : H F n) : (x⁻¹ : H F n).coeff = x.coeff⁻¹ * (alpha F n x.diag x.diag⁻¹)⁻¹ :=
  NormalizedCocycleExtension.inv_coeff' (c := matsumotoDiagonalCocycle (F := F) (n := n)) x

theorem alpha_inv_right (u v : Diag F n) : alpha F n u v⁻¹ = (alpha F n u v)⁻¹ := by
  have h : alpha F n u (v * v⁻¹) = alpha F n u v * alpha F n u v⁻¹ :=
    alpha_mul_right F n u v v⁻¹
  have h1 : v * v⁻¹ = (1 : Diag F n) := mul_inv_cancel v
  have h2 : alpha F n u (1 : Diag F n) = 1 := alpha_one_right F n u
  rw [h1, h2] at h
  have h_eq : alpha F n u v * alpha F n u v⁻¹ = 1 := h.symm
  have h_inv : alpha F n u v * (alpha F n u v)⁻¹ = 1 := mul_inv_cancel _
  have h3 : alpha F n u v * alpha F n u v⁻¹ =
      alpha F n u v * (alpha F n u v)⁻¹ := by
    rw [h_eq, h_inv]
  exact mul_left_cancel h3

theorem alpha_inv_left (u v : Diag F n) : alpha F n u⁻¹ v = (alpha F n u v)⁻¹ := by
  have h : alpha F n (u⁻¹ * u) v = alpha F n u⁻¹ v * alpha F n u v := by
    rw [alpha_mul_left]
  have h1 : u⁻¹ * u = (1 : Diag F n) := inv_mul_cancel u
  have h2 : alpha F n (1 : Diag F n) v = 1 := alpha_one_left F n v
  rw [h1, h2] at h
  have h_eq : alpha F n u⁻¹ v * alpha F n u v = 1 := h.symm
  have h_inv : (alpha F n u v)⁻¹ * alpha F n u v = 1 := inv_mul_cancel _
  have h3 : alpha F n u⁻¹ v * alpha F n u v =
      (alpha F n u v)⁻¹ * alpha F n u v := by
    rw [h_eq, h_inv]
  exact mul_right_cancel h3

theorem sum_k2Symbol_right (a : Fˣ) (v : Fin n → Fˣ) (s : Finset (Fin n)) :
    ∑ j ∈ s, MilnorK.k2Symbol F a (v j) = MilnorK.k2Symbol F a (∏ j ∈ s, v j) := by
  induction s using Finset.induction with
  | empty => simp [MilnorK.k2Symbol_one_right]
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, MilnorK.k2Symbol_mul_right]

theorem sum_k2Symbol_left (u : Fin n → Fˣ) (b : Fˣ) (s : Finset (Fin n)) :
    ∑ i ∈ s, MilnorK.k2Symbol F (u i) b = MilnorK.k2Symbol F (∏ i ∈ s, u i) b := by
  induction s using Finset.induction with
  | empty => simp [MilnorK.k2Symbol_one_left]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MilnorK.k2Symbol_mul_left]

def projHom : H F n →* Diag F n :=
  NormalizedCocycleExtension.projHom (matsumotoDiagonalCocycle (F := F) (n := n))

def inlHom : Multiplicative (MilnorK F 2) →* H F n :=
  NormalizedCocycleExtension.inlHom (matsumotoDiagonalCocycle (F := F) (n := n))

def diagExtension : GroupExtension (Multiplicative (MilnorK F 2)) (H F n) (Diag F n) :=
  NormalizedCocycleExtension.extension (matsumotoDiagonalCocycle (F := F) (n := n))

theorem diagExtension_isCentral : (diagExtension F n).IsCentral :=
  NormalizedCocycleExtension.isCentral (matsumotoDiagonalCocycle (F := F) (n := n))

open scoped commutatorElement

private lemma sum_k2Symbol_diag_prod (u v : Diag F n) (i : Fin n) :
    ∑ j ∈ (Finset.univ : Finset (Fin n)),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j) = 0 := by
  rw [sum_k2Symbol_right]
  have h : (∏ j : Fin n, (v : Fin n → Fˣ) j) = 1 := Diag.prod_eq_one F n v
  rw [h, MilnorK.k2Symbol_one_right]

private lemma alphaAdd_anticomm_aux (u v : Diag F n) :
    - alphaAdd F n v u =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i) := by
  unfold alphaAdd
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← MilnorK.k2Symbol_anticomm]

private lemma sum_filter_swap (u v : Diag F n) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i)) =
    (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) := by
  have h1 : ∀ i : Fin n, (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i)) =
      ∑ j ∈ Finset.univ,
        if j ≤ i then MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i) else 0 := by
    intro i
    rw [Finset.sum_filter]
  have h2 : ∀ i : Fin n, (∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) =
      ∑ j ∈ Finset.univ,
        if i ≤ j then MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j) else 0 := by
    intro i
    rw [Finset.sum_filter]
  calc ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i)
      = ∑ i : Fin n, ∑ j ∈ Finset.univ,
        if j ≤ i then MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i) else 0 := by
          apply Finset.sum_congr rfl; intro i _; exact h1 i
    _ = ∑ j : Fin n, ∑ i ∈ Finset.univ,
      if j ≤ i then MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => j ≤ i),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) j) ((v : Fin n → Fˣ) i) := by
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_filter]
    _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j) := by
          rfl

private lemma sum_le_add_ge (u v : Diag F n) (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
    (∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) =
    (∑ j ∈ Finset.univ, MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) i) := by
  let s_le := Finset.univ.filter (fun j : Fin n => j ≤ i)
  let s_ge := Finset.univ.filter (fun j : Fin n => i ≤ j)
  have h_union : s_le ∪ s_ge = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, s_le, s_ge]
    constructor
    · intro _; trivial
    · intro _
      by_cases hj : j ≤ i
      · left; exact hj
      · right; exact le_of_not_ge hj
  have h_inter : s_le ∩ s_ge = {i} := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, s_le, s_ge,
      Finset.mem_singleton]
    constructor
    · intro ⟨hj1, hj2⟩
      exact le_antisymm hj1 hj2
    · intro hj
      rw [hj]
      exact ⟨le_rfl, le_rfl⟩
  have h_sum := Finset.sum_union_inter (s₁ := s_le) (s₂ := s_ge) (f := fun j => MilnorK.k2Symbol F
    ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j))
  rw [h_union, h_inter, Finset.sum_singleton] at h_sum
  have h_symm := h_sum.symm
  simpa [add_comm] using h_symm

theorem alphaAdd_sub_eq_sum_diag (u v : Diag F n) :
    alphaAdd F n u v - alphaAdd F n v u =
      ∑ i : Fin n, MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) i) := by
  have h_anticomm := alphaAdd_anticomm_aux F n u v
  have h_swap := sum_filter_swap F n u v
  have h_neg : - alphaAdd F n v u =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j) := by
    rw [h_anticomm, h_swap]
  have h_sub : alphaAdd F n u v - alphaAdd F n v u =
      alphaAdd F n u v + (- alphaAdd F n v u) := by abel
  rw [h_sub, h_neg]
  unfold alphaAdd
  have h_combine : ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
      (∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) =
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) i) := by
    intro i
    have h_le_ge := sum_le_add_ge F n u v i
    have h_zero : (∑ j ∈ Finset.univ,
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) = 0 :=
      sum_k2Symbol_diag_prod F n u v i
    calc (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
      MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
        (∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
          MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j))
        = (∑ j ∈ Finset.univ, MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
          MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) i) := h_le_ge
      _ = MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) i) := by rw [h_zero, zero_add]
  calc (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j))
      = ∑ i : Fin n, ((∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j)) +
          (∑ j ∈ Finset.univ.filter (fun j => i ≤ j),
            MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) j))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin n, MilnorK.k2Symbol F ((u : Fin n → Fˣ) i) ((v : Fin n → Fˣ) i) := by
          apply Finset.sum_congr rfl; intro i _; exact h_combine i

theorem H_commutator_coeff (h k : H F n) :
    (⁅h, k⁆ : H F n).coeff = alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹ := by
  have h1 : h * k = ⟨h.diag * k.diag, h.coeff * k.coeff * alpha F n h.diag k.diag⟩ := rfl
  have h2 : (h * k * h⁻¹).diag = k.diag := by
    simp only [H.mul_diag, H.inv_diag]
    calc _ = k.diag * (h.diag * h.diag⁻¹) := by ac_rfl
      _ = k.diag := by rw [mul_inv_cancel, mul_one]
  have h3 : (h * k * h⁻¹).coeff =
      h.coeff * k.coeff * alpha F n h.diag k.diag * (h.coeff⁻¹ * (alpha F n h.diag h.diag⁻¹)⁻¹) *
        alpha F n (h.diag * k.diag) h.diag⁻¹ := by
    simp [H.inv_coeff]
  have h_alpha1 : alpha F n (h.diag * k.diag) h.diag⁻¹ =
      alpha F n h.diag h.diag⁻¹ * alpha F n k.diag h.diag⁻¹ := by
    rw [alpha_mul_left]
  rw [h_alpha1] at h3
  have h_coeff1 : h.coeff * k.coeff * alpha F n h.diag k.diag * (h.coeff⁻¹ * (alpha F n h.diag
    h.diag⁻¹)⁻¹) *
      (alpha F n h.diag h.diag⁻¹ * alpha F n k.diag h.diag⁻¹) =
    k.coeff * alpha F n h.diag k.diag * alpha F n k.diag h.diag⁻¹ := by
    calc h.coeff * k.coeff * alpha F n h.diag k.diag * (h.coeff⁻¹ * (alpha F n h.diag h.diag⁻¹)⁻¹) *
        (alpha F n h.diag h.diag⁻¹ * alpha F n k.diag h.diag⁻¹)
        = h.coeff * h.coeff⁻¹ * (k.coeff * alpha F n h.diag k.diag * ((alpha F n h.diag h.diag⁻¹)⁻¹
          * (alpha F n h.diag h.diag⁻¹ * alpha F n k.diag h.diag⁻¹))) := by ac_rfl
      _ = 1 * (k.coeff * alpha F n h.diag k.diag * ((alpha F n h.diag h.diag⁻¹)⁻¹ * (alpha F n
        h.diag h.diag⁻¹ * alpha F n k.diag h.diag⁻¹))) := by rw [mul_inv_cancel]
      _ = k.coeff * alpha F n h.diag k.diag * alpha F n k.diag h.diag⁻¹ := by
          have : (alpha F n h.diag h.diag⁻¹)⁻¹ * (alpha F n h.diag h.diag⁻¹ * alpha F n k.diag
            h.diag⁻¹) = alpha F n k.diag h.diag⁻¹ := by
            rw [← mul_assoc, inv_mul_cancel, one_mul]
          rw [this, one_mul]
  have h4 : (h * k * h⁻¹).coeff = k.coeff * alpha F n h.diag k.diag * alpha F n k.diag h.diag⁻¹ :=
    by
    rw [h3]
    exact h_coeff1
  have h5 : (⁅h, k⁆ : H F n) = (h * k * h⁻¹) * k⁻¹ := by
    simp [commutatorElement_def]
  have h6 : (⁅h, k⁆ : H F n).coeff =
      (k.coeff * alpha F n h.diag k.diag * alpha F n k.diag h.diag⁻¹) *
        (k.coeff⁻¹ * (alpha F n k.diag k.diag⁻¹)⁻¹) *
        alpha F n k.diag k.diag⁻¹ := by
    rw [h5]
    simp only [H.mul_coeff, H.inv_coeff, H.inv_diag, h4, h2]
  have h_alpha2 : alpha F n k.diag h.diag⁻¹ = (alpha F n k.diag h.diag)⁻¹ := alpha_inv_right F n
    k.diag h.diag
  rw [h_alpha2] at h6
  have h7 : (⁅h, k⁆ : H F n).coeff =
      k.coeff * alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹ *
        (k.coeff⁻¹ * (alpha F n k.diag k.diag⁻¹)⁻¹) * alpha F n k.diag k.diag⁻¹ := h6
  have h8 : (⁅h, k⁆ : H F n).coeff =
      alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹ := by
    calc (⁅h, k⁆ : H F n).coeff
        = k.coeff * alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹ *
          (k.coeff⁻¹ * (alpha F n k.diag k.diag⁻¹)⁻¹) * alpha F n k.diag k.diag⁻¹ := h7
      _ = k.coeff * (alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹) * k.coeff⁻¹ *
          ((alpha F n k.diag k.diag⁻¹)⁻¹ * alpha F n k.diag k.diag⁻¹) := by ac_rfl
      _ = k.coeff * (alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹) * k.coeff⁻¹ := by
          have : (alpha F n k.diag k.diag⁻¹)⁻¹ * alpha F n k.diag k.diag⁻¹ = 1 := inv_mul_cancel _
          rw [this, mul_one]
      _ = alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹ * (k.coeff * k.coeff⁻¹) := by ac_rfl
      _ = alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹ := by
          rw [mul_inv_cancel, mul_one]
  exact h8

theorem lemma12_1 (h k : H F n) :
    (⁅h, k⁆ : H F n) = (diagExtension F n).inl
      (Multiplicative.ofAdd (∑ i : Fin n,
        MilnorK.k2Symbol F ((h.diag : Fin n → Fˣ) i) ((k.diag : Fin n → Fˣ) i))) := by
  have h_coeff := H_commutator_coeff F n h k
  have h_alpha : alpha F n h.diag k.diag * (alpha F n k.diag h.diag)⁻¹ =
      Multiplicative.ofAdd (alphaAdd F n h.diag k.diag - alphaAdd F n k.diag h.diag) := by
    unfold alpha
    rw [ofAdd_sub, div_eq_mul_inv]
  have h_sum : alphaAdd F n h.diag k.diag - alphaAdd F n k.diag h.diag =
      ∑ i : Fin n, MilnorK.k2Symbol F ((h.diag : Fin n → Fˣ) i) ((k.diag : Fin n → Fˣ) i) :=
    alphaAdd_sub_eq_sum_diag F n h.diag k.diag
  have h_diag : (⁅h, k⁆ : H F n).diag = 1 := by
    simp [commutatorElement_def]
  apply H.ext
  · show (⁅h, k⁆ : H F n).diag = ((diagExtension F n).inl _).diag
    rw [h_diag]
    rfl
  · show (⁅h, k⁆ : H F n).coeff = ((diagExtension F n).inl _).coeff
    change (⁅h, k⁆ : H F n).coeff = Multiplicative.ofAdd (∑ i : Fin n,
      MilnorK.k2Symbol F ((h.diag : Fin n → Fˣ) i) ((k.diag : Fin n → Fˣ) i))
    rw [h_coeff, h_alpha, h_sum]

-- Raw cocycle on arbitrary tuples (no determinant condition)
def alphaAddAll (u v : Fin n → Fˣ) : MilnorK F 2 :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i), MilnorK.k2Symbol F (u i) (v j)

theorem alphaAdd_eq_alphaAddAll (u v : Diag F n) :
    alphaAdd F n u v = alphaAddAll F n (u : Fin n → Fˣ) (v : Fin n → Fˣ) := rfl

theorem alphaAddAll_one_left (v : Fin n → Fˣ) : alphaAddAll F n (1 : Fin n → Fˣ) v = 0 := by
  unfold alphaAddAll
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp [MilnorK.k2Symbol_one_left]

theorem alphaAddAll_one_right (u : Fin n → Fˣ) : alphaAddAll F n u (1 : Fin n → Fˣ) = 0 := by
  unfold alphaAddAll
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp [MilnorK.k2Symbol_one_right]

theorem alphaAddAll_mul_left (u₁ u₂ v : Fin n → Fˣ) :
    alphaAddAll F n (u₁ * u₂) v = alphaAddAll F n u₁ v + alphaAddAll F n u₂ v := by
  unfold alphaAddAll
  have h : ∀ i : Fin n, (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u₁ * u₂) i) (v j)) =
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u₁ i) (v j)) +
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u₂ i) (v j)) := by
    intro i
    calc ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F ((u₁ * u₂) i) (v j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          (MilnorK.k2Symbol F (u₁ i) (v j) + MilnorK.k2Symbol F (u₂ i) (v j)) := by
          apply Finset.sum_congr rfl
          intro j _
          change MilnorK.k2Symbol F (u₁ i * u₂ i) (v j) = _
          rw [MilnorK.k2Symbol_mul_left]
        _ = _ := by rw [Finset.sum_add_distrib]
  calc ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F ((u₁ * u₂) i) (v j)
      = ∑ i : Fin n, ((∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u₁ i) (v j)) +
          (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u₂ i) (v j))) := by
          apply Finset.sum_congr rfl; intro i _; exact h i
      _ = _ := by rw [Finset.sum_add_distrib]

theorem alphaAddAll_mul_right (u v₁ v₂ : Fin n → Fˣ) :
    alphaAddAll F n u (v₁ * v₂) = alphaAddAll F n u v₁ + alphaAddAll F n u v₂ := by
  unfold alphaAddAll
  have h : ∀ i : Fin n, (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F (u i) ((v₁ * v₂) j)) =
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u i) (v₁ j)) +
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u i) (v₂ j)) := by
    intro i
    calc ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u i) ((v₁ * v₂) j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          (MilnorK.k2Symbol F (u i) (v₁ j) + MilnorK.k2Symbol F (u i) (v₂ j)) := by
          apply Finset.sum_congr rfl
          intro j _
          change MilnorK.k2Symbol F (u i) (v₁ j * v₂ j) = _
          rw [MilnorK.k2Symbol_mul_right]
        _ = _ := by rw [Finset.sum_add_distrib]
  calc ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    MilnorK.k2Symbol F (u i) ((v₁ * v₂) j)
      = ∑ i : Fin n, ((∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u i) (v₁ j)) +
          (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), MilnorK.k2Symbol F (u i) (v₂ j))) := by
          apply Finset.sum_congr rfl; intro i _; exact h i
      _ = _ := by rw [Finset.sum_add_distrib]

theorem alphaAddAll_single (i j : Fin n) (u v : Fˣ) :
    alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u) (Pi.mulSingle (M := fun _ => Fˣ) j v) =
      if j ≤ i then MilnorK.k2Symbol F u v else 0 := by
  unfold alphaAddAll
  have h_outer : ∀ p ∈ (Finset.univ : Finset (Fin n)), p ≠ i →
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
        MilnorK.k2Symbol F ((Pi.mulSingle (M := fun _ => Fˣ) i u) p) ((Pi.mulSingle (M := fun _ =>
        Fˣ) j v) q)) = 0 := by
    intro p _ hp
    have hp1 : (Pi.mulSingle (M := fun _ => Fˣ) i u) p = 1 := by
      simp [hp]
    simp [hp1, MilnorK.k2Symbol_one_left]
  have h_inner : (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
    MilnorK.k2Symbol F ((Pi.mulSingle (M := fun _ => Fˣ) i u) i) ((Pi.mulSingle (M := fun _ => Fˣ) j
    v) q)) =
      if j ≤ i then MilnorK.k2Symbol F u v else 0 := by
    have hi : (Pi.mulSingle (M := fun _ => Fˣ) i u) i = u := by
      simp
    rw [hi]
    by_cases hj : j ≤ i
    · have hj_mem : j ∈ Finset.univ.filter (fun q : Fin n => q ≤ i) := by
        simp [Finset.mem_filter, hj]
      have h_zero : ∀ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), q ≠ j →
          MilnorK.k2Symbol F u ((Pi.mulSingle (M := fun _ => Fˣ) j v) q) = 0 := by
        intro q hq hqj
        have : (Pi.mulSingle (M := fun _ => Fˣ) j v) q = 1 := by
          simp [hqj]
        rw [this, MilnorK.k2Symbol_one_right]
      have h_single : ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
        MilnorK.k2Symbol F u ((Pi.mulSingle (M := fun _ => Fˣ) j v) q) =
          MilnorK.k2Symbol F u ((Pi.mulSingle (M := fun _ => Fˣ) j v) j) :=
        Finset.sum_eq_single_of_mem j hj_mem h_zero
      have h_single_eq : ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
        MilnorK.k2Symbol F u ((Pi.mulSingle (M := fun _ => Fˣ) j v) q) =
          MilnorK.k2Symbol F u v := by
        calc ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
          MilnorK.k2Symbol F u ((Pi.mulSingle (M := fun _ => Fˣ) j v) q)
            = MilnorK.k2Symbol F u ((Pi.mulSingle (M := fun _ => Fˣ) j v) j) := h_single
            _ = MilnorK.k2Symbol F u v := by simp
      rw [ite_eq_left hj]
      exact h_single_eq
    · have h_all_zero : ∀ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
      MilnorK.k2Symbol F u ((Pi.mulSingle (M := fun _ => Fˣ) j v) q) = 0 := by
        intro q hq
        have hqj : q ≠ j := by
          intro heq
          rw [heq] at hq
          have hq_le : j ≤ i := (Finset.mem_filter.mp hq).2
          exact hj hq_le
        have : (Pi.mulSingle (M := fun _ => Fˣ) j v) q = 1 := by
          simp [hqj]
        rw [this, MilnorK.k2Symbol_one_right]
      rw [ite_eq_right hj]
      exact Finset.sum_eq_zero h_all_zero
  have h_univ : ∑ p ∈ (Finset.univ : Finset (Fin n)),
    (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
    MilnorK.k2Symbol F ((Pi.mulSingle (M := fun _ => Fˣ) i u) p) ((Pi.mulSingle (M := fun _ => Fˣ) j
    v) q)) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
        MilnorK.k2Symbol F ((Pi.mulSingle (M := fun _ => Fˣ) i u) i) ((Pi.mulSingle (M := fun _ =>
        Fˣ) j v) q)) :=
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) h_outer
  calc ∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
    MilnorK.k2Symbol F ((Pi.mulSingle (M := fun _ => Fˣ) i u) p) ((Pi.mulSingle (M := fun _ => Fˣ) j
    v) q)
      = ∑ p ∈ (Finset.univ : Finset (Fin n)), ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
        MilnorK.k2Symbol F ((Pi.mulSingle (M := fun _ => Fˣ) i u) p) ((Pi.mulSingle (M := fun _ =>
        Fˣ) j v) q) := rfl
      _ = ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
        MilnorK.k2Symbol F ((Pi.mulSingle (M := fun _ => Fˣ) i u) i) ((Pi.mulSingle (M := fun _ =>
        Fˣ) j v) q) := h_univ
      _ = if j ≤ i then MilnorK.k2Symbol F u v else 0 := h_inner

def dTuple (i j : Fin n) (u : Fˣ) : Fin n → Fˣ :=
  Pi.mulSingle i u * Pi.mulSingle j u⁻¹

theorem dTuple_apply (i j : Fin n) (hij : i ≠ j) (u : Fˣ) (k : Fin n) :
    dTuple F n i j u k = if k = i then u else if k = j then u⁻¹ else 1 := by
  unfold dTuple
  by_cases hk1 : k = i
  · simp [hk1, hij]
  · by_cases hk2 : k = j
    · simp [hk2, hij.symm]
    · simp [hk1, hk2]

theorem dTuple_prod_eq_one (i j : Fin n) (_hij : i ≠ j) (u : Fˣ) :
    ∏ k : Fin n, dTuple F n i j u k = 1 := by
  unfold dTuple
  simp only [Pi.mul_apply]
  rw [Finset.prod_mul_distrib]
  have h1 : (∏ k : Fin n, Pi.mulSingle (M := fun _ => Fˣ) i u k) = u := by
    have h_eq : ∀ k : Fin n,
      Pi.mulSingle (M := fun _ => Fˣ) i u k = if k = i then u else (1 : Fˣ) := by
      intro k
      simp [Pi.mulSingle_apply, eq_comm]
    simp only [h_eq]
    have h_prod : (∏ k : Fin n,
      (if k = i then u else (1 : Fˣ))) = (if i = i then u else (1 : Fˣ)) :=
      Fintype.prod_eq_single i (fun k hk => by simp [hk])
    simp [h_prod]
  have h2 : (∏ k : Fin n, Pi.mulSingle (M := fun _ => Fˣ) j u⁻¹ k) = u⁻¹ := by
    have h_eq : ∀ k : Fin n,
      Pi.mulSingle (M := fun _ => Fˣ) j u⁻¹ k = if k = j then u⁻¹ else (1 : Fˣ) := by
      intro k
      simp [Pi.mulSingle_apply, eq_comm]
    simp only [h_eq]
    have h_prod : (∏ k : Fin n,
      (if k = j then u⁻¹ else (1 : Fˣ))) = (if j = j then u⁻¹ else (1 : Fˣ)) :=
      Fintype.prod_eq_single j (fun k hk => by simp [hk])
    simp [h_prod]
  calc (∏ k : Fin n, Pi.mulSingle (M := fun _ => Fˣ) i u k) * (∏ k : Fin n,
    Pi.mulSingle (M := fun _ => Fˣ) j u⁻¹ k)
      = u * u⁻¹ := by rw [h1, h2]
    _ = 1 := mul_inv_cancel u

def d_ij (i j : Fin n) (hij : i ≠ j) (u : Fˣ) : Diag F n :=
  ⟨dTuple F n i j u, by
    simp [diagSubgroup, diagProdHom, MonoidHom.mem_ker, dTuple_prod_eq_one F n i j hij u]⟩

theorem d_ij_val (i j : Fin n) (hij : i ≠ j) (u : Fˣ) (k : Fin n) :
    (d_ij F n i j hij u : Fin n → Fˣ) k = if k = i then u else if k = j then u⁻¹ else 1 :=
  dTuple_apply F n i j hij u k

theorem d_ij_mul (i j : Fin n) (hij : i ≠ j) (u v : Fˣ) :
    d_ij F n i j hij (u * v) = d_ij F n i j hij u * d_ij F n i j hij v := by
  apply Subtype.ext
  funext k
  simp only [d_ij_val, Diag.val_mul_val]
  by_cases hk1 : k = i
  · simp [hk1]
  · by_cases hk2 : k = j
    · simp_all [_root_.mul_comm]
    · simp [hk1, hk2]

theorem d_ij_inv (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    d_ij F n i j hij u⁻¹ = (d_ij F n i j hij u)⁻¹ := by
  apply Subtype.ext
  funext k
  simp only [d_ij_val, Diag.val_inv_val]
  by_cases hk1 : k = i
  · simp [hk1]
  · by_cases hk2 : k = j
    · simp [hk2, hij.symm]
    · simp [hk1, hk2]

theorem d_ij_inv_eq_d_ji (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    (d_ij F n i j hij u)⁻¹ = d_ij F n j i hij.symm u := by
  apply Subtype.ext
  funext k
  simp only [d_ij_val, Diag.val_inv_val]
  by_cases hk1 : k = i
  · simp [hk1, hij]
  · by_cases hk2 : k = j
    · simp [hk2, hij.symm]
    · simp [hk1, hk2]

theorem d_ij_one (i j : Fin n) (hij : i ≠ j) :
    d_ij F n i j hij (1 : Fˣ) = 1 := by
  apply Subtype.ext
  funext k
  simp [d_ij_val]

def h_ij (i j : Fin n) (hij : i ≠ j) (u : Fˣ) : H F n :=
  if _h : i < j then ⟨d_ij F n i j hij u, 1⟩ else ⟨d_ij F n i j hij u,
    Multiplicative.ofAdd (MilnorK.k2Symbol F u u)⟩

theorem h_ij_diag (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    (h_ij F n i j hij u).diag = d_ij F n i j hij u := by
  unfold h_ij
  split <;> rfl

theorem h_ij_coeff_lt {i j : Fin n} (hij : i ≠ j) (u : Fˣ) (h : i < j) :
    (h_ij F n i j hij u).coeff = 1 := by
  unfold h_ij
  simp [h]

theorem h_ij_coeff_gt {i j : Fin n} (hij : i ≠ j) (u : Fˣ) (h : ¬ i < j) :
    (h_ij F n i j hij u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol F u u) := by
  unfold h_ij
  simp [h]

theorem alphaAdd_d_ij (i j : Fin n) (hij : i ≠ j) (u v : Fˣ) :
    alphaAdd F n (d_ij F n i j hij u) (d_ij F n i j hij v) = MilnorK.k2Symbol F u v := by
  have h_eq : alphaAdd F n (d_ij F n i j hij u) (d_ij F n i j hij v) =
      alphaAddAll F n (dTuple F n i j u) (dTuple F n i j v) := rfl
  rw [h_eq]
  unfold dTuple
  rw [alphaAddAll_mul_right, alphaAddAll_mul_left, alphaAddAll_mul_left]
  have h1 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u) (Pi.mulSingle (M := fun _ => Fˣ) i
    v) = MilnorK.k2Symbol F u v := by
    rw [alphaAddAll_single]; simp
  have h2 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u) (Pi.mulSingle (M := fun _ => Fˣ) j
    v⁻¹) =
      if j ≤ i then MilnorK.k2Symbol F u v⁻¹ else (0 : MilnorK F 2) := by
    rw [alphaAddAll_single]
  have h3 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) j u⁻¹) (Pi.mulSingle (M := fun _ => Fˣ)
    i v) =
      if i ≤ j then MilnorK.k2Symbol F u⁻¹ v else (0 : MilnorK F 2) := by
    rw [alphaAddAll_single]
  have h4 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) j u⁻¹) (Pi.mulSingle (M := fun _ => Fˣ)
    j v⁻¹) = MilnorK.k2Symbol F u⁻¹ v⁻¹ := by
    rw [alphaAddAll_single]; simp
  rw [h1, h2, h3, h4]
  simp only [MilnorK.k2Symbol_inv_right, MilnorK.k2Symbol_inv_left]
  by_cases hij_le : j ≤ i
  · have h_not_ge : ¬ i ≤ j := fun h => hij (le_antisymm h hij_le)
    simp only [hij_le, h_not_ge, ite_true, ite_false]
    abel
  · have hij_ge : i ≤ j := le_of_not_ge hij_le
    simp only [hij_le, hij_ge, ite_true, ite_false]
    abel

theorem alphaAdd_d_ij_swap (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    alphaAdd F n (d_ij F n i j hij u) (d_ij F n j i hij.symm u) = - MilnorK.k2Symbol F u u := by
  have h_eq : alphaAdd F n (d_ij F n i j hij u) (d_ij F n j i hij.symm u) =
      alphaAddAll F n (dTuple F n i j u) (dTuple F n j i u) := rfl
  rw [h_eq]
  unfold dTuple
  rw [alphaAddAll_mul_right, alphaAddAll_mul_left, alphaAddAll_mul_left]
  have h1 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u) (Pi.mulSingle (M := fun _ => Fˣ) j
    u) =
      if j ≤ i then MilnorK.k2Symbol F u u else (0 : MilnorK F 2) := by
    rw [alphaAddAll_single]
  have h2 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u) (Pi.mulSingle (M := fun _ => Fˣ) i
    u⁻¹) = MilnorK.k2Symbol F u u⁻¹ := by
    rw [alphaAddAll_single]; simp
  have h3 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) j u⁻¹) (Pi.mulSingle (M := fun _ => Fˣ)
    j u) = MilnorK.k2Symbol F u⁻¹ u := by
    rw [alphaAddAll_single]; simp
  have h4 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) j u⁻¹) (Pi.mulSingle (M := fun _ => Fˣ)
    i u⁻¹) =
      if i ≤ j then MilnorK.k2Symbol F u⁻¹ u⁻¹ else (0 : MilnorK F 2) := by
    rw [alphaAddAll_single]
  rw [h1, h2, h3, h4]
  simp only [MilnorK.k2Symbol_inv_right, MilnorK.k2Symbol_inv_left]
  by_cases hij_le : j ≤ i
  · have h_not_ge : ¬ i ≤ j := fun h => hij (le_antisymm h hij_le)
    simp only [hij_le, h_not_ge, ite_true, ite_false]
    abel
  · have hij_ge : i ≤ j := le_of_not_ge hij_le
    simp only [hij_le, hij_ge, ite_true, ite_false]
    abel

theorem h_ij_inv (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    h_ij F n j i hij.symm u = (h_ij F n i j hij u)⁻¹ := by
  have h_eq : h_ij F n j i hij.symm u * h_ij F n i j hij u = (1 : H F n) := by
    have h_alpha_ji : alpha F n (d_ij F n j i hij.symm u) (d_ij F n i j hij u) =
      Multiplicative.ofAdd (- MilnorK.k2Symbol F u u) := by
      unfold alpha
      rw [alphaAdd_d_ij_swap F n j i hij.symm u]
    apply H.ext
    · simp only [H.mul_diag, h_ij_diag]
      have h : d_ij F n j i hij.symm u * d_ij F n i j hij u = (1 : Diag F n) := by
        have h1 : d_ij F n j i hij.symm u = (d_ij F n i j hij u)⁻¹ := (d_ij_inv_eq_d_ji F n i j hij
          u).symm
        rw [h1, inv_mul_cancel]
      calc d_ij F n j i hij.symm u * d_ij F n i j hij u = (1 : Diag F n) := h
        _ = (1 : H F n).diag := rfl
    · simp only [H.mul_coeff, h_ij_diag, H.one_coeff]
      by_cases h_lt : i < j
      · have h_gt : ¬ j < i := not_lt.mpr (le_of_lt h_lt)
        rw [h_ij_coeff_gt F n hij.symm u h_gt, h_ij_coeff_lt F n hij u h_lt, h_alpha_ji]
        simp
      · have h_le : j ≤ i := le_of_not_gt h_lt
        have h_lt_ji : j < i := lt_of_le_of_ne h_le hij.symm
        rw [h_ij_coeff_lt F n hij.symm u h_lt_ji, h_ij_coeff_gt F n hij u h_lt, h_alpha_ji]
        simp
  calc h_ij F n j i hij.symm u
      = h_ij F n j i hij.symm u * 1 := by rw [mul_one]
    _ = h_ij F n j i hij.symm u * (h_ij F n i j hij u * (h_ij F n i j hij u)⁻¹) := by rw
      [mul_inv_cancel]
    _ = (h_ij F n j i hij.symm u * h_ij F n i j hij u) * (h_ij F n i j hij u)⁻¹ := by rw [mul_assoc]
    _ = 1 * (h_ij F n i j hij u)⁻¹ := by rw [h_eq]
    _ = (h_ij F n i j hij u)⁻¹ := by rw [one_mul]

theorem h_ij_mul (i j : Fin n) (hij : i ≠ j) (u v : Fˣ) :
    h_ij F n i j hij u * h_ij F n i j hij v = (diagExtension F n).inl (Multiplicative.ofAdd
      (MilnorK.k2Symbol F u v)) * h_ij F n i j hij (u * v) := by
  have h_diag : d_ij F n i j hij u * d_ij F n i j hij v = d_ij F n i j hij (u * v) := by
    rw [← d_ij_mul]
  have h_alpha : alpha F n (d_ij F n i j hij u) (d_ij F n i j hij v) = Multiplicative.ofAdd
    (MilnorK.k2Symbol F u v) := by
    unfold alpha
    rw [alphaAdd_d_ij]
  have h_coeff : (h_ij F n i j hij u).coeff * (h_ij F n i j hij v).coeff * alpha F n (d_ij F n i j
    hij u) (d_ij F n i j hij v) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u v) * (h_ij F n i j hij (u * v)).coeff := by
    by_cases h_lt : i < j
    · rw [h_ij_coeff_lt F n hij u h_lt, h_ij_coeff_lt F n hij v h_lt,
          h_ij_coeff_lt F n hij (u * v) h_lt, h_alpha]
      simp
    · rw [h_ij_coeff_gt F n hij u h_lt, h_ij_coeff_gt F n hij v h_lt,
          h_ij_coeff_gt F n hij (u * v) h_lt, h_alpha]
      have h_uv : MilnorK.k2Symbol F (u * v) (u * v) = MilnorK.k2Symbol F u u + MilnorK.k2Symbol F v
        v := by
        calc MilnorK.k2Symbol F (u * v) (u * v)
            = MilnorK.k2Symbol F (u * v) u + MilnorK.k2Symbol F (u * v) v := by rw
              [MilnorK.k2Symbol_mul_right]
          _ = (MilnorK.k2Symbol F u u + MilnorK.k2Symbol F v u) + (MilnorK.k2Symbol F u v +
            MilnorK.k2Symbol F v v) := by
              rw [MilnorK.k2Symbol_mul_left, MilnorK.k2Symbol_mul_left]
          _ = MilnorK.k2Symbol F u u + MilnorK.k2Symbol F v v := by
              have h_swap : MilnorK.k2Symbol F v u = - MilnorK.k2Symbol F u v :=
                MilnorK.k2Symbol_anticomm _ _ _
              rw [h_swap]; abel
      simp only [ofAdd_add, h_uv]
      ac_rfl
  apply H.ext
  · simp only [H.mul_diag, h_ij_diag]
    have h_inl : ((diagExtension F n).inl (Multiplicative.ofAdd (MilnorK.k2Symbol F u v))).diag = (1
      : Diag F n) := rfl
    change d_ij F n i j hij u * d_ij F n i j hij v = (1 : Diag F n) * d_ij F n i j hij (u * v)
    rw [h_diag, one_mul]
  · have h_left : (h_ij F n i j hij u * h_ij F n i j hij v).coeff =
        (h_ij F n i j hij u).coeff * (h_ij F n i j hij v).coeff * alpha F n (d_ij F n i j hij u)
          (d_ij F n i j hij v) := by
      simp [h_ij_diag]
    have h_right : ((diagExtension F n).inl (Multiplicative.ofAdd (MilnorK.k2Symbol F u v)) * h_ij F
      n i j hij (u * v)).coeff =
        Multiplicative.ofAdd (MilnorK.k2Symbol F u v) * (h_ij F n i j hij (u * v)).coeff * alpha F n
          (1 : Diag F n) (d_ij F n i j hij (u * v)) := by
      simp [h_ij_diag]
      rfl
    have h_alpha_one : alpha F n (1 : Diag F n) (d_ij F n i j hij (u * v)) = 1 := alpha_one_left F n
      _
    rw [h_left, h_right, h_alpha_one, mul_one]
    exact h_coeff

private theorem d_ij_three_diag (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u : Fˣ) :
    d_ij F n k i hik.symm u * d_ij F n j k hjk u = d_ij F n j i hij.symm u := by
  apply Subtype.ext
  funext l
  simp only [d_ij_val, Diag.val_mul_val]
  by_cases hk : l = k
  · subst hk
    simp [hik.symm, hjk.symm]
  · by_cases hj : l = j
    · subst hj
      simp [hk, hij.symm]
    · by_cases hi : l = i
      · subst hi
        simp [hk, hj]
      · simp [hk, hj, hi]

private theorem alphaAdd_d_ki_d_jk (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) (u : Fˣ) :
    alphaAdd F n (d_ij F n k i hik.symm u) (d_ij F n j k hjk u) =
      (if j ≤ k then MilnorK.k2Symbol F u u else 0) +
      MilnorK.k2Symbol F u u⁻¹ +
      (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else 0) +
      (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else 0) := by
  have h_eq : alphaAdd F n (d_ij F n k i hik.symm u) (d_ij F n j k hjk u) =
      alphaAddAll F n (dTuple F n k i u) (dTuple F n j k u) := rfl
  rw [h_eq]
  unfold dTuple
  have h_left : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) k u * Pi.mulSingle i u⁻¹)
      (Pi.mulSingle j u * Pi.mulSingle k u⁻¹) =
      alphaAddAll F n (Pi.mulSingle k u) (Pi.mulSingle j u * Pi.mulSingle k u⁻¹) +
      alphaAddAll F n (Pi.mulSingle i u⁻¹) (Pi.mulSingle j u * Pi.mulSingle k u⁻¹) := by
    rw [alphaAddAll_mul_left]
  rw [h_left]
  have h1 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) k u)
      (Pi.mulSingle j u * Pi.mulSingle k u⁻¹) =
      alphaAddAll F n (Pi.mulSingle k u) (Pi.mulSingle j u) +
      alphaAddAll F n (Pi.mulSingle k u) (Pi.mulSingle k u⁻¹) := by
    rw [alphaAddAll_mul_right]
  have h2 : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u⁻¹)
      (Pi.mulSingle j u * Pi.mulSingle k u⁻¹) =
      alphaAddAll F n (Pi.mulSingle i u⁻¹) (Pi.mulSingle j u) +
      alphaAddAll F n (Pi.mulSingle i u⁻¹) (Pi.mulSingle k u⁻¹) := by
    rw [alphaAddAll_mul_right]
  rw [h1, h2]
  have hk_j : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) k u) (Pi.mulSingle j u) =
      if j ≤ k then MilnorK.k2Symbol F u u else 0 := by
    rw [alphaAddAll_single]
  have hk_k : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) k u) (Pi.mulSingle k u⁻¹) =
      MilnorK.k2Symbol F u u⁻¹ := by
    rw [alphaAddAll_single]; simp
  have hi_j : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u⁻¹) (Pi.mulSingle j u) =
      if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else 0 := by
    rw [alphaAddAll_single]
  have hi_k : alphaAddAll F n (Pi.mulSingle (M := fun _ => Fˣ) i u⁻¹) (Pi.mulSingle k u⁻¹) =
      if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else 0 := by
    rw [alphaAddAll_single]
  rw [hk_j, hk_k, hi_j, hi_k]
  abel

theorem h_ij_three (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Fˣ) :
    h_ij F n j i hij.symm u = h_ij F n k i hik.symm u * h_ij F n j k hjk u := by
  have h_diag : d_ij F n k i hik.symm u * d_ij F n j k hjk u = d_ij F n j i hij.symm u :=
    d_ij_three_diag F n i j k hij hik hjk u
  have h_s : MilnorK.k2Symbol F u u⁻¹ = -MilnorK.k2Symbol F u u := MilnorK.k2Symbol_inv_right F u u
  have h_s2 : MilnorK.k2Symbol F u⁻¹ u = -MilnorK.k2Symbol F u u := MilnorK.k2Symbol_inv_left F u u
  have h_s3 : MilnorK.k2Symbol F u⁻¹ u⁻¹ = MilnorK.k2Symbol F u u := by
    calc MilnorK.k2Symbol F u⁻¹ u⁻¹
        = -MilnorK.k2Symbol F u u⁻¹ := by rw [MilnorK.k2Symbol_inv_left]
      _ = -(-MilnorK.k2Symbol F u u) := by rw [MilnorK.k2Symbol_inv_right]
      _ = MilnorK.k2Symbol F u u := by abel
  apply H.ext
  · simp only [H.mul_diag, h_ij_diag, h_diag]
  · simp only [H.mul_coeff, h_ij_diag]
    have h_alpha_exp := alphaAdd_d_ki_d_jk F n i j k hik hjk u
    have h_alpha : alpha F n (d_ij F n k i hik.symm u) (d_ij F n j k hjk u) =
        Multiplicative.ofAdd
          ((if j ≤ k then MilnorK.k2Symbol F u u else 0) +
           MilnorK.k2Symbol F u u⁻¹ +
           (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else 0) +
           (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else 0)) := by
      unfold alpha
      rw [h_alpha_exp]
    by_cases h_ij_lt : i < j
    · by_cases h_ik_lt : i < k
      · by_cases h_jk_lt : j < k
        · -- i<j<k  alpha 0
          have h_coeff_ji : (h_ij F n j i hij.symm u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol
            F u u) := by
            have h : ¬ j < i := by omega
            simp [h_ij, h]
          have h_coeff_ki : (h_ij F n k i hik.symm u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol
            F u u) := by
            have h : ¬ k < i := by omega
            simp [h_ij, h]
          have h_coeff_jk : (h_ij F n j k hjk u).coeff = (1 : Multiplicative (MilnorK F 2)) := by
            simp [h_ij, h_jk_lt]
          have h_jk_le : j ≤ k := le_of_lt h_jk_lt
          have h_ji_nle : ¬ j ≤ i := by omega
          have h_ki_nle : ¬ k ≤ i := by omega
          have h1 : (if j ≤ k then MilnorK.k2Symbol F u u else (0 : MilnorK F 2)) = MilnorK.k2Symbol
            F u u := by simp [h_jk_le]
          have h2 : (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else (0 : MilnorK F 2)) = (0 : MilnorK F
            2) := by simp [h_ji_nle]
          have h3 : (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else (0 : MilnorK F 2)) = (0 : MilnorK
            F 2) := by simp [h_ki_nle]
          rw [h_coeff_ji, h_coeff_ki, h_coeff_jk, h_alpha, h1, h2, h3, h_s]
          simp
        · -- i<k<j  alpha -s
          have h_coeff_ji : (h_ij F n j i hij.symm u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol
            F u u) := by
            have h : ¬ j < i := by omega
            simp [h_ij, h]
          have h_coeff_ki : (h_ij F n k i hik.symm u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol
            F u u) := by
            have h : ¬ k < i := by omega
            simp [h_ij, h]
          have h_coeff_jk : (h_ij F n j k hjk u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol F u
            u) := by
            have h : ¬ j < k := h_jk_lt
            simp [h_ij, h]
          have h_jk_nle : ¬ j ≤ k := by omega
          have h_ji_nle : ¬ j ≤ i := by omega
          have h_ki_nle : ¬ k ≤ i := by omega
          have h1 : (if j ≤ k then MilnorK.k2Symbol F u u else (0 : MilnorK F 2)) = (0 : MilnorK F
            2) := by simp [h_jk_nle]
          have h2 : (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else (0 : MilnorK F 2)) = (0 : MilnorK F
            2) := by simp [h_ji_nle]
          have h3 : (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else (0 : MilnorK F 2)) = (0 : MilnorK
            F 2) := by simp [h_ki_nle]
          rw [h_coeff_ji, h_coeff_ki, h_coeff_jk, h_alpha, h1, h2, h3, h_s]
          simp only [zero_add, add_zero]
          simp only [ofAdd_neg]
          have h_eq : MilnorK.k2Symbol F u u + MilnorK.k2Symbol F u u + -MilnorK.k2Symbol F u u =
            MilnorK.k2Symbol F u u := by abel
          calc Multiplicative.ofAdd (MilnorK.k2Symbol F u u)
              = Multiplicative.ofAdd (MilnorK.k2Symbol F u u + MilnorK.k2Symbol F u u +
                -MilnorK.k2Symbol F u u) := by rw [h_eq]
            _ = Multiplicative.ofAdd (MilnorK.k2Symbol F u u) * Multiplicative.ofAdd
              (MilnorK.k2Symbol F u u) * Multiplicative.ofAdd (-MilnorK.k2Symbol F u u) := by
                rw [ofAdd_add, ofAdd_add, ofAdd_neg]
      · -- k<i<j  alpha 0
        have h_ki_lt : k < i := by omega
        have h_coeff_ji : (h_ij F n j i hij.symm u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol F
          u u) := by
          have h : ¬ j < i := by omega
          simp [h_ij, h]
        have h_coeff_ki : (h_ij F n k i hik.symm u).coeff = (1 : Multiplicative (MilnorK F 2)) := by
          simp [h_ij, h_ki_lt]
        have h_coeff_jk : (h_ij F n j k hjk u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol F u u)
          := by
          have h : ¬ j < k := by omega
          simp [h_ij, h]
        have h_jk_nle : ¬ j ≤ k := by omega
        have h_ji_nle : ¬ j ≤ i := by omega
        have h_ki_le : k ≤ i := le_of_lt h_ki_lt
        have h1 : (if j ≤ k then MilnorK.k2Symbol F u u else (0 : MilnorK F 2)) = (0 : MilnorK F 2)
          := by simp [h_jk_nle]
        have h2 : (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else (0 : MilnorK F 2)) = (0 : MilnorK F
          2) := by simp [h_ji_nle]
        have h3 : (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else (0 : MilnorK F 2)) =
          MilnorK.k2Symbol F u⁻¹ u⁻¹ := by simp [h_ki_le]
        rw [h_coeff_ji, h_coeff_ki, h_coeff_jk, h_alpha, h1, h2, h3, h_s, h_s3]
        simp
    · -- ¬i<j => j<i
      by_cases h_ik_lt : i < k
      · by_cases h_jk_lt : j < k
        · -- j<i<k  alpha -s
          have h_coeff_ji : (h_ij F n j i hij.symm u).coeff = (1 : Multiplicative (MilnorK F 2)) :=
            by
            have h : j < i := by omega
            simp [h_ij, h]
          have h_coeff_ki : (h_ij F n k i hik.symm u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol
            F u u) := by
            have h : ¬ k < i := by omega
            simp [h_ij, h]
          have h_coeff_jk : (h_ij F n j k hjk u).coeff = (1 : Multiplicative (MilnorK F 2)) := by
            simp [h_ij, h_jk_lt]
          have h_jk_le : j ≤ k := le_of_lt h_jk_lt
          have h_ji_le : j ≤ i := by omega
          have h_ki_nle : ¬ k ≤ i := by omega
          have h1 : (if j ≤ k then MilnorK.k2Symbol F u u else (0 : MilnorK F 2)) = MilnorK.k2Symbol
            F u u := by simp [h_jk_le]
          have h2 : (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else (0 : MilnorK F 2)) =
            MilnorK.k2Symbol F u⁻¹ u := by simp [h_ji_le]
          have h3 : (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else (0 : MilnorK F 2)) = (0 : MilnorK
            F 2) := by simp [h_ki_nle]
          rw [h_coeff_ji, h_coeff_ki, h_coeff_jk, h_alpha, h1, h2, h3, h_s, h_s2]
          simp [ofAdd_neg]
        · -- j<i, i<k, ¬j<k => impossible
          exfalso
          exact h_jk_lt (lt_trans (by omega : j < i) h_ik_lt)
      · -- ¬i<k => k≤i
        by_cases h_jk_lt : j < k
        · -- j<k<i  alpha 0
          have h_coeff_ji : (h_ij F n j i hij.symm u).coeff = (1 : Multiplicative (MilnorK F 2)) :=
            by
            have h : j < i := by omega
            simp [h_ij, h]
          have h_coeff_ki : (h_ij F n k i hik.symm u).coeff = (1 : Multiplicative (MilnorK F 2)) :=
            by
            have h : k < i := by omega
            simp [h_ij, h]
          have h_coeff_jk : (h_ij F n j k hjk u).coeff = (1 : Multiplicative (MilnorK F 2)) := by
            simp [h_ij, h_jk_lt]
          have h_jk_le : j ≤ k := le_of_lt h_jk_lt
          have h_ji_le : j ≤ i := by omega
          have h_ki_le : k ≤ i := by omega
          have h1 : (if j ≤ k then MilnorK.k2Symbol F u u else (0 : MilnorK F 2)) = MilnorK.k2Symbol
            F u u := by simp [h_jk_le]
          have h2 : (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else (0 : MilnorK F 2)) =
            MilnorK.k2Symbol F u⁻¹ u := by simp [h_ji_le]
          have h3 : (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else (0 : MilnorK F 2)) =
            MilnorK.k2Symbol F u⁻¹ u⁻¹ := by simp [h_ki_le]
          rw [h_coeff_ji, h_coeff_ki, h_coeff_jk, h_alpha, h1, h2, h3, h_s, h_s2, h_s3]
          have h_zero : MilnorK.k2Symbol F u u + -MilnorK.k2Symbol F u u + -MilnorK.k2Symbol F u u +
            MilnorK.k2Symbol F u u = (0 : MilnorK F 2) := by abel
          simp [ofAdd_zero]
        · -- k<j<i  alpha -s
          have h_coeff_ji : (h_ij F n j i hij.symm u).coeff = (1 : Multiplicative (MilnorK F 2)) :=
            by
            have h : j < i := by omega
            simp [h_ij, h]
          have h_coeff_ki : (h_ij F n k i hik.symm u).coeff = (1 : Multiplicative (MilnorK F 2)) :=
            by
            have h : k < i := by omega
            simp [h_ij, h]
          have h_coeff_jk : (h_ij F n j k hjk u).coeff = Multiplicative.ofAdd (MilnorK.k2Symbol F u
            u) := by
            have h : ¬ j < k := h_jk_lt
            simp [h_ij, h]
          have h_jk_nle : ¬ j ≤ k := by omega
          have h_ji_le : j ≤ i := by omega
          have h_ki_le : k ≤ i := by omega
          have h1 : (if j ≤ k then MilnorK.k2Symbol F u u else (0 : MilnorK F 2)) = (0 : MilnorK F
            2) := by simp [h_jk_nle]
          have h2 : (if j ≤ i then MilnorK.k2Symbol F u⁻¹ u else (0 : MilnorK F 2)) =
            MilnorK.k2Symbol F u⁻¹ u := by simp [h_ji_le]
          have h3 : (if k ≤ i then MilnorK.k2Symbol F u⁻¹ u⁻¹ else (0 : MilnorK F 2)) =
            MilnorK.k2Symbol F u⁻¹ u⁻¹ := by simp [h_ki_le]
          rw [h_coeff_ji, h_coeff_ki, h_coeff_jk, h_alpha, h1, h2, h3, h_s, h_s2, h_s3]
          simp [ofAdd_neg]

theorem h_ij_three_inv (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Fˣ) :
    h_ij F n j i hij.symm u = (h_ij F n i k hik u)⁻¹ * (h_ij F n k j hjk.symm u)⁻¹ := by
  calc h_ij F n j i hij.symm u
      = h_ij F n k i hik.symm u * h_ij F n j k hjk u := h_ij_three F n i j k hij hik hjk u
    _ = (h_ij F n i k hik u)⁻¹ * h_ij F n j k hjk u := by rw [← h_ij_inv F n i k hik u]
    _ = (h_ij F n i k hik u)⁻¹ * (h_ij F n k j hjk.symm u)⁻¹ := by rw [← h_ij_inv F n k j hjk.symm
      u]

end MatsumotoDiagonalExtension

end
