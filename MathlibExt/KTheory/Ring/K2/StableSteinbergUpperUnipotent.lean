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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteSupport
import Mathlib.Algebra.Group.Subgroup.Finite

/-! # Finite-rank upper-unipotent subgroup

Minimal finite-rank upper-unipotent carrier for Milnor Section 9: the closure
of the positive roots `x i j hij a` with `i < j < n`, the column-major ordered
positive-root list, and its head-left ordered product evaluator. This module
adds only exact ordered-root membership, duplicate-freeness, generator
membership, evaluator membership, successor recurrences, containment in
`finiteStage`, rank monotonicity, rank-zero/rank-one degeneracy, and rank-zero/
rank-one simp evaluations. It proves no ordered normal form, coefficient or
evaluator uniqueness, injectivity of `toStableE`, matrix uniqueness, TWT/Bruhat
statement, torus/Weyl identity, kernel generation, or Matsumoto claim.
-/

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {R : Type u} [Ring R]

/-- Finite upper-unipotent subgroup: closure of all `x i j hij a` with
`i < j`, `i < n`, and `j < n`. Purpose: finite-rank upper-unipotent carrier
for Milnor Section 9. Nonclaim: no normal form, uniqueness, or injectivity
is asserted. -/
@[expose] public def upperUnipotentSubgroup (n : ℕ) : Subgroup (StableSteinberg R) :=
  Subgroup.closure
    { g | ∃ (i j : ℕ) (hij : i ≠ j) (a : R),
      g = x (R := R) i j hij a ∧ i < j ∧ i < n ∧ j < n }

/-- Column-major enumeration of the positive roots below `n`: unfolding one
rank appends column `n`, namely `(0, n), …, (n - 1, n)`. -/
private def orderedPositiveRootsAux : ℕ → List (ℕ × ℕ)
  | 0 => []
  | (n + 1) => orderedPositiveRootsAux n ++ (List.range n).map (fun i => (i, n))

private theorem orderedPositiveRootsAux_mem {n a b : ℕ} :
    (a, b) ∈ orderedPositiveRootsAux n ↔ a < b ∧ b < n := by
  induction n with
  | zero => simp [orderedPositiveRootsAux]
  | succ m ih =>
    rw [orderedPositiveRootsAux, List.mem_append]
    constructor
    · intro h
      obtain h | h := h
      · obtain ⟨hab, hbn⟩ := ih.mp h
        exact ⟨hab, Nat.lt_succ_of_lt hbn⟩
      · rw [List.mem_map] at h
        obtain ⟨i, hi, hpair⟩ := h
        rw [List.mem_range] at hi
        have ha : a = i := (congrArg Prod.fst hpair).symm
        have hb : b = m := (congrArg Prod.snd hpair).symm
        rw [ha, hb]
        exact ⟨hi, Nat.lt_succ_self m⟩
    · intro h
      obtain ⟨hab, hbn⟩ := h
      by_cases hbn' : b < m
      · exact Or.inl (ih.mpr ⟨hab, hbn'⟩)
      · have hbeq : b = m := by omega
        apply Or.inr
        rw [List.mem_map]
        refine ⟨a, List.mem_range.mpr (hbeq ▸ hab), ?_⟩
        rw [← hbeq]

private theorem orderedPositiveRootsAux_nodup (n : ℕ) :
    (orderedPositiveRootsAux n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ m ih =>
    rw [orderedPositiveRootsAux]
    refine List.Nodup.append ih ?_ ?_
    · exact List.Nodup.map (fun a b h => congrArg Prod.fst h)
        List.nodup_range
    · rw [List.disjoint_left]
      intro p hp hcon
      obtain ⟨a, b⟩ := p
      have hlt := (orderedPositiveRootsAux_mem.mp hp).2
      rw [List.mem_map] at hcon
      obtain ⟨i, hi, hpair⟩ := hcon
      have hbeq : b = m := (congrArg Prod.snd hpair).symm
      omega

/-- Column-major ordered positive roots below `n`: the duplicate-free list of
exactly the pairs `(i, j)` with `i < j < n`, outer loop over `j` ascending and
inner loop over `i` ascending. Purpose: ordered root enumeration for the
upper-unipotent evaluator. Nonclaim: no normal form or uniqueness is asserted. -/
public def orderedPositiveRoots (n : ℕ) : List (ℕ × ℕ) :=
  orderedPositiveRootsAux n

/-- Exact membership: `(a, b)` lies in the ordered roots iff `a < b < n`. -/
public theorem orderedPositiveRoots_mem {n a b : ℕ} :
    (a, b) ∈ orderedPositiveRoots n ↔ a < b ∧ b < n :=
  orderedPositiveRootsAux_mem

/-- The ordered positive roots are duplicate-free. -/
public theorem orderedPositiveRoots_nodup (n : ℕ) :
    (orderedPositiveRoots n).Nodup :=
  orderedPositiveRootsAux_nodup n

/-- Rank zero: there are no positive roots. -/
@[simp] public theorem orderedPositiveRoots_zero :
    orderedPositiveRoots 0 = [] := by
  simp [orderedPositiveRoots, orderedPositiveRootsAux]

/-- Rank one: there are no positive roots. -/
@[simp] public theorem orderedPositiveRoots_one :
    orderedPositiveRoots 1 = [] := by
  simp [orderedPositiveRoots, orderedPositiveRootsAux]

/-- Successor recurrence: unfolding one rank appends column `n`, namely
`(0, n), …, (n - 1, n)`. Purpose: rank induction for downstream packets.
Nonclaim: no normal form or uniqueness is asserted. -/
public theorem orderedPositiveRoots_succ (n : ℕ) :
    orderedPositiveRoots (n + 1) = orderedPositiveRoots n ++
      (List.range n).map (fun i => (i, n)) := by
  simp [orderedPositiveRoots, orderedPositiveRootsAux]

/-- Generator membership: each positive root `x i j hij a` with `i < j < n`
lies in `upperUnipotentSubgroup n`. -/
public theorem x_mem_upperUnipotentSubgroup {n i j : ℕ} (hij : i ≠ j)
    (hlt : i < j) (hi : i < n) (hj : j < n) (a : R) :
    x (R := R) i j hij a ∈ upperUnipotentSubgroup (R := R) n := by
  apply Subgroup.subset_closure
  exact ⟨i, j, hij, a, rfl, hlt, hi, hj⟩

/-- The upper-unipotent subgroup lies in `finiteStage n`, since each positive
root generator has both indices below `n`. -/
public theorem upperUnipotentSubgroup_le_finiteStage (n : ℕ) :
    upperUnipotentSubgroup (R := R) n ≤ finiteStage (R := R) n := by
  rw [upperUnipotentSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, j, hij, a, rfl, hlt, hi, hj⟩ := hg
  exact x_mem_finiteStage hi hj

/-- `upperUnipotentSubgroup` is monotone in the rank. -/
public theorem upperUnipotentSubgroup_mono :
    Monotone (upperUnipotentSubgroup (R := R)) := by
  intro m n hmn
  apply Subgroup.closure_mono
  intro g hg
  obtain ⟨i, j, hij, a, rfl, hlt, hi, hj⟩ := hg
  exact ⟨i, j, hij, a, rfl, hlt, Nat.lt_of_lt_of_le hi hmn,
    Nat.lt_of_lt_of_le hj hmn⟩

/-- No positive root lies below `0`, so the rank-zero subgroup is bottom. -/
public theorem upperUnipotentSubgroup_zero_eq_bot :
    upperUnipotentSubgroup (R := R) 0 = ⊥ :=
  le_bot_iff.mp
    (finiteStage_zero_eq_bot (R := R) ▸
      upperUnipotentSubgroup_le_finiteStage (R := R) 0)

/-- No positive root lies below `1`, so the rank-one subgroup is bottom. -/
public theorem upperUnipotentSubgroup_one_eq_bot :
    upperUnipotentSubgroup (R := R) 1 = ⊥ :=
  le_bot_iff.mp
    (finiteStage_one_eq_bot (R := R) ▸
      upperUnipotentSubgroup_le_finiteStage (R := R) 1)

/-- Root generator at an index pair, trivial off the positive roots. -/
private def upperUnipotentGen (p : ℕ × ℕ) (a : R) : StableSteinberg R :=
  if h : p.1 ≠ p.2 then x (R := R) p.1 p.2 h a else 1

/-- Ordered upper-unipotent product: head-left `List.prod` of the root
generators over `orderedPositiveRoots n` for a coefficient assignment on index
pairs. Only the values of the assignment on `orderedPositiveRoots n` affect
the product, so downstream uniqueness is agreement on that list, not equality
of total functions. Purpose: ordered evaluator for the packet-2 uniqueness
theorem. Nonclaim: no normal form, uniqueness, or injectivity is asserted. -/
public def upperUnipotentProd (n : ℕ) (c : ℕ × ℕ → R) : StableSteinberg R :=
  ((orderedPositiveRoots n).map (fun p => upperUnipotentGen p (c p))).prod

/-- Successor factorization: the rank-`n + 1` product is the rank-`n` product
times the new column-`n` factors. Purpose: rank induction for the packet-2
uniqueness theorem. Nonclaim: no normal form, uniqueness, or injectivity is
asserted. -/
public theorem upperUnipotentProd_succ (n : ℕ) (c : ℕ × ℕ → R) :
    upperUnipotentProd (n + 1) c = upperUnipotentProd n c *
      ((List.range n).map (fun i =>
        if h : i ≠ n then x (R := R) i n h (c (i, n)) else 1)).prod := by
  have hgen : ∀ i : ℕ, upperUnipotentGen (i, n) (c (i, n)) =
      (if h : i ≠ n then x (R := R) i n h (c (i, n)) else 1) :=
    fun _ => rfl
  unfold upperUnipotentProd
  rw [orderedPositiveRoots_succ, List.map_append, List.prod_append, List.map_map]
  simp only [Function.comp_def, hgen]

/-- Evaluator membership: the ordered product lies in the subgroup. -/
public theorem upperUnipotentProd_mem (n : ℕ) (c : ℕ × ℕ → R) :
    upperUnipotentProd n c ∈ upperUnipotentSubgroup (R := R) n := by
  unfold upperUnipotentProd
  apply Subgroup.list_prod_mem
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  obtain ⟨a, b⟩ := p
  have hmem := orderedPositiveRoots_mem.mp hp
  have hgen : upperUnipotentGen (a, b) (c (a, b)) =
      x (R := R) a b (ne_of_lt hmem.1) (c (a, b)) :=
    dite_eq_left (ne_of_lt hmem.1)
  rw [hgen]
  exact x_mem_upperUnipotentSubgroup (ne_of_lt hmem.1) hmem.1
    (Nat.lt_trans hmem.1 hmem.2) hmem.2 _

/-- Rank zero: the ordered product is one. -/
@[simp] public theorem upperUnipotentProd_zero (c : ℕ × ℕ → R) :
    upperUnipotentProd 0 c = 1 := by
  simp [upperUnipotentProd, orderedPositiveRoots_zero]

/-- Rank one: the ordered product is one. -/
@[simp] public theorem upperUnipotentProd_one (c : ℕ × ℕ → R) :
    upperUnipotentProd 1 c = 1 := by
  simp [upperUnipotentProd, orderedPositiveRoots_one]

/-- Inverse of the ordered evaluator is the reversed-order product of negated
root generators. Purpose: explicit inverse word prerequisite for later
collection and closure packets. Nonclaim: no re-collection, closure, normal
form, uniqueness, `toStableE` injectivity, TWT, kernel-generation, or
Matsumoto claim. -/
public theorem upperUnipotentProd_inv_eq_reverse_neg_prod
    (n : ℕ) (c : ℕ × ℕ → R) :
    (upperUnipotentProd (R := R) n c)⁻¹ =
      (((orderedPositiveRoots n).reverse.map (fun p =>
        if h : p.1 ≠ p.2 then x (R := R) p.1 p.2 h (-(c p)) else 1))).prod := by
  have hinv : ∀ p : ℕ × ℕ, (upperUnipotentGen p (c p))⁻¹ =
      (if h : p.1 ≠ p.2 then x (R := R) p.1 p.2 h (-(c p)) else 1) := by
    intro p
    by_cases h : p.1 ≠ p.2
    · unfold upperUnipotentGen
      rw [dite_eq_left h, dite_eq_left h]
      exact (x_neg (R := R) p.1 p.2 h (c p)).symm
    · unfold upperUnipotentGen
      rw [dite_eq_right h, dite_eq_right h, inv_one]
  have aux : ∀ L : List (ℕ × ℕ),
      ((L.map (fun p => upperUnipotentGen p (c p))).prod)⁻¹ =
        ((L.reverse.map (fun p =>
          if h : p.1 ≠ p.2 then x (R := R) p.1 p.2 h (-(c p)) else 1)).prod) := by
    intro L
    induction L with
    | nil => simp
    | cons hd tl ih =>
      rw [List.map_cons, List.prod_cons, mul_inv_rev, ih, hinv hd,
        List.reverse_cons, List.map_append, List.prod_append]
      simp
  unfold upperUnipotentProd
  exact aux (orderedPositiveRoots n)

end StableSteinberg

end AlgebraicKTheory
