/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/GroupTheory/BrauerFowler.lean` (leanprover/lean-eval),
at commit 38361be884302c7edce1908c4aef8296eb2cb27e, for the statement and docstring of
`brauer_fowler`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modification notice: ATLAS placed the statement in its current namespace and
deferred its proof in the former wanted module. This module supplies the proof.
lean-eval ships no `NOTICE` file.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.IndexNormal

/-!
# Brauer–Fowler theorem

The Brauer–Fowler theorem bounds the order of a finite nonabelian simple group
in terms of the order of the centralizer of any involution. We count products
of distinct conjugates of the involution and use the action on the cosets of
a centralizer to obtain the bound `(n ^ 2)!` for centralizer order `n`.
-/

namespace MathlibExt.GroupTheory.BrauerFowlerWanted.GroupTheory

open Subgroup
open scoped BigOperators

private theorem card_offDiag_mul_fiber_le {G : Type*} [Group G] [Finite G] [DecidableEq G]
    (s : Finset G) (hs : ∀ a ∈ s, a⁻¹ = a) (x : G) :
    (s.offDiag.filter fun p => p.1 * p.2 = x).card ≤ Nat.card (centralizer ({x} : Set G)) := by
  let fiber := s.offDiag.filter fun p => p.1 * p.2 = x
  by_cases h : fiber.Nonempty
  · obtain ⟨p₀, hp₀⟩ := h
    let reference : fiber := ⟨p₀, hp₀⟩
    have hprod (p : fiber) : p.val.1 * p.val.2 = x :=
      (Finset.mem_filter.mp p.property).2
    -- The first entry of every pair conjugates the product to its inverse.
    have hinv (p : fiber) : SemiconjBy p.val.1 x x⁻¹ := by
      obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp (Finset.mem_filter.mp p.property).1
      have haa : p.val.1 * p.val.1 = 1 := by
        simpa only [hs _ ha] using inv_mul_cancel p.val.1
      change p.val.1 * x = x⁻¹ * p.val.1
      rw [← hprod p, mul_inv_rev, hs _ hb]
      calc
        p.val.1 * (p.val.1 * p.val.2) = p.val.2 := by
          rw [← mul_assoc, haa, one_mul]
        _ = (p.val.2 * p.val.1⁻¹) * p.val.1 := by simp [mul_assoc]
    let e (p : fiber) : centralizer ({x} : Set G) :=
      ⟨reference.val.1⁻¹ * p.val.1,
        mem_centralizer_singleton_iff.mpr ((hinv reference).inv_symm_left.mul_left (hinv p))⟩
    change fiber.card ≤ _
    rw [← Fintype.card_coe fiber, ← Nat.card_eq_fintype_card]
    apply Nat.card_le_card_of_injective e
    intro p q hpq
    have hfst : p.val.1 = q.val.1 := mul_left_cancel (congrArg Subtype.val hpq)
    apply Subtype.ext
    refine Prod.ext hfst (mul_left_cancel (a := p.val.1) ?_)
    rw [hprod p, hfst, hprod q]
  · change fiber.card ≤ _
    simp [Finset.not_nonempty_iff_eq_empty.mp h]

private theorem exists_centralizer_index_le {G : Type*} [Group G] [Finite G]
    {t : G} (ht : orderOf t = 2) :
    ∃ x : G, x ≠ 1 ∧ (centralizer ({x} : Set G)).index ≤
      (Nat.card (centralizer ({t} : Set G))) ^ 2 := by
  classical
  let := Fintype.ofFinite G
  let s := (Set.toFinite (conjugatesOf t)).toFinset
  let u := (Finset.univ : Finset G).erase 1
  let c (x : G) := Nat.card (centralizer ({x} : Set G))
  have ht₁ : t ≠ 1 := by
    intro h
    simp [h] at ht
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image u c ⟨t, by simpa [u] using ht₁⟩
  have hcx : 0 < c x := Nat.card_pos
  have hs (a : G) (ha : a ∈ s) : a⁻¹ = a := by
    have hconj : IsConj t a := (Set.toFinite (conjugatesOf t)).mem_toFinset.mp ha
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hsemi : SemiconjBy g t a := by
      change g * t = a * g
      rw [← hg, inv_mul_cancel_right]
    exact inv_eq_self_of_orderOf_eq_two ((hsemi.orderOf_eq g).symm.trans ht)
  have hmaps : (s.offDiag : Set (G × G)).MapsTo (fun p => p.1 * p.2) u := by
    intro p hp
    obtain ⟨_, hp₂, hne⟩ := Finset.mem_offDiag.mp hp
    simpa [u, mul_eq_one_iff_eq_inv, hs _ hp₂] using hne
  -- Count ordered pairs with distinct entries by their nonidentity products.
  have hcount : s.offDiag.card ≤ u.card * c x := calc
    _ = ∑ y ∈ u, (s.offDiag.filter fun p => p.1 * p.2 = y).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _y ∈ u, c x :=
      Finset.sum_le_sum fun y hy => (card_offDiag_mul_fiber_le s hs y).trans (hmax y hy)
    _ = _ := by simp
  have hu : u.card < Nat.card G := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.card_erase_lt_of_mem (Finset.mem_univ 1)
  have hlt : s.card * (s.card - 1) < Nat.card G * c x := calc
    _ = s.offDiag.card := by rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]
    _ ≤ u.card * c x := hcount
    _ < _ := (Nat.mul_lt_mul_right hcx).mpr hu
  have hs_card : s.card = (centralizer ({t} : Set G)).index := by
    rw [index_centralizer_eq_ncard, Set.ncard_eq_toFinset_card]
  have hindex_mul : s.card * c t = Nat.card G := by
    rw [hs_card]
    exact index_mul_card _
  rw [← hindex_mul, mul_assoc] at hlt
  have hs_le : s.card ≤ c t * c x := by
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  refine ⟨x, (Finset.mem_erase.mp hx).1, ?_⟩
  apply le_of_mul_le_mul_right _ hcx
  calc
    (centralizer ({x} : Set G)).index * c x = Nat.card G := index_mul_card _
    _ = s.card * c t := hindex_mul.symm
    _ ≤ (c t * c x) * c t := Nat.mul_le_mul_right _ hs_le
    _ = c t ^ 2 * c x := by rw [pow_two]; ac_rfl

set_option linter.dupNamespace false in
/-- **Brauer–Fowler theorem.** There is a function $f \colon \mathbb{N} \to \mathbb{N}$ such that
for every finite nonabelian simple group $G$ and every element $t \in G$ of order $2$, with
centralizer $C_G(t)$ in $G$, the order of $G$ satisfies $|G| \le f(|C_G(t)|)$.

Source: R. Brauer and K. A. Fowler, On groups of even order, Ann. of Math. (2) 62 (1955), 565-583.
https://doi.org/10.2307/1970080 Via leanprover/lean-eval@38361be, problem `brauer_fowler`. -/
public theorem brauer_fowler :
    ∃ f : ℕ → ℕ, ∀ (G : Type) [Group G] [Finite G],
      IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      ∀ t : G, orderOf t = 2 →
        Nat.card G ≤ f (Nat.card (Subgroup.centralizer ({t} : Set G))) := by
  refine ⟨fun n => (n ^ 2).factorial, ?_⟩
  intro G _ _ hsimple hnoncomm t ht
  let : IsSimpleGroup G := hsimple
  obtain ⟨x, hx, hindex⟩ := exists_centralizer_index_le ht
  have hcenter : center G = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G)).resolve_right ?_
    intro h
    obtain ⟨a, b, hab⟩ := hnoncomm
    exact hab (isMulCommutative_iff.mp (center_eq_top_iff.mp h) a b)
  let H := centralizer ({x} : Set G)
  have hproper : H ≠ ⊤ := by
    intro h
    have hmem := centralizer_eq_top_iff_subset.mp h (Set.mem_singleton x)
    exact hx (by simpa [hcenter] using hmem)
  -- The action of a simple group on the cosets of a proper subgroup is faithful.
  have hcore : H.normalCore = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore).resolve_right
      fun h => hproper (top_unique (h ▸ H.normalCore_le))
  have hbound := H.index_normalCore_le_factorial_index
  rw [hcore, index_bot] at hbound
  exact hbound.trans (Nat.factorial_le hindex)

end MathlibExt.GroupTheory.BrauerFowlerWanted.GroupTheory
