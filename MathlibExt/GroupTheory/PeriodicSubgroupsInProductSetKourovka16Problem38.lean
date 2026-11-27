/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.Tactic.Linarith

/-!
# Periodic subgroups in a product set

Every subgroup contained in the setwise product of two periodic subgroups of a soluble group
is periodic. The proof proceeds by induction on derived length. In the abelian kernel of a
quotient, factorizations of an element and its square give a midpoint relation on a finite
orbit. A rational character detecting an element of infinite order would violate this relation.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/PeriodicSubgroupsInProductSetKourovka16Problem38Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.38 (F. de Giovanni). UnsolvedMath record
UM-00701230 (`KOU-16.38`), dataset ulamai/UnsolvedMath v1.8.0.

Soluble is `Group.IsSolvable` (finite derived length), periodic means that every element has finite
order, and `AB` is the pointwise product of the underlying sets; `G` may be infinite.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38Wanted

open Pointwise

/-- **Kourovka Problem 16.38 (subgroups inside a product of periodic subgroups).** The statement,
posed by F. de Giovanni, that for every soluble group $G$ and all subgroups $A$ and $B$ of $G$ in
which every element has finite order, every subgroup $H$ of $G$ contained in the set $AB$ of all
products $ab$ with $a \in A$ and $b \in B$ has every element of finite order. -/
def subgroupInPeriodicProductIsPeriodic : Prop :=
  ∀ (G : Type) [Group G], Group.IsSolvable G → ∀ A B : Subgroup G,
    (∀ a ∈ A, IsOfFinOrder a) → (∀ b ∈ B, IsOfFinOrder b) →
    ∀ H : Subgroup G, (H : Set G) ⊆ (A : Set G) * (B : Set G) → ∀ h ∈ H, IsOfFinOrder h

universe u

/-- Induct on derived length by factoring out the last abelian term of the derived series. -/
private theorem solvable_induction (P : (G : Type u) → [Group G] → Prop)
    (base : ∀ (G : Type u) [Group G] [Subsingleton G], P G)
    (step : ∀ (G : Type u) [Group G] [Group.IsSolvable G] (N : Subgroup G) [N.Normal]
      [IsMulCommutative N], P (G ⧸ N) → P G)
    (G : Type u) [Group G] [hG : Group.IsSolvable G] : P G := by
  obtain ⟨n, hn⟩ := hG.solvable
  induction n generalizing G with
  | zero =>
    have := subsingleton_of_forall_eq (1 : G) fun x =>
      Subgroup.mem_bot.mp (hn ▸ (Subgroup.mem_top x))
    exact base G
  | succ n ih =>
    let N := Subgroup.derivedSeries G n
    have : IsMulCommutative N := Subgroup.commutator_self_eq_bot_iff.mp hn
    apply step G N
    apply ih
    rw [← Subgroup.map_derivedSeries_eq (QuotientGroup.mk'_surjective N) n,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- A finitely generated soluble torsion group is finite, by Schreier's lemma on the
abelian kernel of the quotient in the induction step. -/
private theorem finite_of_fg_periodic (G : Type*) [Group G] [Group.IsSolvable G] :
    Group.FG G → IsMulTorsion G → Finite G := by
  apply solvable_induction (fun G _ => Group.FG G → IsMulTorsion G → Finite G) _ _ G
  · intros
    infer_instance
  · intro G _ _ N _ _ ih hfg ht
    have := ih inferInstance (ht.of_surjective (QuotientGroup.mk'_surjective N))
    have := N.finiteIndex_of_finite_quotient
    let : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm' }
    exact N.finite_iff_finite_and_finiteIndex.mpr
      ⟨CommGroup.finite_of_fg_isMulTorsion N (ht.subgroup N), inferInstance⟩

/-- Summing squares over a finite group forces a midpoint between two translates of a
rational-valued function to agree with both translates. -/
private theorem finite_midpoint {K : Type*} [Group K] [Finite K] (f : K → ℚ) (p q : K)
    (h : ∀ g, 2 * f (g * p) = f g + f (g * q)) : f p = f 1 := by
  classical
  let := Fintype.ofFinite K
  have shift (k : K) : ∑ g, f (g * k) ^ 2 = ∑ g, f g ^ 2 :=
    Equiv.sum_comp (Equiv.mulRight k) (fun g => f g ^ 2)
  have difference (g : K) :
      (f (g * p) - f g) ^ 2 = (f g ^ 2 + f (g * q) ^ 2) / 2 - f (g * p) ^ 2 := by
    rw [show f (g * q) = 2 * f (g * p) - f g by linarith [h g]]
    ring
  have hz : ∑ g, (f (g * p) - f g) ^ 2 = 0 := by
    simp_rw [difference, div_eq_mul_inv]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, shift, shift]
    ring
  simpa [sub_eq_zero] using (Finset.sum_sq_eq_zero_iff _ _).mp hz 1 (Finset.mem_univ _)

/-- A character to the rationals detects any infinite-order element of an abelian group by
extending the map sending its generator to one from the infinite cyclic subgroup. -/
private theorem exists_character {M : Type*} [AddCommGroup M] {x : M}
    (hx : ¬ IsOfFinAddOrder x) : ∃ χ : M →+ ℚ, χ x = 1 := by
  obtain ⟨χ, hχ⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
    (zmultiplesHom M x) (injective_zsmul_iff_not_isOfFinAddOrder.mpr hx) (Int.castAddHom ℚ)
  exact ⟨χ, by simpa using DFunLike.congr_fun hχ (1 : ℤ)⟩

/-- If both an element of an abelian normal subgroup and its square belong to the product
of two periodic subgroups of a soluble group, the element has finite order. Its factorizations
give a midpoint relation on the orbit of the identity under left and right multiplication. -/
private theorem periodic_of_square_mem_product {G : Type*} [Group G] [Group.IsSolvable G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative N] (A B : Subgroup G)
    (hA : IsMulTorsion A) (hB : IsMulTorsion B) (x : N)
    (hx : (x : G) ∈ (A : Set G) * (B : Set G))
    (hx₂ : (x : G) ^ 2 ∈ (A : Set G) * (B : Set G)) : IsOfFinOrder x := by
  classical
  let L := A.subtype.comp (MonoidHom.fst A B)
  let R := B.subtype.comp (MonoidHom.snd A B)
  let π := QuotientGroup.mk' N
  have factor {y : G} (hy : y ∈ (A : Set G) * (B : Set G)) :
      ∃ k : A × B, L k * (R k)⁻¹ = y := by
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    exact ⟨(⟨a, ha⟩, ⟨b⁻¹, B.inv_mem hb⟩), by simp [L, R]⟩
  obtain ⟨p, hp⟩ := factor hx
  obtain ⟨q, hq⟩ := factor hx₂
  let K := Subgroup.closure ({p, q} : Set (A × B))
  have : Group.FG K := (Group.fg_iff_subgroup_fg _).mpr <|
    (Subgroup.fg_iff _).mpr ⟨_, rfl, (Set.finite_singleton q).insert p⟩
  have : Finite K := finite_of_fg_periodic K ‹_›
    (IsMulTorsion.subgroup (fun k : A × B => IsOfFinOrder.prod_iff.mpr ⟨hA _, hB _⟩) K)
  -- Every pair in K has equal components modulo N, so its orbit of the identity lies in N.
  have agrees : Set.EqOn (π.comp L) (π.comp R) (K : Set (A × B)) := by
    apply MonoidHom.eqOn_closure
    intro k hk
    change π (L k) = π (R k)
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rcases hk with rfl | hk
    · exact hp ▸ x.property
    · obtain rfl : k = q := hk
      exact hq ▸ N.pow_mem x.property 2
  let orbit (k : K) : N := ⟨L k.val * (R k.val)⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (L k.val * (R k.val)⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact agrees k.property⟩
  have orbit_mul (i j : K) :
      orbit (i * j) = orbit i * MulAut.conjNormal (R i.val) (orbit j) := by
    apply Subtype.ext
    simp [orbit, MulAut.conjNormal_apply, mul_assoc]
  let a : K := ⟨p, Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q, Subgroup.subset_closure (by simp)⟩
  have ha : orbit a = x := Subtype.ext hp
  have hb : orbit b = x ^ 2 := Subtype.ext hq
  have h₁ : orbit 1 = 1 := Subtype.ext (by simp [orbit])
  let : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm' }
  by_contra hinf
  obtain ⟨χ, hχ⟩ := exists_character (isOfFinAddOrder_ofMul_iff.not.mpr hinf)
  let f (k : K) := χ (Additive.ofMul (orbit k))
  have mid (k : K) : 2 * f (k * a) = f k + f (k * b) := by
    have hm : orbit (k * a) ^ 2 = orbit k * orbit (k * b) := by
      rw [orbit_mul k a, orbit_mul k b, ha, hb, map_pow, mul_pow, sq (orbit k), mul_assoc]
    simpa [f, ofMul_pow, ofMul_mul, two_nsmul, two_mul] using
      congrArg (fun y => χ (Additive.ofMul y)) hm
  have := finite_midpoint f a b mid
  simp [f, ha, h₁, hχ] at this

/--
**Subgroups inside a product of two periodic subgroups of a soluble group are periodic.** Let $G$
be a soluble group and let $A$ and $B$ be subgroups of $G$ in which every element has finite order.
Then every subgroup $H$ of $G$ contained in the set $AB$ of all products $ab$ with $a \in A$ and
$b \in B$ is periodic: every element of $H$ has finite order. This answers Kourovka Problem 16.38
(F. de Giovanni) in the affirmative; the proof is due to Kinyon and Urban (Proposition 3.8).

Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 16.38 (F. de Giovanni); resolution: M. Kinyon and J. Urban
(with Codex gpt-6-astra), Results on problems from the Kourovka Notebook, preprint, version 4 (19
September 2026), Proposition 3.8 (if G is soluble and A, B ≤ G are periodic, every subgroup
contained in the set AB is periodic); the Kourovka Notebook (21st issue) marks 16.38 solved (Yes, AI
solution confirmed by B. Amberg),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem subgroupInPeriodicProductIsPeriodic_holds :
    subgroupInPeriodicProductIsPeriodic := by
  intro G _ hG
  apply solvable_induction (fun G _ => ∀ A B : Subgroup G,
    (∀ a ∈ A, IsOfFinOrder a) → (∀ b ∈ B, IsOfFinOrder b) →
    ∀ H : Subgroup G, (H : Set G) ⊆ (A : Set G) * (B : Set G) → ∀ x ∈ H, IsOfFinOrder x) _ _ G
  · intros
    exact isOfFinOrder_of_finite _
  · intro G _ _ N _ _ ih A B hA hB H hH x hx
    let π := QuotientGroup.mk' N
    have map_periodic (S : Subgroup G) (hS : ∀ s ∈ S, IsOfFinOrder s) :
        ∀ t ∈ S.map π, IsOfFinOrder t := by
      rintro _ ⟨s, hs, rfl⟩
      exact π.isOfFinOrder (hS s hs)
    have incl : (H.map π : Set (G ⧸ N)) ⊆ (A.map π : Set _) * (B.map π : Set _) := by
      rw [Subgroup.coe_map, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul]
      exact Set.image_mono hH
    obtain ⟨m, hm, he⟩ := (ih _ _ (map_periodic A hA) (map_periodic B hB) _ incl
      (π x) ⟨x, hx, rfl⟩).exists_pow_eq_one
    have hN : x ^ m ∈ N := (QuotientGroup.eq_one_iff _).mp ((π.map_pow x m).trans he)
    have hpow := H.pow_mem hx m
    have ht := periodic_of_square_mem_product N A B
      (fun a => A.subtype_injective.isOfFinOrder_iff.mp (hA a a.property))
      (fun b => B.subtype_injective.isOfFinOrder_iff.mp (hB b b.property))
      ⟨x ^ m, hN⟩ (hH hpow) (hH (H.pow_mem hpow 2))
    exact (N.subtype.isOfFinOrder ht).of_pow hm.ne'

end MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38Wanted
