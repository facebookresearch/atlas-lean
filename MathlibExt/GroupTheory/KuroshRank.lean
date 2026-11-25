/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean`,
`Theorems/Thm_Monoid_CoprodI_isTree_cosetGraph.lean`
and
`P2M/Sol/S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean`,
`P2M/Sol/S_Monoid_CoprodI_isTree_cosetGraph.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

@[expose] public section



open Subgroup

namespace GroupTheory

namespace Kurosh

section TorsionCriterion

variable {G : Type*} [Group G]

def ConjTrivial (A H : Subgroup G) : Prop :=
  ∀ g x : G, x ∈ A → g⁻¹ * x * g ∈ H → x = 1

theorem isOfFinOrder_conj {x : G} (g : G) (hx : IsOfFinOrder x) :
    IsOfFinOrder (g⁻¹ * x * g) :=
  (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩ : IsConj x (g⁻¹ * x * g)).isOfFinOrder hx

theorem isOfFinOrder_of_mem_finite {A : Subgroup G} [Finite A] {x : G} (hx : x ∈ A) :
    IsOfFinOrder x :=
  Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite (⟨x, hx⟩ : A))

theorem conjTrivial_of_torsionFree (A H : Subgroup G) [Finite A]
    (hH : ∀ y : G, y ∈ H → IsOfFinOrder y → y = 1) : ConjTrivial A H := by
  intro g x hxA hxH
  have hfin : IsOfFinOrder (g⁻¹ * x * g) := isOfFinOrder_conj g (isOfFinOrder_of_mem_finite hxA)
  have h0 : g⁻¹ * x * g = 1 := hH _ hxH hfin
  have h1 : g⁻¹ * x * g = g⁻¹ * 1 * g := by rw [h0, mul_one, inv_mul_cancel]
  exact mul_left_cancel (mul_right_cancel h1)

end TorsionCriterion

section Divisibility

variable {G : Type*} [Group G] (A H : Subgroup G)

theorem stabilizer_eq_bot_of_conjTrivial (hAH : ConjTrivial A H) (q : G ⧸ H) :
    MulAction.stabilizer A q = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hmem : (a : G) • (g : G ⧸ H) = (g : G ⧸ H) := ha
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, mul_inv_rev] at hmem
    have hinv : (a : G)⁻¹ = 1 := hAH g ((a : G)⁻¹) (inv_mem a.2) hmem
    have : (a : G) = 1 := by rw [← inv_inv (a : G), hinv, inv_one]
    exact Subgroup.mem_bot.mpr (Subtype.ext this)

theorem card_dvd_index_of_conjTrivial [Finite A] [H.FiniteIndex] (hAH : ConjTrivial A H) :
    Nat.card A ∣ H.index := by
  classical
  have key := MulAction.selfEquivSigmaOrbitsQuotientStabilizer A (G ⧸ H)
  have efib : ∀ ω : Quotient (MulAction.orbitRel A (G ⧸ H)),
      (A ⧸ MulAction.stabilizer A ω.out) ≃ A := fun ω =>
    (Subgroup.quotientEquivOfEq (stabilizer_eq_bot_of_conjTrivial A H hAH ω.out)).trans
      QuotientGroup.quotientBot.toEquiv
  have e : (G ⧸ H) ≃ Quotient (MulAction.orbitRel A (G ⧸ H)) × A :=
    (key.trans (Equiv.sigmaCongrRight efib)).trans (Equiv.sigmaEquivProd _ _)
  rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_prod]
  exact dvd_mul_left _ _

end Divisibility

section RankArithmetic

def kuroshRank (a b m : ℕ) : ℕ := 1 + m - m / a - m / b

theorem kuroshRank_add_eq {a b m : ℕ} (hab : m / a + m / b ≤ m) :
    kuroshRank a b m + m / a + m / b = 1 + m := by
  unfold kuroshRank
  omega

theorem kuroshRank_two_three {m : ℕ} (hm : 6 ∣ m) : kuroshRank 2 3 m = 1 + m / 6 := by
  obtain ⟨k, rfl⟩ := hm
  simp only [kuroshRank]
  omega

theorem six_dvd_of_two_dvd_of_three_dvd {m : ℕ} (h2 : 2 ∣ m) (h3 : 3 ∣ m) : 6 ∣ m :=
  (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3

theorem div_add_div_le {a b m : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : m / a + m / b ≤ m := by
  have h1 : m / a ≤ m / 2 := Nat.div_le_div_left ha (by omega)
  have h2 : m / b ≤ m / 2 := Nat.div_le_div_left hb (by omega)
  omega

end RankArithmetic

section Core

def KuroshRankFormula (G : Fin 2 → Type*) [∀ i, Group (G i)] [∀ i, Finite (G i)] : Prop :=
  ∀ H : Subgroup (Monoid.CoprodI G), H.FiniteIndex →
    (∀ i, ConjTrivial (Monoid.CoprodI.of (i := i)).range H) →
    Nonempty (FreeGroupBasis
      (Fin (kuroshRank (Nat.card (G 0)) (Nat.card (G 1)) H.index)) H)

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]

instance finite_range_of (i : Fin 2) : Finite ((Monoid.CoprodI.of (i := i)).range :
    Subgroup (Monoid.CoprodI G)) :=
  Finite.of_equiv (G i) (MonoidHom.ofInjective (Monoid.CoprodI.of_injective i)).toEquiv

omit [∀ i, Finite (G i)] in

theorem card_range_of (i : Fin 2) :
    Nat.card ((Monoid.CoprodI.of (i := i)).range : Subgroup (Monoid.CoprodI G))
      = Nat.card (G i) :=
  (Nat.card_congr (MonoidHom.ofInjective (Monoid.CoprodI.of_injective i)).toEquiv).symm

theorem six_dvd_index_of_conjTrivial (h2 : Nat.card (G 0) = 2) (h3 : Nat.card (G 1) = 3)
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ i, ConjTrivial (Monoid.CoprodI.of (i := i)).range H) :
    6 ∣ H.index := by
  have d0 := card_dvd_index_of_conjTrivial _ H (hH 0)
  have d1 := card_dvd_index_of_conjTrivial _ H (hH 1)
  rw [card_range_of 0, h2] at d0
  rw [card_range_of 1, h3] at d1
  exact six_dvd_of_two_dvd_of_three_dvd d0 d1

theorem kuroshRank_index_eq (h2 : Nat.card (G 0) = 2) (h3 : Nat.card (G 1) = 3)
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ i, ConjTrivial (Monoid.CoprodI.of (i := i)).range H) :
    kuroshRank (Nat.card (G 0)) (Nat.card (G 1)) H.index = 1 + H.index / 6 := by
  rw [h2, h3]
  exact kuroshRank_two_three (six_dvd_index_of_conjTrivial h2 h3 H hH)

end Core

end Kurosh

end GroupTheory

open Subgroup SimpleGraph

namespace GroupTheory

namespace BassSerre

open Monoid Monoid.CoprodI

variable {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]

abbrev Vertex : Type _ :=
  (i : ι) × (CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range)

variable {G} in

abbrev Vertex.mk (i : ι) (g : CoprodI G) : Vertex G :=
  ⟨i, QuotientGroup.mk g⟩

def graph : SimpleGraph (Vertex G) where
  Adj v w := v.1 ≠ w.1 ∧ ∃ g : CoprodI G, Vertex.mk v.1 g = v ∧ Vertex.mk w.1 g = w
  symm := ⟨by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hij, g, hgv, hgw⟩
    exact ⟨hij.symm, g, hgw, hgv⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G}

theorem mk_eq_mk_iff {i : ι} {g h : CoprodI G} :
    Vertex.mk (G := G) i g = Vertex.mk i h ↔ g⁻¹ * h ∈ (of (M := G) (i := i)).range := by
  constructor
  · intro H
    exact QuotientGroup.eq.mp
      (sigma_mk_injective (β := fun j => CoprodI G ⧸ (of (M := G) (i := j)).range) H)
  · intro H
    exact congrArg (Sigma.mk i) (QuotientGroup.eq.mpr H)

theorem adj_mk {i j : ι} (hij : i ≠ j) (g : CoprodI G) :
    (graph G).Adj (Vertex.mk i g) (Vertex.mk j g) :=
  ⟨hij, g, rfl, rfl⟩

theorem adj_iff_exists {v w : Vertex G} :
    (graph G).Adj v w ↔ v.1 ≠ w.1 ∧ ∃ g, Vertex.mk v.1 g = v ∧ Vertex.mk w.1 g = w :=
  Iff.rfl

theorem adj_one {i j : ι} (hij : i ≠ j) :
    (graph G).Adj (Vertex.mk i (1 : CoprodI G)) (Vertex.mk j 1) :=
  adj_mk hij 1

instance : SMul (CoprodI G) (Vertex G) where
  smul g v := ⟨v.1, g • v.2⟩

theorem smul_def (g : CoprodI G) (v : Vertex G) : g • v = ⟨v.1, g • v.2⟩ :=
  rfl

@[simp]
theorem smul_mk (g : CoprodI G) (i : ι) (h : CoprodI G) :
    g • Vertex.mk i h = Vertex.mk i (g * h) :=
  rfl

instance : MulAction (CoprodI G) (Vertex G) where
  one_smul := by
    rintro ⟨i, x⟩
    show (⟨i, (1 : CoprodI G) • x⟩ : Vertex G) = ⟨i, x⟩
    rw [one_smul]
  mul_smul g h := by
    rintro ⟨i, x⟩
    show (⟨i, (g * h) • x⟩ : Vertex G) = ⟨i, g • h • x⟩
    rw [mul_smul]

theorem smul_adj {v w : Vertex G} (g : CoprodI G) (h : (graph G).Adj v w) :
    (graph G).Adj (g • v) (g • w) := by
  obtain ⟨hvw, e, hev, hew⟩ := h
  exact ⟨hvw, g * e, by rw [← hev]; rfl, by rw [← hew]; rfl⟩

def smulHom (g : CoprodI G) : graph G →g graph G where
  toFun v := g • v
  map_rel' := smul_adj g

@[simp]
theorem smulHom_apply (g : CoprodI G) (v : Vertex G) : smulHom g v = g • v :=
  rfl

theorem reachable_smul {v w : Vertex G} (g : CoprodI G) (h : (graph G).Reachable v w) :
    (graph G).Reachable (g • v) (g • w) :=
  h.map (smulHom g)

theorem smul_eq_self_iff {h : CoprodI G} {i : ι} {g : CoprodI G} :
    h • Vertex.mk i g = Vertex.mk i g ↔ g⁻¹ * h * g ∈ (of (M := G) (i := i)).range := by
  rw [smul_mk, mk_eq_mk_iff, show (h * g)⁻¹ * g = (g⁻¹ * h * g)⁻¹ by group, inv_mem_iff]

theorem conjTrivial_iff_forall_smul_ne {H : Subgroup (CoprodI G)} :
    (∀ i, Kurosh.ConjTrivial (of (M := G) (i := i)).range H) ↔
      ∀ h ∈ H, ∀ v : Vertex G, h • v = v → h = 1 := by
  constructor
  · rintro hCT h hH ⟨i, x⟩ hfix
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hx : g⁻¹ * h * g ∈ (of (M := G) (i := i)).range := smul_eq_self_iff.mp hfix
      have hx' : (g⁻¹)⁻¹ * (g⁻¹ * h * g) * g⁻¹ ∈ H := by
        have : (g⁻¹)⁻¹ * (g⁻¹ * h * g) * g⁻¹ = h := by group
        rwa [this]
      have hone := hCT i g⁻¹ (g⁻¹ * h * g) hx hx'
      have hh : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
      rw [hh, hone, mul_one, mul_inv_cancel]
  · rintro hfree i c x hx hcxc
    have hfix : (c⁻¹ * x * c) • Vertex.mk i c⁻¹ = Vertex.mk i c⁻¹ := by
      rw [smul_eq_self_iff]
      have : (c⁻¹)⁻¹ * (c⁻¹ * x * c) * c⁻¹ = x := by group
      rwa [this]
    have hone := hfree _ hcxc _ hfix
    have hx1 : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [hx1, hone, mul_one, mul_inv_cancel]

theorem mk_of_eq_mk_one {i : ι} (m : G i) :
    Vertex.mk (G := G) i (of m) = Vertex.mk i 1 :=
  mk_eq_mk_iff.mpr (MonoidHom.mem_range.mpr ⟨m⁻¹, by simp⟩)

theorem reachable_one_one (i j : ι) :
    (graph G).Reachable (Vertex.mk i (1 : CoprodI G)) (Vertex.mk j 1) := by
  classical
  by_cases h : i = j
  · subst h; exact Reachable.refl _
  · exact (adj_one h).reachable

theorem reachable_one_of {i k : ι} (m : G k) :
    (graph G).Reachable (Vertex.mk i (1 : CoprodI G)) (Vertex.mk i (of m)) := by
  classical
  by_cases hki : k = i
  · subst hki
    rw [mk_of_eq_mk_one]
  · refine (reachable_one_one i k).trans ?_
    rw [← mk_of_eq_mk_one m]
    exact (adj_mk hki (of m)).reachable

theorem reachable_one (i : ι) (g : CoprodI G) (j : ι) :
    (graph G).Reachable (Vertex.mk i (1 : CoprodI G)) (Vertex.mk j g) := by
  induction g using CoprodI.induction_left with
  | one => exact reachable_one_one i j
  | mul m x ih =>
    have step := reachable_smul (of m) ih
    rw [smul_mk, smul_mk, mul_one] at step
    exact (reachable_one_of m).trans step

theorem connected [Nonempty ι] : (graph G).Connected := by
  inhabit ι
  rw [connected_iff_exists_forall_reachable]
  refine ⟨Vertex.mk default 1, ?_⟩
  rintro ⟨j, x⟩
  induction x using QuotientGroup.induction_on with
  | H g => exact reachable_one default g j

theorem eq_one_of_mem_range_of_mem_range {i j : ι} (hij : i ≠ j) {x : CoprodI G}
    (hi : x ∈ (of (M := G) (i := i)).range) (hj : x ∈ (of (M := G) (i := j)).range) :
    x = 1 := by
  classical
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hi
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hj
  have key := congrArg (lift (Pi.mulSingle i (MonoidHom.id (G i)))) hb
  rw [lift_of, lift_of, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm] at key
  simp only [MonoidHom.one_apply, MonoidHom.id_apply] at key
  rw [← key, map_one]

theorem range_inf_range_eq_bot {i j : ι} (hij : i ≠ j) :
    (of (M := G) (i := i)).range ⊓ (of (M := G) (i := j)).range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  exact mem_bot.mpr (eq_one_of_mem_range_of_mem_range hij hx.1 hx.2)

theorem eq_of_mk_eq_mk {i j : ι} (hij : i ≠ j) {g g' : CoprodI G}
    (hgi : Vertex.mk (G := G) i g = Vertex.mk i g')
    (hgj : Vertex.mk (G := G) j g = Vertex.mk j g') :
    g = g' :=
  inv_mul_eq_one.mp
    (eq_one_of_mem_range_of_mem_range hij (mk_eq_mk_iff.mp hgi) (mk_eq_mk_iff.mp hgj))

theorem adj_base_iff {i : ι} {w : Vertex G} :
    (graph G).Adj (Vertex.mk i (1 : CoprodI G)) w ↔
      i ≠ w.1 ∧ ∃ a : G i, Vertex.mk w.1 (of a) = w := by
  constructor
  · rintro ⟨hiw, g, hgi, hgw⟩
    refine ⟨hiw, ?_⟩
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp
      (show g ∈ (of (M := G) (i := i)).range by simpa using mk_eq_mk_iff.mp hgi)
    exact ⟨a, by rw [ha]; exact hgw⟩
  · rintro ⟨hiw, a, haw⟩
    exact ⟨hiw, of a, (mk_of_eq_mk_one a), haw⟩

theorem isTree_of_isAcyclic [Nonempty ι] (h : (graph G).IsAcyclic) : (graph G).IsTree :=
  ⟨connected, h⟩

end BassSerre

end GroupTheory

namespace GroupTheory
namespace BassSerre

open Monoid Monoid.CoprodI

theorem fromRel_eq_graph {G : Fin 2 → Type*} [∀ i, Group (G i)] :
    (SimpleGraph.fromRel fun v w : (i : Fin 2) ×
        (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range) =>
        v.1 ≠ w.1 ∧ ∃ g : Monoid.CoprodI G,
          v.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸
            (Monoid.CoprodI.of (M := G) (i := v.1)).range) ∧
          w.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸
            (Monoid.CoprodI.of (M := G) (i := w.1)).range))
      = graph G := by
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨hij, g, hx, hy⟩ | ⟨hji, g, hy, hx⟩⟩
    · simp only at hij hx hy
      rw [hx, hy]
      exact ⟨hij, g, rfl, rfl⟩
    · simp only at hji hx hy
      rw [hx, hy]
      exact ⟨Ne.symm hji, g, rfl, rfl⟩
  · rintro ⟨hij, g, hx, hy⟩
    simp only [Vertex.mk, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx hy
    refine ⟨fun h => hij (congrArg Sigma.fst h), Or.inl ⟨hij, g, hx.symm, hy.symm⟩⟩

end BassSerre
end GroupTheory
namespace SimpleGraph

variable {V : Type*} {α : Type*}

theorem eq_of_adj_imp_eq_of_walk {G : SimpleGraph V} {f : V → α}
    (hf : ∀ ⦃v w : V⦄, G.Adj v w → f v = f w) {a b : V} (p : G.Walk a b) : f a = f b := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hf h).trans ih

theorem isBridge_of_separating {G : SimpleGraph V} (f : V → α) {a b : V}
    (hab : G.Adj a b) (hfab : f a ≠ f b)
    (hconst : ∀ ⦃v w : V⦄, G.Adj v w → s(v, w) ≠ s(a, b) → f v = f w) :
    G.IsBridge s(a, b) := by
  refine isBridge_iff.mpr fun hr => hfab ?_
  obtain ⟨p⟩ := hr
  refine eq_of_adj_imp_eq_of_walk (fun v w hvw => ?_) p
  rw [deleteEdges_adj] at hvw
  exact hconst hvw.1 fun he => hvw.2 (Set.mem_singleton_iff.mpr he)

end SimpleGraph
namespace GroupTheory
namespace BassSerre
open Monoid Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

def lastIdx (w : Word G) : Option ι :=
  w.toList.getLast?.map Sigma.fst

@[simp]
theorem lastIdx_empty : lastIdx (Word.empty : Word G) = none :=
  rfl

section DecEq

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] in

theorem lastIdx_rcons_getD {i : ι} (p : Word.Pair G i) :
    (lastIdx (Word.rcons p)).getD i = (lastIdx p.tail).getD i := by
  rw [Word.rcons]
  split
  · rfl
  · simp only [lastIdx, Word.cons_toList]
    rcases hl : p.tail.toList with _ | ⟨x, xs⟩
    · simp
    · rw [List.getLast?_cons_cons]

theorem rcons_equivPair (i : ι) (w : Word G) : Word.rcons (Word.equivPair i w) = w := by
  rw [← Word.equivPair_symm, Equiv.symm_apply_apply]

theorem equiv_apply (g : CoprodI G) : Word.equiv g = g • Word.empty :=
  rfl

@[simp]
theorem equiv_one : Word.equiv (1 : CoprodI G) = Word.empty := by
  rw [equiv_apply, one_smul]

theorem equiv_mul (g h : CoprodI G) : Word.equiv (g * h) = g • Word.equiv h := by
  rw [equiv_apply, equiv_apply, mul_smul]

theorem eq_one_of_toList_eq_nil {g : CoprodI G} (h : (Word.equiv g).toList = []) : g = 1 :=
  Word.equiv.injective ((Word.ext h).trans equiv_one.symm)

def sideAux (i : ι) (g : CoprodI G) : ι :=
  (lastIdx (Word.equiv g⁻¹)).getD i

@[simp]
theorem sideAux_one (i : ι) : sideAux i (1 : CoprodI G) = i := by
  simp [sideAux]

theorem sideAux_mul_of {i : ι} (g : CoprodI G) (m : G i) :
    sideAux i (g * of m) = sideAux i g := by
  simp only [sideAux]
  rw [mul_inv_rev, ← map_inv, equiv_mul, Word.of_smul_def, lastIdx_rcons_getD]
  conv_rhs => rw [← rcons_equivPair i (Word.equiv g⁻¹), lastIdx_rcons_getD]

theorem sideAux_eq_sideAux {g : CoprodI G} (hg : g ≠ 1) (i j : ι) :
    sideAux i g = sideAux j g := by
  have hne : (Word.equiv g⁻¹).toList ≠ [] := fun h =>
    hg (inv_eq_one.mp (eq_one_of_toList_eq_nil h))
  simp only [sideAux]
  cases hl : (Word.equiv g⁻¹).toList.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
  | some l => simp only [lastIdx, hl, Option.map_some, Option.getD_some]

def side (v : Vertex G) : ι :=
  Quotient.liftOn' v.2 (sideAux v.1) fun _ _ hab =>
    (sideAux_eq_of_rel (QuotientGroup.leftRel_apply.mp hab)).symm
where

  sideAux_eq_of_rel {i : ι} {a b : CoprodI G} (h : a⁻¹ * b ∈ (of (M := G) (i := i)).range) :
      sideAux i b = sideAux i a := by
    obtain ⟨m, hm⟩ := h
    have hb : b = a * of m := by rw [hm]; group
    rw [hb, sideAux_mul_of]

@[simp]
theorem side_mk (i : ι) (g : CoprodI G) : side (Vertex.mk i g) = sideAux i g :=
  rfl

@[simp]
theorem side_mk_one (i : ι) : side (Vertex.mk i (1 : CoprodI G)) = i := by
  rw [side_mk, sideAux_one]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in

theorem sym2_mk_eq_sym2_mk (htwo : ∀ a b c : ι, a = b ∨ a = c ∨ b = c) {i j k l : ι}
    (hij : i ≠ j) (hkl : k ≠ l) (g : CoprodI G) :
    s(Vertex.mk i g, Vertex.mk j g) = s(Vertex.mk k g, Vertex.mk l g) := by
  rcases htwo i k l with rfl | rfl | h
  · rcases htwo j i l with rfl | rfl | h
    · exact absurd rfl hij
    · rfl
    · exact absurd h hkl
  · rcases htwo j k i with rfl | rfl | h
    · exact Sym2.eq_swap
    · exact absurd rfl hij
    · exact absurd h hkl
  · exact absurd h hkl

theorem isBridge_mk_mk (htwo : ∀ a b c : ι, a = b ∨ a = c ∨ b = c) {i j : ι} (hij : i ≠ j)
    (g : CoprodI G) : (graph G).IsBridge s(Vertex.mk i g, Vertex.mk j g) := by
  refine isBridge_of_separating (fun v => side (g⁻¹ • v)) (adj_mk hij g) ?_ ?_
  · show side (g⁻¹ • Vertex.mk i g) ≠ side (g⁻¹ • Vertex.mk j g)
    rw [smul_mk, smul_mk, inv_mul_cancel, side_mk_one, side_mk_one]
    exact hij
  · rintro v w ⟨hvw, h, hhv, hhw⟩ hne
    show side (g⁻¹ • v) = side (g⁻¹ • w)
    rw [← hhv, ← hhw] at hne ⊢
    rw [smul_mk, smul_mk, side_mk, side_mk]
    rcases eq_or_ne h g with rfl | hhg
    · exact absurd (sym2_mk_eq_sym2_mk htwo hvw hij h) hne
    · exact sideAux_eq_sideAux (fun H => hhg (inv_mul_eq_one.mp H).symm) v.1 w.1

end DecEq

theorem isAcyclic (htwo : ∀ a b c : ι, a = b ∨ a = c ∨ b = c) : (graph G).IsAcyclic := by
  classical
  rw [isAcyclic_iff_forall_adj_isBridge]
  rintro v w ⟨hvw, g, hgv, hgw⟩
  rw [← hgv, ← hgw]
  exact isBridge_mk_mk htwo hvw g

theorem isTree [Nonempty ι] (htwo : ∀ a b c : ι, a = b ∨ a = c ∨ b = c) :
    (graph G).IsTree :=
  isTree_of_isAcyclic (isAcyclic htwo)

theorem isTree_two {G : Fin 2 → Type*} [∀ i, Group (G i)] : (graph G).IsTree :=
  isTree (by decide)

theorem isAcyclic_two {G : Fin 2 → Type*} [∀ i, Group (G i)] : (graph G).IsAcyclic :=
  isAcyclic (by decide)
end GroupTheory.BassSerre

open Subgroup MulAction SimpleGraph Monoid

namespace GroupTheory

namespace GraphTransversal

def WalkConnected {V : Type*} (T : SimpleGraph V) (s : Set V) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ s

structure IsConnectedTransversal {V : Type*} (T : SimpleGraph V) (Γ : Type*) [Group Γ]
    [MulAction Γ V] (D : Set V) : Prop where

  walkConnected : WalkConnected T D

  eq_of_mem_orbit : ∀ v ∈ D, ∀ w ∈ D, v ∈ orbit Γ w → v = w

  exists_mem_orbit : ∀ u : V, ∃ v ∈ D, v ∈ orbit Γ u

variable {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]

theorem walkConnected_singleton (T : SimpleGraph V) (v₀ : V) : WalkConnected T {v₀} := by
  intro v hv w hw
  rw [Set.mem_singleton_iff] at hv hw
  subst hv; subst hw
  exact ⟨Walk.nil, by simp⟩

theorem WalkConnected.insert_of_adj {s : Set V} (hs : WalkConnected T s) {v w : V}
    (hv : v ∈ s) (hadj : T.Adj v w) : WalkConnected T (insert w s) := by
  have key : ∀ x ∈ insert w s, ∃ p : T.Walk v x, ∀ y ∈ p.support, y ∈ insert w s := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨Walk.cons hadj Walk.nil, fun y hy => ?_⟩
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact Set.mem_insert_of_mem _ hv
      · exact Set.mem_insert _ _
    · obtain ⟨p, hp⟩ := hs v hv x hx
      exact ⟨p, fun y hy => Set.mem_insert_of_mem _ (hp y hy)⟩
  intro a ha b hb
  obtain ⟨p, hp⟩ := key a ha
  obtain ⟨q, hq⟩ := key b hb
  refine ⟨p.reverse.append q, fun y hy => ?_⟩
  rw [Walk.support_append, List.mem_append] at hy
  rcases hy with hy | hy
  · rw [Walk.support_reverse, List.mem_reverse] at hy
    exact hp y hy
  · exact hq y (List.mem_of_mem_tail hy)

theorem walkConnected_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hwc : ∀ s ∈ c, WalkConnected T s) : WalkConnected T (⋃₀ c) := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩
  rcases hchain.total hs ht with hst | hts
  · obtain ⟨p, hp⟩ := hwc t ht v (hst hvs) w hwt
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨t, ht, hp x hx⟩⟩
  · obtain ⟨p, hp⟩ := hwc s hs v hvs w (hts hwt)
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨s, hs, hp x hx⟩⟩

private theorem mem_orbit_symm' {a b : V} (h : a ∈ orbit Γ b) : b ∈ orbit Γ a := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ⁻¹, inv_smul_smul γ b⟩

theorem eq_of_mem_orbit_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hinj : ∀ s ∈ c, ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) :
    ∀ v ∈ ⋃₀ c, ∀ w ∈ ⋃₀ c, v ∈ orbit Γ w → v = w := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩ hvw
  rcases hchain.total hs ht with hst | hts
  · exact hinj t ht v (hst hvs) w hwt hvw
  · exact hinj s hs v hvs w (hts hwt) hvw

theorem eq_of_mem_orbit_insert {s : Set V}
    (hs : ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) {w : V}
    (hw : ¬∃ v ∈ s, v ∈ orbit Γ w) :
    ∀ v ∈ insert w s, ∀ v' ∈ insert w s, v ∈ orbit Γ v' → v = v' := by
  intro v hv v' hv' hvv'
  rcases Set.mem_insert_iff.mp hv with rfl | hvs <;>
    rcases Set.mem_insert_iff.mp hv' with rfl | hv's
  · rfl
  · exact absurd ⟨v', hv's, mem_orbit_symm' hvv'⟩ hw
  · exact absurd ⟨v, hvs, hvv'⟩ hw
  · exact hs v hvs v' hv's hvv'

theorem exists_adj_of_walk (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    {s : Set V} {a b : V} (p : T.Walk a b) :
    (∃ v ∈ s, v ∈ orbit Γ a) → (¬∃ v ∈ s, v ∈ orbit Γ b) →
      ∃ v ∈ s, ∃ w, T.Adj v w ∧ ¬∃ v' ∈ s, v' ∈ orbit Γ w := by
  induction p with
  | nil => exact fun ha hb => absurd ha hb
  | @cons a c b hac p ih =>
    intro ha hb
    by_cases hc : ∃ v ∈ s, v ∈ orbit Γ c
    · exact ih hc hb
    · obtain ⟨v, hvs, γ, hγ⟩ := ha
      refine ⟨v, hvs, γ • c, ?_, ?_⟩
      · rw [← hγ]
        exact hsmul γ hac
      · rintro ⟨v', hv's, hv'⟩
        rw [MulAction.orbit_smul] at hv'
        exact hc ⟨v', hv's, hv'⟩

theorem exists_isConnectedTransversal
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧ IsConnectedTransversal T Γ D := by
  classical

  obtain ⟨D, hsub, hDmem, hDmax⟩ := zorn_subset_nonempty
    {s : Set V | v₀ ∈ s ∧ WalkConnected T s ∧ ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w}
    (fun c hc hchain hcne => by
      obtain ⟨s₀, hs₀⟩ := hcne
      exact ⟨⋃₀ c, ⟨Set.mem_sUnion.mpr ⟨s₀, hs₀, (hc hs₀).1⟩,
        walkConnected_sUnion hchain fun s hs => (hc hs).2.1,
        eq_of_mem_orbit_sUnion hchain fun s hs => (hc hs).2.2⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩)
    {v₀}
    ⟨Set.mem_singleton v₀, walkConnected_singleton T v₀, by
      intro v hv w hw _
      rw [Set.mem_singleton_iff] at hv hw
      rw [hv, hw]⟩
  have hv₀D : v₀ ∈ D := hsub (Set.mem_singleton v₀)

  refine ⟨D, hv₀D, hDmem.2.1, hDmem.2.2, fun u => ?_⟩
  by_contra hu

  obtain ⟨p⟩ := hpre v₀ u
  obtain ⟨v, hvD, w, hadj, hw⟩ :=
    exists_adj_of_walk hsmul p ⟨v₀, hv₀D, MulAction.mem_orbit_self v₀⟩ hu

  have hwD : w ∉ D := fun hwD => hw ⟨w, hwD, MulAction.mem_orbit_self w⟩
  have hins : insert w D ∈
      {s : Set V | v₀ ∈ s ∧ WalkConnected T s ∧ ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w} :=
    ⟨Set.mem_insert_of_mem _ hv₀D, hDmem.2.1.insert_of_adj hvD hadj,
      eq_of_mem_orbit_insert hDmem.2.2 hw⟩

  exact hwD (hDmax hins (Set.subset_insert w D) (Set.mem_insert w D))

variable {D : Set V}

noncomputable def orbitRepr (hD : IsConnectedTransversal T Γ D) (v : V) : V :=
  (hD.exists_mem_orbit v).choose

theorem orbitRepr_mem (hD : IsConnectedTransversal T Γ D) (v : V) : orbitRepr hD v ∈ D :=
  (hD.exists_mem_orbit v).choose_spec.1

theorem orbitRepr_mem_orbit (hD : IsConnectedTransversal T Γ D) (v : V) :
    orbitRepr hD v ∈ orbit Γ v :=
  (hD.exists_mem_orbit v).choose_spec.2

noncomputable def transl (hD : IsConnectedTransversal T Γ D) (v : V) : Γ :=
  (orbitRepr_mem_orbit hD v).choose⁻¹

theorem transl_smul_orbitRepr (hD : IsConnectedTransversal T Γ D) (v : V) :
    transl hD v • orbitRepr hD v = v :=
  inv_smul_eq_iff.mpr (orbitRepr_mem_orbit hD v).choose_spec.symm

theorem orbitRepr_eq_self (hD : IsConnectedTransversal T Γ D) {v : V} (hv : v ∈ D) :
    orbitRepr hD v = v :=
  hD.eq_of_mem_orbit _ (orbitRepr_mem hD v) _ hv (orbitRepr_mem_orbit hD v)

theorem orbitRepr_smul (hD : IsConnectedTransversal T Γ D) (γ : Γ) (v : V) :
    orbitRepr hD (γ • v) = orbitRepr hD v := by
  refine hD.eq_of_mem_orbit _ (orbitRepr_mem hD _) _ (orbitRepr_mem hD _) ?_
  rw [MulAction.orbit_eq_iff.mpr (orbitRepr_mem_orbit hD v), ← MulAction.orbit_smul γ v]
  exact orbitRepr_mem_orbit hD (γ • v)

theorem eq_of_smul_eq_smul_of_free (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1)
    {γ γ' : Γ} {v : V} (h : γ • v = γ' • v) : γ = γ' := by
  have h1 : (γ'⁻¹ * γ) • v = v := by rw [mul_smul, h, inv_smul_smul]
  have h2 := hfree _ _ h1
  rwa [inv_mul_eq_one, eq_comm] at h2

theorem transl_eq_one (hD : IsConnectedTransversal T Γ D)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) {v : V} (hv : v ∈ D) :
    transl hD v = 1 := by
  apply hfree _ v
  have h := transl_smul_orbitRepr hD v
  rwa [orbitRepr_eq_self hD hv] at h

theorem mem_of_transl_eq_one (hD : IsConnectedTransversal T Γ D) {v : V}
    (h : transl hD v = 1) : v ∈ D := by
  have h1 := transl_smul_orbitRepr hD v
  rw [h, one_smul] at h1
  rw [← h1]
  exact orbitRepr_mem hD v

theorem transl_smul (hD : IsConnectedTransversal T Γ D)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (γ : Γ) (v : V) :
    transl hD (γ • v) = γ * transl hD v := by
  refine eq_of_smul_eq_smul_of_free hfree (v := orbitRepr hD v) ?_
  rw [mul_smul, transl_smul_orbitRepr, ← orbitRepr_smul hD γ v, transl_smul_orbitRepr]

end GraphTransversal

namespace BassSerre

open GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] {H : Subgroup (CoprodI G)}
  {D : Set (Vertex G)}

theorem smul_adj_subgroup (η : H) {v w : Vertex G} (h : (graph G).Adj v w) :
    (graph G).Adj (η • v) (η • w) :=
  smul_adj (η : CoprodI G) h

theorem exists_transversal (H : Subgroup (CoprodI G)) (v₀ : Vertex G) :
    ∃ D : Set (Vertex G), v₀ ∈ D ∧ IsConnectedTransversal (graph G) H D :=
  GraphTransversal.exists_isConnectedTransversal
    (fun η {_ _} h => smul_adj_subgroup η h) connected.preconnected v₀

theorem forall_smul_eq_of_forall_mem
    (hfree : ∀ h ∈ H, ∀ v : Vertex G, h • v = v → h = 1) :
    ∀ (η : H) (v : Vertex G), η • v = v → η = 1 := fun η v hv =>
  Subtype.ext (hfree (η : CoprodI G) η.2 v hv)

noncomputable def edgeGen (hD : IsConnectedTransversal (graph G) H D) (g : CoprodI G) : H :=
  (transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g)

theorem transl_mk_one_eq (hD : IsConnectedTransversal (graph G) H D) (g : CoprodI G) :
    transl hD (Vertex.mk 1 g) = transl hD (Vertex.mk 0 g) * edgeGen hD g :=
  (mul_inv_cancel_left _ _).symm

theorem transl_mk_mul (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (η : H) (i : Fin 2)
    (g : CoprodI G) :
    transl hD (Vertex.mk i ((η : CoprodI G) * g)) = η * transl hD (Vertex.mk i g) :=
  transl_smul hD hfree η (Vertex.mk i g)

theorem edgeGen_smul (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (η : H) (g : CoprodI G) :
    edgeGen hD ((η : CoprodI G) * g) = edgeGen hD g := by
  show (transl hD (Vertex.mk 0 ((η : CoprodI G) * g)))⁻¹ *
      transl hD (Vertex.mk 1 ((η : CoprodI G) * g)) =
    (transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g)
  rw [transl_mk_mul hD hfree, transl_mk_mul hD hfree]
  group

theorem edgeGen_eq_one_iff (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (g : CoprodI G) :
    edgeGen hD g = 1 ↔ ∃ η : H, Vertex.mk 0 ((η : CoprodI G) * g) ∈ D ∧
      Vertex.mk 1 ((η : CoprodI G) * g) ∈ D := by
  constructor
  · intro h
    have hτ : transl hD (Vertex.mk 1 g) = transl hD (Vertex.mk 0 g) := by
      rw [transl_mk_one_eq hD g, h, mul_one]
    refine ⟨(transl hD (Vertex.mk 0 g))⁻¹, ?_, ?_⟩
    · exact mem_of_transl_eq_one hD
        (by rw [transl_mk_mul hD hfree]; exact inv_mul_cancel _)
    · exact mem_of_transl_eq_one hD
        (by rw [transl_mk_mul hD hfree, hτ]; exact inv_mul_cancel _)
  · rintro ⟨η, h0, h1⟩
    have e0 := transl_eq_one hD hfree h0
    have e1 := transl_eq_one hD hfree h1
    rw [transl_mk_mul hD hfree] at e0 e1
    show (transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g) = 1
    rw [(inv_eq_of_mul_eq_one_right e0).symm, (inv_eq_of_mul_eq_one_right e1).symm]
    group

theorem inv_mul_transl_mem_closure (hD : IsConnectedTransversal (graph G) H D)
    {v w : Vertex G} (hadj : (graph G).Adj v w) :
    (transl hD v)⁻¹ * transl hD w ∈ Subgroup.closure (Set.range (edgeGen hD)) := by
  obtain ⟨hne, g, hgv, hgw⟩ := hadj
  rw [← hgv, ← hgw]
  rcases (by decide : ∀ a b : Fin 2, a ≠ b → a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) v.1 w.1 hne with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact Subgroup.subset_closure (Set.mem_range_self g)
  · rw [h1, h2]
    have hkey : (transl hD (Vertex.mk 1 g))⁻¹ * transl hD (Vertex.mk 0 g) =
        (edgeGen hD g)⁻¹ := by
      show _ = ((transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g))⁻¹
      group
    rw [hkey]
    exact (Subgroup.closure _).inv_mem (Subgroup.subset_closure (Set.mem_range_self g))

theorem inv_mul_transl_mem_closure_of_walk (hD : IsConnectedTransversal (graph G) H D)
    {a b : Vertex G} (p : (graph G).Walk a b) :
    (transl hD a)⁻¹ * transl hD b ∈ Subgroup.closure (Set.range (edgeGen hD)) := by
  induction p with
  | nil =>
    rw [inv_mul_cancel]
    exact (Subgroup.closure _).one_mem
  | @cons a c b hac p ih =>
    have key : (transl hD a)⁻¹ * transl hD b =
        ((transl hD a)⁻¹ * transl hD c) * ((transl hD c)⁻¹ * transl hD b) := by group
    rw [key]
    exact (Subgroup.closure _).mul_mem (inv_mul_transl_mem_closure hD hac) ih

theorem transl_mem_closure (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (v : Vertex G) :
    transl hD v ∈ Subgroup.closure (Set.range (edgeGen hD)) := by
  obtain ⟨d, hd, -⟩ := hD.exists_mem_orbit v
  obtain ⟨p⟩ := connected.preconnected d v
  have h := inv_mul_transl_mem_closure_of_walk hD p
  rwa [transl_eq_one hD hfree hd, inv_one, one_mul] at h

theorem closure_range_edgeGen (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    Subgroup.closure (Set.range (edgeGen hD)) = ⊤ := by
  rw [eq_top_iff]
  intro η _
  obtain ⟨d, hd, -⟩ := hD.exists_mem_orbit (Vertex.mk 0 1)
  have h1 : transl hD (η • d) = η := by
    have h1' := transl_smul hD hfree η d
    rw [transl_eq_one hD hfree hd, mul_one] at h1'
    exact h1'
  rw [← h1]
  exact transl_mem_closure hD hfree _

theorem closure_range_edgeGen_of_forall_mem (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ h ∈ H, ∀ v : Vertex G, h • v = v → h = 1) :
    Subgroup.closure (Set.range (edgeGen hD)) = ⊤ :=
  closure_range_edgeGen hD (forall_smul_eq_of_forall_mem hfree)

end BassSerre

end GroupTheory
open Subgroup MulAction Monoid

namespace GroupTheory

namespace FreeActionTree

section FreeOrbitCount

variable {M : Type*} [Group M] (H K : Subgroup M)


theorem mk''_mk_inv_eq {g g' : M} (η : M) (hη : η ∈ H) (hk : g'⁻¹ * η⁻¹ * g ∈ K) :
    (Quotient.mk'' ((g⁻¹ : M) : M ⧸ H) : orbitRel.Quotient K (M ⧸ H)) =
      Quotient.mk'' ((g'⁻¹ : M) : M ⧸ H) := by
  refine Quotient.sound' (mem_orbit_iff.mpr ⟨(⟨g'⁻¹ * η⁻¹ * g, hk⟩ : K)⁻¹, ?_⟩)
  show (((⟨g'⁻¹ * η⁻¹ * g, hk⟩ : K)⁻¹ : K) : M) • ((g'⁻¹ : M) : M ⧸ H) = ((g⁻¹ : M) : M ⧸ H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
  show ((((g'⁻¹ * η⁻¹ * g)⁻¹ : M) : M) * g'⁻¹)⁻¹ * g⁻¹ ∈ H
  have key : (((g'⁻¹ * η⁻¹ * g)⁻¹ : M) * g'⁻¹)⁻¹ * g⁻¹ = η⁻¹ := by group
  rw [key]
  exact H.inv_mem hη

def toOrbitAux (x : M ⧸ K) : orbitRel.Quotient K (M ⧸ H) :=
  Quotient.liftOn' x (fun g => Quotient.mk'' ((g⁻¹ : M) : M ⧸ H)) fun g g' hgg' => by
    have hk : g'⁻¹ * (1 : M)⁻¹ * g ∈ K := by
      simpa using K.inv_mem (QuotientGroup.leftRel_apply.mp hgg')
    exact mk''_mk_inv_eq H K 1 H.one_mem hk

@[simp]
theorem toOrbitAux_mk (g : M) :
    toOrbitAux H K ((g : M) : M ⧸ K) = Quotient.mk'' ((g⁻¹ : M) : M ⧸ H) :=
  rfl

theorem toOrbitAux_eq_of_mem_orbit {x y : M ⧸ K} (hxy : x ∈ orbit H y) :
    toOrbitAux H K x = toOrbitAux H K y := by
  obtain ⟨η, hη⟩ := hxy
  induction y using QuotientGroup.induction_on with
  | H g' =>
  rw [← hη]
  show toOrbitAux H K (((η : M) * g' : M) : M ⧸ K) = toOrbitAux H K ((g' : M) : M ⧸ K)
  rw [toOrbitAux_mk, toOrbitAux_mk]
  refine mk''_mk_inv_eq H K (η : M) η.2 ?_
  have : g'⁻¹ * (η : M)⁻¹ * ((η : M) * g') = 1 := by group
  rw [this]
  exact K.one_mem

def orbitQuotientEquiv :
    orbitRel.Quotient H (M ⧸ K) ≃ orbitRel.Quotient K (M ⧸ H) where
  toFun q := Quotient.liftOn' q (toOrbitAux H K) fun _ _ h => toOrbitAux_eq_of_mem_orbit H K h
  invFun q := Quotient.liftOn' q (toOrbitAux K H) fun _ _ h => toOrbitAux_eq_of_mem_orbit K H h
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      induction x using QuotientGroup.induction_on with
      | H g =>
        show Quotient.mk'' ((g⁻¹⁻¹ : M) : M ⧸ K) = Quotient.mk'' ((g : M) : M ⧸ K)
        rw [inv_inv]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      induction x using QuotientGroup.induction_on with
      | H g =>
        show Quotient.mk'' ((g⁻¹⁻¹ : M) : M ⧸ H) = Quotient.mk'' ((g : M) : M ⧸ H)
        rw [inv_inv]

noncomputable def quotientEquivOrbitsProd (hKH : Kurosh.ConjTrivial K H) :
    (M ⧸ H) ≃ orbitRel.Quotient K (M ⧸ H) × K := by
  classical
  refine (MulAction.selfEquivSigmaOrbitsQuotientStabilizer K (M ⧸ H)).trans ?_
  refine (Equiv.sigmaCongrRight fun ω => ?_).trans (Equiv.sigmaEquivProd _ _)
  exact (Subgroup.quotientEquivOfEq
    (Kurosh.stabilizer_eq_bot_of_conjTrivial K H hKH ω.out)).trans
    QuotientGroup.quotientBot.toEquiv

theorem card_orbitRelQuotient_mul_card' (hKH : Kurosh.ConjTrivial K H) :
    Nat.card (orbitRel.Quotient H (M ⧸ K)) * Nat.card K = H.index := by
  rw [Nat.card_congr (orbitQuotientEquiv H K), Subgroup.index_eq_card,
    Nat.card_congr (quotientEquivOrbitsProd H K hKH), Nat.card_prod]

theorem finite_orbitRelQuotient [H.FiniteIndex] (hKH : Kurosh.ConjTrivial K H) :
    Finite (orbitRel.Quotient H (M ⧸ K)) := by
  refine Nat.finite_of_card_ne_zero fun h0 => ?_
  have := card_orbitRelQuotient_mul_card' H K hKH
  rw [h0, zero_mul] at this
  exact Subgroup.FiniteIndex.index_ne_zero this.symm

theorem card_orbitRelQuotient_eq_index_div (hK : Nat.card K ≠ 0)
    (hKH : Kurosh.ConjTrivial K H) :
    Nat.card (orbitRel.Quotient H (M ⧸ K)) = H.index / Nat.card K := by
  rw [← card_orbitRelQuotient_mul_card' H K hKH,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hK)]

end FreeOrbitCount

section VertexOrbits

variable {G : Fin 2 → Type*} [∀ i, Group (G i)]

abbrev ComponentOrbits (H : Subgroup (CoprodI G)) (i : Fin 2) : Type _ :=
  orbitRel.Quotient H (CoprodI G ⧸ (CoprodI.of (M := G) (i := i)).range)

def vertexToSigma (H : Subgroup (CoprodI G)) (v : BassSerre.Vertex G) :
    Σ i : Fin 2, ComponentOrbits H i :=
  ⟨v.1, Quotient.mk'' v.2⟩

theorem vertexToSigma_smul (H : Subgroup (CoprodI G)) (η : H) (v : BassSerre.Vertex G) :
    vertexToSigma H ((η : CoprodI G) • v) = vertexToSigma H v := by
  obtain ⟨i, x⟩ := v
  show (⟨i, Quotient.mk'' ((η : CoprodI G) • x)⟩ : Σ i, ComponentOrbits H i)
    = ⟨i, Quotient.mk'' x⟩
  refine congrArg (Sigma.mk i) (Quotient.sound' ?_)
  exact mem_orbit_iff.mpr ⟨η, rfl⟩

theorem vertexToSigma_eq_of_mem_orbit (H : Subgroup (CoprodI G)) {v w : BassSerre.Vertex G}
    (hvw : v ∈ orbit H w) : vertexToSigma H v = vertexToSigma H w := by
  obtain ⟨η, hη⟩ := hvw
  rw [← hη]
  exact vertexToSigma_smul H η w

def sigmaToVertexOrbit (H : Subgroup (CoprodI G)) (p : Σ i : Fin 2, ComponentOrbits H i) :
    orbitRel.Quotient H (BassSerre.Vertex G) :=
  Quotient.liftOn' p.2
    (fun x => Quotient.mk'' (⟨p.1, x⟩ : BassSerre.Vertex G)) fun x y hxy => by
      obtain ⟨η, hη⟩ : x ∈ orbit H y := hxy
      refine Quotient.sound' (mem_orbit_iff.mpr ⟨η, ?_⟩)
      show (⟨p.1, (η : CoprodI G) • y⟩ : BassSerre.Vertex G) = ⟨p.1, x⟩
      rw [show (η : CoprodI G) • y = x from hη]

def vertexOrbitEquivSigma (H : Subgroup (CoprodI G)) :
    orbitRel.Quotient H (BassSerre.Vertex G) ≃ Σ i : Fin 2, ComponentOrbits H i where
  toFun q := Quotient.liftOn' q (vertexToSigma H)
    fun _ _ h => vertexToSigma_eq_of_mem_orbit H h
  invFun := sigmaToVertexOrbit H
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h v =>
      obtain ⟨i, x⟩ := v
      rfl
  right_inv p := by
    obtain ⟨i, ω⟩ := p
    induction ω using Quotient.inductionOn' with
    | h x => rfl

variable [∀ i, Finite (G i)]

theorem card_vertexOrbits (H : Subgroup (CoprodI G)) [H.FiniteIndex]
    (hCT : ∀ i, Kurosh.ConjTrivial (CoprodI.of (M := G) (i := i)).range H) :
    Nat.card (orbitRel.Quotient H (BassSerre.Vertex G)) =
      H.index / Nat.card (G 0) + H.index / Nat.card (G 1) := by
  classical
  haveI hfin : ∀ i : Fin 2, Finite (ComponentOrbits H i) := fun i =>
    finite_orbitRelQuotient H _ (hCT i)
  have hcard : ∀ i : Fin 2, Nat.card (ComponentOrbits H i) = H.index / Nat.card (G i) := by
    intro i
    rw [← Kurosh.card_range_of (G := G) i]
    refine card_orbitRelQuotient_eq_index_div H _ ?_ (hCT i)
    rw [Kurosh.card_range_of (G := G) i]
    exact Nat.card_pos.ne'
  rw [Nat.card_congr (vertexOrbitEquivSigma H), Nat.card_sigma, Fin.sum_univ_two, hcard 0,
    hcard 1]

omit [∀ i, Finite (G i)] in

theorem finite_vertexOrbits (H : Subgroup (CoprodI G)) [H.FiniteIndex]
    (hCT : ∀ i, Kurosh.ConjTrivial (CoprodI.of (M := G) (i := i)).range H) :
    Finite (orbitRel.Quotient H (BassSerre.Vertex G)) := by
  haveI hfin : ∀ i : Fin 2, Finite (ComponentOrbits H i) := fun i =>
    finite_orbitRelQuotient H _ (hCT i)
  exact Finite.of_equiv _ (vertexOrbitEquivSigma H).symm

theorem kuroshRank_eq_one_add_index_sub (H : Subgroup (CoprodI G)) [H.FiniteIndex]
    (hCT : ∀ i, Kurosh.ConjTrivial (CoprodI.of (M := G) (i := i)).range H) :
    Kurosh.kuroshRank (Nat.card (G 0)) (Nat.card (G 1)) H.index =
      1 + H.index - Nat.card (orbitRel.Quotient H (BassSerre.Vertex G)) := by
  rw [card_vertexOrbits H hCT, Kurosh.kuroshRank, Nat.sub_sub]

end VertexOrbits

section Residual

variable (G : Fin 2 → Type*) [∀ i, Group (G i)]

def FreeActionRankFormula : Prop :=
  ∀ H : Subgroup (CoprodI G), H.FiniteIndex →
    (∀ h ∈ H, ∀ v : BassSerre.Vertex G, h • v = v → h = 1) →
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index - Nat.card (orbitRel.Quotient H (BassSerre.Vertex G)))) H)

variable {G} [∀ i, Finite (G i)]

theorem kuroshRankFormula_of_freeActionRankFormula (hfree : FreeActionRankFormula G) :
    Kurosh.KuroshRankFormula G := by
  intro H hFI hCT
  obtain ⟨b⟩ := hfree H hFI (BassSerre.conjTrivial_iff_forall_smul_ne.mp hCT)
  exact ⟨b.reindex (finCongr (kuroshRank_eq_one_add_index_sub H hCT).symm)⟩

end Residual

end FreeActionTree

end GroupTheory
open Subgroup MulAction SimpleGraph Monoid

namespace SimpleGraph
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b u v w : V}

variable (G a b) in

def farSide : Set V :=
  {v | ¬ (G.deleteEdges {s(a, b)}).Reachable a v}

theorem mem_farSide_iff : v ∈ G.farSide a b ↔ ¬ (G.deleteEdges {s(a, b)}).Reachable a v :=
  Iff.rfl

theorem notMem_farSide_left : a ∉ G.farSide a b := fun h => h (Reachable.refl a)

theorem mem_farSide_right (h : G.IsBridge s(a, b)) : b ∈ G.farSide a b :=
  (isBridge_iff).mp h

theorem reachable_of_mem_walk_support (p : G.Walk u v) (hw : w ∈ p.support) :
    G.Reachable u w := by
  induction p with
  | nil =>
    rw [Walk.mem_support_nil_iff] at hw
    exact hw ▸ Reachable.refl _
  | cons h p ih =>
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact Reachable.refl _
    · exact h.reachable.trans (ih hw)

theorem eq_of_adj_of_mem_farSide (hadj : G.Adj v w) (hv : v ∈ G.farSide a b)
    (hw : w ∉ G.farSide a b) : v = b ∧ w = a := by
  rw [mem_farSide_iff, not_not] at hw
  have hedge : s(v, w) = s(a, b) := by
    by_contra hne
    refine hv (hw.trans (Adj.reachable (deleteEdges_adj.mpr ⟨hadj.symm, ?_⟩)))
    rw [Set.mem_singleton_iff]
    intro hcon
    exact hne ((Sym2.eq_swap).trans hcon)
  rcases Sym2.eq_iff.mp hedge with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · exact absurd hv notMem_farSide_left
  · exact ⟨h1, h2⟩

theorem mem_support_of_mem_farSide (p : G.Walk v w) :
    v ∈ G.farSide a b → w ∉ G.farSide a b → a ∈ p.support ∧ b ∈ p.support := by
  induction p with
  | nil => exact fun hv hw => absurd hv hw
  | @cons x y z hadj q ih =>
    intro hv hw
    by_cases hy : y ∈ G.farSide a b
    · obtain ⟨ha, hb⟩ := ih hy hw
      rw [Walk.support_cons]
      exact ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩
    · obtain ⟨hxb, hya⟩ := eq_of_adj_of_mem_farSide hadj hv hy
      constructor
      · rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ (hya ▸ q.start_mem_support)
      · exact hxb ▸ (Walk.cons hadj q).start_mem_support

theorem farSide_subset_farSide {p q x y : V} (hx : x ∈ G.farSide p q)
    (hp : p ∉ G.farSide x y) : G.farSide x y ⊆ G.farSide p q := by
  intro v hv hWpv
  rw [mem_farSide_iff, not_not] at hp
  obtain ⟨W⟩ := hWpv
  have hW : ∀ e ∈ W.edges, e ∈ (G.deleteEdges {s(x, y)}).edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · have hmem := W.edges_subset_edgeSet he
      rw [edgeSet_deleteEdges] at hmem
      exact hmem.1
    · rintro rfl
      exact hx (reachable_of_mem_walk_support W (W.fst_mem_support_of_mem_edges he))
  exact hv (hp.trans ⟨W.transfer _ hW⟩)

end SimpleGraph

namespace GroupTheory

namespace BassSerre

open GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] {H : Subgroup (CoprodI G)}
  {D : Set (Vertex G)}

theorem reachable_deleteEdges_smul (g : CoprodI G) {a b u v : Vertex G}
    (h : ((graph G).deleteEdges {s(a, b)}).Reachable u v) :
    ((graph G).deleteEdges {s(g • a, g • b)}).Reachable (g • u) (g • v) := by
  refine h.map ⟨fun x => g • x, ?_⟩
  intro x y hxy
  rw [deleteEdges_adj] at hxy ⊢
  refine ⟨smul_adj g hxy.1, fun hcon => hxy.2 ?_⟩
  rw [Set.mem_singleton_iff] at hcon ⊢
  rcases Sym2.eq_iff.mp hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨MulAction.injective g h1, MulAction.injective g h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨MulAction.injective g h1, MulAction.injective g h2⟩)

theorem smul_mem_farSide_smul (g : CoprodI G) {a b v : Vertex G}
    (hv : v ∈ (graph G).farSide a b) :
    g • v ∈ (graph G).farSide (g • a) (g • b) := by
  intro hcon
  apply hv
  have hback := reachable_deleteEdges_smul g⁻¹ hcon
  simpa only [inv_smul_smul] using hback

variable (hD : IsConnectedTransversal (graph G) H D)

theorem transl_coe_smul (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (η : H)
    (v : Vertex G) : transl hD ((η : CoprodI G) • v) = η * transl hD v :=
  transl_smul hD hfree η v

theorem exists_walk_of_transl_eq (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    {γ : H} {v w : Vertex G} (hv : transl hD v = γ) (hw : transl hD w = γ) :
    ∃ p : (graph G).Walk v w, ∀ x ∈ p.support, transl hD x = γ := by
  obtain ⟨p₀, hp₀⟩ := hD.walkConnected (orbitRepr hD v) (orbitRepr_mem hD v)
    (orbitRepr hD w) (orbitRepr_mem hD w)
  refine ⟨(p₀.map (smulHom (γ : CoprodI G))).copy ?_ ?_, ?_⟩
  · show (γ : CoprodI G) • orbitRepr hD v = v
    rw [← hv]
    exact transl_smul_orbitRepr hD v
  · show (γ : CoprodI G) • orbitRepr hD w = w
    rw [← hw]
    exact transl_smul_orbitRepr hD w
  · intro x hx
    rw [Walk.support_copy, Walk.support_map, List.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    show transl hD ((γ : CoprodI G) • d) = γ
    rw [transl_coe_smul hD hfree, transl_eq_one hD hfree (hp₀ d hd), mul_one]

include hD in

theorem notMem_farSide_of_mem {p q : Vertex G} (hp : p ∈ D) (hq : q ∉ D) {v : Vertex G}
    (hv : v ∈ D) : v ∉ (graph G).farSide p q := by
  intro hcon
  obtain ⟨W, hW⟩ := hD.walkConnected v hv p hp
  obtain ⟨-, hbq⟩ := mem_support_of_mem_farSide W hcon notMem_farSide_left
  exact hq (hW q hbq)

theorem mem_farSide_of_transl_eq (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    {p q : Vertex G} (hadj : (graph G).Adj p q) (hp : p ∈ D) (hq : q ∉ D) {v : Vertex G}
    (hv : transl hD v = transl hD q) : v ∈ (graph G).farSide p q := by
  by_contra hcon
  obtain ⟨W, hW⟩ := exists_walk_of_transl_eq hD hfree (rfl : transl hD q = transl hD q) hv
  have hbridge : (graph G).IsBridge s(p, q) :=
    (isAcyclic_iff_forall_adj_isBridge.mp isAcyclic_two) hadj
  obtain ⟨hpa, -⟩ := mem_support_of_mem_farSide W (mem_farSide_right hbridge) hcon
  have h1 : transl hD p = transl hD q := hW p hpa
  rw [transl_eq_one hD hfree hp] at h1
  exact hq (mem_of_transl_eq_one hD h1.symm)

variable (H) in

def nonTreeRep (hD : IsConnectedTransversal (graph G) H D) : Set (CoprodI G) :=
  {g | Vertex.mk 0 g ∈ D ∧ edgeGen hD g ≠ 1}

theorem mk_zero_mem_of_mem_nonTreeRep {g : CoprodI G} (hg : g ∈ nonTreeRep H hD) :
    Vertex.mk 0 g ∈ D :=
  hg.1

theorem edgeGen_ne_one_of_mem_nonTreeRep {g : CoprodI G} (hg : g ∈ nonTreeRep H hD) :
    edgeGen hD g ≠ 1 :=
  hg.2

include hD in

theorem eq_of_mk_zero_mem (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    {g g' : CoprodI G} (hg : Vertex.mk 0 g ∈ D) (hg' : Vertex.mk 0 g' ∈ D) (η : H)
    (hη : (η : CoprodI G) * g = g') : g = g' := by
  have horb : Vertex.mk 0 g' ∈ orbit H (Vertex.mk (G := G) 0 g) := by
    refine mem_orbit_iff.mpr ⟨η, ?_⟩
    show (η : CoprodI G) • Vertex.mk 0 g = Vertex.mk 0 g'
    rw [smul_mk, hη]
  have heq : Vertex.mk (G := G) 0 g' = Vertex.mk 0 g := hD.eq_of_mem_orbit _ hg' _ hg horb
  have hfix : η • Vertex.mk (G := G) 0 g = Vertex.mk 0 g := by
    show (η : CoprodI G) • Vertex.mk 0 g = Vertex.mk 0 g
    rw [smul_mk, hη]
    exact heq
  have hone := hfree η _ hfix
  rw [← hη, hone, OneMemClass.coe_one, one_mul]

variable (H) in

noncomputable def letterImage (hD : IsConnectedTransversal (graph G) H D)
    (x : nonTreeRep H hD × Bool) :
    H :=
  cond x.2 (edgeGen hD (x.1 : CoprodI G)) (edgeGen hD (x.1 : CoprodI G))⁻¹

@[simp]
theorem letterImage_true (g : nonTreeRep H hD) :
    letterImage H hD (g, true) = edgeGen hD (g : CoprodI G) :=
  rfl

@[simp]
theorem letterImage_false (g : nonTreeRep H hD) :
    letterImage H hD (g, false) = (edgeGen hD (g : CoprodI G))⁻¹ :=
  rfl

theorem letterImage_ne_one (x : nonTreeRep H hD × Bool) : letterImage H hD x ≠ 1 := by
  obtain ⟨g, _ | _⟩ := x
  · simpa using g.2.2
  · exact g.2.2

variable (H) in

noncomputable def exitSrc (hD : IsConnectedTransversal (graph G) H D) :
    nonTreeRep H hD × Bool → Vertex G
  | (g, true) => Vertex.mk 0 (g : CoprodI G)
  | (g, false) =>
      Vertex.mk 1 ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G) * (g : CoprodI G))

variable (H) in

noncomputable def exitTgt (hD : IsConnectedTransversal (graph G) H D) :
    nonTreeRep H hD × Bool → Vertex G
  | (g, true) => Vertex.mk 1 (g : CoprodI G)
  | (g, false) =>
      Vertex.mk 0 ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G) * (g : CoprodI G))

@[simp]
theorem exitSrc_true (g : nonTreeRep H hD) :
    exitSrc H hD (g, true) = Vertex.mk 0 (g : CoprodI G) :=
  rfl

@[simp]
theorem exitSrc_false (g : nonTreeRep H hD) :
    exitSrc H hD (g, false) =
      Vertex.mk 1 ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G) * (g : CoprodI G)) :=
  rfl

@[simp]
theorem exitTgt_true (g : nonTreeRep H hD) :
    exitTgt H hD (g, true) = Vertex.mk 1 (g : CoprodI G) :=
  rfl

@[simp]
theorem exitTgt_false (g : nonTreeRep H hD) :
    exitTgt H hD (g, false) =
      Vertex.mk 0 ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G) * (g : CoprodI G)) :=
  rfl

theorem adj_exit (x : nonTreeRep H hD × Bool) :
    (graph G).Adj (exitSrc H hD x) (exitTgt H hD x) := by
  obtain ⟨g, _ | _⟩ := x
  · exact adj_mk (by decide) _
  · exact adj_mk (by decide) _

theorem transl_exitSrc (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    (x : nonTreeRep H hD × Bool) : transl hD (exitSrc H hD x) = 1 := by
  obtain ⟨g, _ | _⟩ := x
  · rw [exitSrc_false, transl_mk_mul hD hfree, transl_mk_one_eq hD,
      transl_eq_one hD hfree g.2.1, one_mul, inv_mul_cancel]
  · exact transl_eq_one hD hfree g.2.1

theorem exitSrc_mem (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    (x : nonTreeRep H hD × Bool) : exitSrc H hD x ∈ D :=
  mem_of_transl_eq_one hD (transl_exitSrc hD hfree x)

theorem transl_exitTgt (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    (x : nonTreeRep H hD × Bool) : transl hD (exitTgt H hD x) = letterImage H hD x := by
  obtain ⟨g, _ | _⟩ := x
  · rw [exitTgt_false, transl_mk_mul hD hfree, transl_eq_one hD hfree g.2.1, mul_one,
      letterImage_false]
  · rw [exitTgt_true, transl_mk_one_eq hD, transl_eq_one hD hfree g.2.1, one_mul,
      letterImage_true]

theorem exitTgt_notMem (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    (x : nonTreeRep H hD × Bool) : exitTgt H hD x ∉ D := fun h =>
  letterImage_ne_one hD x ((transl_exitTgt hD hfree x).symm.trans (transl_eq_one hD hfree h))

abbrev revLetter {α : Type*} (x : α × Bool) : α × Bool :=
  (x.1, !x.2)

theorem letterImage_smul_exitSrc_rev (x : nonTreeRep H hD × Bool) :
    ((letterImage H hD x : H) : CoprodI G) • exitSrc H hD (revLetter x) = exitTgt H hD x := by
  obtain ⟨g, _ | _⟩ := x
  · show ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G)) • Vertex.mk 0 (g : CoprodI G) = _
    rw [smul_mk]
    rfl
  · show ((edgeGen hD (g : CoprodI G) : H) : CoprodI G) •
      Vertex.mk 1 ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G) * (g : CoprodI G)) = _
    rw [smul_mk, ← mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one, one_mul]
    rfl

theorem letterImage_smul_exitTgt_rev (x : nonTreeRep H hD × Bool) :
    ((letterImage H hD x : H) : CoprodI G) • exitTgt H hD (revLetter x) = exitSrc H hD x := by
  obtain ⟨g, _ | _⟩ := x
  · show ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G)) • Vertex.mk 1 (g : CoprodI G) = _
    rw [smul_mk]
    rfl
  · show ((edgeGen hD (g : CoprodI G) : H) : CoprodI G) •
      Vertex.mk 0 ((((edgeGen hD (g : CoprodI G))⁻¹ : H) : CoprodI G) * (g : CoprodI G)) = _
    rw [smul_mk, ← mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one, one_mul]
    rfl

theorem eq_of_exit_eq (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    {x y : nonTreeRep H hD × Bool} (hsrc : exitSrc H hD x = exitSrc H hD y)
    (htgt : exitTgt H hD x = exitTgt H hD y) : x = y := by
  obtain ⟨g, bx⟩ := x
  obtain ⟨g', by'⟩ := y
  cases bx <;> cases by'
  · rw [exitSrc_false, exitSrc_false] at hsrc
    rw [exitTgt_false, exitTgt_false] at htgt
    have hwit := eq_of_mk_eq_mk (by decide : (1 : Fin 2) ≠ 0) hsrc htgt
    have hconj : ((edgeGen hD (g' : CoprodI G) * (edgeGen hD (g : CoprodI G))⁻¹ : H) :
        CoprodI G) * (g : CoprodI G) = (g' : CoprodI G) := by
      rw [Subgroup.coe_mul, mul_assoc, hwit, ← mul_assoc, ← Subgroup.coe_mul,
        mul_inv_cancel, OneMemClass.coe_one, one_mul]
    have hgg' : (g : CoprodI G) = (g' : CoprodI G) :=
      eq_of_mk_zero_mem hD hfree g.2.1 g'.2.1 _ hconj
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext hgg', rfl⟩
  · rw [exitSrc_false, exitSrc_true] at hsrc
    have hcon : (1 : Fin 2) = 0 := congrArg Sigma.fst hsrc
    exact absurd hcon (by decide)
  · rw [exitSrc_true, exitSrc_false] at hsrc
    have hcon : (0 : Fin 2) = 1 := congrArg Sigma.fst hsrc
    exact absurd hcon (by decide)
  · rw [exitSrc_true, exitSrc_true] at hsrc
    rw [exitTgt_true, exitTgt_true] at htgt
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext (eq_of_mk_eq_mk (by decide : (0 : Fin 2) ≠ 1) hsrc htgt), rfl⟩

theorem letterImage_smul_mem_farSide_of_mem
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (x : nonTreeRep H hD × Bool)
    {v : Vertex G} (hv : v ∈ D) :
    ((letterImage H hD x : H) : CoprodI G) • v ∈
      (graph G).farSide (exitSrc H hD x) (exitTgt H hD x) := by
  refine mem_farSide_of_transl_eq hD hfree (adj_exit hD x) (exitSrc_mem hD hfree x)
    (exitTgt_notMem hD hfree x) ?_
  rw [transl_coe_smul hD hfree, transl_eq_one hD hfree hv, mul_one,
    transl_exitTgt hD hfree x]

theorem letterImage_smul_mem_farSide (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    (x y : nonTreeRep H hD × Bool) (hxy : y ≠ revLetter x) {v : Vertex G}
    (hv : v ∈ (graph G).farSide (exitSrc H hD y) (exitTgt H hD y)) :
    ((letterImage H hD x : H) : CoprodI G) • v ∈
      (graph G).farSide (exitSrc H hD x) (exitTgt H hD x) := by
  set γ : CoprodI G := ((letterImage H hD x : H) : CoprodI G) with hγ
  have hE1 : γ • exitSrc H hD (revLetter x) = exitTgt H hD x := by
    rw [hγ]; exact letterImage_smul_exitSrc_rev hD x
  have hE2 : γ • exitTgt H hD (revLetter x) = exitSrc H hD x := by
    rw [hγ]; exact letterImage_smul_exitTgt_rev hD x
  have hcoc : ∀ z : Vertex G, transl hD (γ • z) = letterImage H hD x * transl hD z := by
    intro z
    rw [hγ]
    exact transl_coe_smul hD hfree _ z
  have h1 : γ • v ∈ (graph G).farSide (γ • exitSrc H hD y) (γ • exitTgt H hD y) :=
    smul_mem_farSide_smul γ hv
  have htv : transl hD (γ • exitSrc H hD y) = letterImage H hD x := by
    rw [hcoc, transl_exitSrc hD hfree y, mul_one]
  have hsrc : γ • exitSrc H hD y ∈ (graph G).farSide (exitSrc H hD x) (exitTgt H hD x) :=
    mem_farSide_of_transl_eq hD hfree (adj_exit hD x) (exitSrc_mem hD hfree x)
      (exitTgt_notMem hD hfree x) (htv.trans (transl_exitTgt hD hfree x).symm)
  have hp : exitSrc H hD x ∉ (graph G).farSide (γ • exitSrc H hD y) (γ • exitTgt H hD y) := by
    rw [mem_farSide_iff, not_not]
    obtain ⟨W, hW⟩ := exists_walk_of_transl_eq hD hfree htv (transl_exitTgt hD hfree x)
    have htgtW : γ • exitTgt H hD y ∉ W.support := by
      intro hmem
      have hmm := hW _ hmem
      rw [hcoc, transl_exitTgt hD hfree y] at hmm
      exact letterImage_ne_one hD y (mul_left_cancel (hmm.trans (mul_one _).symm))
    refine ⟨(W.append (Walk.cons (adj_exit hD x).symm Walk.nil)).toDeleteEdges _ ?_⟩
    intro e he
    rw [Walk.edges_append, List.mem_append] at he
    rw [Set.mem_singleton_iff]
    rcases he with he | he
    · rintro rfl
      exact htgtW (W.snd_mem_support_of_mem_edges he)
    · rw [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he
      subst he
      intro hcon
      rcases Sym2.eq_iff.mp hcon with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · apply hxy
        refine (eq_of_exit_eq hD hfree ?_ ?_).symm
        · exact MulAction.injective γ (hE1.trans h1')
        · exact MulAction.injective γ (hE2.trans h2')
      · have hcontra : (1 : H) = letterImage H hD x := by
          rw [← transl_exitSrc hD hfree x, h2', htv]
        exact letterImage_ne_one hD x hcontra.symm
  exact farSide_subset_farSide hsrc hp h1

end BassSerre

end GroupTheory

namespace GroupTheory

namespace BassSerre

open GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] {H : Subgroup (CoprodI G)}
  {D : Set (Vertex G)} (hD : IsConnectedTransversal (graph G) H D)

variable (H) in

noncomputable def basisFun (hD : IsConnectedTransversal (graph G) H D) (g : nonTreeRep H hD) :
    H :=
  edgeGen hD (g : CoprodI G)

theorem cond_basisFun_eq_letterImage (x : nonTreeRep H hD × Bool) :
    cond x.2 (basisFun H hD x.1) (basisFun H hD x.1)⁻¹ = letterImage H hD x := by
  obtain ⟨g, _ | _⟩ := x <;> rfl

theorem prod_map_smul_mem_farSide (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    {d₀ : Vertex G} (hd₀ : d₀ ∈ D) (x : nonTreeRep H hD × Bool)
    (L : List (nonTreeRep H hD × Bool))
    (hred : ∀ (L₂ : List (nonTreeRep H hD × Bool)) (z : nonTreeRep H hD) (c : Bool)
      (L₃ : List (nonTreeRep H hD × Bool)), x :: L ≠ L₂ ++ (z, c) :: (z, !c) :: L₃) :
    ((((x :: L).map fun w => cond w.2 (basisFun H hD w.1) (basisFun H hD w.1)⁻¹).prod : H) :
        CoprodI G) • d₀ ∈ (graph G).farSide (exitSrc H hD x) (exitTgt H hD x) := by
  induction L generalizing x with
  | nil =>
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      cond_basisFun_eq_letterImage]
    exact letterImage_smul_mem_farSide_of_mem hD hfree x hd₀
  | cons y L ih =>
    have hxy : y ≠ revLetter x := by
      intro hcon
      exact hred [] x.1 x.2 L (by rw [List.nil_append, hcon])
    have hredtail : ∀ (L₂ : List (nonTreeRep H hD × Bool)) (z : nonTreeRep H hD) (c : Bool)
        (L₃ : List (nonTreeRep H hD × Bool)), y :: L ≠ L₂ ++ (z, c) :: (z, !c) :: L₃ := by
      intro L₂ z c L₃ hcon
      exact hred (x :: L₂) z c L₃ (by rw [List.cons_append, hcon])
    have htail := ih y hredtail
    simp only [List.map_cons, List.prod_cons, cond_basisFun_eq_letterImage] at htail ⊢
    rw [Subgroup.coe_mul, mul_smul]
    exact letterImage_smul_mem_farSide hD hfree x y hxy htail

theorem lift_basisFun_injective (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    Function.Injective (FreeGroup.lift (basisFun H hD)) := by
  classical
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  have hL : FreeGroup.toWord a ≠ [] := fun h => hne (FreeGroup.toWord_eq_nil_iff.mp h)
  obtain ⟨x, L, hxL⟩ : ∃ x L, FreeGroup.toWord a = x :: L := by
    cases h : FreeGroup.toWord a with
    | nil => exact absurd h hL
    | cons x L => exact ⟨x, L, rfl⟩
  have hred : ∀ (L₂ : List (nonTreeRep H hD × Bool)) (z : nonTreeRep H hD) (c : Bool)
      (L₃ : List (nonTreeRep H hD × Bool)), x :: L ≠ L₂ ++ (z, c) :: (z, !c) :: L₃ := by
    intro L₂ z c L₃ hcon
    exact FreeGroup.reduce.not ((FreeGroup.reduce_toWord a).trans (hxL.trans hcon))
  obtain ⟨d₀, hd₀, -⟩ := hD.exists_mem_orbit (Vertex.mk 0 1)
  have hmem := prod_map_smul_mem_farSide hD hfree hd₀ x L hred
  rw [← hxL, ← FreeGroup.lift_mk, FreeGroup.mk_toWord, ha, OneMemClass.coe_one,
    one_smul] at hmem
  exact notMem_farSide_of_mem hD (exitSrc_mem hD hfree x) (exitTgt_notMem hD hfree x) hd₀ hmem

theorem closure_range_basisFun (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    Subgroup.closure (Set.range (basisFun H hD)) = ⊤ := by
  rw [eq_top_iff, ← closure_range_edgeGen hD hfree]
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro _ ⟨g, rfl⟩
  by_cases hg : edgeGen hD g = 1
  · rw [hg]
    exact Subgroup.one_mem _
  · set η : H := (transl hD (Vertex.mk 0 g))⁻¹ with hη
    have hbased : Vertex.mk (G := G) 0 ((η : CoprodI G) * g) ∈ D := by
      refine mem_of_transl_eq_one hD ?_
      rw [transl_mk_mul hD hfree, hη, inv_mul_cancel]
    have hgen : edgeGen hD ((η : CoprodI G) * g) = edgeGen hD g := edgeGen_smul hD hfree η g
    refine Subgroup.subset_closure ⟨⟨(η : CoprodI G) * g, hbased, ?_⟩, hgen⟩
    rw [hgen]
    exact hg

noncomputable def freeGroupBasis (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    FreeGroupBasis (nonTreeRep H hD) H :=
  FreeGroupBasis.ofRepr
    (MulEquiv.ofBijective (FreeGroup.lift (basisFun H hD))
      ⟨lift_basisFun_injective hD hfree,
        MonoidHom.range_eq_top.mp
          (FreeGroup.range_lift_eq_closure.trans (closure_range_basisFun hD hfree))⟩).symm

end BassSerre

end GroupTheory

namespace GroupTheory

namespace BassSerre

open GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] {H : Subgroup (CoprodI G)}
  {D : Set (Vertex G)} (hD : IsConnectedTransversal (graph G) H D)

variable (H) in

def baseRep (_hD : IsConnectedTransversal (graph G) H D) : Set (CoprodI G) :=
  {g | Vertex.mk 0 g ∈ D}

variable (H) in

def treeRep (hD : IsConnectedTransversal (graph G) H D) : Set (CoprodI G) :=
  {g | Vertex.mk 0 g ∈ D ∧ edgeGen hD g = 1}

theorem mk_one_mem_of_mem_treeRep (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    {g : CoprodI G} (hg : g ∈ treeRep H hD) : Vertex.mk 1 g ∈ D := by
  refine mem_of_transl_eq_one hD ?_
  rw [transl_mk_one_eq hD, transl_eq_one hD hfree hg.1, one_mul, hg.2]

theorem mem_treeRep_of_mk_one_mem (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1)
    {g : CoprodI G} (hg : Vertex.mk 0 g ∈ D) (hg' : Vertex.mk 1 g ∈ D) :
    g ∈ treeRep H hD := by
  refine ⟨hg, ?_⟩
  have h1 := transl_eq_one hD hfree hg'
  rw [transl_mk_one_eq hD, transl_eq_one hD hfree hg, one_mul] at h1
  exact h1

noncomputable def baseRepEquivQuotient
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    baseRep H hD ≃ (CoprodI G ⧸ H) := by
  refine Equiv.ofBijective (fun g => QuotientGroup.mk (g : CoprodI G)⁻¹) ⟨?_, ?_⟩
  · intro g g' hgg'
    have hH : ((g : CoprodI G)⁻¹)⁻¹ * ((g' : CoprodI G))⁻¹ ∈ H := QuotientGroup.eq.mp hgg'
    rw [inv_inv] at hH
    refine Subtype.ext (eq_of_mk_zero_mem hD hfree g'.2 g.2 ⟨_, hH⟩ ?_).symm
    show (g : CoprodI G) * (g' : CoprodI G)⁻¹ * (g' : CoprodI G) = (g : CoprodI G)
    exact inv_mul_cancel_right _ _
  · intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      refine ⟨⟨(((transl hD (Vertex.mk 0 y⁻¹))⁻¹ : H) : CoprodI G) * y⁻¹, ?_⟩, ?_⟩
      · refine mem_of_transl_eq_one hD ?_
        rw [transl_mk_mul hD hfree, inv_mul_cancel]
      · refine (QuotientGroup.eq).mpr ?_
        show (((((transl hD (Vertex.mk 0 y⁻¹))⁻¹ : H) : CoprodI G) * y⁻¹)⁻¹)⁻¹ * y ∈ H
        rw [inv_inv, mul_assoc, inv_mul_cancel, mul_one]
        exact SetLike.coe_mem _

theorem nat_card_baseRep (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    Nat.card (baseRep H hD) = H.index := by
  rw [Nat.card_congr (baseRepEquivQuotient hD hfree), Subgroup.index_eq_card]

theorem finite_baseRep [H.FiniteIndex]
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    Finite (baseRep H hD) :=
  Finite.of_equiv _ (baseRepEquivQuotient hD hfree).symm

include hD in

noncomputable def transversalEquivOrbits :
    D ≃ MulAction.orbitRel.Quotient H (Vertex G) := by
  refine Equiv.ofBijective (fun d => Quotient.mk'' (d : Vertex G)) ⟨?_, ?_⟩
  · intro d d' hdd'
    exact Subtype.ext (hD.eq_of_mem_orbit _ d.2 _ d'.2 (Quotient.exact' hdd'))
  · intro x
    induction x using Quotient.inductionOn' with
    | h v =>
      obtain ⟨d, hd, hdorb⟩ := hD.exists_mem_orbit v
      exact ⟨⟨d, hd⟩, Quotient.sound' hdorb⟩

include hD in
theorem nat_card_transversal :
    Nat.card D = Nat.card (MulAction.orbitRel.Quotient H (Vertex G)) :=
  Nat.card_congr (transversalEquivOrbits hD)

include hD in

theorem connected_induce_transversal : ((graph G).induce D).Connected := by
  obtain ⟨d₀, hd₀, -⟩ := hD.exists_mem_orbit (Vertex.mk 0 1)
  haveI : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  refine (connected_iff _).mpr ⟨?_, inferInstance⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩
  obtain ⟨p, hp⟩ := hD.walkConnected v hv w hw
  exact ⟨p.induce D hp⟩

theorem isAcyclic_induce_transversal : ((graph G).induce D).IsAcyclic := by
  intro v c hc
  exact isAcyclic_two (c.map (SimpleGraph.Embedding.induce D).toHom)
    (hc.map Subtype.val_injective)

noncomputable def treeRepEquivEdgeSet
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    treeRep H hD ≃ ((graph G).induce D).edgeSet := by
  refine Equiv.ofBijective (fun g =>
    ⟨s((⟨Vertex.mk 0 (g : CoprodI G), g.2.1⟩ : D),
       (⟨Vertex.mk 1 (g : CoprodI G), mk_one_mem_of_mem_treeRep hD hfree g.2⟩ : D)),
     adj_mk (by decide : (0 : Fin 2) ≠ 1) (g : CoprodI G)⟩) ⟨?_, ?_⟩
  · intro g g' hgg'
    have hgg'' := congrArg Subtype.val hgg'
    rw [Sym2.eq_iff] at hgg''
    rcases hgg'' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subtype.ext (eq_of_mk_eq_mk (by decide : (0 : Fin 2) ≠ 1)
        (congrArg Subtype.val h1) (congrArg Subtype.val h2))
    · have hcon : (0 : Fin 2) = 1 := congrArg (fun v => (Subtype.val v).1) h1
      exact absurd hcon (by decide)
  · rintro ⟨e, he⟩
    revert he
    induction e using Sym2.ind with
    | _ u w =>
      intro he
      obtain ⟨hne, g, hgu, hgw⟩ := (he : ((graph G).induce D).Adj u w)
      rcases (by decide : ∀ a b : Fin 2, a ≠ b → a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0)
        _ _ hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hgu
        rw [h2] at hgw
        refine ⟨⟨g, mem_treeRep_of_mk_one_mem hD hfree (by rw [hgu]; exact u.2)
          (by rw [hgw]; exact w.2)⟩, ?_⟩
        refine Subtype.ext (Sym2.eq_iff.mpr (Or.inl ⟨?_, ?_⟩))
        · exact Subtype.ext hgu
        · exact Subtype.ext hgw
      · rw [h1] at hgu
        rw [h2] at hgw
        refine ⟨⟨g, mem_treeRep_of_mk_one_mem hD hfree (by rw [hgw]; exact w.2)
          (by rw [hgu]; exact u.2)⟩, ?_⟩
        refine Subtype.ext (Sym2.eq_iff.mpr (Or.inr ⟨?_, ?_⟩))
        · exact Subtype.ext hgw
        · exact Subtype.ext hgu

theorem nat_card_treeRep_add_one [H.FiniteIndex]
    (hfree : ∀ h ∈ H, ∀ v : Vertex G, h • v = v → h = 1) :
    Nat.card (treeRep H hD) + 1 = Nat.card D := by
  classical
  have hfree' := forall_smul_eq_of_forall_mem hfree
  haveI : Finite (MulAction.orbitRel.Quotient H (Vertex G)) :=
    FreeActionTree.finite_vertexOrbits H (conjTrivial_iff_forall_smul_ne.mpr hfree)
  haveI : Finite D := Finite.of_equiv _ (transversalEquivOrbits hD).symm
  haveI : Fintype D := Fintype.ofFinite _
  haveI : Fintype ((graph G).induce D).edgeSet := Set.Finite.fintype (Set.toFinite _)
  have hcount := SimpleGraph.IsTree.card_edgeFinset
    ⟨connected_induce_transversal hD, isAcyclic_induce_transversal⟩
  rw [SimpleGraph.edgeFinset_card] at hcount
  rw [Nat.card_congr (treeRepEquivEdgeSet hD hfree'), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact hcount

theorem nat_card_nonTreeRep [H.FiniteIndex]
    (hfree : ∀ h ∈ H, ∀ v : Vertex G, h • v = v → h = 1) :
    Nat.card (nonTreeRep H hD) =
      1 + H.index - Nat.card (MulAction.orbitRel.Quotient H (Vertex G)) := by
  have hfree' := forall_smul_eq_of_forall_mem hfree
  haveI := finite_baseRep hD hfree'
  have hsub : nonTreeRep H hD ⊆ baseRep H hD := fun g hg => hg.1
  have hdiff : baseRep H hD \ nonTreeRep H hD = treeRep H hD := by
    ext g
    simp only [Set.mem_diff, baseRep, nonTreeRep, treeRep, Set.mem_setOf_eq, not_and, not_not]
    exact ⟨fun ⟨hg, hg'⟩ => ⟨hg, hg' hg⟩, fun ⟨hg, hg'⟩ => ⟨hg, fun _ => hg'⟩⟩
  have hpart := Set.ncard_diff_add_ncard_of_subset hsub (Set.toFinite _)
  rw [hdiff] at hpart
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hpart
  have htree := nat_card_treeRep_add_one hD hfree
  have hbase := nat_card_baseRep hD hfree'
  have hvert := nat_card_transversal hD
  omega

theorem finite_nonTreeRep [H.FiniteIndex]
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    Finite (nonTreeRep H hD) :=
  haveI := finite_baseRep hD hfree
  Finite.Set.subset (baseRep H hD) (fun _ hg => hg.1)

end BassSerre

end GroupTheory

namespace GroupTheory

namespace FreeActionTree

open BassSerre

theorem freeActionRankFormula (G : Fin 2 → Type*) [∀ i, Group (G i)] :
    FreeActionRankFormula G := by
  intro H hFI hfree
  haveI := hFI
  obtain ⟨D, -, hD⟩ := exists_transversal H (Vertex.mk 0 1)
  have hfree' := forall_smul_eq_of_forall_mem hfree
  haveI := finite_nonTreeRep hD hfree'
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (nonTreeRep H hD)
  have hn : n = 1 + H.index - Nat.card (MulAction.orbitRel.Quotient H (Vertex G)) := by
    rw [← Nat.card_eq_of_equiv_fin e, nat_card_nonTreeRep hD hfree]
  exact ⟨(freeGroupBasis hD hfree').reindex (e.trans (finCongr hn))⟩

end FreeActionTree

namespace Kurosh

theorem kuroshRankFormula (G : Fin 2 → Type*) [∀ i, Group (G i)] [∀ i, Finite (G i)] :
    KuroshRankFormula G :=
  FreeActionTree.kuroshRankFormula_of_freeActionRankFormula
    (FreeActionTree.freeActionRankFormula G)

end Kurosh

end GroupTheory

namespace Monoid

/-- The coset graph of a free product of two groups is a tree. -/
public theorem CoprodI.isTree_cosetGraph {G : Fin 2 → Type*} [∀ i, Group (G i)] :
    (SimpleGraph.fromRel fun v w : (i : Fin 2) ×
        (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range) =>
        v.1 ≠ w.1 ∧ ∃ g : Monoid.CoprodI G,
          v.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸
            (Monoid.CoprodI.of (M := G) (i := v.1)).range) ∧
          w.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸
            (Monoid.CoprodI.of (M := G) (i := w.1)).range)).IsTree := by
  rw [GroupTheory.BassSerre.fromRel_eq_graph]
  exact GroupTheory.BassSerre.isTree_two

/-- **Kurosh rank formula.** If `H` has finite index in a free product of two
finite groups and meets every conjugate of each factor trivially, then `H` is
free of rank `1 + [G:H] - [G:H]/|G₀| - [G:H]/|G₁|`. -/
public theorem CoprodI.nonempty_freeGroupBasis_fin_kuroshRank
    {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ (i : Fin 2) (g : Monoid.CoprodI G) (x : G i),
      g⁻¹ * Monoid.CoprodI.of x * g ∈ H → x = 1) :
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index - H.index / Nat.card (G 0) - H.index / Nat.card (G 1))) H) := by

  have hCT : ∀ i, GroupTheory.Kurosh.ConjTrivial (Monoid.CoprodI.of (M := G) (i := i)).range H := by
    rintro i g x ⟨a, rfl⟩ h
    rw [hH i g a h, map_one]
  exact GroupTheory.Kurosh.kuroshRankFormula G H inferInstance hCT

end Monoid

