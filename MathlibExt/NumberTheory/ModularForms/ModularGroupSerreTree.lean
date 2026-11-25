/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularGroup_exists_apply_eq_sub_of_apply_neg_eq.lean`
and
`P2M/Sol/S_ModularGroup_exists_apply_eq_sub_of_apply_neg_eq.lean`
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

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import MathlibExt.GroupTheory.KuroshRank
import MathlibExt.NumberTheory.ModularForms.ModularGroupFreeProduct

/-!
# Even functions on the modular group as differences

Every function `c` on `SL(2, ℤ)` with `c (-g) = c g` is a difference `b - a` of a function `a`
invariant under left multiplication by `S` and a function `b` invariant under left
multiplication by `S * T`. The proof uses that the coset graph of the free product
`ℤ/2 ∗ ℤ/3` (the Serre tree) is a tree.
-/

namespace ModularCurve
namespace CupPairing
namespace SerreTree

section Graph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A : Type*} [AddCommGroup A]

private def wsum (κ : V → V → A) : ∀ {v w : V}, G.Walk v w → A
  | _, _, Walk.nil => 0
  | v, _, Walk.cons (v := w') _ p => κ v w' + wsum κ p

private theorem wsum_nil (κ : V → V → A) (v : V) : wsum κ (Walk.nil : G.Walk v v) = 0 := rfl

private theorem wsum_cons (κ : V → V → A) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    wsum κ (Walk.cons h p) = κ u v + wsum κ p := rfl

private theorem wsum_append (κ : V → V → A) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    wsum κ (p.append q) = wsum κ p + wsum κ q := by
  induction p with
  | nil => simp [wsum]
  | cons h p ih => rw [Walk.cons_append, wsum_cons, wsum_cons, ih, add_assoc]

private theorem wsum_concat (κ : V → V → A) {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    wsum κ (p.concat h) = wsum κ p + κ v w := by
  rw [Walk.concat_eq_append, wsum_append, wsum_cons, wsum_nil, add_zero]

private noncomputable def treePath (hG : G.IsTree) (v w : V) : G.Walk v w :=
  Classical.choose (hG.existsUnique_path v w).exists

private theorem treePath_isPath (hG : G.IsTree) (v w : V) : (treePath hG v w).IsPath :=
  Classical.choose_spec (hG.existsUnique_path v w).exists

private theorem eq_treePath (hG : G.IsTree) {v w : V} (p : G.Walk v w) (hp : p.IsPath) :
    p = treePath hG v w :=
  (hG.existsUnique_path v w).unique hp (treePath_isPath hG v w)

private theorem exists_potential (hG : G.IsTree) (κ : V → V → A)
    (hκ : ∀ v w, G.Adj v w → κ v w = -κ w v) :
    ∃ P : V → A, ∀ v w, G.Adj v w → P w - P v = κ v w := by
  classical
  obtain ⟨v₀⟩ := hG.connected.nonempty
  refine ⟨fun u => wsum κ (treePath hG v₀ u), fun v w hvw => ?_⟩
  simp only
  by_cases hw : w ∈ (treePath hG v₀ v).support
  · set p := treePath hG v₀ v with hp
    have hpath : p.IsPath := treePath_isPath hG v₀ v
    have hsplit : (p.takeUntil w hw).append (p.dropUntil w hw) = p := Walk.take_spec p hw
    have h1 : p.takeUntil w hw = treePath hG v₀ w := eq_treePath hG _ (hpath.takeUntil hw)
    have h2 : p.dropUntil w hw = Walk.cons hvw.symm Walk.nil := by
      have hq : (Walk.cons hvw.symm Walk.nil : G.Walk w v).IsPath := by
        rw [Walk.cons_isPath_iff]
        exact ⟨Walk.IsPath.nil, by simpa using hvw.ne.symm⟩
      rw [eq_treePath hG _ (hpath.dropUntil hw), eq_treePath hG _ hq]
    have : wsum κ p = wsum κ (treePath hG v₀ w) + κ w v := by
      conv_lhs => rw [← hsplit, wsum_append, h1, h2, wsum_cons, wsum_nil, add_zero]
    rw [this, hκ w v hvw.symm]
    abel
  · have hq : ((treePath hG v₀ v).concat hvw).IsPath := (treePath_isPath hG v₀ v).concat hw hvw
    rw [← eq_treePath hG _ hq, wsum_concat]
    abel

end Graph

section Coprod

open Monoid

private abbrev Cx : Fin 2 → Type := fun i => Multiplicative (ZMod (i.val + 2))

private abbrev P23 : Type := CoprodI Cx

private abbrev Rg (i : Fin 2) : Subgroup P23 := (CoprodI.of (M := Cx) (i := i)).range

private abbrev Vx : Type := (i : Fin 2) × (P23 ⧸ Rg i)

private def rel (v w : Vx) : Prop :=
  v.1 ≠ w.1 ∧ ∃ g : P23, v.2 = (QuotientGroup.mk g : P23 ⧸ Rg v.1) ∧ w.2 = (QuotientGroup.mk g :
      P23 ⧸ Rg w.1)

private def graph : SimpleGraph Vx := SimpleGraph.fromRel rel

private theorem graph_isTree : graph.IsTree := Monoid.CoprodI.isTree_cosetGraph (G := Cx)

private theorem eq_one_of_of_eq_of (x : Cx 0) (y : Cx 1)
    (h : (CoprodI.of x : P23) = CoprodI.of y) : x = 1 := by
  by_contra hx
  have hw : (CoprodI.of x : P23) • (CoprodI.Word.empty : CoprodI.Word Cx) =
      (CoprodI.of y : P23) • CoprodI.Word.empty := by rw [h]
  have hmem : (⟨0, x⟩ : Σ i, Cx i) ∈ ((CoprodI.of x : P23) • (CoprodI.Word.empty : CoprodI.Word
      Cx)).toList := by
    have hfst : (CoprodI.Word.empty : CoprodI.Word Cx).fstIdx ≠ some (0 : Fin 2) := by
      simp [CoprodI.Word.fstIdx, CoprodI.Word.empty]
    rw [← CoprodI.Word.cons_eq_smul (h1 := hfst) (h2 := hx)]
    simp
  rw [hw, CoprodI.Word.mem_smul_iff_of_ne (show (0 : Fin 2) ≠ 1 by simp)] at hmem
  simp [CoprodI.Word.empty] at hmem

private theorem eq_of_mk_eq_mk {g g' : P23}
    (h0 : (QuotientGroup.mk g : P23 ⧸ Rg 0) = QuotientGroup.mk g')
    (h1 : (QuotientGroup.mk g : P23 ⧸ Rg 1) = QuotientGroup.mk g') : g = g' := by
  rw [QuotientGroup.eq] at h0 h1
  obtain ⟨x, hx⟩ := h0
  obtain ⟨y, hy⟩ := h1
  have hxy : (CoprodI.of x : P23) = CoprodI.of y := by rw [hx, hy]
  have hx1 : x = 1 := eq_one_of_of_eq_of x y hxy
  rw [hx1, map_one] at hx
  exact inv_mul_eq_one.mp hx.symm

variable {A : Type*} [AddCommGroup A]

private noncomputable def dart (c' : P23 → A) : Vx → Vx → A
  | ⟨0, q⟩, ⟨1, q'⟩ => by
      classical
      exact if h : ∃ g : P23, q = QuotientGroup.mk g ∧ q' = QuotientGroup.mk g then c' h.choose
          else 0
  | ⟨1, q'⟩, ⟨0, q⟩ => by
      classical
      exact if h : ∃ g : P23, q = QuotientGroup.mk g ∧ q' = QuotientGroup.mk g then -c' h.choose
          else 0
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 0

private theorem dart_antisymm (c' : P23 → A) (v w : Vx) : dart c' v w = -dart c' w v := by
  obtain ⟨i, q⟩ := v
  obtain ⟨j, q'⟩ := w
  fin_cases i <;> fin_cases j <;> simp [dart] <;> split_ifs <;> simp

private theorem dart_mk (c' : P23 → A) (g : P23) :
    dart c' ⟨0, QuotientGroup.mk g⟩ ⟨1, QuotientGroup.mk g⟩ = c' g := by
  classical
  have h : ∃ g' : P23, (QuotientGroup.mk g : P23 ⧸ Rg 0) = QuotientGroup.mk g' ∧
      (QuotientGroup.mk g : P23 ⧸ Rg 1) = QuotientGroup.mk g' := ⟨g, rfl, rfl⟩
  simp only [dart, dite_eq_left h]
  congr 1
  exact (eq_of_mk_eq_mk h.choose_spec.1 h.choose_spec.2).symm

private theorem graph_adj_mk (g : P23) :
    graph.Adj (⟨0, QuotientGroup.mk g⟩ : Vx) ⟨1, QuotientGroup.mk g⟩ := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => absurd (congrArg Sigma.fst h) (show (0 : Fin 2) ≠ 1 by simp),
    Or.inl ⟨show (0 : Fin 2) ≠ 1 by simp, g, rfl, rfl⟩⟩

private theorem exists_eq_sub_coprod (c' : P23 → A) :
    ∃ a' b' : P23 → A, (∀ p (x : Cx 0), a' (p * CoprodI.of x) = a' p) ∧
      (∀ p (y : Cx 1), b' (p * CoprodI.of y) = b' p) ∧ ∀ p, c' p = b' p - a' p := by
  obtain ⟨P, hP⟩ := exists_potential graph_isTree (dart c') (fun v w _ => dart_antisymm c' v w)
  refine ⟨fun p => P ⟨0, QuotientGroup.mk p⟩, fun p => P ⟨1, QuotientGroup.mk p⟩, ?_, ?_, ?_⟩
  · intro p x
    simp only
    congr 2
    rw [QuotientGroup.eq]
    simp
  · intro p y
    simp only
    congr 2
    rw [QuotientGroup.eq]
    simp
  · intro p
    have := hP _ _ (graph_adj_mk p)
    rw [dart_mk] at this
    exact this.symm

end Coprod

section SL2

open scoped MatrixGroups

open Matrix.SpecialLinearGroup ModularGroup

private theorem eq_one_or_eq_neg_one_of_mem_center {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2,
    ℤ)) :
    z = 1 ∨ z = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨r, hr, hrz⟩ := hz
  simp only [Fintype.card_fin] at hr
  rcases sq_eq_one_iff.mp hr with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hrz]
    simp
  · right
    apply Subtype.ext
    rw [← hrz]
    simp

variable {A : Type*} [AddCommGroup A]

private noncomputable def bar (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) :
    SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ) → A :=
  Quotient.lift c (by
    intro g g' hgg'
    have hgg : g⁻¹ * g' ∈ Subgroup.center SL(2, ℤ) := QuotientGroup.leftRel_apply.mp hgg'
    rcases eq_one_or_eq_neg_one_of_mem_center hgg with h | h
    · rw [inv_mul_eq_one] at h; rw [h]
    · have : g' = -g := by
        have := congrArg (g * ·) h
        simpa using this
      rw [this, hc])

omit [AddCommGroup A] in
private theorem bar_mk (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) (g : SL(2, ℤ)) :
    bar c hc (QuotientGroup.mk g) = c g := rfl

private theorem main' (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) :
    ∃ a b : SL(2, ℤ) → A, (∀ g, a (S * g) = a g) ∧ (∀ g, b (S * T * g) = b g) ∧
      ∀ g, c g = b g - a g := by
  obtain ⟨e, he0, he1⟩ := ModularGroup.exists_mulEquiv_freeProduct_quotient_center
  set c' : P23 → A := fun p => bar c hc (e p⁻¹) with hc'
  obtain ⟨a', b', ha', hb', hab⟩ := exists_eq_sub_coprod c'
  refine ⟨fun g => a' (e.symm (QuotientGroup.mk g))⁻¹, fun g => b' (e.symm (QuotientGroup.mk g))⁻¹,
    ?_, ?_, ?_⟩
  · intro g
    simp only
    rw [QuotientGroup.mk_mul, ← he0, map_mul, e.symm_apply_apply, mul_inv_rev, ← map_inv]
    exact ha' _ _
  · intro g
    simp only
    rw [QuotientGroup.mk_mul, ← he1, map_mul, e.symm_apply_apply, mul_inv_rev, ← map_inv]
    exact hb' _ _
  · intro g
    have := hab (e.symm (QuotientGroup.mk g))⁻¹
    simp only [hc', inv_inv, MulEquiv.apply_symm_apply, bar_mk] at this
    exact this

end SL2

end ModularCurve.CupPairing.SerreTree

open scoped MatrixGroups in
/-- An even function on `SL(2, ℤ)` is the difference of a function invariant under left
multiplication by `S * T` and one invariant under left multiplication by `S`. -/
public theorem ModularGroup.exists_apply_eq_sub_of_apply_neg_eq {A : Type*} [AddCommGroup A]
    (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) :
    ∃ a b : SL(2, ℤ) → A, (∀ g, a (ModularGroup.S * g) = a g) ∧
      (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧ ∀ g, c g = b g - a g :=
  ModularCurve.CupPairing.SerreTree.main' c hc
