/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/ExC4/README.md`
(leansolving/SqueezeBench, commit e2e19eef093a77882da57f348def029533ec2d5e):
the statement of the extremal number at projective-plane orders.
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modification notice: the value reported in the README is stated and proved using
Mathlib's extremal-number function. SqueezeBench ships no `NOTICE` file.
-/

module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.CastCard
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Füredi's theorem on four-cycle-free graphs

For a prime power `q > 13`, `extremalNumber_cycleGraph_four_projectivePlane_order`
gives the exact extremal number on `q ^ 2 + q + 1` vertices. A finite-field model of
the orthogonal polarity graph attains the bound. For the upper bound, we count
two-edge paths to bound the degrees and then study pairs with no common neighbor
in a graph maximizing the edge count and, subject to that, the sum of squared degrees.

The polarity construction is described in Construction 3.7 of the [survey of
Füredi and Simonovits](https://arxiv.org/abs/1306.5167).
-/

namespace MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted

-- The point types correspond to the representatives (a, b, 1), (b, 1, 0)
-- and (1, 0, 0). The relation retains the absolute points until loops are removed.
section Polarity

open _root_.SimpleGraph Finset

private abbrev Point (K : Type*) := (K × K) ⊕ Option K

variable {K : Type*} [Field K]

private def pole : Point K → Point K → Prop
  | .inl (a, b), .inl (c, d) => a + c = b * d
  | .inl (_, b), .inr (some d) => b = d
  | .inr (some b), .inl (_, d) => b = d
  | .inr (some _), .inr (some _) => False
  | .inr none, .inl _ | .inl _, .inr none => False
  | .inr none, .inr _ | .inr _, .inr none => True

private theorem pole_symm : Std.Symm (pole (K := K)) := by
  constructor
  rintro (⟨a, b⟩ | (_ | b)) (⟨c, d⟩ | (_ | d)) h
  all_goals simp only [pole] at h ⊢
  all_goals simpa [add_comm, mul_comm, eq_comm] using h

private def graph (K : Type*) [Field K] : SimpleGraph (Point K) where
  Adj x y := x ≠ y ∧ pole x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, pole_symm.symm _ _ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem pole_common_unique {x y u v : Point K} (hxy : x ≠ y)
    (hxu : pole x u) (hyu : pole y u) (hxv : pole x v) (hyv : pole y v) : u = v := by
  rcases x with ⟨a, b⟩ | (_ | b) <;> rcases y with ⟨c, d⟩ | (_ | d) <;>
    rcases u with ⟨e, f⟩ | (_ | f) <;> rcases v with ⟨g, h⟩ | (_ | h) <;>
    simp only [pole, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Option.some.injEq] at *
  all_goals try contradiction
  all_goals grind

private theorem graph_free : (cycleGraph 4).Free (graph K) := by
  rintro ⟨f⟩
  have edge (i j : Fin 4) (h : (cycleGraph 4).Adj i j) : pole (f i) (f j) :=
    (show (graph K).Adj (f i) (f j) from f.toHom.map_adj h).2
  exact f.injective.ne (by decide : (1 : Fin 4) ≠ 3) <|
    pole_common_unique (f.injective.ne (by decide : (0 : Fin 4) ≠ 2))
      (edge 0 1 (by decide)) (edge 2 1 (by decide))
      (edge 0 3 (by decide)) (edge 2 3 (by decide))

private def row (x : Point K) : Option K → Point K :=
  match x with
  | .inl (a, b) => fun t => t.elim (.inr (some b)) (fun u => .inl (b * u - a, u))
  | .inr (some b) => fun t => t.elim (.inr none) (fun u => .inl (u, b))
  | .inr none => fun t => .inr t

private theorem row_injective (x : Point K) : Function.Injective (row x) := by
  rintro (a | a) (b | b) h <;> rcases x with ⟨x, y⟩ | (_ | x) <;> simp [row] at h ⊢
  all_goals grind

private theorem row_exists (x y : Point K) : (∃ t, row x t = y) ↔ pole x y := by
  rcases x with ⟨a, b⟩ | (_ | b) <;> rcases y with ⟨c, d⟩ | (_ | d) <;>
    simp only [row, pole]
  all_goals constructor
  all_goals try (rintro ⟨(_ | t), h⟩ <;> simp_all)
  · rcases h with ⟨rfl, rfl⟩
    abel
  all_goals intro h
  case inl.inl.mpr =>
    refine ⟨some d, ?_⟩
    simp only [Option.elim_some, Sum.inl.injEq, Prod.mk.injEq, and_true]
    exact sub_eq_iff_eq_add.mpr ((add_comm _ _).trans h).symm
  case inr.some.inl.mpr =>
    exact ⟨some c, by simp [h]⟩
  all_goals exact ⟨none, by simp [h]⟩

variable [Fintype K]

private theorem row_card (x : Point K) :
    Nat.card {y // pole x y} = Fintype.card K + 1 := by
  classical
  let e : Option K → {y // pole x y} := fun t =>
    ⟨row x t, (row_exists x _).mp ⟨t, rfl⟩⟩
  have he : Function.Bijective e :=
    ⟨fun _ _ h => row_injective x (congrArg Subtype.val h), fun y => by
      obtain ⟨t, ht⟩ := (row_exists x y.val).mpr y.prop
      exact ⟨t, Subtype.ext ht⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_eq_fintype_card, Fintype.card_option]

private theorem loops_card : Nat.card {x : Point K // pole x x} = Fintype.card K + 1 := by
  classical
  by_cases h2 : (2 : K) = 0
  · let e : Option K → {x : Point K // pole x x} := fun t =>
      match t with
      | none => ⟨.inr none, trivial⟩
      | some a => ⟨.inl (a, 0), by simp [pole, ← two_mul, h2]⟩
    have he : Function.Bijective e := by
      constructor
      · rintro (_ | a) (_ | b) h
        all_goals have hv := congrArg Subtype.val h
        all_goals simp only [e, Sum.inl.injEq, Prod.mk.injEq, Option.some.injEq,
          reduceCtorEq, and_true] at hv ⊢
        exact hv
      · rintro ⟨⟨a, b⟩ | (_ | a), h⟩
        · have hb : b = 0 := by simpa [pole, ← two_mul, h2, eq_comm] using h
          exact ⟨some a, Subtype.ext (by simp [e, hb])⟩
        · exact ⟨none, rfl⟩
        · exact h.elim
    rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_eq_fintype_card, Fintype.card_option]
  · let e : Option K → {x : Point K // pole x x} := fun t =>
      match t with
      | none => ⟨.inr none, trivial⟩
      | some b => ⟨.inl (b * b / 2, b), by
          simp only [pole, ← two_mul]
          rw [mul_div_cancel₀ _ h2]⟩
    have he : Function.Bijective e := by
      constructor
      · rintro (_ | a) (_ | b) h
        all_goals have hv := congrArg Subtype.val h
        all_goals simp only [e, Sum.inl.injEq, Prod.mk.injEq,
          Option.some.injEq, reduceCtorEq] at hv ⊢
        exact hv.2
      · rintro ⟨⟨a, b⟩ | (_ | a), h⟩
        · have ha : b * b / 2 = a := by
            apply (div_eq_iff h2).2
            simpa [pole, ← two_mul, mul_comm, eq_comm] using h
          exact ⟨some b, Subtype.ext (by simp [e, ha])⟩
        · exact ⟨none, rfl⟩
        · exact h.elim
    rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_eq_fintype_card, Fintype.card_option]

open scoped Classical in
private theorem degree_add_loop (x : Point K) [DecidableRel (graph K).Adj] :
    (graph K).degree x + (if pole x x then 1 else 0) = Fintype.card K + 1 := by
  classical
  have hrow := row_card x
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hrow
  have hN : (graph K).neighborFinset x =
      (univ.filter (pole x)).erase x := by
    ext y
    rw [mem_neighborFinset]
    simp [graph, ne_comm]
  rw [← card_neighborFinset_eq_degree, hN, ← hrow]
  by_cases hx : pole x x
  · simpa [hx] using card_erase_add_one (s := univ.filter (pole x)) (a := x) (by simp [hx])
  · simp [hx]

private theorem graph_edges [DecidableRel (graph K).Adj] :
    2 * (graph K).edgeFinset.card = Fintype.card K * (Fintype.card K + 1) ^ 2 := by
  classical
  let q := Fintype.card K
  have hc : Fintype.card (Point K) = q ^ 2 + q + 1 := by
    simp [Point, q, pow_two, add_assoc]
  have hsum := sum_congr (s₁ := (univ : Finset (Point K))) rfl
    (fun x _ => degree_add_loop x)
  rw [sum_add_distrib, (graph K).sum_degrees_eq_twice_card_edges,
    sum_const, card_univ, hc, smul_eq_mul] at hsum
  have hloop := loops_card (K := K)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hloop
  rw [← sum_filter, sum_const, smul_eq_mul, mul_one, hloop] at hsum
  change 2 * _ + (q + 1) = (q ^ 2 + q + 1) * (q + 1) at hsum
  change 2 * _ = q * (q + 1) ^ 2
  have hpoly : (q ^ 2 + q + 1) * (q + 1) = q * (q + 1) ^ 2 + (q + 1) := by ring
  omega

private theorem sharp_lower (q : ℕ) (hq : IsPrimePow q) :
    q * (q + 1) ^ 2 / 2 ≤ extremalNumber (q ^ 2 + q + 1) (cycleGraph 4) := by
  classical
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p k
  let : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = p ^ k := (Nat.card_eq_fintype_card).symm.trans
    (GaloisField.card p k hk.ne')
  have hn : Fintype.card (Point K) = (p ^ k) ^ 2 + p ^ k + 1 := by
    simp [Point, hK, pow_two, add_assoc]
  have hm := graph_edges (K := K)
  rw [hK] at hm
  have hle := card_edgeFinset_le_extremalNumber (graph_free (K := K))
  rw [hn] at hle
  omega

end Polarity

-- Two-edge-path counts constrain the degrees of a graph exceeding the proposed bound.
section DegreeBounds

open _root_.SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

private theorem common_neighbor_unique (hG : (cycleGraph 4).Free G) {u v a b : V}
    (huv : u ≠ v) (hua : G.Adj u a) (hva : G.Adj v a)
    (hub : G.Adj u b) (hvb : G.Adj v b) : a = b := by
  by_contra hab
  classical
  let f : Fin 4 → V := ![u, a, v, b]
  have ha := hua.ne
  have hb := hva.ne
  have hc := hub.ne
  have hd := hvb.ne
  apply hG
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    have hua' := hua.symm
    have hva' := hva.symm
    have hub' := hub.symm
    have hvb' := hvb.symm
    fin_cases i <;> fin_cases j
    all_goals try (exfalso; revert hij; decide)
    all_goals simp only [f]
    all_goals assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
private theorem mem_neighborFinset_iff {x y : V} :
    y ∈ G.neighborFinset x ↔ G.Adj x y := G.mem_neighborFinset x y

private theorem card_inter_le_one (hG : (cycleGraph 4).Free G) {u v : V}
    (huv : u ≠ v) : (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  simp only [mem_inter, mem_neighborFinset] at ha hb
  exact common_neighbor_unique hG huv ha.1 ha.2 hb.1 hb.2

omit [Fintype V] [DecidableEq V] in
private theorem offDiag_int_card (s : Finset V) :
    (s.offDiag.card : ℤ) = s.card * ((s.card : ℤ) - 1) := by
  rw [offDiag_card, Nat.cast_sub, Nat.cast_mul] <;> nlinarith

private theorem paths_count (hG : (cycleGraph 4).Free G) (U A : Finset V) :
    ∑ v ∈ U, ((G.neighborFinset v ∩ A).card : ℤ) *
      (((G.neighborFinset v ∩ A).card : ℤ) - 1) ≤ A.card * ((A.card : ℤ) - 1) := by
  simp_rw [← offDiag_int_card, ← Nat.cast_sum, ← card_sigma]
  have hc : (U.sigma fun v => (G.neighborFinset v ∩ A).offDiag).card ≤ A.offDiag.card := by
    apply card_le_card_of_injOn (fun x : Σ _ : V, V × V => x.2)
    · rintro ⟨v, a, b⟩ h
      simp only [mem_coe, mem_sigma, mem_offDiag, mem_inter] at h ⊢
      exact ⟨h.2.1.2, h.2.2.1.2, h.2.2.2⟩
    · rintro ⟨v, a, b⟩ hv ⟨w, c, d⟩ hw he
      cases he
      simp only [mem_coe, mem_sigma, mem_offDiag, mem_inter, mem_neighborFinset] at hv hw
      have hvw := common_neighbor_unique hG hv.2.2.2 hv.2.1.1.symm hv.2.2.1.1.symm
        hw.2.1.1.symm hw.2.2.1.1.symm
      simp [hvw]
  exact_mod_cast hc

omit [Fintype V] [DecidableEq V] in
private theorem tangent (U : Finset V) (d : V → ℤ) (k : ℤ) :
    (2*k - 2) * (∑ v ∈ U, d v) - (U.card : ℤ) * (k * (k - 1)) ≤
      ∑ v ∈ U, d v * (d v - 1) := by
  have h := sum_le_sum (s := U)
    (f := fun v => (2*k - 2) * d v - k * (k - 1))
    (g := fun v => d v * (d v - 1))
    (fun v _ => by
      by_cases h : d v < k
      · have hp := mul_nonneg (show k - d v ≥ 0 by omega) (show k - 1 - d v ≥ 0 by omega)
        nlinarith
      · have hp := mul_nonneg (show d v - k ≥ 0 by omega) (show d v - k + 1 ≥ 0 by omega)
        nlinarith)
  simpa [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul] using h

private theorem paths_outside (hG : (cycleGraph 4).Free G) (U C : Finset V) :
    ∑ v ∈ U, ((G.neighborFinset v \ C).card : ℤ) *
      (((G.neighborFinset v \ C).card : ℤ) - 1) ≤
        (Fintype.card V - (C.card : ℤ)) * (Fintype.card V - (C.card : ℤ) - 1) := by
  have hc (v : V) : G.neighborFinset v ∩ (univ \ C) = G.neighborFinset v \ C := by
    ext w
    simp [and_comm]
  simpa only [hc, cast_card_sdiff (subset_univ C), card_univ] using
    paths_count hG U (univ \ C)

private theorem degree_sub_outside (C : Finset V) (x : V) :
    ((G.neighborFinset x \ C).card : ℤ) =
      G.degree x - ((G.neighborFinset x ∩ C).card : ℤ) := by
  have h := congrArg (fun t : ℕ => (t : ℤ)) (card_sdiff_add_card_inter (G.neighborFinset x) C)
  simp only [Nat.cast_add, card_neighborFinset_eq_degree] at h
  omega

omit [DecidableEq V] in
private theorem degrees_int :
    (∑ v : V, (G.degree v : ℤ)) = 2 * (G.edgeFinset.card : ℤ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

private theorem sum_degree_erase (v : V) :
    (∑ x ∈ (univ.erase v), (G.degree x : ℤ)) =
      2 * (G.edgeFinset.card : ℤ) - G.degree v := by
  have h := sum_erase_add (univ : Finset V) (fun x => (G.degree x : ℤ)) (mem_univ v)
  rw [degrees_int] at h
  omega

omit [DecidableEq V] in
private theorem maxDegree_le (q : ℕ) (hq : 13 < q)
    (hn : Fintype.card V = q ^ 2 + q + 1) (hG : (cycleGraph 4).Free G)
    (hE : (q : ℤ) * (q + 1) ^ 2 + 2 ≤ 2 * (G.edgeFinset.card : ℤ)) (v : V) :
    G.degree v ≤ q + 2 := by
  classical
  by_contra! hv
  let C := G.neighborFinset v
  let U := (univ : Finset V).erase v
  let d (x : V) : ℤ := (G.neighborFinset x \ C).card
  have hC : (C.card : ℤ) = G.degree v := rfl
  have hU : (U.card : ℤ) = (q : ℤ)^2 + q := by
    have hh := card_erase_add_one (mem_univ v)
    rw [card_univ, hn] at hh
    have hh' := congrArg (fun t : ℕ => (t : ℤ)) hh
    push_cast at hh'
    linarith
  have hd : (∑ x ∈ U, ((G.degree x : ℤ) - 1)) ≤ ∑ x ∈ U, d x := by
    apply sum_le_sum
    intro x hx
    have hxv : x ≠ v := (mem_erase.mp hx).1
    have hi := card_inter_le_one hG hxv
    dsimp [d, C]
    rw [degree_sub_outside]
    omega
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one,
    show U = univ.erase v from rfl, sum_degree_erase, ← show U = univ.erase v from rfl, hU] at hd
  have ht := tangent U d q
  change _ ≤ ∑ x ∈ U, d x * (d x - 1) at ht
  have hp := paths_outside hG U C
  change ∑ x ∈ U, d x * (d x - 1) ≤ _ at hp
  have htn := ht.trans hp
  rw [hU, hC, hn] at htn
  push_cast at htn
  have hq' : 14 ≤ (q : ℤ) := by exact_mod_cast hq
  have hqd : (q : ℤ) + 3 ≤ G.degree v := by
    have : q + 3 ≤ G.degree v := hv
    exact_mod_cast this
  have hqhi : (G.degree v : ℤ) ≤ q ^ 2 + q := by
    have := G.degree_lt_card_verts v
    rw [hn] at this
    exact_mod_cast Nat.lt_succ_iff.mp this
  have hsum : (q : ℤ)^2 * q + (q : ℤ)^2 + 2 - G.degree v ≤ ∑ x ∈ U, d x := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (2 * (q : ℤ) - 2) by omega)
  have h1 := mul_nonneg (sub_nonneg.mpr hqd) (sub_nonneg.mpr hqhi)
  have h2 := mul_nonneg
    (mul_nonneg (show 0 ≤ (q : ℤ) by omega) (show 0 ≤ (q : ℤ) - 2 by omega))
    (sub_nonneg.mpr hqd)
  nlinarith

omit [DecidableEq V] in
private theorem minDegree_ge_three (q : ℕ) (hq : 13 < q)
    (hn : Fintype.card V = q ^ 2 + q + 1) (hG : (cycleGraph 4).Free G)
    (hE : (q : ℤ) * (q + 1) ^ 2 + 2 ≤ 2 * (G.edgeFinset.card : ℤ)) (v : V) :
    3 ≤ G.degree v := by
  classical
  by_contra! hv
  let C : Finset V := {v}
  let U := (univ : Finset V).erase v
  let d (x : V) : ℤ := (G.neighborFinset x \ C).card
  have hC : (C.card : ℤ) = 1 := by simp [C]
  have hU : (U.card : ℤ) = (q : ℤ)^2 + q := by
    have hh := card_erase_add_one (mem_univ v)
    rw [card_univ, hn] at hh
    have hh' := congrArg (fun t : ℕ => (t : ℤ)) hh
    push_cast at hh'
    linarith
  have hds : (∑ x ∈ U, d x) = 2 * (G.edgeFinset.card : ℤ) - 2 * G.degree v := by
    have he (x : V) : d x = G.degree x - if G.Adj v x then 1 else 0 := by
      dsimp [d]
      rw [degree_sub_outside]
      have hi : G.neighborFinset x ∩ C = C.filter (G.Adj x ·) := by
        ext y
        simp only [C, mem_inter, mem_neighborFinset, mem_singleton, mem_filter]
        exact and_comm
      rw [hi]
      by_cases hx : G.Adj x v <;> simp [C, filter_singleton, hx, G.adj_comm v x]
    simp only [he, sum_sub_distrib]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hf : U.filter (G.Adj v ·) = G.neighborFinset v := by
      ext x
      simp only [U, mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
      exact ⟨And.right, fun h => ⟨h.ne.symm, h⟩⟩
    rw [hf, card_neighborFinset_eq_degree, show U = univ.erase v from rfl, sum_degree_erase]
    ring
  have ht := tangent U d (q + 1)
  have hp := paths_outside hG U C
  change ∑ x ∈ U, d x * (d x - 1) ≤ _ at hp
  have htn := ht.trans hp
  rw [hU, hC, hn, hds] at htn
  push_cast at htn
  have hq' : 14 ≤ (q : ℤ) := by exact_mod_cast hq
  have hv' : (G.degree v : ℤ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hv
  have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ (2 * (q : ℤ)) by positivity)
  have hvm := mul_nonneg (show 0 ≤ (q : ℤ) by positivity) (sub_nonneg.mpr hv')
  nlinarith

omit [DecidableEq V] in
private theorem two_high_neighbors (q : ℕ) (hq : 13 < q)
    (hn : Fintype.card V = q ^ 2 + q + 1) (hG : (cycleGraph 4).Free G)
    (hE : (q : ℤ) * (q + 1) ^ 2 + 2 ≤ 2 * (G.edgeFinset.card : ℤ)) (v : V) :
    ((G.neighborFinset v).filter fun x => G.degree x = q + 2).card ≤ 2 := by
  classical
  by_contra! he
  obtain ⟨T, ht, htcard⟩ := exists_subset_card_eq (show 3 ≤ _ from he)
  have htN : T ⊆ G.neighborFinset v := fun _ h => (mem_filter.mp (ht h)).1
  have htdeg (x : V) (hx : x ∈ T) : G.degree x = q + 2 := (mem_filter.mp (ht hx)).2
  have hvt : v ∉ T := fun h => G.notMem_neighborFinset_self v (htN h)
  let C := T.biUnion (fun x => G.neighborFinset x)
  let U := (univ : Finset V) \ insert v T
  let d (x : V) : ℤ := (G.neighborFinset x \ C).card
  have hCv : v ∈ C := by
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < T.card)
    exact mem_biUnion.mpr
      ⟨x, hx, mem_neighborFinset_iff.mpr (mem_neighborFinset_iff.mp (htN hx)).symm⟩
  have hC : (C.card : ℤ) = 3 * (q : ℤ) + 4 := by
    have hdis : (T : Set V).PairwiseDisjoint (fun x => (G.neighborFinset x).erase v) := by
      intro x hx y hy hxy
      apply Finset.disjoint_left.mpr
      intro z hzx hzy
      obtain ⟨hzv, hzx'⟩ := mem_erase.mp hzx
      have hw := common_neighbor_unique hG hxy (mem_neighborFinset_iff.mp hzx')
        (mem_neighborFinset_iff.mp (mem_erase.mp hzy).2)
        (mem_neighborFinset_iff.mp (htN hx)).symm (mem_neighborFinset_iff.mp (htN hy)).symm
      exact hzv hw
    have hCe : C.erase v = T.biUnion (fun x => (G.neighborFinset x).erase v) := by
      ext w
      constructor
      · rintro h
        obtain ⟨hne, h⟩ := mem_erase.mp h
        obtain ⟨x, hx, hw⟩ := mem_biUnion.mp h
        exact mem_biUnion.mpr ⟨x, hx, mem_erase.mpr ⟨hne, hw⟩⟩
      · rintro h
        obtain ⟨x, hx, hw⟩ := mem_biUnion.mp h
        exact mem_erase.mpr ⟨(mem_erase.mp hw).1, mem_biUnion.mpr ⟨x, hx, (mem_erase.mp hw).2⟩⟩
    have h₁ := card_erase_add_one hCv
    rw [hCe, card_biUnion hdis] at h₁
    have h₂ : (∑ x ∈ T, ((G.neighborFinset x).erase v).card) = 3 * (q + 1) := by
      calc
        _ = ∑ _x ∈ T, (q + 1) := sum_congr rfl fun x hx => by
          have hh := card_erase_add_one (mem_neighborFinset_iff.mpr (mem_neighborFinset_iff.mp
            (htN hx)).symm)
          rw [card_neighborFinset_eq_degree, htdeg x hx] at hh
          omega
        _ = _ := by simp [htcard]
    rw [h₂] at h₁
    exact_mod_cast (show C.card = 3 * q + 4 by omega)
  have hU : (U.card : ℤ) = (q : ℤ)^2 + q - 3 := by
    rw [cast_card_sdiff (subset_univ _), card_univ, card_insert_of_notMem hvt, htcard, hn]
    push_cast
    ring
  have hUd : (∑ x ∈ U, (G.degree x : ℤ)) =
      2 * (G.edgeFinset.card : ℤ) - (G.degree v : ℤ) - 3 * (q + 2) := by
    have h := sum_sdiff (s₁ := insert v T) (f := fun x => (G.degree x : ℤ)) (subset_univ _)
    change (∑ x ∈ U, (G.degree x : ℤ)) + _ = _ at h
    rw [sum_insert hvt, degrees_int] at h
    have hsum : (∑ x ∈ T, (G.degree x : ℤ)) = 3 * (q + 2) := by
      calc
        _ = ∑ _x ∈ T, ((q : ℤ) + 2) := sum_congr rfl fun x hx => by exact_mod_cast htdeg x hx
        _ = _ := by simp [htcard]
    rw [hsum] at h
    linarith
  have hNcard : ((U.filter (G.Adj v ·)).card : ℤ) = G.degree v - 3 := by
    have heq : U.filter (G.Adj v ·) = G.neighborFinset v \ T := by
      ext x
      simp only [U, mem_filter, mem_sdiff, mem_univ, true_and, mem_insert, mem_neighborFinset]
      constructor
      · exact fun ⟨h, ha⟩ => ⟨ha, fun ht' => h (Or.inr ht')⟩
      · exact fun ⟨ha, ht'⟩ => ⟨fun h => h.elim ha.ne.symm ht', ha⟩
    rw [heq, cast_card_sdiff htN, card_neighborFinset_eq_degree, htcard]
    norm_num
  have hcap_general (w : V) (hw : w ∉ T) : (G.neighborFinset w ∩ C).card ≤ 3 := by
    have heq : G.neighborFinset w ∩ C =
        T.biUnion (fun x => G.neighborFinset w ∩ G.neighborFinset x) := by
      ext x
      simp only [mem_inter, mem_biUnion, C]
      aesop
    rw [heq]
    calc
      _ ≤ ∑ x ∈ T, (G.neighborFinset w ∩ G.neighborFinset x).card := card_biUnion_le
      _ ≤ ∑ _x ∈ T, 1 := sum_le_sum fun x hx => card_inter_le_one hG (fun he' => hw (he' ▸ hx))
      _ = _ := by simp [htcard]
  have hcap_neighbor (w : V) (hw : w ∉ T) (ha : G.Adj v w) :
      (G.neighborFinset w ∩ C).card ≤ 1 := by
    apply card_le_one.mpr
    have hz (z : V) (hz : z ∈ G.neighborFinset w ∩ C) : z = v := by
      obtain ⟨hz', hz''⟩ := mem_inter.mp hz
      obtain ⟨x, hx, hz'''⟩ := mem_biUnion.mp hz''
      have hne : w ≠ x := fun he' => hw (he'.symm ▸ hx)
      exact common_neighbor_unique hG hne
        (mem_neighborFinset_iff.mp hz') (mem_neighborFinset_iff.mp hz''') ha.symm
        (mem_neighborFinset_iff.mp (htN hx)).symm
    intro a ha b hb
    exact (hz a ha).trans (hz b hb).symm
  have hd_sum : (∑ x ∈ U, (((G.degree x : ℤ) - 3) + if G.Adj v x then 2 else 0)) ≤
      ∑ x ∈ U, d x := by
    apply sum_le_sum
    intro x hx
    have hw : x ∉ T := fun hs => (mem_sdiff.mp hx).2 (mem_insert_of_mem hs)
    dsimp [d]
    rw [degree_sub_outside]
    by_cases ha : G.Adj v x
    · have := hcap_neighbor x hw ha
      simp [ha]
      omega
    · have := hcap_general x hw
      simp [ha]
      omega
  rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, hU, hUd,
    ← sum_filter, sum_const, nsmul_eq_mul, hNcard] at hd_sum
  have hd_v : (G.degree v : ℤ) - 3 ≤ d v := by
    have := hcap_general v hvt
    dsimp [d]
    rw [degree_sub_outside]
    omega
  have hdeg_v : 3 ≤ G.degree v := by
    simpa [htcard, card_neighborFinset_eq_degree] using card_le_card htN
  have hprod : ((G.degree v : ℤ) - 3) * (G.degree v - 4) ≤ d v * (d v - 1) := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hd_v) (show 0 ≤ d v - (G.degree v - 3) by omega)
    have h₂ := mul_nonneg (sub_nonneg.mpr hd_v) (show 0 ≤ 2 * (G.degree v : ℤ) - 6 by omega)
    have h₃ : d v = (G.degree v : ℤ) - 3 ∨ (G.degree v : ℤ) - 3 + 1 ≤ d v := by omega
    rcases h₃ with h₃ | h₃
    · rw [h₃]
      ring_nf
      rfl
    · have h₄ := mul_nonneg (sub_nonneg.mpr hd_v)
        (show 0 ≤ d v + (G.degree v : ℤ) - 4 by omega)
      nlinarith
  have hp := paths_outside hG (insert v U) C
  change (∑ x ∈ insert v U, d x * (d x - 1)) ≤ _ at hp
  have hvU : v ∉ U := fun h => (mem_sdiff.mp h).2 (mem_insert_self v T)
  rw [sum_insert hvU, hC, hn] at hp
  push_cast at hp
  have htangent := tangent U d ((q : ℤ) - 2)
  rw [hU] at htangent
  have hq' : (14 : ℤ) ≤ q := by exact_mod_cast hq
  have hlower : ((q : ℤ)^2 + q - 3) * (q - 2) + G.degree v - 7 ≤ ∑ x ∈ U, d x := by
    nlinarith
  have hlower' := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 2 * ((q : ℤ) - 2) - 2 by omega)
  have h₁ := mul_nonneg (show 0 ≤ (q : ℤ) by omega) (show 0 ≤ (q : ℤ) - 7 by omega)
  have h₂ := mul_nonneg (show 0 ≤ 2 * (q : ℤ) - 13 by omega)
    (show 0 ≤ (G.degree v : ℤ) by omega)
  nlinarith [sq_nonneg (G.degree v : ℤ)]

end DegreeBounds

-- Off the diagonal, the gap matrix records pairs with no common neighbor.
-- Its commutator with the adjacency matrix is determined by the degree deficiencies.
section NeighborhoodDeficiency

open _root_.SimpleGraph Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def deficiency (q : ℕ) (v : V) : ℤ := q + 1 - G.degree v

private def low (q : ℕ) : Finset V := univ.filter fun v => 0 < deficiency G q v

private def uncovered (v : V) : Finset V :=
  (univ.erase v).filter fun w => (G.neighborFinset v ∩ G.neighborFinset w).card = 0

private theorem mem_uncovered {x y : V} :
    y ∈ uncovered G x ↔ x ≠ y ∧ ¬∃ z, G.Adj x z ∧ G.Adj y z := by
  rw [uncovered, mem_filter, mem_erase]
  simp only [mem_univ, and_true, Finset.card_eq_zero ]
  constructor
  · intro ⟨h, he⟩
    refine ⟨h.symm, ?_⟩
    rintro ⟨z, hx, hy⟩
    have hm : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by simpa using And.intro hx hy
    simp [he] at hm
  · intro ⟨h, hn⟩
    refine ⟨h.symm, eq_empty_iff_forall_notMem.mpr ?_⟩
    intro z hz
    simp only [mem_inter, mem_neighborFinset] at hz
    exact hn ⟨z, hz⟩

private theorem mem_uncovered_symm {x y : V} (h : y ∈ uncovered G x) : x ∈ uncovered G y := by
  rw [mem_uncovered] at h ⊢
  exact ⟨h.1.symm, fun ⟨z, hz, hy⟩ => h.2 ⟨z, hy, hz⟩⟩

private def allOnes (V : Type*) (R : Type*) [One R] : Matrix V V R :=
  Matrix.of fun _ _ => 1

private def gap (q : ℕ) : Matrix V V ℤ :=
  (q : ℤ) • (1 : Matrix V V ℤ) + allOnes V ℤ - G.adjMatrix ℤ * G.adjMatrix ℤ

private theorem adj_sq_apply {R : Type*} [NonAssocSemiring R] (v w : V) :
    (G.adjMatrix R * G.adjMatrix R) v w = (G.neighborFinset v ∩ G.neighborFinset w).card := by
  rw [adjMatrix_mul_apply]
  simp_rw [adjMatrix_apply, G.adj_comm _ w, ← mem_neighborFinset]
  rw [← sum_filter, filter_mem_eq_inter]
  simp

private theorem gap_diag (q : ℕ) (v : V) : gap G q v v = deficiency G q v := by
  simp only [gap, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    ite_true, smul_eq_mul, mul_one, allOnes, Matrix.of_apply, adjMatrix_mul_self_apply_self,
    deficiency]

private theorem gap_offdiag (q : ℕ)
    (hc : ∀ {v w}, v ≠ w → (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    {v w : V} (hvw : v ≠ w) :
    gap G q v w = if w ∈ uncovered G v then 1 else 0 := by
  have h1 := hc hvw
  simp only [gap, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    hvw, ite_false, smul_zero, zero_add, allOnes, Matrix.of_apply, adj_sq_apply,
    uncovered, mem_filter, mem_erase, mem_univ, and_true]
  by_cases he : (G.neighborFinset v ∩ G.neighborFinset w).card = 0
  · simp [he, Ne.symm hvw]
  · have hh : (G.neighborFinset v ∩ G.neighborFinset w).card = 1 := by omega
    simp [hh]

private theorem gap_symm (q : ℕ) (v w : V) : gap G q v w = gap G q w v := by
  by_cases he : v = w
  · subst w
    rfl
  · simp only [gap, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      he, Ne.symm he, ite_false, smul_zero, allOnes, Matrix.of_apply, adj_sq_apply]
    rw [inter_comm]

private theorem gap_row_sum (q : ℕ) (hn : Fintype.card V = q ^ 2 + q + 1) (v : V) :
    (∑ w : V, gap G q v w) =
      (q + 1) * deficiency G q v + ∑ u ∈ G.neighborFinset v, deficiency G q u := by
  have ha :
      (∑ w : V, (G.adjMatrix ℤ * G.adjMatrix ℤ) v w) =
        ∑ x ∈ G.neighborFinset v, (G.degree x : ℤ) := by
    simp only [adjMatrix_mul_apply]
    rw [sum_comm]
    congr with x
    simp [adjMatrix_apply, ← neighborFinset_eq_filter]
  simp only [gap, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, sum_add_distrib,
    sum_sub_distrib, allOnes, Matrix.of_apply, sum_const, nsmul_eq_mul, mul_one,
    card_univ, Matrix.one_apply, smul_eq_mul, mul_ite, mul_zero, ha]
  simp only [sum_ite_eq, mem_univ, ite_true, hn]
  simp only [deficiency, sum_sub_distrib, sum_const, nsmul_eq_mul, card_neighborFinset_eq_degree]
  push_cast
  ring

private theorem uncovered_card (q : ℕ) (hn : Fintype.card V = q ^ 2 + q + 1)
    (hc : ∀ {v w}, v ≠ w → (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    (v : V) : ((uncovered G v).card : ℤ) =
      q * deficiency G q v + ∑ u ∈ G.neighborFinset v, deficiency G q u := by
  have h := sum_erase_add (univ : Finset V) (gap G q v) (mem_univ v)
  rw [gap_diag, gap_row_sum G q hn] at h
  have hi : (∑ w ∈ (univ.erase v), gap G q v w) = (uncovered G v).card := by
    calc
      _ = ∑ w ∈ (univ.erase v), (if w ∈ uncovered G v then (1 : ℤ) else 0) :=
        sum_congr rfl fun w hw => gap_offdiag G q hc (mem_erase.mp hw).1.symm
      _ = _ := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        congr 1
        congr 1
        ext w
        exact ⟨fun h => (mem_filter.mp h).2,
          fun h => mem_filter.mpr ⟨(mem_filter.mp h).1, h⟩⟩
  rw [hi] at h
  linarith

private theorem gap_comm (q : ℕ) (v w : V) :
    (∑ x ∈ G.neighborFinset w, gap G q v x) -
      (∑ x ∈ G.neighborFinset v, gap G q x w) =
      deficiency G q v - deficiency G q w := by
  let A := G.adjMatrix ℤ
  let J := allOnes V ℤ
  have hm : gap G q * A - A * gap G q = J * A - A * J := by
    change ((q : ℤ) • (1 : Matrix V V ℤ) + J - A * A) * A -
      A * ((q : ℤ) • (1 : Matrix V V ℤ) + J - A * A) = _
    simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, mul_assoc]
    abel
  have h := congrArg (fun M : Matrix V V ℤ => M v w) hm
  simp only [Matrix.sub_apply, A, mul_adjMatrix_apply, adjMatrix_mul_apply, J,
    allOnes, Matrix.of_apply, sum_const, nsmul_eq_mul, mul_one, card_neighborFinset_eq_degree] at h
  linarith [show deficiency G q v - deficiency G q w =
    (G.degree w : ℤ) - G.degree v by unfold deficiency; ring]

private theorem covered_neighbors_even
    (hc : ∀ {v w}, v ≠ w → (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    (x : V) : Even (G.neighborFinset x \ uncovered G x).card := by
  classical
  let H : SimpleGraph V := {
    Adj v w := G.Adj v w ∧ v ∈ G.neighborFinset x ∧ w ∈ G.neighborFinset x
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
    loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  have hd (v : V) : H.degree v = if v ∈ G.neighborFinset x \ uncovered G x then 1 else 0 := by
    by_cases hv : v ∈ G.neighborFinset x
    · have hxv : x ≠ v := (mem_neighborFinset_iff.mp hv).ne
      have hvx : v ≠ x := hxv.symm
      have he : H.neighborFinset v = G.neighborFinset x ∩ G.neighborFinset v := by
        ext z
        simp only [mem_neighborFinset, mem_inter]
        change (G.Adj v z ∧ v ∈ G.neighborFinset x ∧ z ∈ G.neighborFinset x) ↔ _
        simp [hv, and_comm]
      have hm := hc hxv
      rw [← card_neighborFinset_eq_degree, he]
      simp only [mem_sdiff, hv, true_and, uncovered, mem_filter, mem_erase, mem_univ, and_true]
      by_cases h : (G.neighborFinset x ∩ G.neighborFinset v).card = 0
      · simp [h, hvx]
      · have : (G.neighborFinset x ∩ G.neighborFinset v).card = 1 := by omega
        simp [this]
    · have he : H.neighborFinset v = ∅ := by
        ext z
        simp only [mem_neighborFinset, notMem_empty]
        change (G.Adj v z ∧ v ∈ G.neighborFinset x ∧ z ∈ G.neighborFinset x) ↔ False
        simp [hv]
      rw [← card_neighborFinset_eq_degree, he]
      simp [hv]
  have h := H.sum_degrees_eq_twice_card_edges
  simp_rw [hd] at h
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter, univ_inter] at h
  exact even_iff_two_dvd.mpr ⟨_, h⟩

private def Perfect (q : ℕ) (p : V) : Prop :=
  deficiency G q p = 0 ∧ ∀ v, G.Adj p v → deficiency G q v = 0

private def PrivateNeighbor (q : ℕ) (y x : V) : Prop :=
  G.Adj y x ∧ deficiency G q x = 0 ∧
    ∀ z ∈ low G q, G.Adj x z → z = y

private theorem gap_zero_of_perfect (q : ℕ) (hn : Fintype.card V = q ^ 2 + q + 1)
    (hc : ∀ {v w}, v ≠ w → (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    {p : V} (hp : Perfect G q p) (v : V) : gap G q p v = 0 := by
  have hu := uncovered_card G q hn hc p
  have hzero : (∑ u ∈ G.neighborFinset p, deficiency G q u) = 0 :=
    sum_eq_zero fun v hv => hp.2 v (mem_neighborFinset_iff.mp hv)
  rw [hp.1, hzero, mul_zero, zero_add] at hu
  have he : uncovered G p = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hu)
  rcases eq_or_ne p v with rfl | h
  · rw [gap_diag, hp.1]
  · rw [gap_offdiag G q hc h, he]
    simp

private theorem gap_nonneg (q : ℕ) (hcap : ∀ v, G.degree v ≤ q + 1)
    (hc : ∀ {v w}, v ≠ w → (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    (v w : V) : 0 ≤ gap G q v w := by
  rcases eq_or_ne v w with rfl | h
  · rw [gap_diag]
    have := hcap v
    unfold deficiency
    omega
  · rw [gap_offdiag G q hc h]
    split <;> omega

private theorem uncovered_subset_low_of_adj_perfect (q : ℕ)
    (hn : Fintype.card V = q ^ 2 + q + 1) (hcap : ∀ v, G.degree v ≤ q + 1)
    (hc : ∀ {v w}, v ≠ w → (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    {p x : V} (hp : Perfect G q p) (hpx : G.Adj p x) :
    uncovered G x ⊆ low G q := by
  intro w hw
  have h := gap_comm G q w p
  have hz (v : V) : gap G q v p = 0 :=
    (gap_symm G q v p).trans (gap_zero_of_perfect G q hn hc hp v)
  simp only [hz, sum_const_zero, sub_zero, hp.1] at h
  have hl := single_le_sum (s := G.neighborFinset p) (f := gap G q w)
    (fun v _ => gap_nonneg G q hcap hc w v) (mem_neighborFinset_iff.mpr hpx)
  have hw' := mem_uncovered_symm G hw
  rw [gap_offdiag G q hc ((mem_uncovered G).mp hw').1] at hl
  simp [hw', h] at hl
  exact mem_filter.mpr ⟨mem_univ _, by omega⟩

private theorem card_without_neighbors (hc : ∀ {v w}, v ≠ w →
      (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    (S : Finset V) {x : V} (hx : x ∉ S) :
    G.degree x ≤ (G.neighborFinset x \ S.biUnion (fun v => G.neighborFinset v)).card + S.card := by
  let C := S.biUnion (fun v => G.neighborFinset v)
  have he : G.neighborFinset x ∩ C =
      S.biUnion (fun v => G.neighborFinset x ∩ G.neighborFinset v) := by
    ext v
    simp only [C, mem_biUnion, mem_inter]
    aesop
  have hb : (G.neighborFinset x ∩ C).card ≤ S.card := by
    rw [he]
    calc
      _ ≤ ∑ v ∈ S, (G.neighborFinset x ∩ G.neighborFinset v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ S, 1 := sum_le_sum fun v hv => hc (fun he' => hx (he' ▸ hv))
      _ = _ := by simp
  have h := card_sdiff_add_card_inter (G.neighborFinset x) C
  rw [card_neighborFinset_eq_degree] at h
  change _ ≤ (G.neighborFinset x \ C).card + _
  omega

private theorem private_adj_perfect (q : ℕ) (hcap : ∀ v, G.degree v ≤ q + 1)
    (hc : ∀ {v w}, v ≠ w → (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1)
    (hS : (low G q).card ≤ q - 1) {y x : V}
    (hx : PrivateNeighbor G q y x) (hq : 1 ≤ q) :
    ∃ p, Perfect G q p ∧ G.Adj p x := by
  let S := low G q
  have hxS : x ∉ S := by simp [S, low, hx.2.1]
  let P := G.neighborFinset x \ S.biUnion (fun v => G.neighborFinset v)
  have hb := card_without_neighbors G hc S hxS
  change G.degree x ≤ P.card + S.card at hb
  have hdx := hx.2.1
  unfold deficiency at hdx
  have hS' : S.card ≤ q - 1 := hS
  have hcount : 1 < P.card := by omega
  have hsub := le_card_sdiff ({y} : Finset V) P
  simp only [card_singleton] at hsub
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < (P \ {y}).card by omega)
  obtain ⟨hpP, hpy⟩ := mem_sdiff.mp hp
  have hpN := mem_neighborFinset_iff.mp (mem_sdiff.mp hpP).1
  have hpS : p ∉ S := fun hs => hpy (mem_singleton.mpr (hx.2.2 p hs hpN))
  have full (v : V) (hv : v ∉ S) : deficiency G q v = 0 := by
    have hh : ¬0 < deficiency G q v := by simpa [S, low] using hv
    have := hcap v
    unfold deficiency at *
    omega
  refine ⟨p, ⟨full p hpS, fun z hz => full z ?_⟩, hpN.symm⟩
  exact fun hs => (mem_sdiff.mp hpP).2 (mem_biUnion.mpr ⟨z, hs, mem_neighborFinset_iff.mpr hz.symm⟩)

end NeighborhoodDeficiency

-- In a graph with a degree cap, optimize first the edge count and then the
-- sum of squared degrees. The second criterion constrains edge switches.
section EdgeSwitches

open _root_.SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

private theorem free_from_common_unique
    (hc : ∀ ⦃u v a b⦄, u ≠ v → G.Adj u a → G.Adj v a → G.Adj u b → G.Adj v b → a = b) :
    (cycleGraph 4).Free G := by
  rintro ⟨f⟩
  have edge (i j : Fin 4) (h : (cycleGraph 4).Adj i j) : G.Adj (f i) (f j) := f.toHom.map_adj h
  exact f.injective.ne (by decide : (1 : Fin 4) ≠ 3) <|
    hc (f.injective.ne (by decide : (0 : Fin 4) ≠ 2))
      (edge 0 1 (by decide)) (edge 2 1 (by decide))
      (edge 0 3 (by decide)) (edge 2 3 (by decide))

private theorem no_square_addEdge
    (hc : ∀ ⦃u v a b⦄, u ≠ v → G.Adj u a → G.Adj v a → G.Adj u b → G.Adj v b → a = b)
    {x y : V}
    (hp : ∀ a b, G.Adj x a → G.Adj a b → G.Adj b y → False) :
    (cycleGraph 4).Free (G ⊔ edge x y) := by
  apply free_from_common_unique
  intro u v a b huv hua hva hub hvb
  by_contra hab
  have haa := hua.ne
  have hbb := hva.ne
  have hcc := hub.ne
  have hdd := hvb.ne
  simp only [sup_adj, edge_adj] at hua hva hub hvb
  have hs (u v : V) : G.Adj u v ↔ G.Adj v u := G.adj_comm u v
  grind

variable [Fintype V] [DecidableEq V]

open scoped Classical in
private noncomputable def degreeSquares (G : SimpleGraph V) : ℤ :=
  ∑ v : V, (G.degree v : ℤ)^2

open scoped Classical in
private def EdgeOptimal (q : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ H : SimpleGraph V, (cycleGraph 4).Free H → (∀ v, H.degree v ≤ q + 1) →
    H.edgeFinset.card ≤ G.edgeFinset.card

open scoped Classical in
private def SquareOptimal (q : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ H : SimpleGraph V, (cycleGraph 4).Free H → (∀ v, H.degree v ≤ q + 1) →
    H.edgeFinset.card = G.edgeFinset.card → degreeSquares H ≤ degreeSquares G

omit [DecidableEq V] in
open scoped Classical in
private theorem exists_optimals (q : ℕ) (G₀ : SimpleGraph V)
    (hG₀ : (cycleGraph 4).Free G₀) (hcap₀ : ∀ v, G₀.degree v ≤ q + 1) :
    ∃ G : SimpleGraph V, (cycleGraph 4).Free G ∧ (∀ v, G.degree v ≤ q + 1) ∧
      G₀.edgeFinset.card ≤ G.edgeFinset.card ∧ EdgeOptimal q G ∧ SquareOptimal q G := by
  classical
  let C := (univ : Finset (SimpleGraph V)).filter
    fun H => (cycleGraph 4).Free H ∧ ∀ v, H.degree v ≤ q + 1
  have h0 : G₀ ∈ C := mem_filter.mpr ⟨mem_univ _, hG₀, hcap₀⟩
  obtain ⟨U, hU, hm⟩ := exists_max_image C (fun H => H.edgeFinset.card) ⟨G₀, h0⟩
  let T := C.filter fun H => H.edgeFinset.card = U.edgeFinset.card
  obtain ⟨G, hGT, hM⟩ := exists_max_image T degreeSquares ⟨U, mem_filter.mpr ⟨hU, rfl⟩⟩
  obtain ⟨hGC, hGedges⟩ := mem_filter.mp hGT
  obtain ⟨_, hGfree, hGcap⟩ := mem_filter.mp hGC
  refine ⟨G, hGfree, hGcap, hGedges ▸ hm _ h0, ?_, ?_⟩
  · intro H hf hd
    rw [hGedges]
    exact hm _ (mem_filter.mpr ⟨mem_univ _, hf, hd⟩)
  · intro H hf hd he
    exact hM _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hf, hd⟩, he.trans hGedges⟩)

open scoped Classical in
private theorem edge_neighbors {a b : V} (hab : a ≠ b) (v : V) :
    (edge a b).neighborFinset v = if v = a then {b} else if v = b then {a} else ∅ := by
  classical
  ext w
  by_cases ha : v = a <;> by_cases hb : v = b <;>
    simp_all [edge_adj, Ne.symm hab]

open scoped Classical in
private theorem add_degrees {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) (v : V) :
    ((G ⊔ edge a b).degree v : ℤ) =
      (G.degree v : ℤ) + (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_sup, edge_neighbors hab]
  by_cases ha : v = a
  · subst v
    have hnb : b ∉ G.neighborFinset a := by simpa using hn
    simp [hab, card_insert_of_notMem hnb]
  · by_cases hb : v = b
    · subst v
      have hnb : a ∉ G.neighborFinset b := by simpa using (mt Adj.symm hn)
      simp [ha, card_insert_of_notMem hnb]
    · simp [ha, hb]

omit [Fintype V] [DecidableEq V] in
private theorem edges_ncard (J : SimpleGraph V) [Fintype J.edgeSet] :
    J.edgeSet.ncard = J.edgeFinset.card := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

omit [DecidableEq V] in
open scoped Classical in
private theorem optimal_has_three_path
    (hc : ∀ ⦃u v a b⦄, u ≠ v → G.Adj u a → G.Adj v a → G.Adj u b → G.Adj v b → a = b)
    (q : ℕ) (hcap : ∀ v, G.degree v ≤ q + 1) (hopt : EdgeOptimal q G)
    {x y : V} (hxy : x ≠ y) (hn : ¬G.Adj x y) (hdx : G.degree x ≤ q) (hdy : G.degree y ≤ q) :
    ∃ a b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b y := by
  classical
  by_contra! hpath
  let H := G ⊔ edge x y
  have hh : (cycleGraph 4).Free H := no_square_addEdge hc (fun a b ha hb hc => hpath a b ha hb hc)
  have hd (v : V) : H.degree v ≤ q + 1 := by
    have hde := add_degrees (G := G) hxy hn v
    simp only [← ncard_neighborSet] at hde ⊢
    change ((G ⊔ edge x y).neighborSet v).ncard ≤ q + 1
    simp only [← ncard_neighborSet] at hcap hdx hdy
    rcases eq_or_ne v x with rfl | hvx
    · simp only [hxy, ite_true, ite_false, add_zero] at hde
      omega
    · rcases eq_or_ne v y with rfl | hvy
      · simp only [hvx, ite_true, ite_false, add_zero] at hde
        omega
      · simp only [hvx, hvy, ite_false, add_zero] at hde
        have := hcap v
        omega
  have he := hopt H hh (fun v => by simpa only [← ncard_neighborSet] using hd v)
  have hf := card_edgeFinset_sup_edge G hn hxy
  simp only [← edges_ncard] at he hf
  change (G ⊔ edge x y).edgeSet.ncard ≤ G.edgeSet.ncard at he
  omega

open scoped Classical in
private theorem delete_degrees {a b : V} (hab : G.Adj a b) (v : V) :
    ((G \ edge a b).degree v : ℤ) =
      (G.degree v : ℤ) - (if v = a then 1 else 0) - (if v = b then 1 else 0) := by
  classical
  have he : (G \ edge a b).neighborFinset v =
      G.neighborFinset v \ (edge a b).neighborFinset v := by
    ext x
    simp
  rw [← card_neighborFinset_eq_degree, he, edge_neighbors hab.ne]
  by_cases ha : v = a
  · subst v
    have hs : ({b} : Finset V) ⊆ G.neighborFinset a := by simpa using hab
    simp [hab.ne, cast_card_sdiff hs]
  · by_cases hb : v = b
    · subst v
      have hs : ({a} : Finset V) ⊆ G.neighborFinset b := by simpa using hab.symm
      simp [ha, cast_card_sdiff hs]
    · simp [ha, hb]

set_option maxHeartbeats 1000000 in
-- Comparing both degree sums before and after the switch takes extra elaboration.
omit [DecidableEq V] in
open scoped Classical in
private theorem switch_improves_only_if
    (hc : ∀ ⦃u v a b⦄, u ≠ v → G.Adj u a → G.Adj v a → G.Adj u b → G.Adj v b → a = b)
    (q : ℕ) (hcap : ∀ v, G.degree v ≤ q + 1) (hopt : SquareOptimal q G)
    {a b c : V} (hab : G.Adj a b) (hac : a ≠ c) (hn : ¬G.Adj a c) (hdc : G.degree c ≤ q)
    (hp : ∀ x y, (G \ edge a b).Adj a x → (G \ edge a b).Adj x y →
      (G \ edge a b).Adj y c → False) :
    G.degree c < G.degree b := by
  classical
  let K := G \ edge a b
  let H := K ⊔ edge a c
  have hKc : ¬K.Adj a c := fun h => hn h.1
  have hbc : b ≠ c := fun he => hn (he ▸ hab)
  have hcf : ∀ ⦃u v x y⦄, u ≠ v → K.Adj u x → K.Adj v x → K.Adj u y → K.Adj v y → x = y :=
    fun _ _ _ _ h huv hvx huy hvy => hc h huv.1 hvx.1 huy.1 hvy.1
  have hH : (cycleGraph 4).Free H := no_square_addEdge hcf hp
  have hde (v : V) : (H.degree v : ℤ) =
      (G.degree v : ℤ) - (if v = b then 1 else 0) + (if v = c then 1 else 0) := by
    have h₁ := add_degrees (G := K) hac hKc v
    have h₂ := delete_degrees (G := G) hab v
    simp only [← ncard_neighborSet] at h₁ h₂ ⊢
    change (↑((K ⊔ edge a c).neighborSet v).ncard : ℤ) = _
    dsimp only [K] at h₁
    linarith
  have hHcap (v : V) : H.degree v ≤ q + 1 := by
    have h := hde v
    by_cases he : v = c
    · subst v
      simp [Ne.symm hbc] at h
      omega
    · simp [he] at h
      split at h <;> have := hcap v <;> omega
  have hb : (H.degree b : ℤ) = (G.degree b : ℤ) - 1 := by simpa [hbc] using hde b
  have hcc : (H.degree c : ℤ) = (G.degree c : ℤ) + 1 := by simpa [Ne.symm hbc] using hde c
  have hs (f : ℕ → ℤ) :
      (∑ v : V, f (H.degree v)) + f (G.degree b) + f (G.degree c) =
        (∑ v : V, f (G.degree v)) + f (H.degree b) + f (H.degree c) := by
    have aux (J : SimpleGraph V) := sum_erase_add ((univ : Finset V).erase b)
      (fun v => f (J.degree v)) (mem_erase.mpr ⟨hbc.symm, mem_univ c⟩)
    have aux' (J : SimpleGraph V) := sum_erase_add (univ : Finset V)
      (fun v => f (J.degree v)) (mem_univ b)
    have he : (∑ v ∈ (univ.erase b).erase c, f (H.degree v)) =
        ∑ v ∈ (univ.erase b).erase c, f (G.degree v) :=
      sum_congr rfl fun v hv => by
        obtain ⟨hvc, hvb, _⟩ := mem_erase.mp hv |>.imp_right mem_erase.mp
        have hh := hde v
        simp only [hvc, hvb, ite_false, sub_zero, add_zero] at hh
        exact congrArg f (by exact_mod_cast hh)
    have h₁ := aux H
    have h₂ := aux G
    have h₃ := aux' H
    have h₄ := aux' G
    simp only [← ncard_neighborSet] at h₁ h₂ h₃ h₄ he ⊢
    linarith
  have ht := hs (fun n => (n : ℤ))
  have hd (J : SimpleGraph V) : (∑ v : V, (J.degree v : ℤ)) = 2 * (J.edgeFinset.card : ℤ) := by
    exact_mod_cast J.sum_degrees_eq_twice_card_edges
  have hdH := hd H
  have hdG := hd G
  simp only [← ncard_neighborSet, ← edges_ncard] at hdH hdG ht hb hcc
  rw [hdH, hdG, hb, hcc] at ht
  have hedge : H.edgeFinset.card = G.edgeFinset.card := by
    simp only [← edges_ncard]
    omega
  have hop := hopt H hH (fun v => by simpa only [← ncard_neighborSet] using hHcap v)
    (by simpa only [← edges_ncard] using hedge)
  have hsq := hs (fun n => (n : ℤ) ^ 2)
  unfold degreeSquares at hop
  simp only [← ncard_neighborSet] at hsq hop
  rw [hb, hcc] at hsq
  have hle : (G.degree c : ℤ) < G.degree b := by
    simp only [← ncard_neighborSet]
    nlinarith
  exact_mod_cast hle

end EdgeSwitches

-- Exclude vertices of degree q + 2 by counting their neighbors' deficiencies
-- and using parity in neighborhoods whose vertices are all paired by triangles.
open _root_.SimpleGraph Finset

section High

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
private theorem sum_deficiency_le (q : ℕ) (hn : Fintype.card V = q ^ 2 + q + 1)
    (hE : (q : ℤ) * (q + 1) ^ 2 + 2 ≤ 2 * (G.edgeFinset.card : ℤ)) :
    (∑ v : V, deficiency G q v) ≤ (q : ℤ) - 1 := by
  simp only [deficiency, sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ, hn, degrees_int]
  push_cast
  nlinarith

private theorem empty_uncovered_even {x : V}
    (hG : (cycleGraph 4).Free G) (hx : (uncovered G x).card = 0) : Even (G.degree x) := by
  simpa only [Finset.card_eq_zero.mp hx, sdiff_empty, card_neighborFinset_eq_degree] using
    covered_neighbors_even G (fun {_ _} he => card_inter_le_one hG he) x

set_option maxHeartbeats 2000000 in
-- The degree bound combines neighborhood sums, parity, and nonlinear arithmetic.
omit [DecidableEq V] in
private theorem no_high_degree (q : ℕ) (hq : 13 < q)
    (hn : Fintype.card V = q ^ 2 + q + 1) (hG : (cycleGraph 4).Free G)
    (hE : (q : ℤ) * (q + 1) ^ 2 + 2 ≤ 2 * (G.edgeFinset.card : ℤ)) (x : V) :
    G.degree x ≤ q + 1 := by
  classical
  let N (v : V) := G.neighborFinset v
  let H := (univ : Finset V).filter fun v => G.degree v = q + 2
  let P (v : V) : ℤ := max (deficiency G q v) 0
  let D := ∑ v : V, P v
  have hcap := maxDegree_le q hq hn hG hE
  have hc {a b : V} (he : a ≠ b) := card_inter_le_one hG he
  have hP (v : V) : 0 ≤ P v := le_max_right _ _
  have hH (v : V) : v ∈ H ↔ G.degree v = q + 2 := by simp [H]
  have hPsum : D ≤ (q : ℤ) - 1 + H.card := by
    have heq (v : V) : P v = deficiency G q v + if v ∈ H then 1 else 0 := by
      by_cases hv : v ∈ H
      · have hd := (hH v).mp hv
        unfold P deficiency
        simp [hd, hv]
      · have hvd := (hH v).not.mp hv
        have hcap' := hcap v
        have hnonneg : 0 ≤ deficiency G q v := by unfold deficiency; omega
        simp [P, hv, max_eq_left hnonneg]
    have hf : (univ.filter (· ∈ H)) = H := by ext v; simp
    dsimp only [D]
    simp_rw [heq]
    rw [sum_add_distrib, ← sum_filter, hf, sum_const, nsmul_eq_mul, mul_one]
    linarith [sum_deficiency_le q hn hE]
  have hneed (v : V) (hv : v ∈ H) : (q : ℤ) ≤ ∑ u ∈ N v, P u := by
    have hu := uncovered_card G q hn hc v
    have hd : deficiency G q v = -1 := by unfold deficiency; have := (hH v).mp hv; omega
    rw [hd] at hu
    have hs : (∑ u ∈ N v, deficiency G q u) ≤ ∑ u ∈ N v, P u :=
      sum_le_sum fun u _ => le_max_left _ _
    nlinarith
  have hdegH (v : V) : ((N v).filter (· ∈ H)).card ≤ 2 := by
    simpa only [hH, N] using two_high_neighbors q hq hn hG hE v
  have hdouble : (H.card : ℤ) * q ≤ 2 * D := by
    calc
      _ = ∑ _v ∈ H, (q : ℤ) := by simp
      _ ≤ ∑ v ∈ H, ∑ u ∈ N v, P u := sum_le_sum hneed
      _ = ∑ u : V, ((N u).filter (· ∈ H)).card * P u := by
        simp_rw [N, neighborFinset_eq_filter, sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro u _
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        have he : (H.filter fun v => G.Adj v u) =
            ((univ.filter fun v => G.Adj u v).filter (· ∈ H)) := by
          ext v
          simp [G.adj_comm v u, and_comm]
        rw [he]
      _ ≤ _ := by
        dsimp only [D]
        rw [mul_sum]
        apply sum_le_sum
        intro v _
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegH v) (hP v)
  have hHle : H.card ≤ 2 := by
    by_contra! hH'
    have hp := mul_nonneg (show (H.card : ℤ) - 3 ≥ 0 by omega)
      (show (q : ℤ) - 2 ≥ 0 by omega)
    nlinarith
  have hNotTwo : H.card ≠ 2 := by
    intro h2
    obtain ⟨a, b, hab, he⟩ := card_eq_two.mp h2
    have ha : a ∈ H := by simp [he]
    have hb : b ∈ H := by simp [he]
    have hPmax (u : V) : P u ≤ (q : ℤ) - 2 := by
      have hmin := minDegree_ge_three q hq hn hG hE u
      dsimp [P, deficiency]
      rw [max_le_iff]
      omega
    have hInt : (∑ z ∈ N a ∩ N b, P z) ≤ (q : ℤ) - 2 := by
      calc
        _ ≤ ∑ _z ∈ N a ∩ N b, ((q : ℤ) - 2) := sum_le_sum fun z _ => hPmax z
        _ = ((N a ∩ N b).card : ℤ) * ((q : ℤ) - 2) := by simp only [sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          have hm := mul_le_mul_of_nonneg_right (show ((N a ∩ N b).card : ℤ) ≤ 1 by
            exact_mod_cast hc hab) (show 0 ≤ (q : ℤ) - 2 by omega)
          simpa using hm
    have hUnion : (∑ z ∈ N a ∪ N b, P z) ≤ D :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ => hP z
    have hs := sum_union_inter (s₁ := N a) (s₂ := N b) (f := P)
    have hs₁ := hneed a ha
    have hs₂ := hneed b hb
    rw [h2] at hPsum
    omega
  by_contra! hx
  have hxH : x ∈ H := (hH x).mpr (by have := hcap x; omega)
  have hHone : H = {x} := by
    have hp : 0 < H.card := card_pos.mpr ⟨x, hxH⟩
    obtain ⟨y, hy⟩ := card_eq_one.mp (by omega : H.card = 1)
    have he : x = y := by simpa [hy] using hxH
    simpa [he] using hy
  have hxHdeg := (hH x).mp hxH
  have hD : D ≤ q := by simpa [hHone] using hPsum
  have hPN : (∑ z ∈ N x, P z) = q := by
    have hle := sum_le_sum_of_subset_of_nonneg (subset_univ (N x)) (fun z _ _ => hP z)
    have hge := hneed x hxH
    linarith [hD]
  have hnotHigh {z : V} (hz : z ≠ x) : G.degree z ≤ q + 1 := by
    have hzH : z ∉ H := by simp [hHone, hz]
    have he := (hH z).not.mp hzH
    have := hcap z
    omega
  have hDefP (z : V) (hz : z ≠ x) : deficiency G q z = P z := by
    have hn := hnotHigh hz
    have hnonneg : 0 ≤ deficiency G q z := by unfold deficiency; omega
    simp [P, max_eq_left hnonneg]
  have hPoutside {z : V} (hz : z ∉ N x) : P z = 0 := by
    have hu := sum_sdiff (s₁ := N x) (f := P) (subset_univ (N x))
    rw [hPN] at hu
    have hsingle := single_le_sum (s := univ \ N x) (f := P)
      (fun z _ => hP z) (mem_sdiff.mpr ⟨mem_univ _, hz⟩)
    linarith [hP z]
  have hUx : (uncovered G x).card = 0 := by
    have hu := uncovered_card G q hn hc x
    have hd : deficiency G q x = -1 := by unfold deficiency; omega
    have hsum : ∑ z ∈ N x, deficiency G q z = q :=
      (sum_congr rfl fun z hz => hDefP z (mem_neighborFinset_iff.mp hz).ne.symm).trans hPN
    rw [hd, hsum, mul_neg, mul_one, neg_add_cancel] at hu
    exact_mod_cast hu
  have hEven := empty_uncovered_even hG hUx
  obtain ⟨z, hz, hPz⟩ : ∃ z ∈ N x, P z = 0 := by
    by_contra! hno
    have hz : (((N x).card : ℕ) : ℤ) ≤ ∑ v ∈ N x, P v := by
      simpa using sum_le_sum (s := N x) (f := fun _ => (1 : ℤ)) fun z hz => by
        have := hno z hz
        have := hP z
        omega
    rw [hPN, card_neighborFinset_eq_degree, hxHdeg] at hz
    omega
  have hxz := mem_neighborFinset_iff.mp hz
  have hdz : G.degree z = q + 1 := by
    have hzz := hDefP z hxz.ne.symm
    unfold deficiency at hzz
    omega
  let A := N z \ N x
  have hA : A.card ≥ q := by
    have h := card_sdiff_add_card_inter (N z) (N x)
    rw [card_neighborFinset_eq_degree, hdz] at h
    have hi := hc hxz.ne.symm
    change (N z ∩ N x).card ≤ 1 at hi
    change A.card + _ = _ at h
    omega
  have hB := le_card_sdiff ({x} : Finset V) A
  simp only [card_singleton] at hB
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (A \ {x}).card by omega)
  obtain ⟨huA, hux'⟩ := mem_sdiff.mp hu
  obtain ⟨huN, huout⟩ := mem_sdiff.mp huA
  have hux : u ≠ x := fun he => hux' (mem_singleton.mpr he)
  have hdu : deficiency G q u = 0 := (hDefP u hux).trans (hPoutside huout)
  have hnfull (v : V) (hv : v ∈ N u) : deficiency G q v = 0 := by
    have huv := mem_neighborFinset_iff.mp hv
    have hvx : v ≠ x := fun h => huout (mem_neighborFinset_iff.mpr ((h ▸ huv).symm))
    by_cases hv' : v ∈ N x
    · have hvz := common_neighbor_unique hG hux huv (mem_neighborFinset_iff.mp hv')
        (mem_neighborFinset_iff.mp huN).symm hxz
      exact hvz ▸ (hDefP z hxz.ne.symm).trans hPz
    · exact (hDefP v hvx).trans (hPoutside hv')
  have huClear : (uncovered G u).card = 0 := by
    have he := uncovered_card G q hn hc u
    rw [hdu, mul_zero, zero_add, sum_eq_zero hnfull] at he
    exact_mod_cast he
  have hEven' := empty_uncovered_even hG huClear
  have hdeg_u : G.degree u = q + 1 := by unfold deficiency at hdu; omega
  rw [hdeg_u] at hEven'
  rw [hxHdeg] at hEven
  obtain ⟨a, ha⟩ := hEven
  obtain ⟨b, hb⟩ := hEven'
  omega

end High

-- Complete the degrees of the deficient vertices using uncovered pairs.
-- The signs of the new gap matrix allow a single edge to be added safely.
open _root_.SimpleGraph Finset Matrix

section Capped

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {q : ℕ}

local notation "δ" => deficiency G q
local notation "S" => low G q
local notation "N" => (fun v => G.neighborFinset v)
local notation "U" => uncovered G

private structure CappedSetup (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : Prop where
  positive : 1 ≤ q
  order : Fintype.card V = q ^ 2 + q + 1
  free : (cycleGraph 4).Free G
  cap : ∀ v, G.degree v ≤ q + 1
  total : (∑ v : V, deficiency G q v) ≤ (q : ℤ) - 1

omit [DecidableEq V] in
private theorem low_iff {v : V} : v ∈ S ↔ 0 < δ v := by simp [low]

omit [DecidableEq V] in
private theorem deficiency_nonneg (h : CappedSetup G q) (v : V) : 0 ≤ δ v := by
  have := h.cap v
  unfold deficiency
  omega

omit [DecidableEq V] in
private theorem full_of_not_low (h : CappedSetup G q) {v : V} (hv : v ∉ S) : δ v = 0 := by
  rw [low_iff, not_lt] at hv
  exact le_antisymm hv (deficiency_nonneg h v)

omit [DecidableEq V] in
private theorem low_degree_le {v : V} (hv : v ∈ S) : G.degree v ≤ q := by
  rw [low_iff, deficiency] at hv
  omega

omit [DecidableEq V] in
private theorem low_sum (h : CappedSetup G q) : (∑ v ∈ S, δ v) = ∑ v : V, δ v := by
  exact sum_subset (subset_univ _) fun v _ hv => full_of_not_low h hv

omit [DecidableEq V] in
private theorem low_card_bound (h : CappedSetup G q) : (S).card ≤ q - 1 := by
  have hs : ((S).card : ℤ) ≤ ∑ v ∈ S, δ v := by
    simpa using sum_le_sum (s := S) (f := fun _ => (1 : ℤ)) (fun v hv => by
      have := low_iff.mp hv
      omega)
  rw [low_sum h] at hs
  have ht := h.total
  omega

omit [DecidableEq V] in
private theorem perfect_exists (h : CappedSetup G q) : ∃ p, Perfect G q p := by
  classical
  let B := (S).biUnion (fun v => insert v (N v))
  have hB : B.card ≤ (S).card * (q + 1) := by
    calc
      _ ≤ ∑ v ∈ S, (insert v (N v)).card := card_biUnion_le
      _ ≤ ∑ _v ∈ S, (q + 1) := by
        apply sum_le_sum
        intro v hv
        change (insert v (G.neighborFinset v)).card ≤ q + 1
        rw [card_insert_of_notMem (G.notMem_neighborFinset_self v), card_neighborFinset_eq_degree]
        have := low_degree_le hv
        omega
      _ = _ := by simp only [sum_const, Nat.nsmul_eq_mul]
  have hlt : B.card < Fintype.card V := by
    rw [h.order]
    have ht := Nat.mul_le_mul_right (q + 1) (low_card_bound h)
    have he := Nat.sub_add_cancel h.positive
    nlinarith
  obtain ⟨p, hp⟩ := exists_mem_notMem_of_card_lt_card (s := B) (t := univ) (by simpa using hlt)
  refine ⟨p, full_of_not_low h ?_, fun v hv => full_of_not_low h ?_⟩
  · exact fun hs => hp.2 (mem_biUnion.mpr ⟨p, hs, mem_insert_self _ _⟩)
  · exact fun hs => hp.2 (mem_biUnion.mpr
      ⟨v, hs, mem_insert_of_mem (mem_neighborFinset_iff.mpr hv.symm)⟩)

private def privateCandidates (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (y : V) :
    Finset V :=
  G.neighborFinset y \ ((low G q).erase y).biUnion (fun v => G.neighborFinset v)

private theorem mem_privateCandidates {x y : V} :
    x ∈ privateCandidates G q y ↔ G.Adj y x ∧ ∀ z ∈ S, G.Adj x z → z = y := by
  simp only [privateCandidates, mem_sdiff, mem_neighborFinset_iff, mem_biUnion, mem_erase]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun z hz hx => by by_contra hne; exact h ⟨z, ⟨hne, hz⟩, hx.symm⟩⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun ⟨z, hz, hx⟩ => hz.1 (h z hz.2 hx.symm)⟩

private theorem privateCandidates_lower (h : CappedSetup G q) {y : V} (hy : y ∈ S) :
    q + 2 ≤ (privateCandidates G q y).card + (S).card + (δ y).toNat := by
  have he := card_without_neighbors G (fun {_ _} he => card_inter_le_one h.free he)
    ((S).erase y) (notMem_erase y S)
  change G.degree y ≤ (privateCandidates G q y).card + _ at he
  have hc := card_erase_add_one hy
  have hn := deficiency_nonneg h y
  have hf := Int.toNat_of_nonneg hn
  have hd : (G.degree y : ℤ) + δ y = q + 1 := by unfold deficiency; ring
  omega

private theorem private_exists_of_small (h : CappedSetup G q) {y : V}
    (hy : y ∈ S) (ht : (N y ∩ S).card ≤ 1) :
    ∃ x, PrivateNeighbor G q y x := by
  have hc := privateCandidates_lower h hy
  have hs := low_card_bound h
  have hys : (((S).card : ℤ) + δ y - 1) ≤ ∑ v : V, δ v := by
    have h := sum_erase_add S δ hy
    rw [low_sum ‹CappedSetup G q›] at h
    have hb : (((S).erase y).card : ℤ) ≤ ∑ v ∈ (S).erase y, δ v := by
      simpa using sum_le_sum (s := (S).erase y) (f := fun _ => (1 : ℤ)) (fun v hv => by
        have := low_iff.mp (mem_erase.mp hv).2
        omega)
    have he := card_erase_add_one hy
    omega
  have htot := h.total
  have hn := Int.toNat_of_nonneg (deficiency_nonneg h y)
  have htwo : 2 ≤ (privateCandidates G q y).card := by omega
  have hnot : ¬privateCandidates G q y ⊆ N y ∩ S :=
    fun hs' => by have := card_le_card hs'; omega
  obtain ⟨x, hx, hn⟩ := not_subset.mp hnot
  obtain ⟨hxy, hp⟩ := mem_privateCandidates.mp hx
  have hn' : x ∉ S := fun hs' => hn (mem_inter.mpr ⟨mem_neighborFinset_iff.mpr hxy, hs'⟩)
  exact ⟨x, hxy, full_of_not_low h hn', hp⟩

private theorem private_neighbor_zero_or_one {v y : V}
    (hv : v ∈ privateCandidates G q y) : (N v ∩ S).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  have hm := (mem_privateCandidates.mp hv).2
  obtain ⟨haN, haS⟩ := mem_inter.mp ha
  obtain ⟨hbN, hbS⟩ := mem_inter.mp hb
  exact (hm a haS (mem_neighborFinset_iff.mp haN)).trans
    (hm b hbS (mem_neighborFinset_iff.mp hbN)).symm

-- Each row prescribes new neighbors for one deficient vertex.
private structure MissingRow (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (y : V) where
  entries : Finset V
  low_entries : entries ⊆ low G q
  card_entries : (entries.card : ℤ) = deficiency G q y
  fresh : ∀ ⦃w⦄, w ∈ entries → y ≠ w ∧ ¬G.Adj y w
  covers : uncovered G y \ low G q ⊆ entries.biUnion (fun w => G.neighborFinset w)
  excludes : ∀ v, deficiency G q v = 0 → G.Adj y v → entries ⊆ uncovered G v

private theorem uncovered_neighbors_cover (h : CappedSetup G q) {y z v : V}
    (hz : z ∈ U y \ S) (hv : δ v = 0) (hyv : G.Adj y v) :
    ∃ w ∈ U v, G.Adj z w := by
  have hc {a b : V} (he : a ≠ b) := card_inter_le_one h.free he
  obtain ⟨hzy, hzs⟩ := mem_sdiff.mp hz
  have hdz := full_of_not_low h hzs
  have hc' := gap_comm G q z v
  rw [hv, hdz, sub_self, sub_eq_zero] at hc'
  have hl := single_le_sum (s := N v) (f := gap G q z)
    (fun w _ => gap_nonneg G q h.cap hc z w) (mem_neighborFinset_iff.mpr hyv.symm)
  have hyz := mem_uncovered_symm G hzy
  rw [gap_offdiag G q hc (mem_uncovered G |>.mp hyz |>.1), hc'] at hl
  simp only [hyz, ite_true] at hl
  by_contra! hno
  have hzero : (∑ w ∈ N z, gap G q w v) = 0 := by
    apply sum_eq_zero
    intro w hw
    by_cases hwv : w = v
    · subst w
      rw [gap_diag, hv]
    · rw [gap_offdiag G q hc hwv]
      have hnv : v ∉ U w := fun h' =>
        hno w (mem_uncovered_symm G h') (mem_neighborFinset_iff.mp hw)
      simp [hnv]
  rw [hzero] at hl
  norm_num at hl

private theorem uncovered_bound_at_neighbor (h : CappedSetup G q) {y v : V}
    (hv : δ v = 0) (hyv : G.Adj y v) :
    ((U v).card : ℤ) + ((U y ∩ S).card : ℤ) ≤ (q : ℤ) - 1 := by
  have hu := uncovered_card G q h.order (fun {_ _} he => card_inter_le_one h.free he) v
  rw [hv, mul_zero, zero_add] at hu
  have hdis : Disjoint (N v) (U y ∩ S) := by
    apply Finset.disjoint_left.mpr
    intro x hnx hx
    have h := (mem_uncovered G).mp (mem_inter.mp hx).1
    exact h.2 ⟨v, hyv, (mem_neighborFinset_iff.mp hnx).symm⟩
  have hl : ((U y ∩ S).card : ℤ) ≤ ∑ x ∈ U y ∩ S, δ x := by
    simpa using sum_le_sum (s := U y ∩ S) (f := fun _ => (1 : ℤ)) (fun x hx => by
      have := low_iff.mp (mem_inter.mp hx).2
      omega)
  have htotal := (sum_le_sum_of_subset_of_nonneg (subset_univ (N v ∪ (U y ∩ S)))
    (fun x _ _ => deficiency_nonneg h x)).trans h.total
  rw [sum_union hdis, ← hu] at htotal
  omega

private theorem missing_row_of_private (h : CappedSetup G q) (hodd : Odd q) {y x : V}
    (hx : PrivateNeighbor G q y x) :
    Nonempty (MissingRow G q y) := by
  classical
  have hc {a b : V} (he : a ≠ b) := card_inter_le_one h.free he
  obtain ⟨p, hp, hpx⟩ := private_adj_perfect G q h.cap hc (low_card_bound h) hx h.positive
  let M := U x
  have hMs : M ⊆ S := uncovered_subset_low_of_adj_perfect G q h.order h.cap hc hp hpx
  have hMcard : (M.card : ℤ) = δ y := by
    have hsum : (∑ v ∈ N x, δ v) = δ y := by
      apply sum_eq_single y
      · intro z hz hzy
        exact full_of_not_low h (fun hzs => hzy (hx.2.2 z hzs (mem_neighborFinset_iff.mp hz)))
      · intro hn
        exact (hn (mem_neighborFinset_iff.mpr hx.1.symm)).elim
    have he := uncovered_card G q h.order hc x
    rw [hx.2.1, hsum, mul_zero, zero_add] at he
    exact he
  have hynM : y ∉ M := by
    intro hyM
    have heq : N x \ U x = (N x).erase y := by
      ext z
      simp only [mem_sdiff, mem_erase]
      exact ⟨fun ⟨hz, hnu⟩ => ⟨fun he => hnu (he.symm ▸ hyM), hz⟩,
        fun ⟨hne, hz⟩ => ⟨hz, fun hu => hne (hx.2.2 z (hMs hu) (mem_neighborFinset_iff.mp hz))⟩⟩
    have hpar := covered_neighbors_even G hc x
    rw [heq] at hpar
    have he : ((N x).erase y).card + 1 = G.degree x := by
      rw [← card_neighborFinset_eq_degree]
      exact card_erase_add_one (mem_neighborFinset_iff.mpr hx.1.symm)
    have hd := hx.2.1
    unfold deficiency at hd
    have heq' : ((N x).erase y).card = q := by omega
    rw [heq'] at hpar
    exact (Nat.not_even_iff_odd.mpr hodd) hpar
  have hnew {w : V} (hw : w ∈ M) : y ≠ w ∧ ¬G.Adj y w := by
    refine ⟨fun he => hynM (he.symm ▸ hw), ?_⟩
    exact fun hye => (mem_uncovered G |>.mp hw).2 ⟨y, hx.1.symm, hye.symm⟩
  let F := U y \ S
  have hF : F ⊆ M.biUnion (fun w => N w) := by
    intro z hz
    obtain ⟨w, hw, ha⟩ := uncovered_neighbors_cover h hz hx.2.1 hx.1
    exact mem_biUnion.mpr ⟨w, hw, mem_neighborFinset_iff.mpr ha.symm⟩
  refine ⟨⟨M, hMs, hMcard, fun {_} hw => hnew hw, hF, ?_⟩⟩
  intro v hv hyv w hw
  by_contra hwn
  let C := (M.erase w).biUnion (fun u => N u)
  let T := F \ C
  have hC : (C.card : ℤ) ≤ ((M.card : ℤ) - 1) * q := by
    have hc' : C.card ≤ (M.erase w).card * q := by
      calc
        _ ≤ ∑ x ∈ M.erase w, (N x).card := card_biUnion_le
        _ ≤ ∑ _x ∈ M.erase w, q := sum_le_sum fun z hz => by
          rw [card_neighborFinset_eq_degree]
          exact low_degree_le (hMs (mem_erase.mp hz).2)
        _ = _ := by simp
    have h₁ := card_erase_add_one hw
    have h₂ : ((M.erase w).card : ℤ) = M.card - 1 := by omega
    exact (by exact_mod_cast hc' : (C.card : ℤ) ≤ (M.erase w).card * (q : ℤ)).trans_eq
      (by rw [h₂])
  have hFt : (F.card : ℤ) + (U y ∩ S).card = (U y).card := by
    exact_mod_cast card_sdiff_add_card_inter (U y) S
  have hUv := uncovered_card G q h.order hc y
  have hNnn : 0 ≤ ∑ u ∈ N y, δ u := sum_nonneg fun u _ => deficiency_nonneg h u
  have hTlower : (q : ℤ) - (U y ∩ S).card ≤ T.card := by
    have hh : (F.card : ℤ) ≤ T.card + C.card := by
      exact_mod_cast (card_le_card_sdiff_add_card (s := F) (t := C))
    nlinarith
  have hT' (z : V) (hz : z ∈ T) : G.Adj w z := by
    obtain ⟨hf, hnc⟩ := mem_sdiff.mp hz
    obtain ⟨u, hum, hn⟩ := mem_biUnion.mp (hF hf)
    have huw : u = w := by
      by_contra he
      exact hnc (mem_biUnion.mpr ⟨u, mem_erase.mpr ⟨he, hum⟩, hn⟩)
    exact huw ▸ mem_neighborFinset_iff.mp hn
  have hassign (z : V) (hz : z ∈ T) : ∃ t ∈ U v, G.Adj z t :=
    uncovered_neighbors_cover h (mem_sdiff.mp hz).1 hv hyv
  let f (z : V) := if hz : z ∈ T then Classical.choose (hassign z hz) else z
  have hf₁ (z : V) (hz : z ∈ T) : f z ∈ U v := by
    rw [show f z = Classical.choose (hassign z hz) by simp [f, hz]]
    exact (Classical.choose_spec (hassign z hz)).1
  have hf₂ (z : V) (hz : z ∈ T) : G.Adj z (f z) := by
    rw [show f z = Classical.choose (hassign z hz) by simp [f, hz]]
    exact (Classical.choose_spec (hassign z hz)).2
  have hb : T.card ≤ (U v).card := by
    apply card_le_card_of_injOn f (fun z hz => hf₁ z hz)
    intro a ha b hb he
    have hneq : w ≠ f a := fun hwfa => hwn (hwfa ▸ hf₁ a ha)
    exact common_neighbor_unique h.free hneq (hT' a ha) (hf₂ a ha).symm
      (hT' b hb) (he.symm ▸ (hf₂ b hb).symm)
  have hbound := uncovered_bound_at_neighbor h hv hyv
  omega

private theorem missing_row_symm {y w : V} (My : MissingRow G q y) (Mw : MissingRow G q w)
    (hx : ∃ x, PrivateNeighbor G q y x) (hw : w ∈ My.entries) : y ∈ Mw.entries := by
  obtain ⟨x, hx⟩ := hx
  have hu := mem_uncovered_symm G (My.excludes x hx.2.1 hx.1 hw)
  have hx' : x ∉ S := by simp [low, hx.2.1]
  obtain ⟨z, hz, hxz⟩ := mem_biUnion.mp (Mw.covers (mem_sdiff.mpr ⟨hu, hx'⟩))
  exact (hx.2.2 z (Mw.low_entries hz) (mem_neighborFinset_iff.mp hxz).symm) ▸ hz

private theorem path_starts_low {y w a b : V} (h : CappedSetup G q)
    (My : MissingRow G q y) (hw : w ∈ My.entries)
    (hya : G.Adj y a) (hab : G.Adj a b) (hbw : G.Adj b w) : a ∈ S := by
  by_contra hna
  exact (mem_uncovered G |>.mp (My.excludes a (full_of_not_low h hna) hya hw)).2
    ⟨b, hab, hbw.symm⟩

set_option maxHeartbeats 1000000 in
-- The proof compares the degree changes from two successive applications of the switch lemma.
omit [DecidableEq V] in
open scoped Classical in
private theorem all_have_private (h : CappedSetup G q) (hodd : Odd q)
    (hE : EdgeOptimal q G) (hD : SquareOptimal q G) {v₀ : V} (hv₀ : v₀ ∈ S) :
    ∃ x, PrivateNeighbor G q v₀ x := by
  classical
  by_contra hcontra
  let B := (S).filter fun v => ¬∃ x, PrivateNeighbor G q v x
  obtain ⟨v, hvB, hvmax⟩ := exists_max_image B δ ⟨v₀, mem_filter.mpr ⟨hv₀, hcontra⟩⟩
  obtain ⟨hv, hvno⟩ := mem_filter.mp hvB
  let C := privateCandidates G q v
  have hClow (y : V) (hy : y ∈ C) : y ∈ S := by
    by_contra hy'
    obtain ⟨hvy, hpr⟩ := mem_privateCandidates.mp hy
    exact hvno ⟨y, hvy, full_of_not_low h hy', hpr⟩
  have hh : ∀ ⦃u v a b : V⦄, u ≠ v → G.Adj u a → G.Adj v a →
      G.Adj u b → G.Adj v b → a = b := by
    intro u v a b
    exact common_neighbor_unique h.free
  have hleaf (y : V) (hy : y ∈ C) : 2 ≤ δ y := by
    have hyS := hClow y hy
    obtain ⟨hvy, hyprivate⟩ := mem_privateCandidates.mp hy
    obtain ⟨x, hx⟩ := private_exists_of_small h hyS (private_neighbor_zero_or_one hy)
    obtain ⟨M⟩ := missing_row_of_private h hodd hx
    have hpos : 0 < M.entries.card := by have := low_iff.mp hyS; have := M.card_entries; omega
    obtain ⟨w, hw⟩ := card_pos.mp hpos
    obtain ⟨hyw, hnew⟩ := M.fresh hw
    have hwS := M.low_entries hw
    have hwdeg : (G.neighborSet w).ncard ≤ q := by
      simpa only [ncard_neighborSet] using low_degree_le hwS
    have hydeg : (G.neighborSet y).ncard ≤ q := by
      simpa only [ncard_neighborSet] using low_degree_le hyS
    have hfirst {a b : V} (hya : G.Adj y a) (hab : G.Adj a b) (hbw : G.Adj b w) : a = v :=
      hyprivate a (path_starts_low h M hw hya hab hbw) hya
    have hshift := switch_improves_only_if hh q
      (fun u => by simpa only [← ncard_neighborSet] using h.cap u) hD hvy.symm hyw hnew
      (by simpa only [← ncard_neighborSet] using hwdeg)
      (fun a b ha hb hc => by
        have he := hfirst ha.1 hb.1 hc.1
        subst a
        exact ha.2 ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hvy.ne.symm⟩))
    have hltd : δ v < δ w := by
      simp only [← ncard_neighborSet] at hshift
      unfold deficiency
      simp only [← ncard_neighborSet]
      omega
    have hus : ∃ t, PrivateNeighbor G q w t := by
      by_contra hno
      have hle := hvmax w (mem_filter.mpr ⟨hwS, hno⟩)
      omega
    obtain ⟨t, ht⟩ := hus
    obtain ⟨W⟩ := missing_row_of_private h hodd ht
    have hyW := missing_row_symm M W ⟨x, hx⟩ hw
    obtain ⟨a, z, hya, haz, hzw⟩ :=
      optimal_has_three_path hh q (fun u => by simpa only [← ncard_neighborSet] using h.cap u)
        hE hyw hnew (by simpa only [← ncard_neighborSet] using hydeg)
        (by simpa only [← ncard_neighborSet] using hwdeg)
    have hav := hfirst hya haz hzw
    subst a
    have hzS := path_starts_low h W hyW hzw.symm haz.symm hya.symm
    have hvw : v ≠ w := fun he => hnew (he ▸ hvy.symm)
    have hshift' := switch_improves_only_if hh q
      (fun u => by simpa only [← ncard_neighborSet] using h.cap u) hD hzw.symm hyw.symm
      (fun ha => hnew ha.symm) (by simpa only [← ncard_neighborSet] using hydeg)
      (fun a b ha hb hc => by
        have hbv := hfirst hc.1.symm hb.1.symm ha.1.symm
        subst b
        have he := hh hvw hb.1.symm ha.1 haz hzw.symm
        subst a
        exact ha.2 ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hzw.ne.symm⟩))
    have hzpos := low_iff.mp hzS
    simp only [← ncard_neighborSet] at hshift'
    unfold deficiency at hzpos ⊢
    simp only [← ncard_neighborSet] at hzpos ⊢
    omega
  have hCs : C ⊆ (S).erase v := by
    intro y hy
    exact mem_erase.mpr ⟨(mem_privateCandidates.mp hy).1.ne.symm, hClow y hy⟩
  have hweight : (((S).erase v).card : ℤ) + C.card ≤ ∑ y ∈ (S).erase v, δ y := by
    have ht : (∑ y ∈ (S).erase v, (1 + if y ∈ C then (1 : ℤ) else 0)) ≤
        ∑ y ∈ (S).erase v, δ y := by
      apply sum_le_sum
      intro y hy
      have hp := low_iff.mp (mem_erase.mp hy).2
      by_cases ht : y ∈ C
      · have hh' := hleaf y ht
        simp [ht]
        omega
      · simp [ht]
        omega
    have hf : ((S).erase v).filter (· ∈ C) = C := by
      ext y
      exact ⟨fun hr => (mem_filter.mp hr).2, fun hr => mem_filter.mpr ⟨hCs hr, hr⟩⟩
    rw [sum_add_distrib, ← sum_filter, hf, sum_const, nsmul_eq_mul, mul_one,
      sum_const, nsmul_eq_mul, mul_one] at ht
    exact ht
  have htotal := h.total
  rw [← low_sum h, ← sum_erase_add S δ hv] at htotal
  have hC := privateCandidates_lower h hv
  have hCv : ((S).erase v).card + 1 = (S).card := card_erase_add_one hv
  have hcast := Int.toNat_of_nonneg (deficiency_nonneg h v)
  change q + 2 ≤ C.card + (S).card + (δ v).toNat at hC
  omega

set_option maxHeartbeats 2000000 in
-- The completion argument uses several finite sums over the original and enlarged graphs.
omit [DecidableEq V] in
open scoped Classical in
private theorem odd_capped_nonempty_impossible (h : CappedSetup G q) (hodd : Odd q)
    (hE : EdgeOptimal q G) (hD : SquareOptimal q G) (hS : (S).Nonempty) : False := by
  classical
  have hp y (hy : y ∈ S) := all_have_private h hodd hE hD hy
  have hm y (hy : y ∈ S) : Nonempty (MissingRow G q y) := by
    obtain ⟨x, hx⟩ := hp y hy
    exact missing_row_of_private h hodd hx
  let M (y : V) (hy : y ∈ S) := Classical.choice (hm y hy)
  let R (y w : V) : Prop := ∃ hy : y ∈ S, w ∈ (M y hy).entries
  have hsymm : Std.Symm R := ⟨fun y w ⟨hy, hw⟩ => by
    have hwS := (M y hy).low_entries hw
    exact ⟨hwS, missing_row_symm (M y hy) (M w hwS) (hp y hy) hw⟩⟩
  have hnew {y w : V} (hr : R y w) : y ≠ w ∧ ¬G.Adj y w := by
    obtain ⟨hy, hw⟩ := hr
    exact (M y hy).fresh hw
  let H : SimpleGraph V := {
    Adj y w := G.Adj y w ∨ R y w
    symm := ⟨fun y w hy => hy.elim (Or.inl ∘ Adj.symm) (Or.inr ∘ hsymm.symm y w)⟩
    loopless := ⟨fun _ hy => hy.elim (fun h => h.ne rfl) (fun h => (hnew h).1 rfl)⟩ }
  have hHadj {y w : V} : H.Adj y w ↔ G.Adj y w ∨ R y w := Iff.rfl
  have hNfull {u : V} (hu : δ u = 0) : H.neighborFinset u = N u := by
    ext w
    rw [mem_neighborFinset_iff, mem_neighborFinset_iff, hHadj]
    exact or_iff_left (fun ⟨h, _⟩ => (low_iff.mp h).ne' hu)
  have hNlow {u : V} (hu : u ∈ S) : H.neighborFinset u = N u ∪ (M u hu).entries := by
    ext w
    simp only [mem_neighborFinset_iff, hHadj, mem_union, R]
    exact or_congr_right ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩
  have hregular (u : V) : deficiency H q u = 0 := by
    unfold deficiency
    rw [← card_neighborFinset_eq_degree]
    by_cases hu : u ∈ S
    · rw [hNlow hu, card_union_of_disjoint]
      · rw [Nat.cast_add, card_neighborFinset_eq_degree, (M u hu).card_entries]
        unfold deficiency
        ring
      · apply Finset.disjoint_left.mpr
        intro w hw hmw
        exact ((M u hu).fresh hmw).2 (mem_neighborFinset_iff.mp hw)
    · rw [hNfull (full_of_not_low h hu), card_neighborFinset_eq_degree]
      exact full_of_not_low h hu
  have hsums (v : V) : (∑ z : V, gap H q z v) = 0 := by
    simp_rw [gap_symm H q _ v]
    rw [gap_row_sum H q h.order v]
    simp only [hregular, mul_zero, sum_const_zero, add_zero]
  have hcomm (z v : V) :
      (∑ w ∈ H.neighborFinset v, gap H q z w) =
        ∑ w ∈ H.neighborFinset z, gap H q w v := by
    have hh := gap_comm H q z v
    simpa only [hregular, sub_self, sub_eq_zero] using hh
  have hfull_nonneg {z v : V} (hz : δ z = 0) (hv : δ v = 0) : 0 ≤ gap H q z v := by
    have he : gap H q z v = gap G q z v := by
      simp only [gap, Matrix.sub_apply, Matrix.add_apply, adj_sq_apply, hNfull hz, hNfull hv]
    rw [he]
    exact gap_nonneg G q h.cap (fun {_ _} he => card_inter_le_one h.free he) z v
  have hmixed_nonpos {z v : V} (hz : δ z = 0) (hv : v ∈ S) : gap H q z v ≤ 0 := by
    have hzv : z ≠ v := fun he => (low_iff.mp hv).ne' (he ▸ hz)
    have hc : ∃ w, H.Adj z w ∧ H.Adj v w := by
      by_cases hu : z ∈ U v
      · have hz' : z ∉ S := by simp [low, hz]
        obtain ⟨w, hw, hzN⟩ := mem_biUnion.mp
          ((M v hv).covers (mem_sdiff.mpr ⟨hu, hz'⟩))
        exact ⟨w, hHadj.mpr (Or.inl (mem_neighborFinset_iff.mp hzN).symm),
          hHadj.mpr (Or.inr ⟨hv, hw⟩)⟩
      · have hc : ∃ w, G.Adj v w ∧ G.Adj z w := by
          by_contra h'
          exact hu ((mem_uncovered G).mpr ⟨hzv.symm, h'⟩)
        obtain ⟨w, hvw, hzw⟩ := hc
        exact ⟨w, hHadj.mpr (Or.inl hzw), hHadj.mpr (Or.inl hvw)⟩
    obtain ⟨w, hzw, hvw⟩ := hc
    have hc := card_pos.mpr
      ⟨w, mem_inter.mpr ⟨mem_neighborFinset_iff.mpr hzw, mem_neighborFinset_iff.mpr hvw⟩⟩
    simp only [gap, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      hzv, ite_false, smul_zero, zero_add, allOnes, Matrix.of_apply, adj_sq_apply]
    omega
  have hperfect {p : V} (hp : Perfect G q p) (z : V) : gap H q p z = 0 := by
    have he : (H.adjMatrix ℤ * H.adjMatrix ℤ) p z =
        (G.adjMatrix ℤ * G.adjMatrix ℤ) p z := by
      rw [adjMatrix_mul_apply, adjMatrix_mul_apply, hNfull hp.1]
      apply sum_congr rfl
      intro w hw
      have hwn := hNfull (hp.2 w (mem_neighborFinset_iff.mp hw))
      simp only [adjMatrix_apply]
      have ha : H.Adj w z ↔ G.Adj w z := by
        rw [← mem_neighborFinset_iff, ← mem_neighborFinset_iff, hwn]
      simp [ha]
    have hgap := gap_zero_of_perfect G q h.order
      (fun {_ _} he => card_inter_le_one h.free he) hp z
    simp only [gap, Matrix.sub_apply, Matrix.add_apply] at hgap ⊢
    rwa [he]
  -- A full neighbor of a perfect vertex also has a zero column.
  have hgood {x p : V} (hp : Perfect G q p) (hpx : G.Adj p x) (z : V) :
      gap H q z x = 0 := by
    have hx := hp.2 x hpx
    have hf (z : V) (hz : δ z = 0) : gap H q z x = 0 := by
      have he := hcomm z p
      simp_rw [gap_symm H q _ p, hperfect hp, sum_const_zero, hNfull hp.1] at he
      have hi := single_le_sum (s := N p) (f := gap H q z)
        (fun t ht => hfull_nonneg hz (hp.2 t (mem_neighborFinset_iff.mp ht)))
        (mem_neighborFinset_iff.mpr hpx)
      exact le_antisymm (he ▸ hi) (hfull_nonneg hz hx)
    have hnonpos (w : V) : gap H q w x ≤ 0 := by
      by_cases hw : w ∈ S
      · rw [gap_symm H q w x]
        exact hmixed_nonpos hx hw
      · rw [hf w (full_of_not_low h hw)]
    have hn := single_le_sum (s := (univ : Finset V)) (f := fun w => -gap H q w x)
      (fun w _ => neg_nonneg.mpr (hnonpos w)) (mem_univ z)
    rw [sum_neg_distrib, hsums x, neg_zero] at hn
    linarith [hnonpos z]
  have hlow_nonneg {z y : V} (hz : z ∈ S) (hy : y ∈ S) : 0 ≤ gap H q z y := by
    obtain ⟨x, hx⟩ := hp y hy
    obtain ⟨p, hpp, hpx⟩ := private_adj_perfect G q h.cap
      (fun {_ _} he => card_inter_le_one h.free he) (low_card_bound h) hx h.positive
    have he := hcomm z x
    simp_rw [hgood hpp hpx, sum_const_zero, hNfull hx.2.1] at he
    have hyN : y ∈ N x := mem_neighborFinset_iff.mpr hx.1.symm
    have hs := sum_erase_add (N x) (gap H q z) hyN
    rw [he] at hs
    have hl : ∑ w ∈ (N x).erase y, gap H q z w ≤ 0 := by
      apply sum_nonpos
      intro w hw
      obtain ⟨hwy, hwN⟩ := mem_erase.mp hw
      have hw' := full_of_not_low h (fun hs => hwy (hx.2.2 w hs (mem_neighborFinset_iff.mp hwN)))
      rw [gap_symm H q z w]
      exact hmixed_nonpos hw' hz
    linarith
  -- A forbidden three-edge path would give two common neighbors in the completion.
  obtain ⟨y, hy⟩ := hS
  have hpos : 0 < (M y hy).entries.card := by
    have h' := (M y hy).card_entries
    have h'' := low_iff.mp hy
    omega
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  obtain ⟨hyw, hn⟩ := (M y hy).fresh hw
  have hwS := (M y hy).low_entries hw
  obtain ⟨a, b, ha, hab, hbw⟩ := optimal_has_three_path
    (by intro u v a b; exact common_neighbor_unique h.free) q
    (fun u => by simpa only [← ncard_neighborSet] using h.cap u) hE hyw hn
    (by simpa only [← ncard_neighborSet] using low_degree_le hy)
    (by simpa only [← ncard_neighborSet] using low_degree_le hwS)
  have hback := missing_row_symm (M y hy) (M w hwS) (hp y hy) hw
  have hbS := path_starts_low h (M w hwS) hback hbw.symm hab.symm ha.symm
  have hyb : y ≠ b := fun he => hn (he.symm ▸ hbw)
  have haw : a ≠ w := fun he => hn (he ▸ ha)
  have hob := hlow_nonneg hy hbS
  simp only [gap, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    hyb, ite_false, smul_zero, zero_add, allOnes, Matrix.of_apply, adj_sq_apply] at hob
  have hc' : (H.neighborFinset y ∩ H.neighborFinset b).card ≤ 1 := by omega
  have ha' : a ∈ H.neighborFinset y ∩ H.neighborFinset b :=
    mem_inter.mpr ⟨mem_neighborFinset_iff.mpr (hHadj.mpr (Or.inl ha)),
      mem_neighborFinset_iff.mpr (hHadj.mpr (Or.inl hab.symm))⟩
  have hw' : w ∈ H.neighborFinset y ∩ H.neighborFinset b :=
    mem_inter.mpr ⟨mem_neighborFinset_iff.mpr (hHadj.mpr (Or.inr ⟨hy, hw⟩)),
      mem_neighborFinset_iff.mpr (hHadj.mpr (Or.inl hbw))⟩
  exact haw (card_le_one.mp hc' a ha' w hw')

omit [DecidableEq V] in
private theorem regular_impossible (h : CappedSetup G q) (hq : IsPrimePow q)
    (h0 : ∀ v, δ v = 0) : False := by
  classical
  obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let A := G.adjMatrix (ZMod p)
  let J := allOnes V (ZMod p)
  have hq0 : (q : ZMod p) = 0 := by
    rw [← hpow, Nat.cast_pow, ZMod.natCast_self, zero_pow hk.ne']
  have hn : (Fintype.card V : ZMod p) = 1 := by
    simp [h.order, hq0]
  have hd (v : V) : G.degree v = q + 1 := by have hh := h0 v; unfold deficiency at hh; omega
  have hdz (v : V) : (G.degree v : ZMod p) = 1 := by simp [hd, hq0]
  have hAA : A * A = J := by
    ext v w
    rcases eq_or_ne v w with rfl | hvw
    · rw [show (A * A) v v = (G.degree v : ZMod p) from adjMatrix_mul_self_apply_self ..]
      exact hdz v
    · change (G.adjMatrix (ZMod p) * G.adjMatrix (ZMod p)) v w = 1
      rw [adj_sq_apply]
      have hu := uncovered_card G q h.order (fun {_ _} he => card_inter_le_one h.free he) v
      simp only [h0, sum_const_zero, mul_zero, add_zero] at hu
      have he : U v = ∅ := card_eq_zero.mp (by exact_mod_cast hu)
      have hc : ∃ a, G.Adj v a ∧ G.Adj w a := by
        by_contra! hno
        have hw : w ∈ U v := (mem_uncovered G).mpr ⟨hvw, fun ⟨a, ha, hwa⟩ => hno a ha hwa⟩
        simp [he] at hw
      obtain ⟨a, hva, hwa⟩ := hc
      have hpos : 0 < (N v ∩ N w).card :=
        card_pos.mpr
          ⟨a, mem_inter.mpr ⟨mem_neighborFinset_iff.mpr hva, mem_neighborFinset_iff.mpr hwa⟩⟩
      have hone : (N v ∩ N w).card ≤ 1 := card_inter_le_one h.free hvw
      rw [show (N v ∩ N w).card = 1 by omega, Nat.cast_one]
  have hAJ : A * J = J := by
    ext v w
    simp only [A, adjMatrix_mul_apply, J, allOnes, Matrix.of_apply, sum_const, nsmul_eq_mul,
      mul_one, card_neighborFinset_eq_degree, hdz]
  have hJA : J * A = J := by
    ext v w
    simp only [A, mul_adjMatrix_apply, J, allOnes, Matrix.of_apply, sum_const, nsmul_eq_mul,
      mul_one, card_neighborFinset_eq_degree, hdz]
  have hJJ : J * J = J := by
    ext v w
    simp only [J, Matrix.mul_apply, allOnes, Matrix.of_apply, sum_const, nsmul_eq_mul,
      mul_one, card_univ, hn]
  have hnil : IsNilpotent (A - J) := ⟨2, by
    simp only [pow_two, sub_mul, mul_sub, hAA, hAJ, hJA, hJJ, sub_self]⟩
  have he := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [trace_sub] at he
  have hJ : Matrix.trace J = 1 := by
    simp only [Matrix.trace, Matrix.diag, J, allOnes, Matrix.of_apply, sum_const,
      nsmul_eq_mul, card_univ, mul_one, hn]
  unfold A at he
  rw [trace_adjMatrix, hJ, zero_sub, neg_eq_zero] at he
  exact one_ne_zero he

omit [DecidableEq V] in
open scoped Classical in
private theorem capped_impossible (h : CappedSetup G q) (hq : IsPrimePow q)
    (hE : EdgeOptimal q G) (hD : SquareOptimal q G) : False := by
  rcases Nat.even_or_odd q with hEven | hOdd
  · obtain ⟨p, hp⟩ := perfect_exists h
    have hu := uncovered_card G q h.order (fun {_ _} he => card_inter_le_one h.free he) p
    have hzero : (∑ u ∈ N p, δ u) = 0 :=
      sum_eq_zero fun v hv => hp.2 v (mem_neighborFinset_iff.mp hv)
    rw [hp.1, mul_zero, hzero, zero_add] at hu
    have hpEven := empty_uncovered_even h.free (by exact_mod_cast hu)
    have hpdeg := hp.1
    unfold deficiency at hpdeg
    obtain ⟨a, ha⟩ := hEven
    obtain ⟨b, hb⟩ := hpEven
    omega
  · by_cases hS : (S).Nonempty
    · exact odd_capped_nonempty_impossible h hOdd hE hD hS
    · exact regular_impossible h hq (fun v => full_of_not_low h (fun hv => hS ⟨v, hv⟩))

end Capped

open scoped Classical in
private theorem sharp_upper (q : ℕ) (hq : IsPrimePow q) (h13 : 13 < q) :
    extremalNumber (q ^ 2 + q + 1) (cycleGraph 4) ≤ q * (q + 1) ^ 2 / 2 := by
  classical
  rw [← Fintype.card_fin (q ^ 2 + q + 1), extremalNumber_le_iff]
  intro G _ hG
  by_contra! hE
  have even_prod : Even (q * (q + 1) ^ 2) := by
    have he : Even (q * (q + 1)) := by
      rcases Nat.even_or_odd q with h | h
      · exact h.mul_right _
      · exact (h.add_odd odd_one).mul_left _
    simpa [pow_two, mul_assoc] using he.mul_right (q + 1)
  have hd : (q : ℤ) * (q + 1) ^ 2 + 2 ≤ 2 * (G.edgeFinset.card : ℤ) := by
    obtain ⟨r, hr⟩ := even_prod
    have hh : 2 * (r : ℤ) = (q : ℤ) * (q + 1) ^ 2 := by exact_mod_cast (by omega : 2 * r = _)
    omega
  have hc := no_high_degree q h13 (Fintype.card_fin _) hG hd
  obtain ⟨H, hHfree, hHcap, he, hEdge, hSq⟩ := exists_optimals q G hG (fun v => by
    simpa only [← ncard_neighborSet] using hc v)
  have hHedges : (q : ℤ) * (q + 1) ^ 2 + 2 ≤ 2 * (H.edgeFinset.card : ℤ) := by
    simp only [← edges_ncard] at he hd ⊢
    omega
  have hData : CappedSetup H q := ⟨by omega, Fintype.card_fin _, hHfree, hHcap,
    sum_deficiency_le q (Fintype.card_fin _) hHedges⟩
  exact capped_impossible hData hq hEdge hSq

open _root_.SimpleGraph in
/-- **Füredi's theorem on four-cycle-free graphs.** For a natural number $n$, let
$\mathrm{ex}(n; C_4)$ be the largest number of edges of a simple graph on $n$ vertices that
contains no four-cycle $C_4$ as a (not necessarily induced) subgraph. For every prime power
$q > 13$, $\mathrm{ex}(q^2 + q + 1; C_4) = q (q + 1)^2 / 2$; the division is exact because
$q (q + 1)$ is even.

The bound is attained by the polarity graph of the projective plane of order $q$.

Source: Z. Füredi, *On the number of edges of quadrilateral-free graphs*,
J. Combin. Theory Ser. B 68 (1996), 1–6; listed in SqueezeBench
`SqueezeBench/Problems/ExC4/README.md`. -/
public theorem extremalNumber_cycleGraph_four_projectivePlane_order
    (q : ℕ) (hq : IsPrimePow q) (h13 : 13 < q) :
    extremalNumber (q ^ 2 + q + 1) (cycleGraph 4) = q * (q + 1) ^ 2 / 2 :=
  le_antisymm (sharp_upper q hq h13) (sharp_lower q hq)

end MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted
