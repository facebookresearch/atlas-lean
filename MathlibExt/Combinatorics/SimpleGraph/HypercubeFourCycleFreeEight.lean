/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/HypercubeC4/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The theorem statement uses the hypercube extremal problem from the “Known values” section at
commit e2e19eef093a77882da57f348def029533ec2d5e, with the bound raised from 680 to 682
following Minamoto.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal

/-!
# A four-cycle-free subgraph of the eight-cube with 682 edges

We use the signed cube construction of M. Minamoto, arXiv:2603.29127v5, §6.3.
A 256-bit word assigns a Boolean spin to each vertex. We retain an edge in direction `i`
when the XOR of its endpoint spins equals the parity of the bits below `i` in either endpoint.
The word below retains 682 edges.

Around a square each vertex spin occurs twice. Flipping the smaller coordinate changes the
parity in the larger direction, so the four edge conditions cannot all hold. The resulting
four-cycle-free subgraph gives the lower bound on the extremal number.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

private abbrev Vertex := BitVec 8

private def flip (x : Vertex) (i : Fin 8) := x ^^^ BitVec.twoPow 8 i

private theorem bit_flip (x : Vertex) (i : Fin 8) (j : ℕ) :
    (flip x i).getLsbD j = (x.getLsbD j ^^ decide (i.val = j)) := by
  simp [flip, BitVec.getLsbD_twoPow, i.isLt]

private theorem flip_flip (x : Vertex) (i : Fin 8) : flip (flip x i) i = x := by
  simp [flip, BitVec.xor_assoc]

private theorem flip_comm (x : Vertex) (i j : Fin 8) : flip (flip x i) j = flip (flip x j) i := by
  simp only [flip, BitVec.xor_assoc]
  rw [BitVec.xor_comm (BitVec.twoPow 8 i)]

private theorem flip_injective (x : Vertex) : Function.Injective (flip x) := by
  intro i j h
  by_contra hij
  have hbit := congrArg (fun y : Vertex => y.getLsbD i) h
  simp only [bit_flip] at hbit
  simp [Fin.val_ne_of_ne (Ne.symm hij)] at hbit

-- The parity of the bits strictly below direction j.
private def lowerParity (x : Vertex) : ℕ → Bool
  | 0 => false
  | j + 1 => lowerParity x j ^^ x.getLsbD j

private theorem lowerParity_flip (x : Vertex) (i : Fin 8) (j : ℕ) :
    lowerParity (flip x i) j = (lowerParity x j ^^ decide (i.val < j)) := by
  induction j with
  | zero => simp [lowerParity]
  | succ j ih =>
    simp only [lowerParity, ih, bit_flip]
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · simp [h, h.ne, Nat.lt_succ_of_lt h, Bool.xor_comm]
    · simp [h, Bool.xor_comm]
    · simp [h.not_gt, h.ne', Nat.not_lt.mpr h]

-- Bit x of the certificate is the spin at vertex x, with the least significant bit first.
private def spin (x : Vertex) : Bool :=
  (0x53c726f0f1ff8f6873d9388f273242fc068c7f02f82c17808f1fece871772c72 : ℕ).testBit x.toNat

private def retained (x : Vertex) (i : Fin 8) : Prop :=
  (spin x ^^ spin (flip x i)) = lowerParity x i

private instance retainedDecidable (x : Vertex) (i : Fin 8) : Decidable (retained x i) :=
  inferInstanceAs (Decidable (_ = _))

private theorem retained_flip (x : Vertex) (i : Fin 8) :
    retained (flip x i) i ↔ retained x i := by
  simp [retained, flip_flip, lowerParity_flip, Bool.xor_comm]

private def witness : SimpleGraph Vertex where
  Adj x y := ∃ i, y = flip x i ∧ retained x i
  symm := ⟨by
    rintro x _ ⟨i, rfl, h⟩
    exact ⟨i, (flip_flip x i).symm, (retained_flip x i).2 h⟩⟩
  loopless := ⟨by
    rintro x ⟨i, h, -⟩
    have hbit := congrArg (fun y : Vertex => y.getLsbD i) h
    simp only [bit_flip] at hbit
    simp at hbit⟩

private def inCube : witness.Copy (hypercubeGraph 8) where
  toHom := {
    toFun := fun x i => x.getLsbD i
    map_rel' := by
      rintro x _ ⟨i, rfl, -⟩
      rw [hypercubeGraph_adj]
      refine ⟨i, by simp only [bit_flip]; simp, ?_⟩
      intro j h
      by_contra hji
      simp only [bit_flip] at h
      simp [Fin.val_ne_of_ne (Ne.symm hji)] at h }
  injective' := fun _ _ h => BitVec.eq_of_getLsbD_eq fun i hi => congrFun h ⟨i, hi⟩

-- On a square, flipping the smaller coordinate reverses the larger coordinate's sign.
-- The four spins occur twice apiece, so they cannot cancel this one sign change.
private theorem square_missing (x : Vertex) {i j : Fin 8} (hij : i ≠ j)
    (hi : retained x i) (hj : retained x j)
    (hij' : retained (flip x i) j) (hji' : retained (flip x j) i) : False := by
  have parity : ∀ {a b c d p q u v : Bool}, u ≠ v →
      (a ^^ b) = p → (a ^^ c) = q → (b ^^ d) = (q ^^ u) → (c ^^ d) = (p ^^ v) → False := by
    decide
  simp only [retained, lowerParity_flip] at hi hj hij' hji'
  rw [flip_comm x j i] at hji'
  refine parity ?_ hi hj hij' hji'
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h <;> simp [h, h.not_gt]

private theorem witness_free : (cycleGraph 4).Free witness := by
  rintro ⟨f⟩
  have edge (a b : Fin 4) (hab : (cycleGraph 4).Adj a b) := f.toHom.map_adj hab
  obtain ⟨i, h1, hi⟩ := edge 0 1 (by decide)
  obtain ⟨j, h3, hj⟩ := edge 0 3 (by decide)
  obtain ⟨k, h2, hk⟩ := edge 1 2 (by decide)
  obtain ⟨l, h2', hl⟩ := edge 3 2 (by decide)
  rw [h1] at h2 hk
  rw [h3] at h2' hl
  have hij : i ≠ j := by
    rintro rfl
    exact (by decide : (1 : Fin 4) ≠ 3) (f.injective (h1.trans h3.symm))
  have hki : k ≠ i := by
    rintro rfl
    rw [flip_flip] at h2
    exact (by decide : (2 : Fin 4) ≠ 0) (f.injective h2)
  -- The two paths to vertex 2 must flip the same pair of coordinates in opposite orders.
  have diagonal := h2.symm.trans h2'
  have hli : l = i := by
    by_contra h
    have he := congrArg (fun y : Vertex => y.getLsbD i) diagonal
    simp only [bit_flip] at he
    simp [Fin.val_ne_of_ne hki, Fin.val_ne_of_ne hij.symm, Fin.val_ne_of_ne h] at he
  subst l
  rw [flip_comm _ j i] at diagonal
  obtain rfl := flip_injective _ diagonal
  exact square_missing _ hij hi hj hk hl

-- Record each retained edge at the endpoint with smaller vertex number.
private def codes : Finset (Fin 256 × Fin 8) :=
  Finset.univ.filter fun (v, i) =>
    let x := BitVec.ofFin v
    x.toNat < (flip x i).toNat ∧ retained x i

set_option maxRecDepth 4096 in
private theorem card_codes : codes.card = 682 := by decide +kernel

private def edgeOfCode (p : Fin 256 × Fin 8) : Sym2 Vertex :=
  s(BitVec.ofFin p.1, flip (BitVec.ofFin p.1) p.2)

private theorem mem_codes (v : Fin 256) (i : Fin 8) :
    (v, i) ∈ codes ↔ (BitVec.ofFin v : Vertex).toNat < (flip (BitVec.ofFin v) i).toNat ∧
      retained (BitVec.ofFin v) i := by
  simp only [codes, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxRecDepth 4096 in
private theorem count_le : 682 ≤ witness.edgeSet.ncard := by
  rw [← card_codes, ← Set.ncard_coe_finset]
  let : Finite Vertex := Finite.of_injective _ inCube.injective
  apply Set.ncard_le_ncard_of_injOn (s := (codes : Set _)) edgeOfCode
  · rintro ⟨v, i⟩ hv
    exact ⟨i, rfl, ((mem_codes v i).mp hv).2⟩
  · rintro ⟨v, i⟩ hv ⟨w, j⟩ hw heq
    obtain ⟨hlt, -⟩ := (mem_codes v i).mp hv
    obtain ⟨hlt', -⟩ := (mem_codes w j).mp hw
    rcases Sym2.eq_iff.mp heq with ⟨h, h'⟩ | ⟨h, h'⟩
    · have hvw : v = w := congrArg BitVec.toFin h
      subst w
      obtain rfl := flip_injective _ h'
      rfl
    · have hback := (congrArg BitVec.toNat h').trans_lt
        (hlt'.trans_eq (congrArg BitVec.toNat h.symm))
      exact (hlt.asymm hback).elim

/-- **Lower bound for four-cycle-free subgraphs of the eight-dimensional hypercube.** Let $Q_8$
be the $8$-dimensional hypercube and $C_4$ the cycle on four vertices. The largest number
$\mathrm{ex}(Q_8, C_4)$ of edges of a subgraph of $Q_8$ that contains no copy of $C_4$ is at
least $682$.

The bound is witnessed by an explicit construction.

Source: M. Minamoto, *C₄-free subgraphs of the hypercubes Q₆, Q₇, and Q₈*,
arXiv:2603.29127v5 (2026), which improves the bound `680` of its earlier
versions; SqueezeBench `SqueezeBench/Problems/HypercubeC4/README.md` and OEIS
A245762 still list `680`. -/
public theorem le_hypercubeTuranNumber_eight_cycleGraph_four :
    682 ≤ hypercubeTuranNumber 8 (cycleGraph 4) := by
  have hfree := (free_congr_right inCube.isoToSubgraph).mp witness_free
  apply le_trans _ (le_hypercubeTuranNumber 8 inCube.toSubgraph hfree)
  rw [Copy.toSubgraph, Subgraph.edgeSet_map, Subgraph.edgeSet_top,
    Set.ncard_image_of_injective _ (Sym2.map.injective inCube.injective)]
  exact count_le

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
