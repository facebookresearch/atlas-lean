/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SimonLiebSelfImprovement

/-!
# The Simon–Lieb inequality from random-current backbones

First exits of walks and random-current backbones from a set, the Simon weight, and the reduction of
the Simon–Lieb inequality to a first-exit bound.

## i. Overview

A walk from `o ∈ S` to `z ∉ S` has a first step leaving `S`; for the backbone of a random current
that step uses an edge with odd current. Conditioning on this edge and on the restriction of the
current to `S` produces the Simon–Lieb bound `⟨σ_oσ_z⟩ ≤ ∑_{x ∈ S, y ∉ S} tanh(βJ_{xy}) ⟨σ_oσ_x⟩_S
⟨σ_yσ_z⟩`. The weight `tanh(βJ_{xy}) ⟨σ_oσ_x⟩_S` is `simonWeight`, and `simonLieb_of_firstExit`
packages a bound of this form as the structure `SimonLieb`.

## ii. Key results

- `walk_firstExit` : first exit of a walk from a set
- `backbone_firstExit` : first exit of a backbone along an odd edge
- `simonWeight` : the Simon weight `tanh(βJ_{xy}) ⟨σ_oσ_x⟩_S`
- `simonLieb_of_firstExit` : packaging a first-exit bound as `SimonLieb`

## iii. Table of contents

- A. First exits
- B. The Simon weight
- C. Reduction to a first-exit bound

## iv. References

- B. Simon, "Correlation inequalities and the decay of correlations in ferromagnets", Comm. Math.
  Phys. 77 (1980) 111–126
- E. H. Lieb, "A refinement of Simon's correlation inequality", Comm. Math. Phys. 77 (1980) 127–135
- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48

-/

@[expose] public section

open SimpleGraph Finset
open scoped BigOperators


namespace StatMech

namespace Sharpness

section FirstExit

variable {V : Type*} {G : SimpleGraph V}

/-! ## A. First exits -/

lemma walk_firstExit {o z : V} (w : G.Walk o z) (S : Finset V) (ho : o ∈ S) (hz : z ∉ S)
    [DecidablePred (fun i => w.getVert i ∉ S)] :
    ∃ k, 1 ≤ k ∧ k ≤ w.length ∧
      w.getVert k ∉ S ∧ w.getVert (k - 1) ∈ S ∧
      G.Adj (w.getVert (k - 1)) (w.getVert k) ∧
      (∀ j < k, w.getVert j ∈ S) := by
  classical
  have hlen : w.getVert w.length ∉ S := by rw [w.getVert_length]; exact hz
  have hex : ∃ i, w.getVert i ∉ S := ⟨w.length, hlen⟩
  have hspec : w.getVert (Nat.find hex) ∉ S := Nat.find_spec hex
  have hkpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · exact absurd (by rw [h0, w.getVert_zero]; exact ho) hspec
    · exact h0
  have hkle : Nat.find hex ≤ w.length := Nat.find_le hlen
  have hprev : ∀ j < Nat.find hex, w.getVert j ∈ S :=
    fun j hj => not_not.mp (Nat.find_min hex hj)
  have hadj : G.Adj (w.getVert (Nat.find hex - 1)) (w.getVert (Nat.find hex)) := by
    have heq : (Nat.find hex - 1) + 1 = Nat.find hex := by omega
    have h := w.adj_getVert_succ (i := Nat.find hex - 1) (by omega)
    rwa [heq] at h
  exact ⟨Nat.find hex, hkpos, hkle, hspec, hprev (Nat.find hex - 1) (by omega), hadj, hprev⟩

end FirstExit

section BackboneFirstExit

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma backbone_getVert_odd {n : Current V} {a b : V} (p : IsBackbonePath G n a b)
    {i : ℕ} (hi : i < p.1.length) :
    G.Adj (p.1.getVert i) (p.1.getVert (i + 1)) ∧
      Odd (n s(p.1.getVert i, p.1.getVert (i + 1))) := by
  have hadj := p.1.adj_getVert_succ hi
  rw [oddSubgraph_adj] at hadj
  exact hadj

lemma backbone_firstExit {n : Current V} {o z : V} (p : IsBackbonePath G n o z)
    (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ p.1.length ∧
      p.1.getVert (k - 1) ∈ S ∧ p.1.getVert k ∉ S ∧
      s(p.1.getVert (k - 1), p.1.getVert k) ∈ G.edgeFinset ∧
      Odd (n s(p.1.getVert (k - 1), p.1.getVert k)) ∧
      1 ≤ n s(p.1.getVert (k - 1), p.1.getVert k) ∧
      (∀ j < k, p.1.getVert j ∈ S) := by
  classical
  obtain ⟨k, hk1, hkle, hyk, hxk, hadj, hprev⟩ :=
    walk_firstExit (G := oddSubgraph G n) p.1 S ho hz
  have heq : (k - 1) + 1 = k := by omega
  have hmem : s(p.1.getVert (k - 1), p.1.getVert k) ∈ G.edgeFinset := by
    have hadjG : G.Adj (p.1.getVert (k - 1)) (p.1.getVert k) := oddSubgraph_le G n hadj
    rw [mem_edgeFinset, mem_edgeSet]; exact hadjG
  have hodd : Odd (n s(p.1.getVert (k - 1), p.1.getVert k)) := by
    have h := (backbone_getVert_odd G p (i := k - 1) (by omega)).2
    rwa [heq] at h
  exact ⟨k, hk1, hkle, hxk, hyk, hmem, hodd, hodd.pos, hprev⟩

lemma backbone_firstExit_crossing {n : Current V} {o z : V} (p : IsBackbonePath G n o z)
    (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ s(x, y) ∈ G.edgeFinset ∧ 1 ≤ n s(x, y) := by
  obtain ⟨k, _, _, hx, hy, he, _, hpos, _⟩ := backbone_firstExit G p S ho hz
  exact ⟨p.1.getVert (k - 1), p.1.getVert k, hx, hy, he, hpos⟩

end BackboneFirstExit

section SimonWeight

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. The Simon weight -/

/-- The Simon weight `w(x, y) = tanh(βJ_{xy}) ⟨σ_oσ_x⟩_{J|S}`. -/
noncomputable def simonWeight (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V) :
    V → V → ℝ :=
  fun x y => Real.tanh (β * J s(x, y)) * expectationJ G β (couplingIn J S) {o, x}

lemma tanh_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  refine div_nonneg ?_ (Real.cosh_pos t).le
  rw [show (0 : ℝ) = Real.sinh 0 from by simp]
  exact Real.sinh_le_sinh.mpr ht

lemma simonWeight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e)
    (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x}) :
    ∀ x y, 0 ≤ simonWeight G β J S o x y := by
  intro x y
  unfold simonWeight
  exact mul_nonneg (tanh_nonneg (mul_nonneg hβ (hJ _))) (hcorr x)

end SimonWeight

section Reduction

variable {V : Type*}

/-! ## C. Reduction to a first-exit bound -/

lemma simonLieb_of_firstExit (τ : V → V → ℝ) (o : V) (S : Finset V)
    (simWeight : V → V → ℝ) (boundaryTargets : Finset V)
    (hτ : ∀ a b, 0 ≤ τ a b) (hw : ∀ x y, 0 ≤ simWeight x y)
    (hbound : ∀ z, z ∉ S →
      τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets, simWeight x y * τ y z) :
    SimonLieb τ o S simWeight boundaryTargets where
  τ_nonneg := hτ
  weight_nonneg := hw
  simon := hbound

lemma simonLieb_simonWeight [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V) (boundaryTargets : Finset V)
    (τ : V → V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x})
    (hτ : ∀ a b, 0 ≤ τ a b)
    (hbound : ∀ z, z ∉ S →
      τ o z ≤ ∑ x ∈ S, ∑ y ∈ boundaryTargets,
        simonWeight G β J S o x y * τ y z) :
    SimonLieb τ o S (simonWeight G β J S o) boundaryTargets :=
  simonLieb_of_firstExit τ o S (simonWeight G β J S o) boundaryTargets hτ
    (simonWeight_nonneg G β J S o hβ hJ hcorr) hbound

lemma simonConst_simonWeight_nonneg [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V)
    (boundaryTargets : Finset V) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hcorr : ∀ x, 0 ≤ expectationJ G β (couplingIn J S) {o, x}) :
    0 ≤ simonConst S (simonWeight G β J S o) boundaryTargets :=
  simonConst_nonneg S (simonWeight G β J S o) boundaryTargets
    (simonWeight_nonneg G β J S o hβ hJ hcorr)

end Reduction

end Sharpness

end StatMech
