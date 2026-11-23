/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.GHSVertexPartition

/-!
# Vertex-partition weights with inhomogeneous couplings

The subset weights of `GHSVertexPartition` for edge-dependent couplings and site-dependent fields.

## i. Overview

For couplings `K_e ≥ 0` and fields `h_x ≥ 0`, the weight of an agreement set `A` in the duplicated
system is `4 T(A) U(Aᶜ)`, where `T(A)` is the partition function of the subgraph induced by `A` with
couplings `2K` and fields `2h` and `U` is the zero-field partition function with couplings `2K`. It
is log-supermodular in `A` (the FKG lattice condition).

## ii. Key results

- `StatMech.Ising.ghsiSubsetMass` : the inhomogeneous subset weight
- `StatMech.Ising.ghsiSubsetMass_eq_four_mul_tZ_uZ` : its product form
- `StatMech.Ising.ghsiSubsetMass_logSupermodular` : the FKG lattice condition

## iii. Table of contents

- A. Ghost-vertex couplings
- B. Factorization
- C. The subset weight

## iv. References

- J. L. Lebowitz, *GHS and other inequalities*, Comm. Math. Phys. 35 (1974) 87–92
- R. S. Ellis, J. L. Monroe and C. M. Newman, *The GHS and other correlation inequalities for a
  class of even ferromagnets*, Comm. Math. Phys. 46 (1976) 167–182
-/

@[expose] public section

open Finset Classical


namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A. Ghost-vertex couplings -/

/-- The ghost-vertex couplings: `2K_{xy}` on an edge `{x, y}`, `2h_x` between `x` and the ghost. -/
noncomputable def ghsiGhostCoupling (K : Sym2 V → ℝ) (hf : V → ℝ)
    (e : Sym2 (Option V)) : ℝ :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | some x, some y => 2 * K s(x, y)
    | some x, none => 2 * hf x
    | none, some y => 2 * hf y
    | none, none => 0,
    by rintro (_ | x) (_ | y) <;> simp only [] <;> rw [Sym2.eq_swap]⟩ e

omit [Fintype V] [DecidableEq V] in
@[simp] lemma ghsiGhostCoupling_some_some (K : Sym2 V → ℝ) (hf : V → ℝ)
    (x y : V) :
    ghsiGhostCoupling K hf s(some x, some y) = 2 * K s(x, y) := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma ghsiGhostCoupling_some_none (K : Sym2 V → ℝ) (hf : V → ℝ)
    (x : V) :
    ghsiGhostCoupling K hf s(some x, none) = 2 * hf x := rfl

/-- The partition function of the subgraph induced by `A` with couplings `2K` and fields `2h` on
`A`. -/
noncomputable def ghsiTZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) : ℝ :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e)
    (fun x => if x ∈ A then 2 * hf x else 0)

/-- The zero-field partition function of the subgraph induced by `A` with couplings `2K`. -/
noncomputable def ghsiUZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e) (fun _ => 0)

/-! ## B. Factorization -/

lemma ghsi_fieldSet_couplingSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V)
    (s : ConfigSpace (Option V)) :
    (∑ e ∈ ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A),
        ghsiGhostCoupling K hf e * bond s e) =
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset A,
          (2 * K e) * bond (fun x => s (some x)) e) +
        spin s none * ∑ x ∈ A, (2 * hf x) * spin s (some x) := by
  unfold ghsvp_vertexEdges
  rw [FieldGhostDict.withGhost_edgeFinset_eq, Finset.filter_union,
    ghsvp_origEdges_filter_fieldSet, ghsvp_ghostEdges_filter_fieldSet]
  have hdisj : Disjoint
      ((ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some))
      (A.image (fun x => s(some x, none))) := by
    apply (FieldGhostDict.disjoint_orig_ghost G).mono
    · intro e he
      exact Finset.mem_filter.mp (by
        rw [ghsvp_origEdges_filter_fieldSet]
        exact he) |>.1
    · intro e he
      exact Finset.mem_filter.mp (by
        rw [ghsvp_ghostEdges_filter_fieldSet]
        exact he) |>.1
  rw [Finset.sum_union hdisj]
  congr 1
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e _
      induction e with
      | h x y =>
        rw [Sym2.map_mk, ghsiGhostCoupling_some_some, bond_mk, bond_mk]
        rfl
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective V) hab
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [ghsiGhostCoupling_some_none, bond_mk]
      ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with h | h
      · exact Option.some_injective V h.1
      · exact absurd h.2 (by simp)

lemma ghsi_fieldSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V)
    (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
        (ghsiGhostCoupling K hf) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e)
        (fun x => if x ∈ A then (2 * hf x) * spin s none else 0)
        (fun x => s (some x)) := by
  unfold wJ
  rw [ghsi_fieldSet_couplingSum]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  congr 2
  rw [Finset.mul_sum]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [Finset.filter_univ_mem]
  simp only [spin]
  ring_nf

lemma ghsi_someSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V)
    (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
        (ghsiGhostCoupling K hf) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e) (fun _ => 0)
        (fun x => s (some x)) := by
  have hedges :
      ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A) =
        (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
    unfold ghsvp_vertexEdges
    rw [FieldGhostDict.withGhost_edgeFinset_eq, Finset.filter_union,
      ghsvp_origEdges_filter_someSet, ghsvp_ghostEdges_filter_someSet]
    simp [ghsvp_vertexEdges]
  unfold wJ
  rw [hedges, Finset.sum_image]
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    congr 2
    funext e
    induction e with
    | h x y =>
      rw [Sym2.map_mk, ghsiGhostCoupling_some_some, bond_mk, bond_mk]
      rfl
  · intro a _ b _ hab
    exact Sym2.map.injective (Option.some_injective V) hab

lemma ghsi_vertexZ_fieldSet_eq_two_mul_tZ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
        (ghsvp_fieldSet A) = 2 * ghsiTZ G K hf A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have htrue :
      (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec true tau z)) = ghsiTZ G K hf A := by
    unfold ghsiTZ ZJ
    apply Finset.sum_congr rfl
    intro tau _
    rw [ghsi_fieldSet_weight_eq]
    congr 2
    funext x
    simp
  have hfalse :
      (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec false tau z)) = ghsiTZ G K hf A := by
    rw [show (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec false tau z)) =
        ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun e => 2 * K e)
          (fun x => -(if x ∈ A then 2 * hf x else 0)) by
      unfold ZJ
      apply Finset.sum_congr rfl
      intro tau _
      rw [ghsi_fieldSet_weight_eq]
      congr 2
      funext x
      by_cases hx : x ∈ A <;> simp [hx]]
    rw [ghsvp_ZJ_negField]
    rfl
  rw [htrue, hfalse]
  ring

lemma ghsi_vertexZ_someSet_eq_two_mul_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
        (ghsvp_someSet A) = 2 * ghsiUZ G K A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have hb : ∀ b : Bool,
      (∑ tau : V → Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
          (ghsiGhostCoupling K hf) (fun _ => 0)
          (fun z => Option.rec b tau z)) = ghsiUZ G K A := by
    intro b
    unfold ghsiUZ ZJ
    apply Finset.sum_congr rfl
    intro tau _
    exact ghsi_someSet_weight_eq G K hf A (fun z => Option.rec b tau z)
  rw [hb, hb]
  ring

/-! ## C. The subset weight -/

/-- The weight of the agreement set `A` in the duplicated inhomogeneous system. -/
noncomputable def ghsiSubsetMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) : ℝ :=
  ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
      (ghsvp_fieldSet A) *
    ghsvp_vertexZ (withGhost G).edgeFinset (ghsiGhostCoupling K hf)
      (ghsvp_someSet Aᶜ)

lemma ghsiSubsetMass_eq_four_mul_tZ_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    ghsiSubsetMass G K hf A = 4 * (ghsiTZ G K hf A * ghsiUZ G K Aᶜ) := by
  unfold ghsiSubsetMass
  rw [ghsi_vertexZ_fieldSet_eq_two_mul_tZ,
    ghsi_vertexZ_someSet_eq_two_mul_uZ]
  ring

lemma ghsiSubsetMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ) (A : Finset V) :
    0 ≤ ghsiSubsetMass G K hf A := by
  unfold ghsiSubsetMass
  exact mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le

lemma ghsiSubsetMass_logSupermodular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x) (A B : Finset V) :
    ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf B ≤
      ghsiSubsetMass G K hf (A ∪ B) * ghsiSubsetMass G K hf (A ∩ B) := by
  let J2 : Sym2 (Option V) → ℝ := ghsiGhostCoupling K hf
  have hJ2 : ∀ e, 0 ≤ J2 e := by
    intro e
    induction e with
    | h a b =>
      rcases a with _ | a <;> rcases b with _ | b <;>
        simp [J2, ghsiGhostCoupling, hK, hhf]
  have hnd : ∀ e ∈ (withGhost G).edgeFinset, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeFinset he
  have hp := ghsvp_vertexZ_logSupermodular (withGhost G).edgeFinset J2 hJ2 hnd
    (ghsvp_fieldSet A) (ghsvp_fieldSet B)
  have hz := ghsvp_vertexZ_logSupermodular (withGhost G).edgeFinset J2 hJ2 hnd
    (ghsvp_someSet Aᶜ) (ghsvp_someSet Bᶜ)
  rw [← ghsvp_fieldSet_union, ← ghsvp_fieldSet_inter] at hp
  have hcu : Aᶜ ∪ Bᶜ = (A ∩ B)ᶜ := by ext x; simp
  have hci : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by ext x; simp
  rw [← ghsvp_someSet_union, ← ghsvp_someSet_inter, hcu, hci] at hz
  unfold ghsiSubsetMass
  change
    (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet A) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Aᶜ)) *
      (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet B) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Bᶜ)) ≤ _
  have hnon1 :
      0 ≤ ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∪ B)) :=
    (ZJ_pos _ _ _).le
  have hnon2 :
      0 ≤ ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∩ B)) :=
    (ZJ_pos _ _ _).le
  have hprod := mul_le_mul hp hz
    (mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le)
    (mul_nonneg hnon1 hnon2)
  nlinarith [hprod]

end StatMech.Ising
