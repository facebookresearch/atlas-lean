/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import PhyslibExt.CondensedMatter.IsingModel.Gibbs

/-!
# High- and low-temperature expansions of the Ising partition function

Even subgraphs, the high-temperature expansion of `Z`, and duality of partition functions from a
contour matching.

## i. Overview

At zero field, `exp (β σ_xσ_y) = cosh β (1 + tanh β · σ_xσ_y)`, so the partition function on a
finite graph is `Z(β) = 2^{|V|} (cosh β)^{|E|} ∑_{F even} (tanh β)^{|F|}`, the sum over even
subgraphs `F` (every vertex has even degree in `F`). If this sum for `Gd` at `β*` matches, up to a
constant `c`, the partition function of `Gp` at `β` (`DualContourMatching`), the two partition
functions are proportional.

## ii. Key results

- `StatMech.Ising.incCount` : the degree of a vertex in an edge set
- `StatMech.Ising.IsEvenSubgraph` : even subgraphs
- `StatMech.Ising.isingZ_high_temp_expansion` : the high-temperature expansion
- `StatMech.Ising.isingZ_self_dual` : duality under the matching hypothesis
- `StatMech.Ising.DualContourMatching` : the matching hypothesis
- `StatMech.Ising.isingZ_self_dual_proportional` : proportional partition functions

## iii. Table of contents

- A. Expansion of the Boltzmann weight
- B. Even subgraphs
- C. The high-temperature expansion
- D. Duality from a contour matching

## iv. References

- H. A. Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys.
  Rev. 60 (1941) 252–262
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Section 3.7
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

section HighTemp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Expansion of the Boltzmann weight -/

lemma exp_mul_eq_cosh_mul (β b : ℝ) (hb : b = 1 ∨ b = -1) :
    Real.exp (β * b) = Real.cosh β * (1 + Real.tanh β * b) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rcases hb with h | h
  · subst h
    rw [mul_one]; field_simp; rw [← Real.cosh_add_sinh]
  · subst h
    rw [show β * (-1) = -β by ring, Real.exp_neg]
    field_simp
    rw [show Real.cosh β + -Real.sinh β = Real.cosh β - Real.sinh β by ring,
      Real.cosh_sub_sinh, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

omit [DecidableEq V] in
lemma isingWeight_field_free_eq_prod (β : ℝ) (s : ConfigSpace V) :
    isingWeight G β 0 s = ∏ e ∈ G.edgeFinset, Real.exp (β * bond s e) := by
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  rw [show -β * -(∑ e ∈ G.edgeFinset, bond s e)
        = β * (∑ e ∈ G.edgeFinset, bond s e) by ring,
    Finset.mul_sum, Real.exp_sum]

omit [DecidableEq V] in
lemma prod_exp_bond_eq (β : ℝ) (s : ConfigSpace V) :
    (∏ e ∈ G.edgeFinset, Real.exp (β * bond s e))
      = (Real.cosh β) ^ G.edgeFinset.card
        * ∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [exp_mul_eq_cosh_mul β (bond s e) (bond_eq_pm s e)]

/-! ## B. Even subgraphs -/

/-- The number of edges of `F` incident to `v`. -/
def incCount (F : Finset (Sym2 V)) (v : V) : ℕ :=
  (F.filter (fun e => v ∈ e)).card

omit [Fintype V] in
lemma incCount_insert (e : Sym2 V) (F : Finset (Sym2 V)) (he : e ∉ F) (v : V) :
    incCount (insert e F) v = incCount F v + (if v ∈ e then 1 else 0) := by
  unfold incCount
  rw [Finset.filter_insert]
  by_cases hv : v ∈ e
  · rw [ite_eq_left hv, Finset.card_insert_of_notMem (by simp [he]), ite_eq_left hv]
  · rw [ite_eq_right hv, ite_eq_right hv, add_zero]

/-- Every vertex has even degree in the edge set `F`. -/
def IsEvenSubgraph (F : Finset (Sym2 V)) : Prop := ∀ v : V, Even (incCount F v)

/-- Being an even subgraph is decidable. -/
instance (F : Finset (Sym2 V)) : Decidable (IsEvenSubgraph F) :=
  Fintype.decidableForallFintype

lemma prod_bond_eq_prod_pow_incCount (s : ConfigSpace V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∏ e ∈ F, bond s e) = ∏ v : V, (spin s v) ^ (incCount F v) := by
  induction F using Finset.induction with
  | empty => simp [incCount]
  | insert e F he ih =>
    rw [Finset.prod_insert he, ih (fun e' he' => hF e' (Finset.mem_insert_of_mem he'))]
    simp_rw [incCount_insert e F he, pow_add]
    rw [Finset.prod_mul_distrib, mul_comm]
    congr 1
    have hd : ¬ e.IsDiag := hF e (Finset.mem_insert_self e F)
    induction e using Sym2.ind with
    | _ x y =>
      rw [Sym2.mk_isDiag_iff] at hd
      rw [bond_mk]
      have hcvt : ∀ v : V, (spin s v) ^ (if v ∈ (s(x, y) : Sym2 V) then 1 else 0)
          = if v ∈ ({x, y} : Finset V) then spin s v else 1 := by
        intro v
        simp only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        by_cases h : v = x ∨ v = y <;> simp [h]
      simp_rw [hcvt]
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pair hd]

omit [Fintype V] [DecidableEq V] in
lemma spin_pow (s : ConfigSpace V) (v : V) (n : ℕ) :
    (spin s v) ^ n = if Even n then 1 else spin s v := by
  have hsq : (spin s v) ^ 2 = 1 := by rw [sq]; exact spin_sq s v
  rcases Nat.even_or_odd n with he | ho
  · rw [ite_eq_left he]
    obtain ⟨k, rfl⟩ := he
    rw [show k + k = 2 * k by ring, pow_mul, hsq, one_pow]
  · rw [ite_eq_right (by simp [Nat.not_even_iff_odd, ho])]
    obtain ⟨k, rfl⟩ := ho
    rw [pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]

lemma sum_prod_spin_set (S : Finset V) :
    (∑ s : ConfigSpace V, ∏ v ∈ S, spin s v)
      = if S = ∅ then (2 : ℝ) ^ Fintype.card V else 0 := by
  have key :
      (∑ s : ConfigSpace V, ∏ v : V,
        (fun v b => if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1) v (s v))
        = ∏ v : V, ∑ b : Bool,
            (if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1) :=
    (Fintype.prod_sum
      (fun v b => if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1)).symm
  have h1 : ∀ s : ConfigSpace V, (∏ v ∈ S, spin s v)
      = ∏ v : V,
          (fun v b => if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1) v (s v) := by
    intro s
    rw [Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  simp_rw [h1]
  rw [key]
  have hfac : ∀ v : V, (∑ b : Bool, if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1)
      = if v ∈ S then 0 else 2 := by
    intro v; by_cases hv : v ∈ S <;> simp [hv]
  simp_rw [hfac]
  by_cases hS : S = ∅
  · subst hS; simp
  · rw [ite_eq_right hS]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [ite_eq_left hv])

lemma sum_prod_bond_subgraph (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∑ s : ConfigSpace V, ∏ e ∈ F, bond s e)
      = if IsEvenSubgraph F then (2 : ℝ) ^ Fintype.card V else 0 := by
  have hstep : ∀ s : ConfigSpace V,
      (∏ e ∈ F, bond s e)
        = ∏ v ∈ Finset.univ.filter (fun v => ¬ Even (incCount F v)), spin s v := by
    intro s
    rw [prod_bond_eq_prod_pow_incCount s F hF]
    simp_rw [spin_pow s]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v _
    by_cases h : Even (incCount F v) <;> simp [h]
  simp_rw [hstep]
  rw [sum_prod_spin_set]
  by_cases hev : IsEvenSubgraph F
  · rw [ite_eq_left hev, ite_eq_left]
    rw [Finset.filter_eq_empty_iff]
    intro v _
    simpa using hev v
  · rw [ite_eq_right hev, ite_eq_right]
    rw [IsEvenSubgraph, not_forall] at hev
    obtain ⟨v, hv⟩ := hev
    exact Finset.ne_empty_of_mem (a := v) (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)

/-! ## C. The high-temperature expansion -/

/-- **High-temperature expansion.** At zero field, `Z(β) = 2^{|V|} (cosh β)^{|E|} ∑_{F even}
(tanh β)^{|F|}`.

S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
Press (2017), Section 3.7. -/
theorem isingZ_high_temp_expansion (β : ℝ) :
    isingZ G β 0
      = (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card
        * ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
            (Real.tanh β) ^ F.card := by
  unfold isingZ
  have hweight : ∀ s : ConfigSpace V,
      isingWeight G β 0 s
        = (Real.cosh β) ^ G.edgeFinset.card
          * ∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e) := by
    intro s
    rw [isingWeight_field_free_eq_prod, prod_exp_bond_eq]
  simp_rw [hweight]
  have hexpand : ∀ s : ConfigSpace V,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e))
        = ∑ F ∈ G.edgeFinset.powerset,
            ∏ e ∈ F, (Real.tanh β * bond s e) := by
    intro s; exact Finset.prod_one_add _
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card
        * ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh β) ^ F.card
      = (Real.cosh β) ^ G.edgeFinset.card
        * ((2 : ℝ) ^ Fintype.card V
            * ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh β) ^ F.card) by ring]
  congr 1
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  have hpull : ∀ s : ConfigSpace V,
      (∏ e ∈ F, (Real.tanh β * bond s e))
        = (Real.tanh β) ^ F.card * ∏ e ∈ F, bond s e := by
    intro s
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  rw [← Finset.mul_sum]
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G
      (by rw [← SimpleGraph.mem_edgeFinset]; exact hF he)
  rw [sum_prod_bond_subgraph F hnd]
  by_cases hev : IsEvenSubgraph F
  · rw [ite_eq_left hev, ite_eq_left hev]; ring
  · rw [ite_eq_right hev, ite_eq_right hev]; ring

end HighTemp

section SelfDual

open StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]

/-! ## D. Duality from a contour matching -/

/-- `tanh β* = exp (-2β)` and the high-temperature expansion of `Gd` at `β*` equals `c` times
`Z_{Gp}(β)`. -/
def DualContourMatching (β βstar c : ℝ) : Prop :=
  Real.tanh βstar = Real.exp (-2 * β) ∧
    (2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        * ∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph,
            (Real.tanh βstar) ^ F.card
      = c * isingZ Gp β 0

lemma isingZ_self_dual (β βstar c : ℝ)
    (hmatch : DualContourMatching Gp Gd β βstar c) :
    isingZ Gd βstar 0 = c * isingZ Gp β 0 := by
  have hZd := isingZ_high_temp_expansion Gd βstar
  obtain ⟨_, hmatch⟩ := hmatch
  rw [hZd, hmatch]

lemma isingZ_self_dual_proportional (β βstar c : ℝ)
    (hmatch : DualContourMatching Gp Gd β βstar c) :
    ∃ factor : ℝ, isingZ Gd βstar 0 = factor * isingZ Gp β 0 :=
  ⟨c, isingZ_self_dual Gp Gd β βstar c hmatch⟩

end SelfDual

end Ising

end StatMech
