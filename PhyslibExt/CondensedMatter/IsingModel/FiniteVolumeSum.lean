/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FiniteVolumeRelabel
public import PhyslibExt.StatisticalMechanics.RandomCluster.SuperMultiplicative

/-!
# Ising models on disjoint unions of graphs

The Ising model on a disjoint union `G ⊕ H` is the product of the models on `G` and `H`.

## i. Overview

Configurations on `V ⊕ W` split as pairs of configurations. The Hamiltonian of `G ⊕ H` is the sum of
the Hamiltonians, the partition function is the product, and the Gibbs probability factorizes. Hence
spin correlations of vertices of `G` are the same in `G ⊕ H` and in `G`.

## ii. Key results

- `StatMech.Ising.isingZ_sum` : the partition function of a disjoint union is the product
- `StatMech.Ising.isingExpectation_spinProd_sum_inl` : correlations inside one component are
  unchanged

## iii. Table of contents

- A. Configurations on a disjoint union
- B. Factorization of the Gibbs distribution
- C. Correlations in one component

## iv. References

- None beyond the sources named in the overview.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-! ## A. Configurations on a disjoint union -/

/-- The equivalence between configurations on `V ⊕ W` and pairs of configurations on `V` and `W`. -/
def isingSumConfigEquiv : ConfigSpace (V ⊕ W) ≃ ConfigSpace V × ConfigSpace W :=
  Equiv.sumPiEquivProdPi (fun _ : V ⊕ W => Bool)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp]
lemma spin_isingSumConfigEquiv_symm_inl (s : ConfigSpace V) (t : ConfigSpace W) (x : V) :
    spin (isingSumConfigEquiv.symm (s, t)) (Sum.inl x) = spin s x := by
  simp [isingSumConfigEquiv, spin]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp]
lemma spin_isingSumConfigEquiv_symm_inr (s : ConfigSpace V) (t : ConfigSpace W) (x : W) :
    spin (isingSumConfigEquiv.symm (s, t)) (Sum.inr x) = spin t x := by
  simp [isingSumConfigEquiv, spin]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp]
lemma spinProd_isingSumConfigEquiv_symm_inl (s : ConfigSpace V) (t : ConfigSpace W)
    (A : Finset V) :
    spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)
        (isingSumConfigEquiv.symm (s, t)) = spinProd A s := by
  simp [spinProd]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
lemma bond_isingSumConfigEquiv_symm_inl (s : ConfigSpace V) (t : ConfigSpace W)
    (e : Sym2 V) :
    bond (isingSumConfigEquiv.symm (s, t)) (Sym2.map Sum.inl e) = bond s e := by
  induction e using Sym2.ind with
  | _ x y => simp [bond]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
lemma bond_isingSumConfigEquiv_symm_inr (s : ConfigSpace V) (t : ConfigSpace W)
    (e : Sym2 W) :
    bond (isingSumConfigEquiv.symm (s, t)) (Sym2.map Sum.inr e) = bond t e := by
  induction e using Sym2.ind with
  | _ x y => simp [bond]

variable (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]

lemma sum_bond_isingSumConfigEquiv_symm (s : ConfigSpace V) (t : ConfigSpace W) :
    (∑ e ∈ (G ⊕g H).edgeFinset, bond (isingSumConfigEquiv.symm (s, t)) e) =
      (∑ e ∈ G.edgeFinset, bond s e) + ∑ e ∈ H.edgeFinset, bond t e := by
  rw [FK.fsm_edgeFinset_sum, Finset.sum_union (FK.fsm_images_disjoint G H)]
  congr 1
  · rw [Finset.sum_image (fun _ _ _ _ h => FK.fsm_map_inl_injective h)]
    exact Finset.sum_congr rfl (fun e _ => bond_isingSumConfigEquiv_symm_inl s t e)
  · rw [Finset.sum_image (fun _ _ _ _ h => FK.fsm_map_inr_injective h)]
    exact Finset.sum_congr rfl (fun e _ => bond_isingSumConfigEquiv_symm_inr s t e)

/-! ## B. Factorization of the Gibbs distribution -/

lemma hamiltonian_isingSumConfigEquiv_symm (h : ℝ)
    (s : ConfigSpace V) (t : ConfigSpace W) :
    hamiltonian (G ⊕g H) h (isingSumConfigEquiv.symm (s, t)) =
      hamiltonian G h s + hamiltonian H h t := by
  unfold hamiltonian
  rw [sum_bond_isingSumConfigEquiv_symm G H, Fintype.sum_sum_type]
  simp only [spin_isingSumConfigEquiv_symm_inl, spin_isingSumConfigEquiv_symm_inr]
  ring

lemma isingWeight_isingSumConfigEquiv_symm (beta h : ℝ)
    (s : ConfigSpace V) (t : ConfigSpace W) :
    isingWeight (G ⊕g H) beta h (isingSumConfigEquiv.symm (s, t)) =
      isingWeight G beta h s * isingWeight H beta h t := by
  unfold isingWeight
  rw [hamiltonian_isingSumConfigEquiv_symm G H]
  rw [show -beta * (hamiltonian G h s + hamiltonian H h t) =
      -beta * hamiltonian G h s + -beta * hamiltonian H h t by ring]
  exact Real.exp_add _ _

lemma isingZ_sum (beta h : ℝ) :
    isingZ (G ⊕g H) beta h = isingZ G beta h * isingZ H beta h := by
  unfold isingZ
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [isingWeight_isingSumConfigEquiv_symm G H]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

lemma isingProb_isingSumConfigEquiv_symm (beta h : ℝ)
    (s : ConfigSpace V) (t : ConfigSpace W) :
    isingProb (G ⊕g H) beta h (isingSumConfigEquiv.symm (s, t)) =
      isingProb G beta h s * isingProb H beta h t := by
  unfold isingProb
  rw [isingWeight_isingSumConfigEquiv_symm G H, isingZ_sum G H]
  field_simp [isingZ_ne_zero G beta h, isingZ_ne_zero H beta h]

/-! ## C. Correlations in one component -/

lemma isingExpectation_spin_sum_inl (beta h : ℝ) (x : V) :
    isingExpectation (G ⊕g H) beta h (fun s => spin s (Sum.inl x)) =
      isingExpectation G beta h (fun s => spin s x) := by
  unfold isingExpectation
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [isingProb_isingSumConfigEquiv_symm G H,
    spin_isingSumConfigEquiv_symm_inl]
  have hinner : ∀ s : ConfigSpace V,
      (∑ t : ConfigSpace W, isingProb G beta h s * isingProb H beta h t * spin s x) =
        isingProb G beta h s * spin s x := by
    intro s
    rw [show (∑ t : ConfigSpace W,
        isingProb G beta h s * isingProb H beta h t * spin s x) =
          (isingProb G beta h s * spin s x) *
            ∑ t : ConfigSpace W, isingProb H beta h t by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)]
    rw [isingProb_sum_eq_one]
    ring
  simp_rw [hinner]

lemma isingExpectation_spinProd_sum_inl (beta h : ℝ) (A : Finset V) :
    isingExpectation (G ⊕g H) beta h
        (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) =
      isingExpectation G beta h (spinProd A) := by
  unfold isingExpectation
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [isingProb_isingSumConfigEquiv_symm G H,
    spinProd_isingSumConfigEquiv_symm_inl]
  have hinner : ∀ s : ConfigSpace V,
      (∑ t : ConfigSpace W,
        isingProb G beta h s * isingProb H beta h t * spinProd A s) =
        isingProb G beta h s * spinProd A s := by
    intro s
    rw [show (∑ t : ConfigSpace W,
        isingProb G beta h s * isingProb H beta h t * spinProd A s) =
          (isingProb G beta h s * spinProd A s) *
            ∑ t : ConfigSpace W, isingProb H beta h t by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)]
    rw [isingProb_sum_eq_one]
    ring
  simp_rw [hinner]

end Ising

end StatMech
