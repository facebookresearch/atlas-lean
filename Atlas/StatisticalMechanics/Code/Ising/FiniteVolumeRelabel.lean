/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FiniteVolumeShift
import Code.Ising.GKS

open Finset

namespace StatMech

namespace Ising

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


def isingCfgEquiv (σ : V ≃ W) : ConfigSpace W ≃ ConfigSpace V where
  toFun ω := fun x => ω (σ x)
  invFun ω := fun y => ω (σ.symm y)
  left_inv ω := by funext y; simp
  right_inv ω := by funext x; simp

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp]
theorem isingCfgEquiv_apply (σ : V ≃ W) (ω : ConfigSpace W) (x : V) :
    isingCfgEquiv σ ω x = ω (σ x) := rfl

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp]
theorem spin_isingCfgEquiv (σ : V ≃ W) (ω : ConfigSpace W) (x : V) :
    spin (isingCfgEquiv σ ω) x = spin ω (σ x) := rfl

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp]
theorem spinProd_isingCfgEquiv (σ : V ≃ W) (ω : ConfigSpace W) (A : Finset V) :
    spinProd A (isingCfgEquiv σ ω) =
      spinProd (A.map σ.toEmbedding) ω := by
  simp [spinProd]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem bond_isingCfgEquiv (σ : V ≃ W) (ω : ConfigSpace W) (e : Sym2 V) :
    bond (isingCfgEquiv σ ω) e = bond ω (Sym2.map σ e) := by
  induction e using Sym2.ind with
  | _ x y => simp [bond]

variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableEq W] in


theorem sum_bond_isingCfgEquiv (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (ω : ConfigSpace W) :
    (∑ e ∈ G.edgeFinset, bond (isingCfgEquiv σ ω) e) =
      ∑ e ∈ H.edgeFinset, bond ω e := by
  symm
  apply Finset.sum_bij' (i := fun e _ => Sym2.map σ.symm e)
    (j := fun e _ => Sym2.map σ e)
  · intro e he
    exact FK.fvs_mem_edgeFinset_map_symm G H σ hσ he
  · intro e he
    exact FK.fvs_mem_edgeFinset_map G H σ hσ he
  · intro e he
    rw [Sym2.map_map]
    simp
  · intro e he
    rw [Sym2.map_map]
    simp
  · intro e he
    rw [bond_isingCfgEquiv, Sym2.map_map]
    simp

omit [DecidableEq V] [DecidableEq W] in

theorem sum_spin_isingCfgEquiv (σ : V ≃ W) (ω : ConfigSpace W) :
    (∑ x : V, spin (isingCfgEquiv σ ω) x) = ∑ y : W, spin ω y := by
  simpa using Equiv.sum_comp σ (fun y : W => spin ω y)

omit [DecidableEq V] [DecidableEq W] in


theorem hamiltonian_isingCfgEquiv (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (h : ℝ)
    (ω : ConfigSpace W) :
    hamiltonian G h (isingCfgEquiv σ ω) = hamiltonian H h ω := by
  unfold hamiltonian
  rw [sum_bond_isingCfgEquiv G H σ hσ ω, sum_spin_isingCfgEquiv σ ω]

omit [DecidableEq V] [DecidableEq W] in

theorem isingWeight_isingCfgEquiv (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (β h : ℝ)
    (ω : ConfigSpace W) :
    isingWeight G β h (isingCfgEquiv σ ω) = isingWeight H β h ω := by
  unfold isingWeight
  rw [hamiltonian_isingCfgEquiv G H σ hσ]


theorem isingZ_relabel (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (β h : ℝ) :
    isingZ G β h = isingZ H β h := by
  unfold isingZ
  rw [← Equiv.sum_comp (isingCfgEquiv σ) (fun ω => isingWeight G β h ω)]
  exact Finset.sum_congr rfl
    (fun ω _ => isingWeight_isingCfgEquiv G H σ hσ β h ω)


theorem isingProb_isingCfgEquiv (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (β h : ℝ)
    (ω : ConfigSpace W) :
    isingProb G β h (isingCfgEquiv σ ω) = isingProb H β h ω := by
  unfold isingProb
  rw [isingWeight_isingCfgEquiv G H σ hσ, isingZ_relabel G H σ hσ]


theorem isingExpectation_spin_relabel (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (β h : ℝ) (x : V) :
    isingExpectation G β h (fun ω => spin ω x) =
      isingExpectation H β h (fun ω => spin ω (σ x)) := by
  unfold isingExpectation
  rw [← Equiv.sum_comp (isingCfgEquiv σ)
    (fun ω => isingProb G β h ω * spin ω x)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [isingProb_isingCfgEquiv G H σ hσ, spin_isingCfgEquiv]


theorem isingExpectation_spinProd_relabel (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (β h : ℝ) (A : Finset V) :
    isingExpectation G β h (spinProd A) =
      isingExpectation H β h (spinProd (A.map σ.toEmbedding)) := by
  unfold isingExpectation
  rw [← Equiv.sum_comp (isingCfgEquiv σ)
    (fun ω => isingProb G β h ω * spinProd A ω)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [isingProb_isingCfgEquiv G H σ hσ, spinProd_isingCfgEquiv]

end Ising

end StatMech
