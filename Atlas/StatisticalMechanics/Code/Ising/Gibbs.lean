/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























import Mathlib
import Code.Foundations.ConfigSpace

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

section Spins

variable {V : Type*}



def spin (s : ConfigSpace V) (x : V) : ℝ := if s x then 1 else -1

@[simp] lemma spin_true (s : ConfigSpace V) {x : V} (hx : s x = true) : spin s x = 1 := by
  simp [spin, hx]

@[simp] lemma spin_false (s : ConfigSpace V) {x : V} (hx : s x = false) : spin s x = -1 := by
  simp [spin, hx]


lemma spin_sq (s : ConfigSpace V) (x : V) : spin s x * spin s x = 1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]


lemma abs_spin_le_one (s : ConfigSpace V) (x : V) : |spin s x| ≤ 1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]




def bond (s : ConfigSpace V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => spin s x * spin s y, fun _ _ => mul_comm _ _⟩ e

@[simp] lemma bond_mk (s : ConfigSpace V) (x y : V) :
    bond s s(x, y) = spin s x * spin s y := rfl

end Spins

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



def hamiltonian (h : ℝ) (s : ConfigSpace V) : ℝ :=
  - (∑ e ∈ G.edgeFinset, bond s e) - h * ∑ x, spin s x


noncomputable def isingWeight (β h : ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (-β * hamiltonian G h s)

omit [DecidableEq V] in

lemma isingWeight_pos (β h : ℝ) (s : ConfigSpace V) : 0 < isingWeight G β h s :=
  Real.exp_pos _

omit [DecidableEq V] in
lemma isingWeight_nonneg (β h : ℝ) (s : ConfigSpace V) : 0 ≤ isingWeight G β h s :=
  (isingWeight_pos G β h s).le



noncomputable def isingZ (β h : ℝ) : ℝ := ∑ s : ConfigSpace V, isingWeight G β h s



lemma isingZ_pos (β h : ℝ) : 0 < isingZ G β h := by
  unfold isingZ
  apply Finset.sum_pos
  · intro s _; exact isingWeight_pos G β h s
  · exact Finset.univ_nonempty

lemma isingZ_ne_zero (β h : ℝ) : isingZ G β h ≠ 0 := (isingZ_pos G β h).ne'



noncomputable def isingProb (β h : ℝ) (s : ConfigSpace V) : ℝ :=
  isingWeight G β h s / isingZ G β h


lemma isingProb_nonneg (β h : ℝ) (s : ConfigSpace V) : 0 ≤ isingProb G β h s :=
  div_nonneg (isingWeight_nonneg G β h s) (isingZ_pos G β h).le


lemma isingProb_pos (β h : ℝ) (s : ConfigSpace V) : 0 < isingProb G β h s :=
  div_pos (isingWeight_pos G β h s) (isingZ_pos G β h)


lemma isingProb_sum_eq_one (β h : ℝ) : ∑ s : ConfigSpace V, isingProb G β h s = 1 := by
  unfold isingProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (isingZ_ne_zero G β h)]
  rfl



noncomputable def isingPMF (β h : ℝ) : PMF (ConfigSpace V) :=
  PMF.ofFintype (fun s => ENNReal.ofReal (isingProb G β h s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => isingProb_nonneg G β h s),
      isingProb_sum_eq_one G β h]
    simp)

@[simp] lemma isingPMF_apply (β h : ℝ) (s : ConfigSpace V) :
    isingPMF G β h s = ENNReal.ofReal (isingProb G β h s) := rfl

end Ising

end StatMech
