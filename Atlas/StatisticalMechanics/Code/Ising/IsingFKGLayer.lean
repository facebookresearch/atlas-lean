/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Code.Ising.InfiniteVolume
import Code.Inequalities.FKG

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.unusedSectionVars false
set_option linter.style.longLine false







variable {V : Type*}





theorem ifk_bond_supermodular (a b : ConfigSpace V) (e : Sym2 V) :
    bond a e + bond b e ≤ bond (a ⊔ b) e + bond (a ⊓ b) e := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [bond_mk]; unfold spin
    rw [show (a ⊔ b) x = (a x || b x) from rfl, show (a ⊓ b) x = (a x && b x) from rfl,
        show (a ⊔ b) y = (a y || b y) from rfl, show (a ⊓ b) y = (a y && b y) from rfl]
    by_cases hax : a x <;> by_cases hbx : b x <;> by_cases hay : a y <;> by_cases hby : b y <;>
      simp_all <;> norm_num




theorem ifk_spin_modular (a b : ConfigSpace V) (x : V) :
    spin a x + spin b x = spin (a ⊔ b) x + spin (a ⊓ b) x := by
  unfold spin
  rw [show (a ⊔ b) x = (a x || b x) from rfl, show (a ⊓ b) x = (a x && b x) from rfl]
  by_cases hax : a x <;> by_cases hbx : b x <;> simp_all



theorem ifk_spin_mono {a b : ConfigSpace V} (hab : a ≤ b) (x : V) : spin a x ≤ spin b x := by
  unfold spin
  have h := hab x
  by_cases ha : a x <;> by_cases hb : b x
  · simp [ha, hb]
  · exact absurd h (by simp [ha, hb])
  · simp [ha, hb]
  · simp [ha, hb]






variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in




theorem ifk_hamiltonian_submodular (h : ℝ) (a b : ConfigSpace V) :
    hamiltonian G h (a ⊔ b) + hamiltonian G h (a ⊓ b)
      ≤ hamiltonian G h a + hamiltonian G h b := by
  unfold hamiltonian
  have hbond : ∑ e ∈ G.edgeFinset, bond a e + ∑ e ∈ G.edgeFinset, bond b e
      ≤ ∑ e ∈ G.edgeFinset, bond (a ⊔ b) e + ∑ e ∈ G.edgeFinset, bond (a ⊓ b) e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => ifk_bond_supermodular a b e)
  have hfield : ∑ x, spin (a ⊔ b) x + ∑ x, spin (a ⊓ b) x = ∑ x, spin a x + ∑ x, spin b x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => (ifk_spin_modular a b x).symm)
  have hfieldh : h * (∑ x, spin (a ⊔ b) x) + h * (∑ x, spin (a ⊓ b) x)
      = h * (∑ x, spin a x) + h * (∑ x, spin b x) := by rw [← mul_add, ← mul_add, hfield]
  linarith [hbond, hfieldh]



omit [DecidableEq V] in



theorem ifk_isingWeight_logSupermodular {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) (a b : ConfigSpace V) :
    isingWeight G β h a * isingWeight G β h b
      ≤ isingWeight G β h (a ⊔ b) * isingWeight G β h (a ⊓ b) := by
  unfold isingWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsub := ifk_hamiltonian_submodular G h a b
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hsub)]




theorem ifk_isingProb_FKGLatticeCondition {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) :
    FKGLatticeCondition (fun s => isingProb G β h s) := by
  have hZpos : 0 < isingZ G β h := isingZ_pos G β h
  intro a b
  simp only [isingProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZpos hZpos)).mpr
    (ifk_isingWeight_logSupermodular G hβ h a b)



theorem ifk_isingProb_positively_associated {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    {f g : ConfigSpace V → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∑ s, isingProb G β h s * f s) * (∑ s, isingProb G β h s * g s)
      ≤ ∑ s, isingProb G β h s * (f s * g s) :=
  fkg_inequality (fun s => isingProb_nonneg G β h s) (isingProb_sum_eq_one G β h)
    (ifk_isingProb_FKGLatticeCondition G hβ h) hf hg



theorem ifk_isingProb_positively_associated_events {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    {A B : Set (ConfigSpace V)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ s, isingProb G β h s * A.indicator (fun _ => (1 : ℝ)) s)
        * (∑ s, isingProb G β h s * B.indicator (fun _ => (1 : ℝ)) s)
      ≤ ∑ s, isingProb G β h s * (A ∩ B).indicator (fun _ => (1 : ℝ)) s :=
  fkg_inequality_events (fun s => isingProb_nonneg G β h s) (isingProb_sum_eq_one G β h)
    (ifk_isingProb_FKGLatticeCondition G hβ h) hA hB








variable {d : ℕ}



theorem ifk_glue_sup (η : ConfigSpace (Site d)) {n : ℕ}
    (τ τ' : {x // x ∈ box d n} → Bool) :
    glue η (τ ⊔ τ') = glue η τ ⊔ glue η τ' := by
  funext x; by_cases hx : x ∈ box d n
  · simp only [glue_mem _ _ hx, Pi.sup_apply]
  · simp only [glue_not_mem _ _ hx, Pi.sup_apply]; exact (sup_idem (η x)).symm


theorem ifk_glue_inf (η : ConfigSpace (Site d)) {n : ℕ}
    (τ τ' : {x // x ∈ box d n} → Bool) :
    glue η (τ ⊓ τ') = glue η τ ⊓ glue η τ' := by
  funext x; by_cases hx : x ∈ box d n
  · simp only [glue_mem _ _ hx, Pi.inf_apply]
  · simp only [glue_not_mem _ _ hx, Pi.inf_apply]; exact (inf_idem (η x)).symm





theorem ifk_fvEnergy_submodular (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (h : ℝ) (τ τ' : {x // x ∈ box d n} → Bool) :
    fvEnergy η n B h (τ ⊔ τ') + fvEnergy η n B h (τ ⊓ τ')
      ≤ fvEnergy η n B h τ + fvEnergy η n B h τ' := by
  unfold fvEnergy
  rw [ifk_glue_sup, ifk_glue_inf]
  have hbond : ∑ e ∈ B, bond (glue η τ) e + ∑ e ∈ B, bond (glue η τ') e
      ≤ ∑ e ∈ B, bond (glue η τ ⊔ glue η τ') e + ∑ e ∈ B, bond (glue η τ ⊓ glue η τ') e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => ifk_bond_supermodular (glue η τ) (glue η τ') e)
  have hfield : ∑ x ∈ boxFinset d n, spin (glue η τ ⊔ glue η τ') x
      + ∑ x ∈ boxFinset d n, spin (glue η τ ⊓ glue η τ') x
      = ∑ x ∈ boxFinset d n, spin (glue η τ) x + ∑ x ∈ boxFinset d n, spin (glue η τ') x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => (ifk_spin_modular (glue η τ) (glue η τ') x).symm)
  have hfieldh : h * (∑ x ∈ boxFinset d n, spin (glue η τ ⊔ glue η τ') x)
      + h * (∑ x ∈ boxFinset d n, spin (glue η τ ⊓ glue η τ') x)
      = h * (∑ x ∈ boxFinset d n, spin (glue η τ) x)
        + h * (∑ x ∈ boxFinset d n, spin (glue η τ') x) := by
    rw [← mul_add, ← mul_add, hfield]
  linarith [hbond, hfieldh]




theorem ifk_fvWeight_logSupermodular (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (τ τ' : {x // x ∈ box d n} → Bool) :
    fvWeight η n B β h τ * fvWeight η n B β h τ'
      ≤ fvWeight η n B β h (τ ⊔ τ') * fvWeight η n B β h (τ ⊓ τ') := by
  unfold fvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsub := ifk_fvEnergy_submodular η n B h τ τ'
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hsub)]




theorem ifk_fvProb_FKGLatticeCondition (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) :
    FKGLatticeCondition (fun τ : {x // x ∈ box d n} → Bool => fvProb η n B β h τ) := by
  have hZpos : 0 < fvZ η n B β h := fvZ_pos η n B β h
  intro a b
  simp only [fvProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZpos hZpos)).mpr
    (ifk_fvWeight_logSupermodular η n B hβ h a b)


theorem ifk_fvProb_positively_associated (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    {f g : ({x // x ∈ box d n} → Bool) → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∑ τ, fvProb η n B β h τ * f τ) * (∑ τ, fvProb η n B β h τ * g τ)
      ≤ ∑ τ, fvProb η n B β h τ * (f τ * g τ) :=
  fkg_inequality (fun τ => fvProb_nonneg η n B β h τ) (fvProb_sum_eq_one η n B β h)
    (ifk_fvProb_FKGLatticeCondition η n B hβ h) hf hg


theorem ifk_fvProb_positively_associated_events (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    {A B' : Set (ConfigSpace {x // x ∈ box d n})} (hA : IsIncreasing A) (hB : IsIncreasing B') :
    (∑ τ, fvProb η n B β h τ * A.indicator (fun _ => (1 : ℝ)) τ)
        * (∑ τ, fvProb η n B β h τ * B'.indicator (fun _ => (1 : ℝ)) τ)
      ≤ ∑ τ, fvProb η n B β h τ * (A ∩ B').indicator (fun _ => (1 : ℝ)) τ :=
  fkg_inequality_events (fun τ => fvProb_nonneg η n B β h τ) (fvProb_sum_eq_one η n B β h)
    (ifk_fvProb_FKGLatticeCondition η n B hβ h) hA hB










theorem ifk_glue_cross_inf {η₁ η₂ : ConfigSpace (Site d)} (hη : η₁ ≤ η₂) {n : ℕ}
    (a b : {x // x ∈ box d n} → Bool) :
    glue η₁ (a ⊓ b) = glue η₁ a ⊓ glue η₂ b := by
  funext x
  by_cases hx : x ∈ box d n
  · simp only [glue_mem _ _ hx, Pi.inf_apply]
  · simp only [glue_not_mem _ _ hx, Pi.inf_apply]
    exact (inf_eq_left.mpr (hη x)).symm


theorem ifk_glue_cross_sup {η₁ η₂ : ConfigSpace (Site d)} (hη : η₁ ≤ η₂) {n : ℕ}
    (a b : {x // x ∈ box d n} → Bool) :
    glue η₂ (a ⊔ b) = glue η₁ a ⊔ glue η₂ b := by
  funext x
  by_cases hx : x ∈ box d n
  · simp only [glue_mem _ _ hx, Pi.sup_apply]
  · simp only [glue_not_mem _ _ hx, Pi.sup_apply]
    exact (sup_eq_right.mpr (hη x)).symm





theorem ifk_fvEnergy_cross {η₁ η₂ : ConfigSpace (Site d)} (hη : η₁ ≤ η₂) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (h : ℝ) (a b : {x // x ∈ box d n} → Bool) :
    fvEnergy η₁ n B h (a ⊓ b) + fvEnergy η₂ n B h (a ⊔ b)
      ≤ fvEnergy η₁ n B h a + fvEnergy η₂ n B h b := by
  unfold fvEnergy
  rw [ifk_glue_cross_inf hη, ifk_glue_cross_sup hη]
  set a' := glue η₁ a
  set b' := glue η₂ b
  have hbond : ∑ e ∈ B, bond a' e + ∑ e ∈ B, bond b' e
      ≤ ∑ e ∈ B, bond (a' ⊔ b') e + ∑ e ∈ B, bond (a' ⊓ b') e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => ifk_bond_supermodular a' b' e)
  have hfield : ∑ x ∈ boxFinset d n, spin (a' ⊔ b') x
      + ∑ x ∈ boxFinset d n, spin (a' ⊓ b') x
      = ∑ x ∈ boxFinset d n, spin a' x + ∑ x ∈ boxFinset d n, spin b' x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => (ifk_spin_modular a' b' x).symm)
  have hfieldh : h * (∑ x ∈ boxFinset d n, spin (a' ⊔ b') x)
      + h * (∑ x ∈ boxFinset d n, spin (a' ⊓ b') x)
      = h * (∑ x ∈ boxFinset d n, spin a' x) + h * (∑ x ∈ boxFinset d n, spin b' x) := by
    rw [← mul_add, ← mul_add, hfield]
  linarith [hbond, hfieldh]



theorem ifk_fvWeight_cross {η₁ η₂ : ConfigSpace (Site d)} (hη : η₁ ≤ η₂) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (a b : {x // x ∈ box d n} → Bool) :
    fvWeight η₁ n B β h a * fvWeight η₂ n B β h b
      ≤ fvWeight η₁ n B β h (a ⊓ b) * fvWeight η₂ n B β h (a ⊔ b) := by
  unfold fvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc := ifk_fvEnergy_cross hη n B h a b
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hc)]



theorem ifk_fvProb_cross {η₁ η₂ : ConfigSpace (Site d)} (hη : η₁ ≤ η₂) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (a b : {x // x ∈ box d n} → Bool) :
    fvProb η₁ n B β h a * fvProb η₂ n B β h b
      ≤ fvProb η₁ n B β h (a ⊓ b) * fvProb η₂ n B β h (a ⊔ b) := by
  have hZ1 : 0 < fvZ η₁ n B β h := fvZ_pos _ _ _ _ _
  have hZ2 : 0 < fvZ η₂ n B β h := fvZ_pos _ _ _ _ _
  simp only [fvProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)).mpr
    (ifk_fvWeight_cross hη n B hβ h a b)





theorem ifk_fvProb_holley_dominates {η₁ η₂ : ConfigSpace (Site d)} (hη : η₁ ≤ η₂) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    {A : Set (ConfigSpace {x // x ∈ box d n})} (hA : IsIncreasing A) :
    ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * fvProb η₁ n B β h τ
      ≤ ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * fvProb η₂ n B β h τ :=
  holley_dominates (fun τ => fvProb_nonneg η₁ n B β h τ) (fun τ => fvProb_nonneg η₂ n B β h τ)
    (by rw [fvProb_sum_eq_one, fvProb_sum_eq_one])
    (fun a b => ifk_fvProb_cross hη n B hβ h a b) hA










theorem ifk_minusField_le_plusField (d : ℕ) : minusField d ≤ plusField d := by
  intro x; simp [minusField, plusField]




theorem ifk_minus_le_plus_dominates (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    {A : Set (ConfigSpace {x // x ∈ box d n})} (hA : IsIncreasing A) :
    ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ
        * fvProb (minusField d) n (bondFinsetTouch d n) β h τ
      ≤ ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ
          * fvProb (plusField d) n (bondFinsetTouch d n) β h τ :=
  ifk_fvProb_holley_dominates (ifk_minusField_le_plusField d) n (bondFinsetTouch d n) hβ h hA



theorem ifk_isIncreasing_siteUp (n : ℕ) (x : {x // x ∈ box d n}) :
    IsIncreasing {τ : ConfigSpace {x // x ∈ box d n} | τ x = true} := by
  intro a b hab ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  have hbx := hab x
  rw [ha] at hbx
  exact Bool.le_iff_imp.mp hbx rfl




theorem ifk_minus_le_plus_siteUp (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (x : {x // x ∈ box d n}) :
    ∑ τ, {τ : ConfigSpace {x // x ∈ box d n} | τ x = true}.indicator (fun _ => (1 : ℝ)) τ
        * fvProb (minusField d) n (bondFinsetTouch d n) β h τ
      ≤ ∑ τ, {τ : ConfigSpace {x // x ∈ box d n} | τ x = true}.indicator (fun _ => (1 : ℝ)) τ
          * fvProb (plusField d) n (bondFinsetTouch d n) β h τ :=
  ifk_minus_le_plus_dominates n hβ h (ifk_isIncreasing_siteUp n x)

end Ising

end StatMech
