/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.Percolation.Theta
import Code.Percolation.TildePc
import Code.Lattice.Clusters
import Code.Lattice.HypercubicLattice

open MeasureTheory Set
open scoped NNReal ENNReal

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}











def crossingEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ v, Connected d ω (origin d) v ∧ v ∉ box d (n - 1)}

@[simp]
theorem mem_crossingEvent {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ crossingEvent d n ↔ ∃ v, Connected d ω (origin d) v ∧ v ∉ box d (n - 1) :=
  Iff.rfl



theorem crossingEvent_antitone (m n : ℕ) (hmn : m ≤ n) :
    crossingEvent d n ⊆ crossingEvent d m := by
  intro ω hω
  obtain ⟨v, hconn, hv⟩ := hω
  exact ⟨v, hconn, fun hvm => hv (box_mono d (by omega) hvm)⟩



noncomputable def crossProb (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) : ℝ :=
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (crossingEvent d n)


theorem crossProb_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    0 ≤ crossProb d p hp n :=
  measureReal_nonneg


theorem crossProb_le_one (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    crossProb d p hp n ≤ 1 := by
  unfold crossProb
  rw [show (1 : ℝ) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real Set.univ by
        rw [probReal_univ]]
  exact measureReal_mono (Set.subset_univ _)




theorem crossProb_antitone (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Antitone (crossProb d p hp) :=
  fun m n hmn => measureReal_mono (crossingEvent_antitone m n hmn)









theorem recursion_le_pow {f : ℕ → ℝ} {r : ℝ} (hf0 : f 0 ≤ 1) (hr : 0 ≤ r)
    (hrec : ∀ k, f (k + 1) ≤ r * f k) : ∀ k, f k ≤ r ^ k := by
  intro k
  induction k with
  | zero => simpa using hf0
  | succ k ih =>
    calc f (k + 1) ≤ r * f k := hrec k
      _ ≤ r * r ^ k := by exact mul_le_mul_of_nonneg_left ih hr
      _ = r ^ (k + 1) := by ring














theorem geometric_subseq_antitone_decay {f : ℕ → ℝ} {r : ℝ} {L : ℕ}
    (hL : 1 ≤ L) (hr0 : 0 < r) (hr1 : r < 1) (hanti : Antitone f)
    (hsub : ∀ k, f (k * L) ≤ r ^ k) :
    ∃ c > 0, ∃ C > 0, ∀ n, f n ≤ C * Real.exp (-c * n) := by
  have hlogr_neg : Real.log r < 0 := Real.log_neg hr0 hr1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set c : ℝ := -(Real.log r) / L with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; exact div_pos (by linarith) hLpos
  refine ⟨c, hc_pos, r⁻¹, by positivity, fun n => ?_⟩
  set k := n / L with hk_def
  
  have hfn : f n ≤ r ^ k := le_trans (hanti (Nat.div_mul_le_self n L)) (hsub k)
  
  have hkpos_real : ((n : ℝ) / L - 1) < (k : ℝ) := by
    have hnlt := Nat.lt_div_mul_add (a := n) (b := L) hL
    have hkk : (n : ℝ) < (k : ℝ) * L + L := by rw [hk_def]; exact_mod_cast hnlt
    rw [div_sub_one hLpos.ne', div_lt_iff₀ hLpos]; linarith
  have hrk : (r : ℝ) ^ (k : ℝ) = Real.exp ((k : ℝ) * Real.log r) := by
    rw [Real.rpow_def_of_pos hr0]; ring_nf
  
  have step2 : (r : ℝ) ^ k ≤ Real.exp (((n : ℝ) / L - 1) * Real.log r) := by
    rw [show (r : ℝ) ^ k = r ^ (k : ℝ) from (Real.rpow_natCast r k).symm, hrk]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hkpos_real.le hlogr_neg.le)
  
  have step3 : Real.exp (((n : ℝ) / L - 1) * Real.log r) = r⁻¹ * Real.exp (-c * n) := by
    rw [sub_mul, one_mul, Real.exp_sub, hc_def,
        show -(-Real.log r / L) * (n : ℝ) = (n / L) * Real.log r from by ring,
        show Real.exp (Real.log r) = r from Real.exp_log hr0]
    ring
  calc f n ≤ r ^ k := hfn
    _ ≤ Real.exp (((n : ℝ) / L - 1) * Real.log r) := step2
    _ = r⁻¹ * Real.exp (-c * n) := step3







theorem step_with_pos_ratio {f : ℕ → ℝ} {r₀ : ℝ} (hfnn : ∀ k, 0 ≤ f k)
    (hr1 : r₀ < 1) (hrec : ∀ k, f (k + 1) ≤ r₀ * f k) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ k, f (k + 1) ≤ r * f k := by
  refine ⟨max r₀ (1 / 2), by positivity, max_lt hr1 (by norm_num), fun k => ?_⟩
  calc f (k + 1) ≤ r₀ * f k := hrec k
    _ ≤ max r₀ (1 / 2) * f k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hfnn k)

















theorem subcritical_decay (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hS0 : origin d ∈ S) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L)
    (hstep : ∀ k, crossProb d p hp ((k + 1) * L) ≤ phi d p hp S * crossProb d p hp (k * L)) :
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
  classical
  
  
  set r₀ : ℝ := phi d p hp S with hr₀_def
  
  set g : ℕ → ℝ := fun k => crossProb d p hp (k * L) with hg_def
  have hgnn : ∀ k, 0 ≤ g k := fun k => crossProb_nonneg d p hp (k * L)
  have hg0 : g 0 ≤ 1 := by simpa [hg_def] using crossProb_le_one d p hp 0
  have hgrec : ∀ k, g (k + 1) ≤ r₀ * g k := hstep
  
  obtain ⟨r, hr0, hr1, hgrec'⟩ := step_with_pos_ratio hgnn hphi hgrec
  
  have hsub : ∀ k, crossProb d p hp (k * L) ≤ r ^ k :=
    recursion_le_pow hg0 hr0.le hgrec'
  
  exact geometric_subseq_antitone_decay hL hr0 hr1 (crossProb_antitone d p hp) hsub

end Percolation

end StatMech
