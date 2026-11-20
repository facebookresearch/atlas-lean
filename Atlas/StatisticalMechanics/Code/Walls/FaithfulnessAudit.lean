/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Ising.AizenmanBarsky
import Code.Walls.ghc_urselleqgap
import Code.Walls.gc31surgery
import Code.Ising.BackboneResummation
import Code.Lattice.BoxSurfaceVolume
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.RootedForestPeelClose
import Code.Walls.bc28forestroot
import Code.Inequalities.Reimer
import Code.Inequalities.ReimerCompression
import Code.Walls.rc18nonmono
import Code.Walls.rc19doublecover

open scoped BigOperators
open Finset SimpleGraph
open StatMech StatMech.Ising StatMech.Walls.GhcEqGap
open StatMech.Lattice StatMech.Percolation

namespace StatMech.Walls

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000













noncomputable def fa_flipAll {V : Type*} (s : ConfigSpace V) : ConfigSpace V := fun i => !(s i)


theorem fa_spin_flipAll {V : Type*} (s : ConfigSpace V) (x : V) :
    spin (fa_flipAll s) x = - spin s x := by
  unfold fa_flipAll spin; by_cases hx : s x <;> simp [hx]


theorem fa_flipAll_bij {V : Type*} : Function.Bijective (fa_flipAll (V := V)) := by
  refine ⟨fun a b hab => ?_, fun b => ⟨fa_flipAll b, ?_⟩⟩
  · funext i; have := congrFun hab i; unfold fa_flipAll at this; simpa using this
  · funext i; unfold fa_flipAll; simp


theorem fa_bond_flipAll {V : Type*} (s : ConfigSpace V) (e : Sym2 V) :
    bond (fa_flipAll s) e = bond s e := by
  induction e with
  | h x y =>
    rw [bond_mk, bond_mk]; unfold fa_flipAll spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem fa_weight_flipAll_h0 (β : ℝ) (s : ConfigSpace V) :
    isingWeight G β 0 (fa_flipAll s) = isingWeight G β 0 s := by
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  have : ∑ e ∈ G.edgeFinset, bond (fa_flipAll s) e = ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_congr rfl (fun e _ => fa_bond_flipAll s e)
  rw [this]


theorem fa_prob_flipAll_h0 (β : ℝ) (s : ConfigSpace V) :
    isingProb G β 0 (fa_flipAll s) = isingProb G β 0 s := by
  unfold isingProb; rw [fa_weight_flipAll_h0]




theorem fa_exp_odd_vanish_h0 (β : ℝ) (f : ConfigSpace V → ℝ)
    (hodd : ∀ s, f (fa_flipAll s) = - f s) :
    isingExpectation G β 0 f = 0 := by
  unfold isingExpectation
  have key : ∑ s : ConfigSpace V, isingProb G β 0 s * f s
      = ∑ s : ConfigSpace V, isingProb G β 0 (fa_flipAll s) * f (fa_flipAll s) :=
    Fintype.sum_bijective fa_flipAll fa_flipAll_bij
      (fun s => isingProb G β 0 s * f s)
      (fun s => isingProb G β 0 (fa_flipAll s) * f (fa_flipAll s))
      (fun s => by
        simp only []
        have hinv : fa_flipAll (fa_flipAll s) = s := by funext i; unfold fa_flipAll; simp
        rw [hinv])
  have hrw : ∑ s : ConfigSpace V, isingProb G β 0 (fa_flipAll s) * f (fa_flipAll s)
      = ∑ s : ConfigSpace V, - (isingProb G β 0 s * f s) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [fa_prob_flipAll_h0, hodd]; ring
  rw [hrw, Finset.sum_neg_distrib] at key
  linarith [key]












theorem fa_ghs_ursell3_h0_eq_zero (β : ℝ) (o x y : V) :
    eg_ursell3 G β 0 o x y = 0 := by
  unfold eg_ursell3
  have h1o : isingExpectation G β 0 (fun s => spin s o) = 0 :=
    fa_exp_odd_vanish_h0 G β _ (fun s => by rw [fa_spin_flipAll])
  have h1x : isingExpectation G β 0 (fun s => spin s x) = 0 :=
    fa_exp_odd_vanish_h0 G β _ (fun s => by rw [fa_spin_flipAll])
  have h1y : isingExpectation G β 0 (fun s => spin s y) = 0 :=
    fa_exp_odd_vanish_h0 G β _ (fun s => by rw [fa_spin_flipAll])
  have h3 : isingExpectation G β 0 (fun s => spin s o * (spin s x * spin s y)) = 0 := by
    apply fa_exp_odd_vanish_h0
    intro s
    show spin (fa_flipAll s) o * (spin (fa_flipAll s) x * spin (fa_flipAll s) y) = _
    rw [fa_spin_flipAll, fa_spin_flipAll, fa_spin_flipAll]; ring
  rw [h1o, h1x, h1y, h3]; ring




theorem fa_ghs_ursell3_h0_nonpos (β : ℝ) (o x y : V) :
    eg_ursell3 G β 0 o x y ≤ 0 :=
  le_of_eq (fa_ghs_ursell3_h0_eq_zero G β o x y)










theorem fa_ghs_ursell3_degenerate_formula (β h : ℝ) (v : V) :
    eg_ursell3 G β h v v v
      = 2 * (isingExpectation G β h (fun s => spin s v))^3
        - 2 * isingExpectation G β h (fun s => spin s v) := by
  unfold eg_ursell3
  have e_sss : (fun s : ConfigSpace V => spin s v * (spin s v * spin s v))
      = (fun s => spin s v) := by
    funext s; rw [spin_sq s v, mul_one]
  have e_ss : (fun s : ConfigSpace V => spin s v * spin s v) = (fun _ => (1:ℝ)) := by
    funext s; exact spin_sq s v
  rw [e_sss, e_ss]
  have hone : isingExpectation G β h (fun _ : ConfigSpace V => (1:ℝ)) = 1 := by
    unfold isingExpectation; simp only [mul_one]; exact isingProb_sum_eq_one G β h
  rw [hone]; ring





theorem fa_ghs_ursell3_degenerate_neg (β h : ℝ) (v : V)
    (hpos : 0 < isingExpectation G β h (fun s => spin s v))
    (hlt : isingExpectation G β h (fun s => spin s v) < 1) :
    eg_ursell3 G β h v v v < 0 := by
  rw [fa_ghs_ursell3_degenerate_formula]
  set m := isingExpectation G β h (fun s => spin s v) with hm
  nlinarith [hpos, hlt, mul_pos hpos hpos]

























theorem fa_ghs_witness_masses_both_zero :
    hnw_mass hmu_TriG 1 (fun _ => 1) hmu_triM ({0} : Finset (Fin 3)) = 0
      ∧ hnw_mass hmu_TriG 1 (fun _ => 1) gc31_zeroM ({0} : Finset (Fin 3)) = 0 :=
  ⟨gc31_mass_zero_of_odd_card hmu_TriG 1 (fun _ => 1) hmu_triM _ (by decide),
   gc31_mass_zero_of_odd_card hmu_TriG 1 (fun _ => 1) gc31_zeroM _ (by decide)⟩



theorem fa_ghs_witness_doubling_is_trivial :
    2 * hnw_mass hmu_TriG 1 (fun _ => 1) hmu_triM ({0} : Finset (Fin 3))
      = hnw_mass hmu_TriG 1 (fun _ => 1) gc31_zeroM ({0} : Finset (Fin 3)) := by
  obtain ⟨h1, h2⟩ := fa_ghs_witness_masses_both_zero
  rw [h1, h2]; ring






theorem fa_ghs_witness_sources_incompatible :
    Sharpness.sources hmu_TriG hmu_triM ≠ ({0} : Finset (Fin 3)) := by
  rw [hmu_tri_src]
  intro h
  have : (0 : Fin 3) ∈ (∅ : Finset (Fin 3)) := by rw [h]; exact Finset.mem_singleton_self 0
  exact absurd this (Finset.notMem_empty 0)






theorem fa_ghs_residue_binds :
    ¬ gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1)
        ({hmu_triM} : Finset (Sharpness.Current (Fin 3))) (∅ : Finset (Fin 3)) 0 1 2 :=
  gc31_massDoubling_fails_triangle_emptyB



















variable {d : ℕ}











theorem fa_bk_boundary_pos_1 : 0 < boxSV_boundaryCard 1 1 := by
  rw [boxSV_boundary_card 1 1 (le_refl 1)]; norm_num


theorem fa_bk_boundary_pos_2 : 0 < boxSV_boundaryCard 2 1 := by
  rw [boxSV_boundary_card 2 1 (le_refl 1)]; norm_num

open Classical in



theorem fa_bk_Tcount_faithful (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Tcount d ω n
      = ((boxFinsetBK d n).filter (fun x => IsTrifurcation d ω x)).card := rfl















theorem fa_bk_residue_entails_geometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (hx0box : x₀ ∈ box d n) (htx0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (hty0 : IsTrifurcation d ω y₀)
    (hxy : x₀ ≠ y₀) (hconn : Connected d ω x₀ y₀)
    (h : rfp_RootedArmDivergence ω n) :
    (∃ b : Site d → Site d, ¬ fsp_sameArm ω y₀ (b x₀) (b y₀))
      ∨ (∃ b : Site d → Site d, ¬ fsp_sameArm ω x₀ (b y₀) (b x₀)) := by
  obtain ⟨b, rank, hbdata, hrank, hdiv⟩ := h
  have hne : rank x₀ ≠ rank y₀ := hrank x₀ hx0box htx0 y₀ hy0box hty0 hxy hconn
  rcases lt_trichotomy (rank x₀) (rank y₀) with hlt | heq | hgt
  · exact Or.inl ⟨b, hdiv x₀ hx0box htx0 y₀ hy0box hty0 hxy hconn hlt⟩
  · exact absurd heq hne
  · exact Or.inr ⟨b, hdiv y₀ hy0box hty0 x₀ hx0box htx0 hxy.symm hconn.symm hgt⟩






theorem fa_bk_residue_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    rfp_RootedArmDivergence ω n :=
  rfp_rootedArmDivergence_of_noTrif ω n hno















theorem fa_bk_residue_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
    rfp_RootedArmDivergence ω n :=
  bc28_rootedArmDivergence_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hdeep





theorem fa_bk_count_of_residue (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (h : rfp_RootedArmDivergence ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc28_Tcount_le_boundary_of_rootedArmDivergence ω n hn h




























theorem fa_reimer_disjointOccurrence_subset {E : Type*} (A B : Set (ConfigSpace E)) :
    StatMech.disjointOccurrence A B ⊆ A ∩ B := by
  intro ω hω
  rw [StatMech.mem_disjointOccurrence] at hω
  obtain ⟨K, L, hKL, hA, hB⟩ := hω
  exact ⟨hA.mem_self, hB.mem_self⟩




theorem fa_reimer_target_true_fin1 (φ : Fin 1 → Bool → ℝ)
    (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin 1))) :
    StatMech.wprob φ (StatMech.disjointOccurrence A B)
      ≤ StatMech.wprob φ A * StatMech.wprob φ B :=
  StatMech.reimer_wprob_one φ hφ0 hφ1 A B




def fa_reimer_parA : Set (ConfigSpace (Fin 4)) := {ω | ω 0 = ω 1}


def fa_reimer_parB : Set (ConfigSpace (Fin 4)) := {ω | ω 2 = ω 3}




theorem fa_reimer_parA_not_increasing : ¬ StatMech.IsIncreasing fa_reimer_parA := by
  intro hinc
  have h1 : (fun _ => false) ∈ fa_reimer_parA := by simp [fa_reimer_parA]
  have hle : (fun _ => false : ConfigSpace (Fin 4)) ≤ (fun i => if i = 0 then true else false) := by
    intro i; simp only; split <;> simp [Bool.le_iff_imp]
  have h2 := hinc hle h1
  simp only [fa_reimer_parA, Set.mem_setOf_eq] at h2
  revert h2; decide






theorem fa_reimer_target_true_nonmonotone (φ : Fin 4 → Bool → ℝ)
    (hφ1 : ∀ i, φ i false + φ i true = 1) :
    StatMech.wprob φ (StatMech.disjointOccurrence fa_reimer_parA fa_reimer_parB)
      = StatMech.wprob φ fa_reimer_parA * StatMech.wprob φ fa_reimer_parB := by
  have hA : StatMech.DependsOn fa_reimer_parA ({0, 1} : Set (Fin 4)) := by
    intro ω ω' hag
    simp only [fa_reimer_parA, Set.mem_setOf_eq]
    rw [hag 0 (by simp), hag 1 (by simp)]
  have hB : StatMech.DependsOn fa_reimer_parB ({2, 3} : Set (Fin 4)) := by
    intro ω ω' hag
    simp only [fa_reimer_parB, Set.mem_setOf_eq]
    rw [hag 2 (by simp), hag 3 (by simp)]
  have hST : Disjoint ({0, 1} : Set (Fin 4)) ({2, 3} : Set (Fin 4)) := by
    rw [Set.disjoint_left]; intro x hx hx'; fin_cases x <;> simp_all
  exact StatMech.reimer_wprob_of_disjoint_support φ hφ1 hA hB hST












theorem fa_reimer_naive_familyBKR_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
        #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :=
  rc18_familyBKR_false











theorem fa_reimer_residue_iff_wall :
    rc18_CylBoxReflInter ↔ rc17_NonMonotoneDeficit :=
  rc18_cylBoxReflInter_iff_nonMonotone





theorem fa_reimer_residue_nonvacuous :
    ((¬ StatMech.IsIncreasing rbi_A ∧ ¬ StatMech.IsDecreasing rbi_A)
        ∨ (¬ StatMech.IsIncreasing rbi_B ∧ ¬ StatMech.IsDecreasing rbi_B))
      ∧ #(rc18_cylBoxSupp rbi_A rbi_B)
          ≤ #(rc10_reflInter (eventFamily rbi_A) (eventFamily rbi_B)) :=
  rc18_cylBoxReflInter_rbi




theorem fa_reimer_target_of_residue (h : rc18_CylBoxReflInter) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter h

end StatMech.Walls
