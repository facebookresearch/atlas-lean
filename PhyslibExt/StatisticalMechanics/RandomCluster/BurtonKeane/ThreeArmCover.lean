/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint

/-!
# The plus configuration and three-arm covers

In the plus configuration the origin has four infinite arms, so it is a trifurcation that admits no
three-arm cover.

## i. Overview

`tac_plus` opens the two coordinate axes of `ℤ²`. The label `tac_ray` (east, west, north, south or
origin) is constant along open walks avoiding the origin, so the four rays are pairwise disconnected
after removing the origin, and each is infinite. The origin is a trifurcation with four branches,
and no choice of three arms covers all of them, so `fcc_ThreeArmCover` fails for this configuration.
The file also records the count from global forest arms.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `tac_ray_const_of_connected` : the ray label is constant along open walks
- `tac_origin_isTrifurcation` : the origin is a trifurcation
- `tac_threeArmCover_false` : the plus configuration has no three-arm cover
- `tac_Tcount_le_boundary_of_globalForestArms` : global forest arms bound the count

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma tac_not_threeArmCover_of_fourArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {y : Site d} (hybox : y ∈ box d n) (htri : IsTrifurcation d ω y)
    (c : Fin 4 → Site d)
    (hconn : ∀ k, Connected d ω y (c k)) (hne : ∀ k, y ≠ c k)
    (hdis : ∀ k l, k ≠ l → ¬ Connected d (removeSite y ω) (c k) (c l)) :
    ¬ fcc_ThreeArmCover ω n := by
  classical
  rintro ⟨arms, harms⟩
  obtain ⟨hsep, hcover⟩ := harms y hybox htri
  choose i hi using fun k => hcover (c k) (hconn k) (hne k)
  obtain ⟨k, l, hkl, hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
  have hwit_kl : Connected d (removeSite y ω)
      (fsp_armWitness ω y (c k)) (fsp_armWitness ω y (c l)) := by
    have h1 := hi k
    have h2 := hi l
    rw [hcol] at h1
    exact h1.symm.trans h2
  have hck : Connected d (removeSite y ω) (fsp_armWitness ω y (c k)) (c k) :=
    fsp_armWitness_inArm ω (hconn k) (hne k)
  have hcl : Connected d (removeSite y ω) (fsp_armWitness ω y (c l)) (c l) :=
    fsp_armWitness_inArm ω (hconn l) (hne l)
  exact hdis k l hkl (hck.symm.trans (hwit_kl.trans hcl))

/-- The plus configuration: exactly the edges of the two coordinate axes of `ℤ²` are open. -/
noncomputable def tac_plus : ConfigSpace (Sym2 (Site 2)) :=
  fun e => Sym2.lift ⟨fun x y => (decide (x 1 = 0 ∧ y 1 = 0)) || (decide (x 0 = 0 ∧ y 0 = 0)),
    by
      intro x y
      simp only [Bool.or_comm]
      congr 1 <;> · rw [decide_eq_decide]; tauto⟩ e

@[simp] lemma tac_plus_mk (x y : Site 2) :
    tac_plus s(x, y) = ((decide (x 1 = 0 ∧ y 1 = 0)) || (decide (x 0 = 0 ∧ y 0 = 0))) := rfl

lemma tac_isOpenEdge_iff (x y : Site 2) :
    IsOpenEdge 2 tac_plus x y ↔
      (hypercubicLattice 2).Adj x y ∧ ((x 1 = 0 ∧ y 1 = 0) ∨ (x 0 = 0 ∧ y 0 = 0)) := by
  unfold IsOpenEdge
  rw [tac_plus_mk]
  simp [Bool.or_eq_true, decide_eq_true_eq]

/-- The ray of the plus containing a site: `1` east, `2` west, `3` north, `4` south, `0` otherwise.
-/
def tac_ray (x : Site 2) : ℤ :=
  if x 1 = 0 ∧ 1 ≤ x 0 then 1
  else if x 1 = 0 ∧ x 0 ≤ -1 then 2
  else if x 0 = 0 ∧ 1 ≤ x 1 then 3
  else if x 0 = 0 ∧ x 1 ≤ -1 then 4
  else 0

lemma tac_ray_east : tac_ray ![1, 0] = 1 := by simp [tac_ray]
lemma tac_ray_west : tac_ray ![-1, 0] = 2 := by simp [tac_ray]
lemma tac_ray_north : tac_ray ![0, 1] = 3 := by simp [tac_ray]
lemma tac_ray_south : tac_ray ![0, -1] = 4 := by simp [tac_ray]

lemma tac_ray_invariant {x y : Site 2}
    (h : IsOpenEdge 2 (removeSite (0 : Site 2) tac_plus) x y) :
    tac_ray x = tac_ray y := by
  obtain ⟨hadj, hopen⟩ := h
  have h0 : (0 : Site 2) ∉ s(x, y) := by
    by_contra hc
    rw [removeSite_apply_of_mem hc] at hopen
    exact absurd hopen (by simp)
  have hxne : x ≠ (0 : Site 2) := fun h => h0 (h ▸ Sym2.mem_mk_left _ _)
  have hyne : y ≠ (0 : Site 2) := fun h => h0 (h ▸ Sym2.mem_mk_right _ _)
  rw [removeSite_apply_of_notMem h0] at hopen
  have hplus : IsOpenEdge 2 tac_plus x y := ⟨hadj, hopen⟩
  rw [tac_isOpenEdge_iff] at hplus
  obtain ⟨hadj', hcase⟩ := hplus
  have hadjsum : (∑ i, (x i - y i).natAbs) = 1 := hadj'
  rw [Fin.sum_univ_two] at hadjsum
  have hx0ne : x ≠ ![0, 0] := by
    rwa [show (0 : Site 2) = ![0, 0] by funext i; fin_cases i <;> simp] at hxne
  have hy0ne : y ≠ ![0, 0] := by
    rwa [show (0 : Site 2) = ![0, 0] by funext i; fin_cases i <;> simp] at hyne
  rcases hcase with ⟨hx1, hy1⟩ | ⟨hx0, hy0⟩
  · have hx0z : x 0 ≠ 0 := fun hc => hx0ne (by funext i; fin_cases i <;> simp_all)
    have hy0z : y 0 ≠ 0 := fun hc => hy0ne (by funext i; fin_cases i <;> simp_all)
    have hsub1 : (x 1 - y 1).natAbs = 0 := by rw [hx1, hy1]; simp
    rw [hsub1, add_zero] at hadjsum
    have hd : (x 0 - y 0).natAbs = 1 := hadjsum
    have hsame : (1 ≤ x 0 ∧ 1 ≤ y 0) ∨ (x 0 ≤ -1 ∧ y 0 ≤ -1) := by omega
    rcases hsame with ⟨hxe, hye⟩ | ⟨hxw, hyw⟩
    · rw [tac_ray, tac_ray, ite_eq_left ⟨hx1, hxe⟩, ite_eq_left ⟨hy1, hye⟩]
    · rw [tac_ray, tac_ray]
      rw [ite_eq_right (by omega), ite_eq_left ⟨hx1, hxw⟩, ite_eq_right (by omega),
        ite_eq_left ⟨hy1, hyw⟩]
  · have hx1z : x 1 ≠ 0 := fun hc => hx0ne (by funext i; fin_cases i <;> simp_all)
    have hy1z : y 1 ≠ 0 := fun hc => hy0ne (by funext i; fin_cases i <;> simp_all)
    have hsub0 : (x 0 - y 0).natAbs = 0 := by rw [hx0, hy0]; simp
    rw [hsub0, zero_add] at hadjsum
    have hd : (x 1 - y 1).natAbs = 1 := hadjsum
    have hsame : (1 ≤ x 1 ∧ 1 ≤ y 1) ∨ (x 1 ≤ -1 ∧ y 1 ≤ -1) := by omega
    rcases hsame with ⟨hxn, hyn⟩ | ⟨hxs, hys⟩
    · rw [tac_ray, tac_ray]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hx0, hxn⟩,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hy0, hyn⟩]
    · rw [tac_ray, tac_ray]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left ⟨hx0, hxs⟩,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left ⟨hy0, hys⟩]

lemma tac_ray_const_of_connected {x y : Site 2}
    (h : Connected 2 (removeSite (0 : Site 2) tac_plus) x y) :
    tac_ray x = tac_ray y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (tac_ray_invariant hadj).trans ih

lemma tac_disconnected_of_ne_ray {x y : Site 2} (h : tac_ray x ≠ tac_ray y) :
    ¬ Connected 2 (removeSite (0 : Site 2) tac_plus) x y :=
  fun hc => h (tac_ray_const_of_connected hc)

lemma tac_conn_east (k : ℕ) : Connected 2 tac_plus ![1, 0] ![(k : ℤ) + 1, 0] := by
  induction k with
  | zero => simpa using connected_refl tac_plus ![(1:ℤ), 0]
  | succ m ih =>
    refine ih.trans ?_
    have hstep : IsOpenEdge 2 tac_plus ![(m:ℤ)+1, 0] ![((m:ℤ)+1)+1, 0] := by
      rw [tac_isOpenEdge_iff]
      exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
        Or.inl ⟨by simp, by simp⟩⟩
    have h := hstep.connected
    rwa [show (((m : ℤ) + 1) + 1) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at h

lemma tac_conn_west (k : ℕ) : Connected 2 tac_plus ![-1, 0] ![-((k : ℤ) + 1), 0] := by
  induction k with
  | zero => simpa using connected_refl tac_plus ![(-1:ℤ), 0]
  | succ m ih =>
    refine ih.trans ?_
    have hstep : IsOpenEdge 2 tac_plus ![-((m:ℤ)+1), 0] ![-(((m:ℤ)+1)+1), 0] := by
      rw [tac_isOpenEdge_iff]
      exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
        Or.inl ⟨by simp, by simp⟩⟩
    have h := hstep.connected
    rwa [show (-(((m : ℤ) + 1) + 1)) = -(((m + 1 : ℕ) : ℤ) + 1) by push_cast; ring] at h

lemma tac_conn_north (k : ℕ) : Connected 2 tac_plus ![0, 1] ![0, (k : ℤ) + 1] := by
  induction k with
  | zero => simpa using connected_refl tac_plus ![(0:ℤ), 1]
  | succ m ih =>
    refine ih.trans ?_
    have hstep : IsOpenEdge 2 tac_plus ![0, (m:ℤ)+1] ![0, ((m:ℤ)+1)+1] := by
      rw [tac_isOpenEdge_iff]
      exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
        Or.inr ⟨by simp, by simp⟩⟩
    have h := hstep.connected
    rwa [show (((m : ℤ) + 1) + 1) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at h

lemma tac_east_infinite : (cluster 2 tac_plus ![1, 0]).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (![(k : ℤ) + 1, 0] : Site 2)) ?_ ?_
  · intro a b hab; have : (a : ℤ) + 1 = (b : ℤ) + 1 := congrFun hab 0; omega
  · intro k; exact tac_conn_east k

lemma tac_west_infinite : (cluster 2 tac_plus ![-1, 0]).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (![-((k : ℤ) + 1), 0] : Site 2)) ?_ ?_
  · intro a b hab; have : -((a : ℤ) + 1) = -((b : ℤ) + 1) := congrFun hab 0; omega
  · intro k; exact tac_conn_west k

lemma tac_north_infinite : (cluster 2 tac_plus ![0, 1]).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (![0, (k : ℤ) + 1] : Site 2)) ?_ ?_
  · intro a b hab; have : (a : ℤ) + 1 = (b : ℤ) + 1 := congrFun hab 1; omega
  · intro k; exact tac_conn_north k

lemma tac_origin_east : Connected 2 tac_plus (0 : Site 2) ![1, 0] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inl ⟨by simp, by simp⟩⟩)

lemma tac_origin_west : Connected 2 tac_plus (0 : Site 2) ![-1, 0] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inl ⟨by simp, by simp⟩⟩)

lemma tac_origin_north : Connected 2 tac_plus (0 : Site 2) ![0, 1] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inr ⟨by simp, by simp⟩⟩)

lemma tac_origin_south : Connected 2 tac_plus (0 : Site 2) ![0, -1] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inr ⟨by simp, by simp⟩⟩)

lemma tac_origin_isTrifurcation : IsTrifurcation 2 tac_plus (0 : Site 2) := by
  refine ⟨![1, 0], ![-1, 0], ![0, 1], ⟨by decide, by decide, by decide⟩,
    ⟨tac_origin_east, tac_origin_west, tac_origin_north⟩,
    ⟨tac_east_infinite, tac_west_infinite, tac_north_infinite⟩, ?_, ?_, ?_⟩
  · exact tac_disconnected_of_ne_ray (by decide)
  · exact tac_disconnected_of_ne_ray (by decide)
  · exact tac_disconnected_of_ne_ray (by decide)

lemma tac_threeArmCover_false : ¬ fcc_ThreeArmCover (d := 2) tac_plus 1 := by
  refine tac_not_threeArmCover_of_fourArm tac_plus 1 (y := (0 : Site 2)) ?_
    tac_origin_isTrifurcation ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]] ?_ ?_ ?_
  · intro i; simp
  · intro k; fin_cases k
    · exact tac_origin_east
    · exact tac_origin_west
    · exact tac_origin_north
    · exact tac_origin_south
  · intro k; fin_cases k <;> exact (by decide)
  · intro k l hkl
    fin_cases k <;> fin_cases l <;>
      first
      | exact absurd rfl hkl
      | exact tac_disconnected_of_ne_ray (by decide)

lemma tac_Tcount_le_boundary_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn h

end Percolation

end StatMech
