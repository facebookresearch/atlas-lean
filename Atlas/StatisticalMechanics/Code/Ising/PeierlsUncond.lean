/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Ising.PeierlsFull
import Code.Lattice.CrossingParity
import Code.Lattice.FaceRegion

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}








noncomputable def flipOnSet (K : Set (Site d)) (σ : ConfigSpace (Site d)) :
    ConfigSpace (Site d) :=
  fun x => if x ∈ K then !(σ x) else σ x

@[simp] lemma flipOnSet_apply (K : Set (Site d)) (σ : ConfigSpace (Site d)) (x : Site d) :
    flipOnSet K σ x = if x ∈ K then !(σ x) else σ x := rfl

lemma flipOnSet_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d} (hx : x ∈ K) :
    flipOnSet K σ x = !(σ x) := by rw [flipOnSet_apply, if_pos hx]

lemma flipOnSet_not_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d}
    (hx : x ∉ K) : flipOnSet K σ x = σ x := by rw [flipOnSet_apply, if_neg hx]


lemma spin_flipOnSet_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d}
    (hx : x ∈ K) : spin (flipOnSet K σ) x = - spin σ x := by
  unfold spin; rw [flipOnSet_mem K σ hx]; by_cases h : σ x <;> simp [h]


lemma spin_flipOnSet_not_mem (K : Set (Site d)) (σ : ConfigSpace (Site d)) {x : Site d}
    (hx : x ∉ K) : spin (flipOnSet K σ) x = spin σ x := by
  unfold spin; rw [flipOnSet_not_mem K σ hx]







noncomputable def crosses (K : Set (Site d)) (e : Sym2 (Site d)) : Prop :=
  Sym2.lift ⟨fun x y => (x ∈ K ↔ y ∉ K), by
    intro x y; simp only [eq_iff_iff]
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> tauto⟩ e

@[simp] lemma crosses_mk (K : Set (Site d)) (x y : Site d) :
    crosses K s(x, y) ↔ (x ∈ K ↔ y ∉ K) := Iff.rfl


noncomputable def crossEdges (K : Set (Site d)) (B : Finset (Sym2 (Site d))) :
    Finset (Sym2 (Site d)) :=
  B.filter (crosses K)


noncomputable def contourLen (K : Set (Site d)) (B : Finset (Sym2 (Site d))) : ℕ :=
  (crossEdges K B).card




noncomputable def crossEdgeBond (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (e : Sym2 (Site d)) : ℝ :=
  Sym2.lift ⟨fun x y => if (x ∈ K ↔ y ∉ K) then bond σ s(x, y) else 0, by
    intro x y; simp only
    rw [bond_mk, bond_mk, mul_comm (spin σ x)]
    by_cases h : (x ∈ K ↔ y ∉ K)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]⟩ e

@[simp] lemma crossEdgeBond_mk (K : Set (Site d)) (σ : ConfigSpace (Site d)) (x y : Site d) :
    crossEdgeBond K σ s(x, y) = if (x ∈ K ↔ y ∉ K) then bond σ s(x, y) else 0 := rfl

lemma crossEdgeBond_of_not_crosses (K : Set (Site d)) (σ : ConfigSpace (Site d))
    {e : Sym2 (Site d)} (he : ¬ crosses K e) : crossEdgeBond K σ e = 0 := by
  induction e with | h x y => rw [crossEdgeBond_mk, if_neg]; rwa [crosses_mk] at he

lemma crossEdgeBond_of_crosses (K : Set (Site d)) (σ : ConfigSpace (Site d))
    {e : Sym2 (Site d)} (he : crosses K e) : crossEdgeBond K σ e = bond σ e := by
  induction e with | h x y => rw [crossEdgeBond_mk, if_pos]; rwa [crosses_mk] at he









lemma bond_flipOnSet_diff (K : Set (Site d)) (σ : ConfigSpace (Site d)) (x y : Site d) :
    bond (flipOnSet K σ) s(x, y) - bond σ s(x, y) = -2 * crossEdgeBond K σ s(x, y) := by
  rw [bond_mk, bond_mk]; unfold crossEdgeBond; simp only [Sym2.lift_mk]
  by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
  · rw [spin_flipOnSet_mem K σ hx, spin_flipOnSet_mem K σ hy, if_neg (by tauto)]; ring
  · rw [spin_flipOnSet_mem K σ hx, spin_flipOnSet_not_mem K σ hy, if_pos (by tauto), bond_mk]
    ring
  · rw [spin_flipOnSet_not_mem K σ hx, spin_flipOnSet_mem K σ hy, if_pos (by tauto), bond_mk]
    ring
  · rw [spin_flipOnSet_not_mem K σ hx, spin_flipOnSet_not_mem K σ hy, if_neg (by tauto)]; ring


lemma bond_flipOnSet_diff_edge (K : Set (Site d)) (σ : ConfigSpace (Site d)) (e : Sym2 (Site d)) :
    bond (flipOnSet K σ) e - bond σ e = -2 * crossEdgeBond K σ e := by
  induction e with | h x y => exact bond_flipOnSet_diff K σ x y



lemma bondSum_flipOnSet_diff (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) :
    (∑ e ∈ B, bond (flipOnSet K σ) e) - (∑ e ∈ B, bond σ e)
      = -2 * ∑ e ∈ B, crossEdgeBond K σ e := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => bond_flipOnSet_diff_edge K σ e)


lemma sum_crossEdgeBond (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) :
    (∑ e ∈ B, crossEdgeBond K σ e) = ∑ e ∈ crossEdges K B, bond σ e := by
  unfold crossEdges
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases he : crosses K e
  · rw [if_pos he, crossEdgeBond_of_crosses K σ he]
  · rw [if_neg he, crossEdgeBond_of_not_crosses K σ he]








def ContourEvent (K : Set (Site d)) (B : Finset (Sym2 (Site d))) (σ : ConfigSpace (Site d)) :
    Prop :=
  ∀ e ∈ crossEdges K B, bond σ e = -1


lemma sum_crossEdgeBond_event (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (h : ContourEvent K B σ) :
    (∑ e ∈ B, crossEdgeBond K σ e) = - (contourLen K B : ℝ) := by
  rw [sum_crossEdgeBond, Finset.sum_congr rfl (fun e he => h e he)]
  simp [contourLen]







noncomputable def flipInteriorOn {n : ℕ} (K : Set (Site d))
    (τ : {x // x ∈ box d n} → Bool) : {x // x ∈ box d n} → Bool :=
  fun x => if (x : Site d) ∈ K then !(τ x) else τ x


lemma flipInteriorOn_involutive {n : ℕ} (K : Set (Site d))
    (τ : {x // x ∈ box d n} → Bool) : flipInteriorOn K (flipInteriorOn K τ) = τ := by
  funext x; unfold flipInteriorOn; by_cases hx : (x : Site d) ∈ K <;> simp [hx]


noncomputable def flipInteriorOnEquiv {n : ℕ} (K : Set (Site d)) :
    ({x // x ∈ box d n} → Bool) ≃ ({x // x ∈ box d n} → Bool) where
  toFun := flipInteriorOn K
  invFun := flipInteriorOn K
  left_inv := flipInteriorOn_involutive K
  right_inv := flipInteriorOn_involutive K

@[simp] lemma flipInteriorOnEquiv_apply {n : ℕ} (K : Set (Site d))
    (τ : {x // x ∈ box d n} → Bool) : flipInteriorOnEquiv K τ = flipInteriorOn K τ := rfl



lemma glue_flipInteriorOn {n : ℕ} (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (τ : {x // x ∈ box d n} → Bool) :
    glue η (flipInteriorOn K τ) = flipOnSet K (glue η τ) := by
  funext x
  unfold flipOnSet flipInteriorOn
  by_cases hx : x ∈ box d n
  · rw [glue_mem _ _ hx]
    by_cases hK' : x ∈ K
    · rw [if_pos hK', glue_mem _ _ hx, if_pos hK']
    · rw [if_neg hK', glue_mem _ _ hx, if_neg hK']
  · rw [glue_not_mem _ _ hx]
    have hxK : x ∉ K := fun h => hx (hK h)
    rw [if_neg hxK, glue_not_mem _ _ hx]








lemma fvEnergy_flipInteriorOn (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d)))
    (τ : {x // x ∈ box d n} → Bool) :
    fvEnergy η n B 0 (flipInteriorOn K τ)
      = fvEnergy η n B 0 τ + 2 * ∑ e ∈ B, crossEdgeBond K (glue η τ) e := by
  unfold fvEnergy
  rw [glue_flipInteriorOn K hK η τ]
  have hbond : (∑ e ∈ B, bond (flipOnSet K (glue η τ)) e)
      = (∑ e ∈ B, bond (glue η τ) e) + (-2) * ∑ e ∈ B, crossEdgeBond K (glue η τ) e := by
    have := bondSum_flipOnSet_diff K (glue η τ) B
    linarith [this]
  rw [hbond]
  ring



lemma fvWeight_flipInteriorOn (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d))) (β : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    fvWeight η n B β 0 (flipInteriorOn K τ)
      = Real.exp (-β * (2 * ∑ e ∈ B, crossEdgeBond K (glue η τ) e))
          * fvWeight η n B β 0 τ := by
  unfold fvWeight
  rw [fvEnergy_flipInteriorOn n K hK η B τ, mul_add, Real.exp_add]
  ring





lemma fvWeight_flipInteriorOn_eq_of_event (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d))) (β : ℝ)
    (τ : {x // x ∈ box d n} → Bool) (hev : ContourEvent K B (glue η τ)) :
    fvWeight η n B β 0 τ
      = Real.exp (-(2 * β) * (contourLen K B : ℝ))
          * fvWeight η n B β 0 (flipInteriorOn K τ) := by
  rw [fvWeight_flipInteriorOn n K hK η B β τ, sum_crossEdgeBond_event K (glue η τ) B hev]
  rw [← mul_assoc, ← Real.exp_add]
  rw [show (-(2 * β) * (contourLen K B : ℝ)) + (-β * (2 * -(contourLen K B : ℝ))) = 0 by ring]
  rw [Real.exp_zero, one_mul]











noncomputable def probContour (K : Set (Site d)) (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β : ℝ) : ℝ :=
  ∑ τ : {x // x ∈ box d n} → Bool,
    (if ContourEvent K B (glue η τ) then fvProb η n B β 0 τ else 0)


lemma probContour_nonneg (K : Set (Site d)) (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β : ℝ) : 0 ≤ probContour K η n B β := by
  unfold probContour
  refine Finset.sum_nonneg (fun τ _ => ?_)
  split
  · exact fvProb_nonneg η n B β 0 τ
  · exact le_refl 0













theorem contour_energy_bound (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d))) (β : ℝ) :
    probContour K η n B β ≤ Real.exp (-(2 * β) * (contourLen K B : ℝ)) := by
  classical
  set c : ℝ := Real.exp (-(2 * β) * (contourLen K B : ℝ)) with hc
  have hcpos : 0 < c := Real.exp_pos _
  
  have hnum : (∑ τ : {x // x ∈ box d n} → Bool,
        (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ else 0))
      ≤ c * fvZ η n B β 0 := by
    
    have hstep : (∑ τ : {x // x ∈ box d n} → Bool,
          (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ else 0))
        = ∑ τ : {x // x ∈ box d n} → Bool,
            (if ContourEvent K B (glue η τ)
              then c * fvWeight η n B β 0 (flipInteriorOn K τ) else 0) := by
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      by_cases hev : ContourEvent K B (glue η τ)
      · rw [if_pos hev, if_pos hev, hc,
          fvWeight_flipInteriorOn_eq_of_event n K hK η B β τ hev]
      · rw [if_neg hev, if_neg hev]
    rw [hstep]
    
    calc (∑ τ : {x // x ∈ box d n} → Bool,
            (if ContourEvent K B (glue η τ)
              then c * fvWeight η n B β 0 (flipInteriorOn K τ) else 0))
        ≤ ∑ τ : {x // x ∈ box d n} → Bool, c * fvWeight η n B β 0 (flipInteriorOn K τ) := by
          refine Finset.sum_le_sum (fun τ _ => ?_)
          split
          · exact le_refl _
          · exact mul_nonneg hcpos.le (fvWeight_nonneg η n B β 0 _)
      _ = c * ∑ τ : {x // x ∈ box d n} → Bool, fvWeight η n B β 0 (flipInteriorOn K τ) := by
          rw [Finset.mul_sum]
      _ = c * ∑ τ : {x // x ∈ box d n} → Bool, fvWeight η n B β 0 τ := by
          congr 1
          exact Equiv.sum_comp (flipInteriorOnEquiv K) (fun τ => fvWeight η n B β 0 τ)
      _ = c * fvZ η n B β 0 := by rw [fvZ]
  
  unfold probContour fvProb
  have hZpos : 0 < fvZ η n B β 0 := fvZ_pos η n B β 0
  have hrw : (∑ τ : {x // x ∈ box d n} → Bool,
        (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ / fvZ η n B β 0 else 0))
      = (∑ τ : {x // x ∈ box d n} → Bool,
          (if ContourEvent K B (glue η τ) then fvWeight η n B β 0 τ else 0)) / fvZ η n B β 0 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hev : ContourEvent K B (glue η τ)
    · rw [if_pos hev, if_pos hev]
    · rw [if_neg hev, if_neg hev, zero_div]
  rw [hrw, div_le_iff₀ hZpos]
  linarith [hnum]










def minusSet (σ : ConfigSpace (Site d)) : Set (Site d) := {x | σ x = false}

@[simp] lemma mem_minusSet {σ : ConfigSpace (Site d)} {x : Site d} :
    x ∈ minusSet σ ↔ σ x = false := Iff.rfl



def minusGraph (σ : ConfigSpace (Site d)) : SimpleGraph (Site d) where
  Adj x y := (hypercubicLattice d).Adj x y ∧ x ∈ minusSet σ ∧ y ∈ minusSet σ
  symm := by intro x y ⟨h1, h2, h3⟩; exact ⟨h1.symm, h3, h2⟩
  loopless := ⟨fun x h => (hypercubicLattice d).irrefl h.1⟩



def minusCluster (σ : ConfigSpace (Site d)) (o : Site d) : Set (Site d) :=
  {x | (minusGraph σ).Reachable o x}


lemma origin_mem_minusCluster {σ : ConfigSpace (Site d)} (o : Site d) :
    o ∈ minusCluster σ o := SimpleGraph.Reachable.refl o


lemma minusCluster_subset_minusSet {σ : ConfigSpace (Site d)} {o : Site d}
    (ho : o ∈ minusSet σ) : minusCluster σ o ⊆ minusSet σ := by
  intro x hx
  obtain ⟨w⟩ := (hx : (minusGraph σ).Reachable o x)
  induction w with
  | nil => exact ho
  | @cons a b c hab _ ih => exact ih hab.2.2






lemma minusCluster_cross_disagree {σ : ConfigSpace (Site d)} {o : Site d}
    (ho : o ∈ minusSet σ) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y)
    (hxy : x ∈ minusCluster σ o ↔ y ∉ minusCluster σ o) :
    spin σ x * spin σ y = -1 := by
  by_cases hx : x ∈ minusCluster σ o
  · have hy : y ∉ minusCluster σ o := hxy.mp hx
    have hxminus : σ x = false := minusCluster_subset_minusSet ho hx
    have hyplus : σ y = true := by
      by_contra hyt
      have hyminus : y ∈ minusSet σ := by
        rw [mem_minusSet, Bool.not_eq_true] at *; exact hyt
      have hadjm : (minusGraph σ).Adj x y :=
        ⟨hadj, minusCluster_subset_minusSet ho hx, hyminus⟩
      exact hy (hx.trans hadjm.reachable)
    unfold spin; rw [hxminus, hyplus]; simp
  · have hy : y ∈ minusCluster σ o := by by_contra hy'; exact hx (hxy.mpr hy')
    have hyminus : σ y = false := minusCluster_subset_minusSet ho hy
    have hxplus : σ x = true := by
      by_contra hxt
      have hxminus : x ∈ minusSet σ := by
        rw [mem_minusSet, Bool.not_eq_true] at *; exact hxt
      have hadjm : (minusGraph σ).Adj y x :=
        ⟨hadj.symm, minusCluster_subset_minusSet ho hy, hxminus⟩
      exact hx (hy.trans hadjm.reachable)
    unfold spin; rw [hxplus, hyminus]; simp


lemma adj_of_mem_bondFinsetTouch {n : ℕ} {x y : Site d}
    (h : s(x, y) ∈ bondFinsetTouch d n) : (hypercubicLattice d).Adj x y := by
  classical
  unfold bondFinsetTouch at h
  rw [Finset.mem_image] at h
  obtain ⟨p, hp, hpe⟩ := h
  unfold bondPairsTouch at hp
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hadj, _⟩ := hp
  rw [Sym2.eq_iff] at hpe
  rcases hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · exact hadj.symm






theorem contourEvent_of_origin_minus {σ : ConfigSpace (Site d)} (n : ℕ)
    (ho : σ (origin d) = false) :
    ContourEvent (minusCluster σ (origin d)) (bondFinsetTouch d n) σ := by
  intro e he
  unfold crossEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨heB, hcr⟩ := he
  induction e with
  | h x y =>
    rw [crosses_mk] at hcr
    have hadj : (hypercubicLattice d).Adj x y := adj_of_mem_bondFinsetTouch (n := n) heB
    rw [bond_mk]
    exact minusCluster_cross_disagree (mem_minusSet.mpr ho) hadj hcr








lemma minusSet_glue_plus_subset_box {n : ℕ} (τ : {x // x ∈ box d n} → Bool) :
    minusSet (glue (plusField d) τ) ⊆ box d n := by
  intro x hx
  by_contra hxbox
  rw [mem_minusSet, glue_not_mem _ _ hxbox] at hx
  simp [plusField] at hx


lemma minusCluster_glue_plus_subset_box {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    minusCluster (glue (plusField d) τ) (origin d) ⊆ box d n := fun _ hx =>
  minusSet_glue_plus_subset_box τ
    (minusCluster_subset_minusSet (mem_minusSet.mpr ho) hx)


lemma minusCluster_glue_plus_finite {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    (minusCluster (glue (plusField d) τ) (origin d)).Finite :=
  (box_finite d n).subset (minusCluster_glue_plus_subset_box τ ho)



noncomputable def clusterFamily (n : ℕ) : Finset (Finset (Site d)) :=
  (boxFinset d n).powerset


noncomputable def minusClusterFinset {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) : Finset (Site d) :=
  (minusCluster_glue_plus_finite τ ho).toFinset

lemma minusClusterFinset_mem_family {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    minusClusterFinset τ ho ∈ clusterFamily (d := d) n := by
  unfold clusterFamily minusClusterFinset
  rw [Finset.mem_powerset]
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  rw [mem_boxFinset]
  exact minusCluster_glue_plus_subset_box τ ho hx

lemma minusClusterFinset_coe {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    ((minusClusterFinset τ ho : Finset (Site d)) : Set (Site d))
      = minusCluster (glue (plusField d) τ) (origin d) :=
  Set.Finite.coe_toFinset _

set_option maxHeartbeats 1000000 in
lemma clusterFamily_subset_boxFinset {n : ℕ} {K : Finset (Site d)}
    (hK : K ∈ clusterFamily (d := d) n) : K ⊆ boxFinset d n :=
  Finset.mem_powerset.mp hK

lemma clusterFamily_subset_box {n : ℕ} {K : Finset (Site d)}
    (hK : K ∈ clusterFamily (d := d) n) : (↑K : Set (Site d)) ⊆ box d n := by
  intro x hx
  rw [Finset.mem_coe] at hx
  have hmem := clusterFamily_subset_boxFinset hK hx
  rw [mem_boxFinset] at hmem
  exact hmem













theorem probOriginMinus_le_sum_probContour (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ clusterFamily (d := d) n,
          probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
  classical
  unfold probOriginMinus probContour
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  set g : Finset (Site d) → ℝ := fun K =>
    (if ContourEvent (↑K) (bondFinsetTouch d n) (glue (plusField d) τ)
      then fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ else 0) with hg
  have hgnn : ∀ K ∈ clusterFamily (d := d) n, 0 ≤ g K := by
    intro K _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField d) τ (origin d) = false
  · rw [if_pos ho]
    have hKmem : minusClusterFinset τ ho ∈ clusterFamily (d := d) n :=
      minusClusterFinset_mem_family τ ho
    have hev : ContourEvent (↑(minusClusterFinset τ ho)) (bondFinsetTouch d n)
        (glue (plusField d) τ) := by
      rw [minusClusterFinset_coe τ ho]; exact contourEvent_of_origin_minus n ho
    have hge : fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ
        = g (minusClusterFinset τ ho) := by rw [hg]; dsimp only; rw [if_pos hev]
    rw [hge]
    exact Finset.single_le_sum hgnn hKmem
  · rw [if_neg ho]
    exact Finset.sum_nonneg hgnn

set_option maxHeartbeats 1000000 in











theorem probOriginMinus_le_sum_exp (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ clusterFamily (d := d) n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  refine le_trans (probOriginMinus_le_sum_probContour n β) ?_
  apply Finset.sum_le_sum
  intro K hK
  have hKbox : (↑K : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hK
  have hbound := contour_energy_bound n (↑K) hKbox (plusField d) (bondFinsetTouch d n) β
  exact hbound























def ContourCountBound (d n : ℕ) (β : ℝ) : Prop :=
  ∑ K ∈ clusterFamily (d := d) n,
      Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ))
    ≤ peierlsBound d β







theorem peierlsContourBound_of_contourCount (n : ℕ) (β : ℝ)
    (hCount : ContourCountBound d n β) :
    PeierlsContourBound d n β :=
  le_trans (probOriginMinus_le_sum_exp n β) hCount







theorem peierls_long_range_order_of_contourCount (hd : 2 ≤ d)
    (hCount : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → ContourCountBound d n β) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₀, hβ₀⟩ := hCount
  refine peierls_long_range_order' hd ⟨β₀, fun n β hβ => ?_⟩
  exact peierlsContourBound_of_contourCount n β (hβ₀ n β hβ)

end Ising

end StatMech
