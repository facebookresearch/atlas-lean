/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















import Code.Sharpness.ABGhostInfluence
import Code.Sharpness.MeanfieldPercoInhom

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

private noncomputable def abccLaw (p : Sym2 W → ℝ) (e : Sym2 W) (b : Bool) : ℝ :=
  if b then p e else 1 - p e

private theorem abccLaw_sum_one (p : Sym2 W → ℝ) (e : Sym2 W) :
    abccLaw p e false + abccLaw p e true = 1 := by
  simp [abccLaw]

private theorem abcc_probV_eq_wprob (p : Sym2 W → ℝ)
    (A : Set (ConfigSpace (Sym2 W))) :
    probV p A = wprob (abccLaw p) A := by
  unfold probV wprob configWeightV pweight edgeWeightV abccLaw
  rfl



theorem abcc_connEvent_singleton_symm (omega : ConfigSpace (Sym2 W)) (a b : W) :
    omega ∈ connEvent H Set.univ a {b} ↔ omega ∈ connEvent H Set.univ b {a} := by
  constructor
  · rintro ⟨ha, z, hzU, hz, hab⟩
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨Set.mem_univ b, a, Set.mem_univ a, Set.mem_singleton a, hab.symm⟩
  · rintro ⟨hb, z, hzU, hz, hba⟩
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨Set.mem_univ a, b, Set.mem_univ b, Set.mem_singleton b, hba.symm⟩



theorem abcc_restricted_iff_blocked (omega : ConfigSpace (Sym2 W)) (u x g : W) :
    omega ∈ connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ ↔
      g ∈ mpiBlockedSet H {u} omega ∧ x ∉ mpiBlockedSet H {u} omega := by
  constructor
  · rintro ⟨hux, hug⟩
    have hxu : omega ∈ connEvent H Set.univ x {u} :=
      (abcc_connEvent_singleton_symm H omega u x).mp hux
    have hgu_not : omega ∉ connEvent H Set.univ g {u} := by
      intro hgu
      exact hug ((abcc_connEvent_singleton_symm H omega u g).mpr hgu)
    exact ⟨(mpi_mem_blockedSet_iff H {u} omega g).mpr hgu_not,
      (mpi_not_mem_blockedSet_iff H {u} omega x).mpr hxu⟩
  · rintro ⟨hg, hx⟩
    have hgu_not : omega ∉ connEvent H Set.univ g {u} :=
      (mpi_mem_blockedSet_iff H {u} omega g).mp hg
    have hxu : omega ∈ connEvent H Set.univ x {u} :=
      (mpi_not_mem_blockedSet_iff H {u} omega x).mp hx
    exact ⟨(abcc_connEvent_singleton_symm H omega u x).mpr hxu, by
      intro hug
      exact hgu_not ((abcc_connEvent_singleton_symm H omega u g).mp hug)⟩



theorem abcc_probV_surface_partition (p : Sym2 W → ℝ) (B : Set W)
    (P : Finset W → Prop) [DecidablePred P]
    (C : Set (ConfigSpace (Sym2 W))) :
    probV p ({omega | P (mpiBlockedSet H B omega)} ∩ C) =
      ∑ S ∈ (Finset.univ.filter P), probV p (mpiSurfaceEvent H B S ∩ C) := by
  classical
  unfold probV
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  let S0 := mpiBlockedSet H B omega
  by_cases hP : P S0
  · have hS0 : S0 ∈ Finset.univ.filter P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩
    by_cases hC : omega ∈ C
    · rw [Set.indicator_of_mem
        (show omega ∈ {omega | P (mpiBlockedSet H B omega)} ∩ C from ⟨hP, hC⟩)]
      symm
      calc
        (∑ S ∈ Finset.univ.filter P,
            (mpiSurfaceEvent H B S ∩ C).indicator (fun _ => (1 : ℝ)) omega *
              configWeightV p omega) =
            (mpiSurfaceEvent H B S0 ∩ C).indicator (fun _ => (1 : ℝ)) omega *
              configWeightV p omega := by
          apply Finset.sum_eq_single S0
          · intro S hS hne
            rw [Set.indicator_of_notMem]
            · exact zero_mul _
            · rintro ⟨hsurf, _⟩
              exact hne hsurf.symm
          · exact fun hnot => False.elim (hnot hS0)
        _ = configWeightV p omega := by
          rw [Set.indicator_of_mem (show omega ∈ mpiSurfaceEvent H B S0 ∩ C from ⟨rfl, hC⟩),
            one_mul]
        _ = 1 * configWeightV p omega := by rw [one_mul]
    · rw [Set.indicator_of_notMem
        (show omega ∉ {omega | P (mpiBlockedSet H B omega)} ∩ C from fun h => hC h.2),
        zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro S _
      rw [Set.indicator_of_notMem]
      · exact zero_mul _
      · exact fun h => hC h.2
  · rw [Set.indicator_of_notMem
      (show omega ∉ {omega | P (mpiBlockedSet H B omega)} ∩ C from fun h => hP h.1), zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro S hS
    rw [Set.indicator_of_notMem]
    · exact zero_mul _
    · rintro ⟨hsurf, _⟩
      have hPS : P S := (Finset.mem_filter.mp hS).2
      apply hP
      change P (mpiBlockedSet H B omega)
      rw [show mpiBlockedSet H B omega = S from hsurf]
      exact hPS




theorem abcc_conn_inside_blocked (B : Set W) (S : Finset W)
    (omega : ConfigSpace (Sym2 W)) (hS : mpiBlockedSet H B omega = S)
    (y g : W) (hgS : g ∈ S)
    (hyg : omega ∈ connEvent H Set.univ y {g}) :
    omega ∈ connEvent H (S : Set W) y {g} := by
  obtain ⟨z, _, hz, walk, _⟩ := shk_walk_of_connToSet H omega Set.univ y {g} hyg
  simp only [Set.mem_singleton_iff] at hz
  subst z
  have hsupp : ∀ z ∈ walk.support, z ∈ S := by
    intro z hz
    by_contra hzS
    have hzu : ConnToSet H omega Set.univ z B := by
      apply (mpi_not_mem_blockedSet_iff H B omega z).mp
      simpa [hS] using hzS
    obtain ⟨b, _, hbB, q, _⟩ := shk_walk_of_connToSet H omega Set.univ z B hzu
    let zg : (openSub H omega).Walk z g := walk.dropUntil z hz
    let gb : (openSub H omega).Walk g b := zg.reverse.append q
    have hgb : ConnToSet H omega Set.univ g B :=
      ⟨Set.mem_univ g, b, Set.mem_univ b, hbB,
        ⟨gb.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩
    have hblocked : g ∈ mpiBlockedSet H B omega := by simpa [hS] using hgS
    exact (mpi_mem_blockedSet_iff H B omega g).mp hblocked hgb
  have hySupp : y ∈ walk.support := by simp
  have hgSupp : g ∈ walk.support := by simp
  exact ⟨hsupp y hySupp, g, hsupp g hgSupp,
    Set.mem_singleton g, ⟨walk.induce (S : Set W) hsupp⟩⟩



theorem abcc_conn_surface_factor (p : Sym2 W → ℝ)
    (B : Set W) (S : Finset W) (y g : W) :
    probV p (connEvent H (S : Set W) y {g} ∩ mpiSurfaceEvent H B S) =
      probV p (connEvent H (S : Set W) y {g}) *
        probV p (mpiSurfaceEvent H B S) := by
  rw [abcc_probV_eq_wprob, abcc_probV_eq_wprob,
    abcc_probV_eq_wprob]
  exact wprob_inter_eq_mul_of_determined
    (connEvent H (S : Set W) y {g}) (mpiSurfaceEvent H B S)
    (K := mpiInternalEdges (S : Set W))
    (L := (mpiInternalEdges (S : Set W))ᶜ)
    disjoint_compl_right (abccLaw p) (abccLaw_sum_one p)
    (mpi_connEvent_determined_internal H S y g)
    (mpi_surfaceEvent_determined_exterior H B S)



theorem abcc_conn_surface_factor_set (p : Sym2 W → ℝ)
    (B : Set W) (S : Finset W) (y : W) (T : Set W) :
    probV p (connEvent H (S : Set W) y T ∩ mpiSurfaceEvent H B S) =
      probV p (connEvent H (S : Set W) y T) *
        probV p (mpiSurfaceEvent H B S) := by
  rw [abcc_probV_eq_wprob, abcc_probV_eq_wprob,
    abcc_probV_eq_wprob]
  exact wprob_inter_eq_mul_of_determined
    (connEvent H (S : Set W) y T) (mpiSurfaceEvent H B S)
    (K := mpiInternalEdges (S : Set W))
    (L := (mpiInternalEdges (S : Set W))ᶜ)
    disjoint_compl_right (abccLaw p) (abccLaw_sum_one p)
    (mpi_connEventSet_determined_internal H S y T)
    (mpi_surfaceEvent_determined_exterior H B S)




theorem abcc_surface_inter_conn_eq_inside (B : Set W) (S : Finset W)
    (g y : W) (hgS : g ∈ S) :
    mpiSurfaceEvent H B S ∩ connEvent H Set.univ y {g} =
      mpiSurfaceEvent H B S ∩ connEvent H (S : Set W) y {g} := by
  ext omega
  constructor
  · rintro ⟨hS, hyg⟩
    exact ⟨hS, abcc_conn_inside_blocked H B S omega hS y g hgS hyg⟩
  · rintro ⟨hS, hyg⟩
    obtain ⟨z, _, hz, walk, _⟩ := shk_walk_of_connToSet H omega (S : Set W) y {g} hyg
    exact ⟨hS, ⟨Set.mem_univ y, z, Set.mem_univ z, hz,
      ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩⟩



theorem abcc_surface_inter_conn_eq_inside_set (B : Set W) (S : Finset W)
    (T : Set W) (y : W) (hTS : T ⊆ (S : Set W)) :
    mpiSurfaceEvent H B S ∩ connEvent H Set.univ y T =
      mpiSurfaceEvent H B S ∩ connEvent H (S : Set W) y T := by
  ext omega
  constructor
  · rintro ⟨hS, hyT⟩
    obtain ⟨z, _, hzT, walk, _⟩ :=
      shk_walk_of_connToSet H omega Set.univ y T hyT
    have hzS : z ∈ S := hTS hzT
    have hyz : omega ∈ connEvent H Set.univ y {z} :=
      ⟨Set.mem_univ y, z, Set.mem_univ z, Set.mem_singleton z,
        ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩
    obtain ⟨hyS, w, hwS, hwz, hconn⟩ :=
      abcc_conn_inside_blocked H B S omega hS y z hzS hyz
    simp only [Set.mem_singleton_iff] at hwz
    subst w
    exact ⟨hS, hyS, z, hzS, hzT, hconn⟩
  · rintro ⟨hS, hyT⟩
    obtain ⟨z, _, hzT, walk, _⟩ :=
      shk_walk_of_connToSet H omega (S : Set W) y T hyT
    exact ⟨hS, Set.mem_univ y, z, Set.mem_univ z, hzT,
      ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩


theorem abcc_conn_inside_subset_global (S : Finset W) (y g : W) :
    connEvent H (S : Set W) y {g} ⊆ connEvent H Set.univ y {g} := by
  intro omega hyg
  obtain ⟨z, _, hz, walk, _⟩ := shk_walk_of_connToSet H omega (S : Set W) y {g} hyg
  exact ⟨Set.mem_univ y, z, Set.mem_univ z, hz,
    ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩


theorem abcc_conn_inside_set_subset_global (S : Finset W) (y : W) (T : Set W) :
    connEvent H (S : Set W) y T ⊆ connEvent H Set.univ y T := by
  intro omega hyT
  obtain ⟨z, _, hzT, walk, _⟩ :=
    shk_walk_of_connToSet H omega (S : Set W) y T hyT
  exact ⟨Set.mem_univ y, z, Set.mem_univ z, hzT,
    ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩



theorem abcc_cluster_conditioning_set (p : Sym2 W → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (u x y : W) (T : Set W) :
    probV p
        ((connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u T)ᶜ) ∩
          connEvent H Set.univ y T) ≤
      probV p (connEvent H Set.univ u {x} ∩
          (connEvent H Set.univ u T)ᶜ) *
        probV p (connEvent H Set.univ y T) := by
  let R : Set (ConfigSpace (Sym2 W)) :=
    connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u T)ᶜ
  let Y : Set (ConfigSpace (Sym2 W)) := connEvent H Set.univ y T
  let P : Finset W → Prop := fun S => (∀ z ∈ T, z ∈ S) ∧ x ∉ S
  letI : DecidablePred P := Classical.decPred P
  have hRset : R = {omega | P (mpiBlockedSet H {u} omega)} := by
    ext omega
    constructor
    · rintro ⟨hux, huT⟩
      constructor
      · intro z hzT
        rw [mpi_mem_blockedSet_iff]
        intro hzu
        have huz : omega ∈ connEvent H Set.univ u {z} :=
          (abcc_connEvent_singleton_symm H omega u z).mpr hzu
        obtain ⟨huU, w, hwU, hwz, hconn⟩ := huz
        simp only [Set.mem_singleton_iff] at hwz
        subst w
        exact huT ⟨huU, z, hwU, hzT, hconn⟩
      · rw [mpi_not_mem_blockedSet_iff]
        exact (abcc_connEvent_singleton_symm H omega u x).mp hux
    · rintro ⟨hTS, hxS⟩
      have hxu : omega ∈ connEvent H Set.univ x {u} :=
        (mpi_not_mem_blockedSet_iff H {u} omega x).mp hxS
      have hux : omega ∈ connEvent H Set.univ u {x} :=
        (abcc_connEvent_singleton_symm H omega u x).mpr hxu
      refine ⟨hux, ?_⟩
      intro huT
      obtain ⟨_, z, _, hzT, huz⟩ := huT
      have hzu : omega ∈ connEvent H Set.univ z {u} :=
        (abcc_connEvent_singleton_symm H omega u z).mp
          ⟨Set.mem_univ u, z, Set.mem_univ z, Set.mem_singleton z, huz⟩
      exact (mpi_mem_blockedSet_iff H {u} omega z).mp (hTS z hzT) hzu
  have hjoint : probV p (R ∩ Y) =
      ∑ S ∈ (Finset.univ.filter P), probV p (mpiSurfaceEvent H {u} S ∩ Y) := by
    rw [hRset]
    exact abcc_probV_surface_partition H p {u} P Y
  have hRprob : probV p R =
      ∑ S ∈ (Finset.univ.filter P), probV p (mpiSurfaceEvent H {u} S) := by
    calc
      probV p R = probV p ({omega | P (mpiBlockedSet H {u} omega)} ∩ Set.univ) := by
        rw [hRset, Set.inter_univ]
      _ = ∑ S ∈ (Finset.univ.filter P),
          probV p (mpiSurfaceEvent H {u} S ∩ Set.univ) :=
        abcc_probV_surface_partition H p {u} P Set.univ
      _ = _ := by simp only [Set.inter_univ]
  change probV p (R ∩ Y) ≤ probV p R * probV p Y
  rw [hjoint, hRprob]
  calc
    (∑ S ∈ Finset.univ.filter P, probV p (mpiSurfaceEvent H {u} S ∩ Y)) ≤
        ∑ S ∈ Finset.univ.filter P,
          probV p Y * probV p (mpiSurfaceEvent H {u} S) := by
      apply Finset.sum_le_sum
      intro S hS
      have hTS : T ⊆ (S : Set W) := (Finset.mem_filter.mp hS).2.1
      have heq : mpiSurfaceEvent H {u} S ∩ Y =
          mpiSurfaceEvent H {u} S ∩ connEvent H (S : Set W) y T :=
        abcc_surface_inter_conn_eq_inside_set H {u} S T y hTS
      rw [heq, Set.inter_comm, abcc_conn_surface_factor_set H]
      have hconn : probV p (connEvent H (S : Set W) y T) ≤ probV p Y :=
        abgi_probV_mono p hp (abcc_conn_inside_set_subset_global H S y T)
      exact mul_le_mul_of_nonneg_right hconn
        (abgi_probV_nonneg p hp (mpiSurfaceEvent H {u} S))
    _ = probV p Y *
        (∑ S ∈ Finset.univ.filter P, probV p (mpiSurfaceEvent H {u} S)) := by
      rw [Finset.mul_sum]
    _ = (∑ S ∈ Finset.univ.filter P, probV p (mpiSurfaceEvent H {u} S)) *
        probV p Y := by ring




theorem abcc_cluster_conditioning (p : Sym2 W → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (u x y g : W) :
    probV p
        ((connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ) ∩
          connEvent H Set.univ y {g}) ≤
      probV p (connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ) *
        probV p (connEvent H Set.univ y {g}) := by
  let R : Set (ConfigSpace (Sym2 W)) :=
    connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ
  let Y : Set (ConfigSpace (Sym2 W)) := connEvent H Set.univ y {g}
  let P : Finset W → Prop := fun S => g ∈ S ∧ x ∉ S
  letI : DecidablePred P := fun S => inferInstanceAs (Decidable (g ∈ S ∧ x ∉ S))
  have hRset : R = {omega | P (mpiBlockedSet H {u} omega)} := by
    ext omega
    exact abcc_restricted_iff_blocked H omega u x g
  have hjoint : probV p (R ∩ Y) =
      ∑ S ∈ (Finset.univ.filter P), probV p (mpiSurfaceEvent H {u} S ∩ Y) := by
    rw [hRset]
    exact abcc_probV_surface_partition H p {u} P Y
  have hRprob : probV p R =
      ∑ S ∈ (Finset.univ.filter P), probV p (mpiSurfaceEvent H {u} S) := by
    calc
      probV p R = probV p ({omega | P (mpiBlockedSet H {u} omega)} ∩ Set.univ) := by
        rw [hRset, Set.inter_univ]
      _ = ∑ S ∈ (Finset.univ.filter P),
          probV p (mpiSurfaceEvent H {u} S ∩ Set.univ) :=
        abcc_probV_surface_partition H p {u} P Set.univ
      _ = _ := by simp only [Set.inter_univ]
  change probV p (R ∩ Y) ≤ probV p R * probV p Y
  rw [hjoint, hRprob]
  calc
    (∑ S ∈ Finset.univ.filter P, probV p (mpiSurfaceEvent H {u} S ∩ Y)) ≤
        ∑ S ∈ Finset.univ.filter P,
          probV p Y * probV p (mpiSurfaceEvent H {u} S) := by
      apply Finset.sum_le_sum
      intro S hS
      have hgS : g ∈ S := (Finset.mem_filter.mp hS).2.1
      have heq : mpiSurfaceEvent H {u} S ∩ Y =
          mpiSurfaceEvent H {u} S ∩ connEvent H (S : Set W) y {g} := by
        exact abcc_surface_inter_conn_eq_inside H {u} S g y hgS
      rw [heq, Set.inter_comm, abcc_conn_surface_factor H]
      have hconn : probV p (connEvent H (S : Set W) y {g}) ≤ probV p Y :=
        abgi_probV_mono p hp (abcc_conn_inside_subset_global H S y g)
      exact mul_le_mul_of_nonneg_right hconn
        (abgi_probV_nonneg p hp (mpiSurfaceEvent H {u} S))
    _ = probV p Y *
        (∑ S ∈ Finset.univ.filter P, probV p (mpiSurfaceEvent H {u} S)) := by
      rw [Finset.mul_sum]
    _ = (∑ S ∈ Finset.univ.filter P, probV p (mpiSurfaceEvent H {u} S)) *
        probV p Y := by ring





theorem abcc_closedPivotal_le_products (p : Sym2 W → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (u x y g : W) :
    probV p (abgiClosedPivotal s(x, y) (connEvent H Set.univ u {g})) ≤
      probV p (connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ) *
          probV p (connEvent H Set.univ y {g}) +
        probV p (connEvent H Set.univ u {y} ∩ (connEvent H Set.univ u {g})ᶜ) *
          probV p (connEvent H Set.univ x {g}) := by
  calc
    probV p (abgiClosedPivotal s(x, y) (connEvent H Set.univ u {g})) ≤
        probV p
            ((connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ) ∩
              connEvent H Set.univ y {g}) +
          probV p
            ((connEvent H Set.univ u {y} ∩ (connEvent H Set.univ u {g})ᶜ) ∩
              connEvent H Set.univ x {g}) :=
      abgi_probV_closedPivotal_conn_le_oriented p hp H Set.univ u {g} x y
        (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
    _ ≤ _ := add_le_add
      (abcc_cluster_conditioning H p hp u x y g)
      (abcc_cluster_conditioning H p hp u y x g)



theorem abcc_closedPivotal_le_products_set (p : Sym2 W → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (u x y : W) (T : Set W) :
    probV p (abgiClosedPivotal s(x, y) (connEvent H Set.univ u T)) ≤
      probV p (connEvent H Set.univ u {x} ∩
          (connEvent H Set.univ u T)ᶜ) *
          probV p (connEvent H Set.univ y T) +
        probV p (connEvent H Set.univ u {y} ∩
          (connEvent H Set.univ u T)ᶜ) *
          probV p (connEvent H Set.univ x T) := by
  calc
    probV p (abgiClosedPivotal s(x, y) (connEvent H Set.univ u T)) ≤
        probV p
            ((connEvent H Set.univ u {x} ∩
                (connEvent H Set.univ u T)ᶜ) ∩
              connEvent H Set.univ y T) +
          probV p
            ((connEvent H Set.univ u {y} ∩
                (connEvent H Set.univ u T)ᶜ) ∩
              connEvent H Set.univ x T) :=
      abgi_probV_closedPivotal_conn_le_oriented p hp H Set.univ u T x y
        (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
    _ ≤ _ := add_le_add
      (abcc_cluster_conditioning_set H p hp u x y T)
      (abcc_cluster_conditioning_set H p hp u y x T)

end Sharpness
end StatMech
