/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.IsingBridgeTargets
import Code.FK.TwoPointInfinite
import Code.FK.BoxTailLimit
import Code.FK.FreeWeakLimit
import Code.FK.MonotoneWeakLimit
import Code.FK.FreeWiredAgreeClose
import Code.Ising.TransitionFK












open Filter
open MeasureTheory

namespace StatMech
namespace Exact3D

open FK


def ising3DOriginBoxVertex (n : ℕ) : boxVerts 3 n :=
  ⟨ising3DOrigin, ising3DOrigin_mem_box n⟩


def ising3DXAxisBoxVertex (n : ℕ) : boxVerts 3 n :=
  ⟨ising3DXAxisRay n, ising3DXAxisRay_mem_box_self n⟩


def ising3DXAxisBoxVertexInBox (N n : ℕ) (h : n ≤ N) : boxVerts 3 N :=
  ⟨ising3DXAxisRay n, ising3DXAxisRay_mem_box_le h⟩



noncomputable def freeFiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((freeFiniteMeasure 3 n hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))



noncomputable def wiredFiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((wiredFiniteMeasure 3 n hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))



noncomputable def freeInfiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((freeInfiniteVolume 3 hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))



noncomputable def wiredInfiniteVolumeXAxisConnectionQ2
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) : ℝ :=
  ((wiredInfiniteVolume 3 hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))



noncomputable def freeInfiniteVolumeXAxisConnectionOfBetaQ2
    (β : ℝ) (hβ : 0 < β) (n : ℕ) : ℝ :=
  freeInfiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) n



noncomputable def freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxConnEvent 3 n (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n)))




noncomputable def freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  if hn : n ≤ N then
    ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
      (boxConnEvent 3 N (ising3DOriginBoxVertex N)
        (ising3DXAxisBoxVertexInBox N n hn)))
  else
    0



noncomputable def wiredInfiniteVolumeXAxisConnectionOfBetaQ2
    (β : ℝ) (hβ : 0 < β) (n : ℕ) : ℝ :=
  wiredInfiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) n




def FreeXAxisQ2ConnectionAgrees (β : ℝ) (hβ : 0 < β) : Prop :=
  FreeXAxisFKConnectionAgrees β
    (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ)




def FreeXAxisWiredQ2ConnectionAgrees (β : ℝ) (hβ : 0 < β) : Prop :=
  FreeXAxisFKConnectionAgrees β
    (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ)




def PlusXAxisWiredQ2ConnectionAgrees (β : ℝ) (hβ : 0 < β) : Prop :=
  PlusXAxisFKConnectionAgrees β
    (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ)



theorem freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
    (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N) :
    Tendsto (fun m =>
      (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))
      atTop
      (nhds ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))) := by
  simpa [boxConnEvent] using
    (fk_free_infinite_measure (d := d) N hp hp1
      (S := connEvent (boxGraph d N) x y)
      (connEvent_isIncreasing (boxGraph d N) x y))



theorem tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    Tendsto (fun N =>
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n)
      atTop
      (nhds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)) := by
  simpa [freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume,
    freeInfiniteVolumeXAxisConnectionOfBetaQ2, freeInfiniteVolumeXAxisConnectionQ2]
    using freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
      3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)



theorem freeFiniteMeasure_real_boxConnEvent_mono_outer_q2
    (d : ℕ) {n M₁ M₂ : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hM₁ : n ≤ M₁) (hM : M₁ ≤ M₂)
    (x y : boxVerts d n) :
    ((freeFiniteMeasure d M₁ hp hp1 (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d n x y)
      ≤
    ((freeFiniteMeasure d M₂ hp hp1 (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d n x y) := by
  have hmono := fkFreeLimit_monotone (d := d) n hp hp1
    (S := connEvent (boxGraph d n) x y)
    (connEvent_isIncreasing (boxGraph d n) x y)
  have hle := hmono (Nat.sub_le_sub_right hM n)
  have hM₂n : n ≤ M₂ := hM₁.trans hM
  have hM₁' : n + (M₁ - n) = M₁ := Nat.add_sub_of_le hM₁
  have hM₂' : n + (M₂ - n) = M₂ := Nat.add_sub_of_le hM₂n
  simpa [boxConnEvent, hM₁', hM₂'] using hle




theorem boxConnEvent_subset_full_boxConnEvent_of_le
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    boxConnEvent d n x y ⊆
      boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) := by
  intro ω hω
  rw [boxConnEvent, Set.mem_preimage] at hω ⊢
  rw [← boxRestrictLE_boxRestrict d h ω] at hω
  exact hω.map
    { toFun := boxVertInclLE d h
      map_rel' := by
        intro a b hab
        rw [openSub_adj] at hab ⊢
        constructor
        · simpa [boxGraph, boxVertInclLE] using hab.1
        · simpa [boxRestrictLE, innerEdgeLE] using hab.2 }





def boxConnectionDetourEvent
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    Set (ConfigSpace (Sym2 (Lattice.Site d))) :=
  boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) \
    boxConnEvent d n x y



theorem full_boxConnEvent_eq_inner_union_detour_of_le
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) =
      boxConnEvent d n x y ∪ boxConnectionDetourEvent d h x y := by
  apply Set.Subset.antisymm
  · intro ω hω
    by_cases hinner : ω ∈ boxConnEvent d n x y
    · exact Or.inl hinner
    · exact Or.inr ⟨hω, hinner⟩
  · intro ω hω
    rcases hω with hinner | hdetour
    · exact boxConnEvent_subset_full_boxConnEvent_of_le d h x y hinner
    · exact hdetour.1




theorem measureReal_full_boxConnEvent_eq_inner_add_detour
    (d : ℕ) (μ : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    [IsFiniteMeasure μ]
    {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y)) =
      μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) := by
  have hdisj :
      Disjoint (boxConnEvent d n x y) (boxConnectionDetourEvent d h x y) := by
    exact Set.disjoint_left.mpr (by
      intro ω hinner hdetour
      exact hdetour.2 hinner)
  have hdetour_meas : MeasurableSet (boxConnectionDetourEvent d h x y) := by
    unfold boxConnectionDetourEvent
    exact (measurableSet_boxConnEvent d N
      (boxVertInclLE d h x) (boxVertInclLE d h y)).diff
        (measurableSet_boxConnEvent d n x y)
  calc
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y))
        = μ.real (boxConnEvent d n x y ∪ boxConnectionDetourEvent d h x y) := by
          rw [full_boxConnEvent_eq_inner_union_detour_of_le]
    _ = μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) :=
          measureReal_union hdisj hdetour_meas




theorem measureReal_full_boxConnEvent_le_inner_add_detour
    (d : ℕ) (μ : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y)) ≤
      μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) := by
  calc
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y))
        = μ.real (boxConnEvent d n x y ∪ boxConnectionDetourEvent d h x y) := by
          rw [full_boxConnEvent_eq_inner_union_detour_of_le]
    _ ≤ μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) :=
          measureReal_union_le _ _



theorem boxVertInclLE_range_iff
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (z : boxVerts d N) :
    (∃ x : boxVerts d n, boxVertInclLE d h x = z) ↔
      (z : Lattice.Site d) ∈ Lattice.box d n := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hz
    exact ⟨⟨(z : Lattice.Site d), hz⟩, Subtype.ext rfl⟩



theorem openSub_boxRestrict_adj_boxVertInclLE
    (d : ℕ) {n N : ℕ} (h : n ≤ N)
    (ω : ConfigSpace (Sym2 (Lattice.Site d))) (x y : boxVerts d n) :
    (openSub (boxGraph d N) (boxRestrict d N ω)).Adj
        (boxVertInclLE d h x) (boxVertInclLE d h y)
      ↔ (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSub_adj, openSub_adj]
  have hadj :
      (boxGraph d N).Adj (boxVertInclLE d h x) (boxVertInclLE d h y)
        ↔ (boxGraph d n).Adj x y := by
    simp [boxGraph, boxVertInclLE]
  have hedge :
      s(boxVertInclLE d h x, boxVertInclLE d h y) = innerEdgeLE d h s(x, y) := by
    rw [innerEdgeLE, Sym2.map_mk]
  have hopen :
      boxRestrict d N ω s(boxVertInclLE d h x, boxVertInclLE d h y) =
        boxRestrict d n ω s(x, y) := by
    rw [hedge]
    exact congrFun (boxRestrictLE_boxRestrict d h ω) s(x, y)
  constructor
  · intro hxy
    exact ⟨hadj.mp hxy.1, by simpa [hopen] using hxy.2⟩
  · intro hxy
    exact ⟨hadj.mpr hxy.1, by simpa [hopen] using hxy.2⟩



theorem boxBoundary_of_openSub_adj_outer_of_le
    (d : ℕ) {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N)
    (ω : ConfigSpace (Sym2 (Lattice.Site d)))
    {x : boxVerts d n} {z : boxVerts d N}
    (hz : (z : Lattice.Site d) ∉ Lattice.box d n)
    (hadj : (openSub (boxGraph d N) (boxRestrict d N ω)).Adj
      (boxVertInclLE d h x) z) :
    boxBoundary d n x := by
  rw [openSub_adj] at hadj
  have hnn : Lattice.NearestNeighbour d (x : Lattice.Site d) (z : Lattice.Site d) := by
    have hcp := hadj.1
    rw [boxGraph, SimpleGraph.comap_adj] at hcp
    exact hcp
  exact ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn hz⟩




theorem connToBdry_of_outer_reachable_not_inner_of_le
    (d : ℕ) {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N)
    (ω : ConfigSpace (Sym2 (Lattice.Site d))) (y : boxVerts d n)
    (houter : (openSub (boxGraph d N) (boxRestrict d N ω)).Reachable
      (boxVertInclLE d h (IsingFK.boxOrigin d n)) (boxVertInclLE d h y))
    (hnotInner : ¬ (openSub (boxGraph d n) (boxRestrict d n ω)).Reachable
      (IsingFK.boxOrigin d n) y) :
    IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω)
      (IsingFK.boxOrigin d n) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at houter
  set OS := openSub (boxGraph d N) (boxRestrict d N ω)
  set os := openSub (boxGraph d n) (boxRestrict d n ω)
  suffices H : ∀ w : boxVerts d N,
      Relation.ReflTransGen OS.Adj (boxVertInclLE d h (IsingFK.boxOrigin d n)) w →
      (IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω)
          (IsingFK.boxOrigin d n)
        ∨ ∃ x : boxVerts d n, boxVertInclLE d h x = w
            ∧ os.Reachable (IsingFK.boxOrigin d n) x) by
    rcases H (boxVertInclLE d h y) houter with hdone | ⟨x, hx, hreach⟩
    · exact hdone
    · have hxy : x = y := by
        apply Subtype.ext
        have := congrArg Subtype.val hx
        simpa [boxVertInclLE] using this
      exact False.elim (hnotInner (by simpa [hxy] using hreach))
  intro w hw
  induction hw with
  | refl =>
      exact Or.inr
        ⟨IsingFK.boxOrigin d n, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w hru hadj ih =>
      rcases ih with hdone | ⟨x, hx, hreach⟩
      · exact Or.inl hdone
      · subst hx
        by_cases hwinner : (w : Lattice.Site d) ∈ Lattice.box d n
        · let x' : boxVerts d n := ⟨(w : Lattice.Site d), hwinner⟩
          have hx' : boxVertInclLE d h x' = w := Subtype.ext rfl
          have hadj' : OS.Adj (boxVertInclLE d h x) (boxVertInclLE d h x') := by
            rwa [hx']
          exact Or.inr
            ⟨x', hx',
              hreach.trans
                ((openSub_boxRestrict_adj_boxVertInclLE d h ω x x').mp
                  (by simpa [OS, os] using hadj')).reachable⟩
        · exact Or.inl
            ⟨x, boxBoundary_of_openSub_adj_outer_of_le d hn h ω hwinner
              (by simpa [OS] using hadj), hreach⟩




theorem boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le
    (d : ℕ) {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N) (y : boxVerts d n) :
    boxConnectionDetourEvent d h (IsingFK.boxOrigin d n) y ⊆
      boxBdryConnEvent d n := by
  intro ω hω
  rcases hω with ⟨houter, hnotInner⟩
  rw [boxConnEvent, Set.mem_preimage, connEvent] at houter hnotInner
  rw [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq]
  exact connToBdry_of_outer_reachable_not_inner_of_le d hn h ω y houter hnotInner



theorem boxConnectionDetourEvent_subset_boxBdryConnEvent_xaxis
    {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N) :
    boxConnectionDetourEvent 3 h
        (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)
      ⊆ boxBdryConnEvent 3 n := by
  have horigin : ising3DOriginBoxVertex n = IsingFK.boxOrigin 3 n := by
    ext
    rfl
  simpa [horigin] using
    boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le
      3 hn h (ising3DXAxisBoxVertex n)



theorem freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_of_le
    (β : ℝ) (hβ : 0 < β) {N n : ℕ} (hn : n ≤ N) :
    freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n ≤
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
  unfold freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
  rw [dif_pos hn]
  exact measureReal_mono
    (boxConnEvent_subset_full_boxConnEvent_of_le 3 hn
      (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n))



theorem eventually_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    ∀ᶠ N in atTop,
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n ≤
        freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_of_le β hβ hN




noncomputable def freeFiniteVolumeXAxisDetourOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  if hn : n ≤ N then
    ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
      (boxConnectionDetourEvent 3 hn
        (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)))
  else
    0




noncomputable def freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxBdryConnEvent 3 n))



theorem freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le
    (β : ℝ) (hβ : 0 < β) {N n : ℕ} (hnpos : 1 ≤ n) (hn : n ≤ N) :
    freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤
      freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n := by
  unfold freeFiniteVolumeXAxisDetourOfBetaQ2InVolume
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume
  rw [dif_pos hn]
  exact measureReal_mono
    (boxConnectionDetourEvent_subset_boxBdryConnEvent_xaxis hnpos hn)



theorem eventually_freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary
    (β : ℝ) (hβ : 0 < β) (n : ℕ) (hnpos : 1 ≤ n) :
    ∀ᶠ N in atTop,
      freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤
        freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le
    β hβ hnpos hN



theorem freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le
    (β : ℝ) (hβ : 0 < β) {N n : ℕ} (hn : n ≤ N) :
    freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n ≤
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n +
        freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n := by
  unfold freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
    freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    freeFiniteVolumeXAxisDetourOfBetaQ2InVolume
  rw [dif_pos hn, dif_pos hn]
  have horigin :
      boxVertInclLE 3 hn (ising3DOriginBoxVertex n) =
        ising3DOriginBoxVertex N := by
    ext
    rfl
  have hxaxis :
      boxVertInclLE 3 hn (ising3DXAxisBoxVertex n) =
        ising3DXAxisBoxVertexInBox N n hn := by
    ext
    rfl
  simpa [horigin, hxaxis] using
    measureReal_full_boxConnEvent_le_inner_add_detour
    (d := 3)
    (μ := (freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ)
      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))))
    hn
    (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)




theorem eventually_freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    ∀ᶠ N in atTop,
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n ≤
        freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n +
          freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact
    freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le
      β hβ hN



theorem wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2
    (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N) :
    Tendsto (fun m =>
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))
      atTop
      (nhds ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))) := by
  simpa [boxConnEvent] using
    (fk_wired_infinite_measure (d := d) N hp hp1
      (S := connEvent (boxGraph d N) x y)
      (connEvent_isIncreasing (boxGraph d N) x y))



theorem freeInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y) ≤ B) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) ≤ B := by
  exact le_of_tendsto
    (freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
      d N hp hp1 x y) hB



theorem le_freeInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y)) :
    B ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
      d N hp hp1 x y) hB



theorem wiredInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y) ≤ B) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) ≤ B := by
  exact le_of_tendsto
    (wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2
      d N hp hp1 x y) hB



theorem le_wiredInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y)) :
    B ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2
      d N hp hp1 x y) hB



theorem freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤ B) :
    freeInfiniteVolumeXAxisConnectionQ2 p hp hp1 n ≤ B := by
  simpa [freeInfiniteVolumeXAxisConnectionQ2] using
    freeInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB



theorem le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (freeFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n))) :
    B ≤ freeInfiniteVolumeXAxisConnectionQ2 p hp hp1 n := by
  simpa [freeInfiniteVolumeXAxisConnectionQ2] using
    le_freeInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB



theorem wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        (wiredFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤ B) :
    wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1 n ≤ B := by
  simpa [wiredInfiniteVolumeXAxisConnectionQ2] using
    wiredInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB



theorem le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (wiredFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n))) :
    B ≤ wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1 n := by
  simpa [wiredInfiniteVolumeXAxisConnectionQ2] using
    le_wiredInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB




theorem
    fkTwoSidedFreeIVQ2_of_eventually_boxConnEvent_bounds
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {Alo Ahi : ℕ → ℝ}
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (boxConnEvent 3 n (ising3DOriginBoxVertex n)
                (ising3DXAxisBoxVertex n)))
    (hhi :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) Alo Ahi mass := by
  refine ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, ?_, ?_⟩
  · filter_upwards [hlo] with n hn
    exact le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n hn
  · filter_upwards [hhi] with n hn
    exact freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n hn




theorem
    fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {Alo Ahi : ℕ → ℝ}
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (boxConnEvent 3 n (ising3DOriginBoxVertex n)
                (ising3DXAxisBoxVertex n)))
    (hhi :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) Alo Ahi mass := by
  refine ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, ?_, ?_⟩
  · filter_upwards [hlo] with n hn
    exact le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n hn
  · filter_upwards [hhi] with n hn
    exact wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n hn




theorem fkExactFreeIVQ2_of_eventually_boxConnEvent_eq
    {p A mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  filter_upwards [h] with n hn
  exact le_antisymm
    (freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))




theorem fkExactWiredIVQ2_of_eventually_boxConnEvent_eq
    {p A mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  filter_upwards [h] with n hn
  exact le_antisymm
    (wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))





theorem fkSubexpFreeIVQ2_of_eventually_boxConnEvent_eq
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1) {A : ℕ → ℝ}
    (hA_pos : ∀ᶠ n in atTop, 0 < A n)
    (hA_log :
      Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
        atTop (nhds 0))
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  refine ⟨hA_pos, hA_log, ?_⟩
  filter_upwards [h] with n hn
  exact le_antisymm
    (freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))





theorem fkSubexpWiredIVQ2_of_eventually_boxConnEvent_eq
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1) {A : ℕ → ℝ}
    (hA_pos : ∀ᶠ n in atTop, 0 < A n)
    (hA_log :
      Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
        atTop (nhds 0))
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  refine ⟨hA_pos, hA_log, ?_⟩
  filter_upwards [h] with n hn
  exact le_antisymm
    (wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))



def FreeFiniteVolumeQ2ExactExponentialOfBeta
    (β : ℝ) (hβpos : 0 < β) (A mass : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ M in atTop,
    (freeFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (boxConnEvent 3 n (ising3DOriginBoxVertex n)
          (ising3DXAxisBoxVertex n)) =
      A * Real.exp (-(mass * (n : ℝ)))



def WiredFiniteVolumeQ2ExactExponentialOfBeta
    (β : ℝ) (hβpos : 0 < β) (A mass : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ M in atTop,
    (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (boxConnEvent 3 n (ising3DOriginBoxVertex n)
          (ising3DXAxisBoxVertex n)) =
      A * Real.exp (-(mass * (n : ℝ)))




def FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta
    (β : ℝ) (hβpos : 0 < β) (A : ℕ → ℝ) (mass : ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < A n) ∧
    Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
      atTop (nhds 0) ∧
    ∀ᶠ n in atTop, ∀ᶠ M in atTop,
      (freeFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxConnEvent 3 n (ising3DOriginBoxVertex n)
            (ising3DXAxisBoxVertex n)) =
        A n * Real.exp (-(mass * (n : ℝ)))




def WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta
    (β : ℝ) (hβpos : 0 < β) (A : ℕ → ℝ) (mass : ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < A n) ∧
    Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
      atTop (nhds 0) ∧
    ∀ᶠ n in atTop, ∀ᶠ M in atTop,
      (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxConnEvent 3 n (ising3DOriginBoxVertex n)
            (ising3DXAxisBoxVertex n)) =
        A n * Real.exp (-(mass * (n : ℝ)))



theorem fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta
    {β A mass : ℝ} (hβpos : 0 < β)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  simpa [freeInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkExactFreeIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) hexact



theorem fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta
    {β A mass : ℝ} (hβpos : 0 < β)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  simpa [wiredInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkExactWiredIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) hexact



theorem fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  rcases hsubexp with ⟨hA_pos, hA_log, hvalues⟩
  simpa [freeInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkSubexpFreeIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hA_pos hA_log hvalues



theorem fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
  rcases hsubexp with ⟨hA_pos, hA_log, hvalues⟩
  simpa [wiredInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkSubexpWiredIVQ2_of_eventually_boxConnEvent_eq
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hA_pos hA_log hvalues



def FreeFiniteVolumeQ2TwoSidedBoundsOfBeta
    (β : ℝ) (hβpos : 0 < β) (Alo Ahi : ℕ → ℝ) (mass : ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < Alo n) ∧
    (∀ᶠ n in atTop, 0 < Ahi n) ∧
    Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
      atTop (nhds 0) ∧
    Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
      atTop (nhds 0) ∧
    (∀ᶠ n in atTop, ∀ᶠ M in atTop,
      Alo n * Real.exp (-(mass * (n : ℝ))) ≤
        (freeFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n))) ∧
    ∀ᶠ n in atTop, ∀ᶠ M in atTop,
      (freeFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxConnEvent 3 n (ising3DOriginBoxVertex n)
            (ising3DXAxisBoxVertex n)) ≤
        Ahi n * Real.exp (-(mass * (n : ℝ)))



def WiredFiniteVolumeQ2TwoSidedBoundsOfBeta
    (β : ℝ) (hβpos : 0 < β) (Alo Ahi : ℕ → ℝ) (mass : ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < Alo n) ∧
    (∀ᶠ n in atTop, 0 < Ahi n) ∧
    Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
      atTop (nhds 0) ∧
    Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
      atTop (nhds 0) ∧
    (∀ᶠ n in atTop, ∀ᶠ M in atTop,
      Alo n * Real.exp (-(mass * (n : ℝ))) ≤
        (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n))) ∧
    ∀ᶠ n in atTop, ∀ᶠ M in atTop,
      (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxConnEvent 3 n (ising3DOriginBoxVertex n)
            (ising3DXAxisBoxVertex n)) ≤
        Ahi n * Real.exp (-(mass * (n : ℝ)))



theorem fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi mass := by
  rcases hbounds with
    ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, hlo, hhi⟩
  simpa [freeInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkTwoSidedFreeIVQ2_of_eventually_boxConnEvent_bounds
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hlo_pos hhi_pos hlo_log hhi_log hlo hhi



theorem fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi mass := by
  rcases hbounds with
    ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, hlo, hhi⟩
  simpa [wiredInfiniteVolumeXAxisConnectionOfBetaQ2] using
    fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hlo_pos hhi_pos hlo_log hhi_log hlo hhi





theorem free_wired_multiOpen_eq_of_not_badP_q2
    (d : ℕ) (hd : 1 ≤ d)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ FK.fwa_badP d)
    (T : Finset (Sym2 (Lattice.Site d))) :
    (FK.freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) =
    (FK.wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) := by
  exact FK.fwa_multiOpen_agree hd hp hp1 hbad T



theorem free_wired_multiOpen_eq_of_beta_not_badP_q2
    (d : ℕ) (hd : 1 ≤ d)
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP d)
    (T : Finset (Sym2 (Lattice.Site d))) :
    (FK.freeInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) =
    (FK.wiredInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.fmu_multiOpen T) :=
  free_wired_multiOpen_eq_of_not_badP_q2 d hd
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) hbad T





theorem free_wired_boxConnEvent_eq_of_not_badP_q2
    (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ FK.fwa_badP d)
    (x y : boxVerts d N) :
    (FK.freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) =
      (FK.wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) := by
  simpa [FK.boxConnEvent] using
    (FK.fwa_box_agree (d := d) hd hp hp1 hbad hN
      (FK.connEvent_isIncreasing (FK.boxGraph d N) x y))



theorem free_wired_boxConnEvent_eq_of_beta_not_badP_q2
    (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP d)
    (x y : boxVerts d N) :
    (FK.freeInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) =
      (FK.wiredInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxConnEvent d N x y) :=
  free_wired_boxConnEvent_eq_of_not_badP_q2 d N hd hN
    (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) hbad x y




theorem freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    {n : ℕ} (hn : 1 ≤ n) :
    freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
      wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n :=
  free_wired_boxConnEvent_eq_of_beta_not_badP_q2 3 n (by norm_num) hn
    hβ hbad (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)



theorem wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    {n : ℕ} (hn : 1 ≤ n) :
    wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n :=
  (freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    hβ hbad hn).symm




theorem eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    ∀ᶠ n in atTop,
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
        wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact
    freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad hn



theorem
    eventually_wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    ∀ᶠ n in atTop,
      wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n =
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n :=
  (eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
    hβ hbad).mono fun _ hn => hn.symm



theorem freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβ) :
    FreeXAxisWiredQ2ConnectionAgrees β hβ := by
  unfold FreeXAxisQ2ConnectionAgrees FreeXAxisWiredQ2ConnectionAgrees at *
  filter_upwards
    [hfree, eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad] with n hconn heq
  exact hconn.trans heq



theorem freeXAxisQ2ConnectionAgrees_of_wired_not_badP
    {β : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hwired : FreeXAxisWiredQ2ConnectionAgrees β hβ) :
    FreeXAxisQ2ConnectionAgrees β hβ := by
  unfold FreeXAxisQ2ConnectionAgrees FreeXAxisWiredQ2ConnectionAgrees at *
  filter_upwards
    [hwired, eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad] with n hconn heq
  exact hconn.trans heq.symm




theorem plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos) :
    PlusXAxisWiredQ2ConnectionAgrees β hβpos := by
  unfold FreeXAxisQ2ConnectionAgrees PlusXAxisWiredQ2ConnectionAgrees at *
  filter_upwards
    [hfree, eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβpos hbad] with n hconn heq
  have htwo :
      twoPointOnXAxis β n = freeTwoPointOnXAxis β n := by
    simpa [twoPointOnXAxis, twoPointAtDisplacement, freeTwoPointOnXAxis,
      freeTwoPointAtDisplacement] using
        hagree β hβc ising3DOrigin (ising3DXAxisRay n)
  calc
    |twoPointOnXAxis β n| = |freeTwoPointOnXAxis β n| := by rw [htwo]
    _ = freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n := hconn
    _ = wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n := heq



theorem
    fkXAxisConnectionExactExponentialDecay_freeInfiniteVolumeQ2_iff_wired
    {β A m : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  FKXAxisConnectionExactExponentialDecay.congr_eventually_iff
    ((eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad).mono fun _ hn => hn.symm)



theorem
    fkXAxisConnectionExactExponentialDecay_wiredInfiniteVolumeQ2_iff_free
    {β A m : ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  (fkXAxisConnectionExactExponentialDecay_freeInfiniteVolumeQ2_iff_wired
    hβ hbad).symm



theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_freeInfiniteVolumeQ2_iff_wired
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually_iff
    ((eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad).mono fun _ hn => hn.symm)



theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_wiredInfiniteVolumeQ2_iff_free
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m :=
  (fkXAxisConnectionSubexponentialPrefactorDecay_freeInfiniteVolumeQ2_iff_wired
    hβ hbad).symm



theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_freeInfiniteVolumeQ2_iff_wired
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m :=
  FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually_iff
    ((eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2
      hβ hbad).mono fun _ hn => hn.symm)



theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_wiredInfiniteVolumeQ2_iff_free
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m :=
  (fkXAxisConnectionTwoSidedSubexponentialBounds_freeInfiniteVolumeQ2_iff_wired
    hβ hbad).symm




theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_exactExponential hA
    (freeXAxisExactExponentialDecay_of_fkConnectionComparison hfree hconn)




theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
      hβpos hA hfree hconn)




theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    (freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      hfree hconn)




theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
      hβpos hfree hconn)




theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      hfree hconn)




theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
      hβpos hfree hconn)




theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_exactExponential hA
    (freeXAxisExactExponentialDecay_of_fkConnectionComparison
      (freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
        hβpos hbad hfree)
      hconn)




theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_exactExponential hA
    (plusXAxisExactExponentialDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)




theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    (freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      (freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
        hβpos hbad hfree)
      hconn)





theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    (plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)




theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      (freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP
        hβpos hbad hfree)
      hconn)





theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)




theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A) (hm : 0 < m)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hA hfree hconn).hasCorrelationLength_inv hm




theorem
    plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hfree hconn).hasCorrelationLength_inv hm




theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hfree hconn).hasCorrelationLength_inv hm




theorem
    plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hfree hconn).hasCorrelationLength_inv hm




theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hfree hconn).hasCorrelationLength_inv hm




theorem
    plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hβc hagree hfree hconn).hasCorrelationLength_inv hm




theorem
    free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β) (hA : 0 < A) (hm : 0 < m)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    hβpos hA hbad hfree hconn).hasCorrelationLength_inv hm




theorem
    free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hbad hfree hconn).hasCorrelationLength_inv hm




theorem
    free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β) (hm : 0 < m)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    hβpos hbad hfree hconn).hasCorrelationLength_inv hm




theorem plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    {β A m : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionExactExponentialDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_exactExponential hA hm
    (plusXAxisExactExponentialDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)




theorem plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionSubexponentialPrefactorDecay
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_subexponentialPrefactor hm
    (plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)




theorem
    plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSidedSubexponentialBounds
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hm : 0 < m)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hm
    (plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
      (plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree
        hβpos hβc hagree hbad hfree)
      hconn)




theorem
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hA hfree
    (fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta hβpos hexact)



theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hfree
    (fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta hβpos hexact)



theorem
    free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hmass : 0 < mass)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    hβpos hA hfree hexact).hasCorrelationLength_inv hmass




theorem
    plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hfree hexact).hasCorrelationLength_inv hmass




theorem
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hfree
    (fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta hβpos hsubexp)



theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hfree
    (fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta hβpos hsubexp)



theorem
    free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    hβpos hfree hsubexp).hasCorrelationLength_inv hmass




theorem
    plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hfree hsubexp).hasCorrelationLength_inv hmass



theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    hβpos hA hbad hfree
    (fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta hβpos hexact)



theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hbad hfree
    (fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta hβpos hexact)




theorem
    free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β) (hA : 0 < A)
    (hmass : 0 < mass)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    hβpos hA hbad hfree hexact).hasCorrelationLength_inv hmass




theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    {β A mass : ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hA : 0 < A) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
    hβpos hβc hA hagree hbad hfree hexact).hasCorrelationLength_inv hmass



theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hbad hfree
    (fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta hβpos hsubexp)



theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hbad hfree
    (fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta hβpos hsubexp)




theorem
    free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    hβpos hbad hfree hsubexp).hasCorrelationLength_inv hmass




theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    {β mass : ℝ} {A : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hsubexp :
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
    hβpos hβc hagree hbad hfree hsubexp).hasCorrelationLength_inv hmass



theorem
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hfree
    (fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta hβpos hbounds)



theorem
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided
    hβpos hβc hagree hfree
    (fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta hβpos hbounds)



theorem
    free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    hβpos hfree hbounds).hasCorrelationLength_inv hmass



theorem
    plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
    hβpos hβc hagree hfree hbounds).hasCorrelationLength_inv hmass



theorem
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    hβpos hbad hfree
    (fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta hβpos hbounds)



theorem
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass :=
  plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided
    hβpos hβc hagree hbad hfree
    (fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta hβpos hbounds)



theorem
    free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hmass : 0 < mass)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    hβpos hbad hfree hbounds).hasCorrelationLength_inv hmass



theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ} (hβpos : 0 < β)
    (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hbounds :
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  (plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
    hβpos hβc hagree hbad hfree hbounds).hasCorrelationLength_inv hmass




theorem
    plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSidedSubexpBounds
    {β mass : ℝ} {Alo Ahi : ℕ → ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) (hmass : 0 < mass)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
    (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
            (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (boxConnEvent 3 n (ising3DOriginBoxVertex n)
                (ising3DXAxisBoxVertex n)))
    (hhi :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSidedSubexponentialBounds
    hβpos hβc hmass hagree hbad hfree
    (fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      hlo_pos hhi_pos hlo_log hhi_log hlo hhi)

end Exact3D
end StatMech
