/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.PlanarTopology
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.LeftFace
import Code.Lattice.ContourLinksExits
import Code.Lattice.OrbitEncloses
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph Function List

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}















theorem polygon_edges_nodup {V : Type*} (g : ℕ → V) (p : ℕ) (hp : 3 ≤ p)
    (hper : ∀ k, g k = g (k % p)) (hinj : Set.InjOn g (Set.Iio p)) :
    ((List.range p).map (fun k => s(g k, g (k + 1)))).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj h
    rw [List.mem_range] at hi hj
    have hi1 : g (i + 1) = g ((i + 1) % p) := hper (i + 1)
    have hj1 : g (j + 1) = g ((j + 1) % p) := hper (j + 1)
    have hmodi : (i + 1) % p < p := Nat.mod_lt _ (by omega)
    have hmodj : (j + 1) % p < p := Nat.mod_lt _ (by omega)
    have vi : (i + 1) % p = if i + 1 = p then 0 else i + 1 := by
      by_cases hc : i + 1 = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    have vj : (j + 1) % p = if j + 1 = p then 0 else j + 1 := by
      by_cases hc : j + 1 = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    rw [hi1, hj1, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hinj (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) h1
    · have e1 : i = (j + 1) % p := hinj (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hmodj) h1
      have e2 : (i + 1) % p = j := hinj (Set.mem_Iio.mpr hmodi) (Set.mem_Iio.mpr hj) h2
      rw [vi] at e2; rw [vj] at e1
      split_ifs at e1 e2 <;> omega
  · exact List.nodup_range




theorem polygon_support_tail_nodup {V : Type*} (g : ℕ → V) (p : ℕ) (hp : 1 ≤ p)
    (hper : ∀ k, g k = g (k % p)) (hinj : Set.InjOn g (Set.Iio p)) :
    (((List.range (p + 1)).map g).tail).Nodup := by
  rw [← List.map_tail]
  have htail : (List.range (p + 1)).tail = List.range' 1 p := by
    rw [List.range_succ_eq_map, List.tail_cons, List.range'_eq_map_range]
    congr 1; funext a; omega
  rw [htail]
  apply List.Nodup.map_on
  · intro a ha b hb h
    rw [List.mem_range'] at ha hb
    have hpa : a % p < p := Nat.mod_lt _ (by omega)
    have hpb : b % p < p := Nat.mod_lt _ (by omega)
    rw [hper a, hper b] at h
    have key : a % p = b % p := hinj (Set.mem_Iio.mpr hpa) (Set.mem_Iio.mpr hpb) h
    have va : a % p = if a = p then 0 else a := by
      by_cases hc : a = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    have vb : b % p = if b = p then 0 else b := by
      by_cases hc : b = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    rw [va, vb] at key
    split_ifs at key <;> omega
  · exact List.nodup_range'










theorem orbitFaceWalk_edges (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    (dartOrbitFaceWalk K e he n).edges
      = (List.range n).map
        (fun k => s(dartFace ((dartNext K)^[k] e), dartFace ((dartNext K)^[k + 1] e))) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [dartOrbitFaceWalk, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_concat, ih,
      List.range_succ, List.map_append]
    simp only [List.concat_eq_append, List.map_cons, List.map_nil]
    rw [Function.iterate_succ_apply']





















theorem orbitFaceWalk_isCycle (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) (p : ℕ)
    (hp : 3 ≤ p) (hcl : (dartNext K)^[p] e = e)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio p)) :
    ((dartOrbitFaceWalk K e he p).copy rfl (by rw [hcl])).IsCycle := by
  set g : ℕ → Site 2 := fun k => dartFace ((dartNext K)^[k] e) with hg
  have hper : ∀ k, g k = g (k % p) := by
    intro k
    show dartFace ((dartNext K)^[k] e) = dartFace ((dartNext K)^[k % p] e)
    rw [iterate_eq_mod_of_period (dartNext K) e hcl k]
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · 
    rw [Walk.isTrail_def, Walk.edges_copy, orbitFaceWalk_edges]
    have hrw : (fun k => s(dartFace ((dartNext K)^[k] e), dartFace ((dartNext K)^[k + 1] e)))
        = (fun k => s(g k, g (k + 1))) := rfl
    rw [hrw]
    exact polygon_edges_nodup g p hp hper hinj
  · 
    intro hnil
    have hlen : ((dartOrbitFaceWalk K e he p).copy rfl (by rw [hcl])).length = 0 := by
      rw [hnil]; rfl
    rw [Walk.length_copy, dartOrbitFaceWalk_length] at hlen
    omega
  · 
    rw [Walk.support_copy, dartOrbitFaceWalk_support]
    have hrw : (fun k => dartFace ((dartNext K)^[k] e)) = g := rfl
    rw [hrw]
    exact polygon_support_tail_nodup g p (by omega) hper hinj











noncomputable def exitBaseSub (hfin : (cluster 2 ω (origin 2)).Finite) :
    {d : Dart // IsBoundaryDart (cluster 2 ω (origin 2)) d} :=
  ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩




theorem exit_period_closure (hfin : (cluster 2 ω (origin 2)).Finite) :
    (dartNext (cluster 2 ω (origin 2)))^[dartOrbitPeriod (cluster 2 ω (origin 2))
      (exitBaseSub (ω := ω) hfin)] (exitDart (ω := ω) hfin) = exitDart (ω := ω) hfin :=
  orbit_iterate_period_eq (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)




noncomputable def exitMinFaceLoop (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin) :=
  ((dartOrbitFaceWalk (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin)
    (dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))).copy
      rfl (by rw [exit_period_closure (ω := ω) hfin])).copy
      (dartFace_exitDart (ω := ω) hfin) (dartFace_exitDart (ω := ω) hfin)



theorem exitMinFaceLoop_support (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitMinFaceLoop (ω := ω) hfin).support
      = (List.range (dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) + 1)).map
        (fun k => dartFace ((dartNext (cluster 2 ω (origin 2)))^[k] (exitDart (ω := ω) hfin))) := by
  rw [exitMinFaceLoop, Walk.support_copy, Walk.support_copy, dartOrbitFaceWalk_support]







theorem exitMinFaceLoop_mem_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    leftExitFaceDown (ω := ω) hfin ∈ (exitMinFaceLoop (ω := ω) hfin).support := by
  obtain ⟨n, hn⟩ := h
  have hcl := exit_period_closure (ω := ω) hfin
  have hppos : 0 < dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) :=
    dartOrbitPeriod_pos (cluster 2 ω (origin 2)) hfin (exitBaseSub (ω := ω) hfin)
  have hface : dartFace ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin))
      = leftExitFaceDown (ω := ω) hfin := by rw [hn]; exact dartFace_leftExitDart (ω := ω) hfin
  have hmod := iterate_eq_mod_of_period (dartNext (cluster 2 ω (origin 2)))
    (exitDart (ω := ω) hfin) hcl n
  rw [exitMinFaceLoop_support, List.mem_map]
  refine ⟨n % dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin),
    List.mem_range.mpr (by have := Nat.mod_lt n hppos; omega), ?_⟩
  rw [← hmod, hface]




















def OrbitFaceSimple (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
    Set.InjOn (fun k => dartFace ((dartNext (cluster 2 ω (origin 2)))^[k] (exitDart (ω := ω) hfin)))
      (Set.Iio (dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)))





theorem exitMinFaceLoop_isCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : OrbitFaceSimple ω hfin) : (exitMinFaceLoop (ω := ω) hfin).IsCycle := by
  obtain ⟨hp, hinj⟩ := h
  rw [exitMinFaceLoop, Walk.isCycle_copy]
  exact orbitFaceWalk_isCycle (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin)
    (dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) hp
    (exit_period_closure (ω := ω) hfin) hinj














theorem cycleHasLeftFace_of_orbitFaceSimple (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsimple : OrbitFaceSimple ω hfin) (hsame : ExitDartsSameOrbit ω hfin) :
    CycleHasLeftFace ω hfin :=
  ⟨exitMinFaceLoop (ω := ω) hfin, exitMinFaceLoop_isCycle (ω := ω) hfin hsimple,
    leftExitFaceDown (ω := ω) hfin, exitMinFaceLoop_mem_leftFace (ω := ω) hfin hsame,
    leftExitFaceDown_coord0_nonpos (ω := ω) hfin⟩






theorem pcAnchoredEnclosure_of_orbitFaceSimple
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ ExitDartsSameOrbit ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure :=
  pcAnchoredEnclosure_of_cycleHasLeftFace
    (fun ω hfin => cycleHasLeftFace_of_orbitFaceSimple (ω := ω) hfin (h ω hfin).1 (h ω hfin).2)












theorem pc_lt_one_of_orbitFaceSimple
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ ExitDartsSameOrbit ω hfin) :
    (StatMech.Percolation.pc 2 : ℝ) < 1 := by
  have := StatMech.Percolation.pc_lt_one_of_enclosure (pcAnchoredEnclosure_of_orbitFaceSimple h)
  exact_mod_cast this































end Lattice

end StatMech
