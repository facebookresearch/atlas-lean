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
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.LeftFace
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.BoundaryConnected
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}












noncomputable def exitDart (hfin : (cluster 2 ω (origin 2)).Finite) : Dart where
  tail := axisSite (exitIndex (ω := ω) hfin)
  head := axisSite (exitIndex (ω := ω) hfin + 1)
  adj := axisSite_exit_adj (ω := ω) hfin

@[simp] theorem exitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).tail = axisSite (exitIndex (ω := ω) hfin) := rfl

@[simp] theorem exitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).head = axisSite (exitIndex (ω := ω) hfin + 1) := rfl




theorem exitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin) :=
  ⟨axisSite_exit_mem (ω := ω) hfin, axisSite_exit_succ_not_mem (ω := ω) hfin⟩



theorem exitDart_dir (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).dir = ![1, 0] := by
  rw [Dart.dir_def, exitDart_head, exitDart_tail]
  funext i; fin_cases i <;> simp [axisSite]



noncomputable def leftExitDart (hfin : (cluster 2 ω (origin 2)).Finite) : Dart where
  tail := leftAxisSite (leftExitIndex (ω := ω) hfin)
  head := leftAxisSite (leftExitIndex (ω := ω) hfin + 1)
  adj := leftAxisSite_exit_adj (ω := ω) hfin

@[simp] theorem leftExitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftExitDart (ω := ω) hfin).tail = leftAxisSite (leftExitIndex (ω := ω) hfin) := rfl

@[simp] theorem leftExitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftExitDart (ω := ω) hfin).head = leftAxisSite (leftExitIndex (ω := ω) hfin + 1) := rfl



theorem leftExitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (leftExitDart (ω := ω) hfin) :=
  ⟨leftAxisSite_exit_mem (ω := ω) hfin, leftAxisSite_exit_succ_not_mem (ω := ω) hfin⟩


theorem leftExitDart_dir (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftExitDart (ω := ω) hfin).dir = ![-1, 0] := by
  rw [Dart.dir_def, leftExitDart_head, leftExitDart_tail, leftAxisSite_succ_eq, leftAxisSite_eq]
  funext i; fin_cases i
  · simp; ring
  · simp












theorem dartDir_cases (e : Dart) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
  have h := unitWt_dir e
  unfold unitWt at h
  rw [Fin.sum_univ_two] at h
  set a := e.dir 0 with ha
  set b := e.dir 1 with hb
  have hd : e.dir = ![a, b] := by funext i; fin_cases i <;> rfl
  have hh : a.natAbs + b.natAbs = 1 := h
  have hcase : (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
    omega
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hd, h1, h2]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))


noncomputable def negPart (z : ℤ) : ℤ := if z < 0 then z else 0



noncomputable def dartFace (e : Dart) : Site 2 :=
  ![ e.tail 0 + negPart (e.dir 0) + negPart (rot90Fun e.dir 0),
     e.tail 1 + negPart (e.dir 1) + negPart (rot90Fun e.dir 1) ]



theorem dartFace_of_dir_right (e : Dart) (hd : e.dir = ![1, 0]) :
    dartFace e = ![e.tail 0, e.tail 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> simp [rot90Fun, negPart]



theorem dartFace_of_dir_left (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> (simp [rot90Fun, negPart]; ring)



theorem dartFace_of_dir_up (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> simp [rot90Fun, negPart] <;> try ring



theorem dartFace_of_dir_down (e : Dart) (hd : e.dir = ![0, -1]) :
    dartFace e = ![e.tail 0, e.tail 1 - 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> simp [rot90Fun, negPart] <;> try ring






theorem dartFace_exitDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    dartFace (exitDart (ω := ω) hfin) = exitFaceUp (ω := ω) hfin := by
  rw [dartFace_of_dir_right _ (exitDart_dir (ω := ω) hfin)]
  show (![axisSite (exitIndex (ω := ω) hfin) 0, axisSite (exitIndex (ω := ω) hfin) 1] : Site 2)
      = exitFaceUp (ω := ω) hfin
  unfold exitFaceUp
  funext i; fin_cases i <;> simp [axisSite]





theorem dartFace_leftExitDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    dartFace (leftExitDart (ω := ω) hfin) = leftExitFaceDown (ω := ω) hfin := by
  rw [dartFace_of_dir_left _ (leftExitDart_dir (ω := ω) hfin)]
  show (![leftAxisSite (leftExitIndex (ω := ω) hfin) 0 - 1,
        leftAxisSite (leftExitIndex (ω := ω) hfin) 1 - 1] : Site 2)
      = leftExitFaceDown (ω := ω) hfin
  unfold leftExitFaceDown
  funext i; fin_cases i <;> simp [leftAxisSite]



theorem dartFace_leftExitDart_coord0_nonpos (hfin : (cluster 2 ω (origin 2)).Finite) :
    dartFace (leftExitDart (ω := ω) hfin) 0 ≤ 0 := by
  rw [dartFace_leftExitDart (ω := ω) hfin]
  exact leftExitFaceDown_coord0_nonpos (ω := ω) hfin














theorem faceBoundaryGraph_adj_vert (K : Set (Site 2)) (a b : ℤ)
    (h : ((![a, b] : Site 2) ∈ K) ↔ ((![a + 1, b] : Site 2) ∉ K)) :
    (faceBoundaryGraph K).Adj ![a, b] ![a, b - 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_bottom a b, ?_⟩
  rw [sharedPrimalEdge_bottom a b, bdEdge_mk]
  unfold faceCorner00 faceCorner10
  exact h



theorem faceBoundaryGraph_adj_horiz (K : Set (Site 2)) (a b : ℤ)
    (h : ((![a, b] : Site 2) ∈ K) ↔ ((![a, b + 1] : Site 2) ∉ K)) :
    (faceBoundaryGraph K).Adj ![a, b] ![a - 1, b] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_left a b, ?_⟩
  rw [sharedPrimalEdge_left a b, bdEdge_mk]
  unfold faceCorner00 faceCorner01
  exact h


theorem dart_head_eq (e : Dart) : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel



theorem dartFace_next_of_dir_right (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![1, 0]) :
    dartFace (dartNext K e) = ![e.tail 0, e.tail 1 - 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![0, -1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![0, 1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0 + 1, e.tail 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_up _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_right _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_down _ (by rw [mkDart_dir, ht]),
        mkDart_tail]



theorem dartFace_next_of_dir_left (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace (dartNext K e) = ![e.tail 0 - 1, e.tail 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![0, 1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![0, -1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0 - 1, e.tail 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_down _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_left _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_up _ (by rw [mkDart_dir, ht]),
        mkDart_tail]



theorem dartFace_next_of_dir_up (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace (dartNext K e) = ![e.tail 0, e.tail 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![-1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0, e.tail 1 + 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_left _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_up _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_right _ (by rw [mkDart_dir, ht]),
        mkDart_tail]



theorem dartFace_next_of_dir_down (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![0, -1]) :
    dartFace (dartNext K e) = ![e.tail 0 - 1, e.tail 1 - 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![-1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0, e.tail 1 - 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_right _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_down _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_left _ (by rw [mkDart_dir, ht]),
        mkDart_tail]






theorem dartFace_step_adj (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (faceBoundaryGraph K).Adj (dartFace e) (dartFace (dartNext K e)) := by
  obtain ⟨htail, hhead⟩ := he
  rcases dartDir_cases e with hd | hd | hd | hd
  · 
    rw [dartFace_of_dir_right e hd, dartFace_next_of_dir_right K e hd]
    have hh : e.head = ![e.tail 0 + 1, e.tail 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
    refine faceBoundaryGraph_adj_vert K (e.tail 0) (e.tail 1) ?_
    constructor
    · intro _; rw [hh] at hhead; exact hhead
    · intro _; show (![e.tail 0, e.tail 1] : Site 2) ∈ K
      have : (![e.tail 0, e.tail 1] : Site 2) = e.tail := by funext i; fin_cases i <;> rfl
      rw [this]; exact htail
  · 
    rw [dartFace_of_dir_left e hd, dartFace_next_of_dir_left K e hd]
    have hh : e.head = ![e.tail 0 - 1, e.tail 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
    
    have key : (faceBoundaryGraph K).Adj ![e.tail 0 - 1, e.tail 1]
        ![e.tail 0 - 1, e.tail 1 - 1] := by
      refine faceBoundaryGraph_adj_vert K (e.tail 0 - 1) (e.tail 1) ?_
      constructor
      · intro hin; exact absurd (by
          have : (![e.tail 0 - 1, e.tail 1] : Site 2) = e.head := hh.symm
          rw [this] at hin; exact hin) hhead
      · intro hout
        exact absurd (by
          have : (![e.tail 0 - 1 + 1, e.tail 1] : Site 2) = e.tail := by
            funext i; fin_cases i <;> simp <;> ring
          rw [this]; exact htail) hout
    exact key.symm
  · 
    rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd]
    have hh : e.head = ![e.tail 0, e.tail 1 + 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
    have key : (faceBoundaryGraph K).Adj ![e.tail 0, e.tail 1] ![e.tail 0 - 1, e.tail 1] := by
      refine faceBoundaryGraph_adj_horiz K (e.tail 0) (e.tail 1) ?_
      constructor
      · intro _; rw [hh] at hhead; exact hhead
      · intro _; show (![e.tail 0, e.tail 1] : Site 2) ∈ K
        have : (![e.tail 0, e.tail 1] : Site 2) = e.tail := by funext i; fin_cases i <;> rfl
        rw [this]; exact htail
    exact key.symm
  · 
    rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd]
    have hh : e.head = ![e.tail 0, e.tail 1 - 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
    refine faceBoundaryGraph_adj_horiz K (e.tail 0) (e.tail 1 - 1) ?_
    constructor
    · intro hin
      exact absurd (by
        have : (![e.tail 0, e.tail 1 - 1] : Site 2) = e.head := by rw [hh]
        rw [this] at hin; exact hin) hhead
    · intro hout
      exact absurd (by
        have : (![e.tail 0, e.tail 1 - 1 + 1] : Site 2) = e.tail := by
          funext i; fin_cases i <;> simp <;> ring
        rw [this]; exact htail) hout










theorem iterate_isBoundaryDart (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    IsBoundaryDart K ((dartNext K)^[n] e) := by
  induction n with
  | zero => simpa using he
  | succ m ih => rw [Function.iterate_succ_apply']; exact dartNext_isBoundaryDart K _ ih



theorem dartFace_iterate_reachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) :
    (faceBoundaryGraph K).Reachable (dartFace e) (dartFace ((dartNext K)^[n] e)) := by
  induction n with
  | zero => simpa using SimpleGraph.Reachable.refl (dartFace e)
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine ih.trans ?_
    exact (dartFace_step_adj K _ (iterate_isBoundaryDart K e he m)).reachable




theorem dartFace_reachable_of_orbit (K : Set (Site 2)) (e f : Dart) (he : IsBoundaryDart K e)
    {n : ℕ} (hf : (dartNext K)^[n] e = f) :
    (faceBoundaryGraph K).Reachable (dartFace e) (dartFace f) := by
  rw [← hf]; exact dartFace_iterate_reachable K e he n

















def ExitDartsSameOrbit (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∃ n : ℕ, (dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin)
    = leftExitDart (ω := ω) hfin







theorem exitFaces_reachable_of_sameOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
      (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
  obtain ⟨n, hn⟩ := h
  have hr := dartFace_reachable_of_orbit (cluster 2 ω (origin 2))
    (exitDart (ω := ω) hfin) (leftExitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin) hn
  rwa [dartFace_exitDart (ω := ω) hfin, dartFace_leftExitDart (ω := ω) hfin] at hr



















theorem pc_lt_one_via_dartOrbit
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  pc_lt_one_via_boundary h



































end Lattice

end StatMech
