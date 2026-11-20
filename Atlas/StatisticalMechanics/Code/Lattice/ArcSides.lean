/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Lattice.Clusters
import Code.Lattice.CrossingParity
import Code.RSW.Defs
import Code.Universality.HVIntersection
import Code.Universality.VSeparatesFixed

open Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.RSW.Box
open StatMech.Universality







noncomputable def boxMinusP (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : SimpleGraph (Site 2) where
  Adj u v := (hypercubicLattice 2).Adj u v ∧ u ∈ rect α β c d ∧ v ∈ rect α β c d ∧
             u ∉ overlapComp ω m m' c d xB hxB ∧ v ∉ overlapComp ω m m' c d xB hxB
  symm := by intro u v ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1.symm, h3, h2, h5, h4⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem boxMinusP_adj (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) (u v : Site 2) :
    (boxMinusP ω α β m m' c d xB hxB).Adj u v ↔
      (hypercubicLattice 2).Adj u v ∧ u ∈ rect α β c d ∧ v ∈ rect α β c d ∧
       u ∉ overlapComp ω m m' c d xB hxB ∧ v ∉ overlapComp ω m m' c d xB hxB := Iff.rfl


theorem boxMinusP_le (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) :
    boxMinusP ω α β m m' c d xB hxB ≤ hypercubicLattice 2 := fun _ _ h => h.1




theorem boxMinusP_walk_dest (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {x z : Site 2}
    (hx : x ∈ rect α β c d) (hxP : x ∉ overlapComp ω m m' c d xB hxB)
    (w : (boxMinusP ω α β m m' c d xB hxB).Walk x z) :
    z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB := by
  induction w with
  | nil => exact ⟨hx, hxP⟩
  | @cons a b e hab p ih => exact ih hab.2.2.1 hab.2.2.2.2




def floodFromLeft (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Set (Site 2) :=
  {z | ∃ x : Site 2, x ∈ rect α β c d ∧ x 0 = α ∧ x ∉ overlapComp ω m m' c d xB hxB ∧
        (boxMinusP ω α β m m' c d xB hxB).Reachable x z}





def arcS_leftRegion (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Set (Site 2) :=
  {z | z ∈ rect α β c d ∧ (z 0 = α ∨ z ∈ floodFromLeft ω α β m m' c d xB hxB)}

@[simp] theorem mem_arcS_leftRegion (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) (z : Site 2) :
    z ∈ arcS_leftRegion ω α β m m' c d xB hxB ↔
      z ∈ rect α β c d ∧ (z 0 = α ∨ z ∈ floodFromLeft ω α β m m' c d xB hxB) := Iff.rfl


theorem floodFromLeft_subset (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {z : Site 2}
    (hz : z ∈ floodFromLeft ω α β m m' c d xB hxB) :
    z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB := by
  obtain ⟨x, hxbox, _, hxP, w⟩ := hz
  obtain ⟨ww⟩ := w
  exact boxMinusP_walk_dest ω α β m m' c d xB hxB hxbox hxP ww


theorem arcS_leftRegion_subset_box (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {z : Site 2}
    (hz : z ∈ arcS_leftRegion ω α β m m' c d xB hxB) : z ∈ rect α β c d := hz.1





theorem arcS_leftRegion_left (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (z : Site 2) (hz : z ∈ rect α β c d) (hzα : z 0 = α) :
    z ∈ arcS_leftRegion ω α β m m' c d xB hxB :=
  ⟨hz, Or.inl hzα⟩






theorem flood_step (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {w t : Site 2}
    (hwL : w ∈ arcS_leftRegion ω α β m m' c d xB hxB)
    (hwP : w ∉ overlapComp ω m m' c d xB hxB)
    (hadj : (hypercubicLattice 2).Adj w t) (ht : t ∈ rect α β c d)
    (htP : t ∉ overlapComp ω m m' c d xB hxB) :
    t ∈ floodFromLeft ω α β m m' c d xB hxB := by
  obtain ⟨hwbox, hwcase⟩ := hwL
  have hstep : (boxMinusP ω α β m m' c d xB hxB).Adj w t := ⟨hadj, hwbox, ht, hwP, htP⟩
  rcases hwcase with hwα | hwflood
  · exact ⟨w, hwbox, hwα, hwP, Adj.reachable hstep⟩
  · obtain ⟨x, hxbox, hxα, hxP, hreach⟩ := hwflood
    exact ⟨x, hxbox, hxα, hxP, hreach.trans (Adj.reachable hstep)⟩








theorem arcS_leftRegion_bdEdge (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) (u v : Site 2)
    (hu : u ∈ rect α β c d) (hv : v ∈ rect α β c d)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (arcS_leftRegion ω α β m m' c d xB hxB) s(u, v)) :
    u ∈ overlapComp ω m m' c d xB hxB ∨ v ∈ overlapComp ω m m' c d xB hxB := by
  classical
  rw [bdEdge_mk] at hbd
  by_contra hcon
  push Not at hcon
  obtain ⟨huP, hvP⟩ := hcon
  by_cases hvL : v ∈ arcS_leftRegion ω α β m m' c d xB hxB
  · 
    have huL : u ∉ arcS_leftRegion ω α β m m' c d xB hxB := fun h => (hbd.mp h) hvL
    exact huL ⟨hu, Or.inr (flood_step ω α β m m' c d xB hxB hvL hvP hadj.symm hu huP)⟩
  · 
    have huL : u ∈ arcS_leftRegion ω α β m m' c d xB hxB := hbd.mpr hvL
    exact hvL ⟨hv, Or.inr (flood_step ω α β m m' c d xB hxB huL huP hadj hv hvP)⟩

















def ArcS_TwoPathsCross (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (x y : Site 2), x ∈ rect α β c d → y ∈ rect α β c d → x 0 = α → y 0 = β →
  ∀ (γ : (hypercubicLattice 2).Walk x y),
    (∀ z ∈ γ.support, z ∈ rect α β c d) →
    ∃ z ∈ γ.support, z ∈ overlapComp ω m m' c d xB hxB





theorem arcS_rightWall_in_L_gives_avoiding_walk (ω : ConfigSpace (Sym2 (Site 2)))
    {α β m m' c d : ℤ} (hαβ : α < β) (xB : Site 2) (hxB : xB ∈ rect m m' c d) {y : Site 2}
    (_hy : y ∈ rect α β c d) (hyβ : y 0 = β)
    (hyL : y ∈ arcS_leftRegion ω α β m m' c d xB hxB) :
    ∃ (x : Site 2) (γ : (hypercubicLattice 2).Walk x y),
      x ∈ rect α β c d ∧ x 0 = α ∧
      (∀ z ∈ γ.support, z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB) := by
  classical
  obtain ⟨_, hcase⟩ := hyL
  rcases hcase with hyα | hyflood
  · 
    
    exact absurd (hyα.symm.trans hyβ) (ne_of_lt hαβ)
  · obtain ⟨x, hxbox, hxα, hxP, hreach⟩ := hyflood
    obtain ⟨γ⟩ := hreach
    
    set f := SimpleGraph.Hom.ofLE (boxMinusP_le ω α β m m' c d xB hxB) with hf
    refine ⟨x, γ.map f, hxbox, hxα, ?_⟩
    intro z hz
    have hsupp := SimpleGraph.Walk.support_map f γ
    obtain ⟨z', hz'mem, hz'eq⟩ := List.mem_map.mp (hsupp ▸ hz)
    have hz'fact : z' ∈ rect α β c d ∧ z' ∉ overlapComp ω m m' c d xB hxB :=
      boxMinusP_walk_dest ω α β m m' c d xB hxB hxbox hxP (γ.takeUntil z' hz'mem)
    
    have hzz' : z = z' := by simpa [hf] using hz'eq.symm
    rw [hzz']; exact hz'fact











theorem arcS_leftRegion_right (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαβ : α < β) (hαm : α ≤ m) (hmm' : m ≤ m') (hm'β : m' ≤ β)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (hcross : ArcS_TwoPathsCross ω α β m m' c d xB hxB) (z : Site 2)
    (hz : z ∈ rect α β c d) (hzβ : z 0 = β) :
    z ∉ arcS_leftRegion ω α β m m' c d xB hxB := by
  classical
  intro hzL
  obtain ⟨x, γ, hxbox, hxα, hsupp⟩ :=
    arcS_rightWall_in_L_gives_avoiding_walk ω hαβ xB hxB hz hzβ hzL
  obtain ⟨w, hwsupp, hwP⟩ :=
    hcross hαm hmm' hm'β x z hxbox hz hxα hzβ γ (fun z hz => (hsupp z hz).1)
  exact (hsupp w hwsupp).2 hwP



















theorem arcS_arc_sides_of_cross (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαβ : α < β)
    (hcross : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcS_TwoPathsCross ω α β m m' c d xB hxB) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro hαm hmm' hm'β xB hxB _hxBbot yT _hyT _hcV
  refine ⟨arcS_leftRegion ω α β m m' c d xB hxB, ?_, ?_, ?_⟩
  · intro z hzbox hzα
    exact arcS_leftRegion_left ω α β m m' c d xB hxB z hzbox hzα
  · intro z hzbox hzβ
    exact arcS_leftRegion_right ω hαβ hαm hmm' hm'β xB hxB (hcross xB hxB) z hzbox hzβ
  · intro u v hu hv hadj hbd
    exact arcS_leftRegion_bdEdge ω α β m m' c d xB hxB u v hu hv hadj hbd

end Lattice

end StatMech
