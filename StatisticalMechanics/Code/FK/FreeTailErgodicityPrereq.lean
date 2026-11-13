/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Foundations.AeTailInvariant
import Code.Lattice.HypercubicLattice
import Code.Percolation.BurtonKeane

open MeasureTheory Set

namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}






def fkTailEdgeWindow (d n : ℕ) : Set (Sym2 (Site d)) :=
  {e | ∀ x, x ∈ e → x ∈ box d n}

theorem fkTailEdgeWindow_mono : Monotone (fkTailEdgeWindow d) := by
  intro m n hmn e he x hx
  exact box_mono d hmn (he x hx)

private noncomputable def fkTailVertexSupport
    (F : Finset (Sym2 (Site d))) : Finset (Site d) :=
  F.biUnion fun e => {e.out.1, e.out.2}

private theorem mem_fkTailVertexSupport_of_mem
    {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)} (he : e ∈ F)
    {x : Site d} (hx : x ∈ e) : x ∈ fkTailVertexSupport F := by
  rw [fkTailVertexSupport, Finset.mem_biUnion]
  refine ⟨e, he, ?_⟩
  have hout : s(e.out.1, e.out.2) = e := e.out_eq
  have hx' : x ∈ s(e.out.1, e.out.2) := by
    rw [hout]
    exact hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    (Sym2.mem_iff.mp hx')




theorem fkTailEdgeWindow_escape (hd : 1 ≤ d)
    (F : Finset (Sym2 (Site d))) (k : ℕ) :
    ∃ g : Multiplicative (Site d),
      (↑(F.image (fun e => g⁻¹ • e)) : Set (Sym2 (Site d))) ⊆
        (fkTailEdgeWindow d k)ᶜ := by
  let V := fkTailVertexSupport F
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ x ∈ V, (x ⟨0, hd⟩).natAbs ≤ M :=
    ⟨V.sup fun x => (x ⟨0, hd⟩).natAbs,
      fun x hx => Finset.le_sup (f := fun x => (x ⟨0, hd⟩).natAbs) hx⟩
  set g : Multiplicative (Site d) :=
    Multiplicative.ofAdd
      (fun i => if i = ⟨0, hd⟩ then (M + k + 1 : ℤ) else 0) with hg
  refine ⟨g, ?_⟩
  intro z hz
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
  obtain ⟨e, he, rfl⟩ := hz
  rw [Set.mem_compl_iff]
  intro hwindow
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxV : x ∈ V :=
        mem_fkTailVertexSupport_of_mem he (Sym2.mem_mk_left x y)
      have hxBound : x ⟨0, hd⟩ ≤ (M : ℤ) := by
        have hnat := hM x hxV
        have habs := Int.le_natAbs (a := x ⟨0, hd⟩)
        omega
      have hxval : (g⁻¹ • x) ⟨0, hd⟩ =
          x ⟨0, hd⟩ - (M + k + 1 : ℤ) := by
        change (-(Multiplicative.toAdd g) + x) ⟨0, hd⟩ = _
        rw [hg]
        change -(if (⟨0, hd⟩ : Fin d) = ⟨0, hd⟩ then
          (M + k + 1 : ℤ) else 0) + x ⟨0, hd⟩ = _
        rw [if_pos rfl]
        ring
      have hxOutside : g⁻¹ • x ∉ box d k := by
        rw [box, Set.mem_setOf_eq]
        intro hall
        have hcoord := hall ⟨0, hd⟩
        rw [hxval] at hcoord
        have hneg : x ⟨0, hd⟩ - (M + k + 1 : ℤ) ≤ -(k + 1 : ℤ) := by
          omega
        have hcast : ((x ⟨0, hd⟩ - (M + k + 1 : ℤ)).natAbs : ℤ) =
            -(x ⟨0, hd⟩ - (M + k + 1 : ℤ)) := by
          rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
          omega
        have hcoord' :
            ((x ⟨0, hd⟩ - (M + k + 1 : ℤ)).natAbs : ℤ) ≤ k := by
          exact_mod_cast hcoord
        rw [hcast] at hcoord'
        omega
      apply hxOutside
      apply hwindow (g⁻¹ • x)
      rw [Percolation.smul_sym2_mk]
      exact Sym2.mem_mk_left (g⁻¹ • x) (g⁻¹ • y)

abbrev FKIsTailEvent (d : ℕ)
    (s : Set (ConfigSpace (Sym2 (Site d)))) : Prop :=
  AtiTailEvent (fkTailEdgeWindow d) s





theorem fk_invariant_event_ae_tail (hd : 1 ≤ d)
    {mu : Measure (ConfigSpace (Sym2 (Site d)))} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    ∀ s : Set (ConfigSpace (Sym2 (Site d))), MeasurableSet s →
      (∀ g : Multiplicative (Site d), shift g ⁻¹' s = s) →
      ∃ s' : Set (ConfigSpace (Sym2 (Site d))),
        FKIsTailEvent d s' ∧ s =ᵐ[mu] s' :=
  ati_invariant_aeTail (fkTailEdgeWindow d) fkTailEdgeWindow_mono
    (fkTailEdgeWindow_escape hd) hmu

end FK

end StatMech
