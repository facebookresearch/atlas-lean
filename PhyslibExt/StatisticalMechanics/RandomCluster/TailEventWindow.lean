/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.AeTailInvariant
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Probability.Percolation.InfiniteClusterCount

/-!
# Translation-invariant edge events are almost surely tail events

For a translation-invariant finite measure on edge configurations of `ℤᵈ`, every measurable
translation-invariant event agrees almost surely with a tail event.

## i. Overview

The edge windows `{e : both endpoints of e lie in Λₙ}` exhaust the edges of `ℤᵈ`, and any finite
edge set can be translated out of any given window. The general result that invariant events of a
translation-invariant measure are almost surely tail events, when finite sets can be moved off every
window, then applies to these windows. The headline is proved unconditionally, for `d ≥ 1` and any
translation-invariant finite measure.

## ii. Key results

- `fk_invariant_event_ae_tail` : a measurable translation-invariant event is almost surely equal to
  a tail event.
- `fkTailEdgeWindow_escape` : every finite edge set can be translated outside any box window.

## iii. Table of contents

- A. Box edge windows
- B. Invariant events are tail events

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 4.3.
-/

@[expose] public section

open MeasureTheory Set

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}

/-! ## A. Box edge windows -/

/-- The edges of `ℤᵈ` with both endpoints in the box `Λₙ`. -/
def fkTailEdgeWindow (d n : ℕ) : Set (Sym2 (Site d)) :=
  {e | ∀ x, x ∈ e → x ∈ box d n}

lemma fkTailEdgeWindow_mono : Monotone (fkTailEdgeWindow d) := by
  intro m n hmn e he x hx
  exact box_mono d hmn (he x hx)

/-- The finite set of endpoints of the edges in `F`. -/
private noncomputable def fkTailVertexSupport
    (F : Finset (Sym2 (Site d))) : Finset (Site d) :=
  F.biUnion fun e => {e.out.1, e.out.2}

private lemma mem_fkTailVertexSupport_of_mem
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

/-- For `d ≥ 1`, every finite edge set can be translated so that it avoids the box window `k`. -/
lemma fkTailEdgeWindow_escape (hd : 1 ≤ d)
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
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        ring
      have hxOutside : g⁻¹ • x ∉ box d k := by
        rw [box, Set.mem_ofPred_eq]
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

/-! ## B. Invariant events are tail events -/

/-- An edge event is a tail event if it does not depend on the edges of any box window. -/
abbrev FKIsTailEvent (d : ℕ)
    (s : Set (ConfigSpace (Sym2 (Site d)))) : Prop :=
  AtiTailEvent (fkTailEdgeWindow d) s

/-- For `d ≥ 1` and a translation-invariant finite measure, every measurable translation-invariant
edge event is almost surely equal to a tail event. -/
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
