/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Code.Inequalities.BK
import Code.Inequalities.DisjointOccurrence
import Code.Inequalities.IncreasingEvent
import Code.Foundations.ProductMeasure

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

namespace Sharpness

open ConfigSpace



variable {E : Type*}










lemma OccursOn.mono_config {A : Set (ConfigSpace E)} (hA : IsIncreasing A) {K : Set E}
    {ω ω' : ConfigSpace E} (h : ω ≤ ω') (hocc : OccursOn A K ω) :
    OccursOn A K ω' := by
  classical
  intro τ hτ
  set σ : ConfigSpace E := fun e => if e ∈ K then ω e else τ e with hσ
  have hσA : σ ∈ A := by
    apply hocc
    intro e he
    simp only [hσ, if_pos he]
  apply hA _ hσA
  intro e
  by_cases he : e ∈ K
  · simp only [hσ, if_pos he]; rw [hτ e he]; exact h e
  · simp only [hσ, if_neg he]; exact le_refl _





lemma disjointOccurrence_isIncreasing {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    IsIncreasing (disjointOccurrence A B) := by
  intro ω ω' hωω' hω
  obtain ⟨K, L, hKL, hAK, hBL⟩ := hω
  exact ⟨K, L, hKL, OccursOn.mono_config hA hωω' hAK, OccursOn.mono_config hB hωω' hBL⟩










lemma bk_triple [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {P Q R : Set (ConfigSpace E)} (hP : IsIncreasing P) (hQ : IsIncreasing Q)
    (hR : IsIncreasing R) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence P (disjointOccurrence Q R))
      ≤ (bernoulliProductMeasure (E := E) p hp).real P
        * (bernoulliProductMeasure (E := E) p hp).real Q
        * (bernoulliProductMeasure (E := E) p hp).real R := by
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have hQR : IsIncreasing (disjointOccurrence Q R) := disjointOccurrence_isIncreasing hQ hR
  calc μ.real (disjointOccurrence P (disjointOccurrence Q R))
      ≤ μ.real P * μ.real (disjointOccurrence Q R) := bk_inequality hp hP hQR
    _ ≤ μ.real P * (μ.real Q * μ.real R) :=
        mul_le_mul_of_nonneg_left (bk_inequality hp hQ hR) measureReal_nonneg
    _ = μ.real P * μ.real Q * μ.real R := by ring
















theorem bk_criterion {ι : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (s : Finset ι) (P Q R : ι → Set (ConfigSpace E))
    (hP : ∀ i ∈ s, IsIncreasing (P i)) (hQ : ∀ i ∈ s, IsIncreasing (Q i))
    (hR : ∀ i ∈ s, IsIncreasing (R i))
    {C : Set (ConfigSpace E)}
    (hC : C ⊆ ⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
    (bernoulliProductMeasure (E := E) p hp).real C
      ≤ ∑ i ∈ s, (bernoulliProductMeasure (E := E) p hp).real (P i)
          * (bernoulliProductMeasure (E := E) p hp).real (Q i)
          * (bernoulliProductMeasure (E := E) p hp).real (R i) := by
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  calc μ.real C
      ≤ μ.real (⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
        measureReal_mono hC (measure_ne_top _ _)
    _ ≤ ∑ i ∈ s, μ.real (disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
        measureReal_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, μ.real (P i) * μ.real (Q i) * μ.real (R i) :=
        Finset.sum_le_sum (fun i hi => bk_triple hp (hP i hi) (hQ i hi) (hR i hi))









variable {V : Type*}



def openSub (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ω s(x, y) = true
  symm := by
    intro x y ⟨hadj, hopen⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x ⟨hadj, _⟩ => G.loopless.1 x hadj⟩



lemma openSub_mono (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)} (h : ω ≤ ω') :
    openSub G ω ≤ openSub G ω' := by
  intro x y ⟨hadj, hopen⟩
  refine ⟨hadj, ?_⟩
  have hb := h s(x, y)
  rw [hopen] at hb
  exact le_antisymm le_top hb




def ConnWithin (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) (A : Set V) (x y : A) : Prop :=
  ((openSub G ω).induce A).Reachable x y


lemma ConnWithin.mono_config (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)} (h : ω ≤ ω')
    {A : Set V} {x y : A} (hc : ConnWithin G ω A x y) : ConnWithin G ω' A x y :=
  hc.mono (fun _ _ hab => openSub_mono G h hab)




def ConnToSet (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) (A : Set V)
    (u : V) (B : Set V) : Prop :=
  ∃ (hu : u ∈ A) (b : V) (hb : b ∈ A), b ∈ B ∧ ConnWithin G ω A ⟨u, hu⟩ ⟨b, hb⟩


def connEvent (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V) :
    Set (ConfigSpace (Sym2 V)) := {ω | ConnToSet G ω A u B}




def edgeOpenEvent (x y : V) : Set (ConfigSpace (Sym2 V)) := {ω | ω s(x, y) = true}



lemma isIncreasing_connEvent (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V) :
    IsIncreasing (connEvent G A u B) := by
  intro ω ω' hωω' hω
  simp only [connEvent, Set.mem_setOf_eq, ConnToSet] at hω ⊢
  obtain ⟨hu, b, hb, hbB, hconn⟩ := hω
  exact ⟨hu, b, hb, hbB, hconn.mono_config G hωω'⟩


lemma isIncreasing_edgeOpenEvent (x y : V) : IsIncreasing (edgeOpenEvent (V := V) x y) := by
  intro ω ω' hωω' hω
  simp only [edgeOpenEvent, Set.mem_setOf_eq] at hω ⊢
  have hb := hωω' s(x, y)
  rw [hω] at hb
  exact le_antisymm le_top hb



set_option linter.unusedVariables false in





















theorem bk_criterion_conn {ι : Type*} [Fintype V] [DecidableEq V]
    {p : ℝ≥0} (hp : p ≤ 1) (G : SimpleGraph V)
    (A S B : Set V) (u : V)
    (s : Finset ι) (boundaryPair : ι → V × V)
    (hincl : connEvent G A u B ⊆
      ⋃ i ∈ s, disjointOccurrence (connEvent G S u {(boundaryPair i).1})
        (disjointOccurrence (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
          (connEvent G A (boundaryPair i).2 B))) :
    (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G A u B)
      ≤ ∑ i ∈ s,
          (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G S u {(boundaryPair i).1})
          * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
          * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G A (boundaryPair i).2 B) := by
  refine bk_criterion hp s
    (fun i => connEvent G S u {(boundaryPair i).1})
    (fun i => edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
    (fun i => connEvent G A (boundaryPair i).2 B)
    (fun i _ => isIncreasing_connEvent G S u _)
    (fun i _ => isIncreasing_edgeOpenEvent _ _)
    (fun i _ => isIncreasing_connEvent G A _ B)
    hincl

end Sharpness

end StatMech
