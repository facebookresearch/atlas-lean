/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalFKG
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQTranslation

/-!
# Translation invariance of the free buffered infinite-volume FK measure

For `0 < p < 1` and `q ≥ 1`, the free buffered infinite-volume random-cluster measure on a periodic
graph is invariant under lattice translations.

## i. Overview

The probability that all edges of a finite set are open determines a measure on configurations.
For the free FK measure on a buffered box, this probability equals the corresponding one on the
translated box. Since the free measure is monotone in the volume for `q ≥ 1`, the translated box is
sandwiched between centered boxes, and both sequences of all-open probabilities converge to the
same infinite-volume limit. Hence the free limit gives the same mass to an all-open event and to its
translate, and agreement on these events, which form a π-system generating the σ-algebra, gives
translation invariance. `freeBufferedInfiniteVolume_isTranslationInvariant` is proved
unconditionally, with only `0 < p < 1` and `1 ≤ q`.

## ii. Key results

- `PeriodicGraph.freeBufferedInfiniteVolume_multiOpen_shift` : the free limit gives the same mass to
  an all-open event and to its translate.
- `PeriodicGraph.freeBufferedInfiniteVolume_isTranslationInvariant` : the free buffered
  infinite-volume FK measure is translation invariant.

## iii. Table of contents

- A. Translated buffered boxes
- B. Comparing all-open probabilities across boxes
- C. Limits of all-open probabilities
- D. Translation invariance

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

/-! ## A. Translated buffered boxes -/

/-- The vertices of the buffered box of index `n` translated by `z`. -/
noncomputable def PeriodicGraph.shiftedBufferedVertices
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) : Finset V :=
  (P.orbitBox (P.bufferedRadius n)).image (P.shift z)

/-- The vertices of the translated buffered box, as a subtype. -/
abbrev PeriodicGraph.ShiftedBufferedVertex
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :=
  {v : V // v ∈ P.shiftedBufferedVertices z n}

/-- The translated buffered box is finite. -/
noncomputable instance PeriodicGraph.instFintypeShiftedBufferedVertex
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    Fintype (P.ShiftedBufferedVertex z n) :=
  Fintype.ofFinset (P.shiftedBufferedVertices z n) (fun _ => Iff.rfl)

/-- Decidable equality of vertices of the translated buffered box. -/
instance PeriodicGraph.instDecidableEqShiftedBufferedVertex
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    DecidableEq (P.ShiftedBufferedVertex z n) := Subtype.instDecidableEq

/-- The graph induced on the translated buffered box. -/
noncomputable def PeriodicGraph.shiftedBufferedGraph
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    SimpleGraph (P.ShiftedBufferedVertex z n) :=
  P.graph.comap Subtype.val

/-- Classical decidability of adjacency in the translated buffered box. -/
noncomputable instance PeriodicGraph.instDecidableRelShiftedBufferedGraph
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    DecidableRel (P.shiftedBufferedGraph z n).Adj := Classical.decRel _

/-- Translation by `z` as a bijection from the buffered box to the translated buffered box. -/
noncomputable def PeriodicGraph.shiftBufferedEquiv
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    P.BufferedVertex n ≃ P.ShiftedBufferedVertex z n where
  toFun x := ⟨P.shift z x.1, Finset.mem_image.2 ⟨x.1, x.2, rfl⟩⟩
  invFun x := ⟨P.shift (-z) x.1, by
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 x.2
    rw [← hxy, P.shift_neg_shift]
    exact hy⟩
  left_inv x := Subtype.ext (P.shift_neg_shift z x.1)
  right_inv x := Subtype.ext (P.shift_shift_neg z x.1)

@[simp] lemma PeriodicGraph.shiftBufferedEquiv_val
    (P : PeriodicGraph V) (z : Site 2) (n : Nat)
    (x : P.BufferedVertex n) :
    (P.shiftBufferedEquiv z n x : V) = P.shift z x.1 := rfl

lemma PeriodicGraph.shiftBufferedEquiv_adj
    (P : PeriodicGraph V) (z : Site 2) (n : Nat)
    (x y : P.BufferedVertex n) :
    (P.bufferedGraph n).Adj x y ↔
      (P.shiftedBufferedGraph z n).Adj
        (P.shiftBufferedEquiv z n x) (P.shiftBufferedEquiv z n y) := by
  exact (P.shift_adj z x.1 y.1).symm

lemma PeriodicGraph.shift_orbitBox_subset_orbitBox
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    P.shift z '' (P.orbitBox n : Set V) ⊆
      (P.orbitBox (n + flc_vrad z) : Set V) := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ P.orbitBox n at hx
  change P.shift z x ∈ P.orbitBox (n + flc_vrad z)
  rw [P.mem_orbitBox_iff] at hx ⊢
  obtain ⟨w, hw, u, hu, rfl⟩ := hx
  refine ⟨w + z, ?_, u, hu, ?_⟩
  · intro i
    calc
      ((w + z) i).natAbs ≤ (w i).natAbs + (z i).natAbs := by
        simpa only [Pi.add_apply] using Int.natAbs_add_le (w i) (z i)
      _ ≤ n + flc_vrad z :=
        Nat.add_le_add (hw i) (flc_vrad_le z i)
  · exact P.shift_add w z u

lemma PeriodicGraph.orbitBox_subset_shift_orbitBox
    (P : PeriodicGraph V) (z : Site 2) {a n : Nat}
    (h : a + flc_vrad z ≤ n) :
    (P.orbitBox a : Set V) ⊆ P.shift z '' (P.orbitBox n : Set V) := by
  intro x hx
  change x ∈ P.orbitBox a at hx
  rw [P.mem_orbitBox_iff] at hx
  obtain ⟨w, hw, u, hu, rfl⟩ := hx
  refine ⟨P.shift (w - z) u, ?_, ?_⟩
  · change P.shift (w - z) u ∈ P.orbitBox n
    rw [P.mem_orbitBox_iff]
    exact ⟨w - z, flc_box_subset_transBox z h hw, u, hu, rfl⟩
  · rw [← P.shift_add (w - z) z u]
    congr 2
    ext i
    simp

lemma PeriodicGraph.bufferedRadius_add_le
    (P : PeriodicGraph V) (n c : Nat) :
    P.bufferedRadius n + c ≤ P.bufferedRadius (n + c) := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.add_succ, Nat.add_succ]
      exact (Nat.succ_le_succ ih).trans
        (Nat.succ_le_of_lt
          (P.bufferedRadius_strictMono (Nat.lt_succ_self (n + c))))

lemma PeriodicGraph.shiftedBuffered_subset_buffered
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    (P.shiftedBufferedVertices z n : Set V) ⊆
      (P.orbitBox (P.bufferedRadius (n + flc_vrad z)) : Set V) := by
  intro x hx
  rw [PeriodicGraph.shiftedBufferedVertices, Finset.coe_image] at hx
  exact P.orbitBox_mono
    (P.bufferedRadius_add_le n (flc_vrad z))
    (P.shift_orbitBox_subset_orbitBox z (P.bufferedRadius n) hx)

lemma PeriodicGraph.buffered_subset_shiftedBuffered
    (P : PeriodicGraph V) (z : Site 2) {a n : Nat}
    (h : a + flc_vrad z ≤ n) :
    (P.orbitBox (P.bufferedRadius a) : Set V) ⊆
      (P.shiftedBufferedVertices z n : Set V) := by
  intro x hx
  rw [PeriodicGraph.shiftedBufferedVertices, Finset.coe_image]
  apply P.orbitBox_subset_shift_orbitBox z
    (n := P.bufferedRadius n) _ hx
  exact (P.bufferedRadius_add_le a (flc_vrad z)).trans
    ((P.bufferedRadius_strictMono.le_iff_le).2 h)

/-- The inclusion of the translated box of index `n` into a buffered box of index `m`
containing it. -/
noncomputable def PeriodicGraph.shiftedToBufferedIncl
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.shiftedBufferedVertices z n : Set V) ⊆
      (P.orbitBox (P.bufferedRadius m) : Set V)) :
    P.ShiftedBufferedVertex z n → P.BufferedVertex m :=
  fun x => ⟨x.1, hsub x.2⟩

/-- The inclusion of the buffered box of index `n` into a translated box of index `m`
containing it. -/
noncomputable def PeriodicGraph.bufferedToShiftedIncl
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.orbitBox (P.bufferedRadius n) : Set V) ⊆
      (P.shiftedBufferedVertices z m : Set V)) :
    P.BufferedVertex n → P.ShiftedBufferedVertex z m :=
  fun x => ⟨x.1, hsub x.2⟩

/-! ## B. Comparing all-open probabilities across boxes -/

lemma PeriodicGraph.freeBufferedMeasure_real_multiOpen
    (P : PeriodicGraph V) (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (t : Finset (Sym2 (P.BufferedVertex n))) :
    (P.freeBufferedMeasure n hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius n)))) =
      med_multiMassProb (fkProb (P.bufferedGraph n) p q) t := by
  classical
  have hevent : fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius n))) =
      P.bufferedCylinder n (med_genericMultiOpenEvent t) := by
    ext omega
    simp only [fmu_multiOpen, Set.mem_ofPred_eq, Finset.forall_mem_image,
      PeriodicGraph.bufferedCylinder, Set.mem_preimage,
      med_genericMultiOpenEvent, PeriodicGraph.bufferedRestrict]
  rw [hevent, P.freeBufferedMeasure_real_cylinder (le_refl n) hp hp1 hq]
  unfold med_multiMassProb
  apply Finset.sum_congr rfl
  intro omega _
  have hrefl : P.bufferedRestrictLE (le_refl n) omega = omega := by
    funext e
    induction e using Sym2.inductionOn with
    | _ x y => rfl
  unfold Set.indicator
  change (if P.bufferedRestrictLE (le_refl n) omega ∈
      med_genericMultiOpenEvent t then 1 else 0) * _ = _
  rw [hrefl]

lemma PeriodicGraph.centered_eq_shifted_free_multiMass
    (P : PeriodicGraph V) (z : Site 2) (n : Nat)
    (t : Finset (Sym2 (P.BufferedVertex n))) (p q : Real) :
    med_multiMassProb (fkProb (P.bufferedGraph n) p q) t =
      med_multiMassProb (fkProb (P.shiftedBufferedGraph z n) p q)
        (t.image (Sym2.map (P.shiftBufferedEquiv z n))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (P.shiftBufferedEquiv z n)
    (fkProb (P.bufferedGraph n) p q)
    (fkProb (P.shiftedBufferedGraph z n) p q)
    (fun omega => fvs_fkProb_reCfgIso (P.bufferedGraph n)
      (P.shiftedBufferedGraph z n) (P.shiftBufferedEquiv z n)
      (P.shiftBufferedEquiv_adj z n) p q omega)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun omega _ => ?_
  rw [med_reCfgIso_preimage (P.shiftBufferedEquiv z n) t]

lemma PeriodicGraph.shifted_free_multiMass_le_buffered
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.shiftedBufferedVertices z n : Set V) ⊆
      (P.orbitBox (P.bufferedRadius m) : Set V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (Sym2 (P.ShiftedBufferedVertex z n))) :
    med_multiMassProb (fkProb (P.shiftedBufferedGraph z n) p q) t ≤
      med_multiMassProb (fkProb (P.bufferedGraph m) p q)
        (t.image (ocd_innerEdge (P.shiftedToBufferedIncl z n m hsub))) := by
  let incl := P.shiftedToBufferedIncl z n m hsub
  have hinj : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun v : P.BufferedVertex m => v.1) h)
  have hadj : ocd_AdjMatch (P.shiftedBufferedGraph z n)
      (P.bufferedGraph m) incl := by
    intro x y
    rfl
  have hdom := bdp_free_inner_dominated_fkProb hinj hadj hp hp1 hq
    (A := med_genericMultiOpenEvent t) (med_genericMultiOpenEvent_increasing t)
  rw [ocd_innerRestrict_preimage_multiOpenEvent hinj t] at hdom
  exact hdom

lemma PeriodicGraph.buffered_free_multiMass_le_shifted
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.orbitBox (P.bufferedRadius n) : Set V) ⊆
      (P.shiftedBufferedVertices z m : Set V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (Sym2 (P.BufferedVertex n))) :
    med_multiMassProb (fkProb (P.bufferedGraph n) p q) t ≤
      med_multiMassProb (fkProb (P.shiftedBufferedGraph z m) p q)
        (t.image (ocd_innerEdge (P.bufferedToShiftedIncl z n m hsub))) := by
  let incl := P.bufferedToShiftedIncl z n m hsub
  have hinj : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun v : P.ShiftedBufferedVertex z m => v.1) h)
  have hadj : ocd_AdjMatch (P.bufferedGraph n)
      (P.shiftedBufferedGraph z m) incl := by
    intro x y
    rfl
  have hdom := bdp_free_inner_dominated_fkProb hinj hadj hp hp1 hq
    (A := med_genericMultiOpenEvent t) (med_genericMultiOpenEvent_increasing t)
  rw [ocd_innerRestrict_preimage_multiOpenEvent hinj t] at hdom
  exact hdom

/-- The free FK probability, in the translated box of index `m`, that the translates of the edges
of `t` are all open. -/
noncomputable def PeriodicGraph.shiftedFreeMultiMass
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    (p q : Real) (m : Nat) (hNm : N ≤ m) : Real :=
  med_multiMassProb (fkProb (P.shiftedBufferedGraph z m) p q)
    ((t.image (Sym2.map (P.bufferedVertexInclLE hNm))).image
      (Sym2.map (P.shiftBufferedEquiv z m)))

lemma PeriodicGraph.shiftedFreeMultiMass_eq_centered
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m : Nat) (hNm : N ≤ m) :
    P.shiftedFreeMultiMass z N t p q m hNm =
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N)))) := by
  let tm := t.image (Sym2.map (P.bufferedVertexInclLE hNm))
  have hglobal : tm.image (P.edgeIncl (P.bufferedRadius m)) =
      t.image (P.edgeIncl (P.bufferedRadius N)) := by
    dsimp only [tm]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro e he
    exact P.edgeIncl_bufferedVertexInclLE hNm e
  rw [← hglobal]
  rw [P.freeBufferedMeasure_real_multiOpen m hp hp1
    (zero_lt_one.trans_le hq) tm]
  have hiso := P.centered_eq_shifted_free_multiMass z m tm p q
  unfold PeriodicGraph.shiftedFreeMultiMass
  exact hiso.symm

lemma PeriodicGraph.shiftedFreeMultiMass_le_centered_shift
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m : Nat) (hNm : N ≤ m) :
    P.shiftedFreeMultiMass z N t p q m hNm ≤
      (P.freeBufferedMeasure (m + flc_vrad z) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image
          (Sym2.map (P.shift z)))) := by
  let tm := t.image (Sym2.map (P.bufferedVertexInclLE hNm))
  let hsub := P.shiftedBuffered_subset_buffered z m
  have hdom := P.shifted_free_multiMass_le_buffered z m
    (m + flc_vrad z) hsub hp hp1 hq
    (tm.image (Sym2.map (P.shiftBufferedEquiv z m)))
  rw [← P.freeBufferedMeasure_real_multiOpen (m + flc_vrad z)
    hp hp1 (zero_lt_one.trans_le hq)] at hdom
  refine hdom.trans_eq ?_
  congr 2
  simp only [tm, Finset.image_image]
  apply Finset.image_congr
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y => rfl

lemma PeriodicGraph.centered_shift_le_shiftedFreeMultiMass
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m a : Nat) (hNm : N ≤ m) (ha : a + flc_vrad z ≤ m)
    (ta : Finset (Sym2 (P.BufferedVertex a)))
    (hta : ta.image (P.edgeIncl (P.bufferedRadius a)) =
      (t.image (P.edgeIncl (P.bufferedRadius N))).image
        (Sym2.map (P.shift z))) :
    (P.freeBufferedMeasure a hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image
          (Sym2.map (P.shift z)))) ≤
      P.shiftedFreeMultiMass z N t p q m hNm := by
  let tm := t.image (Sym2.map (P.bufferedVertexInclLE hNm))
  let hsub := P.buffered_subset_shiftedBuffered z ha
  have hdom := P.buffered_free_multiMass_le_shifted z a m hsub
    hp hp1 hq ta
  rw [← P.freeBufferedMeasure_real_multiOpen a hp hp1
    (zero_lt_one.trans_le hq), hta] at hdom
  have hedge : ta.image
      (ocd_innerEdge (P.bufferedToShiftedIncl z a m hsub)) =
      (tm.image (Sym2.map (P.shiftBufferedEquiv z m))) := by
    apply Finset.image_injective
      (Sym2.map.injective (f := (Subtype.val :
        P.ShiftedBufferedVertex z m → V)) Subtype.val_injective)
    rw [Finset.image_image, Finset.image_image]
    calc
      ta.image ((Sym2.map (Subtype.val : P.ShiftedBufferedVertex z m → V)) ∘
          ocd_innerEdge (P.bufferedToShiftedIncl z a m hsub)) =
          ta.image (P.edgeIncl (P.bufferedRadius a)) := by
            apply Finset.image_congr
            intro e he
            induction e using Sym2.inductionOn with
            | _ x y => rfl
      _ = (t.image (P.edgeIncl (P.bufferedRadius N))).image
          (Sym2.map (P.shift z)) := hta
      _ = tm.image ((Sym2.map (Subtype.val : P.ShiftedBufferedVertex z m → V)) ∘
          Sym2.map (P.shiftBufferedEquiv z m)) := by
            simp only [tm, Finset.image_image]
            apply Finset.image_congr
            intro e he
            induction e using Sym2.inductionOn with
            | _ x y => rfl
  refine hdom.trans_eq ?_
  unfold PeriodicGraph.shiftedFreeMultiMass
  rw [hedge]

/-! ## C. Limits of all-open probabilities -/

lemma isClopen_fmu_multiOpen (T : Finset (Sym2 V)) :
    IsClopen (fmu_multiOpen T) := by
  have heq : fmu_multiOpen T = cylinder T
      {eta : ∀ _e : T, Bool | ∀ e : T, eta e = true} := by
    ext omega
    simp only [fmu_multiOpen, Set.mem_ofPred_eq, cylinder, Set.mem_preimage]
    constructor
    · intro h e
      exact h e.1 e.2
    · intro h e he
      exact h ⟨e, he⟩
  rw [heq]
  exact isClopen_cylinderEvent T _

/-- A lift of a finite set of edges lying in the buffered window `N` to edges of the buffered
box. -/
noncomputable def PeriodicGraph.bufferedEdgeLift
    (P : PeriodicGraph V) (N : Nat) (T : Finset (Sym2 V))
    (hT : ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
    Finset (Sym2 (P.BufferedVertex N)) :=
  T.attach.image fun e => (hT e.1 e.2).choose

lemma PeriodicGraph.bufferedEdgeLift_image
    (P : PeriodicGraph V) (N : Nat) (T : Finset (Sym2 V))
    (hT : ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
    (P.bufferedEdgeLift N T hT).image
        (P.edgeIncl (P.bufferedRadius N)) = T := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨eb, heb, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨e', he'T, heq⟩ := Finset.mem_image.1 heb
    rw [← heq, (hT e'.1 e'.2).choose_spec]
    exact e'.2
  · intro he
    apply Finset.mem_image.2
    refine ⟨(hT e he).choose, ?_, (hT e he).choose_spec⟩
    apply Finset.mem_image.2
    exact ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩

lemma PeriodicGraph.shiftedFreeMultiMass_tendsto_centered
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => P.shiftedFreeMultiMass z N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N)))))) := by
  have hbase := (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (isClopen_fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N))))
  have hsub := hbase.comp (tendsto_add_atTop_nat N)
  refine hsub.congr' ?_
  filter_upwards with k
  symm
  simpa only [Function.comp_apply, Nat.add_comm] using
    P.shiftedFreeMultiMass_eq_centered z N t hp hp1 hq
      (N + k) (Nat.le_add_right N k)

lemma PeriodicGraph.shiftedFreeMultiMass_tendsto_shifted
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => P.shiftedFreeMultiMass z N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image
            (Sym2.map (P.shift z)))))) := by
  classical
  let T := (t.image (P.edgeIncl (P.bufferedRadius N))).image
    (Sym2.map (P.shift z))
  obtain ⟨N', hN'⟩ := P.exists_bufferedLevel_edges T
  let t' := P.bufferedEdgeLift N' T hN'
  have ht' : t'.image (P.edgeIncl (P.bufferedRadius N')) = T :=
    P.bufferedEdgeLift_image N' T hN'
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have hbase : Tendsto (fun r =>
      (P.freeBufferedMeasure r hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen T)) atTop
      (nhds (mu.real (fmu_multiOpen T))) :=
    (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
      (isClopen_fmu_multiOpen T)
  let c := flc_vrad z
  have hlo : Tendsto (fun k =>
      (P.freeBufferedMeasure ((N + k) - c) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen T)) atTop (nhds (mu.real (fmu_multiOpen T))) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + N + c, fun k hk => by omega⟩
  have hhi : Tendsto (fun k =>
      (P.freeBufferedMeasure ((N + k) + c) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen T)) atTop (nhds (mu.real (fmu_multiOpen T))) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk => by omega⟩
  change Tendsto _ _ (nhds (mu.real (fmu_multiOpen T)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (N' + c)] with k hk
    let a := (N + k) - c
    have hN'a : N' ≤ a := by dsimp only [a, c]; omega
    let ta := t'.image (Sym2.map (P.bufferedVertexInclLE hN'a))
    have hta : ta.image (P.edgeIncl (P.bufferedRadius a)) = T := by
      dsimp only [ta]
      rw [Finset.image_image]
      calc
        t'.image (P.edgeIncl (P.bufferedRadius a) ∘
            Sym2.map (P.bufferedVertexInclLE hN'a)) =
            t'.image (P.edgeIncl (P.bufferedRadius N')) := by
              apply Finset.image_congr
              intro e he
              exact P.edgeIncl_bufferedVertexInclLE hN'a e
        _ = T := ht'
    have ha : a + flc_vrad z ≤ N + k := by dsimp only [a, c]; omega
    change _ ≤ P.shiftedFreeMultiMass z N t p q (N + k) _
    simpa only [T, c] using P.centered_shift_le_shiftedFreeMultiMass
      z N t hp hp1 hq (N + k) a (Nat.le_add_right N k) ha ta hta
  · filter_upwards with k
    change P.shiftedFreeMultiMass z N t p q (N + k) _ ≤ _
    simpa only [T, c] using P.shiftedFreeMultiMass_le_centered_shift
      z N t hp hp1 hq (N + k) (Nat.le_add_right N k)

/-! ## D. Translation invariance -/

/-- The free limit gives the same mass to the event that all edges of `T` are open and to its
translate by `z`. -/
lemma PeriodicGraph.freeBufferedInfiniteVolume_multiOpen_shift
    (P : PeriodicGraph V) (z : Site 2) (T : Finset (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V))) (fmu_multiOpen T) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V)))
        (fmu_multiOpen (T.image (Sym2.map (P.shift z)))) := by
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges T
  let t := P.bufferedEdgeLift N T hN
  have ht : t.image (P.edgeIncl (P.bufferedRadius N)) = T :=
    P.bufferedEdgeLift_image N T hN
  have hcenter := P.shiftedFreeMultiMass_tendsto_centered z N t hp hp1 hq
  have hshift := P.shiftedFreeMultiMass_tendsto_shifted z N t hp hp1 hq
  have hreal := tendsto_nhds_unique hcenter hshift
  rw [ht] at hreal
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

lemma PeriodicGraph.configTranslate_preimage_fmu_multiOpen
    (P : PeriodicGraph V) (z : Site 2) (T : Finset (Sym2 V)) :
    P.configTranslate z ⁻¹' fmu_multiOpen T =
      fmu_multiOpen (T.image (Sym2.map (P.shift (-z)))) := by
  ext omega
  simp only [Set.mem_preimage, fmu_multiOpen, Set.mem_ofPred_eq,
    PeriodicGraph.configTranslate, Finset.forall_mem_image]

/-- For `0 < p < 1` and `q ≥ 1`, the free buffered infinite-volume FK measure is invariant under
lattice translations. -/
theorem PeriodicGraph.freeBufferedInfiniteVolume_isTranslationInvariant
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    P.IsTranslationInvariant
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))) := by
  intro z
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  have : IsProbabilityMeasure (Measure.map (P.configTranslate z) mu) :=
    inferInstance
  refine MeasurePreserving.mk (P.measurable_configTranslate z) ?_
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  rw [Measure.map_apply (P.measurable_configTranslate z)
    (fmu_multiOpen_measurable T),
    P.configTranslate_preimage_fmu_multiOpen z T]
  exact (P.freeBufferedInfiniteVolume_multiOpen_shift (-z) T hp hp1 hq).symm

end StatMech.FK.PeriodicPlanar
