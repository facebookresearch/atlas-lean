/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCodingLaw
import Code.OSSS.AdaptiveTau
import Code.OSSS.AdaptDisintegration
import Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]





inductive CausalOrder : Finset E → Type _
  | done : CausalOrder ∅
  | node {R : Finset E} (e : E) (he : e ∈ R)
      (independent : Bool) (closed opened : CausalOrder (R.erase e)) : CausalOrder R




def realizedList : {R : Finset E} → CausalOrder R → ConfigSpace E → List E
  | _, .done, _ => []
  | _, .node e _ _ closed opened, base =>
      if base e then e :: realizedList opened base
      else e :: realizedList closed base


lemma realizedList_toFinset {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedList S base).toFinset = R := by
  induction S with
  | done => rfl
  | @node R e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [realizedList, hb, if_true, List.toFinset_cons]
        rw [iho, Finset.insert_erase he]
      · simp only [realizedList, hb, Bool.false_eq_true, if_false, List.toFinset_cons]
        rw [ihc, Finset.insert_erase he]


lemma realizedList_nodup {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedList S base).Nodup := by
  induction S with
  | done => simp [realizedList]
  | @node R e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [realizedList, hb, if_true, List.nodup_cons]
        refine ⟨?_, iho⟩
        rw [← List.mem_toFinset, realizedList_toFinset]
        simp
      · simp only [realizedList, hb, Bool.false_eq_true, if_false, List.nodup_cons]
        refine ⟨?_, ihc⟩
        rw [← List.mem_toFinset, realizedList_toFinset]
        simp

lemma realizedList_length {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedList S base).length = R.card := by
  rw [← List.toFinset_card_of_nodup (realizedList_nodup S base),
    realizedList_toFinset]




noncomputable def realizedEquiv
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Fin (Fintype.card E) ≃ E := by
  let l := realizedList S base
  have hnd : l.Nodup := realizedList_nodup S base
  have hall : ∀ e : E, e ∈ l := by
    intro e
    rw [← List.mem_toFinset, realizedList_toFinset]
    exact Finset.mem_univ e
  have hlen : l.length = Fintype.card E := by
    calc
      l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = (Finset.univ : Finset E).card := by
        rw [show l = realizedList S base from rfl, realizedList_toFinset]
      _ = Fintype.card E := Finset.card_univ
  exact (finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hall)

lemma realizedEquiv_symm_val
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E) (e : E) :
    ((realizedEquiv S base).symm e : ℕ) = (realizedList S base).idxOf e := by
  unfold realizedEquiv
  simp [List.Nodup.getEquivOfForallMemList]



lemma prefixSet_realizedEquiv (S : CausalOrder (Finset.univ : Finset E))
    (base : ConfigSpace E) (e : E) :
    prefixSet (realizedEquiv S base : Fin (Fintype.card E) → E)
        ((realizedEquiv S base).symm e : ℕ) =
      ((realizedList S base).take ((realizedList S base).idxOf e)).toFinset := by
  ext z
  have hze : z ∈ realizedList S base := by
    rw [← List.mem_toFinset, realizedList_toFinset]
    exact Finset.mem_univ z
  rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt hze]
  rw [mem_prefixSet_iff]
  constructor
  · rintro ⟨j, hj, hjz⟩
    have hpos : j = ((realizedEquiv S base).symm z : Fin (Fintype.card E)) :=
      (realizedEquiv S base).injective (by simpa using hjz)
    subst j
    simpa only [realizedEquiv_symm_val] using hj
  · intro hj
    refine ⟨(realizedEquiv S base).symm z, ?_, by simp⟩
    simpa only [realizedEquiv_symm_val] using hj

lemma thr_realizedEquiv (μ : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E)) (base target : ConfigSpace E) (e : E) :
    thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) target
        ((realizedEquiv S base).symm e) =
      condProbClosed μ
        ((realizedList S base).take ((realizedList S base).idxOf e)).toFinset
        target e := by
  unfold thr
  rw [prefixSet_realizedEquiv, Equiv.apply_symm_apply]




def independentAt : {R : Finset E} → CausalOrder R →
    ConfigSpace E → E → Bool
  | _, .done, _, _ => false
  | _, .node e _ independent closed opened, base, z =>
      if z = e then independent
      else if base e then independentAt opened base z
      else independentAt closed base z




noncomputable def causalMixLabels
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) : Fin (Fintype.card E) → ℝ :=
  fun i => if independentAt S base (realizedEquiv S base i) then V i else U i




noncomputable def frozenCodeAtom (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    Set (Fin (Fintype.card E) → (ℝ × ℝ)) :=
  {z | let sigma := realizedEquiv S base
       let U := fun i => (z i).1
       let V := fun i => (z i).2
       codeMap mu (sigma : Fin (Fintype.card E) → E) U = base ∧
         codeMap mu (sigma : Fin (Fintype.card E) → E)
           (causalMixLabels S base U V) = target}


noncomputable def frozenRawPair (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) (i : Fin (Fintype.card E)) : Set (ℝ × ℝ) :=
  let sigma := realizedEquiv S base
  let A := StatMech.OSSS.GrandCoupling.rawInterval mu
    (sigma : Fin (Fintype.card E) → E) base i
  let B := StatMech.OSSS.GrandCoupling.rawInterval mu
    (sigma : Fin (Fintype.card E) → E) target i
  if independentAt S base (sigma i) then A ×ˢ B else (A ∩ B) ×ˢ Set.univ





theorem frozenCodeAtom_eq_rawPairBox (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    frozenCodeAtom mu S base target =
      Set.univ.pi (frozenRawPair mu S base target) := by
  let sigma := realizedEquiv S base
  have hsigma : realizedEquiv S base = sigma := rfl
  ext z
  have hbase :
      codeMap mu (sigma : Fin (Fintype.card E) → E) (fun i => (z i).1) = base ↔
        ∀ i, (z i).1 ∈ StatMech.OSSS.GrandCoupling.rawInterval mu
          (sigma : Fin (Fintype.card E) → E) base i := by
    have h := Set.ext_iff.mp
      (StatMech.OSSS.GrandCoupling.codeMap_fibre_eq_rawbox mu sigma base)
      (fun i => (z i).1)
    simpa [Set.mem_pi] using h
  have htarget :
      codeMap mu (sigma : Fin (Fintype.card E) → E)
          (causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2)) = target ↔
        ∀ i, causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2) i ∈
          StatMech.OSSS.GrandCoupling.rawInterval mu
            (sigma : Fin (Fintype.card E) → E) target i := by
    have h := Set.ext_iff.mp
      (StatMech.OSSS.GrandCoupling.codeMap_fibre_eq_rawbox mu sigma target)
      (causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2))
    simpa [Set.mem_pi] using h
  simp only [frozenCodeAtom, Set.mem_setOf_eq]
  change
    (codeMap mu (sigma : Fin (Fintype.card E) → E) (fun i => (z i).1) = base ∧
      codeMap mu (sigma : Fin (Fintype.card E) → E)
        (causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2)) = target) ↔
      z ∈ Set.univ.pi (frozenRawPair mu S base target)
  rw [hbase, htarget]
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hb, ht⟩ i
    specialize hb i
    specialize ht i
    simp only [frozenRawPair, hsigma]
    by_cases hi : independentAt S base (sigma i)
    · simpa [hi, causalMixLabels, hsigma] using And.intro hb ht
    · simpa [hi, causalMixLabels, hsigma] using And.intro hb ht
  · intro h
    constructor
    · intro i
      specialize h i
      simp only [frozenRawPair, hsigma] at h
      by_cases hi : independentAt S base (sigma i)
      · simp only [hi, if_true, Set.mem_prod] at h
        exact h.1
      · simp only [hi, Bool.false_eq_true, if_false, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h
        exact h.1
    · intro i
      specialize h i
      simp only [frozenRawPair, hsigma] at h
      by_cases hi : independentAt S base (sigma i)
      · simp only [hi, if_true, Set.mem_prod] at h
        simpa [causalMixLabels, hsigma, hi] using h.2
      · simp only [hi, Bool.false_eq_true, if_false, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h
        simpa [causalMixLabels, hsigma, hi] using h.2




noncomputable def pairedCube (n : ℕ) : Measure (Fin n → (ℝ × ℝ)) :=
  Measure.pi fun _ =>
    (volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1))



theorem pairedCube_measurePreserving (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (pairedCube n) ((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
  simpa [pairedCube, GrandCoupling.Vcube] using
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1))
      (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)))

theorem pairedCube_integral_equiv (n : ℕ)
    (g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) :
    (∫ z, g (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) z)
        ∂(pairedCube n)) =
      ∫ p, g p ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
  exact (pairedCube_measurePreserving n).integral_comp
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).measurableEmbedding g




theorem pairedCube_frozenCodeAtom (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    pairedCube (Fintype.card E) (frozenCodeAtom mu S base target) =
      ∏ i : Fin (Fintype.card E),
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1)))
            (frozenRawPair mu S base target i) := by
  rw [frozenCodeAtom_eq_rawPairBox, pairedCube, Measure.pi_pi]

inductive TripleMode where
  | before
  | flip
  | after
  deriving DecidableEq


inductive TripleOrder : Finset E → Type _
  | done : TripleOrder ∅
  | node {R : Finset E} (e : E) (he : e ∈ R) (mode : TripleMode)
      (closed opened : TripleOrder (R.erase e)) : TripleOrder R

def TripleMode.leftIndependent : TripleMode → Bool
  | .before => true
  | .flip => false
  | .after => false

def TripleMode.rightIndependent : TripleMode → Bool
  | .before => true
  | .flip => true
  | .after => false

def TripleOrder.leftOrder : {R : Finset E} → TripleOrder R → CausalOrder R
  | _, .done => .done
  | _, .node e he mode closed opened =>
      .node e he mode.leftIndependent closed.leftOrder opened.leftOrder

def TripleOrder.rightOrder : {R : Finset E} → TripleOrder R → CausalOrder R
  | _, .done => .done
  | _, .node e he mode closed opened =>
      .node e he mode.rightIndependent closed.rightOrder opened.rightOrder


def tripleModeAt : {R : Finset E} → TripleOrder R →
    ConfigSpace E → E → TripleMode
  | _, .done, _, _ => .after
  | _, .node e _ mode closed opened, base, z =>
      if z = e then mode
      else if base e then tripleModeAt opened base z
      else tripleModeAt closed base z

lemma realizedList_leftOrder_eq_rightOrder {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) :
    realizedList S.leftOrder base = realizedList S.rightOrder base := by
  induction S with
  | done => rfl
  | node e he mode closed opened ihc iho =>
      simp only [TripleOrder.leftOrder, TripleOrder.rightOrder, realizedList]
      split <;> simp_all

lemma realizedEquiv_leftOrder_eq_rightOrder
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    realizedEquiv S.leftOrder base = realizedEquiv S.rightOrder base := by
  apply Equiv.ext
  intro i
  apply (realizedEquiv S.rightOrder base).symm.injective
  apply Fin.ext
  rw [Equiv.symm_apply_apply]
  rw [realizedEquiv_symm_val]
  rw [← realizedList_leftOrder_eq_rightOrder S base]
  rw [← realizedEquiv_symm_val]
  simp

lemma independentAt_leftOrder {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) (z : E) :
    independentAt S.leftOrder base z = (tripleModeAt S base z).leftIndependent := by
  induction S with
  | done => rfl
  | @node R e he mode closed opened ihc iho =>
      simp only [TripleOrder.leftOrder, independentAt, tripleModeAt]
      by_cases hze : z = e
      · simp [hze]
      · simp only [hze, if_false]
        split <;> assumption

lemma independentAt_rightOrder {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) (z : E) :
    independentAt S.rightOrder base z = (tripleModeAt S base z).rightIndependent := by
  induction S with
  | done => rfl
  | @node R e he mode closed opened ihc iho =>
      simp only [TripleOrder.rightOrder, independentAt, tripleModeAt]
      by_cases hze : z = e
      · simp [hze]
      · simp only [hze, if_false]
        split <;> assumption

lemma causalMixLabels_leftOrder_apply
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (i : Fin (Fintype.card E)) :
    causalMixLabels S.leftOrder base U V i =
      match tripleModeAt S base (realizedEquiv S.leftOrder base i) with
      | .before => V i
      | .flip => U i
      | .after => U i := by
  unfold causalMixLabels
  rw [independentAt_leftOrder]
  cases tripleModeAt S base (realizedEquiv S.leftOrder base i) <;> rfl

lemma causalMixLabels_rightOrder_apply
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (i : Fin (Fintype.card E)) :
    causalMixLabels S.rightOrder base U V i =
      match tripleModeAt S base (realizedEquiv S.rightOrder base i) with
      | .before => V i
      | .flip => V i
      | .after => U i := by
  unfold causalMixLabels
  rw [independentAt_rightOrder]
  cases tripleModeAt S base (realizedEquiv S.rightOrder base i) <;> rfl


lemma causalMixLabels_left_eq_right_of_mode_ne_flip
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (i : Fin (Fintype.card E))
    (hmode : tripleModeAt S base (realizedEquiv S.leftOrder base i) ≠ .flip) :
    causalMixLabels S.leftOrder base U V i =
      causalMixLabels S.rightOrder base U V i := by
  rw [causalMixLabels_leftOrder_apply, causalMixLabels_rightOrder_apply]
  rw [← realizedEquiv_leftOrder_eq_rightOrder S base]
  cases hm : tripleModeAt S base (realizedEquiv S.leftOrder base i) <;>
    simp_all



lemma causalMixLabels_leftOrder_eq_rightOrder_of_no_flip
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (hno : ∀ e, tripleModeAt S base e ≠ .flip)
    (U V : Fin (Fintype.card E) → ℝ) :
    causalMixLabels S.leftOrder base U V =
      causalMixLabels S.rightOrder base U V := by
  funext i
  exact causalMixLabels_left_eq_right_of_mode_ne_flip S base U V i
    (hno (realizedEquiv S.leftOrder base i))

lemma measurable_causalMixLabels_right
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U : Fin (Fintype.card E) → ℝ) :
    Measurable (fun V => causalMixLabels S base U V) := by
  apply measurable_pi_lambda
  intro i
  unfold causalMixLabels
  by_cases h : independentAt S base (realizedEquiv S base i)
  · simpa [h] using
      (measurable_pi_apply i : Measurable (fun V : Fin (Fintype.card E) → ℝ => V i))
  · simpa [h] using
      (measurable_const : Measurable (fun _ : Fin (Fintype.card E) → ℝ => U i))



lemma measurable_causalMixLabels_prod
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
        (Fin (Fintype.card E) → ℝ) => causalMixLabels S base p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  unfold causalMixLabels
  by_cases h : independentAt S base (realizedEquiv S base i)
  · simp only [h, if_true]
    exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h, if_false]
    exact (measurable_pi_apply i).comp measurable_fst



lemma causalMixLabels_mono_right
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U : Fin (Fintype.card E) → ℝ) :
    Monotone (fun V => causalMixLabels S base U V) := by
  intro V V' hVV i
  change (if independentAt S base (realizedEquiv S base i) then V i else U i) ≤
    (if independentAt S base (realizedEquiv S base i) then V' i else U i)
  by_cases h : independentAt S base (realizedEquiv S base i)
  · simpa [h] using hVV i
  · simp [h]



noncomputable def frozenTripleCodeAtom (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) : Set (Fin (Fintype.card E) → (ℝ × ℝ)) :=
  frozenCodeAtom mu S.leftOrder base left ∩
    frozenCodeAtom mu S.rightOrder base right



noncomputable def pairedCausalOutputs (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    (Fin (Fintype.card E) → (ℝ × ℝ)) →
      ConfigSpace E × (ConfigSpace E × ConfigSpace E) := fun z =>
  let σ := realizedEquiv S.leftOrder base
  let U := fun i => (z i).1
  let V := fun i => (z i).2
  (codeMap mu (σ : Fin (Fintype.card E) → E) U,
    codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base U V),
    codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base U V))

lemma measurable_pairedCausalOutputs (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Measurable (pairedCausalOutputs mu S base) := by
  let σ := realizedEquiv S.leftOrder base
  let split : (Fin (Fintype.card E) → (ℝ × ℝ)) →
      (Fin (Fintype.card E) → ℝ) × (Fin (Fintype.card E) → ℝ) :=
    fun z => (fun i => (z i).1, fun i => (z i).2)
  have hsplit : Measurable split := by
    have hU : Measurable (fun z : Fin (Fintype.card E) → (ℝ × ℝ) =>
        fun i => (z i).1) := by
      apply measurable_pi_lambda
      intro i
      exact measurable_fst.comp (measurable_pi_apply i)
    have hV : Measurable (fun z : Fin (Fintype.card E) → (ℝ × ℝ) =>
        fun i => (z i).2) := by
      apply measurable_pi_lambda
      intro i
      exact measurable_snd.comp (measurable_pi_apply i)
    exact hU.prodMk hV
  have hbase : Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        codeMap mu (σ : Fin (Fintype.card E) → E) p.1) :=
    (GrandCoupling.measurable_codeMap mu σ).comp measurable_fst
  have hleft : Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.leftOrder base p.1 p.2)) :=
    (GrandCoupling.measurable_codeMap mu σ).comp
      (measurable_causalMixLabels_prod S.leftOrder base)
  have hright : Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.rightOrder base p.1 p.2)) :=
    (GrandCoupling.measurable_codeMap mu σ).comp
      (measurable_causalMixLabels_prod S.rightOrder base)
  change Measurable ((fun p => (codeMap mu (σ : Fin (Fintype.card E) → E) p.1,
    codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base p.1 p.2),
    codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base p.1 p.2))) ∘ split)
  exact (hbase.prodMk (hleft.prodMk hright)).comp hsplit

theorem pairedCausalOutputs_fibre (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    {z | pairedCausalOutputs mu S base z = (base, left, right)} =
      frozenTripleCodeAtom mu S base left right := by
  ext z
  simp only [pairedCausalOutputs, frozenTripleCodeAtom, frozenCodeAtom,
    Set.mem_setOf_eq, Set.mem_inter_iff, Prod.mk.injEq]
  rw [realizedEquiv_leftOrder_eq_rightOrder S base]
  tauto

noncomputable def frozenTripleRawPair (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) (i : Fin (Fintype.card E)) : Set (ℝ × ℝ) :=
  frozenRawPair mu S.leftOrder base left i ∩
    frozenRawPair mu S.rightOrder base right i

theorem frozenTripleCodeAtom_eq_rawPairBox (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    frozenTripleCodeAtom mu S base left right =
      Set.univ.pi (frozenTripleRawPair mu S base left right) := by
  unfold frozenTripleCodeAtom
  rw [frozenCodeAtom_eq_rawPairBox mu S.leftOrder base left]
  rw [frozenCodeAtom_eq_rawPairBox mu S.rightOrder base right]
  ext z
  simp only [frozenTripleRawPair, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    true_implies]
  constructor
  · rintro ⟨hl, hr⟩ i
    exact ⟨hl i, hr i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem pairedCube_frozenTripleCodeAtom (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    pairedCube (Fintype.card E) (frozenTripleCodeAtom mu S base left right) =
      ∏ i : Fin (Fintype.card E),
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1)))
            (frozenTripleRawPair mu S base left right i) := by
  rw [frozenTripleCodeAtom_eq_rawPairBox, pairedCube, Measure.pi_pi]


def fixedListOrder : (l : List E) → l.Nodup → CausalOrder l.toFinset
  | [], _ => .done
  | e :: l, h => by
      have he : e ∉ l := (List.nodup_cons.mp h).1
      have ht : l.Nodup := (List.nodup_cons.mp h).2
      have hem : e ∈ (e :: l).toFinset := by simp
      have herase : (e :: l).toFinset.erase e = l.toFinset := by
        ext z
        simp [he]
      have child : CausalOrder ((e :: l).toFinset.erase e) :=
        herase.symm ▸ fixedListOrder l ht
      exact CausalOrder.node e hem true child child


noncomputable def fixedOrder (R : Finset E) : CausalOrder R :=
  R.toList_toFinset ▸ fixedListOrder R.toList R.nodup_toList

def TripleOrder.beforeOfCausal : {R : Finset E} → CausalOrder R → TripleOrder R
  | _, .done => .done
  | _, .node e he _ closed opened =>
      .node e he .before (TripleOrder.beforeOfCausal closed)
        (TripleOrder.beforeOfCausal opened)



noncomputable def extendDecisionTreeTriple :
    Option ℕ → DecisionTree E → ConfigSpace E → (R : Finset E) → TripleOrder R
  | _, .leaf _, _, R => TripleOrder.beforeOfCausal (fixedOrder R)
  | phase, .node e opened closed, known, R =>
      if he : e ∈ R then
        match phase with
        | some 0 => .node e he .flip
            (extendDecisionTreeTriple none closed (Function.update known e false) (R.erase e))
            (extendDecisionTreeTriple none opened (Function.update known e true) (R.erase e))
        | some (t + 1) => .node e he .before
            (extendDecisionTreeTriple (some t) closed (Function.update known e false) (R.erase e))
            (extendDecisionTreeTriple (some t) opened (Function.update known e true) (R.erase e))
        | none => .node e he .after
            (extendDecisionTreeTriple none closed (Function.update known e false) (R.erase e))
            (extendDecisionTreeTriple none opened (Function.update known e true) (R.erase e))
      else if known e then extendDecisionTreeTriple phase opened known R
      else extendDecisionTreeTriple phase closed known R

lemma tripleModeAt_beforeOfCausal_ne_flip {R : Finset E}
    (S : CausalOrder R) (base : ConfigSpace E) (z : E) :
    tripleModeAt (TripleOrder.beforeOfCausal S) base z ≠ .flip := by
  induction S with
  | done => simp [TripleOrder.beforeOfCausal, tripleModeAt]
  | node e he independent closed opened ihc iho =>
      simp only [TripleOrder.beforeOfCausal, tripleModeAt]
      by_cases hze : z = e
      · simp [hze]
      · simp only [hze, if_false]
        split <;> assumption

lemma tripleModeAt_extendDecisionTreeTriple_none_ne_flip
    (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E) (z : E) :
    tripleModeAt (extendDecisionTreeTriple none T known R) base z ≠ .flip := by
  induction T generalizing known R with
  | leaf b =>
      exact tripleModeAt_beforeOfCausal_ne_flip (fixedOrder R) base z
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · simp only [he, dif_pos, tripleModeAt]
        by_cases hze : z = e
        · simp [hze]
        · simp only [hze, if_false]
          by_cases hb : base e
          · simp only [hb, if_true]
            exact iho (Function.update known e true) (R.erase e)
          · simp only [hb, Bool.false_eq_true, if_false]
            exact ihc (Function.update known e false) (R.erase e)
      · simp only [he, dif_neg]
        by_cases hb : known e
        · simp only [hb, if_true]
          exact iho known R
        · simp only [hb, Bool.false_eq_true, if_false]
          exact ihc known R

theorem tripleModeAt_extendDecisionTreeTriple_flip_unique
    (t : ℕ) (T : DecisionTree E) (known base : ConfigSpace E)
    (R : Finset E) (x y : E)
    (hx : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base x = .flip)
    (hy : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base y = .flip) :
    x = y := by
  induction T generalizing t known R with
  | leaf b =>
      exact False.elim
        (tripleModeAt_beforeOfCausal_ne_flip (fixedOrder R) base x hx)
  | node q opened closed iho ihc =>
      by_cases hqR : q ∈ R
      · rw [extendDecisionTreeTriple, dif_pos hqR] at hx hy
        cases t with
        | zero =>
            have eq_q (z : E)
                (hz : tripleModeAt
                  (.node q hqR .flip
                    (extendDecisionTreeTriple none closed
                      (Function.update known q false) (R.erase q))
                    (extendDecisionTreeTriple none opened
                      (Function.update known q true) (R.erase q))) base z = .flip) :
                z = q := by
              by_contra hn
              simp only [tripleModeAt, hn, if_false] at hz
              by_cases hb : base q
              · simp only [hb, if_true] at hz
                exact tripleModeAt_extendDecisionTreeTriple_none_ne_flip
                  opened (Function.update known q true) base (R.erase q) z hz
              · simp only [hb, Bool.false_eq_true, if_false] at hz
                exact tripleModeAt_extendDecisionTreeTriple_none_ne_flip
                  closed (Function.update known q false) base (R.erase q) z hz
            exact (eq_q x hx).trans (eq_q y hy).symm
        | succ t =>
            have hxn : x ≠ q := by
              intro h
              subst x
              simp [tripleModeAt] at hx
            have hyn : y ≠ q := by
              intro h
              subst y
              simp [tripleModeAt] at hy
            simp only [tripleModeAt, hxn, hyn, if_false] at hx hy
            by_cases hb : base q
            · simp only [hb, if_true] at hx hy
              exact iho t (Function.update known q true) (R.erase q) hx hy
            · simp only [hb, Bool.false_eq_true, if_false] at hx hy
              exact ihc t (Function.update known q false) (R.erase q) hx hy
      · rw [extendDecisionTreeTriple, dif_neg hqR] at hx hy
        by_cases hb : known q
        · simp only [hb, if_true] at hx hy
          exact iho t known R hx hy
        · simp only [hb, Bool.false_eq_true, if_false] at hx hy
          exact ihc t known R hx hy

theorem causal_abs_eq_four_terms { μ : ConfigSpace E → ℝ }
    (hpos : ∀ ω, 0 < μ ω) (hmono : IsMonotonicMeasure μ)
    {f : ConfigSpace E → ℝ} (hf : Monotone f)
    (t : ℕ) (T : DecisionTree E) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (e : E)
    (he : tripleModeAt
      (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip) :
    let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
    let σ := realizedEquiv S.leftOrder base
    let Yl := codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base U V)
    let Yr := codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base U V)
    |f Yr - f Yl| =
      f Yl * Lindeberg.coord e Yl + f Yr * Lindeberg.coord e Yr -
        f Yl * Lindeberg.coord e Yr - f Yr * Lindeberg.coord e Yl := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  let σ := realizedEquiv S.leftOrder base
  let k : Fin (Fintype.card E) := σ.symm e
  let L := causalMixLabels S.leftOrder base U V
  let R := causalMixLabels S.rightOrder base U V
  let Yl := codeMap μ (σ : Fin (Fintype.card E) → E) L
  let Yr := codeMap μ (σ : Fin (Fintype.card E) → E) R
  have hke : σ k = e := by simp [k]
  have hσ : realizedEquiv S.rightOrder base = σ := by
    exact (realizedEquiv_leftOrder_eq_rightOrder S base).symm
  have hoff : ∀ i : Fin (Fintype.card E), (i : ℕ) ≠ k → L i = R i := by
    intro i hi
    have hie : σ i ≠ e := by
      intro h
      have : i = k := σ.injective (by simpa [k] using h)
      exact hi (congrArg Fin.val this)
    apply causalMixLabels_left_eq_right_of_mode_ne_flip
    intro hm
    have := tripleModeAt_extendDecisionTreeTriple_flip_unique
      t T base base Finset.univ (σ i) e hm he
    exact hie this
  have hkL : L k = U k := by
    dsimp only [L]
    rw [causalMixLabels_leftOrder_apply]
    rw [hke, he]
  have hkR : R k = V k := by
    dsimp only [R]
    rw [causalMixLabels_rightOrder_apply]
    rw [hσ]
    rw [hke, he]
  have hdet : Lindeberg.coord e Yr = Lindeberg.coord e Yl → Yr = Yl := by
    intro hc
    have hbit : Yr e = Yl e := by
      unfold Lindeberg.coord at hc
      by_cases h1 : Yr e <;> by_cases h2 : Yl e <;> simp_all
    apply GrandCouplingAssembly.codeMap_det μ
      (σ : Fin (Fintype.card E) → E) σ.injective R L
      k k.2 (fun i hi => (hoff i hi).symm)
    simpa [hke] using hbit
  have hcmp : (f Yl ≤ f Yr ∧ Lindeberg.coord e Yl ≤ Lindeberg.coord e Yr) ∨
      (f Yr ≤ f Yl ∧ Lindeberg.coord e Yr ≤ Lindeberg.coord e Yl) := by
    rcases le_total (U k) (V k) with huv | hvu
    · left
      have hlr : L ≤ R := by
        intro i
        by_cases hi : (i : ℕ) = k
        · have hik : i = k := Fin.ext hi
          subst i
          rw [hkL, hkR]
          exact huv
        · rw [hoff i hi]
      have hy : Yl ≤ Yr := GrandCoupling.codeMap_mono_u hpos hmono _ hlr
      exact ⟨hf hy, Lindeberg.coord_mono e hy⟩
    · right
      have hrl : R ≤ L := by
        intro i
        by_cases hi : (i : ℕ) = k
        · have hik : i = k := Fin.ext hi
          subst i
          rw [hkL, hkR]
          exact hvu
        · rw [hoff i hi]
      have hy : Yr ≤ Yl := GrandCoupling.codeMap_mono_u hpos hmono _ hrl
      exact ⟨hf hy, Lindeberg.coord_mono e hy⟩
  exact GrandCouplingAssembly.tt_algebra (f Yr) (f Yl)
    (Lindeberg.coord e Yr) (Lindeberg.coord e Yl)
    (GrandCouplingAssembly.coord_eq01 e Yr)
    (GrandCouplingAssembly.coord_eq01 e Yl) hcmp (fun h => by rw [hdet h])




noncomputable def extendDecisionTree :
    DecisionTree E → ConfigSpace E → (R : Finset E) → CausalOrder R
  | .leaf _, _, R => fixedOrder R
  | .node e opened closed, known, R =>
      if he : e ∈ R then
        CausalOrder.node e he false
          (extendDecisionTree closed (Function.update known e false) (R.erase e))
          (extendDecisionTree opened (Function.update known e true) (R.erase e))
      else if known e then extendDecisionTree opened known R
      else extendDecisionTree closed known R


def allIndependent : {R : Finset E} → CausalOrder R → CausalOrder R
  | _, .done => .done
  | _, .node e he _ closed opened =>
      .node e he true (allIndependent closed) (allIndependent opened)


@[simp] lemma TripleOrder.leftOrder_beforeOfCausal {R : Finset E}
    (S : CausalOrder R) : (TripleOrder.beforeOfCausal S).leftOrder = allIndependent S := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [TripleOrder.beforeOfCausal, TripleOrder.leftOrder,
        TripleMode.leftIndependent, allIndependent]
      rw [ihc, iho]

@[simp] lemma TripleOrder.rightOrder_beforeOfCausal {R : Finset E}
    (S : CausalOrder R) : (TripleOrder.beforeOfCausal S).rightOrder = allIndependent S := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [TripleOrder.beforeOfCausal, TripleOrder.rightOrder,
        TripleMode.rightIndependent, allIndependent]
      rw [ihc, iho]




def sharedEdges : {R : Finset E} → CausalOrder R → ConfigSpace E → Finset E
  | _, .done, _ => ∅
  | _, .node e _ independent closed opened, base =>
      if base e then
        if independent then sharedEdges opened base else insert e (sharedEdges opened base)
      else
        if independent then sharedEdges closed base else insert e (sharedEdges closed base)

@[simp] lemma sharedEdges_allIndependent {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : sharedEdges (allIndependent S) base = ∅ := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [allIndependent, sharedEdges, if_true]
      split <;> assumption

lemma allIndependent_cast {R S : Finset E} (h : R = S) (C : CausalOrder R) :
    allIndependent (h ▸ C) = h ▸ allIndependent C := by
  subst S
  rfl

@[simp] lemma allIndependent_fixedListOrder (l : List E) (h : l.Nodup) :
    allIndependent (fixedListOrder l h) = fixedListOrder l h := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      rw [fixedListOrder, allIndependent]
      congr 1
      all_goals
        rw [allIndependent_cast]
        simpa using ih (List.nodup_cons.mp h).2

@[simp] lemma allIndependent_fixedOrder (R : Finset E) :
    allIndependent (fixedOrder R) = fixedOrder R := by
  unfold fixedOrder
  rw [allIndependent_cast, allIndependent_fixedListOrder]

lemma sharedEdges_cast {R S : Finset E} (h : R = S) (C : CausalOrder R)
    (base : ConfigSpace E) : sharedEdges (h ▸ C) base = sharedEdges C base := by
  subst S
  rfl

lemma sharedEdges_fixedListOrder (l : List E) (h : l.Nodup) (base : ConfigSpace E) :
    sharedEdges (fixedListOrder l h) base = ∅ := by
  induction l with
  | nil => simp [fixedListOrder, sharedEdges]
  | cons e l ih =>
      rw [fixedListOrder]
      simp only [sharedEdges, if_true]
      split
      · rw [sharedEdges_cast]
        exact ih _
      · rw [sharedEdges_cast]
        exact ih _

@[simp] lemma sharedEdges_fixedOrder (R : Finset E) (base : ConfigSpace E) :
    sharedEdges (fixedOrder R) base = ∅ := by
  let C := fixedListOrder R.toList R.nodup_toList
  let h : R.toList.toFinset = R := Finset.toList_toFinset R
  have hfixed : fixedOrder R = h ▸ C := by
    unfold fixedOrder
    rfl
  rw [hfixed, sharedEdges_cast h C base]
  exact sharedEdges_fixedListOrder R.toList R.nodup_toList base





theorem sharedEdges_extendDecisionTree (T : DecisionTree E) (known base : ConfigSpace E)
    (R : Finset E) (hknown : ∀ z, z ∉ R → known z = base z) :
    sharedEdges (extendDecisionTree T known R) base = T.queried base ∩ R := by
  induction T generalizing known R with
  | leaf b => simp [extendDecisionTree, DecisionTree.queried]
  | node e opened closed iho ihc =>
      rw [extendDecisionTree]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hb : base e
        · simp only [sharedEdges, hb, if_true, Bool.false_eq_true, if_false,
            DecisionTree.queried]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          rw [iho (Function.update known e true) (R.erase e) hk]
          ext z
          simp only [Finset.mem_insert, Finset.mem_inter, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hz, _, hzR⟩)
            · exact ⟨Or.inl rfl, he⟩
            · exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · exact Or.inl hz
            · by_cases hze : z = e
              · exact Or.inl hze
              · exact Or.inr ⟨hz, hze, hzR⟩
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          simp only [sharedEdges, hb, Bool.false_eq_true, if_false,
            DecisionTree.queried]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          rw [ihc (Function.update known e false) (R.erase e) hk]
          ext z
          simp only [Finset.mem_insert, Finset.mem_inter, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hz, _, hzR⟩)
            · exact ⟨Or.inl rfl, he⟩
            · exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · exact Or.inl hz
            · by_cases hze : z = e
              · exact Or.inl hze
              · exact Or.inr ⟨hz, hze, hzR⟩
      · rw [dif_neg he]
        have hkb : known e = base e := hknown e he
        by_cases hb : base e
        · simp only [hkb, hb, if_true, DecisionTree.queried]
          rw [iho known R hknown]
          ext z
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hz, hzR⟩
            exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · subst z
              exact (he hzR).elim
            · exact ⟨hz, hzR⟩
        · simp only [hkb, hb, Bool.false_eq_true, if_false, DecisionTree.queried]
          rw [ihc known R hknown]
          ext z
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hz, hzR⟩
            exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · subst z
              exact (he hzR).elim
            · exact ⟨hz, hzR⟩

theorem sharedEdges_extendDecisionTree_univ (T : DecisionTree E)
    (base : ConfigSpace E) :
    sharedEdges (extendDecisionTree T base (Finset.univ : Finset E)) base =
      T.queried base := by
  rw [sharedEdges_extendDecisionTree T base base Finset.univ (by simp)]
  simp




theorem mean_mem_sharedEdges_extendDecisionTree (μ : ConfigSpace E → ℝ)
    (T : DecisionTree E) (e : E) :
    Lindeberg.mean μ (fun base =>
      if e ∈ sharedEdges
        (extendDecisionTree T base (Finset.univ : Finset E)) base then (1 : ℝ) else 0) =
      LindebergTree.revealmentMu μ T e := by
  unfold LindebergTree.revealmentMu
  apply Finset.sum_congr rfl
  intro base _
  change (if e ∈ sharedEdges
      (extendDecisionTree T base (Finset.univ : Finset E)) base then (1 : ℝ) else 0) *
      μ base = (if e ∈ T.queried base then (1 : ℝ) else 0) * μ base
  rw [sharedEdges_extendDecisionTree_univ]





noncomputable def extendDecisionTreeAt :
    ℕ → DecisionTree E → ConfigSpace E → (R : Finset E) → CausalOrder R
  | _, .leaf _, _, R => fixedOrder R
  | t, .node e opened closed, known, R =>
      if he : e ∈ R then
        CausalOrder.node e he (decide (0 < t))
          (extendDecisionTreeAt (t - 1) closed
            (Function.update known e false) (R.erase e))
          (extendDecisionTreeAt (t - 1) opened
            (Function.update known e true) (R.erase e))
      else if known e then extendDecisionTreeAt t opened known R
      else extendDecisionTreeAt t closed known R

theorem extendDecisionTreeTriple_none_leftOrder (T : DecisionTree E)
    (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple none T known R).leftOrder =
      extendDecisionTreeAt 0 T known R := by
  induction T generalizing known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp [he, TripleOrder.leftOrder, TripleMode.leftIndependent, ihc, iho]
      · simp [he]
        split <;> simp_all

theorem extendDecisionTreeTriple_none_rightOrder (T : DecisionTree E)
    (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple none T known R).rightOrder =
      extendDecisionTreeAt 0 T known R := by
  induction T generalizing known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp [he, TripleOrder.rightOrder, TripleMode.rightIndependent, ihc, iho]
      · simp [he]
        split <;> simp_all

lemma card_insert_inter_sub_one (P R : Finset E) (q : E) (hq : q ∈ R) :
    (insert q P ∩ R).card - 1 = (P ∩ R.erase q).card := by
  have hset : insert q P ∩ R = insert q (P ∩ R.erase q) := by
    ext z
    by_cases hzq : z = q
    · subst z
      simp [hq]
    · simp [hzq]
  rw [hset, Finset.card_insert_of_notMem]
  · simp
  · simp





theorem tripleModeAt_extendDecisionTreeTriple_eq_flip_of_fresh
    (T : DecisionTree E) (base known : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) (t : ℕ) (e : E)
    (hq : PredictableTreeQuery.pathQuery T base t = some e)
    (hfresh : e ∉ LindebergTree.pathPrefix T base t) (heR : e ∈ R) :
    tripleModeAt
        (extendDecisionTreeTriple
          (some ((LindebergTree.pathPrefix T base t ∩ R).card)) T known R)
        base e = .flip := by
  induction T generalizing known R t with
  | leaf b => simp [PredictableTreeQuery.pathQuery] at hq
  | node q opened closed iho ihc =>
      cases t with
      | zero =>
          simp only [PredictableTreeQuery.pathQuery, Option.some.injEq] at hq
          subst e
          simp only [LindebergTree.pathPrefix_zero, Finset.empty_inter, Finset.card_empty]
          simp [extendDecisionTreeTriple, heR, tripleModeAt]
      | succ t =>
          let B := if base q then opened else closed
          have hqB : PredictableTreeQuery.pathQuery B base t = some e := by
            simpa [B, PredictableTreeQuery.pathQuery] using hq
          have hprefix : LindebergTree.pathPrefix (.node q opened closed) base (t + 1) =
              insert q (LindebergTree.pathPrefix B base t) := by
            simp [LindebergTree.pathPrefix_node_succ, B]
          have hefreshB : e ∉ LindebergTree.pathPrefix B base t := by
            intro he
            apply hfresh
            rw [hprefix]
            exact Finset.mem_insert_of_mem he
          have heq : e ≠ q := by
            intro he
            subst e
            apply hfresh
            rw [hprefix]
            exact Finset.mem_insert_self _ _
          by_cases hqR : q ∈ R
          · let P := LindebergTree.pathPrefix B base t
            let k := (P ∩ R.erase q).card
            have hphase : (insert q P ∩ R).card = k + 1 := by
              have hsub := card_insert_inter_sub_one P R q hqR
              have hpos : 0 < (insert q P ∩ R).card := by
                apply Finset.card_pos.mpr
                exact ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hqR⟩⟩
              dsimp only [k]
              omega
            have heErase : e ∈ R.erase q := Finset.mem_erase.mpr ⟨heq, heR⟩
            have hknown' (b : Bool) (hbq : b = base q) : ∀ z, z ∉ R.erase q →
                Function.update known q b z = base z := by
              intro z hz
              by_cases hzq : z = q
              · subst z
                simp [hbq]
              · rw [Function.update_of_ne hzq]
                apply hknown z
                intro hzR
                exact hz (Finset.mem_erase.mpr ⟨hzq, hzR⟩)
            rw [hprefix]
            change tripleModeAt
              (extendDecisionTreeTriple (some ((insert q P ∩ R).card))
                (.node q opened closed) known R) base e = .flip
            rw [hphase]
            simp only [extendDecisionTreeTriple, hqR, dif_pos, tripleModeAt, heq, if_false]
            by_cases hb : base q
            · simp only [hb, if_true]
              have hi := iho (Function.update known q true) (R.erase q)
                (hknown' true (by simp [hb])) t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heErase
              simpa [k, P, B, hb] using hi
            · simp only [hb, Bool.false_eq_true, if_false]
              have hi := ihc (Function.update known q false) (R.erase q)
                (hknown' false (by simp [hb])) t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heErase
              simpa [k, P, B, hb] using hi
          · have hphase :
                (insert q (LindebergTree.pathPrefix B base t) ∩ R).card =
                  (LindebergTree.pathPrefix B base t ∩ R).card := by
              congr 1
              ext z
              simp only [Finset.mem_inter, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hz, hzR⟩
                · exact False.elim (hqR hzR)
                · exact ⟨hz, hzR⟩
              · rintro ⟨hz, hzR⟩
                exact ⟨Or.inr hz, hzR⟩
            have hknownq : known q = base q := hknown q hqR
            rw [hprefix, hphase]
            rw [extendDecisionTreeTriple, dif_neg hqR]
            rw [hknownq]
            by_cases hb : base q
            · simp only [hb, if_true]
              simpa [B, hb] using iho known R hknown t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heR
            · simp only [hb, Bool.false_eq_true, if_false]
              simpa [B, hb] using ihc known R hknown t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heR

@[simp] theorem extendDecisionTreeTriple_leftOrder
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple (some t) T known R).leftOrder =
      extendDecisionTreeAt t T known R := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        cases t with
        | zero =>
            simp [TripleOrder.leftOrder, TripleMode.leftIndependent,
              extendDecisionTreeTriple_none_leftOrder]
        | succ t =>
            simp [TripleOrder.leftOrder, TripleMode.leftIndependent, ihc, iho]
      · by_cases hb : known e
        · simp [he, hb, iho]
        · simp [he, hb, ihc]

@[simp] theorem extendDecisionTreeTriple_rightOrder
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple (some t) T known R).rightOrder =
      extendDecisionTreeAt (t + 1) T known R := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        cases t with
        | zero =>
            simp [TripleOrder.rightOrder, TripleMode.rightIndependent,
              extendDecisionTreeTriple_none_rightOrder]
        | succ t =>
            simp [TripleOrder.rightOrder, TripleMode.rightIndependent, ihc, iho]
      · by_cases hb : known e
        · simp [he, hb, iho]
        · simp [he, hb, ihc]




theorem extendDecisionTreeTriple_known_congr (phase : Option ℕ)
    (T : DecisionTree E) (known known' : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = known' z) :
    extendDecisionTreeTriple phase T known R =
      extendDecisionTreeTriple phase T known' R := by
  induction T generalizing phase known known' R with
  | leaf b => rfl
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        have hup (b : Bool) : ∀ z, z ∉ R.erase e →
            Function.update known e b z = Function.update known' e b z := by
          intro z hz
          by_cases hze : z = e
          · subst z
            simp
          · rw [Function.update_of_ne hze, Function.update_of_ne hze]
            apply hknown z
            intro hzR
            exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
        cases phase with
        | none =>
            simp only
            rw [ihc none _ _ _ (hup false), iho none _ _ _ (hup true)]
        | some t =>
            cases t with
            | zero =>
                simp only
                rw [ihc none _ _ _ (hup false), iho none _ _ _ (hup true)]
            | succ t =>
                simp only
                rw [ihc (some t) _ _ _ (hup false),
                  iho (some t) _ _ _ (hup true)]
      · simp only [he, dif_neg]
        have heq : known e = known' e := hknown e he
        by_cases hb : known e
        · have hb' : known' e := by simpa [heq] using hb
          simp only [hb, hb', if_true]
          exact iho phase known known' R hknown
        · have hb' : ¬ known' e := by simpa [heq] using hb
          simp only [hb, hb', Bool.false_eq_true, if_false]
          exact ihc phase known known' R hknown

@[simp] theorem extendDecisionTreeTriple_univ_seed_congr (phase : Option ℕ)
    (T : DecisionTree E) (known known' : ConfigSpace E) :
    extendDecisionTreeTriple phase T known (Finset.univ : Finset E) =
      extendDecisionTreeTriple phase T known' Finset.univ :=
  extendDecisionTreeTriple_known_congr phase T known known' Finset.univ (by simp)

@[simp] theorem extendDecisionTreeAt_univ_seed_congr (t : ℕ)
    (T : DecisionTree E) (known known' : ConfigSpace E) :
    extendDecisionTreeAt t T known (Finset.univ : Finset E) =
      extendDecisionTreeAt t T known' Finset.univ := by
  rw [← extendDecisionTreeTriple_leftOrder t T known Finset.univ,
    ← extendDecisionTreeTriple_leftOrder t T known' Finset.univ]
  rw [extendDecisionTreeTriple_univ_seed_congr]

@[simp] theorem extendDecisionTreeAt_zero (T : DecisionTree E)
    (known : ConfigSpace E) (R : Finset E) :
    extendDecisionTreeAt 0 T known R = extendDecisionTree T known R := by
  induction T generalizing known R with
  | leaf b => rfl
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeAt, extendDecisionTree]
      by_cases he : e ∈ R
      · simp [he, ihc, iho]
      · simp [he]
        split <;> simp_all

theorem extendDecisionTreeAt_eq_allIndependent_of_card_le (t : ℕ)
    (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hcard : R.card ≤ t) :
    extendDecisionTreeAt t T known R =
      allIndependent (extendDecisionTree T known R) := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeAt, extendDecisionTree]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeAt, extendDecisionTree]
      by_cases he : e ∈ R
      · simp only [he, dif_pos, allIndependent]
        have ht : 0 < t := by
          have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        have hchild : (R.erase e).card ≤ t - 1 := by
          rw [Finset.card_erase_of_mem he]
          omega
        simp only [ht, decide_true]
        rw [ihc (t - 1) (Function.update known e false) (R.erase e) hchild]
        rw [iho (t - 1) (Function.update known e true) (R.erase e) hchild]
      · simp only [he, dif_neg]
        by_cases hb : known e
        · simp only [hb, if_true]
          exact iho t known R hcard
        · simp only [hb, Bool.false_eq_true, if_false]
          exact ihc t known R hcard

@[simp] theorem extendDecisionTreeAt_card_univ_eq_allIndependent
    (T : DecisionTree E) (known : ConfigSpace E) :
    extendDecisionTreeAt (Fintype.card E) T known (Finset.univ : Finset E) =
      allIndependent (extendDecisionTree T known Finset.univ) := by
  apply extendDecisionTreeAt_eq_allIndependent_of_card_le
  simp



theorem sharedEdges_extendDecisionTreeAt_eq_empty_of_card_le (t : ℕ)
    (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) (hcard : R.card ≤ t) :
    sharedEdges (extendDecisionTreeAt t T known R) base = ∅ := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeAt]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        have ht : 0 < t := by
          have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        have hchild : (R.erase e).card ≤ t - 1 := by
          rw [Finset.card_erase_of_mem he]
          omega
        by_cases hb : base e
        · simp only [sharedEdges, hb, if_true, ht, decide_true]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          exact iho (t - 1) (Function.update known e true) (R.erase e) hk hchild
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          simp only [sharedEdges, hb, Bool.false_eq_true, if_false, ht, decide_true]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          exact ihc (t - 1) (Function.update known e false) (R.erase e) hk hchild
      · rw [dif_neg he]
        have hkb : known e = base e := hknown e he
        by_cases hb : base e
        · simp only [hkb, hb, if_true]
          exact iho t known R hknown hcard
        · simp only [hkb, hb, Bool.false_eq_true, if_false]
          exact ihc t known R hknown hcard

@[simp] theorem sharedEdges_extendDecisionTreeAt_card_univ (T : DecisionTree E)
    (known base : ConfigSpace E) :
    sharedEdges (extendDecisionTreeAt (Fintype.card E) T known
      (Finset.univ : Finset E)) base = ∅ := by
  apply sharedEdges_extendDecisionTreeAt_eq_empty_of_card_le
  · simp
  · simp



theorem sharedEdges_extendDecisionTreeAt_succ_subset (t : ℕ)
    (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) :
    sharedEdges (extendDecisionTreeAt (t + 1) T known R) base ⊆
      sharedEdges (extendDecisionTreeAt t T known R) base := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        by_cases hb : base e
        · have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          cases t with
          | zero => simp [sharedEdges, hb]
          | succ t =>
              simpa [sharedEdges, hb, Nat.add_assoc] using
                iho t (Function.update known e true) (R.erase e) hk
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          cases t with
          | zero => simp [sharedEdges, hb]
          | succ t =>
              simpa [sharedEdges, hb, Nat.add_assoc] using
                ihc t (Function.update known e false) (R.erase e) hk
      · simp only [he, dif_neg]
        have hkb : known e = base e := hknown e he
        by_cases hb : base e
        · simp only [hkb, hb, if_true]
          exact iho t known R hknown
        · simp only [hkb, hb, Bool.false_eq_true, if_false]
          exact ihc t known R hknown

noncomputable def sharedAtIndicator (T : DecisionTree E) (base : ConfigSpace E)
    (t : ℕ) (e : E) : ℝ :=
  if e ∈ sharedEdges
      (extendDecisionTreeAt t T base (Finset.univ : Finset E)) base then 1 else 0



noncomputable def sharedStepIndicator (T : DecisionTree E) (base : ConfigSpace E)
    (t : ℕ) (e : E) : ℝ :=
  sharedAtIndicator T base t e - sharedAtIndicator T base (t + 1) e

lemma sharedStepIndicator_nonneg (T : DecisionTree E)
    (base : ConfigSpace E) (t : ℕ) (e : E) :
    0 ≤ sharedStepIndicator T base t e := by
  have hsub := sharedEdges_extendDecisionTreeAt_succ_subset
    t T base base (Finset.univ : Finset E) (by simp)
  unfold sharedStepIndicator sharedAtIndicator
  by_cases hnext : e ∈ sharedEdges
      (extendDecisionTreeAt (t + 1) T base (Finset.univ : Finset E)) base
  · have hnow := hsub hnext
    simp [hnext, hnow]
  · simp [hnext]
    split <;> norm_num



theorem sum_sharedStepIndicator_eq_queried (T : DecisionTree E)
    (base : ConfigSpace E) (e : E) :
    ∑ t ∈ Finset.range (Fintype.card E), sharedStepIndicator T base t e =
      if e ∈ T.queried base then 1 else 0 := by
  unfold sharedStepIndicator
  rw [Finset.sum_range_sub' (fun t => sharedAtIndicator T base t e)
    (Fintype.card E)]
  unfold sharedAtIndicator
  rw [extendDecisionTreeAt_zero, sharedEdges_extendDecisionTree_univ]
  rw [sharedEdges_extendDecisionTreeAt_card_univ]
  simp


theorem sum_mean_sharedStepIndicator_eq_revealmentMu
    (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (e : E) :
    ∑ t ∈ Finset.range (Fintype.card E),
        Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) =
      LindebergTree.revealmentMu μ T e := by
  unfold Lindeberg.mean LindebergTree.revealmentMu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro base _
  rw [← Finset.sum_mul]
  rw [sum_sharedStepIndicator_eq_queried]

lemma sharedEdges_subset {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : sharedEdges S base ⊆ R := by
  induction S with
  | done => simp [sharedEdges]
  | @node R q hq active closed opened ihc iho =>
      by_cases hb : base q <;> by_cases ha : active
      · simpa [sharedEdges, hb, ha] using iho.trans (Finset.erase_subset q R)
      · simp [sharedEdges, hb, ha, Finset.insert_subset_iff, hq,
          iho.trans (Finset.erase_subset q R)]
      · simpa [sharedEdges, hb, ha] using ihc.trans (Finset.erase_subset q R)
      · simp [sharedEdges, hb, ha, Finset.insert_subset_iff, hq,
          ihc.trans (Finset.erase_subset q R)]

lemma mem_sharedEdges_iff_independentAt_false {R : Finset E}
    (S : CausalOrder R) (base : ConfigSpace E) (e : E) (he : e ∈ R) :
    e ∈ sharedEdges S base ↔ independentAt S base e = false := by
  induction S with
  | done => simp at he
  | @node R q hq active closed opened ihc iho =>
      by_cases heq : e = q
      · subst e
        have hno : q ∉ sharedEdges opened base := by
          intro h
          exact (Finset.mem_erase.mp (sharedEdges_subset opened base h)).1 rfl
        have hnc : q ∉ sharedEdges closed base := by
          intro h
          exact (Finset.mem_erase.mp (sharedEdges_subset closed base h)).1 rfl
        by_cases hb : base q <;> by_cases ha : active <;>
          simp [sharedEdges, independentAt, hb, ha, hno, hnc]
      · have heErase : e ∈ R.erase q := Finset.mem_erase.mpr ⟨heq, he⟩
        by_cases hb : base q
        · by_cases ha : active <;>
            simp [sharedEdges, independentAt, heq, hb, ha, iho heErase]
        · by_cases ha : active <;>
            simp [sharedEdges, independentAt, heq, hb, ha, ihc heErase]

noncomputable def tripleFlipIndicator
    (S : TripleOrder (Finset.univ : Finset E))
    (base : ConfigSpace E) (e : E) : ℝ :=
  if tripleModeAt S base e = .flip then 1 else 0



theorem sharedStepIndicator_eq_tripleFlipIndicator
    (T : DecisionTree E) (base : ConfigSpace E) (t : ℕ) (e : E) :
    sharedStepIndicator T base t e =
      tripleFlipIndicator
        (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e := by
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  unfold sharedStepIndicator sharedAtIndicator tripleFlipIndicator
  rw [← extendDecisionTreeTriple_leftOrder t T base Finset.univ]
  rw [← extendDecisionTreeTriple_rightOrder t T base Finset.univ]
  change (if e ∈ sharedEdges S.leftOrder base then 1 else 0) -
      (if e ∈ sharedEdges S.rightOrder base then 1 else 0) =
    if tripleModeAt S base e = TripleMode.flip then 1 else 0
  simp only [mem_sharedEdges_iff_independentAt_false S.leftOrder base e (by simp),
    mem_sharedEdges_iff_independentAt_false S.rightOrder base e (by simp)]
  rw [independentAt_leftOrder, independentAt_rightOrder]
  cases tripleModeAt S base e <;>
    simp [TripleMode.leftIndependent, TripleMode.rightIndependent]



def overlapWeight (a q : ℝ) (base target : Bool) : ℝ :=
  match base, target with
  | false, false => min a q
  | true, false => max (q - a) 0
  | false, true => max (a - q) 0
  | true, true => 1 - max a q

def bitWeight (q : ℝ) (b : Bool) : ℝ := if b then 1 - q else q



lemma rawInterval_toReal_eq_bitWeight (mu : ConfigSpace E → ℝ)
    (hpos : ∀ omega, 0 < mu omega) {n : ℕ} (sigma : Fin n → E)
    (x : ConfigSpace E) (i : Fin n) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)
      (GrandCoupling.rawInterval mu sigma x i)).toReal =
        bitWeight (thr mu sigma x i) (x (sigma i)) := by
  rw [GrandCoupling.vcube_rawInterval mu hpos sigma x i]
  by_cases hb : x (sigma i)
  · simp only [hb, if_true, bitWeight]
    have hsum := condProbBit_true_add_false mu
      (prefixSet sigma (i : ℕ)) x (sigma i)
      (condNorm_pos hpos _ _).ne'
    change condProbBit mu (prefixSet sigma (i : ℕ)) x (sigma i) true =
      1 - condProbBit mu (prefixSet sigma (i : ℕ)) x (sigma i) false
    linarith
  · simp only [hb, Bool.false_eq_true, if_false, bitWeight]
    rfl


def independentWeight (a q : ℝ) (base target : Bool) : ℝ :=
  bitWeight a base * bitWeight q target

lemma bitWeight_false_add_true (q : ℝ) : bitWeight q false + bitWeight q true = 1 := by
  simp [bitWeight]

lemma independentWeight_sum_base (a q : ℝ) (target : Bool) :
    independentWeight a q false target + independentWeight a q true target =
      bitWeight q target := by
  unfold independentWeight
  rw [← add_mul, bitWeight_false_add_true, one_mul]


def splitWeight (independent : Bool) (a q : ℝ) (base target : Bool) : ℝ :=
  if independent then independentWeight a q base target else overlapWeight a q base target

def thresholdInterval (q : ℝ) (b : Bool) : Set ℝ :=
  if b then Set.Ico q 1 else Set.Ico 0 q

lemma volume_thresholdInterval (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    (volume (thresholdInterval q b)).toReal = bitWeight q b := by
  cases b <;> simp [thresholdInterval, bitWeight, Real.volume_Ico, hq0, hq1]



lemma volume_inter_threshold_false_add_true (A : Set ℝ) (hA : MeasurableSet A)
    (hAcube : A ⊆ Set.Ico (0 : ℝ) 1) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (volume (A ∩ thresholdInterval q false)).toReal +
      (volume (A ∩ thresholdInterval q true)).toReal = (volume A).toReal := by
  have hd : Disjoint (A ∩ thresholdInterval q false) (A ∩ thresholdInterval q true) := by
    rw [Set.disjoint_left]
    intro x hx0 hx1
    exact (not_lt_of_ge hx1.2.1) hx0.2.2
  have hu : (A ∩ thresholdInterval q false) ∪ (A ∩ thresholdInterval q true) = A := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      by_cases h : x < q
      · left
        exact ⟨hx, by simpa [thresholdInterval] using ⟨hAcube hx |>.1, h⟩⟩
      · right
        exact ⟨hx, by simpa [thresholdInterval] using ⟨le_of_not_gt h, hAcube hx |>.2⟩⟩
  have hIt : MeasurableSet (thresholdInterval q true) := by
    simp [thresholdInterval]
  have hm := measure_union (μ := volume) hd (hA.inter hIt)
  rw [hu] at hm
  have hAfin : volume A < ⊤ := by
    calc
      volume A ≤ volume (Set.Ico (0 : ℝ) 1) := measure_mono hAcube
      _ < ⊤ := by simp [Real.volume_Ico]
  have h0 : volume (A ∩ thresholdInterval q false) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hAfin)
  have h1 : volume (A ∩ thresholdInterval q true) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hAfin)
  rw [← ENNReal.toReal_add h0 h1, ← hm]



lemma volume_thresholdInterval_inter (a q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (base target : Bool) :
    (volume (thresholdInterval a base ∩ thresholdInterval q target)).toReal =
      overlapWeight a q base target := by
  cases base <;> cases target <;>
    simp only [thresholdInterval, Bool.false_eq_true, if_false, if_true,
      Set.Ico_inter_Ico, Real.volume_Ico]
  · rw [max_self, min_def, overlapWeight]
    by_cases h : a ≤ q
    · rw [if_pos h, sub_zero, ENNReal.toReal_ofReal ha0, min_eq_left h]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [if_neg h, sub_zero, ENNReal.toReal_ofReal hq0, min_eq_right hqa]
  · rw [max_eq_right hq0, min_eq_left ha1, overlapWeight]
    by_cases h : a ≤ q
    · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr h), ENNReal.toReal_zero,
        max_eq_right (sub_nonpos.mpr h)]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hqa), max_eq_left (sub_nonneg.mpr hqa)]
  · rw [max_eq_left ha0, min_eq_right hq1, overlapWeight]
    by_cases h : a ≤ q
    · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h)]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr hqa), ENNReal.toReal_zero,
        max_eq_right (sub_nonpos.mpr hqa)]
  · rw [min_self, overlapWeight]
    by_cases h : a ≤ q
    · rw [max_eq_right h, ENNReal.toReal_ofReal (sub_nonneg.mpr hq1)]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [max_eq_left hqa, ENNReal.toReal_ofReal (sub_nonneg.mpr ha1)]



lemma rawInterval_inter_toReal_eq_overlapWeight (mu : ConfigSpace E → ℝ)
    (hpos : ∀ omega, 0 < mu omega) {n : ℕ} (sigma : Fin n → E)
    (base target : ConfigSpace E) (i : Fin n) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)
      (GrandCoupling.rawInterval mu sigma base i ∩
        GrandCoupling.rawInterval mu sigma target i)).toReal =
      overlapWeight (thr mu sigma base i) (thr mu sigma target i)
        (base (sigma i)) (target (sigma i)) := by
  have ha := thr_mem_Icc mu hpos sigma base i
  have hq := thr_mem_Icc mu hpos sigma target i
  rw [Measure.restrict_apply' measurableSet_Icc]
  have hae :
      (fun z : ℝ => z ∈
        (GrandCoupling.rawInterval mu sigma base i ∩
          GrandCoupling.rawInterval mu sigma target i) ∩ Set.Icc (0 : ℝ) 1)
        =ᵐ[volume]
      (fun z : ℝ => z ∈
        thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
          thresholdInterval (thr mu sigma target i) (target (sigma i))) := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with z hz
    have hz1 : z ≠ 1 := by simpa using hz
    cases hb : base (sigma i) <;> cases ht : target (sigma i) <;>
      simp only [GrandCoupling.rawInterval, hb, ht, Bool.false_eq_true, if_false, if_true,
        thresholdInterval, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_Icc,
        Set.mem_Ico]
    all_goals
      apply propext
      constructor
      · rintro ⟨⟨hB, hT⟩, h0, h1⟩
        have hzlt : z < 1 := lt_of_le_of_ne h1 hz1
        constructor <;> constructor <;> linarith
      · rintro ⟨⟨hB0, hB1⟩, hT0, hT1⟩
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hm := measure_congr hae
  change volume
    ((GrandCoupling.rawInterval mu sigma base i ∩
      GrandCoupling.rawInterval mu sigma target i) ∩ Set.Icc (0 : ℝ) 1) =
    volume (thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
      thresholdInterval (thr mu sigma target i) (target (sigma i))) at hm
  rw [hm]
  exact volume_thresholdInterval_inter _ _ ha.1 ha.2 hq.1 hq.2 _ _

lemma rawInterval_tripleInter_toReal_eq_tripleOverlapWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    {n : ℕ} (sigma : Fin n → E) (base left right : ConfigSpace E) (i : Fin n) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)
      (GrandCoupling.rawInterval mu sigma base i ∩
        GrandCoupling.rawInterval mu sigma left i ∩
        GrandCoupling.rawInterval mu sigma right i)).toReal =
      (volume (thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
        thresholdInterval (thr mu sigma left i) (left (sigma i)) ∩
        thresholdInterval (thr mu sigma right i) (right (sigma i)))).toReal := by
  rw [Measure.restrict_apply' measurableSet_Icc]
  have hae :
      (fun z : ℝ => z ∈
        (GrandCoupling.rawInterval mu sigma base i ∩
          GrandCoupling.rawInterval mu sigma left i ∩
          GrandCoupling.rawInterval mu sigma right i) ∩ Set.Icc (0 : ℝ) 1)
        =ᵐ[volume]
      (fun z : ℝ => z ∈
        thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
          thresholdInterval (thr mu sigma left i) (left (sigma i)) ∩
          thresholdInterval (thr mu sigma right i) (right (sigma i))) := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with z hz
    have hz1 : z ≠ 1 := by simpa using hz
    have ha := thr_mem_Icc mu hpos sigma base i
    have hq := thr_mem_Icc mu hpos sigma left i
    have hr := thr_mem_Icc mu hpos sigma right i
    cases hb : base (sigma i) <;> cases hl : left (sigma i) <;>
      cases hh : right (sigma i) <;>
      simp only [GrandCoupling.rawInterval, hb, hl, hh, Bool.false_eq_true,
        if_false, if_true, thresholdInterval, Set.mem_inter_iff, Set.mem_Iio,
        Set.mem_Ici, Set.mem_Icc, Set.mem_Ico]
    all_goals
      apply propext
      constructor
      · rintro ⟨⟨⟨hB, hL⟩, hR⟩, h0, h1⟩
        have hzlt : z < 1 := lt_of_le_of_ne h1 hz1
        constructor
        · constructor <;> constructor <;> linarith
        · constructor <;> linarith
      · rintro ⟨⟨⟨hB0, hB1⟩, hL0, hL1⟩, hR0, hR1⟩
        exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩,
          by linarith, by linarith⟩
  have hm := measure_congr hae
  change volume
    ((GrandCoupling.rawInterval mu sigma base i ∩
      GrandCoupling.rawInterval mu sigma left i ∩
      GrandCoupling.rawInterval mu sigma right i) ∩ Set.Icc (0 : ℝ) 1) =
    volume (thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
      thresholdInterval (thr mu sigma left i) (left (sigma i)) ∩
      thresholdInterval (thr mu sigma right i) (right (sigma i))) at hm
  rw [hm]



lemma frozenRawPair_toReal_eq_splitWeight (mu : ConfigSpace E → ℝ)
    (hpos : ∀ omega, 0 < mu omega)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) (i : Fin (Fintype.card E)) :
    (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (frozenRawPair mu S base target i)).toReal =
      splitWeight (independentAt S base (realizedEquiv S base i))
        (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) base i)
        (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) target i)
        (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
  let sigma := realizedEquiv S base
  have hsigma : realizedEquiv S base = sigma := rfl
  unfold frozenRawPair
  simp only [hsigma]
  by_cases hi : independentAt S base (sigma i)
  · rw [if_pos hi, Measure.prod_prod, ENNReal.toReal_mul,
      rawInterval_toReal_eq_bitWeight mu hpos,
      rawInterval_toReal_eq_bitWeight mu hpos]
    simp [splitWeight, independentWeight, hi]
  · rw [if_neg hi, Measure.prod_prod, ENNReal.toReal_mul,
      rawInterval_inter_toReal_eq_overlapWeight mu hpos]
    simp [splitWeight, hi]



theorem pairedCube_frozenCodeAtom_toReal_eq_prod_splitWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    (pairedCube (Fintype.card E) (frozenCodeAtom mu S base target)).toReal =
      ∏ i : Fin (Fintype.card E),
        splitWeight (independentAt S base (realizedEquiv S base i))
          (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) base i)
          (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) target i)
          (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
  rw [pairedCube_frozenCodeAtom, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact frozenRawPair_toReal_eq_splitWeight mu hpos S base target i

lemma overlapWeight_sum_base (a q : ℝ) (target : Bool) :
    overlapWeight a q false target + overlapWeight a q true target =
      if target then 1 - q else q := by
  cases target with
  | false =>
      simp only [overlapWeight, Bool.false_eq_true, if_false]
      by_cases h : a ≤ q
      · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
        ring
      · have hqa : q ≤ a := le_of_not_ge h
        rw [min_eq_right hqa, max_eq_right (sub_nonpos.mpr hqa)]
        ring
  | true =>
      simp only [overlapWeight, if_true]
      by_cases h : a ≤ q
      · rw [max_eq_right (sub_nonpos.mpr h), max_eq_right h]
        ring
      · have hqa : q ≤ a := le_of_not_ge h
        rw [max_eq_left (sub_nonneg.mpr hqa), max_eq_left hqa]
        ring

lemma overlapWeight_same_threshold_ne (q : ℝ) {b c : Bool} (hbc : b ≠ c) :
    overlapWeight q q b c = 0 := by
  cases b <;> cases c <;> simp_all [overlapWeight]

lemma splitWeight_sum_base (independent : Bool) (a q : ℝ) (target : Bool) :
    splitWeight independent a q false target + splitWeight independent a q true target =
      bitWeight q target := by
  cases independent with
  | false =>
      simp only [splitWeight, Bool.false_eq_true, if_false]
      rw [overlapWeight_sum_base]
      cases target <;> simp [bitWeight]
  | true =>
      simp only [splitWeight, if_true]
      exact independentWeight_sum_base a q target

lemma overlapWeight_comm (a q : ℝ) (b c : Bool) :
    overlapWeight a q b c = overlapWeight q a c b := by
  cases b <;> cases c <;> simp [overlapWeight, min_comm, max_comm]

noncomputable def tripleOverlapWeight (a q r : ℝ) (b y z : Bool) : ℝ :=
  (volume (thresholdInterval a b ∩ thresholdInterval q y ∩ thresholdInterval r z)).toReal

noncomputable def tripleWeight (mode : TripleMode) (a q r : ℝ) (b y z : Bool) : ℝ :=
  match mode with
  | .before => bitWeight a b * overlapWeight q r y z
  | .flip => overlapWeight a q b y * bitWeight r z
  | .after => tripleOverlapWeight a q r b y z

lemma frozenTripleRawPair_toReal_eq_tripleWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) (i : Fin (Fintype.card E)) :
    (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (frozenTripleRawPair mu S base left right i)).toReal =
      tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
        (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
        (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
        (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
        (base (realizedEquiv S.leftOrder base i))
        (left (realizedEquiv S.leftOrder base i))
        (right (realizedEquiv S.leftOrder base i)) := by
  let sigma := realizedEquiv S.leftOrder base
  have hsigma : realizedEquiv S.leftOrder base = sigma := rfl
  unfold frozenTripleRawPair frozenRawPair
  rw [← realizedEquiv_leftOrder_eq_rightOrder S base]
  simp only [hsigma, independentAt_leftOrder, independentAt_rightOrder]
  cases hm : tripleModeAt S base (sigma i) with
  | before =>
      simp only [hm, TripleMode.leftIndependent, TripleMode.rightIndependent,
        if_true, Set.prod_inter_prod, Set.inter_self, tripleWeight]
      rw [Measure.prod_prod, ENNReal.toReal_mul,
        rawInterval_toReal_eq_bitWeight mu hpos,
        rawInterval_inter_toReal_eq_overlapWeight mu hpos]
  | flip =>
      simp only [hm, TripleMode.leftIndependent, TripleMode.rightIndependent,
        Bool.false_eq_true, if_false, if_true, Set.prod_inter_prod,
        Set.inter_univ, Set.inter_assoc, tripleWeight]
      have hset : GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
          (GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i) =
          GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i := by
        ext x
        simp only [Set.mem_inter_iff]
        tauto
      rw [hset, Set.univ_inter]
      rw [Measure.prod_prod, ENNReal.toReal_mul,
        rawInterval_inter_toReal_eq_overlapWeight mu hpos,
        rawInterval_toReal_eq_bitWeight mu hpos]
  | after =>
      simp only [hm, TripleMode.leftIndependent, TripleMode.rightIndependent,
        Bool.false_eq_true, if_false, Set.prod_inter_prod, Set.inter_univ,
        tripleWeight, tripleOverlapWeight]
      have hset :
          (GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
              GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i) ∩
            (GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
              GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) right i) =
          GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) right i := by
        ext x
        simp only [Set.mem_inter_iff]
        tauto
      rw [hset]
      rw [Measure.prod_prod, ENNReal.toReal_mul,
        rawInterval_tripleInter_toReal_eq_tripleOverlapWeight mu hpos]
      simp

theorem pairedCube_frozenTripleCodeAtom_toReal_eq_prod_tripleWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (pairedCube (Fintype.card E) (frozenTripleCodeAtom mu S base left right)).toReal =
      ∏ i : Fin (Fintype.card E),
        tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
          (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
          (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
          (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
          (base (realizedEquiv S.leftOrder base i))
          (left (realizedEquiv S.leftOrder base i))
          (right (realizedEquiv S.leftOrder base i)) := by
  rw [pairedCube_frozenTripleCodeAtom, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact frozenTripleRawPair_toReal_eq_tripleWeight mu hpos S base left right i

lemma thresholdInterval_subset_Ico (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    thresholdInterval q b ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  cases b
  · simp only [thresholdInterval, Bool.false_eq_true, if_false, Set.mem_Ico] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hq1⟩
  · simp only [thresholdInterval, if_true, Set.mem_Ico] at hx ⊢
    exact ⟨le_trans hq0 hx.1, hx.2⟩

lemma tripleOverlapWeight_sum_third (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b y : Bool) :
    tripleOverlapWeight a q r b y false + tripleOverlapWeight a q r b y true =
      overlapWeight a q b y := by
  unfold tripleOverlapWeight
  have hA : MeasurableSet (thresholdInterval a b ∩ thresholdInterval q y) := by
    cases b <;> cases y <;> simp [thresholdInterval]
  have hsub : thresholdInterval a b ∩ thresholdInterval q y ⊆ Set.Ico (0 : ℝ) 1 :=
    fun _ hx => thresholdInterval_subset_Ico a ha0 ha1 b hx.1
  rw [volume_inter_threshold_false_add_true _ hA hsub r hr0 hr1]
  exact volume_thresholdInterval_inter a q ha0 ha1 hq0 hq1 b y

lemma tripleOverlapWeight_sum_second (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b z : Bool) :
    tripleOverlapWeight a q r b false z + tripleOverlapWeight a q r b true z =
      overlapWeight a r b z := by
  unfold tripleOverlapWeight
  have hcomm : ∀ y : Bool,
      thresholdInterval a b ∩ thresholdInterval q y ∩ thresholdInterval r z =
        (thresholdInterval a b ∩ thresholdInterval r z) ∩ thresholdInterval q y := by
    intro y
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  rw [hcomm false, hcomm true]
  have hA : MeasurableSet (thresholdInterval a b ∩ thresholdInterval r z) := by
    cases b <;> cases z <;> simp [thresholdInterval]
  have hsub : thresholdInterval a b ∩ thresholdInterval r z ⊆ Set.Ico (0 : ℝ) 1 :=
    fun _ hx => thresholdInterval_subset_Ico a ha0 ha1 b hx.1
  rw [volume_inter_threshold_false_add_true _ hA hsub q hq0 hq1]
  exact volume_thresholdInterval_inter a r ha0 ha1 hr0 hr1 b z

lemma tripleWeight_sum_third (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b y : Bool) :
    tripleWeight mode a q r b y false + tripleWeight mode a q r b y true =
      splitWeight mode.leftIndependent a q b y := by
  cases mode with
  | before =>
      simp only [tripleWeight, TripleMode.leftIndependent, splitWeight, if_true]
      rw [← mul_add, overlapWeight_comm q r y false, overlapWeight_comm q r y true,
        overlapWeight_sum_base, bitWeight]
      rfl
  | flip =>
      simp only [tripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      rw [← mul_add, bitWeight_false_add_true, mul_one]
  | after =>
      simp only [tripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_third a q r ha0 ha1 hq0 hq1 hr0 hr1 b y

lemma tripleWeight_sum_second (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b z : Bool) :
    tripleWeight mode a q r b false z + tripleWeight mode a q r b true z =
      splitWeight mode.rightIndependent a r b z := by
  cases mode with
  | before =>
      simp only [tripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [← mul_add, overlapWeight_sum_base]
      unfold independentWeight
      rfl
  | flip =>
      simp only [tripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [← add_mul, overlapWeight_comm a q b false, overlapWeight_comm a q b true,
        overlapWeight_sum_base]
      rfl
  | after =>
      simp only [tripleWeight, TripleMode.rightIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_second a q r ha0 ha1 hq0 hq1 hr0 hr1 b z





noncomputable def crossTripleWeight (mode : TripleMode) (a q r : ℝ)
    (b y z : Bool) : ℝ :=
  match mode with
  | .before => bitWeight a b * bitWeight q y * bitWeight r z
  | .flip => overlapWeight a q b y * bitWeight r z
  | .after => tripleOverlapWeight a q r b y z




noncomputable def frozenCrossCodeAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    Set (Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ)) :=
  {z | let σ := realizedEquiv S.leftOrder base
       let U := fun i => (z i).1.1
       let V := fun i => (z i).1.2
       let V' := fun i => (z i).2
       codeMap μ (σ : Fin (Fintype.card E) → E) U = base ∧
         codeMap μ (σ : Fin (Fintype.card E) → E)
           (causalMixLabels S.leftOrder base U V) = left ∧
         codeMap μ (σ : Fin (Fintype.card E) → E)
           (causalMixLabels S.rightOrder base U V') = right}



noncomputable def tripleCausalOutputs (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    (Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ)) →
      ConfigSpace E × (ConfigSpace E × ConfigSpace E) := fun z =>
  let σ := realizedEquiv S.leftOrder base
  let U := fun i => (z i).1.1
  let V := fun i => (z i).1.2
  let V' := fun i => (z i).2
  (codeMap μ (σ : Fin (Fintype.card E) → E) U,
    codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base U V),
    codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base U V'))

lemma measurable_tripleCausalOutputs (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Measurable (tripleCausalOutputs μ S base) := by
  let σ := realizedEquiv S.leftOrder base
  have hU : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
      fun i => (z i).1.1) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))
  have hV : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
      fun i => (z i).1.2) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))
  have hV' : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
      fun i => (z i).2) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_snd.comp (measurable_pi_apply i)
  have hmix (C : CausalOrder (Finset.univ : Finset E))
      (hW : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        fun i => if independentAt C base (realizedEquiv C base i)
          then (z i).1.2 else (z i).1.1)) :
      Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C base (fun i => (z i).1.1) (fun i => (z i).1.2))) := by
    exact (GrandCoupling.measurable_codeMap μ σ).comp (by simpa [causalMixLabels] using hW)
  have hmix' (C : CausalOrder (Finset.univ : Finset E))
      (hW : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        fun i => if independentAt C base (realizedEquiv C base i)
          then (z i).2 else (z i).1.1)) :
      Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C base (fun i => (z i).1.1) (fun i => (z i).2))) := by
    exact (GrandCoupling.measurable_codeMap μ σ).comp (by simpa [causalMixLabels] using hW)
  have hleftLabels : Measurable
      (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) => fun i =>
        if independentAt S.leftOrder base (realizedEquiv S.leftOrder base i)
          then (z i).1.2 else (z i).1.1) := by
    apply measurable_pi_lambda
    intro i
    split
    · exact measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))
    · exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))
  have hrightLabels : Measurable
      (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) => fun i =>
        if independentAt S.rightOrder base (realizedEquiv S.rightOrder base i)
          then (z i).2 else (z i).1.1) := by
    apply measurable_pi_lambda
    intro i
    split
    · exact measurable_snd.comp (measurable_pi_apply i)
    · exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))
  exact ((GrandCoupling.measurable_codeMap μ σ).comp hU).prodMk
    ((hmix S.leftOrder hleftLabels).prodMk (hmix' S.rightOrder hrightLabels))

theorem tripleCausalOutputs_fibre (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    {z | tripleCausalOutputs μ S base z = (base, left, right)} =
      frozenCrossCodeAtom μ S base left right := by
  ext z
  simp only [tripleCausalOutputs, frozenCrossCodeAtom, Set.mem_setOf_eq, Prod.mk.injEq]

noncomputable def crossRawTriple (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) (i : Fin (Fintype.card E)) :
    Set ((ℝ × ℝ) × ℝ) :=
  let σ := realizedEquiv S.leftOrder base
  let A := GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) base i
  let B := GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) left i
  let C := GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) right i
  match tripleModeAt S base (σ i) with
  | .before => (A ×ˢ B) ×ˢ C
  | .flip => ((A ∩ B) ×ˢ Set.univ) ×ˢ C
  | .after => ((A ∩ B ∩ C) ×ˢ Set.univ) ×ˢ Set.univ

theorem frozenCrossCodeAtom_eq_rawTripleBox (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    frozenCrossCodeAtom μ S base left right =
      Set.univ.pi (crossRawTriple μ S base left right) := by
  let σ := realizedEquiv S.leftOrder base
  have hσ : realizedEquiv S.leftOrder base = σ := rfl
  have hσr : realizedEquiv S.rightOrder base = σ := by
    rw [← hσ, realizedEquiv_leftOrder_eq_rightOrder]
  ext z
  have hbase :
      codeMap μ (σ : Fin (Fintype.card E) → E) (fun i => (z i).1.1) = base ↔
        ∀ i, (z i).1.1 ∈ GrandCoupling.rawInterval μ
          (σ : Fin (Fintype.card E) → E) base i := by
    have h := Set.ext_iff.mp
      (GrandCoupling.codeMap_fibre_eq_rawbox μ σ base) (fun i => (z i).1.1)
    simpa [Set.mem_pi] using h
  have hleft :
      codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.leftOrder base (fun i => (z i).1.1)
            (fun i => (z i).1.2)) = left ↔
        ∀ i, causalMixLabels S.leftOrder base (fun i => (z i).1.1)
            (fun i => (z i).1.2) i ∈
          GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) left i := by
    have h := Set.ext_iff.mp
      (GrandCoupling.codeMap_fibre_eq_rawbox μ σ left)
      (causalMixLabels S.leftOrder base (fun i => (z i).1.1) (fun i => (z i).1.2))
    simpa [Set.mem_pi] using h
  have hright :
      codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.rightOrder base (fun i => (z i).1.1)
            (fun i => (z i).2)) = right ↔
        ∀ i, causalMixLabels S.rightOrder base (fun i => (z i).1.1)
            (fun i => (z i).2) i ∈
          GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) right i := by
    have h := Set.ext_iff.mp
      (GrandCoupling.codeMap_fibre_eq_rawbox μ σ right)
      (causalMixLabels S.rightOrder base (fun i => (z i).1.1) (fun i => (z i).2))
    simpa [Set.mem_pi] using h
  simp only [frozenCrossCodeAtom, Set.mem_setOf_eq]
  change
    (codeMap μ (σ : Fin (Fintype.card E) → E) (fun i => (z i).1.1) = base ∧
      codeMap μ (σ : Fin (Fintype.card E) → E)
        (causalMixLabels S.leftOrder base (fun i => (z i).1.1)
          (fun i => (z i).1.2)) = left ∧
      codeMap μ (σ : Fin (Fintype.card E) → E)
        (causalMixLabels S.rightOrder base (fun i => (z i).1.1)
          (fun i => (z i).2)) = right) ↔
      z ∈ Set.univ.pi (crossRawTriple μ S base left right)
  rw [hbase, hleft, hright]
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hb, hl, hr⟩ i
    specialize hb i
    specialize hl i
    specialize hr i
    cases hm : tripleModeAt S base (σ i) with
    | before =>
        have hl' : (z i).1.2 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) left i := by
          simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
            TripleMode.leftIndependent] using hl
        have hr' : (z i).2 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) right i := by
          simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
            TripleMode.rightIndependent, hσr] using hr
        simpa [crossRawTriple, hσ, hm] using ⟨⟨hb, hl'⟩, hr'⟩
    | flip =>
        have hl' : (z i).1.1 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) left i := by
          simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
            TripleMode.leftIndependent] using hl
        have hr' : (z i).2 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) right i := by
          simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
            TripleMode.rightIndependent, hσr] using hr
        simpa [crossRawTriple, hσ, hm] using ⟨⟨hb, hl'⟩, hr'⟩
    | after =>
        have hl' : (z i).1.1 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) left i := by
          simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
            TripleMode.leftIndependent] using hl
        have hr' : (z i).1.1 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) right i := by
          simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
            TripleMode.rightIndependent, hσr] using hr
        simpa [crossRawTriple, hσ, hm] using
          ⟨⟨hb, hl'⟩, hr'⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> intro i
    · specialize h i
      cases hm : tripleModeAt S base (σ i) <;>
        simp only [crossRawTriple, hσ, hm, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h <;> exact h.1.1
    · specialize h i
      cases hm : tripleModeAt S base (σ i) <;>
        simp only [crossRawTriple, hσ, hm, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h <;>
        simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
          TripleMode.leftIndependent] using h.1.2
    · specialize h i
      cases hm : tripleModeAt S base (σ i) <;>
        simp only [crossRawTriple, hσ, hm, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h <;>
        simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
          TripleMode.rightIndependent, hσr] using h.2


noncomputable def tripleCube (n : ℕ) : Measure (Fin n → ((ℝ × ℝ) × ℝ)) :=
  Measure.pi fun _ =>
    let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
    (ν.prod ν).prod ν

noncomputable def tripleCubeEquiv (n : ℕ) :
    (Fin n → ((ℝ × ℝ) × ℝ)) ≃ᵐ
      (((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (ℝ × ℝ) ℝ (Fin n)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (MeasurableEquiv.refl (Fin n → ℝ)))



theorem tripleCube_measurePreserving (n : ℕ) :
    MeasurePreserving
      (fun z : Fin n → ((ℝ × ℝ) × ℝ) =>
        ((fun i => (z i).1.1, fun i => (z i).1.2), fun i => (z i).2))
      (tripleCube n)
      (((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) := by
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
  have houter := measurePreserving_arrowProdEquivProdArrow (ℝ × ℝ) ℝ (Fin n)
    (fun _ => ν.prod ν) (fun _ => ν)
  have hinner := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => ν) (fun _ => ν)
  have hid : MeasurePreserving (id : (Fin n → ℝ) → (Fin n → ℝ))
      (GrandCoupling.Vcube n) (GrandCoupling.Vcube n) :=
    MeasurePreserving.id (GrandCoupling.Vcube n)
  have hprod := hinner.prod hid
  simpa [tripleCube, GrandCoupling.Vcube, ν, Function.comp_def] using hprod.comp houter

theorem tripleCubeEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (tripleCubeEquiv n) (tripleCube n)
      (((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) := by
  simpa [tripleCubeEquiv, MeasurableEquiv.trans_apply, Function.comp_def] using
    tripleCube_measurePreserving n

theorem tripleCube_integral_equiv (n : ℕ)
    (g : (((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)) → ℝ) :
    (∫ z, g (tripleCubeEquiv n z) ∂(tripleCube n)) =
      ∫ p, g p ∂(((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) := by
  exact (tripleCubeEquiv_measurePreserving n).integral_comp
    (tripleCubeEquiv n).measurableEmbedding g

theorem tripleCube_frozenCrossCodeAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right) =
      ∏ i : Fin (Fintype.card E),
        let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
        (ν.prod ν).prod ν (crossRawTriple μ S base left right i) := by
  rw [frozenCrossCodeAtom_eq_rawTripleBox, tripleCube, Measure.pi_pi]

noncomputable def tripleLabelCube (n : ℕ) : Measure (Fin n → ((ℝ × ℝ) × ℝ)) :=
  Measure.pi fun _ =>
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1))).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))

noncomputable def frozenCrossRawAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) : Set (Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ)) :=
  Set.univ.pi (crossRawTriple μ S base left right)

theorem tripleLabelCube_frozenCrossRawAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    tripleLabelCube (Fintype.card E) (frozenCrossRawAtom μ S base left right) =
      ∏ i : Fin (Fintype.card E),
        (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))).prod
            (volume.restrict (Set.Icc (0 : ℝ) 1)))
          (crossRawTriple μ S base left right i) := by
  rw [tripleLabelCube, frozenCrossRawAtom, Measure.pi_pi]

lemma crossRawTriple_toReal_eq_crossTripleWeight
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) (i : Fin (Fintype.card E)) :
    let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
    ((ν.prod ν).prod ν (crossRawTriple μ S base left right i)).toReal =
      crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
        (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
        (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
        (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
        (base (realizedEquiv S.leftOrder base i))
        (left (realizedEquiv S.leftOrder base i))
        (right (realizedEquiv S.leftOrder base i)) := by
  dsimp only
  let σ := realizedEquiv S.leftOrder base
  have hsigma : realizedEquiv S.leftOrder base = σ := rfl
  unfold crossRawTriple
  simp only [hsigma]
  cases hm : tripleModeAt S base (σ i) with
  | before =>
      simp only [hm, crossTripleWeight]
      rw [Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul,
        ENNReal.toReal_mul, rawInterval_toReal_eq_bitWeight μ hpos,
        rawInterval_toReal_eq_bitWeight μ hpos,
        rawInterval_toReal_eq_bitWeight μ hpos]
  | flip =>
      simp only [hm, crossTripleWeight]
      rw [Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul,
        ENNReal.toReal_mul, rawInterval_inter_toReal_eq_overlapWeight μ hpos,
        rawInterval_toReal_eq_bitWeight μ hpos]
      simp
  | after =>
      simp only [hm, crossTripleWeight, tripleOverlapWeight]
      rw [Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul,
        ENNReal.toReal_mul,
        rawInterval_tripleInter_toReal_eq_tripleOverlapWeight μ hpos]
      simp

lemma overlapWeight_sum_target (a q : ℝ) (base : Bool) :
    overlapWeight a q base false + overlapWeight a q base true = bitWeight a base := by
  rw [overlapWeight_comm a q base false, overlapWeight_comm a q base true,
    overlapWeight_sum_base]
  cases base <;> simp [bitWeight]

lemma crossTripleWeight_sum_third (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b y : Bool) :
    crossTripleWeight mode a q r b y false +
        crossTripleWeight mode a q r b y true =
      splitWeight mode.leftIndependent a q b y := by
  cases mode with
  | before =>
      simp only [crossTripleWeight, TripleMode.leftIndependent, splitWeight, if_true]
      rw [← mul_add, bitWeight_false_add_true, mul_one]
      rfl
  | flip =>
      simp only [crossTripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      rw [← mul_add, bitWeight_false_add_true, mul_one]
  | after =>
      simp only [crossTripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_third a q r ha0 ha1 hq0 hq1 hr0 hr1 b y

lemma crossTripleWeight_sum_second (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b z : Bool) :
    crossTripleWeight mode a q r b false z +
        crossTripleWeight mode a q r b true z =
      splitWeight mode.rightIndependent a r b z := by
  cases mode with
  | before =>
      simp only [crossTripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [show bitWeight a b * bitWeight q false * bitWeight r z +
          bitWeight a b * bitWeight q true * bitWeight r z =
        bitWeight a b * (bitWeight q false + bitWeight q true) * bitWeight r z by ring]
      rw [bitWeight_false_add_true, mul_one]
      rfl
  | flip =>
      simp only [crossTripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [← add_mul, overlapWeight_sum_target]
      rfl
  | after =>
      simp only [crossTripleWeight, TripleMode.rightIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_second a q r ha0 ha1 hq0 hq1 hr0 hr1 b z


noncomputable def tripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e he mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      tripleWeight mode a q r false (left e) (right e) *
          tripleProb μ (insert e F) (Function.update base e false) left right closed
        + tripleWeight mode a q r true (left e) (right e) *
          tripleProb μ (insert e F) (Function.update base e true) left right opened

noncomputable def tripleJointProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e he mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      if base e then
        tripleWeight mode a q r true (left e) (right e) *
          tripleJointProb μ (insert e F) base left right opened
      else
        tripleWeight mode a q r false (left e) (right e) *
          tripleJointProb μ (insert e F) base left right closed

def tripleRealizedSchedule : {R : Finset E} → TripleOrder R →
    ConfigSpace E → List (E × TripleMode)
  | _, .done, _ => []
  | _, .node e _ mode closed opened, base =>
      (e, mode) :: if base e then tripleRealizedSchedule opened base
        else tripleRealizedSchedule closed base

@[simp] lemma tripleRealizedSchedule_map_fst {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) :
    (tripleRealizedSchedule S base).map Prod.fst = realizedList S.leftOrder base := by
  induction S with
  | done => rfl
  | node e he mode closed opened ihc iho =>
      simp only [tripleRealizedSchedule, TripleOrder.leftOrder, realizedList, List.map_cons]
      split <;> simp_all

lemma tripleRealizedSchedule_mode {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) (p : E × TripleMode) (hp : p ∈ tripleRealizedSchedule S base) :
    p.2 = tripleModeAt S base p.1 := by
  induction S with
  | done => simp [tripleRealizedSchedule] at hp
  | @node R e he mode closed opened ihc iho =>
      by_cases hb : base e
      · simp only [tripleRealizedSchedule, hb, if_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [tripleModeAt]
        · have hz : p.1 ∈ realizedList opened.leftOrder base := by
            rw [← tripleRealizedSchedule_map_fst opened base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [tripleModeAt, hne, if_false, hb, if_true]
          exact iho hp
      · simp only [tripleRealizedSchedule, hb, Bool.false_eq_true, if_false,
          List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [tripleModeAt]
        · have hz : p.1 ∈ realizedList closed.leftOrder base := by
            rw [← tripleRealizedSchedule_map_fst closed base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [tripleModeAt, hne, if_false, hb, Bool.false_eq_true]
          exact ihc hp

lemma idxOf_fst_tripleRealizedSchedule
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (p : E × TripleMode) (hp : p ∈ tripleRealizedSchedule S base) :
    (realizedList S.leftOrder base).idxOf p.1 = (tripleRealizedSchedule S base).idxOf p := by
  let l := tripleRealizedSchedule S base
  have hip : l.idxOf p < l.length := List.idxOf_lt_length_iff.mpr hp
  have hget : l.get ⟨l.idxOf p, hip⟩ = p := List.idxOf_get hip
  have hmap : (l.map Prod.fst).Nodup := by
    rw [show l.map Prod.fst = realizedList S.leftOrder base from
      tripleRealizedSchedule_map_fst S base]
    exact realizedList_nodup S.leftOrder base
  have hidx := List.get_idxOf hmap
    (⟨l.idxOf p, by simpa using hip⟩ : Fin (l.map Prod.fst).length)
  simp only [List.get_eq_getElem, List.getElem_map] at hidx
  rw [show l[l.idxOf p] = p from by simpa [List.get_eq_getElem] using hget] at hidx
  rw [show l.map Prod.fst = realizedList S.leftOrder base from
    tripleRealizedSchedule_map_fst S base] at hidx
  exact hidx

noncomputable def tripleScheduleProduct (μ : ConfigSpace E → ℝ) :
    Finset E → ConfigSpace E → ConfigSpace E → ConfigSpace E →
      List (E × TripleMode) → ℝ
  | _, _, _, _, [] => 1
  | F, base, left, right, (e, mode) :: tail =>
      tripleWeight mode (condProbClosed μ F base e)
          (condProbClosed μ F left e) (condProbClosed μ F right e)
          (base e) (left e) (right e) *
        tripleScheduleProduct μ (insert e F) base left right tail

noncomputable def staticTripleScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E)
    (schedule : List (E × TripleMode)) : ℝ :=
  (schedule.map fun p =>
    let before := F ∪ ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
    tripleWeight p.2 (condProbClosed μ before base p.1)
      (condProbClosed μ before left p.1) (condProbClosed μ before right p.1)
      (base p.1) (left p.1) (right p.1)).prod

theorem tripleScheduleProduct_eq_static (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E)
    (schedule : List (E × TripleMode)) (hnd : (schedule.map Prod.fst).Nodup) :
    tripleScheduleProduct μ F base left right schedule =
      staticTripleScheduleProduct μ F base left right schedule := by
  induction schedule generalizing F with
  | nil => rfl
  | cons p tail ih =>
      have hp : p.1 ∉ tail.map Prod.fst := (List.nodup_cons.mp hnd).1
      have htail : (tail.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      rw [tripleScheduleProduct, staticTripleScheduleProduct, List.map_cons, List.prod_cons]
      simp only [List.idxOf_cons_self, List.take_zero, List.map_nil, List.toFinset_nil,
        Finset.union_empty]
      rw [ih (insert p.1 F) htail]
      unfold staticTripleScheduleProduct
      apply congrArg (fun z =>
        tripleWeight p.2 (condProbClosed μ F base p.1)
          (condProbClosed μ F left p.1) (condProbClosed μ F right p.1)
          (base p.1) (left p.1) (right p.1) * z)
      apply congrArg List.prod
      apply List.map_congr_left
      intro q hq
      have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hp (List.mem_map_of_mem hq)
      rw [List.idxOf_cons_ne tail hpq]
      simp only [List.take_succ_cons, List.map_cons, List.toFinset_cons,
        Finset.union_insert, Finset.insert_union]

theorem tripleJointProb_eq_tripleScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) :
    tripleJointProb μ F base left right S =
      tripleScheduleProduct μ F base left right (tripleRealizedSchedule S base) := by
  induction S generalizing F base with
  | done => rfl
  | @node R e he mode closed opened ihc iho =>
      rw [tripleJointProb, tripleRealizedSchedule, tripleScheduleProduct]
      by_cases hb : base e
      · simp only [hb, if_true]
        exact congrArg
          (fun z => tripleWeight mode (condProbClosed μ F base e)
            (condProbClosed μ F left e) (condProbClosed μ F right e)
            true (left e) (right e) * z)
          (iho (insert e F) base)
      · simp only [hb, Bool.false_eq_true, if_false]
        exact congrArg
          (fun z => tripleWeight mode (condProbClosed μ F base e)
            (condProbClosed μ F left e) (condProbClosed μ F right e)
            false (left e) (right e) * z)
          (ihc (insert e F) base)

theorem staticTripleScheduleProduct_eq_prod_realized
    (μ : ConfigSpace E → ℝ) (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    staticTripleScheduleProduct μ ∅ base left right (tripleRealizedSchedule S base) =
      ∏ i : Fin (Fintype.card E),
        tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
          (base (realizedEquiv S.leftOrder base i))
          (left (realizedEquiv S.leftOrder base i))
          (right (realizedEquiv S.leftOrder base i)) := by
  let schedule := tripleRealizedSchedule S base
  let sigma := realizedEquiv S.leftOrder base
  let g : E → ℝ := fun e =>
    tripleWeight (tripleModeAt S base e)
      (thr μ (sigma : Fin (Fintype.card E) → E) base (sigma.symm e))
      (thr μ (sigma : Fin (Fintype.card E) → E) left (sigma.symm e))
      (thr μ (sigma : Fin (Fintype.card E) → E) right (sigma.symm e))
      (base e) (left e) (right e)
  have hfac : (schedule.map fun p =>
      let before := ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
      tripleWeight p.2 (condProbClosed μ before base p.1)
        (condProbClosed μ before left p.1) (condProbClosed μ before right p.1)
        (base p.1) (left p.1) (right p.1)).prod =
      (schedule.map fun p => g p.1).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    simp only
    rw [tripleRealizedSchedule_mode S base p hp]
    rw [← idxOf_fst_tripleRealizedSchedule S base p hp]
    rw [List.map_take]
    rw [show schedule.map Prod.fst = realizedList S.leftOrder base from
      tripleRealizedSchedule_map_fst S base]
    rw [← thr_realizedEquiv μ S.leftOrder base base p.1]
    rw [← thr_realizedEquiv μ S.leftOrder base left p.1]
    rw [← thr_realizedEquiv μ S.leftOrder base right p.1]
  unfold staticTripleScheduleProduct
  simp only [Finset.empty_union]
  rw [show tripleRealizedSchedule S base = schedule from rfl, hfac]
  rw [show (schedule.map fun p => g p.1) = (realizedList S.leftOrder base).map g from by
    change (tripleRealizedSchedule S base).map (g ∘ Prod.fst) =
      (realizedList S.leftOrder base).map g
    rw [← List.map_map, tripleRealizedSchedule_map_fst]]
  rw [← List.prod_toFinset g (realizedList_nodup S.leftOrder base)]
  rw [realizedList_toFinset]
  rw [← sigma.prod_comp g]
  apply Finset.prod_congr rfl
  intro i _
  simp [g, sigma]


noncomputable def crossTripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e _ mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      crossTripleWeight mode a q r false (left e) (right e) *
          crossTripleProb μ (insert e F) (Function.update base e false) left right closed
        + crossTripleWeight mode a q r true (left e) (right e) *
          crossTripleProb μ (insert e F) (Function.update base e true) left right opened

noncomputable def crossTripleJointProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e _ mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      if base e then
        crossTripleWeight mode a q r true (left e) (right e) *
          crossTripleJointProb μ (insert e F) base left right opened
      else
        crossTripleWeight mode a q r false (left e) (right e) *
          crossTripleJointProb μ (insert e F) base left right closed




noncomputable def flipTripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) :
    {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 0
  | _, .node e he mode closed opened =>
      if z = e then
        if mode = .flip then
          tripleProb μ F base left right (.node e he mode closed opened)
        else 0
      else
        let a := condProbClosed μ F base e
        let q := condProbClosed μ F left e
        let r := condProbClosed μ F right e
        tripleWeight mode a q r false (left e) (right e) *
            flipTripleProb μ (insert e F) (Function.update base e false)
              left right z closed
          + tripleWeight mode a q r true (left e) (right e) *
            flipTripleProb μ (insert e F) (Function.update base e true)
              left right z opened


noncomputable def flipCrossTripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) :
    {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 0
  | _, .node e he mode closed opened =>
      if z = e then
        if mode = .flip then
          crossTripleProb μ F base left right (.node e he mode closed opened)
        else 0
      else
        let a := condProbClosed μ F base e
        let q := condProbClosed μ F left e
        let r := condProbClosed μ F right e
        crossTripleWeight mode a q r false (left e) (right e) *
            flipCrossTripleProb μ (insert e F) (Function.update base e false)
              left right z closed
          + crossTripleWeight mode a q r true (left e) (right e) *
            flipCrossTripleProb μ (insert e F) (Function.update base e true)
              left right z opened



noncomputable def flipBaseProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base : ConfigSpace E) (z : E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 0
  | _, .node e _ mode closed opened =>
      if z = e then
        if mode = .flip then 1 else 0
      else
        let a := condProbClosed μ F base e
        bitWeight a false *
            flipBaseProb μ (insert e F) (Function.update base e false) z closed
          + bitWeight a true *
            flipBaseProb μ (insert e F) (Function.update base e true) z opened

@[simp] lemma flipTripleProb_beforeOfCausal
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : CausalOrder R) :
    flipTripleProb μ F base left right z (TripleOrder.beforeOfCausal S) = 0 := by
  induction S generalizing F base with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      by_cases hze : z = e
      · subst z
        simp [flipTripleProb, TripleOrder.beforeOfCausal]
      · simp [flipTripleProb, TripleOrder.beforeOfCausal, hze, ihc, iho]

@[simp] lemma flipCrossTripleProb_beforeOfCausal
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : CausalOrder R) :
    flipCrossTripleProb μ F base left right z (TripleOrder.beforeOfCausal S) = 0 := by
  induction S generalizing F base with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      by_cases hze : z = e
      · subst z
        simp [flipCrossTripleProb, TripleOrder.beforeOfCausal]
      · simp [flipCrossTripleProb, TripleOrder.beforeOfCausal, hze, ihc, iho]

@[simp] lemma flipBaseProb_beforeOfCausal
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base : ConfigSpace E) (z : E) {R : Finset E} (S : CausalOrder R) :
    flipBaseProb μ F base z (TripleOrder.beforeOfCausal S) = 0 := by
  induction S generalizing F base with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      by_cases hze : z = e
      · subst z
        simp [flipBaseProb, TripleOrder.beforeOfCausal]
      · simp [flipBaseProb, TripleOrder.beforeOfCausal, hze, ihc, iho]

@[simp] theorem flipTripleProb_extendDecisionTreeTriple_none
    (μ : ConfigSpace E → ℝ) (F : Finset E) (T : DecisionTree E)
    (known base left right : ConfigSpace E) (R : Finset E) (z : E) :
    flipTripleProb μ F base left right z
      (extendDecisionTreeTriple none T known R) = 0 := by
  induction T generalizing F known base R with
  | leaf b => simp [extendDecisionTreeTriple]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hze : z = e
        · subst z
          simp [flipTripleProb]
        · simp [flipTripleProb, hze, ihc, iho]
      · rw [dif_neg he]
        by_cases hb : known e
        · simp [hb, iho]
        · simp [hb, ihc]

@[simp] theorem flipCrossTripleProb_extendDecisionTreeTriple_none
    (μ : ConfigSpace E → ℝ) (F : Finset E) (T : DecisionTree E)
    (known base left right : ConfigSpace E) (R : Finset E) (z : E) :
    flipCrossTripleProb μ F base left right z
      (extendDecisionTreeTriple none T known R) = 0 := by
  induction T generalizing F known base R with
  | leaf b => simp [extendDecisionTreeTriple]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hze : z = e
        · subst z
          simp [flipCrossTripleProb]
        · simp [flipCrossTripleProb, hze, ihc, iho]
      · rw [dif_neg he]
        by_cases hb : known e
        · simp [hb, iho]
        · simp [hb, ihc]

@[simp] theorem flipBaseProb_extendDecisionTreeTriple_none
    (μ : ConfigSpace E → ℝ) (F : Finset E) (T : DecisionTree E)
    (known base : ConfigSpace E) (R : Finset E) (z : E) :
    flipBaseProb μ F base z (extendDecisionTreeTriple none T known R) = 0 := by
  induction T generalizing F known base R with
  | leaf b => simp [extendDecisionTreeTriple]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hze : z = e
        · subst z
          simp [flipBaseProb]
        · simp [flipBaseProb, hze, ihc, iho]
      · rw [dif_neg he]
        by_cases hb : known e
        · simp [hb, iho]
        · simp [hb, ihc]

noncomputable def crossScheduleProduct (μ : ConfigSpace E → ℝ) :
    Finset E → ConfigSpace E → ConfigSpace E → ConfigSpace E →
      List (E × TripleMode) → ℝ
  | _, _, _, _, [] => 1
  | F, base, left, right, (e, mode) :: tail =>
      crossTripleWeight mode (condProbClosed μ F base e)
          (condProbClosed μ F left e) (condProbClosed μ F right e)
          (base e) (left e) (right e) *
        crossScheduleProduct μ (insert e F) base left right tail

noncomputable def staticCrossScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E)
    (schedule : List (E × TripleMode)) : ℝ :=
  (schedule.map fun p =>
    let before := F ∪ ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
    crossTripleWeight p.2 (condProbClosed μ before base p.1)
      (condProbClosed μ before left p.1) (condProbClosed μ before right p.1)
      (base p.1) (left p.1) (right p.1)).prod

theorem crossScheduleProduct_eq_static (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E)
    (schedule : List (E × TripleMode)) (hnd : (schedule.map Prod.fst).Nodup) :
    crossScheduleProduct μ F base left right schedule =
      staticCrossScheduleProduct μ F base left right schedule := by
  induction schedule generalizing F with
  | nil => rfl
  | cons p tail ih =>
      have hp : p.1 ∉ tail.map Prod.fst := (List.nodup_cons.mp hnd).1
      have htail : (tail.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      rw [crossScheduleProduct, staticCrossScheduleProduct, List.map_cons, List.prod_cons]
      simp only [List.idxOf_cons_self, List.take_zero, List.map_nil, List.toFinset_nil,
        Finset.union_empty]
      rw [ih (insert p.1 F) htail]
      unfold staticCrossScheduleProduct
      apply congrArg (fun z =>
        crossTripleWeight p.2 (condProbClosed μ F base p.1)
          (condProbClosed μ F left p.1) (condProbClosed μ F right p.1)
          (base p.1) (left p.1) (right p.1) * z)
      apply congrArg List.prod
      apply List.map_congr_left
      intro q hq
      have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hp (List.mem_map_of_mem hq)
      rw [List.idxOf_cons_ne tail hpq]
      simp only [List.take_succ_cons, List.map_cons, List.toFinset_cons,
        Finset.union_insert, Finset.insert_union]

theorem crossTripleJointProb_eq_crossScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) :
    crossTripleJointProb μ F base left right S =
      crossScheduleProduct μ F base left right (tripleRealizedSchedule S base) := by
  induction S generalizing F base with
  | done => rfl
  | @node R e he mode closed opened ihc iho =>
      rw [crossTripleJointProb, tripleRealizedSchedule, crossScheduleProduct]
      by_cases hb : base e
      · simp only [hb, if_true]
        exact congrArg
          (fun z => crossTripleWeight mode (condProbClosed μ F base e)
            (condProbClosed μ F left e) (condProbClosed μ F right e)
            true (left e) (right e) * z)
          (iho (insert e F) base)
      · simp only [hb, Bool.false_eq_true, if_false]
        exact congrArg
          (fun z => crossTripleWeight mode (condProbClosed μ F base e)
            (condProbClosed μ F left e) (condProbClosed μ F right e)
            false (left e) (right e) * z)
          (ihc (insert e F) base)

theorem staticCrossScheduleProduct_eq_prod_realized
    (μ : ConfigSpace E → ℝ) (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    staticCrossScheduleProduct μ ∅ base left right (tripleRealizedSchedule S base) =
      ∏ i : Fin (Fintype.card E),
        crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
          (base (realizedEquiv S.leftOrder base i))
          (left (realizedEquiv S.leftOrder base i))
          (right (realizedEquiv S.leftOrder base i)) := by
  let schedule := tripleRealizedSchedule S base
  let sigma := realizedEquiv S.leftOrder base
  let g : E → ℝ := fun e =>
    crossTripleWeight (tripleModeAt S base e)
      (thr μ (sigma : Fin (Fintype.card E) → E) base (sigma.symm e))
      (thr μ (sigma : Fin (Fintype.card E) → E) left (sigma.symm e))
      (thr μ (sigma : Fin (Fintype.card E) → E) right (sigma.symm e))
      (base e) (left e) (right e)
  have hfac : (schedule.map fun p =>
      let before := ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
      crossTripleWeight p.2 (condProbClosed μ before base p.1)
        (condProbClosed μ before left p.1) (condProbClosed μ before right p.1)
        (base p.1) (left p.1) (right p.1)).prod =
      (schedule.map fun p => g p.1).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    simp only
    rw [tripleRealizedSchedule_mode S base p hp]
    rw [← idxOf_fst_tripleRealizedSchedule S base p hp]
    rw [List.map_take]
    rw [show schedule.map Prod.fst = realizedList S.leftOrder base from
      tripleRealizedSchedule_map_fst S base]
    rw [← thr_realizedEquiv μ S.leftOrder base base p.1]
    rw [← thr_realizedEquiv μ S.leftOrder base left p.1]
    rw [← thr_realizedEquiv μ S.leftOrder base right p.1]
  unfold staticCrossScheduleProduct
  simp only [Finset.empty_union]
  rw [show tripleRealizedSchedule S base = schedule from rfl, hfac]
  rw [show (schedule.map fun p => g p.1) = (realizedList S.leftOrder base).map g from by
    change (tripleRealizedSchedule S base).map (g ∘ Prod.fst) =
      (realizedList S.leftOrder base).map g
    rw [← List.map_map, tripleRealizedSchedule_map_fst]]
  rw [← List.prod_toFinset g (realizedList_nodup S.leftOrder base)]
  rw [realizedList_toFinset]
  rw [← sigma.prod_comp g]
  apply Finset.prod_congr rfl
  intro i _
  simp [g, sigma]

theorem tripleLabelCube_frozenCrossRawAtom_toReal_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (tripleLabelCube (Fintype.card E)
      (frozenCrossRawAtom μ S base left right)).toReal =
        crossTripleJointProb μ ∅ base left right S := by
  rw [tripleLabelCube_frozenCrossRawAtom, ENNReal.toReal_prod]
  have hprod : (∏ i : Fin (Fintype.card E),
      ((((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (crossRawTriple μ S base left right i)).toReal) =
      ∏ i : Fin (Fintype.card E),
        crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
          (base (realizedEquiv S.leftOrder base i))
          (left (realizedEquiv S.leftOrder base i))
          (right (realizedEquiv S.leftOrder base i)) := by
    apply Finset.prod_congr rfl
    intro i _
    exact crossRawTriple_toReal_eq_crossTripleWeight μ hpos S base left right i
  rw [hprod]
  rw [← staticCrossScheduleProduct_eq_prod_realized μ S base left right]
  rw [← crossScheduleProduct_eq_static μ ∅ base left right
    (tripleRealizedSchedule S base) (by
      rw [tripleRealizedSchedule_map_fst]
      exact realizedList_nodup S.leftOrder base)]
  exact (crossTripleJointProb_eq_crossScheduleProduct μ ∅ base left right S).symm


theorem tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (tripleCube (Fintype.card E)
      (frozenCrossCodeAtom μ S base left right)).toReal =
      crossTripleJointProb μ ∅ base left right S := by
  rw [frozenCrossCodeAtom_eq_rawTripleBox]
  exact tripleLabelCube_frozenCrossRawAtom_toReal_eq_crossTripleJointProb
    μ hpos S base left right





noncomputable def targetProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ active closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F target e
      splitWeight active a q false (target e) *
          targetProb μ (insert e F) (Function.update base e false) target closed
        + splitWeight active a q true (target e) *
          targetProb μ (insert e F) (Function.update base e true) target opened


noncomputable def jointProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ independent closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F target e
      if base e then
        splitWeight independent a q true (target e) *
          jointProb μ (insert e F) base target opened
      else
        splitWeight independent a q false (target e) *
          jointProb μ (insert e F) base target closed



noncomputable def pathProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (driver target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ _ closed opened =>
      bitWeight (condProbClosed μ F target e) (target e) *
        if driver e then
          pathProb μ (insert e F) driver target opened
        else pathProb μ (insert e F) driver target closed



theorem jointProb_allIndependent_eq_mul_pathProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) :
    jointProb μ F base target (allIndependent S) =
      pathProb μ F base base S * pathProb μ F base target S := by
  induction S generalizing F with
  | done =>
      change (1 : ℝ) = 1 * 1
      ring
  | node e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [allIndependent, jointProb, pathProb, hb, if_true,
          splitWeight, independentWeight]
        rw [iho]
        ring
      · simp only [allIndependent, jointProb, pathProb, hb,
          Bool.false_eq_true, if_false, splitWeight, independentWeight]
        rw [ihc]
        simp only [if_true]
        ring


def realizedSchedule : {R : Finset E} → CausalOrder R →
    ConfigSpace E → List (E × Bool)
  | _, .done, _ => []
  | _, .node e _ independent closed opened, base =>
      (e, independent) :: if base e then realizedSchedule opened base
        else realizedSchedule closed base

@[simp] lemma realizedSchedule_map_fst {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) :
    (realizedSchedule S base).map Prod.fst = realizedList S base := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [realizedSchedule, List.map_cons, realizedList]
      split <;> simp_all

lemma realizedSchedule_length {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedSchedule S base).length = R.card := by
  rw [← realizedList_length S base, ← realizedSchedule_map_fst S base,
    List.length_map]

lemma realizedSchedule_mode {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) (p : E × Bool) (hp : p ∈ realizedSchedule S base) :
    p.2 = independentAt S base p.1 := by
  induction S with
  | done => simp [realizedSchedule] at hp
  | @node R e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [realizedSchedule, hb, if_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [independentAt]
        · have hz : p.1 ∈ realizedList opened base := by
            rw [← realizedSchedule_map_fst opened base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [independentAt, hne, if_false, hb, if_true]
          exact iho hp
      · simp only [realizedSchedule, hb, Bool.false_eq_true, if_false, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [independentAt]
        · have hz : p.1 ∈ realizedList closed base := by
            rw [← realizedSchedule_map_fst closed base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [independentAt, hne, if_false, hb, Bool.false_eq_true]
          exact ihc hp

lemma idxOf_fst_realizedSchedule (S : CausalOrder (Finset.univ : Finset E))
    (base : ConfigSpace E) (p : E × Bool) (hp : p ∈ realizedSchedule S base) :
    (realizedList S base).idxOf p.1 = (realizedSchedule S base).idxOf p := by
  let l := realizedSchedule S base
  have hip : l.idxOf p < l.length := List.idxOf_lt_length_iff.mpr hp
  have hget : l.get ⟨l.idxOf p, hip⟩ = p := List.idxOf_get hip
  have hmap : (l.map Prod.fst).Nodup := by
    rw [show l.map Prod.fst = realizedList S base from realizedSchedule_map_fst S base]
    exact realizedList_nodup S base
  have hidx := List.get_idxOf hmap
    (⟨l.idxOf p, by simpa using hip⟩ : Fin (l.map Prod.fst).length)
  simp only [List.get_eq_getElem, List.getElem_map] at hidx
  rw [show l[l.idxOf p] = p from by simpa [List.get_eq_getElem] using hget] at hidx
  rw [show l.map Prod.fst = realizedList S base from realizedSchedule_map_fst S base] at hidx
  exact hidx


noncomputable def scheduleProduct (μ : ConfigSpace E → ℝ) :
    Finset E → ConfigSpace E → ConfigSpace E → List (E × Bool) → ℝ
  | _, _, _, [] => 1
  | F, base, target, (e, independent) :: tail =>
      splitWeight independent (condProbClosed μ F base e)
          (condProbClosed μ F target e) (base e) (target e) *
        scheduleProduct μ (insert e F) base target tail




noncomputable def staticScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base target : ConfigSpace E) (schedule : List (E × Bool)) : ℝ :=
  (schedule.map fun p =>
    let before := F ∪ ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
    splitWeight p.2 (condProbClosed μ before base p.1)
      (condProbClosed μ before target p.1) (base p.1) (target p.1)).prod



theorem scheduleProduct_eq_staticScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base target : ConfigSpace E) (schedule : List (E × Bool))
    (hnd : (schedule.map Prod.fst).Nodup) :
    scheduleProduct μ F base target schedule =
      staticScheduleProduct μ F base target schedule := by
  induction schedule generalizing F with
  | nil => rfl
  | cons p tail ih =>
      have hp : p.1 ∉ tail.map Prod.fst := (List.nodup_cons.mp hnd).1
      have htail : (tail.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      rw [scheduleProduct, staticScheduleProduct, List.map_cons, List.prod_cons]
      simp only [List.idxOf_cons_self, List.take_zero, List.map_nil, List.toFinset_nil,
        Finset.union_empty]
      rw [ih (insert p.1 F) htail]
      unfold staticScheduleProduct
      apply congrArg (fun x : ℝ =>
        splitWeight p.2 (condProbClosed μ F base p.1)
          (condProbClosed μ F target p.1) (base p.1) (target p.1) * x)
      apply congrArg List.prod
      apply List.map_congr_left
      intro q hq
      have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hp (List.mem_map_of_mem hq)
      have hcoord : p.1 ≠ q.1 := by
        intro heq
        have hmem : q.1 ∈ tail.map Prod.fst := by
          rw [List.mem_map]
          exact ⟨q, hq, rfl⟩
        exact hp (heq ▸ hmem)
      rw [List.idxOf_cons_ne tail hpq]
      simp only [List.take_succ_cons, List.map_cons, List.toFinset_cons,
        Finset.union_insert, Finset.insert_union]

theorem staticScheduleProduct_eq_prod_realized (μ : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E)) (base target : ConfigSpace E) :
    staticScheduleProduct μ ∅ base target (realizedSchedule S base) =
      ∏ i : Fin (Fintype.card E),
        splitWeight (independentAt S base (realizedEquiv S base i))
          (thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) base i)
          (thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) target i)
          (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
  let schedule := realizedSchedule S base
  let σ := realizedEquiv S base
  let g : E → ℝ := fun e =>
    splitWeight (independentAt S base e)
      (thr μ (σ : Fin (Fintype.card E) → E) base (σ.symm e))
      (thr μ (σ : Fin (Fintype.card E) → E) target (σ.symm e))
      (base e) (target e)
  have hfac : (schedule.map fun p =>
      let before := ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
      splitWeight p.2 (condProbClosed μ before base p.1)
        (condProbClosed μ before target p.1) (base p.1) (target p.1)).prod =
      (schedule.map fun p => g p.1).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    simp only
    rw [realizedSchedule_mode S base p hp]
    rw [← idxOf_fst_realizedSchedule S base p hp]
    rw [List.map_take]
    rw [show schedule.map Prod.fst = realizedList S base from
      realizedSchedule_map_fst S base]
    change
      splitWeight (independentAt S base p.1)
          (condProbClosed μ
            ((realizedList S base).take ((realizedList S base).idxOf p.1)).toFinset
            base p.1)
          (condProbClosed μ
            ((realizedList S base).take ((realizedList S base).idxOf p.1)).toFinset
            target p.1) (base p.1) (target p.1) = g p.1
    rw [← thr_realizedEquiv μ S base base p.1]
    rw [← thr_realizedEquiv μ S base target p.1]
  unfold staticScheduleProduct
  simp only [Finset.empty_union]
  rw [show realizedSchedule S base = schedule from rfl, hfac]
  rw [show (schedule.map fun p => g p.1) = (realizedList S base).map g from by
    change (realizedSchedule S base).map (g ∘ Prod.fst) =
      (realizedList S base).map g
    rw [← List.map_map, realizedSchedule_map_fst]]
  rw [← List.prod_toFinset g (realizedList_nodup S base)]
  rw [realizedList_toFinset]
  rw [← σ.prod_comp g]
  apply Finset.prod_congr rfl
  intro i _
  simp [g, σ]



theorem jointProb_eq_scheduleProduct (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) {R : Finset E} (S : CausalOrder R) :
    jointProb μ F base target S =
      scheduleProduct μ F base target (realizedSchedule S base) := by
  induction S generalizing F base with
  | done => rfl
  | @node R e he independent closed opened ihc iho =>
      rw [jointProb, realizedSchedule, scheduleProduct]
      by_cases hb : base e
      · simp only [hb, if_true]
        exact congrArg
          (fun z => splitWeight independent (condProbClosed μ F base e)
            (condProbClosed μ F target e) true (target e) * z)
          (iho (insert e F) base)
      · simp only [hb, Bool.false_eq_true, if_false]
        exact congrArg
          (fun z => splitWeight independent (condProbClosed μ F base e)
            (condProbClosed μ F target e) false (target e) * z)
          (ihc (insert e F) base)



theorem pairedCube_frozenCodeAtom_toReal_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal =
      jointProb μ ∅ base target S := by
  rw [pairedCube_frozenCodeAtom_toReal_eq_prod_splitWeight μ hpos S base target]
  rw [← staticScheduleProduct_eq_prod_realized μ S base target]
  rw [← scheduleProduct_eq_staticScheduleProduct μ ∅ base target
    (realizedSchedule S base) (by
      rw [realizedSchedule_map_fst]
      exact realizedList_nodup S base)]
  exact (jointProb_eq_scheduleProduct μ ∅ base target S).symm


theorem pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (pairedCube (Fintype.card E)
      (frozenTripleCodeAtom μ S base left right)).toReal =
      tripleJointProb μ ∅ base left right S := by
  rw [pairedCube_frozenTripleCodeAtom_toReal_eq_prod_tripleWeight
    μ hpos S base left right]
  rw [← staticTripleScheduleProduct_eq_prod_realized μ S base left right]
  rw [← tripleScheduleProduct_eq_static μ ∅ base left right
    (tripleRealizedSchedule S base) (by
      rw [tripleRealizedSchedule_map_fst]
      exact realizedList_nodup S.leftOrder base)]
  exact (tripleJointProb_eq_tripleScheduleProduct μ ∅ base left right S).symm

noncomputable def baseSum (F : Finset E) (seed : ConfigSpace E)
    (H : ConfigSpace E → ℝ) : ℝ :=
  ∑ base, if Agree F seed base then H base else 0

noncomputable def condObservable (μ : ConfigSpace E → ℝ) (F : Finset E)
    (seed : ConfigSpace E) (g : ConfigSpace E → ℝ) : ℝ :=
  baseSum F seed (fun target => g target * condMass μ F target target)

lemma baseSum_split (F : Finset E) (seed : ConfigSpace E)
    (H : ConfigSpace E → ℝ) (e : E) (he : e ∉ F) :
    baseSum F seed H =
      baseSum (insert e F) (Function.update seed e false) H +
        baseSum (insert e F) (Function.update seed e true) H := by
  unfold baseSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro base _
  by_cases hA : Agree F seed base
  · by_cases hb : base e
    · have hfalse : ¬ Agree (insert e F) (Function.update seed e false) base := by
        intro h
        have := h e (Finset.mem_insert_self e F)
        simp [hb] at this
      have htrue : Agree (insert e F) (Function.update seed e true) base := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [hb]
        · have hze : z ≠ e := fun h => he (h ▸ hz)
          rw [Function.update_of_ne hze]
          exact hA z hz
      simp [hA, hfalse, htrue]
    · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
      have hfalse : Agree (insert e F) (Function.update seed e false) base := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [hb']
        · have hze : z ≠ e := fun h => he (h ▸ hz)
          rw [Function.update_of_ne hze]
          exact hA z hz
      have htrue : ¬ Agree (insert e F) (Function.update seed e true) base := by
        intro h
        have := h e (Finset.mem_insert_self e F)
        simp [hb'] at this
      simp [hA, hfalse, htrue]
  · have hchild : ∀ b : Bool,
        ¬ Agree (insert e F) (Function.update seed e b) base := by
      intro b h
      apply hA
      intro z hz
      have hze : z ≠ e := fun hze => he (hze ▸ hz)
      have hz' := h z (Finset.mem_insert_of_mem hz)
      rw [Function.update_of_ne hze] at hz'
      exact hz'
    simp [hA, hchild]

lemma baseSum_condMass_self_eq_one (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (seed : ConfigSpace E) :
    baseSum F seed (fun base => condMass μ F base base) = 1 := by
  have heq : baseSum F seed (fun base => condMass μ F base base) =
      ∑ base, condMass μ F seed base := by
    unfold baseSum
    apply Finset.sum_congr rfl
    intro base _
    by_cases hA : Agree F seed base
    · rw [if_pos hA]
      unfold condMass
      change ((if Agree F base base then μ base else 0) / condNorm μ F base) =
        (if Agree F seed base then μ base else 0) / condNorm μ F seed
      rw [if_pos (agree_self F base), if_pos hA]
      rw [condNorm_congr μ F seed base (fun e he => (hA e he).symm)]
    · rw [if_neg hA]
      unfold condMass
      change 0 = (if Agree F seed base then μ base else 0) / condNorm μ F seed
      rw [if_neg hA]
      simp
  rw [heq, condMass_sum F seed (condNorm_pos hpos F seed).ne']

theorem baseSum_tripleJointProb_eq_tripleProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (seed left right : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base => tripleJointProb μ F base left right S) =
      tripleProb μ F seed left right S := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleJointProb tripleProb
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro base _ hne
        have hnA : ¬ Agree Finset.univ seed base := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [tripleProb]
      rw [baseSum_split F seed (fun base =>
        tripleJointProb μ F base left right (.node e he mode closed opened)) e heF]
      have hbranch (b : Bool) :
          baseSum (insert e F) (Function.update seed e b)
              (fun base => tripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode (condProbClosed μ F seed e)
                (condProbClosed μ F left e) (condProbClosed μ F right e)
                b (left e) (right e) *
              baseSum (insert e F) (Function.update seed e b)
                (fun base => tripleJointProb μ (insert e F) base left right
                  (if b then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro base _
        by_cases hA : Agree (insert e F) (Function.update seed e b) base
        · have hbit : base e = b := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed base := by
            intro z hz
            have hze : z ≠ e := fun hze => heF (hze ▸ hz)
            have h := hA z (Finset.mem_insert_of_mem hz)
            rw [Function.update_of_ne hze] at h
            exact h
          have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
            condProbClosed_congr μ F base seed e (fun z hz => hag z hz)
          simp only [hA, if_true]
          rw [tripleJointProb, hbit, hq]
          cases b <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [ihc (insert e F) (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update seed e true) hchild]



theorem baseSum_flip_tripleJointProb_eq_flipTripleProb
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (seed left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base =>
      (if tripleModeAt S base z = .flip then 1 else 0) *
        tripleJointProb μ F base left right S) =
      flipTripleProb μ F seed left right z S := by
  induction S generalizing F seed with
  | done => simp [baseSum, tripleModeAt, flipTripleProb]
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      by_cases hze : z = e
      · subst z
        by_cases hm : mode = .flip
        · subst mode
          simp only [tripleModeAt, if_pos rfl, if_true, one_mul]
          rw [baseSum_tripleJointProb_eq_tripleProb μ F seed left right
            (.node e he .flip closed opened) hR]
          simp [flipTripleProb]
        · have hm' : mode ≠ TripleMode.flip := hm
          simp only [tripleModeAt, if_pos rfl, hm', if_false, zero_mul]
          simp [baseSum, flipTripleProb, hm']
      · rw [baseSum_split F seed (fun base =>
          (if tripleModeAt (.node e he mode closed opened) base z = .flip
            then 1 else 0) *
            tripleJointProb μ F base left right
              (.node e he mode closed opened)) e heF]
        have hbranch (b : Bool) :
            baseSum (insert e F) (Function.update seed e b)
                (fun base =>
                  (if tripleModeAt (.node e he mode closed opened) base z = .flip
                    then 1 else 0) *
                    tripleJointProb μ F base left right
                      (.node e he mode closed opened)) =
              tripleWeight mode (condProbClosed μ F seed e)
                  (condProbClosed μ F left e) (condProbClosed μ F right e)
                  b (left e) (right e) *
                baseSum (insert e F) (Function.update seed e b)
                  (fun base =>
                    (if tripleModeAt (if b then opened else closed) base z = .flip
                      then 1 else 0) *
                      tripleJointProb μ (insert e F) base left right
                        (if b then opened else closed)) := by
          unfold baseSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro base _
          by_cases hA : Agree (insert e F) (Function.update seed e b) base
          · have hbit : base e = b := by
              have h := hA e (Finset.mem_insert_self e F)
              simpa using h
            have hag : Agree F seed base := by
              intro x hx
              have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
              have h := hA x (Finset.mem_insert_of_mem hx)
              rw [Function.update_of_ne hxe] at h
              exact h
            have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
              condProbClosed_congr μ F base seed e (fun x hx => hag x hx)
            simp only [hA, if_true]
            rw [tripleJointProb, hbit, hq]
            cases b
            · by_cases hm : tripleModeAt closed base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
            · by_cases hm : tripleModeAt opened base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
          · simp [hA]
        rw [hbranch false, hbranch true]
        simp only [Bool.false_eq_true, if_false, if_true]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp [flipTripleProb, hze]

theorem baseSum_crossTripleJointProb_eq_crossTripleProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (seed left right : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base => crossTripleJointProb μ F base left right S) =
      crossTripleProb μ F seed left right S := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum crossTripleJointProb crossTripleProb
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro base _ hne
        have hnA : ¬ Agree Finset.univ seed base := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [crossTripleProb]
      rw [baseSum_split F seed (fun base =>
        crossTripleJointProb μ F base left right (.node e he mode closed opened)) e heF]
      have hbranch (b : Bool) :
          baseSum (insert e F) (Function.update seed e b)
              (fun base => crossTripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            crossTripleWeight mode (condProbClosed μ F seed e)
                (condProbClosed μ F left e) (condProbClosed μ F right e)
                b (left e) (right e) *
              baseSum (insert e F) (Function.update seed e b)
                (fun base => crossTripleJointProb μ (insert e F) base left right
                  (if b then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro base _
        by_cases hA : Agree (insert e F) (Function.update seed e b) base
        · have hbit : base e = b := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed base := by
            intro z hz
            have hze : z ≠ e := fun hze => heF (hze ▸ hz)
            have h := hA z (Finset.mem_insert_of_mem hz)
            rw [Function.update_of_ne hze] at h
            exact h
          have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
            condProbClosed_congr μ F base seed e (fun z hz => hag z hz)
          simp only [hA, if_true]
          rw [crossTripleJointProb, hbit, hq]
          cases b <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [ihc (insert e F) (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update seed e true) hchild]




theorem baseSum_flip_crossTripleJointProb_eq_flipCrossTripleProb
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (seed left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base =>
      (if tripleModeAt S base z = .flip then 1 else 0) *
        crossTripleJointProb μ F base left right S) =
      flipCrossTripleProb μ F seed left right z S := by
  induction S generalizing F seed with
  | done => simp [baseSum, tripleModeAt, flipCrossTripleProb]
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      by_cases hze : z = e
      · subst z
        by_cases hm : mode = .flip
        · subst mode
          simp only [tripleModeAt, if_pos rfl, if_true, one_mul]
          rw [baseSum_crossTripleJointProb_eq_crossTripleProb μ F seed left right
            (.node e he .flip closed opened) hR]
          simp [flipCrossTripleProb]
        · have hm' : mode ≠ TripleMode.flip := hm
          simp only [tripleModeAt, if_pos rfl, hm', if_false, zero_mul]
          simp [baseSum, flipCrossTripleProb, hm']
      · rw [baseSum_split F seed (fun base =>
          (if tripleModeAt (.node e he mode closed opened) base z = .flip
            then 1 else 0) *
            crossTripleJointProb μ F base left right
              (.node e he mode closed opened)) e heF]
        have hbranch (b : Bool) :
            baseSum (insert e F) (Function.update seed e b)
                (fun base =>
                  (if tripleModeAt (.node e he mode closed opened) base z = .flip
                    then 1 else 0) *
                    crossTripleJointProb μ F base left right
                      (.node e he mode closed opened)) =
              crossTripleWeight mode (condProbClosed μ F seed e)
                  (condProbClosed μ F left e) (condProbClosed μ F right e)
                  b (left e) (right e) *
                baseSum (insert e F) (Function.update seed e b)
                  (fun base =>
                    (if tripleModeAt (if b then opened else closed) base z = .flip
                      then 1 else 0) *
                      crossTripleJointProb μ (insert e F) base left right
                        (if b then opened else closed)) := by
          unfold baseSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro base _
          by_cases hA : Agree (insert e F) (Function.update seed e b) base
          · have hbit : base e = b := by
              have h := hA e (Finset.mem_insert_self e F)
              simpa using h
            have hag : Agree F seed base := by
              intro x hx
              have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
              have h := hA x (Finset.mem_insert_of_mem hx)
              rw [Function.update_of_ne hxe] at h
              exact h
            have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
              condProbClosed_congr μ F base seed e (fun x hx => hag x hx)
            simp only [hA, if_true]
            rw [crossTripleJointProb, hbit, hq]
            cases b
            · by_cases hm : tripleModeAt closed base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
            · by_cases hm : tripleModeAt opened base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
          · simp [hA]
        rw [hbranch false, hbranch true]
        simp only [Bool.false_eq_true, if_false, if_true]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp [flipCrossTripleProb, hze]

theorem sum_tripleJointProb_empty_eq_tripleProb (μ : ConfigSpace E → ℝ)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, tripleJointProb μ ∅ base left right S =
      tripleProb μ ∅ seed left right S := by
  have h := baseSum_tripleJointProb_eq_tripleProb μ ∅ seed left right S (by simp)
  simpa [baseSum, Agree] using h

theorem sum_pairedCube_frozenTripleCodeAtom_eq_tripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, (pairedCube (Fintype.card E)
        (frozenTripleCodeAtom μ S base left right)).toReal =
      tripleProb μ ∅ seed left right S := by
  simp_rw [pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb μ hpos]
  exact sum_tripleJointProb_empty_eq_tripleProb μ seed left right S


theorem sum_crossTripleJointProb_empty_eq_crossTripleProb (μ : ConfigSpace E → ℝ)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, crossTripleJointProb μ ∅ base left right S =
      crossTripleProb μ ∅ seed left right S := by
  have h := baseSum_crossTripleJointProb_eq_crossTripleProb
    μ ∅ seed left right S (by simp)
  simpa [baseSum, Agree] using h

theorem sum_tripleCube_frozenCrossCodeAtom_eq_crossTripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, (tripleCube (Fintype.card E)
        (frozenCrossCodeAtom μ S base left right)).toReal =
      crossTripleProb μ ∅ seed left right S := by
  simp_rw [tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb μ hpos]
  exact sum_crossTripleJointProb_empty_eq_crossTripleProb μ seed left right S


theorem sum_frozenTripleCodeAtom_observable_eq_tripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed : ConfigSpace E) (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g left right *
        (pairedCube (Fintype.card E)
          (frozenTripleCodeAtom μ S base left right)).toReal =
      ∑ left, ∑ right, g left right * tripleProb μ ∅ seed left right S := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  rw [← Finset.mul_sum]
  rw [sum_pairedCube_frozenTripleCodeAtom_eq_tripleProb μ hpos seed left right S]


theorem sum_frozenCrossCodeAtom_observable_eq_crossTripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed : ConfigSpace E) (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g left right *
        (tripleCube (Fintype.card E)
          (frozenCrossCodeAtom μ S base left right)).toReal =
      ∑ left, ∑ right, g left right * crossTripleProb μ ∅ seed left right S := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  rw [← Finset.mul_sum]
  rw [sum_tripleCube_frozenCrossCodeAtom_eq_crossTripleProb μ hpos seed left right S]


theorem sum_frozenTripleCodeAtom_weighted_eq_tripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g base left right *
        (pairedCube (Fintype.card E)
          (frozenTripleCodeAtom μ S base left right)).toReal =
      ∑ base, ∑ left, ∑ right, g base left right *
        tripleJointProb μ ∅ base left right S := by
  simp_rw [pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb μ hpos]


theorem sum_frozenCrossCodeAtom_weighted_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g base left right *
        (tripleCube (Fintype.card E)
          (frozenCrossCodeAtom μ S base left right)).toReal =
      ∑ base, ∑ left, ∑ right, g base left right *
        crossTripleJointProb μ ∅ base left right S := by
  simp_rw [tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb μ hpos]

theorem baseSum_jointProb_eq_targetProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (seed target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base => jointProb μ F base target S) =
      targetProb μ F seed target S := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum jointProb targetProb
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro base _ hne
        have hnA : ¬ Agree Finset.univ seed base := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he independent closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [targetProb]
      rw [baseSum_split F seed (fun base => jointProb μ F base target
        (.node e he independent closed opened)) e heF]
      have hbranch (b : Bool) :
          baseSum (insert e F) (Function.update seed e b)
              (fun base => jointProb μ F base target
                (.node e he independent closed opened)) =
            splitWeight independent (condProbClosed μ F seed e)
                (condProbClosed μ F target e) b (target e) *
              baseSum (insert e F) (Function.update seed e b)
                (fun base => jointProb μ (insert e F) base target
                  (if b then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro base _
        by_cases hA : Agree (insert e F) (Function.update seed e b) base
        · have hbit : base e = b := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed base := by
            intro z hz
            have hze : z ≠ e := fun hze => heF (hze ▸ hz)
            have h := hA z (Finset.mem_insert_of_mem hz)
            rw [Function.update_of_ne hze] at h
            exact h
          have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
            condProbClosed_congr μ F base seed e (fun z hz => hag z hz)
          simp only [hA, if_true]
          rw [jointProb, hbit, hq]
          cases b <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [ihc (insert e F) (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update seed e true) hchild]

theorem sum_jointProb_empty_eq_targetProb (μ : ConfigSpace E → ℝ)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base, jointProb μ ∅ base target S = targetProb μ ∅ seed target S := by
  have h := baseSum_jointProb_eq_targetProb μ ∅ seed target S (by simp)
  simpa [baseSum, Agree] using h

theorem baseSum_tripleJointProb_right_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (base left seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun right => tripleJointProb μ F base left right S) =
      jointProb μ F base left S.leftOrder := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleJointProb jointProb TripleOrder.leftOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro right _ hne
        have hnA : ¬ Agree Finset.univ seed right := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F seed e
      rw [baseSum_split F seed (fun right => tripleJointProb μ F base left right
        (.node e he mode closed opened)) e heF]
      have hbranch (z : Bool) :
          baseSum (insert e F) (Function.update seed e z)
              (fun right => tripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r (base e) (left e) z *
              baseSum (insert e F) (Function.update seed e z)
                (fun right => tripleJointProb μ (insert e F) base left right
                  (if base e then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro right _
        by_cases hA : Agree (insert e F) (Function.update seed e z) right
        · have hbit : right e = z := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed right := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hr : condProbClosed μ F right e = r := by
            change condProbClosed μ F right e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F right seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleJointProb, hr, hbit]
          cases hb : base e <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd left
      have hr := hbnd seed
      by_cases hb : base e
      · simp only [hb, if_true]
        rw [iho (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.leftOrder, jointProb, hb, if_true]
        rw [← add_mul]
        rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          true (left e)]
      · simp only [hb, Bool.false_eq_true, if_false]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [ihc (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.leftOrder, jointProb, hb, Bool.false_eq_true, if_false]
        rw [← add_mul]
        rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          false (left e)]

theorem baseSum_tripleJointProb_left_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (base right seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun left => tripleJointProb μ F base left right S) =
      jointProb μ F base right S.rightOrder := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleJointProb jointProb TripleOrder.rightOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro left _ hne
        have hnA : ¬ Agree Finset.univ seed left := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F seed e
      let r := condProbClosed μ F right e
      rw [baseSum_split F seed (fun left => tripleJointProb μ F base left right
        (.node e he mode closed opened)) e heF]
      have hbranch (y : Bool) :
          baseSum (insert e F) (Function.update seed e y)
              (fun left => tripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r (base e) y (right e) *
              baseSum (insert e F) (Function.update seed e y)
                (fun left => tripleJointProb μ (insert e F) base left right
                  (if base e then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro left _
        by_cases hA : Agree (insert e F) (Function.update seed e y) left
        · have hbit : left e = y := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed left := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hq : condProbClosed μ F left e = q := by
            change condProbClosed μ F left e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F left seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleJointProb, hq, hbit]
          cases hb : base e <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd seed
      have hr := hbnd right
      by_cases hb : base e
      · simp only [hb, if_true]
        rw [iho (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.rightOrder, jointProb, hb, if_true]
        rw [← add_mul]
        rw [tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          true (right e)]
      · simp only [hb, Bool.false_eq_true, if_false]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [ihc (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.rightOrder, jointProb, hb, Bool.false_eq_true, if_false]
        rw [← add_mul]
        rw [tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          false (right e)]

theorem sum_tripleJointProb_right_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (base left seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ right, tripleJointProb μ ∅ base left right S =
      jointProb μ ∅ base left S.leftOrder := by
  have h := baseSum_tripleJointProb_right_eq_jointProb
    μ hpos ∅ base left seed S (by simp)
  simpa [baseSum, Agree] using h

theorem sum_tripleJointProb_left_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (base right seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ left, tripleJointProb μ ∅ base left right S =
      jointProb μ ∅ base right S.rightOrder := by
  have h := baseSum_tripleJointProb_left_eq_jointProb
    μ hpos ∅ base right seed S (by simp)
  simpa [baseSum, Agree] using h

theorem baseSum_tripleProb_right_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base left seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun right => tripleProb μ F base left right S) =
      targetProb μ F base left S.leftOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleProb targetProb TripleOrder.leftOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro right _ hne
        have hnA : ¬ Agree Finset.univ seed right := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.leftOrder, targetProb]
      rw [baseSum_split F seed (fun right => tripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F seed e
      have hbranch (z : Bool) :
          baseSum (insert e F) (Function.update seed e z)
              (fun right => tripleProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r false (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => tripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              tripleWeight mode a q r true (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => tripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro right _
        by_cases hA : Agree (insert e F) (Function.update seed e z) right
        · have hbit : right e = z := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed right := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hr : condProbClosed μ F right e = r := by
            change condProbClosed μ F right e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F right seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleProb, hr, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd left
      have hr := hbnd seed
      let C := targetProb μ (insert e F) (Function.update base e false) left
        closed.leftOrder
      let D := targetProb μ (insert e F) (Function.update base e true) left
        opened.leftOrder
      change
        (tripleWeight mode a q r false (left e) false * C +
            tripleWeight mode a q r true (left e) false * D) +
          (tripleWeight mode a q r false (left e) true * C +
            tripleWeight mode a q r true (left e) true * D) =
        splitWeight mode.leftIndependent a q false (left e) * C +
          splitWeight mode.leftIndependent a q true (left e) * D
      calc
        _ = (tripleWeight mode a q r false (left e) false +
              tripleWeight mode a q r false (left e) true) * C +
            (tripleWeight mode a q r true (left e) false +
              tripleWeight mode a q r true (left e) true) * D := by ring
        _ = _ := by
          rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            false (left e)]
          rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            true (left e)]

theorem baseSum_tripleProb_left_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base right seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun left => tripleProb μ F base left right S) =
      targetProb μ F base right S.rightOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleProb targetProb TripleOrder.rightOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro left _ hne
        have hnA : ¬ Agree Finset.univ seed left := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.rightOrder]
      rw [targetProb]
      rw [baseSum_split F seed (fun left => tripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F seed e
      let r := condProbClosed μ F right e
      have hbranch (y : Bool) :
          baseSum (insert e F) (Function.update seed e y)
              (fun left => tripleProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r false y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => tripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              tripleWeight mode a q r true y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => tripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro left _
        by_cases hA : Agree (insert e F) (Function.update seed e y) left
        · have hbit : left e = y := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed left := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hq : condProbClosed μ F left e = q := by
            change condProbClosed μ F left e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F left seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleProb, hq, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd seed
      have hr := hbnd right
      let C := targetProb μ (insert e F) (Function.update base e false) right
        closed.rightOrder
      let D := targetProb μ (insert e F) (Function.update base e true) right
        opened.rightOrder
      change
        (tripleWeight mode a q r false false (right e) * C +
            tripleWeight mode a q r true false (right e) * D) +
          (tripleWeight mode a q r false true (right e) * C +
            tripleWeight mode a q r true true (right e) * D) =
        splitWeight mode.rightIndependent a r false (right e) * C +
          splitWeight mode.rightIndependent a r true (right e) * D
      calc
        _ = (tripleWeight mode a q r false false (right e) +
              tripleWeight mode a q r false true (right e)) * C +
            (tripleWeight mode a q r true false (right e) +
              tripleWeight mode a q r true true (right e)) * D := by ring
        _ = _ := by
          have h0 := tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2
            hr.1 hr.2 false (right e)
          have h1 := tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2
            hr.1 hr.2 true (right e)
          rw [h0, h1]

theorem baseSum_crossTripleProb_right_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base left seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun right => crossTripleProb μ F base left right S) =
      targetProb μ F base left S.leftOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum crossTripleProb targetProb TripleOrder.leftOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro right _ hne
        have hnA : ¬ Agree Finset.univ seed right := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.leftOrder, targetProb]
      rw [baseSum_split F seed (fun right => crossTripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F seed e
      have hbranch (z : Bool) :
          baseSum (insert e F) (Function.update seed e z)
              (fun right => crossTripleProb μ F base left right
                (.node e he mode closed opened)) =
            crossTripleWeight mode a q r false (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => crossTripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              crossTripleWeight mode a q r true (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => crossTripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro right _
        by_cases hA : Agree (insert e F) (Function.update seed e z) right
        · have hbit : right e = z := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed right := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hr : condProbClosed μ F right e = r := by
            change condProbClosed μ F right e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F right seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [crossTripleProb, hr, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd left
      have hr := hbnd seed
      let C := targetProb μ (insert e F) (Function.update base e false) left
        closed.leftOrder
      let D := targetProb μ (insert e F) (Function.update base e true) left
        opened.leftOrder
      change
        (crossTripleWeight mode a q r false (left e) false * C +
            crossTripleWeight mode a q r true (left e) false * D) +
          (crossTripleWeight mode a q r false (left e) true * C +
            crossTripleWeight mode a q r true (left e) true * D) =
        splitWeight mode.leftIndependent a q false (left e) * C +
          splitWeight mode.leftIndependent a q true (left e) * D
      calc
        _ = (crossTripleWeight mode a q r false (left e) false +
              crossTripleWeight mode a q r false (left e) true) * C +
            (crossTripleWeight mode a q r true (left e) false +
              crossTripleWeight mode a q r true (left e) true) * D := by ring
        _ = _ := by
          rw [crossTripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            false (left e)]
          rw [crossTripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            true (left e)]

theorem baseSum_crossTripleProb_left_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base right seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun left => crossTripleProb μ F base left right S) =
      targetProb μ F base right S.rightOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum crossTripleProb targetProb TripleOrder.rightOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro left _ hne
        have hnA : ¬ Agree Finset.univ seed left := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.rightOrder]
      rw [targetProb]
      rw [baseSum_split F seed (fun left => crossTripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F seed e
      let r := condProbClosed μ F right e
      have hbranch (y : Bool) :
          baseSum (insert e F) (Function.update seed e y)
              (fun left => crossTripleProb μ F base left right
                (.node e he mode closed opened)) =
            crossTripleWeight mode a q r false y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => crossTripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              crossTripleWeight mode a q r true y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => crossTripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro left _
        by_cases hA : Agree (insert e F) (Function.update seed e y) left
        · have hbit : left e = y := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed left := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hq : condProbClosed μ F left e = q := by
            change condProbClosed μ F left e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F left seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [crossTripleProb, hq, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd seed
      have hr := hbnd right
      let C := targetProb μ (insert e F) (Function.update base e false) right
        closed.rightOrder
      let D := targetProb μ (insert e F) (Function.update base e true) right
        opened.rightOrder
      change
        (crossTripleWeight mode a q r false false (right e) * C +
            crossTripleWeight mode a q r true false (right e) * D) +
          (crossTripleWeight mode a q r false true (right e) * C +
            crossTripleWeight mode a q r true true (right e) * D) =
        splitWeight mode.rightIndependent a r false (right e) * C +
          splitWeight mode.rightIndependent a r true (right e) * D
      calc
        _ = (crossTripleWeight mode a q r false false (right e) +
              crossTripleWeight mode a q r false true (right e)) * C +
            (crossTripleWeight mode a q r true false (right e) +
              crossTripleWeight mode a q r true true (right e)) * D := by ring
        _ = _ := by
          rw [crossTripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            false (right e)]
          rw [crossTripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            true (right e)]





theorem jointProb_zero_support (μ : ConfigSpace E → ℝ) (T : DecisionTree E)
    (F R : Finset E) (known base target : ConfigSpace E)
    (hR : R = Finset.univ \ F)
    (hknown : ∀ e, e ∉ R → known e = base e)
    (hagree : Agree F base target)
    (hnz : jointProb μ F base target (extendDecisionTreeAt 0 T known R) ≠ 0) :
    T.eval base = T.eval target := by
  induction T generalizing F R known with
  | leaf b => rfl
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeAt] at hnz
      by_cases heR : e ∈ R
      · rw [dif_pos heR] at hnz
        have heF : e ∉ F := by
          intro heF
          have hmem : e ∈ Finset.univ \ F := by rw [← hR]; exact heR
          exact (Finset.mem_sdiff.mp hmem).2 heF
        have hthr : condProbClosed μ F base e = condProbClosed μ F target e :=
          condProbClosed_congr μ F base target e (fun z hz => (hagree z hz).symm)
        have hR' : R.erase e = Finset.univ \ insert e F := by
          rw [hR]
          ext z
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_insert]
          tauto
        by_cases hb : base e
        · simp only [hb, if_true, Nat.lt_irrefl, decide_false, jointProb,
            splitWeight, Bool.false_eq_true, if_false] at hnz
          have hbit : target e = true := by
            by_contra ht
            have ht' : target e = false := Bool.eq_false_of_not_eq_true ht
            rw [hthr, ht', overlapWeight_same_threshold_ne _ (by decide)] at hnz
            simp at hnz
          have htail : jointProb μ (insert e F) base target
              (extendDecisionTreeAt 0 opened (Function.update known e true) (R.erase e)) ≠ 0 :=
            (mul_ne_zero_iff.mp hnz).2
          have hk' : ∀ z, z ∉ R.erase e → Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z; simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          have ha' : Agree (insert e F) base target := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · simpa [hb] using hbit.symm
            · exact hagree z hz
          simp only [DecisionTree.eval, hb, hbit, if_true]
          exact iho (insert e F) (R.erase e) (Function.update known e true)
            hR' hk' ha' htail
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          simp only [hb, Bool.false_eq_true, if_false, Nat.lt_irrefl, decide_false,
            jointProb, splitWeight] at hnz
          have hbit : target e = false := by
            by_contra ht
            have ht' : target e = true := Bool.eq_true_of_not_eq_false ht
            rw [hthr, ht', overlapWeight_same_threshold_ne _ (by decide)] at hnz
            simp at hnz
          have htail : jointProb μ (insert e F) base target
              (extendDecisionTreeAt 0 closed (Function.update known e false) (R.erase e)) ≠ 0 :=
            (mul_ne_zero_iff.mp hnz).2
          have hk' : ∀ z, z ∉ R.erase e → Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z; simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          have ha' : Agree (insert e F) base target := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · simpa [hb'] using hbit.symm
            · exact hagree z hz
          simp only [DecisionTree.eval, hb, hbit, Bool.false_eq_true, if_false]
          exact ihc (insert e F) (R.erase e) (Function.update known e false)
            hR' hk' ha' htail
      · rw [dif_neg heR] at hnz
        have heF : e ∈ F := by
          by_contra heF
          have hmem : e ∈ Finset.univ \ F :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, heF⟩
          rw [← hR] at hmem
          exact heR hmem
        have hkb : known e = base e := hknown e heR
        have htb : target e = base e := hagree e heF
        by_cases hb : base e
        · simp only [hkb, hb, if_true] at hnz
          simp only [DecisionTree.eval, hb, htb, if_true]
          exact iho F R known hR hknown hagree hnz
        · simp only [hkb, hb, Bool.false_eq_true, if_false] at hnz
          simp only [DecisionTree.eval, hb, htb, Bool.false_eq_true, if_false]
          exact ihc F R known hR hknown hagree hnz

theorem jointProb_zero_support_univ (μ : ConfigSpace E → ℝ) (T : DecisionTree E)
    (base target : ConfigSpace E)
    (hnz : jointProb μ ∅ base target
      (extendDecisionTreeAt 0 T base (Finset.univ : Finset E)) ≠ 0) :
    T.eval base = T.eval target :=
  jointProb_zero_support μ T ∅ Finset.univ base base target
    (by simp) (by simp) (by simp [Agree]) hnz






noncomputable def targetIntegral (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ active closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F target e
      (if active then
          (volume (thresholdInterval a false)).toReal *
            (volume (thresholdInterval q (target e))).toReal
        else
          (volume (thresholdInterval a false ∩ thresholdInterval q (target e))).toReal) *
          targetIntegral μ (insert e F) (Function.update base e false) target closed
        + (if active then
          (volume (thresholdInterval a true)).toReal *
            (volume (thresholdInterval q (target e))).toReal
        else
          (volume (thresholdInterval a true ∩ thresholdInterval q (target e))).toReal) *
          targetIntegral μ (insert e F) (Function.update base e true) target opened


theorem targetIntegral_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (base target : ConfigSpace E)
    {R : Finset E} (S : CausalOrder R) :
    targetIntegral μ F base target S = targetProb μ F base target S := by
  induction S generalizing F base with
  | done => rfl
  | @node R e he active closed opened ihc iho =>
      rw [targetIntegral, targetProb]
      have ha : 0 ≤ condProbClosed μ F base e ∧ condProbClosed μ F base e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F base e false
          (condNorm_pos hpos F base),
          condProbBit_le_one (fun ω => (hpos ω).le) F base e false
          (condNorm_pos hpos F base)⟩
      have hq : 0 ≤ condProbClosed μ F target e ∧ condProbClosed μ F target e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F target e false
          (condNorm_pos hpos F target),
          condProbBit_le_one (fun ω => (hpos ω).le) F target e false
          (condNorm_pos hpos F target)⟩
      by_cases hactive : active
      · simp only [hactive, if_true, splitWeight, independentWeight]
        rw [volume_thresholdInterval _ ha.1 ha.2 false]
        rw [volume_thresholdInterval _ ha.1 ha.2 true]
        rw [volume_thresholdInterval _ hq.1 hq.2 (target e)]
        rw [ihc, iho]
      · simp only [hactive, Bool.false_eq_true, if_false, splitWeight]
        rw [volume_thresholdInterval_inter _ _ ha.1 ha.2 hq.1 hq.2 false (target e)]
        rw [volume_thresholdInterval_inter _ _ ha.1 ha.2 hq.1 hq.2 true (target e)]
        rw [ihc, iho]




theorem sum_pairedCube_frozenCodeAtom_eq_targetIntegral
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base : ConfigSpace E,
        (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal =
      targetIntegral μ ∅ seed target S := by
  simp_rw [pairedCube_frozenCodeAtom_toReal_eq_jointProb μ hpos]
  rw [targetIntegral_eq_targetProb μ hpos]
  rw [← baseSum_jointProb_eq_targetProb μ ∅ seed target S (by simp)]
  unfold baseSum
  simp [Agree]


lemma condMass_chain_step (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (target : ConfigSpace E) (e : E) (he : e ∉ F) :
    condMass μ F target target =
      condProbBit μ F target e (target e) *
        condMass μ (insert e F) target target := by
  unfold condMass
  rw [if_pos (agree_self F target), if_pos (agree_self (insert e F) target)]
  rw [condProbBit_eq_ratio]
  have hF := (condNorm_pos hpos F target).ne'
  have hI := (condNorm_pos hpos (insert e F) target).ne'
  field_simp

lemma condProbBit_eq_closed_or_one_sub (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (target : ConfigSpace E) (e : E) :
    condProbBit μ F target e (target e) =
      if target e then 1 - condProbClosed μ F target e
      else condProbClosed μ F target e := by
  by_cases hb : target e
  · simp only [hb, if_true]
    have hsum := condProbBit_true_add_false μ F target e
      (condNorm_pos hpos F target).ne'
    unfold condProbClosed
    linarith
  · simp only [hb, Bool.false_eq_true, if_false]
    rfl

theorem condObservable_split (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (seed : ConfigSpace E)
    (g : ConfigSpace E → ℝ) (e : E) (he : e ∉ F) :
    condObservable μ F seed g =
      bitWeight (condProbClosed μ F seed e) false *
          condObservable μ (insert e F) (Function.update seed e false) g +
        bitWeight (condProbClosed μ F seed e) true *
          condObservable μ (insert e F) (Function.update seed e true) g := by
  unfold condObservable
  rw [baseSum_split F seed
    (fun target => g target * condMass μ F target target) e he]
  have hbranch (b : Bool) :
      baseSum (insert e F) (Function.update seed e b)
          (fun target => g target * condMass μ F target target) =
        bitWeight (condProbClosed μ F seed e) b *
          baseSum (insert e F) (Function.update seed e b)
            (fun target => g target *
              condMass μ (insert e F) target target) := by
    unfold baseSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    by_cases hA : Agree (insert e F) (Function.update seed e b) target
    · have hbit : target e = b := by
        have h := hA e (Finset.mem_insert_self e F)
        simpa using h
      have hag : Agree F seed target := by
        intro x hx
        have hxe : x ≠ e := fun hxe => he (hxe ▸ hx)
        have h := hA x (Finset.mem_insert_of_mem hx)
        rw [Function.update_of_ne hxe] at h
        exact h
      have hq : condProbClosed μ F target e = condProbClosed μ F seed e :=
        condProbClosed_congr μ F target seed e (fun x hx => hag x hx)
      simp only [hA, if_true]
      rw [condMass_chain_step μ hpos F target e he]
      rw [condProbBit_eq_closed_or_one_sub μ hpos F target e, hbit, hq]
      cases b <;> simp [bitWeight] <;> ring
    · simp [hA]
  rw [hbranch false, hbranch true]

theorem condObservable_empty_eq_mean (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (g : ConfigSpace E → ℝ)
    (seed : ConfigSpace E) :
    condObservable μ ∅ seed g = Lindeberg.mean μ g := by
  unfold condObservable baseSum Lindeberg.mean condMass
  apply Finset.sum_congr rfl
  intro target _
  simp [Agree, condNorm_empty, hμ1]

theorem baseSum_flip_condMass_eq_flipBaseProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (seed : ConfigSpace E) (z : E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base =>
      (if tripleModeAt S base z = .flip then 1 else 0) *
        condMass μ F base base) = flipBaseProb μ F seed z S := by
  induction S generalizing F seed with
  | done => simp [baseSum, tripleModeAt, flipBaseProb]
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      by_cases hze : z = e
      · subst z
        by_cases hm : mode = .flip
        · subst mode
          simp only [tripleModeAt, if_pos rfl, if_true, one_mul]
          rw [baseSum_condMass_self_eq_one μ hpos F seed]
          simp [flipBaseProb]
        · have hm' : mode ≠ TripleMode.flip := hm
          simp only [tripleModeAt, if_pos rfl, hm', if_false, zero_mul]
          simp [baseSum, flipBaseProb, hm']
      · rw [baseSum_split F seed (fun base =>
          (if tripleModeAt (.node e he mode closed opened) base z = .flip
            then 1 else 0) * condMass μ F base base) e heF]
        have hbranch (b : Bool) :
            baseSum (insert e F) (Function.update seed e b)
                (fun base =>
                  (if tripleModeAt (.node e he mode closed opened) base z = .flip
                    then 1 else 0) * condMass μ F base base) =
              bitWeight (condProbClosed μ F seed e) b *
                baseSum (insert e F) (Function.update seed e b)
                  (fun base =>
                    (if tripleModeAt (if b then opened else closed) base z = .flip
                      then 1 else 0) *
                      condMass μ (insert e F) base base) := by
          unfold baseSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro base _
          by_cases hA : Agree (insert e F) (Function.update seed e b) base
          · have hbit : base e = b := by
              have h := hA e (Finset.mem_insert_self e F)
              simpa using h
            have hag : Agree F seed base := by
              intro x hx
              have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
              have h := hA x (Finset.mem_insert_of_mem hx)
              rw [Function.update_of_ne hxe] at h
              exact h
            have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
              condProbClosed_congr μ F base seed e (fun x hx => hag x hx)
            simp only [hA, if_true]
            rw [condMass_chain_step μ hpos F base e heF]
            rw [condProbBit_eq_closed_or_one_sub μ hpos F base e, hbit, hq]
            cases b
            · by_cases hm : tripleModeAt closed base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, bitWeight, mul_assoc]
            · by_cases hm : tripleModeAt opened base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, bitWeight, mul_assoc]
          · simp [hA]
        rw [hbranch false, hbranch true]
        simp only [Bool.false_eq_true, if_false, if_true]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp [flipBaseProb, hze]

theorem flipBaseProb_empty_eq_mean_flip
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (seed : ConfigSpace E) (z : E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    flipBaseProb μ ∅ seed z S =
      Lindeberg.mean μ (fun base =>
        if tripleModeAt S base z = .flip then 1 else 0) := by
  rw [← baseSum_flip_condMass_eq_flipBaseProb μ hpos ∅ seed z S (by simp)]
  unfold baseSum Lindeberg.mean condMass
  apply Finset.sum_congr rfl
  intro base _
  simp [Agree, condNorm_empty, hμ1]

theorem flipBaseProb_extendDecisionTreeTriple_eq_mean_sharedStep
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (seed : ConfigSpace E) (t : ℕ) (z : E) :
    flipBaseProb μ ∅ seed z
        (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) =
      Lindeberg.mean μ (fun base => sharedStepIndicator T base t z) := by
  rw [flipBaseProb_empty_eq_mean_flip μ hpos hμ1 seed z]
  unfold Lindeberg.mean
  apply Finset.sum_congr rfl
  intro base _
  change (if tripleModeAt
      (extendDecisionTreeTriple (some t) T seed Finset.univ) base z = .flip
      then 1 else 0) * μ base = sharedStepIndicator T base t z * μ base
  rw [sharedStepIndicator_eq_tripleFlipIndicator]
  unfold tripleFlipIndicator
  rw [extendDecisionTreeTriple_univ_seed_congr (some t) T base seed]

theorem targetProb_eq_condMass_core (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (base target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) (hR : R = Finset.univ \ F) :
    targetProb μ F base target S = condMass μ F target target := by
  induction S generalizing F base with
  | done =>
      have hFu : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold targetProb condMass
      rw [if_pos (agree_self Finset.univ target), condNorm_univ]
      field_simp [(hpos target).ne']
  | @node R e he active closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [targetProb]
      rw [ihc (insert e F) (Function.update base e false) hchild]
      rw [iho (insert e F) (Function.update base e true) hchild]
      rw [← add_mul, splitWeight_sum_base]
      unfold bitWeight
      rw [← condProbBit_eq_closed_or_one_sub μ hpos F target e]
      exact (condMass_chain_step μ hpos F target e heF).symm




theorem flipTripleProb_right_marginal_extendDecisionTreeTriple
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (driver left rightSeed : ConfigSpace E) (z : E)
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hR : R = Finset.univ \ F) :
    baseSum F rightSeed (fun right =>
      flipTripleProb μ F driver left right z
        (extendDecisionTreeTriple (some t) T known R)) =
      condMass μ F left left *
        flipBaseProb μ F driver z
          (extendDecisionTreeTriple (some t) T known R) := by
  induction T generalizing t F driver rightSeed known R with
  | leaf b => simp [extendDecisionTreeTriple, baseSum]
  | node q opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases hqR : q ∈ R
      · rw [dif_pos hqR]
        have hqF : q ∉ F := by
          intro hqF
          have : q ∈ Finset.univ \ F := by rw [← hR]; exact hqR
          exact (Finset.mem_sdiff.mp this).2 hqF
        have hchild : R.erase q = Finset.univ \ insert q F := by
          rw [hR]
          ext x
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_insert]
          tauto
        cases t with
        | zero =>
            by_cases hzq : z = q
            · subst z
              simp only [flipTripleProb, if_pos rfl, if_true, flipBaseProb, one_mul]
              rw [baseSum_tripleProb_right_eq_targetProb μ hpos F driver left rightSeed
                (.node q hqR .flip
                  (extendDecisionTreeTriple none closed
                    (Function.update known q false) (R.erase q))
                  (extendDecisionTreeTriple none opened
                    (Function.update known q true) (R.erase q))) hR]
              rw [targetProb_eq_condMass_core μ hpos F driver left]
              · ring
              · exact hR
            · simp [flipTripleProb, flipBaseProb, hzq, baseSum]
        | succ t =>
            by_cases hzq : z = q
            · simp [flipTripleProb, flipBaseProb, hzq, baseSum]
            · rw [baseSum_split F rightSeed (fun right =>
                flipTripleProb μ F driver left right z
                  (.node q hqR .before
                    (extendDecisionTreeTriple (some t) closed
                      (Function.update known q false) (R.erase q))
                    (extendDecisionTreeTriple (some t) opened
                      (Function.update known q true) (R.erase q)))) q hqF]
              have hbranch (b : Bool) :
                  baseSum (insert q F) (Function.update rightSeed q b)
                    (fun right => flipTripleProb μ F driver left right z
                      (.node q hqR .before
                        (extendDecisionTreeTriple (some t) closed
                          (Function.update known q false) (R.erase q))
                        (extendDecisionTreeTriple (some t) opened
                          (Function.update known q true) (R.erase q)))) =
                    overlapWeight (condProbClosed μ F left q)
                        (condProbClosed μ F rightSeed q) (left q) b *
                      (bitWeight (condProbClosed μ F driver q) false *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => flipTripleProb μ (insert q F)
                            (Function.update driver q false) left right z
                            (extendDecisionTreeTriple (some t) closed
                              (Function.update known q false) (R.erase q))) +
                       bitWeight (condProbClosed μ F driver q) true *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => flipTripleProb μ (insert q F)
                            (Function.update driver q true) left right z
                            (extendDecisionTreeTriple (some t) opened
                              (Function.update known q true) (R.erase q)))) := by
                unfold baseSum
                rw [mul_add]
                simp_rw [Finset.mul_sum]
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro right _
                by_cases hA : Agree (insert q F) (Function.update rightSeed q b) right
                · have hbit : right q = b := by
                    have h := hA q (Finset.mem_insert_self q F)
                    simpa using h
                  have hag : Agree F rightSeed right := by
                    intro x hx
                    have hxq : x ≠ q := fun hxq => hqF (hxq ▸ hx)
                    have h := hA x (Finset.mem_insert_of_mem hx)
                    rw [Function.update_of_ne hxq] at h
                    exact h
                  have hr : condProbClosed μ F right q =
                      condProbClosed μ F rightSeed q :=
                    condProbClosed_congr μ F right rightSeed q (fun x hx => hag x hx)
                  simp only [hA, if_true]
                  rw [flipTripleProb, hr, hbit]
                  simp [tripleWeight, hzq, mul_add, mul_assoc]
                  ring
                · simp [hA]
              rw [hbranch false, hbranch true]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update rightSeed q false) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update rightSeed q false) t (Function.update known q true)
                (R.erase q) hchild]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update rightSeed q true) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update rightSeed q true) t (Function.update known q true)
                (R.erase q) hchild]
              have hchain := condMass_chain_step μ hpos F left q hqF
              rw [condProbBit_eq_closed_or_one_sub μ hpos F left q] at hchain
              simp only [flipBaseProb, hzq, if_false, bitWeight]
              rw [← add_mul]
              rw [overlapWeight_sum_target]
              by_cases hlq : left q <;> simp [hlq, bitWeight] at hchain ⊢ <;>
                rw [hchain] <;> ring
      · rw [dif_neg hqR]
        by_cases hkq : known q
        · simp only [hkq, if_true]
          exact iho F driver rightSeed t known R hR
        · simp only [hkq, Bool.false_eq_true, if_false]
          exact ihc F driver rightSeed t known R hR




theorem pathProb_eq_condMass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (driver target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) (hR : R = Finset.univ \ F) :
    pathProb μ F driver target S = condMass μ F target target := by
  induction S generalizing F with
  | done =>
      have hFu : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold pathProb condMass
      rw [if_pos (agree_self Finset.univ target), condNorm_univ]
      field_simp [(hpos target).ne']
  | @node R e he independent closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      have hrec :
          (if driver e then
              pathProb μ (insert e F) driver target opened
            else pathProb μ (insert e F) driver target closed) =
            condMass μ (insert e F) target target := by
        by_cases hb : driver e
        · simp only [hb, if_true]
          exact iho (insert e F) hchild
        · simp only [hb, Bool.false_eq_true, if_false]
          exact ihc (insert e F) hchild
      rw [pathProb, hrec]
      have hw : bitWeight (condProbClosed μ F target e) (target e) =
          condProbBit μ F target e (target e) := by
        rw [condProbBit_eq_closed_or_one_sub μ hpos F target e]
        rfl
      rw [hw]
      exact (condMass_chain_step μ hpos F target e heF).symm

theorem pathProb_empty_eq_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (driver target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    pathProb μ ∅ driver target S = μ target := by
  rw [pathProb_eq_condMass μ hpos ∅ driver target S (by simp)]
  unfold condMass
  rw [if_pos (agree_self ∅ target), condNorm_empty, hμ1]
  ring


theorem jointProb_allIndependent_empty_eq_mul_mass
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (base target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    jointProb μ ∅ base target (allIndependent S) = μ base * μ target := by
  rw [jointProb_allIndependent_eq_mul_pathProb]
  rw [pathProb_empty_eq_mass μ hpos hμ1, pathProb_empty_eq_mass μ hpos hμ1]

theorem jointProb_extendDecisionTreeAt_card_eq_mul_mass
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (base target : ConfigSpace E) :
    jointProb μ ∅ base target
        (extendDecisionTreeAt (Fintype.card E) T base (Finset.univ : Finset E)) =
      μ base * μ target := by
  rw [extendDecisionTreeAt_card_univ_eq_allIndependent]
  exact jointProb_allIndependent_empty_eq_mul_mass μ hpos hμ1 base target _


noncomputable def causalPairEnergy (μ : ConfigSpace E → ℝ)
    (T : DecisionTree E) (t : ℕ) : ℝ :=
  ∑ base, ∑ target, (T.evalR base - T.evalR target) ^ 2 *
    jointProb μ ∅ base target
      (extendDecisionTreeAt t T base (Finset.univ : Finset E))

theorem causalPairEnergy_zero (μ : ConfigSpace E → ℝ) (T : DecisionTree E) :
    causalPairEnergy μ T 0 = 0 := by
  unfold causalPairEnergy
  apply Finset.sum_eq_zero
  intro base _
  apply Finset.sum_eq_zero
  intro target _
  rw [extendDecisionTreeAt_zero]
  by_cases hj : jointProb μ ∅ base target
      (extendDecisionTree T base (Finset.univ : Finset E)) = 0
  · rw [hj, mul_zero]
  · have hjAt : jointProb μ ∅ base target
        (extendDecisionTreeAt 0 T base (Finset.univ : Finset E)) ≠ 0 := by
        simpa [extendDecisionTreeAt_zero] using hj
    have heval := jointProb_zero_support_univ μ T base target hjAt
    unfold DecisionTree.evalR
    rw [heval, sub_self, zero_pow (by norm_num), zero_mul]

theorem causalPairEnergy_card_eq_two_var
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) :
    causalPairEnergy μ T (Fintype.card E) = 2 * Lindeberg.var μ T.evalR := by
  unfold causalPairEnergy
  simp_rw [jointProb_extendDecisionTreeAt_card_eq_mul_mass μ hpos hμ1 T]
  have hreorder :
      (∑ base, ∑ target, (T.evalR base - T.evalR target) ^ 2 *
          (μ base * μ target)) =
        ∑ base, ∑ target, μ base * μ target *
          (T.evalR base - T.evalR target) ^ 2 := by
    apply Finset.sum_congr rfl
    intro base _
    apply Finset.sum_congr rfl
    intro target _
    ring
  rw [hreorder]
  rw [Lindeberg.var_eq_double_sum μ hμ1 T.evalR]
  ring



theorem causalPairEnergy_succ_sub (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (T : DecisionTree E) (t : ℕ) :
    causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t =
      ∑ base, ∑ left, ∑ right,
        ((T.evalR base - T.evalR right) ^ 2 -
          (T.evalR base - T.evalR left) ^ 2) *
        tripleJointProb μ ∅ base left right
          (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) := by
  have hleft :
      (∑ base, ∑ left, ∑ right,
          (T.evalR base - T.evalR left) ^ 2 *
            tripleJointProb μ ∅ base left right
              (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E))) =
        causalPairEnergy μ T t := by
    unfold causalPairEnergy
    apply Finset.sum_congr rfl
    intro base _
    apply Finset.sum_congr rfl
    intro left _
    rw [← Finset.mul_sum]
    rw [sum_tripleJointProb_right_eq_jointProb μ hpos base left base]
    rw [extendDecisionTreeTriple_leftOrder]
  have hright :
      (∑ base, ∑ left, ∑ right,
          (T.evalR base - T.evalR right) ^ 2 *
            tripleJointProb μ ∅ base left right
              (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E))) =
        causalPairEnergy μ T (t + 1) := by
    unfold causalPairEnergy
    apply Finset.sum_congr rfl
    intro base _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro right _
    rw [← Finset.mul_sum]
    rw [sum_tripleJointProb_left_eq_jointProb μ hpos base right base]
    rw [extendDecisionTreeTriple_rightOrder]
  rw [← hright, ← hleft]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro base _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro right _
  ring

lemma evalR_sqdiff_sub_sqdiff_le_abs (T : DecisionTree E)
    (base left right : ConfigSpace E) :
    (T.evalR base - T.evalR right) ^ 2 -
        (T.evalR base - T.evalR left) ^ 2 ≤
      |T.evalR right - T.evalR left| := by
  unfold DecisionTree.evalR
  cases hb : T.eval base <;> cases hl : T.eval left <;> cases hr : T.eval right <;>
    norm_num

lemma tripleJointProb_nonneg (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    0 ≤ tripleJointProb μ ∅ base left right S := by
  rw [← pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb
    μ hpos S base left right]
  exact ENNReal.toReal_nonneg

theorem causalPairEnergy_succ_sub_le_abs
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) :
    causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤
      ∑ base, ∑ left, ∑ right, |T.evalR right - T.evalR left| *
        tripleJointProb μ ∅ base left right
          (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) := by
  rw [causalPairEnergy_succ_sub μ hpos T t]
  apply Finset.sum_le_sum
  intro base _
  apply Finset.sum_le_sum
  intro left _
  apply Finset.sum_le_sum
  intro right _
  exact mul_le_mul_of_nonneg_right
    (evalR_sqdiff_sub_sqdiff_le_abs T base left right)
    (tripleJointProb_nonneg μ hpos _ base left right)

noncomputable def causalAbsJump (μ : ConfigSpace E → ℝ)
    (T : DecisionTree E) (t : ℕ) : ℝ :=
  ∑ base, ∑ left, ∑ right, |T.evalR right - T.evalR left| *
    tripleJointProb μ ∅ base left right
      (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E))



theorem tree_osss_of_causal_step_bound
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (hStep : ∀ t < Fintype.card E,
      causalAbsJump μ T t ≤
        2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
          Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) :
    Lindeberg.var μ T.evalR ≤
      ∑ e, LindebergTree.revealmentMu μ T e *
        Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
  have hinc : ∀ t < Fintype.card E,
      causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤
        2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
          Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) := by
    intro t ht
    exact (causalPairEnergy_succ_sub_le_abs μ hpos T t).trans (hStep t ht)
  have hsum := Finset.sum_le_sum (fun t ht => hinc t (Finset.mem_range.mp ht))
  have hleft :
      ∑ t ∈ Finset.range (Fintype.card E),
          (causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t) =
        2 * Lindeberg.var μ T.evalR := by
    rw [Finset.sum_range_sub]
    rw [causalPairEnergy_zero, causalPairEnergy_card_eq_two_var μ hpos hμ1]
    ring
  have hright :
      ∑ t ∈ Finset.range (Fintype.card E),
          2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
            Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) =
        2 * ∑ e, LindebergTree.revealmentMu μ T e *
          Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_comm]
    apply congrArg (fun x : ℝ => 2 * x)
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.mul_sum]
    rw [sum_mean_sharedStepIndicator_eq_revealmentMu]
    ring
  rw [hleft, hright] at hsum
  linarith



theorem tripleJoint_left_energy_eq_causalPairEnergy
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (seed : ConfigSpace E) :
    let S := extendDecisionTreeTriple (some t) T seed
      (Finset.univ : Finset E)
    ∑ base, ∑ left, ∑ right,
        (T.evalR base - T.evalR left) ^ 2 *
          tripleJointProb μ ∅ base left right S =
      causalPairEnergy μ T t := by
  dsimp only
  unfold causalPairEnergy
  apply Finset.sum_congr rfl
  intro base _
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.mul_sum]
  have hm := baseSum_tripleJointProb_right_eq_jointProb
    μ hpos ∅ base left seed
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) (by simp)
  have hm' : ∑ right, tripleJointProb μ ∅ base left right
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) =
        jointProb μ ∅ base left
          (extendDecisionTreeTriple (some t) T seed
            (Finset.univ : Finset E)).leftOrder := by
    simpa [baseSum, Agree] using hm
  rw [hm']
  rw [extendDecisionTreeTriple_leftOrder]
  rw [extendDecisionTreeAt_univ_seed_congr t T seed base]



theorem tripleJoint_right_energy_eq_causalPairEnergy
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (seed : ConfigSpace E) :
    let S := extendDecisionTreeTriple (some t) T seed
      (Finset.univ : Finset E)
    ∑ base, ∑ left, ∑ right,
        (T.evalR base - T.evalR right) ^ 2 *
          tripleJointProb μ ∅ base left right S =
      causalPairEnergy μ T (t + 1) := by
  dsimp only
  unfold causalPairEnergy
  apply Finset.sum_congr rfl
  intro base _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  rw [← Finset.mul_sum]
  have hm := baseSum_tripleJointProb_left_eq_jointProb
    μ hpos ∅ base right seed
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) (by simp)
  have hm' : ∑ left, tripleJointProb μ ∅ base left right
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) =
        jointProb μ ∅ base right
          (extendDecisionTreeTriple (some t) T seed
            (Finset.univ : Finset E)).rightOrder := by
    simpa [baseSum, Agree] using hm
  rw [hm']
  rw [extendDecisionTreeTriple_rightOrder]
  rw [extendDecisionTreeAt_univ_seed_congr (t + 1) T seed base]

noncomputable def causalTripleJump (μ : ConfigSpace E → ℝ)
    (T : DecisionTree E) (t : ℕ) (seed : ConfigSpace E) : ℝ :=
  let S := extendDecisionTreeTriple (some t) T seed
    (Finset.univ : Finset E)
  ∑ base, ∑ left, ∑ right,
    |T.evalR right - T.evalR left| * tripleJointProb μ ∅ base left right S

lemma evalR_pair_energy_diff_le_abs (T : DecisionTree E)
    (base left right : ConfigSpace E) :
    (T.evalR base - T.evalR right) ^ 2 -
        (T.evalR base - T.evalR left) ^ 2 ≤
      |T.evalR right - T.evalR left| := by
  unfold DecisionTree.evalR
  cases hb : T.eval base <;> cases hl : T.eval left <;>
    cases hr : T.eval right <;> simp [hb, hl, hr] <;> norm_num




lemma abs_evalR_sub_eq_disagreement (T : DecisionTree E)
    (left right : ConfigSpace E) :
    |T.evalR right - T.evalR left| =
      T.evalR right + T.evalR left - 2 * T.evalR right * T.evalR left := by
  unfold DecisionTree.evalR
  cases hl : T.eval left <;> cases hr : T.eval right <;>
    simp [hl, hr] <;> norm_num


theorem causalTripleJump_eq_disagreement
    (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (t : ℕ)
    (seed : ConfigSpace E) :
    causalTripleJump μ T t seed =
      let S := extendDecisionTreeTriple (some t) T seed
        (Finset.univ : Finset E)
      ∑ base, ∑ left, ∑ right,
        (T.evalR right + T.evalR left -
          2 * T.evalR right * T.evalR left) *
            tripleJointProb μ ∅ base left right S := by
  unfold causalTripleJump
  simp_rw [abs_evalR_sub_eq_disagreement]



theorem causalPairEnergy_sub_le_causalTripleJump
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (seed : ConfigSpace E) :
    causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤
      causalTripleJump μ T t seed := by
  rw [← tripleJoint_right_energy_eq_causalPairEnergy μ hpos T t seed]
  rw [← tripleJoint_left_energy_eq_causalPairEnergy μ hpos T t seed]
  unfold causalTripleJump
  simp only
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro base _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro left _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro right _
  rw [← sub_mul]
  exact mul_le_mul_of_nonneg_right
    (evalR_pair_energy_diff_le_abs T base left right)
    (tripleJointProb_nonneg μ hpos _ base left right)



theorem two_var_le_sum_causalTripleJump
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) (seed : ConfigSpace E) :
    2 * Lindeberg.var μ T.evalR ≤
      ∑ t ∈ Finset.range (Fintype.card E), causalTripleJump μ T t seed := by
  have hsum :
      (∑ t ∈ Finset.range (Fintype.card E),
        (causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t)) ≤
      ∑ t ∈ Finset.range (Fintype.card E), causalTripleJump μ T t seed :=
    Finset.sum_le_sum fun t _ =>
      causalPairEnergy_sub_le_causalTripleJump μ hpos T t seed
  rw [Finset.sum_range_sub (fun t => causalPairEnergy μ T t) (Fintype.card E)] at hsum
  rw [causalPairEnergy_zero, causalPairEnergy_card_eq_two_var μ hpos hμ1] at hsum
  simpa using hsum




theorem adaptive_tree_osss_of_causalTripleJump_le
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) (seed : ConfigSpace E)
    (hjump : ∀ t < Fintype.card E,
      causalTripleJump μ T t seed ≤
        2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
          Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) :
    Lindeberg.var μ T.evalR ≤
      ∑ e, LindebergTree.revealmentMu μ T e *
        Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
  have htel := two_var_le_sum_causalTripleJump μ hpos hμ1 T seed
  have hsteps :
      (∑ t ∈ Finset.range (Fintype.card E), causalTripleJump μ T t seed) ≤
        ∑ t ∈ Finset.range (Fintype.card E),
          2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
            Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) :=
    Finset.sum_le_sum fun t ht => hjump t (Finset.mem_range.mp ht)
  have hmain := htel.trans hsteps
  have hreorder :
      (∑ t ∈ Finset.range (Fintype.card E),
          2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
            Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) =
        2 * ∑ e, LindebergTree.revealmentMu μ T e *
          Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    apply congrArg (fun z : ℝ => 2 * z)
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.mul_sum]
    rw [sum_mean_sharedStepIndicator_eq_revealmentMu]
    ring
  rw [hreorder] at hmain
  linarith





theorem targetProb_eq_condMass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (base target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) (hR : R = Finset.univ \ F) :
    targetProb μ F base target S = condMass μ F target target := by
  induction S generalizing F base with
  | done =>
      have hFu : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold targetProb condMass
      rw [if_pos (agree_self Finset.univ target), condNorm_univ]
      field_simp [(hpos target).ne']
  | @node R e he active closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [targetProb]
      rw [ihc (insert e F) (Function.update base e false) hchild]
      rw [iho (insert e F) (Function.update base e true) hchild]
      rw [← add_mul, splitWeight_sum_base]
      unfold bitWeight
      rw [← condProbBit_eq_closed_or_one_sub μ hpos F target e]
      exact (condMass_chain_step μ hpos F target e heF).symm


theorem targetProb_empty_eq_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (base target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    targetProb μ ∅ base target S = μ target := by
  rw [targetProb_eq_condMass μ hpos ∅ base target S (by simp)]
  unfold condMass
  rw [if_pos]
  · rw [condNorm_empty, hμ1]
    ring
  · exact agree_self ∅ target

theorem sum_tripleProb_right_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base left seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ right, tripleProb μ ∅ base left right S = μ left := by
  have h := baseSum_tripleProb_right_eq_targetProb μ hpos ∅ base left seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base left S.leftOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_tripleProb_left_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base right seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ left, tripleProb μ ∅ base left right S = μ right := by
  have h := baseSum_tripleProb_left_eq_targetProb μ hpos ∅ base right seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base right S.rightOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_crossTripleProb_right_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base left seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ right, crossTripleProb μ ∅ base left right S = μ left := by
  have h := baseSum_crossTripleProb_right_eq_targetProb μ hpos ∅ base left seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base left S.leftOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_crossTripleProb_left_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base right seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ left, crossTripleProb μ ∅ base left right S = μ right := by
  have h := baseSum_crossTripleProb_left_eq_targetProb μ hpos ∅ base right seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base right S.rightOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_jointProb_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base, jointProb μ ∅ base target S = μ target := by
  rw [sum_jointProb_empty_eq_targetProb μ seed target S]
  exact targetProb_empty_eq_mass μ hpos hμ1 seed target S

theorem sum_frozenCodeAtom_mass_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base,
      (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal = μ target := by
  simp_rw [pairedCube_frozenCodeAtom_toReal_eq_jointProb μ hpos]
  exact sum_jointProb_empty_eq_mass μ hpos hμ1 seed target S

theorem sum_frozenCodeAtom_observable_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (seed : ConfigSpace E) (S : CausalOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ℝ) :
    ∑ base, ∑ target, g target *
      (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal =
        Lindeberg.mean μ g := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Finset.mul_sum]
  rw [sum_frozenCodeAtom_mass_eq_mass μ hpos hμ1 seed target S]


theorem sum_targetProb_eq_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (base : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetProb μ ∅ base target S =
      Lindeberg.mean μ g := by
  simp_rw [targetProb_empty_eq_mass μ hpos hμ1 base]
  rfl


theorem targetIntegral_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base target : ConfigSpace E) (S : CausalOrder (Finset.univ : Finset E)) :
    targetIntegral μ ∅ base target S = μ target := by
  rw [targetIntegral_eq_targetProb μ hpos]
  exact targetProb_empty_eq_mass μ hpos hμ1 base target S


theorem sum_diag_targetIntegral_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base : ConfigSpace E) (S : CausalOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetIntegral μ ∅ base target S =
      Lindeberg.mean μ g := by
  simp_rw [targetIntegral_empty_eq_mass μ hpos hμ1 base]
  rfl



theorem decisionTree_mixed_targetIntegral_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) (base target : ConfigSpace E) :
    targetIntegral μ ∅ base target
      (extendDecisionTree T base (Finset.univ : Finset E)) = μ target :=
  targetIntegral_empty_eq_mass μ hpos hμ1 base target _


theorem decisionTree_mixed_diag_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) (base : ConfigSpace E) (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetIntegral μ ∅ base target
      (extendDecisionTree T base (Finset.univ : Finset E)) = Lindeberg.mean μ g :=
  sum_diag_targetIntegral_eq_mean μ hpos hμ1 base _ g


theorem decisionTreeAt_mixed_targetIntegral_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (t : ℕ) (T : DecisionTree E) (base target : ConfigSpace E) :
    targetIntegral μ ∅ base target
      (extendDecisionTreeAt t T base (Finset.univ : Finset E)) = μ target :=
  targetIntegral_empty_eq_mass μ hpos hμ1 base target _


theorem decisionTreeAt_mixed_diag_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (t : ℕ) (T : DecisionTree E) (base : ConfigSpace E) (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetIntegral μ ∅ base target
      (extendDecisionTreeAt t T base (Finset.univ : Finset E)) = Lindeberg.mean μ g :=
  sum_diag_targetIntegral_eq_mean μ hpos hμ1 base _ g



noncomputable def fiberAbsStep (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) : ℝ :=
  ∫ V, |f (codeMap μ (σ : Fin n → E) (GrandCoupling.Wt U V t))
      - f (codeMap μ (σ : Fin n → E) (GrandCoupling.Wt U V (t - 1)))|
    ∂(GrandCoupling.Vcube n)

noncomputable def fiberObservable (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (U : Fin n → ℝ) (s : ℕ) : ℝ :=
  ∫ V, g (codeMap μ (σ : Fin n → E) (GrandCoupling.Wt U V s))
    ∂(GrandCoupling.Vcube n)




theorem integral_eq_sum_fibre {α β : Type*} [MeasurableSpace α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : Measure α) [IsFiniteMeasure ν] (φ : α → β) (hφ : Measurable φ)
    (g : β → ℝ) :
    (∫ x, g (φ x) ∂ν) = ∑ y, g y * (ν {x | φ x = y}).toReal := by
  have hms : ∀ y : β, MeasurableSet {x : α | φ x = y} :=
    fun y => hφ (measurableSet_singleton y)
  have hpoint : (fun x => g (φ x)) =
      (fun x => ∑ y, g y * Set.indicator {x' | φ x' = y} (fun _ => (1 : ℝ)) x) := by
    funext x
    rw [Finset.sum_eq_single (φ x)]
    · rw [Set.indicator_of_mem (by simp)]
      ring
    · intro y _ hy
      rw [Set.indicator_of_notMem]
      · ring
      · simpa only [Set.mem_setOf_eq] using Ne.symm hy
    · simp
  rw [hpoint, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hms y),
      smul_eq_mul, mul_one]
    rfl
  · intro y _
    exact Integrable.const_mul
      (Integrable.indicator (integrable_const (1 : ℝ)) (hms y)) _




theorem pairedCube_causal_integral_eq_atom_sum (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        g (pairedCausalOutputs mu S base z).2.1
          (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        (pairedCube (Fintype.card E)
          (frozenTripleCodeAtom mu S base left right)).toReal := by
  letI : IsFiniteMeasure (pairedCube (Fintype.card E)) :=
    ⟨by rw [pairedCube, Measure.pi_univ]; simp⟩
  rw [integral_eq_sum_fibre (pairedCube (Fintype.card E))
    (pairedCausalOutputs mu S base) (measurable_pairedCausalOutputs mu S base)
    (fun y => if y.1 = base then g y.2.1 y.2.2 else 0)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single base]
  · simp only [if_pos]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right _
    rw [pairedCausalOutputs_fibre]
  · intro b _ hne
    simp [hne]
  · simp


theorem pairedCube_causal_integral_eq_tripleJointProb
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        g (pairedCausalOutputs mu S base z).2.1
          (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        tripleJointProb mu ∅ base left right S := by
  rw [pairedCube_causal_integral_eq_atom_sum]
  simp_rw [pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb mu hpos]



theorem tripleCube_causal_integral_eq_atom_sum (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then
        g (tripleCausalOutputs μ S base z).2.1
          (tripleCausalOutputs μ S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        (tripleCube (Fintype.card E)
          (frozenCrossCodeAtom μ S base left right)).toReal := by
  letI : IsFiniteMeasure (tripleCube (Fintype.card E)) :=
    ⟨by rw [tripleCube, Measure.pi_univ]; simp⟩
  rw [integral_eq_sum_fibre (tripleCube (Fintype.card E))
    (tripleCausalOutputs μ S base) (measurable_tripleCausalOutputs μ S base)
    (fun y => if y.1 = base then g y.2.1 y.2.2 else 0)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single base]
  · simp only [if_pos]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right _
    rw [tripleCausalOutputs_fibre]
  · intro b _ hne
    simp [hne]
  · simp


theorem tripleCube_causal_integral_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then
        g (tripleCausalOutputs μ S base z).2.1
          (tripleCausalOutputs μ S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        crossTripleJointProb μ ∅ base left right S := by
  rw [tripleCube_causal_integral_eq_atom_sum]
  simp_rw [tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb μ hpos]


theorem pairedCube_causal_integral_pullback (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        g (pairedCausalOutputs mu S base z).2.1
          (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E))) =
    ∫ p, (if codeMap mu (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E) p.1 = base then
        g (codeMap mu (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.leftOrder base p.1 p.2))
          (codeMap mu (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.rightOrder base p.1 p.2)) else 0)
      ∂((GrandCoupling.Vcube (Fintype.card E)).prod
        (GrandCoupling.Vcube (Fintype.card E))) := by
  have hmp := pairedCube_measurePreserving (Fintype.card E)
  rw [← hmp.integral_comp' (fun p =>
    if codeMap mu (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E) p.1 = base then
      g (codeMap mu (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.leftOrder base p.1 p.2))
        (codeMap mu (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.rightOrder base p.1 p.2)) else 0)]
  rfl


theorem tripleCube_causal_integral_pullback (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then
        g (tripleCausalOutputs μ S base z).2.1
          (tripleCausalOutputs μ S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) =
    ∫ q, (if codeMap μ (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E) q.1.1 = base then
        g (codeMap μ (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.leftOrder base q.1.1 q.1.2))
          (codeMap μ (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.rightOrder base q.1.1 q.2)) else 0)
      ∂(((GrandCoupling.Vcube (Fintype.card E)).prod
        (GrandCoupling.Vcube (Fintype.card E))).prod
          (GrandCoupling.Vcube (Fintype.card E))) := by
  let G := fun q : ((Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ)) × (Fin (Fintype.card E) → ℝ) =>
    if codeMap μ (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E) q.1.1 = base then
      g (codeMap μ (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.leftOrder base q.1.1 q.1.2))
        (codeMap μ (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.rightOrder base q.1.1 q.2)) else 0
  change (∫ z, G (tripleCubeEquiv (Fintype.card E) z)
      ∂(tripleCube (Fintype.card E))) = _
  exact tripleCube_integral_equiv (Fintype.card E) G



theorem tripleCube_conditional_product {n : ℕ}
    (A : (Fin n → ℝ) → ℝ)
    (F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hAm : Measurable A) (hFm : Measurable (Function.uncurry F))
    (hGm : Measurable (Function.uncurry G))
    {CA CF CG : ℝ} (hAC : ∀ U, |A U| ≤ CA)
    (hFC : ∀ U V, |F U V| ≤ CF) (hGC : ∀ U V, |G U V| ≤ CG) :
    (∫ q, A q.1.1 * F q.1.1 q.1.2 * G q.1.1 q.2
      ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) =
      ∫ U, A U * (∫ V, F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n) := by
  have hCA0 : 0 ≤ CA := le_trans (abs_nonneg _) (hAC 0)
  have hCF0 : 0 ≤ CF := le_trans (abs_nonneg _) (hFC 0 0)
  let H := fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
    A q.1.1 * F q.1.1 q.1.2 * G q.1.1 q.2
  have hHm : Measurable H :=
    ((hAm.comp (measurable_fst.comp measurable_fst)).mul
      (hFm.comp measurable_fst)).mul
      (hGm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hHC : ∀ q, |H q| ≤ (CA * CF) * CG := by
    intro q
    simp only [H, abs_mul]
    exact mul_le_mul (mul_le_mul (hAC _) (hFC _ _) (abs_nonneg _) hCA0)
      (hGC _ _) (abs_nonneg _) (mul_nonneg hCA0 hCF0)
  have hHi : Integrable H (((GrandCoupling.Vcube n).prod
      (GrandCoupling.Vcube n)).prod (GrandCoupling.Vcube n)) :=
    StatMech.Probability.ContinuousFKG.integrable_of_bdd _ hHm hHC
  rw [show (fun q => A q.1.1 * F q.1.1 q.1.2 * G q.1.1 q.2) = H from rfl]
  rw [integral_prod H hHi]
  have hinner (p : (Fin n → ℝ) × (Fin n → ℝ)) :
      (∫ y, H (p, y) ∂(GrandCoupling.Vcube n)) =
        A p.1 * F p.1 p.2 * (∫ y, G p.1 y ∂(GrandCoupling.Vcube n)) := by
    simp only [H]
    rw [integral_const_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hK : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      A p.1 * F p.1 p.2 * (∫ V, G p.1 V ∂(GrandCoupling.Vcube n)))
      ((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
    have heq : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        A p.1 * F p.1 p.2 * (∫ V, G p.1 V ∂(GrandCoupling.Vcube n))) =
        (fun p => ∫ y, H (p, y) ∂(GrandCoupling.Vcube n)) := by
      funext p
      exact (hinner p).symm
    rw [heq]
    exact hHi.integral_prod_left
  rw [integral_prod _ hK]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro U
  change (∫ y, A U * F U y * (∫ V, G U V ∂(GrandCoupling.Vcube n))
      ∂(GrandCoupling.Vcube n)) = _
  rw [show (fun y => A U * F U y * (∫ V, G U V ∂(GrandCoupling.Vcube n))) =
      (fun y => (A U * (∫ V, G U V ∂(GrandCoupling.Vcube n))) * F U y) by
        funext y; ring]
  rw [integral_const_mul]
  ring



theorem tripleCube_product_le_pairedCube_product {mu : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < mu ω) (hmono : IsMonotonicMeasure mu)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf)
    {g : ConfigSpace E → ℝ} (hg : Monotone g) {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) :
    (∫ z, (if (tripleCausalOutputs mu S base z).1 = base then
        f (tripleCausalOutputs mu S base z).2.1 *
          g (tripleCausalOutputs mu S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) ≤
    ∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        f (pairedCausalOutputs mu S base z).2.1 *
          g (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E)) := by
  let n := Fintype.card E
  let σ := realizedEquiv S.leftOrder base
  let A : (Fin n → ℝ) → ℝ := fun U =>
    if codeMap mu (σ : Fin n → E) U = base then 1 else 0
  let F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun U V =>
    f (codeMap mu (σ : Fin n → E) (causalMixLabels S.leftOrder base U V))
  let G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun U V =>
    g (codeMap mu (σ : Fin n → E) (causalMixLabels S.rightOrder base U V))
  have hset : MeasurableSet {U : Fin n → ℝ |
      codeMap mu (σ : Fin n → E) U = base} :=
    (GrandCoupling.measurable_codeMap mu σ) (measurableSet_singleton base)
  have hAm : Measurable A := by
    unfold A
    exact Measurable.ite hset measurable_const measurable_const
  have hFm : Measurable (Function.uncurry F) :=
    (GrandCoupling.measurable_g_codeMap mu σ f).comp
      (measurable_causalMixLabels_prod S.leftOrder base)
  have hGm : Measurable (Function.uncurry G) :=
    (GrandCoupling.measurable_g_codeMap mu σ g).comp
      (measurable_causalMixLabels_prod S.rightOrder base)
  have hAC : ∀ U, |A U| ≤ (1 : ℝ) := by
    intro U
    unfold A
    split <;> norm_num
  have hFC : ∀ U V, |F U V| ≤ Cf := fun U V => hfC _
  have hGC : ∀ U V, |G U V| ≤ Cg := fun U V => hgC _
  have hcond := StatMech.Probability.fkg_second_block
    (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => A p.1 * F p.1 p.2)
    (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2)
    (hAm.comp measurable_fst |>.mul hFm) hGm
    (Cf := Cf) (Cg := Cg)
    (fun p => by
      rw [abs_mul]
      calc
        |A p.1| * |F p.1 p.2| ≤ 1 * |F p.1 p.2| :=
          mul_le_mul_of_nonneg_right (hAC _) (abs_nonneg _)
        _ ≤ Cf := by simpa using hFC p.1 p.2)
    (fun p => hGC p.1 p.2)
    (fun U V V' hVV => mul_le_mul_of_nonneg_left
      (hf (GrandCoupling.codeMap_mono_u hpos hmono _
        (causalMixLabels_mono_right S.leftOrder base U hVV))) (by
          unfold A
          split <;> norm_num))
    (fun U V V' hVV => hg (GrandCoupling.codeMap_mono_u hpos hmono _
      (causalMixLabels_mono_right S.rightOrder base U hVV)))
  have htriple := tripleCube_conditional_product A F G hAm hFm hGm hAC hFC hGC
  rw [tripleCube_causal_integral_pullback
    (g := fun left right => f left * g right)]
  rw [pairedCube_causal_integral_pullback
    (g := fun left right => f left * g right)]
  simp only [A, F, G, n, σ, ite_mul, one_mul, zero_mul] at htriple hcond ⊢
  rw [htriple]
  rw [StatMech.Probability.cube_eq] at hcond
  have hnorm :
      (∫ U, A U * (∫ V, F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n)) =
      ∫ U, (∫ V, A U * F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro U
    change (A U * (∫ V, F U V ∂(GrandCoupling.Vcube n))) *
      (∫ V, G U V ∂(GrandCoupling.Vcube n)) =
      (∫ V, A U * F U V ∂(GrandCoupling.Vcube n)) *
      (∫ V, G U V ∂(GrandCoupling.Vcube n))
    rw [integral_const_mul]
  have hcond' :
      (∫ U, (∫ V, A U * F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n)) ≤
      ∫ p, (A p.1 * F p.1 p.2) * G p.1 p.2
        ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
    simpa only [A, F, G, n, σ, ite_mul, one_mul, zero_mul] using hcond
  have hfinal := hnorm.trans_le hcond'
  simpa only [A, F, G, n, σ, ite_mul, one_mul, zero_mul] using hfinal



theorem no_flip_causal_atom_eq_zero
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (hno : ∀ e, tripleModeAt S base e ≠ .flip)
    (f : ConfigSpace E → ℝ) :
    (∑ left, ∑ right, |f right - f left| *
      tripleJointProb mu ∅ base left right S) = 0 := by
  rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
    (fun left right => |f right - f left|)]
  rw [pairedCube_causal_integral_pullback mu S base
    (fun left right => |f right - f left|)]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro p
  change (if codeMap mu (realizedEquiv S.leftOrder base :
      Fin (Fintype.card E) → E) p.1 = base then
    |f (codeMap mu (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E)
          (causalMixLabels S.rightOrder base p.1 p.2)) -
      f (codeMap mu (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E)
          (causalMixLabels S.leftOrder base p.1 p.2))| else 0) = 0
  have hlabels := causalMixLabels_leftOrder_eq_rightOrder_of_no_flip
    S base hno p.1 p.2
  rw [hlabels]
  simp


theorem decisionTree_flip_atom_step_le
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmono : IsMonotonicMeasure mu) (T : DecisionTree E) (t : ℕ)
    (hf : Monotone T.evalR) (base : ConfigSpace E) (e : E)
    (he : tripleModeAt
      (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip) :
    let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
    (∑ left, ∑ right, |T.evalR right - T.evalR left| *
        tripleJointProb mu ∅ base left right S) ≤
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right) *
            tripleJointProb mu ∅ base left right S) -
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            crossTripleJointProb mu ∅ base left right S) := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  have hcross₁ := tripleCube_product_le_pairedCube_product hpos hmono S base
    (f := T.evalR) hf (Cf := 1)
    (fun ω => by unfold DecisionTree.evalR; split <;> norm_num)
    (g := Lindeberg.coord e) (Lindeberg.coord_mono e) (Cg := 1)
    (GrandCoupling.abs_coord_le_one e)
  have hcross₂ := tripleCube_product_le_pairedCube_product hpos hmono S base
    (f := Lindeberg.coord e) (Lindeberg.coord_mono e) (Cf := 1)
    (GrandCoupling.abs_coord_le_one e)
    (g := T.evalR) hf (Cg := 1)
    (fun ω => by unfold DecisionTree.evalR; split <;> norm_num)
  have hc₁ :
      (∑ left, ∑ right, T.evalR left * Lindeberg.coord e right *
        crossTripleJointProb mu ∅ base left right S) ≤
      ∑ left, ∑ right, T.evalR left * Lindeberg.coord e right *
        tripleJointProb mu ∅ base left right S := by
    rw [← tripleCube_causal_integral_eq_crossTripleJointProb mu hpos S base
      (fun left right => T.evalR left * Lindeberg.coord e right)]
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => T.evalR left * Lindeberg.coord e right)]
    exact hcross₁
  have hc₂ :
      (∑ left, ∑ right, T.evalR right * Lindeberg.coord e left *
        crossTripleJointProb mu ∅ base left right S) ≤
      ∑ left, ∑ right, T.evalR right * Lindeberg.coord e left *
        tripleJointProb mu ∅ base left right S := by
    rw [← tripleCube_causal_integral_eq_crossTripleJointProb mu hpos S base
      (fun left right => T.evalR right * Lindeberg.coord e left)]
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => T.evalR right * Lindeberg.coord e left)]
    simpa [mul_comm] using hcross₂
  have hcommon :
      (∑ left, ∑ right, |T.evalR right - T.evalR left| *
        tripleJointProb mu ∅ base left right S) =
      ∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right -
          T.evalR left * Lindeberg.coord e right -
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S := by
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => |T.evalR right - T.evalR left|)]
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => T.evalR left * Lindeberg.coord e left +
        T.evalR right * Lindeberg.coord e right -
        T.evalR left * Lindeberg.coord e right -
        T.evalR right * Lindeberg.coord e left)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases hb : (pairedCausalOutputs mu S base z).1 = base
    · simp only [hb, if_true]
      exact causal_abs_eq_four_terms hpos hmono hf
        t T base (fun i => (z i).1) (fun i => (z i).2) e he
    · simp [hb]
  rw [hcommon]
  have hsplitCommon :
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right -
          T.evalR left * Lindeberg.coord e right -
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S) =
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right) *
            tripleJointProb mu ∅ base left right S) -
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro left _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro right _
    ring
  rw [hsplitCommon]
  have hcrossSum :
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            crossTripleJointProb mu ∅ base left right S) ≤
      ∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    exact add_le_add hc₁ hc₂
  linarith


theorem causal_fkg_cross_fiber {mu : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < mu ω) (hmono : IsMonotonicMeasure mu)
    (S₁ S₂ : CausalOrder (Finset.univ : Finset E))
    (base : ConfigSpace E) (σ : Fin (Fintype.card E) ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (e : E)
    (U : Fin (Fintype.card E) → ℝ) :
    (∫ V, f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₁ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E))) *
        (∫ V, Lindeberg.coord e
          (codeMap mu (σ : Fin (Fintype.card E) → E)
            (causalMixLabels S₂ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E))) ≤
      ∫ V, f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₁ base U V)) * Lindeberg.coord e
          (codeMap mu (σ : Fin (Fintype.card E) → E)
            (causalMixLabels S₂ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E)) := by
  refine StatMech.Probability.fkg_second_block_fiber
    (f := fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₁ base p.1 p.2)))
    (g := fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) => Lindeberg.coord e
        (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₂ base p.1 p.2)))
    ((GrandCoupling.measurable_g_codeMap mu σ f).comp
      (measurable_causalMixLabels_prod S₁ base))
    ((GrandCoupling.measurable_g_codeMap mu σ (Lindeberg.coord e)).comp
      (measurable_causalMixLabels_prod S₂ base))
    (Cf := Cf) (Cg := 1) (fun z => hfC _)
    (fun z => GrandCoupling.abs_coord_le_one e _) ?_ ?_ U
  · intro Ufix V V' hVV
    exact hf (GrandCoupling.codeMap_mono_u hpos hmono _
      (causalMixLabels_mono_right S₁ base Ufix hVV))
  · intro Ufix V V' hVV
    exact Lindeberg.coord_mono e (GrandCoupling.codeMap_mono_u hpos hmono _
      (causalMixLabels_mono_right S₂ base Ufix hVV))


theorem causal_abs_integral_fiber_le {mu : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < mu ω) (hmono : IsMonotonicMeasure mu)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) (T : DecisionTree E)
    (base : ConfigSpace E) (e : E)
    (he : tripleModeAt
      (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip)
    (U : Fin (Fintype.card E) → ℝ) :
    let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
    let σ := realizedEquiv S.leftOrder base
    let Yl := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base U V)
    let Yr := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base U V)
    (∫ V, |f (Yr V) - f (Yl V)| ∂(GrandCoupling.Vcube (Fintype.card E))) ≤
      (∫ V, f (Yl V) * Lindeberg.coord e (Yl V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) +
      (∫ V, f (Yr V) * Lindeberg.coord e (Yr V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yl V) ∂(GrandCoupling.Vcube (Fintype.card E))) *
        (∫ V, Lindeberg.coord e (Yr V)
          ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yr V) ∂(GrandCoupling.Vcube (Fintype.card E))) *
        (∫ V, Lindeberg.coord e (Yl V)
          ∂(GrandCoupling.Vcube (Fintype.card E))) := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  let σ := realizedEquiv S.leftOrder base
  let Yl := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
    (causalMixLabels S.leftOrder base U V)
  let Yr := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
    (causalMixLabels S.rightOrder base U V)
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  have hInt (C₁ C₂ : CausalOrder (Finset.univ : Finset E)) :
      Integrable (fun V =>
        f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C₁ base U V)) * Lindeberg.coord e
        (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C₂ base U V)))
        (GrandCoupling.Vcube (Fintype.card E)) := by
    refine StatMech.Probability.ContinuousFKG.integrable_of_bdd _
      (((GrandCoupling.measurable_g_codeMap mu σ f).comp
        (measurable_causalMixLabels_right C₁ base U)).mul
       ((GrandCoupling.measurable_g_codeMap mu σ (Lindeberg.coord e)).comp
        (measurable_causalMixLabels_right C₂ base U))) (C := Cf * 1) ?_
    intro V
    rw [abs_mul]
    exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _)
      (abs_nonneg _) hCf0
  have hEq : (∫ V, |f (Yr V) - f (Yl V)|
        ∂(GrandCoupling.Vcube (Fintype.card E))) =
      (∫ V, f (Yl V) * Lindeberg.coord e (Yl V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) +
      (∫ V, f (Yr V) * Lindeberg.coord e (Yr V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yl V) * Lindeberg.coord e (Yr V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yr V) * Lindeberg.coord e (Yl V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) := by
    let A := fun V => f (Yl V) * Lindeberg.coord e (Yl V)
    let B := fun V => f (Yr V) * Lindeberg.coord e (Yr V)
    let C := fun V => f (Yl V) * Lindeberg.coord e (Yr V)
    let D := fun V => f (Yr V) * Lindeberg.coord e (Yl V)
    have hpoint : ∀ V, |f (Yr V) - f (Yl V)| =
        A V + B V - C V - D V := by
      intro V
      exact causal_abs_eq_four_terms hpos hmono hf t T base U V e he
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    have hA : Integrable A (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.leftOrder S.leftOrder
    have hB : Integrable B (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.rightOrder S.rightOrder
    have hC : Integrable C (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.leftOrder S.rightOrder
    have hD : Integrable D (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.rightOrder S.leftOrder
    change (∫ V, (((A + B) - C) - D) V
      ∂(GrandCoupling.Vcube (Fintype.card E))) =
      (∫ V, A V ∂(GrandCoupling.Vcube (Fintype.card E))) +
      (∫ V, B V ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, C V ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, D V ∂(GrandCoupling.Vcube (Fintype.card E)))
    rw [integral_sub' ((hA.add hB).sub hC) hD]
    rw [integral_sub' (hA.add hB) hC]
    rw [integral_add' hA hB]
  rw [hEq]
  have hcross₁ := causal_fkg_cross_fiber hpos hmono S.leftOrder S.rightOrder
    base σ hf hfC e U
  have hcross₂ := causal_fkg_cross_fiber hpos hmono S.rightOrder S.leftOrder
    base σ hf hfC e U
  dsimp only [Yl, Yr] at hcross₁ hcross₂ ⊢
  linarith




theorem realized_step_fiber_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ)
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) (ht : 1 ≤ t)
    (htn : t - 1 < Fintype.card E) (U : Fin (Fintype.card E) → ℝ) :
    fiberAbsStep μ (realizedEquiv S base) f U t
      ≤ fiberObservable μ (realizedEquiv S base)
          (fun ω => f ω * Lindeberg.coord
            ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩) ω)
          U (t - 1)
        + fiberObservable μ (realizedEquiv S base)
          (fun ω => f ω * Lindeberg.coord
            ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩) ω)
          U t
        - fiberObservable μ (realizedEquiv S base) f U (t - 1)
            * fiberObservable μ (realizedEquiv S base)
              (Lindeberg.coord
                ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩)) U t
        - fiberObservable μ (realizedEquiv S base) f U t
            * fiberObservable μ (realizedEquiv S base)
              (Lindeberg.coord
                ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩))
              U (t - 1) := by
  unfold fiberAbsStep fiberObservable
  exact AdaptiveTau.step_fiber_le hpos hmono (realizedEquiv S base) hf hfC t ht htn U

noncomputable def fiberAdaptAbsStep (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (m t : ℕ) : ℝ :=
  ∫ V, |f (codeMap μ (σ : Fin n → E) (AdaptMConditional.adaptWt U V m t))
      - f (codeMap μ (σ : Fin n → E)
          (AdaptMConditional.adaptWt U V m (t - 1)))| ∂(GrandCoupling.Vcube n)

noncomputable def fiberAdaptObservable (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) (U : Fin n → ℝ) (m s : ℕ) : ℝ :=
  ∫ V, g (codeMap μ (σ : Fin n → E) (AdaptMConditional.adaptWt U V m s))
    ∂(GrandCoupling.Vcube n)




theorem decisionTree_branch_adapt_step_fiber_le {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hmono : IsMonotonicMeasure μ) (T : DecisionTree E)
    (base : ConfigSpace E) {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) (ht : 1 ≤ t)
    (htm : t ≤ (T.queried base).card) (htn : t - 1 < Fintype.card E)
    (U : Fin (Fintype.card E) → ℝ) :
    let S := extendDecisionTree T base (Finset.univ : Finset E)
    let σ := realizedEquiv S base
    let m := (T.queried base).card
    let e := (σ : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩
    fiberAdaptAbsStep μ σ f U m t
      ≤ fiberAdaptObservable μ σ (fun ω => f ω * Lindeberg.coord e ω) U m (t - 1)
        + fiberAdaptObservable μ σ (fun ω => f ω * Lindeberg.coord e ω) U m t
        - fiberAdaptObservable μ σ f U m (t - 1)
            * fiberAdaptObservable μ σ (Lindeberg.coord e) U m t
        - fiberAdaptObservable μ σ f U m t
            * fiberAdaptObservable μ σ (Lindeberg.coord e) U m (t - 1) := by
  dsimp only
  unfold fiberAdaptAbsStep fiberAdaptObservable
  exact AdaptDisintegration.adsD_adapt_step_fiber_le hpos hmono _ hf hfC t _ ht htm htn U

end AdaptiveCausalKernel
end OSSS
end StatMech
