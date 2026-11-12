/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.FK.CriticalPoint
import Code.FK.InfiniteVolume
import Code.FK.Limits
import Code.FK.Comparison
import Code.Percolation.PcNontrivial
import Code.Foundations.MonotoneLimit
import Code.Inequalities.FKG

open MeasureTheory Filter Topology Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation






variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]



theorem openGraph_mono {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    openGraph G a ≤ openGraph G b := by
  intro x y hxy
  rw [openGraph_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  have := h s(x, y)
  rw [hxy.2] at this
  exact le_antisymm le_top this



theorem wiredGraph_mono {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    wiredGraph G bdry a ≤ wiredGraph G bdry b := by
  unfold wiredGraph
  exact sup_le_sup_right (openGraph_mono G h) _



theorem numClustersWired_antitone {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    numClustersWired G bdry b ≤ numClustersWired G bdry a := by
  unfold numClustersWired
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le (wiredGraph_mono G bdry h)









theorem wiredFkWeight_edgeProduct_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q a * edgeProduct G p b
      ≤ wiredFkWeight G bdry p q (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold wiredFkWeight
  
  have hmod : edgeProduct G p a * edgeProduct G p b
      = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
    rw [edgeProduct_logModular G p a b]; ring
  
  have hk : numClustersWired G bdry a ≤ numClustersWired G bdry (a ⊓ b) :=
    numClustersWired_antitone G bdry inf_le_left
  have hclust : q ^ numClustersWired G bdry a ≤ q ^ numClustersWired G bdry (a ⊓ b) :=
    pow_le_pow_right₀ hq hk
  
  have hepa : (0 : ℝ) ≤ edgeProduct G p a := (edgeProduct_pos G hp hp1 a).le
  have hepb : (0 : ℝ) ≤ edgeProduct G p b := (edgeProduct_pos G hp hp1 b).le
  have hepab : (0 : ℝ) ≤ edgeProduct G p (a ⊓ b) := (edgeProduct_pos G hp hp1 (a ⊓ b)).le
  have hepsup : (0 : ℝ) ≤ edgeProduct G p (a ⊔ b) := (edgeProduct_pos G hp hp1 (a ⊔ b)).le
  have hqa : (0 : ℝ) ≤ q ^ numClustersWired G bdry a := pow_nonneg (by linarith) _
  
  calc edgeProduct G p a * q ^ numClustersWired G bdry a * edgeProduct G p b
      = (edgeProduct G p a * edgeProduct G p b) * q ^ numClustersWired G bdry a := by ring
    _ = (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClustersWired G bdry a := by
          rw [hmod]
    _ ≤ (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClustersWired G bdry (a ⊓ b) := by
          apply mul_le_mul_of_nonneg_left hclust
          exact mul_nonneg hepab hepsup
    _ = edgeProduct G p (a ⊓ b) * q ^ numClustersWired G bdry (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
          ring






theorem wiredFkProb_fkProbOne_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q a * fkProb G p 1 b
      ≤ wiredFkProb G bdry p q (a ⊓ b) * fkProb G p 1 (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < wiredFkZ G bdry p q := wiredFkZ_pos G bdry hp hp1 hq0
  have hZ2 : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  unfold wiredFkProb fkProb
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
  rw [fkWeight_one, fkWeight_one]
  exact wiredFkWeight_edgeProduct_cross G bdry hp hp1 hq a b







theorem wiredFkProb_le_fkProbOne_increasing {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p 1 ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun ω => wiredFkProb_nonneg G bdry hp hp1 hq0 ω
  · exact fun ω => fkProb_nonneg G hp hp1 one_pos ω
  · rw [wiredFkProb_sum_eq_one G bdry hp hp1 hq0, fkProb_sum_eq_one G hp hp1 one_pos]
  · exact fun a b => wiredFkProb_fkProbOne_cross G bdry hp hp1 hq a b












theorem sum_prod_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι)
    (h : ι → Bool → ℝ) :
    ∑ ω : ι → Bool, ∏ e ∈ s, h e (ω e)
      = 2 ^ (Fintype.card ι - s.card) * ∏ e ∈ s, (∑ b : Bool, h e b) := by
  classical
  set hbar : ι → Bool → ℝ := fun e b => if e ∈ s then h e b else 1 with hhbar
  have key : ∀ ω : ι → Bool, ∏ e ∈ s, h e (ω e) = ∏ e : ι, hbar e (ω e) := by
    intro ω; rw [Finset.prod_ite_mem Finset.univ s]; congr 1; ext x; simp
  simp_rw [key]; rw [← Fintype.prod_sum]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ s) (fun e => ∑ b : Bool, hbar e b)]
  have h1 : (Finset.univ.filter (· ∈ s)) = s := by ext x; simp
  have h2 : ∀ e ∈ (Finset.univ.filter (fun e => ¬ e ∈ s)), (∑ b : Bool, hbar e b) = 2 := by
    intro e he; simp only [Finset.mem_filter] at he; simp only [hhbar, if_neg he.2]; simp
  rw [Finset.prod_congr rfl h2, Finset.prod_const]
  have hcard : (Finset.univ.filter (fun e => ¬ e ∈ s)).card = Fintype.card ι - s.card := by
    rw [Finset.filter_not, Finset.card_univ_diff]; simp
  rw [hcard, h1]
  have h3 : ∀ e ∈ s, (∑ b : Bool, hbar e b) = ∑ b : Bool, h e b := by
    intro e he; simp only [hhbar, if_pos he]
  rw [Finset.prod_congr rfl h3]; ring





theorem fkProbOne_cylinder {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (F : Finset (Sym2 V))
    (hF : F ⊆ G.edgeFinset) :
    ∑ ω : ConfigSpace (Sym2 V),
        (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb G p 1 ω = p ^ F.card := by
  classical
  have hZpos : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  have hnum : ∑ ω : ConfigSpace (Sym2 V),
      (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb G p 1 ω
      = (∑ ω : ConfigSpace (Sym2 V),
          (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * edgeProduct G p ω) / fkZ G p 1 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold fkProb; rw [fkWeight_one]; ring
  rw [hnum]
  set h : Sym2 V → Bool → ℝ :=
    fun e b => if e ∈ F then (if b then p else 0) else (if b then p else 1 - p) with hh
  have hforced : (∑ ω : ConfigSpace (Sym2 V),
      (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * edgeProduct G p ω)
      = ∑ ω : ConfigSpace (Sym2 V), ∏ e ∈ G.edgeFinset, h e (ω e) := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold edgeProduct
    by_cases hall : ∀ e ∈ F, ω e = true
    · rw [if_pos hall, one_mul]
      refine Finset.prod_congr rfl (fun e he => ?_)
      simp only [hh]
      by_cases heF : e ∈ F
      · rw [if_pos heF, hall e heF]; simp
      · rw [if_neg heF]
    · rw [if_neg hall, zero_mul]
      symm
      push Not at hall
      obtain ⟨e0, he0F, he0⟩ := hall
      apply Finset.prod_eq_zero (i := e0) (hF he0F)
      have he0' : ω e0 = false := by simpa using he0
      simp only [hh, if_pos he0F, he0']; simp
  rw [hforced, sum_prod_factor]
  have hZ : fkZ G p 1
      = 2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card)
        * ∏ e ∈ G.edgeFinset, (∑ b : Bool, (if b then p else 1 - p)) := by
    rw [fkZ_one]
    have heq : (∑ ω : ConfigSpace (Sym2 V), edgeProduct G p ω)
        = ∑ ω : ConfigSpace (Sym2 V),
            ∏ e ∈ G.edgeFinset, (fun (e : Sym2 V) (b : Bool) => if b then p else 1 - p) e (ω e) :=
      rfl
    rw [heq, sum_prod_factor G.edgeFinset (fun (e : Sym2 V) (b : Bool) => if b then p else 1 - p)]
  rw [hZ]
  have hprodF : (∏ e ∈ G.edgeFinset, (∑ b : Bool, h e b))
      = ∏ e ∈ G.edgeFinset, (if e ∈ F then p else 1) := by
    refine Finset.prod_congr rfl (fun e _ => ?_)
    simp only [hh]
    by_cases heF : e ∈ F
    · simp [heF]
    · simp only [heF, if_false]; norm_num
  have hprodZ : (∏ e ∈ G.edgeFinset, (∑ b : Bool, (if b then p else 1 - p)))
      = ∏ e ∈ G.edgeFinset, (1 : ℝ) := by
    refine Finset.prod_congr rfl (fun e _ => ?_); norm_num
  rw [hprodF, hprodZ, Finset.prod_const_one]
  have hpF : (∏ e ∈ G.edgeFinset, (if e ∈ F then p else 1)) = p ^ F.card := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hF, Finset.prod_const]
  rw [hpF]; field_simp







variable {d : ℕ}



def fkExtWord (m : ℕ) (hd : 0 < d) (w : Fin m → Fin d × Bool) : ℕ → Fin d × Bool :=
  fun k => if hk : k < m then w ⟨k, hk⟩ else (⟨0, hd⟩, false)




def fkExistsOpenWalk (d m : ℕ) (hd : 0 < d) : Set (ConfigSpace (Sym2 (Site d))) :=
  ⋃ (w : Fin m → Fin d × Bool) (_ : goodWord (fkExtWord m hd w) m), wordEvent (fkExtWord m hd w) m



theorem isClopen_singleOpen (e : Sym2 (Site d)) :
    IsClopen {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} = (fun ω => ω e) ⁻¹' {true} := rfl
  rw [h]
  exact IsClopen.preimage (isClopen_discrete _) (StatMech.ConfigSpace.continuous_eval e)



theorem isClopen_wordEvent (g : ℕ → Fin d × Bool) (m : ℕ) : IsClopen (wordEvent g m) := by
  have heq : wordEvent g m
      = ⋂ k ∈ (Finset.range m : Set ℕ),
          {ω : ConfigSpace (Sym2 (Site d)) | ω (edgeOf g k) = true} := by
    ext ω
    simp only [wordEvent, Set.mem_setOf_eq, Set.mem_iInter, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h k hk; exact h k (Finset.mem_range.mpr hk)
    · intro h k hk; exact h k (Finset.mem_range.mp hk)
  rw [heq]
  exact Set.Finite.isClopen_biInter (Finset.finite_toSet _) (fun k _ => isClopen_singleOpen _)


theorem isIncreasing_wordEvent (g : ℕ → Fin d × Bool) (m : ℕ) : IsIncreasing (wordEvent g m) := by
  intro x y hxy hx k hk
  have := hxy (edgeOf g k)
  rw [hx k hk] at this
  exact le_antisymm le_top this


theorem isClopen_fkExistsOpenWalk (m : ℕ) (hd : 0 < d) : IsClopen (fkExistsOpenWalk d m hd) := by
  rw [fkExistsOpenWalk]
  apply isClopen_iUnion_of_finite
  intro w
  by_cases hgw : goodWord (fkExtWord m hd w) m
  · rw [Set.iUnion_eq_if, if_pos hgw]; exact isClopen_wordEvent _ _
  · rw [Set.iUnion_eq_if, if_neg hgw]; exact isClopen_empty


theorem isIncreasing_fkExistsOpenWalk (m : ℕ) (hd : 0 < d) :
    IsIncreasing (fkExistsOpenWalk d m hd) := by
  apply isUpperSet_iUnion₂
  intro w _
  exact isIncreasing_wordEvent _ _




theorem percolationEvent_subset_fkExistsOpenWalk (hd : 0 < d) (m : ℕ) :
    percolationEvent d ⊆ fkExistsOpenWalk d m hd := by
  refine (percolationEvent_subset_iUnion_wordEvent hd m).trans ?_
  refine Set.iUnion_subset (fun g => Set.iUnion_subset (fun hg => ?_))
  set w : Fin m → Fin d × Bool := fun i => g i.1 with hw
  have hvert : ∀ j ≤ m, vertOf g j = vertOf (fkExtWord m hd w) j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ k ih =>
      have hk : k < m := by omega
      rw [vertOf_succ, vertOf_succ, ih (by omega)]
      congr 1 <;> simp only [fkExtWord, dif_pos hk, hw]
  have hgood' : goodWord (fkExtWord m hd w) m := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [← hvert a (by omega), ← hvert b (by omega)] at hab
    exact hg (by simp only [Finset.coe_range, Set.mem_Iio]; omega)
      (by simp only [Finset.coe_range, Set.mem_Iio]; omega) hab
  have hwe : wordEvent g m = wordEvent (fkExtWord m hd w) m := by
    apply Set.ext; intro ω
    simp only [wordEvent, Set.mem_setOf_eq, Finset.mem_range]
    have hedge : ∀ k < m, edgeOf g k = edgeOf (fkExtWord m hd w) k := by
      intro k hk; unfold edgeOf; rw [hvert k (by omega), hvert (k + 1) (by omega)]
    constructor
    · intro h k hk; rw [← hedge k hk]; exact h k hk
    · intro h k hk; rw [hedge k hk]; exact h k hk
  rw [hwe]
  exact Set.subset_iUnion_of_subset w (Set.subset_iUnion_of_subset hgood' (le_refl _))




theorem extendEdge_eq_of_range (n : ℕ) (be : Sym2 (boxVerts d n))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    extendEdge d n ω (edgeIncl d n be) = ω be := by
  unfold extendEdge
  have hmem : edgeIncl d n be ∈ Set.range (edgeIncl d n) := ⟨be, rfl⟩
  rw [dif_pos hmem, edgeIncl_injective d n hmem.choose_spec]



theorem range_of_extendEdge_true (n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (e : Sym2 (Site d)) (h : extendEdge d n ω e = true) : e ∈ Set.range (edgeIncl d n) := by
  by_contra hc; unfold extendEdge at h; rw [dif_neg hc] at h; exact absurd h (by simp)



theorem boxEdge_mem (n : ℕ) (be : Sym2 (boxVerts d n)) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) (heq : edgeIncl d n be = s(x, y)) :
    be ∈ (boxGraph d n).edgeFinset := by
  induction be using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj]
    unfold edgeIncl at heq
    rw [Sym2.map_mk, Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · show (hypercubicLattice d).Adj (u : Site d) (v : Site d); rw [h1, h2]; exact hadj
    · show (hypercubicLattice d).Adj (u : Site d) (v : Site d); rw [h1, h2]; exact hadj.symm




theorem exists_boxF (n m : ℕ) (g : ℕ → Fin d × Bool) (hg : goodWord g m)
    (hrange : ∀ k ∈ Finset.range m, edgeOf g k ∈ Set.range (edgeIncl d n)) :
    ∃ F : Finset (Sym2 (boxVerts d n)), F ⊆ (boxGraph d n).edgeFinset ∧ F.card = m ∧
      (extendEdge d n ⁻¹' wordEvent g m ⊆ {ω | ∀ be ∈ F, ω be = true}) := by
  classical
  set bef : {k // k ∈ Finset.range m} → Sym2 (boxVerts d n) :=
    fun k => (hrange k.1 k.2).choose with hbef
  have hbef_spec : ∀ k : {k // k ∈ Finset.range m}, edgeIncl d n (bef k) = edgeOf g k.1 :=
    fun k => (hrange k.1 k.2).choose_spec
  refine ⟨(Finset.range m).attach.image bef, ?_, ?_, ?_⟩
  · intro f hf
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hf
    obtain ⟨k, rfl⟩ := hf
    have hadj : (hypercubicLattice d).Adj (vertOf g k.1) (vertOf g (k.1 + 1)) := by
      rw [vertOf_succ]; exact adj_coordShift _ _ _
    exact boxEdge_mem n (bef k) _ _ hadj (by rw [hbef_spec k]; rfl)
  · rw [Finset.card_image_of_injOn, Finset.card_attach, Finset.card_range]
    intro a _ b _ hab
    have heq : edgeIncl d n (bef a) = edgeIncl d n (bef b) := by rw [hab]
    rw [hbef_spec a, hbef_spec b] at heq
    have ha := Finset.mem_range.mp a.2
    have hb := Finset.mem_range.mp b.2
    exact Subtype.ext ((edgeOf_injOn g m hg) (by simp [ha]) (by simp [hb]) heq)
  · intro ω hω be hbe
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hbe
    obtain ⟨k, rfl⟩ := hbe
    simp only [Set.mem_preimage, wordEvent, Set.mem_setOf_eq] at hω
    have htrue := hω k.1 k.2
    rw [← hbef_spec k] at htrue
    rw [extendEdge_eq_of_range] at htrue
    exact htrue









theorem perWord_box_bound (n m : ℕ) (g : ℕ → Fin d × Bool) (hg : goodWord g m)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
        (extendEdge d n ⁻¹' wordEvent g m).indicator (fun _ => (1 : ℝ)) ω
          * fkProb (boxGraph d n) p 1 ω ≤ p ^ m := by
  classical
  by_cases hempty : (extendEdge d n ⁻¹' wordEvent g m) = ∅
  · rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    positivity
  · rw [← Set.not_nonempty_iff_eq_empty, not_not] at hempty
    obtain ⟨ω0, hω0⟩ := hempty
    simp only [Set.mem_preimage, wordEvent, Set.mem_setOf_eq] at hω0
    have hrange : ∀ k ∈ Finset.range m, edgeOf g k ∈ Set.range (edgeIncl d n) :=
      fun k hk => range_of_extendEdge_true n ω0 _ (hω0 k hk)
    obtain ⟨F, hFsub, hFcard, hFcont⟩ := exists_boxF n m g hg hrange
    calc ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (extendEdge d n ⁻¹' wordEvent g m).indicator (fun _ => (1 : ℝ)) ω
              * fkProb (boxGraph d n) p 1 ω
        ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb (boxGraph d n) p 1 ω := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_right _ (fkProb_nonneg (boxGraph d n) hp hp1 one_pos ω)
          by_cases hω : ω ∈ extendEdge d n ⁻¹' wordEvent g m
          · rw [Set.indicator_of_mem hω]
            have hmem : ∀ be ∈ F, ω be = true := hFcont hω
            rw [if_pos hmem]
          · rw [Set.indicator_of_notMem hω]; split <;> positivity
      _ = p ^ F.card := fkProbOne_cylinder (boxGraph d n) hp hp1 F hFsub
      _ = p ^ m := by rw [hFcard]




theorem wiredFiniteMeasure_real_eq (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real A
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hw : (wiredFiniteMeasure d n hp hp1 hq : Measure _).real A
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' A)).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, wiredFkPMF_toMeasure_toReal]








theorem wiredFiniteMeasure_fkExistsOpenWalk_le (n m : ℕ) (hd : 0 < d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fkExistsOpenWalk d m hd)
      ≤ ((2 * d : ℝ) * p) ^ m := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hAmeas : MeasurableSet (fkExistsOpenWalk d m hd) :=
    IsClopen.measurableSet_configSpace (isClopen_fkExistsOpenWalk m hd)
  
  set μ1 := fkProb (boxGraph d n) p 1 with hμ1
  
  rw [wiredFiniteMeasure_real_eq n hp hp1 hq0 _ hAmeas]
  
  have hHolley :
      (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω)
        ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
              * fkProb (boxGraph d n) p 1 ω :=
    wiredFkProb_le_fkProbOne_increasing (boxGraph d n) (boxBoundary d n) hp hp1 hq
      (isIncreasing_preimage_extendEdge d n (isIncreasing_fkExistsOpenWalk m hd))
  refine hHolley.trans ?_
  
  set S : Finset (Fin m → Fin d × Bool) :=
    Finset.univ.filter (fun w => goodWord (fkExtWord m hd w) m) with hS
  
  have hsplit : ∀ ω : ConfigSpace (Sym2 (boxVerts d n)),
      (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
        ≤ ∑ w ∈ S, (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ extendEdge d n ⁻¹' fkExistsOpenWalk d m hd
    · rw [Set.indicator_of_mem hω]
      rw [Set.mem_preimage, fkExistsOpenWalk, Set.mem_iUnion₂] at hω
      obtain ⟨w, hgw, hwe⟩ := hω
      have hmem : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgw⟩
      have hωmem : ω ∈ extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m := hwe
      have hstep := Finset.single_le_sum
        (f := fun w => (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω)
        (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) hmem
      simp only [] at hstep
      rwa [Set.indicator_of_mem hωmem] at hstep
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg (fun w _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  
  calc ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω * μ1 ω
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (∑ w ∈ S, (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω)
            * μ1 ω := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_right (hsplit ω) (fkProb_nonneg (boxGraph d n) hp hp1 one_pos ω)
    _ = ∑ w ∈ S, ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω * μ1 ω := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        rw [Finset.sum_mul]
    _ ≤ ∑ w ∈ S, p ^ m := by
        apply Finset.sum_le_sum
        intro w hw
        exact perWord_box_bound n m (fkExtWord m hd w) (Finset.mem_filter.mp hw).2 hp hp1
    _ = (S.card : ℝ) * p ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Finset.univ : Finset (Fin m → Fin d × Bool)).card : ℝ) * p ^ m := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp.le m)
        exact_mod_cast Finset.card_le_card (Finset.subset_univ S)
    _ = ((2 * d : ℝ) * p) ^ m := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, Fintype.card_fin]
        push_cast
        rw [mul_pow]
        ring_nf












theorem fkTheta_le_pow (hd : 0 < d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (m : ℕ) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) ≤ ((2 * d : ℝ) * p) ^ m := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨φ, hφ, htends⟩ := wiredInfiniteVolume_isLimit d hp hp1 hq0
  
  have hmono : fkTheta d hp hp1 hq0 (q := q)
      ≤ (wiredInfiniteVolume d hp hp1 hq0 : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fkExistsOpenWalk d m hd) := by
    unfold fkTheta
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (percolationEvent_subset_fkExistsOpenWalk hd m))
  
  have hlim : (wiredInfiniteVolume d hp hp1 hq0 : Measure (ConfigSpace (Sym2 (Site d)))).real
        (fkExistsOpenWalk d m hd) ≤ ((2 * d : ℝ) * p) ^ m :=
    le_of_tendsto (htends.tendsto_real_of_isClopen (isClopen_fkExistsOpenWalk m hd))
      (Filter.Eventually.of_forall
        (fun n => wiredFiniteMeasure_fkExistsOpenWalk_le (φ n) m hd hp hp1 hq))
  exact hmono.trans hlim





theorem fkTheta_eq_zero_of_lt (hd : 0 < d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hsmall : (2 * d : ℝ) * p < 1) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hbase_nonneg : (0 : ℝ) ≤ (2 * d : ℝ) * p := by positivity
  have htend : Filter.Tendsto (fun m => ((2 * d : ℝ) * p) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hsmall
  have hle : fkTheta d hp hp1 hq0 (q := q) ≤ 0 :=
    ge_of_tendsto htend (Filter.Eventually.of_forall (fun m => fkTheta_le_pow hd hp hp1 hq m))
  exact le_antisymm hle (fkTheta_nonneg d hp hp1 hq0 (q := q))


theorem fkSubcriticalSet_bddAbove (d : ℕ) (q : ℝ) : BddAbove (fkSubcriticalSet d q) := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨hp, hp1, hq, _⟩ := hx
  exact hp1.le


theorem le_fkPc_of_mem {d : ℕ} {q p : ℝ} (hp : p ∈ fkSubcriticalSet d q) : p ≤ fkPc d q :=
  le_csSup (fkSubcriticalSet_bddAbove d q) hp









theorem fkPc_pos (hd : 0 < d) {q : ℝ} (hq : 1 ≤ q) : 0 < fkPc d q := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  
  set p : ℝ := 1 / (4 * d) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : p < 1 := by
    rw [hp_def, div_lt_one (by positivity)]; nlinarith
  have hsmall : (2 * d : ℝ) * p < 1 := by
    rw [hp_def, mul_one_div, div_lt_one (by positivity)]; nlinarith
  have hmem : p ∈ fkSubcriticalSet d q :=
    ⟨hp_pos, hp1, zero_lt_one.trans_le hq, fkTheta_eq_zero_of_lt hd hp_pos hp1 hq hsmall⟩
  exact lt_of_lt_of_le hp_pos (le_fkPc_of_mem hmem)




theorem fkPc_pos_of_two_le (hd : 2 ≤ d) {q : ℝ} (hq : 1 ≤ q) : 0 < fkPc d q :=
  fkPc_pos (by omega) hq

end FK

end StatMech
