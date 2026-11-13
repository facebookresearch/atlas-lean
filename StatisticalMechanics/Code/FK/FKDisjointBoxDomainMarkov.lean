/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Code.FK.WiredDominationInner
import Code.FK.MonoBC
import Code.FK.DomainMarkov
import Code.Inequalities.FKG
import Code.Inequalities.IncreasingEvent

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C : SimpleGraph V) [DecidableRel C.Adj]









noncomputable def projOff (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 V) :=
  fun e => if e ∈ F then false else ψ e

theorem projOff_idem (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    projOff F (projOff F ψ) = projOff F ψ := by
  funext e; unfold projOff; by_cases h : e ∈ F <;> simp [h]

theorem agreesOff_projOff (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    AgreesOff F (projOff F ψ) ψ := by
  intro e he; unfold projOff; simp [he]

theorem projOff_eq_of_agreesOff {F : Finset (Sym2 V)} {ψ ρ : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ρ) : projOff F ρ = projOff F ψ := by
  funext e; unfold projOff
  by_cases he : e ∈ F
  · simp [he]
  · simp only [he, if_false]; exact (h e he)



theorem filter_projOff_eq_condFibre (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V))
    (hψ : projOff F ψ = ψ) :
    Finset.univ.filter (fun ρ => projOff F ρ = ψ) = condFibre F ψ := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_condFibre]
  constructor
  · intro h e he
    have : projOff F ρ e = ψ e := by rw [h]
    unfold projOff at this; simpa [he] using this
  · intro h
    have : projOff F ρ = projOff F ψ := projOff_eq_of_agreesOff h
    rw [this, hψ]


theorem condFibre_congr_dom' {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ψ') : condFibre F ψ = condFibre F ψ' := by
  ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr h]



theorem condBcProb_congr_dom' (p q : ℝ) (F : Finset (Sym2 V))
    (ψ ψ' ω : ConfigSpace (Sym2 V)) (h : AgreesOff F ψ ψ') :
    condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
  have hcond : AgreesOff F ψ ω ↔ AgreesOff F ψ' ω := by rw [agreesOff_congr h]
  have hfibre : condFibre F ψ = condFibre F ψ' := condFibre_congr_dom' h
  unfold condBcProb inducedBcZ
  rw [hfibre]
  by_cases hω : AgreesOff F ψ ω
  · rw [if_pos hω, if_pos (hcond.mp hω)]
  · rw [if_neg hω, if_neg (fun h' => hω (hcond.mpr h'))]


noncomputable def fibreReps (F : Finset (Sym2 V)) : Finset (ConfigSpace (Sym2 V)) :=
  Finset.univ.filter (fun ψ => projOff F ψ = ψ)












theorem bcProb_fibre_decompose {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (B : Set (ConfigSpace (Sym2 V))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ)
      = ∑ ψ ∈ fibreReps F,
          (∑ σ ∈ condFibre F ψ, bcProb G C p q σ)
          * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := projOff F) (t := fibreReps F)
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, projOff_idem F ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [fibreReps, Finset.mem_filter] at hψ
  rw [show (Finset.univ.filter (fun ρ => projOff F ρ = ψ)) = condFibre F ψ from
        filter_projOff_eq_condFibre F ψ hψ.2]
  have hRHS : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [hRHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hbc := bcProb_eq_fibreMass_mul_condBcProb G C hp hp1 hq F ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hbc
  have hcc : condBcProb G C p q F ρ ρ = condBcProb G C p q F ψ ρ :=
    condBcProb_congr_dom' G C p q F ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hbc
  rw [hbc]; ring








def DependsOnOutside (F : Finset (Sym2 V)) (B : Set (ConfigSpace (Sym2 V))) : Prop :=
  ∀ ψ ρ, AgreesOff F ψ ρ → (ψ ∈ B ↔ ρ ∈ B)


theorem indicator_const_on_fibre {F : Finset (Sym2 V)} {B : Set (ConfigSpace (Sym2 V))}
    (hB : DependsOnOutside F B) {ψ ρ : ConfigSpace (Sym2 V)} (hρ : AgreesOff F ψ ρ) :
    B.indicator (fun _ => (1:ℝ)) ρ = B.indicator (fun _ => (1:ℝ)) ψ := by
  by_cases h : ψ ∈ B
  · rw [Set.indicator_of_mem ((hB ψ ρ hρ).mp h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hh => h ((hB ψ ρ hρ).mpr hh)),
      Set.indicator_of_notMem h]



theorem condBcProb_sum_outside {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {F : Finset (Sym2 V)} {B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside F B)
    {ψ : ConfigSpace (Sym2 V)} (hψ : projOff F ψ = ψ) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ := by
  classical
  have hrestrict : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb; rw [if_neg hρ, mul_zero]
  rw [hrestrict]
  have hconst : ∀ ρ ∈ condFibre F ψ,
      B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ
        = B.indicator (fun _ => (1:ℝ)) ψ * condBcProb G C p q F ψ ρ := by
    intro ρ hρ
    rw [mem_condFibre] at hρ
    rw [indicator_const_on_fibre hB hρ]
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum]
  have hsum1 : ∑ ρ ∈ condFibre F ψ, condBcProb G C p q F ψ ρ = 1 := by
    have htot : ∑ ρ, condBcProb G C p q F ψ ρ = 1 := condBcProb_sum_eq_one G C hp hp1 hq F ψ
    rw [← htot]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb; rw [if_neg hρ]
  rw [hsum1, mul_one]



theorem condBcProb_cross_outside {p q : ℝ}
    {F : Finset (Sym2 V)} {A B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside F B)
    {ψ : ConfigSpace (Sym2 V)} :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hρ : AgreesOff F ψ ρ
  · have hBρ : B.indicator (fun _ => (1:ℝ)) ρ = B.indicator (fun _ => (1:ℝ)) ψ :=
      indicator_const_on_fibre hB hρ
    have hAB : (A ∩ B).indicator (fun _ => (1:ℝ)) ρ
        = A.indicator (fun _ => (1:ℝ)) ρ * B.indicator (fun _ => (1:ℝ)) ρ := by
      by_cases ha : ρ ∈ A <;> by_cases hb : ρ ∈ B <;>
        simp [Set.indicator, ha, hb, Set.mem_inter_iff]
    rw [hAB, hBρ]; ring
  · unfold condBcProb; rw [if_neg hρ]; ring
















theorem bcProb_disjoint_product_dom {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {F : Finset (Sym2 V)} {A B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside F B)
    {α : ℝ} (hα : 0 ≤ α)
    (hres : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) ≤ α) :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ)
      ≤ α * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) := by
  classical
  rw [bcProb_fibre_decompose G C hp hp1 hq F (A ∩ B),
      bcProb_fibre_decompose G C hp hp1 hq F B, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ψ hψ
  rw [fibreReps, Finset.mem_filter] at hψ
  have hfm : 0 ≤ ∑ σ ∈ condFibre F ψ, bcProb G C p q σ :=
    Finset.sum_nonneg (fun σ _ => bcProb_nonneg G C hp hp1 hq σ)
  have hBcond : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ :=
    condBcProb_sum_outside G C hp hp1 hq hB hψ.2
  have hABcond : (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) :=
    condBcProb_cross_outside G C hB
  rw [hABcond, hBcond]
  have hBind : 0 ≤ B.indicator (fun _ => (1:ℝ)) ψ := Set.indicator_nonneg (fun _ _ => zero_le_one) ψ
  have hres' := hres ψ (Finset.mem_filter.mpr hψ)
  calc (∑ σ ∈ condFibre F ψ, bcProb G C p q σ)
          * (B.indicator (fun _ => (1:ℝ)) ψ *
              (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ))
      ≤ (∑ σ ∈ condFibre F ψ, bcProb G C p q σ) * (B.indicator (fun _ => (1:ℝ)) ψ * α) := by
        apply mul_le_mul_of_nonneg_left _ hfm
        exact mul_le_mul_of_nonneg_left hres' hBind
    _ = α * ((∑ σ ∈ condFibre F ψ, bcProb G C p q σ) * B.indicator (fun _ => (1:ℝ)) ψ) := by ring










theorem bcProb_disjoint_product_lower_of_conditional
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {F : Finset (Sym2 V)} {A B : Set (ConfigSpace (Sym2 V))}
    (hB : DependsOnOutside F B) {α : ℝ}
    (hres : ∀ ψ ∈ fibreReps F, α ≤
      ∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ *
        condBcProb G C p q F ψ ρ) :
    α * (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ *
          bcProb G C p q ρ) ≤
      ∑ ρ, (A ∩ B).indicator (fun _ => (1 : ℝ)) ρ *
        bcProb G C p q ρ := by
  classical
  rw [bcProb_fibre_decompose G C hp hp1 hq F (A ∩ B),
    bcProb_fibre_decompose G C hp hp1 hq F B, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ψ hψ
  rw [fibreReps, Finset.mem_filter] at hψ
  have hfm : 0 ≤ ∑ σ ∈ condFibre F ψ, bcProb G C p q σ :=
    Finset.sum_nonneg (fun σ _ => bcProb_nonneg G C hp hp1 hq σ)
  have hBcond :
      (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ *
          condBcProb G C p q F ψ ρ) =
        B.indicator (fun _ => (1 : ℝ)) ψ :=
    condBcProb_sum_outside G C hp hp1 hq hB hψ.2
  have hABcond :
      (∑ ρ, (A ∩ B).indicator (fun _ => (1 : ℝ)) ρ *
          condBcProb G C p q F ψ ρ) =
        B.indicator (fun _ => (1 : ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ *
            condBcProb G C p q F ψ ρ) :=
    condBcProb_cross_outside G C hB
  rw [hBcond, hABcond]
  have hBind : 0 ≤ B.indicator (fun _ => (1 : ℝ)) ψ :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ψ
  have hres' := hres ψ (Finset.mem_filter.mpr hψ)
  calc
    α * ((∑ σ ∈ condFibre F ψ, bcProb G C p q σ) *
        B.indicator (fun _ => (1 : ℝ)) ψ) =
      (∑ σ ∈ condFibre F ψ, bcProb G C p q σ) *
        (B.indicator (fun _ => (1 : ℝ)) ψ * α) := by ring
    _ ≤ (∑ σ ∈ condFibre F ψ, bcProb G C p q σ) *
        (B.indicator (fun _ => (1 : ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ *
            condBcProb G C p q F ψ ρ)) := by
      apply mul_le_mul_of_nonneg_left _ hfm
      exact mul_le_mul_of_nonneg_left hres' hBind








theorem perFibre_dom_of_wired {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {F : Finset (Sym2 V)} (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) {α : ℝ}
    (hres' : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α) :
    ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) ≤ α := by
  intro ψ hψ
  exact le_trans (condBcProb_mono_bc G C C' hCC' hp hp1 hq F ψ hA) (hres' ψ hψ)








theorem bcProb_disjoint_product_dom_wired {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {F : Finset (Sym2 V)} (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : DependsOnOutside F B)
    {α : ℝ} (hα : 0 ≤ α)
    (hres' : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α) :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ)
      ≤ α * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) :=
  bcProb_disjoint_product_dom G C hp hp1 (lt_of_lt_of_le one_pos hq) hB hα
    (perFibre_dom_of_wired G C hp hp1 hq C' hCC' hA hres')

end FK

end StatMech
