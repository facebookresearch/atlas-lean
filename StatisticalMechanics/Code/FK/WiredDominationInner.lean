/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.FK.MonoBC
import Code.FK.DomainMarkov
import Code.FK.InfiniteVolume
import Code.Inequalities.FKG
import Code.Inequalities.IncreasingEvent
import Code.Foundations.StochasticDomination

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]










omit [DecidableRel G.Adj] in


theorem agreesOff_inf {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : AgreesOff F ψ a) (hb : AgreesOff F ψ b) : AgreesOff F ψ (a ⊓ b) := by
  intro e he
  show (a e && b e) = ψ e
  rw [ha e he, hb e he]; cases ψ e <;> rfl

omit [DecidableRel G.Adj] in


theorem agreesOff_sup {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : AgreesOff F ψ a) (hb : AgreesOff F ψ b) : AgreesOff F ψ (a ⊔ b) := by
  intro e he
  show (a e || b e) = ψ e
  rw [ha e he, hb e he]; cases ψ e <;> rfl

omit [DecidableRel G.Adj] in

theorem condFibre_inf {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : a ∈ condFibre F ψ) (hb : b ∈ condFibre F ψ) : a ⊓ b ∈ condFibre F ψ := by
  rw [mem_condFibre] at ha hb ⊢; exact agreesOff_inf ha hb

omit [DecidableRel G.Adj] in

theorem condFibre_sup {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : a ∈ condFibre F ψ) (hb : b ∈ condFibre F ψ) : a ⊔ b ∈ condFibre F ψ := by
  rw [mem_condFibre] at ha hb ⊢; exact agreesOff_sup ha hb










variable (C : SimpleGraph V) [DecidableRel C.Adj]



noncomputable def inducedBcZ (p q : ℝ) (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ ρ ∈ condFibre F ψ, bcWeight G C p q ρ



theorem inducedBcZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    0 < inducedBcZ G C p q F ψ :=
  Finset.sum_pos (fun ρ _ => bcWeight_pos G C hp hp1 hq ρ) ⟨ψ, self_mem_condFibre F ψ⟩

theorem inducedBcZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    inducedBcZ G C p q F ψ ≠ 0 :=
  (inducedBcZ_pos G C hp hp1 hq F ψ).ne'






noncomputable def condBcProb (p q : ℝ) (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) : ℝ :=
  if AgreesOff F ψ ω then bcWeight G C p q ω / inducedBcZ G C p q F ψ else 0

theorem condBcProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    (0 : ConfigSpace (Sym2 V) → ℝ) ≤ condBcProb G C p q F ψ := by
  intro ω
  unfold condBcProb
  split
  · exact div_nonneg (bcWeight_nonneg G C hp hp1 hq ω) (inducedBcZ_pos G C hp hp1 hq F ψ).le
  · rfl




theorem condBcProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω : ConfigSpace (Sym2 V), condBcProb G C p q F ψ ω = 1 := by
  unfold condBcProb
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div]
  exact div_self (inducedBcZ_ne_zero G C hp hp1 hq F ψ)








theorem condBcProb_eq_div_bcProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) (hω : AgreesOff F ψ ω) :
    condBcProb G C p q F ψ ω
      = bcProb G C p q ω / (∑ ρ ∈ condFibre F ψ, bcProb G C p q ρ) := by
  unfold condBcProb bcProb
  rw [if_pos hω]
  have hZ : (0:ℝ) < bcZ G C p q := bcZ_pos G C hp hp1 hq
  have hIZ : (0:ℝ) < inducedBcZ G C p q F ψ := inducedBcZ_pos G C hp hp1 hq F ψ
  have hsum : (∑ ρ ∈ condFibre F ψ, bcWeight G C p q ρ / bcZ G C p q)
      = inducedBcZ G C p q F ψ / bcZ G C p q := by
    rw [inducedBcZ, ← Finset.sum_div]
  rw [hsum]
  exact (div_div_div_cancel_right₀ hZ.ne' (bcWeight G C p q ω) (inducedBcZ G C p q F ψ)).symm










theorem condBcProb_cross (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (F : Finset (Sym2 V)) (ψ a b : ConfigSpace (Sym2 V)) :
    condBcProb G C p q F ψ a * condBcProb G C' p q F ψ b
      ≤ condBcProb G C p q F ψ (a ⊓ b) * condBcProb G C' p q F ψ (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hRHSnn : 0 ≤ condBcProb G C p q F ψ (a ⊓ b) * condBcProb G C' p q F ψ (a ⊔ b) :=
    mul_nonneg (condBcProb_nonneg G C hp hp1 hq0 F ψ _)
      (condBcProb_nonneg G C' hp hp1 hq0 F ψ _)
  unfold condBcProb
  by_cases ha : AgreesOff F ψ a
  · by_cases hb : AgreesOff F ψ b
    · rw [if_pos ha, if_pos hb, if_pos (agreesOff_inf ha hb), if_pos (agreesOff_sup ha hb),
        div_mul_div_comm, div_mul_div_comm,
        div_le_div_iff_of_pos_right
          (mul_pos (inducedBcZ_pos G C hp hp1 hq0 F ψ) (inducedBcZ_pos G C' hp hp1 hq0 F ψ))]
      exact bcWeight_cross G C C' hCC' hp hp1 hq a b
    · rw [if_neg hb, mul_zero]
      simpa only [condBcProb] using hRHSnn
  · rw [if_neg ha, zero_mul]
    simpa only [condBcProb] using hRHSnn














theorem condBcProb_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V))
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * condBcProb G C p q F ψ ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * condBcProb G C' p q F ψ ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact condBcProb_nonneg G C hp hp1 hq0 F ψ
  · exact condBcProb_nonneg G C' hp hp1 hq0 F ψ
  · rw [condBcProb_sum_eq_one G C hp hp1 hq0, condBcProb_sum_eq_one G C' hp hp1 hq0]
  · exact fun a b => condBcProb_cross G C C' hCC' hp hp1 hq F ψ a b













theorem bcProb_eq_fibreMass_mul_condBcProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ω : ConfigSpace (Sym2 V)) :
    bcProb G C p q ω
      = (∑ ρ ∈ condFibre F ω, bcProb G C p q ρ) * condBcProb G C p q F ω ω := by
  have hself : AgreesOff F ω ω := agreesOff_self F ω
  rw [condBcProb_eq_div_bcProb G C hp hp1 hq F ω ω hself]
  have hbcProb_pos : ∀ ρ, 0 < bcProb G C p q ρ :=
    fun ρ => div_pos (bcWeight_pos G C hp hp1 hq ρ) (bcZ_pos G C hp hp1 hq)
  have hpos : 0 < ∑ ρ ∈ condFibre F ω, bcProb G C p q ρ :=
    Finset.sum_pos (fun ρ _ => hbcProb_pos ρ) ⟨ω, self_mem_condFibre F ω⟩
  field_simp











theorem condBcProb_average_mono (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C' p q ω :=
  bcProb_mono_bc G C C' hCC' hp hp1 hq hA











variable (bdry : V → Prop) [DecidablePred bdry]






















theorem wiredFkProb_inner_dominated (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : StatMech.Lattice.boundaryCliqueGraph bdry ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C' p q ω := by
  have hwired : ∀ ω, wiredFkProb G bdry p q ω
      = bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω := by
    intro ω
    have hw : ∀ η, bcWeight G (StatMech.Lattice.boundaryCliqueGraph bdry) p q η
        = wiredFkWeight G bdry p q η := by
      intro η; rw [bcWeight, wiredFkWeight, numClustersBC_boundaryClique]
    have hZ : bcZ G (StatMech.Lattice.boundaryCliqueGraph bdry) p q = wiredFkZ G bdry p q := by
      rw [bcZ, wiredFkZ]; exact Finset.sum_congr rfl (fun η _ => hw η)
    rw [bcProb, wiredFkProb, hw, hZ]
  rw [Finset.sum_congr rfl (fun ω _ => by rw [hwired ω])]
  exact condBcProb_average_mono G (StatMech.Lattice.boundaryCliqueGraph bdry) C' hCC' hp hp1 hq hA










theorem wiredFkProb_inner_dominated_cond (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : StatMech.Lattice.boundaryCliqueGraph bdry ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V))
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
        * condBcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q F ψ ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * condBcProb G C' p q F ψ ω :=
  condBcProb_mono_bc G (StatMech.Lattice.boundaryCliqueGraph bdry) C' hCC' hp hp1 hq F ψ hA

end FK

end StatMech
