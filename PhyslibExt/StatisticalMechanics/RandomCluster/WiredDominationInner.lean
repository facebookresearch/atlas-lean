/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.DomainMarkov
public import PhyslibExt.StatisticalMechanics.RandomCluster.IvProperties
/-!
# Conditional random-cluster measures with a boundary wiring

The FK measure with boundary wiring `C`, conditioned on the configuration off a finite edge set,
satisfies Holley's condition and is monotone in `C`.

## i. Overview

Fix a finite edge set `F` and an outer configuration `ψ`. The fibre `condFibre F ψ` consists of
the configurations agreeing with `ψ` off `F`; it is closed under `⊓` and `⊔`. The conditional
measure `condBcProb G C p q F ψ` is `φ_C` restricted to this fibre and renormalized. Holley's
condition for `φ_C` restricts to the fibre, so for `q ≥ 1` and `C ≤ C'` the conditional measures
are ordered. `φ_C` is the average of the conditional measures over the fibres.

## ii. Key results

- `condBcProb` : the conditional measure, with `condBcProb_sum_eq_one` and
  `condBcProb_eq_div_bcProb`.
- `condBcProb_mono_bc` : monotonicity of the conditional measure in the wiring.
- `bcProb_eq_fibreMass_mul_condBcProb` : disintegration of `φ_C` over fibres.
- `wiredFkProb_inner_dominated`, `wiredFkProb_inner_dominated_cond` : the wired measure is
  dominated by any wiring above the boundary clique, also conditionally.

## iii. Table of contents

- A. Lattice operations on fibres
- B. The conditional measure
- C. Monotonicity in the boundary condition
- D. Disintegration and wired domination

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-!
## A. Lattice operations on fibres
-/

omit [DecidableRel G.Adj] in
lemma agreesOff_inf {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : AgreesOff F ψ a) (hb : AgreesOff F ψ b) : AgreesOff F ψ (a ⊓ b) := by
  intro e he
  change (a e && b e) = ψ e
  rw [ha e he, hb e he]; cases ψ e <;> rfl

omit [DecidableRel G.Adj] in
lemma agreesOff_sup {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : AgreesOff F ψ a) (hb : AgreesOff F ψ b) : AgreesOff F ψ (a ⊔ b) := by
  intro e he
  change (a e || b e) = ψ e
  rw [ha e he, hb e he]; cases ψ e <;> rfl

omit [DecidableRel G.Adj] in
lemma condFibre_inf {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : a ∈ condFibre F ψ) (hb : b ∈ condFibre F ψ) : a ⊓ b ∈ condFibre F ψ := by
  rw [mem_condFibre] at ha hb ⊢; exact agreesOff_inf ha hb

omit [DecidableRel G.Adj] in
lemma condFibre_sup {F : Finset (Sym2 V)} {ψ a b : ConfigSpace (Sym2 V)}
    (ha : a ∈ condFibre F ψ) (hb : b ∈ condFibre F ψ) : a ⊔ b ∈ condFibre F ψ := by
  rw [mem_condFibre] at ha hb ⊢; exact agreesOff_sup ha hb

variable (C : SimpleGraph V) [DecidableRel C.Adj]

/-!
## B. The conditional measure
-/

/-- The partition function of the fibre of `ψ` off `F`: the sum of `bcWeight` over configurations
agreeing with `ψ` off `F`. -/
noncomputable def inducedBcZ (p q : ℝ) (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ ρ ∈ condFibre F ψ, bcWeight G C p q ρ

lemma inducedBcZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    0 < inducedBcZ G C p q F ψ :=
  Finset.sum_pos (fun ρ _ => bcWeight_pos G C hp hp1 hq ρ) ⟨ψ, self_mem_condFibre F ψ⟩

lemma inducedBcZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    inducedBcZ G C p q F ψ ≠ 0 :=
  (inducedBcZ_pos G C hp hp1 hq F ψ).ne'

/-- The random-cluster measure with wiring `C` conditioned on agreeing with `ψ` off the edge set
`F`. -/
noncomputable def condBcProb (p q : ℝ) (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) : ℝ :=
  if AgreesOff F ψ ω then bcWeight G C p q ω / inducedBcZ G C p q F ψ else 0

lemma condBcProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    (0 : ConfigSpace (Sym2 V) → ℝ) ≤ condBcProb G C p q F ψ := by
  intro ω
  unfold condBcProb
  split
  · exact div_nonneg (bcWeight_nonneg G C hp hp1 hq ω) (inducedBcZ_pos G C hp hp1 hq F ψ).le
  · rfl

lemma condBcProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω : ConfigSpace (Sym2 V), condBcProb G C p q F ψ ω = 1 := by
  unfold condBcProb
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div]
  exact div_self (inducedBcZ_ne_zero G C hp hp1 hq F ψ)

lemma condBcProb_eq_div_bcProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) (hω : AgreesOff F ψ ω) :
    condBcProb G C p q F ψ ω
      = bcProb G C p q ω / (∑ ρ ∈ condFibre F ψ, bcProb G C p q ρ) := by
  unfold condBcProb bcProb
  rw [ite_eq_left hω]
  have hZ : (0 : ℝ) < bcZ G C p q := bcZ_pos G C hp hp1 hq
  have hIZ : (0 : ℝ) < inducedBcZ G C p q F ψ := inducedBcZ_pos G C hp hp1 hq F ψ
  have hsum : (∑ ρ ∈ condFibre F ψ, bcWeight G C p q ρ / bcZ G C p q)
      = inducedBcZ G C p q F ψ / bcZ G C p q := by
    rw [inducedBcZ, ← Finset.sum_div]
  rw [hsum]
  exact (div_div_div_cancel_right₀ hZ.ne' (bcWeight G C p q ω) (inducedBcZ G C p q F ψ)).symm

/-!
## C. Monotonicity in the boundary condition
-/

/-- Holley's condition for the conditional measures with nested wirings `C ≤ C'` and `q ≥ 1`. -/
lemma condBcProb_cross (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
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
    · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (agreesOff_inf ha hb),
        ite_eq_left (agreesOff_sup ha hb),
        div_mul_div_comm, div_mul_div_comm,
        div_le_div_iff_of_pos_right
          (mul_pos (inducedBcZ_pos G C hp hp1 hq0 F ψ) (inducedBcZ_pos G C' hp hp1 hq0 F ψ))]
      exact bcWeight_cross G C C' hCC' hp hp1 hq a b
    · rw [ite_eq_right hb, mul_zero]
      simpa only [condBcProb] using hRHSnn
  · rw [ite_eq_right ha, zero_mul]
    simpa only [condBcProb] using hRHSnn

/-- For `q ≥ 1` and `C ≤ C'`, the conditional measure with wiring `C` is dominated by the one with
wiring `C'` on increasing events. -/
lemma condBcProb_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
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

/-!
## D. Disintegration and wired domination
-/

/-- Disintegration: `φ_C(ω)` is the mass of the fibre of `ω` times the conditional probability of
`ω` in that fibre. -/
lemma bcProb_eq_fibreMass_mul_condBcProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
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

variable (bdry : V → Prop) [DecidablePred bdry]

/-- For `q ≥ 1` the wired measure is dominated by `φ_C'` for any wiring `C'` containing the boundary
clique. -/
lemma wiredFkProb_inner_dominated (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : StatMech.Lattice.boundaryCliqueGraph bdry ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C' p q ω := by
  rw [Finset.sum_congr rfl (fun ω _ => by rw [← bcProb_clique_eq_wiredFkProb])]
  exact bcProb_mono_bc G (StatMech.Lattice.boundaryCliqueGraph bdry) C' hCC' hp hp1 hq hA

/-- Conditional version of `wiredFkProb_inner_dominated`. -/
lemma wiredFkProb_inner_dominated_cond (C' : SimpleGraph V) [DecidableRel C'.Adj]
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
