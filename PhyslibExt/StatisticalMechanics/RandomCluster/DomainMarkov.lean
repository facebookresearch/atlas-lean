/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.RandomCluster

/-!
# Conditioning the random-cluster measure on the edges outside a set

The random-cluster measure on a finite graph, conditioned on the states of all edges outside a
finite set `F`, is the measure with weight proportional to the FK weight on the fibre of
configurations that agree with the conditioning configuration off `F`.

## i. Overview

For a configuration `ψ` and a finite edge set `F`, `condFibre F ψ` is the set of configurations
agreeing with `ψ` off `F`. The conditional law `condFkProb` (FK probability divided by the
probability of the fibre) equals the induced measure `inducedFkProb` (FK weight divided by the
fibre's total weight). The normalizing constant depends on `ψ` only through its restriction to
the complement of `F`. This is the finite-volume form of the domain Markov property used to set up
boundary conditions.

## ii. Key results

- `condFkProb_eq_inducedFkProb` : conditional probability equals the induced weight ratio.
- `condFkProb_sum_eq_one` : the conditional law is a probability measure on the fibre.
- `inducedFkZ_congr` : the induced partition function depends only on `ψ` off `F`.

## iii. Table of contents

- A. Configurations agreeing off a set
- B. The induced measure on a fibre
- C. Conditional probabilities

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Lemma 4.13.
-/

@[expose] public section

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Configurations agreeing off a set -/

/-- `ω` agrees with `ψ` on every edge outside `F`. -/
def AgreesOff (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 V) → Prop :=
  fun ω => ∀ e, e ∉ F → ω e = ψ e

/-- Decidability of agreement off a finite set. -/
instance (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    DecidablePred (AgreesOff F ψ) := by
  intro ω; unfold AgreesOff; infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma agreesOff_self (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    AgreesOff F ψ ψ := fun _ _ => rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma agreesOff_symm {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ω) : AgreesOff F ω ψ := fun e he => (h e he).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma agreesOff_congr {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ω) : AgreesOff F ψ = AgreesOff F ω := by
  funext ρ
  simp only [eq_iff_iff]
  constructor
  · intro hρ e he; rw [hρ e he, h e he]
  · intro hρ e he; rw [hρ e he, ← h e he]

/-- The fibre of configurations agreeing with `ψ` off `F`. -/
noncomputable def condFibre (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    Finset (ConfigSpace (Sym2 V)) :=
  Finset.univ.filter (AgreesOff F ψ)

omit [DecidableRel G.Adj] in
@[simp] lemma mem_condFibre {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)} :
    ω ∈ condFibre F ψ ↔ AgreesOff F ψ ω := by
  unfold condFibre; simp

omit [DecidableRel G.Adj] in
lemma self_mem_condFibre (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ψ ∈ condFibre F ψ := by rw [mem_condFibre]; exact agreesOff_self F ψ

/-! ## B. The induced measure on a fibre -/

/-- The total FK weight of the fibre `condFibre F ψ`. -/
noncomputable def inducedFkZ (p q : ℝ) (F : Finset (Sym2 V))
    (ψ : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ ρ ∈ condFibre F ψ, fkWeight G p q ρ

lemma inducedFkZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    0 < inducedFkZ G p q F ψ := by
  unfold inducedFkZ
  exact Finset.sum_pos (fun ρ _ => fkWeight_pos G hp hp1 hq ρ)
    ⟨ψ, self_mem_condFibre F ψ⟩

lemma inducedFkZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    inducedFkZ G p q F ψ ≠ 0 :=
  (inducedFkZ_pos G hp hp1 hq F ψ).ne'

/-- The FK measure induced on the fibre `condFibre F ψ`: FK weight divided by the fibre's total
weight.
-/
noncomputable def inducedFkProb (p q : ℝ) (F : Finset (Sym2 V))
    (ψ ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkWeight G p q ω / inducedFkZ G p q F ψ

lemma inducedFkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    0 ≤ inducedFkProb G p q F ψ ω :=
  div_nonneg (fkWeight_nonneg G hp hp1 hq ω) (inducedFkZ_pos G hp hp1 hq F ψ).le

lemma inducedFkProb_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    0 < inducedFkProb G p q F ψ ω :=
  div_pos (fkWeight_pos G hp hp1 hq ω) (inducedFkZ_pos G hp hp1 hq F ψ)

lemma inducedFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω ∈ condFibre F ψ, inducedFkProb G p q F ψ ω = 1 := by
  unfold inducedFkProb
  rw [← Finset.sum_div]
  exact div_self (inducedFkZ_ne_zero G hp hp1 hq F ψ)

/-! ## C. Conditional probabilities -/

/-- The random-cluster measure conditioned on agreeing with `ψ` off `F`. -/
noncomputable def condFkProb (p q : ℝ) (F : Finset (Sym2 V))
    (ψ ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkProb G p q ω / ∑ ρ ∈ condFibre F ψ, fkProb G p q ρ

lemma condFibre_fkProb_sum {p q : ℝ} (F : Finset (Sym2 V))
    (ψ : ConfigSpace (Sym2 V)) :
    ∑ ρ ∈ condFibre F ψ, fkProb G p q ρ = inducedFkZ G p q F ψ / fkZ G p q := by
  unfold fkProb inducedFkZ
  rw [Finset.sum_div]

/-- **Domain Markov property (finite volume).** Conditioned on the states of the edges outside `F`,
the random-cluster measure is the FK weight renormalized on the fibre
(Grimmett, *The Random-Cluster Model*, 2006, Lemma 4.13).
-/
theorem condFkProb_eq_inducedFkProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    condFkProb G p q F ψ ω = inducedFkProb G p q F ψ ω := by
  unfold condFkProb inducedFkProb
  rw [condFibre_fkProb_sum]
  unfold fkProb
  rw [div_div_div_cancel_right₀]
  · exact fkZ_ne_zero G hp hp1 hq

lemma condFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω ∈ condFibre F ψ, condFkProb G p q F ψ ω = 1 := by
  rw [Finset.sum_congr rfl
    (fun ω _ => condFkProb_eq_inducedFkProb G hp hp1 hq F ψ ω)]
  exact inducedFkProb_sum_eq_one G hp hp1 hq F ψ

lemma inducedFkZ_congr {p q : ℝ} {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ψ') : inducedFkZ G p q F ψ = inducedFkZ G p q F ψ' := by
  unfold inducedFkZ
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ρ
  simp only [mem_condFibre]
  rw [agreesOff_congr h]

end FK

end StatMech
