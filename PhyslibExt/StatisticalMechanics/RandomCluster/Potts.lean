/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
/-!
# The `q`-state Potts model on a finite graph

The Gibbs measure of the ferromagnetic `q`-state Potts model on a finite graph `G` at inverse
temperature `β` and coupling `J`.

## i. Overview

A spin configuration is `σ : V → Fin q`. Its agreement count `agreement G σ` is the number of
edges `{x, y}` of `G` with `σ x = σ y`. The Potts Boltzmann weight is
`exp (β J · agreement G σ)`; normalizing by the partition function `pottsZ G q β J` gives the
Potts probability `pottsProb`, packaged as a `PMF` by `pottsPMF`. The Hamiltonian is
`H(σ) = -J ∑_{xy ∈ E} 𝟙[σ x = σ y]`, so the weight is `exp (-β H(σ))`. Positivity of the
partition function needs `q ≥ 1`, recorded as `[NeZero q]`.

## ii. Key results

- `StatMech.Potts.monoIndicator` : the indicator `𝟙[σ x = σ y]` of a monochromatic edge.
- `StatMech.Potts.agreement` : the number of monochromatic edges of `G`.
- `StatMech.Potts.pottsWeight`, `StatMech.Potts.pottsZ`, `StatMech.Potts.pottsProb` : weight,
  partition function and probability, with `pottsProb_sum_eq_one`.
- `StatMech.Potts.pottsPMF` : the Potts Gibbs measure as a `PMF`.

## iii. Table of contents

- A. Monochromatic edges
- B. Weights and the partition function
- C. The Potts Gibbs measure

## iv. References

- R. B. Potts, *Some generalized order-disorder transformations*, Proc. Cambridge Philos. Soc. 48
  (1952).
- F. Y. Wu, *The Potts model*, Rev. Mod. Phys. 54 (1982).

-/

@[expose] public section

open scoped BigOperators

namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-!

## A. Monochromatic edges

-/

/-- The indicator of a monochromatic edge: `𝟙[σ x = σ y]` on the unordered pair `s(x, y)`. -/
def monoIndicator {q : ℕ} (σ : V → Fin q) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => if σ x = σ y then (1 : ℝ) else 0, by
    intro a b
    dsimp only
    by_cases h : σ a = σ b
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]⟩

omit [Fintype V] [DecidableEq V] in
@[simp]
lemma monoIndicator_mk {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoIndicator σ (s(x, y)) = if σ x = σ y then (1 : ℝ) else 0 :=
  Sym2.lift_mk _ _ _

omit [Fintype V] [DecidableEq V] in
lemma monoIndicator_nonneg {q : ℕ} (σ : V → Fin q) (e : Sym2 V) :
    0 ≤ monoIndicator σ e := by
  induction e with
  | _ x y => rw [monoIndicator_mk]; split <;> norm_num

/-- The agreement count: the number of edges of `G` whose endpoints carry the same spin. -/
def agreement {q : ℕ} (σ : V → Fin q) : ℝ :=
  ∑ e ∈ G.edgeFinset, monoIndicator σ e

omit [DecidableEq V] in
lemma agreement_nonneg {q : ℕ} (σ : V → Fin q) : 0 ≤ agreement G σ :=
  Finset.sum_nonneg fun e _ => monoIndicator_nonneg σ e

/-!

## B. Weights and the partition function

-/

/-- The Potts Boltzmann weight `exp (β J · agreement G σ)`. -/
noncomputable def pottsWeight {q : ℕ} (β J : ℝ) (σ : V → Fin q) : ℝ :=
  Real.exp (β * J * agreement G σ)

omit [DecidableEq V] in
lemma pottsWeight_pos {q : ℕ} (β J : ℝ) (σ : V → Fin q) : 0 < pottsWeight G β J σ :=
  Real.exp_pos _

omit [DecidableEq V] in
lemma pottsWeight_nonneg {q : ℕ} (β J : ℝ) (σ : V → Fin q) : 0 ≤ pottsWeight G β J σ :=
  (pottsWeight_pos G β J σ).le

/-- The Potts partition function `Z = ∑_σ exp (β J · agreement G σ)`. -/
noncomputable def pottsZ (q : ℕ) (β J : ℝ) : ℝ :=
  ∑ σ : V → Fin q, pottsWeight G β J σ

lemma pottsZ_pos (q : ℕ) [NeZero q] (β J : ℝ) : 0 < pottsZ G q β J :=
  Finset.sum_pos (fun σ _ => pottsWeight_pos G β J σ) Finset.univ_nonempty

lemma pottsZ_ne_zero (q : ℕ) [NeZero q] (β J : ℝ) : pottsZ G q β J ≠ 0 :=
  (pottsZ_pos G q β J).ne'

/-!

## C. The Potts Gibbs measure

-/

/-- The Potts probability of the spin configuration `σ`. -/
noncomputable def pottsProb (q : ℕ) (β J : ℝ) (σ : V → Fin q) : ℝ :=
  pottsWeight G β J σ / pottsZ G q β J

lemma pottsProb_nonneg (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 ≤ pottsProb G q β J σ :=
  div_nonneg (pottsWeight_nonneg G β J σ) (pottsZ_pos G q β J).le

lemma pottsProb_pos (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 < pottsProb G q β J σ :=
  div_pos (pottsWeight_pos G β J σ) (pottsZ_pos G q β J)

lemma pottsProb_sum_eq_one (q : ℕ) [NeZero q] (β J : ℝ) :
    ∑ σ : V → Fin q, pottsProb G q β J σ = 1 := by
  unfold pottsProb
  rw [← Finset.sum_div]
  exact div_self (pottsZ_ne_zero G q β J)

/-- The Potts Gibbs measure on `V → Fin q` as a probability mass function. -/
noncomputable def pottsPMF (q : ℕ) [NeZero q] (β J : ℝ) : PMF (V → Fin q) :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (pottsProb G q β J σ)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun σ _ => pottsProb_nonneg G q β J σ,
      pottsProb_sum_eq_one]
    simp

@[simp]
lemma pottsPMF_apply (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    pottsPMF G q β J σ = ENNReal.ofReal (pottsProb G q β J σ) :=
  PMF.ofFintype_apply _ _

end Potts

end StatMech
