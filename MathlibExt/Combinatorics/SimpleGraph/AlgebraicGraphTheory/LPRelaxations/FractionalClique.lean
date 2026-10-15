/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.NormNum.Basic
/-!
# FractionalClique

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 436
-/

@[expose] public section

open SimpleGraph

-- Combinatorics 436: Fractional clique/fractional clique number
structure FracClique {V : Type*} [Fintype V] (G : SimpleGraph V) where
  w : V → ℝ
  nonneg : ∀ v, 0 ≤ w v
  indep_le : ∀ s : Finset V, G.IsIndepSet s → ∑ v ∈ s, w v ≤ 1


def FracClique.weight {V : Type*} [Fintype V] {G : SimpleGraph V}
    (c : FracClique G) : ℝ :=
  ∑ v ∈ Finset.univ, c.w v


noncomputable def SimpleGraph.fracCliqueNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℝ :=
  sSup {q : ℝ | ∃ c : FracClique G, c.weight = q}


abbrev K2fc := completeGraph (Fin 2)


/-- The fractional clique on `K₂` weighing each vertex `1 / 2`. -/
noncomputable def fc : FracClique K2fc where
  w := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  indep_le := by
    intro s _
    rw [Finset.sum_const, nsmul_eq_mul]
    have hle : s.card ≤ 2 := by
      calc s.card ≤ Fintype.card (Fin 2) := Finset.card_le_univ s
        _ = 2 := by simp
    have hleR : (s.card : ℝ) ≤ 2 := by exact_mod_cast hle
    linarith

-- The fractional clique`fc` has total weight 1.

theorem fc_weight : fc.weight = 1 := by
  show (∑ _v : Fin 2, (1 / 2 : ℝ)) = 1
  rw [Finset.sum_const, nsmul_eq_mul]
  norm_num [Finset.card_univ]

-- The fractional clique number of `K₂` exceeds `1 / 2`, witnessed by `fc`.
example : 1 / 2 < K2fc.fracCliqueNumber := by
  have hbdd : BddAbove {q : ℝ | ∃ c : FracClique K2fc, c.weight = q} := by
    refine ⟨2, ?_⟩
    rintro q ⟨c, rfl⟩
    have h0 : c.w 0 ≤ 1 := by
      have h := c.indep_le ({0} : Finset (Fin 2)) (by decide)
      rwa [Finset.sum_singleton] at h
    have h1 : c.w 1 ≤ 1 := by
      have h := c.indep_le ({1} : Finset (Fin 2)) (by decide)
      rwa [Finset.sum_singleton] at h
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    show (∑ v ∈ Finset.univ, c.w v) ≤ 2
    rw [huniv, Finset.sum_pair (by decide)]
    linarith
  have hle : fc.weight ≤ K2fc.fracCliqueNumber := le_csSup hbdd ⟨fc, rfl⟩
  rw [fc_weight] at hle
  linarith

end
