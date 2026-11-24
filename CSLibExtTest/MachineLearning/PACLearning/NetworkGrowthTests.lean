/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.NetworkGrowth
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Tests for product, composition, and precomposition growth bounds

Exact growth values for full classes on one-, two-, and three-point samples,
a `Fin 2` product instance with its exact product value, a precomposition
instance over an embedding `Fin 2 → Fin 3`, a composition instance where the
sample size exceeds the intermediate type's cardinality so the `min` binds,
and axiom audits for the three public theorems of the production module.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

open Classical

/-- Lower bound on growth from an exhibited sample trace count. -/
private theorem le_growth_of_tracesCard {α β : Type*} [Fintype β]
    (C : ConceptClass α β) (m N : ℕ) (s : Finset α) (hs : s.card = m)
    (hN : tracesCard C s = N) : N ≤ growthFunctionVec C m := by
  unfold growthFunctionVec
  apply le_csSup
  · refine ⟨(Fintype.card β) ^ m, ?_⟩
    rintro n ⟨s', hs', rfl⟩
    calc tracesCard C s' = (traceSetVec C s').card :=
            (traceSetVec_card_eq_tracesCard C s').symm
      _ ≤ (Fintype.card β) ^ s'.card := traceSetVec_card_le C s'
      _ = (Fintype.card β) ^ m := by rw [hs']
  · exact ⟨s, hs, hN⟩

/-- Every labeling of a sample is realized by the full class. -/
private theorem traceSetVec_univ_eq_univ {α β : Type*} [Fintype β]
    [Inhabited β] (s : Finset α) :
    traceSetVec (Set.univ : ConceptClass α β) s = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro t
  rw [mem_traceSetVec]
  refine ⟨fun a => if h : a ∈ s then t ⟨a, h⟩ else default,
    Set.mem_univ _, fun x => ?_⟩
  show t x = (if h : ↑x ∈ s then t ⟨↑x, h⟩ else (default : β))
  rw [dite_eq_left x.2]

/-- Trace count of the full class on any sample. -/
private theorem tracesCard_univ_eq {α β : Type*} [Fintype β] [Inhabited β]
    (s : Finset α) :
    tracesCard (Set.univ : ConceptClass α β) s
      = (Fintype.card β) ^ s.card := by
  rw [← traceSetVec_card_eq_tracesCard, traceSetVec_univ_eq_univ,
    Finset.card_univ, Fintype.card_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe]

/-- Growth of the full class when an `m`-sample exists. -/
private theorem growth_univ_eq {α β : Type*} [Fintype β] [Inhabited β]
    (m : ℕ) (hex : ∃ s0 : Finset α, s0.card = m) :
    growthFunctionVec (Set.univ : ConceptClass α β) m
      = (Fintype.card β) ^ m := by
  apply le_antisymm
  · exact growthFunctionVec_le_pow _ m
  · obtain ⟨s, hs⟩ := hex
    have h := le_growth_of_tracesCard (Set.univ : ConceptClass α β) m _
      s hs (tracesCard_univ_eq s)
    rw [hs] at h
    exact h

/-- A one-point sample of `Fin 1` exists. -/
private theorem hex_fin1 : ∃ s0 : Finset (Fin 1), s0.card = 1 :=
  ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]⟩

/-- A two-point sample of `Fin 2` exists. -/
private theorem hex_fin2 : ∃ s0 : Finset (Fin 2), s0.card = 2 :=
  ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]⟩

/-- A two-point sample of `Fin 3` exists. -/
private theorem hex_fin3_2 : ∃ s0 : Finset (Fin 3), s0.card = 2 :=
  ⟨({0, 1} : Finset (Fin 3)), by decide⟩

/-- A three-point sample of `Fin 3` exists. -/
private theorem hex_fin3_3 : ∃ s0 : Finset (Fin 3), s0.card = 3 :=
  ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]⟩

/-- The product of full classes over `Fin 2` is the full class. -/
private theorem piClass_univ : piClass (fun _ : Fin 2 =>
    (Set.univ : ConceptClass (Fin 1) Bool)) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ => Set.mem_univ _

/-- Exact growth of the `Fin 2` product of full classes. -/
example : growthFunctionVec
    (piClass (fun _ : Fin 2 => (Set.univ : ConceptClass (Fin 1) Bool)))
    1 = 4 := by
  calc growthFunctionVec
        (piClass (fun _ : Fin 2 => (Set.univ : ConceptClass (Fin 1) Bool)))
        1
      = ((2 : ℕ) ^ 2) ^ 1 := by
        rw [piClass_univ, growth_univ_eq 1 hex_fin1, Fintype.card_pi_const,
          Fintype.card_bool]
    _ = 4 := rfl

/-- Exact value of the factor product for the `Fin 2` instance. -/
example : (∏ _ : Fin 2,
    growthFunctionVec (Set.univ : ConceptClass (Fin 1) Bool) 1) = 4 := by
  have hf : growthFunctionVec (Set.univ : ConceptClass (Fin 1) Bool) 1
      = 2 := by
    rw [growth_univ_eq 1 hex_fin1, Fintype.card_bool, pow_one]
  calc (∏ _ : Fin 2,
        growthFunctionVec (Set.univ : ConceptClass (Fin 1) Bool) 1)
      = 2 * 2 := by simp only [Fin.prod_univ_two, hf]
    _ = 4 := rfl

/-- The product bound on the `Fin 2` full-class instance. -/
example : growthFunctionVec
    (piClass (fun _ : Fin 2 => (Set.univ : ConceptClass (Fin 1) Bool)))
    1 ≤ ∏ _ : Fin 2,
      growthFunctionVec (Set.univ : ConceptClass (Fin 1) Bool) 1 :=
  growthFunctionVec_pi_le
    (fun _ : Fin 2 => (Set.univ : ConceptClass (Fin 1) Bool)) 1

/-- A concrete injective embedding `Fin 2 → Fin 3`. -/
private def emb23 : Fin 2 → Fin 3 := fun i => ⟨i.val, by omega⟩

/-- The embedding is injective. -/
private theorem emb23_injective : Function.Injective emb23 := by
  intro a b h
  have hval := congrArg Fin.val h
  exact Fin.ext hval

/-- Precomposing the full class along an injective map stays full. -/
private theorem precompClass_univ {α' α β : Type*} [Inhabited β]
    {f : α' → α} (hf : Function.Injective f) :
    precompClass f (Set.univ : ConceptClass α β) = Set.univ := by
  refine Set.eq_univ_of_forall fun c =>
    ⟨fun y => if h : ∃ x : α', f x = y then c (Classical.choose h)
      else default, Set.mem_univ _, ?_⟩
  funext x
  rw [Function.comp_apply, dite_eq_left ⟨x, rfl⟩]
  congr 1
  apply hf
  exact (Classical.choose_spec (p := fun x' => f x' = f x) ⟨x, rfl⟩).symm

/-- Exact growth of the precomposed full class along the embedding. -/
example : growthFunctionVec
    (precompClass emb23 (Set.univ : ConceptClass (Fin 3) Bool)) 2 = 4 := by
  calc growthFunctionVec
        (precompClass emb23 (Set.univ : ConceptClass (Fin 3) Bool)) 2
      = ((2 : ℕ) ^ 2) := by
        rw [precompClass_univ emb23_injective, growth_univ_eq 2 hex_fin2,
          Fintype.card_bool]
    _ = 4 := rfl

/-- Exact growth of the full class on `Fin 3` at size two. -/
example : growthFunctionVec (Set.univ : ConceptClass (Fin 3) Bool) 2
    = 4 := by
  calc growthFunctionVec (Set.univ : ConceptClass (Fin 3) Bool) 2
      = ((2 : ℕ) ^ 2) := by
        rw [growth_univ_eq 2 hex_fin3_2, Fintype.card_bool]
    _ = 4 := rfl

/-- The precomposition bound on the embedding instance. -/
example : growthFunctionVec
    (precompClass emb23 (Set.univ : ConceptClass (Fin 3) Bool)) 2 ≤
    growthFunctionVec (Set.univ : ConceptClass (Fin 3) Bool) 2 :=
  growthFunctionVec_precomp_le emb23_injective
    (Set.univ : ConceptClass (Fin 3) Bool) 2

/-- Composing full classes over a two-point intermediate type stays full. -/
private theorem compClass_univ :
    compClass (Set.univ : ConceptClass (Fin 3) (Fin 2))
      (Set.univ : ConceptClass (Fin 2) Bool) = Set.univ := by
  refine Set.eq_univ_of_forall fun c =>
    ⟨fun x => if c x then (1 : Fin 2) else 0, Set.mem_univ _,
      fun y => y.val != 0, Set.mem_univ _, ?_⟩
  intro x
  cases hc : c x
  · simp only []
    rw [hc]
    rfl
  · simp only []
    rw [hc]
    rfl

/-- Exact growth of the composed full classes at size three. -/
example : growthFunctionVec
    (compClass (Set.univ : ConceptClass (Fin 3) (Fin 2))
      (Set.univ : ConceptClass (Fin 2) Bool)) 3 = 8 := by
  calc growthFunctionVec
        (compClass (Set.univ : ConceptClass (Fin 3) (Fin 2))
          (Set.univ : ConceptClass (Fin 2) Bool)) 3
      = ((2 : ℕ) ^ 3) := by
        rw [compClass_univ, growth_univ_eq 3 hex_fin3_3, Fintype.card_bool]
    _ = 8 := rfl

/-- Exact value of the right-hand side on the composition instance. -/
example : growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool)
      (min 3 (Fintype.card (Fin 2))) *
      growthFunctionVec (Set.univ : ConceptClass (Fin 3) (Fin 2)) 3
    = 32 := by
  have hmin : min 3 (Fintype.card (Fin 2)) = 2 := by decide
  calc growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool)
          (min 3 (Fintype.card (Fin 2))) *
          growthFunctionVec (Set.univ : ConceptClass (Fin 3) (Fin 2)) 3
      = ((2 : ℕ) ^ 2) * (2 ^ 3) := by
        rw [hmin, growth_univ_eq 2 hex_fin2, growth_univ_eq 3 hex_fin3_3,
          Fintype.card_bool, Fintype.card_fin]
    _ = 32 := rfl

/-- The capped composition bound on the `3 > card (Fin 2)` instance. -/
example : growthFunctionVec
    (compClass (Set.univ : ConceptClass (Fin 3) (Fin 2))
      (Set.univ : ConceptClass (Fin 2) Bool)) 3 ≤
    growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool)
      (min 3 (Fintype.card (Fin 2))) *
      growthFunctionVec (Set.univ : ConceptClass (Fin 3) (Fin 2)) 3 :=
  growthFunctionVec_comp_le_card (Set.univ : ConceptClass (Fin 3) (Fin 2))
    (Set.univ : ConceptClass (Fin 2) Bool) 3

#print axioms growthFunctionVec_pi_le
#print axioms growthFunctionVec_comp_le_card
#print axioms growthFunctionVec_precomp_le

end Cslib.MachineLearning.PACLearning
