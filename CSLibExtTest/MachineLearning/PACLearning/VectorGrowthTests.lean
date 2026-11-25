/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.VectorGrowth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Tests for vector-valued growth functions

Exact growth values for the empty and full classes on one- and two-point
samples, a singleton-class trace count, a `Bool` bridge instance against
`growthFunction`, empty and full product and composition growth values with
composition bound instances, and axiom audits for the eleven public theorems
of the production module.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-- The empty class realizes no labelings on any sample. -/
private theorem trace_empty_vec {α β : Type*} [Fintype β] (s : Finset α) :
    traceSetVec (∅ : ConceptClass α β) s = ∅ := by
  ext t
  simp only [mem_traceSetVec, Finset.notMem_empty]
  exact iff_false_intro fun ⟨c, hc, _⟩ => Set.notMem_empty c hc

/-- The empty class has growth `0` at every sample size. -/
private theorem growth_empty_vec {α β : Type*} [Fintype β] (m : ℕ) :
    growthFunctionVec (∅ : ConceptClass α β) m = 0 := by
  apply le_antisymm
  · unfold growthFunctionVec
    apply csSup_le'
    rintro k ⟨s, hs, rfl⟩
    have hcard : (traceSetVec (∅ : ConceptClass α β) s).card = 0 := by
      rw [trace_empty_vec, Finset.card_empty]
    rw [← traceSetVec_card_eq_tracesCard]
    exact hcard.le
  · exact Nat.zero_le _

/-- The full class realizes every labeling on any sample. -/
private theorem trace_univ_vec (s : Finset (Fin 2)) :
    traceSetVec (Set.univ : ConceptClass (Fin 2) Bool) s = Finset.univ := by
  classical
  ext t
  simp only [mem_traceSetVec, Finset.mem_univ]
  exact iff_true_intro
    ⟨fun a => if h : a ∈ s then t ⟨a, h⟩ else false,
      Set.mem_univ _,
      fun x => (ite_eq_left x.2).symm⟩

/-- Growth of the full class on one-point samples is `2`. -/
private theorem growth_univ_one :
    growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool) 1 = 2 := by
  apply le_antisymm
  · calc growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool) 1
        ≤ (Fintype.card Bool) ^ 1 := growthFunctionVec_le_pow _ _
      _ = 2 ^ 1 := by rw [Fintype.card_bool]
      _ = 2 := pow_one 2
  · have h1 : (traceSetVec (Set.univ : ConceptClass (Fin 2) Bool) {0}).card
        = 2 := by
      rw [trace_univ_vec, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ, Fintype.card_coe, Finset.card_singleton,
        Fintype.card_bool, pow_one]
    have h2 := traceSetVec_card_le_growthFunctionVec
      (Set.univ : ConceptClass (Fin 2) Bool) {0}
    rw [h1, Finset.card_singleton] at h2
    exact h2

/-- Growth of the full class on two-point samples is `4`. -/
private theorem growth_univ_two :
    growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool) 2 = 4 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  apply le_antisymm
  · calc growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool) 2
        ≤ (Fintype.card Bool) ^ 2 := growthFunctionVec_le_pow _ _
      _ = 2 ^ 2 := by rw [Fintype.card_bool]
      _ = 2 * 2 := pow_two 2
      _ = 4 := rfl
  · have h2 : (traceSetVec (Set.univ : ConceptClass (Fin 2) Bool) {0, 1}).card
        = 4 := by
      rw [trace_univ_vec, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ, Fintype.card_coe, Finset.card_pair h01,
        Fintype.card_bool]
      decide
    have h3 := traceSetVec_card_le_growthFunctionVec
      (Set.univ : ConceptClass (Fin 2) Bool) {0, 1}
    rw [h2, Finset.card_pair h01] at h3
    exact h3

/-- The empty class realizes nothing on a one-point sample. -/
example : (traceSetVec (∅ : ConceptClass (Fin 2) Bool) {0}).card = 0 := by
  rw [trace_empty_vec, Finset.card_empty]

/-- The empty class realizes nothing on a two-point sample. -/
example : (traceSetVec (∅ : ConceptClass (Fin 2) Bool) {0, 1}).card
    = 0 := by
  rw [trace_empty_vec, Finset.card_empty]

/-- The empty class has growth `0` on one-point samples. -/
example : growthFunctionVec (∅ : ConceptClass (Fin 2) Bool) 1 = 0 :=
  growth_empty_vec 1

/-- The empty class has growth `0` on two-point samples. -/
example : growthFunctionVec (∅ : ConceptClass (Fin 2) Bool) 2 = 0 :=
  growth_empty_vec 2

/-- The full class has growth `2` on one-point samples. -/
example : growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool) 1 = 2 :=
  growth_univ_one

/-- The full class has growth `4` on two-point samples. -/
example : growthFunctionVec (Set.univ : ConceptClass (Fin 2) Bool) 2 = 4 :=
  growth_univ_two

/-- The `Bool` bridge computes `growthFunction` of the full class. -/
example : growthFunction (Set.univ : ConceptClass (Fin 2) Bool) 2 = 4 := by
  rw [← growthFunctionVec_bool_eq]
  exact growth_univ_two

/-- The singleton class realizes one labeling on a one-point sample. -/
example : (traceSetVec ({fun _ => true} : ConceptClass (Fin 2) Bool) {0}).card
    = 1 := by
  have hsub : traceSetVec ({fun _ => true} : ConceptClass (Fin 2) Bool) {0}
      = {(fun _ => true)} := by
    ext t
    simp only [mem_traceSetVec, Finset.mem_singleton]
    constructor
    · rintro ⟨c, hc, hcu⟩
      rw [Set.mem_singleton_iff] at hc
      subst hc
      funext x
      exact hcu x
    · intro ht
      subst ht
      exact ⟨fun _ => true, Set.mem_singleton _, fun x => rfl⟩
  rw [hsub, Finset.card_singleton]

/-- The product of empty classes is empty. -/
private theorem prod_empty_vec :
    prodClass (∅ : ConceptClass (Fin 2) Bool) (∅ : ConceptClass (Fin 2) Bool)
      = ∅ := by
  ext c
  constructor
  · rintro ⟨c₁, hc₁, _, _, _⟩
    exact absurd hc₁ (Set.notMem_empty _)
  · intro hc
    exact absurd hc (Set.notMem_empty _)

/-- The composition of empty classes is empty. -/
private theorem comp_empty_vec :
    compClass (∅ : ConceptClass (Fin 2) Bool) (∅ : ConceptClass Bool Bool)
      = ∅ := by
  ext c
  constructor
  · rintro ⟨c₁, hc₁, _, _, _⟩
    exact absurd hc₁ (Set.notMem_empty _)
  · intro hc
    exact absurd hc (Set.notMem_empty _)

/-- Growth of the empty product on one-point samples is `0`. -/
private theorem growth_prod_empty :
    growthFunctionVec
      (prodClass (∅ : ConceptClass (Fin 2) Bool) (∅ : ConceptClass (Fin 2) Bool))
      1 = 0 := by
  rw [prod_empty_vec]
  exact growth_empty_vec 1

/-- Growth of the empty composition on one-point samples is `0`. -/
private theorem growth_comp_empty :
    growthFunctionVec
      (compClass (∅ : ConceptClass (Fin 2) Bool) (∅ : ConceptClass Bool Bool))
      1 = 0 := by
  rw [comp_empty_vec]
  exact growth_empty_vec 1

/-- The empty product has growth `0` on one-point samples. -/
example : growthFunctionVec
    (prodClass (∅ : ConceptClass (Fin 2) Bool) (∅ : ConceptClass (Fin 2) Bool))
    1 = 0 :=
  growth_prod_empty

/-- The empty composition has growth `0` on one-point samples. -/
example : growthFunctionVec
    (compClass (∅ : ConceptClass (Fin 2) Bool) (∅ : ConceptClass Bool Bool))
    1 = 0 :=
  growth_comp_empty

/-- The composition bound on empty classes reduces to `0 ≤ 0 * 0`. -/
example : (0 : ℕ) ≤ 0 * 0 := by
  simpa only [growth_comp_empty, growth_empty_vec] using
    growthFunctionVec_comp_le (∅ : ConceptClass (Fin 2) Bool)
      (∅ : ConceptClass Bool Bool) 1 ⟨{true}, Finset.card_singleton _⟩

/-- The full product class realizes every labeling on any sample. -/
private theorem trace_prod_univ (s : Finset (Fin 2)) :
    traceSetVec
      (prodClass (Set.univ : ConceptClass (Fin 2) Bool)
        (Set.univ : ConceptClass (Fin 2) Bool)) s = Finset.univ := by
  classical
  ext t
  simp only [mem_traceSetVec, Finset.mem_univ]
  exact iff_true_intro
    ⟨fun a => ((if h : a ∈ s then (t ⟨a, h⟩).1 else false),
        (if h : a ∈ s then (t ⟨a, h⟩).2 else false)),
      ⟨fun a => if h : a ∈ s then (t ⟨a, h⟩).1 else false, Set.mem_univ _,
        fun a => if h : a ∈ s then (t ⟨a, h⟩).2 else false, Set.mem_univ _,
        fun x => rfl⟩,
      fun x => Prod.ext (ite_eq_left x.2).symm (ite_eq_left x.2).symm⟩

/-- Growth of the full product on one-point samples is `4`. -/
private theorem growth_prod_univ_one :
    growthFunctionVec
      (prodClass (Set.univ : ConceptClass (Fin 2) Bool)
        (Set.univ : ConceptClass (Fin 2) Bool))
      1 = 4 := by
  apply le_antisymm
  · calc growthFunctionVec
          (prodClass (Set.univ : ConceptClass (Fin 2) Bool)
            (Set.univ : ConceptClass (Fin 2) Bool)) 1
        ≤ (Fintype.card (Bool × Bool)) ^ 1 := growthFunctionVec_le_pow _ _
      _ = (2 * 2) ^ 1 := by rw [Fintype.card_prod, Fintype.card_bool]
      _ = 4 := by decide
  · have h1 : (traceSetVec
          (prodClass (Set.univ : ConceptClass (Fin 2) Bool)
            (Set.univ : ConceptClass (Fin 2) Bool)) {0}).card = 4 := by
      rw [trace_prod_univ, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ, Fintype.card_coe, Finset.card_singleton,
        Fintype.card_prod, Fintype.card_bool]
      decide
    have h2 := traceSetVec_card_le_growthFunctionVec
      (prodClass (Set.univ : ConceptClass (Fin 2) Bool)
        (Set.univ : ConceptClass (Fin 2) Bool)) {0}
    rw [h1, Finset.card_singleton] at h2
    exact h2

/-- The full composition class realizes every labeling on any sample. -/
private theorem trace_comp_univ (s : Finset (Fin 2)) :
    traceSetVec
      (compClass (Set.univ : ConceptClass (Fin 2) (Fin 2))
        (Set.univ : ConceptClass (Fin 2) Bool)) s = Finset.univ := by
  classical
  ext t
  simp only [mem_traceSetVec, Finset.mem_univ]
  exact iff_true_intro
    ⟨fun a => if h : a ∈ s then t ⟨a, h⟩ else false,
      ⟨id, Set.mem_univ _,
        fun a => if h : a ∈ s then t ⟨a, h⟩ else false, Set.mem_univ _,
        fun x => rfl⟩,
      fun x => (ite_eq_left x.2).symm⟩

/-- Growth of the full composition on one-point samples is `2`. -/
private theorem growth_comp_univ_one :
    growthFunctionVec
      (compClass (Set.univ : ConceptClass (Fin 2) (Fin 2))
        (Set.univ : ConceptClass (Fin 2) Bool))
      1 = 2 := by
  apply le_antisymm
  · calc growthFunctionVec
          (compClass (Set.univ : ConceptClass (Fin 2) (Fin 2))
            (Set.univ : ConceptClass (Fin 2) Bool)) 1
        ≤ (Fintype.card Bool) ^ 1 := growthFunctionVec_le_pow _ _
      _ = 2 ^ 1 := by rw [Fintype.card_bool]
      _ = 2 := pow_one 2
  · have h1 : (traceSetVec
          (compClass (Set.univ : ConceptClass (Fin 2) (Fin 2))
            (Set.univ : ConceptClass (Fin 2) Bool)) {0}).card = 2 := by
      rw [trace_comp_univ, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ, Fintype.card_coe, Finset.card_singleton,
        Fintype.card_bool, pow_one]
    have h2 := traceSetVec_card_le_growthFunctionVec
      (compClass (Set.univ : ConceptClass (Fin 2) (Fin 2))
        (Set.univ : ConceptClass (Fin 2) Bool)) {0}
    rw [h1, Finset.card_singleton] at h2
    exact h2

/-- The full `Fin 2`-labeled class realizes every labeling on any sample. -/
private theorem trace_univ_fin2 (s : Finset (Fin 2)) :
    traceSetVec (Set.univ : ConceptClass (Fin 2) (Fin 2)) s = Finset.univ := by
  classical
  ext t
  simp only [mem_traceSetVec, Finset.mem_univ]
  exact iff_true_intro
    ⟨fun a => if h : a ∈ s then t ⟨a, h⟩ else 0,
      Set.mem_univ _,
      fun x => (ite_eq_left x.2).symm⟩

/-- Growth of the full `Fin 2`-labeled class on one-point samples is `2`. -/
private theorem growth_univ_fin2_one :
    growthFunctionVec (Set.univ : ConceptClass (Fin 2) (Fin 2)) 1 = 2 := by
  apply le_antisymm
  · calc growthFunctionVec (Set.univ : ConceptClass (Fin 2) (Fin 2)) 1
        ≤ (Fintype.card (Fin 2)) ^ 1 := growthFunctionVec_le_pow _ _
      _ = 2 ^ 1 := by rw [Fintype.card_fin]
      _ = 2 := pow_one 2
  · have h1 : (traceSetVec (Set.univ : ConceptClass (Fin 2) (Fin 2)) {0}).card
        = 2 := by
      rw [trace_univ_fin2, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ, Fintype.card_coe, Finset.card_singleton,
        Fintype.card_fin, pow_one]
    have h2 := traceSetVec_card_le_growthFunctionVec
      (Set.univ : ConceptClass (Fin 2) (Fin 2)) {0}
    rw [h1, Finset.card_singleton] at h2
    exact h2

/-- The full product has growth `4` on one-point samples. -/
example : growthFunctionVec
    (prodClass (Set.univ : ConceptClass (Fin 2) Bool)
      (Set.univ : ConceptClass (Fin 2) Bool))
    1 = 4 :=
  growth_prod_univ_one

/-- The full composition has growth `2` on one-point samples. -/
example : growthFunctionVec
    (compClass (Set.univ : ConceptClass (Fin 2) (Fin 2))
      (Set.univ : ConceptClass (Fin 2) Bool))
    1 = 2 :=
  growth_comp_univ_one

/-- The composition bound on full classes reduces to `2 ≤ 2 * 2`. -/
example : (2 : ℕ) ≤ 2 * 2 := by
  simpa only [growth_comp_univ_one, growth_univ_one, growth_univ_fin2_one] using
    growthFunctionVec_comp_le (Set.univ : ConceptClass (Fin 2) (Fin 2))
      (Set.univ : ConceptClass (Fin 2) Bool) 1 ⟨{0}, Finset.card_singleton _⟩

#print axioms mem_traceSetVec
#print axioms traceSetVec_card_le
#print axioms traceSetVec_card_le_growthFunctionVec
#print axioms growthFunctionVec_le_pow
#print axioms exists_traceSetVec_card_eq_growthFunctionVec
#print axioms traceSetVec_card_mono
#print axioms growthFunctionVec_mono
#print axioms growthFunctionVec_bool_eq
#print axioms growthFunctionVec_prod_le
#print axioms growthFunctionVec_comp_le
#print axioms traceSetVec_card_eq_tracesCard

end Cslib.MachineLearning.PACLearning
