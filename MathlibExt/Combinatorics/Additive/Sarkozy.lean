/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-!
# Furstenberg–Sárközy square-difference theorem

Records the Furstenberg–Sárközy theorem that positive upper density sets contain two
elements differing by a nonzero square.
-/

/-- **Initial segment count.** For a set $A$ of natural numbers and a natural number $N$, the
initial segment count of $A$ at $N$ is the number of elements of $A$ that are less than $N$, that
is, $|A \cap \{0, 1, \dots, N - 1\}|$. -/
noncomputable def initialSegmentCount (A : Set ℕ) (N : ℕ) : ℕ :=
  by classical exact ((Finset.range N).filter (fun n => n ∈ A)).card

/-- Finite initial segment of `A`: elements of `A` below `N`. -/
private noncomputable def sarkozyFin (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  by classical exact (Finset.range N).filter (fun n => n ∈ A)

/-- `sarkozyFin` counts the same as `initialSegmentCount`. -/
private lemma sarkozyFin_card (A : Set ℕ) (N : ℕ) :
    (sarkozyFin A N).card = initialSegmentCount A N :=
  rfl

/-- Membership in `sarkozyFin`. -/
private lemma sarkozyFin_mem (A : Set ℕ) (N : ℕ) (n : ℕ) :
    n ∈ sarkozyFin A N ↔ n ∈ Finset.range N ∧ n ∈ A := by
  simp only [sarkozyFin, Finset.mem_filter]

/-- Correlation count: pairs in `A_N × A_N` with difference `d`. -/
private noncomputable def sarkozyCorr (A : Set ℕ) (N : ℕ) (d : ℤ) : ℕ :=
  (((sarkozyFin A N) ×ˢ (sarkozyFin A N)).filter
    (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = d)).card

/-- Image of `A_N × s` under `(a, i) ↦ a - e i`. -/
private noncomputable def sarkozyIm {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) : Finset ℤ :=
  ((sarkozyFin A N) ×ˢ s).image (fun p : ℕ × ι => (p.1 : ℤ) - e p.2)

/-- Fiber weight for the sum-of-squares identity. -/
private noncomputable def sarkozyW {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) (t : ℤ) : ℝ :=
  ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, (if (a : ℤ) - e i = t then c i else 0)

/-- Each correlation count as a sum of indicators over the product. -/
private lemma sarkozyCorr_eq_sum (A : Set ℕ) (N : ℕ) {ι : Type*} (e : ι → ℤ)
    (i j : ι) :
    ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ)
      = ∑ x ∈ (sarkozyFin A N) ×ˢ (sarkozyFin A N),
        (if (x.1 : ℤ) - (x.2 : ℤ) = e i - e j then (1 : ℝ) else 0) := by
  simp only [sarkozyCorr, ← Finset.sum_boole]

/-- The fiber weight as a single sum over the product. -/
private lemma sarkozyW_eq_sum {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) (t : ℤ) :
    sarkozyW A N s e c t
      = ∑ x ∈ (sarkozyFin A N) ×ˢ s,
        (if (x.1 : ℤ) - e x.2 = t then c x.2 else 0) := by
  simp only [sarkozyW, Finset.sum_product]

/-- Left-hand side of the identity as a four-fold sum. -/
private lemma sarkozyLHS_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ))
      = ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ sarkozyFin A N, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [sarkozyCorr_eq_sum A N e i j,
    Finset.mul_sum _ _ (c i * c j), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : (a : ℤ) - (b : ℤ) = e i - e j
  · have h' : (a : ℤ) - e i = (b : ℤ) - e j :=
      sub_eq_sub_iff_sub_eq_sub.mp h
    simp [h, h']
  · have h' : ¬ ((a : ℤ) - e i = (b : ℤ) - e j) :=
      fun hh => h (sub_eq_sub_iff_sub_eq_sub.mpr hh)
    simp [h, h']

/-- The inner `t`-sum collapses to a single Kronecker term. -/
private lemma sarkozyTsum_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) (x y : ℕ × ι)
    (hx : x ∈ (sarkozyFin A N) ×ˢ s) :
    (∑ t ∈ sarkozyIm A N s e,
      ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
        * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)))
    = (if (x.1 : ℤ) - e x.2 = (y.1 : ℤ) - e y.2 then c x.2 * c y.2 else 0) := by
  by_cases hxy : (x.1 : ℤ) - e x.2 = (y.1 : ℤ) - e y.2
  · have hmem : (x.1 : ℤ) - e x.2 ∈ sarkozyIm A N s e := by
      simp only [sarkozyIm, Finset.mem_image]
      exact ⟨x, hx, rfl⟩
    have hterm : ∀ t ∈ sarkozyIm A N s e,
        (if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)
        = (if (x.1 : ℤ) - e x.2 = t then c x.2 * c y.2 else 0) := by
      intro t _
      rw [← hxy]
      by_cases h : (x.1 : ℤ) - e x.2 = t <;> simp [h]
    have hval : (∑ t ∈ sarkozyIm A N s e,
        ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)))
        = c x.2 * c y.2 := by
      rw [(Finset.sum_congr rfl hterm), Finset.sum_ite_eq, ite_eq_left hmem]
    rw [hval, ite_eq_left hxy]
  · have hterm : ∀ t ∈ sarkozyIm A N s e,
        (if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0) = 0 := by
      intro t _
      by_cases h1 : (x.1 : ℤ) - e x.2 = t
      · by_cases h2 : (y.1 : ℤ) - e y.2 = t
        · exact absurd (h1.trans h2.symm) hxy
        · simp [h2]
      · simp [h1]
    have hzero : (∑ t ∈ sarkozyIm A N s e,
        ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
          * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0))) = 0 :=
      Finset.sum_eq_zero hterm
    rw [hzero, ite_eq_right hxy]

/-- Product sums unfold to iterated sums. -/
private lemma sarkozyProd_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (G : (ℕ × ι) → (ℕ × ι) → ℝ) :
    (∑ x ∈ (sarkozyFin A N) ×ˢ s, ∑ y ∈ (sarkozyFin A N) ×ˢ s, G x y)
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ b ∈ sarkozyFin A N, ∑ j ∈ s,
        G (a, i) (b, j) := by
  simp only [Finset.sum_product]

/-- Right-hand side of the identity as a four-fold sum. -/
private lemma sarkozyRHS_eq {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) :
    (∑ t ∈ sarkozyIm A N s e, (sarkozyW A N s e c t) ^ 2)
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ b ∈ sarkozyFin A N, ∑ j ∈ s,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) := by
  have hexpand : ∀ t ∈ sarkozyIm A N s e,
      (sarkozyW A N s e c t) ^ 2
        = ∑ x ∈ (sarkozyFin A N) ×ˢ s, ∑ y ∈ (sarkozyFin A N) ×ˢ s,
          ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
            * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0)) := by
    intro t _
    rw [sarkozyW_eq_sum A N s e c t, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl hexpand]
  trans ∑ x ∈ (sarkozyFin A N) ×ˢ s, ∑ y ∈ (sarkozyFin A N) ×ˢ s,
    ∑ t ∈ sarkozyIm A N s e,
      ((if (x.1 : ℤ) - e x.2 = t then c x.2 else 0)
        * (if (y.1 : ℤ) - e y.2 = t then c y.2 else 0))
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_comm
  · rw [Finset.sum_congr rfl (fun x hx =>
      Finset.sum_congr rfl (fun y _ => sarkozyTsum_eq A N s e c x y hx))]
    exact sarkozyProd_eq A N s _

/-- The correlation sum-of-squares identity (N1). -/
private lemma sarkozy_corr_sum_sq_identity {ι : Type*} (A : Set ℕ) (N : ℕ)
    (s : Finset ι) (e : ι → ℤ) (c : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ))
      = ∑ t ∈ (sarkozyIm A N s e), (sarkozyW A N s e c t) ^ 2 := by
  have step1 : (∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ sarkozyFin A N, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0))
      = ∑ i ∈ s, ∑ a ∈ sarkozyFin A N, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have step2 : (∑ i ∈ s, ∑ a ∈ sarkozyFin A N, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0))
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) :=
    Finset.sum_comm
  have step3 : (∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ j ∈ s, ∑ b ∈ sarkozyFin A N,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0))
      = ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, ∑ b ∈ sarkozyFin A N, ∑ j ∈ s,
        (if (a : ℤ) - e i = (b : ℤ) - e j then c i * c j else 0) :=
    Finset.sum_congr rfl
      (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
  rw [sarkozyLHS_eq A N s e c, step1, step2, step3, sarkozyRHS_eq A N s e c]

/-- Positive semidefiniteness of the finite correlations (N1 consequence). -/
private lemma sarkozy_corr_nonneg {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * ((sarkozyCorr A N (e i - e j) : ℕ) : ℝ) := by
  rw [sarkozy_corr_sum_sq_identity A N s e c]
  exact Finset.sum_nonneg (fun t _ => sq_nonneg _)

/-- Correlations are even (N2a). -/
private lemma sarkozy_corr_neg (A : Set ℕ) (N : ℕ) (d : ℤ) :
    sarkozyCorr A N (-d) = sarkozyCorr A N d := by
  simp only [sarkozyCorr]
  apply Finset.card_bij (fun p _ => p.swap)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
      Prod.snd_swap] at hp ⊢
    obtain ⟨⟨ha, hb⟩, h⟩ := hp
    exact ⟨⟨hb, ha⟩, by omega⟩
  · intro a₁ _ a₂ _ h
    simpa using congrArg Prod.swap h
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hmem, h⟩ := hb
    rw [Finset.mem_product] at hmem
    refine ⟨b.swap, ?_, Prod.swap_swap b⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_product]
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨hmem.2, hmem.1⟩
    · simp only [Prod.fst_swap, Prod.snd_swap]
      omega

/-- Correlations are bounded by the initial segment count (N2b). -/
private lemma sarkozy_corr_le_card (A : Set ℕ) (N : ℕ) (d : ℤ) :
    sarkozyCorr A N d ≤ (sarkozyFin A N).card := by
  simp only [sarkozyCorr]
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_coe]
    exact hp.1.1
  · intro p hp q hq h
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    obtain ⟨_, hp2⟩ := hp
    obtain ⟨_, hq2⟩ := hq
    have h1 : p.1 = q.1 := h
    have h2 : p.2 = q.2 := by omega
    exact Prod.ext h1 h2

/-- The initial segment count is bounded by `N` (N2b). -/
private lemma sarkozy_card_le (A : Set ℕ) (N : ℕ) :
    (sarkozyFin A N).card ≤ N := by
  have hsub : sarkozyFin A N ⊆ Finset.range N := by
    intro n hn
    exact (sarkozyFin_mem A N n |>.mp hn).1
  calc (sarkozyFin A N).card ≤ (Finset.range N).card := Finset.card_le_card hsub
    _ = N := Finset.card_range N

/-- Correlations vanish at positive squares under NSD (N2c). -/
private lemma sarkozy_corr_sq_eq_zero (A : Set ℕ) (N : ℕ) (k : ℕ) (hk : 0 < k)
    (hNSD : ∀ a b k : ℕ, a ∈ A → b ∈ A → 0 < k → a < b → b ≠ a + k * k) :
    sarkozyCorr A N ((k : ℤ) * k) = 0 := by
  simp only [sarkozyCorr]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [Finset.mem_product] at hp
  obtain ⟨ha, hb⟩ := hp
  rw [sarkozyFin_mem] at ha hb
  intro hcon
  have hpos : (0 : ℤ) < (k : ℤ) * k :=
    mul_pos (by exact_mod_cast hk) (by exact_mod_cast hk)
  have hlt : p.2 < p.1 := by omega
  have heq : p.1 = p.2 + k * k := by
    have hcast : ((p.1 : ℕ) : ℤ) = ((p.2 + k * k : ℕ) : ℤ) := by
      push_cast
      omega
    exact Nat.cast_injective hcast
  exact hNSD p.2 p.1 k hb.2 ha.2 hk hlt heq

/-- Total fiber weight for the Fejér bound (N3 helper). -/
private lemma sarkozyW_tot (A : Set ℕ) (N L : ℕ) :
    (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
      sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t)
      = (L : ℝ) * ((sarkozyFin A N).card : ℝ) := by
  have h1 : (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
        sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t)
      = ∑ a ∈ sarkozyFin A N, ∑ h ∈ Finset.range L,
        ∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
          (if (a : ℤ) - (h : ℤ) = t then (1 : ℝ) else 0) := by
    simp only [sarkozyW]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  rw [h1]
  have h2 : ∀ a ∈ sarkozyFin A N, ∀ h ∈ Finset.range L,
      (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
        (if (a : ℤ) - (h : ℤ) = t then (1 : ℝ) else 0)) = 1 := by
    intro a ha h hh
    rw [Finset.sum_ite_eq]
    have hmem : (a : ℤ) - (h : ℤ)
        ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)) := by
      simp only [sarkozyIm, Finset.mem_image]
      exact ⟨(a, h), Finset.mk_mem_product ha hh, rfl⟩
    rw [ite_eq_left hmem]
  rw [Finset.sum_congr rfl (fun a ha =>
    Finset.sum_congr rfl (fun h hh => h2 a ha h hh))]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- The fiber image lies in an integer interval (N3 helper). -/
private lemma sarkozyIm_sub (A : Set ℕ) (N L : ℕ) :
    sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))
      ⊆ Finset.Ioo (-(L : ℤ)) (N : ℤ) := by
  intro t ht
  simp only [sarkozyIm, Finset.mem_image, Finset.mem_product] at ht
  obtain ⟨⟨a, h⟩, ⟨ha, hh⟩, rfl⟩ := ht
  have ha' : a ∈ sarkozyFin A N := ha
  have hh' : h ∈ Finset.range L := hh
  rw [sarkozyFin_mem, Finset.mem_range] at ha'
  rw [Finset.mem_range] at hh'
  simp only [Finset.mem_Ioo]
  constructor <;> omega

/-- Cardinality bound for the fiber image (N3 helper). -/
private lemma sarkozyIm_card (A : Set ℕ) (N L : ℕ) :
    (sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card ≤ N + L := by
  calc (sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card
      ≤ (Finset.Ioo (-(L : ℤ)) (N : ℤ)).card :=
        Finset.card_le_card (sarkozyIm_sub A N L)
    _ = (((N : ℤ) - (-(L : ℤ)) - 1).toNat) := Int.card_Ioo _ _
    _ ≤ (((N + L : ℕ) : ℤ)).toNat := by
        apply Int.toNat_le_toNat
        push_cast
        omega
    _ = N + L := Int.toNat_natCast (N + L)

/-- Fejér lower bound for the finite correlations (N3). -/
private lemma sarkozy_corr_fejer_lower_bound (A : Set ℕ) (N L : ℕ) :
    (L : ℝ) ^ 2 * ((sarkozyFin A N).card : ℝ) ^ 2
      ≤ ((N : ℝ) + L) * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
        ((sarkozyCorr A N ((h : ℤ) - h') : ℕ) : ℝ)) := by
  have hN1 := sarkozy_corr_sum_sq_identity A N (Finset.range L)
    (fun i => (i : ℤ)) (fun _ => 1)
  have hSeq : (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
        ((sarkozyCorr A N ((h : ℤ) - h') : ℕ) : ℝ))
      = ∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
        (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2 := by
    simpa using hN1
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)))
    (f := sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1))
  rw [sarkozyW_tot A N L] at hCS
  have hcardR : ((sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card : ℝ)
      ≤ (N : ℝ) + (L : ℝ) := by
    have h := sarkozyIm_card A N L
    have h2 : ((sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card : ℝ)
        ≤ ((N + L : ℕ) : ℝ) := by
      exact_mod_cast h
    rwa [Nat.cast_add] at h2
  have hG2nn : 0 ≤ ∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
      (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2 :=
    Finset.sum_nonneg (fun t _ => sq_nonneg _)
  rw [hSeq]
  calc (L : ℝ) ^ 2 * ((sarkozyFin A N).card : ℝ) ^ 2
        = ((L : ℝ) * ((sarkozyFin A N).card : ℝ)) ^ 2 := by ring
    _ ≤ ((sarkozyIm A N (Finset.range L) (fun i => (i : ℤ))).card : ℝ) *
        (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
          (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2) :=
        hCS
    _ ≤ ((N : ℝ) + (L : ℝ)) *
        (∑ t ∈ sarkozyIm A N (Finset.range L) (fun i => (i : ℤ)),
          (sarkozyW A N (Finset.range L) (fun i => (i : ℤ)) (fun _ => 1) t) ^ 2) :=
        mul_le_mul_of_nonneg_right hcardR hG2nn

/-- Type synonym for the GNS construction: finitely supported real functions on `ℤ`. -/
private def sarkozyToep (_γ : ℤ → ℝ) : Type :=
  ℤ →₀ ℝ

private noncomputable instance sarkozyToep_addCommGroup {γ : ℤ → ℝ} :
    AddCommGroup (sarkozyToep γ) :=
  inferInstanceAs (AddCommGroup (ℤ →₀ ℝ))

private noncomputable instance sarkozyToep_module {γ : ℤ → ℝ} :
    Module ℝ (sarkozyToep γ) :=
  inferInstanceAs (Module ℝ (ℤ →₀ ℝ))

/-- The Toeplitz inner product from `γ`, on plain finitely supported functions. -/
private noncomputable def sarkozyToepInnerAux (γ : ℤ → ℝ) (cf df : ℤ →₀ ℝ) : ℝ :=
  ∑ i ∈ cf.support, ∑ j ∈ df.support, cf i * df j * γ (i - j)

/-- The inner sum extends by zero to any larger finite index set. -/
private lemma sarkozyToepInnerAux_extend (γ : ℤ → ℝ) (cf df : ℤ →₀ ℝ)
    (t : Finset ℤ) (hsub : cf.support ⊆ t) :
    sarkozyToepInnerAux γ cf df
      = ∑ i ∈ t, ∑ j ∈ df.support, cf i * df j * γ (i - j) := by
  simp only [sarkozyToepInnerAux]
  exact Finset.sum_subset hsub (fun i _ hi =>
    Finset.sum_eq_zero (fun j _ => by
      rw [Finsupp.notMem_support_iff.mp hi]
      ring))

/-- Additivity of the Toeplitz inner product in the first slot. -/
private lemma sarkozyToepInnerAux_add_left (γ : ℤ → ℝ) (c₁ c₂ d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ (c₁ + c₂) d
      = sarkozyToepInnerAux γ c₁ d + sarkozyToepInnerAux γ c₂ d := by
  rw [sarkozyToepInnerAux_extend γ (c₁ + c₂) d (c₁.support ∪ c₂.support)
      Finsupp.support_add,
    sarkozyToepInnerAux_extend γ c₁ d (c₁.support ∪ c₂.support)
      Finset.subset_union_left,
    sarkozyToepInnerAux_extend γ c₂ d (c₁.support ∪ c₂.support)
      Finset.subset_union_right]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finsupp.add_apply]
  trans ∑ j ∈ d.support, ((c₁ i * d j * γ (i - j)) + (c₂ i * d j * γ (i - j)))
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · exact Finset.sum_add_distrib

/-- Homogeneity of the Toeplitz inner product in the first slot. -/
private lemma sarkozyToepInnerAux_smul_left (γ : ℤ → ℝ) (r : ℝ) (c d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ (r • c) d = r * sarkozyToepInnerAux γ c d := by
  rw [sarkozyToepInnerAux_extend γ (r • c) d c.support Finsupp.support_smul]
  simp only [sarkozyToepInnerAux]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.smul_apply, smul_eq_mul]
  ring

/-- Symmetry of the Toeplitz inner product. -/
private lemma sarkozyToepInnerAux_symm (γ : ℤ → ℝ) (hsymm : ∀ d, γ (-d) = γ d)
    (c d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ d c = sarkozyToepInnerAux γ c d := by
  simp only [sarkozyToepInnerAux]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hγ : γ (j - i) = γ (i - j) := by
    have h : j - i = -(i - j) := by ring
    rw [h]
    exact hsymm (i - j)
  rw [hγ]
  ring

/-- The inner product of basis vectors recovers `γ`. -/
private lemma sarkozyToepInnerAux_single (γ : ℤ → ℝ) (m n : ℤ) :
    sarkozyToepInnerAux γ (Finsupp.single m 1) (Finsupp.single n 1)
      = γ (m - n) := by
  simp only [sarkozyToepInnerAux]
  rw [Finsupp.support_single _ one_ne_zero, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finset.sum_singleton, Finsupp.single_apply,
    Finsupp.single_apply]
  simp

/-- Nonnegativity on the diagonal from positive semidefiniteness. -/
private lemma sarkozyToepInnerAux_nonneg (γ : ℤ → ℝ)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j))
    (c : ℤ →₀ ℝ) : 0 ≤ sarkozyToepInnerAux γ c c := by
  simp only [sarkozyToepInnerAux]
  exact hpos _ _

/-- The shift preserves the Toeplitz inner product. -/
private lemma sarkozyShift_inner_aux (γ : ℤ → ℝ) (c d : ℤ →₀ ℝ) :
    sarkozyToepInnerAux γ (Finsupp.mapDomain (fun i : ℤ => i + 1) c)
      (Finsupp.mapDomain (fun i : ℤ => i + 1) d)
      = sarkozyToepInnerAux γ c d := by
  have hinj : Function.Injective (fun i : ℤ => i + 1) := by
    intro a b h
    simpa using h
  have hsup1 : (Finsupp.mapDomain (fun i : ℤ => i + 1) c).support
      = Finset.image (fun i : ℤ => i + 1) c.support :=
    Finsupp.mapDomain_support_of_injective hinj c
  have hsup2 : (Finsupp.mapDomain (fun i : ℤ => i + 1) d).support
      = Finset.image (fun i : ℤ => i + 1) d.support :=
    Finsupp.mapDomain_support_of_injective hinj d
  have happ : ∀ a : ℤ, (Finsupp.mapDomain (fun i : ℤ => i + 1) c) (a + 1) = c a := by
    intro a
    exact Finsupp.mapDomain_apply' Set.univ _ (Set.subset_univ _)
      hinj.injOn (Set.mem_univ a)
  have happd : ∀ b : ℤ, (Finsupp.mapDomain (fun i : ℤ => i + 1) d) (b + 1) = d b := by
    intro b
    exact Finsupp.mapDomain_apply' Set.univ _ (Set.subset_univ _)
      hinj.injOn (Set.mem_univ b)
  have hdiff : ∀ a b : ℤ, (a + 1) - (b + 1) = a - b := fun a b => by ring
  simp only [sarkozyToepInnerAux, hsup1, hsup2]
  rw [Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro b _
  simp only [happ a, happd b, hdiff a b]

/-- The GNS core structure from `γ`. -/
@[instance_reducible]
private noncomputable def sarkozyToepCore (γ : ℤ → ℝ) (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) :
    PreInnerProductSpace.Core ℝ (sarkozyToep γ) where
  inner c d := sarkozyToepInnerAux γ c d
  conj_inner_symm c d := sarkozyToepInnerAux_symm γ hsymm c d
  re_inner_nonneg c := sarkozyToepInnerAux_nonneg γ hpos c
  add_left c₁ c₂ d := sarkozyToepInnerAux_add_left γ c₁ c₂ d
  smul_left c d r := sarkozyToepInnerAux_smul_left γ r c d

@[instance_reducible]
private noncomputable def sarkozyToep_seminormed (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) :
    SeminormedAddCommGroup (sarkozyToep γ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup
    (c := sarkozyToepCore γ hsymm hpos)

@[instance_reducible]
private noncomputable def sarkozyToep_innerProd (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) := by
  letI := sarkozyToep_seminormed γ hsymm hpos
  exact InnerProductSpace.ofCore (sarkozyToepCore γ hsymm hpos)

/-- The forward shift on the type synonym. -/
private noncomputable def sarkozyShift (γ : ℤ → ℝ) :
    sarkozyToep γ →ₗ[ℝ] sarkozyToep γ :=
  Finsupp.lmapDomain ℝ ℝ (fun i : ℤ => i + 1)

/-- The shift as a linear isometry of the synonym (a real linear isometry). -/
private noncomputable def sarkozyShiftIso (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) := by
  letI := sarkozyToep_seminormed γ hsymm hpos
  letI := sarkozyToep_innerProd γ hsymm hpos
  refine @LinearMap.isometryOfInner ℝ (sarkozyToep γ) _ _ _ (sarkozyToep γ) _ _
    (sarkozyShift γ) (fun c d => ?_)
  have e1 : ∀ c : sarkozyToep γ, ((sarkozyShift γ) c : ℤ →₀ ℝ)
      = Finsupp.mapDomain (fun i : ℤ => i + 1) (c : ℤ →₀ ℝ) :=
    fun c => rfl
  have hAux : sarkozyToepInnerAux γ ((sarkozyShift γ) c) ((sarkozyShift γ) d)
      = sarkozyToepInnerAux γ c d := by
    rw [e1 c, e1 d]
    exact sarkozyShift_inner_aux γ _ _
  exact hAux

/-- The shift moves basis vectors forward by one. -/
private lemma sarkozyShiftIso_single (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) (a : ℤ) :
    (sarkozyShiftIso γ hsymm hpos) (((Finsupp.single a 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (((Finsupp.single (a + 1) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
  have h1 : ((sarkozyShiftIso γ hsymm hpos)
      (((Finsupp.single a 1 : ℤ →₀ ℝ)) : sarkozyToep γ) : ℤ →₀ ℝ)
      = Finsupp.mapDomain (fun i : ℤ => i + 1) (Finsupp.single a 1) := rfl
  have hgoal : ((sarkozyShiftIso γ hsymm hpos)
      (((Finsupp.single a 1 : ℤ →₀ ℝ)) : sarkozyToep γ) : ℤ →₀ ℝ)
      = Finsupp.single (a + 1) 1 := by
    rw [h1, Finsupp.mapDomain_single]
  exact hgoal

/-- Iterates of the shift move the zeroth basis vector forward (N5). -/
private lemma sarkozyShiftIso_iterate_single (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) (m : ℕ) :
    (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (((Finsupp.single (m : ℤ) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
  induction m with
  | zero =>
    rw [Function.iterate_zero, Nat.cast_zero]
    rfl
  | succ m ih =>
    have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have hstep : (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m.succ]
        (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
        = (⇑(sarkozyShiftIso γ hsymm hpos))
          (((⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
            (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ))) :=
      Function.iterate_succ_apply' _ _ _
    have hbridge := congrArg (fun n : ℕ => (⇑(sarkozyShiftIso γ hsymm hpos)) ^[n]
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ))
      (Nat.succ_eq_add_one m)
    have hsingle := sarkozyShiftIso_single γ hsymm hpos ((m : ℤ))
    have hinner : (⇑(sarkozyShiftIso γ hsymm hpos))
        (((⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
          (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)))
        = (((Finsupp.single ((m : ℤ) + 1) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) :=
      Eq.trans (congrArg (⇑(sarkozyShiftIso γ hsymm hpos)) ih) hsingle
    have hchain : (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m.succ]
        (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
        = (((Finsupp.single ((m : ℤ) + 1) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) :=
      Eq.trans hstep hinner
    rw [hcast]
    exact Eq.trans hbridge.symm hchain

/-- Powers of the shift move the zeroth basis vector forward (N5). -/
private lemma sarkozyShiftIso_pow_single (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) (m : ℕ) :
    ((sarkozyShiftIso γ hsymm hpos) ^ m)
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (((Finsupp.single (m : ℤ) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
  have hiter := sarkozyShiftIso_iterate_single γ hsymm hpos m
  have hcoe := @LinearIsometry.coe_pow ℝ (sarkozyToep γ) inferInstance
    (sarkozyToep_seminormed γ hsymm hpos) (sarkozyToep_module)
    (sarkozyShiftIso γ hsymm hpos) m
  have hrewrite : ((sarkozyShiftIso γ hsymm hpos) ^ m)
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
        (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
    rw [hcoe]
  rw [hrewrite]
  exact hiter

/-- GNS dilation: isometric shift on the Hilbert completion with correlations γ (N6). -/
private lemma sarkozy_dilation (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E)
      (_ : CompleteSpace E),
      ∃ (U : E →ₗᵢ[ℝ] E) (v : E), ∀ m n : ℕ,
        inner ℝ ((U ^ m) v) ((U ^ n) v) = γ ((m : ℤ) - n) := by
  let instN : SeminormedAddCommGroup (sarkozyToep γ) :=
    sarkozyToep_seminormed γ hsymm hpos
  let instI : InnerProductSpace ℝ (sarkozyToep γ) :=
    sarkozyToep_innerProd γ hsymm hpos
  set S : (sarkozyToep γ) →ₗᵢ[ℝ] (sarkozyToep γ) :=
    sarkozyShiftIso γ hsymm hpos with hS
  set T : UniformSpace.Completion (sarkozyToep γ) →L[ℝ]
      UniformSpace.Completion (sarkozyToep γ) :=
    S.toContinuousLinearMap.completion with hT
  have hTnorm : ∀ x : UniformSpace.Completion (sarkozyToep γ), ‖T x‖ = ‖x‖ := by
    intro x
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq (Continuous.norm T.continuous) continuous_norm) (fun a => ?_)
    rw [ContinuousLinearMap.completion_apply_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact S.norm_map a
  set U : UniformSpace.Completion (sarkozyToep γ) →ₗᵢ[ℝ]
      UniformSpace.Completion (sarkozyToep γ) :=
    ⟨T.toLinearMap, hTnorm⟩ with hU
  have hUcoe : ∀ x : sarkozyToep γ, U (↑x) = ↑(S x) := fun x =>
    ContinuousLinearMap.completion_apply_coe _ x
  have hcomm : ∀ (m : ℕ) (x : sarkozyToep γ), (U ^ m) (↑x) = ↑((S ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      have e1 : (U ^ (m + 1)) (↑x) = (U ^ m) (U (↑x)) := by
        rw [pow_succ, LinearIsometry.coe_mul, Function.comp_apply]
      have e2 : ((S ^ (m + 1)) x : sarkozyToep γ) = (S ^ m) (S x) := by
        rw [pow_succ, LinearIsometry.coe_mul, Function.comp_apply]
      rw [e1, hUcoe, ih, e2]
  set s0 : sarkozyToep γ :=
    (((Finsupp.single (0 : ℤ) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) with hs0
  refine ⟨UniformSpace.Completion (sarkozyToep γ), inferInstance, inferInstance,
    inferInstance, U, (↑s0 : UniformSpace.Completion (sarkozyToep γ)), ?_⟩
  intro m n
  rw [hcomm, hcomm, UniformSpace.Completion.inner_coe,
    sarkozyShiftIso_pow_single γ hsymm hpos m,
    sarkozyShiftIso_pow_single γ hsymm hpos n]
  exact sarkozyToepInnerAux_single γ (m : ℤ) (n : ℤ)

/-- Correlation limit along a density subsequence (N4). -/
private lemma sarkozy_corr_limit (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hfreq : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      δ * (N : ℝ) ≤ ((initialSegmentCount A N : ℕ) : ℝ))
    (hNSD : ∀ a b k : ℕ, a ∈ A → b ∈ A → 0 < k → a < b → b ≠ a + k * k) :
    ∃ γ : ℤ → ℝ, (∀ d : ℤ, γ (-d) = γ d)
      ∧ (∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
        0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j))
      ∧ (∀ k : ℕ, 0 < k → γ ((k : ℤ) * k) = 0)
      ∧ (∀ L : ℕ, 0 < L → (L : ℝ) ^ 2 * δ ^ 2 ≤
        ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h : ℤ) - h')) := by
  have hfreq' : ∀ k : ℕ, ∃ N : ℕ, k + 1 ≤ N ∧
      δ * (N : ℝ) ≤ ((initialSegmentCount A N : ℕ) : ℝ) := fun k => hfreq (k + 1)
  choose Nseq hNseq using hfreq'
  have hNpos : ∀ k : ℕ, (0 : ℝ) < (Nseq k : ℝ) := by
    intro k
    have h1 : 0 < Nseq k :=
      lt_of_lt_of_le (Nat.zero_lt_succ k) (hNseq k).1
    exact_mod_cast h1
  have hRle : ∀ k : ℕ, ∀ d : ℤ,
      ((sarkozyCorr A (Nseq k) d : ℕ) : ℝ) ≤ (Nseq k : ℝ) := by
    intro k d
    have h := le_trans (sarkozy_corr_le_card A (Nseq k) d) (sarkozy_card_le A (Nseq k))
    exact_mod_cast h
  have hcompact : IsCompact (Set.univ.pi (fun _ : ℤ => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hmem : ∀ k : ℕ, (fun d : ℤ => ((sarkozyCorr A (Nseq k) d : ℕ) : ℝ) / (Nseq k : ℝ))
      ∈ Set.univ.pi (fun _ : ℤ => Set.Icc (0 : ℝ) 1) := by
    intro k
    rw [Set.mem_univ_pi]
    intro d
    rw [Set.mem_Icc]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [div_le_one (hNpos k)]
      exact hRle k d
  obtain ⟨γ, -, φ, hφmono, hφlim⟩ := hcompact.tendsto_subseq hmem
  have hpt : ∀ d : ℤ, Filter.Tendsto
      (fun k : ℕ => ((sarkozyCorr A (Nseq (φ k)) d : ℕ) : ℝ) / (Nseq (φ k) : ℝ))
      Filter.atTop (nhds (γ d)) :=
    fun d => (tendsto_pi_nhds.mp hφlim) d
  have hga : ∀ d : ℤ, γ (-d) = γ d := by
    intro d
    have heq : ∀ k : ℕ, ((sarkozyCorr A (Nseq (φ k)) (-d) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)
        = ((sarkozyCorr A (Nseq (φ k)) d : ℕ) : ℝ) / (Nseq (φ k) : ℝ) := by
      intro k
      rw [sarkozy_corr_neg]
    have h1 := hpt (-d)
    have h2 := hpt d
    rw [show (fun k : ℕ => ((sarkozyCorr A (Nseq (φ k)) (-d) : ℕ) : ℝ) / (Nseq (φ k) : ℝ))
        = (fun k : ℕ => ((sarkozyCorr A (Nseq (φ k)) d : ℕ) : ℝ) / (Nseq (φ k) : ℝ))
      from funext heq] at h1
    exact tendsto_nhds_unique h1 h2
  have hgb : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j) := by
    intro s c
    have hnn : ∀ k : ℕ, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)) := by
      intro k
      have hN1k := sarkozy_corr_nonneg A (Nseq (φ k)) s (fun d => d) c
      have hfactor : (∑ i ∈ s, ∑ j ∈ s, c i * c j *
            (((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)))
          = ((Nseq (φ k) : ℝ))⁻¹ * (∑ i ∈ s, ∑ j ∈ s, c i * c j *
            ((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_inv_mul]
        ring
      rw [hfactor]
      exact mul_nonneg (inv_nonneg.mpr (hNpos (φ k)).le) hN1k
    have hlim : Filter.Tendsto (fun k : ℕ => ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)))
        Filter.atTop
        (nhds (∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j))) := by
      refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => ?_))
      exact tendsto_const_nhds.mul (hpt (i - j))
    exact ge_of_tendsto' hlim hnn
  have hgc : ∀ k : ℕ, 0 < k → γ ((k : ℤ) * k) = 0 := by
    intro k hk
    have h0 : ∀ n : ℕ, ((sarkozyCorr A (Nseq (φ n)) ((k : ℤ) * k) : ℕ) : ℝ)
        / (Nseq (φ n) : ℝ) = 0 := by
      intro n
      rw [sarkozy_corr_sq_eq_zero A (Nseq (φ n)) k hk hNSD]
      simp
    have hlim := hpt ((k : ℤ) * k)
    have hlim0 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (γ ((k : ℤ) * k))) :=
      hlim.congr h0
    have h00 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds
    exact tendsto_nhds_unique hlim0 h00
  have hNseqTop : Filter.Tendsto Nseq Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun k hk => ?_⟩
    have hm := (hNseq k).1
    omega
  have hcomp : Filter.Tendsto (Nseq ∘ φ) Filter.atTop Filter.atTop :=
    hNseqTop.comp hφmono.tendsto_atTop
  have hgd : ∀ L : ℕ, 0 < L → (L : ℝ) ^ 2 * δ ^ 2 ≤
      ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h : ℤ) - h') := by
    intro L hL
    have hC : ∀ k : ℕ, δ * (Nseq (φ k) : ℝ)
        ≤ ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) := by
      intro k
      have h := (hNseq (φ k)).2
      rwa [← sarkozyFin_card] at h
    have hN3 : ∀ k : ℕ, (L : ℝ) ^ 2 * ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) ^ 2
        ≤ ((Nseq (φ k) : ℝ) + (L : ℝ)) * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          ((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ)) :=
      fun k => sarkozy_corr_fejer_lower_bound A (Nseq (φ k)) L
    have hCsq : ∀ k : ℕ, (δ * (Nseq (φ k) : ℝ)) ^ 2
        ≤ ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) ^ 2 := by
      intro k
      exact pow_le_pow_left₀ (mul_nonneg hδ.le (Nat.cast_nonneg _)) (hC k) 2
    have hdiv : ∀ k : ℕ, (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          ((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ)) / (Nseq (φ k) : ℝ)
        = ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          (((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ) / (Nseq (φ k) : ℝ)) := by
      intro k
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h' _
      rw [div_eq_mul_inv]
    have hle : ∀ k : ℕ, ((L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ)) / ((Nseq (φ k) : ℝ) + (L : ℝ))
        ≤ ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          (((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ) / (Nseq (φ k) : ℝ)) := by
      intro k
      have hMpos : (0 : ℝ) < (Nseq (φ k) : ℝ) := hNpos (φ k)
      have hMLpos : (0 : ℝ) < (Nseq (φ k) : ℝ) + (L : ℝ) := by
        have hnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
        linarith [hNpos (φ k)]
      rw [← hdiv k, div_le_div_iff₀ hMLpos hMpos]
      have h2 : (L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ) * (Nseq (φ k) : ℝ)
          = (L : ℝ) ^ 2 * (δ * (Nseq (φ k) : ℝ)) ^ 2 := by
        ring
      rw [h2]
      calc (L : ℝ) ^ 2 * (δ * (Nseq (φ k) : ℝ)) ^ 2
            ≤ (L : ℝ) ^ 2 * ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (hCsq k) (sq_nonneg _)
        _ ≤ ((Nseq (φ k) : ℝ) + (L : ℝ)) * _ := hN3 k
        _ = _ * ((Nseq (φ k) : ℝ) + (L : ℝ)) := mul_comm _ _
    have hLBlim : Filter.Tendsto
        (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ)) / ((Nseq (φ k) : ℝ) + (L : ℝ)))
        Filter.atTop (nhds ((L : ℝ) ^ 2 * δ ^ 2)) := by
      have hfrac : Filter.Tendsto
          (fun k : ℕ => (Nseq (φ k) : ℝ) / ((Nseq (φ k) : ℝ) + (L : ℝ)))
          Filter.atTop (nhds 1) :=
        (tendsto_natCast_div_add_atTop (L : ℝ)).comp hcomp
      have hmul : Filter.Tendsto
          (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2) * ((Nseq (φ k) : ℝ) / ((Nseq (φ k) : ℝ) + (L : ℝ))))
          Filter.atTop (nhds (((L : ℝ) ^ 2 * δ ^ 2) * 1)) :=
        tendsto_const_nhds.mul hfrac
      rw [mul_one] at hmul
      have hfun : (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ))
            / ((Nseq (φ k) : ℝ) + (L : ℝ)))
          = (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2)
            * ((Nseq (φ k) : ℝ) / ((Nseq (φ k) : ℝ) + (L : ℝ)))) := by
        apply funext
        intro k
        ring
      rw [hfun]
      exact hmul
    have hSlim : Filter.Tendsto
        (fun k : ℕ => ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          (((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ) / (Nseq (φ k) : ℝ)))
        Filter.atTop (nhds (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h : ℤ) - h'))) := by
      refine tendsto_finsetSum _ (fun h _ => tendsto_finsetSum _ (fun h' _ => ?_))
      exact hpt ((h : ℤ) - h')
    have hfin := le_of_tendsto_of_tendsto' hLBlim hSlim hle
    exact hfin
  exact ⟨γ, hga, hgb, hgc, hgd⟩

/-- Shift-difference identity for range sums (N7 helper). -/
private lemma sarkozy_sum_shift_diff {G : Type*} [AddCommGroup G] (g : ℕ → G)
    (M h : ℕ) :
    (∑ n ∈ Finset.range M, g (n + h)) - (∑ n ∈ Finset.range M, g n)
      = (∑ k ∈ Finset.range h, g (M + k)) - (∑ k ∈ Finset.range h, g k) := by
  have hadd1 := Finset.sum_range_add g h M
  have hadd2 := Finset.sum_range_add g M h
  have hMH : h + M = M + h := add_comm _ _
  rw [hMH] at hadd1
  have hconv : (∑ x ∈ Finset.range M, g (h + x))
      = (∑ n ∈ Finset.range M, g (n + h)) :=
    Finset.sum_congr rfl (fun n _ => by rw [add_comm h n])
  have key : (∑ n ∈ Finset.range M, g n) + (∑ k ∈ Finset.range h, g (M + k))
      = (∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g (n + h)) := by
    rw [← hconv, ← hadd1, ← hadd2]
  calc (∑ n ∈ Finset.range M, g (n + h)) - (∑ n ∈ Finset.range M, g n)
        = ((∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g (n + h)))
          - ((∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g n)) := by
        abel
    _ = ((∑ n ∈ Finset.range M, g n) + (∑ k ∈ Finset.range h, g (M + k)))
          - ((∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g n)) := by
        rw [← key]
    _ = (∑ k ∈ Finset.range h, g (M + k)) - (∑ k ∈ Finset.range h, g k) := by
        abel

/-- Van der Corput shift bound (N7(i)): averaging over shifts barely moves the sum. -/
private lemma sarkozy_vdc_avg_shift {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C) (M H : ℕ) :
    ‖(H : ℝ) • ∑ n ∈ Finset.range M, x n
      - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
      ≤ (H : ℝ)^2 * C := by
  have hdiff : ∀ h : ℕ, ‖(∑ n ∈ Finset.range M, x n)
        - (∑ n ∈ Finset.range M, x (n + h))‖ ≤ 2 * (h : ℝ) * C := by
    intro h
    have hkey := sarkozy_sum_shift_diff x M h
    have heq : (∑ n ∈ Finset.range M, x n) - (∑ n ∈ Finset.range M, x (n + h))
        = (∑ k ∈ Finset.range h, x k) - (∑ k ∈ Finset.range h, x (M + k)) := by
      calc (∑ n ∈ Finset.range M, x n) - (∑ n ∈ Finset.range M, x (n + h))
            = -((∑ n ∈ Finset.range M, x (n + h))
              - (∑ n ∈ Finset.range M, x n)) := by abel
        _ = -((∑ k ∈ Finset.range h, x (M + k))
              - (∑ k ∈ Finset.range h, x k)) := by rw [hkey]
        _ = (∑ k ∈ Finset.range h, x k)
              - (∑ k ∈ Finset.range h, x (M + k)) := by abel
    rw [heq]
    calc ‖(∑ k ∈ Finset.range h, x k) - (∑ k ∈ Finset.range h, x (M + k))‖
          ≤ ‖∑ k ∈ Finset.range h, x k‖ + ‖∑ k ∈ Finset.range h, x (M + k)‖ :=
          norm_sub_le _ _
      _ ≤ (∑ k ∈ Finset.range h, ‖x k‖)
          + (∑ k ∈ Finset.range h, ‖x (M + k)‖) :=
          add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
      _ ≤ (∑ _k ∈ Finset.range h, C) + (∑ _k ∈ Finset.range h, C) := by
          apply add_le_add <;> exact Finset.sum_le_sum (fun k _ => hx _)
      _ = 2 * (h : ℝ) * C := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hgaussR : ∀ H : ℕ, 2 * (∑ h ∈ Finset.range H, (h : ℝ))
      = (H : ℝ) * ((H : ℝ) - 1) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      rw [Finset.sum_range_succ]
      push_cast at ih ⊢
      linear_combination ih
  have hpair : 2 * (∑ h ∈ Finset.range H, (h : ℝ)) ≤ (H : ℝ)^2 := by
    rw [hgaussR H]
    have hnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    have heq : (H : ℝ) * ((H : ℝ) - 1) = (H : ℝ)^2 - (H : ℝ) := by ring
    rw [heq]
    linarith
  have hHsmul : ((H : ℝ) • ∑ n ∈ Finset.range M, x n)
      = ∑ _h ∈ Finset.range H, (∑ n ∈ Finset.range M, x n) := by
    rw [Finset.sum_const, Finset.card_range]
    exact Nat.cast_smul_eq_nsmul ℝ H _
  have hswap : (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))
      = ∑ h ∈ Finset.range H, ∑ n ∈ Finset.range M, x (n + h) := Finset.sum_comm
  have hD : (H : ℝ) • (∑ n ∈ Finset.range M, x n)
        - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)
      = ∑ h ∈ Finset.range H, ((∑ n ∈ Finset.range M, x n)
        - (∑ n ∈ Finset.range M, x (n + h))) := by
    rw [hHsmul, hswap, ← Finset.sum_sub_distrib]
  rw [hD]
  calc ‖∑ h ∈ Finset.range H, ((∑ n ∈ Finset.range M, x n)
          - (∑ n ∈ Finset.range M, x (n + h)))‖
        ≤ ∑ h ∈ Finset.range H, ‖(∑ n ∈ Finset.range M, x n)
          - (∑ n ∈ Finset.range M, x (n + h))‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.range H, (2 * (h : ℝ) * C) :=
        Finset.sum_le_sum (fun h _ => hdiff h)
    _ = 2 * C * (∑ h ∈ Finset.range H, (h : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
    _ ≤ (H : ℝ)^2 * C := by
        calc 2 * C * (∑ h ∈ Finset.range H, (h : ℝ))
            = (2 * (∑ h ∈ Finset.range H, (h : ℝ))) * C := by ring
          _ ≤ (H : ℝ)^2 * C := mul_le_mul_of_nonneg_right hpair hC

/-- Van der Corput square bound (N7(ii)): the double-shifted sum via correlations. -/
private lemma sarkozy_vdc_sq_bound {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (M H : ℕ) :
    ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖^2
      ≤ (M : ℝ) * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M,
        inner ℝ (x (n + h)) (x (n + h'))) := by
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range M)
    (f := fun n => ‖∑ h ∈ Finset.range H, x (n + h)‖)
  rw [Finset.card_range] at h2
  have hnorm : ∀ n : ℕ, ‖∑ h ∈ Finset.range H, x (n + h)‖^2
      = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        inner ℝ (x (n + h)) (x (n + h')) := by
    intro n
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro h _
    exact inner_sum _ _ _
  have hswap : (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H,
        ∑ h' ∈ Finset.range H, inner ℝ (x (n + h)) (x (n + h')))
      = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H, ∑ n ∈ Finset.range M,
        inner ℝ (x (n + h)) (x (n + h')) := by
    trans ∑ h ∈ Finset.range H, ∑ n ∈ Finset.range M, ∑ h' ∈ Finset.range H,
      inner ℝ (x (n + h)) (x (n + h'))
    · exact Finset.sum_comm
    · apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
  calc ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖^2
      ≤ (∑ n ∈ Finset.range M, ‖∑ h ∈ Finset.range H, x (n + h)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (M : ℝ) * (∑ n ∈ Finset.range M,
          ‖∑ h ∈ Finset.range H, x (n + h)‖^2) := h2
    _ = (M : ℝ) * (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H,
          ∑ h' ∈ Finset.range H, inner ℝ (x (n + h)) (x (n + h'))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        exact hnorm n
    _ = (M : ℝ) * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h'))) := by
        rw [hswap]

/-- Van der Corput correlation stability (N7(iii)): shifting both slots nearly preserves
the correlation sum. -/
private lemma sarkozy_vdc_corr_stable {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C) (M h h' : ℕ) (hle : h' ≤ h) :
    |∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h'))
      - ∑ n ∈ Finset.range M, inner ℝ (x (n + (h - h'))) (x n)|
      ≤ 2 * (h' : ℝ) * C^2 := by
  have key := sarkozy_sum_shift_diff
    (fun m => inner ℝ (x ((h - h') + m)) (x m)) M h'
  have e1 : (∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h')))
      = ∑ n ∈ Finset.range M,
        (fun m => inner ℝ (x ((h - h') + m)) (x m)) (n + h') := by
    apply Finset.sum_congr rfl
    intro n _
    have hnn : n + h = (h - h') + (n + h') := by omega
    rw [hnn]
  have e2 : (∑ n ∈ Finset.range M, inner ℝ (x (n + (h - h'))) (x n))
      = ∑ n ∈ Finset.range M,
        (fun m => inner ℝ (x ((h - h') + m)) (x m)) n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [add_comm n (h - h')]
  have hdecomp : (∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h')))
        - (∑ n ∈ Finset.range M, inner ℝ (x (n + (h - h'))) (x n))
      = (∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k))
        - (∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) k) := by
    rw [e1, e2]
    exact key
  have hterm : ∀ m, |(fun m => inner ℝ (x ((h - h') + m)) (x m)) m| ≤ C^2 := by
    intro m
    calc |(fun m => inner ℝ (x ((h - h') + m)) (x m)) m|
          ≤ ‖x ((h - h') + m)‖ * ‖x m‖ := abs_real_inner_le_norm _ _
      _ ≤ C * C := mul_le_mul (hx _) (hx _) (norm_nonneg _) hC
      _ = C^2 := by ring
  have habs : ∀ X Y : ℝ, |X - Y| ≤ |X| + |Y| := by
    intro X Y
    calc |X - Y| = |X + (-Y)| := by rw [sub_eq_add_neg]
      _ ≤ |X| + |-Y| := abs_add_le _ _
      _ = |X| + |Y| := by rw [abs_neg]
  rw [hdecomp]
  calc |(∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k))
        - (∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) k)|
      ≤ |(∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k))|
        + |(∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) k)| := habs _ _
    _ ≤ (∑ k ∈ Finset.range h',
          |(fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k)|)
        + (∑ k ∈ Finset.range h',
          |(fun m => inner ℝ (x ((h - h') + m)) (x m)) k|) :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ _k ∈ Finset.range h', C^2) + (∑ _k ∈ Finset.range h', C^2) := by
        apply add_le_add <;> exact Finset.sum_le_sum (fun k _ => hterm _)
    _ = 2 * (h' : ℝ) * C^2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Hilbert-space van der Corput lemma (N8): vanishing lag-correlations kill the mean. -/
private lemma sarkozy_vdc_tendsto {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C)
    (hcorr : ∀ d : ℕ, 1 ≤ d → Filter.Tendsto
      (fun (M : ℕ) => (M : ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n + d)) (x n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun (M : ℕ) => (M : ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0:ℝ) < ε^2 := by positivity
  obtain ⟨H, hH1, hHC⟩ : ∃ H : ℕ, 1 ≤ H ∧ C^2 / (H:ℝ) ≤ ε^2 / 16 := by
    refine ⟨Nat.floor (16 * C^2 / ε^2) + 1, Nat.le_add_left 1 _, ?_⟩
    have hHpos : (0:ℝ) < ((((Nat.floor (16 * C^2 / ε^2) + 1 : ℕ))) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    rw [div_le_div_iff₀ hHpos (by norm_num : (0:ℝ) < 16)]
    have hfloor : 16 * C^2 / ε^2 ≤ (((Nat.floor (16 * C^2 / ε^2) + 1 : ℕ) : ℝ)) := by
      have hfl := Nat.lt_floor_add_one (16 * C^2 / ε^2)
      have hcast : ((((Nat.floor (16 * C^2 / ε^2) + 1 : ℕ))) : ℝ)
          = ((Nat.floor (16 * C^2 / ε^2) : ℝ)) + 1 := by push_cast; ring
      rw [hcast]
      linarith
    calc C^2 * 16 = (16 * C^2 / ε^2) * ε^2 := by
            rw [div_mul_cancel₀ _ (ne_of_gt hε2)]; ring
      _ ≤ _ * ε^2 := mul_le_mul_of_nonneg_right hfloor hε2.le
      _ = ε^2 * _ := by ring
  have hHpos : (0:ℝ) < (H:ℝ) := Nat.cast_pos.mpr (by omega)
  have hHne : (H:ℝ) ≠ 0 := ne_of_gt hHpos
  have hK0pos : (0:ℝ) < ε^2/16 := by linarith [hε2]
  obtain ⟨NM1, hNM1⟩ := exists_nat_gt (1 / (ε^2/(32*((H:ℝ)*C^2+1))))
  obtain ⟨NM2, hNM2⟩ := exists_nat_gt (1 / (ε^2/(16*((H:ℝ)^2*C^2+1))))
  have hex : ∀ d : ℕ, ∃ Nd : ℕ, ∀ M : ℕ, Nd ≤ M →
      (1 ≤ d → d < H →
        |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+d)) (x n)| < ε^2/16) := by
    intro d
    by_cases hd : 1 ≤ d ∧ d < H
    · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hcorr d hd.1) (ε^2/16) hK0pos
      refine ⟨N, fun M hM _ _ => ?_⟩
      have hdist := hN M hM
      rwa [dist_zero_right, Real.norm_eq_abs] at hdist
    · exact ⟨0, fun M _ h1 hH => absurd ⟨h1, hH⟩ hd⟩
  choose Nd hNd using hex
  refine ⟨max 1 (max NM1 (max NM2 ((Finset.range H).sup Nd))), fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMNM1 : NM1 ≤ M := by omega
  have hMNM2 : NM2 ≤ M := by omega
  have hMNcorr : (Finset.range H).sup Nd ≤ M := by omega
  have hMpos : (0:ℝ) < (M:ℝ) := Nat.cast_pos.mpr (by omega)
  have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
  have hM1nn : (0:ℝ) ≤ (M:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hMHnn : (0:ℝ) ≤ (M:ℝ)*(H:ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hMHinv : (0:ℝ) ≤ ((M:ℝ)*(H:ℝ))⁻¹ := inv_nonneg.mpr hMHnn
  have hMinv01 : (M:ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_iff_one_le_mul₀ hMpos]
    calc (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
      _ = 1 * (M:ℝ) := by ring
  have hMinv1 : (M:ℝ)⁻¹ ≤ ε^2/(32*((H:ℝ)*C^2+1)) := by
    have h1 : (1:ℝ)/(ε^2/(32*((H:ℝ)*C^2+1))) < (M:ℝ) :=
      lt_of_lt_of_le hNM1 (Nat.cast_le.mpr hMNM1)
    have hδpos : (0:ℝ) < ε^2/(32*((H:ℝ)*C^2+1)) := div_pos hε2 (by positivity)
    rw [inv_le_iff_one_le_mul₀ hMpos]
    calc (1:ℝ) = (ε^2/(32*((H:ℝ)*C^2+1))) * (1/(ε^2/(32*((H:ℝ)*C^2+1)))) :=
          (mul_one_div_cancel (ne_of_gt hδpos)).symm
      _ ≤ (ε^2/(32*((H:ℝ)*C^2+1))) * (M:ℝ) :=
          mul_le_mul_of_nonneg_left h1.le hδpos.le
  have hMinv2 : (M:ℝ)⁻¹ ≤ ε^2/(16*((H:ℝ)^2*C^2+1)) := by
    have h1 : (1:ℝ)/(ε^2/(16*((H:ℝ)^2*C^2+1))) < (M:ℝ) :=
      lt_of_lt_of_le hNM2 (Nat.cast_le.mpr hMNM2)
    have hδpos : (0:ℝ) < ε^2/(16*((H:ℝ)^2*C^2+1)) := div_pos hε2 (by positivity)
    rw [inv_le_iff_one_le_mul₀ hMpos]
    calc (1:ℝ) = (ε^2/(16*((H:ℝ)^2*C^2+1))) * (1/(ε^2/(16*((H:ℝ)^2*C^2+1)))) :=
          (mul_one_div_cancel (ne_of_gt hδpos)).symm
      _ ≤ (ε^2/(16*((H:ℝ)^2*C^2+1))) * (M:ℝ) :=
          mul_le_mul_of_nonneg_left h1.le hδpos.le
  have hcsmall : ∀ d : ℕ, 1 ≤ d → d < H →
      |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+d)) (x n)| < ε^2/16 := by
    intro d hd1 hdH
    have hdmem : d ∈ Finset.range H := Finset.mem_range.mpr hdH
    have hle : Nd d ≤ M := le_trans (Finset.le_sup hdmem) hMNcorr
    exact hNd d M hle hd1 hdH
  have hN7i := sarkozy_vdc_avg_shift x C hC hx M H
  have hN7ii := sarkozy_vdc_sq_bound x M H
  -- off-diagonal correlation bound
  have hterm : ∀ h h' : ℕ, h ∈ Finset.range H → h' ∈ Finset.range H → h ≠ h' →
      |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))|
        ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by
    intro h h' hh hh' hne
    have hhH : h < H := Finset.mem_range.mp hh
    have hh'H : h' < H := Finset.mem_range.mp hh'
    have hSTbound : ∀ S T : ℝ, ∀ e : ℝ,
        |S - T| ≤ e → |S| ≤ |T| + e := by
      intro S T e hST
      have hle := abs_sub_abs_le_abs_sub S T
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- h < h': swap slots, apply N7(iii) with big h'
      have hiii := sarkozy_vdc_corr_stable x C hC hx M h' h (le_of_lt hlt)
      have hd1 : 1 ≤ h' - h := by omega
      have hdH : h' - h < H := by omega
      have hsmall := hcsmall (h'-h) hd1 hdH
      have e : (∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))
          = ∑ n ∈ Finset.range M, inner ℝ (x (n+h')) (x (n+h)) := by
        apply Finset.sum_congr rfl
        intro n _
        exact real_inner_comm _ _
      have hST := hSTbound _ _ _ hiii
      have hhHle : (h:ℝ) ≤ (H:ℝ) := by exact_mod_cast le_of_lt hhH
      have h2 : (M:ℝ)⁻¹*(2*(h:ℝ)*C^2) ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by
        have hcc : 2*(h:ℝ)*C^2 ≤ 2*(H:ℝ)*C^2 := by
          calc 2*(h:ℝ)*C^2 = (2*C^2)*(h:ℝ) := by ring
            _ ≤ (2*C^2)*(H:ℝ) := mul_le_mul_of_nonneg_left hhHle (by positivity)
            _ = 2*(H:ℝ)*C^2 := by ring
        calc (M:ℝ)⁻¹*(2*(h:ℝ)*C^2) = 2*(h:ℝ)*C^2*(M:ℝ)⁻¹ := by ring
          _ ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcc hM1nn
      calc |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))|
          = |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h')) (x (n+h))| := by
            rw [e]
        _ = (M:ℝ)⁻¹ * |(∑ n ∈ Finset.range M, inner ℝ (x (n+h')) (x (n+h)))| := by
            rw [abs_mul, abs_of_nonneg hM1nn]
        _ ≤ (M:ℝ)⁻¹ * (|(∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h'-h))) (x n))| + 2*(h:ℝ)*C^2) :=
            mul_le_mul_of_nonneg_left hST hM1nn
        _ = |(M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h'-h))) (x n))| + (M:ℝ)⁻¹*(2*(h:ℝ)*C^2) := by
            rw [abs_mul, abs_of_nonneg hM1nn]; ring
        _ ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ :=
            add_le_add (le_of_lt hsmall) h2
    · -- h' < h: direct from N7(iii)
      have hiii := sarkozy_vdc_corr_stable x C hC hx M h h' (le_of_lt hgt)
      have hd1 : 1 ≤ h - h' := by omega
      have hdH : h - h' < H := by omega
      have hsmall := hcsmall (h-h') hd1 hdH
      have hST := hSTbound _ _ _ hiii
      have hh'Hle : (h':ℝ) ≤ (H:ℝ) := by exact_mod_cast le_of_lt hh'H
      have h2 : (M:ℝ)⁻¹*(2*(h':ℝ)*C^2) ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by
        have hcc : 2*(h':ℝ)*C^2 ≤ 2*(H:ℝ)*C^2 := by
          calc 2*(h':ℝ)*C^2 = (2*C^2)*(h':ℝ) := by ring
            _ ≤ (2*C^2)*(H:ℝ) := mul_le_mul_of_nonneg_left hh'Hle (by positivity)
            _ = 2*(H:ℝ)*C^2 := by ring
        calc (M:ℝ)⁻¹*(2*(h':ℝ)*C^2) = 2*(h':ℝ)*C^2*(M:ℝ)⁻¹ := by ring
          _ ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcc hM1nn
      calc |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))|
          = (M:ℝ)⁻¹ * |(∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))| := by
            rw [abs_mul, abs_of_nonneg hM1nn]
        _ ≤ (M:ℝ)⁻¹ * (|(∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h-h'))) (x n))| + 2*(h':ℝ)*C^2) :=
            mul_le_mul_of_nonneg_left hST hM1nn
        _ = |(M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h-h'))) (x n))| + (M:ℝ)⁻¹*(2*(h':ℝ)*C^2) := by
            rw [abs_mul, abs_of_nonneg hM1nn]; ring
        _ ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ :=
            add_le_add (le_of_lt hsmall) h2
  -- diagonal bound
  have hdiag : ∀ h ∈ Finset.range H,
      (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h)) ≤ C^2 := by
    intro h _
    have hsq : ∀ n, inner ℝ (x (n+h)) (x (n+h)) = ‖x (n+h)‖^2 :=
      fun n => real_inner_self_eq_norm_sq _
    have hle : (∑ n ∈ Finset.range M, ‖x (n+h)‖^2) ≤ (M:ℝ) * C^2 := by
      calc (∑ n ∈ Finset.range M, ‖x (n+h)‖^2) ≤ ∑ _n ∈ Finset.range M, C^2 :=
            Finset.sum_le_sum (fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hx _) 2)
        _ = (M:ℝ) * C^2 := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h))
        = (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, ‖x (n+h)‖^2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro n _
          exact hsq n
      _ ≤ (M:ℝ)⁻¹ * ((M:ℝ) * C^2) := mul_le_mul_of_nonneg_left hle hM1nn
      _ = C^2 := by field_simp
  -- per-h inner sum bound
  have hKE : (0:ℝ) ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by positivity
  have hinner : ∀ h ∈ Finset.range H,
      (∑ h' ∈ Finset.range H, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ (x (n+h)) (x (n+h')))
        ≤ C^2 + (H:ℝ)*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
    intro h hh
    have hsplit := (Finset.add_sum_erase (Finset.range H)
      (fun h' => (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))) hh).symm
    rw [hsplit]
    apply add_le_add (hdiag h hh)
    have hcards : (((Finset.range H).erase h).card : ℕ) ≤ H := by
      rw [Finset.card_erase_of_mem hh, Finset.card_range]
      exact Nat.sub_le _ _
    calc (∑ h' ∈ (Finset.range H).erase h, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
            inner ℝ (x (n+h)) (x (n+h')))
        ≤ ∑ h' ∈ (Finset.range H).erase h,
            |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))| :=
          Finset.sum_le_sum (fun h' _ => le_abs_self _)
      _ ≤ ∑ _h' ∈ (Finset.range H).erase h, (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) :=
          Finset.sum_le_sum (fun h' h'mem => hterm h h' hh
            (Finset.mem_of_mem_erase h'mem)
            (Ne.symm (Finset.ne_of_mem_erase h'mem)))
      _ = (((Finset.range H).erase h).card : ℝ) * (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (H:ℝ) * (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_right _ hKE
          exact_mod_cast hcards
  -- averaged total
  have hTdist : (M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))
      = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ((M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
  have hTot : (M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))
      ≤ (H:ℝ)*C^2 + (H:ℝ)^2*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
    rw [hTdist]
    calc (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
            inner ℝ (x (n+h)) (x (n+h')))
        ≤ ∑ h ∈ Finset.range H, (C^2 + (H:ℝ)*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹)) :=
          Finset.sum_le_sum (fun h hh => hinner h hh)
      _ = (H:ℝ)*C^2 + (H:ℝ)^2*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- P and Q assembly
  have hS : (∑ n ∈ Finset.range M, x n)
      = ((H:ℝ))⁻¹ • ((H:ℝ) • ∑ n ∈ Finset.range M, x n) := by
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hHne, one_smul]
  have hAB : (M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
        - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))
        = ((M:ℝ)*(H:ℝ))⁻¹ • ((H:ℝ) • (∑ n ∈ Finset.range M, x n)
          - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)) := by
    rw [smul_sub]
    congr 1
    conv_lhs => rw [hS]
    rw [← smul_assoc, smul_eq_mul, ← mul_inv]
  have hQ : ((M:ℝ)*(H:ℝ))⁻¹ * ((H:ℝ)^2*C) = (H:ℝ)*C/(M:ℝ) := by
    field_simp
  have hAnorm : ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)‖
      ≤ ((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
        + (H:ℝ)*C/(M:ℝ) := by
    have htri : ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)‖
        ≤ ‖((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖
          + ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
            - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖ := by
      calc ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)‖
            = ‖((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))
              + ((M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
                - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)))‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have e1 : ‖((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖
        = ((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hMHnn]
    have e2 : ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
          - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖
        = ((M:ℝ)*(H:ℝ))⁻¹ * ‖(H:ℝ) • (∑ n ∈ Finset.range M, x n)
          - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖ := by
      rw [hAB, norm_smul, norm_inv, Real.norm_of_nonneg hMHnn]
    rw [e1, e2] at htri
    have h2 : ((M:ℝ)*(H:ℝ))⁻¹ * ‖(H:ℝ) • (∑ n ∈ Finset.range M, x n)
          - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖ ≤ (H:ℝ)*C/(M:ℝ) := by
      calc ((M:ℝ)*(H:ℝ))⁻¹ * ‖(H:ℝ) • (∑ n ∈ Finset.range M, x n)
            - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
          ≤ ((M:ℝ)*(H:ℝ))⁻¹ * ((H:ℝ)^2*C) :=
            mul_le_mul_of_nonneg_left hN7i hMHinv
        _ = (H:ℝ)*C/(M:ℝ) := hQ
    linarith
  have hP2 : ((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
      ≤ ((H:ℝ))⁻¹^2 * ((M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) := by
    calc ((((M:ℝ)*(H:ℝ))⁻¹
          * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
        = ((((M:ℝ)*(H:ℝ))⁻¹)^2)
          * ((‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2) := by
          ring
      _ ≤ ((((M:ℝ)*(H:ℝ))⁻¹)^2)
          * ((M:ℝ) * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
            ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) :=
          mul_le_mul_of_nonneg_left hN7ii (pow_nonneg hMHinv 2)
      _ = ((H:ℝ))⁻¹^2 * ((M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) := by
          field_simp
  have hPfin : ((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
      ≤ C^2/(H:ℝ) + (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
    calc ((((M:ℝ)*(H:ℝ))⁻¹
          * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
        ≤ ((H:ℝ))⁻¹^2 * ((M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
            ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) := hP2
      _ ≤ ((H:ℝ))⁻¹^2 * ((H:ℝ)*C^2 + (H:ℝ)^2*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hTot (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 2)
      _ = C^2/(H:ℝ) + (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          field_simp
  -- numeric bounds for the 1/M terms
  have hfracbound : ∀ A : ℝ, 0 ≤ A → (ε^2/8)*(A/(A+1)) ≤ ε^2/8 := by
    intro A hA
    have hA1 : (0:ℝ) < A + 1 := by linarith
    have hle : A/(A+1) ≤ 1 := by
      rw [div_le_one hA1]
      linarith
    calc (ε^2/8)*(A/(A+1)) ≤ (ε^2/8)*1 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ε^2/8 := by ring
  have h2E : 2*(2*(H:ℝ)*C^2*(M:ℝ)⁻¹) ≤ ε^2/8 := by
    have hEbound : 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ ≤ 2*(H:ℝ)*C^2*(ε^2/(32*((H:ℝ)*C^2+1))) :=
      mul_le_mul_of_nonneg_left hMinv1 (by positivity)
    have hEeq : 2*(2*(H:ℝ)*C^2*(ε^2/(32*(((H:ℝ)*C^2)+1))))
        = (ε^2/8)*(((H:ℝ)*C^2)/(((H:ℝ)*C^2)+1)) := by
      have hA1 : ((H:ℝ)*C^2)+1 ≠ 0 := ne_of_gt (by positivity)
      have h1 : (32:ℝ)*(((H:ℝ)*C^2)+1) ≠ 0 := mul_ne_zero (by norm_num) hA1
      have h2 : (8:ℝ) ≠ 0 := by norm_num
      field_simp
      ring
    calc 2*(2*(H:ℝ)*C^2*(M:ℝ)⁻¹) ≤ 2*(2*(H:ℝ)*C^2*(ε^2/(32*(((H:ℝ)*C^2)+1)))) := by
            linarith [hEbound]
      _ = (ε^2/8)*(((H:ℝ)*C^2)/(((H:ℝ)*C^2)+1)) := hEeq
      _ ≤ ε^2/8 := hfracbound _ (by positivity)
  have hQ2 : ((H:ℝ)*C/(M:ℝ))^2 ≤ (H:ℝ)^2*C^2*(ε^2/(16*((H:ℝ)^2*C^2+1))) := by
    have hsq : ((H:ℝ)*C/(M:ℝ))^2 = (H:ℝ)^2*C^2*((M:ℝ)⁻¹*(M:ℝ)⁻¹) := by
      field_simp
    rw [hsq]
    have hnn : (0:ℝ) ≤ (H:ℝ)^2*C^2 := by positivity
    have hδ2nn : (0:ℝ) ≤ ε^2/(16*((H:ℝ)^2*C^2+1)) :=
      le_of_lt (div_pos hε2 (by positivity))
    have hmm : (M:ℝ)⁻¹*(M:ℝ)⁻¹ ≤ (ε^2/(16*((H:ℝ)^2*C^2+1)))*1 :=
      mul_le_mul hMinv2 hMinv01 hM1nn hδ2nn
    calc (H:ℝ)^2*C^2*((M:ℝ)⁻¹*(M:ℝ)⁻¹)
        ≤ (H:ℝ)^2*C^2*((ε^2/(16*((H:ℝ)^2*C^2+1)))*1) :=
          mul_le_mul_of_nonneg_left hmm hnn
      _ = (H:ℝ)^2*C^2*(ε^2/(16*((H:ℝ)^2*C^2+1))) := by ring
  have h2Q : 2*((H:ℝ)*C/(M:ℝ))^2 ≤ ε^2/8 := by
    have hQeq : 2*((H:ℝ)^2*C^2*(ε^2/(16*(((H:ℝ)^2*C^2)+1))))
        = (ε^2/8)*(((H:ℝ)^2*C^2)/(((H:ℝ)^2*C^2)+1)) := by
      have hA1 : ((H:ℝ)^2*C^2)+1 ≠ 0 := ne_of_gt (by positivity)
      have h1 : (16:ℝ)*(((H:ℝ)^2*C^2)+1) ≠ 0 := mul_ne_zero (by norm_num) hA1
      have h2 : (8:ℝ) ≠ 0 := by norm_num
      field_simp
      ring
    calc 2*((H:ℝ)*C/(M:ℝ))^2 ≤ 2*((H:ℝ)^2*C^2*(ε^2/(16*(((H:ℝ)^2*C^2)+1)))) := by
            linarith [hQ2]
      _ = (ε^2/8)*(((H:ℝ)^2*C^2)/(((H:ℝ)^2*C^2)+1)) := hQeq
      _ ≤ ε^2/8 := hfracbound _ (by positivity)
  -- final assembly with (a+b)^2 ≤ 2a^2 + 2b^2
  have hPl : 2*((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
      ≤ 2*(C^2/(H:ℝ) + (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹)) := by
    have h := mul_le_mul_of_nonneg_left hPfin (show (0:ℝ) ≤ 2 by norm_num)
    linarith
  have hAsq : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2
      ≤ 2*((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
        + 2*(((H:ℝ)*C/(M:ℝ))^2) := by
    have hPQnn : (0:ℝ) ≤ ((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M,
          ∑ h ∈ Finset.range H, x (n + h)‖ + (H:ℝ)*C/(M:ℝ) := by positivity
    have h1 : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2
        ≤ (((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
          + (H:ℝ)*C/(M:ℝ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hAnorm 2
    have h2 : ((((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
          + (H:ℝ)*C/(M:ℝ))^2)
        ≤ 2*((((M:ℝ)*(H:ℝ))⁻¹
          * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
          + 2*(((H:ℝ)*C/(M:ℝ))^2) := by
      nlinarith [sq_nonneg ((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖) - ((H:ℝ)*C/(M:ℝ)))]
    linarith
  have hfin : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2 ≤ ε^2/2 := by
    have h2C2H : 2*(C^2/(H:ℝ)) ≤ ε^2/8 := by linarith [hHC]
    have h2K0 : 2*(ε^2/16) = ε^2/8 := by ring
    linarith [hAsq, hPl, h2C2H, h2K0, h2E, h2Q]
  have hlt : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2 < ε^2 := by
    linarith [hfin, hε2]
  have hAlt : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖ < ε := by
    have h := abs_lt_of_sq_lt_sq hlt hε.le
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [dist_zero_right]
  exact hAlt

/-- Fixed-point submodule of a power of an isometry (N9–N12 setup). -/
private def sarkozyFix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) (m : ℕ) : Submodule ℝ H :=
  LinearMap.eqLocus ((U ^ m).toLinearMap) LinearMap.id

/-- Closed span of all nontrivial fixed-point submodules (N9–N12 setup). -/
private def sarkozyWclos {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (U : H →ₗᵢ[ℝ] H) : Submodule ℝ H :=
  (⨆ j : ℕ, sarkozyFix U (j + 1)).topologicalClosure

/-- Quadratic correlations vanish on the orthocomplement (N9). -/
private lemma sarkozy_quad_corr_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H)
    (w : H) (hw : w ∈ (sarkozyWclos U)ᗮ) (Q h : ℕ) (hQ : 1 ≤ Q) (hh : 1 ≤ h) :
    Filter.Tendsto
      (fun (M : ℕ) => (M : ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ ((U ^ (Q*Q*((n+h)*(n+h)))) w) ((U ^ (Q*Q*(n*n))) w))
      Filter.atTop (nhds 0) := by
  have ha1 : 1 ≤ 2*Q*Q*h :=
    calc (1:ℕ) = 1*1*1*1 := by ring
      _ ≤ 2*Q*Q*h :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) hQ) hQ) hh
  have hnormT : ‖((U ^ (2*Q*Q*h)).toContinuousLinearMap : H →L[ℝ] H)‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  -- per-term reduction to a linear orbit correlation
  have hexp : ∀ n : ℕ, inner ℝ ((U^(Q*Q*((n+h)*(n+h)))) w) ((U^(Q*Q*(n*n))) w)
      = inner ℝ ((((U^(2*Q*Q*h))^n)) ((U^(Q*Q*(h*h))) w)) w := by
    intro n
    have he : Q*Q*((n+h)*(n+h))
        = Q*Q*(n*n) + ((2*Q*Q*h)*n + Q*Q*(h*h)) := by ring
    have hinner : ((U^((2*Q*Q*h)*n + Q*Q*(h*h))) w)
        = ((((U^(2*Q*Q*h))^n)) ((U^(Q*Q*(h*h))) w)) := by
      rw [pow_add, LinearIsometry.coe_mul, Function.comp_apply, pow_mul]
    have hU : ((U^(Q*Q*((n+h)*(n+h)))) w)
        = ((U^(Q*Q*(n*n))) (((U^((2*Q*Q*h)*n + Q*Q*(h*h))) w))) := by
      rw [he, pow_add, LinearIsometry.coe_mul, Function.comp_apply]
    rw [hU, hinner]
    exact LinearIsometry.inner_map_map _ _ _
  have hbir : ∀ M : ℕ, (M:ℝ)⁻¹ • (∑ n ∈ Finset.range M,
        ((((U^(2*Q*Q*h))^n)) ((U^(Q*Q*(h*h))) w)))
      = birkhoffAverage ℝ (⇑((U ^ (2*Q*Q*h)).toContinuousLinearMap)) id M
        ((U^(Q*Q*(h*h))) w) := by
    intro M
    simp only [birkhoffAverage, birkhoffSum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    simp only [LinearIsometry.coe_pow, LinearIsometry.coe_toContinuousLinearMap, id_eq]
  have hMeq : ∀ M : ℕ, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ ((U ^ (Q*Q*((n+h)*(n+h)))) w) ((U ^ (Q*Q*(n*n))) w)
      = inner ℝ (birkhoffAverage ℝ
        (⇑((U ^ (2*Q*Q*h)).toContinuousLinearMap)) id M ((U^(Q*Q*(h*h))) w)) w := by
    intro M
    rw [← hbir M, real_inner_smul_left, sum_inner]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact hexp n
  have hergodic := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
    ((U ^ (2*Q*Q*h)).toContinuousLinearMap) hnormT ((U^(Q*Q*(h*h))) w)
  have hclosed : IsClosed ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1 :
      Submodule ℝ H) : Set H) := by
    change IsClosed {x : H | ((U ^ (2*Q*Q*h)).toContinuousLinearMap) x
      = (1 : H →L[ℝ] H) x}
    exact isClosed_eq (((U ^ (2*Q*Q*h)).toContinuousLinearMap).continuous)
      (1 : H →L[ℝ] H).continuous
  let _hcomplete : CompleteSpace
      ↥((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1 : Submodule ℝ H)) :=
    completeSpace_coe_iff_isComplete.mpr hclosed.isComplete
  let _hproj : (((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).HasOrthogonalProjection :=
    inferInstance
  -- the ergodic limit lies in W
  have hmemT : ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H)
      ∈ ((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1 :=
    ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w)).2
  have hmem : ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H) ∈ sarkozyFix U (2*Q*Q*h) := by
    have hTmem := hmemT
    rw [LinearMap.mem_eqLocus] at hTmem
    change (U^(2*Q*Q*h)).toLinearMap _ = LinearMap.id _
    exact hTmem
  have haW : ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H) ∈ sarkozyWclos U := by
    have h1 : sarkozyFix U (2*Q*Q*h) ≤ ⨆ j : ℕ, sarkozyFix U (j + 1) := by
      have heq : sarkozyFix U (2*Q*Q*h) = sarkozyFix U ((2*Q*Q*h - 1) + 1) := by
        congr 1
        omega
      rw [heq]
      exact le_iSup (fun j => sarkozyFix U (j + 1)) _
    exact Submodule.le_topologicalClosure _ (h1 hmem)
  have hzero : inner ℝ ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H) w = 0 :=
    Submodule.inner_right_of_mem_orthogonal haW hw
  have hlim : Filter.Tendsto (fun M => inner ℝ (birkhoffAverage ℝ
      (⇑((U ^ (2*Q*Q*h)).toContinuousLinearMap)) id M ((U^(Q*Q*(h*h))) w)) w)
      Filter.atTop
      (nhds (inner ℝ ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
        ((U^(Q*Q*(h*h))) w) : H) w)) :=
    Filter.Tendsto.inner hergodic tendsto_const_nhds
  rw [hzero] at hlim
  exact Filter.Tendsto.congr (fun M => (hMeq M).symm) hlim

/-- Quadratic averages vanish on the orthocomplement (N10). -/
private lemma sarkozy_quad_avg_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H)
    (w : H) (hw : w ∈ (sarkozyWclos U)ᗮ) (Q : ℕ) (hQ : 1 ≤ Q) :
    Filter.Tendsto
      (fun (M : ℕ) => (M : ℝ)⁻¹ • ∑ n ∈ Finset.range M, ((U ^ (Q*Q*(n*n))) w))
      Filter.atTop (nhds 0) := by
  have h := sarkozy_vdc_tendsto (x := fun n => ((U ^ (Q*Q*(n*n))) w)) (C := ‖w‖)
    (norm_nonneg _) (fun n => le_of_eq (((U ^ (Q*Q*(n*n))).norm_map) w))
    (fun d hd => sarkozy_quad_corr_tendsto U w hw Q d hQ hd)
  exact h

/-- Membership in a fixed-point submodule from the isometry equation (N11 helper). -/
private lemma sarkozyFix_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) (m : ℕ) (x : H) (h : (U ^ m) x = x) : x ∈ sarkozyFix U m := by
  change x ∈ LinearMap.eqLocus ((U ^ m).toLinearMap) (LinearMap.id : H →ₗ[ℝ] H)
  rw [LinearMap.mem_eqLocus]
  change (((U ^ m) x = x))
  exact h

/-- Isometry equation from fixed-point submodule membership (N11 helper). -/
private lemma sarkozyFix_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) (m : ℕ) (x : H) (h : x ∈ sarkozyFix U m) : (U ^ m) x = x := by
  have h2 : ((U ^ m).toLinearMap) x = (LinearMap.id : H →ₗ[ℝ] H) x := by
    have := h
    change x ∈ LinearMap.eqLocus ((U ^ m).toLinearMap) (LinearMap.id : H →ₗ[ℝ] H) at this
    rwa [LinearMap.mem_eqLocus] at this
  change (((U ^ m) x = x))
  exact h2

/-- Iterating a fixed point stays fixed (N11 helper). -/
private lemma sarkozyFix_pow_iter {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) {m : ℕ} {x : H} (h : (U ^ m) x = x) (k : ℕ) :
    (((U ^ m) ^ k) x = x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, LinearIsometry.coe_mul, Function.comp_apply, h]
    exact ih

/-- Fixed-point submodules grow along divisibility (N11 helper). -/
private lemma sarkozyFix_mono_div {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) {a c : ℕ} (h : a ∣ c) : sarkozyFix U a ≤ sarkozyFix U c := by
  intro x hx
  obtain ⟨k, rfl⟩ := h
  have hxa := sarkozyFix_eq U a x hx
  have hkk : (((U ^ a) ^ k) x = x) := sarkozyFix_pow_iter U hxa k
  have hck : (U ^ (a * k)) x = x := by
    rw [pow_mul]
    exact hkk
  exact sarkozyFix_mem U (a * k) x hck

/-- Hilbert-space Sárközy recurrence (N11): square-return correlations force orthogonality
to every fixed vector. -/
private lemma sarkozy_hilbert_sarkozy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H) (v : H)
    (hhyp : ∀ k : ℕ, 0 < k → inner ℝ ((U ^ (k*k)) v) v = 0) :
    ∀ u : H, U u = u → inner ℝ u v = 0 := by
  have hWclosed : IsClosed (((sarkozyWclos U) : Submodule ℝ H) : Set H) :=
    Submodule.isClosed_topologicalClosure (⨆ j : ℕ, sarkozyFix U (j + 1))
  let _hWcomplete : CompleteSpace ↥((sarkozyWclos U : Submodule ℝ H)) :=
    completeSpace_coe_iff_isComplete.mpr hWclosed.isComplete
  let _hWproj : (sarkozyWclos U).HasOrthogonalProjection := inferInstance
  set r : H := (sarkozyWclos U).starProjection v with hrdef
  set w : H := v - r with hwdef
  have hr_mem : r ∈ sarkozyWclos U := by
    rw [hrdef]
    exact (((sarkozyWclos U).orthogonalProjectionOnto v)).2
  have hw_mem : w ∈ (sarkozyWclos U)ᗮ := by
    rw [hwdef, hrdef]
    exact Submodule.sub_starProjection_mem_orthogonal v
  have hrv : inner ℝ r v = ‖r‖^2 := by
    have ev : v = r + w := by
      rw [hwdef]
      abel
    rw [ev, inner_add_right, real_inner_self_eq_norm_sq,
      Submodule.inner_right_of_mem_orthogonal hr_mem hw_mem, add_zero]
  have hdirected : Directed (· ≤ ·) (fun j => sarkozyFix U (j + 1)) := by
    intro i j
    have hi : 1 ≤ i + 1 := Nat.le_add_left 1 i
    have hj : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have h1 : (1:ℕ) ≤ (i+1)*(j+1) := by
      calc (1:ℕ) = 1*1 := by ring
        _ ≤ (i+1)*(j+1) := Nat.mul_le_mul hi hj
    have e : ((i+1)*(j+1) - 1) + 1 = (i+1)*(j+1) := by omega
    refine ⟨(i+1)*(j+1) - 1, ?_, ?_⟩
    · change sarkozyFix U (i + 1) ≤ sarkozyFix U (((i + 1) * (j + 1) - 1) + 1)
      rw [e]
      exact sarkozyFix_mono_div U (dvd_mul_right _ _)
    · change sarkozyFix U (j + 1) ≤ sarkozyFix U (((i + 1) * (j + 1) - 1) + 1)
      rw [e]
      exact sarkozyFix_mono_div U ⟨i+1, by ring⟩
  -- the per-threshold estimate
  have hmain : ∀ ε : ℝ, 0 < ε → ‖r‖^2 ≤ 2*ε*‖v‖ := by
    intro ε hε
    have hrclo : r ∈ closure ((⨆ j : ℕ, sarkozyFix U (j + 1) : Submodule ℝ H) : Set H) :=
      hr_mem
    rw [Metric.mem_closure_iff] at hrclo
    obtain ⟨b, hbmem, hdist⟩ := hrclo ε hε
    have hbU : b ∈ ⨆ j : ℕ, sarkozyFix U (j + 1) := hbmem
    rw [(Submodule.mem_iSup_of_directed _ hdirected)] at hbU
    obtain ⟨j, hjb⟩ := hbU
    have hm1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have hrb : ‖r - b‖ < ε := by
      rwa [dist_eq_norm] at hdist
    have hbm := sarkozyFix_eq U (j+1) b hjb
    have hbQ : ∀ n : ℕ, (U^((j+1)*(j+1)*(n*n))) b = b := by
      intro n
      have hpow : ∀ k : ℕ, (((U^(j+1))^k) b = b) :=
        fun k => sarkozyFix_pow_iter U hbm k
      have e : (j+1)*(j+1)*(n*n) = (j+1)*((j+1)*(n*n)) := by ring
      rw [e, pow_mul]
      exact hpow _
    have hsum0 : ∀ M : ℕ, 1 ≤ M →
        (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v) = ‖v‖^2 := by
      intro M hM
      have h0mem : 0 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ h0mem]
      have e0 : inner ℝ ((U^((j+1)*(j+1)*(0*0))) v) v = ‖v‖^2 := by
        have e00 : (j+1)*(j+1)*(0*0) = 0 := by ring
        rw [e00, pow_zero]
        simp
      rw [e0]
      have erest : (∑ n ∈ (Finset.range M).erase 0,
          inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hn0 : n ≠ 0 := Finset.ne_of_mem_erase hn
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hQn : 0 < (j+1)*n := Nat.mul_pos (by omega) hnpos
        have e : (j+1)*(j+1)*(n*n) = ((j+1)*n)*((j+1)*n) := by ring
        rw [e]
        exact hhyp _ hQn
      rw [erest, add_zero]
    have havg : ∀ M : ℕ, 1 ≤ M →
        (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v)
        = ‖v‖^2/(M:ℝ) - (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
          inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) := by
      intro M hM
      have esub : ∀ n : ℕ, inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v
          = inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v
            - inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v := by
        intro n
        have hmap : ((U^((j+1)*(j+1)*(n*n))) w)
            = ((U^((j+1)*(j+1)*(n*n))) v) - ((U^((j+1)*(j+1)*(n*n))) r) := by
          rw [hwdef, map_sub]
        rw [hmap, inner_sub_left]
      have esum : (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v)
          = (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v)
            - (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun n _ => esub n)
      rw [esum, hsum0 M hM, div_eq_inv_mul]
      ring
    have hterm_lb : ∀ n : ℕ, ‖r‖^2 - 2*ε*‖v‖
        ≤ inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v := by
      intro n
      have e : ((U^((j+1)*(j+1)*(n*n))) r)
          = ((U^((j+1)*(j+1)*(n*n))) b) + ((U^((j+1)*(j+1)*(n*n))) (r - b)) := by
        rw [← map_add]
        congr 1
        abel
      have hbQn := hbQ n
      rw [e, hbQn, inner_add_left]
      have h1 : inner ℝ b v ≥ ‖r‖^2 - ε*‖v‖ := by
        have ebr : b = r - (r - b) := by abel
        have hcs : |inner ℝ (r - b) v| ≤ ε*‖v‖ := by
          calc |inner ℝ (r - b) v| ≤ ‖r - b‖ * ‖v‖ := abs_real_inner_le_norm _ _
            _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right (le_of_lt hrb) (norm_nonneg _)
        have ebrw : inner ℝ b v = inner ℝ r v - inner ℝ (r - b) v := by
          conv_lhs => rw [ebr]
          rw [inner_sub_left]
        rw [hrv] at ebrw
        have hab := (abs_le.mp hcs).2
        linarith
      have h2 : inner ℝ (((U^((j+1)*(j+1)*(n*n))) (r - b))) v ≥ -(ε*‖v‖) := by
        have hcs : |inner ℝ (((U^((j+1)*(j+1)*(n*n))) (r - b))) v| ≤ ε*‖v‖ := by
          calc |inner ℝ (((U^((j+1)*(j+1)*(n*n))) (r - b))) v|
                ≤ ‖((U^((j+1)*(j+1)*(n*n))) (r - b))‖ * ‖v‖ :=
                abs_real_inner_le_norm _ _
            _ = ‖r - b‖ * ‖v‖ := by rw [LinearIsometry.norm_map]
            _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right (le_of_lt hrb) (norm_nonneg _)
        have hab := (abs_le.mp hcs).1
        linarith
      linarith
    have hLHS : Filter.Tendsto (fun (M : ℕ) => (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v)
        Filter.atTop (nhds 0) := by
      have h10 := sarkozy_quad_avg_tendsto U w hw_mem (j+1) hm1
      have e : ∀ M : ℕ, inner ℝ ((M:ℝ)⁻¹ • ∑ n ∈ Finset.range M,
          ((U^((j+1)*(j+1)*(n*n))) w)) v
          = (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
            inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v := by
        intro M
        rw [real_inner_smul_left, sum_inner]
      have hinner : Filter.Tendsto (fun (M : ℕ) => inner ℝ ((M:ℝ)⁻¹ • ∑ n ∈ Finset.range M,
          ((U^((j+1)*(j+1)*(n*n))) w)) v) Filter.atTop (nhds (inner ℝ (0:H) v)) :=
        Filter.Tendsto.inner h10 tendsto_const_nhds
      rw [show inner ℝ (0:H) v = 0 from inner_zero_left _] at hinner
      exact Filter.Tendsto.congr (fun M => e M) hinner
    have hBlim : Filter.Tendsto (fun (M : ℕ) => ‖v‖^2/(M:ℝ) - (‖r‖^2 - 2*ε*‖v‖))
        Filter.atTop (nhds (-(‖r‖^2 - 2*ε*‖v‖))) := by
      have h1 : Filter.Tendsto (fun (M : ℕ) => ‖v‖^2/(M:ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have h2 : Filter.Tendsto (fun (M : ℕ) => ‖v‖^2/(M:ℝ) - (‖r‖^2 - 2*ε*‖v‖))
          Filter.atTop (nhds (0 - (‖r‖^2 - 2*ε*‖v‖))) :=
        h1.sub tendsto_const_nhds
      rwa [zero_sub] at h2
    have hAleB : ∀ᶠ (M : ℕ) in Filter.atTop, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
          inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v
          ≤ ‖v‖^2/(M:ℝ) - (‖r‖^2 - 2*ε*‖v‖) := by
      rw [Filter.eventually_atTop]
      refine ⟨1, fun M hM => ?_⟩
      have hMpos : (0:ℝ) < (M:ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
      have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
      have hM1nn : (0:ℝ) ≤ (M:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      have hlb : (‖r‖^2 - 2*ε*‖v‖)
          ≤ (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
            inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) := by
        have h1 : (M:ℝ) * (‖r‖^2 - 2*ε*‖v‖)
            ≤ ∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v := by
          calc (M:ℝ) * (‖r‖^2 - 2*ε*‖v‖)
              = ∑ _n ∈ Finset.range M, (‖r‖^2 - 2*ε*‖v‖) := by
                simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum (fun n _ => hterm_lb n)
        calc (‖r‖^2 - 2*ε*‖v‖) = (M:ℝ)⁻¹ * ((M:ℝ) * (‖r‖^2 - 2*ε*‖v‖)) :=
                (inv_mul_cancel_left₀ hMne _).symm
          _ ≤ (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
              inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) :=
                mul_le_mul_of_nonneg_left h1 hM1nn
      have havgM := havg M hM
      linarith
    have hle : (0:ℝ) ≤ -((‖r‖^2 - 2*ε*‖v‖)) :=
      le_of_tendsto_of_tendsto hLHS hBlim hAleB
    linarith
  have hr0 : r = 0 := by
    by_contra hcon
    have hrpos : (0:ℝ) < ‖r‖ := by
      rcases eq_or_lt_of_le (norm_nonneg r) with h | h
      · exfalso
        apply hcon
        simpa using h.symm
      · exact h
    have hR : (0:ℝ) < ‖r‖^2 := pow_pos hrpos 2
    have hden : (0:ℝ) < 4*(‖v‖+1) := by positivity
    have hdenne : 4*(‖v‖+1) ≠ 0 := ne_of_gt hden
    have hmain2 := hmain (‖r‖^2/(4*(‖v‖+1))) (div_pos hR hden)
    have hclear : ‖r‖^2 * (4*(‖v‖+1)) ≤ 2*‖r‖^2*‖v‖ := by
      have hmul := mul_le_mul_of_nonneg_right hmain2 hden.le
      have eED : 2*(‖r‖^2/(4*(‖v‖+1)))*‖v‖*(4*(‖v‖+1)) = 2*‖r‖^2*‖v‖ := by
        field_simp
      rwa [eED] at hmul
    have hexpand : ‖r‖^2 * (4*(‖v‖+1)) = 4*(‖r‖^2*‖v‖) + 4*‖r‖^2 := by ring
    have hRV : (0:ℝ) ≤ ‖r‖^2*‖v‖ := mul_nonneg (sq_nonneg _) (norm_nonneg _)
    linarith [hclear, hR, hRV, hexpand]
  have hvw : v = w := by
    rw [hwdef, hr0, sub_zero]
  intro u hu
  have huW : u ∈ sarkozyWclos U := by
    have e1 : (U^1) u = u := by
      rw [pow_one]
      exact hu
    have h1 : u ∈ sarkozyFix U 1 := sarkozyFix_mem U 1 u e1
    have h2 : sarkozyFix U 1 ≤ ⨆ j : ℕ, sarkozyFix U (j + 1) :=
      le_iSup (fun j => sarkozyFix U (j + 1)) 0
    exact Submodule.le_topologicalClosure _ (h2 h1)
  rw [hvw]
  exact Submodule.inner_right_of_mem_orthogonal huW hw_mem

/-- Mean-ergodic fixed vector with positive correlation (N12). -/
private lemma sarkozy_fixed_inner_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H) (v : H) (δ : ℝ)
    (hδ : 0 < δ)
    (hfej : ∀ L : ℕ, 0 < L → (L:ℝ)^2 * δ^2 ≤ ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
      inner ℝ ((U^h) v) ((U^h') v)) :
    ∃ u : H, (U u = u) ∧ 0 < inner ℝ u v := by
  have hnormT : ‖(U.toContinuousLinearMap : H →L[ℝ] H)‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  have hergodic := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
    (U.toContinuousLinearMap) hnormT v
  have hclosed : IsClosed (((U.toContinuousLinearMap).eqLocus 1 :
      Submodule ℝ H) : Set H) := by
    change IsClosed {x : H | (U.toContinuousLinearMap) x = (1 : H →L[ℝ] H) x}
    exact isClosed_eq (U.toContinuousLinearMap).continuous (1 : H →L[ℝ] H).continuous
  let _hcomplete : CompleteSpace
      ↥(((U.toContinuousLinearMap).eqLocus 1 : Submodule ℝ H)) :=
    completeSpace_coe_iff_isComplete.mpr hclosed.isComplete
  let _hproj : ((U.toContinuousLinearMap).eqLocus 1).HasOrthogonalProjection :=
    inferInstance
  set p : H := (((U.toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto v : H)
    with hpdef
  have hmemT : p ∈ (U.toContinuousLinearMap).eqLocus 1 := by
    rw [hpdef]
    exact (((U.toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto v).2
  -- Birkhoff averages are scaled orbit sums
  have havec : ∀ L : ℕ, birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v
      = (L:ℝ)⁻¹ • ∑ h ∈ Finset.range L, ((U^h) v) := by
    intro L
    simp only [birkhoffAverage, birkhoffSum]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    simp only [LinearIsometry.coe_pow, LinearIsometry.coe_toContinuousLinearMap, id_eq]
  have hnormsq : ∀ L : ℕ, ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖^2
      = (L:ℝ)⁻¹^2 * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
        inner ℝ ((U^h) v) ((U^h') v)) := by
    intro L
    have e1 : ‖(L:ℝ)⁻¹‖^2 = (L:ℝ)⁻¹^2 := by
      rw [Real.norm_eq_abs, sq_abs]
    have e2 : ‖∑ h ∈ Finset.range L, ((U^h) v)‖^2
        = ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          inner ℝ ((U^h) v) ((U^h') v) := by
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      apply Finset.sum_congr rfl
      intro h _
      exact inner_sum _ _ _
    rw [havec L, norm_smul, mul_pow, e1, e2]
  have hδle : ∀ L : ℕ, 1 ≤ L → δ ≤ ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖ := by
    intro L hL
    have hsqL := hnormsq L
    have hfejL := hfej L (by omega : 0 < L)
    have hsq_bound : δ^2 ≤ ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖^2 := by
      rw [hsqL]
      have hMne : (L:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL))
      have hnn : (0:ℝ) ≤ (L:ℝ)⁻¹^2 :=
        pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 2
      calc δ^2 = (L:ℝ)⁻¹^2 * ((L:ℝ)^2 * δ^2) := by field_simp
        _ ≤ (L:ℝ)⁻¹^2 * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
            inner ℝ ((U^h) v) ((U^h') v)) :=
            mul_le_mul_of_nonneg_left hfejL hnn
    have h := abs_le_of_sq_le_sq hsq_bound (norm_nonneg _)
    rwa [abs_of_pos hδ] at h
  have hnormlim := Filter.Tendsto.norm hergodic
  have hinev : ∀ᶠ L in Filter.atTop,
      δ ≤ ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖ := by
    rw [Filter.eventually_atTop]
    exact ⟨1, fun L hL => hδle L hL⟩
  have hple : δ ≤ ‖p‖ := by
    have h := ge_of_tendsto hnormlim hinev
    rw [hpdef]
    exact h
  have hu : U p = p := by
    have h := hmemT
    rw [LinearMap.mem_eqLocus] at h
    change (U p = p)
    exact h
  have hvo : v - p ∈ ((U.toContinuousLinearMap).eqLocus 1)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal v
  have hinner : inner ℝ p v = ‖p‖^2 := by
    have e : v = p + (v - p) := by abel
    rw [e, inner_add_right, real_inner_self_eq_norm_sq]
    have h0 : inner ℝ p (v - p) = 0 :=
      Submodule.inner_right_of_mem_orthogonal hmemT hvo
    rw [h0, add_zero]
  refine ⟨p, hu, ?_⟩
  rw [hinner]
  calc (0:ℝ) < δ^2 := by positivity
    _ ≤ ‖p‖^2 := pow_le_pow_left₀ hδ.le hple 2

/--
**Furstenberg–Sárközy theorem.** Let $A$ be a set of natural numbers, and suppose there is a real
number $\delta > 0$ such that for every natural number $M$ there is a natural number $N \ge M$
with $\delta N \le |A \cap \{0, 1, \dots, N - 1\}|$. Then there are $a, b \in A$ and a natural
number $k > 0$ with $a < b$ and $b = a + k^2$.

Proves `Wanted` entry `furstenberg_sarkozy`.

Source: A. Sárközy, Acta Math. Acad. Sci. Hungar. 31 (1978) and H. Furstenberg,
J. Analyse Math. 31 (1977); Lean states positive upper density via `initialSegmentCount` with
arbitrarily large N.
-/
public theorem furstenberg_sarkozy :
    ∀ A : Set ℕ,
      (∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
        δ * (N : ℝ) ≤ ((initialSegmentCount A N : ℕ) : ℝ)) →
      ∃ a b k : ℕ, a ∈ A ∧ b ∈ A ∧ 0 < k ∧ a < b ∧ b = a + k * k := by
  intro A hA
  obtain ⟨δ, hδ, hfreq⟩ := hA
  by_contra hcon
  push Not at hcon
  obtain ⟨γ, hsymm, hpos, hzero, hfej⟩ := sarkozy_corr_limit A δ hδ hfreq hcon
  obtain ⟨E, hN, hI, hC, U, v, huv⟩ := sarkozy_dilation γ hsymm hpos
  let hN' := hN
  let hI' := hI
  let hC' := hC
  have hU0 : ((U ^ (0:ℕ)) v) = v := by simp
  have h11hyp : ∀ k : ℕ, 0 < k → inner ℝ ((U ^ (k*k)) v) v = 0 := by
    intro k hk
    have h1 : inner ℝ ((U ^ (k*k)) v) ((U ^ (0:ℕ)) v)
        = γ ((((k*k : ℕ)):ℤ) - (((0:ℕ)):ℤ)) := huv (k*k) 0
    rw [hU0] at h1
    rw [h1]
    have ecast : ((((k*k : ℕ)):ℤ) - (((0:ℕ)):ℤ)) = (k:ℤ)*(k:ℤ) := by
      rw [Nat.cast_mul, Nat.cast_zero, sub_zero]
    rw [ecast]
    exact hzero k hk
  have h12hyp : ∀ L : ℕ, 0 < L → (L:ℝ)^2 * δ^2 ≤ ∑ h ∈ Finset.range L,
      ∑ h' ∈ Finset.range L, inner ℝ ((U^h) v) ((U^h') v) := by
    intro L hL
    calc (L:ℝ)^2 * δ^2
        ≤ ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h:ℤ) - h') :=
          hfej L hL
      _ = ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          inner ℝ ((U^h) v) ((U^h') v) := by
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro h' _
          exact (huv h h').symm
  obtain ⟨u, hu, hpos_inner⟩ := sarkozy_fixed_inner_pos U v δ hδ h12hyp
  have h11 := sarkozy_hilbert_sarkozy U v h11hyp u hu
  linarith

end MathlibExt.Combinatorics.Additive.SarkozyWanted
