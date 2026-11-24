/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteWeight

/-!
# Semigraphoid lemmas for finite conditional independence

Symmetry, decomposition and weak union for `MetaMathlibExt.FiniteWeight.CondIndep`
over a general finite vertex type. Weak union requires a nonnegative weight: for
signed weights it fails, and the zero-conditioning-marginal case uses
`marginal_anti`.
-/

@[expose] public section

namespace MetaMathlibExt.FiniteWeight

/-- Conditional independence is symmetric in its first two arguments. -/
theorem CondIndep.symm {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    {p : (V → α) → ℝ} {A B S : Set V} (h : CondIndep p A B S) : CondIndep p B A S := by
  intro x
  have h' := h x
  rwa [Set.union_comm B A, mul_comm (marginal p (B ∪ S) x) (marginal p (A ∪ S) x)]

/-- A marginal only depends on the values on its variable set. -/
theorem marginal_congr {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    {p : (V → α) → ℝ} {U : Set V} {x z : V → α}
    (h : ∀ v ∈ U, z v = x v) : marginal p U z = marginal p U x := by
  classical
  have hset : (Finset.univ.filter fun y : V → α => ∀ v ∈ U, y v = z v) =
      Finset.univ.filter fun y : V → α => ∀ v ∈ U, y v = x v := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hy v hv
    · rw [hy v hv, h v hv]
    · rw [hy v hv, h v hv]
  simp only [marginal, hset]

open Classical in
/-- Summing a marginal over all assignments to the variables in `T` removes `T`
from the marginal's variable set. -/
theorem sum_marginal_filter_compl {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    (p : (V → α) → ℝ) (T : Finset V) (U : Set V) (hTU : ↑T ⊆ U) (x : V → α) :
    ∑ z ∈ Finset.univ.filter (fun z : V → α => ∀ v ∈ (↑T : Set V)ᶜ, z v = x v),
        marginal p U z =
      marginal p (U \ ↑T) x := by
  classical
  simp only [marginal]
  trans ∑ w ∈ (Finset.univ.filter
      (fun z : V → α => ∀ v ∈ (↑T : Set V)ᶜ, z v = x v)).sigma
      (fun z => Finset.univ.filter (fun y : V → α => ∀ v ∈ U, y v = z v)), p w.2
  · simp only [Finset.sum_sigma]
  refine Finset.sum_nbij' (fun w => w.2)
    (fun y => ⟨fun v => if v ∈ T then y v else x v, y⟩) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨hz, hy⟩ := hw
    intro v hv
    simp only [Set.mem_sdiff, Finset.mem_coe] at hv
    rw [hy v hv.1]
    exact hz v hv.2
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro v hv
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hv
      show (if v ∈ T then y v else x v) = x v
      rw [ite_eq_right hv]
    · intro v hvU
      by_cases hvT : v ∈ T
      · show y v = (if v ∈ T then y v else x v)
        rw [ite_eq_left hvT]
      · show y v = (if v ∈ T then y v else x v)
        rw [ite_eq_right hvT]
        exact hy v ⟨hvU, hvT⟩
  · intro w hw
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hz, hy⟩ := hw
    obtain ⟨z, y⟩ := w
    have hzy : (fun v => if v ∈ T then y v else x v) = z := by
      funext v
      by_cases hvT : v ∈ T
      · simp only [hvT, ite_true]
        exact hy v (hTU hvT)
      · simp only [hvT, ite_false]
        exact (hz v hvT).symm
    simp only [hzy]
  · intro y _
    rfl
  · intro w _
    rfl

/-- **Decomposition** for finite conditional independence: from joint independence
of `X` and `Y ∪ W` given `S`, with `X` disjoint from `Y`, the part `Y` may be dropped. -/
theorem condIndep_decomp {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    {p : (V → α) → ℝ} {X Y W S : Set V}
    (h : CondIndep p X (Y ∪ W) S) (hdisj : Disjoint X Y) : CondIndep p X W S := by
  classical
  intro x
  set T : Finset V := Finset.univ.filter (fun v => v ∈ Y \ (X ∪ W ∪ S)) with hT
  have hTcoe : (↑T : Set V) = Y \ (X ∪ W ∪ S) := by
    ext v
    simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_univ, true_and]
  have hTout : ∀ v ∈ X ∪ W ∪ S, v ∉ (↑T : Set V) := by
    intro v hv
    rw [hTcoe]
    simp only [Set.mem_sdiff]
    exact fun hh => hh.2 hv
  have hTS : ∀ v ∈ S, v ∈ (↑T : Set V)ᶜ := fun v hv => hTout v (Or.inr hv)
  have hTXS : ∀ v ∈ X ∪ S, v ∈ (↑T : Set V)ᶜ := by
    intro v hv
    cases hv with
    | inl hx => exact hTout v (Or.inl (Or.inl hx))
    | inr hs => exact hTout v (Or.inr hs)
  have hTsub1 : (↑T : Set V) ⊆ X ∪ (Y ∪ W) ∪ S := by
    rw [hTcoe]
    intro v hv
    simp only [Set.mem_sdiff, Set.mem_union] at hv ⊢
    tauto
  have hTsub2 : (↑T : Set V) ⊆ Y ∪ W ∪ S := by
    rw [hTcoe]
    intro v hv
    simp only [Set.mem_sdiff, Set.mem_union] at hv ⊢
    tauto
  have hSz : ∀ z ∈ Finset.univ.filter (fun z : V → α => ∀ v ∈ (↑T : Set V)ᶜ, z v = x v),
      marginal p S z = marginal p S x := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact marginal_congr (fun v hv => hz v (hTS v hv))
  have hXSz : ∀ z ∈ Finset.univ.filter (fun z : V → α => ∀ v ∈ (↑T : Set V)ᶜ, z v = x v),
      marginal p (X ∪ S) z = marginal p (X ∪ S) x := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact marginal_congr (fun v hv => hz v (hTXS v hv))
  have key1 := sum_marginal_filter_compl p T (X ∪ (Y ∪ W) ∪ S) hTsub1 x
  have key2 := sum_marginal_filter_compl p T (Y ∪ W ∪ S) hTsub2 x
  have hsum : (∑ z ∈ Finset.univ.filter (fun z : V → α => ∀ v ∈ (↑T : Set V)ᶜ, z v = x v),
        marginal p (X ∪ (Y ∪ W) ∪ S) z) * marginal p S x =
      marginal p (X ∪ S) x * (∑ z ∈ Finset.univ.filter
        (fun z : V → α => ∀ v ∈ (↑T : Set V)ᶜ, z v = x v), marginal p (Y ∪ W ∪ S) z) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [← hSz z hz, ← hXSz z hz]
    exact h z
  rw [key1, key2] at hsum
  have hdisjXY : ∀ v : V, v ∈ X → v ∈ Y → False :=
    fun v hx hy => Set.disjoint_left.mp hdisj hx hy
  have eU1 : (X ∪ (Y ∪ W) ∪ S) \ ↑T = X ∪ W ∪ S := by
    rw [hTcoe]
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    have h' := hdisjXY v
    tauto
  have eU2 : (Y ∪ W ∪ S) \ ↑T = W ∪ S := by
    rw [hTcoe]
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    have h' := hdisjXY v
    tauto
  rw [eU1, eU2] at hsum
  exact hsum

/-- **Weak union** for finite conditional independence of a nonnegative weight:
part of the first family may move into the conditioning family. Nonnegativity is
essential: for signed weights weak union fails, and the zero-conditioning-marginal
case uses that marginals fixing more variables vanish. -/
theorem condIndep_weak_union {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    {p : (V → α) → ℝ} (hp : ∀ x, 0 ≤ p x) {A W B S : Set V}
    (h : CondIndep p (A ∪ W) B S) (hdisj : Disjoint (A ∪ W) B) :
    CondIndep p A B (S ∪ W) := by
  have hBA : Disjoint B A := Disjoint.mono le_rfl Set.subset_union_left hdisj.symm
  have hdec : CondIndep p B W S := condIndep_decomp h.symm hBA
  have h2 : CondIndep p W B S := hdec.symm
  intro x
  have eFull : A ∪ B ∪ (S ∪ W) = (A ∪ W) ∪ B ∪ S := by
    ext v
    simp only [Set.mem_union]
    tauto
  have eA : A ∪ (S ∪ W) = (A ∪ W) ∪ S := by
    ext v
    simp only [Set.mem_union]
    tauto
  have eB : B ∪ (S ∪ W) = W ∪ B ∪ S := by
    ext v
    simp only [Set.mem_union]
    tauto
  have eS : S ∪ W = W ∪ S := Set.union_comm S W
  have hα := h x
  have hβ := h2 x
  rw [eFull, eA, eB, eS]
  by_cases hz : marginal p (W ∪ S) x = 0
  · have hsub1 : W ∪ S ⊆ (A ∪ W) ∪ B ∪ S := by
      intro v hv
      simp only [Set.mem_union] at hv ⊢
      tauto
    have hsub2 : W ∪ S ⊆ (A ∪ W) ∪ S := by
      intro v hv
      simp only [Set.mem_union] at hv ⊢
      tauto
    have hF : marginal p ((A ∪ W) ∪ B ∪ S) x = 0 := by
      have hle := marginal_anti hp hsub1 x
      rw [hz] at hle
      exact le_antisymm hle (marginal_nonneg hp _ x)
    have hAW : marginal p ((A ∪ W) ∪ S) x = 0 := by
      have hle := marginal_anti hp hsub2 x
      rw [hz] at hle
      exact le_antisymm hle (marginal_nonneg hp _ x)
    rw [hF, hz, hAW]
    simp
  · have hSne : marginal p S x ≠ 0 := by
      intro h0
      have hle := marginal_anti hp (Set.subset_union_right : S ⊆ W ∪ S) x
      rw [h0] at hle
      exact hz (le_antisymm hle (marginal_nonneg hp _ x))
    have e1 : (marginal p ((A ∪ W) ∪ B ∪ S) x * marginal p (W ∪ S) x) * marginal p S x =
        (marginal p ((A ∪ W) ∪ B ∪ S) x * marginal p S x) * marginal p (W ∪ S) x := by
      ring
    have e2 : (marginal p ((A ∪ W) ∪ S) x * marginal p (W ∪ B ∪ S) x) * marginal p S x =
        marginal p ((A ∪ W) ∪ S) x * (marginal p (W ∪ B ∪ S) x * marginal p S x) :=
      mul_assoc _ _ _
    have key : (marginal p ((A ∪ W) ∪ B ∪ S) x * marginal p (W ∪ S) x) * marginal p S x =
        (marginal p ((A ∪ W) ∪ S) x * marginal p (W ∪ B ∪ S) x) * marginal p S x := by
      rw [e1, hα, e2, hβ]
      ring
    exact mul_right_cancel₀ hSne key

end MetaMathlibExt.FiniteWeight
