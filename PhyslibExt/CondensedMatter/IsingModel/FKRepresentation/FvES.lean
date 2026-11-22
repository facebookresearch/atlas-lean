/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsLatticeBridge
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsWired
public import PhyslibExt.StatisticalMechanics.RandomCluster.EsCorrelations

/-!
# The wired Edwards–Sokal one-point function

With boundary spins `+`, the Ising one-point function `⟨σ_x⟩` equals the probability, under the
wired random-cluster measure with `q = 2`, that `x` is connected to the boundary.

## i. Overview

In the wired Edwards–Sokal coupling with boundary color `0` (spin `+1`), sum the spin at `x` over
the compatible colorings of a fixed bond configuration `ω`. Such colorings are colorings of the
clusters of `wiredSub`, with the boundary cluster pinned. If `x` is in the boundary cluster its
spin is `+1` for each of the `2^{k - 1}` colorings; otherwise the two colors of its cluster
cancel. Dividing by the partition function gives `⟨σ_x⟩⁺ = φ^w(x ↔ ∂)`.

## ii. Key results

- `ConnToBdry` : `x` is connected by open edges to a boundary vertex.
- `colour_spin_sum` : the spin sum over compatible colorings is `2^{k-1}` or `0`.
- `esWiredOnePoint` : the wired Edwards–Sokal one-point function.
- `esWiredOnePoint_eq_wiredConnToBdryProb` : `⟨σ_x⟩⁺ = φ^w(x ↔ ∂)`.

## iii. Table of contents

- A. Counting pinned colorings
- B. Connection to the boundary
- C. Spin sums over compatible colorings
- D. The one-point function

## iv. References

- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model I. Introduction and relation to
  other models*, Physica 57 (1972) 536–564.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988) 2009–2012.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 1.4.
-/

@[expose] public section

open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-! ## A. Counting pinned colorings -/

lemma sum_eval_factor {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (a₀ : A) (F : B → ℝ) :
    (∑ g : A → B, F (g a₀))
      = (Fintype.card ({a : A // a ≠ a₀} → B)) • (∑ b : B, F b) := by
  classical
  let e : (A → B) ≃ (B × ({a : A // a ≠ a₀} → B)) :=
  { toFun := fun g => (g a₀, fun a => g a.1)
    invFun := fun p => fun a => if h : a = a₀ then p.1 else p.2 ⟨a, h⟩
    left_inv := by intro g; funext a; by_cases h : a = a₀ <;> simp [h]
    right_inv := by rintro ⟨b, h⟩; ext
                    · simp
                    · simp only; rename_i a; rw [dite_eq_right a.2] }
  have hcomp : (∑ g : A → B, F (g a₀)) = ∑ p : B × ({a : A // a ≠ a₀} → B), F p.1 := by
    rw [← e.sum_comp (fun p => F p.1)]; rfl
  rw [hcomp, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- Colorings constant on wired clusters with boundary color `b` correspond to colorings of the
clusters of `wiredSub` with the boundary cluster colored `b`. -/
noncomputable def wiredColourEquiv {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀) :
    {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ}
      ≃ {τ : (wiredSub G bdry ω).ConnectedComponent → Fin q //
            τ ((wiredSub G bdry ω).connectedComponentMk v₀) = b} := by
  refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
  refine ((constOnWiredEquiv G bdry ω).subtypeEquiv ?_).symm
  intro τ
  change (τ ((wiredSub G bdry ω).connectedComponentMk v₀) = b
        ↔ BoundaryFixed bdry b ((constOnWiredEquiv G bdry ω) τ).1)
  constructor
  · intro h x hx
    change τ ((wiredSub G bdry ω).connectedComponentMk x) = b
    rw [wiredSub_componentMk_eq_of_bdry G bdry hx hv₀]; exact h
  · intro h; have := h v₀ hv₀; simpa [constOnWiredEquiv] using this

omit [DecidableRel G.Adj] [DecidableEq V] [DecidablePred bdry] in
lemma wiredColourEquiv_apply_val {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀)
    (σ : {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ}) (x : V) :
    (wiredColourEquiv G bdry b ω v₀ hv₀ σ).1 ((wiredSub G bdry ω).connectedComponentMk x)
      = σ.1 x := rfl

lemma sum_isingSpin : (∑ b : Fin 2, isingSpin b) = 0 := by
  simp [Fin.sum_univ_two, isingSpin]

/-! ## B. Connection to the boundary -/

/-- The vertex `x` is joined by an open path of `ω` to a boundary vertex. -/
def ConnToBdry (ω : ConfigSpace (Sym2 V)) (x : V) : Prop :=
  ∃ y, bdry y ∧ Connected G ω x y

/-- Connection to the boundary is decidable. -/
instance instDecidableConnToBdry (ω : ConfigSpace (Sym2 V)) (x : V) :
    Decidable (ConnToBdry G bdry ω x) :=
  Fintype.decidableExistsFintype

omit [DecidableRel G.Adj] [DecidableEq V] [DecidablePred bdry] in
lemma connToBdry_iff_componentMk_eq (v₀ : V) (hv₀ : bdry v₀)
    (ω : ConfigSpace (Sym2 V)) (x : V) :
    ConnToBdry G bdry ω x ↔
      (wiredSub G bdry ω).connectedComponentMk x
        = (wiredSub G bdry ω).connectedComponentMk v₀ := by
  classical
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h1 : (wiredSub G bdry ω).connectedComponentMk x
        = (wiredSub G bdry ω).connectedComponentMk y := by
      apply SimpleGraph.ConnectedComponent.sound
      have hle : openSub G ω ≤ wiredSub G bdry ω := by rw [wiredSub]; exact le_sup_left
      exact (hxy.mono hle)
    rw [h1]; exact wiredSub_componentMk_eq_of_bdry G bdry hy hv₀
  · intro h
    have hreach : (wiredSub G bdry ω).Reachable x v₀ :=
      SimpleGraph.ConnectedComponent.exact h
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    have key : ∀ z, Relation.ReflTransGen (wiredSub G bdry ω).Adj x z →
        (ConnToBdry G bdry ω x ∨ Connected G ω x z) := by
      intro z hz
      induction hz with
      | refl => exact Or.inr (SimpleGraph.Reachable.refl x)
      | @tail b c hxb hbc ih =>
        rcases ih with hdone | hxb'
        · exact Or.inl hdone
        · rw [wiredSub, SimpleGraph.sup_adj] at hbc
          rcases hbc with hopen | hclique
          · exact Or.inr (hxb'.trans (SimpleGraph.Adj.reachable hopen))
          · rw [boundaryCliqueGraph_adj] at hclique
            exact Or.inl ⟨b, hclique.2.1, hxb'⟩
    rcases key v₀ hreach with hdone | hxv₀
    · exact hdone
    · exact ⟨v₀, hv₀, hxv₀⟩

/-! ## C. Spin sums over compatible colorings -/

lemma card_pinned {C : Type*} [Fintype C] [DecidableEq C] {q : ℕ} (c₀ : C) (b : Fin q) :
    Fintype.card {τ : C → Fin q // τ c₀ = b} = q ^ (Fintype.card C - 1) := by
  rw [Fintype.card_congr (pinnedFunEquiv c₀ b), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

lemma sum_pinned_eq_filter {C : Type*} [Fintype C] [DecidableEq C]
    (c₀ : C) (F : (C → Fin 2) → ℝ) :
    (∑ τ : {τ : C → Fin 2 // τ c₀ = 0}, F τ.1)
      = ∑ τ ∈ Finset.univ.filter (fun τ : C → Fin 2 => τ c₀ = 0), F τ :=
  (Finset.sum_subtype (Finset.univ.filter (fun τ : C → Fin 2 => τ c₀ = 0))
    (fun τ => by simp) F).symm

lemma colour_spin_cancel {C : Type*} [Fintype C] [DecidableEq C]
    (c₀ cx : C) (h : cx ≠ c₀) :
    (∑ τ ∈ Finset.univ.filter (fun τ : C → Fin 2 => τ c₀ = 0), isingSpin (τ cx)) = 0 := by
  classical
  rw [← sum_pinned_eq_filter c₀ (fun τ => isingSpin (τ cx))]
  rw [← (pinnedFunEquiv c₀ (0 : Fin 2)).symm.sum_comp
        (fun τ : {τ : C → Fin 2 // τ c₀ = 0} => isingSpin (τ.1 cx))]
  have hval : ∀ g : {c : C // c ≠ c₀} → Fin 2,
      (fun τ : {τ : C → Fin 2 // τ c₀ = 0} => isingSpin (τ.1 cx))
        ((pinnedFunEquiv c₀ (0 : Fin 2)).symm g) = isingSpin (g ⟨cx, h⟩) := by
    intro g
    change isingSpin (((pinnedFunEquiv c₀ (0 : Fin 2)).symm g).1 cx) = isingSpin (g ⟨cx, h⟩)
    congr 1
    change (if hh : cx = c₀ then (0 : Fin 2) else g ⟨cx, hh⟩) = g ⟨cx, h⟩
    rw [dite_eq_right h]
  rw [Finset.sum_congr rfl (fun g _ => hval g)]
  rw [sum_eval_factor (⟨cx, h⟩ : {c : C // c ≠ c₀}) isingSpin, sum_isingSpin, smul_zero]

lemma colour_spin_const {C : Type*} [Fintype C] [DecidableEq C]
    (c₀ cx : C) (h : cx = c₀) :
    (∑ τ ∈ Finset.univ.filter (fun τ : C → Fin 2 => τ c₀ = 0), isingSpin (τ cx))
      = (2 : ℝ) ^ (Fintype.card C - 1) := by
  classical
  rw [← sum_pinned_eq_filter c₀ (fun τ => isingSpin (τ cx))]
  have hone : ∀ τ : {τ : C → Fin 2 // τ c₀ = 0}, isingSpin (τ.1 cx) = 1 := by
    intro τ; rw [h, τ.2]; rfl
  rw [Finset.sum_congr rfl (fun τ _ => hone τ), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, card_pinned c₀ (0 : Fin 2)]
  push_cast; ring

lemma colour_spin_sum (ω : ConfigSpace (Sym2 V)) (v₀ : V) (hv₀ : bdry v₀) (x : V) :
    (∑ σ ∈ Finset.univ.filter
        (fun σ : V → Fin 2 => ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry 0 σ),
          isingSpin (σ x))
      = if ConnToBdry G bdry ω x then
          (2 : ℝ) ^ (Fintype.card (wiredSub G bdry ω).ConnectedComponent - 1)
        else 0 := by
  classical
  have hreindex :
      (∑ σ ∈ Finset.univ.filter
          (fun σ : V → Fin 2 => ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry 0 σ),
            isingSpin (σ x))
        = ∑ τ ∈ Finset.univ.filter
          (fun τ : (wiredSub G bdry ω).ConnectedComponent → Fin 2 =>
            τ ((wiredSub G bdry ω).connectedComponentMk v₀) = 0),
            isingSpin (τ ((wiredSub G bdry ω).connectedComponentMk x)) := by
    rw [Finset.sum_subtype (p := fun σ : V → Fin 2 =>
          ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry 0 σ)
        (Finset.univ.filter
          (fun σ : V → Fin 2 => ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry 0 σ))
        (fun σ => by simp) (fun σ => isingSpin (σ x))]
    rw [Finset.sum_subtype (p := fun τ : (wiredSub G bdry ω).ConnectedComponent → Fin 2 =>
          τ ((wiredSub G bdry ω).connectedComponentMk v₀) = 0)
        (Finset.univ.filter
          (fun τ : (wiredSub G bdry ω).ConnectedComponent → Fin 2 =>
            τ ((wiredSub G bdry ω).connectedComponentMk v₀) = 0))
        (fun τ => by simp)
        (fun τ => isingSpin (τ ((wiredSub G bdry ω).connectedComponentMk x)))]
    rw [← (wiredColourEquiv G bdry (0 : Fin 2) ω v₀ hv₀).sum_comp
        (fun τ => isingSpin (τ.1 ((wiredSub G bdry ω).connectedComponentMk x)))]
    apply Finset.sum_congr rfl
    intro σ _
    rw [wiredColourEquiv_apply_val]
  rw [hreindex]
  have hiff : ConnToBdry G bdry ω x ↔
      (wiredSub G bdry ω).connectedComponentMk x
        = (wiredSub G bdry ω).connectedComponentMk v₀ :=
    connToBdry_iff_componentMk_eq G bdry v₀ hv₀ ω x
  by_cases h : (wiredSub G bdry ω).connectedComponentMk x
      = (wiredSub G bdry ω).connectedComponentMk v₀
  · rw [ite_eq_left (hiff.mpr h)]
    exact colour_spin_const _ _ h
  · rw [ite_eq_right (fun hc => h (hiff.mp hc))]
    exact colour_spin_cancel _ _ h

lemma numClustersBC_eq_card_wiredSub (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G (boundaryCliqueGraph bdry) ω
      = Fintype.card (wiredSub G bdry ω).ConnectedComponent := by
  rw [numClustersBC]; exact Nat.card_eq_fintype_card

lemma esWeightWired_spin_sum (p : ℝ) (ω : ConfigSpace (Sym2 V)) (v₀ : V) (hv₀ : bdry v₀)
    (x : V) :
    (∑ σ : V → Fin 2, esWeightWired G bdry (0 : Fin 2) p σ ω * isingSpin (σ x))
      = edgeProduct G p ω
        * (if ConnToBdry G bdry ω x then
            (2 : ℝ) ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) else 0) := by
  classical
  have hpt : ∀ σ : V → Fin 2,
      esWeightWired G bdry (0 : Fin 2) p σ ω * isingSpin (σ x)
        = (if ConstOnOpen G ω σ ∧ BoundaryFixed bdry 0 σ then edgeProduct G p ω else 0)
            * isingSpin (σ x) := by
    intro σ
    unfold esWeightWired
    rw [esWeight_eq_of_compatible]
    simp only [compatible_iff_constOnOpen]
    by_cases hb : BoundaryFixed bdry (0 : Fin 2) σ <;>
      by_cases hc : ConstOnOpen G ω σ <;> simp [hb, hc]
  rw [Finset.sum_congr rfl (fun σ _ => hpt σ)]
  rw [Finset.sum_congr rfl (fun σ _ => by rw [ite_mul, zero_mul])]
  rw [← Finset.sum_filter]
  rw [Finset.sum_congr (Finset.filter_congr (fun σ _ =>
        by rw [constOnOpen_boundaryFixed_iff])) (fun σ _ => rfl)]
  rw [← Finset.mul_sum]
  rw [colour_spin_sum G bdry ω v₀ hv₀ x]
  rw [numClustersBC_eq_card_wiredSub]

omit [DecidableRel G.Adj] in
lemma one_le_numClustersBC (v₀ : V) (ω : ConfigSpace (Sym2 V)) :
    1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω := by
  classical
  rw [numClustersBC_eq_card_wiredSub, Nat.one_le_iff_ne_zero, Ne, Fintype.card_eq_zero_iff]
  intro hempty
  exact hempty.false ((wiredSub G bdry ω).connectedComponentMk v₀)

lemma edgeProduct_pow_eq_bcWeight_half (p : ℝ) (ω : ConfigSpace (Sym2 V)) (v₀ : V) :
    (2 : ℝ) * (edgeProduct G p ω
        * (2 : ℝ) ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1))
      = bcWeight G (boundaryCliqueGraph bdry) p (2 : ℝ) ω := by
  rw [bcWeight]
  set k := numClustersBC G (boundaryCliqueGraph bdry) ω with hk
  have hk1 : 1 ≤ k := one_le_numClustersBC G bdry v₀ ω
  have hpow : (2 : ℝ) * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k := by
    rw [← pow_succ']; congr 1; omega
  calc (2 : ℝ) * (edgeProduct G p ω * (2 : ℝ) ^ (k - 1))
      = edgeProduct G p ω * ((2 : ℝ) * (2 : ℝ) ^ (k - 1)) := by ring
    _ = edgeProduct G p ω * (2 : ℝ) ^ k := by rw [hpow]

/-! ## D. The one-point function -/

/-- The one-point function `⟨σ_x⟩` of the wired Edwards–Sokal measure with boundary color `b` and `q
= 2`. -/
noncomputable def esWiredOnePoint (b : Fin 2) (p : ℝ) (x : V) : ℝ :=
  (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin 2,
      esWeightWired G bdry b p σ ω * isingSpin (σ x)) / esZWired G bdry 2 b p

/-- The probability `φ^w(x ↔ ∂)` that `x` is connected to the boundary under the wired
random-cluster measure with `q = 2`. -/
noncomputable def wiredConnToBdryProb (p : ℝ) (x : V) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
    bcProb G (boundaryCliqueGraph bdry) p (2 : ℝ) ω

/-- **Edwards–Sokal one-point identity.** With `+` boundary condition, the Ising magnetization at
`x` equals the probability that `x` is connected to the boundary in the wired FK measure with `q
= 2` (Edwards and Sokal, Phys. Rev. D 38 (1988); Grimmett, *The Random-Cluster Model*, Theorem
1.16). -/
theorem esWiredOnePoint_eq_wiredConnToBdryProb (p : ℝ) (x : V) (v₀ : V) (hv₀ : bdry v₀) :
    esWiredOnePoint G bdry (0 : Fin 2) p x = wiredConnToBdryProb G bdry p x := by
  classical
  unfold esWiredOnePoint wiredConnToBdryProb
  have hnum : (2 : ℝ) * (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin 2,
        esWeightWired G bdry (0 : Fin 2) p σ ω * isingSpin (σ x))
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
          bcWeight G (boundaryCliqueGraph bdry) p (2 : ℝ) ω := by
    rw [Finset.mul_sum]
    have hterm : ∀ ω : ConfigSpace (Sym2 V),
        (2 : ℝ) * (∑ σ : V → Fin 2, esWeightWired G bdry (0 : Fin 2) p σ ω * isingSpin (σ x))
          = if ConnToBdry G bdry ω x then bcWeight G (boundaryCliqueGraph bdry) p (2:ℝ) ω
            else 0 := by
      intro ω
      rw [esWeightWired_spin_sum G bdry p ω v₀ hv₀ x]
      by_cases h : ConnToBdry G bdry ω x
      · rw [ite_eq_left h, ite_eq_left h, edgeProduct_pow_eq_bcWeight_half G bdry p ω v₀]
      · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun ω _ => hterm ω)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x)]
    have h0 : (∑ ω ∈ Finset.univ.filter
          (fun ω : ConfigSpace (Sym2 V) => ¬ ConnToBdry G bdry ω x),
          (if ConnToBdry G bdry ω x then bcWeight G (boundaryCliqueGraph bdry) p (2:ℝ) ω
            else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      rw [ite_eq_right (Finset.mem_filter.1 hω).2]
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [ite_eq_left (Finset.mem_filter.1 hω).2]
  have hden : (2 : ℝ) * esZWired G bdry 2 (0 : Fin 2) p
      = bcZ G (boundaryCliqueGraph bdry) p (2 : ℝ) :=
    esZWired_eq_bcZ G bdry (0 : Fin 2) p v₀ hv₀ (fun ω => one_le_numClustersBC G bdry v₀ ω)
  rw [show ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
        bcProb G (boundaryCliqueGraph bdry) p (2 : ℝ) ω
      = (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
          bcWeight G (boundaryCliqueGraph bdry) p (2 : ℝ) ω)
          / bcZ G (boundaryCliqueGraph bdry) p (2 : ℝ) from by
        unfold bcProb; rw [Finset.sum_div]]
  rw [← hnum, ← hden, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

lemma wiredConnToBdryProb_eq_wiredFkProb_sum (p : ℝ) (x : V) :
    wiredConnToBdryProb G bdry p x
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
          wiredFkProb G bdry p (2 : ℝ) ω := by
  unfold wiredConnToBdryProb
  exact Finset.sum_congr rfl (fun ω _ => (wiredFkProb_eq_bcProb G bdry p (2 : ℝ) ω).symm)

end IsingFK

end StatMech
