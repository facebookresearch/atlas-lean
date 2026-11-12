/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.FK.EdwardsSokal
import Code.FK.RandomCluster

open scoped BigOperators

set_option linter.style.show false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]






def isingSpin : Fin 2 → ℝ := fun a => if a = 0 then 1 else -1



theorem isingSpin_mul (a b : Fin 2) :
    isingSpin a * isingSpin b = 2 * (if a = b then 1 else 0) - 1 := by
  fin_cases a <;> fin_cases b <;> norm_num [isingSpin]






def Connected (ω : ConfigSpace (Sym2 V)) (x y : V) : Prop :=
  (openSub G ω).Reachable x y

instance instDecidableConnected (ω : ConfigSpace (Sym2 V)) (x y : V) :
    Decidable (Connected G ω x y) :=
  inferInstanceAs (Decidable ((openSub G ω).Reachable x y))

instance instDecidablePredConnected (x y : V) :
    DecidablePred (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y) :=
  fun ω => instDecidableConnected G ω x y




noncomputable def connProb (p q : ℝ) (x y : V) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
    fkProb G p q ω







noncomputable def eqFunEquiv {C : Type*} [Fintype C] [DecidableEq C] (q : ℕ) (a b : C)
    (hab : a ≠ b) :
    {f : C → Fin q // f a = f b} ≃ ({c : C // c ≠ b} → Fin q) where
  toFun f := fun c => f.1 c.1
  invFun g := ⟨fun c => if h : c = b then g ⟨a, hab⟩ else g ⟨c, h⟩, by
    show (if h : a = b then g ⟨a, hab⟩ else g ⟨a, h⟩)
        = if h : b = b then g ⟨a, hab⟩ else g ⟨b, h⟩
    rw [dif_neg hab, dif_pos rfl]⟩
  left_inv f := by
    apply Subtype.ext
    funext c
    simp only
    by_cases h : c = b
    · rw [dif_pos h, h]; exact f.2
    · rw [dif_neg h]
  right_inv g := by
    funext c
    simp only
    rw [dif_neg c.2]



theorem card_eqfun_ne {C : Type*} [Fintype C] (q : ℕ) {a b : C} (hab : a ≠ b) :
    Nat.card {f : C → Fin q // f a = f b} = q ^ (Fintype.card C - 1) := by
  classical
  rw [Nat.card_congr (eqFunEquiv q a b hab),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]



theorem card_eqfun_eq {C : Type*} [Fintype C] (q : ℕ) {a b : C} (hab : a = b) :
    Nat.card {f : C → Fin q // f a = f b} = q ^ Fintype.card C := by
  classical
  subst hab
  have h : {f : C → Fin q // f a = f a} = {f : C → Fin q // True} := by simp
  rw [h, Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]




noncomputable def constEqEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V)) (x y : V) :
    {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y} ≃
      {τ : (openSub G ω).ConnectedComponent → Fin q //
        τ ((openSub G ω).connectedComponentMk x)
          = τ ((openSub G ω).connectedComponentMk y)} := by
  refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
  exact ((constOnOpenEquiv G ω).subtypeEquiv (fun _ => Iff.rfl)).symm




theorem card_constEq_connected {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : Connected G ω x y) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y} = q ^ numClusters G ω := by
  rw [Nat.card_congr (constEqEquiv G ω x y),
    card_eqfun_eq q (SimpleGraph.ConnectedComponent.eq.2 hxy)]
  rfl




theorem card_constEq_disconnected {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : ¬ Connected G ω x y) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y}
      = q ^ (numClusters G ω - 1) := by
  have hne : (openSub G ω).connectedComponentMk x ≠ (openSub G ω).connectedComponentMk y := by
    rw [Ne, SimpleGraph.ConnectedComponent.eq]; exact hxy
  rw [Nat.card_congr (constEqEquiv G ω x y), card_eqfun_ne q hne]
  rfl



theorem one_le_numClusters (ω : ConfigSpace (Sym2 V)) (x : V) : 1 ≤ numClusters G ω := by
  unfold numClusters
  rw [Nat.one_le_iff_ne_zero, Ne, Fintype.card_eq_zero_iff]
  intro h
  exact h.false ((openSub G ω).connectedComponentMk x)





theorem card_const_two (ω : ConfigSpace (Sym2 V)) :
    ((Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ)).card : ℝ)
      = 2 ^ numClusters G ω := by
  have h := card_constOnOpen (q := 2) G ω
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  rw [h]; push_cast; ring




theorem esWeight_spinsum_factor (p : ℝ) (ω : ConfigSpace (Sym2 V)) (g : (V → Fin 2) → ℝ) :
    (∑ σ : V → Fin 2, esWeight G p σ ω * g σ)
      = edgeProduct G p ω
        * ∑ σ : V → Fin 2, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [esWeight_factor, monoProd_eq_indicator]
  ring



theorem inner_spin_sum (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin 2,
        (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * (isingSpin (σ x) * isingSpin (σ y)))
      = 2 * (Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ ∧ σ x = σ y)).card
        - (Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ)).card := by
  have hpt : ∀ σ : V → Fin 2,
      (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * (isingSpin (σ x) * isingSpin (σ y))
        = 2 * (if ConstOnOpen G ω σ ∧ σ x = σ y then (1 : ℝ) else 0)
          - (if ConstOnOpen G ω σ then (1 : ℝ) else 0) := by
    intro σ
    rw [isingSpin_mul]
    by_cases hc : ConstOnOpen G ω σ
    · by_cases he : σ x = σ y
      · rw [if_pos hc, if_pos he, if_pos (And.intro hc he)]; ring
      · rw [if_pos hc, if_neg he,
          if_neg (show ¬(ConstOnOpen G ω σ ∧ σ x = σ y) from fun h => he h.2)]; ring
    · rw [if_neg hc, if_neg (show ¬(ConstOnOpen G ω σ ∧ σ x = σ y) from fun h => hc h.1)]; ring
  rw [Finset.sum_congr rfl (fun σ _ => hpt σ)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole]





theorem spinProd_sum_eq (p : ℝ) (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin 2, esWeight G p σ ω * (isingSpin (σ x) * isingSpin (σ y)))
      = if Connected G ω x y then fkWeight G p (2 : ℝ) ω else 0 := by
  rw [esWeight_spinsum_factor, inner_spin_sum, card_const_two G ω]
  by_cases h : Connected G ω x y
  · rw [if_pos h]
    have hcard :
        ((Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
          = 2 ^ numClusters G ω := by
      have hc := card_constEq_connected (q := 2) G ω h
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
      rw [hc]; push_cast; ring
    rw [hcard]
    unfold fkWeight
    ring
  · rw [if_neg h]
    have hcard :
        ((Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
          = 2 ^ (numClusters G ω - 1) := by
      have hc := card_constEq_disconnected (q := 2) G ω h
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
      rw [hc]; push_cast; ring
    rw [hcard]
    
    
    have hk : 1 ≤ numClusters G ω := one_le_numClusters G ω x
    have hpow : (2 : ℝ) ^ numClusters G ω = 2 * 2 ^ (numClusters G ω - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    ring







noncomputable def esTwoPoint (p : ℝ) (x y : V) : ℝ :=
  (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin 2,
      esWeight G p σ ω * (isingSpin (σ x) * isingSpin (σ y))) / esZ G 2 p











theorem esTwoPoint_eq_connProb (p : ℝ) (x y : V) :
    esTwoPoint G p x y = connProb G p 2 x y := by
  classical
  unfold esTwoPoint connProb fkProb
  rw [Finset.sum_congr rfl (fun ω _ => spinProd_sum_eq G p ω x y)]
  rw [esZ_eq_fkZ, Nat.cast_ofNat, Finset.sum_div]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y)]
  have h0 : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
        (if Connected G ω x y then fkWeight G p (2 : ℝ) ω else 0) / fkZ G p 2) = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    rw [if_neg (Finset.mem_filter.1 hω).2, zero_div]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [if_pos (Finset.mem_filter.1 hω).2]





theorem connProb_eq_sum_fkProb (p q : ℝ) (x y : V) :
    connProb G p q x y =
      ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
        fkProb G p q ω :=
  rfl

end FK

end StatMech
