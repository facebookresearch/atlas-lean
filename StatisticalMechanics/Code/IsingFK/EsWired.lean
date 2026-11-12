/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.FK.EdwardsSokal
import Code.FK.MonoBC
import Code.IsingFK.Coloring
import Code.Lattice.BoundaryConditions

open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]












theorem esFree_spin_marginal (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ :=
  esFirstMarginal_eq_pottsProb G q β J σ




theorem esFree_edge_marginal (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q p ω = fkProb G p (q : ℝ) ω :=
  esSecondMarginal_eq_fkProb G q p ω






variable (bdry : V → Prop) [DecidablePred bdry]






def BoundaryFixed {q : ℕ} (b : Fin q) (σ : V → Fin q) : Prop := ∀ x, bdry x → σ x = b

instance instDecidableBoundaryFixed {q : ℕ} (b : Fin q) (σ : V → Fin q) :
    Decidable (BoundaryFixed bdry b σ) := by
  unfold BoundaryFixed; infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidablePred bdry] in


theorem boundaryFixed_const {q : ℕ} (b : Fin q) : BoundaryFixed bdry b (fun _ => b) :=
  fun _ _ => rfl



noncomputable def pottsWeightWired {q : ℕ} (b : Fin q) (β J : ℝ) (σ : V → Fin q) : ℝ :=
  if BoundaryFixed bdry b σ then Potts.pottsWeight G β J σ else 0


noncomputable def pottsZWired (q : ℕ) (b : Fin q) (β J : ℝ) : ℝ :=
  ∑ σ : V → Fin q, pottsWeightWired G bdry b β J σ



theorem pottsZWired_pos (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) :
    0 < pottsZWired G bdry q b β J := by
  unfold pottsZWired pottsWeightWired
  apply Finset.sum_pos'
  · intro σ _; split
    · exact (Potts.pottsWeight_pos G β J σ).le
    · rfl
  · exact ⟨fun _ => b, Finset.mem_univ _, by
      rw [if_pos (boundaryFixed_const bdry b)]; exact Potts.pottsWeight_pos G β J _⟩

theorem pottsZWired_ne_zero (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) :
    pottsZWired G bdry q b β J ≠ 0 :=
  (pottsZWired_pos G bdry q b β J).ne'



noncomputable def pottsProbWired (q : ℕ) (b : Fin q) (β J : ℝ) (σ : V → Fin q) : ℝ :=
  pottsWeightWired G bdry b β J σ / pottsZWired G bdry q b β J


theorem pottsProbWired_nonneg (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) (σ : V → Fin q) :
    0 ≤ pottsProbWired G bdry q b β J σ := by
  unfold pottsProbWired pottsWeightWired
  apply div_nonneg _ (pottsZWired_pos G bdry q b β J).le
  split
  · exact Potts.pottsWeight_nonneg G β J σ
  · rfl


theorem pottsProbWired_sum_eq_one (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) :
    (∑ σ : V → Fin q, pottsProbWired G bdry q b β J σ) = 1 := by
  unfold pottsProbWired
  rw [← Finset.sum_div]
  exact div_self (pottsZWired_ne_zero G bdry q b β J)






theorem pottsProbWired_eq_conditional {q : ℕ} [NeZero q] (b : Fin q) (β J : ℝ) (σ : V → Fin q) :
    pottsProbWired G bdry q b β J σ
      = if BoundaryFixed bdry b σ then
          Potts.pottsProb G q β J σ /
            (∑ τ : V → Fin q,
              if BoundaryFixed bdry b τ then Potts.pottsProb G q β J τ else 0)
        else 0 := by
  unfold pottsProbWired pottsWeightWired pottsZWired pottsWeightWired Potts.pottsProb
  have hZpos : 0 < Potts.pottsZ G q β J := Potts.pottsZ_pos G q β J
  have hden : (∑ τ : V → Fin q,
        if BoundaryFixed bdry b τ then Potts.pottsWeight G β J τ / Potts.pottsZ G q β J else 0)
      = (∑ τ : V → Fin q, if BoundaryFixed bdry b τ then Potts.pottsWeight G β J τ else 0)
          / Potts.pottsZ G q β J := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro τ _; split <;> simp
  rw [hden]
  by_cases h : BoundaryFixed bdry b σ
  · rw [if_pos h, if_pos h, div_div_div_cancel_right₀]
    exact hZpos.ne'
  · rw [if_neg h, if_neg h, zero_div]









noncomputable def esWeightWired {q : ℕ} (b : Fin q) (p : ℝ) (σ : V → Fin q)
    (ω : ConfigSpace (Sym2 V)) : ℝ :=
  if BoundaryFixed bdry b σ then esWeight G p σ ω else 0

omit [DecidableEq V] in

theorem esWeightWired_nonneg {q : ℕ} {b : Fin q} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : 0 ≤ esWeightWired G bdry b p σ ω := by
  unfold esWeightWired
  split
  · exact esWeight_nonneg G hp hp1 σ ω
  · rfl






theorem esWeightWired_sum_omega {q : ℕ} (b : Fin q) (β J : ℝ) (σ : V → Fin q) :
    (∑ ω : ConfigSpace (Sym2 V), esWeightWired G bdry b (1 - Real.exp (-(β * J))) σ ω)
      = esFirstConst G β J * pottsWeightWired G bdry b β J σ := by
  unfold esWeightWired pottsWeightWired
  by_cases h : BoundaryFixed bdry b σ
  · simp only [if_pos h]
    rw [esWeight_sum_eq_pottsWeight]
  · simp only [if_neg h, Finset.sum_const_zero, mul_zero]


noncomputable def esZWired (q : ℕ) (b : Fin q) (p : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin q, esWeightWired G bdry b p σ ω


theorem esZWired_eq_pottsZWired {q : ℕ} [NeZero q] (b : Fin q) (β J : ℝ) :
    esZWired G bdry q b (1 - Real.exp (-(β * J)))
      = esFirstConst G β J * pottsZWired G bdry q b β J := by
  unfold esZWired pottsZWired
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => esWeightWired_sum_omega G bdry b β J σ



noncomputable def esWiredFirstMarginal (q : ℕ) (b : Fin q) (p : ℝ) (σ : V → Fin q) : ℝ :=
  (∑ ω : ConfigSpace (Sym2 V), esWeightWired G bdry b p σ ω) / esZWired G bdry q b p






theorem esWiredFirstMarginal_eq_pottsProbWired {q : ℕ} [NeZero q] (b : Fin q) (β J : ℝ)
    (σ : V → Fin q) :
    esWiredFirstMarginal G bdry q b (1 - Real.exp (-(β * J))) σ
      = pottsProbWired G bdry q b β J σ := by
  unfold esWiredFirstMarginal pottsProbWired
  rw [esWeightWired_sum_omega, esZWired_eq_pottsZWired,
    mul_div_mul_left _ _ (esFirstConst_pos G β J).ne']













noncomputable def wiredSub (ω : ConfigSpace (Sym2 V)) : SimpleGraph V :=
  openSub G ω ⊔ boundaryCliqueGraph bdry

instance instDecidableRelWiredSub (ω : ConfigSpace (Sym2 V)) :
    DecidableRel (wiredSub G bdry ω).Adj := by
  unfold wiredSub; infer_instance



def ConstOnWired {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q) : Prop :=
  ∀ x y, (wiredSub G bdry ω).Adj x y → σ x = σ y

instance instDecidableConstOnWired {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q) :
    Decidable (ConstOnWired G bdry ω σ) := by
  unfold ConstOnWired; infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidablePred bdry] in


theorem constOnWired_reachable {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q)
    (h : ConstOnWired G bdry ω σ) {x y : V} (r : (wiredSub G bdry ω).Reachable x y) :
    σ x = σ y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at r
  induction r with
  | refl => rfl
  | tail _ hab ih => rw [ih]; exact h _ _ hab

omit [DecidableRel G.Adj] in





theorem constOnOpen_boundaryFixed_iff {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (σ : V → Fin q) :
    (ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)
      ↔ (ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ) := by
  constructor
  · rintro ⟨hopen, hbf⟩
    refine ⟨?_, hbf⟩
    intro x y hxy
    rw [wiredSub, SimpleGraph.sup_adj] at hxy
    rcases hxy with hxy | hxy
    · exact hopen x y hxy
    · rw [boundaryCliqueGraph_adj] at hxy
      rw [hbf x hxy.2.1, hbf y hxy.2.2]
  · rintro ⟨hwired, hbf⟩
    refine ⟨?_, hbf⟩
    intro x y hxy
    exact hwired x y (by rw [wiredSub, SimpleGraph.sup_adj]; exact Or.inl hxy)




noncomputable def constOnWiredEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    ((wiredSub G bdry ω).ConnectedComponent → Fin q)
      ≃ {σ : V → Fin q // ConstOnWired G bdry ω σ} where
  toFun τ := ⟨fun v => τ ((wiredSub G bdry ω).connectedComponentMk v), by
    intro x y hxy
    simp only
    congr 1
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy⟩
  invFun σ := SimpleGraph.ConnectedComponent.lift σ.1 (by
    intro v w p _
    exact constOnWired_reachable G bdry ω σ.1 σ.2 p.reachable)
  left_inv τ := by
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl
  right_inv σ := by
    apply Subtype.ext
    funext v
    rfl

omit [DecidableRel G.Adj] in


theorem wiredSub_componentMk_eq_of_bdry {ω : ConfigSpace (Sym2 V)} {x y : V}
    (hx : bdry x) (hy : bdry y) :
    (wiredSub G bdry ω).connectedComponentMk x
      = (wiredSub G bdry ω).connectedComponentMk y := by
  by_cases h : x = y
  · rw [h]
  · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    rw [wiredSub, SimpleGraph.sup_adj]; right
    rw [boundaryCliqueGraph_adj]; exact ⟨h, hx, hy⟩




def pinnedFunEquiv {α : Type*} [DecidableEq α] {q : ℕ} (c₀ : α) (b : Fin q) :
    {τ : α → Fin q // τ c₀ = b} ≃ ({c : α // c ≠ c₀} → Fin q) where
  toFun τ := fun c => τ.1 c.1
  invFun g := ⟨fun a => if h : a = c₀ then b else g ⟨a, h⟩, by simp⟩
  left_inv := by
    rintro ⟨τ, hτ⟩
    apply Subtype.ext; funext a
    by_cases h : a = c₀
    · simp [h, hτ]
    · simp [h]
  right_inv := by
    intro g; funext c
    obtain ⟨a, ha⟩ := c
    simp [ha]






theorem card_constOnOpen_boundaryFixed {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ}
      = q ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) := by
  classical
  have hcongr :
      Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ}
        = Nat.card {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ} :=
    Nat.card_congr
      (Equiv.subtypeEquivRight fun σ => constOnOpen_boundaryFixed_iff G bdry b ω σ)
  rw [hcongr]
  set W := wiredSub G bdry ω with hW
  set c₀ := W.connectedComponentMk v₀ with hc₀
  
  have key : {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ}
      ≃ {τ : W.ConnectedComponent → Fin q // τ c₀ = b} := by
    refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
    refine ((constOnWiredEquiv G bdry ω).subtypeEquiv ?_).symm
    intro τ
    show (τ c₀ = b ↔ BoundaryFixed bdry b ((constOnWiredEquiv G bdry ω) τ).1)
    constructor
    · intro h x hx
      show τ (W.connectedComponentMk x) = b
      rw [wiredSub_componentMk_eq_of_bdry G bdry hx hv₀]
      exact h
    · intro h
      have := h v₀ hv₀
      simpa [constOnWiredEquiv, hc₀] using this
  have hk : numClustersBC G (boundaryCliqueGraph bdry) ω = Fintype.card W.ConnectedComponent := by
    rw [numClustersBC]
    exact Nat.card_eq_fintype_card
  rw [Nat.card_congr key, Nat.card_congr (pinnedFunEquiv c₀ b),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hk]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]




theorem esWeightWired_sum_spins {q : ℕ} (b : Fin q) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω)
      = edgeProduct G p ω
        * (Finset.univ.filter
            (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)).card := by
  classical
  have hpt : ∀ σ : V → Fin q, esWeightWired G bdry b p σ ω
      = if (ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ) then edgeProduct G p ω else 0 := by
    intro σ
    unfold esWeightWired
    rw [esWeight_eq_of_compatible]
    simp only [compatible_iff_constOnOpen]
    by_cases hb : BoundaryFixed bdry b σ <;> by_cases hc : ConstOnOpen G ω σ <;>
      simp [hb, hc]
  rw [Finset.sum_congr rfl (fun σ _ => hpt σ), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_comm]





theorem esWeightWired_sum_spins_eq_bcWeight {q : ℕ} (b : Fin q) (p : ℝ)
    (ω : ConfigSpace (Sym2 V)) (v₀ : V) (hv₀ : bdry v₀) (hq : 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
    (q : ℝ) * (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω)
      = bcWeight G (boundaryCliqueGraph bdry) p (q : ℝ) ω := by
  classical
  rw [esWeightWired_sum_spins]
  have hcard :
      ((Finset.univ.filter
          (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)).card : ℝ)
        = (q : ℝ) ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) := by
    have hN : (Finset.univ.filter
          (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)).card
        = q ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) := by
      rw [← card_constOnOpen_boundaryFixed G bdry b ω v₀ hv₀,
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hN]; push_cast; rfl
  rw [hcard, bcWeight]
  
  set k := numClustersBC G (boundaryCliqueGraph bdry) ω with hk
  have hpow : (q : ℝ) * (q : ℝ) ^ (k - 1) = (q : ℝ) ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  calc (q : ℝ) * (edgeProduct G p ω * (q : ℝ) ^ (k - 1))
      = edgeProduct G p ω * ((q : ℝ) * (q : ℝ) ^ (k - 1)) := by ring
    _ = edgeProduct G p ω * (q : ℝ) ^ k := by rw [hpow]



noncomputable def esWiredSecondMarginal (q : ℕ) (b : Fin q) (p : ℝ)
    (ω : ConfigSpace (Sym2 V)) : ℝ :=
  (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω) / esZWired G bdry q b p




theorem esZWired_eq_bcZ {q : ℕ} (b : Fin q) (p : ℝ) (v₀ : V) (hv₀ : bdry v₀)
    (hq : ∀ ω : ConfigSpace (Sym2 V), 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
    (q : ℝ) * esZWired G bdry q b p = bcZ G (boundaryCliqueGraph bdry) p (q : ℝ) := by
  unfold esZWired bcZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact esWeightWired_sum_spins_eq_bcWeight G bdry b p ω v₀ hv₀ (hq ω)






theorem esWiredSecondMarginal_eq_bcProb {q : ℕ} (b : Fin q) (p : ℝ) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀) (hqpos : 0 < q)
    (hq : ∀ ω : ConfigSpace (Sym2 V), 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
    esWiredSecondMarginal G bdry q b p ω = bcProb G (boundaryCliqueGraph bdry) p (q : ℝ) ω := by
  unfold esWiredSecondMarginal bcProb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  
  rw [show bcWeight G (boundaryCliqueGraph bdry) p (q : ℝ) ω
        = (q : ℝ) * (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω) from
      (esWeightWired_sum_spins_eq_bcWeight G bdry b p ω v₀ hv₀ (hq ω)).symm,
    show bcZ G (boundaryCliqueGraph bdry) p (q : ℝ) = (q : ℝ) * esZWired G bdry q b p from
      (esZWired_eq_bcZ G bdry b p v₀ hv₀ hq).symm,
    mul_div_mul_left _ _ hqR.ne']

end IsingFK

end StatMech
