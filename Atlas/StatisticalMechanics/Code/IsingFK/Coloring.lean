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

namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]






def Compatible {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : Prop :=
  ∀ x y, G.Adj x y → ω s(x, y) = true → σ x = σ y

instance instDecidableCompatible {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    Decidable (Compatible G σ ω) := by
  unfold Compatible; infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem compatible_iff_constOnOpen {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    Compatible G σ ω ↔ ConstOnOpen G ω σ :=
  ⟨fun h x y hadj => h x y hadj.1 hadj.2, fun h x y h1 h2 => h x y ⟨h1, h2⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in




theorem compatible_constant_on_cluster {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) {x y : V} (r : (openSub G ω).Reachable x y) : σ x = σ y :=
  constOnOpen_reachable G ω σ ((compatible_iff_constOnOpen G σ ω).1 h) r






def monoBool {q : ℕ} (σ : V → Fin q) : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y => decide (σ x = σ y), by
    intro a b
    simp only [decide_eq_decide]
    exact ⟨Eq.symm, Eq.symm⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem monoBool_mk {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoBool σ s(x, y) = decide (σ x = σ y) := by
  unfold monoBool; rw [Sym2.lift_mk]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem monoBool_iff {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoBool σ s(x, y) = true ↔ σ x = σ y := by
  rw [monoBool_mk, decide_eq_true_eq]



def disagreeEdges {q : ℕ} (σ : V → Fin q) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ¬ monoBool σ e)

omit [DecidableEq V] in

theorem mem_disagreeEdges {q : ℕ} (σ : V → Fin q) (x y : V) :
    s(x, y) ∈ disagreeEdges G σ ↔ G.Adj x y ∧ σ x ≠ σ y := by
  unfold disagreeEdges
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Bool.not_eq_true, ← Bool.not_eq_true, monoBool_iff]

omit [DecidableEq V] in



theorem compatible_closed_on_disagree {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) {e : Sym2 V} (he : e ∈ disagreeEdges G σ) : ω e = false := by
  induction e with
  | _ x y =>
    rw [mem_disagreeEdges] at he
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact he.2 (h x y he.1 hopen)








def coloring {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) : V → Fin q :=
  fun v => τ ((openSub G ω).connectedComponentMk v)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

@[simp]
theorem coloring_apply {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) (x : V) :
    coloring G ω τ x = τ ((openSub G ω).connectedComponentMk x) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem coloring_compatible {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) :
    Compatible G (coloring G ω τ) ω := by
  rw [compatible_iff_constOnOpen]
  intro x y hxy
  simp only [coloring_apply]
  congr 1
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem coloring_eq_constOnOpenEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) :
    coloring G ω τ = (constOnOpenEquiv G ω τ).1 := rfl





theorem card_compatible {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    Nat.card {σ : V → Fin q // Compatible G σ ω} = q ^ numClusters G ω := by
  have hcongr : Nat.card {σ : V → Fin q // Compatible G σ ω}
      = Nat.card {σ : V → Fin q // ConstOnOpen G ω σ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun σ => compatible_iff_constOnOpen G σ ω)
  rw [hcongr, card_constOnOpen]



omit [DecidableEq V] in

def openCount (ω : ConfigSpace (Sym2 V)) : ℕ :=
  (G.edgeFinset.filter (fun e => ω e = true)).card


def closedCount (ω : ConfigSpace (Sym2 V)) : ℕ :=
  (G.edgeFinset.filter (fun e => ω e = false)).card

omit [DecidableEq V] in


theorem edgeProduct_eq_pow (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p ω = p ^ openCount G ω * (1 - p) ^ closedCount G ω := by
  unfold edgeProduct openCount closedCount
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset (fun e => ω e = true)]
  congr 1
  · rw [Finset.prod_congr rfl (fun e he => if_pos (Finset.mem_filter.1 he).2),
      Finset.prod_const]
  · have hfilt : G.edgeFinset.filter (fun e => ¬ ω e = true)
        = G.edgeFinset.filter (fun e => ω e = false) := by
      apply Finset.filter_congr; intro e _; simp [Bool.not_eq_true]
    rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.1 he).2),
      Finset.prod_const, hfilt]

omit [DecidableEq V] in





theorem esWeight_eq_of_compatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = if Compatible G σ ω then edgeProduct G p ω else 0 := by
  rw [esWeight_factor, monoProd_eq_indicator]
  simp only [compatible_iff_constOnOpen]
  split <;> ring



noncomputable def esJointProb (q : ℕ) (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  esWeight G p σ ω / esZ G q p



theorem esJointProb_incompatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : ¬ Compatible G σ ω) : esJointProb G q p σ ω = 0 := by
  unfold esJointProb
  rw [esWeight_eq_of_compatible, if_neg h, zero_div]






theorem esJointProb_compatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) :
    esJointProb G q p σ ω
      = (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ) := by
  unfold esJointProb
  rw [esWeight_eq_of_compatible, if_pos h, esZ_eq_fkZ, edgeProduct_eq_pow]




theorem esJointProb_eq {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esJointProb G q p σ ω
      = if Compatible G σ ω then
          (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ)
        else 0 := by
  by_cases h : Compatible G σ ω
  · rw [if_pos h, esJointProb_compatible G p σ ω h]
  · rw [if_neg h, esJointProb_incompatible G p σ ω h]

end IsingFK

end StatMech
