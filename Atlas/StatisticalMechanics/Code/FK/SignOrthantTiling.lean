/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.FK.BoxTiling
import Code.FK.FKInterfaceSubadd
import Code.FK.FKUniqPrimitives
import Code.Lattice.BoxSurfaceVolume

open MeasureTheory Set Filter Topology Real
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice










abbrev sot_RepSum (V : Type) : ℕ → Type
  | 0 => PEmpty
  | (k + 1) => V ⊕ sot_RepSum V k

instance sot_instFintypeRepSum (V : Type) [Fintype V] : (k : ℕ) → Fintype (sot_RepSum V k)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | (k + 1) => @instFintypeSum V (sot_RepSum V k) _ (sot_instFintypeRepSum V k)

instance sot_instDecidableEqRepSum (V : Type) [DecidableEq V] :
    (k : ℕ) → DecidableEq (sot_RepSum V k)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | (k + 1) => @instDecidableEqSum V (sot_RepSum V k) _ (sot_instDecidableEqRepSum V k)


def sot_repGraph (V : Type) [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (k : ℕ) → SimpleGraph (sot_RepSum V k)
  | 0 => (⊥ : SimpleGraph PEmpty)
  | (k + 1) => G ⊕g (sot_repGraph V G k)

@[simp] theorem sot_repGraph_succ (V : Type) [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) :
    sot_repGraph V G (k + 1) = G ⊕g (sot_repGraph V G k) := rfl

@[simp] theorem sot_repGraph_zero (V : Type) [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    sot_repGraph V G 0 = (⊥ : SimpleGraph PEmpty) := rfl

noncomputable instance sot_instDecidableRelRepGraph (V : Type) [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (k : ℕ) → DecidableRel (sot_repGraph V G k).Adj
  | 0 => by unfold sot_repGraph; infer_instance
  | (k + 1) => by unfold sot_repGraph; exact Classical.decRel _

instance sot_instIsEmptySym2PEmpty : IsEmpty (Sym2 PEmpty) := by
  constructor; intro e; exact e.recOnSubsingleton (fun x => x.elim)



theorem sot_fkZ_bot_pempty {p q : ℝ} : fkZ (⊥ : SimpleGraph PEmpty) p q = 1 := by
  unfold fkZ
  rw [Finset.sum_eq_single (fun (_ : Sym2 PEmpty) => false)]
  · unfold fkWeight edgeProduct numClusters
    rw [Finset.prod_of_isEmpty, one_mul]
    rw [show Fintype.card (openSub (⊥ : SimpleGraph PEmpty) (fun _ => false)).ConnectedComponent = 0
        from by
          rw [Fintype.card_eq_zero_iff]
          exact ⟨fun c => c.recOnSubsingleton (fun x => x.elim)⟩,
      pow_zero]
  · intro b _ hb
    exact absurd (Subsingleton.elim b _) hb
  · intro h; exact absurd (Finset.mem_univ _) h







theorem sot_repGraph_Z_ge (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ k, (fkZ G p q) ^ k ≤ fkZ (sot_repGraph V G k) p q := by
  intro k
  induction k with
  | zero =>
    rw [pow_zero]
    
    have : fkZ (sot_repGraph V G 0) p q = 1 := sot_fkZ_bot_pempty
    rw [this]
  | succ k ih =>
    rw [pow_succ]
    
    
    have hsucc : fkZ (sot_repGraph V G (k + 1)) p q = fkZ (G ⊕g sot_repGraph V G k) p q := by
      congr 1
    rw [hsucc]
    calc (fkZ G p q) ^ k * fkZ G p q
        ≤ fkZ (sot_repGraph V G k) p q * fkZ G p q :=
          mul_le_mul_of_nonneg_right ih (fkZ_pos G hp hp1 hq).le
      _ = fkZ G p q * fkZ (sot_repGraph V G k) p q := by ring
      _ ≤ fkZ (G ⊕g sot_repGraph V G k) p q := fsm_fkZ_sum_ge G (sot_repGraph V G k) hp hp1 hq





theorem sot_edge_card_lower (d n : ℕ) (hd : 1 ≤ d) :
    (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by
  have h1 := boxSV_edge_card_lower (d := d) (n := n) hd
  rw [fup_edge_card_eq d n] at h1
  have hnat : n * (2 * n + 1) ^ (d - 1) ≤ (boxGraph d n).edgeFinset.card := by
    have h2 : 2 * (n * (2 * n + 1) ^ (d - 1)) ≤ 2 * (boxGraph d n).edgeFinset.card := by
      rw [show 2 * (n * (2 * n + 1) ^ (d - 1)) = (2 * n) * (2 * n + 1) ^ (d - 1) by ring]
      exact h1
    omega
  calc (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) = ((n * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hnat









theorem sot_summable_of_surfaceBound (d : ℕ) (hd : 1 ≤ d) (C : ℝ) (hC : 0 ≤ C)
    (I : ℕ → ℝ) (hI0 : ∀ j, 0 ≤ I j)
    (hIB : ∀ j, I j ≤ C * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) :
    Summable (fun j => I j / bxt_E d (2 ^ (j + 1))) := by
  
  refine Summable.of_nonneg_of_le (f := fun j => (C / 2) * (1 / 2 : ℝ) ^ j)
    (fun j => div_nonneg (hI0 j) (bxt_E_nonneg d _)) ?_ ?_
  · intro j
    
    have hedge : (2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1) ≤ bxt_E d (2 ^ (j + 1)) := by
      have h := sot_edge_card_lower d (2 ^ (j + 1)) hd
      have hpow : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
      rw [bxt_E]
      calc (2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)
          = ((2 ^ (j + 1) : ℕ) : ℝ) * (2 * ((2 ^ (j + 1) : ℕ) : ℝ) + 1) ^ (d - 1) := by
            rw [hpow]; ring_nf
        _ ≤ ((boxGraph d (2 ^ (j + 1))).edgeFinset.card : ℝ) := h
    
    have hpow_pos : (0 : ℝ) < (4 * (2 : ℝ) ^ j + 1) ^ (d - 1) := by positivity
    have hden_pos : (0 : ℝ) < (2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1) := by positivity
    calc I j / bxt_E d (2 ^ (j + 1))
        ≤ I j / ((2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) :=
          div_le_div_of_nonneg_left (hI0 j) hden_pos hedge
      _ ≤ (C * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) /
            ((2 * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)) :=
          div_le_div_of_nonneg_right (hIB j) hden_pos.le
      _ = (C / 2) * (1 / 2 : ℝ) ^ j := by
          have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
          rw [div_pow, one_pow]
          field_simp
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (C / 2)























def sot_OrthantCrossSplit (d : ℕ) (t : ℝ) (C : ℝ) (j : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
    (K : SimpleGraph (boxVerts d (2 ^ j) ⊕ W)) (_ : DecidableRel K.Adj),
    fis_CrossInterface (boxGraph d (2 ^ j)) H K
    ∧ (Nonempty (boxGraph d (2 ^ (j + 1)) ≃g K))
    ∧ ((fkZ (boxGraph d (2 ^ j)) (fsc_logistic t) 2) ^ (2 ^ d - 1)
        ≤ fkZ H (fsc_logistic t) 2)
    ∧ ((fis_interface (boxGraph d (2 ^ j)) H K).card : ℝ)
        ≤ C * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)
    ∧ |(2 : ℝ) ^ d * bxt_E d (2 ^ j) - bxt_E d (2 ^ (j + 1))|
        ≤ ((fis_interface (boxGraph d (2 ^ j)) H K).card : ℝ)
















theorem sot_negLogDoublingBound_of_crossSplit (d : ℕ) (hd : 1 ≤ d) (t : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hsplit : ∀ j, sot_OrthantCrossSplit d t C j) :
    bxt_NegLogDoublingBound d t := by
  classical
  
  choose W _ _ H _ K _ hci hiso hH hIB hEdge using hsplit
  
  set I : ℕ → ℝ := fun j => ((fis_interface (boxGraph d (2 ^ j)) (H j) (K j)).card : ℝ) with hI
  refine ⟨I, ?_, ?_, ?_, ?_⟩
  · 
    intro j; exact Nat.cast_nonneg _
  · 
    exact sot_summable_of_surfaceBound d hd C hC I (fun j => Nat.cast_nonneg _) hIB
  · 
    intro j
    obtain ⟨φ⟩ := hiso j
    exact bxt_doublingBound_of_crossSplit t j (H j) (K j) (hci j) φ (hH j)
  · 
    intro j; exact hEdge j












theorem sot_boxGraph_zero_eq_bot (n : ℕ) : boxGraph 0 n = ⊥ := by
  ext a b
  simp only [boxGraph, SimpleGraph.comap_adj, SimpleGraph.bot_adj, hypercubicLattice_adj]
  constructor
  · intro h; rw [Finset.sum_fin_eq_sum_range] at h; simp at h
  · intro h; exact h.elim



instance sot_subsingleton_boxVerts0 (n : ℕ) : Subsingleton (boxVerts 0 n) :=
  ⟨fun a b => by apply Subtype.ext; funext i; exact i.elim0⟩


instance sot_nonempty_boxVerts0 (n : ℕ) : Nonempty (boxVerts 0 n) :=
  ⟨⟨(fun i => i.elim0), by intro i; exact i.elim0⟩⟩







theorem sot_orthantCrossSplit_satisfiable (t : ℝ) (j : ℕ) :
    sot_OrthantCrossSplit 0 t 0 j := by
  classical
  
  have hE0 : ∀ n, bxt_E 0 n = 0 := by
    intro n
    rw [bxt_E]
    have hc : (boxGraph 0 n).edgeFinset.card = 0 := by
      have hee : (boxGraph 0 n).edgeFinset = ∅ := by
        rw [SimpleGraph.edgeFinset_eq_empty, sot_boxGraph_zero_eq_bot]
      rw [hee, Finset.card_empty]
    rw [hc]; simp
  refine ⟨PEmpty, inferInstance, inferInstance, (⊥ : SimpleGraph PEmpty), inferInstance,
    (⊥ : SimpleGraph (boxVerts 0 (2 ^ j) ⊕ PEmpty)), inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      refine absurd hxy ?_
      match x, y with
      | Sum.inl a, Sum.inl b =>
        rw [SimpleGraph.sum_adj, sot_boxGraph_zero_eq_bot]; simp
      | Sum.inr c, Sum.inr d => rw [SimpleGraph.sum_adj]; simp
      | Sum.inl a, Sum.inr d => rw [SimpleGraph.sum_adj]; simp
      | Sum.inr c, Sum.inl b => rw [SimpleGraph.sum_adj]; simp
    · intro a b h; exact absurd h (by simp)
    · intro c d h; exact absurd h (by simp)
  · 
    refine ⟨?_⟩
    
    haveI : Unique (boxVerts 0 (2 ^ (j + 1))) :=
      uniqueOfSubsingleton (Classical.choice (sot_nonempty_boxVerts0 _))
    haveI : Nonempty (boxVerts 0 (2 ^ j) ⊕ PEmpty) :=
      ⟨Sum.inl (Classical.choice (sot_nonempty_boxVerts0 _))⟩
    haveI : Subsingleton (boxVerts 0 (2 ^ j) ⊕ PEmpty) := by
      constructor
      rintro (a | a) (b | b)
      · exact congrArg Sum.inl (Subsingleton.elim a b)
      · exact b.elim
      · exact a.elim
      · exact a.elim
    haveI : Unique (boxVerts 0 (2 ^ j) ⊕ PEmpty) :=
      uniqueOfSubsingleton (Classical.choice ‹Nonempty (boxVerts 0 (2 ^ j) ⊕ PEmpty)›)
    
    refine ⟨Equiv.ofUnique _ _, ?_⟩
    intro a b
    
    constructor
    · intro h
      
      exact absurd h (by simp)
    · intro h
      
      rw [sot_boxGraph_zero_eq_bot] at h
      exact absurd h (by simp)
  · 
    rw [show (2 : ℕ) ^ 0 - 1 = 0 by norm_num, pow_zero, sot_fkZ_bot_pempty]
  · 
    rw [zero_mul]
    have hle : (fis_interface (boxGraph 0 (2 ^ j)) (⊥ : SimpleGraph PEmpty)
        (⊥ : SimpleGraph (boxVerts 0 (2 ^ j) ⊕ PEmpty))) ⊆ ∅ := by
      rw [fis_interface]
      
      refine Finset.Subset.trans Finset.sdiff_subset ?_
      intro e he
      simp at he
    calc ((fis_interface (boxGraph 0 (2 ^ j)) (⊥ : SimpleGraph PEmpty)
            (⊥ : SimpleGraph (boxVerts 0 (2 ^ j) ⊕ PEmpty))).card : ℝ)
        ≤ ((∅ : Finset (Sym2 (boxVerts 0 (2 ^ j) ⊕ PEmpty))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hle
      _ = 0 := by simp
  · 
    rw [hE0, hE0]; simp


















theorem sot_fk_uniqueness_of_orthantSplit (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (C : ℝ) (hC : 0 ≤ C)
    (hsplit : ∀ t, ∀ j, sot_OrthantCrossSplit d t C j)
    (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| ≤ M)
    (osc : ℝ → ℕ → ℝ) (hosc : ∀ t, Tendsto (osc t) atTop (𝓝 0))
    (hsand : ∀ t, ∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
        - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc t (Nat.log 2 n))
    (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
    (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  have hdoubling : ∀ t, bxt_NegLogDoublingBound d t := fun t =>
    sot_negLogDoublingBound_of_crossSplit d hd t C hC (hsplit t)
  exact bxt_fk_uniqueness_of_doubling hd N eb hEbox hdoubling hbdd osc hosc hsand hfreeRot hwiredRot
































theorem sot_residue_remark : True := trivial

end FK

end StatMech
