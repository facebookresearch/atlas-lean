/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.OSSS.Revealment
import Code.Lattice.Clusters
import Code.Lattice.HypercubicLattice

open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false

namespace StatMech
namespace OSSS
namespace RevealmentConstruction

open StatMech.OSSS
open StatMech.OSSS.DecisionTree
open StatMech.OSSS.Revealment
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]



















def buildTree {State : Type*} (guard : State → E → Bool) (step : State → E → Bool → State)
    (base : State → Bool) : List E → State → DecisionTree E
  | [], σ => DecisionTree.leaf (base σ)
  | e :: rest, σ =>
      if guard σ e then
        DecisionTree.node e (buildTree guard step base rest (step σ e true))
                            (buildTree guard step base rest (step σ e false))
      else
        buildTree guard step base rest σ

omit [Fintype E] in






theorem mem_queried_buildTree {State : Type*} (guard : State → E → Bool)
    (step : State → E → Bool → State) (base : State → Bool) (Inv : State → Prop)
    (ω : ConfigSpace E)
    (hstep : ∀ σ e, Inv σ → guard σ e = true → Inv (step σ e (ω e)))
    (l : List E) (σ : State) (hσ : Inv σ) (i : E)
    (hi : i ∈ (buildTree guard step base l σ).queried ω) :
    ∃ τ, Inv τ ∧ guard τ i = true := by
  induction l generalizing σ with
  | nil => simp [buildTree, DecisionTree.queried] at hi
  | cons e rest ih =>
      simp only [buildTree] at hi
      by_cases hg : guard σ e = true
      · rw [if_pos hg] at hi
        rw [DecisionTree.queried, Finset.mem_insert] at hi
        rcases hi with rfl | hi'
        · exact ⟨σ, hσ, hg⟩
        · by_cases hb : ω e
          · rw [if_pos hb] at hi'
            have hI := hstep σ e hσ hg; rw [hb] at hI
            exact ih (step σ e true) hI hi'
          · rw [if_neg hb] at hi'
            have hI := hstep σ e hσ hg
            simp only [Bool.not_eq_true] at hb; rw [hb] at hI
            exact ih (step σ e false) hI hi'
      · rw [if_neg hg] at hi
        exact ih σ hσ hi









def runState {State : Type*} (guard : State → E → Bool) (step : State → E → Bool → State)
    (ω : ConfigSpace E) : List E → State → State
  | [], σ => σ
  | e :: rest, σ =>
      if guard σ e then runState guard step ω rest (step σ e (ω e))
      else runState guard step ω rest σ

omit [Fintype E] [DecidableEq E] in


theorem eval_buildTree {State : Type*} (guard : State → E → Bool)
    (step : State → E → Bool → State) (base : State → Bool) (ω : ConfigSpace E)
    (l : List E) (σ : State) :
    (buildTree guard step base l σ).eval ω = base (runState guard step ω l σ) := by
  induction l generalizing σ with
  | nil => rfl
  | cons e rest ih =>
      simp only [buildTree, runState]
      by_cases hg : guard σ e = true
      · rw [if_pos hg, if_pos hg]
        simp only [DecisionTree.eval]
        by_cases hb : ω e
        · rw [if_pos hb, hb]; exact ih (step σ e true)
        · rw [if_neg hb]; simp only [Bool.not_eq_true] at hb; rw [hb]; exact ih (step σ e false)
      · rw [if_neg hg, if_neg hg]; exact ih σ

omit [Fintype E] [DecidableEq E] in




theorem runState_inv {State : Type*} (guard : State → E → Bool)
    (step : State → E → Bool → State) (Inv : State → Prop) (ω : ConfigSpace E)
    (hstep : ∀ σ e, Inv σ → guard σ e = true → Inv (step σ e (ω e)))
    (l : List E) (σ : State) (hσ : Inv σ) : Inv (runState guard step ω l σ) := by
  induction l generalizing σ with
  | nil => exact hσ
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : guard σ e = true
      · rw [if_pos hg]; exact ih _ (hstep σ e hσ hg)
      · rw [if_neg hg]; exact ih σ hσ










variable {V : Type*} [DecidableEq V]




inductive ReachOpen (endU endV : E → V) (ω : ConfigSpace E) : V → V → Prop
  | refl (x : V) : ReachOpen endU endV ω x x
  | step {x y z : V} (e : E) (hopen : ω e = true)
      (hxy : (endU e = x ∧ endV e = y) ∨ (endU e = y ∧ endV e = x))
      (hrest : ReachOpen endU endV ω y z) : ReachOpen endU endV ω x z

omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem ReachOpen.trans {endU endV : E → V} {ω : ConfigSpace E} {x y z : V}
    (hxy : ReachOpen endU endV ω x y) (hyz : ReachOpen endU endV ω y z) :
    ReachOpen endU endV ω x z := by
  induction hxy with
  | refl => exact hyz
  | step e hopen hpair _ ih => exact ReachOpen.step e hopen hpair (ih hyz)




def ConnOpenSet (endU endV : E → V) (ω : ConfigSpace E) (x : V) (B : Set V) : Prop :=
  ∃ b ∈ B, ReachOpen endU endV ω x b

omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem connOpenSet_of_mem {endU endV : E → V} {ω : ConfigSpace E} {x : V} {B : Set V}
    (hx : x ∈ B) : ConnOpenSet endU endV ω x B :=
  ⟨x, hx, ReachOpen.refl x⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem connOpenSet_prop {endU endV : E → V} {ω : ConfigSpace E} {B : Set V} {e : E}
    (hopen : ω e = true) (hU : ConnOpenSet endU endV ω (endU e) B) :
    ConnOpenSet endU endV ω (endV e) B := by
  obtain ⟨b, hbB, hreach⟩ := hU
  exact ⟨b, hbB, ReachOpen.step e hopen (Or.inr ⟨rfl, rfl⟩) hreach⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem connOpenSet_prop' {endU endV : E → V} {ω : ConfigSpace E} {B : Set V} {e : E}
    (hopen : ω e = true) (hV : ConnOpenSet endU endV ω (endV e) B) :
    ConnOpenSet endU endV ω (endU e) B := by
  obtain ⟨b, hbB, hreach⟩ := hV
  exact ⟨b, hbB, ReachOpen.step e hopen (Or.inl ⟨rfl, rfl⟩) hreach⟩


















def geomGuard (endU endV : E → V) (disc : Finset V) (e : E) : Bool :=
  decide (endU e ∈ disc ∨ endV e ∈ disc)



def geomStep (endU endV : E → V) (disc : Finset V) (e : E) (b : Bool) : Finset V :=
  if b then insert (endU e) (insert (endV e) disc) else disc



def geomInv (endU endV : E → V) (ω : ConfigSpace E) (B : Set V) (disc : Finset V) : Prop :=
  ∀ x ∈ disc, ConnOpenSet endU endV ω x B

omit [Fintype E] [DecidableEq E] in




theorem geomInv_step (endU endV : E → V) (ω : ConfigSpace E) (B : Set V)
    (disc : Finset V) (e : E) (hInv : geomInv endU endV ω B disc)
    (hg : geomGuard endU endV disc e = true) :
    geomInv endU endV ω B (geomStep endU endV disc e (ω e)) := by
  unfold geomGuard at hg; simp only [decide_eq_true_eq] at hg
  unfold geomStep
  by_cases hb : ω e = true
  · rw [if_pos hb]
    have hUc : ConnOpenSet endU endV ω (endU e) B := by
      rcases hg with hU | hV
      · exact hInv _ hU
      · exact connOpenSet_prop' hb (hInv _ hV)
    have hVc : ConnOpenSet endU endV ω (endV e) B := connOpenSet_prop hb hUc
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hUc
    · exact hVc
    · exact hInv x hx
  · simp only [Bool.not_eq_true] at hb; rw [hb]; simpa using hInv




def exploreTree (endU endV : E → V) (base : Finset V → Bool)
    (l : List E) (disc₀ : Finset V) : DecisionTree E :=
  buildTree (geomGuard endU endV) (geomStep endU endV) base l disc₀

omit [Fintype E] in




theorem queried_exploreTree_imp (endU endV : E → V) (base : Finset V → Bool)
    (ω : ConfigSpace E) (B : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E)
    (hi : i ∈ (exploreTree endU endV base l disc₀).queried ω) :
    ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
  have hInv0 : geomInv endU endV ω B disc₀ :=
    fun x hx => connOpenSet_of_mem (hdisc₀ x hx)
  obtain ⟨τ, hτInv, hτg⟩ := mem_queried_buildTree (guard := geomGuard endU endV)
    (step := geomStep endU endV) (base := base) (Inv := geomInv endU endV ω B) (ω := ω)
    (fun σ e hσ hg => geomInv_step endU endV ω B σ e hσ hg) l disc₀ hInv0 i hi
  unfold geomGuard at hτg; simp only [decide_eq_true_eq] at hτg
  rcases hτg with hU | hV
  · exact Or.inl (hτInv _ hU)
  · exact Or.inr (hτInv _ hV)












theorem reveal_exploreTree_le {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (endU endV : E → V) (base : Finset V → Bool) (B : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E) :
    reveal ν (exploreTree endU endV base l disc₀) i
      ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
  have h := revealment_le_of_queried_imp_or hν (exploreTree endU endV base l disc₀) i
    (fun ω => ConnOpenSet endU endV ω (endU i) B)
    (fun ω => ConnOpenSet endU endV ω (endV i) B)
    (fun ω hq => queried_exploreTree_imp endU endV base ω B l disc₀ hdisc₀ i hq)
  rwa [Revealment.revealment] at h










section Lattice

variable {d : ℕ}




def ConnectedToSet (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (B : Set (Site d)) :
    Prop := ∃ b ∈ B, Connected d ω x b





noncomputable def liftCfg (edge : E → Sym2 (Site d)) (ω : ConfigSpace E) :
    ConfigSpace (Sym2 (Site d)) :=
  fun s => if h : ∃ e, edge e = s then ω h.choose else false

omit [DecidableEq E] [DecidableEq V] in

theorem liftCfg_apply_edge {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    (ω : ConfigSpace E) (e : E) : liftCfg edge ω (edge e) = ω e := by
  unfold liftCfg
  have hex : ∃ e', edge e' = edge e := ⟨e, rfl⟩
  rw [dif_pos hex]; congr 1; exact hinj hex.choose_spec

omit [DecidableEq E] [DecidableEq V] in



theorem reachOpen_imp_connected {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} {ω : ConfigSpace E}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {x y : Site d} (h : ReachOpen endU endV ω x y) :
    Connected d (liftCfg edge ω) x y := by
  induction h with
  | refl x => exact connected_refl _ x
  | step e hopen hpair _ ih =>
      have hedgeopen : liftCfg edge ω (edge e) = true := by
        rw [liftCfg_apply_edge hinj]; exact hopen
      have hopenUV : IsOpenEdge d (liftCfg edge ω) (endU e) (endV e) := by
        refine ⟨hadj e, ?_⟩; rw [← hcoh e]; exact hedgeopen
      rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
      · subst hU; subst hV; exact (IsOpenEdge.connected hopenUV).trans ih
      · subst hU; subst hV; exact (IsOpenEdge.connected (isOpenEdge_symm hopenUV)).trans ih

omit [DecidableEq E] [DecidableEq V] in

theorem connOpenSet_imp_connectedToSet {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {ω : ConfigSpace E} {x : Site d} {B : Set (Site d)}
    (h : ConnOpenSet endU endV ω x B) : ConnectedToSet d (liftCfg edge ω) x B := by
  obtain ⟨b, hbB, hreach⟩ := h
  exact ⟨b, hbB, reachOpen_imp_connected hinj hcoh hadj hreach⟩


theorem expect_indicator_mono {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, P ω → Q ω) :
    expect ν (fun ω => if P ω then (1 : ℝ) else 0)
      ≤ expect ν (fun ω => if Q ω then (1 : ℝ) else 0) := by
  apply expect_mono hν
  intro ω
  by_cases hp : P ω
  · rw [if_pos hp, if_pos (h ω hp)]
  · rw [if_neg hp]; split <;> norm_num













theorem reveal_exploreTree_le_connected {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (base : Finset (Site d) → Bool) (B : Set (Site d)) (l : List E) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E) :
    reveal ν (exploreTree endU endV base l disc₀) i
      ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) B then (1 : ℝ) else 0) := by
  refine le_trans (reveal_exploreTree_le hν endU endV base B l disc₀ hdisc₀ i) ?_
  apply add_le_add
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)

end Lattice











omit [Fintype E] [DecidableEq E] in



theorem runState_geomInv (endU endV : E → V) (ω : ConfigSpace E) (B : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
    geomInv endU endV ω B (runState (geomGuard endU endV) (geomStep endU endV) ω l disc₀) :=
  runState_inv (guard := geomGuard endU endV) (step := geomStep endU endV)
    (Inv := geomInv endU endV ω B) (ω := ω)
    (fun σ e hσ hg => geomInv_step endU endV ω B σ e hσ hg) l disc₀
    (fun x hx => connOpenSet_of_mem (hdisc₀ x hx))

omit [Fintype E] [DecidableEq E] in




theorem eval_exploreTree_imp_conn (endU endV : E → V) (o : V) (B : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
    (ω : ConfigSpace E)
    (h : (exploreTree endU endV (fun disc => decide (o ∈ disc)) l disc₀).eval ω = true) :
    ConnOpenSet endU endV ω o B := by
  rw [exploreTree, eval_buildTree] at h
  simp only [decide_eq_true_eq] at h
  exact runState_geomInv endU endV ω B l disc₀ hdisc₀ o h

end RevealmentConstruction
end OSSS
end StatMech
