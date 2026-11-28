/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BackwardInduction
public import MathlibExt.GameTheory.StrategicGame

set_option autoImplicit false

universe u

namespace MathlibExt.GameTheory.PerfectInfoGame

@[expose] public section
/-!
# Induced normal form of a finite perfect-information tree

A tree profile decomposes into one strategy per player: the choices made at
that player's own decision nodes. Reassembling those strategies recovers the
profile. The induced normal form is the strategic game with those per-player
strategy types and payoffs given by the assembled profile's outcome.

## Main results

* `isNash_inducedGame_iff`: tree Nash equilibrium agrees with Nash equilibrium
  of the induced normal form.
* `exists_isNash_inducedGame`: backward induction gives a pure Nash
  equilibrium of the induced normal form.
-/


/-- A pure strategy of player `i` in the tree `t`: at `i`'s own decision
nodes, a chosen action and a substrategy in every subtree; at other
players' nodes, a substrategy in every subtree; nothing at a leaf. -/
def Strategy {ι : Type*} [DecidableEq ι] :
    (t : PerfectInfoGame ι) → ι → Type _
  | PerfectInfoGame.leaf _, _ => PUnit
  | PerfectInfoGame.node j (n := n) child, i =>
      (if i = j then Fin (n + 1) else PUnit) × (∀ k, Strategy (child k) i)

/-- Assemble one strategy per player into a tree profile, by recursion on the tree. -/
noncomputable def assemble {ι : Type*} [DecidableEq ι] :
    {t : PerfectInfoGame ι} → (∀ i, Strategy t i) → Profile t :=
  fun {t} σ =>
    PerfectInfoGame.rec (motive := fun t => (∀ i, Strategy t i) → Profile t)
      (fun payoff _ => Profile.leaf payoff)
      (fun j _ child ih σ =>
        Profile.node j child (Eq.mp (ite_eq_left rfl) (σ j).1)
          (fun k => ih k (fun i => (σ i).2 k)))
      t σ

/-- Restrict a tree profile to the strategy of player `i`: keep the
actions at `i`'s nodes, drop the actions elsewhere. -/
noncomputable def restrict {ι : Type*} [DecidableEq ι] :
    {t : PerfectInfoGame ι} → Profile t → (i : ι) → Strategy t i :=
  fun τ i =>
    Profile.rec (motive := fun t _ => ∀ i, Strategy t i)
      (fun _ _ => PUnit.unit)
      (fun j _ _ a _ ih i =>
        ((if h : i = j then Eq.mpr (ite_eq_left h) a
          else Eq.mpr (ite_eq_right h) PUnit.unit),
          fun k => ih k i))
      τ i

/-- Cast cancellation: `Eq.mp` undoes `Eq.mpr` (the two proofs of the
same equality are identified by proof irrelevance). -/
private theorem eq_mp_mpr_cancel {α β : Type u} (h1 h2 : α = β) (a : β) :
    Eq.mp h1 (Eq.mpr h2 a) = a := by
  cases h1
  cases h2
  rfl

/-- Cast cancellation: `Eq.mpr` undoes `Eq.mp`. -/
private theorem eq_mpr_mp_cancel {α β : Type u} (h1 h2 : α = β) (x : α) :
    Eq.mpr h1 (Eq.mp h2 x) = x := by
  cases h1
  cases h2
  rfl

private theorem assemble_leaf {ι : Type*} [DecidableEq ι] (payoff : ι → ℝ)
    (σ : ∀ i, Strategy (PerfectInfoGame.leaf payoff) i) :
    assemble (t := PerfectInfoGame.leaf payoff) σ = Profile.leaf payoff := rfl

private theorem assemble_node {ι : Type*} [DecidableEq ι] (j : ι) {n : Nat}
    (child : Fin (n + 1) → PerfectInfoGame ι)
    (σ : ∀ i, Strategy (PerfectInfoGame.node j child) i) :
    assemble (t := PerfectInfoGame.node j child) σ =
      Profile.node j child (Eq.mp (ite_eq_left rfl) (σ j).1)
        (fun k => assemble (fun i => (σ i).2 k)) := rfl

private theorem restrict_leaf {ι : Type*} [DecidableEq ι] (payoff : ι → ℝ)
    (i : ι) :
    restrict (Profile.leaf payoff) i = PUnit.unit := rfl

private theorem restrict_node {ι : Type*} [DecidableEq ι] (j : ι) {n : Nat}
    (child : Fin (n + 1) → PerfectInfoGame ι)
    (a : Fin (n + 1)) (sub : ∀ k, Profile (child k)) (i : ι) :
    restrict (Profile.node j child a sub) i =
      ((if h : i = j then Eq.mpr (ite_eq_left h) a
        else Eq.mpr (ite_eq_right h) PUnit.unit),
        fun k => restrict (sub k) i) := rfl

/-- Any action component at an off-path node equals the cast unit. The
cast proof is taken as given since the arity is inaccessible where this
is applied. -/
private theorem eq_mpr_punit_action {ι : Type*} [DecidableEq ι] {i j : ι} {n : Nat}
    {q : (if i = j then Fin (n + 1) else PUnit) = PUnit}
    (x : if i = j then Fin (n + 1) else PUnit) :
    Eq.mpr q PUnit.unit = x := by
  have l : Eq.mp q (Eq.mpr q PUnit.unit) = PUnit.unit :=
    eq_mp_mpr_cancel _ _ _
  have r : Eq.mp q x = PUnit.unit := Subsingleton.elim _ _
  have key : Eq.mp q (Eq.mpr q PUnit.unit) = Eq.mp q x := Eq.trans l r.symm
  have back := congrArg (Eq.mpr q) key
  have e1 : Eq.mpr q (Eq.mp q (Eq.mpr q PUnit.unit)) = Eq.mpr q PUnit.unit :=
    eq_mpr_mp_cancel _ _ _
  have e2 : Eq.mpr q (Eq.mp q x) = x := eq_mpr_mp_cancel _ _ _
  exact e1.symm.trans (back.trans e2)

/-- Every player has a strategy in every finite tree. -/
theorem strategy_nonempty {ι : Type*} [DecidableEq ι]
    (t : PerfectInfoGame ι) (i : ι) : Nonempty (Strategy t i) := by
  induction t with
  | leaf _ => exact ⟨PUnit.unit⟩
  | node j child ih =>
      refine ⟨?_, fun k => Classical.choice (ih k)⟩
      by_cases h : i = j
      · rw [ite_eq_left h]
        exact 0
      · rw [ite_eq_right h]
        exact PUnit.unit

/-- Assembling the restrictions of a profile recovers the profile. -/
theorem assemble_restrict {ι : Type*} [DecidableEq ι]
    {t : PerfectInfoGame ι} (τ : Profile t) :
    assemble (fun i => restrict τ i) = τ := by
  induction τ with
  | leaf payoff => simp only [assemble, assemble_leaf]
  | node j child a sub ih =>
      simp only [assemble, assemble_node]
      simp only [restrict_node]
      congr 1
      · rw [dite_eq_left True.intro]
        exact eq_mp_mpr_cancel _ _ _
      · apply funext
        intro k
        exact ih k

/-- Restricting an assembled profile to player `i` recovers `i`'s
strategy. -/
theorem restrict_assemble {ι : Type*} [DecidableEq ι]
    {t : PerfectInfoGame ι} (σ : ∀ i, Strategy t i) (i : ι) :
    restrict (assemble σ) i = σ i := by
  induction t with
  | leaf payoff =>
      simp only [assemble, assemble_leaf, restrict_leaf]
      exact match (σ i) with
        | PUnit.unit => rfl
  | node j child ih =>
      simp only [assemble, assemble_node]
      simp only [restrict_node]
      apply Prod.ext
      · dsimp only
        by_cases h : i = j
        · subst h
          rw [dite_eq_left rfl]
          exact eq_mpr_mp_cancel _ _ _
        · rw [dite_eq_right h]
          exact eq_mpr_punit_action (σ i).1
      · apply funext
        intro k
        exact ih k (fun i' => (σ i').2 k)

/-- **The induced normal form** of a perfect-information tree: the
strategic game whose pure strategies are the per-player tree strategies
and whose payoffs are the profile outcomes. -/
noncomputable def inducedGame {ι : Type*} [DecidableEq ι]
    (t : PerfectInfoGame ι) : MathlibExt.GameTheory.StrategicGame ι (Strategy t) where
  payoff i σ := (assemble σ).outcome i
  strategy_nonempty i := strategy_nonempty t i

/-- Payoff in the induced game is the assembled profile's outcome. -/
private theorem inducedGame_payoff_apply {ι : Type*} [DecidableEq ι]
    {t : PerfectInfoGame ι} (i : ι) (σ : ∀ i, Strategy t i) :
    (inducedGame t).payoff i σ = (assemble σ).outcome i := rfl

/-- A unilateral deviation leaves every other player's restriction unchanged. -/
private theorem deviation_restrict_eq {ι : Type*} [DecidableEq ι]
    {t : PerfectInfoGame ι} {j : ι} {τ τ' : Profile t}
    (h : Profile.Deviation j τ τ') {i : ι} (hij : i ≠ j) :
    restrict τ' i = restrict τ i := by
  induction h with
  | leaf payoff => rfl
  | self child a a' sub sub' h ih =>
      simp only [restrict_node, dite_eq_right hij]
      refine Prod.ext rfl ?_
      apply funext
      intro k
      exact ih k
  | other child hij' a sub sub' h ih =>
      simp only [restrict_node]
      refine Prod.ext rfl ?_
      apply funext
      intro k
      exact ih k

/-- Assembling strategies that agree off `j` yields a `j`-deviation. -/
private theorem deviation_assemble_of_agree {ι : Type*} [DecidableEq ι]
    (t : PerfectInfoGame ι) (j : ι) :
    ∀ (σ σ' : ∀ i, Strategy t i),
      (∀ {i : ι}, i ≠ j → σ' i = σ i) →
      Profile.Deviation j (assemble σ) (assemble σ') := by
  induction t with
  | leaf payoff =>
      intro σ σ' h
      simp only [assemble, assemble_leaf]
      exact Profile.Deviation.leaf payoff
  | node k child ih =>
      intro σ σ' h
      simp only [assemble, assemble_node]
      by_cases hkj : k = j
      · subst hkj
        refine Profile.Deviation.self _ _ _ _ _ ?_
        intro k'
        refine ih k' (fun i => (σ i).2 k') (fun i => (σ' i).2 k') ?_
        intro i hi
        show (σ' i).2 k' = (σ i).2 k'
        rw [h hi]
      · have e : σ' k = σ k := h hkj
        rw [e]
        refine Profile.Deviation.other _ hkj _ _ _ ?_
        intro k'
        refine ih k' (fun i => (σ i).2 k') (fun i => (σ' i).2 k') ?_
        intro i hi
        show (σ' i).2 k' = (σ i).2 k'
        rw [h hi]

/-- Profiles whose restrictions agree off `j` differ by a `j`-deviation. -/
private theorem deviation_of_restrict_eq {ι : Type*} [DecidableEq ι]
    {t : PerfectInfoGame ι} {j : ι} (τ τ' : Profile t)
    (h : ∀ {i : ι}, i ≠ j → restrict τ' i = restrict τ i) :
    Profile.Deviation j τ τ' := by
  rw [← assemble_restrict τ, ← assemble_restrict τ']
  refine deviation_assemble_of_agree t j _ _ ?_
  intro i hi
  exact h hi

/-- A tree profile is a Nash equilibrium (no single-player deviation
gains) if and only if its per-player restrictions form a Nash
equilibrium of the induced normal form. -/
theorem isNash_inducedGame_iff {ι : Type*} [DecidableEq ι]
    {t : PerfectInfoGame ι} (τ : Profile t) :
    MathlibExt.GameTheory.StrategicGame.IsNash (inducedGame t)
        (fun i => restrict τ i) ↔ τ.IsNash := by
  constructor
  · intro hNash j τ' hdev
    have agree : ∀ {i : ι}, i ≠ j → restrict τ' i = restrict τ i :=
      fun {i} hi => deviation_restrict_eq hdev hi
    have key : (fun i => restrict τ' i) =
        Function.update (fun i => restrict τ i) j (restrict τ' j) := by
      apply funext
      intro i
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hij]
        exact agree hij
    have key_self :
        Function.update (fun i => restrict τ i) j ((fun i => restrict τ i) j) =
        (fun i => restrict τ i) := by
      apply funext
      intro i
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hij]
    have hle := hNash j (restrict τ' j)
    rw [← key, key_self] at hle
    simp only [inducedGame_payoff_apply, assemble_restrict] at hle
    exact hle
  · intro hNash i s
    have key_self :
        Function.update (fun i => restrict τ i) i ((fun i => restrict τ i) i) =
        (fun i => restrict τ i) := by
      apply funext
      intro i'
      by_cases hij : i' = i
      · subst hij
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hij]
    have hdev : Profile.Deviation i τ
        (assemble (Function.update (fun i => restrict τ i) i s)) := by
      refine deviation_of_restrict_eq _ _ ?_
      intro i' hi'
      rw [restrict_assemble]
      simp only [Function.update_of_ne hi']
    have hle := hNash i _ hdev
    simp only [inducedGame_payoff_apply]
    rw [key_self, assemble_restrict]
    exact hle

/-- The induced normal form of every finite perfect-information tree has
a pure Nash equilibrium (via backward induction). -/
theorem exists_isNash_inducedGame {ι : Type*} [DecidableEq ι]
    (t : PerfectInfoGame ι) :
    ∃ σ, MathlibExt.GameTheory.StrategicGame.IsNash (inducedGame t) σ := by
  obtain ⟨τ, hBI, -⟩ := Profile.exists_isBackwardInduction_isSubgamePerfect t
  exact ⟨_, (isNash_inducedGame_iff τ).mpr hBI.isNash⟩

end

end MathlibExt.GameTheory.PerfectInfoGame
