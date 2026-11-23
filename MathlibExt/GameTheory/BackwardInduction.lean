/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Backward induction and subgame perfection (Atlas EC14.T01)

A finite extensive-form game of perfect information, without chance moves, is
a finite tree. A leaf carries a real payoff for every player in `ι`; an
internal node names the player who moves there and has `n + 1` children, one
per available action, so every decision node has at least one action.

A pure strategy profile `Profile t` picks one action at every decision node
of `t`, including nodes off the path of play. Its outcome is the payoff vector
at the leaf reached by following the chosen actions from the root.

`Deviation j τ τ'` says that `τ'` agrees with `τ` at every node not owned by
player `j`; at `j`'s nodes `τ'` may choose any action. A profile is a Nash
equilibrium when no player gains from such a deviation, and it is subgame
perfect when its restriction to every subtree is a Nash equilibrium of that
subtree. Backward induction chooses, at each node, an action maximizing the
mover's continuation payoff under the profile chosen below. The main theorem:
a backward-induction profile exists and every backward-induction profile is
subgame perfect.

## References

* H. W. Kuhn, "Extensive games and the problem of information", in
  *Contributions to the Theory of Games II*, Ann. of Math. Stud. 28,
  Princeton University Press, 1953, 193--216.
* R. Selten, "Spieltheoretische Behandlung eines Oligopolmodells mit
  Nachfrageträgheit", Z. Gesamte Staatswiss. 121 (1965), 301--324.
* M. J. Osborne and A. Rubinstein, *A Course in Game Theory*, MIT Press, 1994,
  Definition 97.2 (subgame perfect equilibrium) and Proposition 99.2 (Kuhn's
  theorem, by backward induction).
* M. Yildiz, *14.12 Game Theory Lecture Notes, Lectures 7-9*, MIT, 2002,
  Section 1 (backwards induction) and Section 2, Definition 1 (subgame
  perfection).
-/

namespace MathlibExt.GameTheory

/-- A finite perfect-information game tree with players `ι` and real payoffs. -/
inductive PerfectInfoGame (ι : Type*) where
  /-- A terminal node with payoff `payoff j` to each player `j`. -/
  | leaf (payoff : ι → ℝ) : PerfectInfoGame ι
  /-- A decision node where `player` chooses among `n + 1` actions. -/
  | node (player : ι) {n : ℕ} (child : Fin (n + 1) → PerfectInfoGame ι) : PerfectInfoGame ι

namespace PerfectInfoGame

/-- A pure strategy profile on a game tree: an action at every decision node. -/
inductive Profile {ι : Type*} : PerfectInfoGame ι → Type _ where
  /-- The unique profile on a leaf. -/
  | leaf (payoff : ι → ℝ) : Profile (PerfectInfoGame.leaf payoff)
  /-- At a decision node, choose `action` and a profile on every subtree. -/
  | node (player : ι) {n : ℕ} (child : Fin (n + 1) → PerfectInfoGame ι) (action : Fin (n + 1))
      (sub : ∀ k, Profile (child k)) : Profile (PerfectInfoGame.node player child)

namespace Profile

/-- The payoff vector reached by following the profile from the root. -/
def outcome {ι : Type*} : {t : PerfectInfoGame ι} → Profile t → ι → ℝ
  | _, Profile.leaf payoff => payoff
  | _, Profile.node _ _ action sub => outcome (sub action)

/-- `Deviation j τ τ'`: `τ'` differs from `τ` only at decision nodes owned by
player `j`. -/
inductive Deviation {ι : Type*} (j : ι) :
    {t : PerfectInfoGame ι} → Profile t → Profile t → Prop where
  /-- Leaves admit no deviation. -/
  | leaf (payoff : ι → ℝ) : Deviation j (Profile.leaf payoff) (Profile.leaf payoff)
  /-- At `j`'s own node, `j` may change the action and deviate below. -/
  | self {n : ℕ} (child : Fin (n + 1) → PerfectInfoGame ι) (a a' : Fin (n + 1))
      (sub sub' : ∀ k, Profile (child k)) (h : ∀ k, Deviation j (sub k) (sub' k)) :
      Deviation j (Profile.node j child a sub) (Profile.node j child a' sub')
  /-- At another player's node, the action is unchanged and `j` may deviate below. -/
  | other {i : ι} {n : ℕ} (child : Fin (n + 1) → PerfectInfoGame ι) (hij : i ≠ j) (a : Fin (n + 1))
      (sub sub' : ∀ k, Profile (child k)) (h : ∀ k, Deviation j (sub k) (sub' k)) :
      Deviation j (Profile.node i child a sub) (Profile.node i child a sub')

/-- `τ` is a Nash equilibrium of its tree: no player `j` strictly gains by a
deviation at `j`'s own nodes. -/
def IsNash {ι : Type*} {t : PerfectInfoGame ι} (τ : Profile t) : Prop :=
  ∀ (j : ι) (τ' : Profile t), Deviation j τ τ' → τ'.outcome j ≤ τ.outcome j

/-- `τ` is subgame perfect: its restriction to every subtree, the whole tree
included, is a Nash equilibrium of that subtree. -/
inductive IsSubgamePerfect {ι : Type*} : {t : PerfectInfoGame ι} → Profile t → Prop where
  /-- A leaf profile is subgame perfect. -/
  | leaf (payoff : ι → ℝ) : IsSubgamePerfect (Profile.leaf payoff)
  /-- A node profile is subgame perfect when it is Nash and every subprofile is
  subgame perfect. -/
  | node {i : ι} {n : ℕ} {child : Fin (n + 1) → PerfectInfoGame ι} {a : Fin (n + 1)}
      {sub : ∀ k, Profile (child k)} (hnash : IsNash (Profile.node i child a sub))
      (hsub : ∀ k, IsSubgamePerfect (sub k)) : IsSubgamePerfect (Profile.node i child a sub)

/-- `τ` is a backward-induction profile: at every decision node, the chosen
action maximizes the mover's continuation payoff, and the same holds in every
subtree. -/
inductive IsBackwardInduction {ι : Type*} : {t : PerfectInfoGame ι} → Profile t → Prop where
  /-- A leaf profile is a backward-induction profile. -/
  | leaf (payoff : ι → ℝ) : IsBackwardInduction (Profile.leaf payoff)
  /-- At a node owned by `i`, the action `a` maximizes `i`'s continuation payoff. -/
  | node {i : ι} {n : ℕ} {child : Fin (n + 1) → PerfectInfoGame ι} {a : Fin (n + 1)}
      {sub : ∀ k, Profile (child k)} (hopt : ∀ k, (sub k).outcome i ≤ (sub a).outcome i)
      (hsub : ∀ k, IsBackwardInduction (sub k)) :
      IsBackwardInduction (Profile.node i child a sub)

/-- A backward-induction profile is a Nash equilibrium. -/
theorem IsBackwardInduction.isNash {ι : Type*} {t : PerfectInfoGame ι} {τ : Profile t}
    (h : IsBackwardInduction τ) : IsNash τ := by
  induction h with
  | leaf payoff =>
    intro j τ' hdev
    cases hdev
    exact le_rfl
  | node hopt hsub ih =>
    intro j τ' hdev
    cases hdev
    case self a' sub' h =>
      exact le_trans (ih a' _ _ (h a')) (hopt a')
    case other hij sub' h =>
      exact ih _ _ _ (h _)

/-- Every finite perfect-information game tree with nonempty action sets has a
backward-induction profile. -/
theorem exists_isBackwardInduction {ι : Type*} (t : PerfectInfoGame ι) :
    ∃ τ : Profile t, IsBackwardInduction τ := by
  induction t with
  | leaf payoff =>
    exact ⟨Profile.leaf payoff, IsBackwardInduction.leaf payoff⟩
  | node player child ih =>
    rename_i n
    choose sub hsub using ih
    have hne : Nonempty (Fin (n + 1)) := ⟨⟨0, Nat.zero_lt_succ n⟩⟩
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun k => (sub k).outcome player)
      (@Finset.univ_nonempty _ _ hne)
    refine ⟨Profile.node player child a sub, IsBackwardInduction.node ?_ hsub⟩
    intro k
    exact ha k (Finset.mem_univ k)

/-- **Kuhn's theorem.** Every backward-induction profile is subgame perfect. -/
theorem IsBackwardInduction.isSubgamePerfect {ι : Type*} {t : PerfectInfoGame ι} {τ : Profile t}
    (h : IsBackwardInduction τ) : IsSubgamePerfect τ := by
  induction h with
  | leaf payoff =>
    exact IsSubgamePerfect.leaf payoff
  | node hopt hsub ih =>
    exact IsSubgamePerfect.node (IsBackwardInduction.node hopt hsub).isNash ih

/-- Backward induction produces a subgame-perfect profile in every finite
perfect-information game tree with nonempty action sets. -/
theorem exists_isBackwardInduction_isSubgamePerfect {ι : Type*} (t : PerfectInfoGame ι) :
    ∃ τ : Profile t, IsBackwardInduction τ ∧ IsSubgamePerfect τ := by
  obtain ⟨τ, hbi⟩ := exists_isBackwardInduction t
  exact ⟨τ, hbi, hbi.isSubgamePerfect⟩

end Profile

end PerfectInfoGame

end MathlibExt.GameTheory
