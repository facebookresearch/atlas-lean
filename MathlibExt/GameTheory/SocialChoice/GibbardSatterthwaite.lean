/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Basic
public import MathlibExt.Order.StrictTotalOrder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push
import MathlibExt.GameTheory.SocialChoice.Arrow

@[expose] public section

section
namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-! # Gibbard–Satterthwaite theorem

Records onto and strategy-proof resolute SCFs over strict total orders.
Reuses the shared strict-order bundle.
-/

/-- **Strict preference orders for the Gibbard–Satterthwaite theorem.** A strict total order on a
type $\alpha$ is a binary relation $<$ on $\alpha$ that is irreflexive ($a < a$ holds for no $a$),
transitive ($a < b$ and $b < c$ imply $a < c$) and total on distinct elements ($a \ne b$ implies
$a < b$ or $b < a$). In the Gibbard–Satterthwaite development it models a voter's strict
preference over alternatives. -/
abbrev StrictTotalOrder (α : Type*) :=
  MathlibExt.Order.StrictTotalOrder α

namespace StrictTotalOrder

/-- **Building a strict preference order in the Gibbard–Satterthwaite setting.** A binary
relation $<$ on a type $\alpha$ that is irreflexive ($a < a$ holds for no $a$), transitive
($a < b$ and $b < c$ imply $a < c$) and total on distinct elements ($a \ne b$ implies $a < b$ or
$b < a$) defines a strict total order on $\alpha$ whose relation is $<$. -/
abbrev mk {α : Type*} (lt : α → α → Prop)
    (irrefl : ∀ a, ¬lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a) :
    StrictTotalOrder α :=
  MathlibExt.Order.StrictTotalOrder.mk lt irrefl trans total

/-- **Relation of a strict preference order.** The relation of a strict total order $T$ on a type
$\alpha$ is its underlying binary relation $<_T$ on $\alpha$, which is irreflexive, transitive,
and relates any two distinct elements in one direction or the other. -/
abbrev lt {α : Type*} (self : StrictTotalOrder α) : α → α → Prop :=
  MathlibExt.Order.StrictTotalOrder.lt self

/-- **Irreflexivity of strict preference.** Let $T$ be a strict total order on a type $\alpha$,
with relation $<_T$. Then $a <_T a$ fails for every $a \in \alpha$. -/
abbrev irrefl {α : Type*} (self : StrictTotalOrder α) (a : α) : ¬self.lt a a :=
  MathlibExt.Order.StrictTotalOrder.irrefl self a

/-- **Transitivity of strict preferences in the Gibbard–Satterthwaite setting.** Let $<$ be the
relation of a strict total order on a type $\alpha$. If $a, b, c \in \alpha$ satisfy $a < b$ and
$b < c$, then $a < c$. -/
abbrev trans {α : Type*} (self : StrictTotalOrder α) {a b c : α}
    (h1 : self.lt a b) (h2 : self.lt b c) : self.lt a c :=
  MathlibExt.Order.StrictTotalOrder.trans self h1 h2

/-- **Strict preferences in the Gibbard–Satterthwaite setting are total.** Let $<$ be the relation
of a strict total order on a type $\alpha$. If $a, b \in \alpha$ and $a \ne b$, then $a < b$ or
$b < a$. -/
abbrev total {α : Type*} (self : StrictTotalOrder α) {a b : α} (h : a ≠ b) :
    self.lt a b ∨ self.lt b a :=
  MathlibExt.Order.StrictTotalOrder.total self h

end StrictTotalOrder

/-- **Preference profiles for the Gibbard–Satterthwaite theorem.** For a type $A$ of alternatives
and a type $V$ of voters, a profile is a function assigning to each voter $i \in V$ a strict total
order $<_i$ on $A$, the strict preference of voter $i$. -/
abbrev Profile (Alt Voter : Type*) := Voter → StrictTotalOrder Alt

/-- **Social choice functions.** For a type $A$ of alternatives and a type $V$ of voters, a
resolute social choice function is a function $F$ sending each profile $p$ (an assignment of a
strict total order on $A$ to each voter in $V$) to a single chosen alternative $F(p) \in A$. -/
abbrev SocialChoiceFunction (Alt Voter : Type*) := Profile Alt Voter → Alt

/-- **Top-ranked alternative.** For a strict total order $o$ on the alternatives, write
$x \succ_o y$ when $x$ is related to $y$ by $o$ ($o$ ranks $x$ above $y$). An alternative $t$ is
top-ranked by $o$ when $t \succ_o b$ for every alternative $b \ne t$. -/
def IsTopRanked {Alt : Type*} (o : StrictTotalOrder Alt) (top : Alt) : Prop :=
  ∀ b, b ≠ top → o.lt top b

/-- **Onto social choice function.** A resolute social choice function $F$ is onto when every
alternative $a$ is chosen at some profile, that is, $F(p) = a$ for some profile $p$. -/
def IsOnto {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) : Prop :=
  ∀ a, ∃ p : Profile Alt Voter, F p = a

/-- **Profiles differing only at one voter.** Let $p_1$ and $p_2$ be profiles, each assigning a
strict total order on the alternatives to every voter, and let $i$ be a voter. Then $p_2$ differs
from $p_1$ at most at voter $i$ when $p_1(j) = p_2(j)$ for every voter $j \ne i$. -/
def DiffAtMostAt {Alt Voter : Type*} (p₁ p₂ : Profile Alt Voter) (i : Voter) : Prop :=
  ∀ j, j ≠ i → p₁ j = p₂ j

/-- **Strategy-proof social choice function.** For a strict total order $P$, write $x \succ_P y$
when $x$ is related to $y$ by $P$ ($P$ ranks $x$ above $y$). A resolute social choice function $F$
is strategy-proof when, for all profiles $p_1$, $p_2$ and every voter $i$ such that $p_1(j) =
p_2(j)$ for all voters $j \ne i$, it is not the case that $F(p_2) \succ_{p_1(i)} F(p_1)$: no voter
gains by misreporting alone, judged by the true order $p_1(i)$. -/
def IsStrategyProof {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) : Prop :=
  ∀ (p₁ : Profile Alt Voter) (i : Voter) (p₂ : Profile Alt Voter),
    DiffAtMostAt p₁ p₂ i → ¬ (p₁ i).lt (F p₂) (F p₁)

/-- **Dictator of a social choice function.** For a resolute social choice function $F$, a voter
$d$ is a dictator when, for every profile $p$, the chosen alternative $F(p)$ is top-ranked in the
preference order $p(d)$ of voter $d$. -/
def IsDictator {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) (d : Voter) : Prop :=
  ∀ p : Profile Alt Voter, IsTopRanked (p d) (F p)

/-- **Dictatorial social choice function.** A resolute social choice function $F$ is dictatorial
when some voter is a dictator for $F$: there is a voter $d$ such that, for every profile $p$, the
chosen alternative $F(p)$ is top-ranked in the preference order $p(d)$ of voter $d$. -/
def IsDictatorial {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) : Prop :=
  ∃ d : Voter, IsDictator F d

-- Helper lemmas (all with explicit binders; no `variable`).
-- Step 1: monotonicity (Maskin) from strategy-proofness.

/-- Asymmetry of a strict total order. -/
private theorem sto_asymm {Alt : Type*} (o : StrictTotalOrder Alt) {a b : Alt}
    (h : o.lt a b) : ¬ o.lt b a :=
  fun h2 => o.irrefl a (o.trans h h2)

/-- A strict preference implies inequality. -/
private theorem sto_ne_of_lt {Alt : Type*} (o : StrictTotalOrder Alt) {a b : Alt}
    (h : o.lt a b) : a ≠ b :=
  fun heq => o.irrefl a (heq ▸ h)

/-- Totality flipped: if `¬ lt a b` and `a ≠ b` then `lt b a`. -/
private theorem sto_gt_of_not_lt {Alt : Type*} (o : StrictTotalOrder Alt) {a b : Alt}
    (hne : a ≠ b) (h : ¬ o.lt a b) : o.lt b a := by
  rcases o.total hne with h1 | h1
  · exact absurd h1 h
  · exact h1

/-- Single-voter deviation the other way is also unilateral. -/
private theorem diffAtMostAt_update_left {Alt Voter : Type*} [DecidableEq Voter]
    (R : Profile Alt Voter) (i : Voter) (v : StrictTotalOrder Alt) :
    DiffAtMostAt (Function.update R i v) R i :=
  fun _j hj => Function.update_of_ne hj v R

/-- Single-voter deviation is unilateral. -/
private theorem diffAtMostAt_update_right {Alt Voter : Type*} [DecidableEq Voter]
    (R : Profile Alt Voter) (i : Voter) (v : StrictTotalOrder Alt) :
    DiffAtMostAt R (Function.update R i v) i :=
  fun _j hj => (Function.update_of_ne hj v R).symm

/-- One-voter monotonicity: improving the winner's position for one voter
does not change the outcome. Proved by applying strategy-proofness in both
directions. -/
private theorem mono_one {Alt Voter : Type*} [DecidableEq Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (R : Profile Alt Voter) (i : Voter) (v : StrictTotalOrder Alt)
    (hpres : ∀ b, (R i).lt (F R) b → v.lt (F R) b) :
    F (Function.update R i v) = F R := by
  by_contra hne
  have hSP1 : ¬ (R i).lt (F (Function.update R i v)) (F R) :=
    hSP R i (Function.update R i v) (diffAtMostAt_update_right R i v)
  have hSP2 : ¬ (Function.update R i v i).lt (F R) (F (Function.update R i v)) :=
    hSP (Function.update R i v) i R (diffAtMostAt_update_left R i v)
  rw [Function.update_self] at hSP2
  have hne' : F (Function.update R i v) ≠ F R := hne
  rcases (R i).total hne' with h1 | h1
  · exact hSP1 h1
  · exact hSP2 (hpres _ h1)

/-- Multi-voter monotonicity: if every voter's new order preserves every
comparison won by the old winner, the outcome is unchanged. Proved by
changing voters one at a time (`Finset.induction`). -/
private theorem mono_many {Alt Voter : Type*} [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (R S : Profile Alt Voter)
    (hpres : ∀ (i : Voter) (b : Alt), (R i).lt (F R) b → (S i).lt (F R) b) :
    F S = F R := by
  classical
  have := Fintype.ofFinite Voter
  let x : Alt := F R
  let M : Finset Voter → Profile Alt Voter := fun T i => if i ∈ T then S i else R i
  have hM_empty : M ∅ = R := by
    funext i
    simp [M]
  have hM_univ : M Finset.univ = S := by
    funext i
    simp [M]
  have hM_insert : ∀ (T : Finset Voter) (k : Voter), k ∉ T →
      M (insert k T) = Function.update (M T) k (S k) := by
    intro T k hk
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp [M]
    · rw [Function.update_of_ne hjk]
      simp only [M]
      have hmem : (j ∈ insert k T) = (j ∈ T) := by
        simp [Finset.mem_insert, hjk]
      simp only [hmem]
  have key : ∀ T : Finset Voter, T ⊆ Finset.univ → F (M T) = x := by
    refine Finset.induction ?_ ?_
    · intro _
      rw [hM_empty]
    · intro k T hk ih hsub
      have hMT : F (M T) = x :=
        ih (Finset.Subset.trans (Finset.subset_insert k T) hsub)
      have hUpd : M (insert k T) = Function.update (M T) k (S k) :=
        hM_insert T k hk
      have hMk : M T k = R k := by simp [M, hk]
      have hpres' : ∀ b, (M T k).lt (F (M T)) b → (S k).lt (F (M T)) b := by
        intro b hb
        rw [hMT] at hb ⊢
        rw [hMk] at hb
        exact hpres k b hb
      have hmono := mono_one F hSP (M T) k (S k) hpres'
      rw [hUpd, hmono, hMT]
  have := key Finset.univ (Finset.subset_univ _)
  rw [hM_univ] at this
  exact this

-- Step 2: raising a set to the top, unanimity, weak Pareto.

/-- Raise the set `P` to the top of `o`, keeping the internal order inside
and outside `P`. -/
private def raiseOrder {Alt : Type*} [DecidableEq Alt] (o : StrictTotalOrder Alt)
    (P : Finset Alt) : StrictTotalOrder Alt where
  lt := fun x y =>
    (x ∈ P ∧ y ∉ P) ∨ (((x ∈ P ∧ y ∈ P) ∨ (x ∉ P ∧ y ∉ P)) ∧ o.lt x y)
  irrefl := by
    intro a h
    rcases h with ⟨ha, hna⟩ | ⟨_, hlt⟩
    · exact hna ha
    · exact o.irrefl a hlt
  trans := by
    intro a b c hab hbc
    rcases hab with ⟨haP, hnbP⟩ | ⟨hsab, hltab⟩
    · rcases hbc with ⟨hbP, hncP⟩ | ⟨hsbc, _⟩
      · exact absurd hbP hnbP
      · rcases hsbc with ⟨hbP, hcP⟩ | ⟨hnbP, hncP⟩
        · exact absurd hbP hnbP
        · exact Or.inl ⟨haP, hncP⟩
    · rcases hbc with ⟨hbP, hncP⟩ | ⟨hsbc, hltbc⟩
      · rcases hsab with ⟨haP, _⟩ | ⟨_, hnbP⟩
        · exact Or.inl ⟨haP, hncP⟩
        · exact absurd hbP hnbP
      · have hltac : o.lt a c := o.trans hltab hltbc
        rcases hsab with ⟨haP, hbP⟩ | ⟨hnaP, hnbP⟩
        · rcases hsbc with ⟨_, hcP⟩ | ⟨hnbP, _⟩
          · exact Or.inr ⟨Or.inl ⟨haP, hcP⟩, hltac⟩
          · exact absurd hbP hnbP
        · rcases hsbc with ⟨hbP, _⟩ | ⟨_, hncP⟩
          · exact absurd hbP hnbP
          · exact Or.inr ⟨Or.inr ⟨hnaP, hncP⟩, hltac⟩
  total := by
    intro a b hne
    by_cases haP : a ∈ P <;> by_cases hbP : b ∈ P
    · rcases o.total hne with h | h
      · exact Or.inl (Or.inr ⟨Or.inl ⟨haP, hbP⟩, h⟩)
      · exact Or.inr (Or.inr ⟨Or.inl ⟨hbP, haP⟩, h⟩)
    · exact Or.inl (Or.inl ⟨haP, hbP⟩)
    · exact Or.inr (Or.inl ⟨hbP, haP⟩)
    · rcases o.total hne with h | h
      · exact Or.inl (Or.inr ⟨Or.inr ⟨haP, hbP⟩, h⟩)
      · exact Or.inr (Or.inr ⟨Or.inr ⟨hbP, haP⟩, h⟩)

/-- Members of `P` beat non-members in the raised order. -/
private theorem raise_mem_top {Alt : Type*} [DecidableEq Alt] (o : StrictTotalOrder Alt)
    (P : Finset Alt) {x y : Alt} (hx : x ∈ P) (hy : y ∉ P) :
    (raiseOrder o P).lt x y :=
  Or.inl ⟨hx, hy⟩

/-- The raised order agrees with `o` outside `P`. -/
private theorem raise_preserve_outside {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (P : Finset Alt) {x y : Alt}
    (hx : x ∉ P) (hy : y ∉ P) :
    (raiseOrder o P).lt x y ↔ o.lt x y := by
  constructor
  · intro h
    rcases h with ⟨hxP, _⟩ | ⟨_, hlt⟩
    · exact absurd hxP hx
    · exact hlt
  · intro h
    exact Or.inr ⟨Or.inr ⟨hx, hy⟩, h⟩

/-- The raised order agrees with `o` inside `P`. -/
private theorem raise_preserve_inside {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (P : Finset Alt) {x y : Alt}
    (hx : x ∈ P) (hy : y ∈ P) :
    (raiseOrder o P).lt x y ↔ o.lt x y := by
  constructor
  · intro h
    rcases h with ⟨_, hyP⟩ | ⟨_, hlt⟩
    · exact absurd hy hyP
    · exact hlt
  · intro h
    exact Or.inr ⟨Or.inl ⟨hx, hy⟩, h⟩

/-- Raising a singleton puts that alternative on top. -/
private theorem raise_single_top {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (a : Alt) :
    IsTopRanked (raiseOrder o {a}) a := by
  intro b hb
  apply Or.inl
  constructor
  · exact Finset.mem_singleton_self a
  · rw [Finset.mem_singleton]
    exact hb

/-- Unanimity from ontoness plus monotonicity: a unanimous top is chosen. -/
private theorem unanimity {Alt Voter : Type*}
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (hOnto : IsOnto F)
    (R : Profile Alt Voter) (a : Alt) (h : ∀ i, IsTopRanked (R i) a) :
    F R = a := by
  classical
  obtain ⟨Q, hQ⟩ := hOnto a
  have hpres : ∀ (i : Voter) (b : Alt), (Q i).lt (F Q) b → (R i).lt (F Q) b := by
    intro i b hb
    rw [hQ] at hb ⊢
    by_cases hba : b = a
    · rw [hba] at hb
      exact absurd hb ((Q i).irrefl a)
    · exact h i b hba
  have hmono := mono_many F hSP Q R hpres
  rw [hQ] at hmono
  exact hmono

/-- If everyone ranks all of `P` above everything outside, the winner is in `P`. -/
private theorem winner_in_set {Alt Voter : Type*}
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (hOnto : IsOnto F)
    (R : Profile Alt Voter) (P : Finset Alt) (a₀ : Alt) (ha₀ : a₀ ∈ P)
    (h : ∀ (i : Voter) (x : Alt), x ∈ P → ∀ (y : Alt), y ∉ P → (R i).lt x y) :
    F R ∈ P := by
  classical
  by_contra hx
  let x : Alt := F R
  let S : Profile Alt Voter := fun i => raiseOrder (R i) {a₀}
  have hUna : F S = a₀ := unanimity F hSP hOnto S a₀ (fun i => raise_single_top (R i) a₀)
  have hxa : F R ≠ a₀ := by
    intro heq
    apply hx
    rw [heq]
    exact ha₀
  have hpres : ∀ (i : Voter) (c : Alt), (R i).lt x c → (S i).lt x c := by
    intro i c hc
    by_cases hca : c = a₀
    · rw [hca] at hc
      have hlt : (R i).lt a₀ x := h i a₀ ha₀ x hx
      exact absurd hc (sto_asymm (R i) hlt)
    · have hxc : x ∉ ({a₀} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact hxa
      have hcc : c ∉ ({a₀} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact hca
      exact (raise_preserve_outside (R i) {a₀} hxc hcc).mpr hc
  have hmono := mono_many F hSP R S hpres
  have heq : F R = a₀ := hmono.symm.trans hUna
  have hxP : F R ∈ P := by
    rw [heq]
    exact ha₀
  exact hx hxP

/-- Weak Pareto: a unanimously dominated alternative is never chosen. -/
private theorem weakPareto {Alt Voter : Type*}
    [Finite Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (hOnto : IsOnto F)
    (R : Profile Alt Voter) (a b : Alt) (h : ∀ i, (R i).lt a b) :
    F R ≠ b := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty Voter)
  have hne : a ≠ b := sto_ne_of_lt (R i₀) (h i₀)
  intro hFB
  let S : Profile Alt Voter := fun i => raiseOrder (R i) {a}
  have hUna : F S = a := unanimity F hSP hOnto S a (fun i => raise_single_top (R i) a)
  have hpres : ∀ (i : Voter) (c : Alt), (R i).lt (F R) c → (S i).lt (F R) c := by
    intro i c hc
    rw [hFB] at hc ⊢
    by_cases hca : c = a
    · rw [hca] at hc
      exact absurd hc (sto_asymm (R i) (h i))
    · have hbc : b ∉ ({a} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact fun heq => hne (heq ▸ rfl)
      have hcc : c ∉ ({a} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact hca
      exact (raise_preserve_outside (R i) {a} hbc hcc).mpr hc
  have hmono := mono_many F hSP R S hpres
  have hab : a = b := hUna.symm.trans (hmono.trans hFB)
  exact hne hab

/-- With three distinct alternatives, every pair has a third alternative
distinct from both. -/
private theorem third_alt {Alt : Type*}
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (u v : Alt) : ∃ w : Alt, w ≠ u ∧ w ≠ v := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hAlt
  by_contra hcon
  push Not at hcon
  have ha' : a = u ∨ a = v := by
    by_cases h : a = u
    · exact Or.inl h
    · exact Or.inr (hcon a h)
  have hb' : b = u ∨ b = v := by
    by_cases h : b = u
    · exact Or.inl h
    · exact Or.inr (hcon b h)
  have hc' : c = u ∨ c = v := by
    by_cases h : c = u
    · exact Or.inl h
    · exact Or.inr (hcon c h)
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl <;>
    contradiction

-- Step 3: the induced social welfare function (Reny-style reduction to Arrow).

/-- Agreement on a pair from two positive facts (one per order). -/
private theorem pair_agree {Alt : Type*} (o₁ o₂ : StrictTotalOrder Alt) (u v : Alt)
    (h1 : o₁.lt u v) (h2 : o₂.lt u v) :
    (o₁.lt u v ↔ o₂.lt u v) ∧ (o₁.lt v u ↔ o₂.lt v u) :=
  ⟨iff_of_true h1 h2, iff_of_false (sto_asymm o₁ h1) (sto_asymm o₂ h2)⟩

/-- Every pair has a third alternative distinct from both (existential form). -/
private theorem exists_ne {Alt : Type*}
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c) (u : Alt) : ∃ w : Alt, w ≠ u := by
  classical
  obtain ⟨w, hw, _⟩ := third_alt hAlt u u
  exact ⟨w, hw⟩

/-- Raise the pair `{a, b}` to the top of every voter's order. -/
private def raisePair {Alt Voter : Type*} [DecidableEq Alt]
    (R : Profile Alt Voter) (a b : Alt) : Profile Alt Voter :=
  fun i => raiseOrder (R i) {a, b}

/-- The pair-raise does not depend on the order of the pair. -/
private theorem raisePair_comm {Alt Voter : Type*} [DecidableEq Alt]
    (R : Profile Alt Voter) (a b : Alt) :
    raisePair R b a = raisePair R a b := by
  funext i
  unfold raisePair
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact or_comm

/-- The pair-raise preserves every comparison won by a pair member in the
triple-raise. Used for transitivity of the induced social order. -/
private theorem triple_pair_preserve {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (a b c p q w d : Alt)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpq : p ≠ q)
    (hpsub : p = a ∨ p = b ∨ p = c) (hqsub : q = a ∨ q = b ∨ q = c)
    (hw : w = p ∨ w = q)
    (h : (raiseOrder o {a, b, c}).lt w d) : (raiseOrder o {p, q}).lt w d := by
  have hwP : w ∈ ({p, q} : Finset Alt) := by
    rcases hw with rfl | rfl <;> simp
  have hsub : ∀ z : Alt, z ∈ ({p, q} : Finset Alt) → z ∈ ({a, b, c} : Finset Alt) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl
    · rcases hpsub with rfl | rfl | rfl <;> simp
    · rcases hqsub with rfl | rfl | rfl <;> simp
  have hwT : w ∈ ({a, b, c} : Finset Alt) := hsub w hwP
  by_cases hdw : d = w
  · rw [← hdw] at h
    exact absurd h ((raiseOrder o {a, b, c}).irrefl d)
  · by_cases hdP : d ∈ ({p, q} : Finset Alt)
    · have hdT : d ∈ ({a, b, c} : Finset Alt) := hsub d hdP
      have ho : o.lt w d :=
        (raise_preserve_inside o {a, b, c} hwT hdT).mp h
      exact (raise_preserve_inside o {p, q} hwP hdP).mpr ho
    · exact raise_mem_top o {p, q} hwP hdP

/-- Induced social relation: `a` is socially above `b` if `a ≠ b` and `F`
picks `a` when `{a, b}` is raised to the top everywhere. -/
private def socLT {Alt Voter : Type*} [DecidableEq Alt]
    (F : SocialChoiceFunction Alt Voter) (R : Profile Alt Voter) (a b : Alt) : Prop :=
  a ≠ b ∧ F (raisePair R a b) = a

/-- Transitivity of the induced social relation, via the raised triple. -/
private theorem socTrans {Alt Voter : Type*} [DecidableEq Alt]
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) {a b c : Alt}
    (hab : a ≠ b ∧ F (raisePair R a b) = a)
    (hbc : b ≠ c ∧ F (raisePair R b c) = b) :
    a ≠ c ∧ F (raisePair R a c) = a := by
  classical
  obtain ⟨hab2, hFab⟩ := hab
  obtain ⟨hbc2, hFbc⟩ := hbc
  by_cases hac2 : a = c
  · have hswap : raisePair R b c = raisePair R b a := by rw [hac2]
    rw [hswap, raisePair_comm R a b, hFab] at hFbc
    exact absurd hFbc hab2
  · let T : Profile Alt Voter := fun i => raiseOrder (R i) {a, b, c}
    have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b, c} : Finset Alt) →
        ∀ (y : Alt), y ∉ ({a, b, c} : Finset Alt) → (T i).lt x y := by
      intro i x hx y hy
      exact raise_mem_top (R i) {a, b, c} hx hy
    have hmem := winner_in_set F hSP hOnto T {a, b, c} a (by simp) htop
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hwa | hwb | hwc
    · have hpres : ∀ (i : Voter) (d : Alt), (T i).lt (F T) d →
          (raisePair R a c i).lt (F T) d := by
        intro i d hd
        rw [hwa] at hd ⊢
        exact triple_pair_preserve (R i) a b c a c a d hab2 hac2 hbc2 hac2
          (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inl rfl) hd
      have hmono := mono_many F hSP T (raisePair R a c) hpres
      rw [hwa] at hmono
      exact ⟨hac2, hmono⟩
    · have hpres : ∀ (i : Voter) (d : Alt), (T i).lt (F T) d →
          (raisePair R a b i).lt (F T) d := by
        intro i d hd
        rw [hwb] at hd ⊢
        exact triple_pair_preserve (R i) a b c a b b d hab2 hac2 hbc2 hab2
          (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr rfl) hd
      have hmono := mono_many F hSP T (raisePair R a b) hpres
      rw [hwb, hFab] at hmono
      exact absurd hmono hab2
    · have hpres : ∀ (i : Voter) (d : Alt), (T i).lt (F T) d →
          (raisePair R b c i).lt (F T) d := by
        intro i d hd
        rw [hwc] at hd ⊢
        exact triple_pair_preserve (R i) a b c b c c d hab2 hac2 hbc2 hbc2
          (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inr rfl) hd
      have hmono := mono_many F hSP T (raisePair R b c) hpres
      rw [hwc, hFbc] at hmono
      exact absurd hmono hbc2

/-- Totality of the induced social relation. -/
private theorem socTotal {Alt Voter : Type*} [DecidableEq Alt]
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) {a b : Alt} (hne : a ≠ b) :
    (a ≠ b ∧ F (raisePair R a b) = a) ∨ (b ≠ a ∧ F (raisePair R b a) = b) := by
  classical
  have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b} : Finset Alt) →
      ∀ (y : Alt), y ∉ ({a, b} : Finset Alt) → (raisePair R a b i).lt x y := by
    intro i x hx y hy
    exact raise_mem_top (R i) {a, b} hx hy
  have hmem := winner_in_set F hSP hOnto (raisePair R a b) {a, b} a
    (Finset.mem_insert_self a {b}) htop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact Or.inl ⟨hne, h1⟩
  · exact Or.inr ⟨fun heq => hne heq.symm, by rw [raisePair_comm R a b]; exact h1⟩

/-- The induced social welfare function. -/
private def socOrder {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) : StrictTotalOrder Alt where
  lt := socLT F R
  irrefl := fun _a h => h.1 rfl
  trans := fun hab hbc => socTrans F hSP hOnto R hab hbc
  total := fun hne => socTotal F hSP hOnto R hne

/-- The induced SWF is Pareto. -/
private theorem socPareto {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) (a b : Alt) (h : ∀ i, (R i).lt a b) :
    (socOrder F hSP hOnto R).lt a b := by
  change a ≠ b ∧ F (raisePair R a b) = a
  obtain ⟨i₀⟩ := (inferInstance : Nonempty Voter)
  have hne : a ≠ b := sto_ne_of_lt (R i₀) (h i₀)
  refine ⟨hne, ?_⟩
  have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b} : Finset Alt) →
      ∀ (y : Alt), y ∉ ({a, b} : Finset Alt) → (raisePair R a b i).lt x y := by
    intro i x hx y hy
    exact raise_mem_top (R i) {a, b} hx hy
  have hmem := winner_in_set F hSP hOnto (raisePair R a b) {a, b} a
    (Finset.mem_insert_self a {b}) htop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact h1
  · have hagree : ∀ i, (raisePair R a b i).lt a b := by
      intro i
      exact (raise_preserve_inside (R i) {a, b} (by simp) (by simp)).mpr (h i)
    exact absurd h1 (weakPareto F hSP hOnto (raisePair R a b) a b hagree)

/-- The induced SWF satisfies IIA: agreement on a pair determines the social
ranking of that pair, via monotonicity of the raised profiles. -/
private theorem socIIA {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R S : Profile Alt Voter) (a b : Alt) (hne : a ≠ b)
    (hag : ∀ i, ((R i).lt a b ↔ (S i).lt a b) ∧ ((R i).lt b a ↔ (S i).lt b a)) :
    (socOrder F hSP hOnto R).lt a b ↔ (socOrder F hSP hOnto S).lt a b := by
  change (a ≠ b ∧ F (raisePair R a b) = a) ↔ (a ≠ b ∧ F (raisePair S a b) = a)
  have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b} : Finset Alt) →
      ∀ (y : Alt), y ∉ ({a, b} : Finset Alt) → (raisePair R a b i).lt x y := by
    intro i x hx y hy
    exact raise_mem_top (R i) {a, b} hx hy
  have hmem := winner_in_set F hSP hOnto (raisePair R a b) {a, b} a
    (Finset.mem_insert_self a {b}) htop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hpres : ∀ (i : Voter) (d : Alt), (raisePair R a b i).lt (F (raisePair R a b)) d →
      (raisePair S a b i).lt (F (raisePair R a b)) d := by
    intro i d hd
    rcases hmem with hwa | hwb
    · rw [hwa] at hd ⊢
      by_cases hda : d = a
      · rw [hda] at hd
        exact absurd hd ((raisePair R a b i).irrefl a)
      · by_cases hdb : d = b
        · rw [hdb] at hd ⊢
          have e1 := (raise_preserve_inside (R i) {a, b} (by simp) (by simp)).mp hd
          have e2 := (hag i).1.mp e1
          exact (raise_preserve_inside (S i) {a, b} (by simp) (by simp)).mpr e2
        · have hdP : d ∉ ({a, b} : Finset Alt) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hda rfl
            · exact hdb rfl
          exact raise_mem_top (S i) {a, b} (by simp) hdP
    · rw [hwb] at hd ⊢
      by_cases hdb : d = b
      · rw [hdb] at hd
        exact absurd hd ((raisePair R a b i).irrefl b)
      · by_cases hda : d = a
        · rw [hda] at hd ⊢
          have e1 := (raise_preserve_inside (R i) {a, b} (by simp) (by simp)).mp hd
          have e2 := (hag i).2.mp e1
          exact (raise_preserve_inside (S i) {a, b} (by simp) (by simp)).mpr e2
        · have hdP : d ∉ ({a, b} : Finset Alt) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hda rfl
            · exact hdb rfl
          exact raise_mem_top (S i) {a, b} (by simp) hdP
  have hmono := mono_many F hSP (raisePair R a b) (raisePair S a b) hpres
  rw [hmono]

-- Arrow's dictatorship via the existing Arrow development (used for the Reny reduction).

/-- One-direction pair agreement determines the reverse comparison in a strict order. -/
private theorem pair_agree_two_of_one {Alt : Type*} (o₁ o₂ : StrictTotalOrder Alt)
    {a b : Alt} (hne : a ≠ b) (h : o₁.lt a b ↔ o₂.lt a b) :
    o₁.lt b a ↔ o₂.lt b a := by
  have l1 : o₁.lt b a ↔ ¬ o₁.lt a b :=
    ⟨fun h1 h2 => sto_asymm o₁ h2 h1, fun h1 => sto_gt_of_not_lt o₁ hne h1⟩
  have l2 : o₂.lt b a ↔ ¬ o₂.lt a b :=
    ⟨fun h1 h2 => sto_asymm o₂ h2 h1, fun h1 => sto_gt_of_not_lt o₂ hne h1⟩
  rw [l1, l2, h]

/-- The induced SWF satisfies Arrow's Pareto interface. -/
private theorem socPareto_arrow {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F) :
    ArrowWanted.IsPareto (socOrder F hSP hOnto) :=
  fun R a b h => socPareto F hSP hOnto R a b h

/-- The induced SWF satisfies Arrow's IIA interface. -/
private theorem socIIA_arrow {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F) :
    ArrowWanted.IsIIA (socOrder F hSP hOnto) := by
  intro R S a b hag
  by_cases hne : a = b
  · subst hne
    exact iff_of_false ((socOrder F hSP hOnto R).irrefl a)
      ((socOrder F hSP hOnto S).irrefl a)
  · exact socIIA F hSP hOnto R S a b hne
      (fun i => ⟨hag i, pair_agree_two_of_one (R i) (S i) hne (hag i)⟩)

/--
**Gibbard–Satterthwaite theorem, finiteness form.** Let the set of alternatives be finite and the
set of voters be finite and nonempty, and suppose there are at least three distinct alternatives.
Then every resolute social choice function on profiles of strict preference orders that is onto
and strategy-proof is dictatorial.

Source: A. Gibbard, Econometrica 41 (1973), 587-601, DOI 10.2307/1914083; M. A. Satterthwaite, J.
Econom. Theory 10 (1975), 187-217, DOI 10.1016/0022-0531(75)90050-2.
-/
theorem gibbard_satterthwaite_general
    {Alt Voter : Type*} [Finite Alt] [Finite Voter] [Nonempty Voter]
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (F : SocialChoiceFunction Alt Voter)
    (hOnto : IsOnto F) (hSP : IsStrategyProof F) :
    IsDictatorial F := by
  classical
  have := Fintype.ofFinite Alt
  have := Fintype.ofFinite Voter
  obtain ⟨d, hdict⟩ := ArrowWanted.arrow_impossibility_general hAlt (socOrder F hSP hOnto)
    (socPareto_arrow F hSP hOnto) (socIIA_arrow F hSP hOnto)
  refine ⟨d, fun R b hb => ?_⟩
  by_cases hdb : (R d).lt (F R) b
  · exact hdb
  · have hlt : (R d).lt b (F R) := sto_gt_of_not_lt (R d) (Ne.symm hb) hdb
    have hsoc : (socOrder F hSP hOnto R).lt b (F R) := hdict R b (F R) hlt
    obtain ⟨_, hFb⟩ := hsoc
    have hpres : ∀ (i : Voter) (c : Alt), (R i).lt (F R) c →
        (raisePair R b (F R) i).lt (F R) c := by
      intro i c hc
      by_cases hcb : c = b
      · rw [hcb] at hc ⊢
        exact (raise_preserve_inside (R i) {b, F R} (by simp) (by simp)).mpr hc
      · by_cases hcF : c = F R
        · rw [hcF] at hc
          exact absurd hc ((R i).irrefl (F R))
        · have hcP : c ∉ ({b, F R} : Finset Alt) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with h1 | h1
            · exact hcb h1
            · exact hcF h1
          exact raise_mem_top (R i) {b, F R} (by simp) hcP
    have hmono := mono_many F hSP R (raisePair R b (F R)) hpres
    have heq : b = F R := hFb.symm.trans hmono
    exact absurd heq hb

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/--
**Gibbard–Satterthwaite theorem.** Let the set of alternatives be finite and the set of voters be
finite and nonempty, and suppose there are at least three distinct alternatives. Then every
resolute social choice function on profiles of strict preference orders that is onto and
strategy-proof is dictatorial.

Proves `Wanted` entry `gibbard_satterthwaite`.

Source: A. Gibbard, Econometrica 41 (1973), 587-601, DOI 10.2307/1914083; M. A. Satterthwaite, J.
Econom. Theory 10 (1975), 187-217, DOI 10.1016/0022-0531(75)90050-2.
-/
theorem gibbard_satterthwaite
    {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (F : SocialChoiceFunction Alt Voter)
    (hOnto : IsOnto F) (hSP : IsStrategyProof F) :
    IsDictatorial F :=
  gibbard_satterthwaite_general hAlt F hOnto hSP

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
