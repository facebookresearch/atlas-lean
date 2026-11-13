/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

@[expose] public section


open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One attractor step for the reachability player (`owner v =
true`): add vertices that are already winning, reachability
vertices with a move into the set, and opponent vertices whose
every move lands in the set. -/
def attrStep (owner : V → Bool) (edge : V → Finset V)
    (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter (fun v =>
    (owner v ∧ ∃ w ∈ edge v, w ∈ S) ∨
      (¬ owner v ∧ ∀ w ∈ edge v, w ∈ S))

/-- The attractor iterates from the target set. -/
def attrLe (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) : ℕ → Finset V
  | 0 => T
  | k + 1 => attrStep owner edge (attrLe owner edge T k)

/-- The attractor: `Fintype.card V` iterates suffice. -/
def attr (owner : V → Bool) (edge : V → Finset V) (T : Finset V) :
    Finset V :=
  attrLe owner edge T (Fintype.card V)

private theorem attrStep_eq (owner : V → Bool) (edge : V → Finset V)
    (S : Finset V) :
    attrStep owner edge S = S ∪ Finset.univ.filter (fun v =>
      (owner v ∧ ∃ w ∈ edge v, w ∈ S) ∨
        (¬ owner v ∧ ∀ w ∈ edge v, w ∈ S)) := rfl

private theorem attrLe_zero_eq (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) : attrLe owner edge T 0 = T := by simp only [attrLe]

private theorem attrLe_succ_eq (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) (k : ℕ) :
    attrLe owner edge T (k + 1) =
      attrStep owner edge (attrLe owner edge T k) := by simp only [attrLe]

private theorem attr_eq_attrLe (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) :
    attr owner edge T = attrLe owner edge T (Fintype.card V) := rfl

private theorem mem_attrStep {owner : V → Bool} {edge : V → Finset V}
    {S : Finset V} {v : V} :
    v ∈ attrStep owner edge S ↔ v ∈ S ∨
      ((owner v ∧ ∃ w ∈ edge v, w ∈ S) ∨
        (¬ owner v ∧ ∀ w ∈ edge v, w ∈ S)) := by
  rw [attrStep_eq]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem mem_step_of_mem_succ_not_mem {owner : V → Bool}
    {edge : V → Finset V} {T : Finset V} {k : ℕ} {v : V}
    (hmem : v ∈ attrLe owner edge T (k + 1))
    (hnot : v ∉ attrLe owner edge T k) :
    (owner v ∧ ∃ w ∈ edge v, w ∈ attrLe owner edge T k) ∨
      (¬ owner v ∧ ∀ w ∈ edge v, w ∈ attrLe owner edge T k) := by
  rw [attrLe_succ_eq, mem_attrStep] at hmem
  rcases hmem with h | h
  · exact absurd h hnot
  · exact h

/-- The iterates grow. -/
theorem attrLe_succ_subset (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) (k : ℕ) :
    attrLe owner edge T k ⊆ attrLe owner edge T (k + 1) := by
  rw [attrLe_succ_eq, attrStep_eq]
  exact Finset.subset_union_left

/-- The iterates are monotone in the number of steps. -/
theorem attrLe_mono (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) {k l : ℕ} (h : k ≤ l) :
    attrLe owner edge T k ⊆ attrLe owner edge T l := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
    have hkd : k + (d + 1) = k + d + 1 := by omega
    rw [hkd]
    have h2 := attrLe_succ_subset owner edge T (k + d)
    intro x hx
    exact h2 (ih hx)

/-- The attractor is a fixed point of the attractor step. -/
theorem attrStep_attr (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) :
    attrStep owner edge (attr owner edge T) = attr owner edge T := by
  have hstep : attrLe owner edge T (Fintype.card V + 1)
      = attrStep owner edge (attrLe owner edge T (Fintype.card V)) :=
    attrLe_succ_eq _ _ _ _
  have hstab : attrLe owner edge T (Fintype.card V + 1)
      = attrLe owner edge T (Fintype.card V) := by
    have hex : ∃ k, k ≤ Fintype.card V ∧
        attrLe owner edge T (k + 1) = attrLe owner edge T k := by
      by_contra hcon
      have hne : ∀ k, k ≤ Fintype.card V →
          attrLe owner edge T (k + 1) ≠ attrLe owner edge T k := by
        intro k hk heq
        exact hcon ⟨k, hk, heq⟩
      have hstrict : ∀ k, k ≤ Fintype.card V →
          attrLe owner edge T k ⊂ attrLe owner edge T (k + 1) := by
        intro k hk
        have hsub := attrLe_succ_subset owner edge T k
        have hne' : attrLe owner edge T k ≠ attrLe owner edge T (k + 1) :=
          Ne.symm (hne k hk)
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩
      have hcard : ∀ k, k ≤ Fintype.card V + 1 →
          k ≤ (attrLe owner edge T k).card := by
        intro k
        induction k with
        | zero =>
          intro _
          exact Nat.zero_le _
        | succ k ih =>
          intro hk
          have hkN : k ≤ Fintype.card V := by omega
          have hlt := Finset.card_lt_card (hstrict k hkN)
          have hk1 : k ≤ Fintype.card V + 1 := by omega
          have ih' := ih hk1
          omega
      have hbig := hcard (Fintype.card V + 1) le_rfl
      have hsmall : (attrLe owner edge T (Fintype.card V + 1)).card
          ≤ Fintype.card V :=
        Finset.card_le_univ _
      omega
    obtain ⟨k, hk, hkk⟩ := hex
    have hstab_k : ∀ j, k ≤ j →
        attrLe owner edge T j = attrLe owner edge T k := by
      intro j hj
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      clear hj
      induction d with
      | zero => rfl
      | succ d ih =>
        have hkd : k + (d + 1) = k + d + 1 := by omega
        rw [hkd, attrLe_succ_eq, ih, ← attrLe_succ_eq]
        exact hkk
    have h1 := hstab_k (Fintype.card V + 1) (by omega : k ≤ Fintype.card V + 1)
    have h2 := hstab_k (Fintype.card V) hk
    rw [h1, h2]
  rw [hstep] at hstab
  exact hstab

/-- From an attractor vertex, the reachability player has a
positional strategy forcing the play to reach the target,
against any opponent play (on a total game). -/
theorem attr_reach (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) (hne : ∀ v, (edge v).Nonempty) {v : V}
    (hv : v ∈ attr owner edge T) :
    ∃ σ : V → V, (∀ w, σ w ∈ edge w) ∧
      ∀ p : ℕ → V, p 0 = v → (∀ k, p (k + 1) ∈ edge (p k)) →
        (∀ k, owner (p k) = true → p (k + 1) = σ (p k)) →
        ∃ k, p k ∈ T := by
  classical
  have hex1 : ∀ w : V, ∃ n : ℕ,
      (w ∈ attr owner edge T → w ∈ attrLe owner edge T n) ∧
        (w ∈ attr owner edge T →
          ∀ m, w ∈ attrLe owner edge T m → n ≤ m) := by
    intro w
    by_cases hw : w ∈ attr owner edge T
    · have hmemN : w ∈ attrLe owner edge T (Fintype.card V) := hw
      have hex : ∃ k, w ∈ attrLe owner edge T k := ⟨Fintype.card V, hmemN⟩
      exact ⟨Nat.find hex, fun _ => Nat.find_spec hex,
        fun _ m hm => Nat.find_min' hex hm⟩
    · exact ⟨0, fun h => absurd h hw, fun h => absurd h hw⟩
  choose rank hrank using hex1
  have hrankmem : ∀ w, w ∈ attr owner edge T →
      w ∈ attrLe owner edge T (rank w) :=
    fun w hw => (hrank w).1 hw
  have hrankmin : ∀ w, w ∈ attr owner edge T →
      ∀ m, w ∈ attrLe owner edge T m → rank w ≤ m :=
    fun w hw m hm => (hrank w).2 hw m hm
  have huT_of : ∀ u, u ∈ attr owner edge T → rank u = 0 → u ∈ T := by
    intro u hu hr0
    have hmem0 : u ∈ attrLe owner edge T 0 := by
      have h := hrankmem u hu
      rw [hr0] at h
      exact h
    rw [attrLe_zero_eq] at hmem0
    exact hmem0
  have hstrat : ∀ w, ∃ u, u ∈ edge w ∧
      (owner w = true → w ∈ attr owner edge T → rank w ≠ 0 →
        u ∈ attr owner edge T ∧ rank u < rank w) := by
    intro w
    by_cases hw : owner w = true ∧ w ∈ attr owner edge T ∧ rank w ≠ 0
    · obtain ⟨hown, hmem, hrankne⟩ := hw
      obtain ⟨k, hk⟩ : ∃ k, rank w = k + 1 := ⟨rank w - 1, by omega⟩
      have hmemk1 : w ∈ attrLe owner edge T (k + 1) := by
        rw [← hk]
        exact hrankmem w hmem
      have hnotk : w ∉ attrLe owner edge T k := by
        intro hcon
        have hle := hrankmin w hmem k hcon
        omega
      have hstep := mem_step_of_mem_succ_not_mem hmemk1 hnotk
      rcases hstep with ⟨hup, u, humem, huk⟩ | ⟨hdown, _⟩
      · have hmemN : w ∈ attrLe owner edge T (Fintype.card V) := hmem
        have hrN : rank w ≤ Fintype.card V := hrankmin w hmem _ hmemN
        have hkN : k ≤ Fintype.card V := by omega
        have huN : u ∈ attrLe owner edge T (Fintype.card V) :=
          attrLe_mono _ _ _ hkN huk
        have huattr : u ∈ attr owner edge T := huN
        have hle : rank u ≤ k := hrankmin u huattr k huk
        refine ⟨u, humem, fun _ _ _ => ⟨huattr, by omega⟩⟩
      · have hup' : owner w := hown
        exact absurd hup' hdown
    · obtain ⟨u, hu⟩ := hne w
      exact ⟨u, hu, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hw⟩
  choose σ hσ using hstrat
  have hplay : ∀ (n : ℕ) (u : V) (p : ℕ → V), u ∈ attr owner edge T →
      rank u ≤ n → p 0 = u → (∀ k, p (k + 1) ∈ edge (p k)) →
      (∀ k, owner (p k) = true → p (k + 1) = σ (p k)) →
      ∃ k, p k ∈ T := by
    intro n
    induction n with
    | zero =>
      intro u p hu hrank0 hp0 hmem hstrat'
      have h0 : rank u = 0 := le_antisymm hrank0 (Nat.zero_le _)
      have huT : u ∈ T := huT_of u hu h0
      refine ⟨0, ?_⟩
      rw [hp0]
      exact huT
    | succ n ih =>
      intro u p hu hrun hp0 hmem hstrat'
      by_cases hr0 : rank u = 0
      · have huT : u ∈ T := huT_of u hu hr0
        refine ⟨0, ?_⟩
        rw [hp0]
        exact huT
      · obtain ⟨k, hk⟩ : ∃ k, rank u = k + 1 := ⟨rank u - 1, by omega⟩
        have hmemk1 : u ∈ attrLe owner edge T (k + 1) := by
          rw [← hk]
          exact hrankmem u hu
        have hnotk : u ∉ attrLe owner edge T k := by
          intro hcon
          have hle := hrankmin u hu k hcon
          omega
        have hmemN : u ∈ attrLe owner edge T (Fintype.card V) := hu
        have hrN : rank u ≤ Fintype.card V := hrankmin u hu _ hmemN
        have hkN : k ≤ Fintype.card V := by omega
        have h01 : p (0 + 1) ∈ edge u := by
          have h := hmem 0
          rw [hp0] at h
          exact h
        have hnext : p (0 + 1) ∈ attr owner edge T ∧
            rank (p (0 + 1)) < rank u := by
          cases hbk : owner u
          · have hstep := mem_step_of_mem_succ_not_mem hmemk1 hnotk
            have hdown : ¬ owner u := by
              intro hup
              have hcontra : owner u = true := hup
              rw [hbk] at hcontra
              exact absurd hcontra (by decide)
            have hall : ∀ w ∈ edge u, w ∈ attrLe owner edge T k := by
              rcases hstep with ⟨hup, _⟩ | ⟨_, hall⟩
              · exact absurd hup hdown
              · exact hall
            have hpk1 : p (0 + 1) ∈ attrLe owner edge T k := hall _ h01
            have hpkN : p (0 + 1) ∈ attrLe owner edge T (Fintype.card V) :=
              attrLe_mono _ _ _ hkN hpk1
            have hpkattr : p (0 + 1) ∈ attr owner edge T := hpkN
            have hle : rank (p (0 + 1)) ≤ k := hrankmin _ hpkattr k hpk1
            exact ⟨hpkattr, by omega⟩
          · have hown : owner u = true := hbk
            have h0 : owner (p 0) = true := by rw [hp0]; exact hown
            have hfol : p (0 + 1) = σ u := by
              have h := hstrat' 0 h0
              rw [hp0] at h
              exact h
            have hσres := (hσ u).2 hown hu hr0
            rw [hfol]
            exact hσres
        obtain ⟨hnext_attr, hnext_lt⟩ := hnext
        have hnext_le : rank (p (0 + 1)) ≤ n := by omega
        obtain ⟨j, hjT⟩ := ih (p (0 + 1)) (fun k => p (k + 1)) hnext_attr
          hnext_le rfl (fun k => hmem (k + 1))
          (fun k hkok => hstrat' (k + 1) hkok)
        exact ⟨j + 1, hjT⟩
  refine ⟨σ, fun w => (hσ w).1, fun p hp0 hmem hstrat' => ?_⟩
  exact hplay (rank v) v p hv le_rfl hp0 hmem hstrat'

/-- From outside the attractor, the opponent has a positional
strategy keeping the play outside the target forever. -/
theorem attr_safe (owner : V → Bool) (edge : V → Finset V)
    (T : Finset V) (hne : ∀ v, (edge v).Nonempty) {v : V}
    (hv : v ∉ attr owner edge T) :
    ∃ τ : V → V, (∀ w, τ w ∈ edge w) ∧
      ∀ p : ℕ → V, p 0 = v → (∀ k, p (k + 1) ∈ edge (p k)) →
        (∀ k, owner (p k) = false → p (k + 1) = τ (p k)) →
        ∀ k, p k ∉ T := by
  classical
  have hTsub : T ⊆ attr owner edge T := by
    rw [attr_eq_attrLe]
    have hsub : attrLe owner edge T 0 ⊆ attrLe owner edge T (Fintype.card V) :=
      attrLe_mono _ _ _ (Nat.zero_le _)
    rw [attrLe_zero_eq] at hsub
    exact hsub
  have hclosed : ∀ u, u ∉ attr owner edge T →
      (owner u = true → ∀ w ∈ edge u, w ∉ attr owner edge T) ∧
      (owner u = false → ∃ w ∈ edge u, w ∉ attr owner edge T) := by
    intro u hu
    have hfix := attrStep_attr owner edge T
    have hnotin : u ∉ attrStep owner edge (attr owner edge T) := by
      rw [hfix]
      exact hu
    rw [mem_attrStep] at hnotin
    have hdisj : ¬ ((owner u ∧ ∃ w ∈ edge u, w ∈ attr owner edge T) ∨
        (¬ owner u ∧ ∀ w ∈ edge u, w ∈ attr owner edge T)) := by
      intro h
      exact hnotin (Or.inr h)
    constructor
    · intro hown w hwmem hwin
      have hup : owner u := hown
      exact hdisj (Or.inl ⟨hup, w, hwmem, hwin⟩)
    · intro hown
      by_contra hcon
      have hall : ∀ w ∈ edge u, w ∈ attr owner edge T := by
        intro w hwmem
        by_contra hwnot
        exact hcon ⟨w, hwmem, hwnot⟩
      have hdown : ¬ owner u := by
        intro hup
        have hcontra : owner u = true := hup
        rw [hown] at hcontra
        exact absurd hcontra (by decide)
      exact hdisj (Or.inr ⟨hdown, hall⟩)
  have hstrat : ∀ w, ∃ u, u ∈ edge w ∧
      (owner w = false → w ∉ attr owner edge T → u ∉ attr owner edge T) := by
    intro w
    by_cases hw : owner w = false ∧ w ∉ attr owner edge T
    · obtain ⟨u, humem, hunot⟩ := (hclosed w hw.2).2 hw.1
      exact ⟨u, humem, fun _ _ => hunot⟩
    · obtain ⟨u, hu⟩ := hne w
      exact ⟨u, hu, fun h1 h2 => absurd ⟨h1, h2⟩ hw⟩
  choose τ hτ using hstrat
  refine ⟨τ, fun w => (hτ w).1, fun p hp0 hmem hstrat' k => ?_⟩
  have hout : ∀ k, p k ∉ attr owner edge T := by
    intro k
    induction k with
    | zero =>
      rw [hp0]
      exact hv
    | succ k ih =>
      have hpk : p k ∉ attr owner edge T := ih
      cases hbk : owner (p k)
      · have hfol : p (k + 1) = τ (p k) := hstrat' k hbk
        rw [hfol]
        exact (hτ (p k)).2 hbk hpk
      · exact (hclosed (p k) hpk).1 hbk (p (k + 1)) (hmem k)
  exact fun hTin => hout k (hTsub hTin)
