/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.Backtracking
public import Mathlib.Data.Fintype.Pi

/-!
# Backtracking with forward checking: enumerating all solutions

Haralick and Elliott (*Increasing tree search efficiency for constraint satisfaction problems*,
Artificial Intelligence 14 (1980), p. 264) pose the constraint satisfaction problem as finding all
assignments of labels to units that satisfy the constraints; their tree search (Fig. 3(a), with
forward checking as in Section 2.3) outputs every consistent labeling it reaches. `enumerateFC` is
that variant of `backtrackFC`: the same variable and value orders, forward check and wipeout test,
with every value of the picked variable explored instead of stopping at the first success.

Main results, for every search order:

* `toFinset_enumerateFC`: the listed assignments are exactly the solutions within the domains
  (`solutionFinset`).
* `nodup_enumerateFC`: each solution is listed once when the value order has no repeats, as for
  `SearchOrder.ofLinearOrder` and `SearchOrder.mrv`; then `length_enumerateFC` counts solutions.
* `backtrackFC_eq_head?_enumerateFC`: `backtrackFC` returns the first listed solution.

## Cost model

Nothing is charged: `searchEnum` and `enumerateFC` are plain functions, not `TimeM` programs, and
no bound on the number of search nodes or consistency checks is claimed. Haralick and Elliott
measure these searches by consistency checks and tree nodes (Section 3); those counts are not
formalized here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ArcConsistency

variable {X D : Type*} [DecidableEq X] [DecidableEq D] (P : BinaryCSP X D)

/-- Being a solution within finite domains is decidable when there are finitely many
variables. -/
instance decidableIsSolution [Fintype X] (dom : X → Finset D) :
    DecidablePred (IsSolution P dom) := fun σ =>
  inferInstanceAs (Decidable ((∀ x, σ x ∈ dom x) ∧
    ∀ e ∈ P.arcs, P.allowed e.1 e.2 (σ e.1) (σ e.2) = true))

/-- **Solutions of a binary CSP as a finset.** For a binary constraint satisfaction problem $P$
with finitely many variables and finite domains $\mathrm{dom}$, the finset of the solutions of $P$
within $\mathrm{dom}$, taken among the assignments $\sigma$ with $\sigma(x) \in \mathrm{dom}(x)$
for every variable $x$. -/
def solutionFinset [Fintype X] (dom : X → Finset D) : Finset (X → D) :=
  (Fintype.piFinset dom).filter (IsSolution P dom)

theorem mem_solutionFinset [Fintype X] {dom : X → Finset D} {σ : X → D} :
    σ ∈ solutionFinset P dom ↔ IsSolution P dom σ := by
  unfold solutionFinset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨h.1, h⟩

end Cslib.Algorithms.Lean.ArcConsistency

namespace Cslib.Algorithms.Lean.CSPBacktracking

open Cslib.Algorithms.Lean.ArcConsistency

variable {X D : Type*} [DecidableEq X] (P : BinaryCSP X D)

/-- The search of `search`, with fuel `n`, current domains `dom`, partial assignment `asg` and
unassigned variables `U`, listing every assignment it reaches: the values of the picked variable
are all explored and their results concatenated (`List.flatMap`), where `search` stops at the
first success (`List.findSome?`). -/
def searchEnum [Fintype X] (O : SearchOrder X D) :
    ℕ → (X → Finset D) → (X → Option D) → Finset X → List (X → D)
  | 0, _, asg, _ => (toTotal asg).toList
  | n + 1, dom, asg, U =>
      if hU : U.Nonempty then
        (O.vals dom (O.pick dom U hU)).flatMap fun a =>
          if compat P (O.pick dom U hU) a (O.pick dom U hU) a = true ∧
              ∀ y ∈ U.erase (O.pick dom U hU),
                (forwardCheck P dom (O.pick dom U hU) a y).Nonempty then
            searchEnum O n (forwardCheck P dom (O.pick dom U hU) a)
              (Function.update asg (O.pick dom U hU) (some a)) (U.erase (O.pick dom U hU))
          else []
      else (toTotal asg).toList

/-- **Enumeration by backtracking with forward checking** from the domains `dom`, all variables
unassigned: the assignments that `backtrackFC` could return, in the order the search reaches
them. -/
def enumerateFC [Fintype X] (O : SearchOrder X D) (dom : X → Finset D) : List (X → D) :=
  searchEnum P O (Fintype.card X) dom (fun _ => none) Finset.univ

/-- `search` returns the first assignment that `searchEnum` lists. -/
theorem search_eq_head?_searchEnum [Fintype X] (O : SearchOrder X D) :
    ∀ (n : ℕ) (dom : X → Finset D) (asg : X → Option D) (U : Finset X),
      search P O n dom asg U = (searchEnum P O n dom asg U).head? := by
  intro n dom asg U
  induction n generalizing dom asg U with
  | zero =>
    simp only [search, searchEnum, Option.head?_toList]
  | succ n ih =>
    simp only [search, searchEnum]
    by_cases hU : U.Nonempty
    · rw [dite_eq_left hU, dite_eq_left hU, List.head?_flatMap]
      congr 1
      funext a
      by_cases hc : compat P (O.pick dom U hU) a (O.pick dom U hU) a = true ∧
          ∀ y ∈ U.erase (O.pick dom U hU),
            (forwardCheck P dom (O.pick dom U hU) a y).Nonempty
      · rw [ite_eq_left hc, ite_eq_left hc]
        exact ih _ _ _
      · rw [ite_eq_right hc, ite_eq_right hc, List.head?_nil]
    · rw [dite_eq_right hU, dite_eq_right hU, Option.head?_toList]

/-- **Backtracking returns the first enumerated assignment.** -/
theorem backtrackFC_eq_head?_enumerateFC [Fintype X] (O : SearchOrder X D)
    (dom : X → Finset D) : backtrackFC P O dom = (enumerateFC P O dom).head? := by
  unfold backtrackFC enumerateFC
  exact search_eq_head?_searchEnum P O _ _ _ _

private theorem cs_aux_a_soundInv_total {X D : Type*} [DecidableEq X] [Fintype X]
    (P : BinaryCSP X D) (dom₀ dom : X → Finset D) (asg : X → Option D)
    (τ : X → D) (hI : SoundInv P dom₀ dom asg) (h : toTotal asg = some τ) :
    IsSolution P dom₀ τ := by
  constructor
  · intro x
    exact hI.mem x (τ x) (toTotal_eq_some h x)
  · intro e he
    obtain ⟨u, v⟩ := e
    exact allowed_of_compat P
      (hI.pair u (τ u) v (τ v) (toTotal_eq_some h u) (toTotal_eq_some h v)) he

private theorem cs_aux_a_mem_toTotal {X D : Type*} [Fintype X] (asg : X → Option D)
    (τ : X → D) (h : ∀ y, asg y = some (τ y)) : τ ∈ (toTotal asg).toList := by
  rw [Option.mem_toList]
  cases hto : toTotal asg with
  | none =>
    have hsome : ∀ x, (asg x).isSome = true := fun x => by simp [h x]
    simp only [toTotal] at hto
    rw [dite_eq_left hsome] at hto
    simp at hto
  | some σ =>
    have hfun : ∀ x, σ x = τ x := fun x => by
      have h1 := toTotal_eq_some hto x
      have h2 := h x
      rw [h1] at h2
      exact Option.some_inj.mp h2
    have hστ : σ = τ := funext hfun
    rw [hστ]

/-- Every assignment that `searchEnum` lists from a state satisfying the soundness invariant is a
solution within the input domains. -/
theorem searchEnum_sound [Fintype X] (O : SearchOrder X D) (dom₀ : X → Finset D) :
    ∀ (n : ℕ) (dom : X → Finset D) (asg : X → Option D) (U : Finset X) (σ : X → D),
      SoundInv P dom₀ dom asg → σ ∈ searchEnum P O n dom asg U → IsSolution P dom₀ σ := by
  intro n dom asg U
  induction n generalizing dom asg U with
  | zero =>
    intro σ hI hmem
    simp only [searchEnum] at hmem
    rw [Option.mem_toList] at hmem
    exact cs_aux_a_soundInv_total P dom₀ dom asg σ hI hmem
  | succ n ih =>
    intro σ hI hmem
    simp only [searchEnum] at hmem
    by_cases hU : U.Nonempty
    · rw [dite_eq_left hU, List.mem_flatMap] at hmem
      obtain ⟨a, hax, hmem2⟩ := hmem
      by_cases hc : compat P (O.pick dom U hU) a (O.pick dom U hU) a = true ∧
          ∀ y ∈ U.erase (O.pick dom U hU),
            (forwardCheck P dom (O.pick dom U hU) a y).Nonempty
      · rw [ite_eq_left hc] at hmem2
        exact ih _ _ _ _ (soundInv_step P hI ((O.mem_vals dom _ _).mp hax) hc.1) hmem2
      · rw [ite_eq_right hc] at hmem2
        simp at hmem2
    · rw [dite_eq_right hU, Option.mem_toList] at hmem
      exact cs_aux_a_soundInv_total P dom₀ dom asg σ hI hmem

/-- A solution within the current domains that agrees with the partial assignment outside the
unassigned variables is listed, given enough fuel. -/
theorem searchEnum_complete [Fintype X] (O : SearchOrder X D) (τ : X → D) :
    ∀ (n : ℕ) (dom : X → Finset D) (asg : X → Option D) (U : Finset X),
      U.card ≤ n → IsSolution P dom τ → (∀ y ∉ U, asg y = some (τ y)) →
        τ ∈ searchEnum P O n dom asg U := by
  intro n dom asg U
  induction n generalizing dom asg U with
  | zero =>
    intro hcard hσ hag
    simp only [searchEnum]
    have hUe : U = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    have hall : ∀ y, asg y = some (τ y) := fun y => hag y (by simp [hUe])
    exact cs_aux_a_mem_toTotal asg τ hall
  | succ n ih =>
    intro hcard hσ hag
    simp only [searchEnum]
    by_cases hU : U.Nonempty
    · rw [dite_eq_left hU]
      have hfc : IsSolution P
          (forwardCheck P dom (O.pick dom U hU) (τ (O.pick dom U hU))) τ :=
        isSolution_forwardCheck P hσ _
      have hmem : τ (O.pick dom U hU) ∈ O.vals dom (O.pick dom U hU) :=
        (O.mem_vals dom _ _).mpr (hσ.1 _)
      have hcond : compat P (O.pick dom U hU) (τ (O.pick dom U hU))
          (O.pick dom U hU) (τ (O.pick dom U hU)) = true ∧
          ∀ y ∈ U.erase (O.pick dom U hU),
            (forwardCheck P dom (O.pick dom U hU) (τ (O.pick dom U hU)) y).Nonempty :=
        ⟨compat_of_isSolution P hσ _ _, fun y _ => ⟨τ y, hfc.1 y⟩⟩
      have hcard' : (U.erase (O.pick dom U hU)).card ≤ n := by
        rw [Finset.card_erase_of_mem (O.pick_mem dom U hU)]
        omega
      have hag' : ∀ y ∉ U.erase (O.pick dom U hU),
          Function.update asg (O.pick dom U hU) (some (τ (O.pick dom U hU))) y =
            some (τ y) := by
        intro y hy
        by_cases hyx : y = O.pick dom U hU
        · subst hyx
          exact Function.update_self _ _ _
        · rw [Function.update_of_ne hyx]
          apply hag
          intro hyU
          exact hy (Finset.mem_erase.mpr ⟨hyx, hyU⟩)
      refine List.mem_flatMap_of_mem hmem ?_
      simp only [ite_eq_left hcond]
      exact ih _ _ _ hcard' hfc hag'
    · rw [dite_eq_right hU]
      have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      have hall : ∀ y, asg y = some (τ y) := fun y => hag y (by simp [hUe])
      exact cs_aux_a_mem_toTotal asg τ hall

/-- **Soundness of the enumeration**: every listed assignment is a solution within the
domains. -/
theorem isSolution_of_mem_enumerateFC [Fintype X] (O : SearchOrder X D) {dom : X → Finset D}
    {σ : X → D} (h : σ ∈ enumerateFC P O dom) : IsSolution P dom σ := by
  unfold enumerateFC at h
  exact searchEnum_sound P O dom _ _ _ _ _ (soundInv_init P dom) h

/-- **Completeness of the enumeration**: every solution within the domains is listed. -/
theorem mem_enumerateFC_of_isSolution [Fintype X] (O : SearchOrder X D) {dom : X → Finset D}
    {σ : X → D} (hσ : IsSolution P dom σ) : σ ∈ enumerateFC P O dom := by
  have hcard : (Finset.univ : Finset X).card ≤ Fintype.card X := by simp
  have hag : ∀ y ∉ (Finset.univ : Finset X), (fun _ : X => none) y = some (σ y) := by
    intro y hy
    exact absurd (Finset.mem_univ y) hy
  unfold enumerateFC
  exact searchEnum_complete P O σ _ _ _ _ hcard hσ hag

/-- An assignment is listed iff it is a solution within the domains, for every search order. -/
theorem mem_enumerateFC [Fintype X] (O : SearchOrder X D) {dom : X → Finset D} {σ : X → D} :
    σ ∈ enumerateFC P O dom ↔ IsSolution P dom σ := by
  constructor
  · intro h
    exact isSolution_of_mem_enumerateFC P O h
  · intro h
    exact mem_enumerateFC_of_isSolution P O h

/-- **The enumeration equals the solution finset.** For a binary constraint satisfaction problem
$P$ with finitely many variables, every search order and finite domains $\mathrm{dom}$, the set of
assignments listed by backtracking with forward checking is the finset of solutions of $P$ within
$\mathrm{dom}$. -/
theorem toFinset_enumerateFC [Fintype X] [DecidableEq D] (O : SearchOrder X D)
    (dom : X → Finset D) : (enumerateFC P O dom).toFinset = solutionFinset P dom := by
  ext σ
  simp only [List.mem_toFinset, mem_enumerateFC P O, mem_solutionFinset P]

/-- A listed assignment extends the partial assignment it was reached from, when the unassigned
variables are exactly unassigned. -/
theorem eq_of_mem_searchEnum [Fintype X] (O : SearchOrder X D) :
    ∀ (n : ℕ) (dom : X → Finset D) (asg : X → Option D) (U : Finset X) (σ : X → D),
      (∀ y ∈ U, asg y = none) → σ ∈ searchEnum P O n dom asg U →
        ∀ y a, asg y = some a → σ y = a := by
  intro n
  induction n with
  | zero =>
      intro dom asg U σ _ hmem y a hasg
      simp only [searchEnum, Option.mem_toList] at hmem
      have h2 := toTotal_eq_some hmem y
      rw [hasg] at h2
      simpa using h2.symm
  | succ n ih =>
      intro dom asg U σ hU hmem y a hasg
      by_cases hUN : U.Nonempty
      · simp only [searchEnum, dite_eq_left hUN] at hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨a', _, hmem'⟩ := hmem
        split at hmem'
        · have hxU : O.pick dom U hUN ∈ U := O.pick_mem dom U hUN
          have hU' : ∀ z ∈ U.erase (O.pick dom U hUN),
              Function.update asg (O.pick dom U hUN) (some a') z = none := by
            intro z hz
            rw [Finset.mem_erase] at hz
            rw [Function.update_of_ne hz.1 _ _]
            exact hU z hz.2
          have hyU : y ∉ U := by
            intro hy
            rw [hU y hy] at hasg
            cases hasg
          have hyx : y ≠ O.pick dom U hUN := by
            intro h
            subst h
            exact hyU hxU
          have hasg' : Function.update asg (O.pick dom U hUN) (some a') y = some a := by
            rw [Function.update_of_ne hyx _ _]
            exact hasg
          exact ih _ _ _ _ hU' hmem' y a hasg'
        · simp at hmem'
      · simp only [searchEnum, dite_eq_right hUN] at hmem
        simp only [Option.mem_toList] at hmem
        have h2 := toTotal_eq_some hmem y
        rw [hasg] at h2
        simpa using h2.symm

/-- `searchEnum` lists no assignment twice when the value order has no repeats. -/
theorem nodup_searchEnum [Fintype X] (O : SearchOrder X D)
    (hO : ∀ dom x, (O.vals dom x).Nodup) :
    ∀ (n : ℕ) (dom : X → Finset D) (asg : X → Option D) (U : Finset X),
      (∀ y ∈ U, asg y = none) → (searchEnum P O n dom asg U).Nodup := by
  intro n
  induction n with
  | zero =>
      intro dom asg U _
      simp only [searchEnum]
      cases toTotal asg with
      | none => exact List.nodup_nil
      | some σ => exact List.nodup_singleton σ
  | succ n ih =>
      intro dom asg U hU
      by_cases hUN : U.Nonempty
      · simp only [searchEnum, dite_eq_left hUN]
        rw [List.nodup_flatMap]
        constructor
        · intro a _
          split
          · apply ih
            intro z hz
            rw [Finset.mem_erase] at hz
            rw [Function.update_of_ne hz.1 _ _]
            exact hU z hz.2
          · exact List.nodup_nil
        · apply List.Nodup.pairwise_of_forall_ne (hO dom (O.pick dom U hUN))
          intro u _ v _ huv
          change List.Disjoint _ _
          rw [List.disjoint_left]
          intro σ hσu hσv
          beta_reduce at hσu hσv
          split at hσu
          · split at hσv
            · have hU'u : ∀ z ∈ U.erase (O.pick dom U hUN),
                  Function.update asg (O.pick dom U hUN) (some u) z = none := by
                intro z hz
                rw [Finset.mem_erase] at hz
                rw [Function.update_of_ne hz.1 _ _]
                exact hU z hz.2
              have hU'v : ∀ z ∈ U.erase (O.pick dom U hUN),
                  Function.update asg (O.pick dom U hUN) (some v) z = none := by
                intro z hz
                rw [Finset.mem_erase] at hz
                rw [Function.update_of_ne hz.1 _ _]
                exact hU z hz.2
              have ea : σ (O.pick dom U hUN) = u :=
                eq_of_mem_searchEnum P O n _ _ _ _ hU'u hσu _ _
                  (Function.update_self (O.pick dom U hUN) (some u) asg)
              have eb : σ (O.pick dom U hUN) = v :=
                eq_of_mem_searchEnum P O n _ _ _ _ hU'v hσv _ _
                  (Function.update_self (O.pick dom U hUN) (some v) asg)
              exact huv (ea.symm.trans eb)
            · simp at hσv
          · simp at hσu
      · simp only [searchEnum, dite_eq_right hUN]
        cases toTotal asg with
        | none => exact List.nodup_nil
        | some σ => exact List.nodup_singleton σ

/-- **Each solution is listed once** when the search order lists the values of each domain without
repeats. -/
theorem nodup_enumerateFC [Fintype X] (O : SearchOrder X D)
    (hO : ∀ dom x, (O.vals dom x).Nodup) (dom : X → Finset D) :
    (enumerateFC P O dom).Nodup := by
  unfold enumerateFC
  exact nodup_searchEnum P O hO _ _ _ _ (fun y _ => rfl)

/-- **The enumeration counts the solutions** when the value order has no repeats. -/
theorem length_enumerateFC [Fintype X] [DecidableEq D] (O : SearchOrder X D)
    (hO : ∀ dom x, (O.vals dom x).Nodup) (dom : X → Finset D) :
    (enumerateFC P O dom).length = (solutionFinset P dom).card := by
  have hnd := nodup_enumerateFC P O hO dom
  have htf := toFinset_enumerateFC P O dom
  have hcard := List.toFinset_card_of_nodup hnd
  rw [htf] at hcard
  exact hcard.symm

theorem mem_of_mem_ascending {α : Type*} [LinearOrder α] :
    ∀ (n : ℕ) (s : Finset α) (a : α), a ∈ ascending n s → a ∈ s := by
  intro n
  induction n with
  | zero =>
    intro s a h
    simp [ascending] at h
  | succ n ih =>
    intro s a h
    simp only [ascending] at h
    split_ifs at h with hs
    · rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact Finset.min'_mem _ hs
      · exact Finset.mem_of_mem_erase (ih _ _ h)
    · simp at h

theorem nodup_ascending {α : Type*} [LinearOrder α] (n : ℕ) (s : Finset α) :
    (ascending n s).Nodup := by
  induction n generalizing s with
  | zero => simp [ascending]
  | succ n ih =>
    simp only [ascending]
    split_ifs with hs
    · refine List.Nodup.cons ?_ (ih _)
      intro hmem
      have hmem2 := mem_of_mem_ascending n _ _ hmem
      simp at hmem2
    · exact List.nodup_nil

theorem SearchOrder.nodup_vals_ofLinearOrder {X D : Type*} [LinearOrder X] [LinearOrder D]
    (dom : X → Finset D) (x : X) :
    ((SearchOrder.ofLinearOrder : SearchOrder X D).vals dom x).Nodup :=
  nodup_ascending _ _

theorem SearchOrder.nodup_vals_mrv {X D : Type*} [LinearOrder X] [LinearOrder D]
    (dom : X → Finset D) (x : X) :
    ((SearchOrder.mrv : SearchOrder X D).vals dom x).Nodup :=
  nodup_ascending _ _

end Cslib.Algorithms.Lean.CSPBacktracking
