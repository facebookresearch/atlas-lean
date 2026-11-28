/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Automata.Transducers.Sequential

/-!
# Characterization sets of Mealy machines

Two states `q` and `q'` of a Mealy machine `M` are equivalent when `M.runOut q w = M.runOut q' w`
for every input word `w`. A characterization set of `M` is a finite set `W` of input words that
contains the empty word and such that any two states whose output words agree on every word of
`W` are equivalent. Characterization sets are the `W` of the W-method of Vasilevskii and Chow.

Kocsis and Rot (*Complete test suites for automata in monoidal closed categories*,
arXiv:2411.13412v2) define characterization sets for DFAs (Definition 2.3). In their instance
for Mealy machines (Section 5.1), the observation at an input word `w` is a function of the next
input letter `a`: it is the output of the last transition of the run on `w ++ [a]`, not on `w`,
so at the empty word it observes the output of the first transition on each letter. Section 5.1
contrasts this with the traditional extension of the output function to words, which records
every output of the run on `w`, as `runOut` does; the definition here uses the traditional
extension.

## Main results

* `MealyMachine.exists_characterization_set`: a Mealy machine with `n` states has a
  characterization set all of whose words have length at most `n - 1`.

## Implementation notes

Call two states `k`-equivalent when their output words agree on every input word of length at
most `k`. The number of `k`-equivalence classes is counted as the number of distinct functions
sending a word of length at most `k` to its output word (and every longer word to `none`). It
is at most `n`, it is `1` for `k = 0`, it does not decrease with `k`, and once two consecutive
levels have the same number of classes, every later level has the same classes. So
`(n - 1)`-equivalence is equivalence, and choosing one separating word of length at most
`n - 1` for each pair of inequivalent states, together with the empty word, gives the set.
Minimality of the machine is not needed.
-/

@[expose] public section

namespace Cslib.Automata.MealyMachine

variable {State In Out : Type*}

/-- `k`-equivalence of states: agreement on every input word of length at most `k`. -/
private def KEquiv (M : MealyMachine State In Out) (k : ℕ) (q q' : State) : Prop :=
  ∀ w : List In, w.length ≤ k → M.runOut q w = M.runOut q' w

/-- The output words of `q` on the input words of length at most `k`, and `none` on longer
words; two states are `k`-equivalent exactly when these functions agree. -/
private def sig (M : MealyMachine State In Out) (k : ℕ) (q : State) :
    List In → Option (List Out) :=
  fun w => if w.length ≤ k then some (M.runOut q w) else none

private theorem kEquiv_iff_sig_eq (M : MealyMachine State In Out) (k : ℕ) (q q' : State) :
    KEquiv M k q q' ↔ sig M k q = sig M k q' := by
  constructor
  · intro h
    funext w
    by_cases hw : w.length ≤ k
    · simp only [sig, ite_eq_left hw, h w hw]
    · simp only [sig, ite_eq_right hw]
  · intro h w hw
    have := congrFun h w
    simpa only [sig, ite_eq_left hw, Option.some.injEq] using this

/-- States are `(k + 1)`-equivalent exactly when they give the same output on every input
letter and their successors on it are `k`-equivalent. -/
private theorem kEquiv_succ_iff (M : MealyMachine State In Out) (k : ℕ) (q q' : State) :
    KEquiv M (k + 1) q q' ↔
      ∀ a, (M.step q a).2 = (M.step q' a).2 ∧ KEquiv M k (M.step q a).1 (M.step q' a).1 := by
  constructor
  · intro h a
    refine ⟨?_, fun w hw => ?_⟩
    · have := h [a] (by simp)
      rw [runOut_cons, runOut_cons] at this
      exact (List.cons.inj this).1
    · have := h (a :: w) (by simpa using hw)
      rw [runOut_cons, runOut_cons] at this
      exact (List.cons.inj this).2
  · intro h w hw
    cases w with
    | nil => rfl
    | cons a w =>
      rw [runOut_cons, runOut_cons, (h a).1, (h a).2 w (by simpa using hw)]

/-- If `k`-equivalence implies `(k + 1)`-equivalence, then `k`-equivalence implies
equivalence. -/
private theorem runOut_eq_of_kEquiv_of_stable (M : MealyMachine State In Out) (k : ℕ)
    (hk : ∀ q q', KEquiv M k q q' → KEquiv M (k + 1) q q') {q q' : State}
    (h : KEquiv M k q q') (w : List In) : M.runOut q w = M.runOut q' w := by
  have step : ∀ j, ∀ q q', KEquiv M (k + j) q q' → KEquiv M (k + j + 1) q q' := by
    intro j
    induction j with
    | zero => exact hk
    | succ j ih =>
      intro q q' hq
      rw [show k + (j + 1) + 1 = (k + j + 1) + 1 by omega, kEquiv_succ_iff]
      rw [show k + (j + 1) = (k + j) + 1 by omega, kEquiv_succ_iff] at hq
      exact fun a => ⟨(hq a).1, ih _ _ (hq a).2⟩
  have up : ∀ j, KEquiv M (k + j) q q' := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih => exact step j q q' ih
  exact up w.length w (by omega)

/-- Agreement on every input word of length at most `n - 1`, for a machine with `n` states,
implies equivalence. -/
private theorem runOut_eq_of_kEquiv_card_sub_one [Fintype State]
    (M : MealyMachine State In Out) {q q' : State}
    (h : KEquiv M (Fintype.card State - 1) q q') (w : List In) :
    M.runOut q w = M.runOut q' w := by
  classical
  -- `c k` is the number of `k`-equivalence classes.
  let c : ℕ → ℕ := fun k => (Finset.univ.image (sig M k)).card
  have hc_le : ∀ k, c k ≤ Fintype.card State := fun k =>
    (Finset.card_image_le).trans (Finset.card_univ).le
  let trunc : ℕ → (List In → Option (List Out)) → List In → Option (List Out) :=
    fun k F w => if w.length ≤ k then F w else none
  have hsig : ∀ k, sig M k = trunc k ∘ sig M (k + 1) := by
    intro k
    funext q w
    by_cases hw : w.length ≤ k
    · simp only [Function.comp_apply, trunc, sig, ite_eq_left hw, ite_eq_left (hw.trans k.le_succ)]
    · simp only [Function.comp_apply, trunc, sig, ite_eq_right hw]
  have himage : ∀ k, Finset.univ.image (sig M k) =
      (Finset.univ.image (sig M (k + 1))).image (trunc k) := by
    intro k
    rw [Finset.image_image, ← hsig]
  have hc_mono : ∀ k, c k ≤ c (k + 1) := fun k => by
    simp only [c]
    rw [himage k]
    exact Finset.card_image_le
  -- Equal numbers of classes at `k` and `k + 1` make the two levels equal.
  have hstable : ∀ k, c k = c (k + 1) →
      ∀ q q', KEquiv M k q q' → KEquiv M (k + 1) q q' := by
    intro k hck q q' hq
    have hinj : Set.InjOn (trunc k) (Finset.univ.image (sig M (k + 1)) : Set _) := by
      apply Finset.card_image_iff.mp
      simp only [c] at hck
      rw [← himage k]
      exact hck
    rw [kEquiv_iff_sig_eq] at hq ⊢
    apply hinj (by simp) (by simp)
    rw [← Function.comp_apply (f := trunc k), ← hsig, ← Function.comp_apply (f := trunc k),
      ← hsig]
    exact hq
  have hpos : 0 < Fintype.card State := Fintype.card_pos_iff.mpr ⟨M.start⟩
  have hc0 : c 0 = 1 := by
    apply le_antisymm
    · apply Finset.card_le_one.mpr
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩
      rw [← kEquiv_iff_sig_eq]
      intro w hw
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)]
      rfl
    · exact Finset.card_pos.mpr (Finset.univ_nonempty_iff.mpr ⟨M.start⟩ |>.image _)
  -- Until the levels stabilize, the level `k + 1` has at least `k + 2` classes.
  have key : ∀ k, (∀ q q', KEquiv M k q q' → ∀ w, M.runOut q w = M.runOut q' w) ∨
      k + 2 ≤ c (k + 1) := by
    intro k
    induction k with
    | zero =>
      by_cases h1 : c 1 = 1
      · exact Or.inl fun q q' hq =>
          runOut_eq_of_kEquiv_of_stable M 0 (hstable 0 (hc0.trans h1.symm)) hq
      · exact Or.inr (show 2 ≤ c 1 by have : c 0 ≤ c 1 := hc_mono 0; omega)
    | succ k ih =>
      rcases ih with ih | ih
      · exact Or.inl fun q q' hq =>
          ih q q' fun w hw => hq w (hw.trans k.le_succ)
      · by_cases h2 : c (k + 1) = c (k + 2)
        · exact Or.inl fun q q' hq =>
            runOut_eq_of_kEquiv_of_stable M (k + 1) (hstable (k + 1) h2) hq
        · exact Or.inr (show k + 3 ≤ c (k + 2) by
            have : c (k + 1) ≤ c (k + 2) := hc_mono (k + 1); omega)
  rcases key (Fintype.card State - 1) with hkey | hkey
  · exact hkey q q' h w
  · have := hc_le (Fintype.card State - 1 + 1)
    omega

/-- **Characterization sets of finite-state machines.** Let $M$ be a deterministic, completely
specified Mealy machine with a finite set $Q$ of $n$ states, an input alphabet $I$ and an output
alphabet $O$, and let $\lambda^*(q, w)$ be the output word that $M$ produces from state $q$ on
an input word $w$. Then there is a finite set $W$ of input words such that $W$ contains the
empty word, every word of $W$ has length at most $n - 1$, and any two states $q$ and $q'$ with
$\lambda^*(q, w) = \lambda^*(q', w)$ for all $w \in W$ satisfy $\lambda^*(q, w) = \lambda^*(q', w)$
for every input word $w$; that is, $W$ is a characterization set of $M$. Here $n \ge 1$, since
$M$ has a start state. Neither minimality of $M$ nor finiteness of $I$ or $O$ is assumed.

Kocsis and Rot (*Complete test suites for automata in monoidal closed categories*,
arXiv:2411.13412v2) define characterization sets for DFAs (Definition 2.3), and their Section 5.1
contrasts their instance for Mealy machines with the traditional extension of the output function
to words, which records every output of a run, as $\lambda^*$ and `runOut` do. -/
theorem exists_characterization_set [Fintype State] (M : MealyMachine State In Out) :
    ∃ W : Finset (List In), [] ∈ W ∧ (∀ w ∈ W, w.length ≤ Fintype.card State - 1) ∧
      ∀ q q' : State, (∀ w ∈ W, M.runOut q w = M.runOut q' w) →
        ∀ w, M.runOut q w = M.runOut q' w := by
  classical
  -- A separating word of length at most `n - 1` for each pair of states that has one.
  let sep : State × State → List In := fun p =>
    if h : ∃ w : List In, w.length ≤ Fintype.card State - 1 ∧
        M.runOut p.1 w ≠ M.runOut p.2 w then h.choose else []
  refine ⟨insert [] (Finset.univ.image sep), Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
      simp only [sep]
      split_ifs with h
      · exact h.choose_spec.1
      · simp
  · intro q q' hW
    apply runOut_eq_of_kEquiv_card_sub_one M
    intro w hw
    by_contra hne
    have h : ∃ w : List In, w.length ≤ Fintype.card State - 1 ∧
        M.runOut q w ≠ M.runOut q' w := ⟨w, hw, hne⟩
    have hmem : sep (q, q') ∈ insert [] (Finset.univ.image sep) :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    have hsep : sep (q, q') = h.choose := dite_eq_left h
    exact h.choose_spec.2 (hsep ▸ hW _ hmem)

end Cslib.Automata.MealyMachine
