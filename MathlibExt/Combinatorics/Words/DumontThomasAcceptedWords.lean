/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.DumontThomasNumeration
import Mathlib.Data.List.Chain

/-!
# Accepted words in Dumont–Thomas numeration

Each defined transition selects a letter of a substitution image. The prefix before that
letter has length equal to the digit read. Reversing the transition pairs gives an admissible
sequence indexed from the least significant digit.

## References

* Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*,
  INTEGERS 24 (2024), Article A112, pp. 1–27, Lemma 3.8 (pp. 7–8).
-/

namespace MetaMathlibExt

-- The first pair supplies the starting state; its word is not part of the run.
private theorem steps_of_accepted {A : Type*} (η : A → List A) (start : List A × A)
    (digits : List ℕ) (h : (substitutionAutomaton η start.2 digits).isSome) :
    ∃ steps : List (List A × A), steps.map (fun p => p.1.length) = digits ∧
      (start :: steps).IsChain (fun p q => q.1 ++ [q.2] <+: η p.2) := by
  induction digits generalizing start with
  | nil => exact ⟨[], rfl, .singleton _⟩
  | cons d digits ih =>
    rw [substitutionAutomaton_cons] at h
    cases hnext : (η start.2)[d]? with
    | none => simp [hnext] at h
    | some y =>
      obtain ⟨hd, hy⟩ := List.getElem?_eq_some_iff.mp hnext
      obtain ⟨steps, hdigits, hchain⟩ :=
        ih ((η start.2).take d, y) (by simpa only [hnext, Option.bind_some] using h)
      refine ⟨((η start.2).take d, y) :: steps, ?_, .cons_cons ?_ hchain⟩
      · simp [hdigits, Nat.min_eq_left hd.le]
      · change (η start.2).take d ++ [y] <+: η start.2
        rw [← hy, ← List.take_succ_eq_append_getElem hd]
        exact List.take_prefix _ _

-- Reversal turns each transition into the admissibility condition at the next lower index.
private theorem admissible_of_steps {A : Type*} (η : A → List A) (x : A)
    (steps : List (List A × A)) (hpos : 0 < steps.length)
    (hchain : (([], x) :: steps).IsChain (fun p q => q.1 ++ [q.2] <+: η p.2)) :
    IsLetterAdmissibleSequence η x (fun i => (([], x) :: steps).reverse[i]?.getD ([], x))
      (steps.length - 1) := by
  let pairs := (([], x) :: steps).reverse
  have hlength : pairs.length = steps.length + 1 := by simp [pairs]
  have hchain' : pairs.IsChain (fun p q => p.1 ++ [p.2] <+: η q.2) :=
    List.isChain_reverse.mpr hchain
  have hstep (i : ℕ) (hi : i < steps.length) :
      (pairs[i]?.getD ([], x)).1 ++ [(pairs[i]?.getD ([], x)).2] <+:
        η (pairs[i + 1]?.getD ([], x)).2 := by
    have hi' : i + 1 < pairs.length := by omega
    simpa only [List.getElem?_eq_getElem (show i < pairs.length by omega),
      List.getElem?_eq_getElem hi', Option.getD_some] using hchain'.getElem i hi'
  have hseed : pairs[steps.length]? = some ([], x) := by
    dsimp [pairs]
    rw [List.getElem?_reverse' (j := 0) (by simp)]
    rfl
  refine ⟨fun i hi => hstep i (by omega), ?_⟩
  simpa only [show steps.length - 1 + 1 = steps.length by omega, hseed, Option.getD_some]
    using hstep (steps.length - 1) (by omega)

-- An accepted run supplies the transitions without a non-erasing or growth assumption.
set_option linter.unusedVariables false in
/-- **Accepted digit words come from admissible sequences.** Let $\eta$ be a substitution on an
alphabet $A$, let $x \in A$, let $k \ge 1$, and let $v_0, v_1, \dots, v_{k-1}$ be natural
numbers. If the digit word $v_{k-1} v_{k-2} \cdots v_0$ is accepted by the automaton
$\mathcal{A}_{\eta,x}$ (that is, its run from $x$ is defined), then there is an $x$-admissible
sequence $(m_i, a_i)_{0 \le i \le k-1}$ with $|m_i| = v_i$ for every $i < k$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.8. -/
public theorem exists_letterAdmissibleSequence_of_accepted {A : Type*}
    (η : A → List A) (hη : IsSubstitution η) (k : ℕ) (hk : 1 ≤ k) (x : A) (v : ℕ → ℕ)
    (hv : (substitutionAutomaton η x ((List.range k).map fun t => v (k - 1 - t))).isSome) :
    ∃ s, IsLetterAdmissibleSequence η x s (k - 1) ∧ ∀ i < k, (s i).1.length = v i := by
  obtain ⟨steps, hdigits, hchain⟩ := steps_of_accepted η ([], x) _ hv
  have hlength : steps.length = k := by
    simpa only [List.length_map, List.length_range] using congrArg List.length hdigits
  let s (i : ℕ) := (([], x) :: steps).reverse[i]?.getD ([], x)
  refine ⟨s, ?_, ?_⟩
  · rw [← hlength]
    exact admissible_of_steps η x steps (by omega) hchain
  · intro i hi
    let t := k - 1 - i
    have ht : t < k := by dsimp [t]; omega
    have hback : k - 1 - t = i := by dsimp [t]; omega
    have hslot : (([], x) :: steps).reverse[i]? = steps[t]? := by
      rw [List.getElem?_reverse' (j := t + 1) (by simp only [List.length_cons]; dsimp [t]; omega)]
      rfl
    have hdigit := congrArg (fun ds : List ℕ => ds[t]?) hdigits
    have hsome := List.getElem?_eq_getElem (l := steps) (i := t) (by omega)
    simpa only [List.getElem?_map, List.getElem?_range ht, hback, hsome, Option.map_some,
      Option.some.injEq, s, hslot, Option.getD_some] using hdigit

end MetaMathlibExt
