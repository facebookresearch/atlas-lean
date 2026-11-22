/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.LKSoundness

/-!
# Tests for soundness of the propositional sequent calculus LK

* Truth tables: each connective under the valuation that makes atom `0` true and every other
  atom false.
* Boundary cases of `Valid`: the empty sequent is false under every valuation; with no
  hypotheses a sequent is true when some conclusion is true; with no conclusions it is true
  exactly when some hypothesis is false.
* Derivations: the identity sequent, excluded middle, Peirce's law, a derivation that chains two
  sequents with cut, and a derivation of `p, ¬p ⊢` without cut, which needs exchange.
* `Deriv.sound`: Peirce's law and the conclusion of the cut derivation are true, while the empty
  sequent and an atom with no hypotheses have no derivation.
-/

@[expose] public section

namespace MathlibExt.Logic.LKSoundness.Tests

/-- The atom `0`. -/
abbrev p : PForm := .atom 0

/-- The atom `1`. -/
abbrev q : PForm := .atom 1

/-- The valuation that makes atom `0` true and every other atom false. -/
def v₀ (n : ℕ) : Bool := n == 0

example : p.eval v₀ = true ∧ q.eval v₀ = false := by decide

example : (PForm.impl p q).eval v₀ = false ∧ (PForm.impl q p).eval v₀ = true ∧
    (PForm.impl q q).eval v₀ = true := by
  decide

example : (PForm.conj p q).eval v₀ = false ∧ (PForm.conj p p).eval v₀ = true := by decide

example : (PForm.disj p q).eval v₀ = true ∧ (PForm.disj q q).eval v₀ = false := by decide

example : (PForm.neg p).eval v₀ = false ∧ (PForm.neg q).eval v₀ = true := by decide

/-- The empty sequent is false under every valuation. -/
example (v : ℕ → Bool) : ¬ Valid v [] [] := by
  intro h
  obtain ⟨b, hb, -⟩ := h (by simp)
  simp at hb

/-- With no hypotheses, a sequent with a true conclusion is true. -/
example : Valid v₀ [] [p] := fun _ => ⟨p, by simp, by decide⟩

/-- With no conclusions, a sequent with a false hypothesis is true. -/
example : Valid v₀ [q] [] := fun h => absurd (h q (by simp)) (by decide)

/-- With no conclusions, a sequent whose hypotheses are all true is false. -/
example : ¬ Valid v₀ [p] [] := by
  intro h
  obtain ⟨b, hb, -⟩ := h (by decide)
  simp at hb

/-- The identity sequent `p ⊢ p`. -/
example : Deriv [p] [p] := .ax (a := p) (by simp) (by simp)

/-- Excluded middle: exchange moves `¬p` to the head of the succedent, where `negR` introduces
it. -/
example : Deriv [] [.disj p (.neg p)] :=
  .disjR (.exchR (.negR (.ax (a := p) (by simp) (by simp))) (List.Perm.swap _ _ _))

/-- Peirce's law `((p → q) → p) → p`. -/
theorem deriv_peirce : Deriv [] [.impl (.impl (.impl p q) p) p] :=
  .implR (.implL (.implR (.ax (a := p) (by simp) (by simp))) (.ax (a := p) (by simp) (by simp)))

/-- Cut on `p ∨ q` chains `p ⊢ p ∨ q, q ∨ p` and `p ∨ q, p ⊢ q ∨ p` into `p ⊢ q ∨ p`. -/
theorem deriv_cut : Deriv [p] [.disj q p] :=
  .cut (a := .disj p q)
    (.disjR (.ax (a := p) (by simp) (by simp)))
    (.disjL (.disjR (.ax (a := p) (by simp) (by simp)))
      (.disjR (.ax (a := q) (by simp) (by simp))))

/-- `p, ¬p ⊢` has a derivation without cut: exchange moves `¬p` to the head of the antecedent,
where `negL` reduces the sequent to `p ⊢ p`. -/
example : Deriv [p, .neg p] [] :=
  .exchL (.negL (.ax (a := p) (by simp) (by simp))) (List.Perm.swap _ _ _)

/-- By soundness, Peirce's law is true under every valuation. -/
example (v : ℕ → Bool) : (PForm.impl (.impl (.impl p q) p) p).eval v = true := by
  obtain ⟨b, hb, hbt⟩ := deriv_peirce.sound v (by simp)
  simp only [List.mem_singleton] at hb
  exact hb ▸ hbt

/-- By soundness, `q ∨ p` is true under every valuation that makes `p` true. -/
example (v : ℕ → Bool) (hv : v 0 = true) : (PForm.disj q p).eval v = true := by
  obtain ⟨b, hb, hbt⟩ := deriv_cut.sound v (by simpa [PForm.eval] using hv)
  simp only [List.mem_singleton] at hb
  exact hb ▸ hbt

/-- The empty sequent has no derivation, since it is false under every valuation. -/
example : ¬ Deriv [] [] := fun h => by
  obtain ⟨b, hb, -⟩ := h.sound (fun _ => true) (by simp)
  simp at hb

/-- With no hypotheses, an atom has no derivation, since it is false under the valuation that
makes every atom false. -/
example : ¬ Deriv [] [p] := fun h => by
  obtain ⟨b, hb, hbt⟩ := h.sound (fun _ => false) (by simp)
  simp only [List.mem_singleton] at hb
  subst hb
  exact absurd hbt (by decide)

end MathlibExt.Logic.LKSoundness.Tests
