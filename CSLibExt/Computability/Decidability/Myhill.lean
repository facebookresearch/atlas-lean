/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.Reduce

@[expose] public section

/-!
# Myhill's isomorphism theorem: the easy direction

Myhill's isomorphism theorem (Soare, *Recursively Enumerable Sets and Degrees*,
Ch. I, Theorem 7.1; Rogers, *Theory of Recursive Functions and Effective
Computability*, §7.6) says that two recursively enumerable sets are
recursively isomorphic if and only if they are 1-equivalent. The easy
direction — a recursive isomorphism gives a 1-equivalence — is proved here:
a computable bijection translating `P` to `Q` is itself a 1-reduction, and
its computable inverse (found by unbounded search) is a 1-reduction back.
The hard direction (the back-and-forth construction) is registered as a
wanted theorem in `WantedExt/TheoryOfComputation/MyhillBackAndForth.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

/-- Two predicates are **recursively isomorphic** when a computable bijection
translates membership in one to membership in the other.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 7.1. -/
def RecursiveIsomorphic (P Q : ℕ → Prop) : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧ Function.Bijective f ∧ ∀ n, P n ↔ Q (f n)

/-- **The inverse of a computable bijection is computable**, by unbounded search
for the unique preimage.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (inverses of recursive permutations). -/
theorem computable_invFun_of_bijective {f : ℕ → ℕ} (hf : Computable f)
    (hbij : Function.Bijective f) : Computable (Function.invFun f) := by
  have hbeq_pt : ∀ a b : ℕ, BEq.beq a b = decide (a = b) := fun a b ↦ by
    by_cases h : a = b <;> simp [h]
  have hpart : Partrec (fun n : ℕ ↦ Nat.rfind (fun m ↦ Part.some (decide (f m = n)))) := by
    apply Partrec.rfind
    change Partrec (fun q : ℕ × ℕ ↦ Part.some (decide (f q.2 = q.1)))
    have hbeq : Computable (fun q : ℕ × ℕ ↦ BEq.beq (f q.2) q.1) :=
      Computable₂.comp Primrec.beq.to_comp (hf.comp Computable.snd) Computable.fst
    exact Computable.of_eq hbeq (fun q ↦ hbeq_pt (f q.2) q.1)
  have heq : ∀ n, Nat.rfind (fun m ↦ Part.some (decide (f m = n))) =
      Part.some (Function.invFun f n) := by
    intro n
    have hDom : (Nat.rfind (fun m ↦ Part.some (decide (f m = n)))).Dom :=
      Nat.rfind_dom.2 ⟨Function.invFun f n,
        by simp [Function.invFun_eq (hbij.surjective n)], fun _ ↦ trivial⟩
    have hget : (Nat.rfind (fun m ↦ Part.some (decide (f m = n)))).get hDom =
        Function.invFun f n := by
      have hspec : decide (f ((Nat.rfind (fun m ↦ Part.some (decide (f m = n)))).get hDom)
          = n) = true := by
        have h := Nat.rfind_spec ⟨hDom, rfl⟩
        exact (Part.mem_some_iff.1 h).symm
      have hfn : f ((Nat.rfind (fun m ↦ Part.some (decide (f m = n)))).get hDom) = n :=
        of_decide_eq_true hspec
      exact hbij.injective (hfn.trans (Function.invFun_eq (hbij.surjective n)).symm)
    exact Part.eq_some_iff.2 ⟨hDom, hget⟩
  exact hpart.of_eq heq

/-- **A recursive isomorphism gives a 1-equivalence** (the easy direction of
Myhill's isomorphism theorem).
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 7.1. -/
theorem recursiveIsomorphic_to_oneOneEquiv {P Q : ℕ → Prop}
    (h : RecursiveIsomorphic P Q) : OneOneEquiv P Q := by
  obtain ⟨f, hf, hbij, hiff⟩ := h
  let e : ℕ ≃ ℕ := Equiv.ofBijective f hbij
  have he : e.Computable := by
    refine ⟨?_, ?_⟩
    · exact Computable.of_eq hf (fun n ↦ (Equiv.ofBijective_apply f hbij n).symm)
    · apply Computable.of_eq (computable_invFun_of_bijective hf hbij)
      intro n
      symm
      rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
      exact (Function.invFun_eq (hbij.surjective n)).symm
  have h1 : OneOneEquiv (Q ∘ e) Q := OneOneEquiv.of_equiv he
  have hPQ : P = Q ∘ e := by
    funext n
    change P n = Q (f n)
    exact propext (hiff n)
  rw [hPQ]
  exact h1

end Cslib.Decidability
