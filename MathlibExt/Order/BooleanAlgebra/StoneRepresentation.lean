/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.PrimeIdeal
import Mathlib.Util.Superscript

@[expose] public section

universe u

namespace MathlibExt.Order.BooleanAlgebra.StoneRepresentation

/-!
# Stone's representation theorem for Boolean algebras

Records the algebraic form: every Boolean algebra embeds as a bounded lattice
hom into a powerset. Complement preservation is automatic for such homs.
-/

private theorem inf_compl_eq_bot_iff_le {B : Type u} [BooleanAlgebra B] {a b : B} :
    a ⊓ bᶜ = ⊥ ↔ a ≤ b := by
  constructor
  · intro h
    have h1 : (a ⊓ b) ⊔ (a ⊓ bᶜ) = a := by
      rw [← inf_sup_left, sup_compl_eq_top]
      simp
    have ha : a ⊓ b = a := by
      calc a ⊓ b = (a ⊓ b) ⊔ (a ⊓ bᶜ) := by rw [h]; simp
      _ = a := h1
    exact inf_eq_left.mp ha
  · intro h
    rw [← le_bot_iff]
    calc a ⊓ bᶜ ≤ b ⊓ bᶜ := inf_le_inf h le_rfl
    _ = ⊥ := inf_compl_eq_bot

private theorem exists_prime_sep {B : Type u} [BooleanAlgebra B] {a b : B} (h : ¬ a ≤ b) :
    ∃ I : Order.Ideal B, I.IsPrime ∧ b ∈ I ∧ a ∉ I := by
  have hc : a ⊓ bᶜ ≠ ⊥ := fun he => h (inf_compl_eq_bot_iff_le.mp he)
  have hJ : (Order.Ideal.principal (a ⊓ bᶜ)ᶜ).IsProper := by
    rw [Order.Ideal.isProper_iff_top_notMem, Order.Ideal.mem_principal]
    intro htop
    apply hc
    have h1 : (a ⊓ bᶜ)ᶜ = ⊤ := top_le_iff.mp htop
    have h2 := congrArg (· ᶜ) h1
    simpa using h2
  obtain ⟨M, hJM, hMmax⟩ := hJ.exists_le_maximal
  have hMprime : M.IsPrime := @Order.Ideal.IsMaximal.isPrime _ _ _ hMmax
  refine ⟨M, hMprime, ?_, ?_⟩
  · have hb : b ≤ (a ⊓ bᶜ)ᶜ := by
      have hcc : (a ⊓ bᶜ)ᶜ = aᶜ ⊔ b := by rw [compl_inf, compl_compl]
      rw [hcc]
      exact le_sup_right
    exact Order.Ideal.mem_of_mem_of_le (Order.Ideal.mem_principal.mpr hb) hJM
  · intro ha
    have h1 : a ⊓ bᶜ ∈ M := M.lower inf_le_left ha
    have h2 : (a ⊓ bᶜ)ᶜ ∈ M :=
      Order.Ideal.mem_of_mem_of_le Order.Ideal.mem_principal_self hJM
    have h3 : (a ⊓ bᶜ) ⊔ (a ⊓ bᶜ)ᶜ ∈ M := Order.Ideal.sup_mem h1 h2
    rw [sup_compl_eq_top] at h3
    exact (Order.Ideal.isProper_iff_top_notMem.mp hMmax.toIsProper) h3

/--
**Stone representation theorem.** Every Boolean algebra $B$ embeds in a power set algebra: there
are a set $X$ and an injective map $f$ from $B$ to the power set of $X$ such that
$f(a \sqcup b) = f(a) \cup f(b)$ and $f(a \sqcap b) = f(a) \cap f(b)$ for all $a, b \in B$,
$f(\top) = X$ and $f(\bot) = \emptyset$.

Such a map automatically preserves complements: $f(a^c) = X \setminus f(a)$ for all $a \in B$.

Source: M. H. Stone, The Theory of Representation for Boolean Algebras, Trans. Amer. Math. Soc. 40
(1936), 37–111, DOI 10.2307/1989664.
Proves `Wanted` entry `stone_representation_theorem`.
-/
theorem stone_representation_theorem
    {B : Type u} [BooleanAlgebra B] :
    ∃ (X : Type u) (f : BoundedLatticeHom B (Set X)), Function.Injective f := by
  refine ⟨{ I : Order.Ideal B // I.IsPrime },
    ⟨⟨⟨fun b => { J : { I : Order.Ideal B // I.IsPrime } | b ∉ J.1 }, ?_⟩, ?_⟩,
      ?_, ?_⟩, ?_⟩
  · intro a b
    show ({ J : { I : Order.Ideal B // I.IsPrime } | a ⊔ b ∉ J.1 } : Set _) = _ ⊔ _
    ext J
    simp only [Set.mem_ofPred_eq]
    change (a ⊔ b ∉ J.1) ↔ (a ∉ J.1 ∨ b ∉ J.1)
    rw [Order.Ideal.sup_mem_iff]
    by_cases ha : a ∈ J.1 <;> simp [ha]
  · intro a b
    change ({ J : { I : Order.Ideal B // I.IsPrime } | a ⊓ b ∉ J.1 } : Set _) = _ ⊓ _
    ext J
    simp only [Set.mem_ofPred_eq]
    change (a ⊓ b ∉ J.1) ↔ (a ∉ J.1 ∧ b ∉ J.1)
    constructor
    · intro h
      refine ⟨?_, ?_⟩ <;> intro hm <;> apply h
      · exact J.1.lower inf_le_left hm
      · exact J.1.lower inf_le_right hm
    · intro h hm
      rcases Order.Ideal.IsPrime.mem_or_mem J.2 hm with h1 | h1
      · exact h.1 h1
      · exact h.2 h1
  · change ({ J : { I : Order.Ideal B // I.IsPrime } | (⊤ : B) ∉ J.1 } : Set _) = ⊤
    ext J
    simp only [Set.mem_ofPred_eq]
    change (⊤ : B) ∉ J.1 ↔ True
    exact iff_true_intro (Order.Ideal.isProper_iff_top_notMem.mp J.2.toIsProper)
  · change ({ J : { I : Order.Ideal B // I.IsPrime } | (⊥ : B) ∉ J.1 } : Set _) = ⊥
    ext J
    simp only [Set.mem_ofPred_eq, Set.bot_eq_empty, Set.notMem_empty]
    exact ⟨fun h => h (Order.Ideal.bot_mem _), fun h => h.elim⟩
  · intro a b hab
    by_contra hne
    have hab' : ({ J : { I : Order.Ideal B // I.IsPrime } | a ∉ J.1 } : Set _) =
        { J : { I : Order.Ideal B // I.IsPrime } | b ∉ J.1 } := hab
    by_cases hle : a ≤ b
    · have hn : ¬ b ≤ a := fun hba => hne (le_antisymm hle hba)
      obtain ⟨M, hM, haM, hbM⟩ := exists_prime_sep hn
      have hmem : (⟨M, hM⟩ : { I : Order.Ideal B // I.IsPrime }) ∈
          ({ J : { I : Order.Ideal B // I.IsPrime } | b ∉ J.1 } : Set _) := hbM
      rw [← hab'] at hmem
      exact hmem haM
    · obtain ⟨M, hM, hbM, haM⟩ := exists_prime_sep hle
      have hmem : (⟨M, hM⟩ : { I : Order.Ideal B // I.IsPrime }) ∈
          ({ J : { I : Order.Ideal B // I.IsPrime } | a ∉ J.1 } : Set _) := haM
      rw [hab'] at hmem
      exact hmem hbM

end MathlibExt.Order.BooleanAlgebra.StoneRepresentation
