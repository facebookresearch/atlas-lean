/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card

/-!
# Counting labelled finite structures

For a relational first-order language `L` with finitely many symbols, there are finitely many
`L`-structures on a finite set; a structure on `Fin n` is a *labelled* structure with `n`
elements. The proportion of labelled structures on `Fin n` satisfying a sentence `φ` is the
quantity whose limit the zero-one law of first-order logic (Glebskii, Kogan, Liogon'kii and
Talanov 1969; Fagin 1976) describes.

* `FirstOrder.Language.finite_structure`: finitely many structures on a finite set.
* `FirstOrder.Language.nonempty_structure`: a relational language has a structure on every
  type (all relations empty).
* `FirstOrder.Language.satFraction`: the proportion of labelled structures on `Fin n`
  satisfying a sentence.
* `FirstOrder.Language.satFraction_not`: the proportion for `∼φ` is one minus that for `φ`.

## References

* R. Fagin, "Probabilities on finite models", *J. Symbolic Logic* 41 (1976), 50-58.
* P. G. Kolaitis and M. Y. Vardi, "0-1 laws for fragments of existential second-order logic:
  a survey", MFCS 2000, LNCS 1893, 84-98, Section 1.
-/

@[expose] public section

namespace FirstOrder.Language

variable (L : Language)

/-- **Finitely many structures on a finite set.** If `L` is relational with finitely many
symbols, there are only finitely many `L`-structures on a finite type: a structure is
determined by its relations, one subset of `M^k` for each relation symbol of arity `k`. -/
theorem finite_structure [L.IsRelational] [Finite L.Symbols] (M : Type*) [Finite M] :
    Finite (L.Structure M) := by
  have : Finite (Σ l, L.Relations l) :=
    Finite.of_injective (β := L.Symbols) Sum.inr Sum.inr_injective
  refine Finite.of_injective
    (fun S : L.Structure M => fun p : (Σ l, L.Relations l) => S.RelMap p.2) ?_
  rintro ⟨f₁, r₁⟩ ⟨f₂, r₂⟩ h
  have hf : @f₁ = @f₂ := by
    funext n f
    exact isEmptyElim f
  have hr : @r₁ = @r₂ := by
    funext n R x
    exact congrFun (congrFun h ⟨n, R⟩) x
  subst hf
  subst hr
  rfl

/-- **Relational languages have structures on every type.** Interpreting every relation
symbol as the empty relation gives an `L`-structure on any type when `L` has no function
symbols. -/
theorem nonempty_structure [L.IsRelational] (M : Type*) : Nonempty (L.Structure M) :=
  ⟨{ funMap := fun f => isEmptyElim f
     RelMap := fun _ _ => False }⟩

/-- **Proportion of labelled structures satisfying a sentence.** For a first-order sentence
`φ` and `n : ℕ`, the number of `L`-structures on `Fin n` in which `φ` is true, divided by the
number of all `L`-structures on `Fin n`. For a relational language with finitely many
symbols both counts are finite and the denominator is positive
(`FirstOrder.Language.finite_structure`, `FirstOrder.Language.nonempty_structure`); this is
the probability `μ_n(φ)` of Fagin, "Probabilities on finite models" (J. Symbolic Logic 41,
1976), for the uniform distribution on labelled structures. -/
noncomputable def satFraction (φ : L.Sentence) (n : ℕ) : ℝ :=
  (Set.ncard {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S φ} : ℝ) /
    Nat.card (L.Structure (Fin n))

/-- **Proportion for a negated sentence.** For a relational language with finitely many
symbols, the proportion of labelled structures on `Fin n` satisfying `∼φ` is one minus the
proportion satisfying `φ`. -/
theorem satFraction_not [L.IsRelational] [Finite L.Symbols] (φ : L.Sentence) (n : ℕ) :
    L.satFraction (∼φ) n = 1 - L.satFraction φ n := by
  have := L.finite_structure (Fin n)
  have := L.nonempty_structure (Fin n)
  have hpos : (0 : ℝ) < Nat.card (L.Structure (Fin n)) := by exact_mod_cast Nat.card_pos
  have hset : {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼φ)} =
      {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S φ}ᶜ := by
    ext S
    exact @Sentence.realize_not L (Fin n) S φ
  have hcard := Set.ncard_add_ncard_compl
    {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S φ}
  unfold satFraction
  rw [hset, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast (by omega : _ = _)

end FirstOrder.Language
