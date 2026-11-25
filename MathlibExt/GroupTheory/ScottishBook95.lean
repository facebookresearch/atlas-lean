/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The additive reals as permutations of the natural numbers

We embed the additive group of real numbers into the permutations of a countable set by
identifying reals with rational sequences and translating each copy of the rationals.
-/

public section

namespace MathlibExt.GroupTheory.ScottishBook95Wanted

open Cardinal

/--
**The additive group of the reals embeds in the infinite symmetric group.** There is an injective
group homomorphism from the additive group $(\mathbb{R}, +)$ of real numbers into the group
$S_\infty$ of all permutations of the natural numbers.

Source: J. Schreier and S. Ulam,
Problem 95 of the Scottish Book; affirmative answer of Schreier and Ulam,
November 1935, recorded in the typescript addendum Ad 95. `Multiplicative ℝ`
is the additive group `ℝ` viewed multiplicatively, so a monoid homomorphism
out of it is an additive homomorphism out of `ℝ`.
-/
theorem real_addGroup_embeds_in_perm_nat :
    ∃ f : Multiplicative ℝ →* Equiv.Perm ℕ, Function.Injective f := by
  have hcard : #(ℕ → ℚ) = 𝔠 := by
    rw [← power_def, mk_nat, Cardinal.mkRat, aleph0_power_aleph0]
  obtain ⟨coords⟩ : Nonempty (ℝ ≃ₗ[ℚ] (ℕ → ℚ)) := by
    apply Module.nonempty_linearEquiv_iff_rank_eq.mpr
    rw [Real.rank_rat_real, Module.Free.rank_eq_mk_of_infinite_lt, hcard]
    simpa [hcard] using aleph0_lt_continuum
  let translate : Multiplicative ℝ →* Equiv.Perm (ℕ × ℚ) :=
    { toFun := fun x => Equiv.prodCongrRight fun n => Equiv.addLeft (coords x.toAdd n)
      map_one' := Equiv.ext fun ⟨n, q⟩ => by simp
      map_mul' x y := Equiv.ext fun ⟨n, q⟩ => by simp }
  obtain ⟨number⟩ : Nonempty ((ℕ × ℚ) ≃ ℕ) := nonempty_equiv_of_countable
  refine ⟨number.permCongrHom.toMonoidHom.comp translate, number.permCongrHom.injective.comp ?_⟩
  -- The image of (n, 0) recovers the nth coordinate.
  intro x y h
  apply Multiplicative.toAdd.injective
  apply coords.injective
  funext n
  simpa [translate] using congrArg (fun p : Equiv.Perm (ℕ × ℚ) => (p (n, 0)).2) h

end MathlibExt.GroupTheory.ScottishBook95Wanted
