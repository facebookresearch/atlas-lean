/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.FiniteWeylWord

/-! # List-level Bruhat middle of finite Weyl words

For `i j : Fin m → Fin n` with pointwise distinctness `hij : ∀ k, i k ≠ j k`
and units `u : Fin m → Fˣ` over `[Field F]`, `finiteWeyl_list_bruhatMiddle_eq`
identifies the canonical Bruhat middle of the head-left `List.ofFn`/`List.prod`
ordered product of the finite `weylSLUnit` matrices with the ordered product of
their accepted `weylMonomialSLUnit` realizations, preserving exact `List.ofFn`
order on both sides. The `[Field F]` hypothesis is required by the accepted
`bruhatMiddle_monomialSLHom` retraction; the pointwise lift itself is
`[CommRing]`-general via `weylSLUnit_eq_monomialSLHom`. The empty list
(`m = 0`) gives `bruhatMiddle 1 = 1` through the monoid-hom image of the empty
product. Purpose: list-level monomial input for the finite central-kernel
containment route. Nonclaims: no StableE evaluation, kernel hypothesis,
permutation-triviality, torus landing, subgroup containment, kernel generation,
or Matsumoto claim.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u

/-- Canonical Bruhat middle of a finite Weyl list product: for pointwise
distinct indices `hij : ∀ k, i k ≠ j k`, the `bruhatMiddle` of the head-left
`List.ofFn`/`List.prod` ordered product of `weylSLUnit (i k) (j k) (hij k)`
`(u k)` is the ordered product of the accepted `weylMonomialSLUnit`
realizations in the same `List.ofFn` order. `[Field F]` is required by the
`bruhatMiddle_monomialSLHom` retraction; the pointwise step is
`[CommRing]`-general. The empty list gives `bruhatMiddle 1 = 1`; low ranks
need no special case since the statement is uniform in `m n`. Orientation is
head-left throughout. Nonclaims: no StableE evaluation, kernel hypothesis,
permutation-triviality, torus landing, subgroup containment, kernel generation,
or Matsumoto claim. -/
public theorem finiteWeyl_list_bruhatMiddle_eq
    {F : Type u} [Field F] {m n : ℕ}
    (i j : Fin m → Fin n) (hij : ∀ k, i k ≠ j k) (u : Fin m → Fˣ) :
    bruhatMiddle
      (List.prod (List.ofFn (fun k => weylSLUnit (i k) (j k) (hij k) (u k)))) =
    List.prod (List.ofFn (fun k =>
      weylMonomialSLUnit (i k) (j k) (hij k) (u k))) := by
  let word : FiniteWeylWord F (Fin n) :=
    FiniteWeylWord.ofFn fun k =>
      { left := i k
        right := j k
        ne := hij k
        unit := u k }
  have hword := FiniteWeylWord.bruhatMiddle_specialLinearEval word
  dsimp [word, FiniteWeylWord.ofFn,
    FiniteWeylWord.specialLinearEval,
    FiniteWeylWord.monomialSLEval,
    WeylLetter.specialLinear, WeylLetter.monomialSL] at hword
  simp only [List.map_ofFn] at hword
  change bruhatMiddle
      (List.prod (List.ofFn fun k =>
        weylSLUnit (i k) (j k) (hij k) (u k))) =
    List.prod (List.ofFn fun k =>
      weylMonomialSLUnit (i k) (j k) (hij k) (u k)) at hword
  exact hword

end Matrix.GeneralLinearGroup

end
