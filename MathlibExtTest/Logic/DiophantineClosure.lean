/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.DiophantineClosure
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for closure properties of Diophantine sets
-/

set_option autoImplicit false

@[expose] public section

namespace DiophantineClosureTest

open MetaMathlibExt MvPolynomial

#check @isDiophantine_of_finite
#check @IsDiophantine.exists_family
#check @isDiophantine_setOf_forall_eval_eq_zero
#check @isDiophantine_setOf_eval_eq_zero
#check @IsDiophantine.inter
#check @IsDiophantine.union
#check @IsDiophantine.preimage_eval
#check @IsDiophantine.comp
#check @IsDiophantine.image_eval
#check @IsDiophantine.exists_proj
#check @IsDiophantine.iff_single
#check @isDiophantine_setOf_ne_zero

/-- The diagonal $\{(x, y) \mid x = y\} \subseteq \mathbb{Q}^2$ is a zero set. -/
example : IsDiophantine (Int.castRingHom ℚ) {x : Fin 2 → ℚ | eval₂ (Int.castRingHom ℚ) x
    (X 0 - X 1 : MvPolynomial (Fin 2) ℤ) = 0} :=
  isDiophantine_setOf_eval_eq_zero _ _

/-- The points of $\mathbb{Q}^2$ with both coordinates nonzero. -/
example : IsDiophantine (Int.castRingHom ℚ) ({x : Fin 2 → ℚ | x 0 ≠ 0} ∩ {x | x 1 ≠ 0}) :=
  (isDiophantine_setOf_ne_zero _ 0).inter (isDiophantine_setOf_ne_zero _ 1)

/-- The points of $\mathbb{Z}^2$ on one of the two coordinate axes. -/
example : IsDiophantine (RingHom.id ℤ)
    ({x : Fin 2 → ℤ | eval₂ (RingHom.id ℤ) x (X 0) = 0} ∪
      {x | eval₂ (RingHom.id ℤ) x (X 1) = 0}) :=
  (isDiophantine_setOf_eval_eq_zero _ _).union (isDiophantine_setOf_eval_eq_zero _ _)

/-- Swapping the two coordinates preserves Diophantine sets. -/
example (T : Set (Fin 2 → ℚ)) (hT : IsDiophantine (Int.castRingHom ℚ) T) :
    IsDiophantine (Int.castRingHom ℚ) {x : Fin 2 → ℚ | x ∘ ![1, 0] ∈ T} :=
  hT.comp _

/-- The first coordinates of a Diophantine subset of $\mathbb{Q}^{1 + 1}$. -/
example (S : Set (Fin (1 + 1) → ℚ)) (hS : IsDiophantine (Int.castRingHom ℚ) S) :
    IsDiophantine (Int.castRingHom ℚ) {x : Fin 1 → ℚ | ∃ z : Fin 1 → ℚ, Fin.append x z ∈ S} :=
  hS.exists_proj

/-- The rational squares: the image of $\mathbb{Q}$ under $t \mapsto t^2$. -/
example : IsDiophantine (Int.castRingHom ℚ)
    {x : Fin 1 → ℚ | ∃ t ∈ (Set.univ : Set (Fin 1 → ℚ)),
      ∀ i, x i = eval₂ (Int.castRingHom ℚ) t (![X 0 ^ 2] i)} :=
  (isDiophantine_univ _ 1).image_eval _

/-- Over $\mathbb{Q}$ a Diophantine set is cut out by a single polynomial. -/
example (S : Set (Fin 2 → ℚ)) (hS : IsDiophantine (Int.castRingHom ℚ) S) :
    ∃ (n : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin n) ℤ), ∀ x : Fin 2 → ℚ,
      x ∈ S ↔ ∃ y : Fin n → ℚ, eval₂ (Int.castRingHom ℚ) (Sum.elim x y) p = 0 :=
  (IsDiophantine.iff_single _ S).1 hS

end DiophantineClosureTest
