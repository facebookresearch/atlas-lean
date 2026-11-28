/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The first derived limit of a tower of abelian groups

For a tower of abelian groups `(A n, f n : A (n + 1) → A n)` indexed by `ℕ`, this file defines the
difference map `∏ A n → ∏ A n`, `(x n) ↦ (x n - f n (x (n + 1)))`, identifies its kernel with the
compatible families (the limit of the tower), defines `R¹ lim` as its cokernel, and proves that the
difference map is surjective, so that `R¹ lim = 0`, when every transition map is surjective.

This follows The Stacks Project, Lemma 15.88.1 (Tag 07KW): item (2) represents `R lim A_n` by the
two-term complex `∏ A_n → ∏ A_n`, `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))` in degrees `0` and `1`, so that
`lim A_n` and `R¹ lim A_n` are the kernel and the cokernel of that map, and item (3) states
`R¹ lim A_n = 0` for a Mittag-Leffler system. Here the cokernel is taken as the definition of
`R¹ lim` (no derived functor is constructed), and item (3) is proved for towers with surjective
transition maps, a special case of Mittag-Leffler systems.
-/

@[expose] public section

set_option autoImplicit false

namespace LimOne

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)] (f : ∀ n, A (n + 1) →+ A n)

/-- The difference map `∏ A n → ∏ A n`, `(x n) ↦ (x n - f n (x (n + 1)))`, of a tower of abelian
groups `(A n, f n : A (n + 1) → A n)`: the differential of the two-term complex that represents
`R lim` of the tower (The Stacks Project, Lemma 15.88.1 (2), Tag 07KW). -/
def differenceMap : (∀ n, A n) →+ (∀ n, A n) where
  toFun x n := x n - f n (x (n + 1))
  map_zero' := by
    funext n
    simp
  map_add' x y := by
    funext n
    simp only [Pi.add_apply, map_add]
    exact add_sub_add_comm _ _ _ _

@[simp]
theorem differenceMap_apply (x : ∀ n, A n) (n : ℕ) :
    differenceMap f x n = x n - f n (x (n + 1)) :=
  rfl

/-- The kernel of the difference map consists of the compatible families, the elements of the
limit of the tower: `x` lies in it if and only if `f n (x (n + 1)) = x n` for every `n`. -/
theorem mem_ker_differenceMap_iff (x : ∀ n, A n) :
    x ∈ (differenceMap f).ker ↔ ∀ n, f n (x (n + 1)) = x n := by
  rw [AddMonoidHom.mem_ker, funext_iff]
  simp only [differenceMap_apply, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun n => eq_comm

/-- The first derived limit `R¹ lim` of a tower of abelian groups `(A n, f n)`: the cokernel of the
difference map `∏ A n → ∏ A n`, `(x n) ↦ (x n - f n (x (n + 1)))` (The Stacks Project,
Lemma 15.88.1 (2), Tag 07KW, by which `R lim` of the tower is represented by that map in degrees `0`
and `1`). -/
abbrev limOne : Type _ := (∀ n, A n) ⧸ (differenceMap f).range

/-- **The difference map of a tower with surjective transition maps is surjective**: if every
transition map `f n : A (n + 1) → A n` is surjective, then every `y ∈ ∏ A n` is
`x n - f n (x (n + 1))` for some `x ∈ ∏ A n`. One takes `x 0 = 0` and chooses `x (n + 1)` with
`f n (x (n + 1)) = x n - y n` (The Stacks Project, Lemma 15.88.1 (3), Tag 07KW, for a Mittag-Leffler
system; a tower with surjective transition maps is one). -/
theorem differenceMap_surjective (hf : ∀ n, Function.Surjective (f n)) :
    Function.Surjective (differenceMap f) := by
  intro y
  let x : ∀ n, A n := fun n =>
    Nat.rec (motive := fun n => A n) 0 (fun n xn => (hf n (xn - y n)).choose) n
  have hx : ∀ n, f n (x (n + 1)) = x n - y n := fun n => (hf n (x n - y n)).choose_spec
  refine ⟨x, funext fun n => ?_⟩
  rw [differenceMap_apply, hx, sub_sub_cancel]

/-- **`R¹ lim = 0` for a tower with surjective transition maps**: the cokernel of the difference map
is trivial (The Stacks Project, Lemma 15.88.1 (3), Tag 07KW, for this special case of a
Mittag-Leffler system). -/
theorem subsingleton_limOne (hf : ∀ n, Function.Surjective (f n)) :
    Subsingleton (limOne f) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientAddGroup.induction_on with
  | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
      rw [QuotientAddGroup.eq]
      exact differenceMap_surjective f hf _

end LimOne
