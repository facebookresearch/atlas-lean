/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Involutions in quotients by a normal closure (Kourovka Notebook Problem 18.94)

We use the Klein bottle group in the form ℤ ⋊ ℤ, with the second generator acting by
inversion on the first factor. The elements `a = (0, 1)` and `b = (1, 1)` have the same square.
Killing `a` makes the image of `b` square to one, and its odd first coordinate detects it
in the quotient.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.InvolutionFreeQuotientKourovka18Problem94Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.94 (A. I.
Sozutov). UnsolvedMath record UM-00701523 (`KOU-18.94`), dataset ulamai/UnsolvedMath v1.8.0.

Without involutions means `g² = 1 → g = 1`; `⟨(aⁿ)^G⟩` is the normal closure of `aⁿ`.
-/

/-- **Sozutov's question on involutions in quotients (Kourovka 18.94).** This is the statement
that whenever $G$ is a group without involutions (if $g^2 = 1$ then $g = 1$), $a \in G$ is not the
square of any element of $G$, and $n$ is an odd natural number, the quotient of $G$ by the normal
closure of $a^n$ has no involutions: every element $y$ of the quotient with $y^2 = 1$ is $1$. -/
def involutionFreeQuotientByNonSquarePower : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, g ^ 2 = 1 → g = 1) → ∀ a : G, (¬ ∃ x : G, x ^ 2 = a) →
    ∀ n : ℕ, Odd n → ∀ y : G ⧸ Subgroup.normalClosure {a ^ n}, y ^ 2 = 1 → y = 1

private abbrev inversionAction : Multiplicative ℤ →* MulAut (Multiplicative ℤ) :=
  zpowersHom _ (MulEquiv.inv _)

private abbrev KleinBottle := Multiplicative ℤ ⋊[inversionAction] Multiplicative ℤ

private theorem kleinBottle_sq_eq_one (g : KleinBottle) (hg : g ^ 2 = 1) : g = 1 := by
  rw [sq] at hg
  have hr := congrArg (fun x : KleinBottle ↦ x.right.toAdd) hg
  change g.right.toAdd + g.right.toAdd = 0 at hr
  have hr' : g.right = 1 := show g.right.toAdd = 0 by omega
  apply SemidirectProduct.ext _ hr'
  have hl := congrArg SemidirectProduct.left hg
  simp only [SemidirectProduct.mul_left, hr', map_one, MulAut.one_apply,
    SemidirectProduct.one_left] at hl
  change g.left.toAdd + g.left.toAdd = 0 at hl
  change g.left.toAdd = 0
  omega

/-- Inversion preserves parity, so the first coordinate modulo two is a homomorphism. -/
private def leftParity : KleinBottle →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (g.left.toAdd : ZMod 2)
  map_one' := rfl
  map_mul' g h := by
    have hinv : (MulEquiv.inv (Multiplicative ℤ) : MulAut _) ^ (2 : ℤ) = 1 := by
      ext x
      exact inv_inv x
    change ((g.left.toAdd + ((inversionAction g.right) h.left).toAdd : ℤ) : ZMod 2) =
      (g.left.toAdd : ZMod 2) + (h.left.toAdd : ZMod 2)
    rw [Int.cast_add]
    congr 1
    rcases Int.even_or_odd' g.right.toAdd with ⟨k, hk | hk⟩
    · simp [inversionAction, hk, zpow_mul, hinv]
    · simp [inversionAction, hk, zpow_add, zpow_mul, hinv,
        ZMod.neg_eq_self_mod_two]

/--
**Quotients by the normal closure of an odd power of a non-square can have involutions.** There
exist a group $G$ without involutions (if $g^2 = 1$ then $g = 1$), an element $a \in G$ that is
not the square of any element of $G$, and an odd natural number $n$ such that the quotient of $G$
by the normal closure of $a^n$ contains an involution, that is, an element $y \ne 1$ with
$y^2 = 1$. This answers Kourovka Problem 18.94 in the negative.

Besides an example of V. I. Trofimov, the group $G = \langle a, b \mid a^2 = b^2 \rangle$ with
$n = 1$ is an example: its quotient by the normal closure of $a$ has order $2$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.94 (A. I.
Sozutov); resolution: V. I. Trofimov (example), as recorded in the Kourovka Archive, Problem 18.94,
Kourovka Archive, Problem 18.94: No, not always, by an example of V. I. Trofimov; another example: G
= ⟨a, b | a² = b²⟩ modulo ⟨a^G⟩ has order 2, https://arxiv.org/abs/1401.0300v49.
-/
theorem involutionFreeQuotientByNonSquarePower_refuted :
    ¬ involutionFreeQuotientByNonSquarePower := by
  let a : KleinBottle := ⟨1, Multiplicative.ofAdd 1⟩
  let b : KleinBottle := ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩
  have ha : ¬ ∃ x : KleinBottle, x ^ 2 = a := by
    rintro ⟨x, hx⟩
    rw [sq] at hx
    have hr := congrArg (fun g : KleinBottle ↦ g.right.toAdd) hx
    change x.right.toAdd + x.right.toAdd = 1 at hr
    omega
  have hab : b ^ 2 = a ^ 2 := rfl
  let N := Subgroup.normalClosure ({a ^ 1} : Set KleinBottle)
  let q := QuotientGroup.mk' N
  have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).2 (Subgroup.subset_normalClosure (by simp))
  have hqb : q b ^ 2 = 1 := by rw [← map_pow, hab, map_pow, hqa, one_pow]
  intro h
  have hb := h KleinBottle kleinBottle_sq_eq_one a ha 1 odd_one (q b) hqb
  have hN : N ≤ leftParity.ker :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr (by rw [pow_one]; rfl))
  have hparity := hN ((QuotientGroup.eq_one_iff b).1 hb)
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) hparity

end MathlibExt.GroupTheory.InvolutionFreeQuotientKourovka18Problem94Wanted
