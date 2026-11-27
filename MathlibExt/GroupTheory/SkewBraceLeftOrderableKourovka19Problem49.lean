/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Defs.Unbundled
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Order.RelClasses

/-!
# A skew brace with a non-left-orderable additive group

Nasybullov's skew brace on the integers refutes Kourovka Notebook Problem 19.49.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.49 (V.
Lebed, L. Vendramin). UnsolvedMath record UM-00701597 (`KOU-19.49`), dataset ulamai/UnsolvedMath
v1.8.0.

A skew brace is a type `B` with an `AddGroup` and a `Group` structure satisfying `a * (b + c) = a *
b - a + a * c`, where `x - y = x + (-y)`. A group is left-orderable when some strict total order is
invariant under left multiplication (left addition for `+`).
-/

/-- **Left-orderable multiplication.** The multiplication of a set $B$ is left-orderable when there
is a strict total order $<$ on $B$ that is invariant under left multiplication: for all
$a, b, c \in B$, if $b < c$ then $a b < a c$. -/
def LeftOrderableMul (B : Type*) [Mul B] : Prop :=
  ∃ r : B → B → Prop, IsStrictTotalOrder B r ∧ ∀ a b c : B, r b c → r (a * b) (a * c)

/-- **Left-orderable addition.** The addition of a set $B$ is left-orderable when there is a strict
total order $<$ on $B$ that is invariant under left addition: for all $a, b, c \in B$, if $b < c$
then $a + b < a + c$. -/
def LeftOrderableAdd (B : Type*) [Add B] : Prop :=
  ∃ r : B → B → Prop, IsStrictTotalOrder B r ∧ ∀ a b c : B, r b c → r (a + b) (a + c)

/-- **Left-orderability of the additive group of a skew brace (Kourovka 19.49).** The statement
that for every skew brace $B$, that is, a set with two group structures, an addition $+$ (not
necessarily commutative) and a multiplication $\cdot$, satisfying
$a \cdot (b + c) = a \cdot b - a + a \cdot c$ for all $a, b, c \in B$: if the multiplication of
$B$ is left-orderable, then the addition of $B$ is left-orderable. -/
def skewBraceAdditiveLeftOrderable : Prop :=
  ∀ (B : Type) [AddGroup B] [Group B], (∀ a b c : B, a * (b + c) = a * b - a + a * c) →
    LeftOrderableMul B → LeftOrderableAdd B

private theorem negOnePow_sign_mul (a b : ℤ) :
    ((a.negOnePow : ℤ) * b).negOnePow = b.negOnePow := by
  rcases Int.units_eq_one_or a.negOnePow with h | h <;>
    simp only [h, Units.val_one, Units.val_neg, one_mul, neg_mul, Int.negOnePow_neg]

private theorem sign_mul_sign_mul (a b : ℤ) :
    (a.negOnePow : ℤ) * ((a.negOnePow : ℤ) * b) = b := by
  rw [← mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul]

private def braceAdd (a b : Multiplicative ℤ) : Multiplicative ℤ :=
  Multiplicative.ofAdd (a.toAdd + (a.toAdd.negOnePow : ℤ) * b.toAdd)

/-- The twisted addition on the integers in Nasybullov's counterexample. -/
@[instance_reducible]
private def braceAddGroup : AddGroup (Multiplicative ℤ) := by
  letI : Add (Multiplicative ℤ) := ⟨braceAdd⟩
  letI : Zero (Multiplicative ℤ) := ⟨Multiplicative.ofAdd 0⟩
  letI : Neg (Multiplicative ℤ) :=
    ⟨fun a => Multiplicative.ofAdd (-((a.toAdd.negOnePow : ℤ) * a.toAdd))⟩
  refine AddGroup.ofLeftAxioms (fun a b c => ?_) (fun a => ?_) (fun a => ?_)
  · apply Multiplicative.toAdd.injective
    change (braceAdd (braceAdd a b) c).toAdd = (braceAdd a (braceAdd b c)).toAdd
    simp only [braceAdd, toAdd_ofAdd, Int.negOnePow_add, negOnePow_sign_mul,
      Units.val_mul, mul_add, mul_assoc, add_assoc]
  · apply Multiplicative.toAdd.injective
    change (braceAdd (Multiplicative.ofAdd 0) a).toAdd = a.toAdd
    simp only [braceAdd, toAdd_ofAdd, Int.negOnePow_zero, Units.val_one, one_mul, zero_add]
  · apply Multiplicative.toAdd.injective
    change (braceAdd (Multiplicative.ofAdd (-((a.toAdd.negOnePow : ℤ) * a.toAdd))) a).toAdd = 0
    simp only [braceAdd, toAdd_ofAdd, Int.negOnePow_neg, negOnePow_sign_mul, neg_add_cancel]

attribute [local instance] braceAddGroup

private theorem brace_distrib (a b c : Multiplicative ℤ) :
    a * (b + c) = a * b - a + a * c := by
  have translate : a * c = a + Multiplicative.ofAdd ((a.toAdd.negOnePow : ℤ) * c.toAdd) := by
    apply Multiplicative.toAdd.injective
    change a.toAdd + c.toAdd = a.toAdd + (a.toAdd.negOnePow : ℤ) *
      ((a.toAdd.negOnePow : ℤ) * c.toAdd)
    rw [sign_mul_sign_mul]
  rw [translate, sub_eq_add_neg, add_assoc, neg_add_cancel_left]
  apply Multiplicative.toAdd.injective
  change (a * braceAdd b c).toAdd =
    (braceAdd (a * b) (Multiplicative.ofAdd ((a.toAdd.negOnePow : ℤ) * c.toAdd))).toAdd
  simp only [toAdd_mul, braceAdd, toAdd_ofAdd, Int.negOnePow_add, Units.val_mul, add_assoc,
    mul_assoc]
  rw [mul_left_comm (a.toAdd.negOnePow : ℤ), sign_mul_sign_mul]

/--
**A skew brace whose additive group is not left-orderable.** There is a skew brace $B$, that is, a
set with two group structures, an addition $+$ and a multiplication $\cdot$, satisfying
$a \cdot (b + c) = a \cdot b - a + a \cdot c$ for all $a, b, c \in B$, whose multiplication is
left-orderable but whose addition is not left-orderable. That is, the statement of Kourovka
Problem 19.49 fails.

Nasybullov's example (Example 3.1) is $\mathbb{Z}$ with addition $a \oplus b = a + (-1)^a b$ and
multiplication $a \odot b = a + b$: the multiplicative group is infinite cyclic, hence
left-orderable, while the additive group is infinite dihedral and has an element of order $2$, so
it is not left-orderable. The Kourovka Archive answers 19.49 "No, not always".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 19.49 (V. Lebed, L. Vendramin); resolution: T. Nasybullov, Connections between
properties of the additive and the multiplicative groups of a two-sided skew brace, J. Algebra 540
(2019), 156-167 (arXiv:1809.09418), Example 3.1: on ℤ, a ⊕ b = a + (−1)^a b and a ⊙ b = a + b define
a skew brace with infinite cyclic multiplicative group and infinite dihedral additive group, which
has 2-torsion and so is not left-orderable, answering Problem 19.49; Kourovka Archive, Problem
19.49: No, not always, https://arxiv.org/abs/1809.09418.
-/
theorem skewBraceAdditiveLeftOrderable_refuted : ¬ skewBraceAdditiveLeftOrderable := by
  intro h
  have hMul : LeftOrderableMul (Multiplicative ℤ) :=
    ⟨(· < ·), inferInstance, fun a _ _ hbc => Int.add_lt_add_left hbc a.toAdd⟩
  obtain ⟨r, hr, hAdd⟩ := h (Multiplicative ℤ) brace_distrib hMul
  let x : Multiplicative ℤ := Multiplicative.ofAdd 1
  have hx : x ≠ 0 := by decide
  have hxx : x + x = 0 := rfl
  -- Left addition by x exchanges x and 0.
  rcases trichotomous_of r x 0 with hlt | heq | hgt
  · exact asymm_of r hlt (by simpa only [hxx, add_zero] using hAdd x x 0 hlt)
  · exact hx heq
  · exact asymm_of r hgt (by simpa only [hxx, add_zero] using hAdd x 0 x hgt)

end MathlibExt.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49Wanted
