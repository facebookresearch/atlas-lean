/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Gauss-reduced integral binary quadratic forms

This module defines the coefficient-level predicate for Gauss reducedness
following Mortenson, *A Kronecker-type identity* (Bull. LMS 49 (2017)),
author manuscript `arXiv:1702.01627v2`, Section 2, line 259.
-/

@[expose] public section

namespace BinaryQuadraticForm

/-- **Gauss-reduced binary quadratic forms.** The integral binary quadratic form
$a x^2 + b x y + c y^2$ is Gauss reduced when $a > 0$, its discriminant $b^2 - 4ac$ is negative,
$|b| \le a \le c$, and $b \ge 0$ whenever $|b| = a$ or $a = c$.

For example, $x^2 - x y + y^2$ is positive definite and satisfies $|b| \le a \le c$, but it is not
reduced, because $|b| = a$ and $b < 0$.

Source: Mortenson, *A Kronecker-type identity*, Bull. LMS 49 (2017), arXiv:1702.01627v2,
Section 2, line 259. -/
def IsGaussReduced (a b c : ℤ) : Prop :=
  0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)

theorem IsGaussReduced_iff (a b c : ℤ) :
    IsGaussReduced a b c ↔
      0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
        ((|b| = a ∨ a = c) → 0 ≤ b) :=
  Iff.rfl

theorem IsGaussReduced.mk {a b c : ℤ} (hpos : 0 < a)
    (hdisc : discrim a b c < 0) (habs : |b| ≤ a) (hac : a ≤ c)
    (hbnd : (|b| = a ∨ a = c) → 0 ≤ b) :
    IsGaussReduced a b c :=
  ⟨hpos, hdisc, habs, hac, hbnd⟩

theorem IsGaussReduced.pos {a b c : ℤ}
    (h : IsGaussReduced a b c) : 0 < a :=
  h.1

theorem IsGaussReduced.discrim_neg {a b c : ℤ}
    (h : IsGaussReduced a b c) : discrim a b c < 0 :=
  h.2.1

theorem IsGaussReduced.abs_le {a b c : ℤ}
    (h : IsGaussReduced a b c) : |b| ≤ a :=
  h.2.2.1

theorem IsGaussReduced.le {a b c : ℤ}
    (h : IsGaussReduced a b c) : a ≤ c :=
  h.2.2.2.1

theorem IsGaussReduced.boundary {a b c : ℤ}
    (h : IsGaussReduced a b c) :
    (|b| = a ∨ a = c) → 0 ≤ b :=
  h.2.2.2.2

theorem IsGaussReduced.neg_le {a b c : ℤ}
    (h : IsGaussReduced a b c) : -a ≤ b :=
  (_root_.abs_le.mp h.abs_le).1

theorem IsGaussReduced.le_of_abs_le {a b c : ℤ}
    (h : IsGaussReduced a b c) : b ≤ a :=
  (_root_.abs_le.mp h.abs_le).2

theorem IsGaussReduced.loose_bounds {a b c : ℤ}
    (h : IsGaussReduced a b c) : -a ≤ b ∧ b ≤ a :=
  _root_.abs_le.mp h.abs_le

end BinaryQuadraticForm
