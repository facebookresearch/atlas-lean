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

/-- Gauss reducedness for the integral binary quadratic form
`a*x^2 + b*x*y + c*y^2` in the strict source convention:

`IsGaussReduced a b c` holds iff `0 < a`, `discrim a b c < 0`,
`|b| ≤ a`, `a ≤ c`, and `(|b| = a ∨ a = c) → 0 ≤ b`.

This is Mortenson `arXiv:1702.01627v2` Section 2 line 259. In particular
`(1,-1,1)` is positive definite and satisfies the loose inequalities but
is not reduced because the tie-break requires `b ≥ 0`. -/
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
