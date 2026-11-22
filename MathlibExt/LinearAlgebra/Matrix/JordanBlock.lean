/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Jordan blocks

The canonical field-valued Jordan block and its entry formula live here so clients can
use them without importing the Jordan normal-form existence proof.
-/

@[expose] public section

universe v

variable {K : Type*} [Field K]

namespace MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

/--
A Jordan block of size `s` with eigenvalue `μ`: `μ` on the diagonal, `1` on the first
superdiagonal, `0` elsewhere.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
Jordan normal form; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Section 3.4.
-/
def jordanBlock (s : ℕ) (μ : K) : Matrix (Fin s) (Fin s) K :=
  fun i j => if i.val + 1 = j.val then 1 else if i = j then μ else 0

/--
Characteristic entrywise description of a Jordan block.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
Jordan normal form; https://en.wikipedia.org/wiki/Jordan_normal_form.
-/
theorem jordanBlock_apply (s : ℕ) (μ : K) (i j : Fin s) :
    jordanBlock s μ i j = (if i.val + 1 = j.val then 1 else if i = j then μ else 0) := rfl

end MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
