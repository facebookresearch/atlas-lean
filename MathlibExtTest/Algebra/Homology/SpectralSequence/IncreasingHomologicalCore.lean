/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.SpectralSequence.IncreasingHomologicalCore

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory

namespace CategoryTheory.Abelian.SpectralObject

example (p q : ℕ) :
    coreE₁IncreasingHomologicalNat.deg (p, q) =
      -(p : ℤ) - (q : ℤ) := by
  simp

example (p q : ℕ) :
    coreE₁IncreasingHomologicalNat.i₁ (p, q) =
      (((p : ℤ) - 1 : ℤ) : EInt) := by
  simp

example (p q : ℕ) :
    coreE₁IncreasingHomologicalNat.i₂ (p, q) =
      ((p : ℤ) : EInt) := by
  simp

example (q : ℕ) :
    coreE₁IncreasingHomologicalNat.i₁ (0, q) =
      ((-1 : ℤ) : EInt) := by
  simp

example (q : ℕ) :
    coreE₁IncreasingHomologicalNat.i₂ (0, q) =
      ((0 : ℤ) : EInt) := by
  simp

example (p q : ℕ) :
    coreE₁IncreasingHomologicalNat.i₀ 1 (p, q) =
      coreE₁IncreasingHomologicalNat.i₁ (p, q) :=
  SpectralSequenceDataCore.hi₀₁ (data := coreE₁IncreasingHomologicalNat) (p, q)

example (p q : ℕ) :
    coreE₁IncreasingHomologicalNat.i₂ (p, q) =
      coreE₁IncreasingHomologicalNat.i₃ 1 (p, q) :=
  SpectralSequenceDataCore.hi₂₃ (data := coreE₁IncreasingHomologicalNat) (p, q)

end CategoryTheory.Abelian.SpectralObject
