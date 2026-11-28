/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Module
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Finite generation in a fixed graded degree

Let `R` be a commutative ring and `I` a finitely generated ideal. For every `n : ℕ`, the
quotient `I^n/I^(n+1)` is a finitely generated module over `R/I`.

If `M` is a finitely generated `R`-module, then each module piece `I^n M/I^(n+1) M` is also
finitely generated over `R/I`.

References: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapters 2 and 10.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Ideal

universe u v

variable {R : Type u} [CommRing R]

/-- Let `R` be a commutative ring, `I : Ideal R` a finitely generated ideal (`I.FG`), and `n : ℕ`.
The degree-`n` quotient `I.AssociatedGradedPiece n = I^n/I^(n+1)` is a finitely generated
`R/I`-module: `Module.Finite (R ⧸ I) (I.AssociatedGradedPiece n)`. -/
theorem associatedGradedPiece_finite_of_fg
    (I : Ideal R) (hI : I.FG) (n : ℕ) :
    Module.Finite (R ⧸ I) (I.AssociatedGradedPiece n) := by
  let _ : Module.Finite R (I ^ n : Ideal R) :=
    Module.Finite.iff_fg.mpr (Ideal.FG.pow hI)
  infer_instance

/-- Let `R` be a commutative ring, `M` a finitely generated `R`-module, and `I : Ideal R` a
finitely generated ideal (`I.FG`). For every `n : ℕ`, `I.AssociatedGradedModulePiece M n = I^n
M/I^(n+1) M` is a finitely generated module over `R/I`. -/
theorem associatedGradedModulePiece_finite_of_fg
    (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I.FG) (n : ℕ) :
    Module.Finite (R ⧸ I) (I.AssociatedGradedModulePiece M n) := by
  have hnum : (I ^ n • (⊤ : Submodule R M)).FG :=
    Submodule.FG.smul (Ideal.FG.pow hI) Module.Finite.fg_top
  let _ : Module.Finite R ↥(I ^ n • (⊤ : Submodule R M)) :=
    Module.Finite.iff_fg.mpr hnum
  infer_instance

end Ideal
