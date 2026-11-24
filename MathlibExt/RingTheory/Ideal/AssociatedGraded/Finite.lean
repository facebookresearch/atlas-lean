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
# Finiteness of fixed associated-graded pieces

Finite generation of the filtration ideal makes every ring piece finite over the degree-zero
quotient. If the filtered module is finite as well, every module piece is finite. These named
providers use only finite-generation hypotheses and preserve the literal quotient carriers.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Ideal

universe u v

variable {R : Type u} [CommRing R]

/-- If `I` is finitely generated, its degree-`n` associated-graded piece is finite over `R ⧸ I`. -/
theorem associatedGradedPiece_finite_of_fg
    (I : Ideal R) (hI : I.FG) (n : ℕ) :
    Module.Finite (R ⧸ I) (I.AssociatedGradedPiece n) := by
  let _ : Module.Finite R (I ^ n : Ideal R) :=
    Module.Finite.iff_fg.mpr (Ideal.FG.pow hI)
  infer_instance

/-- If `I` and `M` are finite, the degree-`n` associated-graded module piece is finite over
`R ⧸ I`. -/
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
