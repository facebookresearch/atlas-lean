/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.Algebra.Homology.SpectralObject.ZeroColumnEdge

/-!
# Public clients of the native column-zero edge

These clients use independent object and morphism universes and the original
native page recipe. The representative and both of its characteristics use
lower support. Upper support and positive-column vanishing enter the
isomorphism theorem explicitly.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable (X : SpectralObject D EInt)
variable [X.HasSpectralSequence coreE₁FirstQuadrantHomological]
variable (hneg : ∀ (n a : ℤ), a < 0 →
  IsZero ((X.H n).obj
    (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))

example (q : ℕ) :
    X.stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) ⟶
      ((X.spectralSequence coreE₁FirstQuadrantHomological).page (2 : ℤ)).X (0, q) :=
  X.nativeZeroColumnStageZeroRepresentative hneg q

example (q : ℕ) : Epi (X.nativeZeroColumnStageZeroRepresentative hneg q) :=
  X.nativeZeroColumnStageZeroRepresentative_epi hneg q

example (q : ℕ) : Epi (X.nativeZeroColumnStageZeroRepresentative hneg q) := inferInstance

example (q : ℕ) :
  let n : ℤ := -(q : ℤ)
  let hLower : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let eP := X.spectralSequencePageXIso coreE₁FirstQuadrantHomological
    (2 : ℤ) (by omega) (0, q)
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (n - 1) n (n + 1)
    (by simp [n, coreE₁FirstQuadrantHomological]) (by omega) rfl
  let eL := X.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    bot_le hLower hMiddle hUpper (n - 1) n (n + 1)
    (hneg (n + 1) (-2) (by omega)) (by omega) rfl
  let g₀ := (X.cokernelSequenceE
    (homOfLE (bot_le : (⊥ : EInt) ≤ ((-1 : ℤ) : EInt)))
    (homOfLE hMiddle) (homOfLE hUpper)
    (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
    (Subsingleton.elim _ _) (n - 1) n (n + 1) (by omega) rfl).g
  X.nativeZeroColumnStageZeroRepresentative hneg q ≫ eP.hom = g₀ ≫ eL.hom :=
  X.nativeZeroColumnStageZeroRepresentative_comp_pageXIso_hom hneg q

example (q : ℕ) :
    ((X.spectralSequence coreE₁FirstQuadrantHomological).page (2 : ℤ)).X (0, q) ⟶
      (X.H (-(q : ℤ))).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (⊤ : EInt)))) :=
  X.nativeZeroColumnEdge hneg q

example (q : ℕ) :
    X.nativeZeroColumnStageZeroRepresentative hneg q ≫ X.nativeZeroColumnEdge hneg q =
      X.stableIntervalStepToAbutment (-(q : ℤ)) ((0 : ℤ) : EInt) :=
  X.nativeZeroColumnEdge_representation hneg q

example :
    X.nativeZeroColumnStageZeroRepresentative hneg 0 ≫ X.nativeZeroColumnEdge hneg 0 =
      X.stableIntervalStepToAbutment (-(0 : ℤ)) ((0 : ℤ) : EInt) :=
  X.nativeZeroColumnEdge_representation hneg 0

variable (hupper : ∀ (d : ℕ) (a : ℤ), (d : ℤ) ≤ a →
  IsZero ((X.H (-(d : ℤ))).obj
    (mk₁ (homOfLE (le_top : (a : EInt) ≤ (⊤ : EInt))))))
variable (hpos : ∀ (p t : ℕ), 1 ≤ p →
  IsZero (((X.spectralSequence coreE₁FirstQuadrantHomological).page (2 : ℤ)).X (p, t)))

example (q : ℕ) : IsIso (X.nativeZeroColumnEdge hneg q) :=
  X.isIso_nativeZeroColumnEdge hneg hupper hpos q

example : IsIso (X.nativeZeroColumnEdge hneg 0) :=
  X.isIso_nativeZeroColumnEdge hneg hupper hpos 0

example (t : ℕ) :
    IsZero (((X.spectralSequence coreE₁FirstQuadrantHomological).page (2 : ℤ)).X (1, t)) :=
  hpos 1 t le_rfl

end CategoryTheory.Abelian.SpectralObject

end
