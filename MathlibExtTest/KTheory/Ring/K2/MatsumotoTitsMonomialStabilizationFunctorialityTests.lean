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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsMonomialStabilization

/-!
# Tests for functorial Matsumoto--Tits monomial stabilization
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open MatsumotoTitsMonomialExtension

universe u

variable (F : Type u) [Field F]

example (n : ℕ) :
    (titsMonomialGroupExtension F n).Hom
      (titsMonomialGroupExtension F (n + 1)) :=
  ambientTitsMonomialSuccExtensionHom F n

example (n : ℕ) :
    (titsMonomialExtension F n).Hom
      (titsMonomialExtension F (n + 1)) :=
  titsMonomialSuccExtensionHom F n

example (n : ℕ) (p : HMTits F n) :
    ambientLiftHom F (n + 1) (HMTitsSuccHom F n p) =
      titsMonomialLiftSuccHom F n (ambientLiftHom F n p) :=
  HMTitsSuccHom_ambient F n p

example (n : ℕ) (c : Multiplicative (MilnorK F 2)) :
    HMTitsSuccHom F n (inlHom F n c) = inlHom F (n + 1) c :=
  HMTitsSuccHom_inl F n c
