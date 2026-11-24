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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsMonomialExtension

/-!
# Tests for functorial Matsumoto--Tits monomial extensions
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open MatsumotoTitsMonomialExtension

universe u

variable {F K L : Type u} [Field F] [Field K] [Field L]

example (f : F →+* K) (n : ℕ) :
    (titsMonomialGroupExtension F n).Hom
      (titsMonomialGroupExtension K n) :=
  ambientTitsMonomialExtensionHom f n

example (f : F →+* K) (n : ℕ) :
    (titsMonomialExtension F n).Hom (titsMonomialExtension K n) :=
  titsMonomialExtensionHom f n

example (f : F →+* K) (n : ℕ) (p : HMTits F n) :
    ambientLiftHom K n (HMTitsMap f n p) =
      titsMonomialLiftMap f n (ambientLiftHom F n p) :=
  HMTitsMap_fst f n p

example (n : ℕ) :
    HMTitsMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (HMTits F n) :=
  HMTitsMap_id n

example (f : F →+* K) (g : K →+* L) (n : ℕ) :
    HMTitsMap (F := F) (K := L) (g.comp f) n =
      (HMTitsMap g n).comp (HMTitsMap f n) :=
  HMTitsMap_comp f g n
