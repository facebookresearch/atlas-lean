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

public import MathlibExt.KTheory.Ring.K2.MatsumotoMonomialExtension

/-!
# Tests for functorial Matsumoto monomial extensions
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open MatsumotoMonomialExtension

universe u

variable {F K L : Type u} [Field F] [Field K] [Field L]

example (f : F →+* K) (n : ℕ) :
    (PermutationBilinearCocycle.monomialGroupExtension
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)).Hom
      (PermutationBilinearCocycle.monomialGroupExtension
        (MatsumotoPermutationAction.milnorK2Bicharacter K) (Fin n)) :=
  ambientMonomialExtensionHom f n

example (f : F →+* K) (n : ℕ) :
    (monomialExtension F n).Hom (monomialExtension K n) :=
  monomialExtensionHom f n

example (f : F →+* K) (n : ℕ) (p : HM F n) :
    ambientLiftHom K n (HMMap f n p) =
      ambientMonomialLiftMap f n (ambientLiftHom F n p) :=
  HMMap_fst f n p

example (n : ℕ) :
    HMMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (HM F n) :=
  HMMap_id n

example (f : F →+* K) (g : K →+* L) (n : ℕ) :
    HMMap (F := F) (K := L) (g.comp f) n =
      (HMMap g n).comp (HMMap f n) :=
  HMMap_comp f g n
