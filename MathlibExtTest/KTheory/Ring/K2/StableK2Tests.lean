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

import MathlibExt.KTheory.Ring.K2.AbelianFunctor
import MathlibExt.KTheory.Ring.K2.StableSteinbergUniversal

/-!
# Stable `K₂` regression tests

Consumer-style `example` checks for the stable Steinberg and `K₂` API:
generator relations, the canonical map to stable elementary matrices and its
surjectivity, `K₂` kernel membership, ring-map naturality, and the public
centrality and universality statements, all at concrete `ℚ`/small indices,
plus same-universe ring-equivalence transport.
-/

open AlgebraicKTheory
open CategoryTheory
open scoped commutatorElement

universe u

namespace MathlibExtTest.KTheory.Ring.K2.StableK2Tests

/-- Additive Steinberg relation at `(0, 1)` over `ℚ`. -/
example (a b : ℚ) (hij : (0 : ℕ) ≠ 1) :
    StableSteinberg.x (R := ℚ) 0 1 hij a * StableSteinberg.x 0 1 hij b =
      StableSteinberg.x 0 1 hij (a + b) :=
  StableSteinberg.x_add 0 1 hij a b

/-- Distant commutator relation at `(0, 1, 2, 3)` over `ℚ`. -/
example (a b : ℚ) (hij : (0 : ℕ) ≠ 1) (hkl : (2 : ℕ) ≠ 3)
    (hil : (0 : ℕ) ≠ 3) (hjk : (1 : ℕ) ≠ 2) :
    ⁅StableSteinberg.x (R := ℚ) 0 1 hij a, StableSteinberg.x 2 3 hkl b⁆ = 1 :=
  StableSteinberg.x_comm 0 1 2 3 hij hkl hil hjk a b

/-- Chevalley relation at `(0, 1, 2)` over `ℚ`. -/
example (a b : ℚ) (hij : (0 : ℕ) ≠ 1) (hjk : (1 : ℕ) ≠ 2)
    (hik : (0 : ℕ) ≠ 2) :
    ⁅StableSteinberg.x (R := ℚ) 0 1 hij a, StableSteinberg.x 1 2 hjk b⁆ =
      StableSteinberg.x 0 2 hik (a * b) :=
  StableSteinberg.x_chev 0 1 2 hij hjk hik a b

/-- Canonical map sends `x₀₁(a)` to `e₀₁(a)`. -/
example (a : ℚ) (hij : (0 : ℕ) ≠ 1) :
    StableSteinberg.toStableE (StableSteinberg.x (R := ℚ) 0 1 hij a) =
      StableE.natElementary 0 1 hij a :=
  StableSteinberg.toStableE_x 0 1 hij a

/-- Canonical map onto stable elementary matrices is surjective. -/
example : Function.Surjective (StableSteinberg.toStableE (R := ℚ)) :=
  StableSteinberg.toStableE_surjective

/-- `K₂` inclusion lands in the Steinberg-to-elementary kernel. -/
example (x : K2 ℚ) :
    (K2.inclusion.app (RingCat.of ℚ) x : StableSteinberg ℚ) ∈
      MonoidHom.ker (StableSteinberg.toStableE (R := ℚ)) :=
  K2.inclusion_apply_mem_ker x

/-- `K₂` inclusion is natural under ring maps. -/
example (f : ℚ →+* ℚ) (x : K2 ℚ) :
    K2.inclusion.app (RingCat.of ℚ) (K2.mapRingHom f x) =
      StableSteinberg.mapRingHom f (K2.inclusion.app (RingCat.of ℚ) x) :=
  K2.inclusion_mapRingHom_apply f x

/-- Kernel of the canonical map is central. -/
example :
    MonoidHom.ker (StableSteinberg.toStableE (R := ℚ)) ≤
      Subgroup.center (StableSteinberg ℚ) :=
  StableSteinberg.ker_toStableE_le_center

/-- Stable Steinberg extension is universal among central extensions. -/
example : (StableSteinberg.steinbergExtension ℚ).IsUniversal :=
  StableSteinberg.steinbergExtension_isUniversal ℚ

/-- Ring equivalence induces an additive `K₂` equivalence. -/
noncomputable example {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    Additive (K2 R) ≃+ Additive (K2 S) :=
  K2.equivOfRingEquiv e

/-- Ring-equivalence transport acts via the functorial map. -/
example {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (x : K2 R) :
    K2.equivOfRingEquiv e (Additive.ofMul x) =
      Additive.ofMul (K2.mapRingHom e.toRingHom x) :=
  by simp

/-- `K2.equivOfRingEquiv` along `RingEquiv.refl` is the identity. -/
example (R : Type u) [Ring R] :
    K2.equivOfRingEquiv (RingEquiv.refl R) = AddEquiv.refl (Additive (K2 R)) :=
  K2.equivOfRingEquiv_id R

/-- `K2.equivOfRingEquiv` respects `RingEquiv.trans` orientation (forward). -/
example (R S T : Type u) [Ring R] [Ring S] [Ring T] (e : R ≃+* S) (e' : S ≃+* T) :
    K2.equivOfRingEquiv (e.trans e') =
      (K2.equivOfRingEquiv e).trans (K2.equivOfRingEquiv e') :=
  K2.equivOfRingEquiv_comp e e'

/-- `K2.equivOfRingEquiv` along `e.symm` is the symmetric equivalence. -/
example (R S : Type u) [Ring R] [Ring S] (e : R ≃+* S) :
    K2.equivOfRingEquiv e.symm = (K2.equivOfRingEquiv e).symm :=
  K2.equivOfRingEquiv_symm e

section RingEquivCoherence

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- The underlying hom is the additive functor map. -/
example (e : R ≃+* S) :
    (K2.equivOfRingEquiv e).toAddMonoidHom =
      (K2.addCommGrpFunctor.map (RingCat.ofHom e.toRingHom)).hom :=
  K2.equivOfRingEquiv_toAddMonoidHom e

/-- Pointwise form of the underlying additive functor map. -/
example (e : R ≃+* S) (x : Additive (K2 R)) :
    K2.equivOfRingEquiv e x =
      K2.addCommGrpFunctor.map (RingCat.ofHom e.toRingHom) x :=
  K2.equivOfRingEquiv_apply e x

/-- Pointwise forward composition has the expected application order. -/
example (e : R ≃+* S) (e' : S ≃+* T)
    (x : Additive (K2 R)) :
    K2.equivOfRingEquiv (e.trans e') x =
      K2.equivOfRingEquiv e' (K2.equivOfRingEquiv e x) := by
  simp

/-- Pointwise inverse transport agrees with the inverse additive
equivalence. -/
example (e : R ≃+* S) (x : Additive (K2 S)) :
    K2.equivOfRingEquiv e.symm x = (K2.equivOfRingEquiv e).symm x := by
  simp

end RingEquivCoherence

end MathlibExtTest.KTheory.Ring.K2.StableK2Tests
