/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.FrobeniusGeometry

/-! # Tests for the absolute and geometric Frobenius of schemes

The `p`-th power endomorphism (including on the zero ring, where `p` is not the characteristic),
the action of the absolute Frobenius on points and sections, its naturality, the geometric
Frobenius over a finite field, and the computation on `Spec F_p`, where the Frobenius acts
trivially on global sections.
-/

open CategoryTheory AlgebraicGeometry MathlibExt.AlgebraicGeometry.FrobeniusGeometry

namespace MathlibExtTest.AlgebraicGeometry.FrobeniusGeometry

variable (p : ℕ) [Fact p.Prime]

example (x : ZMod p) : primePowerEndomorphism (ZMod p) p (ZMod.natCast_self p) x = x ^ p :=
  primePowerEndomorphism_apply _ p _ x

/-- On the zero ring, where `p = 0` without `p` being the characteristic, the endomorphism is
still the `p`-th power map. -/
example (x : PUnit) : primePowerEndomorphism PUnit p (Subsingleton.elim _ _) x = x ^ p :=
  primePowerEndomorphism_apply _ p _ x

variable {X Y : Scheme} (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)

example (x : X) : absoluteFrobenius X p hX x = x := rfl

example (U : X.Opens) (g : Γ(X, U)) : (absoluteFrobenius X p hX).app U g = g ^ p :=
  absoluteFrobenius_app_apply X p hX U g

/-- `p` vanishes on every open, including the empty one, whose ring of sections is zero. -/
example (U : X.Opens) : (p : Γ(X, U)) = 0 := cast_eq_zero_of_isInCharacteristic hX U

example (f : X ⟶ Y) : absoluteFrobenius X p hX ≫ f = f ≫ absoluteFrobenius Y p hY :=
  absoluteFrobenius_naturality p hX hY f

example (n : ℕ) (g : Γ(X, ⊤)) :
    (End.asHom (End.of (absoluteFrobenius X p hX) ^ n)).appTop g = g ^ p ^ n := by
  simp

/-- The geometric Frobenius over `F_q`, `q = p ^ f`, is a morphism over `F_q` whose underlying
morphism is the `f`-th power of the absolute Frobenius. -/
example {k : Type} [Field k] [Fintype k] [CharP k p] (Z : Over (Spec (.of k))) (f : ℕ)
    (hcard : Fintype.card k = p ^ f) :
    (geometricFrobenius Z p f hcard).left ≫ Z.hom = Z.hom ∧
      (geometricFrobenius Z p f hcard).left =
        End.asHom (End.of (absoluteFrobenius Z.left p (isInCharacteristic_of_over Z)) ^ f) :=
  ⟨Over.w _, rfl⟩

example (Z : Over (Spec (CommRingCat.of (ZMod p)))) :
    (primeFieldFrobenius p Z).left = absoluteFrobenius Z.left p (isInCharacteristic_of_over Z) :=
  primeFieldFrobenius_left p Z

/-- On `Spec F_p` the absolute Frobenius acts trivially on global sections (`a ^ p = a`). -/
example (a : ZMod p) :
    (absoluteFrobenius (Spec (.of (ZMod p))) p
        (isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of (ZMod p))))))).appTop
      ((Scheme.ΓSpecIso (.of (ZMod p))).inv a) = (Scheme.ΓSpecIso (.of (ZMod p))).inv a := by
  refine (absoluteFrobenius_app_apply _ p _ ⊤ _).trans ?_
  rw [← map_pow, ZMod.pow_card]

end MathlibExtTest.AlgebraicGeometry.FrobeniusGeometry
