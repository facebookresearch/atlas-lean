/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.ExactSequencePowIndex

@[expose] public section

/-- Consumer with the original binders. -/
example {G U F : Type*} [CommGroup G] [CommGroup U] [CommGroup F]
    (ι : U →* G) (φ : G →* F) (hι : Function.Injective ι)
    (hφ : Function.Surjective φ) (hexact : ι.range = φ.ker) {n : ℕ}
    (hF : ∀ x : F, x ^ n = 1 → x = 1) :
    (powMonoidHom n : G →* G).range.index
      = (powMonoidHom n : F →* F).range.index
        * (powMonoidHom n : U →* U).range.index :=
  MonoidHom.index_range_powMonoidHom_eq_mul_of_exact ι φ hι hφ hexact hF

/-- The same consumer in a higher universe. -/
example {G U F : Type 1} [CommGroup G] [CommGroup U] [CommGroup F]
    (ι : U →* G) (φ : G →* F) (hι : Function.Injective ι)
    (hφ : Function.Surjective φ) (hexact : ι.range = φ.ker) {n : ℕ}
    (hF : ∀ x : F, x ^ n = 1 → x = 1) :
    (powMonoidHom n : G →* G).range.index
      = (powMonoidHom n : F →* F).range.index
        * (powMonoidHom n : U →* U).range.index :=
  MonoidHom.index_range_powMonoidHom_eq_mul_of_exact ι φ hι hφ hexact hF

/-- Boundary: the torsion hypothesis on the quotient is not automatic.
In the group of order two, the nontrivial element is killed by squaring,
so the hypothesis fails for exponent two. -/
example : ¬ ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 → x = 1 := by
  intro h
  have h1 := h (Multiplicative.ofAdd 1) (by decide)
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [toAdd_ofAdd, toAdd_one] at h2
  exact (by decide : (1 : ZMod 2) ≠ 0) h2
