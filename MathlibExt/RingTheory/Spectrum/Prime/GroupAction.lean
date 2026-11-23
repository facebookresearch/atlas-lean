/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Group actions on prime spectra

The group action on a prime spectrum induced by a group acting
on the underlying commutative semiring by automorphisms is provided
upstream by Mathlib (`MulAction G (PrimeSpectrum R)`). This module retains
the compatibility alias `smul_asIdeal` used within MathlibExt.
-/

@[expose] public section

open scoped Pointwise

namespace PrimeSpectrum

section Basic

variable {G R : Type*} [Group G] [CommSemiring R] [MulSemiringAction G R]

/-- **Translating a prime ideal by a group element.** Let a group $G$ act on a commutative
semiring $R$ by semiring automorphisms, and let $G$ act on the prime spectrum of $R$ by the
induced action. For every $g \in G$ and every point $\mathfrak p$ of the prime spectrum of $R$,
the prime ideal underlying the translated point $g \cdot \mathfrak p$ is the image of the ideal
$\mathfrak p$ under the automorphism of $R$ given by $g$. -/
@[simp]
theorem smul_asIdeal (g : G) (p : PrimeSpectrum R) :
    (g • p).asIdeal = g • p.asIdeal :=
  rfl

end Basic

end PrimeSpectrum
