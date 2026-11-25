/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.FractionalIdeal.GroupAction
public import MathlibExt.RingTheory.Spectrum.Prime.GroupAction

/-!
# Compatibility of fractional-ideal and prime-spectrum actions
-/

@[expose] public section

open scoped nonZeroDivisors Pointwise

namespace PrimeSpectrum

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R] [CommRing K]
  [MulSemiringAction G R] [Algebra R K] [IsFractionRing R K]

/-- **Viewing prime ideals as fractional ideals commutes with the group action.** Let a group $G$
act on an integral domain $R$ by ring automorphisms, let $K$ be a fraction field of $R$, and let
$G$ act on the fractional ideals of $R$ in $K$ through the extension of each automorphism of $R$
to $K$. For $g \in G$ and a prime ideal $\mathfrak p$ of $R$, write
$g \cdot \mathfrak p = \{g \cdot x : x \in \mathfrak p\}$ for the image of $\mathfrak p$ under
$g$, again a prime ideal of $R$. Then for every $g \in G$ and every prime ideal $\mathfrak p$ of
$R$, the ideal $g \cdot \mathfrak p$ viewed as a fractional ideal in $K$ equals $g$ applied to
$\mathfrak p$ viewed as a fractional ideal in $K$. -/
@[simp]
theorem smul_asIdeal_coe (g : G) (p : PrimeSpectrum R) :
    FractionalIdeal.coeIdeal (S := R⁰) (P := K) (g • p).asIdeal =
      g • FractionalIdeal.coeIdeal (S := R⁰) (P := K) p.asIdeal := by
  rw [smul_asIdeal, FractionalIdeal.smul_coeIdeal]

end PrimeSpectrum
