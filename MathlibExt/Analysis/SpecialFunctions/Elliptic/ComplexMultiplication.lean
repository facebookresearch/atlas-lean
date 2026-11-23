/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Complex multiplication of period lattices

This file defines the endomorphism ring of a complex period lattice.
-/

@[expose] public section

namespace PeriodPair

/-- **Endomorphism ring of a period lattice.** Let $\omega_1, \omega_2$ be
$\mathbb{R}$-linearly independent complex numbers with period lattice
$\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$. The endomorphism ring of $\Lambda$ is the
subring of $\mathbb{C}$ consisting of all $a \in \mathbb{C}$ such that $a z \in \Lambda$ for every
$z \in \Lambda$. -/
def endomorphismRing (L : PeriodPair) : Subring ℂ where
  carrier := {a | ∀ z ∈ L.lattice, a * z ∈ L.lattice}
  mul_mem' ha hb z hz := by
    rw [mul_assoc]
    exact ha _ (hb z hz)
  one_mem' z hz := by simpa using hz
  add_mem' ha hb z hz := by
    rw [add_mul]
    exact add_mem (ha z hz) (hb z hz)
  zero_mem' _ _ := by simp
  neg_mem' ha z hz := by
    rw [neg_mul]
    exact neg_mem (ha z hz)

@[simp]
theorem mem_endomorphismRing {L : PeriodPair} {a : ℂ} :
    a ∈ L.endomorphismRing ↔ ∀ z ∈ L.lattice, a * z ∈ L.lattice :=
  Iff.rfl

/-- **Lattices that are proper ideals.** Let $\Lambda$ be the period lattice of a pair of
$\mathbb{R}$-linearly independent complex numbers, and let $\mathcal{O}$ be a subring of
$\mathbb{C}$. Then $\Lambda$ is a proper ideal of $\mathcal{O}$ when the endomorphism ring of
$\Lambda$, the subring of all $a \in \mathbb{C}$ with $a z \in \Lambda$ for every $z \in \Lambda$,
equals $\mathcal{O}$.

The ambient assumptions that $\mathcal{O}$ is an imaginary quadratic order and that $\Lambda$ is
an $\mathcal{O}$-ideal are deliberately kept separate from this predicate. -/
def IsProperIdeal (L : PeriodPair) (𝒪 : Subring ℂ) : Prop :=
  L.endomorphismRing = 𝒪

@[simp]
theorem isProperIdeal_endomorphismRing (L : PeriodPair) :
    L.IsProperIdeal L.endomorphismRing :=
  rfl

end PeriodPair
