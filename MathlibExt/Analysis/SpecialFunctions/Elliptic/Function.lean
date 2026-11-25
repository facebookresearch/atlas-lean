/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Elliptic functions
-/

@[expose] public section

namespace PeriodPair

/-- **Lattice-periodic functions.** Let $L$ be a pair of $\mathbb{R}$-linearly independent
complex numbers $\omega_1, \omega_2$ with period lattice
$\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$. A function $f : \mathbb{C} \to \mathbb{C}$
is lattice-periodic for $L$ when every element of $\Lambda$ is a period of $f$, that is,
$f(z + \omega) = f(z)$ for all $\omega \in \Lambda$ and all $z \in \mathbb{C}$. -/
def IsLatticePeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop :=
  ∀ ω : L.lattice, f.Periodic (ω : ℂ)

/-- **Elliptic functions.** Let $L$ be a pair of $\mathbb{R}$-linearly independent complex
numbers $\omega_1, \omega_2$ with period lattice
$\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$. A function $f : \mathbb{C} \to \mathbb{C}$
is an elliptic function for $L$ when it is meromorphic at every point of $\mathbb{C}$ and
lattice-periodic for $L$, that is, $f(z + \omega) = f(z)$ for all $z \in \mathbb{C}$ and all
$\omega \in \Lambda$. -/
structure IsEllipticFunction (L : PeriodPair) (f : ℂ → ℂ) : Prop where
  meromorphic : Meromorphic f
  periodic : L.IsLatticePeriodic f

theorem isLatticePeriodic_const (L : PeriodPair) (c : ℂ) :
    L.IsLatticePeriodic fun _ ↦ c :=
  fun _ _ ↦ rfl

theorem IsEllipticFunction.const (L : PeriodPair) (c : ℂ) :
    L.IsEllipticFunction fun _ ↦ c :=
  ⟨Meromorphic.const c, isLatticePeriodic_const L c⟩

theorem IsEllipticFunction.add {L : PeriodPair} {f g : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (hg : L.IsEllipticFunction g) :
    L.IsEllipticFunction (f + g) :=
  ⟨hf.meromorphic.add hg.meromorphic, fun ω ↦ (hf.periodic ω).add (hg.periodic ω)⟩

theorem IsEllipticFunction.mul {L : PeriodPair} {f g : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (hg : L.IsEllipticFunction g) :
    L.IsEllipticFunction (f * g) :=
  ⟨hf.meromorphic.mul hg.meromorphic, fun ω ↦ (hf.periodic ω).mul (hg.periodic ω)⟩

end PeriodPair
