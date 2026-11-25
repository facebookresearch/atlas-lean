/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.MeromorphicAtCusps

/-!
# Modular functions

This module defines modular functions on the upper half-plane for an
arbitrary subgroup of `SL(2, ℤ)`: meromorphic functions invariant under
the group action and meromorphic at the cusps.
-/

@[expose]
public section

open scoped UpperHalfPlane MatrixGroups

namespace ModularFunction

/-- **Meromorphy on the upper half-plane.** A function $f \colon \mathbb{H} \to \mathbb{C}$ on
the upper half-plane is meromorphic when there is a function $g \colon \mathbb{C} \to \mathbb{C}$
that is meromorphic on the open set $\{z \in \mathbb{C} : \operatorname{Im} z > 0\}$ and
satisfies $g(\tau) = f(\tau)$ for every $\tau \in \mathbb{H}$. -/
def IsMeromorphicOnH (f : ℍ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, MeromorphicOn g UpperHalfPlane.upperHalfPlaneSet ∧
    ∀ τ : ℍ, g (τ : ℂ) = f τ

/-- **Invariance under a subgroup of the modular group.** Let $\Gamma$ be a subgroup of
$\mathrm{SL}(2, \mathbb{Z})$. A function $f \colon \mathbb{H} \to \mathbb{C}$ on the upper
half-plane is invariant under $\Gamma$ when $f(\gamma \cdot \tau) = f(\tau)$ for every
$\gamma \in \Gamma$ and every $\tau \in \mathbb{H}$, where $\gamma$ acts on $\mathbb{H}$ by
Möbius transformations. -/
def IsInvariantUnder (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∀ (γ : SL(2, ℤ)), γ ∈ Γ → ∀ τ : ℍ, f (γ • τ) = f τ

end ModularFunction

open ModularFunction

/-- **Modular functions.** Let $\Gamma$ be a subgroup of $\mathrm{SL}(2, \mathbb{Z})$. A function
$f \colon \mathbb{H} \to \mathbb{C}$ on the upper half-plane is a modular function for $\Gamma$
when it is meromorphic on $\mathbb{H}$, invariant under $\Gamma$, and meromorphic at the cusps.

No congruence hypothesis is assumed on $\Gamma$. -/
structure IsModularFunction (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop where
  meromorphicOnH : IsMeromorphicOnH f
  invariant : IsInvariantUnder f Γ
  meromorphicAtCusps : IsMeromorphicAtCusps f
