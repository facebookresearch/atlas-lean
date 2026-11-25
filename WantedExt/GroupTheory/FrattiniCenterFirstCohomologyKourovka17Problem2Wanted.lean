/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Vanishing `H¹(G/Φ(G), Z(Φ(G)))` for non-abelian `p`-groups (Kourovka Notebook Problem 17.2)

Kourovka Notebook, Archive of Solved Problems, Problem 17.2 (A. Abdollahi): (P. Schmid). Does there
exist a finite non-abelian `p`-group `G` such that `H¹(G/Φ(G), Z(Φ(G))) = 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.FrattiniCenterFirstCohomologyKourovka17Problem2Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.2 (A.
Abdollahi). UnsolvedMath record UM-00701304 (`KOU-17.2`), dataset ulamai/UnsolvedMath v1.8.0.

`Φ(G)` is `frattini G` and `G/Φ(G)` acts on `Z(Φ(G))` by conjugation. A 1-cocycle of `G/Φ(G)` is
recorded by its inflation to `G`: a map `δ : G → Z(Φ(G))` with `δ(gh) = δ(g) · g δ(h) g⁻¹` that is
trivial on `Φ(G)`; these maps are exactly the inflated cocycles, since `Φ(G)` centralizes `Z(Φ(G))`.
`H¹ = 0` says each such map is a coboundary `δ(g) = g a g⁻¹ a⁻¹`, `a ∈ Z(Φ(G))`.
-/

/-- **Centre of the Frattini subgroup.** An element $x$ of a group $G$ lies in the centre
$Z(\Phi(G))$ of the Frattini subgroup $\Phi(G)$ when $x \in \Phi(G)$ and $xy = yx$ for every
$y \in \Phi(G)$. -/
def InFrattiniCenter {G : Type*} [Group G] (x : G) : Prop :=
  x ∈ frattini G ∧ ∀ y ∈ frattini G, x * y = y * x

/-- **Vanishing first cohomology of $G/\Phi(G)$ in $Z(\Phi(G))$.** Let $G$ be a group, let
$\Phi(G)$ be its Frattini subgroup and let $Z(\Phi(G))$ be the centre of $\Phi(G)$. The property
holds when every map $\delta \colon G \to Z(\Phi(G))$ with
$\delta(gh) = \delta(g)\, g\, \delta(h)\, g^{-1}$ for all $g, h \in G$ and $\delta(g) = 1$ for all
$g \in \Phi(G)$ is a coboundary: there is an $a \in Z(\Phi(G))$ with $\delta(g) = g a g^{-1} a^{-1}$
for all $g \in G$.

Such maps $\delta$ are exactly the inflations to $G$ of the 1-cocycles of $G/\Phi(G)$ with values
in $Z(\Phi(G))$ for the conjugation action, so the property says
$H^1(G/\Phi(G), Z(\Phi(G))) = 0$. -/
def FrattiniCenterH1Trivial (G : Type*) [Group G] : Prop :=
  ∀ δ : G → G, (∀ g, InFrattiniCenter (δ g)) → (∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹)) →
    (∀ g ∈ frattini G, δ g = 1) → ∃ a : G, InFrattiniCenter a ∧ ∀ g, δ g = g * a * g⁻¹ * a⁻¹

/-- **Kourovka Problem 17.2 (a non-abelian $p$-group with trivial $H^1$).** The statement, a
question of P. Schmid recorded by A. Abdollahi, that there exist a prime $p$ and a finite
non-abelian $p$-group $G$ such that, writing $\Phi(G)$ for the Frattini subgroup of $G$ and
$Z(\Phi(G))$ for its centre, the first cohomology group $H^1(G/\Phi(G), Z(\Phi(G)))$ for the
conjugation action of $G/\Phi(G)$ on $Z(\Phi(G))$ is trivial. -/
def nonabelianPGroupFrattiniCenterH1Trivial : Prop :=
  ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : Finite G), p.Prime ∧ IsPGroup p G ∧
    (∃ a b : G, a * b ≠ b * a) ∧ FrattiniCenterH1Trivial G

/--
**A non-abelian $p$-group with $H^1(G/\Phi(G), Z(\Phi(G))) = 0$ (Kourovka 17.2).** There exist a
prime $p$ and a finite non-abelian $p$-group $G$ such that, writing $\Phi(G)$ for the Frattini
subgroup of $G$ and $Z(\Phi(G))$ for its centre, the first cohomology group
$H^1(G/\Phi(G), Z(\Phi(G)))$ for the conjugation action of $G/\Phi(G)$ on $Z(\Phi(G))$ is trivial.

This answers Kourovka Problem 17.2 in the affirmative: the Kourovka Archive answers "Yes, it does",
citing Abdollahi (2011).

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.2 (A. Abdollahi); resolution: A.
Abdollahi, J. Algebra 342 (2011), 154-160, Kourovka Archive, Problem 17.2 (Yes, it does).
-/
public theorem_wanted nonabelianPGroupFrattiniCenterH1Trivial_holds :
    nonabelianPGroupFrattiniCenterH1Trivial

end MathlibExt.GroupTheory.FrattiniCenterFirstCohomologyKourovka17Problem2Wanted
