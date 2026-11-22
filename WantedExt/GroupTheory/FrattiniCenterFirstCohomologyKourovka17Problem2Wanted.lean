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

/-- `x` lies in the centre `Z(Φ(G))` of the Frattini subgroup. -/
def InFrattiniCenter {G : Type*} [Group G] (x : G) : Prop :=
  x ∈ frattini G ∧ ∀ y ∈ frattini G, x * y = y * x

/-- `H¹(G/Φ(G), Z(Φ(G))) = 0` for the conjugation action. A 1-cocycle of `G/Φ(G)` with values in
`Z(Φ(G))` is recorded by its inflation to `G`: a map `δ : G → Z(Φ(G))` with
`δ (g h) = δ g · g (δ h) g⁻¹` that is trivial on `Φ(G)` (such maps are exactly the inflations).
The class vanishes when the cocycle is a coboundary `δ g = g a g⁻¹ a⁻¹` with `a ∈ Z(Φ(G))`. -/
def FrattiniCenterH1Trivial (G : Type*) [Group G] : Prop :=
  ∀ δ : G → G, (∀ g, InFrattiniCenter (δ g)) → (∀ g h, δ (g * h) = δ g * (g * δ h * g⁻¹)) →
    (∀ g ∈ frattini G, δ g = 1) → ∃ a : G, InFrattiniCenter a ∧ ∀ g, δ g = g * a * g⁻¹ * a⁻¹

/-- Kourovka 17.2 (A. Abdollahi; P. Schmid's question): there is a finite non-abelian `p`-group
`G` with `H¹(G/Φ(G), Z(Φ(G))) = 0`. -/
def nonabelianPGroupFrattiniCenterH1Trivial : Prop :=
  ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : Finite G), p.Prime ∧ IsPGroup p G ∧
    (∃ a b : G, a * b ≠ b * a) ∧ FrattiniCenterH1Trivial G

/--
Resolved true: the Kourovka Archive answers 17.2 "Yes, it does", citing Abdollahi (2011): there is a
finite non-abelian `p`-group `G` with `H¹(G/Φ(G), Z(Φ(G))) = 0`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.2 (A. Abdollahi); resolution: A.
Abdollahi, J. Algebra 342 (2011), 154-160, Kourovka Archive, Problem 17.2 (Yes, it does).
-/
public theorem_wanted nonabelianPGroupFrattiniCenterH1Trivial_holds :
    nonabelianPGroupFrattiniCenterH1Trivial

end MathlibExt.GroupTheory.FrattiniCenterFirstCohomologyKourovka17Problem2Wanted
