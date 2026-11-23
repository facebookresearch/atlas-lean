/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 22, Problem 7082
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace MathlibExt.Analysis.AMR22Problem7082Wanted

/-! Source record `AMR-022-7082__2307082`. -/

/-- **Open unit disc.** The open unit disc $\mathbb{D}$ is the set of complex numbers $z$ with
$|z| < 1$, the open ball of radius $1$ about $0$ in $\mathbb{C}$. -/
def UnitDisc : Set ℂ := Metric.ball (0 : ℂ) 1

/-- **Injectivity at each parameter of the disc.** Let $\mathbb{D}$ be the open unit disc, $E$ a
set of complex numbers and $F$ a function assigning a complex number $F(w, z)$ to each pair of
complex numbers $w, z$. Condition (a) holds for $E$ and $F$ when, for every $z \in \mathbb{D}$,
the map $w \mapsto F(w, z)$ is injective on $E$.

This is condition (a) of Problem 7.82 in AMR-022-7082. -/
def IsInjectiveInParam (E : Set ℂ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ z ∈ UnitDisc, Set.InjOn (fun w => F w z) E

/-- **Holomorphic dependence of a motion on the parameter.** Let $\mathbb{D}$ be the open unit
disc, $E$ a set of complex numbers and $F$ a function assigning a complex number $F(w, z)$ to
each pair of complex numbers $w, z$. Condition (b) holds for $E$ and $F$ when, for every
$w \in E$, the map $z \mapsto F(w, z)$ is analytic on $\mathbb{D}$.

This is condition (b) of Problem 7.82 in AMR-022-7082. -/
def IsAnalyticInDisc (E : Set ℂ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ w ∈ E, AnalyticOn ℂ (F w) UnitDisc

/-- **Motion equal to the identity at parameter zero.** Let $E$ be a set of complex numbers and
$F$ a function assigning a complex number $F(w, z)$ to each pair of complex numbers $w, z$.
Condition (c) holds for $E$ and $F$ when $F(w, 0) = w$ for every $w \in E$.

This is condition (c) of Problem 7.82 in AMR-022-7082. -/
def IsNormalizedAtZero (E : Set ℂ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ w ∈ E, F w 0 = w

/-- **Agreement of two motions on a set.** Let $\mathbb{D}$ be the open unit disc, $E$ a set of
complex numbers, and $F$ and $G$ functions assigning complex numbers $F(w, z)$ and $G(w, z)$ to
each pair of complex numbers $w, z$. Then $G$ agrees with $F$ on $E$ when $G(w, z) = F(w, z)$
for every $w \in E$ and every $z \in \mathbb{D}$. -/
def AgreesOnDisc (E : Set ℂ) (F G : ℂ → ℂ → ℂ) : Prop :=
  ∀ w ∈ E, ∀ z ∈ UnitDisc, G w z = F w z

/-- **Extension problem for holomorphic motions.** Let $\mathbb{D}$ be the open unit disc. The
proposition asserts the following. Let $E$ be a set of complex numbers and $F$ a function
assigning a complex number $F(w, z)$ to each pair of complex numbers $w, z$, such that (a) for
every $z \in \mathbb{D}$ the map $w \mapsto F(w, z)$ is injective on $E$, (b) for every
$w \in E$ the map $z \mapsto F(w, z)$ is analytic on $\mathbb{D}$, and (c) $F(w, 0) = w$ for
every $w \in E$. Then there is a function $G$ of the same kind that satisfies (a), (b) and (c)
with $E$ replaced by $\mathbb{C}$ and has $G(w, z) = F(w, z)$ for all $w \in E$ and all
$z \in \mathbb{D}$.

Conditions (a), (b) and (c) say that $F$ is a holomorphic motion of $E$ over $\mathbb{D}$; the
question, due to Sullivan, Thurston and Royden, is whether every such motion extends to a
holomorphic motion of the whole plane.

Source: AMR-022-7082, Problem 7.82. -/
def conjecture : Prop :=
  ∀ (E : Set ℂ) (F : ℂ → ℂ → ℂ),
    IsInjectiveInParam E F →
      IsAnalyticInDisc E F →
        IsNormalizedAtZero E F →
          ∃ G : ℂ → ℂ → ℂ,
            IsInjectiveInParam Set.univ G ∧
              IsAnalyticInDisc Set.univ G ∧
                IsNormalizedAtZero Set.univ G ∧ AgreesOnDisc E F G

/--
**Holomorphic motions of planar sets extend to the plane.** Let $\mathbb{D}$ be the open unit
disc, $E$ a set of complex numbers and $F$ a function assigning a complex number $F(w, z)$ to
each pair of complex numbers $w, z$, such that (a) for every $z \in \mathbb{D}$ the map
$w \mapsto F(w, z)$ is injective on $E$, (b) for every $w \in E$ the map $z \mapsto F(w, z)$ is
analytic on $\mathbb{D}$, and (c) $F(w, 0) = w$ for every $w \in E$. Then there is a function
$G$ of the same kind that satisfies (a), (b) and (c) with $E$ replaced by $\mathbb{C}$ and has
$G(w, z) = F(w, z)$ for all $w \in E$ and all $z \in \mathbb{D}$.

This answers the extension problem for holomorphic motions affirmatively. It follows from
Słodkowski’s extended λ-lemma: every holomorphic motion over the unit disk extends to a
holomorphic motion of the Riemann sphere.

Source: Zbigniew
Słodkowski, Holomorphic motions and polynomial hulls, Proceedings of the American Mathematical
Society 111 (1991), 347–355, https://doi.org/10.2307/2048323. Moved from
`OpenConjectures/Analysis/AMR22Problem7082`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.AMR22Problem7082Wanted
