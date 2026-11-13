/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 2, Combinatorics 20, Combinatorics 23, Combinatorics 24, Combinatorics 429, Combinatorics 441

/-!
# `MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.Homomorphisms`

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.4, page 7. (for
  `SimpleGraph.Subgraph.IsRetract`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.2 Cores, page 104. (for
  `SimpleGraph.HasCore`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8, page 115. (for
  `SimpleGraph.IsLocalInjection`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8 Foldings and Covers, page 115. (for
  `SimpleGraph.IsLocalIsomorphism`, `SimpleGraph.Covers`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 6.8 Foldings and Covers, page 114. (for
  `SimpleGraph.IsFolding`)
-/

open SimpleGraph

namespace MetaMathlibExt

-- Combinatorics 2: Retract

/-- **Retract.** Let $Y$ be a subgraph of a graph $X$. A *retraction* from $X$ to $Y$ is a
homomorphism $f$ from $X$ to $Y$, regarded as a graph in its own right, whose restriction to the
vertex set of $Y$ is the identity map. We say that $Y$ is a *retract* of $X$ if there is a
retraction from $X$ to $Y$.
-/
def _root_.SimpleGraph.Subgraph.IsRetract {V : Type*} {G : SimpleGraph V}
    (H : G.Subgraph) : Prop :=
  ∃ φ : G →g H.coe, ∀ (h : H.verts), φ h.val = h

-- Combinatorics 20: Core/has core

def _root_.SimpleGraph.IsCore {V : Type*} [Fintype V] (X : SimpleGraph V) : Prop :=
  ∀ f : X →g X, Function.Bijective f

/-- **Core of a graph.** A finite graph $X$ is a *core* if every homomorphism from $X$ to itself
is a bijection. For finite graphs $X$ and $Y$, $Y$ is a *core of* $X$ if $Y$ is a core, there is a
homomorphism from $X$ to $Y$, and there is an injective homomorphism from $Y$ to $X$; that is, $Y$
is isomorphic to a subgraph of $X$.
-/
def _root_.SimpleGraph.HasCore {V W : Type*} [Fintype V] [Fintype W]
    (X : SimpleGraph V) (Y : SimpleGraph W) : Prop :=
  Y.IsCore ∧ Nonempty (X →g Y) ∧ ∃ f : Y →g X, Function.Injective f

-- Combinatorics 23: Local injection

/-- **Local injection.** A homomorphism $f$ from a finite graph $X$ to a finite graph $Y$ is a
*local injection* if any two distinct vertices of $X$ with the same image under $f$ are at
distance at least $3$ in $X$.

Vertices in different components of $X$ count as being at infinite distance.
-/
def _root_.SimpleGraph.IsLocalInjection {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) : Prop :=
  ∀ a b : V, f a = f b → a ≠ b → 3 ≤ G.edist a b

-- Combinatorics 24: Local isomorphism

/-- **Local isomorphism.** A homomorphism $f$ from a finite graph $X$ to a finite graph $Y$ is a
*local isomorphism* if for every vertex $x$ of $X$, $f$ maps the set of neighbours of $x$
bijectively onto the set of neighbours of $f(x)$.
-/
def _root_.SimpleGraph.IsLocalIsomorphism {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) : Prop :=
  ∀ x : V, Set.BijOn f (G.neighborSet x) (H.neighborSet (f x))

-- Combinatorics 429: Covers (graph)

/-- **Graph cover.** A finite graph $X$ *covers* a finite graph $Y$ if there is a surjective local
isomorphism from $X$ to $Y$.
-/
def _root_.SimpleGraph.Covers {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : G →g H, G.IsLocalIsomorphism H f ∧ Function.Surjective f

-- Combinatorics 441: Folding

def _root_.SimpleGraph.IsSimpleFolding.{u} {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) : Prop :=
  ∃ a b : V, a ≠ b ∧ G.edist a b = 2 ∧ f a = f b ∧
    ∀ x y : V, f x = f y → x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

/-- A homomorphism from X to Y is a *simple folding* if it has one fibre consisting of two vertices
at distance two, and all other fibres are singletons. A homomorphism is a *folding* if it is the
composition of a non-negative number of simple foldings.
-/
inductive _root_.SimpleGraph.IsFolding.{u} : ∀ {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (_f : G →g H), Prop where
  | id {V : Type u} {G : SimpleGraph V} : IsFolding G G Hom.id
  | simple {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) :
      G.IsSimpleFolding H f → IsFolding G H f
  | comp {V W X : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
      (f : G →g I) (g : I →g H) :
      IsFolding G I f → IsFolding I H g → IsFolding G H (g.comp f)

end MetaMathlibExt

end
