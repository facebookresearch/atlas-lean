/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Chromatic symmetric functions via coloring profiles

The chromatic symmetric function of a graph is determined by the counts of
proper colorings with each multiplicity profile: for every finite labeled
palette and every prescribed multiplicity of each color, count the proper
colorings realizing exactly those multiplicities. This module packages those
counts (`chromaticProfileCount`) and the resulting notion of two graphs having
the same chromatic symmetric function (`SameChromaticSymmetricFunction`),
together with its basic equivalence and isomorphism-invariance interface.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- **Chromatic profile count.** Let $G$ be a simple graph on a finite vertex set $V$, let $k$ be
a natural number and let $m : \{0, \dots, k-1\} \to \mathbb{N}$. The chromatic profile count of
$G$ at $k$ and $m$ is the number of proper colorings $c : V \to \{0, \dots, k-1\}$ of $G$ such
that for every color $i$, exactly $m(i)$ vertices $v$ satisfy $c(v) = i$.

These counts are the coefficients of the chromatic symmetric function. -/
noncomputable def chromaticProfileCount [Finite V] (G : SimpleGraph V) (k : ℕ)
    (multiplicity : Fin k → ℕ) : ℕ :=
  Nat.card { c : G.Coloring (Fin k) //
    ∀ color, Nat.card { v : V // c v = color } = multiplicity color }

/-- **Graphs with the same chromatic symmetric function.** Let $G$ and $H$ be simple graphs on
finite vertex sets. We say that $G$ and $H$ have the same chromatic symmetric function when, for
every natural number $k$ and every $m : \{0, \dots, k-1\} \to \mathbb{N}$, the chromatic profile
count of $G$ at $k$ and $m$ equals that of $H$: both graphs have equally many proper colorings
with colors $\{0, \dots, k-1\}$ in which each color $i$ is used on exactly $m(i)$ vertices.

This is equality of chromatic symmetric functions, expressed through their coefficients. -/
def SameChromaticSymmetricFunction [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ k multiplicity,
    chromaticProfileCount G k multiplicity = chromaticProfileCount H k multiplicity

/-- **Reflexivity of having the same chromatic symmetric function.** Every simple graph on a
finite vertex set has the same chromatic symmetric function as itself. -/
theorem SameChromaticSymmetricFunction.refl [Finite V] (G : SimpleGraph V) :
    SameChromaticSymmetricFunction G G :=
  fun _ _ => rfl

/-- **Symmetry of having the same chromatic symmetric function.** Let $G$ and $H$ be simple
graphs on finite vertex sets. If $G$ has the same chromatic symmetric function as $H$, then $H$
has the same chromatic symmetric function as $G$. -/
theorem SameChromaticSymmetricFunction.symm
    [Finite V] [Finite W]
    (h : SameChromaticSymmetricFunction G H) : SameChromaticSymmetricFunction H G :=
  fun k multiplicity => (h k multiplicity).symm

/-- **Transitivity of having the same chromatic symmetric function.** Let $G$, $H$ and $K$ be
simple graphs on finite vertex sets. If $G$ has the same chromatic symmetric function as $H$, and
$H$ has the same chromatic symmetric function as $K$, then $G$ has the same chromatic symmetric
function as $K$. -/
theorem SameChromaticSymmetricFunction.trans [Finite V] [Finite W]
    {U : Type*} [Finite U] {K : SimpleGraph U}
    (hGH : SameChromaticSymmetricFunction G H)
    (hHK : SameChromaticSymmetricFunction H K) : SameChromaticSymmetricFunction G K :=
  fun k multiplicity => (hGH k multiplicity).trans (hHK k multiplicity)

/-- **Isomorphic graphs have the same chromatic symmetric function.** If $G$ and $H$ are
isomorphic simple graphs on finite vertex sets, then $G$ and $H$ have the same chromatic
symmetric function.

The proof transports colorings and their color classes along the isomorphism. -/
theorem SameChromaticSymmetricFunction.of_iso [Finite V] [Finite W] (e : G ≃g H) :
    SameChromaticSymmetricFunction G H := by
  intro k multiplicity
  classical
  let F : G.Coloring (Fin k) → H.Coloring (Fin k) := fun c => c.comap e.symm.toHom
  let B : H.Coloring (Fin k) → G.Coloring (Fin k) := fun d => d.comap e.toHom
  have hBF : ∀ c, B (F c) = c := fun c => by
    ext v
    simp [F, B, Coloring.comap]
  have hFB : ∀ d, F (B d) = d := fun d => by
    ext w
    simp [F, B, Coloring.comap]
  have hfib : ∀ (c : G.Coloring (Fin k)) (color : Fin k),
      Nat.card { w : W // F c w = color } = Nat.card { v : V // c v = color } := by
    intro c color
    apply Nat.card_congr
    refine
      { toFun := fun w => ⟨e.symm w, w.property⟩
        invFun := fun v => ⟨e v, by simpa [F, Coloring.comap] using v.property⟩
        left_inv := fun w => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  apply Nat.card_congr
  refine Equiv.subtypeEquiv ⟨F, B, hBF, hFB⟩ (fun c => ?_)
  simp only [Equiv.coe_fn_mk]
  constructor
  · intro h color
    rw [hfib c color]
    exact h color
  · intro h color
    rw [← hfib c color]
    exact h color

end SimpleGraph

end
