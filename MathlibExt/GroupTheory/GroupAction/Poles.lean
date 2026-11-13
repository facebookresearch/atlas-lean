/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.FixedPoints

@[expose] public section

/-!
# Poles of a group action

A pole of a group action is a point fixed by some nonidentity element of the
group. The group action permutes the set of poles: acting by `g` sends a pole
to a pole, since the stabilizer of `g • p` is the conjugate of the stabilizer
of `p`.

Source: `v1/Atlas/AlgebraNotes/code/SylowTheorems.lean`
(`SylowTheorems.poles`, `SylowTheorems.smul_mem_poles`, fully proved there),
formalizing a lemma used in the book's proof of the Sylow theorems (Proofs and
Applications of the Sylow Theorems, Section on Stabilizer): if `p` is a pole
and `g` is in `G`, then `g • p` is a pole.

## Main results

* `MulAction.poles`: the set of poles of a group action.
* `MulAction.smul_mem_poles`: the action sends poles to poles.
* `MulAction.image_smul_poles`: the action by any `g` permutes the set of poles.
* `MulAction.poles_eq_iUnion_fixedBy`: the poles are the union of the fixed-point
  sets of the nonidentity elements.
-/

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- A pole of a group action is a point fixed by some nonidentity element. -/
def poles (G : Type*) (X : Type*) [Group G] [MulAction G X] : Set X :=
  {x : X | ∃ g : G, g ≠ 1 ∧ g • x = x}

/-- **Characterization of poles.** Let a group $G$ act on a set $X$. A point $p \in X$ is
a pole of the action if and only if there is some $g \in G$ with $g \neq 1$ and
$g \cdot p = p$. -/
theorem mem_poles {p : X} : p ∈ poles G X ↔ ∃ g : G, g ≠ 1 ∧ g • p = p :=
  Iff.rfl

/-- **The action sends poles to poles.** Let a group $G$ act on a set $X$. If $p \in X$ is a
pole of the action, then $g \cdot p$ is a pole for every $g \in G$.

If $p$ is fixed by $h \neq 1$, then $g \cdot p$ is fixed by the conjugate $g h g^{-1} \neq 1$. -/
theorem smul_mem_poles (g : G) {p : X} (hp : p ∈ poles G X) :
    g • p ∈ poles G X := by
  obtain ⟨h, hne, hfix⟩ := hp
  refine ⟨g * h * g⁻¹, ?_, ?_⟩
  · intro heq
    apply hne
    have hconj : h = g⁻¹ * (g * h * g⁻¹) * g := by simp [mul_assoc]
    rw [hconj, heq, mul_one, inv_mul_cancel]
  · calc (g * h * g⁻¹) • (g • p)
        = g • (h • (g⁻¹ • (g • p))) := by rw [mul_smul, mul_smul]
      _ = g • (h • p) := by rw [inv_smul_smul]
      _ = g • p := by rw [hfix]

/-- **The poles are invariant under the action.** Let a group $G$ act on a set $X$ and let
$P \subseteq X$ be the set of poles of the action. For every $g \in G$, the image of $P$
under the map $x \mapsto g \cdot x$ is $P$. -/
theorem image_smul_poles (g : G) : (g • ·) '' poles G X = poles G X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_poles g hy
  · intro hx
    exact ⟨g⁻¹ • x, smul_mem_poles g⁻¹ hx, smul_inv_smul g x⟩

/-- **The poles as a union of fixed-point sets.** Let a group $G$ act on a set $X$. The set
of poles equals $\bigcup_{g \in G,\, g \neq 1} \{x \in X : g \cdot x = x\}$, the union of
the fixed-point sets of the nonidentity elements of $G$. -/
theorem poles_eq_iUnion_fixedBy :
    poles G X = ⋃ g ∈ {g : G | g ≠ 1}, MulAction.fixedBy X g := by
  ext p
  constructor
  · rintro ⟨g, hg, hfix⟩
    exact Set.mem_iUnion₂.mpr ⟨g, hg, MulAction.mem_fixedBy.mpr hfix⟩
  · intro hp
    obtain ⟨g, hg, hfix⟩ := Set.mem_iUnion₂.mp hp
    exact ⟨g, hg, MulAction.mem_fixedBy.mp hfix⟩

end MulAction

end
