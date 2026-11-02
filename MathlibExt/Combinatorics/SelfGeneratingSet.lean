/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Lattice

@[expose]
public section


namespace MetaMathlibExt
namespace SelfGeneratingSet

/-!
# Self-generating sets

This file formalizes the characterization of self-generating sets from Peter Hinz,
*On generalized Lichtenberg figures*, Journal of Integer Sequences 25 (2022), Article 22.6.5,
lines 163–180 of the source:

<https://cs.uwaterloo.ca/journals/JIS/VOL25/Hinz/hinz5.tex>

The archived source has SHA-256
`4c3205a109846590bbaf42330e44139bc52250e1712be01e11c7580312e7b134`.

Concept `jis_term_23e11a02338d8f3d91eda68b`; source statement
`jis_b9342f43164eb6b4d229b602`.
-/

/-- **Strict growth of a set of generators.** A finite set $F$ of functions
$\mathbb{N} \to \mathbb{N}$ has strict growth when $x < f(x)$ for every $f \in F$ and every
$x \in \mathbb{N}$. -/
def StrictGrowth (F : Finset (Nat → Nat)) : Prop :=
  ∀ f ∈ F, ∀ x, x < f x

/-- **Self-generating sets.** Let $F$ be a finite set of functions $\mathbb{N} \to \mathbb{N}$
and let $s \in \mathbb{N}$. A set $\Gamma \subseteq \mathbb{N}$ is self-generating for $s$ and $F$
when $s \in \Gamma$ and $f(x) \in \Gamma$ for every $f \in F$ and every $x \in \Gamma$.

The source writes this condition as $\mathrm{SG}(s, F)$. -/
def SG (F : Finset (Nat → Nat)) (seed : Nat) (Gamma : Set Nat) : Prop :=
  seed ∈ Gamma ∧ ∀ f ∈ F, ∀ x ∈ Gamma, f x ∈ Gamma

/-- **Fixed-point sets for a seed and generators.** Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ and let $s \in \mathbb{N}$. A set $C \subseteq \mathbb{N}$ is a
fixed-point set for $F$ and $s$ when, for every $y \in \mathbb{N}$, $y \in C$ if and only if
$y = s$ or $y = f(x)$ for some $f \in F$ and some $x \in C$; equivalently,
$C = \{s\} \cup \bigcup_{f \in F} f(C)$. -/
def FixedPoint (F : Finset (Nat → Nat)) (seed : Nat) (C : Set Nat) : Prop :=
  ∀ y, y ∈ C ↔ y = seed ∨ ∃ f ∈ F, ∃ x ∈ C, f x = y

/-- **Reachability from a seed by generators.** Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ and let $s \in \mathbb{N}$. Reachability from $s$ is the least
predicate on $\mathbb{N}$ that holds at $s$ and holds at $f(w)$ whenever it holds at $w$ and
$f \in F$. Thus $y$ is reachable exactly when $y = f_k(\cdots f_1(s) \cdots)$ for some $k \ge 0$
and $f_1, \ldots, f_k \in F$; the case $k = 0$ is $s$ itself. -/
inductive Gen (F : Finset (Nat → Nat)) (seed : Nat) : Nat → Prop where
  | seed_mem : Gen F seed seed
  | step (w : Nat) : Gen F seed w → ∀ f ∈ F, Gen F seed (f w)

/-- **Set generated from a seed.** For a finite set $F$ of functions $\mathbb{N} \to \mathbb{N}$
and a seed $s \in \mathbb{N}$, the set generated from $s$ by $F$ consists of all numbers
$f_k(\cdots f_1(s) \cdots)$ with $k \ge 0$ and $f_1, \dots, f_k \in F$; the case $k = 0$ gives
$s$ itself. -/
def GeneratedSet (F : Finset (Nat → Nat)) (seed : Nat) : Set Nat :=
  {y | Gen F seed y}

/-- **Fixed-point sets are self-generating.** Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ and $s \in \mathbb{N}$. Every fixed-point set $C$ for $F$ and $s$ is
self-generating: $s \in C$, and $f(x) \in C$ for every $f \in F$ and every $x \in C$. -/
theorem fixedPoint_isSG {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hC : FixedPoint F seed C) : SG F seed C := by
  constructor
  · exact (hC seed).mpr (Or.inl rfl)
  · intro f hf x hx
    exact (hC (f x)).mpr (Or.inr ⟨f, hf, x, hx, rfl⟩)

/-- **The generated set is self-generating.** Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ and $s \in \mathbb{N}$. The set generated from $s$ by $F$ contains $s$
and is closed under every $f \in F$: if $x$ is in it and $f \in F$, then $f(x)$ is in it. -/
theorem generated_isSG {F : Finset (Nat → Nat)} {seed : Nat} :
    SG F seed (GeneratedSet F seed) := by
  constructor
  · exact Gen.seed_mem
  · intro f hf x hx
    exact Gen.step x hx f hf

/-- **The generated set lies in every self-generating set.** Let $F$ be a finite set of
functions $\mathbb{N} \to \mathbb{N}$ and let $s \in \mathbb{N}$. If a set $G \subseteq \mathbb{N}$
contains $s$ and satisfies $f(x) \in G$ for every $f \in F$ and every $x \in G$, then $G$ contains
the set generated from $s$ by $F$, that is, every number obtained from $s$ by applying finitely
many (possibly no) functions of $F$ in succession. -/
theorem generated_le_of_sg {F : Finset (Nat → Nat)} {seed : Nat} {G : Set Nat}
    (hG : SG F seed G) : GeneratedSet F seed ⊆ G := by
  intro y hy
  have hgen : Gen F seed y := hy
  clear hy
  induction hgen with
  | seed_mem => exact hG.1
  | step w _ f hf ih => exact hG.2 f hf w ih

/-- **The generated set is a fixed-point set.** Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ and $s \in \mathbb{N}$, and let $\Gamma$ be the set generated from $s$
by $F$. Then for every $y \in \mathbb{N}$, $y \in \Gamma$ if and only if $y = s$ or $y = f(x)$
for some $f \in F$ and $x \in \Gamma$.

This direction does not require the generators to be strictly increasing. -/
theorem generated_fixedPoint {F : Finset (Nat → Nat)} {seed : Nat} :
    FixedPoint F seed (GeneratedSet F seed) := by
  intro y
  constructor
  · intro hy
    have hgen : Gen F seed y := hy
    cases hgen with
    | seed_mem => exact Or.inl rfl
    | step w hw f hf => exact Or.inr ⟨f, hf, w, hw, rfl⟩
  · intro hy
    cases hy with
    | inl heq =>
      subst heq
      exact Gen.seed_mem
    | inr h =>
      obtain ⟨f, hf, x, hx, heq⟩ := h
      have hxg : Gen F seed x := hx
      subst heq
      exact Gen.step x hxg f hf

/-- **Under strict growth, a fixed-point set is the generated set.** Let $F$ be a finite set of
functions $\mathbb{N} \to \mathbb{N}$ with $x < f(x)$ for every $f \in F$ and every
$x \in \mathbb{N}$, let $s \in \mathbb{N}$, and let $C \subseteq \mathbb{N}$ be a fixed-point set
for $F$ and $s$: $y \in C$ exactly when $y = s$ or $y = f(x)$ for some $f \in F$ and $x \in C$.
Then $C$ equals the set generated from $s$ by $F$, the numbers obtained from $s$ by applying
finitely many functions of $F$.

The proof is by strong induction: if an element of $C$ is $f(x)$ with $f \in F$ and $x \in C$,
then strict growth gives $x < f(x)$. -/
theorem fixedPoint_eq_generated {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hg : StrictGrowth F) (hC : FixedPoint F seed C) :
    C = GeneratedSet F seed := by
  have hSG : SG F seed C := fixedPoint_isSG hC
  have key : ∀ n, n ∈ C → Gen F seed n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hn
      have hor : n = seed ∨ ∃ f ∈ F, ∃ x ∈ C, f x = n := (hC n).mp hn
      cases hor with
      | inl heq =>
        subst heq
        exact Gen.seed_mem
      | inr h =>
        obtain ⟨f, hf, x, hx, heq⟩ := h
        have hlt : x < f x := hg f hf x
        have hlt' : x < n := heq ▸ hlt
        have ihx : Gen F seed x := ihn x hlt' hx
        rw [← heq]
        exact Gen.step x ihx f hf
  apply Set.ext
  intro y
  constructor
  · intro hy
    exact key y hy
  · intro hy
    exact generated_le_of_sg hSG hy

/-- **The generated set is the intersection of all self-generating sets.** Let $F$ be a finite
set of functions $\mathbb{N} \to \mathbb{N}$ and $s \in \mathbb{N}$. The set generated from $s$ by
$F$ equals the intersection of all sets $G \subseteq \mathbb{N}$ that contain $s$ and are closed
under every $f \in F$. -/
theorem generated_eq_sInter {F : Finset (Nat → Nat)} {seed : Nat} :
    GeneratedSet F seed = Set.sInter {G | SG F seed G} := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    change ∀ G ∈ {G | SG F seed G}, y ∈ G
    intro G hG
    have hGs : SG F seed G := hG
    exact generated_le_of_sg hGs hy
  · intro hy
    have hgenSG : SG F seed (GeneratedSet F seed) := generated_isSG
    have hmem : GeneratedSet F seed ∈ {G | SG F seed G} := hgenSG
    have hy' : ∀ G ∈ {G | SG F seed G}, y ∈ G := hy
    exact hy' _ hmem

/-- **Under strict growth, a fixed-point set is the intersection of all self-generating sets.**
Let $F$ be a finite set of functions $\mathbb{N} \to \mathbb{N}$ with $x < f(x)$ for every
$f \in F$ and every $x \in \mathbb{N}$, and let $s \in \mathbb{N}$. If $C$ is a fixed-point set for
$F$ and $s$, then $C$ is the intersection of all sets $G \subseteq \mathbb{N}$ that contain $s$
and are closed under every $f \in F$. -/
theorem fixedPoint_eq_sInter {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hg : StrictGrowth F) (hC : FixedPoint F seed C) :
    C = Set.sInter {G | SG F seed G} := by
  rw [fixedPoint_eq_generated hg hC, generated_eq_sInter]

/-- **Under strict growth, a fixed-point set is the least self-generating set.** Let $F$ be a
finite set of functions $\mathbb{N} \to \mathbb{N}$ with $x < f(x)$ for every $f \in F$ and every
$x \in \mathbb{N}$, and let $s \in \mathbb{N}$. If $C$ is a fixed-point set for $F$ and $s$, then
$C$ contains $s$ and is closed under every $f \in F$, and $C \subseteq G$ for every set
$G \subseteq \mathbb{N}$ that contains $s$ and is closed under every $f \in F$. -/
theorem fixedPoint_isLeast {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hg : StrictGrowth F) (hC : FixedPoint F seed C) :
    SG F seed C ∧ ∀ G, SG F seed G → C ⊆ G := by
  constructor
  · exact fixedPoint_isSG hC
  · intro G hG
    rw [fixedPoint_eq_generated hg hC]
    exact generated_le_of_sg hG

/-- **The least self-generating set is the generated set.** Let $F$ be a finite set of
functions $\mathbb{N} \to \mathbb{N}$ and let $s \in \mathbb{N}$. Call a set
$G \subseteq \mathbb{N}$ self-generating if $s \in G$ and $f(x) \in G$ for every $f \in F$ and
every $x \in G$. If $C$ is self-generating and is contained in every self-generating set, then
$C$ equals the set generated from $s$ by $F$. -/
theorem isLeast_eq_generated {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hC : SG F seed C) (hle : ∀ G, SG F seed G → C ⊆ G) :
    C = GeneratedSet F seed := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    exact hle _ generated_isSG hy
  · intro hy
    exact generated_le_of_sg hC hy

/-- **Under strict growth, fixed-point sets are unique.** Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ with $x < f(x)$ for every $f \in F$ and every $x \in \mathbb{N}$, and
let $s \in \mathbb{N}$. If $C_1$ and $C_2$ are both fixed-point sets for $F$ and $s$, then
$C_1 = C_2$. -/
theorem fixedPoint_unique {F : Finset (Nat → Nat)} {seed : Nat} {C1 C2 : Set Nat}
    (hg : StrictGrowth F) (h1 : FixedPoint F seed C1)
    (h2 : FixedPoint F seed C2) : C1 = C2 := by
  rw [fixedPoint_eq_generated hg h1, fixedPoint_eq_generated hg h2]

end SelfGeneratingSet
end MetaMathlibExt
