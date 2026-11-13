/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order

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

/-- Every generator in `F` strictly increases its argument. -/
def StrictGrowth (F : Finset (Nat → Nat)) : Prop :=
  ∀ f ∈ F, ∀ x, x < f x

/-- `Gamma` contains `seed` and is closed under every generator in `F`. This is the source's
`SG(seed, F)` condition. -/
def SG (F : Finset (Nat → Nat)) (seed : Nat) (Gamma : Set Nat) : Prop :=
  seed ∈ Gamma ∧ ∀ f ∈ F, ∀ x ∈ Gamma, f x ∈ Gamma

/-- The fixed-point characterization of the self-generating set: each element is either the seed
or the image under a generator of an element already in the set. -/
def FixedPoint (F : Finset (Nat → Nat)) (seed : Nat) (C : Set Nat) : Prop :=
  ∀ y, y ∈ C ↔ y = seed ∨ ∃ f ∈ F, ∃ x ∈ C, f x = y

/-- Reachability from `seed` by a finite composition of generators in `F`. The constructor
`seed_mem` represents the empty composition. -/
inductive Gen (F : Finset (Nat → Nat)) (seed : Nat) : Nat → Prop where
  | seed_mem : Gen F seed seed
  | step (w : Nat) : Gen F seed w → ∀ f ∈ F, Gen F seed (f w)

/-- The closure of `seed` under finite compositions of generators in `F`. -/
def GeneratedSet (F : Finset (Nat → Nat)) (seed : Nat) : Set Nat :=
  {y | Gen F seed y}

/-- A fixed point satisfies the self-generating condition. -/
theorem fixedPoint_isSG {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hC : FixedPoint F seed C) : SG F seed C := by
  constructor
  · exact (hC seed).mpr (Or.inl rfl)
  · intro f hf x hx
    exact (hC (f x)).mpr (Or.inr ⟨f, hf, x, hx, rfl⟩)

/-- The generated closure satisfies the self-generating condition. -/
theorem generated_isSG {F : Finset (Nat → Nat)} {seed : Nat} :
    SG F seed (GeneratedSet F seed) := by
  constructor
  · exact Gen.seed_mem
  · intro f hf x hx
    exact Gen.step x hx f hf

/-- The generated closure is contained in every self-generating set. -/
theorem generated_le_of_sg {F : Finset (Nat → Nat)} {seed : Nat} {G : Set Nat}
    (hG : SG F seed G) : GeneratedSet F seed ⊆ G := by
  intro y hy
  have hgen : Gen F seed y := hy
  clear hy
  induction hgen with
  | seed_mem => exact hG.1
  | step w _ f hf ih => exact hG.2 f hf w ih

/-- The generated closure is a fixed point. This direction does not require strict growth. -/
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

/-- Under strict growth, a fixed point is the generated closure. The proof uses strong induction:
if a non-seed element is `f x`, then strict growth gives `x < f x`. -/
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

/-- The generated closure is the intersection of all self-generating sets. -/
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

/-- Under strict growth, a fixed point is the intersection of all self-generating sets. -/
theorem fixedPoint_eq_sInter {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hg : StrictGrowth F) (hC : FixedPoint F seed C) :
    C = Set.sInter {G | SG F seed G} := by
  rw [fixedPoint_eq_generated hg hC, generated_eq_sInter]

/-- Under strict growth, a fixed point is the least self-generating set. -/
theorem fixedPoint_isLeast {F : Finset (Nat → Nat)} {seed : Nat} {C : Set Nat}
    (hg : StrictGrowth F) (hC : FixedPoint F seed C) :
    SG F seed C ∧ ∀ G, SG F seed G → C ⊆ G := by
  constructor
  · exact fixedPoint_isSG hC
  · intro G hG
    rw [fixedPoint_eq_generated hg hC]
    exact generated_le_of_sg hG

/-- Every least self-generating set is the generated closure. -/
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

/-- Under strict growth, the fixed-point self-generating set is unique. -/
theorem fixedPoint_unique {F : Finset (Nat → Nat)} {seed : Nat} {C1 C2 : Set Nat}
    (hg : StrictGrowth F) (h1 : FixedPoint F seed C1)
    (h2 : FixedPoint F seed C2) : C1 = C2 := by
  rw [fixedPoint_eq_generated hg h1, fixedPoint_eq_generated hg h2]

end SelfGeneratingSet
end MetaMathlibExt
