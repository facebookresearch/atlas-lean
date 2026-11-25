/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# N384 (Definition 19.4): Lipschitz parametrizable sets

Clean-room formalization of ATLAS `NumberTheoryI` N384, Definition 19.4:
a set `B` in a metric space `X` is `d`-Lipschitz parametrizable when it is
the union of the images of finitely many Lipschitz continuous maps
`fᵢ : [0, 1]^d → X`.

Here `[0, 1]^d` is the subtype of `Set.Icc (0 : Fin d → ℝ) 1`, and the
finite family is indexed by `Fin n`, with equality (not just covering).

## N386 supporting-source map

Supporting source (prerequisite only, not the full N386 theorem):
`Atlas/NumberTheoryI/code/AnalyticClassNumber.lean` at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, lines 49--62
(`IsLipschitzParametrizable.image_linearEquiv`).
That source shows the image of a parametrizable set under a linear
equivalence is parametrizable by composing charts; the general theorem
`IsLipschitzParametrizable.image_lipschitzWith` below abstracts this to an
arbitrary Lipschitz map, which is all the N386 change of basis needs.
-/

@[expose] public section

/-- **The unit cube.** For a natural number $d$, the closed unit cube $[0, 1]^d$ is the set of
points $x \in \mathbb{R}^d$ with $0 \le x_i \le 1$ for every coordinate $i$. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.Icc 0 1

/-- **Lipschitz parametrizable sets.** Let $X$ be a metric space and $d$ a natural number. A set
$B \subseteq X$ is $d$-Lipschitz parametrizable if there are a natural number $n$ (possibly $0$)
and Lipschitz maps $f_1, \dots, f_n : [0, 1]^d \to X$ out of the closed unit cube
$[0, 1]^d \subseteq \mathbb{R}^d$ such that $B$ equals the union of their images,
$B = f_1([0, 1]^d) \cup \dots \cup f_n([0, 1]^d)$. -/
def IsLipschitzParametrizable {X : Type*} [MetricSpace X] (d : ℕ) (B : Set X) : Prop :=
  ∃ (n : ℕ) (f : Fin n → (↥(unitCube d) → X)),
    (∀ i, ∃ K : NNReal, LipschitzWith K (f i)) ∧ B = ⋃ i, Set.range (f i)

/-- **The origin lies in the unit cube.** For every natural number $d$, the origin of
$\mathbb{R}^d$ lies in the closed unit cube $[0, 1]^d$. -/
theorem unitCube_zero_mem (d : ℕ) : (0 : Fin d → ℝ) ∈ unitCube d :=
  Set.mem_Icc.mpr ⟨le_rfl, fun _ => zero_le_one⟩

/-- **The empty set is Lipschitz parametrizable.** Let $X$ be a metric space. For every natural
number $d$, the empty subset of $X$ is $d$-Lipschitz parametrizable, via the empty family of
maps. -/
theorem isLipschitzParametrizable_empty {X : Type*} [MetricSpace X] (d : ℕ) :
    IsLipschitzParametrizable d (∅ : Set X) := by
  refine ⟨0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  symm
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨i, _, _⟩ := hx
  exact i.elim0

/-- **Singletons are Lipschitz parametrizable.** Let $X$ be a metric space. For every natural
number $d$ and every point $x \in X$, the set $\lbrace x \rbrace$ is $d$-Lipschitz parametrizable,
via a single constant map. -/
theorem isLipschitzParametrizable_singleton {X : Type*} [MetricSpace X] (d : ℕ)
    (x : X) : IsLipschitzParametrizable d ({x} : Set X) := by
  refine ⟨1, fun _ _ => x, fun _ => ⟨0, LipschitzWith.const' _⟩, ?_⟩
  ext y
  simp only [Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro rfl
    exact ⟨0, ⟨0, unitCube_zero_mem d⟩, rfl⟩
  · rintro ⟨_, _, rfl⟩
    rfl

namespace Finset

/-- **Finsets are Lipschitz parametrizable.** Let $X$ be a metric space and $d$ a natural number.
Every finite set $s$ of points of $X$, given as a finset, is $d$-Lipschitz parametrizable. -/
theorem isLipschitzParametrizable_coe {X : Type*} [MetricSpace X] (d : ℕ)
    (s : Finset X) : IsLipschitzParametrizable d (↑s : Set X) := by
  refine ⟨Fintype.card ↥s, fun i _ => ((Fintype.equivFin ↥s).symm i : X),
    fun _ => ⟨0, LipschitzWith.const' _⟩, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · intro hx
    refine ⟨Fintype.equivFin ↥s ⟨x, hx⟩, ⟨0, unitCube_zero_mem d⟩, ?_⟩
    show ((Fintype.equivFin ↥s).symm (Fintype.equivFin ↥s ⟨x, hx⟩) : ↥s).val = x
    rw [Equiv.symm_apply_apply]
  · rintro ⟨i, _, rfl⟩
    exact ((Fintype.equivFin ↥s).symm i).property

end Finset

namespace Set

/-- **Finite sets are Lipschitz parametrizable.** Let $X$ be a metric space. Every finite set
$B \subseteq X$ is $d$-Lipschitz parametrizable for every natural number $d$. -/
theorem Finite.isLipschitzParametrizable {X : Type*} [MetricSpace X] {B : Set X}
    (hB : B.Finite) (d : ℕ) : IsLipschitzParametrizable d B := by
  obtain ⟨s, rfl⟩ := hB.exists_finset_coe
  exact Finset.isLipschitzParametrizable_coe d s

end Set

/-- **Lipschitz images of Lipschitz parametrizable sets.** Let $X$ and $Y$ be metric spaces,
let $d$ be a natural number and let $f : X \to Y$ be a Lipschitz map. If a set $B \subseteq X$ is
$d$-Lipschitz parametrizable, then its image $f(B) \subseteq Y$ is $d$-Lipschitz parametrizable. -/
theorem IsLipschitzParametrizable.image_lipschitzWith {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {d : ℕ} {B : Set X}
    (hB : IsLipschitzParametrizable d B) {f : X → Y} {K : NNReal}
    (hf : LipschitzWith K f) : IsLipschitzParametrizable d (f '' B) := by
  obtain ⟨n, charts, hLip, hEq⟩ := hB
  refine ⟨n, fun i => f ∘ charts i, fun i => ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hLip i
    exact ⟨K * L, hf.comp hL⟩
  · rw [hEq, Set.image_iUnion]
    refine Set.iUnion_congr fun i => ?_
    ext y
    simp only [Set.mem_image, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨charts i a, ⟨a, rfl⟩, rfl⟩
