/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/LaxApproximation.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `lax_approximation` (manifest
`manifests/problems/lax_approximation.toml`, revision 1, submitted by Kim Morrison).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The adapted portions are the definitions `Torus`, `VolumePreservingEquiv`, `deltaDist`,
`ToralDynamicalSystem`, `ToralDynamicalSystem.toVolumePreservingEquiv`, `cube`, `cubeShift` and
`IsCyclicCubeExchange`, the instance `Fact (0 < 1)` and the statement of `lax_approximation`.
In the former wanted module, ATLAS converted the `@[eval_problem]` theorem into a Batteries
`theorem_wanted`, replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, placed the
declarations in the namespace below and gave them docstrings; the mathematical statements are
unchanged. The source was distributed without a `NOTICE` file. The declarations are moved here
with their full names and statements preserved, the instance is named explicitly to keep the
name Lean generated for it there, and the proof is new.
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Lax's approximation theorem for toral homeomorphisms

`lax_approximation` (Peter Lax 1971): every volume-preserving homeomorphism of
the `d`-torus (`d ≥ 1`) can be approximated arbitrarily well, in the
`L∞`-metric `δ`, by cyclic cube exchange transformations.

"Cyclic" means a single full `nᵈ`-cycle (`σ.IsCycle ∧ σ.support = univ`). The assumption
`0 < d` excludes the zero-dimensional grid, on which every permutation is the identity.

## Proof

The homeomorphism `T` is uniformly continuous, and we fix a grid of cubes of side `1/N` with `N`
large. Since `T` preserves volume, any `k` cubes meet at least `k` cubes after applying `T`, so
Hall's marriage theorem gives a permutation `σ` of the cubes such that `T` maps a point of each
cube `K` into the cube `σ K`. To make the permutation a single cycle, each cube is cut into
`m ^ d` subcubes, where `σ ^ m = 1`, numbered in base `m`. The subcube with number `y` in `K` is
sent to the subcube with number `y + 1` in `σ K`, and the last subcube of `K` to the first subcube
of the cube that follows `σ K` for the base-`N` odometer, a single cycle through all cubes. An
orbit that starts at a first subcube comes back to a first subcube after `m ^ d` steps, in the cube
that follows the starting one for the odometer, so the permutation of the subcubes is a single
cycle. The cube exchange it defines translates each subcube onto its image, so it is a
measure-preserving measurable equivalence, and it moves every point to within `ε` of its image
under `T`.
-/

@[expose] public section

namespace MathlibExt.Dynamics.LaxApproximationWanted
namespace Dynamics.LaxApproximation

open MeasureTheory
open scoped ENNReal

-- Named explicitly: this is the name Lean generated for it in the former wanted module.
set_option linter.dupNamespace false in
instance instFactLtRealOfNat_wantedExt : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

set_option linter.dupNamespace false in
/-- **Torus.** For a natural number $d$, the $d$-dimensional torus is
$\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$, the product of $d$ copies of the circle
$\mathbb{R}/\mathbb{Z}$. -/
abbrev Torus (d : ℕ) : Type := Fin d → AddCircle (1 : ℝ)

set_option linter.dupNamespace false in
/-- **Volume-preserving transformations of the torus.** Let $d$ be a natural number. A
volume-preserving transformation of the torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ is a
bijection $T$ of $\mathbb{T}^d$ such that $T$ and $T^{-1}$ are measurable and $T$ preserves
the volume measure. -/
structure VolumePreservingEquiv (d : ℕ) where
  toMeasurableEquiv : Torus d ≃ᵐ Torus d
  measurePreserving :
    MeasurePreserving toMeasurableEquiv (volume : Measure (Torus d)) volume

set_option linter.dupNamespace false in
/-- **Essential-supremum distance between volume-preserving maps.** Let $d$ be a natural
number and let $T$ and $S$ be measurable, invertible, volume-preserving transformations of the
torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$. Let $\rho$ be the distance on $\mathbb{T}^d$
given by the maximum over the coordinates of the distance on the circle $\mathbb{R}/\mathbb{Z}$
(taken to be $0$ when $d = 0$). The distance $\delta(T, S) \in [0, \infty]$ is the essential
supremum, with respect to the volume measure, of the function $x \mapsto \rho(T x, S x)$.

This is Knill's metric $\delta$. -/
noncomputable def deltaDist {d : ℕ} (T S : VolumePreservingEquiv d) : ℝ≥0∞ :=
  essSup (fun x => edist (T.toMeasurableEquiv x) (S.toMeasurableEquiv x))
    (volume : Measure (Torus d))

set_option linter.dupNamespace false in
/-- **Toral dynamical system.** Let $d$ be a natural number. A toral dynamical system on the
torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ is a homeomorphism of $\mathbb{T}^d$ that
preserves the volume measure. -/
structure ToralDynamicalSystem (d : ℕ) where
  toHomeomorph : Torus d ≃ₜ Torus d
  measurePreserving :
    MeasurePreserving toHomeomorph (volume : Measure (Torus d)) volume

set_option linter.dupNamespace false in
/-- **Toral dynamical systems as volume-preserving transformations.** Let $d$ be a natural
number. A volume-preserving homeomorphism $T$ of the torus
$\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ is regarded as a measurable, invertible,
volume-preserving transformation of $\mathbb{T}^d$: the same map, with its inverse, viewed as
a measurable equivalence. -/
noncomputable def ToralDynamicalSystem.toVolumePreservingEquiv {d : ℕ}
    (T : ToralDynamicalSystem d) : VolumePreservingEquiv d where
  toMeasurableEquiv := T.toHomeomorph.toMeasurableEquiv
  measurePreserving := T.measurePreserving

set_option linter.dupNamespace false in
/-- **Grid cube in the torus.** Let $n$ and $d$ be natural numbers and let
$k = (k_0, \dots, k_{d-1})$ with each $k_i \in \{0, \dots, n-1\}$. The grid cube with
index $k$ is the set of points $x$ of the torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$
such that, for every $i < d$, the coordinate $x_i$ is the class modulo $1$ of some real
number $r$ with $k_i/n \le r < (k_i + 1)/n$. -/
def cube (n : ℕ) {d : ℕ} (k : Fin d → Fin n) : Set (Torus d) :=
  { x | ∀ i, ∃ r : ℝ, (k i : ℝ) / n ≤ r ∧ r < ((k i : ℝ) + 1) / n ∧
        x i = ((r : ℝ) : AddCircle (1 : ℝ)) }

set_option linter.dupNamespace false in
/-- **Coordinate shift between grid cubes.** Let $n$ and $d$ be natural numbers, let
$\sigma$ be a permutation of the index set $\{0, \dots, n-1\}^d$, let $k$ be an index and
let $i < d$. The shift along axis $i$ determined by $\sigma$ and $k$ is the point
$(\sigma(k)_i - k_i)/n$ of the circle $\mathbb{R}/\mathbb{Z}$, that is, the class modulo $1$
of this real number.

For an index $j$, the grid cube with index $j$ is the set of points of the torus
$(\mathbb{R}/\mathbb{Z})^d$ whose $m$-th coordinate is the class of a real number in
$[j_m/n, (j_m + 1)/n)$ for every $m < d$. For $n > 0$, translating the $m$-th coordinate of
each point of the grid cube with index $k$ by the shift along axis $m$, for every $m < d$,
carries that cube onto the grid cube with index $\sigma(k)$. -/
noncomputable def cubeShift (n : ℕ) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n))
    (k : Fin d → Fin n) (i : Fin d) : AddCircle (1 : ℝ) :=
  ((((((σ k) i : ℤ) - (k i : ℤ) : ℝ) / (n : ℝ)) : ℝ) : AddCircle (1 : ℝ))

set_option linter.dupNamespace false in
/-- **Cyclic cube exchange.** Let $n$ and $d$ be natural numbers. For an index
$k \in \{0, \dots, n-1\}^d$, the grid cube with index $k$ is the set of points of the torus
$\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ whose $i$-th coordinate is the class of a real
number in $[k_i/n, (k_i + 1)/n)$ for every $i < d$. A measurable, invertible,
volume-preserving transformation $T$ of $\mathbb{T}^d$ is a cyclic cube exchange with $n$
subdivisions if $n > 0$ and there is a permutation $\sigma$ of $\{0, \dots, n-1\}^d$ that is
a single cycle moving every index, such that for every index $k$, every point $x$ of the
grid cube with index $k$ and every $i < d$, we have
$(T x)_i = x_i + (\sigma(k)_i - k_i)/n$ in $\mathbb{R}/\mathbb{Z}$. Thus $T$ translates each
grid cube $k$ rigidly onto the grid cube $\sigma(k)$. -/
def IsCyclicCubeExchange {d : ℕ} (T : VolumePreservingEquiv d) (n : ℕ) : Prop :=
  0 < n ∧ ∃ σ : Equiv.Perm (Fin d → Fin n),
    σ.IsCycle ∧ σ.support = Finset.univ ∧
    ∀ k : Fin d → Fin n, ∀ x ∈ cube n k, ∀ i,
      T.toMeasurableEquiv x i = x i + cubeShift n σ k i

/-! ### The interval index on the circle -/

/-- The representative in `[0, 1)` of a point of the circle. -/
private noncomputable def rep (x : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco 1 0 x : ℝ)

private theorem rep_mem (x : AddCircle (1 : ℝ)) : rep x ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [rep] using (AddCircle.equivIco 1 0 x).2

private theorem coe_rep (x : AddCircle (1 : ℝ)) : ((rep x : ℝ) : AddCircle (1 : ℝ)) = x :=
  AddCircle.coe_equivIco

private theorem rep_coe {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    rep (r : AddCircle (1 : ℝ)) = r :=
  AddCircle.equivIco_coe_of_mem (by simpa using hr)

/-- The index `j` of the interval `[j/n, (j+1)/n)` containing a point of the circle. -/
private noncomputable def idx (n : ℕ) [NeZero n] (x : AddCircle (1 : ℝ)) : Fin n :=
  Fin.ofNat n ⌊(n : ℝ) * rep x⌋₊

private theorem idx_val (n : ℕ) [NeZero n] (x : AddCircle (1 : ℝ)) :
    (idx n x : ℕ) = ⌊(n : ℝ) * rep x⌋₊ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨h0, h1⟩ := rep_mem x
  have hlt : ⌊(n : ℝ) * rep x⌋₊ < n := by
    rw [Nat.floor_lt (by positivity)]
    nlinarith
  rw [idx, Fin.val_ofNat, Nat.mod_eq_of_lt hlt]

private theorem idx_bounds (n : ℕ) [NeZero n] (x : AddCircle (1 : ℝ)) :
    ((idx n x : ℕ) : ℝ) ≤ n * rep x ∧ (n : ℝ) * rep x < (idx n x : ℕ) + 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [idx_val]
  exact ⟨Nat.floor_le (by have := (rep_mem x).1; positivity), Nat.lt_floor_add_one _⟩

private theorem idx_eq_iff (n : ℕ) [NeZero n] (x : AddCircle (1 : ℝ)) (j : Fin n) :
    idx n x = j ↔ (j : ℝ) / n ≤ rep x ∧ rep x < ((j : ℝ) + 1) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [Fin.ext_iff, idx_val, Nat.floor_eq_iff (by have := (rep_mem x).1; positivity),
    div_le_iff₀ hn, lt_div_iff₀ hn]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

private theorem mem_interval_iff (n : ℕ) [NeZero n] (x : AddCircle (1 : ℝ)) (j : Fin n) :
    (∃ r : ℝ, (j : ℝ) / n ≤ r ∧ r < ((j : ℝ) + 1) / n ∧ x = ((r : ℝ) : AddCircle (1 : ℝ))) ↔
      idx n x = j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [idx_eq_iff]
  constructor
  · rintro ⟨r, h1, h2, rfl⟩
    have hj : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    have hr : r ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨le_trans (by positivity) h1, h2.trans_le (by rw [div_le_one hn]; exact hj)⟩
    rw [rep_coe hr]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨rep x, h1, h2, (coe_rep x).symm⟩

private theorem mem_cube_iff (n : ℕ) [NeZero n] {d : ℕ} (k : Fin d → Fin n) (x : Torus d) :
    x ∈ cube n k ↔ ∀ i, idx n (x i) = k i :=
  forall_congr' fun i => mem_interval_iff n (x i) (k i)

/-- Translating by `(j' - j)/n` moves the interval with index `j` onto the one with index `j'`. -/
private theorem idx_add_shift (n : ℕ) [NeZero n] (x : AddCircle (1 : ℝ)) (j j' : Fin n)
    (h : idx n x = j) :
    idx n (x + ((((j' : ℤ) - (j : ℤ) : ℝ) / (n : ℝ) : ℝ) : AddCircle (1 : ℝ))) = j' := by
  rw [← mem_interval_iff] at h ⊢
  obtain ⟨r, h1, h2, rfl⟩ := h
  refine ⟨r + (((j' : ℤ) - (j : ℤ) : ℝ) / (n : ℝ) : ℝ), ?_, ?_, by rw [AddCircle.coe_add]⟩ <;>
    · simp only [Int.cast_natCast, sub_div, add_div] at h1 h2 ⊢
      linarith

private theorem idx_add_shift_iff (n : ℕ) [NeZero n] (x : AddCircle (1 : ℝ)) (j j' : Fin n) :
    idx n (x + ((((j' : ℤ) - (j : ℤ) : ℝ) / (n : ℝ) : ℝ) : AddCircle (1 : ℝ))) = j' ↔
      idx n x = j := by
  refine ⟨fun h => ?_, idx_add_shift n x j j'⟩
  have h' := idx_add_shift n _ j' j h
  have e : (((j' : ℤ) - (j : ℤ) : ℝ) / (n : ℝ) + ((j : ℤ) - (j' : ℤ) : ℝ) / (n : ℝ)) = 0 := by
    ring
  rwa [add_assoc, ← AddCircle.coe_add, e, AddCircle.coe_zero, add_zero] at h'

/-! ### Cube exchanges defined by a permutation of the grid -/

/-- The index of the grid cube containing a point of the torus. -/
private noncomputable def cubeIdx (n : ℕ) [NeZero n] {d : ℕ} (x : Torus d) : Fin d → Fin n :=
  fun i => idx n (x i)

private theorem cubeIdx_eq_iff (n : ℕ) [NeZero n] {d : ℕ} (x : Torus d) (k : Fin d → Fin n) :
    cubeIdx n x = k ↔ x ∈ cube n k := by
  rw [mem_cube_iff, funext_iff]
  rfl

private theorem preimage_cubeIdx (n : ℕ) [NeZero n] {d : ℕ} (k : Fin d → Fin n) :
    cubeIdx n ⁻¹' {k} = cube n k := by
  ext x
  exact cubeIdx_eq_iff n x k

private theorem measurable_idx (n : ℕ) [NeZero n] : Measurable (idx n) := by
  have h1 : Measurable rep :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  exact (measurable_of_countable _).comp (Nat.measurable_floor.comp (h1.const_mul _))

private theorem measurable_cubeIdx (n : ℕ) [NeZero n] {d : ℕ} :
    Measurable (cubeIdx n : Torus d → Fin d → Fin n) :=
  measurable_pi_iff.2 fun i => (measurable_idx n).comp (measurable_pi_apply i)

/-- The translation vector carrying the cube `k` onto the cube `σ k`. -/
private noncomputable def shiftVec (n : ℕ) {d : ℕ} (σ : Equiv.Perm (Fin d → Fin n))
    (k : Fin d → Fin n) : Torus d :=
  fun i => cubeShift n σ k i

private theorem add_shiftVec_mem_iff (n : ℕ) [NeZero n] {d : ℕ} (σ : Equiv.Perm (Fin d → Fin n))
    (k : Fin d → Fin n) (x : Torus d) :
    x + shiftVec n σ k ∈ cube n (σ k) ↔ x ∈ cube n k := by
  rw [mem_cube_iff, mem_cube_iff]
  exact forall_congr' fun i => idx_add_shift_iff n (x i) (k i) (σ k i)

/-- The cube exchange defined by a permutation `σ` of the grid. -/
private noncomputable def exchange (n : ℕ) [NeZero n] {d : ℕ} (σ : Equiv.Perm (Fin d → Fin n))
    (x : Torus d) : Torus d :=
  x + shiftVec n σ (cubeIdx n x)

private theorem cubeIdx_exchange (n : ℕ) [NeZero n] {d : ℕ} (σ : Equiv.Perm (Fin d → Fin n))
    (x : Torus d) : cubeIdx n (exchange n σ x) = σ (cubeIdx n x) := by
  funext i
  exact idx_add_shift n (x i) _ _ rfl

private theorem exchange_inv (n : ℕ) [NeZero n] {d : ℕ} (σ : Equiv.Perm (Fin d → Fin n))
    (x : Torus d) : exchange n σ⁻¹ (exchange n σ x) = x := by
  have h := cubeIdx_exchange n σ x
  funext i
  have e : ∀ a b : ℕ, ((a : ℤ) - (b : ℤ) : ℝ) / (n : ℝ) + ((b : ℤ) - (a : ℤ) : ℝ) / (n : ℝ) = 0 :=
    fun a b => by ring
  change (x + shiftVec n σ (cubeIdx n x)) i + shiftVec n σ⁻¹ (cubeIdx n (exchange n σ x)) i = x i
  rw [h]
  simp only [Pi.add_apply, shiftVec, cubeShift, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  rw [add_assoc, ← AddCircle.coe_add, e, AddCircle.coe_zero, add_zero]

private theorem measurable_exchange (n : ℕ) [NeZero n] {d : ℕ} (σ : Equiv.Perm (Fin d → Fin n)) :
    Measurable (exchange n σ) :=
  measurable_id.add ((measurable_of_countable (shiftVec n σ)).comp (measurable_cubeIdx n))

/-- The cube exchange defined by `σ`, as a measurable equivalence. -/
private noncomputable def exchangeEquiv (n : ℕ) [NeZero n] {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) : Torus d ≃ᵐ Torus d where
  toFun := exchange n σ
  invFun := exchange n σ⁻¹
  left_inv x := exchange_inv n σ x
  right_inv x := by simpa using exchange_inv n σ⁻¹ x
  measurable_toFun := measurable_exchange n σ
  measurable_invFun := measurable_exchange n σ⁻¹

private theorem measure_eq_sum (n : ℕ) [NeZero n] {d : ℕ} (A : Set (Torus d)) :
    volume A = ∑ k : Fin d → Fin n, volume (A ∩ cube n k) := by
  have hmeas : ∀ k : Fin d → Fin n, MeasurableSet (cubeIdx n ⁻¹' {k}) :=
    fun k => measurable_cubeIdx n (measurableSet_singleton k)
  have h := sum_measure_preimage_singleton (μ := volume.restrict A) Finset.univ
    (fun k _ => hmeas k)
  rw [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Measure.restrict_apply (hmeas k), Set.inter_comm, preimage_cubeIdx]

private theorem measurePreserving_exchange (n : ℕ) [NeZero n] {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) :
    MeasurePreserving (exchange n σ) (volume : Measure (Torus d)) volume := by
  refine ⟨measurable_exchange n σ, ?_⟩
  ext E hE
  rw [Measure.map_apply (measurable_exchange n σ) hE, measure_eq_sum n, measure_eq_sum n E,
    ← Equiv.sum_comp σ (fun j => volume (E ∩ cube n j))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hset : exchange n σ ⁻¹' E ∩ cube n k =
      (fun x => x + shiftVec n σ k) ⁻¹' (E ∩ cube n (σ k)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, add_shiftVec_mem_iff]
    refine and_congr_left fun hxk => ?_
    have hk : cubeIdx n x = k := (cubeIdx_eq_iff n x k).2 hxk
    rw [exchange, hk]
  rw [hset, measure_preimage_add_right]

/-! ### Hall's marriage theorem for the cubes -/

private theorem measure_cube_eq (N : ℕ) [NeZero N] {d : ℕ} (K K' : Fin d → Fin N) :
    volume (cube N K) = volume (cube N K') := by
  have h : cube N K = (fun x => x + shiftVec N (Equiv.swap K K') K) ⁻¹' cube N K' := by
    ext x
    have := add_shiftVec_mem_iff N (Equiv.swap K K') K x
    rw [Equiv.swap_apply_left] at this
    exact this.symm
  rw [h, measure_preimage_add_right]

private theorem volume_univ_torus (d : ℕ) : volume (Set.univ : Set (Torus d)) = 1 := by
  rw [volume_pi, Measure.pi_univ]
  simp [AddCircle.measure_univ]

private theorem sum_measure_cube (N : ℕ) [NeZero N] (d : ℕ) :
    ∑ K : Fin d → Fin N, volume (cube N K) = 1 := by
  have h := measure_eq_sum N (Set.univ : Set (Torus d))
  simp only [Set.univ_inter] at h
  rw [← h, volume_univ_torus]

private theorem measure_cube_ne_zero (N : ℕ) [NeZero N] {d : ℕ} (K : Fin d → Fin N) :
    volume (cube N K) ≠ 0 := by
  intro h
  have h1 := sum_measure_cube N d
  rw [Finset.sum_eq_zero (fun K' _ => (measure_cube_eq N K' K).trans h)] at h1
  exact zero_ne_one h1

private theorem measure_cube_ne_top (N : ℕ) [NeZero N] {d : ℕ} (K : Fin d → Fin N) :
    volume (cube N K) ≠ ⊤ := by
  have h : volume (cube N K) ≤ 1 := by
    rw [← sum_measure_cube N d]
    exact Finset.single_le_sum (f := fun K' => volume (cube N K')) (fun _ _ => zero_le)
      (Finset.mem_univ K)
  exact ne_top_of_le_ne_top ENNReal.one_ne_top h

/-- Hall's marriage theorem gives a permutation `σ` of the cubes such that `T` maps a point of
each cube `K` into the cube `σ K`. -/
private theorem exists_perm_hall (N : ℕ) [NeZero N] {d : ℕ} (T : ToralDynamicalSystem d) :
    ∃ σ : Equiv.Perm (Fin d → Fin N), ∀ K, ∃ z ∈ cube N K, T.toHomeomorph z ∈ cube N (σ K) := by
  classical
  let t : (Fin d → Fin N) → Finset (Fin d → Fin N) := fun K =>
    Finset.univ.filter fun J => ∃ z ∈ cube N K, T.toHomeomorph z ∈ cube N J
  have hmeas : ∀ (u : Finset (Fin d → Fin N)), ∀ y ∈ u, MeasurableSet (cubeIdx N ⁻¹' {y}) :=
    fun _ y _ => measurable_cubeIdx N (measurableSet_singleton y)
  have hc : ∀ y : Fin d → Fin N, volume (cubeIdx N ⁻¹' {y}) = volume (cube N 0) := fun y => by
    rw [preimage_cubeIdx]
    exact measure_cube_eq N y 0
  have hall : ∀ s : Finset (Fin d → Fin N), s.card ≤ (s.biUnion t).card := by
    intro s
    have hsub : cubeIdx N ⁻¹' (s : Set (Fin d → Fin N)) ⊆
        T.toHomeomorph ⁻¹' (cubeIdx N ⁻¹' ((s.biUnion t : Finset _) : Set (Fin d → Fin N))) := by
      intro x hx
      simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_biUnion] at hx ⊢
      refine ⟨cubeIdx N x, hx, ?_⟩
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, (cubeIdx_eq_iff N x _).1 rfl, (cubeIdx_eq_iff N _ _).1 rfl⟩
    have h1 := sum_measure_preimage_singleton (μ := volume) s (hmeas s)
    have h2 := sum_measure_preimage_singleton (μ := volume) (s.biUnion t) (hmeas _)
    simp only [hc, Finset.sum_const, nsmul_eq_mul] at h1 h2
    have hle : volume (cubeIdx N ⁻¹' (s : Set (Fin d → Fin N))) ≤
        volume (cubeIdx N ⁻¹' ((s.biUnion t : Finset _) : Set (Fin d → Fin N))) :=
      (measure_mono hsub).trans_eq (T.measurePreserving.measure_preimage
        (measurable_cubeIdx N (Finset.measurableSet _)).nullMeasurableSet)
    rw [← h1, ← h2] at hle
    exact_mod_cast (ENNReal.mul_le_mul_iff_left (measure_cube_ne_zero N 0)
      (measure_cube_ne_top N 0)).1 hle
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  refine ⟨Equiv.ofBijective f hf.bijective_of_finite, fun K => ?_⟩
  have := hft K
  simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

/-! ### The odometer -/

/-- The odometer: the successor map of the base-`N` expansion of grid indices. -/
private def odometer (N d : ℕ) : Equiv.Perm (Fin d → Fin N) :=
  finFunctionFinEquiv.symm.permCongr (finRotate (N ^ d))

private theorem permCongr_iterate {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) (k : ℕ)
    (b : β) : (e.permCongr p)^[k] b = e (p^[k] (e.symm b)) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]

private theorem finRotate_val (M : ℕ) [NeZero M] (j : Fin M) :
    (finRotate M j : ℕ) = (j + 1) % M := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  rw [coe_finRotate]
  split_ifs with h
  · subst h
    simp
  · have : (j : ℕ) + 1 < M' + 1 := by
      have := Fin.val_lt_last h
      omega
    rw [Nat.mod_eq_of_lt this]

private theorem finRotate_iterate_val (M : ℕ) [NeZero M] (k : ℕ) (i : Fin M) :
    ((finRotate M)^[k] i : ℕ) = (i + k) % M := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih => rw [Function.iterate_succ_apply', finRotate_val, ih, Nat.mod_add_mod, add_assoc]

private theorem odometer_iterate (N d k : ℕ) (a : Fin d → Fin N) :
    (odometer N d)^[k] a =
      finFunctionFinEquiv.symm ((finRotate (N ^ d))^[k] (finFunctionFinEquiv a)) := by
  rw [odometer, permCongr_iterate, Equiv.symm_symm]

private theorem odometer_reach (N d : ℕ) [NeZero N] (a a' : Fin d → Fin N) :
    ∃ k, (odometer N d)^[k] a = a' := by
  refine ⟨(finFunctionFinEquiv a' : ℕ) + (N ^ d - finFunctionFinEquiv a), ?_⟩
  rw [odometer_iterate, Equiv.symm_apply_eq]
  ext
  rw [finRotate_iterate_val]
  have h1 := (finFunctionFinEquiv a).isLt
  have h2 := (finFunctionFinEquiv a').isLt
  rw [show (finFunctionFinEquiv a : ℕ) +
      ((finFunctionFinEquiv a' : ℕ) + (N ^ d - finFunctionFinEquiv a)) =
      (finFunctionFinEquiv a' : ℕ) + N ^ d by omega, Nat.add_mod_right, Nat.mod_eq_of_lt h2]

private theorem odometer_iterate_zero_eq_iff (N d : ℕ) [NeZero N] (t : ℕ) :
    (odometer N d)^[t] (finFunctionFinEquiv.symm 0) = finFunctionFinEquiv.symm 0 ↔
      N ^ d ∣ t := by
  rw [odometer_iterate, Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq, Fin.ext_iff,
    finRotate_iterate_val, Fin.val_zero, zero_add, Nat.dvd_iff_mod_eq_zero]

/-- Each coordinate of the odometer's step increases by `0` or `1` modulo `N`. -/
private theorem odometer_apply_val (N d : ℕ) (hN : 1 < N) (a : Fin d → Fin N) (i : Fin d) :
    ((odometer N d a i : ℕ) = a i) ∨ ((odometer N d a i : ℕ) = a i + 1) ∨
      ((odometer N d a i : ℕ) = 0 ∧ (a i : ℕ) + 1 = N) := by
  have : NeZero N := ⟨by omega⟩
  set v : ℕ := (finFunctionFinEquiv a : ℕ) with hv
  have ha : (a i : ℕ) = v / N ^ (i : ℕ) % N := by
    rw [hv, ← finFunctionFinEquiv_symm_apply_val, Equiv.symm_apply_apply]
  have ho : (odometer N d a i : ℕ) = (v + 1) / N ^ (i : ℕ) % N := by
    have h1 : odometer N d a =
        finFunctionFinEquiv.symm (finRotate (N ^ d) (finFunctionFinEquiv a)) := rfl
    have key : ∀ w : ℕ, w % N ^ d / N ^ (i : ℕ) % N = w / N ^ (i : ℕ) % N := by
      intro w
      have hd : N ^ d = N ^ (i : ℕ) * N ^ (d - i) := by
        rw [← pow_add, Nat.add_sub_cancel' i.isLt.le]
      rw [hd, Nat.mod_mul_right_div_self,
        Nat.mod_mod_of_dvd _ (dvd_pow_self N (by omega : d - (i : ℕ) ≠ 0))]
    rw [h1, finFunctionFinEquiv_symm_apply_val, finRotate_val, key]
  rw [ho, Nat.succ_div, ha]
  have hq := Nat.mod_lt (v / N ^ (i : ℕ)) (by omega : 0 < N)
  split_ifs
  · rw [Nat.add_mod_eq_ite, Nat.mod_eq_of_lt hN]
    split_ifs <;> omega
  · left
    rw [add_zero]

/-! ### A twisted lift of a permutation that is a single cycle -/

/-- The lift of `σ` to `X × Y` that moves along `Y` by `τ` and adds a step of `π` each time the
second coordinate reaches `b₀`. -/
private def twist {X Y : Type*} [DecidableEq Y] (σ π : Equiv.Perm X) (τ : Equiv.Perm Y)
    (b₀ : Y) : Equiv.Perm (X × Y) where
  toFun p := (if τ p.2 = b₀ then π (σ p.1) else σ p.1, τ p.2)
  invFun p := (σ⁻¹ (if p.2 = b₀ then π⁻¹ p.1 else p.1), τ⁻¹ p.2)
  left_inv p := by
    rcases p with ⟨a, b⟩
    by_cases h : τ b = b₀
    · subst h
      simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨a, b⟩
    by_cases h : b = b₀
    · subst h
      simp
    · simp [h]

private theorem twist_apply {X Y : Type*} [DecidableEq Y] (σ π : Equiv.Perm X)
    (τ : Equiv.Perm Y) (b₀ : Y) (p : X × Y) :
    twist σ π τ b₀ p = (if τ p.2 = b₀ then π (σ p.1) else σ p.1, τ p.2) :=
  rfl

/-- If `σ ^ M = 1`, the orbit of `b₀` under `τ` has length `M`, every point reaches `b₀`, and
`π` is transitive, then the twisted lift is transitive: its return map to the slice `b₀` is
`π`. -/
private theorem twist_sameCycle {X Y : Type*} [DecidableEq Y] (σ π : Equiv.Perm X)
    (τ : Equiv.Perm Y) (b₀ : Y) (M : ℕ) (hM : 0 < M) (hσ : σ ^ M = 1)
    (hτM : τ^[M] b₀ = b₀) (hτ : ∀ t, 0 < t → t < M → τ^[t] b₀ ≠ b₀)
    (hreach : ∀ b, ∃ k, τ^[k] b = b₀) (hπ : ∀ a a', ∃ k, π^[k] a = a') (p q : X × Y) :
    (twist σ π τ b₀).SameCycle p q := by
  have hsnd : ∀ k (p : X × Y), ((twist σ π τ b₀)^[k] p).2 = τ^[k] p.2 := by
    intro k
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have hpart : ∀ a t, t < M → (twist σ π τ b₀)^[t] (a, b₀) = ((σ ^ t) a, τ^[t] b₀) := by
    intro a t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have hne : τ (τ^[t] b₀) ≠ b₀ := by
        rw [← Function.iterate_succ_apply' τ]
        exact hτ (t + 1) (Nat.succ_pos t) ht
      rw [Function.iterate_succ_apply', ih (by omega), twist_apply]
      simp [hne, pow_succ', Function.iterate_succ_apply']
  have hret : ∀ a, (twist σ π τ b₀)^[M] (a, b₀) = (π a, b₀) := by
    intro a
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have heq : τ (τ^[M'] b₀) = b₀ := by
      rw [← Function.iterate_succ_apply' τ]
      exact hτM
    rw [Function.iterate_succ_apply', hpart a M' (by omega), twist_apply]
    simp only [heq, ↓reduceIte]
    rw [← Equiv.Perm.mul_apply σ, ← pow_succ', hσ, Equiv.Perm.one_apply]
  have hslice : ∀ a k, (twist σ π τ b₀).SameCycle (a, b₀) (π^[k] a, b₀) := by
    intro a k
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      refine ih.trans ?_
      rw [Function.iterate_succ_apply', ← hret, Equiv.Perm.iterate_eq_pow]
      exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)
  have hto : ∀ p : X × Y, ∃ a, (twist σ π τ b₀).SameCycle p (a, b₀) := by
    rintro ⟨a, b⟩
    obtain ⟨k, hk⟩ := hreach b
    refine ⟨((twist σ π τ b₀)^[k] (a, b)).1, ?_⟩
    have h : (twist σ π τ b₀)^[k] (a, b) = (((twist σ π τ b₀)^[k] (a, b)).1, b₀) :=
      Prod.ext rfl (by rw [hsnd]; exact hk)
    rw [← h, Equiv.Perm.iterate_eq_pow]
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)
  obtain ⟨a₁, h₁⟩ := hto p
  obtain ⟨a₂, h₂⟩ := hto q
  obtain ⟨k, hk⟩ := hπ a₁ a₂
  rw [← hk] at h₂
  exact h₁.trans ((hslice a₁ k).trans h₂.symm)

private theorem sameCycle_permCongr {α β : Type*} (e : α ≃ β) (f : Equiv.Perm α) {x y : β}
    (h : f.SameCycle (e.symm x) (e.symm y)) : (e.permCongr f).SameCycle x y := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  have h1 : (e.permCongr f) ^ i = e.permCongr (f ^ i) :=
    (map_zpow (Equiv.permCongrHom e) f i).symm
  rw [h1, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]

private theorem isCycle_of_sameCycle {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (h : ∀ x y, f.SameCycle x y) {x₀ x₁ : α} (hne : x₀ ≠ x₁) :
    f.IsCycle ∧ f.support = Finset.univ := by
  have hmove : ∀ x, f x ≠ x := fun x hx =>
    hne (((h x x₀).eq_of_left hx).symm.trans ((h x x₁).eq_of_left hx))
  refine ⟨⟨x₀, hmove x₀, fun y _ => h x₀ y⟩, ?_⟩
  ext x
  simp [Equiv.Perm.mem_support, hmove x]

/-! ### Coarse and fine grids -/

/-- Splitting an index of the grid with `N * m` subdivisions into a coarse and a fine part. -/
private def splitEquiv (N m d : ℕ) :
    (Fin d → Fin (N * m)) ≃ (Fin d → Fin N) × (Fin d → Fin m) :=
  (Equiv.piCongrRight fun _ => finProdFinEquiv.symm).trans
    (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => Fin N) (fun _ => Fin m))

private theorem splitEquiv_fst (N m d : ℕ) (j : Fin d → Fin (N * m)) (i : Fin d) :
    (splitEquiv N m d j).1 i = (j i).divNat :=
  rfl

private theorem idx_divNat (N m : ℕ) [NeZero N] [NeZero m] (x : AddCircle (1 : ℝ)) :
    (idx (N * m) x).divNat = idx N x := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  ext
  rw [Fin.coe_divNat, idx_val, idx_val, ← Nat.floor_div_natCast]
  congr 1
  push_cast
  field_simp

/-- The fine cube with index `j` lies in the coarse cube with the coarse part of `j`. -/
private theorem cubeIdx_coarse (N m : ℕ) [NeZero N] [NeZero m] {d : ℕ} (x : Torus d) :
    cubeIdx N x = (splitEquiv N m d (cubeIdx (N * m) x)).1 := by
  funext i
  rw [splitEquiv_fst]
  exact (idx_divNat N m (x i)).symm

/-! ### Distances -/

private theorem dist_coe_le (r s : ℝ) (k : ℤ) :
    dist (r : AddCircle (1 : ℝ)) (s : AddCircle (1 : ℝ)) ≤ |r - s - k| := by
  have hk : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 := (AddCircle.coe_eq_zero_iff 1).2 ⟨k, by simp⟩
  have h : (r : AddCircle (1 : ℝ)) - s = ((r - s - k : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub, AddCircle.coe_sub, hk, sub_zero]
  rw [dist_eq_norm, h]
  exact QuotientAddGroup.norm_mk_le_norm.trans_eq (Real.norm_eq_abs _)

/-- Points in the same or in neighbouring intervals of length `1/N` are at distance `< 2/N`. -/
private theorem dist_lt_of_idx (N : ℕ) [NeZero N] (x y : AddCircle (1 : ℝ))
    (h : (idx N y : ℕ) = idx N x ∨ (idx N y : ℕ) = idx N x + 1 ∨
      ((idx N y : ℕ) = 0 ∧ (idx N x : ℕ) + 1 = N)) :
    dist x y < 2 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hx1, hx2⟩ := idx_bounds N x
  obtain ⟨hy1, hy2⟩ := idx_bounds N y
  rw [← coe_rep x, ← coe_rep y]
  have key : ∀ k : ℤ, |(N : ℝ) * rep x - N * rep y - N * k| < 2 →
      dist ((rep x : ℝ) : AddCircle (1 : ℝ)) (rep y : AddCircle (1 : ℝ)) < 2 / N := by
    intro k hk
    refine (dist_coe_le _ _ k).trans_lt ?_
    rw [lt_div_iff₀ hn]
    have : |rep x - rep y - k| * N = |(N : ℝ) * rep x - N * rep y - N * k| := by
      rw [show (N : ℝ) * rep x - N * rep y - N * k = N * (rep x - rep y - k) by ring, abs_mul,
        abs_of_pos hn, mul_comm]
    rw [this]
    exact hk
  rcases h with h | h | ⟨h1, h2⟩
  · have h' : ((idx N y : ℕ) : ℝ) = (idx N x : ℕ) := by exact_mod_cast h
    apply key 0
    rw [Int.cast_zero, mul_zero, sub_zero, abs_lt]
    constructor <;> linarith
  · have h' : ((idx N y : ℕ) : ℝ) = (idx N x : ℕ) + 1 := by exact_mod_cast h
    apply key 0
    rw [Int.cast_zero, mul_zero, sub_zero, abs_lt]
    constructor <;> linarith
  · have h1' : ((idx N y : ℕ) : ℝ) = 0 := by exact_mod_cast h1
    have h2' : ((idx N x : ℕ) : ℝ) + 1 = N := by exact_mod_cast h2
    apply key 1
    rw [Int.cast_one, mul_one, abs_lt]
    constructor <;> linarith

/- **Lax's approximation theorem.** Every toral dynamical system on `𝕋^d`
(`d ≥ 1`) is approximated arbitrarily well in the metric `δ` by cyclic cube
exchange transformations. -/
set_option linter.dupNamespace false in
/-- **Lax's approximation theorem.** Let $d \ge 1$ be a natural number and let $T$ be a toral
dynamical system on the torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$, regarded as a
measurable, invertible, volume-preserving transformation of $\mathbb{T}^d$. Then for every
$\varepsilon \in (0, \infty]$ there are a natural number $n$ and a measurable, invertible,
volume-preserving transformation $S$ of $\mathbb{T}^d$ such that $S$ is a cyclic cube exchange
with $n$ subdivisions and $\delta(T, S) < \varepsilon$, where $\delta$ is the
essential-supremum distance between volume-preserving maps.

Source: P. D. Lax, *Approximation of measure preserving transformations*, Comm. Pure Appl. Math. 24
(1971). Knill, *Some fundamental theorems in mathematics*, §110. Via leanprover/lean-eval@38361be,
problem `lax_approximation`. -/
theorem lax_approximation {d : ℕ} (hd : 0 < d) (T : ToralDynamicalSystem d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (S : VolumePreservingEquiv d),
      IsCyclicCubeExchange S n ∧ deltaDist T.toVolumePreservingEquiv S < ε := by
  -- A real tolerance `e` and the modulus `δ` of uniform continuity of `T` for `e / 2`.
  obtain ⟨e, he0, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e < ε := by
    obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    exact ⟨r, ENNReal.ofReal_pos.1 hr1, hr2⟩
  obtain ⟨δ, hδ, hT⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous T.toHomeomorph.continuous) (e / 2)
    (half_pos he0)
  -- The coarse grid: `N` subdivisions with `2 / N < δ` and `2 / N ≤ e / 2`.
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ + 4 / e + 2)
  have hδ' : 0 < 2 / δ := div_pos two_pos hδ
  have he' : 0 < 4 / e := div_pos (by norm_num) he0
  have hN2 : 1 < N := by
    have : (1 : ℝ) < N := by linarith
    exact_mod_cast this
  have : NeZero N := ⟨by omega⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hNδ : 2 / (N : ℝ) < δ := by
    have h : 2 / δ < N := by linarith
    rw [div_lt_iff₀ hδ] at h
    rw [div_lt_iff₀ hNpos]
    linarith
  have hNe : 2 / (N : ℝ) ≤ e / 2 := by
    have h : 4 / e < N := by linarith
    rw [div_lt_iff₀ he0] at h
    rw [div_le_div_iff₀ hNpos two_pos]
    linarith
  -- Hall's theorem on the coarse grid.
  obtain ⟨σ, hσ⟩ := exists_perm_hall N T
  -- The fine grid: each coarse cube is cut into `m ^ d` cubes, with `σ ^ m = 1`.
  have hσm : σ ^ Fintype.card (Equiv.Perm (Fin d → Fin N)) = 1 := pow_card_eq_one
  have hm0 : Fintype.card (Equiv.Perm (Fin d → Fin N)) ≠ 0 := Fintype.card_ne_zero
  generalize Fintype.card (Equiv.Perm (Fin d → Fin N)) = m at hσm hm0
  have : NeZero m := ⟨hm0⟩
  have hσM : σ ^ (m ^ d) = 1 := by
    rw [show m ^ d = m * m ^ (d - 1) by rw [← pow_succ', Nat.sub_add_cancel hd], pow_mul, hσm,
      one_pow]
  -- The cyclic permutation of the fine grid.
  let b₀ : Fin d → Fin m := finFunctionFinEquiv.symm 0
  let Φ : Equiv.Perm (Fin d → Fin (N * m)) :=
    (splitEquiv N m d).symm.permCongr (twist σ (odometer N d) (odometer m d) b₀)
  have hcyc : Φ.IsCycle ∧ Φ.support = Finset.univ := by
    have hNm : 1 < N * m := lt_of_lt_of_le hN2 (Nat.le_mul_of_pos_right N
      (Nat.pos_of_ne_zero hm0))
    refine isCycle_of_sameCycle Φ (fun x y => sameCycle_permCongr _ _ ?_)
      (x₀ := fun _ => 0) (x₁ := fun _ => ⟨1, hNm⟩) ?_
    · refine twist_sameCycle σ (odometer N d) (odometer m d) b₀ (m ^ d)
        (Nat.pos_of_ne_zero (pow_ne_zero d hm0)) hσM
        ((odometer_iterate_zero_eq_iff m d _).2 dvd_rfl)
        (fun t ht0 htM => mt (odometer_iterate_zero_eq_iff m d t).1
          (Nat.not_dvd_of_pos_of_lt ht0 htM))
        (fun b => odometer_reach m d b b₀) (odometer_reach N d) _ _
    · intro h
      have := congrArg Fin.val (congrFun h ⟨0, hd⟩)
      simp at this
  have : NeZero (N * m) := ⟨Nat.mul_ne_zero (NeZero.ne N) hm0⟩
  let S : VolumePreservingEquiv d :=
    ⟨exchangeEquiv (N * m) Φ, measurePreserving_exchange (N * m) Φ⟩
  refine ⟨N * m, S, ?_, ?_⟩
  · refine ⟨Nat.pos_of_ne_zero (NeZero.ne _), Φ, hcyc.1, hcyc.2, fun k x hx i => ?_⟩
    have hk : cubeIdx (N * m) x = k := (cubeIdx_eq_iff _ x k).2 hx
    change (x + shiftVec (N * m) Φ (cubeIdx (N * m) x)) i = _
    rw [hk]
    rfl
  · refine lt_of_le_of_lt ?_ heε
    refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x => ?_)
    change edist (T.toHomeomorph x) (exchange (N * m) Φ x) ≤ ENNReal.ofReal e
    refine (edist_lt_ofReal.2 ?_).le
    -- `x` lies in the fine cube `j`, inside the coarse cube `K`.
    obtain ⟨z, hzK, hTz⟩ := hσ (splitEquiv N m d (cubeIdx (N * m) x)).1
    have hxK := cubeIdx_coarse N m x
    have hzK' := (cubeIdx_eq_iff N z _).2 hzK
    have hTz' := (cubeIdx_eq_iff N _ _).2 hTz
    have hSx : cubeIdx N (exchange (N * m) Φ x) =
        (twist σ (odometer N d) (odometer m d) b₀ (splitEquiv N m d (cubeIdx (N * m) x))).1 := by
      rw [cubeIdx_coarse N m, cubeIdx_exchange]
      simp [Φ, Equiv.permCongr_apply]
    have h1 : dist x z < δ := by
      rw [dist_pi_lt_iff hδ]
      intro i
      refine (dist_lt_of_idx N (x i) (z i) (Or.inl ?_)).trans hNδ
      exact congrArg Fin.val (congrFun (hzK'.trans hxK.symm) i)
    have h2 : dist (T.toHomeomorph z) (exchange (N * m) Φ x) < 2 / N := by
      rw [dist_pi_lt_iff (by positivity)]
      intro i
      apply dist_lt_of_idx
      have hTzi : idx N (T.toHomeomorph z i) = σ (splitEquiv N m d (cubeIdx (N * m) x)).1 i :=
        congrFun hTz' i
      have hSxi := congrFun hSx i
      change idx N (exchange (N * m) Φ x i) = _ at hSxi
      rw [hTzi, hSxi, twist_apply]
      split_ifs
      · exact odometer_apply_val N d hN2 _ i
      · exact Or.inl rfl
    calc dist (T.toHomeomorph x) (exchange (N * m) Φ x)
        ≤ dist (T.toHomeomorph x) (T.toHomeomorph z) +
            dist (T.toHomeomorph z) (exchange (N * m) Φ x) := dist_triangle _ _ _
      _ < e / 2 + e / 2 := add_lt_add_of_lt_of_le (hT h1) (h2.le.trans hNe)
      _ = e := add_halves e

end Dynamics.LaxApproximation

end MathlibExt.Dynamics.LaxApproximationWanted
