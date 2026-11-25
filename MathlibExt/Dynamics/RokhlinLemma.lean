/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/RokhlinLemma.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `rokhlin_lemma`:
the four tower and aperiodicity definitions and the statement of the Rokhlin lemma.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

The wanted module placed the declarations in their present namespace and revised the docstrings.
This module moves them to the proved library and supplies the proof.
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Rokhlin's lemma for non-invertible maps

`Dynamics.rokhlin_lemma` constructs a measurable base whose disjoint forward images cover
a prescribed fraction of a standard Borel probability space. The proof constructs a small set
visited by almost every orbit, then groups first entrance times into blocks of the given height.
-/

@[expose] public section

namespace MathlibExt.Dynamics.RokhlinLemmaWanted
namespace Dynamics

open MeasureTheory Set

set_option linter.dupNamespace false in
/-- **Aperiodic transformation.** Let $\mu$ be a measure on a measurable space $\Omega$. A map
$T : \Omega \to \Omega$ is aperiodic with respect to $\mu$ if the set of periodic points of $T$,
the points $x$ with $T^k(x) = x$ for some $k \ge 1$, where $T^k$ is the $k$-fold iterate of $T$,
has (outer) $\mu$-measure zero. Equivalently, for $\mu$-almost every $x$, no positive iterate of
$T$ fixes $x$. -/
def IsAperiodic {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (μ : Measure Ω) : Prop :=
  μ (Function.periodicPts T) = 0

set_option linter.dupNamespace false in
/-- **Floor of a Rokhlin tower.** For a map $T : \Omega \to \Omega$, a set
$B \subseteq \Omega$ and $k \in \mathbb{N}$, the level-$k$ floor with base $B$ is the image
$T^k(B)$ of $B$ under the $k$-fold iterate $T^k$ of $T$; the level-$0$ floor is $B$. -/
def towerFloor {Ω : Type*} (T : Ω → Ω) (B : Set Ω) (k : ℕ) : Set Ω :=
  T^[k] '' B

set_option linter.dupNamespace false in
/-- **Union of a Rokhlin tower.** For a map $T : \Omega \to \Omega$, a set
$B \subseteq \Omega$ and $n \in \mathbb{N}$, the union of the tower with base $B$ and height $n$
is the set $\bigcup_{k=0}^{n-1} T^k(B)$ of its floors $B, T(B), \dots, T^{n-1}(B)$, where
$T^k(B)$ is the image of $B$ under the $k$-fold iterate of $T$. It is empty when $n = 0$, and
no disjointness of the floors is required. -/
def towerUnion {Ω : Type*} (T : Ω → Ω) (B : Set Ω) (n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range n, towerFloor T B k

set_option linter.dupNamespace false in
/-- **Rokhlin tower.** Let $\Omega$ be a measurable space, $T : \Omega \to \Omega$ a map and
$n \in \mathbb{N}$. A set $B \subseteq \Omega$ is the base of a Rokhlin tower of height $n$
for $T$ if $B$ is measurable and the floors $B, T(B), \dots, T^{n-1}(B)$ are pairwise
disjoint, that is, $T^i(B) \cap T^j(B) = \emptyset$ for all $i \ne j$ with $i, j < n$; here
$T^k(B)$ is the image of $B$ under the $k$-fold iterate of $T$.

Only the base is required to be measurable. For a non-invertible $T$, the floors need not be
measurable, so evaluating a measure on their union uses its outer measure. -/
def IsRokhlinTower {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (B : Set Ω) (n : ℕ) : Prop :=
  MeasurableSet B ∧
    (Finset.range n : Set ℕ).PairwiseDisjoint (towerFloor T B)

section

open Function Filter

variable {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω} {μ : Measure Ω}

/-- Each nonperiodic point has a basic neighborhood that its next few iterates miss.
Discard points of each neighborhood that return to it too soon. -/
private theorem separated_cover [StandardBorelSpace Ω] (hT : Measurable T) (m : ℕ) :
    ∃ E : ℕ → Set Ω, (∀ i, MeasurableSet (E i)) ∧
      (∀ i x, x ∈ E i → ∀ k, 0 < k → k < m → T^[k] x ∉ E i) ∧
      ∀ x ∉ periodicPts T, ∃ i, x ∈ E i := by
  classical
  let := upgradeStandardBorel Ω
  obtain ⟨U, hU⟩ := TopologicalSpace.exists_seq_basis Ω
  have hm i : MeasurableSet (U i) := (hU.isOpen (mem_range_self i)).measurableSet
  let E i := U i \ ⋃ k ∈ Finset.Ioo 0 m, T^[k] ⁻¹' U i
  refine ⟨E, fun i ↦ (hm i).diff (.iUnion fun k ↦ .iUnion fun _ ↦
    (hT.iterate k) (hm i)), ?_, ?_⟩
  · intro i x hx k hk hkm hy
    exact hx.2 (mem_iUnion₂.mpr ⟨k, Finset.mem_Ioo.mpr ⟨hk, hkm⟩, hy.1⟩)
  · intro x hx
    let F := (Finset.Ioo 0 m).image (fun k ↦ T^[k] x)
    have hxF : x ∈ (F : Set Ω)ᶜ := by
      intro h
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
      exact hx (mem_periodicPts.mpr ⟨k, (Finset.mem_Ioo.mp hk).1, heq⟩)
    obtain ⟨_, ⟨i, rfl⟩, hi, hsub⟩ := hU.exists_subset_of_mem_open hxF
      F.finite_toSet.isClosed.isOpen_compl
    refine ⟨i, hi, ?_⟩
    intro h
    obtain ⟨k, hk, hkU⟩ := mem_iUnion₂.mp h
    exact hsub hkU (Finset.mem_image_of_mem _ hk)

/-- Select the first member of the countable cover visited infinitely often. Its index
is constant along the orbit. This gives a single set with well-separated visits. -/
private theorem exists_marker [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ) (m : ℕ) :
    ∃ A : Set Ω, MeasurableSet A ∧
      (∀ x ∈ A, ∀ k, 0 < k → k < m → T^[k] x ∉ A) ∧
      ∀ᵐ x ∂μ, ∃ k : ℕ, T^[k] x ∈ A := by
  classical
  obtain ⟨E, hE, hsep, hcover⟩ := separated_cover hT.measurable m
  let R i := {x : Ω | ∃ᶠ k in atTop, T^[k] x ∈ E i}
  have hR i : MeasurableSet (R i) := by
    simp only [R, frequently_atTop, ofPred_forall, ofPred_exists]
    refine .iInter fun b ↦ .iUnion fun k ↦ ?_
    by_cases h : b ≤ k
    · simp only [h, true_and]
      exact (hT.iterate k).measurable (hE i)
    · simp [h]
  have hinv i k x : T^[k] x ∈ R i ↔ x ∈ R i := by
    change (∃ᶠ j in atTop, T^[j] (T^[k] x) ∈ E i) ↔ ∃ᶠ j in atTop, T^[j] x ∈ E i
    conv_rhs => rw [← map_add_atTop_eq_nat k, frequently_map]
    simp only [iterate_add_apply]
  let C i := R i \ ⋃ j ∈ Finset.range i, R j
  have hC i : MeasurableSet (C i) := (hR i).diff (.iUnion fun j ↦ .iUnion fun _ ↦ hR j)
  have hCi i k x : T^[k] x ∈ C i ↔ x ∈ C i := by
    simp [C, hinv]
  let A := ⋃ i, E i ∩ C i
  refine ⟨A, .iUnion fun i ↦ (hE i).inter (hC i), ?_, ?_⟩
  · intro x hx k hk hkm hy
    obtain ⟨i, hxi, hxc⟩ := mem_iUnion.mp hx
    obtain ⟨j, hyj, hyc⟩ := mem_iUnion.mp hy
    have hj := (hCi j k x).mp hyc
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hj.2 (mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hij, hxc.1⟩)
    · exact hsep i x hxi k hk hkm hyj
    · exact hxc.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hji, hj.1⟩)
  · have hrec : ∀ᵐ x ∂μ, ∀ i, x ∈ E i → x ∈ R i :=
      ae_all_iff.mpr fun i ↦ hT.conservative.ae_mem_imp_frequently_image_mem
        (hE i).nullMeasurableSet
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hap, hrec] with x hx hr
    obtain ⟨i, hi⟩ := hcover x hx
    have hex : ∃ j, x ∈ R j := ⟨i, hr i hi⟩
    let j := Nat.find hex
    have hj : x ∈ R j := Nat.find_spec hex
    have hc : x ∈ C j := by
      refine ⟨hj, ?_⟩
      intro h
      obtain ⟨l, hl, hlR⟩ := mem_iUnion₂.mp h
      exact Nat.find_min hex (Finset.mem_range.mp hl) hlR
    obtain ⟨k, hk⟩ := hj.exists
    exact ⟨k, mem_iUnion.mpr ⟨j, hk, (hCi j k x).mpr hc⟩⟩

section
omit [MeasurableSpace Ω]

/-- A set admitting no short return has disjoint iterated preimages. -/
private theorem preimages_disjoint {A : Set Ω} {m : ℕ}
    (h : ∀ x ∈ A, ∀ k, 0 < k → k < m → T^[k] x ∉ A) :
    (Finset.range m : Set ℕ).PairwiseDisjoint (fun k ↦ T^[k] ⁻¹' A) := by
  intro i hi j hj hij
  wlog hlt : i < j generalizing i j
  · exact (this hj hi hij.symm (by omega)).symm
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  apply h _ hxi (j - i) (by omega) (by have := Finset.mem_range.mp hj; omega)
  rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
  exact hxj

/-- The points whose first visit to the marker is exactly at time `k`. -/
private def firstVisit (T : Ω → Ω) (A : Set Ω) (k : ℕ) : Set Ω :=
  T^[k] ⁻¹' A \ ⋃ j ∈ Finset.range k, T^[j] ⁻¹' A

private theorem firstVisit_unique {A : Set Ω} {x : Ω} {i j : ℕ}
    (hi : x ∈ firstVisit T A i) (hj : x ∈ firstVisit T A j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (hj.2 (mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr h, hi.1⟩)).elim
  · exact h
  · exact (hi.2 (mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr h, hj.1⟩)).elim

private theorem firstVisit_iterate {A : Set Ω} {x : Ω} {k j : ℕ}
    (hx : x ∈ firstVisit T A k) (hj : j ≤ k) : T^[j] x ∈ firstVisit T A (k - j) := by
  refine ⟨?_, ?_⟩
  · change T^[k - j] (T^[j] x) ∈ A
    rw [← iterate_add_apply, Nat.sub_add_cancel hj]
    exact hx.1
  · intro h
    obtain ⟨i, hi, hmem⟩ := mem_iUnion₂.mp h
    apply hx.2 (mem_iUnion₂.mpr ⟨i + j, Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hi
      omega), ?_⟩)
    simpa only [mem_preimage, iterate_add_apply] using hmem

end

/-- Assemble full blocks of height `n` by using positive multiples of `n` as first visit times.
Only points within `n` steps of the marker can be missed among the orbits that visit it. -/
private theorem build_preimage_tower (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    (n : ℕ) (hn : 0 < n) :
    ∃ D : Set Ω, MeasurableSet D ∧
      (Finset.range n : Set ℕ).PairwiseDisjoint (fun k ↦ T^[k] ⁻¹' D) ∧
      ∀ x, (∃ k : ℕ, T^[k] x ∈ A) →
        x ∈ (⋃ k ∈ Finset.range n, T^[k] ⁻¹' D) ∪ (⋃ k ∈ Finset.range n, T^[k] ⁻¹' A) := by
  classical
  let D := ⋃ k : ℕ, ⋃ (_ : n ≤ k ∧ n ∣ k), firstVisit T A k
  have hD : MeasurableSet D := .iUnion fun k ↦ .iUnion fun _ ↦
    ((hT.iterate k) hA).diff (.iUnion fun j ↦ .iUnion fun _ ↦ (hT.iterate j) hA)
  refine ⟨D, hD, preimages_disjoint ?_, ?_⟩
  · intro x hx j hj hjn hy
    obtain ⟨k, ⟨hnk, hdk⟩, hk⟩ := mem_iUnion₂.mp hx
    obtain ⟨l, ⟨_, hdl⟩, hl⟩ := mem_iUnion₂.mp hy
    have heq := firstVisit_unique (firstVisit_iterate hk (show j ≤ k by omega)) hl
    have hd : n ∣ j := by
      have hsub := Nat.dvd_sub hdk hdl
      rwa [← heq, Nat.sub_sub_self (show j ≤ k by omega)] at hsub
    exact (Nat.le_of_dvd hj hd).not_gt hjn
  · intro x hx
    let k := Nat.find hx
    have hk : x ∈ firstVisit T A k := by
      refine ⟨Nat.find_spec hx, ?_⟩
      intro h
      obtain ⟨j, hj, hjA⟩ := mem_iUnion₂.mp h
      exact Nat.find_min hx (Finset.mem_range.mp hj) hjA
    by_cases hkn : k < n
    · exact Or.inr (mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hkn, hk.1⟩)
    · have hmod := Nat.mod_lt k hn
      refine Or.inl (mem_iUnion₂.mpr ⟨k % n, Finset.mem_range.mpr hmod, ?_⟩)
      have hd : n ∣ k - k % n := Nat.dvd_sub_mod k
      have hpos : 0 < k - k % n := by omega
      exact mem_iUnion₂.mpr ⟨k - k % n, ⟨Nat.le_of_dvd hpos hd, hd⟩,
        firstVisit_iterate hk (Nat.mod_le ..)⟩

/-- Reverse a preimage tower by taking its deepest preimage as base. On the range of
the corresponding iterate every point of the preimage tower lies on a forward floor. -/
private theorem forward_tower (hT : MeasurePreserving T μ μ) {D : Set Ω}
    (hD : MeasurableSet D) {n : ℕ}
    (hdis : (Finset.range n : Set ℕ).PairwiseDisjoint (fun k ↦ T^[k] ⁻¹' D)) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (⋃ k ∈ Finset.range n, T^[k] ⁻¹' D) ≤ μ (towerUnion T B n) := by
  let m := n - 1
  let B := T^[m] ⁻¹' D
  have hfloor (k : ℕ) (hk : k < n) : towerFloor T B k ⊆ T^[m - k] ⁻¹' D := by
    rintro _ ⟨x, hx, rfl⟩
    change T^[m - k] (T^[k] x) ∈ D
    rw [← iterate_add_apply, Nat.sub_add_cancel (show k ≤ m by dsimp [m]; omega)]
    exact hx
  refine ⟨B, ⟨(hT.iterate m).measurable hD, ?_⟩, ?_⟩
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have H := hdis (Finset.mem_range.mpr (show m - i < n by dsimp [m]; omega))
      (Finset.mem_range.mpr (show m - j < n by dsimp [m]; omega))
      (show m - i ≠ m - j by dsimp [m]; omega)
    exact H.mono (hfloor i hi') (hfloor j hj')
  · let U := ⋃ k ∈ Finset.range n, T^[k] ⁻¹' D
    have hU : MeasurableSet U := .iUnion fun k ↦ .iUnion fun _ ↦ (hT.iterate k).measurable hD
    calc
      μ U = μ (T^[m] ⁻¹' U) := ((hT.iterate m).measure_preimage hU.nullMeasurableSet).symm
      _ ≤ μ (T^[m] ⁻¹' towerUnion T B n) := by
        apply measure_mono
        intro x hx
        obtain ⟨k, hk, hkD⟩ := mem_iUnion₂.mp (show T^[m] x ∈ U from hx)
        have hkn := Finset.mem_range.mp hk
        refine mem_iUnion₂.mpr ⟨m - k, Finset.mem_range.mpr (by dsimp [m]; omega),
          T^[k] x, ?_, ?_⟩
        · change T^[m] (T^[k] x) ∈ D
          simpa only [mem_preimage, ← iterate_add_apply, add_comm m k] using hkD
        · rw [← iterate_add_apply, Nat.sub_add_cancel (show k ≤ m by dsimp [m]; omega)]
      _ ≤ μ (towerUnion T B n) := (hT.iterate m).measure_preimage_le _

end

set_option linter.dupNamespace false in
/-- **Rokhlin lemma for non-invertible maps.** Let $\Omega$ be a standard Borel space with a
probability measure $\mu$, and let $T : \Omega \to \Omega$ be a measure-preserving map that is
aperiodic with respect to $\mu$. Then for every integer $n \ge 1$ and every
$\varepsilon \in (0, \infty]$ there is a measurable set $B \subseteq \Omega$ such that the
floors $B, T(B), \dots, T^{n-1}(B)$ are pairwise disjoint, where $T^k(B)$ is the image of $B$
under the $k$-fold iterate of $T$, and their union $\bigcup_{k=0}^{n-1} T^k(B)$ has outer
$\mu$-measure at least $1 - \varepsilon$ (truncated subtraction, so the bound is $0$ when
$\varepsilon \ge 1$). No invertibility of $T$ is assumed.

Source: V. A. Rokhlin, *A general measure-preserving transformation is not mixing*, Doklady Akademii
Nauk SSSR 60 (1948), 349-351 (original Russian; English translation later); S. Kakutani, *Induced
measure-preserving transformations*, Proc. Imp. Acad. Tokyo 19 (1943), 635-641 (independent
discovery); S.-M. Heinemann and O. Schmitt, *Rokhlin's lemma for non-invertible maps*, Dynam.
Systems Appl. 10 (2001), no. 2, 201-213. The classical form is listed as §109 in O. Knill, *Some
Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `rokhlin_lemma`. -/
public theorem rokhlin_lemma {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (_hT : MeasurePreserving T μ μ) (_hap : IsAperiodic T μ)
    (n : ℕ) (_hn : 1 ≤ n) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (towerUnion T B n) ≥ 1 - ε := by
  obtain ⟨m, _, hm⟩ := ENNReal.exists_nat_pos_inv_mul_lt (ENNReal.natCast_ne_top n) _hε.ne'
  obtain ⟨A, hA, hsep, hit⟩ := exists_marker _hT _hap m
  have hpre k := (_hT.iterate k).measure_preimage hA.nullMeasurableSet
  have hsmall : μ A ≤ (m : ENNReal)⁻¹ := by
    apply ENNReal.le_inv_iff_mul_le.mpr
    have hsum := measure_biUnion_finset (μ := μ) (preimages_disjoint hsep)
      (fun k _ ↦ (_hT.iterate k).measurable hA)
    simpa only [hsum, hpre, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using
      (prob_le_one (μ := μ) (s := ⋃ k ∈ Finset.range m, T^[k] ⁻¹' A))
  obtain ⟨D, hD, hdis, hcover⟩ := build_preimage_tower _hT.measurable hA n _hn
  obtain ⟨B, hB, hforward⟩ := forward_tower _hT hD hdis
  refine ⟨B, hB, tsub_le_iff_right.mpr ?_⟩
  let U := ⋃ k ∈ Finset.range n, T^[k] ⁻¹' D
  let V := ⋃ k ∈ Finset.range n, T^[k] ⁻¹' A
  have hfull : μ univ ≤ μ (U ∪ V) :=
    measure_mono_ae (hit.mono fun x hx _ ↦ hcover x hx)
  have hV : μ V ≤ (n : ENNReal) * μ A := by
    simpa only [hpre, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (measure_biUnion_finset_le (μ := μ) (Finset.range n) (fun k ↦ T^[k] ⁻¹' A))
  rw [measure_univ] at hfull
  apply (hfull.trans (measure_union_le U V)).trans
  apply add_le_add hforward
  exact hV.trans ((mul_le_mul_right hsmall _).trans (by simpa only [mul_comm] using hm.le))

end Dynamics

end MathlibExt.Dynamics.RokhlinLemmaWanted
