/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/OrnsteinWeiss.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `ornstein_weiss_rokhlin`:
the definitions of freeness and the integer box, and the statement of the Rokhlin lemma.
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

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Ornstein–Weiss `ℤᵈ` Rokhlin lemma (Ornstein–Weiss, 1987)

For every dimension `d ≥ 1`, every free
measure-preserving `ℤᵈ`-action `T` on a standard Borel probability
space, every box size `N ≥ 1`, and every `ε > 0`, there is a measurable
base `B` such that the translates `T v '' B` for `v ∈ [0, N)ᵈ` are
pairwise disjoint and their union has measure at least `1 − ε`. Knill discusses this
multidimensional extension in §109 of *Some Fundamental Theorems in Mathematics*.

The action laws give each `T v` the inverse `T (-v)`. The standard Borel hypothesis
provides a countable family of measurable sets separating points.

## Proof

Let `a` be the supremum of the measures of bases for the box of side `N`. Partition a conull
set into countably many measurable sets such that the translates of each set by a large box
are disjoint. Over one partition member at a time, replace the old bases in that box by a
regular grid of new bases. The padding around the grid prevents collisions with the old towers
outside the box. Sum the resulting inequalities over finitely many partition members and let
the old base measure tend to `a`. Exhausting the partition gives `k^d ≤ (N * (k + 1))^d * a`
for each grid size `k`. Letting `k` grow gives the required tower coverage.
-/

namespace MathlibExt.Dynamics.OrnsteinWeissWanted.Dynamics

open MeasureTheory Set Filter

set_option linter.dupNamespace false in
/-- **Free $\mathbb{Z}^d$-action.** Let $d$ be a natural number, let $\mu$ be a measure on a
measurable space $\Omega$, and let $T$ assign to each $v \in \mathbb{Z}^d$ a map
$T_v \colon \Omega \to \Omega$. Then $T$ is free (in the Ornstein–Weiss sense) with respect to
$\mu$ if, for every nonzero $v \in \mathbb{Z}^d$, the set of points $x \in \Omega$ with
$T_v(x) = x$ has $\mu$-measure zero. -/
@[expose] public def IsFreeAction {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (T : (Fin d → ℤ) → Ω → Ω) : Prop :=
  ∀ v : Fin d → ℤ, v ≠ 0 → μ {x | T v x = x} = 0

set_option linter.dupNamespace false in
/-- **Integer box.** For natural numbers $d$ and $N$, the integer box $[0, N)^d$ is the finite set
of vectors $v \in \mathbb{Z}^d$ with $0 \le v_i < N$ for every coordinate $i$. -/
@[expose] public noncomputable def boxShape (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) (N : ℤ))

private abbrev Lattice (d : ℕ) := Fin d → ℤ

private structure Action {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d : ℕ) where
  T : Lattice d → Ω → Ω
  zero (x) : T 0 x = x
  add (u v x) : T (u + v) x = T u (T v x)
  mp (u) : MeasurePreserving (T u) μ μ

namespace Action

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ} (A : Action μ d)

private def shift (v : Lattice d) (B : Set Ω) : Set Ω := A.T v '' B

private theorem cancel (v : Lattice d) (x : Ω) : A.T (-v) (A.T v x) = x := by
  rw [← A.add, neg_add_cancel, A.zero]

private theorem shift_eq (v : Lattice d) (B : Set Ω) : A.shift v B = A.T (-v) ⁻¹' B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, A.cancel] using hy
  · intro hx
    exact ⟨_, hx, by rw [← A.add, add_neg_cancel, A.zero]⟩

private theorem measurable_shift (v : Lattice d) {B : Set Ω} (hB : MeasurableSet B) :
    MeasurableSet (A.shift v B) := A.shift_eq v B ▸ (A.mp (-v)).measurable hB

private theorem real_shift (v : Lattice d) {B : Set Ω} (hB : MeasurableSet B) :
    μ.real (A.shift v B) = μ.real B := by
  rw [A.shift_eq, Measure.real, (A.mp (-v)).measure_preimage hB.nullMeasurableSet]
  rfl

private def region (F : Finset (Lattice d)) (B : Set Ω) : Set Ω := ⋃ v ∈ F, A.shift v B

private def Packs (F : Finset (Lattice d)) (B : Set Ω) : Prop :=
  (F : Set (Lattice d)).PairwiseDisjoint (fun v ↦ A.shift v B)

private theorem measurable_region (F : Finset (Lattice d)) {B : Set Ω} (hB : MeasurableSet B) :
    MeasurableSet (A.region F B) :=
  .iUnion fun v ↦ .iUnion fun _ ↦ A.measurable_shift v hB

private theorem real_region [IsProbabilityMeasure μ] {F : Finset (Lattice d)} {B : Set Ω}
    (hB : MeasurableSet B) (hp : A.Packs F B) : μ.real (A.region F B) = F.card * μ.real B := by
  rw [region, measureReal_biUnion_finset hp (fun v _ ↦ A.measurable_shift v hB)]
  simp [A.real_shift _ hB]

/-- A countable measurable partition of a conull set into bases of disjoint finite towers. -/
private theorem partition [StandardBorelSpace Ω] (hf : IsFreeAction μ A.T)
    (Q : Finset (Lattice d)) :
    ∃ E : ℕ → Set Ω, (∀ i, MeasurableSet (E i)) ∧ Pairwise (Function.onFun Disjoint E) ∧
      (∀ i, A.Packs Q (E i)) ∧ ∀ᵐ x ∂μ, x ∈ ⋃ i, E i := by
  classical
  let := upgradeStandardBorel Ω
  obtain ⟨U, hU⟩ := TopologicalSpace.exists_seq_basis Ω
  have hm i : MeasurableSet (U i) := (hU.isOpen (mem_range_self i)).measurableSet
  let D := (Q.biUnion fun v ↦ Q.image (fun w ↦ v - w)).erase 0
  let V i := U i \ ⋃ g ∈ D, A.T g ⁻¹' U i
  have hV i : MeasurableSet (V i) := (hm i).diff (.iUnion fun g ↦
    .iUnion fun _ ↦ (A.mp g).measurable (hm i))
  refine ⟨disjointed V, MeasurableSet.disjointed hV, disjoint_disjointed V, ?_, ?_⟩
  · intro i v hv w hw hvw
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hxy : A.T (v - w) x = y := by
      rw [sub_eq_neg_add, A.add, ← he, A.cancel]
    have hg : v - w ∈ D := Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hvw,
      Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ hw⟩⟩
    have hx' := disjointed_le V i hx
    have hy' := disjointed_le V i hy
    exact hx'.2 (mem_iUnion₂.mpr ⟨v - w, hg, by simpa only [mem_preimage, hxy] using hy'.1⟩)
  · rw [iUnion_disjointed]
    have hfree : ∀ᵐ x ∂μ, ∀ g : Lattice d, g ≠ 0 → A.T g x ≠ x :=
      ae_all_iff.mpr fun g ↦ by
        by_cases hg : g = 0
        · simp [hg]
        · simpa [hg] using measure_eq_zero_iff_ae_notMem.mp (hf g hg)
    filter_upwards [hfree] with x hx
    let F := D.image (fun g ↦ A.T g x)
    have hxF : x ∈ (F : Set Ω)ᶜ := by
      rintro h
      obtain ⟨g, hg, he⟩ := Finset.mem_image.mp h
      exact hx g (Finset.mem_erase.mp hg).1 he
    obtain ⟨_, ⟨i, rfl⟩, hi, hsub⟩ := hU.exists_subset_of_mem_open hxF
      F.finite_toSet.isClosed.isOpen_compl
    refine mem_iUnion.mpr ⟨i, hi, ?_⟩
    intro h
    obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
    exact hsub hxg (Finset.mem_image_of_mem _ hg)

/-- The offsets `P` place disjoint copies of the tile `F` inside `Q`. The padding in `Q`
contains the base of any old tile that could meet one of these copies. -/
private structure Grid (F P Q : Finset (Lattice d)) : Prop where
  sub : P ⊆ Q
  inside : ∀ u ∈ F, ∀ p ∈ P, u + p ∈ Q
  trim : ∀ u ∈ F, ∀ p ∈ P, ∀ v ∈ F, u + p - v ∈ Q
  unique : ∀ u ∈ F, ∀ v ∈ F, u ≠ v → ∀ p ∈ P, ∀ r ∈ P, u + p ≠ v + r

/-- Replace the old bases in the padded box by a regular grid of new bases. -/
private theorem replace_packs {F P Q : Finset (Lattice d)} (g : Grid F P Q) {B E : Set Ω}
    (hB : A.Packs F B) (hE : A.Packs Q E) :
    A.Packs F ((B \ A.region Q E) ∪ A.region P E) := by
  classical
  have cross {u v : Lattice d} (hu : u ∈ F) (hv : v ∈ F) {x y : Ω}
      (hx : x ∉ A.region Q E) (hy : y ∈ A.region P E) (eq : A.T u x = A.T v y) : False := by
    obtain ⟨p, hp, z, hz, rfl⟩ := mem_iUnion₂.mp hy
    apply hx
    refine mem_iUnion₂.mpr ⟨v + p - u, g.trim v hv p hp u hu, z, hz, ?_⟩
    rw [sub_eq_neg_add, A.add, A.add, ← eq, A.cancel]
  intro u hu v hv huv
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Set.disjoint_left.mp (hB hu hv huv) ⟨x, hx.1, rfl⟩ ⟨y, hy.1, he⟩
  · exact cross hu hv hx.2 hy he.symm
  · exact cross hv hu hy.2 hx he
  · obtain ⟨p, hp, z, hz, rfl⟩ := mem_iUnion₂.mp hx
    obtain ⟨r, hr, t, ht, rfl⟩ := mem_iUnion₂.mp hy
    rw [← A.add, ← A.add] at he
    exact Set.disjoint_left.mp (hE (g.inside u hu p hp) (g.inside v hv r hr)
      (g.unique u hu v hv huv p hp r hr)) ⟨z, hz, rfl⟩ ⟨t, ht, he⟩

private def masses (F : Finset (Lattice d)) : Set ℝ :=
  {r | ∃ B, MeasurableSet B ∧ A.Packs F B ∧ μ.real B = r}

private theorem zero_mass (F : Finset (Lattice d)) : 0 ∈ A.masses F := by
  refine ⟨∅, .empty, ?_, by simp⟩
  intro u _ v _ _
  simp [shift]

variable [IsProbabilityMeasure μ]

private theorem bounded_masses (F : Finset (Lattice d)) : BddAbove (A.masses F) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨B, _, _, rfl⟩
  simp

/-- The gain in base measure is at most the gap to the supremum. -/
private theorem replace_bound {F P Q : Finset (Lattice d)} (g : Grid F P Q) {B E : Set Ω}
    (hB : MeasurableSet B) (hF : A.Packs F B) (hE : MeasurableSet E) (hQ : A.Packs Q E) :
    P.card * μ.real E ≤ (sSup (A.masses F) - μ.real B) + μ.real (B ∩ A.region Q E) := by
  let R := A.region Q E
  let S := A.region P E
  have hR : MeasurableSet R := A.measurable_region Q hE
  have hS : MeasurableSet S := A.measurable_region P hE
  have hSR : S ⊆ R := iUnion₂_mono' fun p hp ↦ ⟨p, g.sub hp, Subset.rfl⟩
  have hd : Disjoint (B \ R) S := Set.disjoint_left.mpr fun _ hx hy ↦ hx.2 (hSR hy)
  have hsup := le_csSup (A.bounded_masses F) (show μ.real ((B \ R) ∪ S) ∈ A.masses F from
    ⟨_, (hB.diff hR).union hS, A.replace_packs g hF hQ, rfl⟩)
  rw [measureReal_union hd hS] at hsup
  have hmass : μ.real S = P.card * μ.real E := A.real_region hE
    (fun _ hu _ hv huv ↦ hQ (g.sub hu) (g.sub hv) huv)
  have hsplit := measureReal_sdiff_add_inter (μ := μ) (s := B) hR
  change _ ≤ _ + μ.real (B ∩ R)
  linarith

/-- Across disjoint classes of centers each translate charges the old base at most once. -/
private theorem sum_inter_region (Q : Finset (Lattice d)) {B : Set Ω} (hB : MeasurableSet B)
    {E : ℕ → Set Ω} (hm : ∀ i, MeasurableSet (E i)) (hd : Pairwise (Function.onFun Disjoint E))
    (I : Finset ℕ) :
    ∑ i ∈ I, μ.real (B ∩ A.region Q (E i)) ≤ Q.card * μ.real B := by
  classical
  calc
    _ ≤ ∑ i ∈ I, ∑ q ∈ Q, μ.real (B ∩ A.shift q (E i)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [region, inter_iUnion] using
        measureReal_biUnion_finset_le (μ := μ) Q (fun q ↦ B ∩ A.shift q (E i))
    _ = ∑ q ∈ Q, ∑ i ∈ I, μ.real (B ∩ A.shift q (E i)) := Finset.sum_comm
    _ ≤ ∑ _q ∈ Q, μ.real B := by
      apply Finset.sum_le_sum
      intro q _
      have hdis : (I : Set ℕ).PairwiseDisjoint (fun i ↦ B ∩ A.shift q (E i)) := by
        intro i _ j _ hij
        simp only [A.shift_eq]
        exact ((hd hij).preimage (A.T (-q))).mono inter_subset_right inter_subset_right
      rw [← measureReal_biUnion_finset hdis (fun i _ ↦ hB.inter (A.measurable_shift q (hm i)))]
      exact measureReal_mono (iUnion₂_subset fun _ _ ↦ inter_subset_left)
    _ = _ := by simp

/-- Average the replacements over a partition, letting the old base approach the supremum. -/
private theorem grid_bound [StandardBorelSpace Ω] (hf : IsFreeAction μ A.T)
    {F P Q : Finset (Lattice d)} (g : Grid F P Q) :
    (P.card : ℝ) ≤ Q.card * sSup (A.masses F) := by
  classical
  obtain ⟨E, hm, hd, hp, hfull⟩ := A.partition hf Q
  obtain ⟨r, _, hr, hmem⟩ := exists_seq_tendsto_sSup ⟨_, A.zero_mass F⟩ (A.bounded_masses F)
  let a := sSup (A.masses F)
  have hfin (I : Finset ℕ) : P.card * (∑ i ∈ I, μ.real (E i)) ≤ Q.card * a := by
    have hlim := ((tendsto_const_nhds (x := a)).sub hr).const_mul (I.card : ℝ)
    have H (n : ℕ) : P.card * (∑ i ∈ I, μ.real (E i)) ≤
        I.card * (a - r n) + Q.card * r n := by
      obtain ⟨B, hB, hF, he⟩ := hmem n
      rw [← he, Finset.mul_sum]
      calc
        _ ≤ ∑ i ∈ I, ((a - μ.real B) + μ.real (B ∩ A.region Q (E i))) :=
          Finset.sum_le_sum fun i _ ↦ A.replace_bound g hB hF (hm i) (hp i)
        _ ≤ _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact A.sum_inter_region Q hB hm hd I
    simpa [a] using ge_of_tendsto' (hlim.add (hr.const_mul (Q.card : ℝ))) H
  have hμ : μ (⋃ i, E i) = 1 := by
    rw [← measure_univ (μ := μ)]
    exact measure_congr (ae_eq_univ.mpr hfull)
  have hsum : HasSum (fun i ↦ μ.real (E i)) 1 := by
    have H := (summable_measure_toReal (μ := μ) hm hd).hasSum
    simp only [Measure.real] at H
    rwa [← ENNReal.tsum_toReal_eq (fun i ↦ measure_ne_top μ (E i)),
      ← measure_iUnion hd hm, hμ, ENNReal.toReal_one] at H
  simpa using le_of_tendsto' (hsum.tendsto_sum_nat.const_mul (P.card : ℝ))
    (fun n ↦ hfin (Finset.range n))

end Action

private theorem mem_box {d n : ℕ} {v : Lattice d} :
    v ∈ boxShape d n ↔ ∀ i, 0 ≤ v i ∧ v i < n := by
  simp [boxShape]

private theorem card_box (d n : ℕ) : (boxShape d n).card = n ^ d := by
  simp [boxShape, Fintype.card_piFinset, Int.card_Ico]

/-- Put a grid of side length `k` inside a box padded by one tile width.
Reduction modulo `N` recovers the floor of each small tile. -/
private theorem box_grid (d N k : ℕ) (hN : 1 ≤ N) :
    ∃ P : Finset (Lattice d), P.card = k ^ d ∧
      Action.Grid (boxShape d N) P (boxShape d (N * (k + 1))) := by
  classical
  let f (z : Lattice d) : Lattice d := fun i ↦ N * (z i + 1)
  let P := (boxShape d k).image f
  have pos : 0 < (N : ℤ) := by exact_mod_cast hN
  have inj : Function.Injective f := by
    intro z w h
    funext i
    have hi := congrFun h i
    change (N : ℤ) * (z i + 1) = N * (w i + 1) at hi
    exact add_right_cancel (mul_left_cancel₀ pos.ne' hi)
  have bounds {p : Lattice d} (hp : p ∈ P) (i : Fin d) :
      N ≤ p i ∧ p i ≤ (N : ℤ) * k := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    have hi := mem_box.mp hz i
    change N ≤ (N : ℤ) * (z i + 1) ∧ (N : ℤ) * (z i + 1) ≤ N * k
    constructor
    · simpa using mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ z i + 1 by omega) pos.le
    · exact mul_le_mul_of_nonneg_left (by omega) pos.le
  refine ⟨P, (Finset.card_image_of_injective _ inj).trans (card_box d k), ?_⟩
  constructor
  · intro p hp
    apply mem_box.mpr
    intro i
    have := bounds hp i
    simp only [mul_add, mul_one]
    omega
  · intro u hu p hp
    apply mem_box.mpr
    intro i
    have := bounds hp i
    have := mem_box.mp hu i
    simp only [Pi.add_apply, mul_add, mul_one]
    omega
  · intro u hu p hp v hv
    apply mem_box.mpr
    intro i
    have := bounds hp i
    have := mem_box.mp hu i
    have := mem_box.mp hv i
    simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_one]
    omega
  · intro u hu v hv huv p hp r hr eq
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hr
    apply huv
    funext i
    have hi := congrArg (fun g : Lattice d ↦ g i % N) eq
    simpa only [Pi.add_apply, f, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (mem_box.mp hu i).1 (mem_box.mp hu i).2,
      Int.emod_eq_of_lt (mem_box.mp hv i).1 (mem_box.mp hv i).2] using hi

private theorem full_density {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ} (A : Action μ d)
    (hf : IsFreeAction μ A.T) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ (N : ℝ) ^ d * sSup (A.masses (boxShape d N)) := by
  let a := sSup (A.masses (boxShape d N))
  have H (k : ℕ) : ((k : ℝ) / (k + 1)) ^ d ≤ (N : ℝ) ^ d * a := by
    obtain ⟨P, hP, g⟩ := box_grid d N k hN
    have h := A.grid_bound hf g
    rw [hP, card_box] at h
    push_cast at h
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc
      _ ≤ _ := h
      _ = _ := by rw [mul_pow]; ring
  simpa using le_of_tendsto' ((tendsto_natCast_div_add_atTop (1 : ℝ)).pow d) H

set_option linter.dupNamespace false in
/-- **Ornstein–Weiss Rokhlin lemma for $\mathbb{Z}^d$-actions.** Let $d \ge 1$, let $\Omega$ be a
standard Borel space with a probability measure $\mu$, and let $T$ assign to each
$v \in \mathbb{Z}^d$ a map $T_v \colon \Omega \to \Omega$ such that $T_0$ is the identity,
$T_{u + v} = T_u \circ T_v$ for all $u, v \in \mathbb{Z}^d$, every $T_v$ is measure preserving
for $\mu$, and the action is free (for every $v \ne 0$ the set of fixed points of $T_v$ has
$\mu$-measure zero). Then for every integer $N \ge 1$ and every $\varepsilon \in (0, \infty]$
there is a measurable set $B \subseteq \Omega$ such that the images $T_v(B)$, for $v$ in the
integer box $[0, N)^d$, are pairwise disjoint and their union has measure at least
$1 - \varepsilon$.

Source: D. S. Ornstein and B. Weiss, *Entropy and isomorphism theorems for actions of amenable
groups*, J. Anal. Math. 48 (1987), 1-141. Listed as §109 in O. Knill, *Some Fundamental Theorems
in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
Via leanprover/lean-eval@38361be, problem `ornstein_weiss_rokhlin`. -/
public theorem ornstein_weiss_rokhlin {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    {d : ℕ} (_hd : 1 ≤ d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (Fin d → ℤ) → Ω → Ω)
    (_hid : ∀ x, T 0 x = x)
    (_hT : ∀ v, MeasurePreserving (T v) μ μ)
    (_hgrp : ∀ u v x, T (u + v) x = T u (T v x))
    (_hfree : IsFreeAction μ T)
    (N : ℕ) (_hN : 1 ≤ N) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω,
      MeasurableSet B ∧
      ((boxShape d N : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).PairwiseDisjoint
        (fun v => T v '' B) ∧
      μ (⋃ v ∈ boxShape d N, T v '' B) ≥ 1 - ε := by
  classical
  let A : Action μ d := ⟨T, _hid, _hgrp, _hT⟩
  let F := boxShape d N
  by_cases hε : ε < 1
  · have h : 0 < ε.toReal := ENNReal.toReal_pos _hε.ne' (hε.trans ENNReal.one_lt_top).ne
    have hn : 0 < (N : ℝ) := by exact_mod_cast _hN
    have hpow : 0 < (N : ℝ) ^ d := pow_pos hn d
    have hsup : (1 - ε.toReal) / (N : ℝ) ^ d < sSup (A.masses F) := by
      apply (div_lt_iff₀ hpow).mpr
      rw [mul_comm]
      exact (sub_lt_self 1 h).trans_le (full_density A _hfree N _hN)
    obtain ⟨_, ⟨B, hB, hp, rfl⟩, hm⟩ := exists_lt_of_lt_csSup ⟨_, A.zero_mass F⟩ hsup
    refine ⟨B, hB, hp, ?_⟩
    apply (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top μ _)).mp
    change (1 - ε).toReal ≤ μ.real (A.region F B)
    rw [ENNReal.toReal_sub_of_le hε.le ENNReal.one_ne_top, ENNReal.toReal_one,
      A.real_region hB hp, card_box, Nat.cast_pow, mul_comm]
    exact ((div_lt_iff₀ hpow).mp hm).le
  · refine ⟨∅, .empty, ?_, ?_⟩
    · intro _ _ _ _ _
      simp
    · simp [tsub_eq_zero_of_le (le_of_not_gt hε)]

end MathlibExt.Dynamics.OrnsteinWeissWanted.Dynamics
