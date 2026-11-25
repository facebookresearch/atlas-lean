/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Algebra.Order.Group.Pointwise.Interval
public import MathlibExt.Data.Set.Interval
public import MathlibExt.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

@[expose] public section

open Filter

open scoped Topology

namespace Set

/--
**Partial density.** Let $\beta$ be a preorder in which every set $\{x \in \beta \mid x \le b\}$
is finite, let $S, A \subseteq \beta$ and $b \in \beta$, and write
$A_{<b} = \{x \in A \mid x < b\}$. The partial density of $S$ relative to $A$ at $b$ is the
proportion $\lvert S \cap A_{<b} \rvert / \lvert A_{<b} \rvert$ of elements of $A_{<b}$ that lie
in $S$, taken to be $0$ when $A_{<b}$ is empty. By default $A = \beta$.

Source: inspired by https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

theorem partialDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : S.partialDensity A b ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ inter_subset_right

/--
**Upper density.** Let $\beta$ be a preorder in which every set $\{x \in \beta \mid x \le b\}$
is finite, and let $S, A \subseteq \beta$. The upper density of $S$ relative to $A$ is the limit
superior, as $b \to \infty$ in $\beta$, of the partial densities of $S$ relative to $A$ at $b$.
By default $A = \beta$.
-/
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

/--
**Lower density.** Let $\beta$ be a preorder in which every set $\{x \in \beta \mid x \le b\}$
is finite, and let $S, A \subseteq \beta$. The lower density of $S$ relative to $A$ is the limit
inferior, as $b \to \infty$ in $\beta$, of the partial densities of $S$ relative to $A$ at $b$.
By default $A = \beta$.
-/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

theorem lowerDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : S.lowerDensity A ≤ 1 := by
  by_cases h : atTop (α := β) = ⊥
  · simp [h, Set.lowerDensity, Filter.liminf_eq]
  · have : (atTop (α := β)).NeBot := ⟨h⟩
    apply Real.sSup_le (fun x hx ↦ ?_) one_pos.le
    simpa using hx.mono fun y hy ↦ hy.trans (Set.partialDensity_le_one _ _ y)

theorem lowerDensity_nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : 0 ≤ S.lowerDensity A := by
  rw [Set.lowerDensity, Filter.liminf_eq]
  exact (em _).elim (le_csSup · <| .of_forall fun _ ↦ by positivity)
    (Real.sSup_of_not_bddAbove · |>.ge)

/--
**Density of a set.** Let $\beta$ be a preorder in which every set
$\{x \in \beta \mid x \le b\}$ is finite, let $S, A \subseteq \beta$ and $\alpha \in \mathbb{R}$,
and write $\beta_{<b} = \{x \in \beta \mid x < b\}$. The set $S$ has density $\alpha$ relative to
$A$ if the partial density
$\lvert S \cap A \cap \beta_{<b} \rvert / \lvert A \cap \beta_{<b} \rvert$, taken to be $0$ when
the denominator is $0$, tends to $\alpha$ as $b \to \infty$ in $\beta$.

By default $A = \beta$; for $\beta = \mathbb{N}$ this is the natural density of $S$.
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

/--
**Positive density.** Let $\beta$ be a preorder in which every set
$\{x \in \beta \mid x \le b\}$ is finite, and let $S, A \subseteq \beta$. The set $S$ has positive
density relative to $A$ if there is a real number $\alpha > 0$ such that $S$ has density $\alpha$
relative to $A$. By default $A = \beta$.
-/
def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

/--
**Two-sided partial density.** For a set $S$ of integers and a natural number $N$, the
two-sided partial natural density of $S$ at $N$ is $\lvert S \cap [-N, N] \rvert / (2N + 1)$,
where $[-N, N]$ is the set of integers $m$ with $-N \le m \le N$.
-/
noncomputable def intPartialDensity (S : Set ℤ) (N : ℕ) : ℝ :=
  open scoped Classical in
  (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => m ∈ S)).card : ℝ) /
    (2 * (N : ℝ) + 1)

/-- **Two-sided natural density.** A set $S$ of integers has two-sided natural density
$\alpha \in \mathbb{R}$ if $\lvert S \cap [-N, N] \rvert / (2N + 1)$ tends to $\alpha$ as the
natural number $N$ tends to infinity, where $[-N, N]$ is the set of integers $m$ with
$-N \le m \le N$. -/
def HasIntDensity (S : Set ℤ) (α : ℝ) : Prop :=
  Tendsto (fun N : ℕ => S.intPartialDensity N) atTop (𝓝 α)

@[simp]
theorem intPartialDensity_empty (N : ℕ) : intPartialDensity (∅ : Set ℤ) N = 0 := by
  simp [intPartialDensity]

namespace HasIntDensity

@[simp]
theorem empty : HasIntDensity (∅ : Set ℤ) 0 := by
  simp [HasIntDensity]

end HasIntDensity

namespace HasDensity

-- TODO(mercuris): generalise these to non-univ `A`

/-- **The whole order has density one.** Let $\beta$ be a partial order with a least element
and at least two elements, in which every closed interval $[a, b]$ is finite. Then the set of
all elements of $\beta$ has density $1$ (relative to all of $\beta$). -/
@[simp]
theorem univ {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
    (@Set.univ β).HasDensity 1 := by
  by_cases h : atTop (α := β) = ⊥
  · simp [h, HasDensity]
  · simp only [HasDensity, partialDensity, inter_self, univ_inter]
    let ⟨b, hb⟩ := Set.Iio_eventually_ncard_ne_zero β
    refine tendsto_const_nhds.congr' ?_
    exact (eventually_ge_atTop b).mono fun n hn ↦ (div_self <| mod_cast hb n hn).symm

theorem univ_nat_hasDensity_one : (@Set.univ ℕ).HasDensity 1 := univ

@[simp]
theorem empty {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] (A : Set β := Set.univ) :
    Set.HasDensity (∅ : Set β) 0 A := by
  simpa [HasDensity, partialDensity] using tendsto_const_nhds

theorem mono {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β]
    {S T : Set β} {αS αT : ℝ} [(atTop (α := β)).NeBot] (h : S ⊆ T) (hS : S.HasDensity αS)
    (hT : T.HasDensity αT) : αS ≤ αT := by
  rw [HasDensity] at hS hT
  apply le_of_tendsto_of_tendsto hS hT
  filter_upwards [eventually_ge_atTop ⊥] with b hb
  apply div_le_div_of_nonneg_right
  grw [Set.ncard_le_ncard (inter_subset_inter_left _ (inter_subset_inter_left _ h))]
  exact Nat.cast_nonneg _

theorem nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] [(atTop : Filter β).NeBot]
    {S : Set β} {α : ℝ} (h : S.HasDensity α) : 0 ≤ α :=
  le_of_tendsto_of_tendsto' empty h fun b => by simp [div_nonneg, partialDensity]

end Set.HasDensity

namespace Nat

open Set

/--
**Natural density of the even numbers.** The set of even natural numbers has natural
density $1/2$.
-/
theorem hasDensity_even : {n : ℕ | Even n}.HasDensity (1 / 2) := by
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, ncard_Iio_nat, one_div]
  have h {n : ℕ} (hn : 1 ≤ n) : (({n : ℕ | Even n} ∩ Iio n).ncard : ℝ) / n =
      if Even n then 2⁻¹ else (n + 1 : ℝ) /  n * 2⁻¹ := by
    split_ifs with h
    · rw [← image_mul_two_Iio_even h, ncard_image_of_injective _
          (mul_right_injective₀ (by simp)), Set.ncard_Iio_nat,
        cast_div_charZero (even_iff_two_dvd.mp h), cast_ofNat,
        div_div_cancel_left' <| cast_ne_zero.2 (by linarith)]
    · replace h : Even (n + 1) := by simpa [Nat.even_add', ← Nat.not_even_iff_odd]
      rw [← image_mul_two_Iio n, ncard_image_of_injective _
          (mul_right_injective₀ (by simp)), Set.ncard_Iio_nat,
        cast_div (even_iff_two_dvd.mp h) (by norm_num), cast_add]; ring
  refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (h hn).symm⟩)
    (Tendsto.if' tendsto_const_nhds ?_)
  replace h : Tendsto (fun (k : ℕ) => 1 + 1 / (k : ℝ)) atTop (𝓝 1) := by
    simpa using Tendsto.const_add (M := ℝ) _ tendsto_one_div_atTop_nhds_zero_nat
  simpa using Tendsto.mul_const _ <|
    Tendsto.congr' (eventually_atTop.2 ⟨1, fun k hk => by field_simp⟩) h

/-- **Finite sets have natural density zero.** Every finite set of natural numbers has natural
density $0$. -/
theorem hasDensity_zero_of_finite {S : Set ℕ} (h : S.Finite) : S.HasDensity 0 := by
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, ncard_Iio_nat]
  have (n : ℕ) : ((S ∩ Set.Iio n).ncard : ℝ) / n ≤ S.ncard / n := by
    by_cases h₀ : n = 0; simp [h₀]
    exact div_le_div₀ (by simp) (by simpa using Set.ncard_inter_le_ncard_left _ _ h)
      (by simpa using n.pos_of_ne_zero h₀) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat _)
    (fun _ => div_nonneg (cast_nonneg _) (cast_nonneg _)) this

/-- **Sets of nonzero natural density are infinite.** If a set $S$ of natural numbers has
natural density $\alpha$ with $\alpha \neq 0$, then $S$ is infinite. -/
theorem infinite_of_hasDensity_pos {S : Set ℕ} {α : ℝ} (h : S.HasDensity α) (hα : α ≠ 0) :
    S.Infinite :=
  mt hasDensity_zero_of_finite fun h' => hα (tendsto_nhds_unique h h')

end Nat

/-! ## Logarithmic Density -/

section LogarithmicDensity

open Finset Real

/--
**Logarithmic density.** A set $A$ of natural numbers has logarithmic density
$d \in \mathbb{R}$ if
$\frac{1}{\log n} \sum_{k \in A,\, k \le n} \frac{1}{k}$
tends to $d$ as $n \to \infty$, where $\log$ is the natural logarithm, the term $1/k$ for $k = 0$
is taken to be $0$, and the whole expression is taken to be $0$ when $\log n = 0$.

Logarithmic density is a weaker notion than natural density: if a set has natural density $d$,
then it also has logarithmic density $d$, but the converse is false.
-/
def Set.HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  open scoped Classical in
  Tendsto (fun n : ℕ => (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / .log n : ℝ)) atTop (𝓝 d)

end LogarithmicDensity
