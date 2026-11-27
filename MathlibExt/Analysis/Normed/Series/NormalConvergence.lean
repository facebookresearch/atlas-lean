/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Normal convergence of series of functions

This module defines normal convergence of a series of functions `f : ℕ → X → E`
with values in a seminormed additive commutative group, on a set `S : Set X`,
via the extended-nonnegative-real supremum norm, together with the local version
and the basic API: behaviour on the empty set and for the zero series, and
monotonicity under shrinking the domain, both globally and locally.

The supremum is taken in `ℝ≥0∞`, so unbounded families still have a well-defined
supremum; finiteness of the `ℝ≥0∞` tsum is the convergence condition (`Summable`
is not suitable as the primary predicate for `ℝ≥0∞`, where an infinite sum may
legitimately converge to `∞`).

The declarations live at the root level with the function family first and the
set last, mirroring nearby Mathlib function-series APIs such as
`TendstoUniformlyOn` and `TendstoLocallyUniformlyOn`.
-/

@[expose] public section

open Topology
open scoped ENNReal

variable {X E : Type*} [SeminormedAddCommGroup E]

/-- **Extended supremum norm on a set.** Let $X$ be a type and $E$ a seminormed additive
commutative group. For a function $g : X \to E$ and a set $S \subseteq X$, the supremum norm of
$g$ on $S$ is $\sup_{x \in S} \|g(x)\|$, taken in the extended nonnegative reals $[0, \infty]$;
in particular it is $0$ when $S$ is empty and $\infty$ when $\|g\|$ is unbounded on $S$. -/
noncomputable def supNormOn (g : X → E) (S : Set X) : ℝ≥0∞ :=
  ⨆ x : S, ENNReal.ofReal ‖g x‖

/-- Normal convergence of the function series `f` on `S`: the sup-norm series
is finite in `ℝ≥0∞`. -/
def ConvergesNormallyOn (f : ℕ → X → E) (S : Set X) : Prop :=
  ∑' n, supNormOn (f n) S ≠ ∞

/-- **Supremum norm over the empty set.** For every function $g \colon X \to E$ into a seminormed
additive commutative group $E$, the supremum norm of $g$ on the empty set, valued in
$[0, \infty]$, is $0$. -/
@[simp]
theorem supNormOn_empty (g : X → E) : supNormOn g ∅ = 0 := by
  unfold supNormOn
  rw [iSup_of_empty]
  rfl

/-- **Supremum norm of the zero function.** For every set $S \subseteq X$, the supremum norm on
$S$ of the zero function from $X$ to a seminormed additive commutative group $E$ is $0$. -/
@[simp]
theorem supNormOn_zero (S : Set X) : supNormOn (0 : X → E) S = 0 := by
  simp [supNormOn]

/-- **Monotonicity of the supremum norm in the domain.** If $T \subseteq S \subseteq X$, then for
every function $g \colon X \to E$ into a seminormed additive commutative group $E$, the supremum
norm of $g$ on $T$ is at most the supremum norm of $g$ on $S$. -/
theorem supNormOn_mono {S T : Set X} (h : T ⊆ S) (g : X → E) :
    supNormOn g T ≤ supNormOn g S := by
  unfold supNormOn
  apply iSup_mono'
  intro x
  exact ⟨⟨x.1, h x.2⟩, le_rfl⟩

/-- **Normal convergence on the empty set.** Every series of functions $f_n \colon X \to E$
($n \in \mathbb{N}$) with values in a seminormed additive commutative group $E$ converges
normally on the empty set. -/
@[simp]
theorem convergesNormallyOn_empty (f : ℕ → X → E) : ConvergesNormallyOn f ∅ := by
  simp [ConvergesNormallyOn, supNormOn_empty]

/-- **Normal convergence of the zero series.** For every set $S \subseteq X$ and every seminormed
additive commutative group $E$, the series of functions $X \to E$ whose terms are all zero
converges normally on $S$. -/
@[simp]
theorem convergesNormallyOn_zero (S : Set X) :
    ConvergesNormallyOn (0 : ℕ → X → E) S := by
  simp [ConvergesNormallyOn, supNormOn_zero]

/-- **Normal convergence passes to subsets.** Let $f_n \colon X \to E$ ($n \in \mathbb{N}$) be
functions into a seminormed additive commutative group $E$ and let $T \subseteq S \subseteq X$.
If the series $\sum_n f_n$ converges normally on $S$, then it converges normally on $T$. -/
theorem ConvergesNormallyOn.mono {f : ℕ → X → E} {S T : Set X}
    (h : ConvergesNormallyOn f S) (hTS : T ⊆ S) : ConvergesNormallyOn f T := by
  unfold ConvergesNormallyOn at h ⊢
  exact ne_top_of_le_ne_top h (ENNReal.tsum_le_tsum fun n => supNormOn_mono hTS _)

variable [TopologicalSpace X]

/-- Local normal convergence of the function series `f` on `S`: every `x ∈ S`
has a neighbourhood whose intersection with `S` carries normal convergence. -/
def ConvergesLocallyNormallyOn (f : ℕ → X → E) (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ U ∈ 𝓝 x, ConvergesNormallyOn f (U ∩ S)

/-- **Local normal convergence gives a neighbourhood of each point of the set.** Let $X$ be a
topological space, $E$ a seminormed additive commutative group, $f_n \colon X \to E$
($n \in \mathbb{N}$) functions and $S \subseteq X$. If the series $\sum_n f_n$ converges locally
normally on $S$, then every $x \in S$ has a neighbourhood $U$ such that the series converges
normally on $U \cap S$. -/
theorem ConvergesLocallyNormallyOn.exists_nhds_inter {f : ℕ → X → E} {S : Set X}
    {x : X} (h : ConvergesLocallyNormallyOn f S) (hx : x ∈ S) :
    ∃ U ∈ 𝓝 x, ConvergesNormallyOn f (U ∩ S) :=
  h x hx

/-- **Local normal convergence on the empty set.** Let $X$ be a topological space. Every series
of functions $f_n \colon X \to E$ ($n \in \mathbb{N}$) with values in a seminormed additive
commutative group $E$ converges locally normally on the empty set. -/
@[simp]
theorem convergesLocallyNormallyOn_empty (f : ℕ → X → E) :
    ConvergesLocallyNormallyOn f ∅ :=
  fun x hx => absurd hx (Set.notMem_empty x)

/-- **Local normal convergence of the zero series.** Let $X$ be a topological space and $E$ a
seminormed additive commutative group. For every set $S \subseteq X$, the series of functions
$X \to E$ whose terms are all zero converges locally normally on $S$. -/
@[simp]
theorem convergesLocallyNormallyOn_zero (S : Set X) :
    ConvergesLocallyNormallyOn (0 : ℕ → X → E) S := by
  intro x _
  exact ⟨Set.univ, Filter.univ_mem, by simp⟩

/-- **Local normal convergence passes to subsets.** Let $X$ be a topological space, let
$f_n \colon X \to E$ ($n \in \mathbb{N}$) be functions into a seminormed additive commutative
group $E$ and let $T \subseteq S \subseteq X$. If the series $\sum_n f_n$ converges locally
normally on $S$, then it converges locally normally on $T$. -/
theorem ConvergesLocallyNormallyOn.mono {f : ℕ → X → E} {S T : Set X}
    (h : ConvergesLocallyNormallyOn f S) (hTS : T ⊆ S) :
    ConvergesLocallyNormallyOn f T := by
  intro x hx
  obtain ⟨U, hU, hconv⟩ := h x (hTS hx)
  exact ⟨U, hU, hconv.mono (Set.inter_subset_inter (fun x hx => hx) hTS)⟩
