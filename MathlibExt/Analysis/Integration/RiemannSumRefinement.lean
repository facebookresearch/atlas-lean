/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannPartition
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Riemann sums under refinement

If the point set of `T` is included in that of `T'`, then the Riemann sums of `f` with
respect to `T` and `T'` differ by at most the oscillation of `f` at the
mesh scale of `T` times the length `b - a` of the interval. The book states
this (Theorem II) with the oscillation measured by the modulus of
continuity `w_f(‖T‖)` and `f` continuous on `[a, b]`; here it is stated
with an explicit oscillation bound `ω`, which is both more general (no
continuity is needed, only the bound at the mesh scale) and independent of
the modulus-of-continuity API. The book's Theorem III, the bound for two
arbitrary tagged partitions in terms of a common refinement, follows by
the triangle inequality.

## Main definitions

* `TaggedPartition.IsTaggedRefinement`: `T'` is a tagged refinement of `T`
  when every subinterval of `T'` is contained in some subinterval of `T`
  (witnessed by `assign`), and the subintervals of `T'` assigned to each
  `T`-subinterval telescope to its length.

## Main results

* `telescope_sum_of_embedding`: the fine subinterval lengths in each fiber
  telescope to the corresponding coarse subinterval length.
* `TaggedPartition.nonempty_isTaggedRefinement_of_isRefinement`: construct
  tagged-refinement data from point-set inclusion.
* `riemannSum_eq_fiber`: the Riemann sum over `T` rewritten as a sum over
  the refinement `T'`, grouped by the parent subinterval.
* `riemannSum_sub_le_of_isRefinement`: Theorem II in oscillation form.
* `riemannSum_sub_le_of_isTaggedRefinement`: the estimate given explicit
  tagged-refinement data.
* `riemannSum_sub_le_of_commonRefinement`: Theorem III in oscillation form,
  given a common tagged refinement.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorems II and III, "The
Riemann Integral section", and
`v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean`
(`telescope_sum_of_embedding`, `TaggedPartition.IsTaggedRefinement`, `riemannSum_eq_fiber`,
`riemannSum_sub_le_modulusOfContinuity_mul`,
`riemannSum_sub_le_modulusOfContinuity_add_mul_of_commonRefinement`).
In v1 the oscillation is `modulusOfContinuity f a b T.toPartition.mesh`
and `f` is assumed continuous on `[a, b]`; here the bound is an explicit
hypothesis `hω`, so continuity is not needed.
The point-set refinement hypothesis is `Partition.IsRefinement`; the
assignment and telescope data used by the estimate are constructed from it.
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration

variable {a b : ℝ}

/-- **Telescoping over the fibers of an assignment.** Let $y_0, \dots, y_N$ be real numbers,
let $\varphi : \{0, \dots, m\} \to \{0, \dots, N\}$ be strictly increasing, and let
$\sigma : \{0, \dots, N-1\} \to \{0, \dots, m-1\}$ satisfy
$\varphi(\sigma(j)) \le j < \varphi(\sigma(j) + 1)$ for every $j < N$. Then for every $k < m$,

$$\sum_{j < N,\ \sigma(j) = k} (y_{j+1} - y_j) = y_{\varphi(k+1)} - y_{\varphi(k)}.$$ -/
lemma telescope_sum_of_embedding {n'' m : ℕ} (pts : Fin (n'' + 1) → ℝ)
    (φ : Fin (m + 1) → Fin (n'' + 1)) (hφ_strict : StrictMono φ)
    (assign : Fin n'' → Fin m)
    (hassign_spec : ∀ j : Fin n'', (φ (assign j).castSucc).val ≤ j.val ∧
      j.val < (φ (assign j).succ).val)
    (k : Fin m) :
    ∑ j ∈ Finset.univ.filter (fun j => assign j = k),
      (pts j.succ - pts j.castSucc) = pts (φ k.succ) - pts (φ k.castSucc) := by
  have hfilter_eq : Finset.univ.filter (fun j : Fin n'' => assign j = k) =
      Finset.univ.filter (fun j : Fin n'' => (φ k.castSucc).val ≤ j.val ∧
        j.val < (φ k.succ).val) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; have := hassign_spec j; rw [h] at this; exact this
    · intro ⟨hleft, hright⟩
      by_contra hne
      have hspec := hassign_spec j
      rcases Fin.lt_or_lt_of_ne hne with h | h
      · have _h1 := hφ_strict.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have := hspec.2; omega
      · have _h1 := hφ_strict.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have := hspec.1; omega
  rw [hfilter_eq]
  set a' := (φ k.castSucc).val; set b' := (φ k.succ).val
  have hab' : a' ≤ b' := (hφ_strict Fin.castSucc_lt_succ).le
  have hb'_lt : b' < n'' + 1 := (φ k.succ).isLt
  let g : ℕ → ℝ := fun i => if h : i < n'' + 1 then pts ⟨i, h⟩ else 0
  suffices hsuff : ∀ j ∈ Finset.univ.filter (fun j : Fin n'' => a' ≤ j.val ∧ j.val < b'),
      pts j.succ - pts j.castSucc = g (j.val + 1) - g j.val by
    rw [Finset.sum_congr rfl hsuff]
    have hbij : ∑ j ∈ Finset.univ.filter (fun j : Fin n'' => a' ≤ j.val ∧ j.val < b'),
        (g (↑j + 1) - g ↑j) = ∑ i ∈ Finset.Ico a' b', (g (i + 1) - g i) :=
      Finset.sum_nbij (fun j => j.val)
        (fun j hj => Finset.mem_Ico.mpr (Finset.mem_filter.mp hj).2)
        (fun _ _ _ _ h => Fin.ext h)
        (fun i hi => ⟨⟨i, by have := (Finset.mem_Ico.mp hi).2; omega⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_Ico.mp hi⟩, rfl⟩)
        (fun _ _ => rfl)
    rw [hbij, Finset.sum_Ico_sub g hab']
    simp only [g, hb'_lt, Nat.lt_of_le_of_lt hab' hb'_lt, dite_eq_left]
    congr 1
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  simp only [g, show j.val < n'' + 1 from by omega,
    show j.val + 1 < n'' + 1 from by omega, dite_eq_left]
  congr 1

/-- **Tagged-refinement data.** Let $T$ and $T'$ be tagged partitions of $[a, b]$ with points
$a = x_0 < \dots < x_n = b$ and $a = x'_0 < \dots < x'_{n'} = b$ respectively. Tagged-refinement
data from $T$ to $T'$ consist of a map $\sigma$ assigning to each index $j < n'$ an index
$\sigma(j) < n$ such that $x_{\sigma(j)} \le x'_j$ and $x'_{j+1} \le x_{\sigma(j)+1}$ for every
$j < n'$ (so the $j$-th subinterval of $T'$ lies in the $\sigma(j)$-th subinterval of $T$), and
such that for every $k < n$ the lengths assigned to $k$ add up to its length:
$\sum_{j < n',\ \sigma(j) = k} (x'_{j+1} - x'_j) = x_{k+1} - x_k$. The tags of $T$ and $T'$
play no role.

Such data exist whenever every point of $T$ is a point of $T'$. -/
structure TaggedPartition.IsTaggedRefinement (T T' : TaggedPartition a b) where
  assign : Fin T'.n → Fin T.n
  contained_left : ∀ j : Fin T'.n, T.points (assign j).castSucc ≤ T'.points j.castSucc
  contained_right : ∀ j : Fin T'.n, T'.points j.succ ≤ T.points (assign j).succ
  telescope : ∀ k : Fin T.n,
    ∑ j ∈ Finset.univ.filter (fun j => assign j = k),
      (T'.points j.succ - T'.points j.castSucc) = T.points k.succ - T.points k.castSucc

private lemma exists_endpointEmbedding_of_isRefinement (P Q : Partition a b)
    (href : Q.IsRefinement P) :
    ∃ φ : Fin (P.n + 1) → Fin (Q.n + 1), StrictMono φ ∧
      (∀ i, Q.points (φ i) = P.points i) ∧ φ 0 = 0 ∧
      φ (Fin.last P.n) = Fin.last Q.n := by
  classical
  change Set.range P.points ⊆ Set.range Q.points at href
  have hex : ∀ i : Fin (P.n + 1), ∃ j : Fin (Q.n + 1),
      Q.points j = P.points i := by
    intro i
    exact href ⟨i, rfl⟩
  choose φ hφ using hex
  refine ⟨φ, ?_, hφ, ?_, ?_⟩
  · intro i j hij
    apply Q.ordered.lt_iff_lt.mp
    rw [hφ i, hφ j]
    exact P.ordered hij
  · apply Q.ordered.injective
    rw [hφ 0, P.first, Q.first]
  · apply Q.ordered.injective
    rw [hφ (Fin.last P.n), P.last, Q.last]

private lemma exists_parent_interval {n m : ℕ}
    (φ : Fin (m + 1) → Fin (n + 1))
    (hφ_zero : (φ 0).val = 0) (hφ_last : (φ (Fin.last m)).val = n)
    (j : Fin n) :
    ∃ k : Fin m, (φ k.castSucc).val ≤ j.val ∧ j.val < (φ k.succ).val := by
  let good := Finset.univ.filter (fun i : Fin (m + 1) => (φ i).val ≤ j.val)
  have hgood_ne : good.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  have hlast_not : Fin.last m ∉ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    omega
  let k₀ := good.max' hgood_ne
  have hk₀_mem : k₀ ∈ good := Finset.max'_mem good hgood_ne
  have hk₀_le : (φ k₀).val ≤ j.val := (Finset.mem_filter.mp hk₀_mem).2
  have hk₀_lt : k₀ < Fin.last m :=
    Fin.lt_last_iff_ne_last.mpr (fun h => hlast_not (h ▸ hk₀_mem))
  let k : Fin m := ⟨k₀.val, Fin.lt_def.mp hk₀_lt⟩
  have hcast : k.castSucc = k₀ := Fin.ext rfl
  refine ⟨k, ?_, ?_⟩
  · rw [hcast]
    exact hk₀_le
  · have hsucc_not : k.succ ∉ good := by
      intro hmem
      have hle := Finset.le_max' good k.succ hmem
      change k₀.val + 1 ≤ k₀.val at hle
      omega
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hsucc_not
    exact hsucc_not

/-- **Refinements carry tagged-refinement data.** Let $T$ and $T'$ be tagged partitions of
$[a, b]$ such that every point of $T$ is a point of $T'$. Then tagged-refinement data from $T$
to $T'$ exist: an assignment of each subinterval of $T'$ to a subinterval of $T$ that contains
it, such that for each subinterval of $T$ the lengths of the subintervals of $T'$ assigned to it
add up to its length. -/
theorem TaggedPartition.nonempty_isTaggedRefinement_of_isRefinement
    (T T' : TaggedPartition a b) (href : T'.toPartition.IsRefinement T.toPartition) :
    Nonempty (T.IsTaggedRefinement T') := by
  classical
  obtain ⟨φ, hφ_strict, hφ_spec, hφ_zero, hφ_last⟩ :=
    exists_endpointEmbedding_of_isRefinement T.toPartition T'.toPartition href
  have hex := exists_parent_interval φ (congr_arg Fin.val hφ_zero)
    (congr_arg Fin.val hφ_last)
  choose assign hleft hright using hex
  refine ⟨{
    assign := assign
    contained_left := ?_
    contained_right := ?_
    telescope := ?_
  }⟩
  · intro j
    rw [← hφ_spec (assign j).castSucc]
    exact T'.ordered.monotone (hleft j)
  · intro j
    rw [← hφ_spec (assign j).succ]
    exact T'.ordered.monotone (Nat.lt_iff_add_one_le.mp (hright j))
  · intro k
    rw [← hφ_spec k.succ, ← hφ_spec k.castSucc]
    exact telescope_sum_of_embedding T'.points φ hφ_strict assign
      (fun j => ⟨hleft j, hright j⟩) k

/-- **Riemann sum regrouped over a refinement.** Let $f : \mathbb{R} \to \mathbb{R}$, let $T$ be
a tagged partition of $[a, b]$ with points $x_0 < \dots < x_n$ and tags
$\xi_0, \dots, \xi_{n-1}$, and let $T'$ be a tagged partition of $[a, b]$ with points
$x'_0 < \dots < x'_{n'}$, together with tagged-refinement data from $T$ to $T'$ assigning to
each $j < n'$ an index $\sigma(j) < n$. Then the Riemann sum $S_f(T)$ of $f$ over $T$ satisfies

$$S_f(T) = \sum_{j=0}^{n'-1} f(\xi_{\sigma(j)}) \, (x'_{j+1} - x'_j).$$ -/
lemma riemannSum_eq_fiber (f : ℝ → ℝ) (T T' : TaggedPartition a b)
    (href : T.IsTaggedRefinement T') :
    riemannSum f T = ∑ j : Fin T'.n,
      f (T.tags (href.assign j)) * (T'.points j.succ - T'.points j.castSucc) := by
  unfold riemannSum
  conv_lhs => arg 2; ext k; rw [← href.telescope k, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := href.assign) (fun i _ => Finset.mem_univ _)]
  congr 1; ext k
  apply Finset.sum_congr rfl
  intro j hj; simp only [Finset.mem_filter] at hj; rw [← hj.2]

/-- **Riemann sums under refinement, given refinement data.** Let $f : \mathbb{R} \to \mathbb{R}$,
let $T$ and $T'$ be tagged partitions of $[a, b]$ together with tagged-refinement data from $T$
to $T'$, and let $\omega \in \mathbb{R}$ satisfy $|f(x) - f(y)| \le \omega$ for all
$x, y \in [a, b]$ with $|x - y| \le \|T\|$, where $\|T\|$ is the mesh of $T$. Writing $S_f(T)$
for the Riemann sum of $f$ over $T$, we have $|S_f(T) - S_f(T')| \le \omega (b - a)$. -/
theorem riemannSum_sub_le_of_isTaggedRefinement
    (f : ℝ → ℝ) (T T' : TaggedPartition a b) {ω : ℝ}
    (hω : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ T.toPartition.mesh → |f x - f y| ≤ ω)
    (href : T.IsTaggedRefinement T') :
    |riemannSum f T - riemannSum f T'| ≤ ω * (b - a) := by
  rw [riemannSum_eq_fiber f T T' href]
  have hdiff : (∑ j : Fin T'.n,
      f (T.tags (href.assign j)) * (T'.points j.succ - T'.points j.castSucc)) -
    riemannSum f T' =
    ∑ j : Fin T'.n, (f (T.tags (href.assign j)) - f (T'.tags j)) *
      (T'.points j.succ - T'.points j.castSucc) := by
    unfold riemannSum
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  rw [hdiff]
  calc |∑ j : Fin T'.n, (f (T.tags (href.assign j)) - f (T'.tags j)) *
        (T'.points j.succ - T'.points j.castSucc)|
      ≤ ∑ j : Fin T'.n, |(f (T.tags (href.assign j)) - f (T'.tags j)) *
        (T'.points j.succ - T'.points j.castSucc)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin T'.n, |f (T.tags (href.assign j)) - f (T'.tags j)| *
          (T'.points j.succ - T'.points j.castSucc) := by
            congr 1; ext j
            rw [abs_mul, abs_of_nonneg (T'.toPartition.succ_sub_castSucc_nonneg j)]
    _ ≤ ∑ j : Fin T'.n, ω *
          (T'.points j.succ - T'.points j.castSucc) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_right _
              (T'.toPartition.succ_sub_castSucc_nonneg j)
            refine hω _ (T.tag_mem_Icc (href.assign j)) _
              (T'.tag_mem_Icc j) ?_
            set k := href.assign j
            have htk := T.tag_mem k
            have htj := T'.tag_mem j
            have hleft := href.contained_left j
            have hright := href.contained_right j
            have habs : |T.tags k - T'.tags j| ≤
                T.points k.succ - T.points k.castSucc := by
              rw [abs_le]
              exact ⟨by linarith [htk.1, htj.2, hright],
                     by linarith [htj.1, hleft, htk.2]⟩
            exact habs.trans (T.toPartition.le_mesh k)
    _ = ω * (b - a) := by
            rw [← Finset.mul_sum, T'.toPartition.sum_sub_eq]

/-- **Riemann sums under refinement.** Let $f : \mathbb{R} \to \mathbb{R}$, let $T$ and $T'$ be
tagged partitions of $[a, b]$ such that every point of $T$ is a point of $T'$, and let
$\omega \in \mathbb{R}$ satisfy $|f(x) - f(y)| \le \omega$ for all $x, y \in [a, b]$ with
$|x - y| \le \|T\|$, where $\|T\|$ is the mesh of $T$. Writing $S_f(T)$ for the Riemann sum of
$f$ over $T$, we have $|S_f(T) - S_f(T')| \le \omega (b - a)$.

This is Theorem II of the Riemann integral section in oscillation form: an explicit bound
$\omega$ replaces the modulus of continuity, so $f$ need not be continuous. -/
theorem riemannSum_sub_le_of_isRefinement
    (f : ℝ → ℝ) (T T' : TaggedPartition a b) {ω : ℝ}
    (hω : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ T.toPartition.mesh → |f x - f y| ≤ ω)
    (href : T'.toPartition.IsRefinement T.toPartition) :
    |riemannSum f T - riemannSum f T'| ≤ ω * (b - a) := by
  obtain ⟨hdata⟩ := T.nonempty_isTaggedRefinement_of_isRefinement T' href
  exact riemannSum_sub_le_of_isTaggedRefinement f T T' hω hdata

/-- **Riemann sums of two partitions with a common refinement.** Let $f : \mathbb{R} \to \mathbb{R}$
and let $T_1$, $T_2$ be tagged partitions of $[a, b]$ with meshes $\|T_1\|$ and $\|T_2\|$.
Suppose $\omega_1, \omega_2 \in \mathbb{R}$ satisfy, for $i = 1, 2$, $|f(x) - f(y)| \le \omega_i$
for all $x, y \in [a, b]$ with $|x - y| \le \|T_i\|$. Let $T''$ be a tagged partition of
$[a, b]$ together with tagged-refinement data from $T_1$ to $T''$ and from $T_2$ to $T''$.
Writing $S_f(T)$ for the Riemann sum of $f$ over $T$, we have
$|S_f(T_1) - S_f(T_2)| \le (\omega_1 + \omega_2)(b - a)$.

This is Theorem III of the Riemann integral section in oscillation form: explicit bounds
$\omega_i$ replace the modulus of continuity, so $f$ need not be continuous. -/
theorem riemannSum_sub_le_of_commonRefinement
    (f : ℝ → ℝ) (T₁ T₂ : TaggedPartition a b) {ω₁ ω₂ : ℝ}
    (hω₁ : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ T₁.toPartition.mesh → |f x - f y| ≤ ω₁)
    (hω₂ : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ T₂.toPartition.mesh → |f x - f y| ≤ ω₂)
    (T'' : TaggedPartition a b)
    (href₁ : T₁.IsTaggedRefinement T'')
    (href₂ : T₂.IsTaggedRefinement T'') :
    |riemannSum f T₁ - riemannSum f T₂| ≤ (ω₁ + ω₂) * (b - a) := by
  have h1 := riemannSum_sub_le_of_isTaggedRefinement f T₁ T'' hω₁ href₁
  have h2 := riemannSum_sub_le_of_isTaggedRefinement f T₂ T'' hω₂ href₂
  calc |riemannSum f T₁ - riemannSum f T₂|
      = |(riemannSum f T₁ - riemannSum f T'') + (riemannSum f T'' - riemannSum f T₂)| := by
          ring_nf
    _ ≤ |riemannSum f T₁ - riemannSum f T''| + |riemannSum f T'' - riemannSum f T₂| :=
          abs_add_le _ _
    _ = |riemannSum f T₁ - riemannSum f T''| + |riemannSum f T₂ - riemannSum f T''| := by
          rw [abs_sub_comm (riemannSum f T'') (riemannSum f T₂)]
    _ ≤ ω₁ * (b - a) + ω₂ * (b - a) := by
          linarith
    _ = (ω₁ + ω₂) * (b - a) := by
          ring

end MathlibExt.Analysis.Integration
