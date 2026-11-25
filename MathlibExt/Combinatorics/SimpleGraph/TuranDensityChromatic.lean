/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.TuranDensityComplete
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import MathlibExt.Combinatorics.SimpleGraph.ErdosStoneEdges
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Turán density of a general graph (Erdős–Stone–Simonovits)

`π(H) = 1 - 1/(χ(H) - 1)` for every finite graph `H` with an edge.

* Lower bound: the Turán graph `T(n, r)` is `r`-colourable, so it contains no graph of chromatic
  number larger than `r`. Hence `ex(n, H) ≥ ex(n, K_{r+1}) = t(n, r)` for every graph `H` that is
  not `r`-colourable, and `π(H) ≥ π(K_{r+1}) = 1 - 1/r`.
* Upper bound: an `(r + 1)`-colourable graph on `t` vertices lies in `K_{r+1}(t)`, whose density is
  at most `1 - 1/r` by the edge form of the Erdős–Stone theorem
  (`MathlibExt.Combinatorics.SimpleGraph.ErdosStoneEdges`).

Reference: *Extremal Combinatorics* lecture notes (extremalcombinatorics.com), Example 3.3.1 and
Theorem 3.3.10.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.TuranDensityChromatic

open Filter Topology Finset _root_.SimpleGraph

/-- **Turán graphs are `r`-colourable.** Colouring the vertex `v` of `T(n, r)` by `v mod r` is a
proper colouring with `r` colours (P. Turán, 1941; the parts of `T(n, r)` are its colour
classes). -/
theorem turanGraph_colorable (n : ℕ) {r : ℕ} (hr : 0 < r) : (turanGraph n r).Colorable r :=
  ⟨Coloring.mk (fun v => (⟨v.1 % r, Nat.mod_lt _ hr⟩ : Fin r)) fun {v w} hvw h =>
    hvw (by simpa using congrArg Fin.val h)⟩

/-- **Extremal numbers dominate those of cliques.** If `H` is not `r`-colourable (`r ≥ 1`), the
Turán graph `T(n, r)` is `H`-free, so `ex(n, K_{r+1}) ≤ ex(n, H)` for every `n` (*Extremal
Combinatorics* lecture notes, extremalcombinatorics.com, Example 3.3.1). -/
theorem extremalNumber_top_le {W : Type*} (H : _root_.SimpleGraph W) {r : ℕ} (hr : 1 ≤ r)
    (hH : ¬ H.Colorable r) (n : ℕ) :
    extremalNumber n (⊤ : _root_.SimpleGraph (Fin (r + 1))) ≤ extremalNumber n H := by
  classical
  have : Nontrivial (Fin (r + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [extremalNumber_top, Fintype.card_fin, Nat.add_sub_cancel]
  have hfree : H.Free (turanGraph n r) := by
    rintro ⟨f⟩
    exact hH ((turanGraph_colorable n hr).of_hom f.toHom)
  simpa using card_edgeFinset_le_extremalNumber hfree

/-- **Lower bound on the Turán density.** If `H` is not `r`-colourable (`r ≥ 1`), then
`π(H) ≥ 1 - 1/r`; in particular `π(H) ≥ 1 - 1/(χ(H) - 1)` (*Extremal Combinatorics* lecture
notes, extremalcombinatorics.com, Example 3.3.1, the lower-bound half of Theorem 3.3.10). -/
theorem one_sub_inv_le_turanDensity {W : Type*} (H : _root_.SimpleGraph W) {r : ℕ} (hr : 1 ≤ r)
    (hH : ¬ H.Colorable r) : 1 - 1 / (r : ℝ) ≤ turanDensity H := by
  rw [← TuranDensityComplete.turanDensity_completeGraph hr]
  refine le_of_tendsto_of_tendsto' (tendsto_turanDensity _) (tendsto_turanDensity H) fun n => ?_
  gcongr
  exact_mod_cast extremalNumber_top_le H hr hH n

/-- **Lower bound on the Turán density, chromatic form.** If `χ(H) = r + 1` with `r ≥ 1`, then
`π(H) ≥ 1 - 1/r` (*Extremal Combinatorics* lecture notes, extremalcombinatorics.com,
Example 3.3.1). -/
theorem one_sub_inv_le_turanDensity_of_chromaticNumber {W : Type*} (H : _root_.SimpleGraph W)
    {r : ℕ} (hr : 1 ≤ r) (hχ : H.chromaticNumber = r + 1) : 1 - 1 / (r : ℝ) ≤ turanDensity H := by
  refine one_sub_inv_le_turanDensity H hr fun hc => ?_
  have := hc.chromaticNumber_le
  rw [hχ] at this
  exact absurd this (by norm_cast; omega)

/-- **Turán density of complete multipartite graphs.** For `r ≥ 1` and every `t`, the complete
`(r + 1)`-partite graph `K_{r+1}(t)` has Turán density at most `1 - 1/r`: by the Erdős–Stone
theorem, for every `δ > 0` a graph on `n` vertices with `(1 - 1/r + δ) n²/2` edges contains it once
`n` is large (*Extremal Combinatorics* lecture notes, extremalcombinatorics.com, proof of
Theorem 3.3.10). -/
theorem turanDensity_completeEquipartiteGraph_le {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    turanDensity (completeEquipartiteGraph (r + 1) t) ≤ 1 - 1 / (r : ℝ) := by
  classical
  set K := completeEquipartiteGraph (r + 1) t
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := half_pos hε
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hc0 : 0 ≤ 1 - 1 / (r : ℝ) + δ := by
    have : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hr'
    linarith
  have hES := ErdosStoneEdges.eventually_completeEquipartiteGraph_isContained_of_card_edgeFinset
    hr t hδ0
  have hle : ∀ᶠ n : ℕ in atTop, (extremalNumber n K / n.choose 2 : ℝ) ≤
      (1 - 1 / (r : ℝ) + δ) * ((n : ℝ) / ((n : ℝ) + (-1))) := by
    filter_upwards [hES, eventually_ge_atTop 2] with n hn hn2
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hX : (extremalNumber n K : ℝ) ≤ (1 - 1 / (r : ℝ) + δ) * n ^ 2 / 2 := by
      have h0 : (0 : ℝ) ≤ (1 - 1 / (r : ℝ) + δ) * n ^ 2 / 2 := by positivity
      have := (extremalNumber_le_iff_of_nonneg (V := Fin n) K h0).2 fun G _ hfree => by
        by_contra hlt
        push Not at hlt
        exact hfree (hn hlt.le)
      simpa using this
    rw [Nat.cast_choose_two, div_le_iff₀ (by nlinarith)]
    calc (extremalNumber n K : ℝ) ≤ (1 - 1 / (r : ℝ) + δ) * n ^ 2 / 2 := hX
      _ = (1 - 1 / (r : ℝ) + δ) * ((n : ℝ) / ((n : ℝ) + (-1))) * ((n : ℝ) * (n - 1) / 2) := by
          have : (n : ℝ) + -1 ≠ 0 := by linarith
          field_simp
          ring
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / (r : ℝ) + δ) * ((n : ℝ) / ((n : ℝ) + (-1))))
      atTop (𝓝 (1 - 1 / (r : ℝ) + δ)) := by
    simpa using (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (-1)).const_mul (1 - 1 / (r : ℝ) + δ)
  have := le_of_tendsto_of_tendsto (tendsto_turanDensity K) hlim hle
  linarith

/-- **Turán density of a general graph (Erdős–Stone–Simonovits).** A finite graph `H` of
chromatic number `r + 1 ≥ 2` (equivalently, `H` has an edge and `χ(H) = r + 1`) has Turán density
`π(H) = 1 - 1/r`, that is, `ex(n, H) = (1 - 1/r + o(1)) C(n, 2)` (*Extremal Combinatorics* lecture
notes, extremalcombinatorics.com, Theorem 3.3.10, stated there as `π(H) = (χ(H) - 2)/(χ(H) - 1)`
for every graph with at least one edge). The lower bound is
`one_sub_inv_le_turanDensity_of_chromaticNumber`; the upper bound comes from
`turanDensity_completeEquipartiteGraph_le`, since an `(r + 1)`-colourable graph on `t` vertices is
contained in `K_{r+1}(t)`. -/
theorem turanDensity_eq_one_sub_inv_of_chromaticNumber {W : Type*} [Finite W]
    (H : _root_.SimpleGraph W) {r : ℕ} (hr : 1 ≤ r) (hχ : H.chromaticNumber = r + 1) :
    turanDensity H = 1 - 1 / r := by
  classical
  have : Fintype W := Fintype.ofFinite W
  refine le_antisymm ?_ (one_sub_inv_le_turanDensity_of_chromaticNumber H hr hχ)
  have hc : H.Colorable (r + 1) := by
    rw [← chromaticNumber_le_iff_colorable, hχ]; rfl
  have hK : H ⊑ completeEquipartiteGraph (r + 1) (Fintype.card W) :=
    isContained_completeEquipartiteGraph_of_colorable hc.some _ fun c =>
      Fintype.card_le_of_embedding (Function.Embedding.subtype _)
  refine le_trans ?_ (turanDensity_completeEquipartiteGraph_le hr (Fintype.card W))
  refine le_of_tendsto_of_tendsto' (tendsto_turanDensity H) (tendsto_turanDensity _) fun n => ?_
  gcongr
  exact_mod_cast hK.extremalNumber_le

end MathlibExt.Combinatorics.SimpleGraph.TuranDensityChromatic
