/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Sequences

/-!
# Isometric self-embeddings of compact sets

A distance-preserving map that sends a compact set into itself maps it onto itself.
-/

@[expose] public section

namespace MathlibExt.Geometry.ScottishBook3Wanted

universe u

/-- **An isometry maps an invariant compact set onto itself.** If $K$ is compact in a metric
space and an isometry $f$ sends $K$ into itself, then $f(K) = K$.

Source: The orbit argument for the Scottish Book problem “No compact set is congruent to a
proper subset of itself”.
-/
theorem image_eq_of_isometry_mapsTo {α : Type u} [MetricSpace α] {K : Set α} {f : α → α}
    (hK : IsCompact K) (hIso : Isometry f) (hMaps : Set.MapsTo f K K) : f '' K = K := by
  have hIter (n : ℕ) : Isometry f^[n] := by
    induction n with
    | zero => exact isometry_id
    | succ n ih => exact ih.comp hIso
  refine Set.Subset.antisymm hMaps.image_subset ?_
  intro x hx
  obtain ⟨_, _, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun n => hMaps.iterate n hx)
  apply (Metric.mem_of_closed' (hK.image hIso.continuous).isClosed).mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
  have hclose : dist (f^[φ N] x) (f^[φ (N + 1)] x) < ε :=
    hN N le_rfl (N + 1) (Nat.le_succ N)
  -- Cancel the common iterates. The positive gap gives a point of the image close to x.
  obtain ⟨k, hgap⟩ := Nat.exists_eq_add_of_lt (hφ (Nat.lt_succ_self N))
  refine ⟨f (f^[k] x), ⟨_, hMaps.iterate k hx, rfl⟩, ?_⟩
  rwa [hgap, Nat.add_assoc, Function.iterate_add_apply, (hIter (φ N)).dist_eq,
    Function.iterate_succ_apply'] at hclose

/--
**No compact set is congruent to a proper subset of itself.** Let $K$ be a compact subset of
a metric space $X$. Then there is no map $f : X \to X$ with $d(f(x), f(y)) = d(x, y)$ for all
$x, y \in X$ such that $f(K) \subseteq K$ and $f(K) \neq K$.

The underlying fact is that an isometric embedding of a compact metric space into itself is
surjective.

Source: S. Banach and S. Ulam, Problem 3 of the Scottish Book,
stated and proved in the Scottish Book typescript.
-/
theorem noCompactSetCongruentToProperSubset :
    ∀ (α : Type) [MetricSpace α] {K : Set α}, IsCompact K →
      ¬ ∃ (f : α → α), (∀ x y, dist (f x) (f y) = dist x y) ∧ f '' K ⊆ K ∧ f '' K ≠ K := by
  intro α _ K hK ⟨f, hf, hsub, hne⟩
  exact hne (image_eq_of_isometry_mapsTo hK (Isometry.of_dist_eq hf)
    (Set.mapsTo_iff_image_subset.mpr hsub))

end MathlibExt.Geometry.ScottishBook3Wanted
