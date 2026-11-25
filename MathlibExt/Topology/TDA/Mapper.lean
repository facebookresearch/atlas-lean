/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.SingleLinkage

/-!
# Mapper

The Mapper construction of G. Singh, F. Mémoli and G. Carlsson (2007), as described in
G. Carlsson, *Topology and data*, Bull. AMS 46 (2009), §3.2, steps (1)–(5): given a point cloud
`X` with a dissimilarity `d`, a filter (reference map) `f : X → Z` and a covering
`U : ι → Set Z` of the reference space, cluster each preimage `f⁻¹(U α)` by single linkage at
scale `ε`, and take the nerve of the resulting covering of `X`, whose vertices are the pairs
`(α, c)` with `c` a cluster of `f⁻¹(U α)`.

* `slClusters d ε A`: the single-linkage clusters at scale `ε` of a subset `A`, with chains
  required to stay inside `A`.
* `mapper d ε f U`: the Mapper complex.
* `mapper_card_le`: if every family of more than `n + 1` distinct cover elements has empty
  intersection (covering dimension at most `n`), every simplex of the Mapper complex has at most
  `n + 1` vertices (the remark at the end of step (5) in §3.2).
-/

@[expose] public section

namespace MathlibExt.Topology.TDA

variable {X : Type*}

/-- **Single-linkage clusters of a subset.** The clusters at scale `ε` of a subset `A ⊆ X` are
the classes of `ε`-equivalence for the dissimilarity `d` restricted to `A`, viewed as subsets of
`X`: chains must stay inside `A` (Carlsson, *Topology and data*, Bull. AMS 2009, §3.2,
step (4)). -/
def slClusters (d : X → X → ℝ) (ε : ℝ) (A : Set X) : Set (Set X) :=
  {C | ∃ x : A, C = {y | ∃ hy : y ∈ A, SLEquiv (fun a b : A => d a b) ε x ⟨y, hy⟩}}

theorem subset_of_mem_slClusters {d : X → X → ℝ} {ε : ℝ} {A C : Set X}
    (hC : C ∈ slClusters d ε A) : C ⊆ A := by
  obtain ⟨x, rfl⟩ := hC
  exact fun _ ⟨hy, _⟩ => hy

/-- **Clusters of a subset are disjoint or equal.** Two single-linkage clusters of the same
subset that share a point are equal, since clusters are equivalence classes; so the clusters of
`A` partition `A` (Carlsson, *Topology and data*, Bull. AMS 2009, §3.2: single linkage produces
a partition of the point cloud). -/
theorem eq_of_mem_slClusters {d : X → X → ℝ} {ε : ℝ} {A C C' : Set X}
    (hC : C ∈ slClusters d ε A) (hC' : C' ∈ slClusters d ε A) {x : X} (hx : x ∈ C)
    (hx' : x ∈ C') : C = C' := by
  obtain ⟨c, rfl⟩ := hC
  obtain ⟨c', rfl⟩ := hC'
  obtain ⟨hxA, hcx⟩ := hx
  obtain ⟨_, hcx₂⟩ := hx'
  have e := SLEquiv.equivalence (fun a b : A => d a b) ε
  have hcc₂ : SLEquiv (fun a b : A => d a b) ε c c' := e.trans hcx (e.symm hcx₂)
  ext y
  exact ⟨fun ⟨hy, h⟩ => ⟨hy, e.trans (e.symm hcc₂) h⟩, fun ⟨hy, h⟩ => ⟨hy, e.trans hcc₂ h⟩⟩

/-- **The clusters of a subset cover it.** Every point of `A` lies in a single-linkage cluster
of `A`, so the clusters of the preimages `f⁻¹(U α)` cover `X` when the `U α` cover the image of
`f` (Carlsson, *Topology and data*, Bull. AMS 2009, §3.2, step (4): the clusters form a covering
of `X`). -/
theorem exists_mem_slClusters {d : X → X → ℝ} {ε : ℝ} {A : Set X} {x : X} (hx : x ∈ A) :
    ∃ C ∈ slClusters d ε A, x ∈ C :=
  ⟨_, ⟨⟨x, hx⟩, rfl⟩, hx, (SLEquiv.equivalence _ ε).refl _⟩

/-- **Mapper complex.** For a dissimilarity `d` on `X`, a scale `ε`, a filter `f : X → Z` and a
family `U : ι → Set Z` (a covering of the reference space), the Mapper complex is the nerve of the
family of single-linkage clusters `c` of the preimages `f⁻¹(U α)`, indexed by the pairs
`(α, c)`: a finite set of such pairs spans a simplex when the clusters have a point in common
(Carlsson, *Topology and data*, Bull. AMS 2009, §3.2, steps (1)–(5), with single-linkage
clustering in step (4); G. Singh, F. Mémoli and G. Carlsson, *Topological methods for the
analysis of high dimensional data sets and 3D object recognition*, SPBG 2007). -/
def mapper {Z ι : Type*} (d : X → X → ℝ) (ε : ℝ) (f : X → Z) (U : ι → Set Z) :
    PreAbstractSimplicialComplex {p : ι × Set X // p.2 ∈ slClusters d ε (f ⁻¹' U p.1)} :=
  nerve fun p => p.1.2

/-- **Dimension of the Mapper complex.** If the covering has dimension at most `n`, i.e. any
finite set of indices whose sets `U i` have a common point has at most `n + 1` elements, then
every simplex of the Mapper complex has at most `n + 1` vertices (Carlsson, *Topology and data*,
Bull. AMS 2009, §3.2, the remark after step (5)). Clusters of the same preimage that share a
point coincide, so the vertices of a simplex lie over distinct cover elements. -/
theorem mapper_card_le {Z ι : Type*} {d : X → X → ℝ} {ε : ℝ} {f : X → Z} {U : ι → Set Z}
    {n : ℕ} (hdim : ∀ s : Finset ι, (∃ z, ∀ i ∈ s, z ∈ U i) → s.card ≤ n + 1)
    {σ} (hσ : σ ∈ mapper d ε f U) : σ.card ≤ n + 1 := by
  classical
  obtain ⟨-, x, hx⟩ := hσ
  have hinj : Set.InjOn (fun p : {p : ι × Set X // p.2 ∈ slClusters d ε (f ⁻¹' U p.1)} => p.1.1)
      σ := by
    intro p hp q hq hpq
    have hq' : q.1.2 ∈ slClusters d ε (f ⁻¹' U p.1.1) := by
      simp only at hpq
      rw [hpq]
      exact q.2
    have h2 : p.1.2 = q.1.2 := eq_of_mem_slClusters p.2 hq' (hx p hp) (hx q hq)
    exact Subtype.ext (Prod.ext hpq h2)
  rw [← Finset.card_image_of_injOn hinj]
  refine hdim _ ⟨f x, fun i hi => ?_⟩
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
  exact subset_of_mem_slClusters p.2 (hx p hp)

end MathlibExt.Topology.TDA
