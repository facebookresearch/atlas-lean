/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.SingleLinkage
public import MathlibExt.Topology.TDA.PersistenceModule
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Zero-dimensional persistence: the cluster functor and its stability

The single-linkage clusters at all scales form an `ℝ`-persistence object in the category of sets
(G. Carlsson, *Topology and data*, Bull. AMS 46 (2009), Def. 2.9 with `C = Sets`): the functor
`r ↦ X / ∼_r`, whose structure maps send a cluster to the cluster containing it at a larger
scale. For a metric space this is `π₀` of the Vietoris–Rips filtration
(`slEquiv_dist_iff_reachable`), the set-level form of zero-dimensional persistent homology.

`clusterFunctorInterleaving`: if two dissimilarities on the same set differ by at most `η`
everywhere, their cluster functors are `η`-interleaved in the sense of Chazal, de Silva, Glisse
and Oudot (arXiv:1207.3674, §3.2). This is the zero-dimensional, same-set case of the stability of
Vietoris–Rips persistence, proved by the chain argument of Carlsson and Mémoli (JMLR 11 (2010),
Lemma 15).
-/

@[expose] public section

open CategoryTheory

universe u

namespace MathlibExt.Topology.TDA

variable {X : Type u}

/-- **The cluster functor (zero-dimensional persistence).** For a dissimilarity `d` on `X`, the
functor `ℝ ⥤ Type` sending `r` to the set of single-linkage clusters `X / ∼_r` at scale `r`, and
`r ≤ s` to the map sending each `r`-cluster to the `s`-cluster containing it: an `ℝ`-persistence
object in the category of sets (Carlsson, *Topology and data*, Bull. AMS 2009, Def. 2.9 and
§3.2, where single-linkage clusters are `π₀` of the Vietoris–Rips complex). -/
def clusterFunctor (d : X → X → ℝ) : ℝ ⥤ Type u where
  obj r := Quot (SLEquiv d r)
  map {r s} h := TypeCat.ofHom (Quot.map id fun a b (hab : SLEquiv d r a b) => hab.mono (leOfHom h))
  map_id r := by
    ext z
    induction z using Quot.ind
    rfl
  map_comp _ _ := by
    ext z
    induction z using Quot.ind
    rfl

/-- **Stability of zero-dimensional persistence.** If two dissimilarities on the same set satisfy
`|d₁ x y - d₂ x y| ≤ η` for all `x, y`, with `η ≥ 0`, then their cluster functors are
`η`-interleaved: an `r`-cluster for `d₁` lies in an `(r + η)`-cluster for `d₂` and conversely, and
the two round trips are the structure maps over `2η` (interleavings as in Chazal, de Silva, Glisse
and Oudot, arXiv:1207.3674, §3.2; the inclusions are the chain argument of Carlsson and Mémoli,
JMLR 11 (2010), Lemma 15). -/
def clusterFunctorInterleaving {d₁ d₂ : X → X → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x y, |d₁ x y - d₂ x y| ≤ η) :
    Interleaving (clusterFunctor d₁) (clusterFunctor d₂) η where
  nonneg := hη
  φ r := TypeCat.ofHom <| Quot.map id <|
    fun x y (hxy : SLEquiv d₁ r x y) => hxy.of_le_add fun a b => by
      have := h a b
      rw [abs_le] at this
      linarith
  ψ r := TypeCat.ofHom <| Quot.map id <|
    fun x y (hxy : SLEquiv d₂ r x y) => hxy.of_le_add fun a b => by
      have := h a b
      rw [abs_le] at this
      linarith
  φ_natural _ _ _ := by
    ext z
    induction z using Quot.ind
    rfl
  ψ_natural _ _ _ := by
    ext z
    induction z using Quot.ind
    rfl
  ψ_comp_φ _ := by
    ext z
    induction z using Quot.ind
    rfl
  φ_comp_ψ _ := by
    ext z
    induction z using Quot.ind
    rfl

end MathlibExt.Topology.TDA
