/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
module

/-
Completed proof port; original Apache 2.0 author/license header retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialNerve/Quasicategory.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import MathlibExt.AlgebraicTopology.CategoricalSource.HornGluing
/-!
# The simplicial nerve of a locally Kan simplicial category is a quasicategory

Let `C` be a simplicial category all of whose mapping simplicial sets are Kan complexes. We show
that its simplicial (homotopy coherent) nerve `SimplicialNerve C` is a quasicategory. This is the
basic source of quasicategories from simplicial categories, for instance from simplicial categories
of Kan complexes or of fibrant-cofibrant objects of a simplicial model category.

An `m`-simplex of `SimplicialNerve C` is a simplicial functor `C[Δ^m] ⥤ C` out of the simplicial
thickening of `Fin (m + 1)`. A map `σ₀ : Λ[n + 2, i] ⟶ SimplicialNerve C` from an inner horn has
faces `σ j : C[Δ^{n+1}] ⥤ C` for `j ≠ i`, which agree on the faces of codimension two. We glue them
to a simplicial functor `C[Λ^{n+2}_i] ⥤ C` out of the rigidified horn `MathlibExt.CategoricalSource.HornThickening` by
`MathlibExt.CategoricalSource.HornThickening.exists_desc`, extend it to `C[Δ^{n+2}]` by
`MathlibExt.CategoricalSource.HornThickening.exists_extension`, and obtain a filler of `σ₀`.

## Main declarations

* `CategoryTheory.SimplicialNerve.quasicategory`: the simplicial nerve of a simplicial category
  whose mapping simplicial sets are Kan complexes is a quasicategory.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.1.5.10.
-/

public section

open CategoryTheory EnrichedCategory

universe v u

namespace CategoryTheory.SimplicialNerve

open MathlibExt.CategoricalSource

/-- The simplicial nerve of a simplicial category whose mapping simplicial sets are Kan complexes
is a quasicategory. -/
instance quasicategory (C : Type u) [Category.{v} C] [SimplicialCategory C]
    [∀ a b : C, SSet.KanComplex (a ⟶[SSet] b)] : SSet.Quasicategory (SimplicialNerve C) := by
  refine SSet.quasicategory_of_filler _ fun n i σ₀ h₀ h₁ ↦ ?_
  have key (j : Fin (n + 3)) (hj : j ≠ i) (m : Fin (n + 2)) :
      SSet.yonedaEquiv (SSet.stdSimplex.δ m ≫ SSet.horn.ι i j hj ≫ σ₀) =
        (SimplicialNerve C).δ m (σ₀.app _ (SSet.horn.face i j hj)) := by
    rw [← SSet.yonedaEquiv.symm_apply_apply (SSet.horn.ι i j hj ≫ σ₀),
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply, SSet.yonedaEquiv_comp,
      SSet.horn.yonedaEquiv_ι]
  obtain ⟨F, hF⟩ := HornThickening.exists_desc h₀ h₁ (fun j hj ↦ σ₀.app _ (SSet.horn.face i j hj))
    fun j k hj hk hjk ↦ by
      have := congrArg SSet.yonedaEquiv
        ((SSet.horn.isCompatible_iff _).1 (SSet.horn.IsCompatible.of_hom σ₀) j k hj hk hjk)
      rwa [key, key] at this
  obtain ⟨G, hG⟩ := HornThickening.exists_extension (c := (⟨i⟩ : ULift.{v} (Fin (n + 3))))
    (bot_lt_iff_ne_bot.2 fun h ↦ h₀.ne' (congrArg ULift.down h))
    (lt_top_iff_ne_top.2 fun h ↦ h₁.ne (congrArg ULift.down h)) F
  refine ⟨G, fun j hj ↦ ?_⟩
  -- The `j`-th face of `G` is `G` precomposed with the coface functor, by definition of the
  -- simplicial nerve, and composition of simplicial functors is associative by definition.
  rw [← hF j hj, ← hG]
  exact (congrArg (fun F ↦ EnrichedFunctor.comp SSet F G) (HornThickening.δ_comp_ι j hj)).symm

end CategoryTheory.SimplicialNerve

end
