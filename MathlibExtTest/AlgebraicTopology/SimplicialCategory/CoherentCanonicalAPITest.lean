/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallLimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomOpenBox

/-!
# Coherent constructions as clients of the canonical simplicial-category APIs

The realization adjunction and raised-universe limits use `EnrichedCat` directly.
Its counit evaluates whole coherent Hom maps, and the canonical vertex inverse
is the original constant simplex. For the smallest inner horn, a growing path
chain from the endpoint-only path to the full path is excluded, while the chain
which stays on the full path belongs to the horn.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open CategoryTheory.SimplicialEnrichment CategoryTheory.CoherentRealization
open scoped Simplicial

namespace CoherentCanonicalAPITest

/-- The coherent adjunction has exactly the canonical category and nerve as its target. -/
abbrev canonicalAdjunction : realizationFunctor.{u} ⊣ simplicialNerveFunctor.{u, u} :=
  realizationAdjunction

/-- The existing limit instance applies directly to the canonical category, one universe up. -/
example : HasLimitsOfSize.{u + 1, u + 1}
    (EnrichedCat.{u + 1, u + 2, u + 1} SSet.{u + 1}) := inferInstance

/-- The canonical vertex inverse is equal as a whole enriched functor to the constant simplex. -/
example (C : EnrichedCat.{u, u + 1, u} SSet.{u}) (c : C) :
    (SimplicialNerve.vertexEquiv (ForgetEnrichment SSet.{u} C)).symm c =
      constantSimplex C ⦋0⦌ c := by
  apply (SimplicialNerve.vertexEquiv (ForgetEnrichment SSet.{u} C)).injective
  exact (SimplicialNerve.vertexEquiv (ForgetEnrichment SSet.{u} C)).apply_symm_apply c

/-- The zero-path instance remains available to clients of the canonical vertex API. -/
example (i j : coherentSimplex.{u} ⦋0⦌) :
    Subsingleton (SimplicialThickening.Path i.as j.as) := inferInstance

/-- Its original path morphisms still have their subsingleton instance. -/
example (i j : coherentSimplex.{u} ⦋0⦌) (a b : SimplicialThickening.Path i.as j.as) :
    Subsingleton (a ⟶ b) := inferInstance

/-- A counit in the canonical category evaluates every Hom simplex with its original endpoints. -/
example (C : EnrichedCat.{u, u + 1, u} SSet.{u}) {n : SimplexCategory}
    (σ : (simplicialNerveFunctor.obj C).obj (op n)) (i j : coherentSimplex.{u} n) :
    simplexHom (simplicialNerveFunctor.obj C) σ i j rfl rfl ≫
      (canonicalAdjunction.counit.app C).map (vertex (simplicialNerveFunctor.obj C) σ i)
        (vertex (simplicialNerveFunctor.obj C) σ j) = σ.map i j :=
  counit_simplexHom C σ i j

private abbrev hij : (0 : Fin 3) ≤ Fin.last 2 := Fin.zero_le _
private abbrev middle : IntervalHom.Interior (0 : Fin 3) (Fin.last 2) :=
  ⟨1, by decide, by decide⟩

private def growingChain : (nerve (SimplicialThickening.Path (0 : Fin 3) (Fin.last 2))) _⦋1⦌ :=
  ComposableArrows.mk₁ ((IntervalHom.reinsertFunctor hij).map
    (homOfLE (Set.empty_subset (Set.univ : Set (IntervalHom.Interior (0 : Fin 3) (Fin.last 2))))))

private def retainedChain : (nerve (SimplicialThickening.Path (0 : Fin 3) (Fin.last 2))) _⦋1⦌ :=
  ComposableArrows.mk₁ (𝟙 (IntervalHom.reinsert hij Set.univ))

/-- The edge which first omits the distinguished vertex and then retains it is outside the horn. -/
example : growingChain ∉ (HomOpenBox.subcomplex hij middle).obj (op ⦋1⦌) := by
  rw [HomOpenBox.subcomplex_eq_hornPaths, MathlibExt.CategoricalSource.mem_hornPaths_iff]
  rintro (⟨t, ht₀, ht₂, htne, -⟩ | ⟨t, ht₀, ht₂, ht⟩)
  · have h : t = (1 : Fin 3) := by apply Fin.ext; simp only [Fin.lt_def] at *; omega
    exact htne h
  · have h : t = (1 : Fin 3) := by apply Fin.ext; simp only [Fin.lt_def] at *; omega
    subst t
    change (1 : Fin 3) ∈ (IntervalHom.reinsert hij ∅).I at ht
    simp [IntervalHom.reinsert] at ht

/-- The edge which retains the middle vertex at both ends belongs to the same original horn. -/
example : retainedChain ∈ (HomOpenBox.subcomplex hij middle).obj (op ⦋1⦌) := by
  rw [HomOpenBox.subcomplex_eq_hornPaths, MathlibExt.CategoricalSource.mem_hornPaths_iff]
  refine Or.inr ⟨1, by decide, by decide, ?_⟩
  change (1 : Fin 3) ∈ (IntervalHom.reinsert hij Set.univ).I
  exact Or.inr ⟨middle, Set.mem_univ _, rfl⟩

end CoherentCanonicalAPITest
