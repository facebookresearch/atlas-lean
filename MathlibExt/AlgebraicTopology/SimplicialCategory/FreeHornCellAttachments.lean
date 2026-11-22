/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeIndexedPushoutAnodyne
import MathlibExt.AlgebraicTopology.SimplicialCategory.SingleHomQuiverMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFamilies
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomAnodyne

/-!
# Actual free-horn coproduct pushouts have anodyne original Homs

Literal horn-family membership selects the exact original generating
map as an equality of arrows. The whole original coproduct cocones
transport along those equalities. The proved indexed word filtration
then gives anodyne Hom maps for every actual small free-horn attachment.
No enriched pushout or transfer weakness is supplied as a conclusion.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeHornCells

variable {O : Type u}

/-- The actual positive-dimensional horn labels and original ordered object pair. -/
abbrev Index (O : Type u) := Σ n : ℕ, O × O × Fin (n + 2)

/-- The same original free-horn domain generating quiver. -/
abbrev domainQuiver (t : Index O) : SimplicialQuiver.Data O :=
  SimplicialQuiver.SingleHom.quiver t.2.1 t.2.2.1 (Λ[t.1 + 1, t.2.2.2] : SSet.{u})

/-- The same original standard-simplex target generating quiver. -/
abbrev targetQuiver (t : Index O) : SimplicialQuiver.Data O :=
  SimplicialQuiver.SingleHom.quiver t.2.1 t.2.2.1 (Δ[t.1 + 1] : SSet.{u})

/-- The original horn inclusion at its same exact ordered pair, and initial maps elsewhere. -/
def quiverMap (t : Index O) : ∀ a b : O, (domainQuiver t).Hom a b ⟶ (targetQuiver t).Hom a b :=
  SimplicialQuiver.SingleHom.quiverMap t.2.1 t.2.2.1 (Λ[t.1 + 1, t.2.2.2]).ι

/-- Every original quiver Hom map is genuinely anodyne, from the native scalar horn theorem. -/
theorem quiverMap_anodyne (t : Index O) (a b : O) : SSet.anodyneExtensions (quiverMap t a b) :=
  SimplicialQuiver.SingleHom.quiverMap_anodyne t.2.1 t.2.2.1 _
    (SSet.anodyneExtensions.horn_ι t.2.2.2) a b

private theorem indexWitness {A B : FixedObjects O} (f : A ⟶ B) (hf : hornFamily O f) :
    ∃ t : Index O, Arrow.mk f = Arrow.mk (FreeQuiver.map (quiverMap t)) := by
  obtain ⟨t, ht⟩ := (MorphismProperty.ofHoms_iff
    (fun t : Index O => (FreeSingleHom.functor t.2.1 t.2.2.1).map (Λ[t.1 + 1, t.2.2.2]).ι) f).mp hf
  exact ⟨t, ht.trans (congrArg Arrow.mk
    (SimplicialQuiver.SingleHom.free_quiverMap t.2.1 t.2.2.1 (Λ[t.1 + 1, t.2.2.2]).ι)).symm⟩

/-- Every actual small coproduct pushout of the literal free horns is anodyne on all original Homs. -/
theorem coproduct_pushouts_le_homAnodyne :
    (MorphismProperty.coproducts.{u} (hornFamily O)).pushouts ≤ homAnodyne O := by
  classical
  rintro C D f ⟨A, B, p, s, k, hpc, hp⟩
  obtain ⟨I, hpc⟩ := (MorphismProperty.coproducts_iff _ p).mp hpc
  rcases hpc with ⟨F₁, F₂, c₁, c₂, h₁, h₂, τ, hτ⟩
  choose idx hi using (fun i : I => indexWitness (τ.app (Discrete.mk i)) (hτ (Discrete.mk i)))
  let Q (i : I) := domainQuiver (idx i)
  let R (i : I) := targetQuiver (idx i)
  let m (i : I) := quiverMap (idx i)
  let e (i : I) : Arrow.mk (FreeQuiver.map (m i)) ≅ Arrow.mk (τ.app (Discrete.mk i)) :=
    eqToIso (hi i).symm
  let e₁ : Discrete.functor (fun i => FreeQuiver.object (Q i)) ≅ F₁ :=
    Discrete.natIso (fun i => Arrow.leftFunc.mapIso (e i.as))
  let e₂ : Discrete.functor (fun i => FreeQuiver.object (R i)) ≅ F₂ :=
    Discrete.natIso (fun i => Arrow.rightFunc.mapIso (e i.as))
  let c₁' : Cofan (fun i => FreeQuiver.object (Q i)) := (Cocone.precompose e₁.hom).obj c₁
  let c₂' : Cofan (fun i => FreeQuiver.object (R i)) := (Cocone.precompose e₂.hom).obj c₂
  have h₁' : IsColimit c₁' := (IsColimit.precomposeHomEquiv e₁ c₁).symm h₁
  have h₂' : IsColimit c₂' := (IsColimit.precomposeHomEquiv e₂ c₂).symm h₂
  let φ := h₁.desc (Cocone.mk c₂.pt (τ ≫ c₂.ι))
  change IsPushout s φ f k at hp
  have hφ (i : I) : c₁'.inj i ≫ φ = FreeQuiver.map (m i) ≫ c₂'.inj i := by
    change ((e i).hom.left ≫ c₁.ι.app (Discrete.mk i)) ≫ φ =
      FreeQuiver.map (m i) ≫ (e i).hom.right ≫ c₂.ι.app (Discrete.mk i)
    have ho : c₁.ι.app (Discrete.mk i) ≫ φ = τ.app (Discrete.mk i) ≫ c₂.ι.app (Discrete.mk i) :=
      h₁.fac (Cocone.mk c₂.pt (τ ≫ c₂.ι)) (Discrete.mk i)
    have hw : (e i).hom.left ≫ τ.app (Discrete.mk i) = FreeQuiver.map (m i) ≫ (e i).hom.right :=
      (e i).hom.w
    rw [Category.assoc, ho, ← Category.assoc, hw, Category.assoc]
  apply (homAnodyne_iff f).mpr
  intro x y
  exact FreeIndexedPushout.hom_anodyne_of_isPushout m (fun i a b => quiverMap_anodyne (idx i) a b)
    c₁' c₂' h₁' h₂' φ hφ s f k hp x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeHornCells
