/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.OneCellOpenComplement
public import MathlibExt.CategoryTheory.TrivialBundleWithFiberOver
public import MathlibExt.Topology.Category.TopCat.Subspace

/-!
# Trivial bundles over one-cell complements

For a base pushout IsPushout t l r b with r a closed embedding and a total-space pullback
along b, a fixed-fiber trivial-bundle presentation over the complement of the range of l
gives one over the complement of the range of r. The construction identifies the new-cell
complement with the preimage of the ambient complement and transports the presentation
through that base isomorphism. A second construction restricts an ambient presentation to
the new-cell complement when b maps that complement into the ambient one.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

namespace modelCategoryQuillen

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
variable {E E₃ : TopCat.{u}} {p : E ⟶ X₄} {p₃ : E₃ ⟶ X₃} {e : E₃ ⟶ E}

/-- Transport a fixed-fiber over-presentation from the new-cell complement
    to the ambient complement. -/
noncomputable def trivialBundleWithFiberOver_oneCellComplement
    (sqBase : IsPushout t l r b)
    (hr : IsClosedEmbedding r.hom)
    (sqQ : IsPullback e p₃ p b)
    (F : TopCat.{u})
    (h_new : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (AlgebraicTopology.subspaceIncl ((Set.range l.hom)ᶜ))) :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ)) := by
  have h_eq : ⇑b ⁻¹' ((Set.range r.hom)ᶜ) = (Set.range l.hom)ᶜ :=
    preimage_oneCellOpenComplement_eq sqBase
  rw [←h_eq] at h_new
  have h_home : IsHomeomorph (((Set.range r.hom)ᶜ).restrictPreimage b) :=
    isHomeomorph_oneCellOpenComplement_restrictPreimage sqBase hr
  let baseSub : TopCat.of ↥(⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ⟶
      TopCat.of ↥((Set.range r.hom)ᶜ) :=
    AlgebraicTopology.subspaceMap b (fun x hx => hx)
  have h_eq_fun : ⇑baseSub = (((Set.range r.hom)ᶜ).restrictPreimage b) := rfl
  rw [←h_eq_fun] at h_home
  haveI : IsIso baseSub :=
    (TopCat.isIso_iff_isHomeomorph baseSub).mpr h_home
  let baseIso0 : TopCat.of ↥(⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ≅
      TopCat.of ↥((Set.range r.hom)ᶜ) :=
    CategoryTheory.asIso baseSub
  have h_sub_eq : baseSub ≫ AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ) =
      AlgebraicTopology.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ≫ b :=
    AlgebraicTopology.subspaceMap_comp_subspaceIncl b (fun x hx => hx)
  let sq_pull : IsPullback (Limits.pullback.fst h_new.p' baseIso0.inv)
      (Limits.pullback.snd h_new.p' baseIso0.inv) h_new.p' baseIso0.inv :=
    IsPullback.of_hasPullback h_new.p' baseIso0.inv
  have h_triv : CategoryTheory.TrivialBundleWithFiber F
      (Limits.pullback.snd h_new.p' baseIso0.inv) :=
    h_new.trivial.pullback sq_pull
  have sq_pasted : IsPullback
      ((Limits.pullback.fst h_new.p' baseIso0.inv ≫ h_new.t) ≫ e)
      (Limits.pullback.snd h_new.p' baseIso0.inv) p
      ((baseIso0.inv ≫ AlgebraicTopology.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ))) ≫ b) :=
    (sq_pull.paste_horiz h_new.sq).paste_horiz sqQ
  have h_bot : ((baseIso0.inv ≫
      AlgebraicTopology.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ))) ≫ b) =
      AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ) := by
    calc ((baseIso0.inv ≫
            AlgebraicTopology.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ))) ≫ b)
        = baseIso0.inv ≫ (AlgebraicTopology.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ≫ b) := by
          rw [Category.assoc]
      _ = baseIso0.inv ≫ (baseSub ≫
            AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ)) := by
          rw [←h_sub_eq]
      _ = (baseIso0.inv ≫ baseSub) ≫
            AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ) := by
          rw [←Category.assoc]
      _ = (baseIso0.inv ≫ baseIso0.hom) ≫
            AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ) := rfl
      _ = 𝟙 _ ≫ AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ) := by
          rw [Iso.inv_hom_id]
      _ = AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ) := by
          rw [Category.id_comp]
  rw [h_bot] at sq_pasted
  exact ⟨Limits.pullback h_new.p' baseIso0.inv,
    Limits.pullback.snd h_new.p' baseIso0.inv,
    (Limits.pullback.fst h_new.p' baseIso0.inv ≫ h_new.t) ≫ e,
    sq_pasted, h_triv⟩

/-- Forward supplier for the one-cell datum: restrict an ambient-complement
    over-presentation to the old-side complement along the attachment map. -/
noncomputable def trivialBundleWithFiberOver_oneCellComplementForward
    (sqQ : IsPullback e p₃ p b)
    (F : TopCat.{u})
    (hAmb : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ)))
    (hMaps : Set.MapsTo b ((Set.range l.hom)ᶜ) ((Set.range r.hom)ᶜ)) :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (AlgebraicTopology.subspaceIncl ((Set.range l.hom)ᶜ)) := by
  let g : TopCat.of ↥((Set.range l.hom)ᶜ) ⟶
      TopCat.of ↥((Set.range r.hom)ᶜ) :=
    AlgebraicTopology.subspaceMap b hMaps
  have hBase : AlgebraicTopology.subspaceIncl ((Set.range l.hom)ᶜ) ≫ b =
      g ≫ AlgebraicTopology.subspaceIncl ((Set.range r.hom)ᶜ) :=
    (AlgebraicTopology.subspaceMap_comp_subspaceIncl b hMaps).symm
  exact hAmb.forwardOfAmbientPullback sqQ hBase
    (IsPullback.of_hasPullback hAmb.p' g)

end modelCategoryQuillen

end TopCat
