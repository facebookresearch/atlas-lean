/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.PushoutComplement
public import MathlibExt.CategoryTheory.TrivialBundleWithFiberOver
public import MathlibExt.Topology.Category.TopCat.Subspace

/-!
# Trivial bundles over complements in a pushout

In `TopCat.{u}`, let `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a
pushout, with `Set.range r` closed. Let `p : E ⟶ X₄` and `p₃ : E₃ ⟶ X₃` be related by the
pullback square `IsPullback e p₃ p b`. A trivialization of `p₃` with fixed fiber `F` over
`(Set.range l.hom)ᶜ` induces a trivialization of `p` with the same fiber over `(Set.range
r.hom)ᶜ`.

Here `TrivialBundleWithFiberOver F p f` specifies a pullback presentation of `p` along `f`
whose total space is a product of the new base and `F`. Restriction also gives the reverse
construction whenever `b` maps the new-side complement into the ambient complement; this
direction only requires the specified pullback square and the subset condition.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat


variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
variable {E E₃ : TopCat.{u}} {p : E ⟶ X₄} {p₃ : E₃ ⟶ X₃} {e : E₃ ⟶ E}

/-- In `TopCat.{u}`, suppose `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a
pushout and `Set.range r.hom` is closed. Let `p : E ⟶ X₄`, `p₃ : E₃ ⟶ X₃`, and `e : E₃ ⟶ E`
form the pullback `IsPullback e p₃ p b`. For a fixed fiber `F : TopCat.{u}`, a presentation
`h_new` trivializing `p₃` over `(Set.range l.hom)ᶜ` induces a presentation trivializing `p`
over `(Set.range r.hom)ᶜ`. Both presentations are pullbacks along the corresponding subspace
inclusions with total spaces products of their bases and `F`. -/
noncomputable def trivialBundleWithFiberOverPushoutComplement
    (sqBase : IsPushout t l r b)
    (hr : IsClosed (Set.range r.hom))
    (sqQ : IsPullback e p₃ p b)
    (F : TopCat.{u})
    (h_new : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (TopCat.subspaceIncl ((Set.range l.hom)ᶜ))) :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (TopCat.subspaceIncl ((Set.range r.hom)ᶜ)) := by
  have h_eq : ⇑b ⁻¹' ((Set.range r.hom)ᶜ) = (Set.range l.hom)ᶜ :=
    preimage_compl_range_of_isPushout sqBase
  rw [←h_eq] at h_new
  have h_home : IsHomeomorph (((Set.range r.hom)ᶜ).restrictPreimage b) :=
    isHomeomorph_restrictPreimage_compl_range_of_isPushout sqBase hr
  let baseSub : TopCat.of ↥(⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ⟶
      TopCat.of ↥((Set.range r.hom)ᶜ) :=
    TopCat.subspaceMap b (fun x hx => hx)
  have h_eq_fun : ⇑baseSub = (((Set.range r.hom)ᶜ).restrictPreimage b) := rfl
  rw [←h_eq_fun] at h_home
  haveI : IsIso baseSub :=
    (TopCat.isIso_iff_isHomeomorph baseSub).mpr h_home
  let baseIso0 : TopCat.of ↥(⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ≅
      TopCat.of ↥((Set.range r.hom)ᶜ) :=
    CategoryTheory.asIso baseSub
  have h_sub_eq : baseSub ≫ TopCat.subspaceIncl ((Set.range r.hom)ᶜ) =
      TopCat.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ≫ b :=
    TopCat.subspaceMap_comp_subspaceIncl b (fun x hx => hx)
  let sq_pull : IsPullback (Limits.pullback.fst h_new.p' baseIso0.inv)
      (Limits.pullback.snd h_new.p' baseIso0.inv) h_new.p' baseIso0.inv :=
    IsPullback.of_hasPullback h_new.p' baseIso0.inv
  have h_triv : CategoryTheory.TrivialBundleWithFiber F
      (Limits.pullback.snd h_new.p' baseIso0.inv) :=
    h_new.trivial.pullback sq_pull
  have sq_pasted : IsPullback
      ((Limits.pullback.fst h_new.p' baseIso0.inv ≫ h_new.t) ≫ e)
      (Limits.pullback.snd h_new.p' baseIso0.inv) p
      ((baseIso0.inv ≫ TopCat.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ))) ≫ b) :=
    (sq_pull.paste_horiz h_new.sq).paste_horiz sqQ
  have h_bot : ((baseIso0.inv ≫
      TopCat.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ))) ≫ b) =
      TopCat.subspaceIncl ((Set.range r.hom)ᶜ) := by
    calc ((baseIso0.inv ≫
            TopCat.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ))) ≫ b)
        = baseIso0.inv ≫ (TopCat.subspaceIncl (⇑b ⁻¹' ((Set.range r.hom)ᶜ)) ≫ b) := by
          rw [Category.assoc]
      _ = baseIso0.inv ≫ (baseSub ≫
            TopCat.subspaceIncl ((Set.range r.hom)ᶜ)) := by
          rw [←h_sub_eq]
      _ = (baseIso0.inv ≫ baseSub) ≫
            TopCat.subspaceIncl ((Set.range r.hom)ᶜ) := by
          rw [←Category.assoc]
      _ = (baseIso0.inv ≫ baseIso0.hom) ≫
            TopCat.subspaceIncl ((Set.range r.hom)ᶜ) := rfl
      _ = 𝟙 _ ≫ TopCat.subspaceIncl ((Set.range r.hom)ᶜ) := by
          rw [Iso.inv_hom_id]
      _ = TopCat.subspaceIncl ((Set.range r.hom)ᶜ) := by
          rw [Category.id_comp]
  rw [h_bot] at sq_pasted
  exact ⟨Limits.pullback h_new.p' baseIso0.inv,
    Limits.pullback.snd h_new.p' baseIso0.inv,
    (Limits.pullback.fst h_new.p' baseIso0.inv ≫ h_new.t) ≫ e,
    sq_pasted, h_triv⟩

/-- Let `p : E ⟶ X₄`, `p₃ : E₃ ⟶ X₃`, `b : X₃ ⟶ X₄`, and `e : E₃ ⟶ E` form a pullback square in
`TopCat.{u}`. Let `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `F : TopCat.{u}`. If `p` has a trivial
pullback presentation with fiber `F` over `(Set.range r.hom)ᶜ`, and `b` maps `(Set.range
l.hom)ᶜ` into that complement, then restriction yields a trivial pullback presentation of `p₃`
with fiber `F` over `(Set.range l.hom)ᶜ`. -/
noncomputable def trivialBundleWithFiberOverComplementOfAmbient
    (sqQ : IsPullback e p₃ p b)
    (F : TopCat.{u})
    (hAmb : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (TopCat.subspaceIncl ((Set.range r.hom)ᶜ)))
    (hMaps : Set.MapsTo b ((Set.range l.hom)ᶜ) ((Set.range r.hom)ᶜ)) :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (TopCat.subspaceIncl ((Set.range l.hom)ᶜ)) := by
  let g : TopCat.of ↥((Set.range l.hom)ᶜ) ⟶
      TopCat.of ↥((Set.range r.hom)ᶜ) :=
    TopCat.subspaceMap b hMaps
  have hBase : TopCat.subspaceIncl ((Set.range l.hom)ᶜ) ≫ b =
      g ≫ TopCat.subspaceIncl ((Set.range r.hom)ᶜ) :=
    (TopCat.subspaceMap_comp_subspaceIncl b hMaps).symm
  exact hAmb.forwardOfAmbientPullback sqQ hBase
    (IsPullback.of_hasPullback hAmb.p' g)


end TopCat
