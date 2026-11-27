/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing data from opens and transition maps

`AlgebraicGeometry.Scheme.GlueData.MkCore` packages gluing data given by schemes `U i`,
opens `V i j ⊆ U i` and transition maps `t i j : V i j ⟶ V j i` such that `V i i` is all of
`U i`, `t i i` is the identity, `t i j` sends `V i j ∩ V i k` into `V j i ∩ V j k`, and on
`V i j ∩ V i k` the two routes to `U k`, through `t i j` and `t j k` or through `t i k`, agree.
These conditions are stated with opens instead of pullbacks. `MkCore.glueData` turns the
data into `Scheme.GlueData`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.GlueData

/-- Gluing data for schemes given by opens `V i j` of `U i` and transition maps
`t i j : V i j ⟶ V j i` such that `V i i` is all of `U i` (`V_id`), `t i i` is the identity
(`t_id`), `t i j` sends `V i j ∩ V i k` into `V j i ∩ V j k` (`t_inter`), and on
`V i j ∩ V i k` the two routes to `U k`, through `t i j` and `t j k` or through `t i k`, agree
(`cocycle`). This is the scheme analogue of `TopCat.GlueData.MkCore`. -/
structure MkCore where
  /-- The index type. -/
  {J : Type u}
  /-- The schemes to glue. -/
  U : J → Scheme.{u}
  /-- The open of `U i` glued to `U j`. -/
  V : ∀ i, J → (U i).Opens
  /-- The transition maps. -/
  t : ∀ i j, (V i j : Scheme.{u}) ⟶ (V j i : Scheme.{u})
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, t i i = 𝟙 _
  t_inter : ∀ i j k, (V i j).ι ⁻¹ᵁ (V i k) ≤ t i j ⁻¹ᵁ ((V j i).ι ⁻¹ᵁ (V j k))
  cocycle : ∀ i j k,
    (t i j).resLE ((V j i).ι ⁻¹ᵁ (V j k)) ((V i j).ι ⁻¹ᵁ (V i k)) (t_inter i j k) ≫
      ((U j).restrictRestrictComm (V j i) (V j k)).hom ≫ ((V j k).ι ⁻¹ᵁ (V j i)).ι ≫
        t j k ≫ (V k j).ι =
    ((U i).restrictRestrictComm (V i j) (V i k)).hom ≫ ((V i k).ι ⁻¹ᵁ (V i j)).ι ≫
      t i k ≫ (V k i).ι

namespace MkCore

variable (h : MkCore.{u})

/-- The triple overlap `V i j ∩ V i k`, as an open of `V i j`. -/
abbrev W (i j k : h.J) : (h.V i j : Scheme.{u}).Opens := (h.V i j).ι ⁻¹ᵁ (h.V i k)

/-- The transition map restricted to triple overlaps. -/
noncomputable abbrev τ (i j k : h.J) : (h.W i j k : Scheme.{u}) ⟶ (h.W j i k : Scheme.{u}) :=
  (h.t i j).resLE (h.W j i k) (h.W i j k) (h.t_inter i j k)

/-- The canonical isomorphism swapping the two sides of a triple overlap. -/
noncomputable abbrev σ (i j k : h.J) : (h.W i j k : Scheme.{u}) ≅ (h.W i k j : Scheme.{u}) :=
  (h.U i).restrictRestrictComm (h.V i j) (h.V i k)

/-- `σ` commutes with the inclusions into `U i`. -/
@[reassoc]
lemma σ_hom_ι_ι (i j k : h.J) :
    (h.σ i j k).hom ≫ (h.W i k j).ι ≫ (h.V i k).ι = (h.W i j k).ι ≫ (h.V i j).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- `σ` is an involution. -/
@[reassoc]
lemma σ_hom_σ_hom (i j k : h.J) : (h.σ i j k).hom ≫ (h.σ i k j).hom = 𝟙 _ := by
  rw [← cancel_mono ((h.W i j k).ι ≫ (h.V i j).ι), Category.assoc, σ_hom_ι_ι, σ_hom_ι_ι,
    Category.id_comp]

/-- `σ j i i` commutes with the inclusion. -/
@[reassoc]
lemma σ_self_hom_ι (i j : h.J) : (h.σ j i i).hom ≫ (h.W j i i).ι = (h.W j i i).ι := by
  rw [← cancel_mono (h.V j i).ι, Category.assoc, σ_hom_ι_ι]

/-- `τ` is the restriction of `t`. -/
@[reassoc]
lemma τ_ι (i j k : h.J) : h.τ i j k ≫ (h.W j i k).ι = (h.W i j k).ι ≫ h.t i j :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The cocycle condition in terms of `τ` and `σ`. -/
lemma cocycle' (i j k : h.J) :
    h.τ i j k ≫ (h.σ j i k).hom ≫ (h.W j k i).ι ≫ h.t j k ≫ (h.V k j).ι =
      (h.σ i j k).hom ≫ (h.W i k j).ι ≫ h.t i k ≫ (h.V k i).ι :=
  h.cocycle i j k

/-- The overlap `V i j ∩ V i i` is all of `V i j`. -/
lemma W_self (i j : h.J) : h.W i j i = ⊤ := by
  change (h.V i j).ι ⁻¹ᵁ h.V i i = ⊤
  rw [h.V_id]
  rfl

/-- The inclusion of `W i j i` is an isomorphism. -/
scoped instance (i j : h.J) : IsIso (h.W i j i).ι := by
  rw [show (h.W i j i).ι = ((h.V i j : Scheme.{u}).isoOfEq (h.W_self i j)).hom ≫
      (⊤ : (h.V i j : Scheme.{u}).Opens).ι from ((h.V i j : Scheme.{u}).isoOfEq_hom_ι _).symm]
  have : IsIso (⊤ : (h.V i j : Scheme.{u}).Opens).ι := (Scheme.topIso _).isIso_hom
  infer_instance

/-- `t j i` is inverse to `t i j`. -/
@[reassoc (attr := simp)]
lemma t_inv (i j : h.J) : h.t i j ≫ h.t j i = 𝟙 _ := by
  have c := h.cocycle' i j i
  rw [h.t_id, Category.id_comp, σ_hom_ι_ι, σ_self_hom_ι_assoc, τ_ι_assoc] at c
  rw [← cancel_epi (h.W i j i).ι, ← cancel_mono (h.V i j).ι]
  simpa only [Category.assoc, Category.comp_id] using c

/-- The transition maps are isomorphisms. -/
scoped instance (i j : h.J) : IsIso (h.t i j) := ⟨h.t j i, h.t_inv i j, h.t_inv j i⟩

/-- The pullback of two opens of `U i` is their intersection. -/
noncomputable abbrev isoW (i j k : h.J) :
    pullback (h.V i j).ι (h.V i k).ι ≅ (h.W i j k : Scheme.{u}) :=
  pullbackRestrictIsoRestrict (h.V i j).ι (h.V i k)

/-- The transition map on triple overlaps, phrased with pullbacks. -/
noncomputable def t' (i j k : h.J) :
    pullback (h.V i j).ι (h.V i k).ι ⟶ pullback (h.V j k).ι (h.V j i).ι :=
  (h.isoW i j k).hom ≫ h.τ i j k ≫ (h.σ j i k).hom ≫ (h.isoW j k i).inv

/-- The cocycle condition on triple overlaps, as an identity of endomorphisms. -/
lemma core (i j k : h.J) :
    h.τ i j k ≫ (h.σ j i k).hom ≫ h.τ j k i ≫ (h.σ k j i).hom ≫ h.τ k i j ≫ (h.σ i k j).hom =
      𝟙 _ := by
  rw [← cancel_mono ((h.W i j k).ι ≫ (h.V i j).ι)]
  simp only [Category.assoc, Category.id_comp]
  rw [σ_hom_ι_ι, τ_ι_assoc, h.cocycle' j k i, σ_hom_σ_hom_assoc, τ_ι_assoc, t_inv_assoc]

/-- The gluing data associated with `h`. -/
noncomputable def glueData : Scheme.GlueData.{u} where
  J := h.J
  U := h.U
  V ij := h.V ij.1 ij.2
  f i j := (h.V i j).ι
  f_id i := h.V_id i ▸ (Scheme.topIso (h.U i)).isIso_hom
  f_open i j := inferInstance
  t := h.t
  t_id := h.t_id
  t' := h.t'
  t_fac i j k := by
    change h.t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ h.t i j
    rw [t', Category.assoc, Category.assoc, Category.assoc, ← pullbackRestrictIsoRestrict_hom_ι,
      Category.assoc, cancel_epi, ← cancel_mono (h.V j i).ι]
    change h.τ i j k ≫ (h.σ j i k).hom ≫ ((h.V j k).ι ∣_ h.V j i) ≫ (h.V j i).ι = _
    rw [morphismRestrict_ι, σ_hom_ι_ι, Category.assoc, τ_ι_assoc]
  cocycle i j k := by
    change h.t' i j k ≫ h.t' j k i ≫ h.t' k i j = 𝟙 _
    simp only [t', Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (h.core i j k), Iso.hom_inv_id]

@[scoped simp] lemma glueData_J : h.glueData.J = h.J := rfl
@[scoped simp] lemma glueData_U (i : h.J) : h.glueData.U i = h.U i := rfl
@[scoped simp] lemma glueData_V (i j : h.J) : h.glueData.V (i, j) = (h.V i j : Scheme.{u}) := rfl
@[scoped simp] lemma glueData_f (i j : h.J) : h.glueData.f i j = (h.V i j).ι := rfl
@[scoped simp] lemma glueData_t (i j : h.J) : h.glueData.t i j = h.t i j := rfl

/-- The gluing condition for `h.glueData`. -/
lemma t_ι_ι (i j : h.J) :
    h.t i j ≫ (h.V j i).ι ≫ h.glueData.ι j = (h.V i j).ι ≫ h.glueData.ι i :=
  h.glueData.glue_condition i j

/-- The charts of the glued scheme are open immersions. -/
scoped instance (i : h.J) : IsOpenImmersion (h.glueData.ι i) :=
  Scheme.GlueData.ι_isOpenImmersion h.glueData i

/-- The preimage in `U i` of the image of `U j` in the glued scheme is `V i j`. -/
lemma preimage_opensRange (i j : h.J) :
    (h.glueData.ι i) ⁻¹ᵁ (h.glueData.ι j).opensRange = h.V i j := by
  have hP := h.glueData.vPullbackConeIsLimit i j
  let e := hP.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ pullback.fst (h.glueData.ι i) (h.glueData.ι j) = (h.V i j).ι :=
    hP.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingCospan.left
  have hrange : Set.range (pullback.fst (h.glueData.ι i) (h.glueData.ι j)) =
      (h.V i j : Set (h.U i)) := by
    rw [← Scheme.Opens.range_ι (h.V i j), ← he]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := (Scheme.homeoOfIso e).surjective a
      exact ⟨b, (Scheme.Hom.comp_apply _ _ b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨e.hom b, (Scheme.Hom.comp_apply _ _ b).symm⟩
  ext1
  exact (Scheme.Pullback.range_fst (h.glueData.ι i) (h.glueData.ι j)).symm.trans hrange

end MkCore

end AlgebraicGeometry.Scheme.GlueData
