/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModels

/-!
# Uniqueness and étale base change of Néron models

For a `NeronModel` over a domain `R` with fraction field `K`, the mapping property says
exactly that restriction to generic fibres is a bijection on morphisms from smooth
`R`-schemes. From this:

* two Néron models of the same `K`-scheme are related by a unique isomorphism over `R`
  compatible with the two identifications of their generic fibres
  (`NeronModel.existsUnique_iso`);
* the base change of a Néron model along a smooth morphism `Spec R' ⟶ Spec R` whose generic
  square is a pullback (`K' = R' ⊗_R K`) is a Néron model of the base-changed generic scheme
  (`NeronModel.baseChange`), so the comparison morphism `baseChangeMap` to any Néron model
  over `R'` is an isomorphism (`NeronModel.isIso_baseChangeMap`).

These use only the mapping property: `R` and `R'` need not be Dedekind domains, the
generic scheme need not be of finite type, and étale base change is generalized to
smooth base change with `K' = R' ⊗_R K`.

References: S. Lichtenstein, *Néron models*, seminar notes, Stanford, 2011,
http://math.stanford.edu/~conrad/mordellsem/Notes/L11.pdf: Definition 1.3.2, p. 2;
Proposition 1.4.2 (i), p. 5; Proposition 1.4.3 with its proof, pp. 5–6.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NeronModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Spec (.of K))}

namespace NeronModel

/-- The mapping property of a Néron model `N`, restated: for every smooth `R`-scheme `Y`,
taking generic fibres is a bijection from `R`-morphisms `Y ⟶ N.model` to `K`-morphisms
between the generic fibres. -/
theorem bijective_map (N : NeronModel R K A) (Y : Over (trait R)) [Smooth Y.hom] :
    Function.Bijective (fun e : Y ⟶ N.model ↦ (genericFunctor R K).map e) := by
  refine ⟨fun e₁ e₂ h ↦ (N.homEquiv Y).injective ?_, fun g ↦
    ⟨(N.homEquiv Y).symm (g ≫ N.genericIso.hom), ?_⟩⟩
  · change (genericFunctor R K).map e₁ ≫ _ = (genericFunctor R K).map e₂ ≫ _
    simp only at h
    rw [h]
  · simp only
    rw [← cancel_mono N.genericIso.hom]
    exact N.extend_generic Y _

/-- A smooth, separated, locally finite type `R`-scheme `M` with an identification `i` of its
generic fibre with `A` is a Néron model of `A` as soon as, for every smooth `R`-scheme `Y`,
taking generic fibres is a bijection from `Y ⟶ M` to morphisms between the generic fibres. -/
def ofBijective (M : Over (trait R)) [Smooth M.hom] [IsSeparated M.hom]
    [LocallyOfFiniteType M.hom] (i : (genericFunctor R K).obj M ≅ A)
    (h : ∀ (Y : Over (trait R)) [Smooth Y.hom],
      Function.Bijective (fun e : Y ⟶ M ↦ (genericFunctor R K).map e)) :
    NeronModel R K A where
  model := M
  genericIso := i
  mappingProperty Y _ f := by
    obtain ⟨e, he⟩ := (h Y).2 (f ≫ i.inv)
    simp only at he
    refine ⟨e, by simp [he], fun e' he' ↦ (h Y).1 ?_⟩
    simp only
    rw [he, ← he']
    simp

/-- The isomorphism between two Néron models `M` and `N` of the same `K`-scheme `A`: the
extensions of the identity of `A` in both directions. -/
def isoOfGeneric (M N : NeronModel R K A) : M.model ≅ N.model where
  hom := map M N (𝟙 A)
  inv := map N M (𝟙 A)
  hom_inv_id := by rw [← map_comp, Category.comp_id, map_id]
  inv_hom_id := by rw [← map_comp, Category.comp_id, map_id]

/-- **Uniqueness of Néron models.** If `M` and `N` are Néron models of the same `K`-scheme
`A`, there is a unique isomorphism `M.model ≅ N.model` over `R` whose generic fibre is
compatible with the two identifications of the generic fibres with `A`.

This is Lichtenstein, *Néron models*, Proposition 1.4.2 (i), p. 5, for a domain `R` with
fraction field `K` and any `K`-scheme `A`; the proof uses only the mapping property. -/
theorem existsUnique_iso (M N : NeronModel R K A) :
    ∃! e : M.model ≅ N.model,
      (genericFunctor R K).map e.hom ≫ N.genericIso.hom = M.genericIso.hom := by
  refine ⟨isoOfGeneric M N, (map_generic M N (𝟙 A)).trans (Category.comp_id _), fun e he ↦ ?_⟩
  ext1
  apply (N.homEquiv M.model).injective
  change (genericFunctor R K).map e.hom ≫ N.genericIso.hom =
    (genericFunctor R K).map (map M N (𝟙 A)) ≫ N.genericIso.hom
  rw [map_generic, Category.comp_id]
  exact he

section BaseChange

variable (R K) (R' : Type u) [CommRing R'] (K' : Type u) [Field K'] [Algebra R' K']
  [IsFractionRing R' K'] (φ : trait R' ⟶ trait R) [Smooth φ]
  (ψ : Spec (.of K') ⟶ Spec (.of K))
  (h : IsPullback ψ (genericInclusion R' K') (genericInclusion R K) φ)

include h in
/-- For a smooth `φ : Spec R' ⟶ Spec R` whose generic square with `ψ : Spec K' ⟶ Spec K` is a
pullback, and a Néron model `M` over `R`, taking generic fibres over `R'` is a bijection from
`R'`-morphisms `Y' ⟶ M.model ×_R R'` to morphisms between the generic fibres, for every smooth
`R'`-scheme `Y'`. -/
theorem bijective_map_baseChange (M : NeronModel R K A) (Y' : Over (trait R'))
    [Smooth Y'.hom] :
    Function.Bijective
      (fun e : Y' ⟶ (Over.pullback φ).obj M.model ↦ (genericFunctor R' K').map e) := by
  let Y : Over (trait R) := (Over.map φ).obj Y'
  have : Smooth Y.hom := by dsimp [Y]; infer_instance
  have hP : IsPullback (pullback.fst Y'.hom (genericInclusion R' K'))
      (pullback.snd Y'.hom (genericInclusion R' K') ≫ ψ) (Y'.hom ≫ φ) (genericInclusion R K) :=
    ((IsPullback.of_hasPullback Y'.hom (genericInclusion R' K')).flip.paste_horiz h).flip
  set c := hP.isoPullback
  have e0 : pullback.fst Y.hom (genericInclusion R K) =
      c.inv ≫ pullback.fst Y'.hom (genericInclusion R' K') :=
    hP.isoPullback_inv_fst.symm
  refine ⟨fun e₁ e₂ he ↦ ?_, fun f ↦ ?_⟩
  · simp only at he
    let flat (e : Y' ⟶ (Over.pullback φ).obj M.model) : Y ⟶ M.model :=
      Over.homMk (e.left ≫ pullback.fst M.model.hom φ) (by
        have := Over.w e
        simp only [Over.pullback_obj_hom] at this
        simp [Y, pullback.condition, reassoc_of% this])
    have hflat : flat e₁ = flat e₂ := by
      apply (M.bijective_map Y).1
      ext1
      simp only [Over.pullback_map_left]
      apply pullback.hom_ext
      · simp only [pullback.lift_fst]
        rw [e0]
        have := congrArg (fun k ↦ k.left ≫ pullback.fst _ (genericInclusion R' K') ≫
          pullback.fst M.model.hom φ) he
        simp only [Over.pullback_map_left, pullback.lift_fst_assoc, Category.assoc] at this
        simp [flat, this]
      · simp
    have h1 : e₁.left ≫ pullback.fst M.model.hom φ = e₂.left ≫ pullback.fst M.model.hom φ :=
      congrArg Over.Hom.left hflat
    ext1
    apply pullback.hom_ext h1
    have w₁ := Over.w e₁
    have w₂ := Over.w e₂
    simp only [Over.pullback_obj_hom] at w₁ w₂
    rw [w₁, w₂]
  · let F := f.left
    have hf := Over.w f
    simp only [Over.pullback_obj_hom] at hf
    let u := F ≫ pullback.fst _ _ ≫ pullback.fst M.model.hom φ
    have hu : u ≫ M.model.hom =
        (pullback.snd Y'.hom (genericInclusion R' K') ≫ ψ) ≫ genericInclusion R K := by
      simp only [u, Category.assoc, pullback.condition, h.w]
      rw [← pullback.condition_assoc]
      simp only [Over.pullback_obj_hom, pullback.condition_assoc]
      rw [reassoc_of% hf]
    let g : (genericFunctor R K).obj Y ⟶ (genericFunctor R K).obj M.model :=
      Over.homMk (c.inv ≫ pullback.lift u _ hu) (by
        simp only [Over.pullback_obj_hom, Category.assoc, pullback.lift_snd]
        exact hP.isoPullback_inv_snd)
    obtain ⟨e₀, he₀⟩ := (M.bijective_map Y).2 g
    simp only at he₀
    have w₀ : e₀.left ≫ M.model.hom = Y'.hom ≫ φ := Over.w e₀
    have key : pullback.fst Y'.hom (genericInclusion R' K') ≫ e₀.left = u := by
      have := congrArg (fun k ↦ c.hom ≫ k.left ≫ pullback.fst M.model.hom (genericInclusion R K))
        he₀
      simp only [Over.pullback_map_left, pullback.lift_fst, g, Over.homMk_left,
        Category.assoc, Iso.hom_inv_id_assoc] at this
      rw [← this, ← Category.assoc]
      congr 1
      exact hP.isoPullback_hom_fst.symm
    refine ⟨Over.homMk (pullback.lift e₀.left Y'.hom w₀) (by simp), ?_⟩
    ext1
    simp only [Over.pullback_map_left]
    apply pullback.hom_ext
    · simp only [pullback.lift_fst]
      apply pullback.hom_ext
      · simpa [u, F] using key
      · simp only [Over.homMk_left, Category.assoc, pullback.lift_snd]
        simp only [Over.pullback_obj_hom, pullback.condition, reassoc_of% hf]
    · simpa using hf.symm


/-- **Étale base change of Néron models.** Let `φ : Spec R' ⟶ Spec R` be smooth (for instance
étale), with `ψ : Spec K' ⟶ Spec K` making the square of generic points a pullback, that is,
`K' = R' ⊗_R K`. If `M` is a Néron model of `A` over `R`, then its base change `M.model ×_R R'`,
with the identification of its generic fibre with `A ×_K K'` induced by that of `M`
(`genericBaseChangeIso`), is a Néron model of `A ×_K K'` over `R'`.

This is Lichtenstein, *Néron models*, Proposition 1.4.3 with its proof, pp. 5–6, stated there
for an integral domain `R'` étale over a Dedekind domain `R`; here `R'` is any domain with
fraction field `K'`, smoothness of `φ` replaces étaleness, and `A` is any `K`-scheme. -/
def baseChange (M : NeronModel R K A) : NeronModel R' K' ((Over.pullback ψ).obj A) :=
  have : IsSeparated ((Over.pullback φ).obj M.model).hom :=
    inferInstanceAs (IsSeparated (pullback.snd M.model.hom φ))
  have : LocallyOfFiniteType ((Over.pullback φ).obj M.model).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd M.model.hom φ))
  ofBijective ((Over.pullback φ).obj M.model)
    (genericBaseChangeIso R K R' K' φ ψ h.w M.model ≪≫ (Over.pullback ψ).mapIso M.genericIso)
    (fun Y' _ ↦ bijective_map_baseChange R K R' K' φ ψ h M Y')

/-- The model of `NeronModel.baseChange` is the base change of the model. -/
@[simp] theorem baseChange_model (M : NeronModel R K A) :
    (baseChange R K R' K' φ ψ h M).model = (Over.pullback φ).obj M.model := rfl

/-- The identification of the generic fibre of `NeronModel.baseChange` is the one induced by
`M.genericIso`. -/
theorem baseChange_genericIso (M : NeronModel R K A) :
    (baseChange R K R' K' φ ψ h M).genericIso =
      genericBaseChangeIso R K R' K' φ ψ h.w M.model ≪≫ (Over.pullback ψ).mapIso M.genericIso :=
  rfl

/-- Under the hypotheses of `NeronModel.baseChange`, the base-change morphism
`baseChangeMap` from `M.model ×_R R'` to any Néron model `N` of `A ×_K K'` over `R'` is an
isomorphism (Lichtenstein, *Néron models*, Propositions 1.4.2 (i) and 1.4.3, p. 5). -/
theorem isIso_baseChangeMap (M : NeronModel R K A)
    (N : NeronModel R' K' ((Over.pullback ψ).obj A)) :
    IsIso (baseChangeMap R K R' K' φ ψ h.w M N) := by
  have : baseChangeMap R K R' K' φ ψ h.w M N =
      (isoOfGeneric (baseChange R K R' K' φ ψ h M) N).hom := by
    simp only [baseChangeMap, isoOfGeneric, map, baseChange, ofBijective, Category.comp_id]
    rfl
  rw [this]
  exact Iso.isIso_hom _

end BaseChange

end NeronModel

end MathlibExt.AlgebraicGeometry.NeronModels
