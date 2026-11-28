/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.NeronModelGroupLaw
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# The canonical morphism of Néron models under base change

Let `R ⟶ R'` be a map of domains with fraction fields `K ⟶ K'`, presented by morphisms
`φ : Spec R' ⟶ Spec R` and `ψ : Spec K' ⟶ Spec K` with commuting square of generic points. For a
Néron model `M` of a `K`-scheme `A` over `R` and a Néron model `N` of `A ×_K K'` over `R'`, the
canonical morphism `baseChangeMap : M.model ×_R R' ⟶ N.model` is the extension of the identity of
`A ×_K K'` on generic fibres. This file proves:

* `NeronModel.existsUnique_baseChangeMap`: it is the unique such `R'`-morphism;
* `NeronModel.isMonHom_baseChangeMap`, `NeronModel.isMonHom_baseChangeMap_of_groupStructure`: for
  a group object `A` and group laws on the models extending those of `A` and `A ×_K K'`, it is a
  homomorphism of group objects, `M.model ×_R R'` carrying the group law transported by the
  pullback functor (`Functor.grpObjObj`, available under `open scoped CategoryTheory.Obj`);
* `NeronModel.existsUnique_baseChangeMap_ringOfIntegers`,
  `NeronModel.isMonHom_baseChangeMap_ringOfIntegers`: the case `R = 𝓞_L`, `R' = 𝓞_{L'}` for
  number fields `L ⊆ L'`.

Auxiliary results: `NeronModel.isMonHom_of_isMonHom_map` (a morphism from a smooth group object
into a Néron model is a homomorphism as soon as its generic fibre is one) and the instance
`NeronModel.isMonHom_genericBaseChangeIso` (the generic comparison `genericBaseChangeIso` is a
homomorphism for the transported group laws).

Not formalized here: the statement that pullback along the canonical morphism on
`ω = ε^*Ω^g` is injective with finite cokernel; Mathlib has no sheaf of relative differentials
of a morphism of schemes.

References: C.-L. Chai, *Néron models for semiabelian varieties: congruence and change of base
field*, Asian J. Math. 4 (2000), no. 4, §1, p. 715 (the canonical homomorphism `can_{A,M/K}`
from the base change of the Néron model to the Néron model of the base change, extending the
natural isomorphism of generic fibres, over a henselian discrete valuation ring with perfect
residue field); P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch*, Séminaire
Bourbaki exp. 616 (1983/84), Astérisque 121–122 (1985), Remarque after 1.2, p. 27 (the map from
the base change of the Néron model over the ring of integers of a number field to the Néron
model over a finite extension).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NeronModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SemistableModels
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj CategoryTheory.Obj

universe u

namespace NeronModel

section Reflect

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Spec (.of K))} (N : NeronModel R K A)

/-- Let `N` be a Néron model over `R` whose model carries a group object structure, `T` a smooth
`R`-scheme with a group object structure and `f : T ⟶ N.model`. If the generic fibre of `f` is a
homomorphism of group objects (generic fibres carrying the group laws transported by the generic
fibre functor), then so is `f`. Morphisms from smooth `R`-schemes into a Néron model are
determined by their generic fibres (`NeronModel.map_injective`). -/
theorem isMonHom_of_isMonHom_map [GrpObj N.model] {T : Over (trait R)} [Smooth T.hom]
    [GrpObj T] (f : T ⟶ N.model) (h : IsMonHom ((genericFunctor R K).map f)) :
    IsMonHom f where
  one_hom := N.map_injective <| by
    have h1 := h.one_hom
    simp only [Functor.obj.η_def, Category.assoc] at h1
    rw [Functor.map_comp]
    exact (cancel_epi _).1 h1
  mul_hom := N.map_injective <| by
    have h1 := h.mul_hom
    simp only [Functor.obj.μ_def, Category.assoc, μ_natural_assoc] at h1
    rw [Functor.map_comp, Functor.map_comp]
    exact (cancel_epi _).1 h1

end Reflect

section BaseChange

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (R' : Type u) [CommRing R'] (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
  (φ : trait R' ⟶ trait R) (ψ : Spec (.of K') ⟶ Spec (.of K))
  (sq : ψ ≫ genericInclusion R K = genericInclusion R' K' ≫ φ)

@[reassoc]
private lemma eqToHom_pullback_naturality {S T : Scheme.{u}} {a b : S ⟶ T} (h : a = b)
    {M₁ M₂ : Over T} (g : M₁ ⟶ M₂) :
    (Over.pullback a).map g ≫ eqToHom (congrArg (fun f ↦ (Over.pullback f).obj M₂) h) =
      eqToHom (congrArg (fun f ↦ (Over.pullback f).obj M₁) h) ≫ (Over.pullback b).map g := by
  subst h
  simp

/-- The generic comparison `genericBaseChangeIso`, from the generic fibre of the base change to
the base change of the generic fibre, is natural in the `R`-scheme. -/
@[reassoc]
theorem genericBaseChangeIso_hom_naturality {M₁ M₂ : Over (trait R)} (g : M₁ ⟶ M₂) :
    (genericFunctor R' K').map ((Over.pullback φ).map g) ≫
        (genericBaseChangeIso R K R' K' φ ψ sq M₂).hom =
      (genericBaseChangeIso R K R' K' φ ψ sq M₁).hom ≫
        (Over.pullback ψ).map ((genericFunctor R K).map g) := by
  simp only [genericBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    eqToIso.hom]
  have n1 := (Over.pullbackComp (genericInclusion R' K') φ).inv.naturality g
  have n3 := (Over.pullbackComp ψ (genericInclusion R K)).hom.naturality g
  simp only [Functor.comp_map] at n1 n3
  rw [reassoc_of% n1, eqToHom_pullback_naturality_assoc sq.symm g, n3]
  simp only [Category.assoc]

private lemma genericBaseChangeIso_δ (M₁ M₂ : Over (trait R)) :
    (genericBaseChangeIso R K R' K' φ ψ sq (M₁ ⊗ M₂)).hom ≫
        (Over.pullback ψ).map (δ (genericFunctor R K) M₁ M₂) ≫ δ (Over.pullback ψ) _ _ =
      (genericFunctor R' K').map (δ (Over.pullback φ) M₁ M₂) ≫ δ (genericFunctor R' K') _ _ ≫
        ((genericBaseChangeIso R K R' K' φ ψ sq M₁).hom ⊗ₘ
          (genericBaseChangeIso R K R' K' φ ψ sq M₂).hom) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, δ_fst, δ_fst_assoc, tensorHom_fst, ← Functor.map_comp_assoc,
      ← Functor.map_comp]
    exact (genericBaseChangeIso_hom_naturality R K R' K' φ ψ sq _).symm
  · simp only [Category.assoc, δ_snd, δ_snd_assoc, tensorHom_snd, ← Functor.map_comp_assoc,
      ← Functor.map_comp]
    exact (genericBaseChangeIso_hom_naturality R K R' K' φ ψ sq _).symm

/-- For a group object `M` over `Spec R`, the generic comparison `genericBaseChangeIso`, from the
generic fibre of `M ×_R R'` to `(generic fibre of M) ×_K K'`, is a homomorphism of group objects,
both sides carrying the group laws transported along the pullback functors. -/
instance isMonHom_genericBaseChangeIso (M : Over (trait R)) [GrpObj M] :
    IsMonHom (genericBaseChangeIso R K R' K' φ ψ sq M).hom where
  one_hom := by
    have key : ε (genericFunctor R' K') ≫ (genericFunctor R' K').map (ε (Over.pullback φ)) ≫
        (genericBaseChangeIso R K R' K' φ ψ sq (𝟙_ _)).hom =
        ε (Over.pullback ψ) ≫ (Over.pullback ψ).map (ε (genericFunctor R K)) := by
      rw [← cancel_mono ((Over.pullback ψ).map («η» (genericFunctor R K)) ≫
        «η» (Over.pullback ψ))]
      exact toUnit_unique _ _
    simp only [Functor.obj.η_def, Category.assoc, Functor.map_comp,
      genericBaseChangeIso_hom_naturality]
    rw [reassoc_of% key]
  mul_hom := by
    have key : «μ» (genericFunctor R' K') _ _ ≫
        (genericFunctor R' K').map («μ» (Over.pullback φ) M M) ≫
        (genericBaseChangeIso R K R' K' φ ψ sq (M ⊗ M)).hom =
        ((genericBaseChangeIso R K R' K' φ ψ sq M).hom ⊗ₘ
          (genericBaseChangeIso R K R' K' φ ψ sq M).hom) ≫
          «μ» (Over.pullback ψ) _ _ ≫ (Over.pullback ψ).map («μ» (genericFunctor R K) M M) := by
      rw [← cancel_mono ((Over.pullback ψ).map (δ (genericFunctor R K) M M) ≫
        δ (Over.pullback ψ) _ _), Category.assoc, Category.assoc, genericBaseChangeIso_δ]
      simp [← Functor.map_comp_assoc]
    simp only [Functor.obj.μ_def, Category.assoc, Functor.map_comp,
      genericBaseChangeIso_hom_naturality]
    rw [reassoc_of% key]

variable {A : Over (Spec (.of K))}

/-- **Uniqueness of the canonical morphism.** Let `φ : Spec R' ⟶ Spec R` and
`ψ : Spec K' ⟶ Spec K` commute with the generic points, `A` a `K`-scheme, `M` a Néron model of `A`
over `R` and `N` a Néron model of `A ×_K K'` over `R'`. There is exactly one `R'`-morphism
`e : M.model ×_R R' ⟶ N.model` whose generic fibre is the identity of `A ×_K K'`, that is,
`e_{K'}` followed by `N.genericIso` equals `genericBaseChangeIso` followed by the base change of
`M.genericIso`; `baseChangeMap` is such a morphism (`baseChangeMap_generic`).

This is the uniqueness in the characterization of the canonical morphism in Chai, *Néron models
for semiabelian varieties: congruence and change of base field*, §1, p. 715, there over a
henselian discrete valuation ring with perfect residue field and for an abelian variety `A`;
here `R`, `R'` are any domains, the extension need not be finite, `A` is any `K`-scheme and
Néron models are locally of finite type (`NeronModel`). -/
theorem existsUnique_baseChangeMap (M : NeronModel R K A)
    (N : NeronModel R' K' ((Over.pullback ψ).obj A)) :
    ∃! e : (Over.pullback φ).obj M.model ⟶ N.model,
      (genericFunctor R' K').map e ≫ N.genericIso.hom =
        (genericBaseChangeIso R K R' K' φ ψ sq M.model).hom ≫
          (Over.pullback ψ).map M.genericIso.hom :=
  ⟨baseChangeMap R K R' K' φ ψ sq M N, baseChangeMap_generic R K R' K' φ ψ sq M N,
    fun _ he ↦ (N.homEquiv _).injective
      (he.trans (baseChangeMap_generic R K R' K' φ ψ sq M N).symm)⟩

/-- **The canonical morphism is a homomorphism.** Let `A` be a group object over `Spec K`, `M` a
Néron model of `A` over `R` and `N` a Néron model of `A ×_K K'` over `R'`, with group object
structures `gM` on `M.model` and `gN` on `N.model` for which `M.genericIso` and `N.genericIso`
are homomorphisms (`A ×_K K'` carrying the group law transported by pullback). Give
`M.model ×_R R'` the group law transported along the pullback functor (`Functor.grpObjObj`).
Then `baseChangeMap` is a homomorphism of group objects.

This is the statement that the canonical morphism `can_{A,M/K}` is a homomorphism, Chai, *Néron
models for semiabelian varieties: congruence and change of base field*, §1, p. 715, there over a
henselian discrete valuation ring with perfect residue field and for an abelian variety; here
`R`, `R'` are any domains, the extension need not be finite and `A` need not be commutative. -/
theorem isMonHom_baseChangeMap [GrpObj A] (M : NeronModel R K A)
    (N : NeronModel R' K' ((Over.pullback ψ).obj A)) (gM : GrpObj M.model)
    (hM : letI := gM; IsMonHom M.genericIso.hom) (gN : GrpObj N.model)
    (hN : letI := gN; IsMonHom N.genericIso.hom) :
    letI := gM; letI := gN
    IsMonHom (baseChangeMap R K R' K' φ ψ sq M N) := by
  let := gM; let := gN
  have : IsMonHom M.genericIso.hom := hM
  have : IsMonHom N.genericIso.hom := hN
  apply N.isMonHom_of_isMonHom_map
  have e : (genericFunctor R' K').map (baseChangeMap R K R' K' φ ψ sq M N) =
      (genericBaseChangeIso R K R' K' φ ψ sq M.model).hom ≫
        (Over.pullback ψ).map M.genericIso.hom ≫ N.genericIso.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact baseChangeMap_generic R K R' K' φ ψ sq M N
  rw [e]
  have h1 : IsMonHom (genericBaseChangeIso R K R' K' φ ψ sq M.model).hom := inferInstance
  have h2 : IsMonHom ((Over.pullback ψ).map M.genericIso.hom) := inferInstance
  have h3 : IsMonHom N.genericIso.inv := inferInstance
  have h23 := @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h2 h3
  exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 h23

/-- **The canonical morphism of Néron models with their group laws.** For a commutative group
object `A` over `Spec K` and Néron models `M` of `A` over `R`, `N` of `A ×_K K'` over `R'`, each
with a `NeronModel.GroupStructure` (for instance `NeronModel.groupStructure`, the only one up to
equality of group laws by `NeronModel.groupStructure_unique`), `baseChangeMap` is a homomorphism
from `M.model ×_R R'`, with the group law transported by pullback, to `N.model`
(Chai, *Néron models for semiabelian varieties: congruence and change of base field*, §1,
p. 715; see `NeronModel.isMonHom_baseChangeMap`). -/
theorem isMonHom_baseChangeMap_of_groupStructure [GrpObj A] [IsCommMonObj A]
    (M : NeronModel R K A) (N : NeronModel R' K' ((Over.pullback ψ).obj A))
    [M.GroupStructure] [N.GroupStructure] :
    IsMonHom (baseChangeMap R K R' K' φ ψ sq M N) :=
  isMonHom_baseChangeMap R K R' K' φ ψ sq M N _ GroupStructure.compatible _
    GroupStructure.compatible

end BaseChange

section NumberField

open _root_.NumberField

variable (L L' : Type u) [Field L] [Field L'] [NumberField L] [NumberField L'] [Algebra L L']

/-- The morphism `Spec 𝓞_{L'} ⟶ Spec 𝓞_L` induced by the inclusion `𝓞_L ⊆ 𝓞_{L'}`. -/
abbrev ringOfIntegersSpecMap : trait (𝓞 L') ⟶ trait (𝓞 L) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))

/-- The morphism `Spec L' ⟶ Spec L` induced by the field extension `L ⊆ L'`. -/
abbrev fieldSpecMap : Spec (.of L') ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L L'))

/-- The square of generic points for the extension `𝓞_L ⟶ 𝓞_{L'}` of rings of integers
commutes. -/
theorem fieldSpecMap_comp_genericInclusion :
    fieldSpecMap L L' ≫ genericInclusion (𝓞 L) L =
      genericInclusion (𝓞 L') L' ≫ ringOfIntegersSpecMap L L' := by
  simp only [genericInclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

variable {L L'} {A : Over (Spec (.of L))}

/-- **The canonical morphism for an extension of number fields, uniqueness.** For number fields
`L` and `L'` with an `L`-algebra structure on `L'` (so `L'/L` is finite), an `L`-scheme `A`, a
Néron model `M` of `A` over `𝓞_L` and a Néron model `N` of `A ×_L L'` over `𝓞_{L'}`, there is
exactly one `𝓞_{L'}`-morphism `M.model ×_{𝓞_L} 𝓞_{L'} ⟶ N.model` that is the identity of
`A ×_L L'` on generic fibres (read through `genericBaseChangeIso`, `M.genericIso` and
`N.genericIso`); `baseChangeMap` is one.

This is the uniqueness of the map in Deligne, *Preuve des conjectures de Tate et de
Shafarevitch*, Séminaire Bourbaki exp. 616, Remarque after 1.2, p. 27; `A` need not be an
abelian variety. -/
theorem existsUnique_baseChangeMap_ringOfIntegers (M : NeronModel (𝓞 L) L A)
    (N : NeronModel (𝓞 L') L' ((Over.pullback (fieldSpecMap L L')).obj A)) :
    ∃! e : (Over.pullback (ringOfIntegersSpecMap L L')).obj M.model ⟶ N.model,
      (genericFunctor (𝓞 L') L').map e ≫ N.genericIso.hom =
        (genericBaseChangeIso (𝓞 L) L (𝓞 L') L' _ _
            (fieldSpecMap_comp_genericInclusion L L') M.model).hom ≫
          (Over.pullback (fieldSpecMap L L')).map M.genericIso.hom :=
  existsUnique_baseChangeMap _ _ _ _ _ _ _ M N

/-- **The canonical morphism for an extension of number fields is a homomorphism.** For number
fields `L` and `L'` with an `L`-algebra structure on `L'`, a commutative group object `A` over
`Spec L` and Néron models `M` of `A` over `𝓞_L` and `N` of `A ×_L L'` over `𝓞_{L'}`, each with a
`NeronModel.GroupStructure`, `baseChangeMap : M.model ×_{𝓞_L} 𝓞_{L'} ⟶ N.model` is a
homomorphism of group objects, the source carrying the group law transported by pullback
(Deligne, *Preuve des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki exp. 616,
Remarque after 1.2, p. 27; Chai, *Néron models for semiabelian varieties: congruence and change
of base field*, §1, p. 715). -/
theorem isMonHom_baseChangeMap_ringOfIntegers [GrpObj A] [IsCommMonObj A]
    (M : NeronModel (𝓞 L) L A)
    (N : NeronModel (𝓞 L') L' ((Over.pullback (fieldSpecMap L L')).obj A))
    [M.GroupStructure] [N.GroupStructure] :
    IsMonHom (baseChangeMap (𝓞 L) L (𝓞 L') L' _ _
      (fieldSpecMap_comp_genericInclusion L L') M N) :=
  isMonHom_baseChangeMap_of_groupStructure _ _ _ _ _ _ _ M N

end NumberField

end NeronModel

end MathlibExt.AlgebraicGeometry.NeronModels
