/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModels

/-!
# General arithmetic interface probes

The residue comparison evaluates an actual global regular constant after
reducing the integral identity point on Spec R, for every local ring R.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.NeronModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels

variable (R : Type) [CommRing R] [IsLocalRing R]

def identityModel : Over (trait R) := Over.mk (𝟙 (trait R))

def reducedIdentity : SpecialPoint R (identityModel R) :=
  reducePoint R (identityModel R) ⟨𝟙 (trait R), by simp [identityModel]⟩

example (a : R) :
    (Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).hom.hom
      (((reducedIdentity R).1 ≫
        pullback.fst (identityModel R).hom (specialInclusion R)).appTop.hom
          ((Scheme.ΓSpecIso (.of R)).inv.hom a)) = IsLocalRing.residue R a := by
  have hp : (reducedIdentity R).1 ≫
      pullback.fst (identityModel R).hom (specialInclusion R) =
      specialInclusion R := by
    simp [reducedIdentity, reducePoint, identityModel]
  rw [hp]
  have h :
      (Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))).appTop ≫
          (Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).hom =
      CommRingCat.ofHom (IsLocalRing.residue R) := by
    rw [Scheme.ΓSpecIso_naturality, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  exact congrArg (fun f : CommRingCat.of R ⟶
    CommRingCat.of (IsLocalRing.ResidueField R) ↦ f.hom a) h

section Models

variable (R K : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A B : Over (Spec (.of K))}

-- Restriction to the generic fibre and unique extension are inverse.
example (N : NeronModel R K A) (Y : Over (trait R)) [Smooth Y.hom] (e : Y ⟶ N.model) :
    (N.homEquiv Y).symm (N.homEquiv Y e) = e :=
  (N.homEquiv Y).symm_apply_apply e

example (N : NeronModel R K A) (Y : Over (trait R)) [Smooth Y.hom]
    (f : (genericFunctor R K).obj Y ⟶ A) :
    (genericFunctor R K).map ((N.homEquiv Y).symm f) ≫ N.genericIso.hom = f :=
  N.extend_generic Y f

-- Extension of generic maps is functorial.
example (M : NeronModel R K A) : NeronModel.map M M (𝟙 A) = 𝟙 M.model :=
  NeronModel.map_id M

example (M : NeronModel R K A) (N : NeronModel R K B) (f : A ⟶ B) :
    NeronModel.map M N (f ≫ 𝟙 B) = NeronModel.map M N f ≫ NeronModel.map N N (𝟙 B) :=
  NeronModel.map_comp M N N f (𝟙 B)

-- A smooth separated model with the mapping property is a Néron model of its own generic
-- fibre, with the identity comparison.
example (M : Over (trait R)) [Smooth M.hom] [IsSeparated M.hom] [LocallyOfFiniteType M.hom]
    (h : HasMappingProperty R K M) : (ofMappingProperty R K M h).model = M :=
  rfl

-- Finite-type Néron models are Néron models.
example (N : FiniteTypeNeronModel R K A) : QuasiCompact N.model.hom := inferInstance

-- The pullback of a group object is a group object, so generic fibres of group models are
-- group schemes.
example (G : Over (trait R)) [GrpObj G] : GrpObj ((genericFunctor R K).obj G) := inferInstance

example (G : Over (trait R)) [GrpObj G] [IsCommMonObj G] :
    IsCommMonObj ((genericFunctor R K).obj G) := inferInstance

end Models

section BaseChange

variable (R K R' K' : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing R'] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
  (φ : trait R' ⟶ trait R) (ψ : Spec (.of K') ⟶ Spec (.of K))
  (sq : ψ ≫ genericInclusion R K = genericInclusion R' K' ≫ φ)
  {A : Over (Spec (.of K))}

-- An integral map whose generic restriction is the base-change comparison is the canonical
-- base-change map.
example (M : NeronModel R K A) (N : NeronModel R' K' ((Over.pullback ψ).obj A))
    (q : (Over.pullback φ).obj M.model ⟶ N.model)
    (hq : (genericFunctor R' K').map q ≫ N.genericIso.hom =
      (genericBaseChangeIso R K R' K' φ ψ sq M.model).hom ≫
        (Over.pullback ψ).map M.genericIso.hom) :
    q = baseChangeMap R K R' K' φ ψ sq M N := by
  apply (N.homEquiv _).injective
  exact hq.trans (baseChangeMap_generic R K R' K' φ ψ sq M N).symm

end BaseChange

end MathlibExtTest.AlgebraicGeometry.NeronModels
