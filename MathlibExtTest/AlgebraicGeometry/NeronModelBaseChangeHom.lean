/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModelBaseChangeHom

/-!
# Tests for the canonical morphism of Néron models under base change

For an abelian variety over a number field `L` and an extension `L'/L` of number fields, the
canonical morphism from the base change of the Néron model over `𝓞_L` to the Néron model over
`𝓞_{L'}` is unique and is a homomorphism for the Néron group laws.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.NeronModelBaseChangeHom

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels
open scoped CategoryTheory.Obj
open NumberField

universe u

section NumberField

variable {L L' : Type u} [Field L] [Field L'] [NumberField L] [NumberField L'] [Algebra L L']
  (A : AbelianScheme (Spec (.of L))) (M : NeronModel (𝓞 L) L A.model)
  (N : NeronModel (𝓞 L') L' ((Over.pullback (NeronModel.fieldSpecMap L L')).obj A.model))

/-- The canonical morphism for an abelian variety over a number field is unique. -/
example : ∃! e : (Over.pullback (NeronModel.ringOfIntegersSpecMap L L')).obj M.model ⟶ N.model,
    (genericFunctor (𝓞 L') L').map e ≫ N.genericIso.hom =
      (genericBaseChangeIso (𝓞 L) L (𝓞 L') L' _ _
          (NeronModel.fieldSpecMap_comp_genericInclusion L L') M.model).hom ≫
        (Over.pullback (NeronModel.fieldSpecMap L L')).map M.genericIso.hom :=
  NeronModel.existsUnique_baseChangeMap_ringOfIntegers M N

/-- The canonical morphism for an abelian variety over a number field is a homomorphism for the
Néron group laws. -/
example :
    letI := M.groupStructure
    letI := N.groupStructure
    IsMonHom (baseChangeMap (𝓞 L) L (𝓞 L') L' _ _
      (NeronModel.fieldSpecMap_comp_genericInclusion L L') M N) :=
  letI := M.groupStructure
  letI := N.groupStructure
  NeronModel.isMonHom_baseChangeMap_ringOfIntegers M N

end NumberField

section General

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (R' : Type u) [CommRing R'] (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
  (φ : trait R' ⟶ trait R) (ψ : Spec (.of K') ⟶ Spec (.of K))
  (sq : ψ ≫ genericInclusion R K = genericInclusion R' K' ≫ φ)
  {A : Over (Spec (.of K))} [GrpObj A] (M : NeronModel R K A)
  (N : NeronModel R' K' ((Over.pullback ψ).obj A))

/-- With the group laws `NeronModel.grpObj`, the canonical morphism is a homomorphism. -/
example :
    letI := M.grpObj
    letI := N.grpObj
    IsMonHom (baseChangeMap R K R' K' φ ψ sq M N) :=
  NeronModel.isMonHom_baseChangeMap R K R' K' φ ψ sq M N M.grpObj M.isMonHom_genericIso_grpObj
    N.grpObj N.isMonHom_genericIso_grpObj

/-- Any morphism with the generic property of `baseChangeMap_generic` is `baseChangeMap`. -/
example (e : (Over.pullback φ).obj M.model ⟶ N.model)
    (he : (genericFunctor R' K').map e ≫ N.genericIso.hom =
      (genericBaseChangeIso R K R' K' φ ψ sq M.model).hom ≫
        (Over.pullback ψ).map M.genericIso.hom) :
    e = baseChangeMap R K R' K' φ ψ sq M N :=
  (NeronModel.existsUnique_baseChangeMap R K R' K' φ ψ sq M N).unique he
    (baseChangeMap_generic R K R' K' φ ψ sq M N)

/-- The generic comparison is a homomorphism of group objects. -/
example :
    letI := M.grpObj
    IsMonHom (genericBaseChangeIso R K R' K' φ ψ sq M.model).hom :=
  letI := M.grpObj
  inferInstance

end General

#check @NeronModel.isMonHom_of_isMonHom_map
#check @NeronModel.genericBaseChangeIso_hom_naturality
#check @NeronModel.isMonHom_genericBaseChangeIso
#check @NeronModel.existsUnique_baseChangeMap
#check @NeronModel.isMonHom_baseChangeMap
#check @NeronModel.isMonHom_baseChangeMap_of_groupStructure
#check @NeronModel.ringOfIntegersSpecMap
#check @NeronModel.fieldSpecMap
#check @NeronModel.fieldSpecMap_comp_genericInclusion
#check @NeronModel.existsUnique_baseChangeMap_ringOfIntegers
#check @NeronModel.isMonHom_baseChangeMap_ringOfIntegers

end MathlibExtTest.AlgebraicGeometry.NeronModelBaseChangeHom
