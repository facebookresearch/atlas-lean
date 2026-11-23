/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.StabilizedFunctorRawMap
public import MathlibExt.KTheory.Exact.Extension.MapLeftSumTargetCoherence
public import MathlibExt.KTheory.Exact.Quillen.Functor

/-!
# Original given-quotient objects under the actual stabilized extension functor

Every original localized extension object retains its given quotient
image. The positive extension and denominator remain in their original
order. The object equation below is a computation of the actual two
functors; no target square or component restriction is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]


private theorem originalExtensionMapHEq
    {A B A' B' : ExtensionCategory D} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) :
    HEq ((target (C := D)).map a) ((target (C := D)).map b) := by
  cases hA
  cases hB
  cases h
  exact HEq.rfl

private theorem originalLocalizedMapHEq
    {A B A' B' : SInverse (Core D) (ExtensionCategory D)}
    (hA : A = A') (hB : B = B') {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) :
    HEq ((localizedTarget (C := D)).map a) ((localizedTarget (C := D)).map b) := by
  cases hA
  cases hB
  cases h
  exact HEq.rfl

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalStabilizedTargetObjectImage
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (localizedTarget (C := D)).obj ((stabilizedFunctorMap F).obj a) =
      (⟨F.obj a.of.1.row.X₃⟩ : QuillenQ D) := by
  have hRow : ((stabilizedFunctorMap F).obj a).of.1.row.X₃ = F.obj a.of.1.row.X₃ :=
    (congrArg (fun A : SInverse (Core D) (ExtensionCategory D) => A.of.1.row.X₃)
      (stabilizedFunctorMap_obj F a)).trans
      ((congrArg (fun p : ExtensionCategory D × Core D => p.1.row.X₃)
        (stabilizedFunctorObject_of F a)).trans
        ((congrArg (fun E : ExtensionCategory D => E.row.X₃) (mapFunctor_obj F a.of.1)).trans
          (mapObject_components F a.of.1).2.2))
  exact (localizedTarget_obj ((stabilizedFunctorMap F).obj a)).trans
    (congrArg (fun X : D => (⟨X⟩ : QuillenQ D)) hRow)

private theorem originalQuillenTargetObjectImage
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (QuillenQ.map F).obj ((localizedTarget (C := C)).obj a) =
      (⟨F.obj a.of.1.row.X₃⟩ : QuillenQ D) :=
  (congrArg (QuillenQ.map F).obj (localizedTarget_obj a)).trans (by rfl)

/-- Every original localized given quotient has the actual Quillen image object. -/
public theorem stabilizedFunctorMap_target_obj
    (a : SInverse (Core C) (ExtensionCategory C)) :
    (localizedTarget (C := D)).obj ((stabilizedFunctorMap F).obj a) =
      (QuillenQ.map F).obj ((localizedTarget (C := C)).obj a) :=
  (originalStabilizedTargetObjectImage F a).trans (originalQuillenTargetObjectImage F a).symm


private theorem originalMappedQuotientTarget (E : ExtensionCategory C) :
    (target (C := D)).obj ((mapFunctor F).obj E) =
      (⟨F.obj E.row.X₃⟩ : QuillenQ D) :=
  (target_obj ((mapFunctor F).obj E)).trans
    (congrArg (fun X : D => (⟨X⟩ : QuillenQ D))
      ((congrArg (fun A : ExtensionCategory D => A.row.X₃) (mapFunctor_obj F E)).trans
        (mapObject_components F E).2.2))

private theorem originalMappedRawTarget
    {a b : SInverse (Core C) (ExtensionCategory C)}
    (r : MonoidalActionCategory.RawHom a b) :
    HEq ((localizedTarget (C := D)).map
      (MonoidalActionCategory.Hom.mk (stabilizedFunctorRawMap F r)))
      ((QuillenQ.map F).map ((localizedTarget (C := C)).map (MonoidalActionCategory.Hom.mk r))) :=
by
  let G := mapFunctor F
  let TD := target (C := D)
  let TC := target (C := C)
  let Q := QuillenQ.map F
  let E := a.of.1
  let E' := b.of.1
  let U := stabilizedFunctorObject F a
  let V := stabilizedFunctorObject F b
  let m := stabilizedFunctorRawMap F r
  let A := leftSumObj (F.core.obj r.stabilizer) (G.obj E)
  let B := G.obj (leftSumObj r.stabilizer E)
  let Z := G.obj E'
  let θ : B ≅ A := (mapLeftSumNaturalityIso F).app (r.stabilizer, E)
  let g : B ⟶ Z := G.map r.hom.1
  let R : (⟨F.obj E.row.X₃⟩ : QuillenQ D) ⟶ ⟨F.obj E'.row.X₃⟩ :=
    Q.map (TC.map r.hom.1)
  have hA : (m.stabilizer ⊙ₗ U.of).1 = A :=
    congrArg₂ (fun (T : Core D) (p : ExtensionCategory D × Core D) => (T ⊙ₗ p).1)
      (stabilizedFunctorRawMap_components F r).1 (stabilizedFunctorObject_of F a)
  have hZ : V.of.1 = Z := congrArg Prod.fst (stabilizedFunctorObject_of F b)
  have hRecipe : HEq m.hom.1 (θ.inv ≫ g) := (stabilizedFunctorRawMap_components F r).2.1
  have hDirect : (localizedTarget (C := D)).map (MonoidalActionCategory.Hom.mk m) =
      TD.map m.hom.1 := localizedTargetMap_mk m
  have hImage := originalExtensionMapHEq hA hZ hRecipe
  have hComp : TD.map (θ.inv ≫ g) = TD.map θ.inv ≫ TD.map g := TD.map_comp θ.inv g
  have hDom : TD.obj A = (⟨F.obj E.row.X₃⟩ : QuillenQ D) :=
    (leftSumObj_target (F.core.obj r.stabilizer) (G.obj E)).trans
      (originalMappedQuotientTarget F E)
  have hMid : TD.obj B = (⟨F.obj E.row.X₃⟩ : QuillenQ D) :=
    originalMappedQuotientTarget F (leftSumObj r.stabilizer E)
  have hCod : TD.obj Z = (⟨F.obj E'.row.X₃⟩ : QuillenQ D) :=
    originalMappedQuotientTarget F E'
  have hθ : HEq (TD.map θ.inv) (𝟙 (⟨F.obj E.row.X₃⟩ : QuillenQ D)) :=
    mapLeftSumNaturalityIso_target_inv_heq F r.stabilizer E
  have hg : HEq (TD.map g) R := Functor.hcongr_hom (mapFunctor_target F) r.hom.1
  have hProduct := heq_comp hDom hMid hCod hθ hg
  have hRight : Q.map ((localizedTarget (C := C)).map (MonoidalActionCategory.Hom.mk r)) = R :=
    congrArg (fun f : (⟨E.row.X₃⟩ : QuillenQ C) ⟶ ⟨E'.row.X₃⟩ => Q.map f)
      (localizedTargetMap_mk r)
  exact (heq_of_eq hDirect).trans (hImage.trans ((heq_of_eq hComp).trans
    (hProduct.trans ((heq_of_eq (Category.id_comp R)).trans (heq_of_eq hRight.symm)))))

private theorem originalStabilizedTargetSquareComputed :
    stabilizedFunctorMap F ⋙ localizedTarget (C := D) =
      localizedTarget (C := C) ⋙ QuillenQ.map F := by
  let L := stabilizedFunctorMap F ⋙ localizedTarget (C := D)
  let R := localizedTarget (C := C) ⋙ QuillenQ.map F
  have hObj (a : SInverse (Core C) (ExtensionCategory C)) : L.obj a = R.obj a :=
    stabilizedFunctorMap_target_obj F a
  refine Functor.hext hObj ?_
  intro a b f
  refine Quotient.inductionOn f ?_
  intro r
  have h := originalLocalizedMapHEq (stabilizedFunctorMap_obj F a)
    (stabilizedFunctorMap_obj F b) (stabilizedFunctorMap_mkHom_heq F r)
  exact h.trans (originalMappedRawTarget F r)

/-- The actual localized extension functor lies over the original Quillen exact-functor map. -/
public theorem stabilizedFunctorMap_target :
    stabilizedFunctorMap F ⋙ localizedTarget (C := D) =
      localizedTarget (C := C) ⋙ QuillenQ.map F :=
  originalStabilizedTargetSquareComputed F

end AlgebraicKTheory.ExtensionCategory

end
