/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.EqToHom

/-!
# Changing the coefficient category of a nerve-pullback bar

A functor between arbitrary coefficient categories that preserves the
required discrete coproducts gives the canonical comparison on each degree, on the
simplicial bar, and on its unnormalized alternating-face complex. The
comparison uses the inverse of the existing coproduct comparison and the
existing data/simplicial and alternating-complex comparison Isos.

The source category has independent object and Hom universes; the
simplicial and coproduct level is their maximum. Both coefficient
categories have independently sized objects and morphisms. No abelian,
exactness, flatness, local-system, connectedness, model-category, or fiber
hypothesis is used. Complex comparisons additionally require preadditivity
and an additive functor. The whole base-map square keeps the actual
original simplex-reindexing map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology AlgebraicTopology
open scoped Simplicial

universe uG vG vA vB uA uB

namespace CategoryTheory.CategoryHomology

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A] [HasCoproducts.{max uG vG} A]
variable {B : Type uB} [Category.{vB} B] [HasCoproducts.{max uG vG} B]
variable (F : A ⥤ B) [∀ I : Type (max uG vG), PreservesColimitsOfShape (Discrete I) F]
variable {T : SSet.{max uG vG}} (φ : T ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

/-- The actual preserved-coproduct comparison in each original degree. -/
public noncomputable def nervePullbackCoefficientDegreeChangeOfCategoryIso (n : ℕ) :
    F.obj (nervePullbackCoefficientObj φ M n) ≅
      nervePullbackCoefficientObj φ (M ⋙ F) n :=
  (asIso (sigmaComparison F (nervePullbackCoefficientFamily φ M n))).symm

/-- Every original coefficient summand follows the same target functor. -/
public theorem nervePullbackCoefficientDegreeChangeOfCategoryIso_ι (n : ℕ) (σ : T _⦋n⦌) :
    F.map (nervePullbackCoefficientι φ M σ) ≫ (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ
      M n).hom =
      nervePullbackCoefficientι φ (M ⋙ F) σ :=
  map_ι_comp_inv_sigmaComparison F (nervePullbackCoefficientFamily φ M n) σ

/-- Every changed-target summand maps through the SAME original injection under F. -/
public theorem nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι (n : ℕ) (σ : T _⦋n⦌) :
    nervePullbackCoefficientι φ (M ⋙ F) σ ≫ (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M
      n).inv =
      F.map (nervePullbackCoefficientι φ M σ) :=
  ι_comp_sigmaComparison F (nervePullbackCoefficientFamily φ M n) σ

omit [HasCoproducts.{max uG vG} A] [HasCoproducts.{max uG vG} B]
    [∀ I : Type (max uG vG), PreservesColimitsOfShape (Discrete I) F] in
/-- The actual endpoint transport and face coefficient commute with F. -/
private theorem faceHom_map {n : ℕ} (i : Fin (n + 2)) (σ : T _⦋n + 1⦌) :
    F.map (nervePullbackCoefficientFaceHom φ M i σ) =
      nervePullbackCoefficientFaceHom φ (M ⋙ F) i σ := by
  let c := φ.app (Opposite.op ⦋n + 1⦌) σ
  let h := nervePullback_face_index φ i σ
  change F.map (M.map (faceLeftHom i c) ≫ eqToHom (congrArg (fun c => M.obj c.left) h)) =
    F.map (M.map (faceLeftHom i c)) ≫ eqToHom (congrArg (fun c => F.obj (M.obj c.left)) h)
  exact (F.map_comp _ _).trans
    (congrArg (fun k => F.map (M.map (faceLeftHom i c)) ≫ k)
      (CategoryTheory.eqToHom_map F (congrArg (fun c => M.obj c.left) h)))

omit [HasCoproducts.{max uG vG} A] [HasCoproducts.{max uG vG} B]
    [∀ I : Type (max uG vG), PreservesColimitsOfShape (Discrete I) F] in
private theorem degeneracyHom_map {n : ℕ} (i : Fin (n + 1)) (σ : T _⦋n⦌) :
    F.map (nervePullbackCoefficientDegeneracyHom φ M i σ) =
      nervePullbackCoefficientDegeneracyHom φ (M ⋙ F) i σ := by
  let c := φ.app (Opposite.op ⦋n⦌) σ
  let h := nervePullback_degeneracy_index φ i σ
  change F.map (M.map (degeneracyLeftHom i c) ≫ eqToHom (congrArg (fun c => M.obj c.left) h)) =
    F.map (M.map (degeneracyLeftHom i c)) ≫ eqToHom (congrArg (fun c => F.obj (M.obj c.left)) h)
  exact (F.map_comp _ _).trans
    (congrArg (fun k => F.map (M.map (degeneracyLeftHom i c)) ≫ k)
      (CategoryTheory.eqToHom_map F (congrArg (fun c => M.obj c.left) h)))

/-- Naturality of the actual coproduct comparison with one actual face. -/
private theorem degreeIso_face {n : ℕ} (i : Fin (n + 2)) :
    (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M (n + 1)).hom ≫
      nervePullbackCoefficientFace φ (M ⋙ F) i =
      F.map (nervePullbackCoefficientFace φ M i) ≫
        (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n).hom
        := by
  let eH := nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M (n + 1)
  let eL := nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n
  let dA := nervePullbackCoefficientFace φ M i
  let dB := nervePullbackCoefficientFace φ (M ⋙ F) i
  have hc : eH.inv ≫ F.map dA = dB ≫ eL.inv := by
    apply nervePullbackCoefficient_hom_ext φ (M ⋙ F)
    intro σ
    let a := nervePullbackCoefficientι φ (M ⋙ F) σ
    let b := nervePullbackCoefficientι φ M σ
    let a' := nervePullbackCoefficientι φ (M ⋙ F) (T.δ i σ)
    let b' := nervePullbackCoefficientι φ M (T.δ i σ)
    let cA := nervePullbackCoefficientFaceHom φ M i σ
    let cB := nervePullbackCoefficientFaceHom φ (M ⋙ F) i σ
    have hi : a ≫ eH.inv = F.map b := nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι F φ M
      (n + 1) σ
    have hi' : a' ≫ eL.inv = F.map b' := nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι F φ
      M n (T.δ i σ)
    have hfA : b ≫ dA = cA ≫ b' := nervePullbackCoefficientι_face φ M i σ
    have hfB : a ≫ dB = cB ≫ a' := nervePullbackCoefficientι_face φ (M ⋙ F) i σ
    have hL : a ≫ (eH.inv ≫ F.map dA) = F.map cA ≫ F.map b' :=
      (Category.assoc a eH.inv (F.map dA)).symm.trans
        ((congrArg (fun h => h ≫ F.map dA) hi).trans
          ((F.map_comp b dA).symm.trans
            ((congrArg F.map hfA).trans (F.map_comp cA b'))))
    have hR : a ≫ (dB ≫ eL.inv) = F.map cA ≫ F.map b' :=
      (Category.assoc a dB eL.inv).symm.trans
        ((congrArg (fun h => h ≫ eL.inv) hfB).trans
          ((Category.assoc cB a' eL.inv).trans
            ((congrArg (fun h => cB ≫ h) hi').trans
              (congrArg (fun h => h ≫ F.map b') (faceHom_map F φ M i σ).symm))))
    exact hL.trans hR.symm
  have sq : CommSq eH.symm.hom dB (F.map dA) eL.symm.hom := ⟨hc⟩
  exact (CommSq.horiz_inv (f := eH.symm) (i := eL.symm) sq).w

/-- The same actual comparison commutes with each degeneracy. -/
private theorem degreeIso_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n).hom ≫
      nervePullbackCoefficientDegeneracy φ (M ⋙ F) i =
      F.map (nervePullbackCoefficientDegeneracy φ M i) ≫
        (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M (n + 1)).hom
        := by
  let eL := nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n
  let eH := nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M (n + 1)
  let sA := nervePullbackCoefficientDegeneracy φ M i
  let sB := nervePullbackCoefficientDegeneracy φ (M ⋙ F) i
  have hc : eL.inv ≫ F.map sA = sB ≫ eH.inv := by
    apply nervePullbackCoefficient_hom_ext φ (M ⋙ F)
    intro σ
    let a := nervePullbackCoefficientι φ (M ⋙ F) σ
    let b := nervePullbackCoefficientι φ M σ
    let a' := nervePullbackCoefficientι φ (M ⋙ F) (T.σ i σ)
    let b' := nervePullbackCoefficientι φ M (T.σ i σ)
    let cA := nervePullbackCoefficientDegeneracyHom φ M i σ
    let cB := nervePullbackCoefficientDegeneracyHom φ (M ⋙ F) i σ
    have hi : a ≫ eL.inv = F.map b := nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι F φ M
      n σ
    have hi' : a' ≫ eH.inv = F.map b' := nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι F φ
      M (n + 1) (T.σ i σ)
    have hsA : b ≫ sA = cA ≫ b' := nervePullbackCoefficientι_degeneracy φ M i σ
    have hsB : a ≫ sB = cB ≫ a' := nervePullbackCoefficientι_degeneracy φ (M ⋙ F) i σ
    have hL : a ≫ (eL.inv ≫ F.map sA) = F.map cA ≫ F.map b' :=
      (Category.assoc a eL.inv (F.map sA)).symm.trans
        ((congrArg (fun h => h ≫ F.map sA) hi).trans
          ((F.map_comp b sA).symm.trans
            ((congrArg F.map hsA).trans (F.map_comp cA b'))))
    have hR : a ≫ (sB ≫ eH.inv) = F.map cA ≫ F.map b' :=
      (Category.assoc a sB eH.inv).symm.trans
        ((congrArg (fun h => h ≫ eH.inv) hsB).trans
          ((Category.assoc cB a' eH.inv).trans
            ((congrArg (fun h => cB ≫ h) hi').trans
              (congrArg (fun h => h ≫ F.map b') (degeneracyHom_map F φ M i σ).symm))))
    exact hL.trans hR.symm
  have sq : CommSq eL.symm.hom sB (F.map sA) eH.symm.hom := ⟨hc⟩
  exact (CommSq.horiz_inv (f := eL.symm) (i := eH.symm) sq).w

/-- The existing data-Iso constructor assembles all the DERIVED degree squares. -/
private noncomputable def dataIso :
    SimplicialObject.Data.mapObj F (nervePullbackCoefficientData φ M) ≅
      nervePullbackCoefficientData φ (M ⋙ F) :=
  SimplicialObject.Data.isoOfIso (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M)
    (fun {_n} i => degreeIso_face F φ M i)
    (fun {_n} i => degreeIso_degeneracy F φ M i)

/-- Actual postcomposition and the same generic bar after changing target. -/
public noncomputable def nervePullbackCoefficientSimplicialChangeOfCategoryIso :
    (nervePullbackCoefficientSimplicial φ M ⋙ F) ≅
      nervePullbackCoefficientSimplicial φ (M ⋙ F) :=
  SimplicialObject.Data.toSimplicialObject_mapObjIso F (nervePullbackCoefficientData φ M) ≪≫
    (SimplicialObject.Data.toSimplicialFunctor (C := B)).mapIso (dataIso F φ M)


section ChainComplex

variable [Preadditive A] [Preadditive B] [F.Additive]

/-- The stock alternating-chain natural Iso carries the same actual bar
comparison; no homology-preservation assumption is used. -/
public noncomputable def nervePullbackCoefficientComplexChangeOfCategoryIso :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (nervePullbackCoefficientComplex φ M)) ≅
        nervePullbackCoefficientComplex φ (M ⋙ F) :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso F).app
      (nervePullbackCoefficientSimplicial φ M) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex B).mapIso
      (nervePullbackCoefficientSimplicialChangeOfCategoryIso F φ M)


/-- The SAME original degree comparison is the actual chain-Iso component. -/
public theorem nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f (n : ℕ) :
    (nervePullbackCoefficientComplexChangeOfCategoryIso F φ M).hom.f n =
      (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n).hom
      := by
  let D : SimplicialObject.Data A := nervePullbackCoefficientData φ M
  let D' : SimplicialObject.Data B := nervePullbackCoefficientData φ (M ⋙ F)
  let d : SimplicialObject.Data.mapObj F D ≅ D' := dataIso F φ M
  let c₀ : D.toSimplicialObject ⋙ F ≅
      (SimplicialObject.Data.mapObj F D).toSimplicialObject :=
    SimplicialObject.Data.toSimplicialObject_mapObjIso F D
  let c₁ : (SimplicialObject.Data.mapObj F D).toSimplicialObject ≅ D'.toSimplicialObject :=
    (SimplicialObject.Data.toSimplicialFunctor (C := B)).mapIso d
  let c : nervePullbackCoefficientSimplicial φ M ⋙ F ≅
      nervePullbackCoefficientSimplicial φ (M ⋙ F) :=
        nervePullbackCoefficientSimplicialChangeOfCategoryIso F φ M
  let e := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso F).app
    (nervePullbackCoefficientSimplicial φ M)
  have he : e.hom.f n = 𝟙 _ := rfl
  have hc : ((AlgebraicTopology.alternatingFaceMapComplex B).map c.hom).f n =
      c.hom.app (Opposite.op ⦋n⦌) :=
    AlgebraicTopology.alternatingFaceMapComplex_map_f c.hom n
  have hc₀ : c₀.hom.app (Opposite.op ⦋n⦌) = 𝟙 _ :=
    SimplicialObject.Data.toSimplicialObject_mapObjIso_hom_app_mk F D n
  have hc₁ : c₁.hom.app (Opposite.op ⦋n⦌) = d.hom.app n :=
    SimplicialObject.Data.toSimplicialFunctor_map_app_mk d.hom n
  let ε : ∀ k, (SimplicialObject.Data.mapObj F D).obj k ≅ D'.obj k :=
    nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M
  have hδ : ∀ {k : ℕ} (i : Fin (k + 2)),
      (ε (k + 1)).hom ≫ D'.δ i = (SimplicialObject.Data.mapObj F D).δ i ≫ (ε k).hom := by
    intro k i
    change (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M (k + 1)).hom ≫
      nervePullbackCoefficientFace φ (M ⋙ F) i =
      F.map (nervePullbackCoefficientFace φ M i) ≫
        (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M k).hom
    exact degreeIso_face F φ M i
  have hσ : ∀ {k : ℕ} (i : Fin (k + 1)),
      (ε k).hom ≫ D'.σ i = (SimplicialObject.Data.mapObj F D).σ i ≫ (ε (k + 1)).hom := by
    intro k i
    change (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M k).hom ≫
      nervePullbackCoefficientDegeneracy φ (M ⋙ F) i =
      F.map (nervePullbackCoefficientDegeneracy φ M i) ≫
        (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M (k + 1)).hom
    exact degreeIso_degeneracy F φ M i
  have hd : d.hom.app n = (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n).hom := by
    change (SimplicialObject.Data.isoOfIso ε hδ hσ).hom.app n = (ε n).hom
    exact SimplicialObject.Data.isoOfIso_hom_app
      (X := SimplicialObject.Data.mapObj F D) (Y := D') ε hδ hσ n
  have hcomp : c.hom.app (Opposite.op ⦋n⦌) =
      c₀.hom.app (Opposite.op ⦋n⦌) ≫ c₁.hom.app (Opposite.op ⦋n⦌) := rfl
  have hcomponent : c.hom.app (Opposite.op ⦋n⦌) = (nervePullbackCoefficientDegreeChangeOfCategoryIso
    F φ M n).hom :=
    hcomp.trans ((congrArg₂ (fun f g => f ≫ g) hc₀ hc₁).trans
      ((Category.id_comp _).trans hd))
  change e.hom.f n ≫ ((AlgebraicTopology.alternatingFaceMapComplex B).map c.hom).f n = _
  exact (congrArg (fun f => f ≫ ((AlgebraicTopology.alternatingFaceMapComplex B).map c.hom).f n)
    he).trans
    ((Category.id_comp _).trans (hc.trans hcomponent))

omit [Preadditive A] [Preadditive B] [F.Additive] in
/-- The actual coefficient comparison keeps the SAME whole base map. -/
private theorem degreeIso_base {U : SSet.{max uG vG}} (f : T ⟶ U)
    (ψ : U ⟶ CategoryTheory.nerve G) (n : ℕ) :
    F.map (nervePullbackCoefficientBaseMap f ψ M n) ≫
      (nervePullbackCoefficientDegreeChangeOfCategoryIso F ψ M n).hom =
      (nervePullbackCoefficientDegreeChangeOfCategoryIso F (f ≫ ψ) M n).hom ≫
        nervePullbackCoefficientBaseMap f ψ (M ⋙ F) n
        := by
  let eS := nervePullbackCoefficientDegreeChangeOfCategoryIso F (f ≫ ψ) M n
  let eT := nervePullbackCoefficientDegreeChangeOfCategoryIso F ψ M n
  let bA := nervePullbackCoefficientBaseMap f ψ M n
  let bB := nervePullbackCoefficientBaseMap f ψ (M ⋙ F) n
  have hc : bB ≫ eT.inv = eS.inv ≫ F.map bA := by
    apply nervePullbackCoefficient_hom_ext (f ≫ ψ) (M ⋙ F)
    intro σ
    let τ := f.app (Opposite.op ⦋n⦌) σ
    let a := nervePullbackCoefficientι (f ≫ ψ) (M ⋙ F) σ
    let b := nervePullbackCoefficientι (f ≫ ψ) M σ
    let a' := nervePullbackCoefficientι ψ (M ⋙ F) τ
    let b' := nervePullbackCoefficientι ψ M τ
    have hb : b ≫ bA = b' := nervePullbackCoefficientι_baseMap f ψ M σ
    have ha : a ≫ bB = a' := nervePullbackCoefficientι_baseMap f ψ (M ⋙ F) σ
    have hi : a ≫ eS.inv = F.map b := nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι F (f ≫
      ψ) M n σ
    have hi' : a' ≫ eT.inv = F.map b' := nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι F ψ
      M n τ
    have hL : a ≫ (bB ≫ eT.inv) = F.map b' :=
      (Category.assoc a bB eT.inv).symm.trans
        ((congrArg (fun h => h ≫ eT.inv) ha).trans hi')
    have hR : a ≫ (eS.inv ≫ F.map bA) = F.map b' :=
      (Category.assoc a eS.inv (F.map bA)).symm.trans
        ((congrArg (fun h => h ≫ F.map bA) hi).trans
          ((F.map_comp b bA).symm.trans (congrArg F.map hb)))
    exact hL.trans hR.symm
  have sq : CommSq bB eS.symm.hom eT.symm.hom (F.map bA) := ⟨hc⟩
  exact (CommSq.vert_inv (g := eS.symm) (h := eT.symm) sq).w

/-- The actual augmentation/base chain map commutes with the returned target
comparison in EVERY original degree, not only on homology. -/
public theorem nervePullbackCoefficientComplexChangeOfCategoryIso_base {U : SSet.{max uG vG}} (f : T
  ⟶ U)
    (ψ : U ⟶ CategoryTheory.nerve G) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (nervePullbackCoefficientBaseComplexMap f ψ M) ≫
        (nervePullbackCoefficientComplexChangeOfCategoryIso F ψ M).hom =
      (nervePullbackCoefficientComplexChangeOfCategoryIso F (f ≫ ψ) M).hom ≫
        nervePullbackCoefficientBaseComplexMap f ψ (M ⋙ F) := by
  ext n
  change F.map ((nervePullbackCoefficientBaseComplexMap f ψ M).f n) ≫
      (nervePullbackCoefficientComplexChangeOfCategoryIso F ψ M).hom.f n =
    (nervePullbackCoefficientComplexChangeOfCategoryIso F (f ≫ ψ) M).hom.f n ≫
      (nervePullbackCoefficientBaseComplexMap f ψ (M ⋙ F)).f n
  rw [nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f,
    nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f,
    nervePullbackCoefficientBaseComplexMap_f,
    nervePullbackCoefficientBaseComplexMap_f]
  exact degreeIso_base F M f ψ n

end ChainComplex

end CategoryTheory.CategoryHomology

end
