/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorRestriction

/-!
# Coefficient naturality of base-change tensor cancellation

For a commutative algebra R → S, the comparison M ⊗_S (S ⊗_R L) ≅ M ⊗_R L is natural in both
the S-coefficient M and the R-input L. At input carrier height max(w,v), these comparisons
form an isomorphism of coefficient-to-input functors with output height max(w,t,v).

Precomposing the input with any R-module diagram X gives a coefficient-natural diagram
isomorphism. Its component at a diagram object is the same base-change cancellation map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct

universe u w t v

namespace ModuleCat.TensorRestriction

variable (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]

/-- The tensor bifunctor with an extended R-input.

Send an S-module M and R-module L to M ⊗_S (S ⊗_R L), at the stated common input and output
heights. -/
abbrev extendedFactory : ModuleCat.{t} S ⥤
    (ModuleCat.{max w v} R ⥤ ModuleCat.{max w t v} S) :=
  ModuleCat.tensorBifunctorAt.{w, t, max w v} S ⋙
    (whiskeringLeft (ModuleCat.{max w v} R) (ModuleCat.{max w v} S)
      (ModuleCat.{max w t v} S)).obj (ModuleCat.extendScalars (algebraMap R S))

/-- Coefficient naturality of inverse tensor cancellation.

For g : M → N, first applying inverse cancellation and then the coefficient map on the
extended tensor equals applying g on the direct tensor and then inverse cancellation for N. -/
@[reassoc]
theorem cancellationNatIso_inv_coefficient {M N : ModuleCat.{t} S} (g : M ⟶ N)
    (L : ModuleCat.{max w v} R) :
    (cancellationNatIso R S M).inv.app L ≫ ((extendedFactory R S).map g).app L =
      ((factory.{u, w, t, max w v} R S).map g).app L ≫
        (cancellationNatIso R S N).inv.app L := by
  let φ : R →+* S := algebraMap R S
  letI : Algebra R S := φ.toAlgebra
  letI : Module R M := Module.compHom M (algebraMap R S)
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : SMulCommClass R S M := ⟨fun r s m => by
    change (algebraMap R S r) • (s • m) = s • ((algebraMap R S r) • m)
    exact smul_comm _ _ _⟩
  letI : SMulCommClass R S N := ⟨fun r s n => by
    change (algebraMap R S r) • (s • n) = s • ((algebraMap R S r) • n)
    exact smul_comm _ _ _⟩
  let T := ((extendedFactory R S).obj N).obj L
  letI : Module R T := Module.compHom T (algebraMap R S)
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro m l
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hm := cancellationNatIso_inv_tmul R S M L m l
  have hn := cancellationNatIso_inv_tmul R S N L (g.hom m) l
  have hg := coefficientMapAt_tmul R S g L m l
  have ht := ModuleCat.tensorHomAt_tmul S g
    (𝟙 ((ModuleCat.extendScalars (algebraMap R S)).obj L)) m ((1 : S) ⊗ₜ[R] l)
  exact (congrArg (((extendedFactory R S).map g).app L).hom hm).trans
    (ht.trans ((congrArg ((cancellationNatIso R S N).inv.app L).hom hg).trans hn).symm)

/-- Coefficient naturality of forward tensor cancellation.

For g : M → N, the coefficient map on M ⊗_S (S ⊗_R L) followed by cancellation for N equals
cancellation for M followed by g ⊗ id_L. -/
@[reassoc]
theorem cancellationNatIso_hom_coefficient {M N : ModuleCat.{t} S} (g : M ⟶ N)
    (L : ModuleCat.{max w v} R) :
    ((extendedFactory R S).map g).app L ≫ (cancellationNatIso R S N).hom.app L =
      (cancellationNatIso R S M).hom.app L ≫
        ((factory.{u, w, t, max w v} R S).map g).app L := by
  let cM := (cancellationNatIso R S M).app L
  let cN := (cancellationNatIso R S N).app L
  apply (cancel_epi cM.inv).1
  let a := ((extendedFactory R S).map g).app L
  let b := ((factory.{u, w, t, max w v} R S).map g).app L
  change cM.inv ≫ (a ≫ cN.hom) = cM.inv ≫ (cM.hom ≫ b)
  have h : cM.inv ≫ a = b ≫ cN.inv := cancellationNatIso_inv_coefficient R S g L
  exact (Category.assoc cM.inv a cN.hom).symm.trans
    ((congrArg (fun x => x ≫ cN.hom) h).trans
      ((Category.assoc b cN.inv cN.hom).trans
        ((congrArg (fun x => b ≫ x) cN.inv_hom_id).trans
          ((Category.comp_id b).trans (cM.inv_hom_id_assoc b).symm))))

/-- The coefficient-natural cancellation isomorphism of bifunctors.

The extended-input tensor bifunctor is naturally isomorphic to (M,L) ↦ M ⊗_R L through base-
change cancellation. -/
def cancellationFactoryIso : extendedFactory R S ≅
    (factory R S : ModuleCat.{t} S ⥤ ModuleCat.{max w v} R ⥤ ModuleCat.{max w t v} S) :=
  NatIso.ofComponents (fun M => cancellationNatIso R S M) (by
    intro M N g
    apply NatTrans.ext
    funext L
    exact cancellationNatIso_hom_coefficient R S g L)

/-- The cancellation isomorphism for an R-module diagram.

For X : J → ModuleCat R at the stated input height, precompose the input variable of the
coefficient-natural cancellation to obtain an isomorphism of coefficient families of
J-diagrams. -/
def cancellationDiagramIso {J : Type*} [Category J] (X : J ⥤ ModuleCat.{max w v} R) :
    extendedFactory R S ⋙
        (whiskeringLeft J (ModuleCat.{max w v} R) (ModuleCat.{max w t v} S)).obj X ≅
      (factory R S : ModuleCat.{t} S ⥤ ModuleCat.{max w v} R ⥤ ModuleCat.{max w t v} S) ⋙
        (whiskeringLeft J (ModuleCat.{max w v} R) (ModuleCat.{max w t v} S)).obj X :=
  isoWhiskerRight (cancellationFactoryIso R S)
    ((whiskeringLeft J (ModuleCat.{max w v} R) (ModuleCat.{max w t v} S)).obj X)

/-- Components of diagramwise tensor cancellation.

At coefficient M and diagram object j, the forward diagram comparison is cancellationNatIso R
S M at X_j. -/
theorem cancellationDiagramIso_hom_app {J : Type*} [Category J]
    (X : J ⥤ ModuleCat.{max w v} R) (M : ModuleCat.{t} S) (j : J) :
    ((cancellationDiagramIso R S X).hom.app M).app j =
      (cancellationNatIso R S M).hom.app (X.obj j) := rfl

end ModuleCat.TensorRestriction

end
