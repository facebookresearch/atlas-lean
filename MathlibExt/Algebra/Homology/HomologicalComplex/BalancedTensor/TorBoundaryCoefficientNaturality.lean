/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorBoundary
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ParameterMap
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ZeroNaturality

/-!
# Coefficient naturality of the Tor boundary

Let R be a ring, P a complex of right R-modules, and g : N → N′ a map
of left R-modules. The connecting boundary of the boundary–cycles–homology
sequence commutes with the Tor map induced by g and with tensoring the
boundary object with g. The comparison includes the canonical degree-zero
derived-to-tensor isomorphism.

The coefficients are arbitrary. The coordinated construction retains
projective resolutions in the two module categories, while the
common-height version lifts independently sized P and N,N′. The complex
shape and its index universe are unchanged.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex.BalancedTensor

universe u v w t κ

variable (R : Type u) [Ring R]
variable {ι : Type κ} {c : ComplexShape ι}

section Coordinated

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]

/-- For i = c.prev j, changing arbitrary left coefficients by g commutes
with the canonical boundary Tor₁ᴿ(homologyⱼ(P),N) → image(dᵢⱼ) ⊗ᴿ N. -/
@[reassoc]
theorem torBoundary_coeff_naturality
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
    {N N' : ModuleCat.{v} R} (g : N ⟶ N')
    (i j : ι) (hi : c.prev j = i) :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j)).map g ≫
        torBoundary R P N' i j hi =
      torBoundary R P N i j hi ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj
          (Abelian.image (P.d i j))).map g := by
  let B := ModuleCat.BalancedTensor.groupBifunctor R
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} := B.flip.obj N
  let F' : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} := B.flip.obj N'
  let : F.Additive := Functor.LeftDerivedBalance.flippedObjAdditive B N
  let : F'.Additive := Functor.LeftDerivedBalance.flippedObjAdditive B N'
  let α : F ⟶ F' := B.flip.map g
  let S := HomologicalComplex.boundariesCyclesHomologySequence P i j
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi
  have hδ := LeftDerivedDelta.LDdelta_natural_functor α 0 S hS
  have h₀ := congrArg (fun β : F.leftDerived 0 ⟶ F' => β.app S.X₁)
    (NatTrans.leftDerivedZeroIsoSelf_hom_naturality_functor α)
  change (NatTrans.leftDerived α 0).app S.X₁ ≫
      (F'.leftDerivedZeroIsoSelf.app S.X₁).hom =
    (F.leftDerivedZeroIsoSelf.app S.X₁).hom ≫ α.app S.X₁ at h₀
  change (NatTrans.leftDerived α 1).app S.X₃ ≫
      (LeftDerivedDelta.LDdelta F' 0 S hS ≫ (F'.leftDerivedZeroIsoSelf.app S.X₁).hom) =
    (LeftDerivedDelta.LDdelta F 0 S hS ≫ (F.leftDerivedZeroIsoSelf.app S.X₁).hom) ≫
      α.app S.X₁
  calc
    _ = ((NatTrans.leftDerived α 1).app S.X₃ ≫ LeftDerivedDelta.LDdelta F' 0 S hS) ≫
        (F'.leftDerivedZeroIsoSelf.app S.X₁).hom := (Category.assoc _ _ _).symm
    _ = (LeftDerivedDelta.LDdelta F 0 S hS ≫ (NatTrans.leftDerived α 0).app S.X₁) ≫
        (F'.leftDerivedZeroIsoSelf.app S.X₁).hom :=
      congrArg (fun z => z ≫ (F'.leftDerivedZeroIsoSelf.app S.X₁).hom) hδ
    _ = LeftDerivedDelta.LDdelta F 0 S hS ≫
        ((NatTrans.leftDerived α 0).app S.X₁ ≫ (F'.leftDerivedZeroIsoSelf.app S.X₁).hom) :=
      Category.assoc _ _ _
    _ = LeftDerivedDelta.LDdelta F 0 S hS ≫
        ((F.leftDerivedZeroIsoSelf.app S.X₁).hom ≫ α.app S.X₁) :=
      congrArg (fun z => LeftDerivedDelta.LDdelta F 0 S hS ≫ z) h₀
    _ = _ := (Category.assoc _ _ _).symm

/-- The canonical Tor boundary is a natural transformation in the left
coefficient module, for every right complex and i = c.prev j. -/
def torBoundaryCoeffNatTrans
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
    (i j : ι) (hi : c.prev j = i) :
    (ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j) ⟶
      (ModuleCat.BalancedTensor.groupBifunctor R).obj (Abelian.image (P.d i j)) where
  app N := torBoundary R P N i j hi
  naturality := by
    intro N N' g
    exact torBoundary_coeff_naturality R P g i j hi

end Coordinated

/-- For independently sized right complexes and left coefficients, the
canonical coefficient lifts to T = max(u,v,w,t) commute with the Tor
boundary factory. The complex-shape universe is independent of T. -/
@[reassoc]
theorem torBoundaryAt_coeff_naturality
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
    {N N' : ModuleCat.{w} R} (g : N ⟶ N')
    (i j : ι) (hi : c.prev j = i) :
    let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
    let gL := (ModuleCat.uliftFunctor.{max u v w t, w} R).map g
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (PL.homology j)).map gL ≫
        torBoundaryAt R P N' i j hi =
      torBoundaryAt R P N i j hi ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj
          (Abelian.image (PL.d i j))).map gL := by
  let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
  let NL : ModuleCat.{max u v w t} R := (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
  let NL' : ModuleCat.{max u v w t} R := (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N'
  let gL : NL ⟶ NL' := (ModuleCat.uliftFunctor.{max u v w t, w} R).map g
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  exact torBoundary_coeff_naturality R PL gL i j hi

end HomologicalComplex.BalancedTensor
