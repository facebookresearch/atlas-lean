/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TwistedCharacterQuotientModels
public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels

/-!
# Actual projective matrix-group quotients and character torsors

The projective group is the actual scalar-torus quotient of the fixed
GL2 scheme: its projection is a genuine fppf scalar torsor with the
literal scalar action and scheme-valued universal property.
The character quotient's effective action is the actual projective-group
torsor R to M_B, preserving the actual conjugation action and quotient
map. These torsors retain coefficient-scheme data that a set of matrix
orbits would lose.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.1; Stacks Project Tag0CQJ.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ProjectiveMatrixGroupQuotients

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels ExpansionParameterModels
open TwistedRankTwoRepresentations TwistedCharacterQuotientModels

variable [F : FrameTheory 2] [M : GL2MatrixTheory]

def scalarScheme (Gm : TorusTheory ℂ 1) : torusScheme ℂ 1 ⟶ frameScheme 2 :=
  (M.points (torusScheme ℂ 1)).symm
    (Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Gm.units (torusScheme ℂ 1) (𝟙 (torusScheme ℂ 1)) 0))

def scalarActionMap (Gm : TorusTheory ℂ 1) :
    torusScheme ℂ 1 ⊗ frameScheme 2 ⟶ frameScheme 2 :=
  tensorHom (scalarScheme Gm) (𝟙 (frameScheme 2)) ≫ μ[frameScheme 2]

structure ProjectiveGL2 (Gm : TorusTheory ℂ 1) where
  scheme : Over (Spec (.of ℂ))
  [group : GrpObj scheme]
  projection : frameScheme 2 ⟶ scheme
  [hom : IsMonHom projection]
  scalar_hom : letI := Gm.group; IsMonHom (scalarScheme Gm)
  scalar_kernel : scalarScheme Gm ≫ projection = toUnit (torusScheme ℂ 1) ≫ η[scheme]
  torsor : letI := Gm.group; GroupTorsorGeometry.Torsor (torusScheme ℂ 1) scheme
  total : letI := Gm.group; torsor.total ≅ frameScheme 2
  projection_normalized : letI := Gm.group; total.hom ≫ projection = torsor.projection
  action_normalized : letI := Gm.group
    γ[torusScheme ℂ 1,torsor.total] ≫ total.hom =
      (torusScheme ℂ 1 ◁ total.hom) ≫ scalarActionMap Gm
  universal : ∀ (Z : Over (Spec (.of ℂ))) (f : frameScheme 2 ⟶ Z),
    scalarActionMap Gm ≫ f = snd (torusScheme ℂ 1) (frameScheme 2) ≫ f →
      ∃! h : scheme ⟶ Z, projection ≫ h = f

attribute [instance] ProjectiveGL2.group
attribute [instance] ProjectiveGL2.hom

variable {Gm : TorusTheory ℂ 1} (P : ProjectiveGL2 Gm)
  (g : ℕ) [C : Conjugation g]

structure CharacterTorsor where
  torsor : GroupTorsorGeometry.Torsor P.scheme (bettiScheme g)
  total : torsor.total ≅ representation g
  projection : total.hom ≫ quotientMap g = torsor.projection
  action : tensorHom P.projection (𝟙 torsor.total) ≫ γ[P.scheme,torsor.total] ≫ total.hom =
    (frameScheme 2 ◁ total.hom) ≫ γ[frameScheme 2,representation g]

end MathlibExt.AlgebraicGeometry.ProjectiveMatrixGroupQuotients
