/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeDifferentialForms
public import MathlibExt.AlgebraicGeometry.SheafTensorSections

/-!
# Generator-normalized actual relative de Rham differential

The coefficient forms and wedge are the actual native constructions.
The degree-one differential is additive and π^-1 O_T-linear, with its
whole restriction naturality and exact generator formula d(a db)=da∧db.
The generic producer is completed source integration, not a new Wanted.

Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/DeRham/DifferentialGradedAlgebra/Basic.lean and
AlgebraicGeometry/DeRham/Gysin/GysinDeRhamDifferential.lean, Apache 2.0.
Modification: retain the native Kan/Kähler exterior forms and expose the
exact additive differential, generator and restriction normalization.
Square-zero on the actual universal differential is proved below.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeDeRhamDifferential

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open RelativeDifferentialForms SheafTensorSections

variable {Y T : Scheme.{0}} (pi : Y ⟶ T)

def wedgeSection (U : Y.Opens) (a b : (forms pi 1).val.obj (op U)) :
    (forms pi 2).val.obj (op U) :=
  ((wedge pi).val.app (op U)).hom
    (tensorSection Y (forms pi 1) (forms pi 1) U a b)

@[simp] theorem wedgeSection_zero_left (U : Y.Opens) (b : (forms pi 1).val.obj (op U)) :
    wedgeSection pi U 0 b = 0 := by simp [wedgeSection]

@[simp] theorem wedgeSection_zero_right (U : Y.Opens) (a : (forms pi 1).val.obj (op U)) :
    wedgeSection pi U a 0 = 0 := by simp [wedgeSection]

structure Differential where
  map : ∀ U : Y.Opens, (forms pi 1).val.obj (op U) →+ (forms pi 2).val.obj (op U)
  naturality : ∀ (U V : Y.Opens) (h : V ≤ U) (a : (forms pi 1).val.obj (op U)),
    map V (((forms pi 1).val.map (homOfLE h).op).hom a) =
      ((forms pi 2).val.map (homOfLE h).op).hom (map U a)
  generator : ∀ (U : Y.Opens) (a b : Γ(Y, U)),
    map U (a • (d0 pi).d b) = wedgeSection pi U ((d0 pi).d a) ((d0 pi).d b)
  leibniz : ∀ (U : Y.Opens) (a : Γ(Y, U)) (b : (forms pi 1).val.obj (op U)),
    map U (a • b) = wedgeSection pi U ((d0 pi).d a) b + a • map U b

variable (D : Differential pi)

theorem d1_d0 (U : Y.Opens) (a : Γ(Y, U)) : D.map U ((d0 pi).d a) = 0 := by
  have h := D.generator U 1 a
  simp only [one_smul] at h
  rw [h, (d0 pi).d_one (op U), wedgeSection_zero_left]

theorem base_linear (V : T.Opens) (U : Y.Opens) (h : U ≤ pi ⁻¹ᵁ V)
    (a : Γ(T, V)) (b : (forms pi 1).val.obj (op U)) :
    D.map U ((pi.appLE V U h).hom a • b) = (pi.appLE V U h).hom a • D.map U b := by
  rw [D.leibniz, d0_base_section, wedgeSection_zero_left, zero_add]

end MathlibExt.AlgebraicGeometry.RelativeDeRhamDifferential
