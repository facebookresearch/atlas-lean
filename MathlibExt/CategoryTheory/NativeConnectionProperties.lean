/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeGaussManinOutputs

/-!
# Native connection extension, curvature and Griffiths predicates

These properties apply to an ACTUAL K-linear sheaf map on the original
native module. The degree-one extension is fixed on EVERY native
tensor generator by the connection and the original form differential.
Curvature is the literal native composite, and Griffiths uses the
native image of the original tensor filtration inclusion.

Source: Scholze, arXiv:1205.3463v2, Definitions 7.4--7.5 and Theorem 8.8;
Stacks Tags 07HY and 07I0; native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeConnectionProperties

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations RingSheafModuleTensors NativeRingInverseImages
open NativeFilteredDeRhamOutputs

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}] [HasSheafify J AddCommGrpCat.{1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (K O : Sheaf J CommRingCat.{1}) (k : K ⟶ O) (E Ω : Modules O)

abbrev restrictK := restrict K O k
abbrev oneForms := tensor O E Ω
abbrev twoForms := tensor O E (exterior O Ω 2)

/-- This wedge source is fixed on every native tensor and exterior unit. -/
structure WedgeSource where
  map : tensor O (oneForms O E Ω) Ω ⟶ twoForms O E Ω
  source : ∀ (U : Cᵒᵖ) (m : E.val.obj U) (w v : Ω.val.obj U),
    (map.val.app U).hom
      (generator O (oneForms O E Ω) Ω U (generator O E Ω U m w) v) =
    generator O E (exterior O Ω 2) U m
      (exteriorUnit O Ω 2 U
        (_root_.exteriorPower.ιMulti (O.obj.obj U) 2 (fun i : Fin 2 => if i = 0 then w else v)))

variable (d : ∀ U : Cᵒᵖ, O.obj.obj U →+ Ω.val.obj U)

/-- A native K-linear original form differential, with the actual product rule. Analytic
source integration additionally fixes it on every continuous affinoid quotient unit. -/
structure FormDifferentialSource where
  map : (restrictK K O k).obj Ω ⟶ (restrictK K O k).obj (exterior O Ω 2)
  leibniz : ∀ (U : Cᵒᵖ) (a : O.obj.obj U) (w : Ω.val.obj U),
    letI : Module (O.obj.obj U) (((restrictK K O k).obj (exterior O Ω 2)).val.obj U) :=
      inferInstanceAs (Module (O.obj.obj U) ((exterior O Ω 2).val.obj U))
    (map.val.app U).hom (a • w) = a • (map.val.app U).hom w +
      (show (((restrictK K O k).obj (exterior O Ω 2)).val.obj U) from
        exteriorUnit O Ω 2 U
          (_root_.exteriorPower.ιMulti (O.obj.obj U) 2 (fun i : Fin 2 => if i = 0 then d U a else w)))
  exact_zero : ∀ U a, (map.val.app U).hom (d U a) = 0

def FormDifferentialSource.sections (A : FormDifferentialSource K O k Ω d) (U : Cᵒᵖ) :
    Ω.val.obj U →+ (exterior O Ω 2).val.obj U := (A.map.val.app U).hom.toAddMonoidHom

variable (nabla : (restrictK K O k).obj E ⟶ (restrictK K O k).obj (oneForms O E Ω))

/-- The Leibniz rule retains the ORIGINAL O action and the native tensor unit. -/
def IsConnection : Prop := ∀ (U : Cᵒᵖ) (a : O.obj.obj U) (m : E.val.obj U),
  letI : Module (O.obj.obj U) (((restrictK K O k).obj (oneForms O E Ω)).val.obj U) :=
    inferInstanceAs (Module (O.obj.obj U) ((oneForms O E Ω).val.obj U))
  (nabla.val.app U).hom (a • m) = a • (nabla.val.app U).hom m +
    (show (((restrictK K O k).obj (oneForms O E Ω)).val.obj U) from generator O E Ω U m (d U a))

variable (d₁ : ∀ U : Cᵒᵖ, Ω.val.obj U →+ (exterior O Ω 2).val.obj U)
  (W : WedgeSource O E Ω)

/-- The extension's values are fixed on every ORIGINAL sheafified tensor generator. -/
structure ExtensionSource where
  map : (restrictK K O k).obj (oneForms O E Ω) ⟶ (restrictK K O k).obj (twoForms O E Ω)
  source : ∀ (U : Cᵒᵖ) (m : E.val.obj U) (w : Ω.val.obj U),
    (map.val.app U).hom
      (show (((restrictK K O k).obj (oneForms O E Ω)).val.obj U) from generator O E Ω U m w) =
    (show (((restrictK K O k).obj (twoForms O E Ω)).val.obj U) from
      (W.map.val.app U).hom
        (generator O (oneForms O E Ω) Ω U
          (show (oneForms O E Ω).val.obj U from (nabla.val.app U).hom m) w) +
      generator O E (exterior O Ω 2) U m (d₁ U w))

/-- Integrability is zero of the literal computed native curvature composite. -/
def IsIntegrable (N : ExtensionSource K O k E Ω nabla d₁ W) : Prop := nabla ≫ N.map = 0

variable (F : CoefficientFiltration O E)

def tensorFiltration (j : ℤ) : Modules O := image ((tensorFunctor O Ω).map (F.pieces j).ι)

/-- Griffiths transversality uses the ORIGINAL sheaf filtration and its native tensor image. -/
def Griffiths : Prop := ∀ (U : Cᵒᵖ) (j : ℤ) (m : E.val.obj U),
  m ∈ (F.pieces j).toSubmodule.obj U →
    (show (oneForms O E Ω).val.obj U from (nabla.val.app U).hom m) ∈
      LinearMap.range ((image.ι ((tensorFunctor O Ω).map (F.pieces (j - 1)).ι)).val.app U).hom

end MathlibExt.CategoryTheory.NativeConnectionProperties
