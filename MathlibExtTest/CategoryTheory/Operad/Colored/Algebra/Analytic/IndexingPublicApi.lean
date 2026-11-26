/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.CategoryTheory.Operad.Colored.Algebra.Analytic.Indexing

/-!
# Focused O7E analytic indexing public-contract packet

Pins the stable downstream-facing contracts for fixed-output
analytic indexing: the index-to-profile conversion with
computations, the groupoid input-equivalence laws, inclusion
into profiles with output/map laws, the input family with
object/map laws, the combined factors family with outer/inner
object and map laws, and the analytic summand with object
computation.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v w

variable {Color : Type u} {d : Color} {V : Type w}
  [Category.{v} V]

-- Fixed-output profiles keep inputs.
example (P : AnalyticIndex Color d) :
    P.toColoredProfile.inputs = P.inputs :=
  P.toColoredProfile_inputs

-- Fixed-output profiles keep input colors.
example (P : AnalyticIndex Color d) (i : P.inputs) :
    P.toColoredProfile.inputColor i = P.inputColor i :=
  P.toColoredProfile_inputColor i

-- Fixed-output profiles fix the output color.
example (P : AnalyticIndex Color d) :
    P.toColoredProfile.outputColor = d :=
  P.toColoredProfile_outputColor

-- Identity input equivalences are reflexivity.
example (P : AnalyticIndex Color d) :
    (𝟙 P : P ⟶ P).inputEquiv = Equiv.refl _ :=
  AnalyticIndex.id_inputEquiv P

-- Composite input equivalences compose.
example {P Q R : AnalyticIndex Color d} (f : P ⟶ Q)
    (g : Q ⟶ R) :
    (f ≫ g).inputEquiv =
      f.inputEquiv.trans g.inputEquiv :=
  AnalyticIndex.comp_inputEquiv f g

-- Inverse input equivalences are symmetric.
example {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    (Groupoid.inv f).inputEquiv = f.inputEquiv.symm :=
  AnalyticIndex.inv_inputEquiv f

-- Inclusion preserves the fixed output color.
example (P : AnalyticIndex Color d) :
    ((analyticToProfileFunctor Color d).obj P).outputColor =
      d :=
  analyticToProfileFunctor_obj_outputColor Color d P

-- Inclusion preserves input equivalences.
example {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    ((analyticToProfileFunctor Color d).map f).inputEquiv =
      f.inputEquiv :=
  analyticToProfileFunctor_map_inputEquiv Color d f

-- Input families evaluate carriers at input colors.
example (A : Color → V) (P : AnalyticIndex Color d)
    (i : P.inputs) :
    ((analyticInputFamily (d := d) A).obj P).obj i =
      A (P.inputColor i) :=
  analyticInputFamily_obj A P i

-- Input-family relabelling is color transport.
example (A : Color → V) {P Q : AnalyticIndex Color d}
    (f : P ⟶ Q) (i : P.inputs) :
    ((analyticInputFamily (d := d) A).map f).hom i =
      eqToHom (congrArg A (f.inputColor_eq i)) :=
  analyticInputFamily_map_hom A f i

-- Input-family index maps are input equivalences.
example (A : Color → V) {P Q : AnalyticIndex Color d}
    (f : P ⟶ Q) :
    ((analyticInputFamily (d := d) A).map f).equiv =
      f.inputEquiv :=
  analyticInputFamily_map_equiv A f

-- The operation slot evaluates the collection.
example (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (P : AnalyticIndex Color d) :
    ((analyticFactors (d := d) O A).obj P).obj
        (analyticFactorsOuterIndex O A P) =
      O.obj P.toColoredProfile :=
  analyticFactors_obj_outer O A P

-- Carrier slots evaluate carriers at input colors.
example (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (P : AnalyticIndex Color d)
    (i : P.inputs) :
    ((analyticFactors (d := d) O A).obj P).obj
        (analyticFactorsInnerIndex O A P i) =
      A (P.inputColor i) :=
  analyticFactors_obj_inner O A P i

-- Combined-family index maps lift input equivalences.
example (O : ColoredSymmetricCollection Color V)
    (A : Color → V) {P Q : AnalyticIndex Color d}
    (f : P ⟶ Q) :
    ((analyticFactors (d := d) O A).map f).equiv =
      Equiv.optionCongr f.inputEquiv :=
  analyticFactors_map_equiv O A f

-- Operation components relabel the collection.
example (O : ColoredSymmetricCollection Color V)
    (A : Color → V) {P Q : AnalyticIndex Color d}
    (f : P ⟶ Q) :
    ((analyticFactors (d := d) O A).map f).hom
        (analyticFactorsOuterIndex O A P) =
      O.map ((analyticToProfileFunctor Color d).map f) :=
  analyticFactors_map_outer O A f

-- Carrier components transport colors.
example (O : ColoredSymmetricCollection Color V)
    (A : Color → V) {P Q : AnalyticIndex Color d}
    (f : P ⟶ Q) (i : P.inputs) :
    ((analyticFactors (d := d) O A).map f).hom
        (analyticFactorsInnerIndex O A P i) =
      eqToHom (congrArg A (f.inputColor_eq i)) :=
  analyticFactors_map_inner O A f i

variable [FiniteTensor V]

-- The analytic summand tensors the combined family.
example (O : ColoredSymmetricCollection Color V)
    (A : Color → V) (P : AnalyticIndex Color d) :
    (analyticSummand (d := d) O A).obj P =
      (FiniteTensor.tensor (V := V)).obj
        ((analyticFactors (d := d) O A).obj P) :=
  analyticSummand_obj O A P
