/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceFullCoefficientLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientHomNaturality

/-!
# The SAME unique full original coefficient lift map

The genuine native lift theorem and actual full ambient Hom monicity
construct a uniquely determined original raw Hom for every complete
joint flag. All scalar operators and every actual original native flag
map retain their SAME complete Hom and coefficient readbacks.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace

/-- The uniquely determined SAME full original raw Hom lift of the actual complete coefficient. -/
def coefficientLift (T : Data) {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q :=
  (exists_native_coefficient_lift T q p).choose

/-- The SAME actual lift has its exact complete original ambient coefficient readback. -/
theorem coefficientLift_ambient (T : Data) {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    (ambientHomMap T).app q (coefficientLift T p) = p.val :=
  (exists_native_coefficient_lift T q p).choose_spec

/-- The SAME full original raw Hom lift is unique by the actual native ambient mono. -/
theorem coefficientLift_unique (T : Data) {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q)
    (a : (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q)
    (ha : (ambientHomMap T).app q a = p.val) : a = coefficientLift T p := by
  let _ := ambientHomMap_mono.{u} T
  exact injective_of_mono ((ambientHomMap T).app q) (ha.trans (coefficientLift_ambient T p).symm)

/-- EVERY SAME scalar operator retains the uniquely determined full original coefficient lift. -/
theorem coefficientLift_scalar (T : Data) {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (p : (fullCoefficient.{u} T).obj q) :
    (hom T.object (sourceVertex T) (targetVertex T)).map θ (coefficientLift T p) =
      coefficientLift T ((fullCoefficient T).map θ p) := by
  apply coefficientLift_unique T ((fullCoefficient T).map θ p)
  have h := ConcreteCategory.congr_hom ((ambientHomMap T).naturality θ) (coefficientLift T p)
  exact h.trans (congrArg ((OriginalBead.TerminalFlag.coefficientObject T.dimension).map θ)
    (coefficientLift_ambient T p))

/-- The SAME complete joint coefficient complex maps to its actual original raw native Hom. -/
def coefficientLiftMap (T : Data) : fullCoefficient.{u} T ⟶
    hom T.object.{u} (sourceVertex T) (targetVertex T) where
  app q := ↾coefficientLift T
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (coefficientLift_scalar T θ p).symm

/-- The SAME entire native lift map retains its literal original joint-coefficient inclusion. -/
theorem coefficientLiftMap_ambient (T : Data) :
    coefficientLiftMap.{u} T ≫ ambientHomMap T = (coefficientComplex T).ι := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  exact coefficientLift_ambient T p

/-- EVERY actual original native flag map retains the SAME unique complete coefficient lifts. -/
theorem coefficientLift_native {T U : Data} (f : T ⟶ U) {q : SimplexCategoryᵒᵖ}
    (p : (fullCoefficient.{u} T).obj q) (p' : (fullCoefficient.{u} U).obj q)
    (hflags : (OriginalFlaggedNecklace.coefficientFunctor.{u}.map f).app q p.val = p'.val) :
    (nativeHomMap f).app q (coefficientLift T p) = coefficientLift U p' := by
  apply coefficientLift_unique U p'
  have h := ConcreteCategory.congr_hom (congr_app (ambientHomMap_native.{u} f) q) (coefficientLift T p)
  exact h.trans ((congrArg ((OriginalFlaggedNecklace.coefficientFunctor.map f).app q)
    (coefficientLift_ambient T p)).trans hflags)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
