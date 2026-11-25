/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneTestingRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneStrongDeformation
public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationAnodyne
public import Mathlib.Data.List.TFAE

/-!
# Relative deformation recognition between naive fibrant objects

For the original monomorphism between two naive fibrant objects, testing
equivalence, anodyneness and strong deformation data are equivalent. The
native data retain an actual retraction and a homotopy stationary on the
whole source cylinder, with both prescribed endpoints.

This is Cisinski, Higher Categories and Homotopical Algebra, July 30,
2026, Proposition 2.4.34 (printed p.63 / PDF p.79), with the stated generic
factorization hypotheses and the same chosen exact cylinder and system.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasInitial C] [InitialMonoClass C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]
  [MorphismProperty.HasFactorization An An.rlp]

/-- All three relative deformation conditions for the original monomorphism
between naive fibrant objects, using the actual chosen cylinder data. -/
theorem testingEquivalences_anodyne_strongDeformationData_tfae
    {X Y : C} (i : X ⟶ Y) [Mono i]
    (hX : An.naiveFibrantObjects X) (hY : An.naiveFibrantObjects Y) :
    List.TFAE [P.testingEquivalences An i, An i, Nonempty (P.StrongDeformationData i)] := by
  apply List.tfae_of_forall (b := An i)
  intro Q hQ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with rfl | rfl | rfl
  · exact testingEquivalences_iff_anodyne_of_mono_of_naiveFibrant P An i hY
  · exact Iff.rfl
  · exact ⟨fun ⟨D⟩ => D.mem_anodyne,
      fun hi => nonempty_strongDeformationData_of_anodyne P An i hi hX hY⟩

/-- Testing membership is equivalent to the existence of an actual retraction
and a full stationary homotopy between the two prescribed endpoints. -/
theorem testingEquivalences_iff_nonempty_strongDeformationData_of_mono
    {X Y : C} (i : X ⟶ Y) [Mono i]
    (hX : An.naiveFibrantObjects X) (hY : An.naiveFibrantObjects Y) :
    P.testingEquivalences An i ↔ Nonempty (P.StrongDeformationData i) :=
  (testingEquivalences_anodyne_strongDeformationData_tfae P An i hX hY).out 1 3

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
