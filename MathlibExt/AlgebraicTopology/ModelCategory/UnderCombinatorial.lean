/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
public import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
public import MathlibExt.AlgebraicTopology.ModelCategory.Under

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Presentable.Comma

/-!
# Combinatorial model structures on Under categories

An Under category over a locally presentable category is locally presentable.
For a combinatorial model category, strict images of its generating families
under the costar functor generate the created model structure on every Under
category.

This file makes no monoidal, smash-product, enrichment, properness, or
Quillen-equivalence claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- The literal image of a generating morphism property under the costar
functor into an Under category. -/
noncomputable def underCostar [HasBinaryCoproducts C]
    (I : MorphismProperty C) (S : C) : MorphismProperty (Under S) :=
  I.strictMap (CategoryTheory.Under.costar S)

/-- Right lifting against costar images is detected by the Under forgetful
functor. -/
theorem underCostar_rlp [HasBinaryCoproducts C]
    (I : MorphismProperty C) (S : C) :
    (I.underCostar S).rlp =
      I.rlp.inverseImage (CategoryTheory.Under.forget S) := by
  simpa [underCostar] using
    strictMap_rlp_eq_inverseImage_rlp I
      (CategoryTheory.Under.costar S)
      (CategoryTheory.Under.forget S)
      (CategoryTheory.Under.costarAdjForget S)

end CategoryTheory.MorphismProperty

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] (S : C)

/-- Under categories of locally presentable categories are locally
presentable. This uses actual Under colimits supplied by base wide pushouts;
it does not assert that the forgetful functor creates arbitrary colimits. -/
noncomputable instance isLocallyPresentable
    [IsLocallyPresentable.{w} C] :
    IsLocallyPresentable.{w} (Under S) := by
  obtain ⟨κ₀, hκ₀, hC₀⟩ :=
    IsLocallyPresentable.exists_cardinal.{w} C
  let _ : Fact κ₀.IsRegular := hκ₀
  let _ : IsCardinalLocallyPresentable C κ₀ := hC₀
  obtain ⟨κ, hκ, hUnder⟩ :=
    IsAccessibleCategory.exists_cardinal (Under S)
  let _ : Fact κ.IsRegular := hκ
  let _ : IsCardinalAccessibleCategory (Under S) κ := hUnder
  let hUnderLocallyPresentable :
      IsCardinalLocallyPresentable (Under S) κ :=
    { toHasCardinalFilteredGenerator := inferInstance
      toHasColimitsOfSize := inferInstance }
  exact
    { exists_cardinal :=
        ⟨κ, inferInstance, hUnderLocallyPresentable⟩ }

end CategoryTheory.Under

namespace HomotopicalAlgebra.ModelCategory

open CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [ModelCategory C] (S : C)

/-- Combinatoriality transfers to every Under category through strict costar
images of the two base generating families. -/
noncomputable instance underIsCombinatorial
    [IsCombinatorialModelCategory.{w} C] :
    IsCombinatorialModelCategory.{w} (Under S) := by
  obtain ⟨κ, hκ, hbot, hC, ⟨G⟩⟩ :=
    IsCombinatorialModelCategory.exists_cardinal (C := C)
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  let _ : IsCardinalLocallyPresentable C κ := hC
  let _ : IsLocallyPresentable.{w} C :=
    { exists_cardinal := ⟨κ, inferInstance, hC⟩ }
  let _ : IsLocallyPresentable.{w} (Under S) := inferInstance
  have hISmall : (G.I.underCostar S).IsSmall.{w} := by
    change (G.I.strictMap (Under.costar S)).IsSmall.{w}
    exact G.I_smallObject.isSmall.strictMap (Under.costar S)
  have hJSmall : (G.J.underCostar S).IsSmall.{w} := by
    change (G.J.strictMap (Under.costar S)).IsSmall.{w}
    exact G.J_smallObject.isSmall.strictMap (Under.costar S)
  let _ : (G.I.underCostar S).IsSmall.{w} := hISmall
  let _ : (G.J.underCostar S).IsSmall.{w} := hJSmall
  let _ : (G.I.underCostar S).HasSmallObjectArgument.{w} :=
    hasSmallObjectArgument_of_isSmall (G.I.underCostar S)
  let _ : (G.J.underCostar S).HasSmallObjectArgument.{w} :=
    hasSmallObjectArgument_of_isSmall (G.J.underCostar S)
  have hIrlp : (G.I.underCostar S).rlp =
      trivialFibrations (Under S) := by
    calc
      (G.I.underCostar S).rlp =
          G.I.rlp.inverseImage (Under.forget S) :=
        MorphismProperty.underCostar_rlp G.I S
      _ = (trivialFibrations C).inverseImage (Under.forget S) :=
        congrArg (fun P : MorphismProperty C =>
          P.inverseImage (Under.forget S)) G.I_rlp
      _ = (trivialFibrations C).under :=
        (MorphismProperty.under_eq_inverseImage
          (trivialFibrations C) S).symm
      _ = trivialFibrations (Under S) :=
        (trivialFibrations_under_eq S).symm
  have hJrlp : (G.J.underCostar S).rlp =
      fibrations (Under S) := by
    calc
      (G.J.underCostar S).rlp =
          G.J.rlp.inverseImage (Under.forget S) :=
        MorphismProperty.underCostar_rlp G.J S
      _ = (fibrations C).inverseImage (Under.forget S) :=
        congrArg (fun P : MorphismProperty C =>
          P.inverseImage (Under.forget S)) G.J_rlp
      _ = (fibrations C).under :=
        (MorphismProperty.under_eq_inverseImage (fibrations C) S).symm
      _ = fibrations (Under S) :=
        (fibrations_under_def S).symm
  exact isCombinatorialModelCategory_of_generators
    (G.I.underCostar S) (G.J.underCostar S) hIrlp hJrlp

end HomotopicalAlgebra.ModelCategory
