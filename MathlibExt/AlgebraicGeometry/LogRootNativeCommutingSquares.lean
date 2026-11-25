/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogRootCompositionModels
public import MathlibExt.AlgebraicGeometry.EtaleLogNativeCategory

/-!
# Original log-section squares supplied by native slice arrows

The slice equation is transported through the original normalized log
composition. This fixes the entire log-section square before applying
alpha, including all sections with zero alpha image. The lemma supplies
the original square used to normalize finite root composition cells.

Source: Kato, Logarithmic structures of Fontaine--Illusie, Section 1;
Talpo--Vistoli, arXiv:1410.1164v2, Section 6 and Theorem 5.24.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootNativeCommutingSquares

open _root_.CategoryTheory
open EtaleLogSchemes EtaleLogDiagrams EtaleLogNativeCategory LogRootCompositionModels

variable [InverseImageTheory.{0}] [N : NativeCategoryModel.{0}]

omit [InverseImageTheory.{0}] in
/-- Native composition equality fixes the actual original log sections. -/
theorem original_square_of_equality {X Y Z : LogScheme.{0}}
    (f : EtaleLogSchemes.Hom X Y) (g : EtaleLogSchemes.Hom Y Z)
    (h : EtaleLogSchemes.Hom X Z) (w : N.operations.compose f g = h) :
    OriginalSquare f g h := by
  subst h
  exact
    { base := N.operations.compose_map f g
      log_sections := N.operations.compose_sections f g }

omit [InverseImageTheory.{0}] in
/-- The slice arrow supplies that precise square through its original Over.w equation. -/
theorem original_square_of_over {X : LogScheme.{0}} {U V : Over X} (a : U ⟶ V) :
    OriginalSquare a.left V.hom U.hom :=
  original_square_of_equality a.left V.hom U.hom (Over.w a)

end MathlibExt.AlgebraicGeometry.LogRootNativeCommutingSquares
