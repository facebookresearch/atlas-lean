/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceAssociator

/-!
# Whole original three-piece associator readbacks

The actual native associator retains each of the SAME three complete
input pieces. These full simplicial-map equations use the original
prefix/suffix operators, including zero-length original pieces.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead.OrdinalCharts

/-- The SAME original whole first piece is retained under native reassociation. -/
theorem associator_first (T U V : Data) :
    concatLeft.{u} T U ≫ concatLeft (T.concat U) V ≫ (associatorMorphism T U V).map =
      concatLeft T (U.concat V) := by
  apply (cancel_mono (complex (T.concat (U.concat V)).joints).ι).1
  simp only [Category.assoc]
  have h : prefixOperator T.dimension U.dimension ≫
      prefixOperator (T.dimension + U.dimension) V.dimension ≫
        (associatorMorphism T U V).operator = prefixOperator T.dimension (U.dimension + V.dimension) := by
    ext i : 3
    exact Fin.ext rfl
  exact congrArg (fun e => (complex.{u} T.joints).ι ≫ SSet.stdSimplex.map e) h

/-- The SAME original whole middle piece is retained under native reassociation. -/
theorem associator_middle (T U V : Data) :
    concatRight.{u} T U ≫ concatLeft (T.concat U) V ≫ (associatorMorphism T U V).map =
      concatLeft U V ≫ concatRight T (U.concat V) := by
  apply (cancel_mono (complex (T.concat (U.concat V)).joints).ι).1
  simp only [Category.assoc]
  have h : suffixOperator T.dimension U.dimension ≫
      prefixOperator (T.dimension + U.dimension) V.dimension ≫
        (associatorMorphism T U V).operator =
      prefixOperator U.dimension V.dimension ≫ suffixOperator T.dimension (U.dimension + V.dimension) := by
    ext i : 3
    exact Fin.ext rfl
  exact congrArg (fun e => (complex.{u} U.joints).ι ≫ SSet.stdSimplex.map e) h

/-- The SAME original whole last piece is retained under native reassociation. -/
theorem associator_last (T U V : Data) :
    concatRight.{u} (T.concat U) V ≫ (associatorMorphism T U V).map =
      concatRight U V ≫ concatRight T (U.concat V) := by
  apply (cancel_mono (complex (T.concat (U.concat V)).joints).ι).1
  simp only [Category.assoc]
  have h : suffixOperator (T.dimension + U.dimension) V.dimension ≫
      (associatorMorphism T U V).operator =
      suffixOperator U.dimension V.dimension ≫ suffixOperator T.dimension (U.dimension + V.dimension) := by
    ext i : 3
    apply Fin.ext
    change T.dimension + U.dimension + i.val = T.dimension + (U.dimension + i.val)
    omega
  exact congrArg (fun e => (complex.{u} V.joints).ι ≫ SSet.stdSimplex.map e) h

end SSet.OriginalNecklace
