/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalSuccessor

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

local instance : HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))
variable {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

example (p : ℕ) : B.partialTotal p ⟶ B.totalRow p :=
  B.partialTotalRowQuotient p

example (p j n : ℕ) (h : p + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) p j n h ≫
        (B.partialTotalRowQuotient p).f n =
      (B.partialTotalLastRowIso p).hom.f j ≫
        (B.totalRowXIso p j n h).inv :=
  B.ιTotal_partialTotalRowQuotient p j n h

example (p i j n : ℕ) (h : i + j = n) (hi : i ≠ p) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i j n h ≫
        (B.partialTotalRowQuotient p).f n = 0 :=
  B.ιTotal_partialTotalRowQuotient_eq_zero p i j n h hi

example (φ : B ⟶ B') (p : ℕ) :
    B.partialTotalHom φ p ≫ B'.partialTotalRowQuotient p =
      B.partialTotalRowQuotient p ≫ totalRowMap φ p :=
  B.partialTotalRowQuotient_naturality φ p

example (m : ℕ) : ShortComplex (ChainComplex C ℕ) :=
  B.partialTotalSuccShortComplex m

example (m n : ℕ) :
    ((B.partialTotalSuccShortComplex m).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting :=
  B.partialTotalSuccDegreeSplitting m n

example (m n : ℕ) :
    (B.partialTotal (m + 1)).X n ≅
      (B.partialTotal m).X n ⊞ (B.totalRow (m + 1)).X n :=
  B.partialTotalSuccDegreeIso m n

example (m n : ℕ) :
    ((B.partialTotalSuccShortComplex m).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).ShortExact :=
  B.partialTotalSuccDegreewiseShortExact m n

example (n : ℕ) :
    ((B.partialTotalSuccShortComplex 0).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting :=
  B.partialTotalSuccDegreeSplitting 0 n

example (φ : B ⟶ B') (m : ℕ) :
    B.partialTotalSuccShortComplex m ⟶
      B'.partialTotalSuccShortComplex m :=
  B.partialTotalSuccShortComplexMap φ m

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

example (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (m : ℕ) :
    (B.partialTotalSuccShortComplex m).ShortExact :=
  B.partialTotalSuccShortExact m

example (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    (B.partialTotalSuccShortComplex 0).ShortExact :=
  B.partialTotalSuccShortExact 0

end Abelian

end HomologicalComplex₂

end
