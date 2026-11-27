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

public import MathlibExt.Algebra.Homology.HomologyMapSquare

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace MathlibExtTest.Algebra.Homology.HomologyMapSquare

section ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {S₀ S₁ S₂ S₃ : ShortComplex C}
  [S₀.HasHomology] [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology]
variable {f : S₀ ⟶ S₁} {g : S₀ ⟶ S₂}
  {h : S₁ ⟶ S₃} {i : S₂ ⟶ S₃}

example (sq : CommSq f g h i) :
    CommSq (ShortComplex.homologyMap f) (ShortComplex.homologyMap g)
      (ShortComplex.homologyMap h) (ShortComplex.homologyMap i) :=
  ShortComplex.homologyMap_commSq sq

end ShortComplex

section HomologicalComplex

variable {ι : Type w} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {c : ComplexShape ι}
variable {K₀ K₁ K₂ K₃ : HomologicalComplex C c}
variable {f : K₀ ⟶ K₁} {g : K₀ ⟶ K₂}
  {h : K₁ ⟶ K₃} {i : K₂ ⟶ K₃}

example (sq : CommSq f g h i) (n : ι)
    [K₀.HasHomology n] [K₁.HasHomology n]
    [K₂.HasHomology n] [K₃.HasHomology n] :
    CommSq (HomologicalComplex.homologyMap f n)
      (HomologicalComplex.homologyMap g n)
      (HomologicalComplex.homologyMap h n)
      (HomologicalComplex.homologyMap i n) :=
  HomologicalComplex.homologyMap_commSq sq n

end HomologicalComplex

#print axioms CategoryTheory.ShortComplex.homologyMap_square
#print axioms HomologicalComplex.homologyMap_square

end MathlibExtTest.Algebra.Homology.HomologyMapSquare
