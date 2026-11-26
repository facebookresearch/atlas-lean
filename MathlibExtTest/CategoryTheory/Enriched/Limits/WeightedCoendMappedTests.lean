/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendMapped

set_option autoImplicit false
noncomputable section
universe uV vV uA uD vD

namespace MathlibExtTest.WeightedCoendMapped

open CategoryTheory CategoryTheory.Enriched MonoidalCategory Opposite Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {D : Type uD} [Category.{vD} D]
  (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) (J : V ⥤ D)
  [HasCoproduct (weightedCoend.relations W F)] [HasCoproduct (weightedCoend.objects W F)]
  [HasCoequalizer (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)]
  [PreservesColimit (Discrete.functor (weightedCoend.objects W F)) J]
  [PreservesColimit (parallelPair (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)) J]

-- Extensionality needs no preservation of the relation coproduct and no enrichment on D.
example {X : D} {f g : J.obj (Enriched.weightedCoend W F) ⟶ X}
    (h : ∀ a, J.map (weightedCoend.ι W F a) ≫ f =
      J.map (weightedCoend.ι W F a) ≫ g) : f = g :=
  weightedCoend.Mapped.hom_ext W F J h

section Descent
variable [PreservesColimit (Discrete.functor (weightedCoend.relations W F)) J]

example {X : D} (q : ∀ a, J.obj (weightedCoend.objects W F a) ⟶ X)
    (hq : weightedCoend.Mapped.Balanced W F J q) (a : A) :
    J.map (weightedCoend.ι W F a) ≫ weightedCoend.Mapped.desc W F J q hq = q a :=
  weightedCoend.Mapped.gen_desc W F J q hq a

example (X : D) : (J.obj (Enriched.weightedCoend W F) ⟶ X) ≃
    {q : ∀ a, J.obj (weightedCoend.objects W F a) ⟶ X //
      weightedCoend.Mapped.Balanced W F J q} :=
  weightedCoend.Mapped.homEquiv W F J X

example (X : D) (f : J.obj (Enriched.weightedCoend W F) ⟶ X) :
    (weightedCoend.Mapped.homEquiv W F J X).symm
      ((weightedCoend.Mapped.homEquiv W F J X) f) = f :=
  (weightedCoend.Mapped.homEquiv W F J X).left_inv f
end Descent

#check @weightedCoend.Mapped.Balanced
#print axioms weightedCoend.Mapped.desc
#print axioms weightedCoend.Mapped.gen_desc
#print axioms weightedCoend.Mapped.hom_ext
#print axioms weightedCoend.Mapped.homEquiv

end MathlibExtTest.WeightedCoendMapped
