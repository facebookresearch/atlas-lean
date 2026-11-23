/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationEdgeWord

/-!
# Tests for realization edge words

These public-only clients pin the indexed word constructors, combinatorial and
topological interpretations, total morphism representation, map-to-path-class
equation, and conditional arbitrary-hom faithfulness reduction. No
approximation or unconditional fullness/faithfulness theorem is imported.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationEdgeWordTests

section Constructors

example {X : SSet.{u}} (x y : X _⦋0⦌) (e : X.Edge x y) :
    (SSet.RealizationEdgeWord.edge x y e).toHom =
      SSet.FundamentalGroupoid.homMk e := by
  simp

example {X : SSet.{u}} (x y : X _⦋0⦌) (e : X.Edge x y) :
    (SSet.RealizationEdgeWord.edge x y e).realizedPath =
      TopCat.pathEquiv (SSet.realizedEdgePath e) := by
  simp

example {X : SSet.{u}} (a : SSet.FundamentalGroupoid X) :
    (SSet.RealizationEdgeWord.identity a).toHom = 𝟙 a := by
  simp

example {X : SSet.{u}} (a : SSet.FundamentalGroupoid X) :
    (SSet.RealizationEdgeWord.identity a).realizedPath =
      Path.refl ((SSet.realizationFundamentalGroupoidFunctor X).obj a).as := by
  simp

example {X : SSet.{u}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    w.inverse.toHom = inv w.toHom := by
  simp

example {X : SSet.{u}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    w.inverse.realizedPath = w.realizedPath.symm := by
  simp

example {X : SSet.{u}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    w.inverse.inverse.toHom = w.toHom := by
  simp

example {X : SSet.{u}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    w.inverse.inverse.realizedPath = w.realizedPath := by
  simp

example {X : SSet.{u}} {a b c : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b)
    (w' : SSet.RealizationEdgeWord X b c) :
    (w.compose w').toHom = w.toHom ≫ w'.toHom := by
  simp

example {X : SSet.{u}} {a b c : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b)
    (w' : SSet.RealizationEdgeWord X b c) :
    (w.compose w').realizedPath =
      w.realizedPath.trans w'.realizedPath := by
  simp

example {X : SSet.{u}} {a b c d : SSet.FundamentalGroupoid X}
    (w₀ : SSet.RealizationEdgeWord X a b)
    (w₁ : SSet.RealizationEdgeWord X b c)
    (w₂ : SSet.RealizationEdgeWord X c d) :
    ((w₀.compose w₁).compose w₂).toHom =
      (w₀.compose (w₁.compose w₂)).toHom := by
  simp [Category.assoc]

end Constructors

section RepresentationAndMap

example {X : SSet.{u}} {a b : SSet.FundamentalGroupoid X} (f : a ⟶ b) :
    ∃ w : SSet.RealizationEdgeWord X a b, w.toHom = f :=
  SSet.RealizationEdgeWord.exists_word f

example {X : SSet.{u}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    (SSet.realizationFundamentalGroupoidFunctor X).map w.toHom =
      Path.Homotopic.Quotient.mk w.realizedPath :=
  SSet.RealizationEdgeWord.map_toHom_eq_mk_realizedPath w

example {X : SSet.{1}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    (SSet.realizationFundamentalGroupoidFunctor X).map w.toHom =
      Path.Homotopic.Quotient.mk w.realizedPath :=
  SSet.RealizationEdgeWord.map_toHom_eq_mk_realizedPath w

example {X : SSet.{0}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    (SSet.realizationFundamentalGroupoidFunctor X).map w.toHom =
      Path.Homotopic.Quotient.mk w.realizedPath :=
  SSet.RealizationEdgeWord.map_toHom_eq_mk_realizedPath w

end RepresentationAndMap

section ConditionalFaithfulness

variable {X : SSet.{u}}
  (happrox : ∀ {a b : SSet.FundamentalGroupoid X}
    (w w' : SSet.RealizationEdgeWord X a b),
    w.realizedPath.Homotopy w'.realizedPath → w.toHom = w'.toHom)

example : (SSet.realizationFundamentalGroupoidFunctor X).Faithful :=
  SSet.RealizationEdgeWord.faithful_of_edgeWord_homotopy happrox

example {a b : SSet.FundamentalGroupoid X} {f g : a ⟶ b}
    (hfg : (SSet.realizationFundamentalGroupoidFunctor X).map f =
      (SSet.realizationFundamentalGroupoidFunctor X).map g) : f = g := by
  let _ : (SSet.realizationFundamentalGroupoidFunctor X).Faithful :=
    SSet.RealizationEdgeWord.faithful_of_edgeWord_homotopy happrox
  exact Functor.map_injective
    (SSet.realizationFundamentalGroupoidFunctor X) hfg

end ConditionalFaithfulness

/-- error: Unknown constant `SSet.RealizationEdgeWord.eq_toHom_of_realizedPath_homotopy` -/
#guard_msgs (error, substring := true) in
#check SSet.RealizationEdgeWord.eq_toHom_of_realizedPath_homotopy

/-- error: Unknown constant `SSet.realizationFundamentalGroupoidFunctor_faithful` -/
#guard_msgs (error, substring := true) in
#check SSet.realizationFundamentalGroupoidFunctor_faithful

#print axioms SSet.RealizationEdgeWord.exists_word
#print axioms SSet.RealizationEdgeWord.map_toHom_eq_mk_realizedPath
#print axioms SSet.RealizationEdgeWord.faithful_of_edgeWord_homotopy

end RealizationEdgeWordTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
