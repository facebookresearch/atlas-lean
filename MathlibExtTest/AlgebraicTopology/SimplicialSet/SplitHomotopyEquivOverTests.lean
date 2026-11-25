/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SplitHomotopyEquivOver

import MathlibExt.AlgebraicTopology.ModelCategory.Proper
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexFirstContraction

/-!
# Tests for split simplicial homotopy equivalences over a base

These tests cover identity data, contraction of `Δ[1]` over the terminal
simplicial set, its nonidentity pullback/product projection, both homotopy
endpoints, the over-base equation, realization weak-equivalence membership,
ordinary and mixed universe levels, standard axioms, and negative instance
claims.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace SplitHomotopyEquivOverTests

private noncomputable def identitySplit (X : SSet.{u}) :
    SSet.SplitHomotopyEquivOver (𝟙 X) where
  section_ := 𝟙 X
  section_comp := by simp
  homotopyOver := by
    simpa using SSet.HomotopyRelOver.refl (𝟙 X)
      (⊥ : X.Subcomplex) (𝟙 X)

section Identity

variable (X : SSet.{u})

example : SSet.SplitHomotopyEquivOver (𝟙 X) :=
  identitySplit X

example : (identitySplit X).section_ = 𝟙 X :=
  rfl

example : (identitySplit X).section_ ≫ 𝟙 X = 𝟙 X :=
  (identitySplit X).section_comp

example : SSet.Homotopy
    ((𝟙 X) ≫ (identitySplit X).section_) (𝟙 X) :=
  (identitySplit X).homotopyOver.toHomotopyRel.toHomotopy

example : SSet.realizationWeakEquivalences (𝟙 X) :=
  (identitySplit X).mem_realizationWeakEquivalences

end Identity

private noncomputable def firstVertexSection :
    (⊤_ SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)

private noncomputable def intervalProjection :
    (Δ[1] : SSet.{u}) ⟶ (⊤_ SSet.{u}) :=
  terminal.from _

private noncomputable def intervalSplit :
    SSet.SplitHomotopyEquivOver intervalProjection.{u} where
  section_ := firstVertexSection.{u}
  section_comp := terminal.hom_ext _ _
  homotopyOver :=
    { toHomotopyRel :=
        { h := (SSet.stdSimplex.homotopyConstFirstId.{u} 1).h
          h₀ := by
            exact (SSet.stdSimplex.homotopyConstFirstId.{u} 1).h₀.trans
              (by rfl)
          h₁ :=
            (SSet.stdSimplex.homotopyConstFirstId.{u} 1).h₁
          stationary := by
            intro n x hx t
            cases hx }
      over := terminal.hom_ext _ _ }

section Interval

example : SSet.SplitHomotopyEquivOver
    intervalProjection.{u} :=
  intervalSplit.{u}

example :
    intervalSplit.{u}.section_ ≫ intervalProjection.{u} =
      𝟙 (⊤_ SSet.{u}) :=
  intervalSplit.{u}.section_comp

example : SSet.Homotopy
    (intervalProjection.{u} ≫ intervalSplit.{u}.section_)
    (𝟙 (Δ[1] : SSet.{u})) :=
  intervalSplit.{u}.homotopyOver.toHomotopyRel.toHomotopy

example :
    intervalSplit.{u}.homotopyOver.h ≫ intervalProjection.{u} =
      fst (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        ((intervalProjection.{u} ≫ intervalSplit.{u}.section_) ≫
          intervalProjection.{u}) :=
  intervalSplit.{u}.homotopyOver.over

example : SSet.realizationWeakEquivalences
    intervalProjection.{u} :=
  intervalSplit.{u}.mem_realizationWeakEquivalences

end Interval

section BaseChange

variable (X : SSet.{u})

private noncomputable def terminalBaseMap :
    X ⟶ (⊤_ SSet.{u}) :=
  terminal.from _

/-- Pulling the interval contraction back over `X` gives the nontrivial
contractible-factor projection modelled as a pullback over the point. -/
private noncomputable def intervalProductSplit :
    SSet.SplitHomotopyEquivOver
      (pullback.fst (terminalBaseMap X) intervalProjection.{u}) :=
  intervalSplit.{u}.baseChange (terminalBaseMap X)

example :
    (intervalProductSplit X).section_ ≫
        pullback.fst (terminalBaseMap X) intervalProjection.{u} =
      𝟙 X :=
  (intervalProductSplit X).section_comp

example :
    SSet.ι₀ ≫ (intervalProductSplit X).homotopyOver.h =
      pullback.fst (terminalBaseMap X) intervalProjection.{u} ≫
        (intervalProductSplit X).section_ :=
  (intervalProductSplit X).homotopyOver.h₀

example :
    SSet.ι₁ ≫ (intervalProductSplit X).homotopyOver.h =
      𝟙 (pullback (terminalBaseMap X) intervalProjection.{u}) :=
  (intervalProductSplit X).homotopyOver.h₁

example :
    (intervalProductSplit X).homotopyOver.h =
      SSet.SplitHomotopyEquivOver.baseChangeHomotopyMap
        intervalSplit.{u} (terminalBaseMap X) :=
  rfl

example :
    (intervalProductSplit X).homotopyOver.h ≫
        pullback.fst (terminalBaseMap X) intervalProjection.{u} =
      fst
          (pullback (terminalBaseMap X) intervalProjection.{u})
          (Δ[1] : SSet.{u}) ≫
        pullback.fst (terminalBaseMap X) intervalProjection.{u} :=
  SSet.SplitHomotopyEquivOver.baseChangeHomotopyMap_fst
    intervalSplit.{u} (terminalBaseMap X)

example :
    (intervalProductSplit X).homotopyOver.h ≫
        pullback.fst (terminalBaseMap X) intervalProjection.{u} =
      fst
          (pullback (terminalBaseMap X) intervalProjection.{u})
          (Δ[1] : SSet.{u}) ≫
        (((pullback.fst (terminalBaseMap X)
              intervalProjection.{u}) ≫
            (intervalProductSplit X).section_) ≫
          pullback.fst (terminalBaseMap X)
            intervalProjection.{u}) :=
  (intervalProductSplit X).homotopyOver.over

example : SSet.realizationWeakEquivalences
    (pullback.fst (terminalBaseMap X) intervalProjection.{u}) :=
  intervalSplit.{u}.baseChange_fst_mem_realizationWeakEquivalences
    (terminalBaseMap X)

end BaseChange

section Universes

variable (X₀ : SSet.{0}) (X₁ : SSet.{1})

example : SSet.realizationWeakEquivalences (𝟙 X₀) :=
  (identitySplit X₀).mem_realizationWeakEquivalences

example : SSet.realizationWeakEquivalences (𝟙 X₁) :=
  (identitySplit X₁).mem_realizationWeakEquivalences

variable (Xuv : SSet.{max u v})

example : SSet.realizationWeakEquivalences (𝟙 Xuv) :=
  (identitySplit Xuv).mem_realizationWeakEquivalences

example : SSet.realizationWeakEquivalences
    (pullback.fst (terminalBaseMap Xuv)
      intervalProjection.{max u v}) :=
  intervalSplit.{max u v}.baseChange_fst_mem_realizationWeakEquivalences
    (terminalBaseMap Xuv)

end Universes

section Nonclaims

variable {E B : SSet.{u}} (p : E ⟶ B)

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth Fibration p

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth HomotopicalAlgebra.ModelCategory SSet.{u}

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth HomotopicalAlgebra.IsRightProper SSet.{u}

end Nonclaims

#print axioms SSet.SplitHomotopyEquivOver
#print axioms SSet.SplitHomotopyEquivOver.baseChange
#print axioms SSet.SplitHomotopyEquivOver.mem_realizationWeakEquivalences
#print axioms SSet.SplitHomotopyEquivOver.baseChange_fst_mem_realizationWeakEquivalences

end SplitHomotopyEquivOverTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
