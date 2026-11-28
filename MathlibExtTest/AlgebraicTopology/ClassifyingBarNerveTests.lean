/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monad.TopologicalClassifyingBar
public import MathlibExt.CategoryTheory.Monad.ClassifyingNerveData
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Topology.Instances.Discrete
public meta import Mathlib.Tactic.FinCases

/-!
# A noncommutative finite-group projection on classifying bars

The finite groups are `H = Perm (Fin 3)` and `G = H × H`, with discrete
topologies. The group map is the first projection. Let `a = (0 1)` and
`b = (1 2)`, and use the two source entries `g = (a,1)` and `h = (b,a)`.
Their projected degree-two word is `(a,b)`. Its interior face has product
`a*b`, with value one at zero; reversing the multiplication gives value two.

The tests evaluate the actual `TopCat` classifying-bar map in degrees one
and two, its endpoint and interior faces, and insertion of the unit by a
degeneracy. Separately, the exported evaluated cartesian bar is compared
with the nerve of `SingleObj Gᵐᵒᵖ` through its canonical data isomorphism.
This checks the same multiplication order and unit position on the nerve.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Monad Opposite
open scoped MonoidalCategory

namespace MathlibExtTest.AlgebraicTopology.ClassifyingBarNerve

private abbrev H := Equiv.Perm (Fin 3)

private instance : TopologicalSpace H := ⊥

private instance : DiscreteTopology H := discreteTopology_bot H

private instance : ContinuousMul H := ⟨continuous_of_discreteTopology⟩

private abbrev G := H × H

private abbrev π : G →ₜ* H := ContinuousMonoidHom.fst H H

private abbrev a : H := Equiv.swap (0 : Fin 3) 1

private abbrev b : H := Equiv.swap (1 : Fin 3) 2

private abbrev g : G := (a, 1)

private abbrev h : G := (b, a)

private def pairWord {J : Type} (x y : J) : Fin 2 → J :=
  fun i => if i = 0 then x else y

private def barOne (J : Type) [TopologicalSpace J] [Monoid J] [ContinuousMul J]
    (x : J) : ((BBar J).obj (op (SimplexCategory.mk 1)) : Type) :=
  (PUnit.unit, (x, PUnit.unit))

private def barTwo (J : Type) [TopologicalSpace J] [Monoid J] [ContinuousMul J]
    (x y : J) : ((BBar J).obj (op (SimplexCategory.mk 2)) : Type) :=
  (PUnit.unit, (x, (y, PUnit.unit)))

private lemma barOne_coordinate (J : Type) [TopologicalSpace J] [Monoid J]
    [ContinuousMul J] (x : J) :
    BBarDegreeHomeomorph J 1 (barOne J x) = fun _ : Fin 1 => x := by
  funext i
  fin_cases i
  rfl

private lemma barTwo_coordinate (J : Type) [TopologicalSpace J] [Monoid J]
    [ContinuousMul J] (x y : J) :
    BBarDegreeHomeomorph J 2 (barTwo J x y) = pairWord x y := by
  funext i
  fin_cases i <;> rfl

private lemma powOne_component (X : TopCat.{0}) :
    (monadPowHom (topTensorMonadHom G π) 1).app X = (topTensorMonadHom G π).app X := by
  have hpow := monadPowHom_succ_app (topTensorMonadHom G π) 0 X
  change (monadPowHom (topTensorMonadHom G π) 1).app X =
    𝟙 ((tensorMonad (GTop G)).obj X) ≫ (topTensorMonadHom G π).app X at hpow
  exact hpow.trans (Category.id_comp _)

private lemma map_barOne (x : G) :
    (BBarMap G π).app (op (SimplexCategory.mk 1)) (barOne G x) = barOne H (π x) := by
  refine (ConcreteCategory.congr_hom (BBarMap_app_op_mk G π 1) (barOne G x)).trans ?_
  rw [powOne_component]
  change (topPoint ◁ (topTensorMonadHom G π).app topPoint) (barOne G x) = barOne H (π x)
  rw [TopCat.whiskerLeft_apply]
  simp only [barOne, topTensorMonadHom_app]

private lemma map_barTwo (x y : G) :
    (BBarMap G π).app (op (SimplexCategory.mk 2)) (barTwo G x y) =
      barTwo H (π x) (π y) := by
  refine (ConcreteCategory.congr_hom (BBarMap_app_op_mk G π 2) (barTwo G x y)).trans ?_
  rw [monadPowHom_succ_app, powOne_component]
  change (PUnit.unit,
    (GTop H ◁ (topTensorMonadHom G π).app topPoint)
      ((topTensorMonadHom G π).app (GTop G ⊗ topPoint) (x, (y, PUnit.unit)))) =
    (PUnit.unit, (π x, (π y, PUnit.unit)))
  rw [topTensorMonadHom_app, TopCat.whiskerLeft_apply, topTensorMonadHom_app]

private abbrev imageOne :=
  (BBarMap G π).app (op (SimplexCategory.mk 1)) (barOne G g)

private abbrev imageTwo :=
  (BBarMap G π).app (op (SimplexCategory.mk 2)) (barTwo G g h)

private lemma imageTwo_coordinate :
    BBarDegreeHomeomorph H 2 imageTwo = pairWord a b :=
  (congrArg (BBarDegreeHomeomorph H 2) (map_barTwo g h)).trans
    (barTwo_coordinate H a b)

private lemma projected_middle_face :
    BBarDegreeHomeomorph H 1
      ((BBar H).map (SimplexCategory.δ (1 : Fin 3)).op imageTwo) =
        fun _ : Fin 1 => a * b := by
  have hface := BBarDegreeHomeomorph_dInterior H 1 (0 : Fin 1) imageTwo
  change BBarDegreeHomeomorph H 1
    ((BBar H).map (SimplexCategory.δ (1 : Fin 3)).op imageTwo) =
      topTupleContract H 0 (BBarDegreeHomeomorph H 2 imageTwo) at hface
  calc
    _ = topTupleContract H 0 (pairWord a b) :=
      hface.trans (congrArg (topTupleContract H 0) imageTwo_coordinate)
    _ = _ := by funext i; fin_cases i; rfl

example : π g = a ∧ π h = b := ⟨rfl, rfl⟩

example : π (1, b) = 1 ∧ ((1, b) : G) ≠ 1 := by
  constructor
  · rfl
  · intro heq
    have hb := congrArg (fun x : G => x.2 (1 : Fin 3)) heq
    change (2 : Fin 3) = 1 at hb
    exact (by decide : (2 : Fin 3) ≠ 1) hb

example : π g ≠ 1 := by
  intro heq
  have hz := congrArg (fun σ : H => σ (0 : Fin 3)) heq
  change (1 : Fin 3) = 0 at hz
  exact (by decide : (1 : Fin 3) ≠ 0) hz

example : (BBarDegreeHomeomorph H 1 imageOne) 0 (0 : Fin 3) = 1 := by
  have hc := (congrArg (BBarDegreeHomeomorph H 1) (map_barOne g)).trans
    (barOne_coordinate H a)
  exact congrArg (fun t : Fin 1 → H => t 0 (0 : Fin 3)) hc

example : (BBarDegreeHomeomorph H 2 imageTwo) 0 (0 : Fin 3) = 1 ∧
    (BBarDegreeHomeomorph H 2 imageTwo) 1 (1 : Fin 3) = 2 := by
  constructor
  · exact congrArg (fun t : Fin 2 → H => t 0 (0 : Fin 3)) imageTwo_coordinate
  · exact congrArg (fun t : Fin 2 → H => t 1 (1 : Fin 3)) imageTwo_coordinate

example : (BBarDegreeHomeomorph H 1
    ((BBar H).map (SimplexCategory.δ (0 : Fin 3)).op imageTwo)) 0 (1 : Fin 3) = 2 := by
  have hc := (BBarDegreeHomeomorph_d0 H 1 imageTwo).trans
    (congrArg Fin.tail imageTwo_coordinate)
  exact congrArg (fun t : Fin 1 → H => t 0 (1 : Fin 3)) hc

example : (BBarDegreeHomeomorph H 1
    ((BBar H).map (SimplexCategory.δ (2 : Fin 3)).op imageTwo)) 0 (0 : Fin 3) = 1 := by
  have hc := (BBarDegreeHomeomorph_dLast H 1 imageTwo).trans
    (congrArg Fin.init imageTwo_coordinate)
  exact congrArg (fun t : Fin 1 → H => t 0 (0 : Fin 3)) hc

example : (BBarDegreeHomeomorph H 1
    ((BBar H).map (SimplexCategory.δ (1 : Fin 3)).op imageTwo)) 0 (0 : Fin 3) = 1 :=
  congrArg (fun t : Fin 1 → H => t 0 (0 : Fin 3)) projected_middle_face

example : (a * b) (0 : Fin 3) = 1 ∧ (b * a) (0 : Fin 3) = 2 := by decide

example : (BBar H).map (SimplexCategory.δ (1 : Fin 3)).op imageTwo =
    (BBarMap G π).app (op (SimplexCategory.mk 1))
      ((BBar G).map (SimplexCategory.δ (1 : Fin 3)).op (barTwo G g h)) :=
  (ConcreteCategory.congr_hom
    ((BBarMap G π).naturality (SimplexCategory.δ (1 : Fin 3)).op) (barTwo G g h)).symm

private lemma projected_degeneracy :
    BBarDegreeHomeomorph H 2
      ((BBarMap G π).app (op (SimplexCategory.mk 2))
        ((BBar G).map (SimplexCategory.σ (0 : Fin 2)).op (barOne G g))) =
      pairWord (1 : H) a := by
  have hn := ConcreteCategory.congr_hom
    ((BBarMap G π).naturality (SimplexCategory.σ (0 : Fin 2)).op) (barOne G g)
  have hc := (congrArg (BBarDegreeHomeomorph H 1) (map_barOne g)).trans
    (barOne_coordinate H a)
  calc
    _ = BBarDegreeHomeomorph H 2
        ((BBar H).map (SimplexCategory.σ (0 : Fin 2)).op imageOne) :=
      congrArg (BBarDegreeHomeomorph H 2) hn
    _ = topTupleInsert H 0 (fun _ : Fin 1 => a) :=
      (BBarDegreeHomeomorph_s H 1 0 imageOne).trans (congrArg (topTupleInsert H 0) hc)
    _ = _ := by funext i; fin_cases i <;> rfl

example : (BBarDegreeHomeomorph H 2
    ((BBarMap G π).app (op (SimplexCategory.mk 2))
      ((BBar G).map (SimplexCategory.σ (0 : Fin 2)).op (barOne G g)))) 0 (0 : Fin 3) = 0 ∧
    (BBarDegreeHomeomorph H 2
      ((BBarMap G π).app (op (SimplexCategory.mk 2))
        ((BBar G).map (SimplexCategory.σ (0 : Fin 2)).op (barOne G g)))) 1 (0 : Fin 3) = 1 := by
  constructor
  · exact congrArg (fun t : Fin 2 → H => t 0 (0 : Fin 3)) projected_degeneracy
  · exact congrArg (fun t : Fin 2 → H => t 1 (0 : Fin 3)) projected_degeneracy

attribute [local instance] typeMonObj pointModObj

private abbrev pointIndex : Discrete PUnit.{1} := Discrete.mk PUnit.unit

private def dataOne (J : Type) [Monoid J] (x : J) : (barEvalData J pointIndex).obj 1 :=
  (barTupleEquiv J pointIndex 1).symm (fun _ : Fin 1 => x)

private def dataTwo (J : Type) [Monoid J] (x y : J) : (barEvalData J pointIndex).obj 2 :=
  (barTupleEquiv J pointIndex 2).symm (pairWord x y)

private lemma data_comparison_coordinate (J : Type) [Monoid J] (n : ℕ)
    (x : (barEvalData J pointIndex).obj n) :
    nerveTupleEquiv J n ((tupleIso J pointIndex n).hom x) =
      barTupleEquiv J pointIndex n x := by
  change nerveTupleEquiv J n
    ((nerveTupleEquiv J n).symm (barTupleEquiv J pointIndex n x)) = _
  exact (nerveTupleEquiv J n).apply_symm_apply _

private lemma nerve_middle_coordinate :
    nerveTupleEquiv G 1
      ((nerveOppData G).δ (1 : Fin 3)
        ((tupleIso G pointIndex 2).hom (dataTwo G g h))) =
      fun _ : Fin 1 => g * h := by
  have hn := ConcreteCategory.congr_hom
    (tupleIso_face G pointIndex (1 : Fin 3)) (dataTwo G g h)
  calc
    _ = nerveTupleEquiv G 1
        ((tupleIso G pointIndex 1).hom
          ((barEvalData G pointIndex).δ (1 : Fin 3) (dataTwo G g h))) :=
      congrArg (nerveTupleEquiv G 1) hn
    _ = barTupleEquiv G pointIndex 1
        ((barEvalData G pointIndex).δ (1 : Fin 3) (dataTwo G g h)) :=
      data_comparison_coordinate G 1 _
    _ = tupleMulAt G 1 (pairWord g h) 0 :=
      (barTuple_middle_face G pointIndex 1 (dataTwo G g h) 0 1 rfl).trans
        (congrArg (fun t : Fin 2 → G => tupleMulAt G 1 t 0)
          ((barTupleEquiv G pointIndex 2).apply_symm_apply (pairWord g h)))
    _ = _ := by funext i; fin_cases i; rfl

example : π ((nerveTupleEquiv G 2
    ((tupleIso G pointIndex 2).hom (dataTwo G g h))) 0) (0 : Fin 3) = 1 ∧
    π ((nerveTupleEquiv G 2
      ((tupleIso G pointIndex 2).hom (dataTwo G g h))) 1) (1 : Fin 3) = 2 := by
  have hc := (data_comparison_coordinate G 2 (dataTwo G g h)).trans
    ((barTupleEquiv G pointIndex 2).apply_symm_apply (pairWord g h))
  constructor
  · exact congrArg (fun t : Fin 2 → G => π (t 0) (0 : Fin 3)) hc
  · exact congrArg (fun t : Fin 2 → G => π (t 1) (1 : Fin 3)) hc

example : π ((nerveTupleEquiv G 1
    ((nerveOppData G).δ (1 : Fin 3)
      ((tupleIso G pointIndex 2).hom (dataTwo G g h)))) 0) (0 : Fin 3) = 1 :=
  congrArg (fun t : Fin 1 → G => π (t 0) (0 : Fin 3)) nerve_middle_coordinate

private lemma nerve_degeneracy_coordinate :
    nerveTupleEquiv G 2
      ((nerveOppData G).σ (0 : Fin 2)
        ((tupleIso G pointIndex 1).hom (dataOne G g))) =
      pairWord (1 : G) g := by
  have hn := ConcreteCategory.congr_hom
    (tupleIso_degeneracy G pointIndex (0 : Fin 2)) (dataOne G g)
  calc
    _ = nerveTupleEquiv G 2
        ((tupleIso G pointIndex 2).hom
          ((barEvalData G pointIndex).σ (0 : Fin 2) (dataOne G g))) :=
      congrArg (nerveTupleEquiv G 2) hn
    _ = barTupleEquiv G pointIndex 2
        ((barEvalData G pointIndex).σ (0 : Fin 2) (dataOne G g)) :=
      data_comparison_coordinate G 2 _
    _ = tupleInsAt G 1 (fun _ : Fin 1 => g) 0 :=
      (barTuple_degen G pointIndex 1 (dataOne G g) 0).trans
        (congrArg (fun t : Fin 1 → G => tupleInsAt G 1 t 0)
          ((barTupleEquiv G pointIndex 1).apply_symm_apply (fun _ : Fin 1 => g)))
    _ = _ := by funext i; fin_cases i <;> rfl

example : π ((nerveTupleEquiv G 2
    ((nerveOppData G).σ (0 : Fin 2)
      ((tupleIso G pointIndex 1).hom (dataOne G g)))) 0) (0 : Fin 3) = 0 ∧
    π ((nerveTupleEquiv G 2
      ((nerveOppData G).σ (0 : Fin 2)
        ((tupleIso G pointIndex 1).hom (dataOne G g)))) 1) (0 : Fin 3) = 1 := by
  constructor
  · exact congrArg (fun t : Fin 2 → G => π (t 0) (0 : Fin 3)) nerve_degeneracy_coordinate
  · exact congrArg (fun t : Fin 2 → G => π (t 1) (0 : Fin 3)) nerve_degeneracy_coordinate

end MathlibExtTest.AlgebraicTopology.ClassifyingBarNerve
