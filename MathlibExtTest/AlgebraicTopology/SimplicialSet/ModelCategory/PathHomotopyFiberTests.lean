/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathHomotopyFiber

/-!
# Tests for explicit simplicial path homotopy fibers

The tests lock the generic and based endpoint orientations, compatible-map
coherence, universe polymorphism, strict-comparison direction, and privacy.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
  CategoryTheory.MonoidalCategory Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace PathHomotopyFiberTests

section Generic

variable {X Y B X' Y' B' X'' Y'' B'' Z : SSet.{u}}
variable {f : X ⟶ B} {g : Y ⟶ B}
variable {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
variable {f'' : X'' ⟶ B''} {g'' : Y'' ⟶ B''}

example : SSet.pathHomotopyPullback f g ⟶ X :=
  SSet.pathHomotopyPullbackLeft f g

example : SSet.pathHomotopyPullback f g ⟶ Y :=
  SSet.pathHomotopyPullbackRight f g

example : SSet.pathHomotopyPullback f g ⟶ SSet.pathSpace B :=
  SSet.pathHomotopyPullbackPath f g

example : SSet.pathHomotopyPullbackPath f g ≫ SSet.eval₀ =
    SSet.pathHomotopyPullbackLeft f g ≫ f :=
  SSet.pathHomotopyPullbackPath_evalZero f g

example : SSet.pathHomotopyPullbackPath f g ≫ SSet.eval₁ =
    SSet.pathHomotopyPullbackRight f g ≫ g :=
  SSet.pathHomotopyPullbackPath_evalOne f g

example {a c : Z ⟶ SSet.pathHomotopyPullback f g}
    (hleft : a ≫ SSet.pathHomotopyPullbackLeft f g =
      c ≫ SSet.pathHomotopyPullbackLeft f g)
    (hright : a ≫ SSet.pathHomotopyPullbackRight f g =
      c ≫ SSet.pathHomotopyPullbackRight f g)
    (hpath : a ≫ SSet.pathHomotopyPullbackPath f g =
      c ≫ SSet.pathHomotopyPullbackPath f g) : a = c :=
  SSet.pathHomotopyPullback_hom_ext hleft hright hpath

variable (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
variable (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g')

example : SSet.pathHomotopyPullback f g ⟶
    SSet.pathHomotopyPullback f' g' :=
  SSet.pathHomotopyPullbackMap l r h hf hg

example : SSet.pathHomotopyPullbackMap l r h hf hg ≫
      SSet.pathHomotopyPullbackLeft f' g' =
    SSet.pathHomotopyPullbackLeft f g ≫ l := by simp

example : SSet.pathHomotopyPullbackMap l r h hf hg ≫
      SSet.pathHomotopyPullbackRight f' g' =
    SSet.pathHomotopyPullbackRight f g ≫ r := by simp

example : SSet.pathHomotopyPullbackMap l r h hf hg ≫
      SSet.pathHomotopyPullbackPath f' g' =
    SSet.pathHomotopyPullbackPath f g ≫
      (ihom (Δ[1] : SSet.{u})).map h := by simp

example : SSet.pathHomotopyPullbackMap (𝟙 X) (𝟙 Y) (𝟙 B)
      (by simp) (by simp) = 𝟙 (SSet.pathHomotopyPullback f g) :=
  SSet.pathHomotopyPullbackMap_id f g

variable (l' : X' ⟶ X'') (r' : Y' ⟶ Y'') (h' : B' ⟶ B'')
variable (hf' : f' ≫ h' = l' ≫ f'') (hg' : g' ≫ h' = r' ≫ g'')

example : SSet.pathHomotopyPullbackMap l r h hf hg ≫
      SSet.pathHomotopyPullbackMap l' r' h' hf' hg' =
    SSet.pathHomotopyPullbackMap (l ≫ l') (r ≫ r') (h ≫ h')
      (by
        calc
          f ≫ (h ≫ h') = (f ≫ h) ≫ h' := (Category.assoc _ _ _).symm
          _ = (l ≫ f') ≫ h' := by rw [hf]
          _ = l ≫ (f' ≫ h') := Category.assoc _ _ _
          _ = l ≫ (l' ≫ f'') := by rw [hf']
          _ = (l ≫ l') ≫ f'' := (Category.assoc _ _ _).symm)
      (by
        calc
          g ≫ (h ≫ h') = (g ≫ h) ≫ h' := (Category.assoc _ _ _).symm
          _ = (r ≫ g') ≫ h' := by rw [hg]
          _ = r ≫ (g' ≫ h') := Category.assoc _ _ _
          _ = r ≫ (r' ≫ g'') := by rw [hg']
          _ = (r ≫ r') ≫ g'' := (Category.assoc _ _ _).symm) :=
  SSet.pathHomotopyPullbackMap_comp l r h l' r' h' hf hg hf' hg'

#guard_msgs (error, substring := true) in
example : SSet.pathHomotopyPullback f g ⟶
    SSet.pathHomotopyPullback f' g' :=
  SSet.pathHomotopyPullbackMap l r h hf

#guard_msgs (error, substring := true) in
example : SSet.pathHomotopyPullback f g ⟶
    SSet.pathHomotopyPullback f' g' :=
  SSet.pathHomotopyPullbackMap l r h (hg := hg)

end Generic

section Based

variable {X B X' B' X'' B'' Z : SSet.{u}}
variable {f : X ⟶ B} {f' : X' ⟶ B'} {f'' : X'' ⟶ B''}
variable {b : B _⦋0⦌} {b' : B' _⦋0⦌} {b'' : B'' _⦋0⦌}

example : SSet.pathHomotopyFiber f b ⟶ X :=
  SSet.pathHomotopyFiberToTotal f b

example : SSet.pathHomotopyFiber f b ⟶ SSet.pathSpace B :=
  SSet.pathHomotopyFiberPath f b

example : SSet.pathHomotopyFiberPath f b ≫ SSet.eval₀ =
    SSet.pathHomotopyFiberToTotal f b ≫ f :=
  SSet.pathHomotopyFiberPath_evalZero f b

example : SSet.pathHomotopyFiberPath f b ≫ SSet.eval₁ =
    SSet.const (X := SSet.pathHomotopyFiber f b) b :=
  SSet.pathHomotopyFiberPath_evalOne f b

example {a c : Z ⟶ SSet.pathHomotopyFiber f b}
    (htotal : a ≫ SSet.pathHomotopyFiberToTotal f b =
      c ≫ SSet.pathHomotopyFiberToTotal f b)
    (hpath : a ≫ SSet.pathHomotopyFiberPath f b =
      c ≫ SSet.pathHomotopyFiberPath f b) : a = c :=
  SSet.pathHomotopyFiber_hom_ext htotal hpath

variable (l : X ⟶ X') (h : B ⟶ B') (hf : f ≫ h = l ≫ f')
variable (hb : h.app _ b = b')

example : SSet.pathHomotopyFiber f b ⟶ SSet.pathHomotopyFiber f' b' :=
  SSet.pathHomotopyFiberMap l h hf hb

example : SSet.pathHomotopyFiberMap l h hf hb ≫
      SSet.pathHomotopyFiberToTotal f' b' =
    SSet.pathHomotopyFiberToTotal f b ≫ l := by simp

example : SSet.pathHomotopyFiberMap l h hf hb ≫
      SSet.pathHomotopyFiberPath f' b' =
    SSet.pathHomotopyFiberPath f b ≫
      (ihom (Δ[1] : SSet.{u})).map h := by simp

example : SSet.pathHomotopyFiberMap (𝟙 X) (𝟙 B) (by simp) (by simp) =
    𝟙 (SSet.pathHomotopyFiber f b) :=
  SSet.pathHomotopyFiberMap_id f b

variable (l' : X' ⟶ X'') (h' : B' ⟶ B'')
variable (hf' : f' ≫ h' = l' ≫ f'') (hb' : h'.app _ b' = b'')

example : SSet.pathHomotopyFiberMap l h hf hb ≫
      SSet.pathHomotopyFiberMap l' h' hf' hb' =
    SSet.pathHomotopyFiberMap (l ≫ l') (h ≫ h')
      (by
        calc
          f ≫ (h ≫ h') = (f ≫ h) ≫ h' := (Category.assoc _ _ _).symm
          _ = (l ≫ f') ≫ h' := by rw [hf]
          _ = l ≫ (f' ≫ h') := Category.assoc _ _ _
          _ = l ≫ (l' ≫ f'') := by rw [hf']
          _ = (l ≫ l') ≫ f'' := (Category.assoc _ _ _).symm)
      (by
        change h'.app _ (h.app _ b) = b''
        rw [hb, hb']) :=
  SSet.pathHomotopyFiberMap_comp l h l' h' hf hf' hb hb'

#guard_msgs (error, substring := true) in
example : SSet.pathHomotopyFiber f b ⟶ SSet.pathHomotopyFiber f' b' :=
  SSet.pathHomotopyFiberMap l h hf

end Based

section Strict

variable {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌)

example : (SSet.Subcomplex.fiber f b : SSet.{u}) ⟶
    SSet.pathHomotopyFiber f b :=
  SSet.strictFiberToPathHomotopyFiber f b

example : SSet.strictFiberToPathHomotopyFiber f b ≫
      SSet.pathHomotopyFiberToTotal f b =
    (SSet.Subcomplex.fiber f b).ι := by simp

example : SSet.strictFiberToPathHomotopyFiber f b ≫
      SSet.pathHomotopyFiberPath f b =
    SSet.const b ≫ SSet.constPath B := by simp

#guard_msgs (error, substring := true) in
#check SSet.pathHomotopyFiberToStrictFiber

#guard_msgs (error, substring := true) in
#check SSet.pathHomotopyFiber_weakEquivalence

#guard_msgs (error, substring := true) in
#check SSet.pathHomotopyFiberBarComparison

end Strict

section OppositeEndpoints

private def intervalVertex (i : Fin 2) : (Δ[1] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.const 1 i _

private theorem intervalVertex_zero_ne_one :
    intervalVertex 0 ≠ intervalVertex 1 := by
  intro h
  have h' := congrArg SSet.stdSimplex.obj₀Equiv h
  simp [intervalVertex, SSet.stdSimplex.const] at h'

private def endpointZero : (Δ[0] : SSet.{0}) ⟶ Δ[1] :=
  SSet.const (intervalVertex 0)

private noncomputable def deltaZeroIsoUnit :
    (Δ[0] : SSet.{0}) ≅ (𝟙_ SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit

private noncomputable def identityIntervalPath :
    (Δ[0] : SSet.{0}) ⟶ SSet.pathSpace (Δ[1] : SSet.{0}) :=
  MonoidalClosed.curry
    (((Δ[1] : SSet.{0}) ◁ deltaZeroIsoUnit.hom) ≫
      (ρ_ (Δ[1] : SSet.{0})).hom)

private theorem identityIntervalPath_evalZero :
    identityIntervalPath ≫ SSet.eval₀ = endpointZero := by
  rw [SSet.comp_eval₀_eq_ι₀_braiding_uncurry]
  rw [identityIntervalPath, MonoidalClosed.uncurry_curry]
  have he : deltaZeroIsoUnit.hom =
      CartesianMonoidalCategory.toUnit (Δ[0] : SSet.{0}) :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  calc
    SSet.ι₀ ≫ (β_ (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0})).hom ≫
          ((Δ[1] : SSet.{0}) ◁ deltaZeroIsoUnit.hom) ≫
          (ρ_ (Δ[1] : SSet.{0})).hom =
        SSet.ι₀ ≫ (β_ (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0})).hom ≫
          CartesianMonoidalCategory.fst (Δ[1] : SSet.{0}) Δ[0] := by
      rw [he]
      simpa only [Category.assoc] using congrArg
        (fun k => SSet.ι₀ ≫
          (β_ (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0})).hom ≫ k)
        (CartesianMonoidalCategory.whiskerLeft_toUnit_comp_rightUnitor_hom
          (Δ[1] : SSet.{0}) Δ[0])
    _ = SSet.ι₀ ≫
        CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) Δ[1] := by
      simpa only [Category.assoc] using congrArg (fun k => SSet.ι₀ ≫ k)
        (CartesianMonoidalCategory.braiding_hom_fst
          (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}))
    _ = endpointZero := by
      simp [endpointZero, intervalVertex, SSet.stdSimplex.const]

private theorem identityIntervalPath_evalOne :
    identityIntervalPath ≫ SSet.eval₁ =
      SSet.const (intervalVertex 1) := by
  rw [SSet.comp_eval₁_eq_ι₁_braiding_uncurry]
  rw [identityIntervalPath, MonoidalClosed.uncurry_curry]
  have he : deltaZeroIsoUnit.hom =
      CartesianMonoidalCategory.toUnit (Δ[0] : SSet.{0}) :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  calc
    SSet.ι₁ ≫ (β_ (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0})).hom ≫
          ((Δ[1] : SSet.{0}) ◁ deltaZeroIsoUnit.hom) ≫
          (ρ_ (Δ[1] : SSet.{0})).hom =
        SSet.ι₁ ≫ (β_ (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0})).hom ≫
          CartesianMonoidalCategory.fst (Δ[1] : SSet.{0}) Δ[0] := by
      rw [he]
      simpa only [Category.assoc] using congrArg
        (fun k => SSet.ι₁ ≫
          (β_ (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0})).hom ≫ k)
        (CartesianMonoidalCategory.whiskerLeft_toUnit_comp_rightUnitor_hom
          (Δ[1] : SSet.{0}) Δ[0])
    _ = SSet.ι₁ ≫
        CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) Δ[1] := by
      simpa only [Category.assoc] using congrArg (fun k => SSet.ι₁ ≫ k)
        (CartesianMonoidalCategory.braiding_hom_fst
          (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}))
    _ = SSet.const (intervalVertex 1) := by
      simp [intervalVertex, SSet.stdSimplex.const]

private theorem testTensorLeftIsoProd_hom_fst (X Y : SSet.{0}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        Limits.prod.fst =
      SemiCartesianMonoidalCategory.fst X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.left⟩

private theorem testTensorLeftIsoProd_hom_snd (X Y : SSet.{0}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        Limits.prod.snd =
      SemiCartesianMonoidalCategory.snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.right⟩

private noncomputable def testPathEndpointPair :
    SSet.pathSpace (Δ[1] : SSet.{0}) ⟶ Δ[1] ⨯ Δ[1] :=
  SSet.evalPair ≫
    (CartesianMonoidalCategory.tensorLeftIsoProd
      (Δ[1] : SSet.{0})).hom.app Δ[1]

set_option backward.isDefEq.respectTransparency false in
private theorem testPathEndpointPair_fst :
    testPathEndpointPair ≫ Limits.prod.fst =
      (SSet.eval₀ : SSet.pathSpace (Δ[1] : SSet.{0}) ⟶ Δ[1]) := by
  rw [testPathEndpointPair, Category.assoc,
    testTensorLeftIsoProd_hom_fst]
  exact SSet.evalPair_fst

set_option backward.isDefEq.respectTransparency false in
private theorem testPathEndpointPair_snd :
    testPathEndpointPair ≫ Limits.prod.snd =
      (SSet.eval₁ : SSet.pathSpace (Δ[1] : SSet.{0}) ⟶ Δ[1]) := by
  rw [testPathEndpointPair, Category.assoc,
    testTensorLeftIsoProd_hom_snd]
  exact SSet.evalPair_snd

private instance strictOppositeEndpointEmpty : IsEmpty
    (((SSet.Subcomplex.fiber endpointZero (intervalVertex 1) : SSet.{0}).obj
      (Opposite.op ⦋0⦌))) := by
  constructor
  intro z
  have hz := (SSet.Subcomplex.mem_fiber_obj_zero_iff
    endpointZero (intervalVertex 1)).mp z.property
  apply intervalVertex_zero_ne_one
  simpa [endpointZero] using hz

private noncomputable def oppositeEndpointPathPoint :
    (Δ[0] : SSet.{0}) ⟶
      SSet.pathHomotopyFiber endpointZero (intervalVertex 1) := by
  with_unfolding_all
    exact pullback.lift
      (Limits.prod.lift (𝟙 _) (𝟙 _))
      identityIntervalPath
      (by
        apply Limits.prod.hom_ext
        · simp only [Category.assoc, Limits.prod.map_fst]
          change endpointZero =
            identityIntervalPath ≫ testPathEndpointPair ≫ Limits.prod.fst
          rw [testPathEndpointPair_fst]
          exact identityIntervalPath_evalZero.symm
        · simp only [Category.assoc, Limits.prod.map_snd]
          change SSet.const (intervalVertex 1) =
            identityIntervalPath ≫ testPathEndpointPair ≫ Limits.prod.snd
          rw [testPathEndpointPair_snd]
          exact identityIntervalPath_evalOne.symm)

private instance pathOppositeEndpointNonempty : Nonempty
    ((SSet.pathHomotopyFiber endpointZero (intervalVertex 1)).obj
      (Opposite.op ⦋0⦌)) :=
  ⟨oppositeEndpointPathPoint.app _
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))⟩

example : IsEmpty
    (((SSet.Subcomplex.fiber endpointZero (intervalVertex 1) : SSet.{0}).obj
      (Opposite.op ⦋0⦌))) := inferInstance

example : Nonempty
    ((SSet.pathHomotopyFiber endpointZero (intervalVertex 1)).obj
      (Opposite.op ⦋0⦌)) := inferInstance

end OppositeEndpoints

section Universes

example {X B : SSet.{1}} (f : X ⟶ B) (b : B _⦋0⦌) : SSet.{1} :=
  SSet.pathHomotopyFiber f b

example {X B : SSet.{0}} (f : X ⟶ B) (b : B _⦋0⦌) : SSet.{0} :=
  SSet.pathHomotopyFiber f b

example (B : SSet.{u}) : SSet.{u} :=
  SSet.pathHomotopyPullback (𝟙 B) (𝟙 B)

#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

end Universes

#check SSet.pathHomotopyPullback
#check SSet.pathHomotopyPullbackLeft
#check SSet.pathHomotopyPullbackRight
#check SSet.pathHomotopyPullbackPath
#check SSet.pathHomotopyPullbackPath_evalZero
#check SSet.pathHomotopyPullbackPath_evalOne
#check SSet.pathHomotopyPullback_hom_ext
#check SSet.pathHomotopyPullbackMap
#check SSet.pathHomotopyPullbackMap_left
#check SSet.pathHomotopyPullbackMap_right
#check SSet.pathHomotopyPullbackMap_path
#check SSet.pathHomotopyPullbackMap_id
#check SSet.pathHomotopyPullbackMap_comp
#check SSet.pathHomotopyFiber
#check SSet.pathHomotopyFiberToTotal
#check SSet.pathHomotopyFiberPath
#check SSet.pathHomotopyFiberPath_evalZero
#check SSet.pathHomotopyFiberPath_evalOne
#check SSet.pathHomotopyFiber_hom_ext
#check SSet.pathHomotopyFiberMap
#check SSet.pathHomotopyFiberMap_toTotal
#check SSet.pathHomotopyFiberMap_path
#check SSet.pathHomotopyFiberMap_id
#check SSet.pathHomotopyFiberMap_comp
#check SSet.strictFiberToPathHomotopyFiber
#check SSet.strictFiberToPathHomotopyFiber_toTotal
#check SSet.strictFiberToPathHomotopyFiber_path

#print axioms SSet.pathHomotopyPullback
#print axioms SSet.pathHomotopyPullbackLeft
#print axioms SSet.pathHomotopyPullbackRight
#print axioms SSet.pathHomotopyPullbackPath
#print axioms SSet.pathHomotopyPullbackPath_evalZero
#print axioms SSet.pathHomotopyPullbackPath_evalOne
#print axioms SSet.pathHomotopyPullback_hom_ext
#print axioms SSet.pathHomotopyPullbackMap
#print axioms SSet.pathHomotopyPullbackMap_left
#print axioms SSet.pathHomotopyPullbackMap_right
#print axioms SSet.pathHomotopyPullbackMap_path
#print axioms SSet.pathHomotopyPullbackMap_id
#print axioms SSet.pathHomotopyPullbackMap_comp
#print axioms SSet.pathHomotopyFiber
#print axioms SSet.pathHomotopyFiberToTotal
#print axioms SSet.pathHomotopyFiberPath
#print axioms SSet.pathHomotopyFiberPath_evalZero
#print axioms SSet.pathHomotopyFiberPath_evalOne
#print axioms SSet.pathHomotopyFiber_hom_ext
#print axioms SSet.pathHomotopyFiberMap
#print axioms SSet.pathHomotopyFiberMap_toTotal
#print axioms SSet.pathHomotopyFiberMap_path
#print axioms SSet.pathHomotopyFiberMap_id
#print axioms SSet.pathHomotopyFiberMap_comp
#print axioms SSet.strictFiberToPathHomotopyFiber
#print axioms SSet.strictFiberToPathHomotopyFiber_toTotal
#print axioms SSet.strictFiberToPathHomotopyFiber_path

end PathHomotopyFiberTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
