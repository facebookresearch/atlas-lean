/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackChowGroups
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Actual algebraic-space cycles and the Kresch comparison

An algebraic space is the original etale quotient sheaf over the base.
Its point diagram is the discrete category of its actual relative sections.
The coherent dictionary identifies an existing stack with that whole point
diagram, including every reindexing map and stabilizer. The ordinary Chow
group is the independently defined principal-divisor quotient on those cuts.

The map to Kresch's bundle/projective presentation is computed through the
zero-bundle stage and identity projective stage. Its bijectivity is a theorem
request. No comparison map or inverse is selected independently of cycle classes.

Source: Kresch, math/9810166v1, Definition 2.1.4 and Theorem 2.1.12(i).
The discrete-category functor uses the native Mathlib typeToCat construction
at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, with small discrete
Hom universes; original source is Apache 2.0, Mathlib contributors.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.AlgebraicSpaceChowComparison

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackCycleRelations StackChowGroups

/-- Actual space sections with equality morphisms in the small Hom universe. -/
structure SpacePoint (A : Type 1) where
  as : A

instance (A : Type 1) : Category.{0} (SpacePoint A) where
  Hom x y := PLift.{0} (x.as = y.as)
  id _x := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

instance (A : Type 1) (x y : SpacePoint A) : Subsingleton (x ⟶ y) :=
  inferInstanceAs (Subsingleton (PLift.{0} (x.as = y.as)))

def mapSpacePoints {A B : Type 1} (f : A → B) : SpacePoint A ⥤ SpacePoint B where
  obj x := ⟨f x.as⟩
  map h := ⟨congrArg f h.down⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Discrete point categories keep the small Hom universe of the stack model. -/
def discreteCategories : Type 1 ⥤ Cat.{0, 1} where
  obj A := Cat.of (SpacePoint A)
  map f := (mapSpacePoints f).toCatHom
  map_id A := by
    ext
    fapply CategoryTheory.Functor.ext
    · intro x; rfl
    · intro x y f
      apply PLift.ext
      exact Subsingleton.elim _ _
  map_comp f g := by
    ext
    fapply CategoryTheory.Functor.ext
    · intro x; rfl
    · intro x y h
      apply PLift.ext
      exact Subsingleton.elim _ _

variable {S : Scheme.{0}} (A : AlgebraicSpaceOver S)

def pointDiagram : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{0, 1} :=
  (A.relativePresheaf ⋙ discreteCategories).toPseudofunctor'

/-- Full coherent realization of the original quotient-space point diagram. -/
structure SpaceDictionary (X : Stack S) where
  comparison : Pseudofunctor.StrongTrans X.toPseudofunctor (pointDiagram A)
  equivalence : ∀ T : Over S, (comparison.app (.mk (op T))).toFunctor.IsEquivalence

variable {A} {X : Stack S} (M : SpaceDictionary A X)

def pointEquivalence (T : Over S) : X.Fibre T ≌ SpacePoint (A.relativePresheaf.obj (op T)) := by
  letI := M.equivalence T
  exact (M.comparison.app (.mk (op T))).toFunctor.asEquivalence

/-- Algebraic-space points have the actual discrete Hom sets. -/
theorem point_hom_subsingleton (M : SpaceDictionary A X)
    (T : Over S) (x y : X.Fibre T) : Subsingleton (x ⟶ y) := by
  let e := pointEquivalence M T
  exact ⟨fun f g ↦ e.functor.map_injective (Subsingleton.elim _ _)⟩

variable {scope : Stack S → Prop}
  (D : CycleConstructionData S scope) (K : KreschPresentation D)
  (hX : scope X) (C : CycleClassData D K X hX)

/-- Ordinary algebraic-space Chow, using its actual cuts and principal divisors. -/
abbrev OrdinaryChow (d : ℤ) := NaiveChowGroup D X hX d

/-- The comparison is the literal zero-bundle and identity-projective class map. -/
def cycleComparison (d : ℤ) : OrdinaryChow D hX d →+ ChowGroup D K X hX d :=
  (projectiveClass D K X hX d ⟨X, hX, _, C.identity⟩).comp (naiveToBundle D K C d)

theorem cycleComparison_generator (d : ℤ) (z : CycleGroup X d) :
    cycleComparison D K hX C d (naiveCycleClass D X hX d z) =
      stackCycleClass D K C d z := rfl

end AlgebraicGeometry.AlgebraicSpaceChowComparison
