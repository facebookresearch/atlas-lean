/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.UnitCopower
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorInterfaces
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorColimits
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.Types
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Basic.Finite.Sigma
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorPreserving
public import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.ColorBlind
public import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.AssocULift
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.FiniteTensorPreserving
public import MathlibExt.CategoryTheory.Operad.Tensor.FreeAlgebraConstruction
public import MathlibExt.CategoryTheory.Operad.Colored.Algebra.Analytic.Indexing
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Fintype.Order
public import Mathlib.SetTheory.Cardinal.NatCard
public import MathlibExt.CategoryTheory.Operad.FiniteSet.Assoc
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.OfSymmetric
public import MathlibExt.CategoryTheory.Monoidal.TensorWord
public import MathlibExt.CategoryTheory.Monoidal.TensorWordAdjunction
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Order.Sigma
public import Mathlib.Order.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# AssociativeTensorWords

The original associative operad and its full algebra and monad comparisons with tensor words.
-/

/- Source proof segment: DiscretePiEquivalence -/
section source_DiscretePiEquivalence
/-!
# Discrete categories on dependent products
-/

@[expose] public section

set_option autoImplicit false

universe ui u v

namespace CategoryTheory

/-- A dependent product of discrete categories is discrete. -/
instance piIsDiscrete {I : Type ui} {C : I → Type u}
    [∀ i, Category.{v} (C i)] [∀ i, IsDiscrete (C i)] : IsDiscrete (∀ i, C i) where
  subsingleton _ _ := ⟨fun f g => funext (fun i => Subsingleton.elim (f i) (g i))⟩
  eq_of_hom f := funext (fun i => IsDiscrete.eq_of_hom (f i))

namespace Discrete

/-- The actual discrete category on a dependent product is
equivalent to the original product of discrete categories. -/
def piEquivalence {I : Type ui} (X : I → Type u) :
    Discrete (∀ i, X i) ≌ (∀ i, Discrete (X i)) where
  functor := Discrete.functor (fun x i => Discrete.mk (x i))
  inverse :=
    { obj p := Discrete.mk (fun i => (p i).as)
      map f := eqToHom (by
        congr 1
        funext i
        exact Discrete.eq_of_hom (f i)) }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)



end Discrete
end CategoryTheory
end
end source_DiscretePiEquivalence

/- Source proof segment: UnitCopowerComparison -/
section source_UnitCopowerComparison
/-!
# The actual finite tensor comparison of unit copowers

The tensor coproduct cocone is proved colimiting from preservation
in each original tensor slot. Its target coproduct is independently
colimiting, via the actual finite multiplication of empty tensors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits FiniteFamily Limits.FiniteMultifunctor

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The original discrete diagram of unit copies at one input. -/
def factorDiagram (X : FiniteFamily (Type us)) (i : X.index) : Discrete (X.obj i) ⥤ C :=
  Discrete.functor (fun _ => unitObject C)

/-- The actual coproduct cocone at one original input. -/
def factorCocone (X : FiniteFamily (Type us)) (i : X.index) : Cocone (factorDiagram C X i) :=
  Cofan.mk ((functor C).obj (X.obj i)) (fun x => Sigma.ι (fun _ : X.obj i => unitObject C) x)

/-- Every source factor cocone is the actual unit coproduct colimit. -/
def factorIsColimit (X : FiniteFamily (Type us)) (i : X.index) :
    IsColimit (factorCocone C X i) :=
  coproductIsCoproduct (fun _ : X.obj i => unitObject C)

/-- The source tensor diagram uses all original input copy choices. -/
def tensorDiagram (X : FiniteFamily (Type us)) : (∀ i : X.index, Discrete (X.obj i)) ⥤ C :=
  finiteIndexDiagram (fixedIndexTensorFunctor X.index) (factorDiagram C X)

/-- The actual finite tensor of original factor coproduct cocones. -/
def tensorCocone (X : FiniteFamily (Type us)) : Cocone (tensorDiagram C X) :=
  finiteIndexCocone (fixedIndexTensorFunctor X.index) (factorCocone C X)

/-- The finite tensor coproduct cocone is actually colimiting,
derived solely from preservation in the original individual slots. -/
def tensorIsColimit (X : FiniteFamily (Type us)) : IsColimit (tensorCocone C X) := by
  classical
  let : @Functor.PreservesColimitsInEachSlot.{0, u, v, u, v, us}
      X.index C _ C _ (Classical.decEq X.index) (fixedIndexTensorFunctor X.index) :=
    FiniteTensorPreservesColimitsInEachSlot.preserves X.index
  exact isColimitFiniteIndexCocone (fixedIndexTensorFunctor X.index) (factorIsColimit C X)

/-- The unit coproduct indexed by the complete original tuple of choices. -/
def choiceCocone (X : FiniteFamily (Type us)) :
    Cocone (Discrete.functor (fun _ : (∀ i : X.index, X.obj i) => unitObject C)) :=
  Cofan.mk ((functor C).obj (∀ i : X.index, X.obj i))
    (fun x => Sigma.ι (fun _ : (∀ i : X.index, X.obj i) => unitObject C) x)

/-- The complete-choice target cocone is the ordinary unit coproduct colimit. -/
def choiceIsColimit (X : FiniteFamily (Type us)) : IsColimit (choiceCocone C X) :=
  coproductIsCoproduct (fun _ : (∀ i : X.index, X.obj i) => unitObject C)

/-- The original tensor at each choice is the tensor of empty
tensors; its source flatten comparison gives the actual unit coefficient. -/
def tensorChoiceDiagramIso (X : FiniteFamily (Type us)) :
    tensorDiagram C X ≅ (Discrete.piEquivalence X.obj).inverse ⋙
      Discrete.functor (fun _ : (∀ i : X.index, X.obj i) => unitObject C) :=
  NatIso.ofComponents (fun _ => emptyScalarTensorIso X.index) (by
    intro p q f
    have hpq : p = q := IsDiscrete.eq_of_hom f
    subst q
    have hf : f = 𝟙 p := Subsingleton.elim _ _
    subst f
    simp only [Functor.map_id, Category.id_comp, Category.comp_id])

/-- The actual comparison target cocone retains every original
unit-multiplication map and every complete-choice coproduct injection. -/
def comparisonTargetCocone (X : FiniteFamily (Type us)) : Cocone (tensorDiagram C X) :=
  (Cocone.precompose (tensorChoiceDiagramIso C X).hom).obj
    ((choiceCocone C X).whisker (Discrete.piEquivalence X.obj).inverse)

/-- The target cocone is actually colimiting, by source diagram
isomorphism and the proved equivalence of the original discrete tuple categories. -/
def comparisonTargetIsColimit (X : FiniteFamily (Type us)) :
    IsColimit (comparisonTargetCocone C X) :=
  (IsColimit.precomposeHomEquiv (tensorChoiceDiagramIso C X) _).symm
    ((Functor.Final.isColimitWhiskerEquiv (Discrete.piEquivalence X.obj).inverse _).symm
      (choiceIsColimit C X))

/-- The actual finite tensor comparison, between two constructed
colimits, for every original finite family including the empty one. -/
def comparisonIsoApp (X : FiniteFamily (Type us)) :
    (FiniteTensor.tensor (V := C)).obj ((FiniteFamily.map (functor C)).obj X) ≅
      (functor C).obj ((FiniteTensor.tensor (V := Type us)).obj X) :=
  (tensorIsColimit C X).coconePointUniqueUpToIso (comparisonTargetIsColimit C X)

/-- The actual injection of a full original tuple into its finite
tensor of unit copowers. -/
def tensorι (X : FiniteFamily (Type us)) (x : ∀ i : X.index, X.obj i) :
    (FiniteTensor.tensor (V := C)).obj (emptyScalarFamily X.index) ⟶
      (FiniteTensor.tensor (V := C)).obj ((FiniteFamily.map (functor C)).obj X) :=
  (fixedIndexTensorFunctor X.index).map
    (fun i => Sigma.ι (fun _ : X.obj i => unitObject C) (x i))

/-- Every actual original tensor coproduct injection is sent to
the same full-choice coefficient injection after the original empty
tensor multiplication. -/
@[reassoc]
theorem tensorι_comparison (X : FiniteFamily (Type us)) (x : ∀ i : X.index, X.obj i) :
    tensorι C X x ≫ (comparisonIsoApp C X).hom =
      (emptyScalarTensorIso X.index).hom ≫
        Sigma.ι (fun _ : (∀ i : X.index, X.obj i) => unitObject C) x :=
  (tensorIsColimit C X).fac (comparisonTargetCocone C X) (fun i => Discrete.mk (x i))





end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerComparison

/- Source proof segment: UnitCopowerComparisonNaturality -/
section source_UnitCopowerComparisonNaturality
/-!
# Full finite-profile naturality of the actual unit-copower comparison
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits FiniteFamily

private theorem comparisonNaturalityFromInjections {V : Type*} [Category* V]
    {U V' A B E FA FB : V} (i : U ⟶ A) (j : V' ⟶ B) (r : U ⟶ V') (a : A ⟶ B)
    (ca : A ⟶ FA) (cb : B ⟶ FB) (ua : U ⟶ E) (ub : V' ⟶ E)
    (ia : E ⟶ FA) (ib : E ⟶ FB) (b : FA ⟶ FB)
    (hn : i ≫ a = r ≫ j) (ha : i ≫ ca = ua ≫ ia)
    (hb : j ≫ cb = ub ≫ ib) (hu : r ≫ ub = ua) (hi : ia ≫ b = ib) :
    i ≫ (a ≫ cb) = i ≫ (ca ≫ b) := by
  rw [← Category.assoc i a, hn, Category.assoc r j, hb,
    ← Category.assoc r ub, hu, ← Category.assoc i ca, ha, Category.assoc ua ia, hi]

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]

/-- The original source factor maps of a simultaneous unit
coproduct injection, with the original finite index unchanged. -/
def tensorιFactors (X : FiniteFamily (Type us)) (x : ∀ i : X.index, X.obj i) :
    emptyScalarFamily (C := C) X.index ⟶ (FiniteFamily.map (functor C)).obj X where
  equiv := Equiv.refl X.index
  hom i := Sigma.ι (fun _ : X.obj i => unitObject C) (x i)

/-- The constructed tensor injection is the actual tensor of
these original source factor maps. -/
theorem tensorι_eq_map (X : FiniteFamily (Type us)) (x : ∀ i : X.index, X.obj i) :
    tensorι C X x = (FiniteTensor.tensor (V := C)).map (tensorιFactors C X x) := rfl

/-- Every original input map and input permutation commutes with
the simultaneous injection at the actual finite-family source. -/
theorem tensorιFactors_naturality {X Y : FiniteFamily (Type us)} (f : X ⟶ Y)
    (x : ∀ i : X.index, X.obj i) :
    tensorιFactors C X x ≫ (FiniteFamily.map (functor C)).map f =
      emptyScalarFamilyRelabel f.equiv ≫ tensorιFactors C Y (typeTensorMap f x) := by
  apply FiniteFamily.Hom_ext
  · ext i
    rfl
  · intro i
    change HEq
      (Sigma.ι (fun _ : X.obj i => unitObject C) (x i) ≫ (functor C).map (f.hom i))
      (𝟙 (unitObject C) ≫
        Sigma.ι (fun _ : Y.obj (f.equiv i) => unitObject C) (typeTensorMap f x (f.equiv i)))
    exact heq_of_eq ((ι_map C (f.hom i) (x i)).trans
      ((congrArg (fun z => Sigma.ι (fun _ : Y.obj (f.equiv i) => unitObject C) z)
        (typeTensorMap_apply f x i).symm).trans (Category.id_comp _).symm))

/-- The original tensor injections are natural under all actual
finite input permutations and coefficient source maps. -/
@[reassoc]
theorem tensorι_naturality {X Y : FiniteFamily (Type us)} (f : X ⟶ Y)
    (x : ∀ i : X.index, X.obj i) :
    tensorι C X x ≫ (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map (functor C)).map f) =
      (FiniteTensor.tensor (V := C)).map (emptyScalarFamilyRelabel f.equiv) ≫
        tensorι C Y (typeTensorMap f x) :=
  ((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
    ((congrArg (FiniteTensor.tensor (V := C)).map (tensorιFactors_naturality C f x)).trans
      ((FiniteTensor.tensor (V := C)).map_comp _ _))

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual component comparison is natural under all source
finite-family maps, including arbitrary original permutations. -/
theorem comparisonIsoApp_naturality {X Y : FiniteFamily (Type us)} (f : X ⟶ Y) :
    (FiniteTensor.tensor (V := C)).map ((FiniteFamily.map (functor C)).map f) ≫
        (comparisonIsoApp C Y).hom =
      (comparisonIsoApp C X).hom ≫
        (functor C).map ((FiniteTensor.tensor (V := Type us)).map f) := by
  refine (tensorIsColimit C X).hom_ext fun p => ?_
  let x : ∀ i : X.index, X.obj i := fun i => (p i).as
  exact comparisonNaturalityFromInjections
    (tensorι C X x) (tensorι C Y (typeTensorMap f x))
    ((FiniteTensor.tensor (V := C)).map (emptyScalarFamilyRelabel f.equiv))
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.map (functor C)).map f))
    (comparisonIsoApp C X).hom (comparisonIsoApp C Y).hom
    (emptyScalarTensorIso X.index).hom (emptyScalarTensorIso Y.index).hom
    (Sigma.ι (fun _ : (∀ i : X.index, X.obj i) => unitObject C) x)
    (Sigma.ι (fun _ : (∀ i : Y.index, Y.obj i) => unitObject C) (typeTensorMap f x))
    ((functor C).map ((FiniteTensor.tensor (V := Type us)).map f))
    (tensorι_naturality C f x) (tensorι_comparison C X x)
    (tensorι_comparison C Y (typeTensorMap f x)) (emptyScalarTensorIso_relabel f.equiv)
    (ι_map C ((FiniteTensor.tensor (V := Type us)).map f) x)

/-- The actual finite tensor comparison is a natural isomorphism
between tensoring the original unit copowers and the unit copower
of the original source finite tensor. -/
def comparisonIso : FiniteFamily.map (functor C) ⋙ FiniteTensor.tensor (V := C) ≅
    FiniteTensor.tensor (V := Type us) ⋙ functor C :=
  NatIso.ofComponents (comparisonIsoApp C) (by
    intro X Y f
    exact comparisonIsoApp_naturality C f)



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerComparisonNaturality

/- Source proof segment: UnitScalarSingleton -/
section source_UnitScalarSingleton
/-!
# The actual empty-tensor multiplication at one input
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory FiniteFamily

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
/-- The actual collapse of one empty block is the original
singleton-flatten map, including its empty input bijection. -/
theorem emptyScalarFlattenIso_singleton :
    (emptyScalarFlattenIso (C := C) (FintypeCat.of PUnit)).hom =
      FiniteFamily.singletonFlattenIso.hom.app (FiniteFamily.empty : FiniteFamily C) := by
  apply FiniteFamily.Hom_ext
  · ext p
    exact nomatch p.2
  · intro p
    exact nomatch p.2

/-- Finite multiplication of the actual empty tensor at one
input is exactly the original tensor singleton comparison. -/
theorem emptyScalarTensorIso_singleton :
    (emptyScalarTensorIso (C := C) (FintypeCat.of PUnit)).hom =
      (FiniteTensor.singletonIso (V := C)).hom.app (unitObject C) := by
  let T := FiniteTensor.tensor (V := C)
  let e := (FiniteTensor.flattenIso (V := C)).app (emptyScalarBlocks (C := C) (FintypeCat.of PUnit))
  have h : T.map (emptyScalarFlattenIso (C := C) (FintypeCat.of PUnit)).hom =
      e.hom ≫ (FiniteTensor.singletonIso (V := C)).hom.app (unitObject C) :=
    (congrArg T.map emptyScalarFlattenIso_singleton).trans
      (CategoryTheory.singletonFlattenLaw_app (FiniteFamily.empty : FiniteFamily C))
  exact (congrArg (fun k => e.inv ≫ k) h).trans (e.inv_hom_id_assoc _)



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitScalarSingleton

/- Source proof segment: UnitCopowerSingletonCoherence -/
section source_UnitCopowerSingletonCoherence
/-!
# The actual unit-copower comparison preserves tensor singletons
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits FiniteFamily

private theorem singletonComparisonFromSquares {V : Type*} [Category* V]
    {U A E B D : V} (i : U ⟶ A) (c : A ⟶ B) (b : B ⟶ D) (s : A ⟶ D)
    (m : U ⟶ E) (u : U ⟶ E) (j : E ⟶ B) (k : E ⟶ D)
    (hb : i ≫ c = m ≫ j) (hj : j ≫ b = k) (hm : m = u) (hs : i ≫ s = u ≫ k) :
    i ≫ (c ≫ b) = i ≫ s := by
  rw [← Category.assoc i c, hb, Category.assoc m j, hj, hm, hs]

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]

/-- The original one-slot coefficient injection is precisely the
singleton-family map of the original coproduct injection. -/
theorem tensorιFactors_singleton (X : Type us) (x : PUnit → X) :
    tensorιFactors C ((FiniteFamily.singleton (C := Type us)).obj X) x =
      (FiniteFamily.singleton (C := C)).map
        (Sigma.ι (fun _ : X => unitObject C) (x PUnit.unit)) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i
    rfl

/-- The original singleton tensor comparison evaluates every
actual singleton coproduct injection as the original coefficient injection. -/
theorem tensorι_singleton (X : Type us) (x : PUnit → X) :
    tensorι C ((FiniteFamily.singleton (C := Type us)).obj X) x ≫
        (FiniteTensor.singletonIso (V := C)).hom.app ((functor C).obj X) =
      (FiniteTensor.singletonIso (V := C)).hom.app (unitObject C) ≫
        Sigma.ι (fun _ : X => unitObject C) (x PUnit.unit) :=
  (congrArg (fun k => (FiniteTensor.tensor (V := C)).map k ≫
      (FiniteTensor.singletonIso (V := C)).hom.app ((functor C).obj X))
      (tensorιFactors_singleton C X x)).trans
    ((FiniteTensor.singletonIso (V := C)).hom.naturality
      (Sigma.ι (fun _ : X => unitObject C) (x PUnit.unit)))

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual finite tensor comparison satisfies its complete
singleton equation; equality follows after all original tensor
coproduct injections from the proved source singleton law. -/
theorem comparisonIso_singleton (X : Type us) :
    (comparisonIso C).hom.app ((FiniteFamily.singleton (C := Type us)).obj X) ≫
        (functor C).map ((FiniteTensor.singletonIso (V := Type us)).hom.app X) =
      (FiniteTensor.singletonIso (V := C)).hom.app ((functor C).obj X) := by
  refine (tensorIsColimit C ((FiniteFamily.singleton (C := Type us)).obj X)).hom_ext fun p => ?_
  let x : PUnit → X := fun i => (p i).as
  have hj : Sigma.ι (fun _ : (PUnit → X) => unitObject C) x ≫
      (functor C).map ((FiniteTensor.singletonIso (V := Type us)).hom.app X) =
    Sigma.ι (fun _ : X => unitObject C) (x PUnit.unit) :=
    ι_map C ((FiniteTensor.singletonIso (V := Type us)).hom.app X) x
  exact singletonComparisonFromSquares
    (tensorι C ((FiniteFamily.singleton (C := Type us)).obj X) x)
    ((comparisonIso C).hom.app ((FiniteFamily.singleton (C := Type us)).obj X))
    ((functor C).map ((FiniteTensor.singletonIso (V := Type us)).hom.app X))
    ((FiniteTensor.singletonIso (V := C)).hom.app ((functor C).obj X))
    (emptyScalarTensorIso (FintypeCat.of PUnit)).hom
    ((FiniteTensor.singletonIso (V := C)).hom.app (unitObject C))
    (Sigma.ι (fun _ : (PUnit → X) => unitObject C) x)
    (Sigma.ι (fun _ : X => unitObject C) (x PUnit.unit))
    (tensorι_comparison C ((FiniteFamily.singleton (C := Type us)).obj X) x) hj
    emptyScalarTensorIso_singleton (tensorι_singleton C X x)



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerSingletonCoherence

/- Source proof segment: UnitScalarFlattenSource -/
section source_UnitScalarFlattenSource
/-!
# Original empty-tensor source maps for finite flattening
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory FiniteFamily

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original dependent sum of finite input blocks. -/
def scalarTotalIndex (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) : FintypeCat.{0} := by
  letI : Finite I := I.property
  letI : ∀ i, Finite (J i) := fun i => (J i).property
  exact FintypeCat.of (Σ i : I, J i)

/-- Original finite outer and inner indices with empty leaf families. -/
def scalarTriple (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    FiniteFamily (FiniteFamily (FiniteFamily C)) :=
  ⟨I, fun i => emptyScalarBlocks (J i)⟩

/-- The original two levels of actual empty tensor factors. -/
def scalarNestedFamily (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    FiniteFamily (FiniteFamily C) :=
  (FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj (scalarTriple I J)

/-- Collapse each original empty leaf block, keeping all outer indices. -/
def scalarEmptyCollapse (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (scalarTriple I J) ⟶
      emptyScalarBlocks I where
  equiv := Equiv.refl I
  hom i := (emptyScalarFlattenIso (J i)).hom

/-- Multiply the actual inner unit tensors in every original block. -/
def scalarInnerCollapse (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (scalarNestedFamily I J) ⟶
      emptyScalarFamily I where
  equiv := Equiv.refl I
  hom i := (emptyScalarTensorIso (J i)).hom

/-- The defining finite unit multiplication cancels its original
flatten comparison, with no terminal-unit hypothesis. -/
@[reassoc]
theorem emptyScalarTensorIso_flatten (I : FintypeCat.{0}) :
    (FiniteTensor.flattenIso (V := C)).hom.app (emptyScalarBlocks I) ≫
        (emptyScalarTensorIso (C := C) I).hom =
      (FiniteTensor.tensor (V := C)).map (emptyScalarFlattenIso I).hom :=
  ((FiniteTensor.flattenIso (V := C)).app (emptyScalarBlocks I)).hom_inv_id_assoc _

/-- The original branch flattening followed by its unit multiplication
is exactly the tensor of the original empty-block collapse map. -/
theorem scalarInnerCollapse_source (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app (scalarTriple I J) ≫
        scalarInnerCollapse I J =
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (scalarEmptyCollapse I J) := by
  apply FiniteFamily.Hom_ext
  · ext i
    rfl
  · intro i
    exact heq_of_eq (emptyScalarTensorIso_flatten (C := C) (J i))

omit [FiniteTensor C] in
/-- Both original three-level empty-source bijections collapse
to the same empty profile. The full dependent sum association is retained. -/
theorem scalarEmptyCollapse_flatten (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    (FiniteFamily.flatten (C := C)).map (scalarEmptyCollapse I J) ≫
        (emptyScalarFlattenIso I).hom =
      FiniteFamily.flattenAssocIso.hom.app (scalarTriple I J) ≫
        (emptyScalarFlattenIso (scalarTotalIndex I J)).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    exact nomatch p.2.2
  · intro p
    exact nomatch p.2.2




end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitScalarFlattenSource

/- Source proof segment: UnitScalarFlattenCoherence -/
section source_UnitScalarFlattenCoherence
/-!
# Finite substitution coherence of the actual empty tensor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory FiniteFamily

private theorem scalarFlattenFromSquares {V : Type*} [Category* V]
    {A B X Y Z U Q E : V} (a : A ≅ B) (b : B ≅ X)
    (c : X ⟶ Y) (r : Y ⟶ Z) (m : Z ⟶ E)
    (d : A ⟶ U) (e : U ⟶ Y) (g : U ⟶ Z)
    (f : A ⟶ Q) (u : Q ⟶ Z) (z : Q ⟶ E) (n : B ⟶ E)
    (h1 : d ≫ e = a.hom ≫ (b.hom ≫ c)) (h2 : e ≫ r = g)
    (h3 : d ≫ g = f ≫ u) (h4 : u ≫ m = z) (h5 : f ≫ z = a.hom ≫ n) :
    c ≫ (r ≫ m) = b.inv ≫ n := by
  have hbig : a.hom ≫ (b.hom ≫ (c ≫ (r ≫ m))) = a.hom ≫ n := by
    calc
      a.hom ≫ (b.hom ≫ (c ≫ (r ≫ m))) =
          (a.hom ≫ (b.hom ≫ c)) ≫ (r ≫ m) := by simp only [Category.assoc]
      _ = (d ≫ e) ≫ (r ≫ m) := congrArg (fun k => k ≫ (r ≫ m)) h1.symm
      _ = d ≫ ((e ≫ r) ≫ m) := by simp only [Category.assoc]
      _ = d ≫ (g ≫ m) := congrArg (fun k => d ≫ (k ≫ m)) h2
      _ = (f ≫ u) ≫ m := (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ m) h3)
      _ = f ≫ z := (Category.assoc _ _ _).trans (congrArg (fun k => f ≫ k) h4)
      _ = a.hom ≫ n := h5
  have hb : b.hom ≫ (c ≫ (r ≫ m)) = n := (cancel_epi a.hom).1 hbig
  exact (b.inv_hom_id_assoc _).symm.trans (congrArg (fun k => b.inv ≫ k) hb)

private theorem discardMiddleIdentity {V : Type*} [Category* V]
    {A B X Y : V} (a : A ⟶ B) (b : B ⟶ X) (k : X ⟶ X) (c : X ⟶ Y)
    (h : k = 𝟙 X) : a ≫ (b ≫ (k ≫ c)) = a ≫ (b ≫ c) := by
  rw [h, Category.id_comp]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Multiplying all original inner unit tensors and then the
outer unit tensor equals multiplication on the original flattened
finite input type. This is proved from the actual tensor pentagon
and original empty-source maps, including all empty blocks. -/
theorem emptyScalarTensorIso_flatten_coherence (I : FintypeCat.{0}) (J : I → FintypeCat.{0}) :
    (FiniteTensor.flattenIso (V := C)).hom.app (scalarNestedFamily I J) ≫
        (FiniteTensor.tensor (V := C)).map (scalarInnerCollapse I J) ≫
        (emptyScalarTensorIso I).hom =
      (emptyScalarTensorIso (C := C) (scalarTotalIndex I J)).hom := by
  let T := FiniteTensor.tensor (V := C)
  let N := scalarTriple (C := C) I J
  let M := (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj N
  let Z := (FiniteFamily.flatten (C := FiniteFamily C)).obj N
  let U := scalarNestedFamily (C := C) I J
  let a := T.mapIso (FiniteFamily.flattenAssocIso.app N)
  let b := (FiniteTensor.flattenIso (V := C)).app Z
  let c := (FiniteTensor.flattenIso (V := C)).hom.app U
  let r := T.map (scalarInnerCollapse (C := C) I J)
  let m := (emptyScalarTensorIso (C := C) I).hom
  let d := (FiniteTensor.flattenIso (V := C)).hom.app M
  let e := T.map ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app N)
  let g := T.map ((FiniteFamily.map T).map (scalarEmptyCollapse (C := C) I J))
  let f := T.map ((FiniteFamily.flatten (C := C)).map (scalarEmptyCollapse (C := C) I J))
  let u := (FiniteTensor.flattenIso (V := C)).hom.app (emptyScalarBlocks (C := C) I)
  let z := T.map (emptyScalarFlattenIso (C := C) I).hom
  let n := T.map (emptyScalarFlattenIso (C := C) (scalarTotalIndex I J)).hom
  have h1 : d ≫ e = a.hom ≫ (b.hom ≫ c) := by
    let k := T.map ((FiniteFamily.flattenMapIso T).hom.app N)
    have hp : d ≫ e = a.hom ≫ (b.hom ≫ (k ≫ c)) :=
      FiniteTensor.flattenAssocLaw_app_unfold N
    have hk : k = 𝟙 _ :=
      (congrArg T.map (FiniteTensor.flattenMapIso_hom_app_eq_id T N)).trans (T.map_id _)
    exact hp.trans (discardMiddleIdentity a.hom b.hom k c hk)
  have h2 : e ≫ r = g :=
    (T.map_comp _ _).symm.trans (congrArg T.map (scalarInnerCollapse_source (C := C) I J))
  have h3 : d ≫ g = f ≫ u :=
    ((FiniteTensor.flattenIso (V := C)).hom.naturality (scalarEmptyCollapse (C := C) I J)).symm
  have h4 : u ≫ m = z := emptyScalarTensorIso_flatten (C := C) I
  have h5 : f ≫ z = a.hom ≫ n :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (scalarEmptyCollapse_flatten (C := C) I J)).trans (T.map_comp _ _))
  exact scalarFlattenFromSquares a b c r m d e g f u z n h1 h2 h3 h4 h5



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitScalarFlattenCoherence

/- Source proof segment: UnitCopowerFlattenInjections -/
section source_UnitCopowerFlattenInjections
/-!
# Original nested coproduct injection squares for tensor flattening
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits FiniteFamily

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]

/-- The original coefficient-copy factors at two levels, with all
original outer and inner indices retained. -/
def nestedιFactors (X : FiniteFamily (FiniteFamily (Type us)))
    (x : ∀ p : (FiniteFamily.flatten (C := Type us)).obj X |>.index,
      ((FiniteFamily.flatten (C := Type us)).obj X).obj p) :
    scalarNestedFamily (C := C) X.index (fun i => (X.obj i).index) ⟶
      (FiniteFamily.map (FiniteFamily.map (functor C))).obj X where
  equiv := Equiv.refl X.index
  hom i := tensorιFactors C (X.obj i) (fun j => x ⟨i, j⟩)

/-- Flattening the actual two-level injection factors gives the
original injection factors on the actual dependent-sum index. -/
theorem nestedιFactors_flatten (X : FiniteFamily (FiniteFamily (Type us)))
    (x : ∀ p : ((FiniteFamily.flatten (C := Type us)).obj X).index,
      ((FiniteFamily.flatten (C := Type us)).obj X).obj p) :
    (FiniteFamily.flatten (C := C)).map (nestedιFactors C X x) =
      tensorιFactors C ((FiniteFamily.flatten (C := Type us)).obj X) x := by
  apply FiniteFamily.Hom_ext
  · ext p
    rfl
  · intro p
    cases p
    rfl

/-- Tensor the original inner injection maps without changing
any original outer input. -/
def nestedTensorιFactors (X : FiniteFamily (FiniteFamily (Type us)))
    (x : ∀ p : ((FiniteFamily.flatten (C := Type us)).obj X).index,
      ((FiniteFamily.flatten (C := Type us)).obj X).obj p) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        (scalarNestedFamily (C := C) X.index (fun i => (X.obj i).index)) ⟶
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
        ((FiniteFamily.map (FiniteFamily.map (functor C))).obj X) :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (nestedιFactors C X x)

/-- The actual original finite tensor flattening comparison
commutes with every original two-level coproduct injection. -/
@[reassoc]
theorem tensorι_flatten (X : FiniteFamily (FiniteFamily (Type us)))
    (x : ∀ p : ((FiniteFamily.flatten (C := Type us)).obj X).index,
      ((FiniteFamily.flatten (C := Type us)).obj X).obj p) :
    tensorι C ((FiniteFamily.flatten (C := Type us)).obj X) x ≫
        (FiniteTensor.flattenIso (V := C)).hom.app
          ((FiniteFamily.map (FiniteFamily.map (functor C))).obj X) =
      (FiniteTensor.flattenIso (V := C)).hom.app
          (scalarNestedFamily (C := C) X.index (fun i => (X.obj i).index)) ≫
        (FiniteTensor.tensor (V := C)).map (nestedTensorιFactors C X x) :=
  (congrArg (fun k => (FiniteTensor.tensor (V := C)).map k ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        ((FiniteFamily.map (FiniteFamily.map (functor C))).obj X))
      (nestedιFactors_flatten C X x).symm).trans
    ((FiniteTensor.flattenIso (V := C)).hom.naturality (nestedιFactors C X x))

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Every original inner coproduct injection followed by its
actual comparison is its actual inner scalar multiplication and
the same original inner complete-choice coefficient injection. -/
theorem nestedTensorιFactors_comparison (X : FiniteFamily (FiniteFamily (Type us)))
    (x : ∀ p : ((FiniteFamily.flatten (C := Type us)).obj X).index,
      ((FiniteFamily.flatten (C := Type us)).obj X).obj p) :
    nestedTensorιFactors C X x ≫ (FiniteFamily.mapIso (comparisonIso C)).hom.app X =
      scalarInnerCollapse (C := C) X.index (fun i => (X.obj i).index) ≫
        tensorιFactors C ((FiniteFamily.map (FiniteTensor.tensor (V := Type us))).obj X)
          (fun i j => x ⟨i, j⟩) := by
  apply FiniteFamily.Hom_ext
  · ext i
    rfl
  · intro i
    exact heq_of_eq (tensorι_comparison C (X.obj i) (fun j => x ⟨i, j⟩))

/-- The actual outer tensor of the original inner coefficient
injection squares is the tensor of the original inner scalar
multiplications followed by the original outer coefficient injection. -/
@[reassoc]
theorem nestedTensorι_comparison (X : FiniteFamily (FiniteFamily (Type us)))
    (x : ∀ p : ((FiniteFamily.flatten (C := Type us)).obj X).index,
      ((FiniteFamily.flatten (C := Type us)).obj X).obj p) :
    (FiniteTensor.tensor (V := C)).map (nestedTensorιFactors C X x) ≫
        (FiniteTensor.tensor (V := C)).map ((FiniteFamily.mapIso (comparisonIso C)).hom.app X) =
      (FiniteTensor.tensor (V := C)).map (scalarInnerCollapse (C := C) X.index (fun i => (X.obj i).index)) ≫
        tensorι C ((FiniteFamily.map (FiniteTensor.tensor (V := Type us))).obj X)
          (fun i j => x ⟨i, j⟩) :=
  ((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
    ((congrArg (FiniteTensor.tensor (V := C)).map (nestedTensorιFactors_comparison C X x)).trans
      ((FiniteTensor.tensor (V := C)).map_comp _ _))




end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerFlattenInjections

/- Source proof segment: UnitCopowerFlattenCoherence -/
section source_UnitCopowerFlattenCoherence
/-!
# The actual finite tensor flattening law of unit copowers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits FiniteFamily

private theorem flattenComparisonFromSquares {V : Type*} [Category* V]
    {U V' W A B D E FA F : V}
    (i : U ⟶ A) (c : A ⟶ B) (n : B ⟶ D) (o : D ⟶ F)
    (u : U ⟶ V') (s : V' ⟶ B) (r : V' ⟶ W) (j : W ⟶ D)
    (m : W ⟶ E) (mt : U ⟶ E) (ia : E ⟶ FA) (ib : E ⟶ F)
    (cf : A ⟶ FA) (b : FA ⟶ F)
    (hn : i ≫ c = u ≫ s) (hb : s ≫ n = r ≫ j) (ho : j ≫ o = m ≫ ib)
    (hu : u ≫ (r ≫ m) = mt) (hf : i ≫ cf = mt ≫ ia) (hm : ia ≫ b = ib) :
    i ≫ (c ≫ (n ≫ o)) = i ≫ (cf ≫ b) := by
  calc
    i ≫ (c ≫ (n ≫ o)) = (i ≫ c) ≫ (n ≫ o) := (Category.assoc _ _ _).symm
    _ = (u ≫ s) ≫ (n ≫ o) := congrArg (fun k => k ≫ (n ≫ o)) hn
    _ = u ≫ ((s ≫ n) ≫ o) := by simp only [Category.assoc]
    _ = u ≫ ((r ≫ j) ≫ o) := congrArg (fun k => u ≫ (k ≫ o)) hb
    _ = u ≫ (r ≫ (j ≫ o)) := by simp only [Category.assoc]
    _ = u ≫ (r ≫ (m ≫ ib)) := congrArg (fun k => u ≫ (r ≫ k)) ho
    _ = (u ≫ (r ≫ m)) ≫ ib := by simp only [Category.assoc]
    _ = mt ≫ ib := congrArg (fun k => k ≫ ib) hu
    _ = mt ≫ (ia ≫ b) := congrArg (fun k => mt ≫ k) hm.symm
    _ = (mt ≫ ia) ≫ b := (Category.assoc _ _ _).symm
    _ = (i ≫ cf) ≫ b := congrArg (fun k => k ≫ b) hf.symm
    _ = i ≫ (cf ≫ b) := Category.assoc _ _ _

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual finite tensor comparison satisfies its complete
flattening equation. The original tensor coproduct injections detect
it; their source flattening, coefficient maps, original tuple curry,
and proved scalar pentagon establish the equation. -/
theorem comparisonIso_flatten (X : FiniteFamily (FiniteFamily (Type us))) :
    (FiniteTensor.flattenIso (V := C)).hom.app
          ((FiniteFamily.map (FiniteFamily.map (functor C))).obj X) ≫
        (FiniteTensor.tensor (V := C)).map ((FiniteFamily.mapIso (comparisonIso C)).hom.app X) ≫
        (comparisonIso C).hom.app ((FiniteFamily.map (FiniteTensor.tensor (V := Type us))).obj X) =
      (comparisonIso C).hom.app ((FiniteFamily.flatten (C := Type us)).obj X) ≫
        (functor C).map ((FiniteTensor.flattenIso (V := Type us)).hom.app X) := by
  let L := (FiniteFamily.flatten (C := Type us)).obj X
  refine (tensorIsColimit C L).hom_ext fun p => ?_
  let x : ∀ q : L.index, L.obj q := fun q => (p q).as
  let Y := (FiniteFamily.map (FiniteTensor.tensor (V := Type us))).obj X
  let y : ∀ i : Y.index, Y.obj i := fun i j => x ⟨i, j⟩
  have hm : Sigma.ι (fun _ : (∀ q : L.index, L.obj q) => unitObject C) x ≫
      (functor C).map ((FiniteTensor.flattenIso (V := Type us)).hom.app X) =
    Sigma.ι (fun _ : (∀ i : Y.index, Y.obj i) => unitObject C) y :=
    ι_map C ((FiniteTensor.flattenIso (V := Type us)).hom.app X) x
  exact flattenComparisonFromSquares
    (tensorι C L x)
    ((FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.map (FiniteFamily.map (functor C))).obj X))
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.mapIso (comparisonIso C)).hom.app X))
    ((comparisonIso C).hom.app Y)
    ((FiniteTensor.flattenIso (V := C)).hom.app
      (scalarNestedFamily (C := C) X.index (fun i => (X.obj i).index)))
    ((FiniteTensor.tensor (V := C)).map (nestedTensorιFactors C X x))
    ((FiniteTensor.tensor (V := C)).map (scalarInnerCollapse (C := C) X.index (fun i => (X.obj i).index)))
    (tensorι C Y y) (emptyScalarTensorIso X.index).hom
    (emptyScalarTensorIso L.index).hom
    (Sigma.ι (fun _ : (∀ q : L.index, L.obj q) => unitObject C) x)
    (Sigma.ι (fun _ : (∀ i : Y.index, Y.obj i) => unitObject C) y)
    ((comparisonIso C).hom.app L)
    ((functor C).map ((FiniteTensor.flattenIso (V := Type us)).hom.app X))
    (tensorι_flatten C X x) (nestedTensorι_comparison C X x)
    (tensorι_comparison C Y y)
    (emptyScalarTensorIso_flatten_coherence X.index (fun i => (X.obj i).index))
    (tensorι_comparison C L x) hm



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerFlattenCoherence

/- Source proof segment: UnitCopowerPreserving -/
section source_UnitCopowerPreserving
/-!
# The actual unit-copower functor preserves coherent finite tensors
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual unit copower functor preserves the source coherent
finite tensors. Its comparison and both coherence equations have
been constructed from the source finite tensor colimit hypotheses. -/
def preserving : FiniteTensor.Preserving (functor C) :=
  FiniteTensor.Preserving.mkOfComponents (comparisonIso C)
    (comparisonIso_singleton C) (comparisonIso_flatten C)

/-- The preserving structure has the constructed actual finite
tensor coproduct comparison, with its original injection equations. -/
@[simp]
theorem preserving_comparison : (preserving C).comparisonIso = comparisonIso C := rfl



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerPreserving

/- Source proof segment: AssociativeTensorOperad -/
section source_AssociativeTensorOperad
/-!
# The actual one-color associative tensor operad

The coefficient at every original finite input type is the actual
coproduct of tensor-unit copies indexed by its lifted linear orders.
The mapped units, natural simultaneous lexicographic substitution,
and every operad law use the proved unit-copower preserving functor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits Operad

/-- The genuine source associative set operad, lifted to the
source coefficient universe and given the one original color. -/
def associativeSetOperad : ColoredOperadObj PUnit.{1} (Type us) :=
  ColoredOperadObj.ColorBlind.obj PUnit.{1} SetOperad.assocULift.{us}

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual associative tensor operad is constructed from the
genuine source associative operad and actual preserving unit copowers.
Its full units, symmetric actions, natural simultaneous substitution,
and all operad laws are transported by the canonical operad mapping API. -/
def associativeOperad : ColoredOperadObj PUnit.{1} C :=
  (ColoredOperadObj.mapFunctor (preserving C)).obj associativeSetOperad

/-- Its entire original coefficient functor is the genuine
one-color associative source functor followed by actual unit copowers. -/
@[simp]
theorem associativeOperad_toCollection :
    (associativeOperad C).toCollection =
      (ColoredOperadObj.ColorBlind.obj PUnit.{1} SetOperad.assocULift.{us}).toCollection ⋙ functor C := rfl

/-- Every finite original profile coefficient, including arity
zero and one, is the actual unit copower indexed by lifted linear orders. -/
theorem associativeOperad_coefficient (P : ColoredProfile PUnit.{1}) :
    (associativeOperad C).toCollection.obj P =
      ∐ (fun _ : ULift.{us} (LinearOrder P.inputs) => unitObject C) := rfl

/-- Every original input permutation acts by the source linear-order
transport, followed by the actual unit-copower coefficient map. -/
theorem associativeOperad_relabel {P Q : ColoredProfile PUnit.{1}} (f : P ⟶ Q) :
    (associativeOperad C).toCollection.map f =
      (functor C).map (SetOperad.assocULift.{us}.toCollection.map
        (FinBijGroupoid.homOfEquiv f.inputEquiv)) := rfl

/-- The actual unit map uses the original empty-tensor comparison
and the actual source unary associative unit. -/
theorem associativeOperad_unit (c : PUnit.{1}) :
    (associativeOperad C).unit c =
      (ColoredOperadObj.MapData.unitSourceIso (preserving C)).hom ≫
        (functor C).map (associativeSetOperad.unit c) := rfl

/-- Actual tensor substitution is the proved finite tensor
comparison followed by the original lifted lexicographic substitution. -/
theorem associativeOperad_substitution (d : ColoredSubstitutionData PUnit.{1}) :
    (associativeOperad C).subst.app d =
      ColoredOperadObj.MapData.sourceComparisonHom (preserving C) associativeSetOperad.toCollection d ≫
        (functor C).map (associativeSetOperad.subst.app d) := rfl



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_AssociativeTensorOperad

/- Source proof segment: AssociativeProfileTensorCoproduct -/
section source_AssociativeProfileTensorCoproduct
/-!
# The actual associative weighted profile tensors are tensor copowers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

private theorem profileCoefficientCopyBeta {V : Type*} [Category* V]
    {A B D E : V} (e : A ≅ B) (i : D ⟶ B) (a : B ⟶ E) (b : D ⟶ E)
    (h : i ≫ a = b) : (i ≫ e.inv) ≫ (e.hom ≫ a) = b := by
  rw [Category.assoc, e.inv_hom_id_assoc]
  exact h

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Retain the original associative coefficient and every original
input tensor factor in their actual coefficient/leaf grouping. -/
def associativeProfileFactorsIso (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    (analyticFactors (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X)).obj P ≅
      (coefficientLeafFamilyFunctor ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).obj
        ((FiniteTensor.UnitCopower.functor C).obj (ULift.{us} (LinearOrder P.inputs))) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs)) (fun i => match i with
    | none => by with_unfolding_all exact Iso.refl _
    | some _ => Iso.refl _)

/-- Every actual associative weighted tensor profile is the
coproduct of its original input tensor over its actual operation
orders, with the original tensor-unit coefficient retained. -/
def associativeProfileTensorIso (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X)).obj P ≅
      ∐ (fun _ : ULift.{us} (LinearOrder P.inputs) =>
        (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) :=
  (FiniteTensor.tensor (V := C)).mapIso (associativeProfileFactorsIso X P) ≪≫
    coefficientCopowerTensorIso (ULift.{us} (LinearOrder P.inputs))
      ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)

/-- Insert one original associative operation's actual tensor-unit
coefficient before every original input leaf, into the weighted profile. -/
def associativeProfileCoefficientInjection (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (L : ULift.{us} (LinearOrder P.inputs)) :
    (coefficientLeafTensorFunctor ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).obj
        (FiniteTensor.UnitCopower.unitObject C) ⟶
      (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X)).obj P :=
  (coefficientLeafTensorFunctor ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).map
      (Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) => FiniteTensor.UnitCopower.unitObject C) L) ≫
    ((FiniteTensor.tensor (V := C)).mapIso (associativeProfileFactorsIso X P)).inv

/-- The actual original operation coefficient injection becomes
precisely its original input tensor copy, including nullary profiles. -/
@[reassoc]
theorem associativeProfileCoefficientInjection_β (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (L : ULift.{us} (LinearOrder P.inputs)) :
    associativeProfileCoefficientInjection X P L ≫ (associativeProfileTensorIso X P).hom =
      (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫
        Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) =>
          (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) L := by
  exact profileCoefficientCopyBeta
    ((FiniteTensor.tensor (V := C)).mapIso (associativeProfileFactorsIso X P)) _ _ _
    (coefficientCopowerTensorIso_ι _ _ L)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeProfileTensorCoproduct

/- Source proof segment: AssociativeOrderedProfiles -/
section source_AssociativeOrderedProfiles
/-!
# Actual finite ordered profiles for the associative tensor specialization

The morphisms retain their original input bijections and preserve the
supplied linear orders. Empty profiles are included. Finite increasing
enumeration identifies this groupoid with the discrete word lengths.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory

/-- An original one-color finite input profile with its actual
associative-operation linear order. -/
structure OrderedProfile where
  /-- The original one-color finite input profile. -/
  profile : AnalyticIndex PUnit.{1} PUnit.unit
  /-- The actual associative-operation order on the original finite input type. -/
  order : LinearOrder profile.inputs

namespace OrderedProfile

/-- Original input bijections preserving the actual operation order. -/
abbrev Hom (P Q : OrderedProfile) :=
  @OrderIso P.profile.inputs Q.profile.inputs P.order.toLE Q.order.toLE

theorem Hom.ext {P Q : OrderedProfile} {f g : Hom P Q}
    (h : ∀ i, f i = g i) : f = g := by
  let : LE P.profile.inputs := P.order.toLE
  let : LE Q.profile.inputs := Q.order.toLE
  exact OrderIso.ext (funext h)

/-- Finite ordered profiles form the actual groupoid of
order-preserving input relabellings. -/
instance : Groupoid OrderedProfile where
  Hom := Hom
  id P := @OrderIso.refl P.profile.inputs P.order.toLE
  comp {P Q R} f g := @OrderIso.trans _ _ _ P.order.toLE Q.order.toLE R.order.toLE f g
  inv {P Q} f := @OrderIso.symm _ _ P.order.toLE Q.order.toLE f
  id_comp _ := Hom.ext (fun _ => rfl)
  comp_id _ := Hom.ext (fun _ => rfl)
  assoc _ _ _ := Hom.ext (fun _ => rfl)
  inv_comp f := Hom.ext (fun i => f.toEquiv.apply_symm_apply i)
  comp_inv f := Hom.ext (fun i => f.toEquiv.symm_apply_apply i)

/-- Actual source input bijections are retained when the operation
order is forgotten, with every original one-color label preserved. -/
def forget : OrderedProfile ⥤ AnalyticIndex PUnit.{1} PUnit.unit where
  obj P := P.profile
  map f :=
    { inputEquiv := f.toEquiv
      inputColor_eq _ := Subsingleton.elim _ _
      outputColor_eq := rfl }
  map_id _ := ColoredProfile.Hom.ext rfl
  map_comp _ _ := ColoredProfile.Hom.ext rfl

/-- The actual ordered-profile morphism retains its original
finite input equivalence. -/
@[simp]
theorem forget_map_inputEquiv {P Q : OrderedProfile} (f : P ⟶ Q) :
    (forget.map f).inputEquiv = f.toEquiv := rfl

/-- Every finite ordered input has its actual cardinal word length. -/
def count (P : OrderedProfile) : ℕ := Nat.card P.profile.inputs

/-- The canonical increasing enumeration of every actual finite
operation order, including the empty order. -/
def enumeration (P : OrderedProfile) :
    @OrderIso (Fin (count P)) P.profile.inputs
      (inferInstance : LinearOrder (Fin (count P))).toLE P.order.toLE := by
  let : LinearOrder P.profile.inputs := P.order
  let : Fintype P.profile.inputs := Fintype.ofFinite _
  exact Fintype.orderIsoFinOfCardEq _ Fintype.card_eq_nat_card

/-- Original input bijections preserve the actual word length. -/
theorem count_eq {P Q : OrderedProfile} (f : P ⟶ Q) : count P = count Q :=
  Nat.card_congr f.toEquiv

/-- There is at most one increasing bijection of finite actual
ordered profiles. This follows from finite linear-order rigidity. -/
instance homSubsingleton (P Q : OrderedProfile) : Subsingleton (P ⟶ Q) := by
  let : LinearOrder P.profile.inputs := P.order
  let : LinearOrder Q.profile.inputs := Q.order
  exact OrderIso.subsingleton_of_wellFoundedLT

/-- Equal word lengths give the actual increasing bijection of
the original source and target input orders. -/
def homOfCountEq (P Q : OrderedProfile) (h : count P = count Q) : P ⟶ Q := by
  let : LE P.profile.inputs := P.order.toLE
  let : LE Q.profile.inputs := Q.order.toLE
  exact (enumeration P).symm.trans ((Fin.castOrderIso h).trans (enumeration Q))

/-- Actual ordered-profile maps are precisely equalities of their
word lengths, with the original increasing bijection as inverse. -/
def homEquivCount (P Q : OrderedProfile) : (P ⟶ Q) ≃ (count P = count Q) where
  toFun := count_eq
  invFun := homOfCountEq P Q
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The actual word-length functor sends every original increasing
relabeling to its proved equality of cardinal lengths. -/
def countFunctor : OrderedProfile ⥤ Discrete ℕ where
  obj P := Discrete.mk (count P)
  map f := Discrete.eqToHom' (count_eq f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The canonical length-n profile with its ordinary increasing
order; length zero is the original empty profile. -/
def canonical (n : ℕ) : OrderedProfile where
  profile := AnalyticIndex.ofFin (fun _ : Fin n => PUnit.unit)
  order := by
    change LinearOrder (Fin n)
    infer_instance

/-- Canonical finite word profiles retain the original length,
including degree zero. -/
@[simp]
theorem count_canonical (n : ℕ) : count (canonical n) = n := by
  exact Nat.card_fin n




end OrderedProfile

end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOrderedProfiles

/- Source proof segment: AssociativeOrderRelabel -/
section source_AssociativeOrderRelabel
/-!
# Actual associative-operation order relabeling
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory

/-- The original set associative coefficients on original
one-color finite profiles, with their actual permutation maps. -/
def orderFunctor : AnalyticIndex PUnit.{1} PUnit.unit ⥤ Type :=
  analyticToProfileFunctor PUnit.{1} PUnit.unit ⋙
    (ColoredOperadObj.ColorBlind.obj PUnit.{1} SetOperad.assoc).toCollection

/-- Every original coefficient is the supplied finite input order. -/
@[simp]
theorem orderFunctor_obj (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    orderFunctor.obj P = LinearOrder P.inputs := rfl

/-- The actual associative permutation map preserves the original
input comparisons along its actual source input equivalence. -/
theorem orderFunctor_map_le_iff {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q)
    (L : LinearOrder P.inputs) (a b : P.inputs) :
    @LE.le Q.inputs ((orderFunctor.map f) L).toLE (f.inputEquiv a) (f.inputEquiv b) ↔
      @LE.le P.inputs L.toLE a b := by
  with_unfolding_all
    let : LinearOrder P.toColoredProfile.inputs := L
    let : DecidableEq Q.toColoredProfile.inputs := f.inputEquiv.symm.decidableEq
    change @LE.le Q.inputs (f.inputEquiv.symm.linearOrder).toLE
      (f.inputEquiv a) (f.inputEquiv b) ↔ @LE.le P.inputs L.toLE a b
    change @LE.le P.inputs L.toLE (f.inputEquiv.symm (f.inputEquiv a))
      (f.inputEquiv.symm (f.inputEquiv b)) ↔ @LE.le P.inputs L.toLE a b
    have he :
        @LE.le P.inputs L.toLE (f.inputEquiv.symm (f.inputEquiv a))
            (f.inputEquiv.symm (f.inputEquiv b)) = @LE.le P.inputs L.toLE a b :=
      congrArg₂ (fun x y => @LE.le P.inputs L.toLE x y)
        (f.inputEquiv.symm_apply_apply a) (f.inputEquiv.symm_apply_apply b)
    exact ⟨fun hp => Eq.mp he hp, fun hp => Eq.mpr he hp⟩

/-- Forgetting an actual increasing ordered-profile bijection
and applying the original associative permutation action returns
the target's exact original order. -/
theorem orderFunctor_map_order {P Q : OrderedProfile} (f : P ⟶ Q) :
    (orderFunctor.map (OrderedProfile.forget.map f)) P.order = Q.order := by
  let : LinearOrder P.profile.inputs := P.order
  let : LinearOrder Q.profile.inputs := Q.order
  apply LinearOrder.ext
  intro a b
  have h := orderFunctor_map_le_iff (OrderedProfile.forget.map f) P.order
    (f.toEquiv.symm a) (f.toEquiv.symm b)
  have ht :
      @LE.le Q.profile.inputs
          ((orderFunctor.map (OrderedProfile.forget.map f)) P.order).toLE a b ↔
        @LE.le P.profile.inputs P.order.toLE (f.toEquiv.symm a) (f.toEquiv.symm b) := by
    have he :
        @LE.le Q.profile.inputs
            ((orderFunctor.map (OrderedProfile.forget.map f)) P.order).toLE
            ((OrderedProfile.forget.map f).inputEquiv (f.toEquiv.symm a))
            ((OrderedProfile.forget.map f).inputEquiv (f.toEquiv.symm b)) =
          @LE.le Q.profile.inputs
            ((orderFunctor.map (OrderedProfile.forget.map f)) P.order).toLE a b :=
      congrArg₂ (fun x y => @LE.le Q.profile.inputs
        ((orderFunctor.map (OrderedProfile.forget.map f)) P.order).toLE x y)
        (f.toEquiv.apply_symm_apply a) (f.toEquiv.apply_symm_apply b)
    exact he ▸ h
  exact ht.trans f.symm.le_iff_le

/-- Every original associative relabeling whose order image is
the given target order is an actual increasing input bijection. -/
def orderedHomOfRelabel {P Q : OrderedProfile} (f : P.profile ⟶ Q.profile)
    (h : (orderFunctor.map f) P.order = Q.order) : P ⟶ Q := by
  let : LinearOrder P.profile.inputs := P.order
  let : LinearOrder Q.profile.inputs := Q.order
  refine { toEquiv := f.inputEquiv, map_rel_iff' := ?_ }
  intro a b
  exact (congrArg (fun L : LinearOrder Q.profile.inputs =>
      @LE.le Q.profile.inputs L.toLE (f.inputEquiv a) (f.inputEquiv b)) h).symm ▸
    orderFunctor_map_le_iff f P.order a b

/-- The recovered increasing map retains exactly the original
source input bijection. -/
@[simp]
theorem orderedHomOfRelabel_inputEquiv {P Q : OrderedProfile} (f : P.profile ⟶ Q.profile)
    (h : (orderFunctor.map f) P.order = Q.order) :
    (orderedHomOfRelabel f h).toEquiv = f.inputEquiv := rfl




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOrderRelabel

/- Source proof segment: AssociativeWordLengthEquivalence -/
section source_AssociativeWordLengthEquivalence
/-!
# Ordered associative input profiles are discrete word lengths
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us

namespace CategoryTheory.Operad.Tensor.Associative.OrderedProfile

open CategoryTheory

/-- The canonical finite increasingly ordered profiles at every
original length, including zero. -/
def canonicalFunctor : Discrete ℕ ⥤ OrderedProfile := Discrete.functor canonical

/-- The actual increasing enumeration is the isomorphism between
an original ordered input profile and its canonical finite word profile. -/
def canonicalIso (P : OrderedProfile) : P ≅ canonical (count P) where
  hom := homOfCountEq P (canonical (count P)) (count_canonical (count P)).symm
  inv := homOfCountEq (canonical (count P)) P (count_canonical (count P))
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Canonicalizing the original order by its actual increasing
input enumeration is natural under every original increasing relabeling. -/
def canonicalUnitIso : 𝟭 OrderedProfile ≅ countFunctor ⋙ canonicalFunctor :=
  NatIso.ofComponents canonicalIso (fun _ => Subsingleton.elim _ _)

/-- The actual canonical finite word profile has exactly its
original supplied length. -/
def canonicalCounitIso : canonicalFunctor ⋙ countFunctor ≅ 𝟭 (Discrete ℕ) :=
  NatIso.ofComponents (fun n => eqToIso (congrArg Discrete.mk (count_canonical n.as)))
    (fun _ => Subsingleton.elim _ _)

/-- The actual finite ordered associative input groupoid is
equivalent to discrete nonnegative word lengths, with explicit
forward/inverse functors and natural inverse isomorphisms. -/
def wordLengthEquivalence : OrderedProfile ≌ Discrete ℕ :=
  Equivalence.mk countFunctor canonicalFunctor canonicalUnitIso canonicalCounitIso

/-- The explicit increasing-enumeration equivalence proves the
actual original word-length functor is an equivalence. -/
instance countFunctorIsEquivalence : countFunctor.IsEquivalence :=
  inferInstanceAs wordLengthEquivalence.functor.IsEquivalence

/-- Ordered profile colimits require only the original small
word-length colimits. Their original indexing groupoid is essentially small. -/
instance orderedProfileEssentiallySmall : EssentiallySmall.{us} OrderedProfile :=
  (essentiallySmall_congr wordLengthEquivalence).2 inferInstance

/-- The comparison retains the actual word length of every
original ordered finite profile. -/
@[simp]
theorem wordLengthEquivalence_obj (P : OrderedProfile) :
    wordLengthEquivalence.functor.obj P = Discrete.mk (count P) := rfl

/-- The explicit inverse gives the canonical ordered finite
profile at every word length, including degree zero. -/
@[simp]
theorem wordLengthEquivalence_inverse_obj (n : Discrete ℕ) :
    wordLengthEquivalence.inverse.obj n = canonical n.as := rfl




end CategoryTheory.Operad.Tensor.Associative.OrderedProfile
end
end
end source_AssociativeWordLengthEquivalence

/- Source proof segment: AssociativeOrderFibers -/
section source_AssociativeOrderFibers
/-!
# The actual associative coefficient fibers are ordered finite profiles
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory

/-- Each actual finite profile has the discrete fiber of its
original associative-operation linear orders. Original permutations
act by the actual coefficient relabeling functor. -/
def orderCategories : AnalyticIndex PUnit.{1} PUnit.unit ⥤ Cat := orderFunctor ⋙ typeToCat

/-- Every actual coefficient fiber is discrete: equality arrows
between its supplied original orders are unique. -/
instance orderCategoriesHomSubsingleton (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (a b : orderCategories.obj P) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton
    ((show Discrete (LinearOrder P.inputs) from a) ⟶
      (show Discrete (LinearOrder P.inputs) from b)))

/-- The actual joint indexing of original profiles and their
associative coefficients, with all original quotient maps retained. -/
abbrev OrderFiber := Grothendieck orderCategories

namespace OrderFiber

private theorem identityNaturality {V : Type*} [Category* V] {A B : V}
    (f g : A ⟶ B) (h : f = g) : f ≫ 𝟙 B = 𝟙 A ≫ g :=
  (Category.comp_id f).trans (h.trans (Category.id_comp g).symm)

/-- Each original profile and coefficient order is its actual
ordered input profile. -/
def toOrdered : OrderFiber ⥤ OrderedProfile where
  obj s := ⟨s.base, s.fiber.as⟩
  map f := orderedHomOfRelabel f.base (Discrete.eq_of_hom f.fiber)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Every ordered profile supplies its original coefficient in
the actual profile fiber, with the original input map and proved
coefficient relabeling equality on every morphism. -/
def fromOrdered : OrderedProfile ⥤ OrderFiber where
  obj P := ⟨P.profile, Discrete.mk P.order⟩
  map f :=
    { base := OrderedProfile.forget.map f
      fiber := Discrete.eqToHom' (orderFunctor_map_order f) }
  map_id P := by
    refine Grothendieck.ext _ _ (OrderedProfile.forget.map_id P) ?_
    with_unfolding_all exact Subsingleton.elim _ _
  map_comp f g := by
    refine Grothendieck.ext _ _ (OrderedProfile.forget.map_comp f g) ?_
    with_unfolding_all exact Subsingleton.elim _ _

/-- Recovering the joint coefficient indexing from the actual
ordered-profile map retains the full original input map and
coefficient equality morphism. -/
theorem fromOrdered_toOrdered_map {s t : OrderFiber} (f : s ⟶ t) :
    fromOrdered.map (toOrdered.map f) = f := by
  refine Grothendieck.ext _ _ (ColoredProfile.Hom.ext rfl) ?_
  with_unfolding_all exact Subsingleton.elim _ _

/-- The recovered increasing input map is the original one. -/
theorem toOrdered_fromOrdered_map {P Q : OrderedProfile} (f : P ⟶ Q) :
    toOrdered.map (fromOrdered.map f) = f := Subsingleton.elim _ _

/-- The original profile/coefficient indexing is recovered by
the explicit conversions, naturally under all its original maps. -/
def unitIso : 𝟭 OrderFiber ≅ toOrdered ⋙ fromOrdered :=
  NatIso.ofComponents (fun s => Iso.refl s) (by
    intro s t f
    exact identityNaturality f (fromOrdered.map (toOrdered.map f))
      (fromOrdered_toOrdered_map f).symm)

/-- The explicit ordered profiles are recovered naturally under
every actual increasing original input bijection. -/
def counitIso : fromOrdered ⋙ toOrdered ≅ 𝟭 OrderedProfile :=
  NatIso.ofComponents (fun P => Iso.refl P) (by
    intro P Q f
    exact Subsingleton.elim _ _)

/-- The actual associative coefficient Grothendieck indexing is
the original finite ordered-profile groupoid, with explicit inverse
object and full morphism constructions. -/
def orderedEquivalence : OrderFiber ≌ OrderedProfile :=
  Equivalence.mk toOrdered fromOrdered unitIso counitIso

/-- Taking the actual associative coefficient quotient leaves
the discrete original word lengths, including degree zero. -/
def wordLengthEquivalence : OrderFiber ≌ Discrete ℕ :=
  orderedEquivalence.trans OrderedProfile.wordLengthEquivalence

/-- The actual combined profile/coefficient index is source-small,
through its proved equivalence to original finite word lengths. -/
instance orderFiberEssentiallySmall : EssentiallySmall.{0} OrderFiber :=
  (essentiallySmall_congr wordLengthEquivalence).2 inferInstance




end OrderFiber

end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOrderFibers

/- Source proof segment: UnitScalarNullary -/
section source_UnitScalarNullary
/-!
# The actual empty-tensor multiplication on the empty input
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory FiniteFamily

private theorem nullaryScalarFromSquares {V : Type*} [Category* V]
    {A B X Y Z : V} (a : A ≅ X) (r : A ⟶ B) (b : B ⟶ Y) (c : X ⟶ Y)
    (u : Y ⟶ Z) (z : B ⟶ Z) (q : X ⟶ Z) (w : A ⟶ Z)
    (hn : r ≫ b = a.hom ≫ c) (hb : b ≫ u = z)
    (hc : c ≫ u = q) (hr : r ≫ z = w) : a.inv ≫ w = q := by
  have h : w = a.hom ≫ q := by
    calc
      w = r ≫ z := hr.symm
      _ = r ≫ (b ≫ u) := congrArg (fun k => r ≫ k) hb.symm
      _ = (a.hom ≫ c) ≫ u := (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ u) hn)
      _ = a.hom ≫ q := (Category.assoc _ _ _).trans (congrArg (fun k => a.hom ≫ k) hc)
  exact (congrArg (fun k => a.inv ≫ k) h).trans (a.inv_hom_id_assoc _)

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The family of zero empty blocks is the actual empty family. -/
def scalarNullaryBlocksIso : emptyScalarBlocks (C := C) (FintypeCat.of Empty) ≅
    (FiniteFamily.empty : FiniteFamily (FiniteFamily C)) :=
  FiniteFamily.isoOfReindex (Equiv.refl Empty) (fun p => nomatch p)

/-- The family of zero actual empty tensors is the actual empty family. -/
def scalarNullaryFamilyIso : emptyScalarFamily (C := C) (FintypeCat.of Empty) ≅
    (FiniteFamily.empty : FiniteFamily C) :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).mapIso scalarNullaryBlocksIso ≪≫
    FiniteFamily.mapEmptyIso (FiniteTensor.tensor (V := C))

omit [FiniteTensor C] in
/-- The original zero-block flattening and its original empty
input bijection compose to the same empty source as before. -/
theorem scalarNullaryFlattenSquare :
    (FiniteFamily.flatten (C := C)).map (scalarNullaryBlocksIso (C := C)).hom ≫
        (Operad.Tensor.emptyNestedFlattenIso (C := C)).hom =
      (emptyScalarFlattenIso (C := C) (FintypeCat.of Empty)).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    exact nomatch p.1
  · intro p
    exact nomatch p.1

/-- The actual multiplication at the empty input is precisely
the tensor of the original empty-family identification. It is
derived from the source right unit law, never from terminality. -/
theorem emptyScalarTensorIso_nullary :
    (emptyScalarTensorIso (C := C) (FintypeCat.of Empty)).hom =
      (FiniteTensor.tensor (V := C)).map (scalarNullaryFamilyIso (C := C)).hom := by
  let T := FiniteTensor.tensor (V := C)
  let a := (FiniteTensor.flattenIso (V := C)).app (emptyScalarBlocks (C := C) (FintypeCat.of Empty))
  let r := T.map ((FiniteFamily.flatten (C := C)).map (scalarNullaryBlocksIso (C := C)).hom)
  let b := (FiniteTensor.flattenIso (V := C)).hom.app (FiniteFamily.empty : FiniteFamily (FiniteFamily C))
  let c := T.map ((FiniteFamily.map T).map (scalarNullaryBlocksIso (C := C)).hom)
  let u := T.map (FiniteFamily.mapEmptyIso T).hom
  let z := T.map (Operad.Tensor.emptyNestedFlattenIso (C := C)).hom
  let q := T.map (scalarNullaryFamilyIso (C := C)).hom
  let w := T.map (emptyScalarFlattenIso (C := C) (FintypeCat.of Empty)).hom
  have hn : r ≫ b = a.hom ≫ c :=
    (FiniteTensor.flattenIso (V := C)).hom.naturality (scalarNullaryBlocksIso (C := C)).hom
  have hb : b ≫ u = z := Operad.Tensor.flattenIso_empty_collapse
  have hc : c ≫ u = q := (T.map_comp _ _).symm
  have hr : r ≫ z = w :=
    (T.map_comp _ _).symm.trans (congrArg T.map (scalarNullaryFlattenSquare (C := C)))
  exact nullaryScalarFromSquares a r b c u z q w hn hb hc hr



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitScalarNullary

/- Source proof segment: UnitCopowerUnitSource -/
section source_UnitCopowerUnitSource
/-!
# The actual unit-source comparison of unit copowers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits FiniteFamily

private theorem unitIsoFromInjection {V : Type*} [Category* V]
    {U E A B : V} (i : U ≅ E) (a : E ⟶ A) (c : A ⟶ B)
    (k : U ⟶ A) (m : U ⟶ E) (j : E ⟶ B)
    (hk : k = i.hom ≫ a) (hb : k ≫ c = m ≫ j) (hm : m = i.hom) : a ≫ c = j := by
  apply (cancel_epi i.hom).1
  rw [← Category.assoc i.hom a, ← hk, hb, hm]

/-- The original source empty tensor has its unique empty choice. -/
def emptyChoice : (FiniteTensor.tensor (V := Type us)).obj (FiniteFamily.empty : FiniteFamily (Type us)) :=
  fun p => nomatch p

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]

/-- The actual empty-profile coefficient injection factors are
the original empty-family comparisons, with the original empty bijections. -/
theorem unitSourceFactorSquare :
    (scalarNullaryFamilyIso (C := C)).hom ≫
        (Operad.ColoredOperadObj.MapData.emptyFamilyIso (functor C)).hom =
      tensorιFactors C (FiniteFamily.empty : FiniteFamily (Type us)) emptyChoice := by
  apply FiniteFamily.Hom_ext
  · ext p
    exact nomatch p
  · intro p
    exact nomatch p

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual unit-source comparison is the original unit-copy
injection at the unique empty source choice. This is derived from
source empty tensor coherence and the constructed coproduct comparison. -/
theorem unitSourceIso_hom :
    (Operad.ColoredOperadObj.MapData.unitSourceIso (preserving C)).hom =
      Sigma.ι (fun _ : (FiniteTensor.tensor (V := Type us)).obj
        (FiniteFamily.empty : FiniteFamily (Type us)) => unitObject C) emptyChoice := by
  let T := FiniteTensor.tensor (V := C)
  let i := T.mapIso (scalarNullaryFamilyIso (C := C))
  let a := T.map (Operad.ColoredOperadObj.MapData.emptyFamilyIso (functor C)).hom
  let c := (comparisonIso C).hom.app (FiniteFamily.empty : FiniteFamily (Type us))
  let k := tensorι C (FiniteFamily.empty : FiniteFamily (Type us)) emptyChoice
  let m := (emptyScalarTensorIso (C := C) (FintypeCat.of Empty)).hom
  let j := Sigma.ι (fun _ : (FiniteTensor.tensor (V := Type us)).obj
    (FiniteFamily.empty : FiniteFamily (Type us)) => unitObject C) emptyChoice
  have hk : k = i.hom ≫ a :=
    (congrArg T.map (unitSourceFactorSquare C)).symm.trans (T.map_comp _ _)
  have hb : k ≫ c = m ≫ j :=
    tensorι_comparison C (FiniteFamily.empty : FiniteFamily (Type us)) emptyChoice
  have hm : m = i.hom := emptyScalarTensorIso_nullary
  exact unitIsoFromInjection i a c k m j hk hb hm



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerUnitSource

/- Source proof segment: AssociativeTensorInjections -/
section source_AssociativeTensorInjections
/-!
# Original coefficient injections of the associative tensor operad
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits Operad FiniteFamily

private theorem substitutionInjectionFromComparison {V : Type*} [Category* V]
    {U A B D E Q : V} (e : A ≅ B) (i : U ⟶ A) (c : A ⟶ D) (b : D ⟶ Q)
    (m : U ⟶ E) (j : E ⟶ D) (k : E ⟶ Q)
    (hc : i ≫ c = m ≫ j) (hb : j ≫ b = k) :
    (i ≫ e.hom) ≫ (e.inv ≫ (c ≫ b)) = m ≫ k := by
  rw [Category.assoc i e.hom, e.hom_inv_id_assoc,
    ← Category.assoc i c, hc, Category.assoc m j, hb]

/-- The original lifted linear-order action under an arbitrary
finite input bijection. -/
def associativeRelabel {P Q : ColoredProfile PUnit.{1}} (f : P ⟶ Q)
    (o : ULift.{us} (LinearOrder P.inputs)) : ULift.{us} (LinearOrder Q.inputs) :=
  letI : LinearOrder P.inputs := o.down
  letI : DecidableEq Q.inputs := f.inputEquiv.symm.decidableEq
  ULift.up f.inputEquiv.symm.linearOrder

/-- The genuine source lifted associative action is the original
linear-order relabelling, at every original finite profile. -/
theorem associativeSetOperad_relabel {P Q : ColoredProfile PUnit.{1}} (f : P ⟶ Q)
    (o : ULift.{us} (LinearOrder P.inputs)) :
    associativeSetOperad.{us}.toCollection.map f o = associativeRelabel f o := rfl

/-- The genuine source unary unit is the original canonical
linear order, lifted into the source operation universe. -/
theorem associativeSetOperad_unit (c : PUnit.{1}) :
    associativeSetOperad.{us}.unit c emptyChoice =
      ULift.up (inferInstance : LinearOrder PUnit.{1}) := rfl

/-- Original coefficients of one simultaneous associative
substitution, including its root and every original finite branch. -/
def associativeFactors (d : ColoredSubstitutionData PUnit.{1}) : FiniteFamily (Type us) :=
  (ColoredOperadObj.substitutionFactors associativeSetOperad.{us}.toCollection).obj d

/-- The original lexicographic order on the original dependent
sum of input blocks; no linear order is discarded. -/
def associativeLexicographic (d : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} d).index, (associativeFactors.{us} d).obj o) :
    ULift.{us} (LinearOrder d.totalProfile.inputs) :=
  letI : LinearOrder d.inner.index := (a none).down
  letI : ∀ i : d.inner.index, LinearOrder (d.inner.obj i).inputs := fun i => (a (some i)).down
  ULift.up (inferInstance : LinearOrder (Σₗ i : d.inner.index, (d.inner.obj i).inputs))

/-- The source associative substitution is precisely the lifted
original lexicographic substitution on every finite input block. -/
theorem associativeSetOperad_substitution (d : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} d).index, (associativeFactors.{us} d).obj o) :
    associativeSetOperad.{us}.subst.app d a = associativeLexicographic.{us} d a := by
  with_unfolding_all rfl

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Every original permutation acts on an actual coefficient
coproduct injection by the original lifted linear-order permutation. -/
@[reassoc]
theorem associativeOperad_relabel_ι {P Q : ColoredProfile PUnit.{1}} (f : P ⟶ Q)
    (o : ULift.{us} (LinearOrder P.inputs)) :
    Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) => unitObject C) o ≫
        (associativeOperad C).toCollection.map f =
      Sigma.ι (fun _ : ULift.{us} (LinearOrder Q.inputs) => unitObject C) (associativeRelabel f o) :=
  (ι_map C (associativeSetOperad.{us}.toCollection.map f) o).trans
    (congrArg (fun z => Sigma.ι (fun _ : ULift.{us} (LinearOrder Q.inputs) => unitObject C) z)
      (associativeSetOperad_relabel f o))

/-- The actual associative unary unit is the actual coefficient
coproduct injection of the original canonical linear order. -/
theorem associativeOperad_unit_ι (c : PUnit.{1}) :
    (associativeOperad C).unit c =
      Sigma.ι (fun _ : ULift.{us} (LinearOrder PUnit.{1}) => unitObject C)
        (ULift.up (inferInstance : LinearOrder PUnit.{1})) :=
  (congrArg (fun k => k ≫ (functor C).map (associativeSetOperad.{us}.unit c))
    (unitSourceIso_hom C)).trans
    ((ι_map C (associativeSetOperad.{us}.unit c) emptyChoice).trans
      (congrArg (fun z => Sigma.ι (fun _ : ULift.{us} (LinearOrder PUnit.{1}) => unitObject C) z)
        (associativeSetOperad_unit c)))

/-- Tensor every original associative coefficient injection,
then use the original canonical substitution-factor comparison. -/
def associativeSubstitutionι (d : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} d).index, (associativeFactors.{us} d).obj o) :
    (FiniteTensor.tensor (V := C)).obj (emptyScalarFamily (associativeFactors.{us} d).index) ⟶
      (ColoredOperadObj.substitutionSource (associativeOperad C).toCollection).obj d :=
  tensorι C (associativeFactors.{us} d) a ≫
    (FiniteTensor.tensor (V := C)).map
      (ColoredOperadObj.MapData.factorsIso (functor C) associativeSetOperad.{us}.toCollection d).hom

/-- Actual tensor associative substitution sends each tensor of
original coefficient-copy injections to its exact original lifted
lexicographic coefficient injection after actual unit multiplication. -/
@[reassoc]
theorem associativeSubstitutionι_subst (d : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} d).index, (associativeFactors.{us} d).obj o) :
    associativeSubstitutionι C d a ≫ (associativeOperad C).subst.app d =
      (emptyScalarTensorIso (associativeFactors.{us} d).index).hom ≫
        Sigma.ι (fun _ : ULift.{us} (LinearOrder d.totalProfile.inputs) => unitObject C)
          (associativeLexicographic.{us} d a) := by
  let e := (FiniteTensor.tensor (V := C)).mapIso
    (ColoredOperadObj.MapData.factorsIso (functor C) associativeSetOperad.{us}.toCollection d)
  have hb : Sigma.ι (fun _ : (∀ o : (associativeFactors.{us} d).index, (associativeFactors.{us} d).obj o) => unitObject
    C) a ≫
      (functor C).map (associativeSetOperad.{us}.subst.app d) =
    Sigma.ι (fun _ : ULift.{us} (LinearOrder d.totalProfile.inputs) => unitObject C)
      (associativeLexicographic.{us} d a) :=
    (ι_map C (associativeSetOperad.{us}.subst.app d) a).trans
      (congrArg (fun z => Sigma.ι (fun _ : ULift.{us} (LinearOrder d.totalProfile.inputs) => unitObject C) z)
        (associativeSetOperad_substitution d a))
  have hs : (associativeOperad C).subst.app d =
      e.inv ≫ (((comparisonIso C).hom.app (associativeFactors.{us} d)) ≫
        (functor C).map (associativeSetOperad.{us}.subst.app d)) := Category.assoc _ _ _
  exact (congrArg (fun k => associativeSubstitutionι C d a ≫ k) hs).trans
    (substitutionInjectionFromComparison e (tensorι C (associativeFactors.{us} d) a)
    ((comparisonIso C).hom.app (associativeFactors.{us} d))
    ((functor C).map (associativeSetOperad.{us}.subst.app d))
    (emptyScalarTensorIso (associativeFactors.{us} d).index).hom
    (Sigma.ι (fun _ : (∀ o : (associativeFactors.{us} d).index, (associativeFactors.{us} d).obj o) => unitObject C) a)
    (Sigma.ι (fun _ : ULift.{us} (LinearOrder d.totalProfile.inputs) => unitObject C)
      (associativeLexicographic.{us} d a))
    (tensorι_comparison C (associativeFactors.{us} d) a) hb)





end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_AssociativeTensorInjections

/- Source proof segment: LiftedAssociativeOrderFunctor -/
section source_LiftedAssociativeOrderFunctor
/-!
# Actual lifted associative coefficient fibers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory CategoryTheory.FiniteTensor.UnitCopower

/-- The actual source-universe lifted associative coefficients
on every original finite one-color profile. -/
def liftedOrderFunctor : AnalyticIndex PUnit.{1} PUnit.unit ⥤ Type us :=
  analyticToProfileFunctor PUnit.{1} PUnit.unit ⋙
    (ColoredOperadObj.ColorBlind.obj PUnit.{1} SetOperad.assocULift.{us}).toCollection

/-- Every source lifted coefficient is the lifted original
finite input order, with the original finite input type retained. -/
@[simp]
theorem liftedOrderFunctor_obj (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    liftedOrderFunctor.{us}.obj P = ULift.{us} (LinearOrder P.inputs) := rfl

/-- The lifted original associative permutation map projects
to the actual original associative permutation of input orders. -/
theorem liftedOrderFunctor_map_down {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q)
    (o : liftedOrderFunctor.{us}.obj P) :
    ((liftedOrderFunctor.{us}.map f) o).down = (orderFunctor.map f) o.down := rfl

/-- Applying the actual original input map to a lifted order is
the lift of its original source coefficient map. -/
theorem liftedOrderFunctor_map_up {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q)
    (o : orderFunctor.obj P) :
    (liftedOrderFunctor.{us}.map f) (ULift.up o) = ULift.up ((orderFunctor.map f) o) := rfl

/-- The actual source-us discrete fiber category of lifted
associative coefficients, with every original permutation map. -/
def liftedOrderCategories : AnalyticIndex PUnit.{1} PUnit.unit ⥤ Cat.{us, us} :=
  liftedOrderFunctor.{us} ⋙ typeToCat

/-- Equality arrows in each actual lifted coefficient fiber are
unique, through its original discrete coefficient category. -/
instance liftedOrderCategoriesHomSubsingleton (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (a b : liftedOrderCategories.{us}.obj P) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton
    ((show Discrete (ULift.{us} (LinearOrder P.inputs)) from a) ⟶
      (show Discrete (ULift.{us} (LinearOrder P.inputs)) from b)))

/-- The actual joint indexing of original profiles and source-us
lifted associative coefficients. -/
abbrev LiftedOrderFiber := Grothendieck liftedOrderCategories.{us}




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_LiftedAssociativeOrderFunctor

/- Source proof segment: AssociativeProfileTensorNaturality -/
section source_AssociativeProfileTensorNaturality
/-!
# Actual associative weighted-profile tensor coproduct naturality
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

private theorem profileTensorIsoFromSquares {V : Type*} [Category* V]
    {X Y PX PY QX QY : V} (f : X ⟶ Y) (p : X ⟶ PX) (q : Y ⟶ PY)
    (g : PX ⟶ PY) (a : PX ⟶ QX) (b : PY ⟶ QY) (s : QX ⟶ QY)
    (hp : f ≫ q = p ≫ g) (ha : g ≫ b = a ≫ s) :
    f ≫ (q ≫ b) = (p ≫ a) ≫ s := by
  rw [← Category.assoc f q, hp, Category.assoc p g, ha, ← Category.assoc]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Every actual original profile relabeling retains its source
associative coefficient map and all original input maps under the
displayed coefficient/leaf factor identification. -/
theorem associativeProfileFactorsIso_naturality (X : C)
    {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q) :
    (analyticFactors (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X)).map f ≫ (associativeProfileFactorsIso X Q).hom =
      (associativeProfileFactorsIso X P).hom ≫
        coefficientLeafMap ((FiniteTensor.UnitCopower.functor C).map (liftedOrderFunctor.map f))
          ((analyticInputFamily (fun _ : PUnit.{1} => X)).map f) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      let a := (FiniteTensor.UnitCopower.functor C).map (liftedOrderFunctor.map f)
      change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
      exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)
    | some i =>
      let a := eqToHom (congrArg (fun _ : PUnit.{1} => X) (f.inputColor_eq i))
      change HEq (a ≫ 𝟙 _) (𝟙 _ ≫ a)
      exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual associative weighted tensor profile coproduct
identification is natural under every original coefficient permutation
and every original input tensor relabeling. -/
theorem associativeProfileTensorIso_naturality (X : C)
    {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q) :
    (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X)).map f ≫ (associativeProfileTensorIso X Q).hom =
      (associativeProfileTensorIso X P).hom ≫
        Sigma.map' (liftedOrderFunctor.map f)
          (fun _ => (FiniteTensor.tensor (V := C)).map
            ((analyticInputFamily (fun _ : PUnit.{1} => X)).map f)) := by
  let T := FiniteTensor.tensor (V := C)
  let l := (analyticInputFamily (fun _ : PUnit.{1} => X)).map f
  let g := coefficientLeafMap ((FiniteTensor.UnitCopower.functor C).map (liftedOrderFunctor.map f)) l
  have hp :
      (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (fun _ : PUnit.{1} => X)).map f ≫
          ((T.mapIso (associativeProfileFactorsIso X Q)).hom) =
        (T.mapIso (associativeProfileFactorsIso X P)).hom ≫ T.map g :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (associativeProfileFactorsIso_naturality X f)).trans (T.map_comp _ _))
  exact profileTensorIsoFromSquares _ _ _ _ _ _ _ hp
    (coefficientCopowerTensorIso_naturality (liftedOrderFunctor.map f) l)



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeProfileTensorNaturality

/- Source proof segment: AssociativeTensorCoproductFunctor -/
section source_AssociativeTensorCoproductFunctor
/-!
# The actual original order-indexed tensor coproduct profile functor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]

/-- The original input tensor functor on the original profiles. -/
def associativeInputTensor (X : C) : AnalyticIndex PUnit.{1} PUnit.unit ⥤ C :=
  analyticInputFamily (fun _ : PUnit.{1} => X) ⋙ FiniteTensor.tensor

/-- The actual profile functor taking the tensor coproduct over
all source-us original associative operation orders. Its maps use
the actual original coefficient and input tensor maps. -/
def associativeTensorCoproductFunctor (X : C) : AnalyticIndex PUnit.{1} PUnit.unit ⥤ C where
  obj P := ∐ (fun _ : liftedOrderFunctor.{us}.obj P => (associativeInputTensor X).obj P)
  map f := Sigma.map' (liftedOrderFunctor.map f) (fun _ => (associativeInputTensor X).map f)
  map_id P := by
    rw [liftedOrderFunctor.map_id, (associativeInputTensor X).map_id]
    exact Sigma.map'_id_id (f := fun _ : liftedOrderFunctor.{us}.obj P =>
      (associativeInputTensor X).obj P)
  map_comp {P Q R} f g := by
    rw [liftedOrderFunctor.map_comp, (associativeInputTensor X).map_comp]
    exact (Sigma.map'_comp_map'
      (f := fun _ : liftedOrderFunctor.{us}.obj R => (associativeInputTensor X).obj R)
      (g := fun _ : liftedOrderFunctor.{us}.obj Q => (associativeInputTensor X).obj Q)
      (h := fun _ : liftedOrderFunctor.{us}.obj P => (associativeInputTensor X).obj P)
      (liftedOrderFunctor.map g) (liftedOrderFunctor.map f)
      (fun _ => (associativeInputTensor X).map g) (fun _ => (associativeInputTensor X).map f)).symm

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual original associative weighted tensor profile
functor is naturally the actual order-indexed tensor coproduct.
Both its coefficient and input permutation maps are retained. -/
def associativeTensorProfileNatIso (X : C) :
    analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) ≅ associativeTensorCoproductFunctor X :=
  NatIso.ofComponents (associativeProfileTensorIso X)
    (fun f => associativeProfileTensorIso_naturality X f)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeTensorCoproductFunctor

/- Source proof segment: AssociativeOrderedTensorDiagram -/
section source_AssociativeOrderedTensorDiagram
/-!
# Original ordered input tensors and their actual word-length colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original input tensor on every original increasingly
ordered finite profile, using its original profile relabelings. -/
def orderedTensorDiagram (X : C) : OrderedProfile ⥤ C :=
  OrderedProfile.forget ⋙ analyticInputFamily (fun _ : PUnit.{1} => X) ⋙ FiniteTensor.tensor

/-- The original finite tensor at each discrete nonnegative
word length, with the empty finite input tensor retained at zero. -/
def wordLengthTensorDiagram (X : C) : Discrete ℕ ⥤ C :=
  Discrete.functor (fun n => (FiniteTensor.tensor (V := C)).obj
    ({ index := FintypeCat.of (Fin n), obj := fun _ => X } : FiniteFamily C))

/-- The canonical ordered input profile has exactly the original
finite tensor at its supplied word length. -/
def canonicalTensorIso (X : C) :
    OrderedProfile.canonicalFunctor ⋙ orderedTensorDiagram X ≅ wordLengthTensorDiagram X :=
  Discrete.natIso (fun _ => Iso.refl _)

/-- Increasingly enumerate every original associative operation
order, retaining the actual finite tensor input bijection. -/
def orderedTensorLengthIso (X : C) :
    orderedTensorDiagram X ≅ OrderedProfile.countFunctor ⋙ wordLengthTensorDiagram X :=
  (Functor.leftUnitor (orderedTensorDiagram X)).symm ≪≫
    Functor.isoWhiskerRight OrderedProfile.canonicalUnitIso (orderedTensorDiagram X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft OrderedProfile.countFunctor (canonicalTensorIso X)

variable [HasColimitsOfShape (Discrete ℕ) C]

/-- The actual ordered input diagram has its colimit from the
source word-length coproduct and its actual increasing enumeration. -/
instance hasColimitOrderedTensorDiagram (X : C) : HasColimit (orderedTensorDiagram X) := by
  let : HasColimit (OrderedProfile.countFunctor ⋙ wordLengthTensorDiagram X) := inferInstance
  exact hasColimit_of_iso (orderedTensorLengthIso X)

/-- Taking the actual original ordered-profile colimit gives the
coproduct of all original finite input tensors, including degree zero. -/
def orderedTensorColimitLengthIso (X : C) :
    colimit (orderedTensorDiagram X) ≅ colimit (wordLengthTensorDiagram X) :=
  HasColimit.isoOfNatIso (orderedTensorLengthIso X) ≪≫
    Functor.Final.colimitIso OrderedProfile.countFunctor (wordLengthTensorDiagram X)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOrderedTensorDiagram

/- Source proof segment: LiftedAssociativeOrderEquivalence -/
section source_LiftedAssociativeOrderEquivalence
/-!
# Actual lift/unlift equivalence of associative coefficient fibers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us usSize

namespace CategoryTheory.Operad.Tensor.Associative.LiftedOrderFiber

open CategoryTheory

private theorem identityNaturality {V : Type*} [Category* V] {A B : V}
    (f g : A ⟶ B) (h : f = g) : f ≫ 𝟙 B = 𝟙 A ≫ g :=
  (Category.comp_id f).trans (h.trans (Category.id_comp g).symm)

/-- Unlift the actual source-us coefficient while retaining its
original profile and every original input and coefficient map. -/
def unlift : LiftedOrderFiber.{us} ⥤ OrderFiber where
  obj s := ⟨s.base, Discrete.mk s.fiber.as.down⟩
  map f :=
    { base := f.base
      fiber := Discrete.eqToHom'
        ((liftedOrderFunctor_map_down f.base _).symm.trans
          (congrArg ULift.down (Discrete.eq_of_hom f.fiber))) }
  map_id _ := by
    refine Grothendieck.ext _ _ rfl ?_
    with_unfolding_all exact Subsingleton.elim _ _
  map_comp _ _ := by
    refine Grothendieck.ext _ _ rfl ?_
    with_unfolding_all exact Subsingleton.elim _ _

/-- Lift the original coefficient into the actual source universe
without changing its profile, input bijections, or coefficient equalities. -/
def lift : OrderFiber ⥤ LiftedOrderFiber.{us} where
  obj s := ⟨s.base, Discrete.mk (ULift.up s.fiber.as)⟩
  map f :=
    { base := f.base
      fiber := Discrete.eqToHom'
        ((liftedOrderFunctor_map_up f.base _).trans
          (congrArg ULift.up (Discrete.eq_of_hom f.fiber))) }
  map_id _ := by
    refine Grothendieck.ext _ _ rfl ?_
    with_unfolding_all exact Subsingleton.elim _ _
  map_comp _ _ := by
    refine Grothendieck.ext _ _ rfl ?_
    with_unfolding_all exact Subsingleton.elim _ _

/-- The original base map and discrete coefficient equality are
recovered after the actual source lift and unlift. -/
theorem unlift_lift_map {s t : OrderFiber} (f : s ⟶ t) :
    unlift.map (lift.{us}.map f) = f := by
  refine Grothendieck.ext _ _ rfl ?_
  with_unfolding_all exact Subsingleton.elim _ _

/-- Unlifting and lifting the source-us fiber recovers the original
profile map and original lifted coefficient equality morphism. -/
theorem lift_unlift_map {s t : LiftedOrderFiber.{us}} (f : s ⟶ t) :
    lift.map (unlift.map f) = f := by
  refine Grothendieck.ext _ _ rfl ?_
  with_unfolding_all exact Subsingleton.elim _ _

/-- The actual original lifted coefficient fiber is recovered
naturally by the source lift/unlift object and full morphism constructions. -/
def unitIso : 𝟭 LiftedOrderFiber.{us} ≅ unlift ⋙ lift :=
  NatIso.ofComponents (fun s => Iso.refl s) (by
    intro s t f
    exact identityNaturality f (lift.map (unlift.map f)) (lift_unlift_map f).symm)

/-- The actual unlifted original coefficient fiber is recovered
naturally under all original profile and coefficient maps. -/
def counitIso : lift.{us} ⋙ unlift ≅ 𝟭 OrderFiber :=
  NatIso.ofComponents (fun s => Iso.refl s) (by
    intro s t f
    exact identityNaturality (unlift.{us}.map (lift.{us}.map f)) f (unlift_lift_map.{us} f))

/-- The actual source-us lifted associative Grothendieck indexing
is equivalent to the original actual coefficient fiber indexing,
with explicit object/morphism conversions and proved natural inverses. -/
def unliftEquivalence : LiftedOrderFiber.{us} ≌ OrderFiber :=
  Equivalence.mk unlift.{us} lift.{us} unitIso.{us} counitIso.{us}

/-- Original ordered finite profiles are the actual source-us
lifted coefficient fibers, through explicit original inverse functors. -/
def orderedEquivalence : LiftedOrderFiber.{us} ≌ OrderedProfile :=
  unliftEquivalence.trans OrderFiber.orderedEquivalence

/-- The actual original lifted coefficient/profile quotient has
the original discrete nonnegative word lengths, including degree zero. -/
def wordLengthEquivalence : LiftedOrderFiber.{us} ≌ Discrete ℕ :=
  unliftEquivalence.trans OrderFiber.wordLengthEquivalence

/-- Source-us lifted coefficient/profile indexing is essentially
small at every required source size, by its actual word-length equivalence. -/
instance liftedOrderFiberEssentiallySmall : EssentiallySmall.{usSize} LiftedOrderFiber.{us} :=
  (essentiallySmall_congr wordLengthEquivalence).2 inferInstance

/-- Unlifting retains the exact original profile and input map
under the actual base forgetful functors. -/
theorem unlift_forget : unlift.{us} ⋙ Grothendieck.forget orderCategories =
    Grothendieck.forget liftedOrderCategories.{us} := by
  apply Functor.ext (fun _ => rfl)

/-- Lifting retains the original profile and full original input
map under the actual base forgetful functors. -/
theorem lift_forget : lift.{us} ⋙ Grothendieck.forget liftedOrderCategories.{us} =
    Grothendieck.forget orderCategories := by
  apply Functor.ext (fun _ => rfl)

/-- The inverse coefficient lift uses the exact original order,
wrapped in the source-us coefficient type at the original profile. -/
@[simp]
theorem lift_obj_coefficient (s : OrderFiber) :
    (lift.{us}.obj s).fiber.as = ULift.up s.fiber.as := rfl

/-- The original source-us coefficient is unlifted exactly as
supplied, without changing its actual original input profile. -/
@[simp]
theorem unlift_obj_coefficient (s : LiftedOrderFiber.{us}) :
    (unlift.obj s).fiber.as = s.fiber.as.down := rfl

/-- Every actual original lifted fiber base map is unchanged. -/
@[simp]
theorem unlift_map_base {s t : LiftedOrderFiber.{us}} (f : s ⟶ t) :
    (unlift.map f).base = f.base := rfl

/-- Every actual original unlifted fiber base map is unchanged. -/
@[simp]
theorem lift_map_base {s t : OrderFiber} (f : s ⟶ t) :
    (lift.{us}.map f).base = f.base := rfl





end CategoryTheory.Operad.Tensor.Associative.LiftedOrderFiber
end
end
end source_LiftedAssociativeOrderEquivalence

/- Source proof segment: AssociativeFiberTensor -/
section source_AssociativeFiberTensor
/-!
# Actual original input tensors over associative coefficient fibers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original input tensor over the actual joint source-us
profile/associative-coefficient indexing. All original input maps
are retained by its actual base forgetful functor. -/
def associativeFiberTensor (X : C) : LiftedOrderFiber.{us} ⥤ C :=
  Grothendieck.forget liftedOrderCategories.{us} ⋙
    analyticInputFamily (fun _ : PUnit.{1} => X) ⋙ FiniteTensor.tensor

/-- In one original profile fiber, the input tensor is the
original tensor at each of its actual associative order coefficients. -/
def associativeFiberDiagramIso (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X ≅
      Discrete.functor (fun _ : liftedOrderFunctor.{us}.obj P =>
        (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) :=
  Discrete.natIso (fun _ => Iso.refl _)

/-- The actual original fiber tensor is the original ordered
profile tensor under the explicitly proved coefficient/order equivalence. -/
def associativeFiberOrderedIso (X : C) :
    associativeFiberTensor X ≅
      LiftedOrderFiber.orderedEquivalence.{us}.functor ⋙ orderedTensorDiagram X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro s t f
    have hb :
        OrderedProfile.forget.map
            (OrderFiber.toOrdered.map (LiftedOrderFiber.unlift.map f)) = f.base :=
      ColoredProfile.Hom.ext rfl
    have hm := congrArg (fun g => (FiniteTensor.tensor (V := C)).map
      ((analyticInputFamily (fun _ : PUnit.{1} => X)).map g)) hb
    exact (Category.comp_id _).trans (hm.symm.trans (Category.id_comp _).symm))

variable [HasColimitsOfSize.{us, us} C]

/-- The actual discrete coefficient shape has the source-us
colimits, derived from its original lifted coefficient type. -/
instance associativeCoefficientDiscreteColimits (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    HasColimitsOfShape (Discrete (liftedOrderFunctor.{us}.obj P)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (liftedOrderFunctor.{us}.obj P))

/-- The actual original coefficient fiber has the source small
colimits, through its concrete discrete lifted-order category. -/
instance associativeCoefficientFiberColimits (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    HasColimitsOfShape (liftedOrderCategories.{us}.obj P) C :=
  inferInstanceAs (HasColimitsOfShape (Discrete (ULift.{us} (LinearOrder P.inputs))) C)

/-- The original joint profile/coefficient shape has the source
small colimits, by its proved actual original word-length equivalence. -/
instance associativeLiftedFiberColimits : HasColimitsOfShape LiftedOrderFiber.{us} C :=
  HasColimitsOfShape.of_essentiallySmall C LiftedOrderFiber.{us}

omit [FiniteTensor C] in
/-- Discrete nonnegative word lengths have the required source
small colimits. This is a concrete source-size derivation. -/
theorem associativeWordLengthColimits : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)

local instance : HasColimitsOfShape (Discrete ℕ) C := associativeWordLengthColimits (C := C)

/-- The actual coefficient-copy cocone on the original fiber
tensor diagram, with every original coefficient injection retained. -/
def associativeFiberCopyCocone (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    Cocone (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X) where
  pt := ∐ (fun _ : liftedOrderFunctor.{us}.obj P =>
    (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P))
  ι := (associativeFiberDiagramIso X P).hom ≫
    Discrete.natTrans (fun o => Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj P =>
      (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) o.as)

/-- The original fiber coefficient-copy cocone is colimiting,
from its actual discrete source coproduct and actual diagram comparison. -/
def associativeFiberCopyIsColimit (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    IsColimit (associativeFiberCopyCocone X P) := by
  with_unfolding_all
    exact (IsColimit.precomposeHomEquiv (associativeFiberDiagramIso X P) _).symm
      (coproductIsCoproduct (fun _ : liftedOrderFunctor.{us}.obj P =>
        (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)))

/-- The actual original order fiber tensor colimit is the
coproduct of the unchanged original finite input tensor over its
source-us lifted associative coefficient orders. -/
def associativeFiberColimitIso (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    colimit (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X) ≅
      ∐ (fun _ : liftedOrderFunctor.{us}.obj P =>
        (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) := by
  with_unfolding_all
    exact (colimit.isColimit
      (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X)).coconePointUniqueUpToIso
        (associativeFiberCopyIsColimit X P)

/-- Each original associative order coefficient injection in its
actual fiber colimit is the original input tensor's corresponding copy. -/
@[reassoc]
theorem associativeFiberColimitIso_ι (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : liftedOrderFunctor.{us}.obj P) :
    colimit.ι (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X) (Discrete.mk o) ≫
      (associativeFiberColimitIso X P).hom =
    Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj P =>
      (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) o := by
  with_unfolding_all
    exact ((colimit.isColimit
        (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X)).fac
          (associativeFiberCopyCocone X P) (Discrete.mk o)).trans (Category.id_comp _)

/-- The actual original profile map moves the original coefficient
fiber injection by the original lifted associative permutation and
actual finite tensor input map. This is the original Grothendieck
cocone naturality, applied to its original profile transport morphism. -/
@[reassoc]
theorem associativeFiberι_map (X : C) {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q)
    (o : liftedOrderFunctor.{us}.obj P) :
    colimit.ι (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X) (Discrete.mk o) ≫
        (fiberwiseColimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)).map f =
      (FiniteTensor.tensor (V := C)).map ((analyticInputFamily (fun _ : PUnit.{1} => X)).map f) ≫
        colimit.ι (Grothendieck.ι liftedOrderCategories.{us} Q ⋙ associativeFiberTensor X)
          (Discrete.mk ((liftedOrderFunctor.{us}.map f) o)) :=
  ((natTransIntoForgetCompFiberwiseColimit
      (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)).naturality
        ((Grothendieck.ιNatTrans (F := liftedOrderCategories.{us}) f).app (Discrete.mk o))).symm

/-- The original joint profile/coefficient tensor colimit is
the actual all-length finite tensor coproduct, by the proved
ordered-profile equivalence and original colimit invariance. -/
def associativeFiberColimitWordIso (X : C) :
    colimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) ≅ colimit (wordLengthTensorDiagram X) :=
  HasColimit.isoOfNatIso (associativeFiberOrderedIso X) ≪≫
    Functor.Final.colimitIso LiftedOrderFiber.orderedEquivalence.functor (orderedTensorDiagram X) ≪≫
    orderedTensorColimitLengthIso X






end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeFiberTensor

/- Source proof segment: AssociativeFiberCopowerFunctor -/
section source_AssociativeFiberCopowerFunctor
/-!
# Actual fiberwise tensor colimits are the original tensor copower functor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

private theorem fiberTensorCopowerSquare {V : Type*} [Category* V]
    {A B X Y TX TY : V} (i : A ⟶ X) (j : B ⟶ Y) (f : X ⟶ Y) (t : A ⟶ B)
    (c : X ⟶ TX) (d : Y ⟶ TY) (p : A ⟶ TX) (q : B ⟶ TY) (g : TX ⟶ TY)
    (hn : i ≫ f = t ≫ j) (hc : i ≫ c = p) (hd : j ≫ d = q) (hg : p ≫ g = t ≫ q) :
    i ≫ (f ≫ d) = i ≫ (c ≫ g) := by
  rw [← Category.assoc i f, hn, Category.assoc t j, hd,
    ← Category.assoc i c, hc, hg]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]

/-- The actual original order fiber colimit identification is
natural under all original profile/input/coefficient relabelings. -/
theorem associativeFiberColimitIso_naturality (X : C)
    {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q) :
    (fiberwiseColimit (associativeFiberTensor X)).map f ≫ (associativeFiberColimitIso X Q).hom =
      (associativeFiberColimitIso X P).hom ≫ (associativeTensorCoproductFunctor X).map f := by
  apply (colimit.isColimit
    (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X)).hom_ext
  rintro ⟨o⟩
  exact fiberTensorCopowerSquare _ _ _ _ _ _ _ _ _
    (associativeFiberι_map X f o) (associativeFiberColimitIso_ι X P o)
    (associativeFiberColimitIso_ι X Q ((liftedOrderFunctor.map f) o))
    (Sigma.ι_comp_map'
      (g := fun _ : liftedOrderFunctor.{us}.obj P => (associativeInputTensor X).obj P)
      (f := fun _ : liftedOrderFunctor.{us}.obj Q => (associativeInputTensor X).obj Q)
      (liftedOrderFunctor.map f) (fun _ => (associativeInputTensor X).map f) o)

/-- The actual original fiberwise tensor colimit functor is the
actual tensor coproduct over each original associative order fiber,
with all original input and operation-order maps retained. -/
def associativeFiberCopowerNatIso (X : C) :
    fiberwiseColimit (associativeFiberTensor (C := C) X : LiftedOrderFiber.{us} ⥤ C) ≅
      associativeTensorCoproductFunctor X :=
  NatIso.ofComponents (associativeFiberColimitIso X)
    (fun f => associativeFiberColimitIso_naturality X f)

variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The actual original associative weighted tensor profile
functor is naturally the actual fiberwise input tensor colimit;
its coefficient quotient maps are the original ones. -/
def associativeProfileFiberNatIso (X : C) :
    analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) ≅
      fiberwiseColimit (associativeFiberTensor (C := C) X : LiftedOrderFiber.{us} ⥤ C) :=
  associativeTensorProfileNatIso X ≪≫ (associativeFiberCopowerNatIso X).symm




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeFiberCopowerFunctor

/- Source proof segment: AssociativeProfileWordColimit -/
section source_AssociativeProfileWordColimit
/-!
# Actual associative profile coinvariants are the tensor-word coproduct
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d
local instance : HasColimitsOfShape (Discrete ℕ) C := associativeWordLengthColimits (C := C)

/-- The actual associative profile coinvariant carrier is the
actual colimit over the joint original profile and operation-order
fibers. This uses the proved tensor/copower and fiberwise-colimit
natural identifications and the genuine Grothendieck colimit theorem. -/
def associativeProfileFiberColimitIso (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) PUnit.unit ≅
      colimit (associativeFiberTensor (C := C) X : LiftedOrderFiber.{us} ⥤ C) :=
  HasColimit.isoOfNatIso (associativeProfileFiberNatIso X) ≪≫
    colimitFiberwiseColimitIso (associativeFiberTensor (C := C) X : LiftedOrderFiber.{us} ⥤ C)

/-- Taking the actual associative weighted profile coinvariants
gives the coproduct of all actual finite input tensors, over every
nonnegative word length and with degree zero the empty tensor. -/
def associativeProfileWordColimitIso (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) PUnit.unit ≅
      colimit (wordLengthTensorDiagram X) :=
  associativeProfileFiberColimitIso X ≪≫ associativeFiberColimitWordIso X




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeProfileWordColimit

/- Source proof segment: BinaryTensorWordColimit -/
section source_BinaryTensorWordColimit
/-!
# The original binary finite input tensors have the actual tensor-word coproduct
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original binary symmetric finite tensor at every original
nonnegative word length, including the original tensor unit at zero. -/
def binaryWordLengthTensorDiagram (X : C) : Discrete ℕ ⥤ C :=
  Discrete.functor (fun n => OrderedTensor.finiteTensorFunctor.obj
    (OrderedTensor.constantFinFamily n X))

/-- Every original binary finite input tensor is the existing
tensor power of the original object at its original word length. -/
def binaryWordLengthPowerIso (X : C) :
    binaryWordLengthTensorDiagram X ≅
      Discrete.functor (fun n => TensorPower.tensorPowObj X n) :=
  Discrete.natIso (fun n => eqToIso (OrderedTensor.finiteTensorFunctor_constant_obj n.as X))

variable [HasColimitsOfShape (Discrete ℕ) C]

/-- The actual original binary input tensor colimit is exactly
the existing coproduct of tensor powers, with degree zero the
original tensor unit. No finite tensor or word outcome is a premise. -/
def binaryTensorWordColimitIso (X : C) :
    colimit (binaryWordLengthTensorDiagram X) ≅ TensorWord.tensorWordObj X :=
  HasColimit.isoOfNatIso (binaryWordLengthPowerIso X) ≪≫
    (Sigma.isoColimit (Discrete.functor (fun n => TensorPower.tensorPowObj X n))).symm



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_BinaryTensorWordColimit

/- Source proof segment: AssociativeBinaryTensorWords -/
section source_AssociativeBinaryTensorWords
/-!
# The source associative tensor-operad free carrier is the original tensor-word carrier
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative binary tensor words construction. -/
local instance associativeBinaryTensorWordsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The constructed coherent finite tensor word-length diagram
uses exactly the original binary finite tensor diagram at every length. -/
def sourceWordLengthDiagramIso (X : C) :
    wordLengthTensorDiagram X ≅ binaryWordLengthTensorDiagram X :=
  Discrete.natIso (fun _ => Iso.refl _)

/-- The actual original associative coefficient-weighted profile
coinvariant carrier is the coproduct of the original binary tensor
words over every nonnegative length, including degree zero. -/
def associativeTensorWordsIso (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) PUnit.unit ≅ TensorWord.tensorWordObj X :=
  associativeProfileWordColimitIso X ≪≫
    HasColimit.isoOfNatIso (sourceWordLengthDiagramIso X) ≪≫ binaryTensorWordColimitIso X

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- Degree zero of the source tensor-word diagram is exactly
the original tensor unit, supplied by the actual binary source producer. -/
theorem sourceWordLength_zero (X : C) :
    (wordLengthTensorDiagram X).obj (Discrete.mk 0) = 𝟙_ C :=
  OrderedTensor.finiteTensorFunctor_constant_zero X




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeBinaryTensorWords

/- Source proof segment: AssociativeWordMonoid -/
section source_AssociativeWordMonoid
/-!
# The tensor-word free monoid on the actual associative profile carrier
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative word monoid construction. -/
local instance associativeWordMonoidFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The monoid of actual original tensor words on the constructed
associative profile carrier, through the proved weighted quotient
and original binary word carrier isomorphism. -/
def associativeWordMon (X : C) : Mon C :=
  let : MonObj (profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) PUnit.unit) :=
    MonObj.ofIso (associativeTensorWordsIso X).symm
  Mon.mk (profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
    (fun _ : PUnit.{1} => X) PUnit.unit)

/-- The actual original associative profile carrier is isomorphic
as the transported tensor-word monoid to the original free word monoid. -/
def associativeWordMonIso (X : C) : associativeWordMon X ≅ TensorWord.tensorWordMon X := by
  let e := associativeTensorWordsIso X
  let : MonObj (profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) PUnit.unit) := MonObj.ofIso e.symm
  let : IsMonHom e.inv := CategoryTheory.isMonHom_ofIso e.symm
  exact (Mon.mkIso' e.symm).symm

/-- Its unit is the original degree-zero tensor-unit word copy,
carried back to the actual operation-weighted profile quotient. -/
theorem associativeWordMon_one (X : C) :
    (associativeWordMon X).mon.one = TensorWord.tensorWordOne X ≫
      (associativeTensorWordsIso X).inv := rfl

/-- The universal original monoid map out of the actual associative
profile carrier is the original word extension, through its proved
actual word monoid comparison. Both inverse maps are explicit. -/
def associativeWordHomEquiv (X : C) (M : Mon C) :
    (associativeWordMon X ⟶ M) ≃ (X ⟶ M.X) :=
  ((associativeWordMonIso X).homCongr (Iso.refl M)).trans
    (TensorWord.tensorWordHomEquiv X M).symm




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeWordMonoid

/- Source proof segment: LiftedAssociativeWordLengthReadbacks -/
section source_LiftedAssociativeWordLengthReadbacks
/-!
# Original profile and word-length maps of lifted associative fibers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us

namespace CategoryTheory.Operad.Tensor.Associative.LiftedOrderFiber

open CategoryTheory

/-- The original canonical finite profile and lifted increasing
coefficient at every original word length, including zero. -/
def canonical (n : ℕ) : LiftedOrderFiber.{us} :=
  ⟨(OrderedProfile.canonical n).profile,
    Discrete.mk (ULift.up (OrderedProfile.canonical n).order)⟩

/-- The actual word-length comparison retains the original
cardinal length of the original finite input profile. -/
@[simp]
theorem wordLength_obj (s : LiftedOrderFiber.{us}) :
    wordLengthEquivalence.functor.obj s = Discrete.mk (Nat.card s.base.inputs) := rfl

/-- Every original source profile/input map induces its actual
equality of word lengths through the original input bijection. -/
theorem wordLength_map {s t : LiftedOrderFiber.{us}} (f : s ⟶ t) :
    wordLengthEquivalence.functor.map f = Discrete.eqToHom' (Nat.card_congr f.base.inputEquiv) :=
  Subsingleton.elim _ _

/-- The actual inverse comparison is precisely the original
canonical increasingly ordered profile and its lifted coefficient. -/
@[simp]
theorem wordLength_inverse_obj (n : Discrete ℕ) :
    wordLengthEquivalence.{us}.inverse.obj n = canonical n.as := rfl

/-- Every original canonical coefficient profile has its supplied
word length. In particular the actual nullary profile has length zero. -/
theorem wordLength_canonical (n : ℕ) :
    wordLengthEquivalence.functor.obj (canonical.{us} n) = Discrete.mk n :=
  congrArg Discrete.mk (Nat.card_fin n)

/-- The actual inverse retains precisely the original finite
input profile, including the zero and one input profiles. -/
theorem wordLength_inverse_base (n : Discrete ℕ) :
    (wordLengthEquivalence.{us}.inverse.obj n).base = (OrderedProfile.canonical n.as).profile := rfl

/-- The actual source-us coefficient in the inverse comparison
is the lift of the original canonical increasing input order. -/
theorem wordLength_inverse_coefficient (n : Discrete ℕ) :
    (wordLengthEquivalence.{us}.inverse.obj n).fiber.as =
      ULift.up (OrderedProfile.canonical n.as).order := rfl

/-- The actual original input map of the unlifted natural inverse
is the original identity on that input profile. -/
@[simp]
theorem unitIso_base (s : LiftedOrderFiber.{us}) :
    (unitIso.hom.app s).base = 𝟙 s.base := rfl

/-- The actual original input map of the lifted natural inverse
is the original identity on that input profile. -/
@[simp]
theorem counitIso_base (s : OrderFiber) :
    (counitIso.{us}.hom.app s).base = 𝟙 s.base := rfl




end CategoryTheory.Operad.Tensor.Associative.LiftedOrderFiber
end
end
end source_LiftedAssociativeWordLengthReadbacks

/- Source proof segment: AssociativeFiberTensorReadbacks -/
section source_AssociativeFiberTensorReadbacks
/-!
# Actual coefficient injection and word-colimit maps of fiber tensors
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

private theorem conjugateFiberInjection {V : Type*} [Category* V]
    {TP TQ AP BP AQ BQ : V} (ip : TP ⟶ AP) (iq : TQ ⟶ AQ)
    (ep : AP ≅ BP) (eq : AQ ≅ BQ) (m : AP ⟶ AQ) (t : TP ⟶ TQ)
    (jp : TP ⟶ BP) (jq : TQ ⟶ BQ)
    (hp : ip ≫ ep.hom = jp) (hq : iq ≫ eq.hom = jq) (hn : ip ≫ m = t ≫ iq) :
    jp ≫ (ep.inv ≫ (m ≫ eq.hom)) = t ≫ jq := by
  rw [← hp, Category.assoc ip ep.hom, ep.hom_inv_id_assoc,
    ← Category.assoc ip m, hn, Category.assoc t iq, hq]

private theorem fourColimitInjectionSteps {V : Type*} [Category* V]
    {A B C D E U V' W : V} (i : U ⟶ A)
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E)
    (p : U ⟶ V') (j : V' ⟶ B) (k : V' ⟶ C) (q : V' ⟶ W)
    (l : W ⟶ D) (m : W ⟶ E)
    (h1 : i ≫ a = p ≫ j) (h2 : j ≫ b = k)
    (h3 : k ≫ c = q ≫ l) (h4 : l ≫ d = m) :
    i ≫ (a ≫ (b ≫ (c ≫ d))) = p ≫ (q ≫ m) := by
  rw [← Category.assoc i a, h1, Category.assoc p j,
    ← Category.assoc j b, h2, ← Category.assoc k c, h3,
    Category.assoc q l, h4]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original joint tensor maps each actual profile transport
by exactly its original finite tensor input map. -/
theorem associativeFiberTensor_map (X : C) {s t : LiftedOrderFiber.{us}} (f : s ⟶ t) :
    (associativeFiberTensor X).map f =
      (FiniteTensor.tensor (V := C)).map ((analyticInputFamily (fun _ : PUnit.{1} => X)).map f.base) := rfl

/-- The actual ordered comparison retains the same original input
tensor on each original coefficient profile, with identity tensor map. -/
@[simp]
theorem associativeFiberOrderedIso_hom_app (X : C) (s : LiftedOrderFiber.{us}) :
    (associativeFiberOrderedIso X).hom.app s =
      𝟙 ((FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj s.base)) := rfl

variable [HasColimitsOfSize.{us, us} C]

local instance : HasColimitsOfShape (Discrete ℕ) C := associativeWordLengthColimits (C := C)

/-- Under the actual original coefficient-copy colimit comparison,
every original profile map moves its original coefficient injection
by the original tensor input map and lifted coefficient permutation. -/
@[reassoc]
theorem associativeFiberSigmaι_map (X : C) {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q)
    (o : liftedOrderFunctor.{us}.obj P) :
    Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj P =>
        (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) o ≫
      (associativeFiberColimitIso X P).inv ≫
      (fiberwiseColimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)).map f ≫
      (associativeFiberColimitIso X Q).hom =
    (FiniteTensor.tensor (V := C)).map ((analyticInputFamily (fun _ : PUnit.{1} => X)).map f) ≫
      Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj Q =>
        (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj Q))
        ((liftedOrderFunctor.{us}.map f) o) :=
  conjugateFiberInjection
    (colimit.ι (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X) (Discrete.mk o))
    (colimit.ι (Grothendieck.ι liftedOrderCategories.{us} Q ⋙ associativeFiberTensor X)
      (Discrete.mk ((liftedOrderFunctor.{us}.map f) o)))
    (associativeFiberColimitIso X P) (associativeFiberColimitIso X Q)
    ((fiberwiseColimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)).map f)
    ((FiniteTensor.tensor (V := C)).map ((analyticInputFamily (fun _ : PUnit.{1} => X)).map f))
    (Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj P =>
      (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) o)
    (Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj Q =>
      (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj Q))
      ((liftedOrderFunctor.{us}.map f) o))
    (associativeFiberColimitIso_ι X P o)
    (associativeFiberColimitIso_ι X Q ((liftedOrderFunctor.{us}.map f) o))
    (associativeFiberι_map X f o)

/-- Every original joint coefficient/profile tensor injection is
sent to its original increasingly enumerated finite word tensor and
that word's actual colimit injection. -/
@[reassoc]
theorem associativeFiberColimitWordIso_ι (X : C) (s : LiftedOrderFiber.{us}) :
    colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) s ≫
        (associativeFiberColimitWordIso X).hom =
      (associativeFiberOrderedIso X).hom.app s ≫
        (orderedTensorLengthIso X).hom.app (LiftedOrderFiber.orderedEquivalence.functor.obj s) ≫
        colimit.ι (wordLengthTensorDiagram X)
          (OrderedProfile.countFunctor.obj (LiftedOrderFiber.orderedEquivalence.functor.obj s)) := by
  let η := associativeFiberOrderedIso X
  let F := LiftedOrderFiber.orderedEquivalence.{us}.functor
  let ε := orderedTensorLengthIso X
  let D := orderedTensorDiagram X
  let W := wordLengthTensorDiagram X
  let H := OrderedProfile.countFunctor
  have h := fourColimitInjectionSteps
    (colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) s)
    (HasColimit.isoOfNatIso η).hom (Functor.Final.colimitIso F D).hom
    (HasColimit.isoOfNatIso ε).hom (Functor.Final.colimitIso H W).hom
    (η.hom.app s) (colimit.ι (F ⋙ D) s) (colimit.ι D (F.obj s))
    (ε.hom.app (F.obj s)) (colimit.ι (H ⋙ W) (F.obj s)) (colimit.ι W (H.obj (F.obj s)))
    (HasColimit.ι_isoOfNatIso_hom η s) (Functor.Final.ι_colimitIso_hom F D s)
    (HasColimit.ι_isoOfNatIso_hom ε (F.obj s)) (Functor.Final.ι_colimitIso_hom H W (F.obj s))
  simpa only [associativeFiberColimitWordIso, orderedTensorColimitLengthIso,
    Iso.trans_hom, Category.assoc] using h




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeFiberTensorReadbacks

/- Source proof segment: AssociativeProfileWordInjections -/
section source_AssociativeProfileWordInjections
/-!
# Original operation-copy injections in the actual associative tensor-word quotient
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

private theorem associateFour {V : Type*} [Category* V] {A B C D E : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) :
    ((a ≫ b) ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

private theorem profileJointCopyFromSquares {V : Type*} [Category* V]
    {U L S A F B K J : V} (i : U ⟶ S) (p : S ⟶ A) (a : S ⟶ B)
    (e : F ≅ B) (k : F ⟶ K) (c : K ⟶ J) (t : A ⟶ J)
    (j : L ⟶ J) (u : U ⟶ L) (l : L ⟶ F)
    (hp : p ≫ t = a ≫ e.inv ≫ k ≫ c) (hi : i ≫ a = u ≫ l ≫ e.hom)
    (hj : l ≫ k ≫ c = j) : i ≫ p ≫ t = u ≫ j := by
  rw [hp, ← Category.assoc i a, hi]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hj]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d
local instance : HasColimitsOfShape (Discrete ℕ) C := associativeWordLengthColimits (C := C)

/-- Each original associative operation coefficient tensor copy
passes through the actual profile quotient to its original joint
profile/order tensor colimit injection. -/
theorem associativeProfileFiberColimitIso_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection X P o ≫
        profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (fun _ : PUnit.{1} => X) P ≫ (associativeProfileFiberColimitIso X).hom =
      (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫
        colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) ⟨P, Discrete.mk o⟩ := by
  let e := associativeProfileFiberNatIso X
  let c := associativeFiberColimitIso X P
  let J := colimitFiberwiseColimitIso (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)
  have hp := HasColimit.ι_isoOfNatIso_hom e P
  have hcopy := associativeProfileCoefficientInjection_β X P o
  have hc := associativeFiberColimitIso_ι X P o
  have hj := ι_colimitFiberwiseColimitIso_hom
    (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) P (Discrete.mk o)
  have he : e.hom.app P = (associativeProfileTensorIso X P).hom ≫ c.inv := rfl
  have hp' :
      profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (fun _ : PUnit.{1} => X) P ≫ (associativeProfileFiberColimitIso X).hom =
        (associativeProfileTensorIso X P).hom ≫ c.inv ≫
          colimit.ι (fiberwiseColimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)) P ≫ J.hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ J.hom) hp).trans
        ((congrArg (fun x => (x ≫
          colimit.ι (fiberwiseColimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)) P) ≫
          J.hom) he).trans
            (associateFour (associativeProfileTensorIso X P).hom c.inv
              (colimit.ι (fiberwiseColimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)) P)
              J.hom)))
  have hcopy' :
      associativeProfileCoefficientInjection X P o ≫ (associativeProfileTensorIso X P).hom =
        (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫
          colimit.ι (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X)
            (Discrete.mk o) ≫ c.hom :=
    hcopy.trans (congrArg ((unitCoefficientTensorIso
      ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫ ·) hc.symm)
  exact profileJointCopyFromSquares
    (associativeProfileCoefficientInjection X P o)
    (profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P)
    (associativeProfileTensorIso X P).hom c
    (colimit.ι (fiberwiseColimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C)) P)
    J.hom (associativeProfileFiberColimitIso X).hom
    (colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) ⟨P, Discrete.mk o⟩)
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom
    (colimit.ι (Grothendieck.ι liftedOrderCategories.{us} P ⋙ associativeFiberTensor X) (Discrete.mk o))
    hp' hcopy' hj

/-- Every actual original associative operation copy descends
through the original weighted profile quotient to its original
increasingly ordered finite tensor-word injection. -/
theorem associativeProfileWordColimitIso_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection X P o ≫
        profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (fun _ : PUnit.{1} => X) P ≫ (associativeProfileWordColimitIso X).hom =
      (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫
        (associativeFiberOrderedIso X).hom.app ⟨P, Discrete.mk o⟩ ≫
        (orderedTensorLengthIso X).hom.app
          (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩) ≫
        colimit.ι (wordLengthTensorDiagram X)
          (OrderedProfile.countFunctor.obj
            (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩)) := by
  let j := colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) ⟨P, Discrete.mk o⟩
  let p := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom
  let a := (associativeProfileFiberColimitIso X).hom
  let b := (associativeFiberColimitWordIso X).hom
  have h1 := associativeProfileFiberColimitIso_coefficient X P o
  have h2 := associativeFiberColimitWordIso_ι X ⟨P, Discrete.mk o⟩
  let i := associativeProfileCoefficientInjection X P o
  let q := profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
    (fun _ : PUnit.{1} => X) P
  exact (Category.assoc i q (a ≫ b)).symm.trans
    ((Category.assoc (i ≫ q) a b).symm.trans
      ((congrArg (· ≫ b) ((Category.assoc i q a).trans h1)).trans
        ((Category.assoc p j b).trans (congrArg (p ≫ ·) h2))))




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeProfileWordInjections

/- Source proof segment: OriginalMonadAlgebraTransport -/
section source_OriginalMonadAlgebraTransport
/-!
# Actual algebra transport through original carrier isomorphisms
-/

@[expose] public section
set_option autoImplicit false
universe u v

namespace CategoryTheory.Monad.Algebra

open CategoryTheory

private theorem carrierUnitFromOriginalSquare {V : Type*} [Category* V]
    {X Y TX TY : V} (e : X ≅ Y) (uX : X ⟶ TX) (uY : Y ⟶ TY)
    (f : TY ⟶ TX) (a : TX ⟶ X)
    (hn : uY ≫ f = e.inv ≫ uX) (hu : uX ≫ a = 𝟙 X) :
    uY ≫ (f ≫ (a ≫ e.hom)) = 𝟙 Y := by
  rw [← Category.assoc uY f, hn, Category.assoc e.inv uX,
    ← Category.assoc uX a e.hom, hu, Category.id_comp, e.inv_hom_id]

variable {C : Type u} [Category.{v} C] {T : Monad C}

/-- Transport a supplied actual monad algebra along an actual
carrier isomorphism. Both algebra laws follow from the original
laws and the actual unit/multiplication naturality. -/
def transportAlongIso (A : Algebra T) {Y : C} (e : A.A ≅ Y) : Algebra T where
  A := Y
  a := T.map e.inv ≫ A.a ≫ e.hom
  unit := by
    have hn : T.η.app Y ≫ T.map e.inv = e.inv ≫ T.η.app A.A := by
      simpa only [Functor.id_map] using (T.η.naturality e.inv).symm
    exact carrierUnitFromOriginalSquare e (T.η.app A.A) (T.η.app Y) (T.map e.inv) A.a hn A.unit
  assoc := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (T.μ.app Y) (T.map e.inv) (A.a ≫ e.hom),
      ← T.μ.naturality e.inv]
    change (T.map (T.map e.inv) ≫ T.μ.app A.A) ≫ (A.a ≫ e.hom) = _
    rw [Category.assoc, ← Category.assoc (T.μ.app A.A) A.a e.hom, A.assoc, Category.assoc]
    have hmap : T.map e.hom ≫ T.map e.inv = 𝟙 (T.obj A.A) :=
      (T.map_comp _ _).symm.trans
        ((congrArg T.map e.hom_inv_id).trans (T.map_id _))
    rw [← Category.assoc (T.map e.hom) (T.map e.inv) (A.a ≫ e.hom), hmap, Category.id_comp]

/-- The actual carrier isomorphism preserves the transported
action, and its inverse is the original inverse carrier map. -/
def transportAlongIsoIso (A : Algebra T) {Y : C} (e : A.A ≅ Y) :
    A ≅ transportAlongIso A e :=
  isoMk e (by
    change T.map e.hom ≫ (T.map e.inv ≫ (A.a ≫ e.hom)) = A.a ≫ e.hom
    rw [← Category.assoc, ← T.map_comp, e.hom_inv_id, T.map_id, Category.id_comp])

@[simp]
theorem transportAlongIso_a (A : Algebra T) {Y : C} (e : A.A ≅ Y) :
    (transportAlongIso A e).a = T.map e.inv ≫ A.a ≫ e.hom := rfl

@[simp]
theorem transportAlongIsoIso_hom_f (A : Algebra T) {Y : C} (e : A.A ≅ Y) :
    (transportAlongIsoIso A e).hom.f = e.hom := rfl

@[simp]
theorem transportAlongIsoIso_inv_f (A : Algebra T) {Y : C} (e : A.A ≅ Y) :
    (transportAlongIsoIso A e).inv.f = e.inv := rfl




end CategoryTheory.Monad.Algebra
end
end source_OriginalMonadAlgebraTransport

/- Source proof segment: ChosenCanonicalOrderedProfiles -/
section source_ChosenCanonicalOrderedProfiles
/-!
# Original canonical profiles ordered by the actual source enumeration

The underlying canonical finite profile is unchanged. Its selected
operation order is the pullback of the increasing order along the
ACTUAL source Fintype.equivFin map. No increasing-identity assertion
about that chosen finite enumeration is made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative.OrderedProfile

open CategoryTheory

/-- The exact source finite enumeration used by the produced
finite tensor on the original canonical Fin n input type. -/
def chosenRank (n : ℕ) : Fin n ≃ Fin (@Fintype.card (Fin n)
    (@FintypeCat.fintype (FintypeCat.of (Fin n)))) :=
  @Fintype.equivFin (Fin n) (@FintypeCat.fintype (FintypeCat.of (Fin n)))

/-- The original canonical finite profile, with the operation
order dictated by the actual source finite input enumeration. -/
def chosenCanonical (n : ℕ) : OrderedProfile where
  profile := (canonical n).profile
  order := by
    letI : DecidableEq (Fin n) := (chosenRank n).decidableEq
    exact (chosenRank n).linearOrder

/-- The actual source chosen canonical profile retains its
original supplied word length, including length zero. -/
@[simp]
theorem count_chosenCanonical (n : ℕ) : count (chosenCanonical n) = n := Nat.card_fin n

/-- The actual source chosen canonical profiles at every
nonnegative word length, with their exact source operation orders. -/
def chosenCanonicalFunctor : Discrete ℕ ⥤ OrderedProfile := Discrete.functor chosenCanonical

/-- Increasingly identify every original operation order with
the source chosen canonical order at its actual word length. -/
def chosenCanonicalIso (P : OrderedProfile) : P ≅ chosenCanonical (count P) where
  hom := homOfCountEq P (chosenCanonical (count P)) (count_chosenCanonical (count P)).symm
  inv := homOfCountEq (chosenCanonical (count P)) P (count_chosenCanonical (count P))
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The actual increasing source maps to chosen canonical
profiles are natural under every original increasing input bijection. -/
def chosenCanonicalUnitIso : 𝟭 OrderedProfile ≅ countFunctor ⋙ chosenCanonicalFunctor :=
  NatIso.ofComponents chosenCanonicalIso (fun _ => Subsingleton.elim _ _)

/-- The source chosen operation-order comparison on the original
canonical Fin n profile. Its input map is retained explicitly. -/
def canonicalToChosenIso (n : ℕ) : canonical n ≅ chosenCanonical n where
  hom := homOfCountEq (canonical n) (chosenCanonical n)
    ((count_canonical n).trans (count_chosenCanonical n).symm)
  inv := homOfCountEq (chosenCanonical n) (canonical n)
    ((count_chosenCanonical n).trans (count_canonical n).symm)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Original output canonical profiles remain literally the
same finite input profiles; only their actual operation order is tracked. -/
@[simp]
theorem chosenCanonical_profile (n : ℕ) : (chosenCanonical n).profile = (canonical n).profile := rfl




end CategoryTheory.Operad.Tensor.Associative.OrderedProfile
end
end
end source_ChosenCanonicalOrderedProfiles

/- Source proof segment: AssociativeBinaryWordInjections -/
section source_AssociativeBinaryWordInjections
/-!
# Original associative operation copies and binary tensor-word injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem wordInjectionThreeSteps {V : Type*} [Category* V]
    {A B C D U V' W : V} (i : U ⟶ A) (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (p : U ⟶ V') (j : V' ⟶ B) (q : V' ⟶ W) (k : W ⟶ C) (l : W ⟶ D)
    (h1 : i ≫ a = p ≫ j) (h2 : j ≫ b = q ≫ k) (h3 : k ≫ c = l) :
    i ≫ (a ≫ (b ≫ c)) = (p ≫ q) ≫ l := by
  rw [← Category.assoc i a, h1, Category.assoc p j,
    ← Category.assoc j b, h2, Category.assoc q k, h3, Category.assoc]

private theorem postCopyWordInjection {V : Type*} [Category* V]
    {D A B C L P : V} (i : D ⟶ A) (q : A ⟶ B) (a : B ⟶ C) (b : C ⟶ P)
    (u : D ⟶ L) (j : L ⟶ C) (k : L ⟶ P)
    (h1 : i ≫ (q ≫ a) = u ≫ j) (h2 : j ≫ b = k) :
    i ≫ (q ≫ (a ≫ b)) = u ≫ k := by
  rw [← Category.assoc q a b, ← Category.assoc i (q ≫ a) b, h1, Category.assoc u j, h2]

private theorem removeWordIdentity {V : Type*} [Category* V]
    {D L Q : V} (p : D ⟶ L) (i : L ⟶ L) (j : L ⟶ Q) (h : i = 𝟙 L) :
    p ≫ (i ≫ j) = p ≫ j := by
  rw [h, Category.id_comp]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative binary word injections construction. -/
local instance associativeBinaryWordInjectionsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual produced word-length tensor is the original binary
tensor power at every original nonnegative word length. -/
def associativeWordPowerIso (X : C) : wordLengthTensorDiagram X ≅
    Discrete.functor (fun n => TensorPower.tensorPowObj X n) :=
  sourceWordLengthDiagramIso X ≪≫ binaryWordLengthPowerIso X

omit [MonoidalClosed C] in
/-- Original word-length colimit injections become precisely
the original binary tensor-power word injections under the actual
source comparison, with all source power maps retained. -/
theorem associativeWordColimitPowerIso_ι (X : C) (n : Discrete ℕ) :
    colimit.ι (wordLengthTensorDiagram X) n ≫
        (HasColimit.isoOfNatIso (sourceWordLengthDiagramIso X) ≪≫ binaryTensorWordColimitIso X).hom =
      (associativeWordPowerIso X).hom.app n ≫ TensorWord.tensorWordι X n.as := by
  let η := sourceWordLengthDiagramIso X
  let ρ := binaryWordLengthPowerIso X
  let D := Discrete.functor (fun n => TensorPower.tensorPowObj X n)
  let c : colimit D ≅ TensorWord.tensorWordObj X := (Sigma.isoColimit D).symm
  have h3 : colimit.ι D n ≫ c.hom = TensorWord.tensorWordι X n.as := Sigma.ι_isoColimit_inv D n.as
  have h := wordInjectionThreeSteps (colimit.ι (wordLengthTensorDiagram X) n)
    (HasColimit.isoOfNatIso η).hom (HasColimit.isoOfNatIso ρ).hom c.hom
    (η.hom.app n) (colimit.ι (binaryWordLengthTensorDiagram X) n)
    (ρ.hom.app n) (colimit.ι D n) (TensorWord.tensorWordι X n.as)
    (HasColimit.ι_isoOfNatIso_hom η n) (HasColimit.ι_isoOfNatIso_hom ρ n)
    h3
  with_unfolding_all
    simpa only [η, ρ, D, c, binaryTensorWordColimitIso, associativeWordPowerIso, Iso.trans_hom,
      NatTrans.comp_app, Category.assoc] using h

/-- Increasingly enumerate the original operation order and use
the actual source tensor/power comparison. This retains every
original finite profile and its selected original lifted order. -/
def associativeOrderedPowerIso (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : liftedOrderFunctor.{us}.obj P) :
    (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P) ≅
      TensorPower.tensorPowObj X (Nat.card P.inputs) :=
  (orderedTensorLengthIso X).app (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩) ≪≫
    (associativeWordPowerIso X).app
      (OrderedProfile.countFunctor.obj (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩))

/-- Every original associative operation coefficient copy in the
ACTUAL weighted quotient becomes its original increasingly ordered
binary tensor-power word injection, including degree zero. -/
theorem associativeTensorWordsIso_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection X P o ≫
        profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (fun _ : PUnit.{1} => X) P ≫ (associativeTensorWordsIso X).hom =
      (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫
        (associativeOrderedPowerIso X P o).hom ≫ TensorWord.tensorWordι X (Nat.card P.inputs) := by
  let u := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom
  let J := LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩
  let n := OrderedProfile.countFunctor.obj J
  let j := (orderedTensorLengthIso X).hom.app J ≫ colimit.ι (wordLengthTensorDiagram X) n
  let b := (HasColimit.isoOfNatIso (sourceWordLengthDiagramIso X) ≪≫ binaryTensorWordColimitIso X).hom
  let k := (associativeOrderedPowerIso X P o).hom ≫ TensorWord.tensorWordι X (Nat.card P.inputs)
  have h1 : associativeProfileCoefficientInjection X P o ≫
      profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) P ≫ (associativeProfileWordColimitIso X).hom = u ≫ j :=
    (associativeProfileWordColimitIso_coefficient X P o).trans
      (removeWordIdentity u ((associativeFiberOrderedIso X).hom.app ⟨P, Discrete.mk o⟩) j rfl)
  have h2 : j ≫ b = k :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => (orderedTensorLengthIso X).hom.app J ≫ q)
        (associativeWordColimitPowerIso_ι X n)).trans (Category.assoc _ _ _).symm)
  exact postCopyWordInjection
    (associativeProfileCoefficientInjection X P o)
    (profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P)
    (associativeProfileWordColimitIso X).hom b u j k h1 h2



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeBinaryWordInjections

/- Source proof segment: ChosenOrderedTensorWords -/
section source_ChosenOrderedTensorWords
/-!
# Actual tensor-word comparisons with the source canonical strand order
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen ordered tensor words construction. -/
local instance chosenOrderedTensorWordsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original source chosen canonical finite profile has its
actual original finite tensor at each supplied nonnegative length. -/
def chosenCanonicalTensorIso (X : C) :
    OrderedProfile.chosenCanonicalFunctor ⋙ orderedTensorDiagram X ≅ wordLengthTensorDiagram X :=
  Discrete.natIso (fun _ => Iso.refl _)

/-- Increasingly enumerate each original operation order into
the ACTUAL source chosen canonical strand order; all original input
bijections and finite tensor maps are retained. -/
def chosenOrderedTensorLengthIso (X : C) :
    orderedTensorDiagram X ≅ OrderedProfile.countFunctor ⋙ wordLengthTensorDiagram X :=
  (Functor.leftUnitor (orderedTensorDiagram X)).symm ≪≫
    Functor.isoWhiskerRight OrderedProfile.chosenCanonicalUnitIso (orderedTensorDiagram X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft OrderedProfile.countFunctor (chosenCanonicalTensorIso X)

/-- The proved natural adjustment of the old increasing
canonical comparison to the ACTUAL source chosen strand comparison. -/
def orderedTensorStrandAdjustment (X : C) :
    OrderedProfile.countFunctor ⋙ wordLengthTensorDiagram X ≅
      OrderedProfile.countFunctor ⋙ wordLengthTensorDiagram X :=
  (orderedTensorLengthIso X).symm ≪≫ chosenOrderedTensorLengthIso X

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- Adjusting the original tensor comparison uses exactly the
proved natural source strand isomorphism, with no identity-enumeration premise. -/
theorem orderedTensorStrandAdjustment_comp (X : C) :
    orderedTensorLengthIso X ≪≫ orderedTensorStrandAdjustment X = chosenOrderedTensorLengthIso X := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  exact (orderedTensorLengthIso X).hom_inv_id_app_assoc P _

/-- The actual ordered tensor colimit maps to original word
lengths using the corrected source chosen canonical strand maps. -/
def chosenOrderedTensorColimitLengthIso (X : C) :
    colimit (orderedTensorDiagram X) ≅ colimit (wordLengthTensorDiagram X) :=
  HasColimit.isoOfNatIso (chosenOrderedTensorLengthIso X) ≪≫
    Functor.Final.colimitIso OrderedProfile.countFunctor (wordLengthTensorDiagram X)

/-- The actual original coefficient/profile joint tensor colimit
maps to word lengths with the original chosen source strand permutation. -/
def chosenAssociativeFiberColimitWordIso (X : C) :
    colimit (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) ≅ colimit (wordLengthTensorDiagram X) :=
  HasColimit.isoOfNatIso (associativeFiberOrderedIso X) ≪≫
    Functor.Final.colimitIso LiftedOrderFiber.orderedEquivalence.functor (orderedTensorDiagram X) ≪≫
    chosenOrderedTensorColimitLengthIso X

/-- The actual weighted associative quotient keeps the original
profile/coefficient maps and uses its PROVED source strand-adjusted
joint tensor/word comparison. -/
def chosenAssociativeProfileWordIso (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) PUnit.unit ≅ colimit (wordLengthTensorDiagram X) :=
  associativeProfileFiberColimitIso X ≪≫ chosenAssociativeFiberColimitWordIso X

/-- The actual original associative quotient is the original
binary word carrier through its exact source canonical strand correction. -/
def chosenAssociativeTensorWordsIso (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) PUnit.unit ≅ TensorWord.tensorWordObj X :=
  chosenAssociativeProfileWordIso X ≪≫
    HasColimit.isoOfNatIso (sourceWordLengthDiagramIso X) ≪≫ binaryTensorWordColimitIso X

/-- The old valid graded carrier isomorphism and the actual
source chosen carrier differ by this explicit
isomorphism; no old operad or tensor-word map is changed. -/
def associativeWordStrandAdjustment (X : C) : TensorWord.tensorWordObj X ≅ TensorWord.tensorWordObj X :=
  (associativeTensorWordsIso X).symm ≪≫ chosenAssociativeTensorWordsIso X

/-- The actual source chosen word carrier is exactly the old
graded carrier comparison followed by its explicit source strand adjustment. -/
theorem associativeWordStrandAdjustment_comp (X : C) :
    associativeTensorWordsIso X ≪≫ associativeWordStrandAdjustment X = chosenAssociativeTensorWordsIso X := by
  apply Iso.ext
  exact (associativeTensorWordsIso X).hom_inv_id_assoc _





end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenOrderedTensorWords

/- Source proof segment: ChosenAssociativeWordInjections -/
section source_ChosenAssociativeWordInjections
/-!
# Original coefficient-copy injections under the source strand-adjusted word maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem twoColimitInjectionSteps {V : Type*} [Category* V]
    {A B C U W : V} (i : U ⟶ A) (a : A ⟶ B) (b : B ⟶ C)
    (p : U ⟶ W) (j : W ⟶ B) (k : W ⟶ C)
    (h1 : i ≫ a = p ≫ j) (h2 : j ≫ b = k) : i ≫ (a ≫ b) = p ≫ k := by
  rw [← Category.assoc i a, h1, Category.assoc p j, h2]

private theorem removeChosenIdentity {V : Type*} [Category* V]
    {U W C : V} (p : U ⟶ W) (i : W ⟶ W) (j : W ⟶ C) (hi : i = 𝟙 W) :
    p ≫ (i ≫ j) = p ≫ j := by
  rw [hi, Category.id_comp]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen associative word injections construction. -/
local instance chosenAssociativeWordInjectionsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

omit [MonoidalClosed C] in
/-- Every original ordered tensor colimit injection uses the
actual chosen canonical input order and original finite tensor map. -/
theorem chosenOrderedTensorColimitLengthIso_ι (X : C) (P : OrderedProfile) :
    colimit.ι (orderedTensorDiagram X) P ≫ (chosenOrderedTensorColimitLengthIso X).hom =
      (chosenOrderedTensorLengthIso X).hom.app P ≫
        colimit.ι (wordLengthTensorDiagram X) (OrderedProfile.countFunctor.obj P) := by
  let e := chosenOrderedTensorLengthIso X
  let F := OrderedProfile.countFunctor
  let D := wordLengthTensorDiagram X
  exact twoColimitInjectionSteps (colimit.ι (orderedTensorDiagram X) P)
    (HasColimit.isoOfNatIso e).hom (Functor.Final.colimitIso F D).hom
    (e.hom.app P) (colimit.ι (F ⋙ D) P) (colimit.ι D (F.obj P))
    (HasColimit.ι_isoOfNatIso_hom e P) (Functor.Final.ι_colimitIso_hom F D P)

omit [MonoidalClosed C] in
/-- Each original joint coefficient/profile input tensor uses
its actual original profile and the exact chosen canonical strand map. -/
theorem chosenAssociativeFiberColimitWordIso_ι (X : C) (s : LiftedOrderFiber.{us}) :
    colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) s ≫
        (chosenAssociativeFiberColimitWordIso X).hom =
      (chosenOrderedTensorLengthIso X).hom.app (LiftedOrderFiber.orderedEquivalence.functor.obj s) ≫
        colimit.ι (wordLengthTensorDiagram X)
          (OrderedProfile.countFunctor.obj (LiftedOrderFiber.orderedEquivalence.functor.obj s)) := by
  let e := associativeFiberOrderedIso X
  let F := LiftedOrderFiber.orderedEquivalence.{us}.functor
  let D := orderedTensorDiagram X
  let p := e.hom.app s
  let k := colimit.ι D (F.obj s)
  have h1 : colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) s ≫
      ((HasColimit.isoOfNatIso e).hom ≫ (Functor.Final.colimitIso F D).hom) = p ≫ k :=
    twoColimitInjectionSteps (colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) s)
      (HasColimit.isoOfNatIso e).hom (Functor.Final.colimitIso F D).hom
      p (colimit.ι (F ⋙ D) s) k
      (HasColimit.ι_isoOfNatIso_hom e s) (Functor.Final.ι_colimitIso_hom F D s)
  have h2 := chosenOrderedTensorColimitLengthIso_ι X (F.obj s)
  have h := twoColimitInjectionSteps
    (colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) s)
    ((HasColimit.isoOfNatIso e).hom ≫ (Functor.Final.colimitIso F D).hom)
    (chosenOrderedTensorColimitLengthIso X).hom p k
    ((chosenOrderedTensorLengthIso X).hom.app (F.obj s) ≫
      colimit.ι (wordLengthTensorDiagram X) (OrderedProfile.countFunctor.obj (F.obj s))) h1 h2
  have hp : p = 𝟙 _ := rfl
  have h' := h.trans ((congrArg (fun q => q ≫
      ((chosenOrderedTensorLengthIso X).hom.app (F.obj s) ≫
        colimit.ι (wordLengthTensorDiagram X) (OrderedProfile.countFunctor.obj (F.obj s)))) hp).trans
          (Category.id_comp _))
  simpa only [chosenAssociativeFiberColimitWordIso, Iso.trans_hom, Category.assoc, Category.id_comp] using h'

/-- Every original associative coefficient copy reaches the
actual source strand-corrected increasing total word injection,
with every original input profile and order retained. -/
theorem chosenAssociativeProfileWordIso_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection X P o ≫
        profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P ≫
        (chosenAssociativeProfileWordIso X).hom =
      (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫
        (chosenOrderedTensorLengthIso X).hom.app
          (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩) ≫
        colimit.ι (wordLengthTensorDiagram X)
          (OrderedProfile.countFunctor.obj (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩)) := by
  let i := associativeProfileCoefficientInjection X P o
  let q := profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P
  let u := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom
  let j := colimit.ι (associativeFiberTensor X : LiftedOrderFiber.{us} ⥤ C) ⟨P, Discrete.mk o⟩
  have h := twoColimitInjectionSteps (i ≫ q) (associativeProfileFiberColimitIso X).hom
    (chosenAssociativeFiberColimitWordIso X).hom u j
    ((chosenOrderedTensorLengthIso X).hom.app
        (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩) ≫
      colimit.ι (wordLengthTensorDiagram X)
        (OrderedProfile.countFunctor.obj (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩)))
    ((Category.assoc _ _ _).trans (associativeProfileFiberColimitIso_coefficient X P o))
    (chosenAssociativeFiberColimitWordIso_ι X ⟨P, Discrete.mk o⟩)
  simpa only [chosenAssociativeProfileWordIso, Iso.trans_hom, Category.assoc] using h

/-- The original operation input tensor, increasingly identified
with the source chosen canonical profile, is the original binary
power with all original strand maps retained. -/
def chosenAssociativeOrderedPowerIso (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : liftedOrderFunctor.{us}.obj P) :
    (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P) ≅
      TensorPower.tensorPowObj X (Nat.card P.inputs) :=
  (chosenOrderedTensorLengthIso X).app (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩) ≪≫
    (associativeWordPowerIso X).app
      (OrderedProfile.countFunctor.obj (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩))

/-- Every original coefficient copy in the actual weighted
associative quotient reaches the original binary word injection
through its PROVED chosen canonical strand correction. -/
theorem chosenAssociativeTensorWordsIso_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection X P o ≫
        profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P ≫
        (chosenAssociativeTensorWordsIso X).hom =
      (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom ≫
        (chosenAssociativeOrderedPowerIso X P o).hom ≫ TensorWord.tensorWordι X (Nat.card P.inputs) := by
  let b := (HasColimit.isoOfNatIso (sourceWordLengthDiagramIso X) ≪≫ binaryTensorWordColimitIso X).hom
  let u := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom
  let J := LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩
  let n := OrderedProfile.countFunctor.obj J
  let j := (chosenOrderedTensorLengthIso X).hom.app J ≫ colimit.ι (wordLengthTensorDiagram X) n
  have h1 := chosenAssociativeProfileWordIso_coefficient X P o
  have h2 : j ≫ b = (chosenAssociativeOrderedPowerIso X P o).hom ≫
      TensorWord.tensorWordι X (Nat.card P.inputs) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => (chosenOrderedTensorLengthIso X).hom.app J ≫ q)
        (associativeWordColimitPowerIso_ι X n)).trans (Category.assoc _ _ _).symm)
  have h := twoColimitInjectionSteps
    (associativeProfileCoefficientInjection X P o ≫
      profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P)
    (chosenAssociativeProfileWordIso X).hom b u j
    ((chosenAssociativeOrderedPowerIso X P o).hom ≫ TensorWord.tensorWordι X (Nat.card P.inputs))
    ((Category.assoc _ _ _).trans h1) h2
  simpa only [b, u, chosenAssociativeTensorWordsIso, Iso.trans_hom, Category.assoc] using h



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenAssociativeWordInjections

/- Source proof segment: OrderedWordEvaluation -/
section source_OrderedWordEvaluation
/-!
# Actual finite word evaluation through the public tensor-word lift

The evaluation maps are the original tensor-word injections followed
by the actual universal monoid extension. No evaluator, concatenation,
or monoid-operation outcome is supplied as a hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory Limits MonoidalCategory TensorPower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

local instance : HasColimitsOfShape (Discrete ℕ) C := HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))

/-- Evaluate every original finite word injection using the actual
public tensor-word monoid extension of the supplied generator map. -/
def finiteWordEvaluation {X : C} (M : Mon C) (f : X ⟶ M.X) (n : ℕ) : tensorPowObj X n ⟶ M.X :=
  tensorWordι X n ≫ tensorWordLift M f

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The public extension evaluates each actual original injection
by its original recursive unit and multiplication assembly. -/
theorem finiteWordEvaluation_rec {X : C} (M : Mon C) (f : X ⟶ M.X) (n : ℕ) :
    finiteWordEvaluation M f n =
      Nat.rec (motive := fun n => tensorPowObj X n ⟶ M.X)
        M.mon.one (fun _ ih => (ih ⊗ₘ f) ≫ M.mon.mul) n :=
  Sigma.ι_comp_desc _ n

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The actual empty word evaluates by the original monoid unit. -/
@[simp]
theorem finiteWordEvaluation_zero {X : C} (M : Mon C) (f : X ⟶ M.X) :
    finiteWordEvaluation M f 0 = M.mon.one := finiteWordEvaluation_rec M f 0

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- Appending one original input multiplies its original value
after evaluating the entire original preceding word. -/
theorem finiteWordEvaluation_succ {X : C} (M : Mon C) (f : X ⟶ M.X) (n : ℕ) :
    finiteWordEvaluation M f (n + 1) = (finiteWordEvaluation M f n ⊗ₘ f) ≫ M.mon.mul := by
  rw [finiteWordEvaluation_rec, finiteWordEvaluation_rec]
  rfl

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The actual unary word evaluation is the original left unitor
followed by the original generator map. -/
theorem finiteWordEvaluation_one {X : C} (M : Mon C) (f : X ⟶ M.X) :
    finiteWordEvaluation M f 1 = (λ_ X).hom ≫ f := by
  exact (finiteWordEvaluation_rec M f 1).trans (MonObj.one_mul_hom f)

/-- Original finite word evaluation respects the actual tensor
power add comparison, derived from the public monoid extension and
the original tensor-word multiplication injection equation. -/
theorem finiteWordEvaluation_add {X : C} (M : Mon C) (f : X ⟶ M.X) (m n : ℕ) :
    finiteWordEvaluation M f (m + n) =
      (tensorPowObj_add X m n).hom ≫
        ((finiteWordEvaluation M f m ⊗ₘ finiteWordEvaluation M f n) ≫ M.mon.mul) := by
  let g := tensorWordLift M f
  have hmul : tensorWordMul X ≫ g = (g ⊗ₘ g) ≫ M.mon.mul := IsMonHom.mul_hom g
  apply (tensorPowObj_add X m n).inv_comp_eq.mp
  change (tensorPowObj_add X m n).inv ≫ (tensorWordι X (m + n) ≫ g) = _
  rw [← Category.assoc, ← tensorWordMul_ι, Category.assoc, hmul, ← Category.assoc,
    tensorHom_comp_tensorHom]
  rfl

/-- Evaluate original words of words in their actual free word monoid. -/
def wordConcatenationEvaluation (X : C) (n : ℕ) :
    tensorPowObj (tensorWordObj X) n ⟶ tensorWordObj X :=
  finiteWordEvaluation (tensorWordMon X) (𝟙 (tensorWordObj X)) n

/-- The original empty list of words produces its original degree-zero unit word. -/
@[simp]
theorem wordConcatenationEvaluation_zero (X : C) :
    wordConcatenationEvaluation X 0 = tensorWordOne X :=
  finiteWordEvaluation_zero (tensorWordMon X) (𝟙 _)

/-- The original unary list of words evaluates by the actual unitor. -/
theorem wordConcatenationEvaluation_one (X : C) :
    wordConcatenationEvaluation X 1 = (λ_ (tensorWordObj X)).hom := by
  exact (finiteWordEvaluation_one (tensorWordMon X) (𝟙 _)).trans (Category.comp_id _)

/-- The original binary list of words is the original binary word multiplication. -/
theorem wordConcatenationEvaluation_two (X : C) :
    wordConcatenationEvaluation X 2 =
      ((λ_ (tensorWordObj X)).hom ⊗ₘ 𝟙 (tensorWordObj X)) ≫ tensorWordMul X := by
  have h := finiteWordEvaluation_succ (tensorWordMon X) (𝟙 _) 1
  have h1 : finiteWordEvaluation (tensorWordMon X) (𝟙 _) 1 = (λ_ (tensorWordObj X)).hom :=
    (finiteWordEvaluation_one (tensorWordMon X) (𝟙 _)).trans (Category.comp_id _)
  exact h.trans (congrArg (fun k => (k ⊗ₘ 𝟙 (tensorWordObj X)) ≫ tensorWordMul X) h1)




end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OrderedWordEvaluation

/- Source proof segment: AssociativeWordEvaluationOperations -/
section source_AssociativeWordEvaluationOperations
/-!
# Original tensor-word monoid evaluation as associative tensor operations

These operation maps are constructed from the actual public monoid
extension and source chosen strand comparison. No algebra or
operation-preservation outcome is supplied as an assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem evaluateCoefficientCopy {V : Type*} [Category* V]
    {A B D E Q L : V} (i : A ⟶ B) (p : B ⟶ D) (c : D ⟶ E) (g : E ⟶ Q)
    (u : A ⟶ L) (t : L ⟶ E) (h : i ≫ (p ≫ c) = u ≫ t) :
    i ≫ (p ≫ (c ≫ g)) = u ≫ (t ≫ g) := by
  rw [← Category.assoc p c g, ← Category.assoc i (p ≫ c) g, h, Category.assoc u t g]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative word evaluation operations construction. -/
local instance associativeWordEvaluationOperationsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual word monoid evaluates the original associative
operation/profile coinvariants on its own carrier through the
PROVED source chosen strand map and the actual public word extension. -/
def wordEvaluationAction (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) ⟶
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)
  | PUnit.unit => (chosenAssociativeTensorWordsIso (TensorWord.tensorWordObj X)).hom ≫
      TensorWord.tensorWordLift (TensorWord.tensorWordMon X) (𝟙 (TensorWord.tensorWordObj X))

/-- Every original associative tensor operation is obtained by
actual profile descent into the original word-monoid evaluation.
This is an operation family, before its algebra laws are proved. -/
def wordEvaluationOperations (X : C) :
    Operations (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) :=
  operationsEquiv (FiniteTensor.UnitCopower.associativeOperad C).toCollection _ _ (wordEvaluationAction X)

/-- Each original root order coefficient copy is evaluated by
the actual original increasingly ordered word inputs, with every
source finite strand correction retained. -/
theorem wordEvaluationOperations_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection (TensorWord.tensorWordObj X) P o ≫
        (wordEvaluationOperations X).app PUnit.unit P =
      (unitCoefficientTensorIso
          ((analyticInputFamily (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)).obj P)).hom ≫
        (chosenAssociativeOrderedPowerIso (TensorWord.tensorWordObj X) P o).hom ≫
        TensorWord.wordConcatenationEvaluation X (Nat.card P.inputs) := by
  let W := TensorWord.tensorWordObj X
  let p := profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => W) P
  let c := (chosenAssociativeTensorWordsIso W).hom
  let g := TensorWord.tensorWordLift (TensorWord.tensorWordMon X) (𝟙 W)
  let i := associativeProfileCoefficientInjection W P o
  let u := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => W)).obj P)).hom
  let t := (chosenAssociativeOrderedPowerIso W P o).hom ≫ TensorWord.tensorWordι W (Nat.card P.inputs)
  have h := evaluateCoefficientCopy i p c g u t (chosenAssociativeTensorWordsIso_coefficient W P o)
  exact h.trans (congrArg (fun q => u ≫ q)
    (Category.assoc (chosenAssociativeOrderedPowerIso W P o).hom
      (TensorWord.tensorWordι W (Nat.card P.inputs)) g))

/-- The constructed operation action retains the actual original
word-monoid extension map after source-strand-corrected profile descent. -/
theorem wordEvaluationOperations_desc (X : C) :
    (wordEvaluationOperations X).desc = wordEvaluationAction X :=
  (operationsEquiv (FiniteTensor.UnitCopower.associativeOperad C).toCollection _ _).symm_apply_apply _



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeWordEvaluationOperations

/- Source proof segment: AssociativeCoefficientOperationExt -/
section source_AssociativeCoefficientOperationExt
/-!
# Original associative coefficient copies detect full tensor operation maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits

private theorem copyFromIsoBeta {V : Type*} [Category* V]
    {D B A Q : V} (u : D ⟶ B) (i : B ⟶ A) (e : Q ≅ A) (j : D ⟶ Q)
    (h : j ≫ e.hom = u ≫ i) : u ≫ (i ≫ e.inv) = j := by
  rw [← Category.assoc u i, ← h, Category.assoc j e.hom, e.hom_inv_id, Category.comp_id]

private theorem compareCopiesUnderInverse {V : Type*} [Category* V]
    {D B A Q Z : V} (u : D ⟶ B) (i : B ⟶ A) (e : Q ≅ A) (j : D ⟶ Q)
    (f g : Q ⟶ Z) (h : j ≫ e.hom = u ≫ i) (hf : j ≫ f = j ≫ g) :
    u ≫ (i ≫ (e.inv ≫ f)) = u ≫ (i ≫ (e.inv ≫ g)) := by
  have hi := copyFromIsoBeta u i e j h
  simpa only [Category.assoc] using
    (((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ f) hi)).trans
      (hf.trans ((congrArg (fun p => p ≫ g) hi.symm).trans (Category.assoc _ _ _))))

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Full original coefficient-weighted operation maps agree if
they agree after EVERY original lifted order coefficient-copy
injection, retaining all original finite input leaves. -/
theorem associativeCoefficientOperation_hom_ext (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) {Z : C}
    {f g : (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X)).obj P ⟶ Z}
    (h : ∀ o : ULift.{us} (LinearOrder P.inputs),
      associativeProfileCoefficientInjection X P o ≫ f =
        associativeProfileCoefficientInjection X P o ≫ g) : f = g := by
  let e := associativeProfileTensorIso X P
  let u := unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)
  apply (cancel_epi e.inv).1
  apply Sigma.hom_ext
  intro o
  apply (cancel_epi u.hom).1
  exact compareCopiesUnderInverse u.hom
    (Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) =>
      (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) o)
    e (associativeProfileCoefficientInjection X P o) f g
    (associativeProfileCoefficientInjection_β X P o) (h o)



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeCoefficientOperationExt

/- Source proof segment: AssociativeWordCarrierConjugation -/
section source_AssociativeWordCarrierConjugation
/-!
# The original free As action on the exact chosen word carrier

The action and operations below are conjugated from the actual
constructed free algebra by the proved source strand-adjusted
carrier isomorphism. They are not supplied as output assumptions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem conjugatedProfileOperationFromSquares {V : Type*} [Category* V]
    {D A B C E F : V} (i : D ⟶ A) (t : A ⟶ B) (a : B ⟶ C) (e : C ⟶ E)
    (h : D ⟶ F) (j : F ⟶ B) (f : F ⟶ C)
    (hn : i ≫ t = h ≫ j) (hj : j ≫ a = f) :
    i ≫ (t ≫ (a ≫ e)) = h ≫ (f ≫ e) := by
  rw [← Category.assoc i t, hn, Category.assoc h j, ← Category.assoc j a, hj]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative word carrier conjugation construction. -/
local instance associativeWordCarrierConjugationFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original constructed free As carrier at its one color
is the original tensor-word carrier through the actual source
chosen strand map, with both original component inverse maps. -/
def chosenWordCarrierIso (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) ≅ (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) where
  hom d := match d with
    | PUnit.unit => (chosenAssociativeTensorWordsIso X).hom
  inv d := match d with
    | PUnit.unit => (chosenAssociativeTensorWordsIso X).inv
  hom_inv_id := by
    funext d
    cases d
    exact (chosenAssociativeTensorWordsIso X).hom_inv_id
  inv_hom_id := by
    funext d
    cases d
    exact (chosenAssociativeTensorWordsIso X).inv_hom_id

/-- The ACTUAL constructed free operadic multiplication,
conjugated into the exact original source corrected word carrier. -/
def conjugatedFreeWordAction (X : C) :
    profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) ⟶
        (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) :=
  profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection (chosenWordCarrierIso X).inv ≫
    (freeAlgebra.{0, v, u, us} (FiniteTensor.UnitCopower.associativeOperad C) (fun _ : PUnit.{1} => X)).action ≫
    (chosenWordCarrierIso X).hom

/-- The ACTUAL free As tensor operations on the original word
carrier, before comparison with original monoid evaluation. -/
def conjugatedFreeWordOperations (X : C) :
    Operations (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) :=
  operationsEquiv (FiniteTensor.UnitCopower.associativeOperad C).toCollection _ _
    (conjugatedFreeWordAction X)

/-- Every original profile recovers the actual original free
operation after its exact source input/output carrier isomorphisms.
No preservation or operation comparison is assumed. -/
theorem conjugatedFreeWordOperations_app (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    (conjugatedFreeWordOperations X).app PUnit.unit P =
      (analyticSummandCarrierMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (chosenWordCarrierIso X).inv).app P ≫
      freeOperation.{0, v, u, us} (FiniteTensor.UnitCopower.associativeOperad C) (fun _ : PUnit.{1} => X) P ≫
      (chosenWordCarrierIso X).hom PUnit.unit :=
  conjugatedProfileOperationFromSquares
    (profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) P)
    (profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection (chosenWordCarrierIso X).inv PUnit.unit)
    (profileMultiplication.{0, v, u, us} (FiniteTensor.UnitCopower.associativeOperad C) (fun _ : PUnit.{1} => X)
      PUnit.unit)
    ((chosenWordCarrierIso X).hom PUnit.unit)
    ((analyticSummandCarrierMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (chosenWordCarrierIso X).inv).app P)
    (profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X)) P)
    (freeOperation.{0, v, u, us} (FiniteTensor.UnitCopower.associativeOperad C) (fun _ : PUnit.{1} => X) P)
    (profileι_map (FiniteTensor.UnitCopower.associativeOperad C).toCollection (chosenWordCarrierIso X).inv P)
    (profileMultiplication_profile.{0, v, u, us} (FiniteTensor.UnitCopower.associativeOperad C) (fun _ : PUnit.{1} => X)
      P)

/-- Descending the actual conjugated original operation family
returns precisely the actual source conjugated free action. -/
theorem conjugatedFreeWordOperations_desc (X : C) :
    (conjugatedFreeWordOperations X).desc = conjugatedFreeWordAction X :=
  (operationsEquiv (FiniteTensor.UnitCopower.associativeOperad C).toCollection _ _).symm_apply_apply _



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeWordCarrierConjugation

/- Source proof segment: ConjugatedFreeWordAlgebra -/
section source_ConjugatedFreeWordAlgebra
/-!
# The actual free As algebra on the original corrected word carrier
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory TensorWord
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the conjugated free word algebra construction. -/
local instance conjugatedFreeWordAlgebraFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- Transport the ACTUAL constructed free As action through the
proved source carrier isomorphism. Unit and associativity are proved
by the actual monad algebra transport, with no action-law premise. -/
def conjugatedFreeWordEMAlgebra (X : C) :
    Monad.Algebra (profileMonad.{0, v, u, us} (associativeOperad.{us, v, u} C)) :=
  Monad.Algebra.transportAlongIso
    ((tensorAlgebraToEM.{0, v, u, us} (associativeOperad.{us, v, u} C)).obj
      (freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X)))
    (chosenWordCarrierIso X)

/-- Recover every original free As tensor operation on the exact
original word carrier from its actual transported algebra action. -/
def conjugatedFreeWordAlgebra (X : C) : Algebra (associativeOperad.{us, v, u} C) :=
  (emToTensorAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C)).obj (conjugatedFreeWordEMAlgebra X)

/-- The actual transported algebra action is the original
constructed conjugated free operadic action. -/
theorem conjugatedFreeWordAlgebra_action (X : C) :
    (conjugatedFreeWordAlgebra X).action = conjugatedFreeWordAction X :=
  Algebra.ofAction_action.{0, v, u, us} (associativeOperad.{us, v, u} C)
    (conjugatedFreeWordEMAlgebra X).A (conjugatedFreeWordEMAlgebra X).a
    (conjugatedFreeWordEMAlgebra X).unit (conjugatedFreeWordEMAlgebra X).assoc

/-- Every original operation map of the constructed word-carrier
algebra is exactly the original conjugated free operation map. -/
theorem conjugatedFreeWordAlgebra_operations (X : C) :
    (conjugatedFreeWordAlgebra X).operations = conjugatedFreeWordOperations X := rfl

/-- The actual original corrected carrier map preserves every
original tensor operation of the constructed free As algebra. -/
def conjugatedFreeWordAlgebraHom (X : C) :
    freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X) ⟶
      conjugatedFreeWordAlgebra X :=
  Algebra.Hom.ofActionEquation _ _ (chosenWordCarrierIso X).hom (by
    let B := (tensorAlgebraToEM.{0, v, u, us} (associativeOperad.{us, v, u} C)).obj
      (freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X))
    let e := Monad.Algebra.transportAlongIsoIso B (chosenWordCarrierIso X)
    have h : profileMap (associativeOperad.{us, v, u} C).toCollection (chosenWordCarrierIso X).hom ≫
        conjugatedFreeWordAction X =
      (freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X)).action ≫
        (chosenWordCarrierIso X).hom := e.hom.h
    exact (congrArg (profileMap (associativeOperad.{us, v, u} C).toCollection
      (chosenWordCarrierIso X).hom ≫ ·) (conjugatedFreeWordAlgebra_action X)).trans h)

/-- The original inverse carrier map also preserves all the
original tensor operations, by the actual inverse algebra square. -/
def conjugatedFreeWordAlgebraInv (X : C) :
    conjugatedFreeWordAlgebra X ⟶
      freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X) :=
  Algebra.Hom.ofActionEquation _ _ (chosenWordCarrierIso X).inv (by
    let B := (tensorAlgebraToEM.{0, v, u, us} (associativeOperad.{us, v, u} C)).obj
      (freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X))
    let e := Monad.Algebra.transportAlongIsoIso B (chosenWordCarrierIso X)
    have h : profileMap (associativeOperad.{us, v, u} C).toCollection (chosenWordCarrierIso X).inv ≫
        (freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X)).action =
      conjugatedFreeWordAction X ≫ (chosenWordCarrierIso X).inv := e.inv.h
    exact h.trans (congrArg (· ≫ (chosenWordCarrierIso X).inv)
      (conjugatedFreeWordAlgebra_action X).symm))

/-- The actual free As algebra is isomorphic, through its proved
original strand-corrected carrier maps, to the constructed word-carrier
algebra, with every original operation square and both inverse laws. -/
def conjugatedFreeWordAlgebraIso (X : C) :
    freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X) ≅
      conjugatedFreeWordAlgebra X where
  hom := conjugatedFreeWordAlgebraHom X
  inv := conjugatedFreeWordAlgebraInv X
  hom_inv_id := Algebra.Hom.ext (chosenWordCarrierIso X).hom_inv_id
  inv_hom_id := Algebra.Hom.ext (chosenWordCarrierIso X).inv_hom_id

@[simp]
theorem conjugatedFreeWordAlgebraIso_hom_carrier (X : C) :
    (conjugatedFreeWordAlgebraIso X).hom.hom = (chosenWordCarrierIso X).hom := rfl

@[simp]
theorem conjugatedFreeWordAlgebraIso_inv_carrier (X : C) :
    (conjugatedFreeWordAlgebraIso X).inv.hom = (chosenWordCarrierIso X).inv := rfl




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ConjugatedFreeWordAlgebra

/- Source proof segment: AssociativeOperationLeafCopies -/
section source_AssociativeOperationLeafCopies
/-!
# Actual associative operadic substitution on original coefficient and leaf copies
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem copiedSubstitutionFromNormalization {V : Type*} [Category* V]
    {D S N A B Q : V} (h : S ≅ N) (i : D ⟶ N) (f : S ⟶ A)
    (k : N ⟶ B) (t : B ⟶ A) (m : D ⟶ Q) (j : Q ⟶ B)
    (hf : f = h.hom ≫ (k ≫ t)) (hk : i ≫ k = m ≫ j) :
    (i ≫ h.inv) ≫ f = m ≫ (j ≫ t) := by
  rw [hf, Category.assoc i h.inv, h.inv_hom_id_assoc,
    ← Category.assoc i k, hk, Category.assoc m j]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original raw associative substitution source, normalized
by its actual original coefficient/leaf tensor isomorphism. -/
def associativeOperationSourceIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    algebraSubstitutionSource (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s ≅
      (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).obj
        ((FiniteTensor.tensor (V := C)).obj
          ((ColoredOperadObj.substitutionFactors (associativeOperad C).toCollection).obj s)) :=
  (FiniteTensor.tensor (V := C)).mapIso
      (substitutionToLeavesIso (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s) ≪≫
    coefficientLeavesNormalizationIso
      ((ColoredOperadObj.substitutionFactors (associativeOperad C).toCollection).obj s)
      (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)

/-- Insert every original root and branch associative order copy
in the original raw substitution source, preserving every original leaf. -/
def associativeOperationCopy (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).obj
        ((FiniteTensor.tensor (V := C)).obj (emptyScalarFamily (associativeFactors.{us} s).index)) ⟶
      algebraSubstitutionSource (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s :=
  (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
      (associativeSubstitutionι C s a) ≫ (associativeOperationSourceIso X s).inv

/-- The original coefficient/leaf target comparison is exactly
the original profile coefficient-copy target comparison, retaining
every original tensor input. -/
theorem associativeOperationTargetIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (substitutionLeavesTargetIso (associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) s).hom =
      (associativeProfileFactorsIso X (profileInputs s.totalProfile)).inv := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      with_unfolding_all exact heq_of_eq (Category.id_comp (𝟙 _)).symm
    | some i =>
      with_unfolding_all exact heq_of_eq (Category.id_comp (𝟙 _)).symm

/-- The original raw associative operation coefficient copies
substitute to the original lifted lexicographic coefficient copy,
with every original input leaf retained and actual scalar multiplication. -/
theorem associativeOperationCopy_substitution (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    associativeOperationCopy X s a ≫
        operadSubstitutionInputs (associativeOperad C) (fun _ : PUnit.{1} => X) s =
      (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
          (emptyScalarTensorIso (associativeFactors.{us} s).index).hom ≫
        associativeProfileCoefficientInjection X (profileInputs s.totalProfile)
          (associativeLexicographic.{us} s a) := by
  let L := profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile
  let F := coefficientLeafTensorFunctor L
  let h := associativeOperationSourceIso X s
  let i := F.map (associativeSubstitutionι C s a)
  let k := F.map ((associativeOperad C).subst.app s)
  let t := (FiniteTensor.tensor (V := C)).map
    (substitutionLeavesTargetIso (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s).hom
  let m := F.map (emptyScalarTensorIso (associativeFactors.{us} s).index).hom
  let j := F.map (Sigma.ι (fun _ : ULift.{us} (LinearOrder s.totalProfile.inputs) => unitObject C)
    (associativeLexicographic.{us} s a))
  have hf : operadSubstitutionInputs (associativeOperad C) (fun _ : PUnit.{1} => X) s =
      h.hom ≫ (k ≫ t) := by
    have hs := operadSubstitutionInputs_factorization (associativeOperad C) (fun _ : PUnit.{1} => X) s
    have hh : h.hom = (FiniteTensor.tensor (V := C)).map
        (substitutionToLeavesIso (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s).hom ≫
          coefficientLeavesNormalization
            ((ColoredOperadObj.substitutionFactors (associativeOperad C).toCollection).obj s) L :=
      congrArg (_ ≫ ·) (coefficientLeavesNormalizationIso_hom _ _)
    exact hs.trans ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ (k ≫ t)) hh.symm))
  have hk : i ≫ k = m ≫ j :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (associativeSubstitutionι_subst C s a)).trans (F.map_comp _ _))
  have ht : t = ((FiniteTensor.tensor (V := C)).mapIso
      (associativeProfileFactorsIso X (profileInputs s.totalProfile))).inv :=
    congrArg (FiniteTensor.tensor (V := C)).map (associativeOperationTargetIso X s)
  have he := copiedSubstitutionFromNormalization h i
    (operadSubstitutionInputs (associativeOperad C) (fun _ : PUnit.{1} => X) s) k t m j hf hk
  exact he.trans (congrArg (fun q => m ≫ (j ≫ q)) ht)



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOperationLeafCopies

/- Source proof segment: AssociativeFreeOperationWordCopies -/
section source_AssociativeFreeOperationWordCopies
/-!
# Actual free associative operations on original word coefficient copies
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem copiedFreeOperationFromSource {V : Type*} [Category* V]
    {D R B A Q : V} (e : R ≅ B) (i : D ⟶ R) (k : B ⟶ A)
    (f : A ⟶ Q) (t : R ⟶ Q) (h : k ≫ f = e.inv ≫ t) :
    (i ≫ (e.hom ≫ k)) ≫ f = i ≫ t := by
  rw [Category.assoc i, Category.assoc e.hom, h, e.hom_inv_id_assoc]

private theorem removeSourceIso {V : Type*} [Category* V]
    {D L A Q : V} (e : D ≅ L) (i : D ⟶ A) (f : A ⟶ Q) (g : L ⟶ Q)
    (h : i ≫ f = e.hom ≫ g) : (e.inv ≫ i) ≫ f = g := by
  rw [Category.assoc e.inv i, h, e.inv_hom_id_assoc]

private theorem eraseIdentityWordInput {V : Type*} [Category* V]
    {D L Q : V} (p : D ⟶ L) (e : L ⟶ L) (j : L ⟶ Q) (he : e = 𝟙 L) :
    p ≫ (e ≫ j) = p ≫ j := by
  rw [he, Category.id_comp]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C := associativeWordLengthColimits (C := C)

/-- The actual original root and inner associative coefficient
copies, with their original leaf inputs, assembled into the actual
outer free-operation input by original inner quotient injections. -/
def associativeOperationTensorInjection (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).obj
        ((FiniteTensor.tensor (V := C)).obj (emptyScalarFamily (associativeFactors.{us} s).index)) ⟶
      (analyticSummand (associativeOperad C).toCollection
        (profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X))).obj
          (profileInputs s.outerProfile) :=
  associativeOperationCopy X s a ≫
    (FiniteTensor.flattenIso (V := C)).hom.app
      (nestedOperationFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s) ≫
    (FiniteTensor.tensor (V := C)).map
      (operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s)

/-- The source actual unit coefficients and original leaves
normalize to precisely the original total input tensor. -/
def associativeOperationLeavesIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).obj
        ((FiniteTensor.tensor (V := C)).obj (emptyScalarFamily (associativeFactors.{us} s).index)) ≅
      (FiniteTensor.tensor (V := C)).obj (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile) :=
  (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).mapIso
      (emptyScalarTensorIso (associativeFactors.{us} s).index) ≪≫
    unitCoefficientTensorIso (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)

/-- Every original root and branch operation copy evaluates the
ACTUAL free operadic operation by the original lifted lexicographic
coefficient copy and actual original total quotient injection. -/
theorem associativeOperationTensorInjection_freeOperation (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    associativeOperationTensorInjection X s a ≫
        freeOperation (associativeOperad C) (fun _ : PUnit.{1} => X) (profileInputs s.outerProfile) =
      (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
          (emptyScalarTensorIso (associativeFactors.{us} s).index).hom ≫
        associativeProfileCoefficientInjection X (profileInputs s.totalProfile)
          (associativeLexicographic.{us} s a) ≫
        profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) (profileInputs s.totalProfile) := by
  let e := (FiniteTensor.flattenIso (V := C)).app
    (nestedOperationFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s)
  have h := copiedFreeOperationFromSource e (associativeOperationCopy X s a)
    ((FiniteTensor.tensor (V := C)).map
      (operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s))
    (freeOperation (associativeOperad C) (fun _ : PUnit.{1} => X) (profileInputs s.outerProfile))
    (operadSubstitutionInputs (associativeOperad C) (fun _ : PUnit.{1} => X) s ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) (profileInputs s.totalProfile))
    (operationInjection_freeOperation (associativeOperad C) (fun _ : PUnit.{1} => X) s)
  exact h.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ profileι (associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) (profileInputs s.totalProfile))
        (associativeOperationCopy_substitution X s a)).trans (Category.assoc _ _ _)))

/-- A source substitution with the one original output color.
All original finite inner profiles, colors and word inputs are retained. -/
def associativeUnitOutputSubstitution (inner : FiniteFamily (ColoredProfile PUnit.{1})) :
    ColoredSubstitutionData PUnit.{1} := ⟨PUnit.unit, inner⟩

/-- The actual input tensor of the original source words, with
their root and branch order copies, into the actual free operation. -/
def associativeNormalizedWordInputs (X : C) (inner : FiniteFamily (ColoredProfile PUnit.{1}))
    (a : ∀ o : (associativeFactors.{us} (associativeUnitOutputSubstitution inner)).index,
      (associativeFactors.{us} (associativeUnitOutputSubstitution inner)).obj o) :
    (FiniteTensor.tensor (V := C)).obj
        (profileLeafFamily (fun _ : PUnit.{1} => X) (associativeUnitOutputSubstitution inner).totalProfile) ⟶
      (analyticSummand (associativeOperad C).toCollection
        (profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X))).obj
          (profileInputs (associativeUnitOutputSubstitution inner).outerProfile) :=
  (associativeOperationLeavesIso X (associativeUnitOutputSubstitution inner)).inv ≫
    associativeOperationTensorInjection X (associativeUnitOutputSubstitution inner) a

/-- Every actual original source operation word input evaluates
the constructed free As operation to the original increasing tensor
word of its lifted lexicographic total order, including empty blocks. -/
theorem associativeNormalizedWordInputs_freeOperation (X : C) (inner : FiniteFamily (ColoredProfile PUnit.{1}))
    (a : ∀ o : (associativeFactors.{us} (associativeUnitOutputSubstitution inner)).index,
      (associativeFactors.{us} (associativeUnitOutputSubstitution inner)).obj o) :
    associativeNormalizedWordInputs X inner a ≫
        freeOperation (associativeOperad C) (fun _ : PUnit.{1} => X)
          (profileInputs (associativeUnitOutputSubstitution inner).outerProfile) ≫
        (associativeProfileWordColimitIso X).hom =
      (orderedTensorLengthIso X).hom.app
          (LiftedOrderFiber.orderedEquivalence.functor.obj
            ⟨profileInputs (associativeUnitOutputSubstitution inner).totalProfile,
              Discrete.mk (associativeLexicographic.{us} (associativeUnitOutputSubstitution inner) a)⟩) ≫
        colimit.ι (wordLengthTensorDiagram X)
          (OrderedProfile.countFunctor.obj
            (LiftedOrderFiber.orderedEquivalence.functor.obj
              ⟨profileInputs (associativeUnitOutputSubstitution inner).totalProfile,
                Discrete.mk (associativeLexicographic.{us} (associativeUnitOutputSubstitution inner) a)⟩)) := by
  let s := associativeUnitOutputSubstitution inner
  let L := profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile
  let m := (coefficientLeafTensorFunctor L).map (emptyScalarTensorIso (associativeFactors.{us} s).index).hom
  let i := associativeOperationTensorInjection X s a
  let f := freeOperation (associativeOperad C) (fun _ : PUnit.{1} => X) (profileInputs s.outerProfile)
  let q := profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) (profileInputs s.totalProfile)
  let c := associativeProfileCoefficientInjection X (profileInputs s.totalProfile) (associativeLexicographic.{us} s a)
  let e := associativeOperationLeavesIso X s
  let w := (associativeProfileWordColimitIso X).hom
  let j := (orderedTensorLengthIso X).hom.app
    (LiftedOrderFiber.orderedEquivalence.functor.obj ⟨profileInputs s.totalProfile,
      Discrete.mk (associativeLexicographic.{us} s a)⟩) ≫
    colimit.ι (wordLengthTensorDiagram X)
      (OrderedProfile.countFunctor.obj (LiftedOrderFiber.orderedEquivalence.functor.obj
        ⟨profileInputs s.totalProfile, Discrete.mk (associativeLexicographic.{us} s a)⟩))
  have hcopy : c ≫ (q ≫ w) = (unitCoefficientTensorIso L).hom ≫ j := by
    have hp := associativeProfileWordColimitIso_coefficient X (profileInputs s.totalProfile)
      (associativeLexicographic.{us} s a)
    exact hp.trans (eraseIdentityWordInput (unitCoefficientTensorIso L).hom
      ((associativeFiberOrderedIso X).hom.app ⟨profileInputs s.totalProfile,
        Discrete.mk (associativeLexicographic.{us} s a)⟩) j rfl)
  have hi : i ≫ f = m ≫ (c ≫ q) := associativeOperationTensorInjection_freeOperation X s a
  have h : i ≫ (f ≫ w) = e.hom ≫ j :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ w) hi).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => m ≫ k) ((Category.assoc _ _ _).trans hcopy)).trans
            (Category.assoc _ _ _).symm)))
  exact removeSourceIso e i (f ≫ w) j h




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeFreeOperationWordCopies

/- Source proof segment: AsCoefficientCopies -/
section source_AsCoefficientCopies
/-!
# The actual original associative coefficient-copy factors
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.InputCopies

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- The original tensor-unit factor for every actual root and
branch coefficient of a source associative substitution. -/
def unitCoefficients (s : ColoredSubstitutionData PUnit.{1}) : FiniteFamily C :=
  emptyScalarFamily (FintypeCat.of (Option s.inner.index))

/-- Insert the original root and inner order coefficients by
their actual coproduct injections, without changing any input index. -/
def coefficientCopies (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    unitCoefficients (C := C) s ⟶
      (ColoredOperadObj.substitutionFactors (associativeOperad C).toCollection).obj s where
  equiv := Equiv.refl (Option s.inner.index)
  hom o := match o with
    | none => Sigma.ι (fun _ : ULift.{us} (LinearOrder s.outerProfile.inputs) => unitObject C) (a none)
    | some i => Sigma.ι (fun _ : ULift.{us} (LinearOrder (s.inner.obj i).inputs) => unitObject C) (a (some i))

/-- The original simultaneous coefficient-copy maps agree with
the actual source tensor-copower factors and their original
canonical operad factor comparison. -/
theorem coefficientCopies_source (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    tensorιFactors C (associativeFactors.{us} s) a ≫
        (ColoredOperadObj.MapData.factorsIso (functor C) associativeSetOperad.{us}.toCollection s).hom =
      coefficientCopies (C := C) s a := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none => with_unfolding_all exact heq_of_eq (Category.comp_id _)
    | some i => with_unfolding_all exact heq_of_eq (Category.comp_id _)

/-- Tensoring the original root and inner coefficient-copy
factor maps is exactly the constructed actual associative
substitution coefficient injection, at every finite profile. -/
theorem coefficientCopies_tensor (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (FiniteTensor.tensor (V := C)).map (coefficientCopies (C := C) s a) =
      associativeSubstitutionι C s a :=
  (congrArg (FiniteTensor.tensor (V := C)).map (coefficientCopies_source (C := C) s a).symm).trans
    ((FiniteTensor.tensor (V := C)).map_comp _ _)



end CategoryTheory.Operad.Tensor.Associative.InputCopies
end
end
end source_AsCoefficientCopies

/- Source proof segment: AsUnitInputFactors -/
section source_AsUnitInputFactors
/-!
# Original unit coefficient and input families for associative operation copies
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.InputCopies

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Only a source indexing collection of the actual tensor unit;
no unit operad or operad law is asserted for this intermediate family. -/
def unitCollection (C : Type u) [Category.{v} C] [FiniteTensor C] :
    ColoredSymmetricCollection PUnit.{1} C :=
  (Functor.const (ColoredProfile PUnit.{1})).obj (unitObject C)

/-- One original unit coefficient before the original input leaves. -/
def unitProfileFactors (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit) : FiniteFamily C :=
  (coefficientLeafFamilyFunctor ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).obj (unitObject C)

/-- The original root singleton and all original inner unit/input
families, including inner profiles with no inputs. -/
def unitNestedFactors (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option s.inner.index)
  obj o := match o with
    | none => (FiniteFamily.singleton (C := C)).obj (unitObject C)
    | some i => unitProfileFactors X (profileInputs (s.inner.obj i))

variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Every original inner coefficient copy map preserves the
original leaf factors by their identities. -/
def innerCopyFactors (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : ULift.{us} (LinearOrder P.inputs)) :
    unitProfileFactors X P ⟶
      (analyticFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X)).obj P where
  equiv := Equiv.refl (Option P.inputs)
  hom j := match j with
    | none => Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) => unitObject C) o
    | some _ => 𝟙 X

/-- Every original inner coefficient copy is the corresponding
original coefficient-leaf map followed by the actual original
weighted-profile factor comparison. -/
theorem innerCopyFactors_source (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : ULift.{us} (LinearOrder P.inputs)) :
    (coefficientLeafFamilyFunctor ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).map
        (Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) => unitObject C) o) ≫
      (associativeProfileFactorsIso X P).inv = innerCopyFactors X P o := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro j
    cases j with
    | none =>
      with_unfolding_all
        change HEq
          (Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) => unitObject C) o ≫
            (𝟙 _ ≫ 𝟙 _))
          (Sigma.ι (fun _ : ULift.{us} (LinearOrder P.inputs) => unitObject C) o)
        exact heq_of_eq (by simp only [Category.comp_id])
    | some _ =>
      with_unfolding_all
        change HEq ((𝟙 X) ≫ (𝟙 X ≫ 𝟙 X)) (𝟙 X)
        exact heq_of_eq (by simp only [Category.id_comp])

/-- The actual tensor of an original inner coefficient-copy map
is the parent's original profile coefficient injection. -/
theorem innerCopyFactors_tensor (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : ULift.{us} (LinearOrder P.inputs)) :
    (FiniteTensor.tensor (V := C)).map (innerCopyFactors X P o) =
      associativeProfileCoefficientInjection X P o :=
  (congrArg (FiniteTensor.tensor (V := C)).map (innerCopyFactors_source X P o).symm).trans
    ((FiniteTensor.tensor (V := C)).map_comp _ _)

/-- The actual original root and all inner coefficient copies
in the original nested operation/input family. -/
def nestedCopies (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    unitNestedFactors X s ⟶
      nestedOperationFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s where
  equiv := Equiv.refl (Option s.inner.index)
  hom o := match o with
    | none => (FiniteFamily.singleton (C := C)).map
        (Sigma.ι (fun _ : ULift.{us} (LinearOrder s.outerProfile.inputs) => unitObject C) (a none))
    | some i => innerCopyFactors X (profileInputs (s.inner.obj i)) (a (some i))

/-- The original raw unit/input factor bijection uses exactly
the same root/inner/leaf placement as the source substitution map. -/
def unitToLeavesIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteFamily.flatten (C := C)).obj (unitNestedFactors X s) ≅
      (FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested (unitCoefficients (C := C) s)
          (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)) := by
  let e₁ : ((FiniteFamily.flatten (C := C)).obj (unitNestedFactors X s)).index ≃
      ((FiniteFamily.flatten (C := C)).obj
        (nestedOperationFactors (unitCollection C) (fun _ : PUnit.{1} => X) s)).index :=
    Equiv.sigmaCongrRight (fun o => by
      cases o with
      | none => exact Equiv.refl PUnit
      | some i => exact Equiv.refl (Option (s.inner.obj i).inputs))
  let e₂ : ((FiniteFamily.flatten (C := C)).obj
      (substitutionInputFactors (unitCollection C) (fun _ : PUnit.{1} => X) s)).index ≃
      ((FiniteFamily.flatten (C := C)).obj
        (coefficientLeavesNested (unitCoefficients (C := C) s)
          (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile))).index :=
    Equiv.sigmaCongrRight (fun o => by
      cases o with
      | none => exact Equiv.refl (Option s.inner.index)
      | some i => exact Equiv.refl PUnit)
  exact FiniteFamily.isoOfReindex
    ((e₁.trans (substitutionFactorEquiv (unitCollection C) (fun _ : PUnit.{1} => X) s)).trans e₂)
    (by
      rintro ⟨o, j⟩
      cases o with
      | none => cases j; rfl
      | some i => cases j <;> rfl)

/-- The actual unit coefficient/source input normalization is
constructed from the original factor bijection and tensor flattening. -/
def unitSourceIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteTensor.tensor (V := C)).obj ((FiniteFamily.flatten (C := C)).obj (unitNestedFactors X s)) ≅
      (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).obj
        ((FiniteTensor.tensor (V := C)).obj (unitCoefficients (C := C) s)) :=
  (FiniteTensor.tensor (V := C)).mapIso (unitToLeavesIso X s) ≪≫
    coefficientLeavesNormalizationIso (unitCoefficients (C := C) s)
      (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)




end CategoryTheory.Operad.Tensor.Associative.InputCopies
end
end
end source_AsUnitInputFactors

/- Source proof segment: AsCopyReindexSquare -/
section source_AsCopyReindexSquare
/-!
# Original coefficient-copy and leaf regrouping square
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.InputCopies

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Copying original coefficients then regrouping the original
nested source equals regrouping its unit/input source then copying
the exact same root and branch coefficients; all original leaves
retain their identities and original dependent-sum positions. -/
theorem nestedCopies_reindex (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (FiniteFamily.flatten (C := C)).map (nestedCopies X s a) ≫
        (substitutionToLeavesIso (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s).hom =
      (unitToLeavesIso X s).hom ≫
        (FiniteFamily.flatten (C := C)).map
          (coefficientLeavesNestedMap (coefficientCopies (C := C) s a)
            (𝟙 (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile))) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    rintro ⟨o, j⟩
    cases o with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  · rintro ⟨o, j⟩
    cases o with
    | none =>
      cases j
      with_unfolding_all
        let r := Sigma.ι (fun _ : ULift.{us} (LinearOrder s.outerProfile.inputs) => unitObject C) (a none)
        change HEq (r ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _))) (𝟙 (unitObject C) ≫ r)
        exact heq_of_eq (by simp only [Category.id_comp, Category.comp_id])
    | some i =>
      cases j with
      | none =>
        with_unfolding_all
          let r := Sigma.ι (fun _ : ULift.{us} (LinearOrder (s.inner.obj i).inputs) => unitObject C) (a (some i))
          change HEq (r ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _))) (𝟙 (unitObject C) ≫ r)
          exact heq_of_eq (by simp only [Category.id_comp, Category.comp_id])
      | some j =>
        with_unfolding_all
          change HEq ((𝟙 X) ≫ (𝟙 X ≫ (𝟙 X ≫ 𝟙 X))) ((𝟙 X) ≫ (𝟙 X))
          exact heq_of_eq (by simp only [Category.id_comp])



end CategoryTheory.Operad.Tensor.Associative.InputCopies
end
end
end source_AsCopyReindexSquare

/- Source proof segment: AsCopyNormalization -/
section source_AsCopyNormalization
/-!
# Actual original associative input copies commute with source normalization
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.InputCopies

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem normalizeCopyFromSquares {V : Type*} [Category* V]
    {A B X Y U W : V} (h0 : A ≅ U) (h1 : B ≅ W) (f : A ⟶ B) (q : U ⟶ W)
    (p0 : A ⟶ X) (n0 : X ⟶ U) (p1 : B ⟶ Y) (n1 : Y ⟶ W) (r : X ⟶ Y)
    (hp0 : h0.hom = p0 ≫ n0) (hp1 : h1.hom = p1 ≫ n1)
    (hs : f ≫ p1 = p0 ≫ r) (hn : r ≫ n1 = n0 ≫ q) :
    f ≫ h1.hom = h0.hom ≫ q := by
  rw [hp0, hp1, ← Category.assoc f p1, hs, Category.assoc p0 r,
    hn, Category.assoc p0 n0]

private theorem sourceCopyThroughInverse {V : Type*} [Category* V]
    {A B U W : V} (h0 : A ≅ U) (h1 : B ≅ W) (f : A ⟶ B) (q : U ⟶ W)
    (h : f ≫ h1.hom = h0.hom ≫ q) :
    h0.inv ≫ f = q ≫ h1.inv := by
  apply (cancel_mono h1.hom).1
  rw [Category.assoc h0.inv f, h, h0.inv_hom_id_assoc,
    Category.assoc q h1.inv, h1.inv_hom_id, Category.comp_id]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Tensoring the original root and inner coefficient-copy maps
commutes with the complete original coefficient/leaf source
normalization. Original coefficients and all leaf identities are retained. -/
theorem nestedCopies_normalization (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (nestedCopies X s a)) ≫
        (associativeOperationSourceIso X s).hom =
      (unitSourceIso X s).hom ≫
        (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
          (associativeSubstitutionι C s a) := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let L := profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile
  let Ku := unitCoefficients (C := C) s
  let K := (ColoredOperadObj.substitutionFactors (associativeOperad C).toCollection).obj s
  let k := coefficientCopies (C := C) s a
  let h0 := unitSourceIso X s
  let h1 := associativeOperationSourceIso X s
  let f := T.map (F.map (nestedCopies X s a))
  let q := (coefficientLeafTensorFunctor L).map (associativeSubstitutionι C s a)
  let p0 := T.map (unitToLeavesIso X s).hom
  let n0 := coefficientLeavesNormalization Ku L
  let p1 := T.map (substitutionToLeavesIso (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s).hom
  let n1 := coefficientLeavesNormalization K L
  let r := T.map (F.map (coefficientLeavesNestedMap k (𝟙 L)))
  have hp0 : h0.hom = p0 ≫ n0 :=
    congrArg (fun t => p0 ≫ t) (coefficientLeavesNormalizationIso_hom Ku L)
  have hp1 : h1.hom = p1 ≫ n1 :=
    congrArg (fun t => p1 ≫ t) (coefficientLeavesNormalizationIso_hom K L)
  have hs : f ≫ p1 = p0 ≫ r :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (nestedCopies_reindex X s a)).trans (T.map_comp _ _))
  have hq : T.map (coefficientLeafMap (T.map k) (𝟙 L)) = q :=
    (congrArg T.map (coefficientLeafMap_idLeaves (T.map k) L)).trans
      (congrArg (coefficientLeafTensorFunctor L).map (coefficientCopies_tensor (C := C) s a))
  have hn : r ≫ n1 = n0 ≫ q :=
    (coefficientLeavesNormalization_naturality k (𝟙 L)).trans (congrArg (fun t => n0 ≫ t) hq)
  exact normalizeCopyFromSquares h0 h1 f q p0 n0 p1 n1 r hp0 hp1 hs hn

/-- The parent's normalized original As coefficient-copy injection
is exactly the actual original tensor of its root and inner coefficient
copies, reached by the actual original unit/input source normalizer. -/
theorem nestedCopies_parentCopy (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (unitSourceIso X s).inv ≫
        (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (nestedCopies X s a)) =
      associativeOperationCopy X s a :=
  sourceCopyThroughInverse (unitSourceIso X s) (associativeOperationSourceIso X s)
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (nestedCopies X s a)))
    ((coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
      (associativeSubstitutionι C s a)) (nestedCopies_normalization X s a)




end CategoryTheory.Operad.Tensor.Associative.InputCopies
end
end
end source_AsCopyNormalization

/- Source proof segment: AsAssembledInputCopies -/
section source_AsAssembledInputCopies
/-!
# Actual assembled original coefficient and chosen inner profile injections
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.InputCopies

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual assembled original root coefficient copy and
chosen inner profile quotient injections, with all original leaves. -/
def assembledCopies (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (unitNestedFactors X s) ⟶
      (analyticFactors (associativeOperad C).toCollection
        (profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X))).obj
          (profileInputs s.outerProfile) where
  equiv := Equiv.refl (Option s.inner.index)
  hom o := match o with
    | none => (FiniteTensor.singletonIso (V := C)).hom.app (unitObject C) ≫
        Sigma.ι (fun _ : ULift.{us} (LinearOrder s.outerProfile.inputs) => unitObject C) (a none)
    | some i => associativeProfileCoefficientInjection X (profileInputs (s.inner.obj i)) (a (some i)) ≫
        profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X)
          (profileInputs (s.inner.obj i))

/-- The original tensor of each coefficient-copy factor followed
by the original operation injection is exactly the displayed root
copy and each original chosen inner coefficient/profile copy. -/
theorem nestedCopies_assembled (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (nestedCopies X s a) ≫
      operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s =
        assembledCopies X s a := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq ((FiniteTensor.singletonIso (V := C)).hom.naturality
        (Sigma.ι (fun _ : ULift.{us} (LinearOrder s.outerProfile.inputs) => unitObject C) (a none)))
    | some i =>
      exact heq_of_eq (congrArg (fun k => k ≫
          profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X)
            (profileInputs (s.inner.obj i)))
        (innerCopyFactors_tensor X (profileInputs (s.inner.obj i)) (a (some i))))

/-- The exact original assembled tensor input map into the free
outer operation, with all original inner coefficient and leaf copies. -/
def assembledTensorInjection (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (FiniteTensor.tensor (V := C)).obj ((FiniteFamily.flatten (C := C)).obj (unitNestedFactors X s)) ⟶
      (analyticSummand (associativeOperad C).toCollection
        (profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X))).obj
          (profileInputs s.outerProfile) :=
  (FiniteTensor.flattenIso (V := C)).hom.app (unitNestedFactors X s) ≫
    (FiniteTensor.tensor (V := C)).map (assembledCopies X s a)

/-- The actual original copy maps and tensor flattening assemble
exactly the actual original chosen-word input injections. -/
theorem nestedCopies_tensor_assembled (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (nestedCopies X s a)) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        (nestedOperationFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s) ≫
      (FiniteTensor.tensor (V := C)).map
        (operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s) =
        assembledTensorInjection X s a := by
  let T := FiniteTensor.tensor (V := C)
  let f := nestedCopies X s a
  let m := operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality f
  have hm := congrArg T.map (nestedCopies_assembled X s a)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ T.map m) hn).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => (FiniteTensor.flattenIso (V := C)).hom.app (unitNestedFactors X s) ≫ k)
          ((T.map_comp _ _).symm.trans hm))))




end CategoryTheory.Operad.Tensor.Associative.InputCopies
end
end
end source_AsAssembledInputCopies

/- Source proof segment: AsOriginalInputAlignment -/
section source_AsOriginalInputAlignment
/-!
# The original chosen-word coefficient/input copies are the actual operation source copies
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.InputCopies

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem assembleOriginalCopies {V : Type*} [Category* V]
    {D S A B : V} (u : S ≅ D) (f : S ⟶ A) (c : A ⟶ B) (v : D ⟶ A) (d : S ⟶ B)
    (h0 : u.inv ≫ f = v) (h1 : f ≫ c = d) : u.inv ≫ d = v ≫ c := by
  rw [← h1, ← Category.assoc u.inv f, h0]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual original assembled chosen-word input tensor map,
under the actual original unit/input source normalizer, equals the
parent's actual coefficient-copy source injection and source assembly. -/
theorem assembledTensorInjection_parentCopy (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (unitSourceIso X s).inv ≫ assembledTensorInjection X s a =
      associativeOperationCopy X s a ≫
        (FiniteTensor.flattenIso (V := C)).hom.app
          (nestedOperationFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s) ≫
        (FiniteTensor.tensor (V := C)).map
          (operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s) :=
  assembleOriginalCopies (unitSourceIso X s)
    ((FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (nestedCopies X s a)))
    ((FiniteTensor.flattenIso (V := C)).hom.app
        (nestedOperationFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s) ≫
      (FiniteTensor.tensor (V := C)).map
        (operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) s))
    (associativeOperationCopy X s a) (assembledTensorInjection X s a)
    (nestedCopies_parentCopy X s a) (nestedCopies_tensor_assembled X s a)

/-- The original outer root coefficient is its actual unit-source
singleton collapse and original associative order copy. -/
theorem assembledCopies_root (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o) :
    (assembledCopies X s a).hom none =
      (FiniteTensor.singletonIso (V := C)).hom.app (unitObject C) ≫
        Sigma.ι (fun _ : ULift.{us} (LinearOrder s.outerProfile.inputs) => unitObject C) (a none) := rfl

/-- Each original inner input is the actual original associative
coefficient copy followed by its actual original profile quotient
injection, with all its original input leaves retained. -/
theorem assembledCopies_inner (X : C) (s : ColoredSubstitutionData PUnit.{1})
    (a : ∀ o : (associativeFactors.{us} s).index, (associativeFactors.{us} s).obj o)
    (i : s.inner.index) :
    (assembledCopies X s a).hom (some i) =
      associativeProfileCoefficientInjection X (profileInputs (s.inner.obj i)) (a (some i)) ≫
        profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X)
          (profileInputs (s.inner.obj i)) := rfl



end CategoryTheory.Operad.Tensor.Associative.InputCopies
end
end
end source_AsOriginalInputAlignment

/- Source proof segment: OriginalUnitLeafBlocks -/
section source_OriginalUnitLeafBlocks
/-!
# Original input leaf blocks and actual block unit coefficient removal
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Every original input leaf block on its unchanged original
inner profile index, with no operation coefficient included. -/
def leafBlocks (X : C) (s : ColoredSubstitutionData PUnit.{1}) : FiniteFamily (FiniteFamily C) where
  index := s.inner.index
  obj i := profileLeafFamily (fun _ : PUnit.{1} => X) (s.inner.obj i)

/-- The original flattened input leaf family is the original
total profile's input leaf family, through its actual dependent sum. -/
def leafBlocksFlattenIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteFamily.flatten (C := C)).obj (leafBlocks X s) ≅
      profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile :=
  FiniteFamily.isoOfReindex (Equiv.refl _) (fun _ => rfl)

/-- The evaluated original leaf tensor at every unchanged inner
profile; no coefficient or root unit is included. -/
def evaluatedLeaves (X : C) (s : ColoredSubstitutionData PUnit.{1}) : FiniteFamily C :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (leafBlocks X s)

/-- Remove the actual root singleton unit and each original inner
coefficient unit, while retaining every original evaluated leaf block. -/
def blockUnitCollapse (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (InputCopies.unitNestedFactors X s) ⟶
      (coefficientLeafFamilyFunctor (evaluatedLeaves X s)).obj (unitObject C) where
  equiv := Equiv.refl (Option s.inner.index)
  hom o := match o with
    | none => (FiniteTensor.singletonIso (V := C)).hom.app (unitObject C)
    | some i => (unitCoefficientTensorIso ((leafBlocks X s).obj i)).hom

/-- The original total input normalization collects all original
unit coefficients, performs their actual finite unit multiplication,
and removes the resulting actual input coefficient unit. -/
def totalInputNormalizer (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteTensor.tensor (V := C)).obj
      ((FiniteFamily.flatten (C := C)).obj (InputCopies.unitNestedFactors X s)) ⟶
        (FiniteTensor.tensor (V := C)).obj (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile) :=
  (InputCopies.unitSourceIso X s).hom ≫
    (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
      (emptyScalarTensorIso (InputCopies.unitCoefficients (C := C) s).index).hom ≫
    (unitCoefficientTensorIso (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).hom

/-- The original block input normalization removes each original
inner unit coefficient and the actual root unit, then flattens the
original evaluated input leaf blocks and their original total index. -/
def blockInputNormalizer (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteTensor.tensor (V := C)).obj
      ((FiniteFamily.flatten (C := C)).obj (InputCopies.unitNestedFactors X s)) ⟶
        (FiniteTensor.tensor (V := C)).obj (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile) :=
  (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s) ≫
    (FiniteTensor.tensor (V := C)).map (blockUnitCollapse X s) ≫
    (unitCoefficientTensorIso (evaluatedLeaves X s)).hom ≫
    (FiniteTensor.flattenIso (V := C)).inv.app (leafBlocks X s) ≫
    (FiniteTensor.tensor (V := C)).map (leafBlocksFlattenIso X s).hom




end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_OriginalUnitLeafBlocks

/- Source proof segment: UnitPartitionSetup -/
section source_UnitPartitionSetup
/-!
# Actual empty-coefficient refinement of original finite leaf blocks
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Every original finite input leaf block has an empty coefficient
source; its actual tensor is the genuine tensor unit. -/
def emptyBlockCoefficients (B : FiniteFamily (FiniteFamily C)) : FiniteFamily (FiniteFamily C) :=
  emptyScalarBlocks B.index

/-- Each original branch retains its actual unit coefficient and
all original leaf inputs on their unchanged indices. -/
def unitLeafBlocks (B : FiniteFamily (FiniteFamily C)) : FiniteFamily (FiniteFamily C) :=
  partitionedScalarLeaves (emptyBlockCoefficients B) B.obj (fun _ => unitObject C)

/-- The actual complete source of every original empty coefficient
and original singleton leaf refinement. -/
def expandedLeafBlocks (B : FiniteFamily (FiniteFamily C)) : FiniteFamily (FiniteFamily C) :=
  (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj
    (partitionedCoefficientLeavesTriple (emptyBlockCoefficients B) B.obj)

/-- Insert each actual original empty coefficient before its
original singleton leaf blocks, retaining every original leaf. -/
def leafBlockExpansionIso (B : FiniteFamily (FiniteFamily C)) : B ≅ expandedLeafBlocks B :=
  FiniteFamily.isoOfComponents (Equiv.refl B.index)
    (fun i => unitCoefficientFlattenIso (B.obj i))

/-- The original finite branch unit insertion map is the inverse
of its actual unit coefficient removal, on each original input block. -/
def branchUnitInsertion (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B ⟶
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (unitLeafBlocks B) where
  equiv := Equiv.refl B.index
  hom i := (unitCoefficientTensorIso (B.obj i)).inv

/-- The actual inverse finite branch unit removal map, retaining
every original evaluated leaf tensor. -/
def branchUnitRemoval (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (unitLeafBlocks B) ⟶
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B where
  equiv := Equiv.refl B.index
  hom i := (unitCoefficientTensorIso (B.obj i)).hom

/-- Original input branches and source partition leaf indices
are exactly the same original dependent sum of finite leaf types. -/
def partitionLeavesIso (B : FiniteFamily (FiniteFamily C)) :
    partitionedLeafFamily (emptyBlockCoefficients B) B.obj ≅
      (FiniteFamily.flatten (C := C)).obj B :=
  FiniteFamily.isoOfReindex (Equiv.refl _) (fun _ => rfl)

omit [FiniteTensor C] in
/-- Copy every original input leaf through its actual empty
coefficient refinement, source coefficient collection and original
empty-coefficient collapse; the original total input bijection results. -/
theorem leafExpansion_source_square (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.flatten (C := C)).map (leafBlockExpansionIso B).hom ≫
      (partitionedCoefficientLeavesSourceIso (emptyBlockCoefficients B) B.obj).hom ≫
      (FiniteFamily.flatten (C := C)).map
        (coefficientLeavesNestedMap (emptyScalarFlattenIso B.index).hom
          (𝟙 (partitionedLeafFamily (emptyBlockCoefficients B) B.obj))) =
    (partitionLeavesIso B).inv ≫
      (unitCoefficientFlattenIso (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    cases p with
    | mk i j => rfl
  · rintro ⟨i, j⟩
    with_unfolding_all
      let Z := (B.obj i).obj j
      change HEq (𝟙 Z ≫ 𝟙 Z ≫ 𝟙 Z) (((𝟙 Z) ≫ 𝟙 Z) ≫ 𝟙 Z)
      exact heq_of_eq (by simp only [Category.id_comp])

/-- The original branch empty coefficient refinement followed
by the existing exact branch normalizations is the original unit insertion. -/
theorem branchExpansion_normalization (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (leafBlockExpansionIso B).hom ≫
      partitionedCoefficientLeavesActionMap (emptyBlockCoefficients B) B.obj (fun _ => unitObject C)
        (fun _ => 𝟙 (unitObject C)) = branchUnitInsertion B := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    have h := unitCoefficientTensorIso_inv (B.obj i)
    with_unfolding_all
      change HEq
        ((FiniteTensor.tensor (V := C)).map (unitCoefficientFlattenIso (B.obj i)).hom ≫
          (coefficientLeavesNormalization FiniteFamily.empty (B.obj i) ≫
            (coefficientLeafTensorFunctor (B.obj i)).map (𝟙 (unitObject C))))
        (unitCoefficientTensorIso (B.obj i)).inv
      exact heq_of_eq ((congrArg (fun f => (FiniteTensor.tensor (V := C)).map
          (unitCoefficientFlattenIso (B.obj i)).hom ≫
            (coefficientLeavesNormalization FiniteFamily.empty (B.obj i) ≫ f))
          ((coefficientLeafTensorFunctor (B.obj i)).map_id (unitObject C))).trans
        ((congrArg (fun f => (FiniteTensor.tensor (V := C)).map
          (unitCoefficientFlattenIso (B.obj i)).hom ≫ f) (Category.comp_id _)).trans h.symm))




end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_UnitPartitionSetup

/- Source proof segment: UnitPartitionTriangle -/
section source_UnitPartitionTriangle
/-!
# Original finite unit coefficient partition triangles
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem emptyCoefficientTriangleFromSquares {V : Type*} [Category* V]
    {A B C D E F G : V} (p : A ⟶ B) (r : B ⟶ C) (n : C ⟶ D)
    (c : D ⟶ E) (u : E ⟶ F) (v : C ⟶ G) (w : F ⟶ G)
    (t : A ⟶ F) (n0 : G ⟶ E)
    (hn : n ≫ c = v ≫ n0) (hs : p ≫ (r ≫ v) = t ≫ w)
    (hu : w ≫ (n0 ≫ u) = 𝟙 F) : p ≫ (r ≫ (n ≫ (c ≫ u))) = t := by
  rw [← Category.assoc n c, hn, Category.assoc v n0,
    ← Category.assoc r v, ← Category.assoc p (r ≫ v), hs,
    Category.assoc t w, hu, Category.comp_id]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The actual identity branch coefficient map is the original
identity on the original finite family of tensor units. -/
theorem unitPartitionCoefficientMap_id (B : FiniteFamily (FiniteFamily C)) :
    partitionedCoefficientMap (emptyBlockCoefficients B) (fun _ => unitObject C)
      (fun _ => 𝟙 (unitObject C)) = 𝟙 (emptyScalarFamily (C := C) B.index) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    rfl

/-- Original branch coefficient flattening and actual unit
multiplication retain the actual original empty coefficient collapse. -/
theorem unitPartitionCoefficient_fold (B : FiniteFamily (FiniteFamily C)) :
    ((FiniteTensor.flattenIso (V := C)).hom.app (emptyBlockCoefficients B) ≫
        (FiniteTensor.tensor (V := C)).map
          (partitionedCoefficientMap (emptyBlockCoefficients B) (fun _ => unitObject C)
            (fun _ => 𝟙 (unitObject C)))) ≫ (emptyScalarTensorIso B.index).hom =
      (FiniteTensor.tensor (V := C)).map (emptyScalarFlattenIso B.index).hom := by
  have h := congrArg (FiniteTensor.tensor (V := C)).map (unitPartitionCoefficientMap_id (C := C) B)
  have hi : (FiniteTensor.tensor (V := C)).map
      (partitionedCoefficientMap (emptyBlockCoefficients B) (fun _ => unitObject C)
        (fun _ => 𝟙 (unitObject C))) = 𝟙 _ := h.trans ((FiniteTensor.tensor (V := C)).map_id _)
  exact (congrArg (fun m => ((FiniteTensor.flattenIso (V := C)).hom.app (emptyBlockCoefficients B) ≫ m) ≫
      (emptyScalarTensorIso B.index).hom) hi).trans
    ((congrArg (fun m => m ≫ (emptyScalarTensorIso B.index).hom) (Category.comp_id _)).trans
      (emptyScalarTensorIso_flatten B.index))

/-- The actual original empty coefficient source, collected after
all original leaf refinements, removes to the original total leaf
tensor. No terminal tensor-unit assumption is used. -/
theorem unitExpansion_collected_triangle (B : FiniteFamily (FiniteFamily C)) :
    (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (leafBlockExpansionIso B).hom) ≫
      (FiniteTensor.tensor (V := C)).map (partitionedCoefficientLeavesSourceIso (emptyBlockCoefficients B) B.obj).hom ≫
      coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj (emptyBlockCoefficients B))
        (partitionedLeafFamily (emptyBlockCoefficients B) B.obj) ≫
      (coefficientLeafTensorFunctor (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).map
        ((FiniteTensor.tensor (V := C)).map (emptyScalarFlattenIso B.index).hom) ≫
      (unitCoefficientTensorIso (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).hom =
        (FiniteTensor.tensor (V := C)).map (partitionLeavesIso B).inv := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let N := emptyBlockCoefficients B
  let L := partitionedLeafFamily N B.obj
  let k := (emptyScalarFlattenIso (C := C) B.index).hom
  let p := T.map (F.map (leafBlockExpansionIso B).hom)
  let r := T.map (partitionedCoefficientLeavesSourceIso N B.obj).hom
  let n := coefficientLeavesNormalization (F.obj N) L
  let c := (coefficientLeafTensorFunctor L).map (T.map k)
  let u := (unitCoefficientTensorIso L).hom
  let v := T.map (F.map (coefficientLeavesNestedMap k (𝟙 L)))
  let w := T.map (unitCoefficientFlattenIso L).hom
  let t := T.map (partitionLeavesIso B).inv
  let n0 := coefficientLeavesNormalization (FiniteFamily.empty : FiniteFamily C) L
  have hn : n ≫ c = v ≫ n0 := by
    have h := coefficientLeavesNormalization_naturality k (𝟙 L)
    rw [coefficientLeafMap_idLeaves] at h
    exact h.symm
  have hs : p ≫ (r ≫ v) = t ≫ w := by
    have h := congrArg T.map (leafExpansion_source_square (C := C) B)
    let a0 := F.map (leafBlockExpansionIso B).hom
    let b0 := (partitionedCoefficientLeavesSourceIso N B.obj).hom
    let c0 := F.map (coefficientLeavesNestedMap k (𝟙 L))
    have hsplit : T.map (a0 ≫ (b0 ≫ c0)) = p ≫ (r ≫ v) :=
      (T.map_comp a0 (b0 ≫ c0)).trans
        (congrArg (fun f => p ≫ f) (T.map_comp b0 c0))
    exact hsplit.symm.trans (h.trans (T.map_comp _ _))
  have hu : w ≫ (n0 ≫ u) = 𝟙 _ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun i => i ≫ u) (unitCoefficientTensorIso_inv L).symm).trans
        ((unitCoefficientTensorIso L).inv_hom_id))
  exact emptyCoefficientTriangleFromSquares p r n c u v w t n0 hn hs hu



end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_UnitPartitionTriangle

/- Source proof segment: UnitPartitionErasure -/
section source_UnitPartitionErasure
/-!
# Actual finite partition unit removal from source tensor coherence
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem unitTriangleFromAction {V : Type*} [Category* V]
    {A B C D E F G H : V} (q : A ⟶ B) (p : B ⟶ C) (n : C ⟶ D)
    (a : D ⟶ E) (m : E ⟶ F) (u : F ⟶ G) (a0 : B ⟶ H) (dist : H ⟶ E)
    (b0 : A ⟶ H) (c : D ⟶ F) (t : A ⟶ G)
    (ha : p ≫ (n ≫ a) = a0 ≫ dist) (hq : q ≫ a0 = b0)
    (hf : a ≫ m = c) (ht : q ≫ (p ≫ (n ≫ (c ≫ u))) = t) :
    b0 ≫ (dist ≫ (m ≫ u)) = t := by
  rw [← hq, Category.assoc q a0, ← Category.assoc a0 dist,
    ← ha, Category.assoc p (n ≫ a), Category.assoc n a,
    ← Category.assoc a m, hf]
  exact ht

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original refined leaf sources followed by the existing
branch normalizations assemble the actual original unit insertions. -/
theorem branchExpansion_tensor_normalization (B : FiniteFamily (FiniteFamily C)) :
    (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (leafBlockExpansionIso B).hom) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app (expandedLeafBlocks B) ≫
      (FiniteTensor.tensor (V := C)).map
        (partitionedCoefficientLeavesActionMap (emptyBlockCoefficients B) B.obj (fun _ => unitObject C)
          (fun _ => 𝟙 (unitObject C))) =
    (FiniteTensor.flattenIso (V := C)).hom.app B ≫
      (FiniteTensor.tensor (V := C)).map (branchUnitInsertion B) := by
  let T := FiniteTensor.tensor (V := C)
  let e := (leafBlockExpansionIso B).hom
  let m := partitionedCoefficientLeavesActionMap (emptyBlockCoefficients B) B.obj (fun _ => unitObject C)
    (fun _ => 𝟙 (unitObject C))
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality e
  have hm := congrArg T.map (branchExpansion_normalization (C := C) B)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ T.map m) hn).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => (FiniteTensor.flattenIso (V := C)).hom.app B ≫ f)
          ((T.map_comp _ _).symm.trans hm))))

/-- Each actual original branch unit insertion, original source
coefficient/leaf distribution, actual total unit multiplication and
actual final coefficient-unit removal form the original input triangle. -/
theorem unitPartition_insertion_triangle (B : FiniteFamily (FiniteFamily C)) :
    (FiniteTensor.flattenIso (V := C)).hom.app B ≫
      (FiniteTensor.tensor (V := C)).map (branchUnitInsertion B) ≫
      (partitionedScalarLeavesDistributionIso (emptyBlockCoefficients B) B.obj (fun _ => unitObject C)).hom ≫
      (coefficientLeafTensorFunctor (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).map
        (emptyScalarTensorIso B.index).hom ≫
      (unitCoefficientTensorIso (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).hom =
        (FiniteTensor.tensor (V := C)).map (partitionLeavesIso B).inv := by
  let T := FiniteTensor.tensor (V := C)
  let N := emptyBlockCoefficients B
  let L := partitionedLeafFamily N B.obj
  let F := coefficientLeafTensorFunctor L
  let q := T.map ((FiniteFamily.flatten (C := C)).map (leafBlockExpansionIso B).hom)
  let p := T.map (partitionedCoefficientLeavesSourceIso N B.obj).hom
  let n := coefficientLeavesNormalization ((FiniteFamily.flatten (C := C)).obj N) L
  let a := F.map ((FiniteTensor.flattenIso (V := C)).hom.app N ≫
    T.map (partitionedCoefficientMap N (fun _ => unitObject C) (fun _ => 𝟙 (unitObject C))))
  let m := F.map (emptyScalarTensorIso B.index).hom
  let u := (unitCoefficientTensorIso L).hom
  let a0 := (FiniteTensor.flattenIso (V := C)).hom.app (expandedLeafBlocks B) ≫
    T.map (partitionedCoefficientLeavesActionMap N B.obj (fun _ => unitObject C) (fun _ => 𝟙 (unitObject C)))
  let dist := (partitionedScalarLeavesDistributionIso N B.obj (fun _ => unitObject C)).hom
  let b0 := (FiniteTensor.flattenIso (V := C)).hom.app B ≫ T.map (branchUnitInsertion B)
  let c := F.map (T.map (emptyScalarFlattenIso B.index).hom)
  let t := T.map (partitionLeavesIso B).inv
  have ha : p ≫ (n ≫ a) = a0 ≫ dist :=
    (partitionedCoefficientLeaves_action N B.obj (fun _ => unitObject C) (fun _ => 𝟙 (unitObject C))).trans
      (Category.assoc _ _ _).symm
  have hq : q ≫ a0 = b0 := branchExpansion_tensor_normalization (C := C) B
  have hf : a ≫ m = c := (F.map_comp _ _).symm.trans
    (congrArg F.map (unitPartitionCoefficient_fold (C := C) B))
  have ht : q ≫ (p ≫ (n ≫ (c ≫ u))) = t := unitExpansion_collected_triangle (C := C) B
  exact (Category.assoc ((FiniteTensor.flattenIso (V := C)).hom.app B)
    (T.map (branchUnitInsertion B)) (dist ≫ (m ≫ u))).symm.trans
      (unitTriangleFromAction q p n a m u a0 dist b0 c t ha hq hf ht)



end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_UnitPartitionErasure

/- Source proof segment: UnitPartitionRemoval -/
section source_UnitPartitionRemoval
/-!
# Original finite branch unit removal and flattening
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original branch unit insertion and removal form an actual
finite-family isomorphism, componentwise by the original unit unitor. -/
def branchUnitIso (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B ≅
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (unitLeafBlocks B) :=
  FiniteFamily.isoOfComponents (Equiv.refl B.index)
    (fun i => (unitCoefficientTensorIso (B.obj i)).symm)

theorem branchUnitIso_hom (B : FiniteFamily (FiniteFamily C)) :
    (branchUnitIso B).hom = branchUnitInsertion B := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    rfl

theorem branchUnitIso_inv (B : FiniteFamily (FiniteFamily C)) :
    (branchUnitIso B).inv = branchUnitRemoval B := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    change HEq (eqToHom _ ≫ (unitCoefficientTensorIso (B.obj i)).hom)
      (unitCoefficientTensorIso (B.obj i)).hom
    exact eqToHom_comp_heq _ _

/-- Original branch units may be removed separately before the
original inner block flattening. This follows from the actual finite
partition unit triangle and its original branch isomorphisms. -/
theorem unitPartition_removal (B : FiniteFamily (FiniteFamily C)) :
    (partitionedScalarLeavesDistributionIso (emptyBlockCoefficients B) B.obj (fun _ => unitObject C)).hom ≫
      (coefficientLeafTensorFunctor (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).map
        (emptyScalarTensorIso B.index).hom ≫
      (unitCoefficientTensorIso (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).hom =
    (FiniteTensor.tensor (V := C)).map (branchUnitRemoval B) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app B ≫
      (FiniteTensor.tensor (V := C)).map (partitionLeavesIso B).inv := by
  let T := FiniteTensor.tensor (V := C)
  let e := (FiniteTensor.flattenIso (V := C)).app B ≪≫ T.mapIso (branchUnitIso B)
  let h := (partitionedScalarLeavesDistributionIso (emptyBlockCoefficients B) B.obj (fun _ => unitObject C)).hom ≫
    (coefficientLeafTensorFunctor (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).map
      (emptyScalarTensorIso B.index).hom ≫
    (unitCoefficientTensorIso (partitionedLeafFamily (emptyBlockCoefficients B) B.obj)).hom
  let t := T.map (partitionLeavesIso B).inv
  have ht : e.hom ≫ h = t := by
    change ((FiniteTensor.flattenIso (V := C)).hom.app B ≫ T.map (branchUnitIso B).hom) ≫ h = t
    rw [branchUnitIso_hom]
    exact (Category.assoc _ _ _).trans (unitPartition_insertion_triangle B)
  have hr : h = e.inv ≫ t := (Iso.eq_inv_comp e).mpr ht
  have hi : e.inv = T.map (branchUnitRemoval B) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app B := by
    simp only [e, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      branchUnitIso_inv]
  exact hr.trans ((congrArg (· ≫ t) hi).trans (Category.assoc _ _ _))



end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_UnitPartitionRemoval

/- Source proof segment: EmptyUnitLeafNormalization -/
section source_EmptyUnitLeafNormalization
/-!
# The actual nullary unit coefficient normalization
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

omit [FiniteTensor C] in
/-- The two displayed original empty-source identifications agree;
their carrier is empty and their source remains the original empty family. -/
theorem emptyUnit_source_identity :
    (unitCoefficientFlattenIso (FiniteFamily.empty : FiniteFamily C)).hom ≫
      (emptyLeafRawIso (FiniteFamily.empty : FiniteFamily C)).hom =
        𝟙 (FiniteFamily.empty : FiniteFamily C) := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i
  · intro i
    cases i

/-- With no original leaves, unit coefficient removal is the
actual singleton coefficient tensor unitor, with its original
empty-to-singleton index identification. -/
theorem unitCoefficientTensorIso_empty :
    (unitCoefficientTensorIso (FiniteFamily.empty : FiniteFamily C)).hom =
      (emptyLeafTensorIso (unitObject C)).hom := by
  let T := FiniteTensor.tensor (V := C)
  let e := unitCoefficientTensorIso (FiniteFamily.empty : FiniteFamily C)
  let n := coefficientLeavesNormalization FiniteFamily.empty (FiniteFamily.empty : FiniteFamily C)
  let p := T.map (unitCoefficientFlattenIso (FiniteFamily.empty : FiniteFamily C)).hom
  let q := T.map (emptyLeafRawIso (FiniteFamily.empty : FiniteFamily C)).hom
  let h := (emptyLeafTensorIso (unitObject C)).hom
  have hp : p ≫ q = 𝟙 (unitObject C) :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (emptyUnit_source_identity (C := C))).trans (T.map_id _))
  have hn : n ≫ h = q := coefficientLeavesNormalization_empty FiniteFamily.empty
  have he : e.inv = p ≫ n := unitCoefficientTensorIso_inv FiniteFamily.empty
  have hi : e.inv ≫ h = 𝟙 (unitObject C) :=
    (congrArg (· ≫ h) he).trans
      ((Category.assoc _ _ _).trans ((congrArg (p ≫ ·) hn).trans hp))
  exact (Category.comp_id e.hom).symm.trans ((Iso.inv_comp_eq e).mp hi).symm



end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_EmptyUnitLeafNormalization

/- Source proof segment: RootEmptyLeafBlocks -/
section source_RootEmptyLeafBlocks
/-!
# Original root empty block before a heterogeneous finite leaf partition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C]

/-- One original root empty leaf block followed by each original
heterogeneous inner input leaf block. -/
def rootEmptyBlocks (B : FiniteFamily (FiniteFamily C)) : FiniteFamily (FiniteFamily C) where
  index := FintypeCat.of (Option B.index)
  obj o := match o with
    | none => FiniteFamily.empty
    | some i => B.obj i

/-- The exact original leaf map inserts no root leaves and retains
all original inner dependent-sum leaves. -/
def rootEmptyInputEquiv (B : FiniteFamily (FiniteFamily C)) :
    ((FiniteFamily.flatten (C := C)).obj B).index ≃
      ((FiniteFamily.flatten (C := C)).obj (rootEmptyBlocks B)).index where
  toFun p := ⟨some p.1, p.2⟩
  invFun p := match p with
    | ⟨none, e⟩ => e.elim
    | ⟨some i, j⟩ => ⟨i, j⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨o, j⟩
    cases o with
    | none => cases j
    | some i => rfl

/-- Insert the empty root branch while retaining every original inner leaf of the flattened family. -/
def rootEmptyInputIso (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.flatten (C := C)).obj B ≅
      (FiniteFamily.flatten (C := C)).obj (rootEmptyBlocks B) :=
  FiniteFamily.isoOfReindex (rootEmptyInputEquiv B) (fun _ => rfl)

/-- The original root empty branch and original singleton inner
leaf blocks at the actual three-level source. -/
def rootEmptyTriple (B : FiniteFamily (FiniteFamily C)) :
    FiniteFamily (FiniteFamily (FiniteFamily C)) where
  index := FintypeCat.of (Option B.index)
  obj o := match o with
    | none => FiniteFamily.empty
    | some i => (FiniteFamily.singleton (C := FiniteFamily C)).obj (B.obj i)

/-- Local flattening of the actual root empty branch and original
singleton inner branches gives the original root-empty leaf partition. -/
def rootEmptyTripleFlattenIso (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj (rootEmptyTriple B) ≅
      rootEmptyBlocks B :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option B.index))
    (fun o => match o with
      | none => emptyNestedFlattenIso
      | some i => FiniteFamily.singletonFlattenIso.app (B.obj i))

/-- The full original inner branch partition is the actual
flattened triple's branch partition after discarding its empty root. -/
def rootEmptyTripleBlocksIso (B : FiniteFamily (FiniteFamily C)) :
    B ≅ (FiniteFamily.flatten (C := FiniteFamily C)).obj (rootEmptyTriple B) :=
  FiniteFamily.isoOfComponents
    { toFun i := ⟨some i, PUnit.unit⟩
      invFun p := match p with
        | ⟨none, e⟩ => e.elim
        | ⟨some i, _⟩ => i
      left_inv _ := rfl
      right_inv p := by
        rcases p with ⟨o, j⟩
        cases o with
        | none => cases j
        | some i => cases j; rfl }
    (fun _ => Iso.refl _)

/-- The original total leaf-source identification is exactly the
original block bijection, original dependent-sum associator and original
local empty/singleton index flattening. -/
theorem rootEmptyInput_source (B : FiniteFamily (FiniteFamily C)) :
    (rootEmptyInputIso B).hom =
      (FiniteFamily.flatten (C := C)).map (rootEmptyTripleBlocksIso B).hom ≫
        (FiniteFamily.flattenAssocIso (C := C)).inv.app (rootEmptyTriple B) ≫
        (FiniteFamily.flatten (C := C)).map (rootEmptyTripleFlattenIso B).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨i, j⟩
    rfl
  · rintro ⟨i, j⟩
    change HEq (𝟙 ((B.obj i).obj j))
      (𝟙 ((B.obj i).obj j) ≫ (𝟙 ((B.obj i).obj j) ≫ 𝟙 ((B.obj i).obj j)))
    exact heq_of_eq (by simp only [Category.id_comp])

variable [FiniteTensor C]

/-- The actual original evaluated root and leaf tensor family
is the original coefficient unit before evaluated original inner leaves. -/
def rootEvaluatedIso (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (rootEmptyBlocks B) ≅
      (coefficientLeafFamilyFunctor ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B)).obj
        (unitObject C) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option B.index))
    (fun o => match o with
      | none => Iso.refl _
      | some _ => Iso.refl _)

/-- Evaluate the empty-root triple at each inner tensor, retaining its empty coefficient and original leaves. -/
def rootEmptyTripleTensorIso (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.map (FiniteFamily.map (FiniteTensor.tensor (V := C)))).obj (rootEmptyTriple B) ≅
      coefficientLeavesNested FiniteFamily.empty
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option B.index))
    (fun o => match o with
      | none => FiniteFamily.mapEmptyIso (FiniteTensor.tensor (V := C))
      | some _ => Iso.refl _)

/-- The actual local root empty and inner singleton tensor collapses
retain exactly the original coefficient unit and inner leaf tensors. -/
theorem rootEmptyTriple_local_collapse (B : FiniteFamily (FiniteFamily C)) :
    (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app (rootEmptyTriple B) ≫
      (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (rootEmptyTripleTensorIso B).hom ≫
      coefficientLeavesCollapse FiniteFamily.empty
        ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B) =
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (rootEmptyTripleFlattenIso B).hom ≫
      (rootEvaluatedIso B).hom := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      change HEq
        ((FiniteTensor.flattenIso (V := C)).hom.app (FiniteFamily.empty : FiniteFamily (FiniteFamily C)) ≫
          (FiniteTensor.tensor (V := C)).map (FiniteFamily.mapEmptyIso (FiniteTensor.tensor (V := C))).hom ≫ 𝟙 _)
        ((FiniteTensor.tensor (V := C)).map (emptyNestedFlattenIso (C := C)).hom ≫ 𝟙 _)
      exact heq_of_eq ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ 𝟙 _) (flattenIso_empty_collapse (C := C))))
    | some i =>
      let T := FiniteTensor.tensor (V := C)
      let L := B.obj i
      let h := (FiniteTensor.flattenIso (V := C)).hom.app ((FiniteFamily.singleton (C := FiniteFamily C)).obj L)
      let u := (FiniteTensor.singletonIso (V := C)).hom.app (T.obj L)
      let r := T.map (FiniteFamily.singletonFlattenIso.hom.app L)
      have hu : h ≫ u = r := (singletonFlattenLaw_app L).symm
      change HEq (h ≫ T.map (𝟙 ((FiniteFamily.singleton (C := C)).obj (T.obj L))) ≫ u) (r ≫ 𝟙 _)
      exact heq_of_eq ((congrArg (fun f => h ≫ f ≫ u) (T.map_id _)).trans
        ((congrArg (h ≫ ·) (Category.id_comp u)).trans
          (hu.trans (Category.comp_id r).symm)))



end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_RootEmptyLeafBlocks

/- Source proof segment: RootUnitPartitionFlatten -/
section source_RootUnitPartitionFlatten
/-!
# Removing the actual root tensor unit commutes with original leaf-block flattening
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem rootPentagonCancel {V : Type*} [Category* V]
    {A B C D E : V} (a : A ⟶ B) (b : B ⟶ C) (r : D ⟶ A)
    (r' : A ⟶ D) (d : D ⟶ E) (e : E ⟶ C) (h : E ⟶ E)
    (hp : a ≫ b = r' ≫ (d ≫ (h ≫ e))) (hh : h = 𝟙 E)
    (hr : r ≫ r' = 𝟙 D) : r ≫ (a ≫ b) = d ≫ e := by
  rw [hp, hh, Category.id_comp, ← Category.assoc, hr, Category.id_comp]

private theorem rootCollapseFromSquares {V : Type*} [Category* V]
    {A B C D E F G H I J : V}
    (q : A ⟶ B) (r : B ⟶ C) (p : C ⟶ D) (z : D ⟶ E) (u : E ⟶ J)
    (a : C ⟶ F) (b : F ⟶ G) (c : G ⟶ J) (v : F ⟶ E)
    (d : B ⟶ H) (e : H ⟶ G) (j : H ⟶ I) (n : I ⟶ J)
    (f : A ⟶ I)
    (hp : p ≫ z = a ≫ v) (hc : b ≫ c = v ≫ u)
    (ha : r ≫ (a ≫ b) = d ≫ e) (he : j ≫ n = e ≫ c)
    (hq : q ≫ (d ≫ j) = f) :
    q ≫ (r ≫ (p ≫ (z ≫ u))) = f ≫ n := by
  rw [← Category.assoc p z, hp, Category.assoc a v,
    ← hc, ← Category.assoc a b, ← Category.assoc r,
    ha, Category.assoc d e, ← he, ← Category.assoc d j,
    ← Category.assoc q, hq]

private theorem rootInverseTriangle {V : Type*} [Category* V]
    {A B C : V} (e : A ≅ B) (k : A ≅ C) (d : B ⟶ C)
    (h : e.hom ≫ d = k.hom) : d ≫ k.inv = e.inv := by
  have he : d = e.inv ≫ k.hom := (Iso.eq_inv_comp e).mpr h
  rw [he, Category.assoc, k.hom_inv_id, Category.comp_id]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original root-empty partition flattening produces exactly
the original coefficient-unit insertion before the tensor of the original
evaluated inner leaf blocks. Every source index remains explicit. -/
theorem rootEmpty_flatten_triangle (B : FiniteFamily (FiniteFamily C)) :
    (FiniteTensor.tensor (V := C)).map (rootEmptyInputIso B).hom ≫
      (FiniteTensor.flattenIso (V := C)).hom.app (rootEmptyBlocks B) ≫
      (FiniteTensor.tensor (V := C)).map (rootEvaluatedIso B).hom =
    (FiniteTensor.flattenIso (V := C)).hom.app B ≫
      (unitCoefficientTensorIso ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B)).inv := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let M := rootEmptyTriple B
  let A := (FiniteFamily.map F).obj M
  let D := (FiniteFamily.flatten (C := FiniteFamily C)).obj M
  let E := (FiniteFamily.map (FiniteFamily.map T)).obj M
  let K := (FiniteFamily.map T).obj B
  let N := coefficientLeavesNested FiniteFamily.empty K
  let q := T.map (F.map (rootEmptyTripleBlocksIso B).hom)
  let r := T.map (FiniteFamily.flattenAssocIso.inv.app M)
  let p := T.map (F.map (rootEmptyTripleFlattenIso B).hom)
  let a := (FiniteTensor.flattenIso (V := C)).hom.app A
  let b := T.map ((FiniteFamily.mapIso (FiniteTensor.flattenIso (V := C))).hom.app M)
  let d := (FiniteTensor.flattenIso (V := C)).hom.app D
  let e := (FiniteTensor.flattenIso (V := C)).hom.app E
  let h := T.map ((FiniteFamily.flattenMapIso T).hom.app M)
  let c := T.map ((FiniteFamily.map T).map (rootEmptyTripleTensorIso B).hom ≫
    coefficientLeavesCollapse FiniteFamily.empty K)
  let u := T.map (rootEvaluatedIso B).hom
  let n := coefficientLeavesNormalization FiniteFamily.empty K
  let j := T.map (F.map (rootEmptyTripleTensorIso B).hom)
  let i := T.map (unitCoefficientFlattenIso K).hom
  let z := (FiniteTensor.flattenIso (V := C)).hom.app (rootEmptyBlocks B)
  have hh : h = 𝟙 _ := by
    change T.map (𝟙 _) = 𝟙 _
    exact T.map_id _
  have hpa := FiniteTensor.flattenAssocLaw_app_unfold M
  change a ≫ b = T.map (FiniteFamily.flattenAssocIso.hom.app M) ≫ d ≫ h ≫ e at hpa
  have ha : r ≫ (a ≫ b) = d ≫ e := by
    have hi : r ≫ T.map (FiniteFamily.flattenAssocIso.hom.app M) = 𝟙 _ :=
      (T.map_comp _ _).symm.trans
        ((congrArg T.map (FiniteFamily.flattenAssocIso.inv_hom_id_app M)).trans (T.map_id _))
    exact rootPentagonCancel a b r (T.map (FiniteFamily.flattenAssocIso.hom.app M)) d e h hpa hh hi
  have hc : b ≫ c = T.map ((FiniteFamily.map T).map (rootEmptyTripleFlattenIso B).hom) ≫ u := by
    have hh0 := congrArg T.map (rootEmptyTriple_local_collapse B)
    change T.map (_ ≫ (_ ≫ _)) = T.map (_ ≫ _) at hh0
    exact (T.map_comp _ _).symm.trans (hh0.trans (T.map_comp _ _))
  have hp := (FiniteTensor.flattenIso (V := C)).hom.naturality (rootEmptyTripleFlattenIso B).hom
  change p ≫ z = a ≫ T.map ((FiniteFamily.map T).map (rootEmptyTripleFlattenIso B).hom) at hp
  have hn := (FiniteTensor.flattenIso (V := C)).hom.naturality (rootEmptyTripleTensorIso B).hom
  change j ≫ (FiniteTensor.flattenIso (V := C)).hom.app N =
    e ≫ T.map ((FiniteFamily.map T).map (rootEmptyTripleTensorIso B).hom) at hn
  have he : j ≫ n = e ≫ c := by
    change j ≫ ((FiniteTensor.flattenIso (V := C)).hom.app N ≫ T.map (coefficientLeavesCollapse FiniteFamily.empty K)) =
      e ≫ c
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ T.map (coefficientLeavesCollapse FiniteFamily.empty K)) hn).trans
        ((Category.assoc _ _ _).trans
          (congrArg (e ≫ ·) (T.map_comp _ _).symm)))
  have hs : (FiniteTensor.tensor (V := C)).map (rootEmptyInputIso B).hom = q ≫ (r ≫ p) :=
    (congrArg T.map (rootEmptyInput_source B)).trans
      ((T.map_comp _ _).trans (congrArg (q ≫ ·) (T.map_comp _ _)))
  have hq := (FiniteTensor.flattenIso (V := C)).hom.naturality (rootEmptyTripleBlocksIso B).hom
  change q ≫ d = (FiniteTensor.flattenIso (V := C)).hom.app B ≫
    T.map ((FiniteFamily.map T).map (rootEmptyTripleBlocksIso B).hom) at hq
  have hsource : ((FiniteFamily.map T).map (rootEmptyTripleBlocksIso B).hom) ≫
      (F.map (rootEmptyTripleTensorIso B).hom) = (unitCoefficientFlattenIso K).hom := by
    apply FiniteFamily.Hom_ext
    · ext p
      rfl
    · intro p
      change HEq ((T.map (𝟙 (B.obj p))) ≫ 𝟙 (T.obj (B.obj p)))
        (𝟙 (T.obj (B.obj p)))
      exact heq_of_eq ((congrArg (· ≫ 𝟙 _) (T.map_id _)).trans (Category.id_comp _))
  have hqi : T.map ((FiniteFamily.map T).map (rootEmptyTripleBlocksIso B).hom) ≫ j = i :=
    (T.map_comp _ _).symm.trans (congrArg T.map hsource)
  have hi : i ≫ n = (unitCoefficientTensorIso K).inv := (unitCoefficientTensorIso_inv K).symm
  let f := (FiniteTensor.flattenIso (V := C)).hom.app B ≫ i
  have hqj : q ≫ (d ≫ j) = f :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ j) hq).trans
        ((Category.assoc _ _ _).trans
          (congrArg ((FiniteTensor.flattenIso (V := C)).hom.app B ≫ ·) hqi)))
  have hg := rootCollapseFromSquares q r p z u a b c
    (T.map ((FiniteFamily.map T).map (rootEmptyTripleFlattenIso B).hom)) d e j n f hp hc ha he hqj
  exact (congrArg (· ≫ (z ≫ u)) hs).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (q ≫ ·) (Category.assoc r p (z ≫ u))).trans
        (hg.trans ((Category.assoc _ _ _).trans
          (congrArg ((FiniteTensor.flattenIso (V := C)).hom.app B ≫ ·) hi)))))

/-- Actual original root unit removal followed by original input
block flattening is the inverse of the original root-empty leaf-source
insertion, through its displayed dependent-sum index identification. -/
theorem rootEmpty_unit_removal (B : FiniteFamily (FiniteFamily C)) :
    (FiniteTensor.flattenIso (V := C)).hom.app (rootEmptyBlocks B) ≫
      (FiniteTensor.tensor (V := C)).map (rootEvaluatedIso B).hom ≫
      (unitCoefficientTensorIso ((FiniteFamily.map (FiniteTensor.tensor (V := C))).obj B)).hom ≫
      (FiniteTensor.flattenIso (V := C)).inv.app B =
    (FiniteTensor.tensor (V := C)).map (rootEmptyInputIso B).inv := by
  let T := FiniteTensor.tensor (V := C)
  let e := T.mapIso (rootEmptyInputIso B)
  let k := (FiniteTensor.flattenIso (V := C)).app B ≪≫
    (unitCoefficientTensorIso ((FiniteFamily.map T).obj B)).symm
  let d := (FiniteTensor.flattenIso (V := C)).hom.app (rootEmptyBlocks B) ≫
    T.map (rootEvaluatedIso B).hom
  have h : e.hom ≫ d = k.hom := rootEmpty_flatten_triangle B
  have hr : d ≫ k.inv = e.inv := rootInverseTriangle e k d h
  exact (Category.assoc _ _ _).symm.trans hr




end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_RootUnitPartitionFlatten

/- Source proof segment: OriginalRootUnitPartition -/
section source_OriginalRootUnitPartition
/-!
# Original root singleton and inner unit coefficient/leaf partition identifications
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem originalRootMapCancel {V : Type*} [Category* V]
    {A B E : V} (e : A ≅ B) (u : B ⟶ E) (h : A ⟶ E)
    (hh : h = e.hom ≫ u) : e.inv ≫ (h ≫ 𝟙 E) = u := by
  rw [hh, Category.comp_id, ← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem originalInnerMapIdentity {V : Type*} [Category* V]
    {A B : V} (h : A ⟶ B) : 𝟙 A ≫ (h ≫ 𝟙 B) = h := by
  rw [Category.comp_id, Category.id_comp]

private theorem originalDoubleIdentity {V : Type*} [Category* V] (X : V) :
    𝟙 X ≫ 𝟙 X = 𝟙 X := Category.id_comp _

private theorem originalTripleRightIdentity {V : Type*} [Category* V] (X : V) :
    𝟙 X ≫ (𝟙 X ≫ 𝟙 X) = 𝟙 X := by
  rw [Category.id_comp, Category.id_comp]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Replace only the original root singleton by its displayed
empty-leaf coefficient family, retaining every original inner unit
coefficient and every original inner input leaf. -/
def originalUnitPartitionIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    InputCopies.unitNestedFactors X s ≅ unitLeafBlocks (rootEmptyBlocks (leafBlocks X s)) :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option s.inner.index))
    (fun o => match o with
      | none => (emptyLeafFamilyIso (unitObject C)).symm
      | some _ => Iso.refl _)

/-- The partition's original dependent-sum leaves discard no inner
input, and have exactly the original total profile's input family. -/
def originalPartitionLeavesIso (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    partitionedLeafFamily (emptyBlockCoefficients (rootEmptyBlocks (leafBlocks X s)))
      (rootEmptyBlocks (leafBlocks X s)).obj ≅
        profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile :=
  partitionLeavesIso (rootEmptyBlocks (leafBlocks X s)) ≪≫
    (rootEmptyInputIso (leafBlocks X s)).symm ≪≫ leafBlocksFlattenIso X s

/-- The original root singleton/inner unit factor map followed by
the original partition coefficient collection and original leaf map is
the original source substitution factor bijection. -/
theorem originalUnitPartition_source (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteFamily.flatten (C := C)).map (originalUnitPartitionIso X s).hom ≫
      (partitionedScalarLeavesIso
        (emptyBlockCoefficients (rootEmptyBlocks (leafBlocks X s)))
        (rootEmptyBlocks (leafBlocks X s)).obj (fun _ => unitObject C)).hom ≫
      (FiniteFamily.flatten (C := C)).map
        (coefficientLeavesNestedMap
          (𝟙 (InputCopies.unitCoefficients (C := C) s))
          (originalPartitionLeavesIso X s).hom) =
    (InputCopies.unitToLeavesIso X s).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    rcases p with ⟨o, j⟩
    cases o with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  · rintro ⟨o, j⟩
    cases o with
    | none =>
      cases j
      with_unfolding_all
        change HEq
          ((eqToHom _ ≫ 𝟙 (unitObject C)) ≫ 𝟙 (unitObject C) ≫ 𝟙 (unitObject C))
          (𝟙 (unitObject C))
        exact (heq_comp rfl rfl rfl (eqToHom_comp_heq _ _) (HEq.rfl : HEq (𝟙 (unitObject C) ≫ 𝟙 _) _)).trans
          (heq_of_eq (originalTripleRightIdentity _))
    | some i =>
      cases j with
      | none =>
        with_unfolding_all
          change HEq (𝟙 (unitObject C) ≫ 𝟙 (unitObject C) ≫ 𝟙 (unitObject C))
            (𝟙 (unitObject C))
          exact heq_of_eq (by simp only [Category.id_comp])
      | some j =>
        have hl : HEq ((originalPartitionLeavesIso X s).hom.hom ⟨some i, j⟩) (𝟙 X) := by
          with_unfolding_all
            change HEq ((𝟙 X) ≫ ((eqToHom _ ≫ 𝟙 X) ≫ 𝟙 X)) (𝟙 X)
            exact (heq_comp rfl rfl rfl (HEq.rfl : HEq (𝟙 X) _)
              (heq_comp rfl rfl rfl (eqToHom_comp_heq _ _) (HEq.rfl : HEq (𝟙 X) _))).trans
                (heq_of_eq (originalTripleRightIdentity X))
        with_unfolding_all
          change HEq (𝟙 X ≫ (𝟙 X ≫ (originalPartitionLeavesIso X s).hom.hom ⟨some i, j⟩)) (𝟙 X)
          exact (heq_comp rfl rfl rfl (HEq.rfl : HEq (𝟙 X) _)
            (heq_comp rfl rfl rfl (HEq.rfl : HEq (𝟙 X) _) hl)).trans
              (heq_of_eq ((Category.id_comp _).trans (originalDoubleIdentity X)))

/-- Original per-block root singleton and inner coefficient unit
removal equals the partition's branch unit removal followed by the
actual original evaluated coefficient-unit/leaf family identification. -/
theorem originalUnitPartition_collapse (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (originalUnitPartitionIso X s).hom ≫
      branchUnitRemoval (rootEmptyBlocks (leafBlocks X s)) ≫
      (rootEvaluatedIso (leafBlocks X s)).hom = blockUnitCollapse X s := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      let T := FiniteTensor.tensor (V := C)
      let E := unitObject C
      let e := T.mapIso (emptyLeafFamilyIso E)
      let u := (FiniteTensor.singletonIso (V := C)).hom.app E
      have h := unitCoefficientTensorIso_empty (C := C)
      have hh : (unitCoefficientTensorIso (FiniteFamily.empty : FiniteFamily C)).hom = e.hom ≫ u :=
        h.trans (emptyLeafTensorIso_hom E)
      with_unfolding_all
        change HEq (e.inv ≫ (unitCoefficientTensorIso (FiniteFamily.empty : FiniteFamily C)).hom ≫ 𝟙 E) u
        exact heq_of_eq (originalRootMapCancel e u _ hh)
    | some i =>
      let L := (leafBlocks X s).obj i
      let T := FiniteTensor.tensor (V := C)
      with_unfolding_all
        change HEq (T.map (𝟙 ((coefficientLeafFamilyFunctor L).obj (unitObject C))) ≫
          (unitCoefficientTensorIso L).hom ≫ 𝟙 (T.obj L)) (unitCoefficientTensorIso L).hom
        exact heq_of_eq ((congrArg (fun f => f ≫ (unitCoefficientTensorIso L).hom ≫ 𝟙 _) (T.map_id _)).trans
          (originalInnerMapIdentity _))




end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_OriginalRootUnitPartition

/- Source proof segment: CollectedUnitLeafNaturality -/
section source_CollectedUnitLeafNaturality
/-!
# Original leaf-map naturality of collected actual unit coefficients
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem collectedLeafNaturalityFromSquares {V : Type*} [Category* V]
    {A B C D E F G H : V}
    (r : A ⟶ B) (n' : B ⟶ C) (m' : C ⟶ D) (u' : D ⟶ E)
    (n : A ⟶ F) (f : F ⟶ C) (m : F ⟶ G) (g : G ⟶ D)
    (u : G ⟶ H) (l : H ⟶ E)
    (hn : r ≫ n' = n ≫ f) (hm : f ≫ m' = m ≫ g)
    (hu : g ≫ u' = u ≫ l) :
    r ≫ (n' ≫ (m' ≫ u')) = n ≫ (m ≫ (u ≫ l)) := by
  rw [← Category.assoc r n', hn, Category.assoc n f,
    ← Category.assoc f m', hm, Category.assoc m g, hu]

variable {C : Type u} [Category.{v} C]

/-- An original leaf input map commutes with the original
coefficient map, retaining all original coefficient and leaf indices. -/
theorem coefficientLeafInput_map_square {A E : C} {L M : FiniteFamily C}
    (f : A ⟶ E) (l : L ⟶ M) :
    coefficientLeafMap (𝟙 A) l ≫ (coefficientLeafFamilyFunctor M).map f =
      (coefficientLeafFamilyFunctor L).map f ≫ coefficientLeafMap (𝟙 E) l := by
  apply FiniteFamily.Hom_ext
  · ext o
    cases o <;> rfl
  · intro o
    cases o with
    | none => exact heq_of_eq ((Category.id_comp f).trans (Category.comp_id f).symm)
    | some i => exact heq_of_eq ((Category.comp_id (l.hom i)).trans (Category.id_comp (l.hom i)).symm)

variable [FiniteTensor C]

/-- The original collected unit coefficient normalization is
natural in every original finite leaf map, with the coefficient source
unchanged and actual all-unit scalar multiplication displayed. -/
theorem collectedUnit_leaf_naturality {K L M : FiniteFamily C}
    (f : (FiniteTensor.tensor (V := C)).obj K ⟶ unitObject C) (l : L ⟶ M) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (coefficientLeavesNestedMap (𝟙 K) l)) ≫
      coefficientLeavesNormalization K M ≫
      (coefficientLeafTensorFunctor M).map f ≫ (unitCoefficientTensorIso M).hom =
    coefficientLeavesNormalization K L ≫
      (coefficientLeafTensorFunctor L).map f ≫ (unitCoefficientTensorIso L).hom ≫
      (FiniteTensor.tensor (V := C)).map l := by
  let T := FiniteTensor.tensor (V := C)
  let r := T.map ((FiniteFamily.flatten (C := C)).map (coefficientLeavesNestedMap (𝟙 K) l))
  let n := coefficientLeavesNormalization K L
  let n' := coefficientLeavesNormalization K M
  let m := (coefficientLeafTensorFunctor L).map f
  let m' := (coefficientLeafTensorFunctor M).map f
  let u := (unitCoefficientTensorIso L).hom
  let u' := (unitCoefficientTensorIso M).hom
  let a := T.map (coefficientLeafMap (𝟙 (T.obj K)) l)
  let b := T.map (coefficientLeafMap (𝟙 (unitObject C)) l)
  have h0 := coefficientLeavesNormalization_naturality (𝟙 K) l
  have hn : r ≫ n' = n ≫ a := h0.trans
    (congrArg (n ≫ ·) (congrArg T.map
      (congrArg (fun h => coefficientLeafMap h l) (T.map_id K))))
  have hm : a ≫ m' = m ≫ b :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (coefficientLeafInput_map_square f l)).trans (T.map_comp _ _))
  have hu : b ≫ u' = u ≫ T.map l := unitCoefficientTensorIso_naturality l
  exact collectedLeafNaturalityFromSquares r n' m' u' n a m b u (T.map l) hn hm hu



end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_CollectedUnitLeafNaturality

/- Source proof segment: OriginalUnitCollectedNormalization -/
section source_OriginalUnitCollectedNormalization
/-!
# Original total unit/input normalization through its actual coefficient/leaf partition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem originalCollectFromSquares {V : Type*} [Category* V]
    {A B C D E F G H I J : V}
    (p : A ⟶ B) (q : B ⟶ C) (r : C ⟶ D) (n : D ⟶ E)
    (m : E ⟶ F) (u : F ⟶ G) (n' : C ⟶ H) (m' : H ⟶ I)
    (u' : I ⟶ J) (l : J ⟶ G)
    (hs : r ≫ (n ≫ (m ≫ u)) = n' ≫ (m' ≫ (u' ≫ l))) :
    p ≫ (q ≫ (r ≫ (n ≫ (m ≫ u)))) =
      p ≫ (q ≫ (n' ≫ (m' ≫ (u' ≫ l)))) := by
  rw [hs]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The original total unit normalizer is exactly the actual
root-singleton/inner-unit partition, its original scalar distribution,
all-unit multiplication, final coefficient-unit removal and unchanged
original total leaf map. -/
theorem totalInputNormalizer_partition (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    totalInputNormalizer X s =
      (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.flatten (C := C)).map (originalUnitPartitionIso X s).hom) ≫
        (FiniteTensor.flattenIso (V := C)).hom.app (unitLeafBlocks (rootEmptyBlocks (leafBlocks X s))) ≫
        (partitionedScalarLeavesDistributionIso
          (emptyBlockCoefficients (rootEmptyBlocks (leafBlocks X s)))
          (rootEmptyBlocks (leafBlocks X s)).obj (fun _ => unitObject C)).hom ≫
        (coefficientLeafTensorFunctor
          (partitionedLeafFamily (emptyBlockCoefficients (rootEmptyBlocks (leafBlocks X s)))
            (rootEmptyBlocks (leafBlocks X s)).obj)).map
          (emptyScalarTensorIso (InputCopies.unitCoefficients (C := C) s).index).hom ≫
        (unitCoefficientTensorIso
          (partitionedLeafFamily (emptyBlockCoefficients (rootEmptyBlocks (leafBlocks X s)))
            (rootEmptyBlocks (leafBlocks X s)).obj)).hom ≫
        (FiniteTensor.tensor (V := C)).map (originalPartitionLeavesIso X s).hom := by
  let T := FiniteTensor.tensor (V := C)
  let F := FiniteFamily.flatten (C := C)
  let B := rootEmptyBlocks (leafBlocks X s)
  let N := emptyBlockCoefficients B
  let L := partitionedLeafFamily N B.obj
  let M := profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile
  let K := InputCopies.unitCoefficients (C := C) s
  let p := T.map (F.map (originalUnitPartitionIso X s).hom)
  let q := T.map (partitionedScalarLeavesIso N B.obj (fun _ => unitObject C)).hom
  let r := T.map (F.map (coefficientLeavesNestedMap (𝟙 K) (originalPartitionLeavesIso X s).hom))
  let n := coefficientLeavesNormalization K M
  let m := (coefficientLeafTensorFunctor M).map (emptyScalarTensorIso K.index).hom
  let u := (unitCoefficientTensorIso M).hom
  let n' := coefficientLeavesNormalization K L
  let m' := (coefficientLeafTensorFunctor L).map (emptyScalarTensorIso K.index).hom
  let u' := (unitCoefficientTensorIso L).hom
  let l := T.map (originalPartitionLeavesIso X s).hom
  let a := (FiniteTensor.flattenIso (V := C)).hom.app (unitLeafBlocks B)
  let ai := (FiniteTensor.flattenIso (V := C)).inv.app (unitLeafBlocks B)
  let d := (partitionedScalarLeavesDistributionIso N B.obj (fun _ => unitObject C)).hom
  have hsource : T.map (InputCopies.unitToLeavesIso X s).hom = p ≫ (q ≫ r) :=
    (congrArg T.map (originalUnitPartition_source X s).symm).trans
      ((T.map_comp _ _).trans (congrArg (p ≫ ·) (T.map_comp _ _)))
  have hs : r ≫ (n ≫ (m ≫ u)) = n' ≫ (m' ≫ (u' ≫ l)) :=
    collectedUnit_leaf_naturality (emptyScalarTensorIso K.index).hom (originalPartitionLeavesIso X s).hom
  have hd : d = ai ≫ (q ≫ n') := partitionedScalarLeavesDistributionIso_hom N B.obj (fun _ => unitObject C)
  have ha : a ≫ d = q ≫ n' := by
    have hi : a ≫ ai = 𝟙 _ := (FiniteTensor.flattenIso (V := C)).hom_inv_id_app (unitLeafBlocks B)
    exact (congrArg (a ≫ ·) hd).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (q ≫ n')) hi).trans (Category.id_comp _)))
  have ht : totalInputNormalizer X s = p ≫ (q ≫ (r ≫ (n ≫ (m ≫ u)))) := by
    change ((T.map (InputCopies.unitToLeavesIso X s).hom ≫
      (coefficientLeavesNormalizationIso K M).hom) ≫ (m ≫ u)) = _
    exact (congrArg (fun f => (f ≫ (coefficientLeavesNormalizationIso K M).hom) ≫ (m ≫ u)) hsource).trans
      ((Category.assoc _ _ _).trans
        ((Category.assoc p (q ≫ r) _).trans
          ((congrArg (p ≫ ·) (Category.assoc q r _)).trans
            (congrArg (fun f => p ≫ (q ≫ (r ≫ (f ≫ (m ≫ u)))))
              (coefficientLeavesNormalizationIso_hom K M)))))
  have hm := originalCollectFromSquares p q r n m u n' m' u' l hs
  have hfinal : p ≫ (q ≫ (n' ≫ (m' ≫ (u' ≫ l)))) =
      p ≫ (a ≫ (d ≫ (m' ≫ (u' ≫ l)))) := by
    exact (congrArg (p ≫ ·) ((Category.assoc q n' _).symm.trans
      ((congrArg (· ≫ (m' ≫ (u' ≫ l))) ha.symm).trans (Category.assoc _ _ _))))
  exact ht.trans (hm.trans hfinal)



end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_OriginalUnitCollectedNormalization

/- Source proof segment: OriginalUnitInputNormalization -/
section source_OriginalUnitInputNormalization
/-!
# Equality of the two actual original operation unit/input normalizations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization

open CategoryTheory FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem originalUnitJoin {V : Type*} [Category* V]
    {A B C D E F G H I J K L N : V}
    (p : A ⟶ B) (a : B ⟶ C) (dist : C ⟶ D) (m : D ⟶ E) (u : E ⟶ F)
    (l : F ⟶ N) (r : C ⟶ G) (b : G ⟶ H) (j : H ⟶ F)
    (z : H ⟶ I) (w : I ⟶ N) (f : A ⟶ J) (g : J ⟶ C)
    (e : G ⟶ K) (v : K ⟶ L) (t : L ⟶ I) (c : J ⟶ K)
    (hrem : dist ≫ (m ≫ u) = r ≫ (b ≫ j))
    (hleaf : j ≫ l = z ≫ w) (hroot : b ≫ z = e ≫ (v ≫ t))
    (hn : p ≫ a = f ≫ g) (hc : g ≫ (r ≫ e) = c) :
    p ≫ (a ≫ (dist ≫ (m ≫ (u ≫ l)))) =
      f ≫ (c ≫ (v ≫ (t ≫ w))) := by
  rw [← Category.assoc m u l, ← Category.assoc dist (m ≫ u) l,
    hrem, Category.assoc r (b ≫ j) l, Category.assoc b j l, hleaf,
    ← Category.assoc b z, hroot]
  simp only [Category.assoc]
  rw [← Category.assoc p a, hn]
  simp only [Category.assoc]
  rw [← Category.assoc r e, ← Category.assoc g, hc]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- Collecting all original actual tensor-unit coefficients and
then removing their tensor unit agrees with removing each original
inner coefficient unit and the root singleton unit separately, then
flattening the original heterogeneous input leaf blocks. The original
total leaf-index identification remains explicit. -/
theorem totalInputNormalizer_eq_blockInputNormalizer
    (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    totalInputNormalizer X s = blockInputNormalizer X s := by
  let T := FiniteTensor.tensor (V := C)
  let B0 := leafBlocks X s
  let B := rootEmptyBlocks B0
  let N := emptyBlockCoefficients B
  let L := partitionedLeafFamily N B.obj
  let p := T.map ((FiniteFamily.flatten (C := C)).map (originalUnitPartitionIso X s).hom)
  let a := (FiniteTensor.flattenIso (V := C)).hom.app (unitLeafBlocks B)
  let dist := (partitionedScalarLeavesDistributionIso N B.obj (fun _ => unitObject C)).hom
  let m := (coefficientLeafTensorFunctor L).map (emptyScalarTensorIso (InputCopies.unitCoefficients (C := C)
    s).index).hom
  let u := (unitCoefficientTensorIso L).hom
  let l := T.map (originalPartitionLeavesIso X s).hom
  let r := T.map (branchUnitRemoval B)
  let b := (FiniteTensor.flattenIso (V := C)).inv.app B
  let j := T.map (partitionLeavesIso B).inv
  let z := T.map (rootEmptyInputIso B0).inv
  let w := T.map (leafBlocksFlattenIso X s).hom
  let f := (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s)
  let g := T.map ((FiniteFamily.map T).map (originalUnitPartitionIso X s).hom)
  let e := T.map (rootEvaluatedIso B0).hom
  let v := (unitCoefficientTensorIso ((FiniteFamily.map T).obj B0)).hom
  let t := (FiniteTensor.flattenIso (V := C)).inv.app B0
  let c := T.map (blockUnitCollapse X s)
  have hrem : dist ≫ (m ≫ u) = r ≫ (b ≫ j) := unitPartition_removal B
  have hleaf : j ≫ l = z ≫ w := by
    have hi : j ≫ T.map (partitionLeavesIso B).hom = 𝟙 _ :=
      (T.map_comp _ _).symm.trans
        ((congrArg T.map (partitionLeavesIso B).inv_hom_id).trans (T.map_id _))
    have hl : l = T.map (partitionLeavesIso B).hom ≫ (z ≫ w) :=
      (T.map_comp _ _).trans
        (congrArg (T.map (partitionLeavesIso B).hom ≫ ·) (T.map_comp _ _))
    exact (congrArg (j ≫ ·) hl).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (z ≫ w)) hi).trans (Category.id_comp _)))
  have hroot : b ≫ z = e ≫ (v ≫ t) := by
    let h := (FiniteTensor.flattenIso (V := C)).app B
    have hr : h.hom ≫ (e ≫ (v ≫ t)) = z := rootEmpty_unit_removal B0
    exact ((Iso.eq_inv_comp h).mpr hr).symm
  have hn : p ≫ a = f ≫ g :=
    (FiniteTensor.flattenIso (V := C)).hom.naturality (originalUnitPartitionIso X s).hom
  have hc : g ≫ (r ≫ e) = c := by
    let a0 := (FiniteFamily.map T).map (originalUnitPartitionIso X s).hom
    let b0 := branchUnitRemoval B
    let c0 := (rootEvaluatedIso B0).hom
    have hsplit : T.map (a0 ≫ (b0 ≫ c0)) = g ≫ (r ≫ e) :=
      (T.map_comp a0 (b0 ≫ c0)).trans (congrArg (g ≫ ·) (T.map_comp b0 c0))
    exact hsplit.symm.trans (congrArg T.map (originalUnitPartition_collapse X s))
  have ht := totalInputNormalizer_partition X s
  have hjoin := originalUnitJoin p a dist m u l r b j z w f g e v t c hrem hleaf hroot hn hc
  exact ht.trans hjoin

/-- Exact original source map equation for both actual unit
normalizations, including every finite original root and inner profile,
nullary and unary cases, and the unchanged dependent-sum leaf map. -/
theorem unitSourceIso_block_normalization
    (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (InputCopies.unitSourceIso X s).hom ≫
      (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
        (emptyScalarTensorIso (InputCopies.unitCoefficients (C := C) s).index).hom ≫
      (unitCoefficientTensorIso (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).hom =
    (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s) ≫
      (FiniteTensor.tensor (V := C)).map (blockUnitCollapse X s) ≫
      (unitCoefficientTensorIso (evaluatedLeaves X s)).hom ≫
      (FiniteTensor.flattenIso (V := C)).inv.app (leafBlocks X s) ≫
      (FiniteTensor.tensor (V := C)).map (leafBlocksFlattenIso X s).hom :=
  totalInputNormalizer_eq_blockInputNormalizer X s

omit [FiniteTensor C] in
/-- The displayed original total leaf identification is the
identity on the unchanged original dependent-sum input family. -/
theorem leafBlocksFlattenIso_hom_identity
    (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (leafBlocksFlattenIso X s).hom =
      𝟙 (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    rfl

/-- The exact source unit normalization equation on the original
total leaf carrier, with its unchanged final identity input map removed. -/
theorem unitSourceIso_block_normalization_original
    (X : C) (s : ColoredSubstitutionData PUnit.{1}) :
    (InputCopies.unitSourceIso X s).hom ≫
      (coefficientLeafTensorFunctor (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).map
        (emptyScalarTensorIso (InputCopies.unitCoefficients (C := C) s).index).hom ≫
      (unitCoefficientTensorIso (profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile)).hom =
    (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s) ≫
      (FiniteTensor.tensor (V := C)).map (blockUnitCollapse X s) ≫
      (unitCoefficientTensorIso (evaluatedLeaves X s)).hom ≫
      (FiniteTensor.flattenIso (V := C)).inv.app (leafBlocks X s) := by
  let T := FiniteTensor.tensor (V := C)
  let p := (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s)
  let q := T.map (blockUnitCollapse X s)
  let u := (unitCoefficientTensorIso (evaluatedLeaves X s)).hom
  let t := (FiniteTensor.flattenIso (V := C)).inv.app (leafBlocks X s)
  have hm : T.map (leafBlocksFlattenIso X s).hom = 𝟙 _ :=
    (congrArg T.map (leafBlocksFlattenIso_hom_identity X s)).trans (T.map_id _)
  exact (unitSourceIso_block_normalization X s).trans
    ((congrArg (fun f => p ≫ (q ≫ (u ≫ (t ≫ f)))) hm).trans
      (congrArg (fun f => p ≫ (q ≫ (u ≫ f))) (Category.comp_id t)))





end CategoryTheory.Operad.Tensor.Associative.UnitWordNormalization
end
end
end source_OriginalUnitInputNormalization

/- Source proof segment: ChosenAssembledFreeWordEvaluation -/
section source_ChosenAssembledFreeWordEvaluation
/-!
# The actual assembled free As operation reaches its chosen total word
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory TensorWord
open CategoryTheory.FiniteTensor.UnitCopower

private theorem assembledEvaluationFromOriginalCopy {V : Type*} [Category* V]
    {S D A B L Q : V} (e : S ≅ D) (assembled : S ⟶ A) (copy : D ⟶ A)
    (f : A ⟶ Q) (m : D ⟶ B) (u : B ⟶ L) (j : L ⟶ Q)
    (hi : e.inv ≫ assembled = copy) (hf : copy ≫ f = m ≫ (u ≫ j)) :
    assembled ≫ f = e.hom ≫ (m ≫ (u ≫ j)) := by
  apply (cancel_epi e.inv).1
  rw [← Category.assoc e.inv assembled, hi, hf, e.inv_hom_id_assoc]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen assembled free word evaluation construction. -/
local instance chosenAssembledFreeWordEvaluationFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- Every actual original root/inner coefficient and leaf copy
in the constructed free As operation reaches the original total
lexicographic word through the proved chosen strand map. -/
theorem chosenAssembledFreeWordEvaluation (X : C)
    (inner : FiniteFamily (ColoredProfile PUnit.{1}))
    (a : ∀ o : (associativeFactors.{us} (associativeUnitOutputSubstitution inner)).index,
      (associativeFactors.{us} (associativeUnitOutputSubstitution inner)).obj o) :
    InputCopies.assembledTensorInjection X (associativeUnitOutputSubstitution inner) a ≫
        freeOperation.{0, v, u, us} (associativeOperad C) (fun _ : PUnit.{1} => X)
          (profileInputs (associativeUnitOutputSubstitution inner).outerProfile) ≫
        (chosenAssociativeTensorWordsIso X).hom =
      UnitWordNormalization.totalInputNormalizer X (associativeUnitOutputSubstitution inner) ≫
        (chosenAssociativeOrderedPowerIso X
          (profileInputs (associativeUnitOutputSubstitution inner).totalProfile)
          (associativeLexicographic.{us} (associativeUnitOutputSubstitution inner) a)).hom ≫
        tensorWordι X (Nat.card (associativeUnitOutputSubstitution inner).totalProfile.inputs) := by
  let s := associativeUnitOutputSubstitution inner
  let L := profileLeafFamily (fun _ : PUnit.{1} => X) s.totalProfile
  let e := InputCopies.unitSourceIso X s
  let assembled := InputCopies.assembledTensorInjection X s a
  let copy := associativeOperationTensorInjection X s a
  let f := freeOperation.{0, v, u, us} (associativeOperad C) (fun _ : PUnit.{1} => X)
    (profileInputs s.outerProfile)
  let w := (chosenAssociativeTensorWordsIso X).hom
  let m := (coefficientLeafTensorFunctor L).map
    (emptyScalarTensorIso (C := C) (associativeFactors.{us} s).index).hom
  let c := associativeProfileCoefficientInjection X (profileInputs s.totalProfile)
    (associativeLexicographic.{us} s a)
  let q := profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X)
    (profileInputs s.totalProfile)
  let u := (unitCoefficientTensorIso L).hom
  let j := (chosenAssociativeOrderedPowerIso X (profileInputs s.totalProfile)
    (associativeLexicographic.{us} s a)).hom ≫ tensorWordι X (Nat.card s.totalProfile.inputs)
  have hi : e.inv ≫ assembled = copy := InputCopies.assembledTensorInjection_parentCopy X s a
  have hc : copy ≫ f = m ≫ (c ≫ q) :=
    associativeOperationTensorInjection_freeOperation X s a
  have hw : c ≫ (q ≫ w) = u ≫ j :=
    chosenAssociativeTensorWordsIso_coefficient X (profileInputs s.totalProfile)
      (associativeLexicographic.{us} s a)
  have hf : copy ≫ (f ≫ w) = m ≫ (u ≫ j) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ w) hc).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => m ≫ k) ((Category.assoc _ _ _).trans hw))))
  have hm : m = (coefficientLeafTensorFunctor L).map
      (emptyScalarTensorIso (C := C) (InputCopies.unitCoefficients (C := C) s).index).hom := by
    rfl
  have h := assembledEvaluationFromOriginalCopy e assembled copy (f ≫ w) m u j hi hf
  rw [hm] at h
  have hn : UnitWordNormalization.totalInputNormalizer X s =
      e.hom ≫ ((coefficientLeafTensorFunctor L).map
        (emptyScalarTensorIso (C := C) (InputCopies.unitCoefficients (C := C) s).index).hom ≫ u) := rfl
  change assembled ≫ (f ≫ w) = UnitWordNormalization.totalInputNormalizer X s ≫ j
  rw [hn]
  exact h.trans
    ((congrArg (e.hom ≫ ·) (Category.assoc
      ((coefficientLeafTensorFunctor L).map
        (emptyScalarTensorIso (C := C) (InputCopies.unitCoefficients (C := C) s).index).hom) u j).symm).trans
      (Category.assoc _ _ _).symm)



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenAssembledFreeWordEvaluation

/- Source proof segment: WordInputSlotColimits -/
section source_WordInputSlotColimits
/-!
# Actual original coefficient and word input colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

/-- The original coefficient slot and every original finite
input slot, unchanged from the coefficient/leaf tensor family. -/
def wordInputFactorIndex (I : FintypeCat.{0}) : FintypeCat.{0} := by
  letI : Finite I := I.property
  letI : Fintype I := Fintype.ofFinite I
  exact FintypeCat.of (Option I)

/-- The root coefficient has its actual singleton index and
every word input its original nonnegative degree index. -/
def wordInputSlotIndex (I : FintypeCat.{0}) : Option I → Type
  | none => Discrete PUnit.{1}
  | some _ => Discrete ℕ

/-- Every original factor degree index is the original discrete category. -/
@[instance_reducible]
def wordInputSlotCategory (I : FintypeCat.{0}) (o : Option I) :
    Category.{0} (wordInputSlotIndex I o) := by
  cases o
  · exact inferInstanceAs (Category (Discrete PUnit.{1}))
  · exact inferInstanceAs (Category (Discrete ℕ))

attribute [instance] wordInputSlotCategory

/-- The entire original coefficient/input index category family
is supplied from the actual named discrete slot categories. -/
@[instance_reducible]
def wordInputSlotCategories (I : FintypeCat.{0}) :
    ∀ o : Option I, Category.{0} (wordInputSlotIndex I o) := wordInputSlotCategory I

attribute [instance] wordInputSlotCategories

/-- The same original category family on the actual original
bundled finite coefficient/leaf index. -/
@[instance_reducible]
def wordInputFactorSlotCategories (I : FintypeCat.{0}) :
    ∀ o : wordInputFactorIndex I, Category.{0} (wordInputSlotIndex I o) :=
  fun o => wordInputSlotCategory I o

attribute [instance] wordInputFactorSlotCategories

/-- Every original root/word factor index is source-small,
derived from its actual singleton or degree type. -/
instance wordInputSlotEssentiallySmall (I : FintypeCat.{0}) (o : Option I) :
    EssentiallySmall.{us} (wordInputSlotIndex I o) := by
  cases o
  · exact inferInstanceAs (EssentiallySmall.{us} (Discrete PUnit.{1}))
  · exact inferInstanceAs (EssentiallySmall.{us} (Discrete ℕ))

/-- Original coefficient/word degree choices, retaining every original input. -/
abbrev WordInputSlotTuple (I : FintypeCat.{0}) := ∀ o : Option I, wordInputSlotIndex I o

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the word input slot colimits construction. -/
local instance wordInputSlotColimitsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : HasColimitsOfShape (Discrete ℕ) C := HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)

/-- The actual root coefficient has the original discrete
singleton constant diagram; the unit is not assumed terminal. -/
def wordInputRootDiagram : Discrete PUnit.{1} ⥤ C :=
  Discrete.functor (fun _ => FiniteTensor.UnitCopower.unitObject C)

/-- Its actual constant coefficient cocone has the original
coefficient as point and original identity injections. -/
def wordInputRootCocone : Cocone (wordInputRootDiagram (C := C)) :=
  Cofan.mk (FiniteTensor.UnitCopower.unitObject C) (fun _ => 𝟙 _)

/-- The original singleton coefficient cocone is colimiting by
its actual unique index and original identity maps, not terminality. -/
def wordInputRootIsColimit : IsColimit (wordInputRootCocone (C := C)) where
  desc s := s.ι.app (Discrete.mk PUnit.unit)
  fac s j := by
    cases j with
    | mk j => cases j; exact Category.id_comp _
  uniq s m h := (Category.id_comp m).symm.trans (h (Discrete.mk PUnit.unit))

/-- The original degree diagram of tensor powers for a word input. -/
def wordInputPowerDiagram (X : C) : Discrete ℕ ⥤ C :=
  Discrete.functor (fun n => TensorPower.tensorPowObj X n)

/-- The actual original word input coproduct cocone, with exactly
the original tensor-word object and original word degree injections. -/
def wordInputPowerCocone (X : C) : Cocone (wordInputPowerDiagram X) :=
  Cofan.mk (TensorWord.tensorWordObj X) (fun n => TensorWord.tensorWordι X n)

/-- The original word input degree cocone is actually colimiting,
using the original tensor-word coproduct universal property. -/
def wordInputPowerIsColimit (X : C) : IsColimit (wordInputPowerCocone X) :=
  coproductIsCoproduct (fun n => TensorPower.tensorPowObj X n)

/-- All actual original coefficient and word input diagrams,
with their unchanged root and every original finite input slot. -/
def wordInputSlotDiagram (X : C) (I : FintypeCat.{0}) :
    ∀ o : Option I, wordInputSlotIndex I o ⥤ C
  | none => wordInputRootDiagram
  | some _ => wordInputPowerDiagram X

/-- Every original coefficient/input cocone is the actual root
singleton cocone or original tensor-word degree coproduct cocone. -/
def wordInputSlotCocone (X : C) (I : FintypeCat.{0}) :
    ∀ o : Option I, Cocone (wordInputSlotDiagram X I o)
  | none => wordInputRootCocone
  | some _ => wordInputPowerCocone X

/-- Each original slot cocone is proved colimiting from its
actual root singleton or original word coproduct construction. -/
def wordInputSlotIsColimit (X : C) (I : FintypeCat.{0}) :
    ∀ o : Option I, IsColimit (wordInputSlotCocone X I o)
  | none => wordInputRootIsColimit
  | some _ => wordInputPowerIsColimit X




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_WordInputSlotColimits

/- Source proof segment: WordInputTensorCocone -/
section source_WordInputTensorCocone
/-!
# Actual original finite word-input tensor colimit cocone
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory Limits.FiniteMultifunctor

instance wordInputTupleCategory (I : FintypeCat.{0}) : Category.{0} (WordInputSlotTuple I) :=
  CategoryTheory.pi (fun o : Option I => wordInputSlotIndex I o)

/-- The original degree tuple corresponding to each original
input's word degree, with the actual singleton root coefficient index. -/
def wordInputDegreeTuple (I : FintypeCat.{0}) (m : I → ℕ) : WordInputSlotTuple I
  | none => Discrete.mk PUnit.unit
  | some i => Discrete.mk (m i)

/-- Read the original degree from every original input slot. -/
def wordInputDegrees (I : FintypeCat.{0}) (p : WordInputSlotTuple I) : I → ℕ :=
  fun i => (p (some i)).as

/-- Every original tensor-input index tuple is precisely its
original input degrees and actual singleton coefficient choice. -/
theorem wordInputDegreeTuple_degrees (I : FintypeCat.{0}) (p : WordInputSlotTuple I) :
    wordInputDegreeTuple I (wordInputDegrees I p) = p := by
  funext o
  cases o with
  | none =>
      apply Discrete.ext
      exact Subsingleton.elim _ _
  | some i => rfl

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the word input tensor cocone construction. -/
local instance wordInputTensorCoconeFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : HasColimitsOfShape (Discrete ℕ) C := HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)

/-- The actual original unit-coefficient tensor of word inputs,
with its unchanged original finite input type. -/
def wordInputTargetFactors (X : C) (I : FintypeCat.{0}) : FiniteFamily C :=
  (coefficientLeafFamilyFunctor (⟨I, fun _ => TensorWord.tensorWordObj X⟩ : FiniteFamily C)).obj
    (FiniteTensor.UnitCopower.unitObject C)

/-- The original source coefficient and each supplied original
word power, on the unchanged original coefficient/leaf input index. -/
def wordInputSourceFactors (X : C) (I : FintypeCat.{0}) (m : I → ℕ) : FiniteFamily C where
  index := wordInputFactorIndex I
  obj o := match o with
    | none => FiniteTensor.UnitCopower.unitObject C
    | some i => TensorPower.tensorPowObj X (m i)

/-- The original simultaneous word-degree tensor injection
factors, with root coefficient identity and every original input map. -/
def wordInputInjectionFactors (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    wordInputSourceFactors X I m ⟶ wordInputTargetFactors X I where
  equiv := Equiv.refl (Option I)
  hom o := match o with
    | none => 𝟙 (FiniteTensor.UnitCopower.unitObject C)
    | some i => TensorWord.tensorWordι X (m i)

/-- The ACTUAL original produced finite tensor map of the
original coefficient identity and word degree input injections.
No ordered identity enumeration replaces the original map. -/
def wordInputInjection (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteTensor.tensor (V := C)).obj (wordInputSourceFactors X I m) ⟶
      (FiniteTensor.tensor (V := C)).obj (wordInputTargetFactors X I) :=
  (FiniteTensor.tensor (V := C)).map (wordInputInjectionFactors X I m)

/-- The actual original simultaneous coefficient/word factor
diagram, followed by the original unchanged finite input tensor. -/
def wordInputTensorDiagram (X : C) (I : FintypeCat.{0}) : WordInputSlotTuple I ⥤ C :=
  finiteIndexDiagram (fixedIndexTensorFunctor (C := C) (wordInputFactorIndex I)) (wordInputSlotDiagram X I)

/-- Apply the original finite input tensor to the actual
original coefficient and word degree colimit cocones. -/
def wordInputGenericTensorCocone (X : C) (I : FintypeCat.{0}) : Cocone (wordInputTensorDiagram X I) :=
  finiteIndexCocone (fixedIndexTensorFunctor (C := C) (wordInputFactorIndex I)) (wordInputSlotCocone X I)

/-- The actual finite tensor of original slot cocones is colimiting,
from the source separate slot preservation and actual slot colimit proofs. -/
def wordInputGenericTensorIsColimit (X : C) (I : FintypeCat.{0}) :
    IsColimit (wordInputGenericTensorCocone X I) := by
  classical
  letI : ∀ o : wordInputFactorIndex I, EssentiallySmall.{us} (wordInputSlotIndex I o) :=
    fun o => wordInputSlotEssentiallySmall I o
  letI : Functor.PreservesColimitsInEachSlot.{0, u, v, u, v, us}
      (fixedIndexTensorFunctor (C := C) (wordInputFactorIndex I)) :=
    (FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C).preserves (wordInputFactorIndex I)
  exact isColimitFiniteIndexCocone (fixedIndexTensorFunctor (C := C) (wordInputFactorIndex I))
    (wordInputSlotIsColimit X I)

/-- The original coefficient and word-input colimit point factors
are precisely the original unit coefficient and original word leaves. -/
def wordInputPointFactorsIso (X : C) (I : FintypeCat.{0}) :
    (FiniteFamily.fixedIndexFunctor (C := C) (wordInputFactorIndex I)).obj
        (fun o => (wordInputSlotCocone X I o).pt) ≅ wordInputTargetFactors X I :=
  FiniteFamily.isoOfReindex (Equiv.refl (Option I)) (fun o => by cases o <;> rfl)

/-- The actual generic tensor colimit point has the exact
original coefficient/word tensor domain, with only identity factor maps. -/
def wordInputPointIso (X : C) (I : FintypeCat.{0}) :
    (wordInputGenericTensorCocone X I).pt ≅
      (FiniteTensor.tensor (V := C)).obj (wordInputTargetFactors X I) :=
  (FiniteTensor.tensor (V := C)).mapIso (wordInputPointFactorsIso X I)

/-- The actual original word-input tensor cocone has precisely
the required original coefficient/word tensor as its colimit point. -/
def wordInputTensorCocone (X : C) (I : FintypeCat.{0}) : Cocone (wordInputTensorDiagram X I) where
  pt := (FiniteTensor.tensor (V := C)).obj (wordInputTargetFactors X I)
  ι := (wordInputGenericTensorCocone X I).ι ≫ (Functor.const (WordInputSlotTuple I)).map (wordInputPointIso X I).hom

/-- The original input tensor cocone is the generic constructed
colimit cocone through the actual original identity-factor point comparison. -/
def wordInputTensorCoconeIso (X : C) (I : FintypeCat.{0}) :
    wordInputGenericTensorCocone X I ≅ wordInputTensorCocone X I :=
  Cocone.ext (wordInputPointIso X I) (fun _ => rfl)

/-- The required original unit-coefficient word input tensor
is actually the colimit of all original word degree tensor injections. -/
def wordInputTensorIsColimit (X : C) (I : FintypeCat.{0}) :
    IsColimit (wordInputTensorCocone X I) :=
  IsColimit.ofIsoColimit (wordInputGenericTensorIsColimit X I) (wordInputTensorCoconeIso X I)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_WordInputTensorCocone

/- Source proof segment: WordInputTensorHomExt -/
section source_WordInputTensorHomExt
/-!
# Original finite word-input injections determine tensor maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory Limits.FiniteMultifunctor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the word input tensor hom ext construction. -/
local instance wordInputTensorHomExtFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : HasColimitsOfShape (Discrete ℕ) C := HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)

/-- The actual original family of coefficient and power tensor
objects at an original degree tuple, with all original indices retained. -/
def wordInputDiagramFactors (X : C) (I : FintypeCat.{0}) (p : WordInputSlotTuple I) : FiniteFamily C :=
  (FiniteFamily.fixedIndexFunctor (C := C) (wordInputFactorIndex I)).obj
    (fun o => (wordInputSlotDiagram X I o).obj (p o))

/-- The original degree tuple source has precisely its original
coefficient and original power input factors, through identity factor maps. -/
def wordInputSourcePointIso (X : C) (I : FintypeCat.{0}) (p : WordInputSlotTuple I) :
    wordInputDiagramFactors X I p ≅ wordInputSourceFactors X I (wordInputDegrees I p) :=
  FiniteFamily.isoOfReindex (Equiv.refl (Option I)) (fun o => by cases o <;> rfl)

omit [MonoidalClosed C] in
/-- Every actual original tensor colimit factor injection is its
original coefficient identity or original word degree input injection. -/
theorem wordInputInjectionFactorComparison (X : C) (I : FintypeCat.{0}) (p : WordInputSlotTuple I) :
    (FiniteFamily.fixedIndexFunctor (C := C) (wordInputFactorIndex I)).map
        (fun o => (wordInputSlotCocone X I o).ι.app (p o)) ≫
      (wordInputPointFactorsIso X I).hom =
    (wordInputSourcePointIso X I p).hom ≫ wordInputInjectionFactors X I (wordInputDegrees I p) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        with_unfolding_all
          exact heq_of_eq (show (𝟙 _ ≫ 𝟙 _) = (𝟙 _ ≫ 𝟙 _) from rfl)
    | some i =>
        with_unfolding_all
          exact heq_of_eq ((Category.comp_id (TensorWord.tensorWordι X ((p (some i)).as))).trans
            (Category.id_comp (TensorWord.tensorWordι X ((p (some i)).as))).symm)

omit [MonoidalClosed C] in
/-- Every actual original tensor colimit injection is the ACTUAL
produced finite tensor of the named original coefficient/word factor
maps, preceded only by its original source identity-factor comparison. -/
@[reassoc]
theorem wordInputTensorCocone_ι (X : C) (I : FintypeCat.{0}) (p : WordInputSlotTuple I) :
    (wordInputTensorCocone X I).ι.app p =
      (FiniteTensor.tensor (V := C)).map (wordInputSourcePointIso X I p).hom ≫
        wordInputInjection X I (wordInputDegrees I p) :=
  ((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
    ((congrArg (FiniteTensor.tensor (V := C)).map (wordInputInjectionFactorComparison X I p)).trans
      ((FiniteTensor.tensor (V := C)).map_comp _ _))

/-- Original maps out of the actual unit-coefficient tensor of
word inputs are determined by EVERY original finite input degree
tuple and its ACTUAL original finite tensor word injection.
The colimit and each original root/input factor colimit are constructed
from source separate slot preservation; no such outcome is an input. -/
theorem wordInputTensor_hom_ext (X : C) (I : FintypeCat.{0}) {Z : C}
    {f g : (FiniteTensor.tensor (V := C)).obj (wordInputTargetFactors X I) ⟶ Z}
    (h : ∀ m : I → ℕ, wordInputInjection X I m ≫ f = wordInputInjection X I m ≫ g) : f = g := by
  apply (wordInputTensorIsColimit X I).hom_ext
  intro p
  have hm := congrArg (fun k => (FiniteTensor.tensor (V := C)).map (wordInputSourcePointIso X I p).hom ≫ k)
    (h (wordInputDegrees I p))
  exact (congrArg (fun k => k ≫ f) (wordInputTensorCocone_ι X I p)).trans
    ((Category.assoc _ _ _).trans
      (hm.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ g) (wordInputTensorCocone_ι X I p).symm))))

/-- The hom-ext statement has the EXACT original coefficient-leaf
tensor domain, with the original finite input index and tensor unit. -/
theorem wordInputCoefficientTensor_hom_ext (X : C) (I : FintypeCat.{0}) {Z : C}
    {f g : (FiniteTensor.tensor (V := C)).obj
      ((coefficientLeafFamilyFunctor (⟨I, fun _ => TensorWord.tensorWordObj X⟩ : FiniteFamily C)).obj
        (FiniteTensor.UnitCopower.unitObject C)) ⟶ Z}
    (h : ∀ m : I → ℕ,
      (FiniteTensor.tensor (V := C)).map (wordInputInjectionFactors X I m) ≫ f =
        (FiniteTensor.tensor (V := C)).map (wordInputInjectionFactors X I m) ≫ g) : f = g :=
  wordInputTensor_hom_ext X I h




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_WordInputTensorHomExt

/- Source proof segment: OrderedWordBlockData -/
section source_OrderedWordBlockData
/-!
# Original ordered finite blocks of homogeneous tensor words
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory MonoidalCategory TensorPower

/-- The total original word length, summed in the original order
of its finite blocks, including every empty block. -/
def orderedBlockLength : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, m => orderedBlockLength (fun i : Fin n => m i.castSucc) + m (Fin.last n)

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensor the original word-block powers in their original
finite order, with the actual tensor unit at zero blocks. -/
def orderedBlockTensor (X : C) : {n : ℕ} → (Fin n → ℕ) → C
  | 0, _ => 𝟙_ C
  | n + 1, m => orderedBlockTensor X (fun i : Fin n => m i.castSucc) ⊗ tensorPowObj X (m (Fin.last n))

/-- The actual canonical add-power flattening of every original
finite block sequence. No concatenation map is an input. -/
def orderedBlockPowerIso (X : C) : {n : ℕ} → (m : Fin n → ℕ) →
    tensorPowObj X (orderedBlockLength m) ≅ orderedBlockTensor X m
  | 0, _ => Iso.refl _
  | n + 1, m => tensorPowObj_add X (orderedBlockLength (fun i : Fin n => m i.castSucc)) (m (Fin.last n)) ≪≫
      tensorIso (orderedBlockPowerIso X (fun i : Fin n => m i.castSucc)) (Iso.refl _)

/-- The original binary ordered-tensor block data, preserving
each supplied finite block count, including zero input blocks. -/
def originalWordBlocks (X : C) : {n : ℕ} → (Fin n → ℕ) → OrderedTensor.Blocks C
  | 0, _ => .nil
  | n + 1, m => .snoc (originalWordBlocks X (fun i : Fin n => m i.castSucc))
      (fun _ : Fin (m (Fin.last n)) => X)

omit [Category.{v} C] [MonoidalCategory C] in
/-- The original ordered block data retain every original outer slot. -/
theorem originalWordBlocks_length (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    (originalWordBlocks X m).length = n
  | 0, _ => rfl
  | n + 1, m => congrArg (· + 1) (originalWordBlocks_length X (fun i : Fin n => m i.castSucc))

omit [Category.{v} C] [MonoidalCategory C] in
/-- The original flattened input count is the supplied ordered sum. -/
theorem originalWordBlocks_total (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    (originalWordBlocks X m).totalArity = orderedBlockLength m
  | 0, _ => rfl
  | n + 1, m => congrArg (· + m (Fin.last n))
      (originalWordBlocks_total X (fun i : Fin n => m i.castSucc))

omit [Category.{v} C] [MonoidalCategory C] in
/-- Every actual original flattened block input is the original
object, with the original empty input indices retained. -/
theorem originalWordBlocks_inputs (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ)
    (j : Fin (originalWordBlocks X m).totalArity), (originalWordBlocks X m).inputs j = X
  | 0, _, j => Fin.elim0 j
  | n + 1, m, j => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · exact (Fin.append_left _ _ i).trans
          (originalWordBlocks_inputs X (fun i : Fin n => m i.castSucc) i)
      · exact Fin.append_right _ _ i

/-- The actual original ordered block tensors are the supplied
binary tensor powers, with their original order retained. -/
theorem orderedBlockTensor_eq_ordered (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    orderedBlockTensor X m = OrderedTensor.obj (fun i : Fin n => tensorPowObj X (m i))
  | 0, _ => rfl
  | n + 1, m => congrArg (fun Y => Y ⊗ tensorPowObj X (m (Fin.last n)))
      (orderedBlockTensor_eq_ordered X (fun i : Fin n => m i.castSucc))

/-- The original block fold carrier equals the explicit ordered
word-block tensor, using the actual constant-power comparisons. -/
theorem originalWordBlocks_tensor (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    OrderedTensor.obj (originalWordBlocks X m).blockTensors = orderedBlockTensor X m
  | 0, _ => rfl
  | n + 1, m => by
      let B := originalWordBlocks X (fun i : Fin n => m i.castSucc)
      exact (OrderedTensor.Blocks.obj_blockTensors_snoc B (fun _ : Fin (m (Fin.last n)) => X)).trans
        (congrArg₂ (fun A B : C => A ⊗ B) (originalWordBlocks_tensor X (fun i : Fin n => m i.castSucc))
          (OrderedTensor.obj_constant X (m (Fin.last n))))

/-- The actual original flattened input carrier is its original
finite binary tensor power, with the original count equality retained. -/
theorem originalWordBlocks_inputTensor (X : C) {n : ℕ} (m : Fin n → ℕ) :
    OrderedTensor.obj (originalWordBlocks X m).inputs = tensorPowObj X (orderedBlockLength m) :=
  (congrArg OrderedTensor.obj (funext (originalWordBlocks_inputs X m))).trans
    ((OrderedTensor.obj_constant X _).trans (congrArg (tensorPowObj X) (originalWordBlocks_total X m)))

/-- The ACTUAL original ordered block flattening, on the original
power carriers, retaining both original source/target object comparisons. -/
def originalWordBlockPowerIso (X : C) {n : ℕ} (m : Fin n → ℕ) :
    tensorPowObj X (orderedBlockLength m) ≅ orderedBlockTensor X m :=
  (eqToIso (originalWordBlocks_inputTensor X m)).symm ≪≫
    OrderedTensor.Blocks.flattenIso (originalWordBlocks X m) ≪≫
      eqToIso (originalWordBlocks_tensor X m)



end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OrderedWordBlockData

/- Source proof segment: OrderedWordBlockPositions -/
section source_OrderedWordBlockPositions
/-!
# Original dependent-sum positions of ordered word blocks
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory MonoidalCategory

/-- Split the original last block from its original dependent
sum of input positions; all zero-length blocks are retained. -/
def blockSigmaLastEquiv {n : ℕ} (m : Fin (n + 1) → ℕ) :
    ((Σ i : Fin n, Fin (m i.castSucc)) ⊕ Fin (m (Fin.last n))) ≃
      (Σ i : Fin (n + 1), Fin (m i)) where
  toFun p := match p with
    | .inl p => ⟨p.1.castSucc, p.2⟩
    | .inr j => ⟨Fin.last n, j⟩
  invFun p := Fin.lastCases
    (motive := fun i => Fin (m i) → ((Σ i : Fin n, Fin (m i.castSucc)) ⊕ Fin (m (Fin.last n))))
    (fun j => .inr j) (fun i j => .inl ⟨i, j⟩) p.1 p.2
  left_inv p := by
    cases p with
    | inl p => simp only [Fin.lastCases_castSucc]
    | inr j => simp only [Fin.lastCases_last]
  right_inv p := by
    rcases p with ⟨i, j⟩
    revert j
    refine Fin.lastCases (fun j => ?_) (fun i j => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

omit [Category.{v} C] [MonoidalCategory C] in
/-- Every original block position is its original outer finite
slot and original inner finite word slot, including empty inputs. -/
def originalWordBlockPositions (X : C) : {n : ℕ} → (m : Fin n → ℕ) →
    (originalWordBlocks X m).position ≃ (Σ i : Fin n, Fin (m i))
  | 0, _ =>
      { toFun := Empty.elim
        invFun := fun p => Fin.elim0 p.1
        left_inv := fun p => Empty.elim p
        right_inv := fun p => Fin.elim0 p.1 }
  | n + 1, m => (Equiv.sumCongr
      (originalWordBlockPositions X (fun i : Fin n => m i.castSucc)) (Equiv.refl _)).trans
        (blockSigmaLastEquiv m)

omit [Category.{v} C] [MonoidalCategory C] in
/-- The original flattened finite word input is its exact
original dependent-sum block and inner input position. -/
def originalWordBlockInputEquiv (X : C) {n : ℕ} (m : Fin n → ℕ) :
    Fin (orderedBlockLength m) ≃ (Σ i : Fin n, Fin (m i)) :=
  (Fin.castOrderIso (originalWordBlocks_total X m).symm).toEquiv.trans
    ((originalWordBlocks X m).positionEquiv.trans (originalWordBlockPositions X m))

omit [Category.{v} C] [MonoidalCategory C] in
/-- The actual original dependent-sum index has exactly the
supplied total original block word length, including zero. -/
theorem originalWordBlockSigmaCard {n : ℕ} (m : Fin n → ℕ) :
    Nat.card (Σ i : Fin n, Fin (m i)) = orderedBlockLength m :=
  (Nat.card_congr (originalWordBlockInputEquiv (PUnit.unit : PUnit.{1}) m)).symm.trans (Nat.card_fin _)




end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OrderedWordBlockPositions

/- Source proof segment: OrderedWordSigmaEnumeration -/
section source_OrderedWordSigmaEnumeration
/-!
# Original increasing dependent-sum enumeration of finite word blocks
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory

/-- Original ordered append enumeration of the complete dependent
sum of the actual finite block input types, including empty blocks. -/
def orderedBlockPositionEquiv : {n : ℕ} → (m : Fin n → ℕ) →
    Fin (orderedBlockLength m) ≃ (Σ i : Fin n, Fin (m i))
  | 0, _ =>
      { toFun := Fin.elim0
        invFun := fun p => Fin.elim0 p.1
        left_inv := fun p => Fin.elim0 p
        right_inv := fun p => Fin.elim0 p.1 }
  | n + 1, m => finSumFinEquiv.symm.trans
      ((Equiv.sumCongr (orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)) (Equiv.refl _)).trans
        (blockSigmaLastEquiv m))

/-- Every original initial block position retains its original
outer and inner indices under the actual append enumeration. -/
@[simp]
theorem orderedBlockPositionEquiv_castAdd {n : ℕ} (m : Fin (n + 1) → ℕ)
    (j : Fin (orderedBlockLength (fun i : Fin n => m i.castSucc))) :
    orderedBlockPositionEquiv m (Fin.castAdd (m (Fin.last n)) j) =
      ⟨(orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc) j).1.castSucc,
        (orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc) j).2⟩ := by
  change (blockSigmaLastEquiv m)
      ((Equiv.sumCongr (orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)) (Equiv.refl _))
        (finSumFinEquiv.symm (Fin.castAdd (m (Fin.last n)) j))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- The original last block input retains its exact original
last outer slot and its original finite inner word input. -/
@[simp]
theorem orderedBlockPositionEquiv_natAdd {n : ℕ} (m : Fin (n + 1) → ℕ)
    (j : Fin (m (Fin.last n))) :
    orderedBlockPositionEquiv m (Fin.natAdd (orderedBlockLength (fun i : Fin n => m i.castSucc)) j) =
      ⟨Fin.last n, j⟩ := by
  change (blockSigmaLastEquiv m)
      ((Equiv.sumCongr (orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)) (Equiv.refl _))
        (finSumFinEquiv.symm (Fin.natAdd (orderedBlockLength (fun i : Fin n => m i.castSucc)) j))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl



end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OrderedWordSigmaEnumeration

/- Source proof segment: OrderedBlockOrderIso -/
section source_OrderedBlockOrderIso
/-!
# Original finite block position enumeration preserves the lexicographic order
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory

theorem ltOfTwoEqualities {N : ℕ} (a b c d : Fin N)
    (ha : a = c) (hb : b = d) (h : c < d) : a < b :=
  Eq.mpr (congrArg₂ (fun x y : Fin N => x < y) ha hb) h

/-- Original prefix positions under the inverse ordered block
enumeration retain the actual prefix word length. -/
theorem orderedBlockPositionEquiv_symm_prefix {n : ℕ} (m : Fin (n + 1) → ℕ)
    (i : Fin n) (j : Fin (m i.castSucc)) :
    (orderedBlockPositionEquiv m).symm ⟨i.castSucc, j⟩ =
      Fin.castAdd (m (Fin.last n))
        ((orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)).symm ⟨i, j⟩) := by
  apply (orderedBlockPositionEquiv m).injective
  rw [Equiv.apply_symm_apply, orderedBlockPositionEquiv_castAdd]
  exact congrArg (fun p : (Σ i : Fin n, Fin (m i.castSucc)) =>
    (⟨p.1.castSucc, p.2⟩ : Σ i : Fin (n + 1), Fin (m i)))
    ((orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)).apply_symm_apply ⟨i, j⟩).symm

/-- Original last-block positions retain their actual offset
under the inverse ordered block enumeration. -/
theorem orderedBlockPositionEquiv_symm_last {n : ℕ} (m : Fin (n + 1) → ℕ)
    (j : Fin (m (Fin.last n))) :
    (orderedBlockPositionEquiv m).symm ⟨Fin.last n, j⟩ =
      Fin.natAdd (orderedBlockLength (fun i : Fin n => m i.castSucc)) j := by
  apply (orderedBlockPositionEquiv m).injective
  rw [Equiv.apply_symm_apply, orderedBlockPositionEquiv_natAdd]

/-- The actual inverse original block-position enumeration is
strictly increasing for the original lexicographic input order. -/
theorem orderedBlockPositionEquiv_symm_strictMono : ∀ {n : ℕ} (m : Fin n → ℕ),
    StrictMono (fun p : (Σₗ i : Fin n, Fin (m i)) => (orderedBlockPositionEquiv m).symm p)
  | 0, _ => by rintro ⟨i, a⟩; exact i.elim0
  | n + 1, m => by
    let e := orderedBlockPositionEquiv m
    have hs : StrictMono (fun p : (Σₗ i : Fin (n + 1), Fin (m i)) => e.symm p) := by
      rintro ⟨i, a⟩ ⟨j, b⟩ h
      revert a b h
      refine Fin.lastCases (fun a => ?_) (fun i a => ?_) i
      · refine Fin.lastCases (fun b h => ?_) (fun j b h => ?_) j
        · have hab : a < b := by
            rcases (Sigma.Lex.lt_def.mp h) with hbad | ⟨heq, hinner⟩
            · exact False.elim ((lt_irrefl _) hbad)
            · exact hinner
          exact ltOfTwoEqualities _ _ _ _
            (orderedBlockPositionEquiv_symm_last m a) (orderedBlockPositionEquiv_symm_last m b)
            ((Fin.natAdd_lt_natAdd_iff _).mpr hab)
        · rcases (Sigma.Lex.lt_def.mp h) with hbad | ⟨heq, hinner⟩
          · exact False.elim (not_lt_of_ge (Fin.le_last _) hbad)
          · exact False.elim ((Fin.castSucc_lt_last j).ne heq.symm)
      · refine Fin.lastCases (fun b h => ?_) (fun j b h => ?_) j
        · have hc :
              Fin.castAdd (m (Fin.last n))
                ((orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)).symm ⟨i, a⟩) <
                Fin.natAdd (orderedBlockLength (fun i : Fin n => m i.castSucc)) b := by
            change ((orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)).symm ⟨i, a⟩).val <
              orderedBlockLength (fun i : Fin n => m i.castSucc) + b.val
            omega
          exact ltOfTwoEqualities _ _ _ _
            (orderedBlockPositionEquiv_symm_prefix m i a) (orderedBlockPositionEquiv_symm_last m b) hc
        · have hc :
              @LT.lt (Σₗ i : Fin n, Fin (m i.castSucc))
                (inferInstance : LinearOrder (Σₗ i : Fin n, Fin (m i.castSucc))).toLT ⟨i, a⟩ ⟨j, b⟩ := by
            rcases (Sigma.Lex.lt_def.mp h) with houter | ⟨heq, hinner⟩
            · exact @Sigma.Lex.left (Fin n) (fun i => Fin (m i.castSucc))
                (fun i j => i < j) (fun _ a b => a < b) i j a b
                (Fin.castSucc_lt_castSucc_iff.mp houter)
            · have hij : i = j := Fin.castSucc_injective _ heq
              cases hij
              have ht : a < b := by simpa only [eq_rec_constant] using hinner
              exact @Sigma.Lex.right (Fin n) (fun i => Fin (m i.castSucc))
                (fun i j => i < j) (fun _ a b => a < b) i a b ht
          have hd := Fin.strictMono_castAdd (m (Fin.last n))
            (orderedBlockPositionEquiv_symm_strictMono (fun i : Fin n => m i.castSucc) hc)
          exact ltOfTwoEqualities _ _ _ _
            (orderedBlockPositionEquiv_symm_prefix m i a) (orderedBlockPositionEquiv_symm_prefix m j b) hd
    exact hs

/-- The original increasing enumeration of all finite block
positions is an order isomorphism, including every empty block. -/
def orderedBlockPositionOrderIso {n : ℕ} (m : Fin n → ℕ) :
    Fin (orderedBlockLength m) ≃o (Σₗ i : Fin n, Fin (m i)) :=
  (StrictMono.orderIsoOfRightInverse
    (fun p : (Σₗ i : Fin n, Fin (m i)) => (orderedBlockPositionEquiv m).symm p)
    (orderedBlockPositionEquiv_symm_strictMono m) (orderedBlockPositionEquiv m)
    (orderedBlockPositionEquiv m).symm_apply_apply).symm

/-- The increasing order isomorphism uses exactly the original
recursive block position bijection. -/
theorem orderedBlockPositionOrderIso_toEquiv {n : ℕ} (m : Fin n → ℕ) :
    (orderedBlockPositionOrderIso m).toEquiv = orderedBlockPositionEquiv m := by
  apply Equiv.ext
  intro i
  rfl



end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OrderedBlockOrderIso

/- Source proof segment: OrderedWordConcatenation -/
section source_OrderedWordConcatenation
/-!
# Actual ordered simultaneous word injections evaluate by concatenation
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory Limits MonoidalCategory TensorPower

private theorem blockConcatenationStep {V : Type*} [Category* V] [MonoidalCategory V]
    {A B P U Z W : V} (f : A ⟶ P) (e : P ⟶ W) (j : B ⟶ W)
    (μ : W ⊗ W ⟶ W) (eval : P ⊗ W ⟶ W) (q : U ≅ A) (r : Z ≅ U ⊗ B)
    (i : U ⟶ W) (k : Z ⟶ W)
    (he : eval = (e ⊗ₘ 𝟙 W) ≫ μ) (hi : f ≫ e = q.inv ≫ i)
    (hm : (i ⊗ₘ j) ≫ μ = r.inv ≫ k) :
    (f ⊗ₘ j) ≫ eval = ((q.inv ⊗ₘ 𝟙 B) ≫ r.inv) ≫ k := by
  rw [he, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, hi]
  have ht : (q.inv ≫ i) ⊗ₘ j = (q.inv ⊗ₘ 𝟙 B) ≫ (i ⊗ₘ j) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht, Category.assoc, hm, ← Category.assoc]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

local instance : HasColimitsOfShape (Discrete ℕ) C := HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))

/-- Tensor the actual original word injection at every original
finite block slot. The empty list has the original unit identity map. -/
def orderedBlockInjection (X : C) : {n : ℕ} → (m : Fin n → ℕ) →
    orderedBlockTensor X m ⟶ tensorPowObj (tensorWordObj X) n
  | 0, _ => 𝟙 (𝟙_ C)
  | n + 1, m => orderedBlockInjection X (fun i : Fin n => m i.castSucc) ⊗ₘ
      tensorWordι X (m (Fin.last n))

/-- Actual finite evaluation on all original simultaneous word
injections concatenates the original ordered word blocks using the
constructed canonical add-power isomorphism. Empty blocks are retained. -/
theorem orderedBlockInjection_evaluation (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    orderedBlockInjection X m ≫ wordConcatenationEvaluation X n =
      (orderedBlockPowerIso X m).inv ≫ tensorWordι X (orderedBlockLength m)
  | 0, _ => by
      rw [wordConcatenationEvaluation_zero]
      rfl
  | n + 1, m => by
      let p := fun i : Fin n => m i.castSucc
      let k := m (Fin.last n)
      have hrec : wordConcatenationEvaluation X (n + 1) =
          (wordConcatenationEvaluation X n ⊗ₘ 𝟙 (tensorWordObj X)) ≫ tensorWordMul X :=
        finiteWordEvaluation_succ (tensorWordMon X) (𝟙 _) n
      have ih := orderedBlockInjection_evaluation X p
      have hinv : (orderedBlockPowerIso X m).inv =
          ((orderedBlockPowerIso X p).inv ⊗ₘ 𝟙 (tensorPowObj X k)) ≫
            (tensorPowObj_add X (orderedBlockLength p) k).inv := rfl
      have h := blockConcatenationStep (orderedBlockInjection X p) (wordConcatenationEvaluation X n)
        (tensorWordι X k) (tensorWordMul X) (wordConcatenationEvaluation X (n + 1))
        (orderedBlockPowerIso X p) (tensorPowObj_add X (orderedBlockLength p) k)
        (tensorWordι X (orderedBlockLength p)) (tensorWordι X (orderedBlockLength p + k))
        hrec ih (tensorWordMul_ι X (orderedBlockLength p) k)
      exact h.trans (congrArg (fun f => f ≫ tensorWordι X (orderedBlockLength p + k)) hinv.symm)

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The simultaneous original block injection is exactly the
actual ordered tensor map of the original word injections, before
transporting its original constant output family to the binary power. -/
theorem orderedBlockInjection_heq (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    HEq (orderedBlockInjection X m)
      (OrderedTensor.map (fun i : Fin n => tensorWordι X (m i)))
  | 0, _ => by
      change HEq (𝟙 (𝟙_ C)) (𝟙 (𝟙_ C))
      rfl
  | n + 1, m => by
      let p := fun i : Fin n => m i.castSucc
      change HEq (orderedBlockInjection X p ⊗ₘ tensorWordι X (m (Fin.last n)))
        (OrderedTensor.map (fun i : Fin n => tensorWordι X (p i)) ⊗ₘ tensorWordι X (m (Fin.last n)))
      exact OrderedTensor.tensorMapBoundary_heq
        (orderedBlockTensor_eq_ordered X p) (OrderedTensor.obj_constant (tensorWordObj X) n).symm
        rfl rfl (orderedBlockInjection_heq X p) HEq.rfl

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The actual source/target comparisons express the original
simultaneous block tensor injection on the binary power carriers. -/
theorem orderedBlockInjection_eq (X : C) {n : ℕ} (m : Fin n → ℕ) :
    orderedBlockInjection X m =
      eqToHom (orderedBlockTensor_eq_ordered X m) ≫
        OrderedTensor.map (fun i : Fin n => tensorWordι X (m i)) ≫
        eqToHom (OrderedTensor.obj_constant (tensorWordObj X) n) :=
  (conj_eqToHom_iff_heq _ _ (orderedBlockTensor_eq_ordered X m)
    (OrderedTensor.obj_constant (tensorWordObj X) n).symm).mpr (orderedBlockInjection_heq X m)




end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OrderedWordConcatenation

/- Source proof segment: ConstantOrderedAppend -/
section source_ConstantOrderedAppend
/-!
# Original constant-family append is the actual tensor-power add map
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorPower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private theorem rightUnitorInv_heq {A B : C} (h : A = B) :
    HEq (ρ_ A).inv (ρ_ B).inv := by
  cases h
  rfl

private theorem associatorHom_heq {A B D A' B' D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') :
    HEq (α_ A B D).hom (α_ A' B' D').hom := by
  cases hA
  cases hB
  cases hD
  rfl

private theorem tensorEqToHom {A B D E : C} (hA : A = B) (hD : D = E) :
    eqToHom hA ⊗ₘ eqToHom hD = eqToHom (congrArg₂ (fun X Y : C => X ⊗ Y) hA hD) := by
  cases hA
  cases hD
  simp only [eqToHom_refl, id_tensorHom_id]

omit [MonoidalCategory C] in
private theorem transportFromHEq {A B A' B' : C} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hf : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  cases hA
  cases hB
  have hfg : f = g := eq_of_heq hf
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hfg

omit [MonoidalCategory C] in
private theorem inverseFromHEq {A B A' B' : C} (hA : A = A') (hB : B = B')
    (e : A ≅ B) (e' : A' ≅ B') (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hA
  cases hB
  have he : e = e' := Iso.ext (eq_of_heq h)
  exact heq_of_eq (congrArg Iso.inv he)

omit [Category.{v} C] [MonoidalCategory C] in
/-- Appending the original two constant families gives the
original constant family on the original sum of their finite lengths. -/
theorem constantAppendFamilyEq (X : C) (m n : ℕ) :
    Fin.append (fun _ : Fin m => X) (fun _ : Fin n => X) = (fun _ : Fin (m + n) => X) := by
  funext i
  exact Fin.addCases (fun j => Fin.append_left _ _ j) (fun j => Fin.append_right _ _ j) i

/-- The actual original appended tensor carrier is its original
binary tensor power, through the original constant-family comparison. -/
theorem constantAppendObjEq (X : C) (m n : ℕ) :
    obj (Fin.append (fun _ : Fin m => X) (fun _ : Fin n => X)) = tensorPowObj X (m + n) :=
  (congrArg obj (constantAppendFamilyEq X m n)).trans (obj_constant X (m + n))

/-- The original ordered constant-family object comparison. -/
def constantPowerIso (X : C) (n : ℕ) : obj (fun _ : Fin n => X) ≅ tensorPowObj X n :=
  eqToIso (obj_constant X n)

/-- The original constant-family append carrier comparison. -/
def constantAppendFamilyIso (X : C) (m n : ℕ) :
    obj (Fin.append (fun _ : Fin m => X) (fun _ : Fin n => X)) ≅ obj (fun _ : Fin (m + n) => X) :=
  eqToIso (congrArg obj (constantAppendFamilyEq X m n))

/-- The actual original append map has the same recursively
constructed unitors and associators as the original tensor-power add map. -/
theorem constantAppend_hom_heq (X : C) (m : ℕ) : ∀ n : ℕ,
    HEq (appendIso (fun _ : Fin m => X) (fun _ : Fin n => X)).hom
      (tensorPowObj_add X m n).hom
  | 0 => by
      rw [appendIso_zero_hom, tensorPowObj_add_zero_right]
      exact (eqToHom_comp_heq _ _).trans (rightUnitorInv_heq (obj_constant X m))
  | n + 1 => by
      rw [appendIso_succ_hom]
      let hdom := constantAppendObjEq X m n
      let htarget := congrArg₂ (fun A B : C => A ⊗ B) (obj_constant X m) (obj_constant X n)
      have ht : HEq
          ((appendIso (fun _ : Fin m => X) (fun _ : Fin n => X)).hom ⊗ₘ 𝟙 X)
          ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) :=
        tensorMapBoundary_heq hdom htarget rfl rfl (constantAppend_hom_heq X m n) HEq.rfl
      have ha := associatorHom_heq (obj_constant X m) (obj_constant X n) (rfl : X = X)
      have hc : HEq
          (((appendIso (fun _ : Fin m => X) (fun _ : Fin n => X)).hom ⊗ₘ 𝟙 X) ≫
            (α_ (obj (fun _ : Fin m => X)) (obj (fun _ : Fin n => X)) X).hom)
          (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
            (α_ (tensorPowObj X m) (tensorPowObj X n) X).hom) :=
        heq_comp (congrArg (fun A : C => A ⊗ X) hdom)
          (congrArg (fun A : C => A ⊗ X) htarget)
          (congrArg₂ (fun A B : C => A ⊗ (B ⊗ X)) (obj_constant X m) (obj_constant X n)) ht ha
      exact (eqToHom_comp_heq _ _).trans hc

/-- The original append map, before the actual object comparisons,
is the tensor-power add map with the complete original endpoint transports. -/
theorem constantAppend_original_hom (X : C) (m n : ℕ) :
    (appendIso (fun _ : Fin m => X) (fun _ : Fin n => X)).hom =
      eqToHom (constantAppendObjEq X m n) ≫ (tensorPowObj_add X m n).hom ≫
        eqToHom (congrArg₂ (fun A B : C => A ⊗ B) (obj_constant X m) (obj_constant X n)).symm :=
  (conj_eqToHom_iff_heq _ _ (constantAppendObjEq X m n)
    (congrArg₂ (fun A B : C => A ⊗ B) (obj_constant X m) (obj_constant X n))).2
      (constantAppend_hom_heq X m n)

/-- The original inverse append map retains both actual endpoint
transports and the original inverse tensor-power add map. -/
theorem constantAppend_original_inv (X : C) (m n : ℕ) :
    (appendIso (fun _ : Fin m => X) (fun _ : Fin n => X)).inv =
      eqToHom (congrArg₂ (fun A B : C => A ⊗ B) (obj_constant X m) (obj_constant X n)) ≫
        (tensorPowObj_add X m n).inv ≫ eqToHom (constantAppendObjEq X m n).symm :=
  (conj_eqToHom_iff_heq _ _
    (congrArg₂ (fun A B : C => A ⊗ B) (obj_constant X m) (obj_constant X n))
    (constantAppendObjEq X m n)).2
    (inverseFromHEq (constantAppendObjEq X m n)
      (congrArg₂ (fun A B : C => A ⊗ B) (obj_constant X m) (obj_constant X n))
      (appendIso (fun _ : Fin m => X) (fun _ : Fin n => X)) (tensorPowObj_add X m n)
      (constantAppend_hom_heq X m n))

/-- The actual constant-family append comparison transports the
original append map through the original power object comparisons. -/
def constantAppendIso (X : C) (m n : ℕ) : tensorPowObj X (m + n) ≅ tensorPowObj X m ⊗ tensorPowObj X n :=
  (constantPowerIso X (m + n)).symm ≪≫
    (constantAppendFamilyIso X m n).symm ≪≫
      appendIso (fun _ : Fin m => X) (fun _ : Fin n => X) ≪≫
        tensorIso (constantPowerIso X m) (constantPowerIso X n)

/-- The full original append comparison is the existing actual
tensor-power add map, including all zero and one length cases. -/
theorem constantAppendIso_hom (X : C) (m n : ℕ) :
    (constantAppendIso X m n).hom = (tensorPowObj_add X m n).hom := by
  have h := transportFromHEq (constantAppendObjEq X m n)
    (congrArg₂ (fun A B : C => A ⊗ B) (obj_constant X m) (obj_constant X n))
    (appendIso (fun _ : Fin m => X) (fun _ : Fin n => X)).hom
    (tensorPowObj_add X m n).hom (constantAppend_hom_heq X m n)
  simpa only [constantAppendIso, constantPowerIso, constantAppendFamilyIso,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, tensorIso_hom,
    Category.assoc, tensorEqToHom, eqToHom_trans_assoc] using h

/-- The complete constant-family append isomorphism, with both
original inverse maps, is the original tensor-power add isomorphism. -/
theorem constantAppendIso_eq (X : C) (m n : ℕ) :
    constantAppendIso X m n = tensorPowObj_add X m n := Iso.ext (constantAppendIso_hom X m n)

/-- The exact constructed comparison has the actual original
inverse tensor-power add map. -/
theorem constantAppendIso_inv (X : C) (m n : ℕ) :
    (constantAppendIso X m n).inv = (tensorPowObj_add X m n).inv :=
  congrArg Iso.inv (constantAppendIso_eq X m n)




end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_ConstantOrderedAppend

/- Source proof segment: OriginalWordBlockFlatten -/
section source_OriginalWordBlockFlatten
/-!
# The actual original word-block flattening is the original power concatenation
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory MonoidalCategory TensorPower OrderedTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private theorem appendFamily_heq {m n : ℕ} (A B : Fin m → C) (D : Fin n → C)
    (h : A = B) : HEq (OrderedTensor.appendIso A D).hom (OrderedTensor.appendIso B D).hom := by
  cases h
  rfl

private theorem powerAddCount_heq (X : C) {a b : ℕ} (h : a = b) (n : ℕ) :
    HEq (tensorPowObj_add X a n).hom (tensorPowObj_add X b n).hom := by
  cases h
  rfl

omit [MonoidalCategory C] in
private theorem identityObject_heq {A B : C} (h : A = B) : HEq (𝟙 A) (𝟙 B) := by
  cases h
  rfl

/-- Appending one actual original homogeneous word block has
the original tensor-power add map, retaining the original prefix
inputs and actual original total-count equality. -/
theorem originalWordBlocks_append_heq (X : C) {n : ℕ} (m : Fin n → ℕ) (k : ℕ) :
    HEq (OrderedTensor.appendIso (originalWordBlocks X m).inputs (fun _ : Fin k => X)).hom
      (tensorPowObj_add X (orderedBlockLength m) k).hom :=
  (appendFamily_heq (originalWordBlocks X m).inputs
    (fun _ : Fin (originalWordBlocks X m).totalArity => X) (fun _ : Fin k => X)
    (funext (originalWordBlocks_inputs X m))).trans
    ((constantAppend_hom_heq X (originalWordBlocks X m).totalArity k).trans
      (powerAddCount_heq X (originalWordBlocks_total X m) k))

/-- The untransported ACTUAL original block flattening map has
exactly the recursively constructed add-power word map, with every
original outer and inner block and its empty input retained. -/
theorem originalWordBlocks_flatten_heq (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    HEq (OrderedTensor.Blocks.flattenIso (originalWordBlocks X m)).hom
      (orderedBlockPowerIso X m).hom
  | 0, _ => HEq.rfl
  | n + 1, m => by
      let mp : Fin n → ℕ := fun i => m i.castSucc
      let B := originalWordBlocks X mp
      let k := m (Fin.last n)
      let a := (OrderedTensor.appendIso B.inputs (fun _ : Fin k => X)).hom
      let b := (OrderedTensor.Blocks.flattenIso B).hom ⊗ₘ 𝟙 (OrderedTensor.obj (fun _ : Fin k => X))
      let a' := (tensorPowObj_add X (orderedBlockLength mp) k).hom
      let b' := (orderedBlockPowerIso X mp).hom ⊗ₘ 𝟙 (tensorPowObj X k)
      have ha : HEq a a' := originalWordBlocks_append_heq X mp k
      have hb : HEq b b' := tensorMapBoundary_heq
        (originalWordBlocks_inputTensor X mp) (originalWordBlocks_tensor X mp)
        (obj_constant X k) (obj_constant X k)
        (originalWordBlocks_flatten_heq X mp) (identityObject_heq (obj_constant X k))
      have hc : HEq (a ≫ b) (a' ≫ b') := heq_comp
        (originalWordBlocks_inputTensor X m)
        (congrArg₂ (fun A D : C => A ⊗ D) (originalWordBlocks_inputTensor X mp) (obj_constant X k))
        (congrArg₂ (fun A D : C => A ⊗ D) (originalWordBlocks_tensor X mp) (obj_constant X k)) ha hb
      have hs : (OrderedTensor.Blocks.flattenIso (originalWordBlocks X m)).hom =
          (a ≫ b) ≫ eqToHom (OrderedTensor.Blocks.obj_blockTensors_snoc B (fun _ : Fin k => X)).symm :=
        (OrderedTensor.Blocks.flattenIso_snoc_hom B (fun _ : Fin k => X)).trans (Category.assoc _ _ _).symm
      exact (heq_of_eq hs).trans ((comp_eqToHom_heq _ _).trans hc)

/-- The full normalized original word-block power isomorphism
is exactly the original recursive add-power isomorphism. Both maps
come from source monoidal data; no flattening outcome is a premise. -/
theorem originalWordBlockPowerIso_eq (X : C) {n : ℕ} (m : Fin n → ℕ) :
    originalWordBlockPowerIso X m = orderedBlockPowerIso X m := by
  apply Iso.ext
  have h := (conj_eqToHom_iff_heq
    (OrderedTensor.Blocks.flattenIso (originalWordBlocks X m)).hom
    (orderedBlockPowerIso X m).hom
    (originalWordBlocks_inputTensor X m) (originalWordBlocks_tensor X m)).2
      (originalWordBlocks_flatten_heq X m)
  simp only [originalWordBlockPowerIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The actual original flatten inverse is exactly the original
recursive finite word-concatenation power map. -/
theorem originalWordBlockPowerIso_inv (X : C) {n : ℕ} (m : Fin n → ℕ) :
    (originalWordBlockPowerIso X m).inv = (orderedBlockPowerIso X m).inv :=
  congrArg Iso.inv (originalWordBlockPowerIso_eq X m)




end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OriginalWordBlockFlatten

/- Source proof segment: OriginalOrderedWordConcatenation -/
section source_OriginalOrderedWordConcatenation
/-!
# Original ordered block flattening computes actual tensor-word evaluation
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory Limits MonoidalCategory TensorPower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

local instance : HasColimitsOfShape (Discrete ℕ) C := HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))

/-- Every original ordered tensor of original word injections
evaluates by the ACTUAL original block flattening inverse and its
original total-length word injection. No flatten outcome is assumed. -/
theorem orderedBlockInjection_originalEvaluation (X : C) {n : ℕ} (m : Fin n → ℕ) :
    orderedBlockInjection X m ≫ wordConcatenationEvaluation X n =
      (originalWordBlockPowerIso X m).inv ≫ tensorWordι X (orderedBlockLength m) :=
  (orderedBlockInjection_evaluation X m).trans
    (congrArg (fun f => f ≫ tensorWordι X (orderedBlockLength m))
      (originalWordBlockPowerIso_inv X m).symm)

/-- The actual ordered tensor map of the original component word
injections computes with the original block source and target object
comparisons, then actual original block flattening and total-word injection. -/
theorem orderedWordMap_originalEvaluation (X : C) {n : ℕ} (m : Fin n → ℕ) :
    OrderedTensor.map (fun i : Fin n => tensorWordι X (m i)) ≫
        eqToHom (OrderedTensor.obj_constant (tensorWordObj X) n) ≫
        wordConcatenationEvaluation X n =
      eqToHom (orderedBlockTensor_eq_ordered X m).symm ≫
        (originalWordBlockPowerIso X m).inv ≫ tensorWordι X (orderedBlockLength m) := by
  let e := eqToIso (orderedBlockTensor_eq_ordered X m)
  have hi := orderedBlockInjection_eq X m
  have h := orderedBlockInjection_originalEvaluation X m
  have h' : e.hom ≫ (OrderedTensor.map (fun i : Fin n => tensorWordι X (m i)) ≫
      eqToHom (OrderedTensor.obj_constant (tensorWordObj X) n) ≫ wordConcatenationEvaluation X n) =
    (originalWordBlockPowerIso X m).inv ≫ tensorWordι X (orderedBlockLength m) := by
    simpa only [e, eqToIso.hom, Category.assoc] using
      ((congrArg (fun f => f ≫ wordConcatenationEvaluation X n) hi.symm).trans h)
  exact e.eq_inv_comp.mpr h'




end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_OriginalOrderedWordConcatenation

/- Source proof segment: FiniteWordEnumerationReadbacks -/
section source_FiniteWordEnumerationReadbacks
/-!
# The actual original finite tensor word enumeration is retained

No chosen enumeration of a `Fin n` input is assumed increasing.
The original fixed-index word map is expressed through its actual
enumerated component maps. A graded correction records the original
chosen finite enumeration as a genuine tensor permutation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory Limits MonoidalCategory TensorPower

attribute [local instance] FintypeCat.fintype

/-- The original finite input enumeration, independent of object
values and with the original bundled finite-type instance retained. -/
def originalFiniteInputEnumeration (I : FintypeCat.{0}) : Fin (Fintype.card I) ≃ I :=
  (Fintype.equivFin I).symm

/-- The original ordered block lengths under the ACTUAL original
finite enumeration. This does not replace the enumeration by identity. -/
def originalEnumeratedBlockLengths (I : FintypeCat.{0}) (m : I → ℕ) : Fin (Fintype.card I) → ℕ :=
  fun i => m (originalFiniteInputEnumeration I i)

/-- The actual finite tensor generator copies use the original
input slots before every original input enumeration and tensor map. -/
def originalFiniteBlockFamily {C : Type u} (X : C) (I : FintypeCat.{0}) (m : I → ℕ)
    [Category.{v} C] [MonoidalCategory C] : FiniteFamily C :=
  ⟨I, fun i => tensorPowObj X (m i)⟩

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

local instance : HasColimitsOfShape (Discrete ℕ) C := HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))

/-- The actual unchanged-index finite tensor of original block
word injections, through the original produced finite tensor functor. -/
def originalFiniteWordMap (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    OrderedTensor.finiteTensorFunctor.obj (originalFiniteBlockFamily X I m) ⟶
      OrderedTensor.finiteTensorFunctor.obj (⟨I, fun _ => tensorWordObj X⟩ : FiniteFamily C) :=
  OrderedTensor.finiteTensorFunctor.map
    (OrderedTensor.fixedIndexHom I (fun i => tensorWordι X (m i)))

/-- The original target finite tensor is its original binary
power, with the actual chosen finite count retained. -/
def originalFiniteWordTargetIso (X : C) (I : FintypeCat.{0}) :
    OrderedTensor.finiteTensorFunctor.obj (⟨I, fun _ => tensorWordObj X⟩ : FiniteFamily C) ≅
      tensorPowObj (tensorWordObj X) (Fintype.card I) :=
  eqToIso (OrderedTensor.obj_constant (tensorWordObj X) (Fintype.card I))

/-- The original source finite tensor is the tensor of its
original block powers in its ACTUAL chosen finite enumeration. -/
def originalFiniteWordSourceIso (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    OrderedTensor.finiteTensorFunctor.obj (originalFiniteBlockFamily X I m) ≅
      orderedBlockTensor X (originalEnumeratedBlockLengths I m) :=
  (eqToIso (orderedBlockTensor_eq_ordered X (originalEnumeratedBlockLengths I m))).symm

omit [MonoidalClosed C] in
/-- Exact original produced map readback: each original word
injection appears at its ACTUAL original finite enumeration position. -/
theorem originalFiniteWordMap_eq (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    originalFiniteWordMap X I m =
      OrderedTensor.map (fun i : Fin (Fintype.card I) =>
        tensorWordι X (originalEnumeratedBlockLengths I m i)) :=
  OrderedTensor.finiteTensorFunctor_map_fixedIndex I (fun i => tensorWordι X (m i))

/-- The original finite tensor word injections evaluate using
their ACTUAL original enumerated block order, the ACTUAL original
block flatten inverse and original total-word injection. -/
theorem originalFiniteWordMap_evaluation (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    originalFiniteWordMap X I m ≫ (originalFiniteWordTargetIso X I).hom ≫
        wordConcatenationEvaluation X (Fintype.card I) =
      (originalFiniteWordSourceIso X I m).hom ≫
        (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv ≫
        tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m)) :=
  (congrArg (fun f => f ≫ (originalFiniteWordTargetIso X I).hom ≫
      wordConcatenationEvaluation X (Fintype.card I)) (originalFiniteWordMap_eq X I m)).trans
    (orderedWordMap_originalEvaluation X (originalEnumeratedBlockLengths I m))

/-- The exact original flattened dependent-sum input positions,
with the ACTUAL original outer finite enumeration retained. -/
def originalFiniteWordInputEquiv (I : FintypeCat.{0}) (m : I → ℕ) :
    Fin (orderedBlockLength (originalEnumeratedBlockLengths I m)) ≃ (Σ i : I, Fin (m i)) :=
  (orderedBlockPositionEquiv (originalEnumeratedBlockLengths I m)).trans
    (Equiv.sigmaCongrLeft (β := fun i : I => Fin (m i)) (originalFiniteInputEnumeration I))

/-- The chosen original enumeration of a canonical original
`Fin n` input, including its actual finite cardinal comparison. -/
def originalFinInputPermutation (n : ℕ) : Equiv.Perm (Fin n) := by
  let I : FintypeCat.{0} := FintypeCat.of (Fin n)
  let h : @Fintype.card I (@FintypeCat.fintype I) = n :=
    (@Fintype.card_congr (Fin n) (Fin n) (@FintypeCat.fintype I)
      (inferInstance : Fintype (Fin n)) (Equiv.refl _)).trans (Fintype.card_fin n)
  exact (finCongr h.symm).trans (originalFiniteInputEnumeration I)

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual strand permutation on a homogeneous binary power,
through its original ordered tensor object comparisons. -/
def degreeStrandPermutation (X : C) (n : ℕ) (p : Equiv.Perm (Fin n)) :
    tensorPowObj X n ≅ tensorPowObj X n :=
  (OrderedTensor.constantPowerIso X n).symm ≪≫
    OrderedTensor.permutationIso p (fun _ : Fin n => X) ≪≫
      OrderedTensor.constantPowerIso X n

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The original finite word degree correction retains the actual
chosen original `Fin n` input permutation. No identity is assumed. -/
def degreeStrandCorrection (X : C) (n : ℕ) : tensorPowObj X n ≅ tensorPowObj X n :=
  degreeStrandPermutation X n (originalFinInputPermutation n)




end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_FiniteWordEnumerationReadbacks

/- Source proof segment: ChosenFinOrderIso -/
section source_ChosenFinOrderIso
/-!
# Exact source finite enumeration is increasing for the chosen canonical order
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative.OrderedProfile

open CategoryTheory CategoryTheory.MonoidalCategory.TensorWord

/-- The actual source permutation of canonical Fin n inputs is
an increasing bijection into the exact chosen source operation order. -/
def chosenFinOrderIso (n : ℕ) :
    @OrderIso (Fin n) (Fin n) (inferInstance : LinearOrder (Fin n)).toLE
      (chosenCanonical n).order.toLE where
  toEquiv := originalFinInputPermutation n
  map_rel_iff' := by
    intro a b
    change (chosenRank n) (originalFinInputPermutation n a) ≤
      (chosenRank n) (originalFinInputPermutation n b) ↔ a ≤ b
    have ha : ((chosenRank n) (originalFinInputPermutation n a)).val = a.val := by
      unfold chosenRank originalFinInputPermutation originalFiniteInputEnumeration
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    have hb : ((chosenRank n) (originalFinInputPermutation n b)).val = b.val := by
      unfold chosenRank originalFinInputPermutation originalFiniteInputEnumeration
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    change ((chosenRank n) (originalFinInputPermutation n a)).val ≤
      ((chosenRank n) (originalFinInputPermutation n b)).val ↔ a.val ≤ b.val
    have he := congrArg₂ (fun x y : ℕ => x ≤ y) ha hb
    exact ⟨fun h => Eq.mp he h, fun h => Eq.mpr he h⟩



end CategoryTheory.Operad.Tensor.Associative.OrderedProfile
end
end
end source_ChosenFinOrderIso

/- Source proof segment: ChosenLexicographicInput -/
section source_ChosenLexicographicInput
/-!
# Original outer and inner strand maps enumerate the chosen lexicographic inputs
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative.OrderedProfile

open CategoryTheory CategoryTheory.MonoidalCategory.TensorWord

attribute [local instance] FintypeCat.fintype

/-- The original source order on an arbitrary finite outer input
type is pulled back along its actual Fintype.equivFin rank map. -/
@[instance_reducible]
def chosenOuterOrder (I : FintypeCat.{0}) : LinearOrder I := by
  classical
  exact (Fintype.equivFin I).linearOrder

/-- The actual original finite input enumeration is increasing
for that actual source chosen outer input order. -/
def chosenOuterOrderIso (I : FintypeCat.{0}) :
    @OrderIso (Fin (Fintype.card I)) I
      (inferInstance : LinearOrder (Fin (Fintype.card I))).toLE (chosenOuterOrder I).toLE where
  toEquiv := originalFiniteInputEnumeration I
  map_rel_iff' := by
    intro a b
    change (Fintype.equivFin I) ((originalFiniteInputEnumeration I) a) ≤
      (Fintype.equivFin I) ((originalFiniteInputEnumeration I) b) ↔ a ≤ b
    unfold originalFiniteInputEnumeration
    exact ⟨fun h => by simpa only [Equiv.apply_symm_apply] using h,
      fun h => by simpa only [Equiv.apply_symm_apply] using h⟩

/-- The actual source lexicographic order on all original inner
word inputs, with the actual chosen outer and inner strand orders. -/
@[instance_reducible]
def chosenLexicographicOrder (I : FintypeCat.{0}) (m : I → ℕ) :
    LinearOrder (Σ i : I, Fin (m i)) := by
  let : LinearOrder I := chosenOuterOrder I
  let : ∀ i : I, LinearOrder (Fin (m i)) := fun i => (chosenCanonical (m i)).order
  exact (inferInstance : LinearOrder (Σₗ i : I, Fin (m i)))

/-- The original source block bijection followed by every actual
inner source permutation; no input enumeration is replaced by identity. -/
def chosenLexicographicInputEquiv (I : FintypeCat.{0}) (m : I → ℕ) :
    Fin (orderedBlockLength (originalEnumeratedBlockLengths I m)) ≃ (Σ i : I, Fin (m i)) :=
  (originalFiniteWordInputEquiv I m).trans
    (Equiv.sigmaCongrRight (fun i => originalFinInputPermutation (m i)))

/-- The actual outer and inner source maps preserve the original
lexicographic order of finite word block positions. -/
def chosenLexicographicSigmaIso (I : FintypeCat.{0}) (m : I → ℕ) :
    @OrderIso (Σₗ i : Fin (Fintype.card I), Fin (originalEnumeratedBlockLengths I m i))
      (Σ i : I, Fin (m i))
      (inferInstance : LinearOrder
        (Σₗ i : Fin (Fintype.card I), Fin (originalEnumeratedBlockLengths I m i))).toLE
      (chosenLexicographicOrder I m).toLE := by
  let : LinearOrder I := chosenOuterOrder I
  let : ∀ i : I, LinearOrder (Fin (m i)) := fun i => (chosenCanonical (m i)).order
  let e := originalFiniteInputEnumeration I
  let g := (Equiv.sigmaCongrLeft (β := fun i : I => Fin (m i)) e).trans
    (Equiv.sigmaCongrRight (fun i => originalFinInputPermutation (m i)))
  refine { toEquiv := g, map_rel_iff' := ?_ }
  rintro ⟨i, a⟩ ⟨j, b⟩
  change Sigma.Lex (fun i j : I => @LT.lt I (chosenOuterOrder I).toLT i j)
      (fun i a b => @LE.le (Fin (m i)) (chosenCanonical (m i)).order.toLE a b)
      ⟨e i, originalFinInputPermutation (m (e i)) a⟩
      ⟨e j, originalFinInputPermutation (m (e j)) b⟩ ↔
    @Sigma.Lex (Fin (Fintype.card I)) (fun i => Fin (originalEnumeratedBlockLengths I m i))
      (fun i j => i < j) (fun _ a b => a ≤ b) ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · cases hij
    have hn :
        @LE.le (Fin (m (e i))) (chosenCanonical (m (e i))).order.toLE
          (originalFinInputPermutation (m (e i)) a) (originalFinInputPermutation (m (e i)) b) ↔
        @LE.le (Fin (m (e i))) (Fin.instLinearOrder).toLE a b :=
      (chosenFinOrderIso (m (e i))).map_rel_iff' (a := a) (b := b)
    constructor
    · intro h
      rcases Sigma.lex_iff.mp h with hout | ⟨heq, hin⟩
      · exact False.elim ((lt_irrefl (e i)) hout)
      · have hh : @LE.le (Fin (m (e i))) (chosenCanonical (m (e i))).order.toLE
            (originalFinInputPermutation (m (e i)) a) (originalFinInputPermutation (m (e i)) b) := by
          simpa only [eq_rec_constant] using hin
        exact @Sigma.Lex.right (Fin (Fintype.card I))
          (fun i => Fin (originalEnumeratedBlockLengths I m i))
          (fun i j => i < j) (fun _ a b => a ≤ b) i a b (hn.mp hh)
    · intro h
      rcases Sigma.lex_iff.mp h with hout | ⟨heq, hin⟩
      · exact False.elim ((lt_irrefl i) hout)
      · have hh : @LE.le (Fin (m (e i))) (Fin.instLinearOrder).toLE a b := by
          change a.val ≤ b.val
          have ht : @LE.le (Fin (originalEnumeratedBlockLengths I m i)) instLEFin a b := by
            simpa only [eq_rec_constant] using hin
          exact ht
        exact @Sigma.Lex.right I (fun i => Fin (m i))
          (fun i j => @LT.lt I (chosenOuterOrder I).toLT i j)
          (fun i a b => @LE.le (Fin (m i)) (chosenCanonical (m i)).order.toLE a b)
          (e i) _ _ (hn.mpr hh)
  · have he : e i ≠ e j := fun h => hij (e.injective h)
    have hn : @LT.lt I (chosenOuterOrder I).toLT (e i) (e j) ↔ i < j :=
      (chosenOuterOrderIso I).lt_iff_lt
    constructor
    · intro h
      rcases Sigma.lex_iff.mp h with hout | ⟨heq, hin⟩
      · exact @Sigma.Lex.left (Fin (Fintype.card I))
          (fun i => Fin (originalEnumeratedBlockLengths I m i))
          (fun i j => i < j) (fun _ a b => a ≤ b) i j a b (hn.mp hout)
      · exact False.elim (he heq)
    · intro h
      rcases Sigma.lex_iff.mp h with hout | ⟨heq, hin⟩
      · exact @Sigma.Lex.left I (fun i => Fin (m i))
          (fun i j => @LT.lt I (chosenOuterOrder I).toLT i j)
          (fun i a b => @LE.le (Fin (m i)) (chosenCanonical (m i)).order.toLE a b)
          (e i) (e j) _ _ (hn.mpr hout)
      · exact False.elim (hij heq)

/-- The full original source chosen lexicographic input map is
an increasing enumeration of every actual word block input. -/
def chosenLexicographicInputOrderIso (I : FintypeCat.{0}) (m : I → ℕ) :
    @OrderIso (Fin (orderedBlockLength (originalEnumeratedBlockLengths I m)))
      (Σ i : I, Fin (m i))
      (inferInstance : LinearOrder (Fin (orderedBlockLength (originalEnumeratedBlockLengths I m)))).toLE
      (chosenLexicographicOrder I m).toLE :=
  @OrderIso.trans _ _ _
    (inferInstance : LinearOrder (Fin (orderedBlockLength (originalEnumeratedBlockLengths I m)))).toLE
    (inferInstance : LinearOrder
      (Σₗ i : Fin (Fintype.card I), Fin (originalEnumeratedBlockLengths I m i))).toLE
    (chosenLexicographicOrder I m).toLE
    (orderedBlockPositionOrderIso (originalEnumeratedBlockLengths I m)) (chosenLexicographicSigmaIso I m)

/-- Its underlying map is exactly the original block input map
followed by the actual original inner strand permutations. -/
theorem chosenLexicographicInputOrderIso_toEquiv (I : FintypeCat.{0}) (m : I → ℕ) :
    (chosenLexicographicInputOrderIso I m).toEquiv = chosenLexicographicInputEquiv I m := by
  apply Equiv.ext
  intro i
  exact congrArg (chosenLexicographicSigmaIso I m)
    (congrFun (congrArg Equiv.toFun (orderedBlockPositionOrderIso_toEquiv _)) i)



end CategoryTheory.Operad.Tensor.Associative.OrderedProfile
end
end
end source_ChosenLexicographicInput

/- Source proof segment: ChosenLexicographicEnumeration -/
section source_ChosenLexicographicEnumeration
/-!
# Actual chosen lexicographic total enumeration equals the original source block map
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative.OrderedProfile

open CategoryTheory CategoryTheory.MonoidalCategory.TensorWord

attribute [local instance] FintypeCat.fintype

/-- The original total profile of source chosen outer and inner
word blocks, with its original lexicographic operation order. -/
def chosenLexicographicProfile (I : FintypeCat.{0}) (m : I → ℕ) : OrderedProfile where
  profile :=
    { inputs := FintypeCat.of (Σ i : I, Fin (m i))
      inputColor := fun _ => PUnit.unit }
  order := chosenLexicographicOrder I m

/-- The exact total original input count is its actual enumerated
block length, proved from the original source bijection. -/
theorem chosenLexicographic_count (I : FintypeCat.{0}) (m : I → ℕ) :
    count (chosenLexicographicProfile I m) =
      orderedBlockLength (originalEnumeratedBlockLengths I m) :=
  (Nat.card_congr (chosenLexicographicInputEquiv I m)).symm.trans (Nat.card_fin _)

/-- The actual total lexicographic increasing enumeration is the
original outer block input map followed by every actual source inner
strand permutation, with the original total count transport retained. -/
theorem enumeration_chosenLexicographic (I : FintypeCat.{0}) (m : I → ℕ) :
    (enumeration (chosenLexicographicProfile I m)).toEquiv =
      (finCongr (chosenLexicographic_count I m)).trans (chosenLexicographicInputEquiv I m) := by
  let e := chosenLexicographicInputOrderIso I m
  let c := Fin.castOrderIso (chosenLexicographic_count I m)
  have h : enumeration (chosenLexicographicProfile I m) =
      @OrderIso.trans _ _ _
        (Fin.instLinearOrder).toLE (Fin.instLinearOrder).toLE
        (chosenLexicographicOrder I m).toLE c e := by
    let : LinearOrder ((chosenLexicographicProfile I m).profile.inputs) :=
      (chosenLexicographicProfile I m).order
    exact Subsingleton.elim _ _
  exact (congrArg (fun f : @OrderIso (Fin (count (chosenLexicographicProfile I m)))
      (Σ i : I, Fin (m i)) (Fin.instLinearOrder).toLE
      (chosenLexicographicOrder I m).toLE => f.toEquiv) h).trans
    (congrArg ((finCongr (chosenLexicographic_count I m)).trans)
      (chosenLexicographicInputOrderIso_toEquiv I m))

/-- The actual one-word chosen canonical increasing enumeration
is its original source finite input permutation and exact count cast. -/
theorem enumeration_chosenCanonical (n : ℕ) :
    (enumeration (chosenCanonical n)).toEquiv =
      (finCongr (count_chosenCanonical n)).trans (originalFinInputPermutation n) := by
  let e := chosenFinOrderIso n
  let c := Fin.castOrderIso (count_chosenCanonical n)
  have h : enumeration (chosenCanonical n) =
      @OrderIso.trans _ _ _ (Fin.instLinearOrder).toLE (Fin.instLinearOrder).toLE
        (chosenCanonical n).order.toLE c e := by
    let : LinearOrder (chosenCanonical n).profile.inputs := (chosenCanonical n).order
    exact Subsingleton.elim _ _
  exact congrArg (fun f : @OrderIso (Fin (count (chosenCanonical n))) (Fin n)
    (Fin.instLinearOrder).toLE (chosenCanonical n).order.toLE => f.toEquiv) h




end CategoryTheory.Operad.Tensor.Associative.OrderedProfile
end
end
end source_ChosenLexicographicEnumeration

/- Source proof segment: ChosenOuterCanonicalMap -/
section source_ChosenOuterCanonicalMap
/-!
# Exact source rank map from original chosen outer order to chosen canonical profile
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Operad.Tensor.Associative.OrderedProfile

open CategoryTheory CategoryTheory.MonoidalCategory.TensorWord

attribute [local instance] FintypeCat.fintype

/-- The original constant-output profile with its ACTUAL source
outer enumeration order. -/
def chosenOuterProfile (I : FintypeCat.{0}) : OrderedProfile where
  profile := ⟨I, fun _ => PUnit.unit⟩
  order := chosenOuterOrder I

/-- The actual source outer finite count agrees with the original
profile word count, with the original bundled Fintype instance retained. -/
theorem chosenOuter_count (I : FintypeCat.{0}) : count (chosenOuterProfile I) = Fintype.card I :=
  Fintype.card_eq_nat_card.symm

/-- The actual increasing source map from the original chosen
outer order to chosen canonical word order, with both original
rank maps and the actual cardinal transport retained. -/
def chosenOuterToCanonicalEquiv (I : FintypeCat.{0}) :
    I ≃ (chosenCanonical (count (chosenOuterProfile I))).profile.inputs :=
  (Fintype.equivFin I).trans
    ((finCongr (chosenOuter_count I).symm).trans
      (originalFinInputPermutation (count (chosenOuterProfile I))))

/-- The actual original increasing source profile map has exactly
the two chosen source rank maps and original count transport. -/
theorem chosenOuterToCanonical_inputEquiv (I : FintypeCat.{0}) :
    (chosenCanonicalIso (chosenOuterProfile I)).hom.toEquiv = chosenOuterToCanonicalEquiv I := by
  let : LE I := (chosenOuterOrder I).toLE
  let p := chosenOuterProfile I
  let n := count p
  let e : p ⟶ chosenCanonical n :=
    @OrderIso.trans _ _ _ (chosenOuterOrder I).toLE (Fin.instLinearOrder).toLE
      (chosenCanonical n).order.toLE
      ((chosenOuterOrderIso I).symm.trans (Fin.castOrderIso (chosenOuter_count I).symm))
      (chosenFinOrderIso n)
  have h : (chosenCanonicalIso p).hom = e := Subsingleton.elim _ _
  exact congrArg (fun f : p ⟶ chosenCanonical n => f.toEquiv) h



end CategoryTheory.Operad.Tensor.Associative.OrderedProfile
end
end
end source_ChosenOuterCanonicalMap

/- Source proof segment: OriginalInputCarrierNaturality -/
section source_OriginalInputCarrierNaturality
/-!
# Original carrier maps commute with every original input order map
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.StrandNaturality

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The actual original map on finite input tensors for a
carrier map; its original profile bijections are unchanged. -/
def inputTensorCarrierMap {X Y : C} (f : X ⟶ Y) :
    analyticInputFamily (d := PUnit.unit) (fun _ : PUnit.{1} => X) ⋙ FiniteTensor.tensor ⟶
      analyticInputFamily (d := PUnit.unit) (fun _ : PUnit.{1} => Y) ⋙ FiniteTensor.tensor :=
  Functor.whiskerRight (analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f))
    (FiniteTensor.tensor (V := C))

/-- Its original finite-family components are the supplied
carrier map at every unchanged actual input position. -/
@[simp]
theorem inputTensorCarrierMap_app {X Y : C} (f : X ⟶ Y) (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    (inputTensorCarrierMap f).app P =
      (FiniteTensor.tensor (V := C)).map
        ((analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f)).app P) := rfl

/-- Every original profile/input bijection commutes with the
actual original carrier map on its finite input tensor. -/
theorem inputTensorCarrierMap_naturality {X Y : C} (f : X ⟶ Y)
    {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (g : P ⟶ Q) :
    (FiniteTensor.tensor (V := C)).map ((analyticInputFamily (fun _ : PUnit.{1} => X)).map g) ≫
      (inputTensorCarrierMap f).app Q =
    (inputTensorCarrierMap f).app P ≫
      (FiniteTensor.tensor (V := C)).map ((analyticInputFamily (fun _ : PUnit.{1} => Y)).map g) :=
  (inputTensorCarrierMap f).naturality g

/-- The same actual carrier map on the original ordered input
profiles; no chosen enumeration is replaced by an identity. -/
def orderedTensorCarrierMap {X Y : C} (f : X ⟶ Y) : orderedTensorDiagram X ⟶ orderedTensorDiagram Y :=
  Functor.whiskerLeft OrderedProfile.forget (inputTensorCarrierMap f)

/-- The actual word-length carrier map uses precisely the original
constant Fin-n input family map at every nonnegative length. -/
def wordTensorCarrierMap {X Y : C} (f : X ⟶ Y) :
    wordLengthTensorDiagram X ⟶ wordLengthTensorDiagram Y :=
  Discrete.natTrans (fun n => (orderedTensorCarrierMap f).app (OrderedProfile.canonical n.as))

/-- Source chosen canonical profiles retain their original input
profiles, so the actual carrier tensor map is the same original
map at those profiles, with every chosen order map retained. -/
theorem chosenCanonical_carrier {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (orderedTensorCarrierMap f).app (OrderedProfile.chosenCanonical n) =
      (wordTensorCarrierMap f).app (Discrete.mk n) := rfl

/-- The actual source carrier maps commute with the exact chosen
increasing profile map at every original ordered finite profile. -/
theorem chosenProfile_carrier_square {X Y : C} (f : X ⟶ Y) (P : OrderedProfile) :
    (orderedTensorDiagram X).map (OrderedProfile.chosenCanonicalIso P).hom ≫
      (wordTensorCarrierMap f).app (Discrete.mk (OrderedProfile.count P)) =
    (orderedTensorCarrierMap f).app P ≫
      (orderedTensorDiagram Y).map (OrderedProfile.chosenCanonicalIso P).hom :=
  (orderedTensorCarrierMap f).naturality (OrderedProfile.chosenCanonicalIso P).hom



end CategoryTheory.Operad.Tensor.Associative.StrandNaturality
end
end
end source_OriginalInputCarrierNaturality

/- Source proof segment: ChosenOrderedCarrierNaturality -/
section source_ChosenOrderedCarrierNaturality
/-!
# The corrected source ordered tensor comparison is natural in original carriers
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.StrandNaturality

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen ordered carrier naturality construction. -/
local instance chosenOrderedCarrierNaturalityFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The corrected comparison at every original ordered profile
is exactly its actual chosen increasing finite input tensor map. -/
theorem chosenOrderedTensorLengthIso_hom_app (X : C) (P : OrderedProfile) :
    (chosenOrderedTensorLengthIso X).hom.app P =
      (orderedTensorDiagram X).map (OrderedProfile.chosenCanonicalIso P).hom := by
  with_unfolding_all
    change 𝟙 _ ≫ ((orderedTensorDiagram X).map (OrderedProfile.chosenCanonicalIso P).hom ≫
      (𝟙 _ ≫ 𝟙 _)) = _
    simp only [Category.id_comp, Category.comp_id]

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- Each corrected original ordered finite tensor map is natural
under the actual original carrier map, retaining the source chosen
profile bijection rather than asserting its enumeration is an identity. -/
theorem chosenOrderedTensorLengthIso_carrier {X Y : C} (f : X ⟶ Y) (P : OrderedProfile) :
    (orderedTensorCarrierMap f).app P ≫ (chosenOrderedTensorLengthIso Y).hom.app P =
      (chosenOrderedTensorLengthIso X).hom.app P ≫
        (wordTensorCarrierMap f).app (Discrete.mk (OrderedProfile.count P)) := by
  have hx := chosenOrderedTensorLengthIso_hom_app X P
  have hy := chosenOrderedTensorLengthIso_hom_app Y P
  exact (congrArg (fun q => (orderedTensorCarrierMap f).app P ≫ q) hy).trans
    ((chosenProfile_carrier_square f P).symm.trans
      (congrArg (fun q => q ≫ (wordTensorCarrierMap f).app (Discrete.mk (OrderedProfile.count P))) hx.symm))

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- Full carrier naturality of the actual corrected ordered
tensor/word-length natural transformation. -/
theorem chosenOrderedTensorLengthIso_naturality {X Y : C} (f : X ⟶ Y) :
    orderedTensorCarrierMap f ≫ (chosenOrderedTensorLengthIso Y).hom =
      (chosenOrderedTensorLengthIso X).hom ≫
        Functor.whiskerLeft OrderedProfile.countFunctor (wordTensorCarrierMap f) := by
  apply NatTrans.ext
  funext P
  exact chosenOrderedTensorLengthIso_carrier f P



end CategoryTheory.Operad.Tensor.Associative.StrandNaturality
end
end
end source_ChosenOrderedCarrierNaturality

/- Source proof segment: ChosenConstantTensorMap -/
section source_ChosenConstantTensorMap
/-!
# Actual normalized source strand map on constant finite tensor inputs
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative.OrderedProfile

open CategoryTheory MonoidalCategory CategoryTheory.MonoidalCategory.TensorWord

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual source constant-family input map induced by the
chosen-order increasing canonical profile map. -/
def chosenConstantFamilyMap (Y : C) (I : FintypeCat.{0}) :
    (⟨I, fun _ => Y⟩ : FiniteFamily C) ⟶
      (⟨(chosenCanonical (count (chosenOuterProfile I))).profile.inputs, fun _ => Y⟩ : FiniteFamily C) :=
  { equiv := (chosenCanonicalIso (chosenOuterProfile I)).hom.toEquiv
    hom _ := 𝟙 Y }

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem chosenConstantFamilyMap_count (Y : C) (I : FintypeCat.{0}) :
    OrderedTensor.arity (⟨I, fun _ => Y⟩ : FiniteFamily C) =
      OrderedTensor.arity
        (⟨(chosenCanonical (count (chosenOuterProfile I))).profile.inputs, fun _ => Y⟩ : FiniteFamily C) := by
  change Fintype.card I = @Fintype.card (Fin (count (chosenOuterProfile I)))
    (@FintypeCat.fintype (FintypeCat.of (Fin (count (chosenOuterProfile I)))))
  let n := count (chosenOuterProfile I)
  have h : @Fintype.card (Fin n) (@FintypeCat.fintype (FintypeCat.of (Fin n))) = n :=
    (@Fintype.card_congr (Fin n) (Fin n)
      (@FintypeCat.fintype (FintypeCat.of (Fin n))) (inferInstance : Fintype (Fin n))
      (Equiv.refl _)).trans (Fintype.card_fin n)
  exact (chosenOuter_count I).symm.trans h.symm

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual normalized source input map is precisely the
original finite cardinality cast after both original rank maps cancel. -/
theorem chosenConstantFamilyMap_enumeratedEquiv (Y : C) (I : FintypeCat.{0}) :
    OrderedTensor.enumeratedEquiv (chosenConstantFamilyMap Y I) =
      finCongr (chosenConstantFamilyMap_count Y I) := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  change ((@Fintype.equivFin (Fin (count (chosenOuterProfile I)))
      (@FintypeCat.fintype (FintypeCat.of (Fin (count (chosenOuterProfile I))))))
      ((chosenCanonicalIso (chosenOuterProfile I)).hom.toEquiv ((originalFiniteInputEnumeration I) i))).val = i.val
  have h := chosenOuterToCanonical_inputEquiv I
  have hp := congrFun (congrArg Equiv.toFun h) ((originalFiniteInputEnumeration I) i)
  have hq := congrArg (fun j : Fin (count (chosenOuterProfile I)) =>
    ((@Fintype.equivFin (Fin (count (chosenOuterProfile I)))
      (@FintypeCat.fintype (FintypeCat.of (Fin (count (chosenOuterProfile I)))))) j).val) hp
  exact hq.trans (by
    let n := count (chosenOuterProfile I)
    let j := (finCongr (chosenOuter_count I).symm) i
    have hp : ((chosenRank n) (originalFinInputPermutation n j)).val = j.val := by
      unfold chosenRank originalFinInputPermutation originalFiniteInputEnumeration
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    have hi : (Fintype.equivFin I) ((originalFiniteInputEnumeration I) i) = i :=
      (Fintype.equivFin I).apply_symm_apply i
    have hstep := congrArg (fun k : Fin (Fintype.card I) =>
      ((chosenRank n) (originalFinInputPermutation n ((finCongr (chosenOuter_count I).symm) k))).val) hi
    exact hstep.trans hp)



end CategoryTheory.Operad.Tensor.Associative.OrderedProfile
end
end
end source_ChosenConstantTensorMap

/- Source proof segment: ConstantEnumeratedTensorTransport -/
section source_ConstantEnumeratedTensorTransport
/-!
# Actual identity-strand finite tensor maps on constant original families
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- Constant original families with equal actual finite counts
have equal original ordered tensor carriers. -/
theorem constantFiniteCarrier_eq (Y : C) (I J : FintypeCat.{0}) (h : Fintype.card I = Fintype.card J) :
    finiteObj (⟨I, fun _ => Y⟩ : FiniteFamily C) =
      finiteObj (⟨J, fun _ => Y⟩ : FiniteFamily C) :=
  obj_congr h (fun _ => Y) (fun _ => Y) (fun _ => rfl)

theorem constantOrderedMap_eqToHom (Y : C) {m n : ℕ} (e : Fin m ≃ Fin n) (h : m = n)
    (he : e = finCongr h) :
    mapEquiv (X := fun _ => Y) (Y := fun _ => Y) e (fun _ => 𝟙 Y) =
      eqToHom (obj_congr h (fun _ => Y) (fun _ => Y) (fun _ => rfl)) := by
  cases h
  have hr : e = Equiv.refl _ := he
  exact (mapEquiv_congr (X := fun _ : Fin m => Y) (Y := fun _ : Fin m => Y)
    hr (fun _ => 𝟙 Y) (fun _ => 𝟙 Y) (fun _ => HEq.rfl)).trans
    ((mapEquiv_id (fun _ : Fin m => Y)).trans
      (eqToHom_refl (obj (fun _ : Fin m => Y))
        (obj_congr rfl (fun _ => Y) (fun _ => Y) (fun _ => rfl))).symm)

/-- The actual identity-component map of constant original
families whose enumerated input map is the cardinality cast is
exactly equality transport on the original tensor carrier. -/
theorem constantFiniteMap_eqToHom (Y : C) (I J : FintypeCat.{0}) (e : I ≃ J)
    (h : Fintype.card I = Fintype.card J)
    (he : (Fintype.equivFin I).symm.trans (e.trans (Fintype.equivFin J)) = finCongr h) :
    finiteTensorFunctor.map
        ({ equiv := e, hom := fun _ => 𝟙 Y } :
          (⟨I, fun _ => Y⟩ : FiniteFamily C) ⟶ (⟨J, fun _ => Y⟩ : FiniteFamily C)) =
      eqToHom (constantFiniteCarrier_eq Y I J h) := by
  have hm :
      mapEquiv ((Fintype.equivFin I).symm.trans (e.trans (Fintype.equivFin J)))
        (fun _ => 𝟙 Y) = eqToHom (constantFiniteCarrier_eq Y I J h) := by
    exact constantOrderedMap_eqToHom Y _ h he
  have hs : finiteTensorFunctor.map
      ({ equiv := e, hom := fun _ => 𝟙 Y } :
        (⟨I, fun _ => Y⟩ : FiniteFamily C) ⟶ (⟨J, fun _ => Y⟩ : FiniteFamily C)) =
      mapEquiv ((Fintype.equivFin I).symm.trans (e.trans (Fintype.equivFin J))) (fun _ => 𝟙 Y) := by
    change mapEquiv _ _ = _
    apply mapEquiv_congr rfl
    intro i
    exact heq_of_eq (Category.comp_id (𝟙 Y))
  exact hs.trans hm



end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_ConstantEnumeratedTensorTransport

/- Source proof segment: ChosenOuterTensorComparison -/
section source_ChosenOuterTensorComparison
/-!
# Actual chosen outer word-input tensor comparison equals the original constant tensor power map
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory
open OrderedProfile

attribute [local instance] FintypeCat.fintype

private theorem equalityTransportPair {V : Type*} [Category* V]
    {A B D E : V} (h1 : A = B) (h2 : B = E) (h3 : A = D) (h4 : D = E) :
    eqToHom h1 ≫ eqToHom h2 = eqToHom h3 ≫ eqToHom h4 := by
  rw [eqToHom_trans, eqToHom_trans]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen outer tensor comparison construction. -/
local instance chosenOuterTensorComparisonFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual chosen canonical input map on constant original
families is exactly the original carrier equality transport, after
its source and target rank maps cancel. -/
theorem chosenConstantFamilyMap_tensor (Y : C) (I : FintypeCat.{0}) :
    OrderedTensor.finiteTensorFunctor.map (chosenConstantFamilyMap Y I) =
      eqToHom (OrderedTensor.constantFiniteCarrier_eq Y I
        (chosenCanonical (count (chosenOuterProfile I))).profile.inputs
        (chosenConstantFamilyMap_count Y I)) :=
  OrderedTensor.constantFiniteMap_eqToHom Y I _
    (chosenCanonicalIso (chosenOuterProfile I)).hom.toEquiv
    (chosenConstantFamilyMap_count Y I) (chosenConstantFamilyMap_enumeratedEquiv Y I)

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The original actual chosen source input comparison reaches
the stock power at its ORIGINAL Nat.card word length through the
actual constant-input carrier comparison and original count cast. -/
theorem chosenOuterPowerComparison (Y : C) (I : FintypeCat.{0}) :
    (chosenAssociativeOrderedPowerIso Y (chosenOuterProfile I).profile
      (ULift.up (chosenOuterOrder I))).hom =
      eqToHom (OrderedTensor.obj_constant Y (Fintype.card I)) ≫
        eqToHom (congrArg (TensorPower.tensorPowObj Y) Fintype.card_eq_nat_card) := by
  let P := chosenOuterProfile I
  have hc := StrandNaturality.chosenOrderedTensorLengthIso_hom_app Y P
  have hf : (orderedTensorDiagram Y).map (chosenCanonicalIso P).hom =
      OrderedTensor.finiteTensorFunctor.map (chosenConstantFamilyMap Y I) := by
    apply congrArg OrderedTensor.finiteTensorFunctor.map
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact heq_of_eq rfl
  have ht := chosenConstantFamilyMap_tensor Y I
  have hhead := hc.trans hf
  change (chosenOrderedTensorLengthIso Y).hom.app P ≫
    (associativeWordPowerIso Y).hom.app (Discrete.mk (count P)) = _
  exact (congrArg (fun f => f ≫ (associativeWordPowerIso Y).hom.app (Discrete.mk (count P))) hhead).trans
    (by
      have hb : (associativeWordPowerIso Y).hom.app (Discrete.mk (count P)) =
          eqToHom (OrderedTensor.finiteTensorFunctor_constant_obj (count P) Y) := by
        change 𝟙 _ ≫ eqToHom (OrderedTensor.finiteTensorFunctor_constant_obj (count P) Y) = _
        exact Category.id_comp _
      exact (congrArg (fun f => f ≫ (associativeWordPowerIso Y).hom.app (Discrete.mk (count P))) ht).trans
        ((congrArg (fun f => eqToHom (OrderedTensor.constantFiniteCarrier_eq Y I
            (chosenCanonical (count P)).profile.inputs (chosenConstantFamilyMap_count Y I)) ≫ f) hb).trans
          (equalityTransportPair _ _ _ _)))



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenOuterTensorComparison

/- Source proof segment: ChosenWordTargetComparison -/
section source_ChosenWordTargetComparison
/-!
# Actual chosen associative outer comparison on the original word carrier
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory
open OrderedProfile TensorWord

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen word target comparison construction. -/
local instance chosenWordTargetComparisonFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

omit [MonoidalClosed C] in
/-- The actual chosen associative input comparison on the
ORIGINAL tensor-word carrier is exactly its original finite word
target comparison, followed by the actual source cardinality cast. -/
theorem chosenWordOuterTarget (X : C) (I : FintypeCat.{0}) :
    (chosenAssociativeOrderedPowerIso (tensorWordObj X) (chosenOuterProfile I).profile
      (ULift.up (chosenOuterOrder I))).hom =
      (originalFiniteWordTargetIso X I).hom ≫
        eqToHom (congrArg (TensorPower.tensorPowObj (tensorWordObj X)) Fintype.card_eq_nat_card) :=
  chosenOuterPowerComparison (tensorWordObj X) I



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenWordTargetComparison

/- Source proof segment: ChosenRootWordInputEvaluation -/
section source_ChosenRootWordInputEvaluation
/-!
# Original chosen-root word operation evaluation on every original input tuple
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory
open OrderedProfile TensorWord

attribute [local instance] FintypeCat.fintype

private theorem evaluateOriginalRootFromSquares {V : Type*} [Category* V]
    {D A B E P Q : V} (i : D ⟶ A) (c : A ⟶ B) (f : B ⟶ Q)
    (u : A ⟶ E) (t : E ⟶ P) (g : P ⟶ Q)
    (v : D ⟶ P) (h : c ≫ f = u ≫ (t ≫ g))
    (hv : i ≫ (u ≫ t) = v) : i ≫ (c ≫ f) = v ≫ g := by
  rw [h, ← Category.assoc u t g, ← Category.assoc i (u ≫ t) g, hv]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen root word input evaluation construction. -/
local instance chosenRootWordInputEvaluationFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)

private theorem transportWordEvaluation (X : C) {n m : ℕ} (h : n = m) :
    eqToHom (congrArg (TensorPower.tensorPowObj (tensorWordObj X)) h) ≫
        wordConcatenationEvaluation X m = wordConcatenationEvaluation X n := by
  cases h
  exact Category.id_comp _

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The original word-input source has the same original unit
and power objects as the coefficient-leaf source, through actual
identity component maps on every original input. -/
def chosenRootWordSourceFactorsIso (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    wordInputSourceFactors X I m ≅
      (coefficientLeafFamilyFunctor (originalFiniteBlockFamily X I m)).obj
        (FiniteTensor.UnitCopower.unitObject C) :=
  FiniteFamily.isoOfReindex (Equiv.refl (Option I)) (fun o => by cases o <;> rfl)

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- Actual unit removal on the original named source input
family, including its explicit identity component comparison. -/
def chosenRootWordInputRemovalIso (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteTensor.tensor (V := C)).obj (wordInputSourceFactors X I m) ≅
      (FiniteTensor.tensor (V := C)).obj (originalFiniteBlockFamily X I m) :=
  (FiniteTensor.tensor (V := C)).mapIso (chosenRootWordSourceFactorsIso X I m) ≪≫
    unitCoefficientTensorIso (originalFiniteBlockFamily X I m)

/-- The original input word injections are the ACTUAL original
coefficient identity and unchanged-index finite leaf-word maps. -/
def chosenRootWordLeafMap (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    originalFiniteBlockFamily X I m ⟶ (⟨I, fun _ => tensorWordObj X⟩ : FiniteFamily C) :=
  OrderedTensor.fixedIndexHom I (fun i => tensorWordι X (m i))

omit [MonoidalClosed C] in
/-- The original root-and-word-input factor map is precisely the
original coefficient identity and every original finite leaf input map. -/
theorem chosenRootWordInputFactors (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    wordInputInjectionFactors X I m =
      (chosenRootWordSourceFactorsIso X I m).hom ≫
        coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) (chosenRootWordLeafMap X I m) := by
  apply FiniteFamily.Hom_ext
  · ext o
    cases o <;> rfl
  · intro o
    cases o with
    | none =>
        with_unfolding_all
          exact heq_of_eq (Category.id_comp _).symm
    | some i =>
        with_unfolding_all
          exact heq_of_eq (Category.id_comp _).symm

omit [MonoidalClosed C] in
/-- Removing the actual original root unit is natural under all
the original simultaneous word degree input injections. -/
theorem chosenRootWordInputUnitRemoval (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    wordInputInjection X I m ≫
        (unitCoefficientTensorIso (⟨I, fun _ => tensorWordObj X⟩ : FiniteFamily C)).hom =
      (chosenRootWordInputRemovalIso X I m).hom ≫
        originalFiniteWordMap X I m :=
  (congrArg (fun k => (FiniteTensor.tensor (V := C)).map k ≫
      (unitCoefficientTensorIso (⟨I, fun _ => tensorWordObj X⟩ : FiniteFamily C)).hom)
      (chosenRootWordInputFactors X I m)).trans
    (((congrArg (fun k => k ≫
      (unitCoefficientTensorIso (⟨I, fun _ => tensorWordObj X⟩ : FiniteFamily C)).hom)
        ((FiniteTensor.tensor (V := C)).map_comp _ _)).trans (Category.assoc _ _ _)).trans
      ((congrArg (fun k => (FiniteTensor.tensor (V := C)).map
          (chosenRootWordSourceFactorsIso X I m).hom ≫ k)
          (unitCoefficientTensorIso_naturality (chosenRootWordLeafMap X I m))).trans
        (Category.assoc _ _ _).symm))

/-- Every actual original word-input tuple for the source chosen
root coefficient evaluates the word operation by ACTUAL original
block flattening and its original concatenated word injection. -/
theorem chosenRootWordInputs_evaluation (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    wordInputInjection X I m ≫
        associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
          (ULift.up (chosenOuterOrder I)) ≫
        (wordEvaluationOperations X).app PUnit.unit (chosenOuterProfile I).profile =
      (chosenRootWordInputRemovalIso X I m).hom ≫
        (originalFiniteWordSourceIso X I m).hom ≫
        (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv ≫
        tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m)) := by
  have h := wordEvaluationOperations_coefficient X (chosenOuterProfile I).profile
    (ULift.up (chosenOuterOrder I))
  have hpow := chosenWordOuterTarget X I
  have hunit := chosenRootWordInputUnitRemoval X I m
  let u := (unitCoefficientTensorIso (⟨I, fun _ => tensorWordObj X⟩ : FiniteFamily C)).hom
  let p := (originalFiniteWordTargetIso X I).hom
  let c : TensorPower.tensorPowObj (tensorWordObj X) (Fintype.card I) ⟶
      TensorPower.tensorPowObj (tensorWordObj X) (Nat.card I) :=
    eqToHom (congrArg (TensorPower.tensorPowObj (tensorWordObj X))
      (@Fintype.card_eq_nat_card I (@FintypeCat.fintype I)))
  let g := wordConcatenationEvaluation X (Nat.card I)
  have hcast : c ≫ g = wordConcatenationEvaluation X (Fintype.card I) :=
    transportWordEvaluation X Fintype.card_eq_nat_card
  have hp : (chosenAssociativeOrderedPowerIso (tensorWordObj X) (chosenOuterProfile I).profile
      (ULift.up (chosenOuterOrder I))).hom ≫ g = p ≫ wordConcatenationEvaluation X (Fintype.card I) :=
    (congrArg (fun k => k ≫ g) hpow).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => p ≫ k) hcast))
  have h' := (congrArg (fun k => wordInputInjection X I m ≫ k) h).trans
    (congrArg (fun k => wordInputInjection X I m ≫ (u ≫ k)) hp)
  have h'' : wordInputInjection X I m ≫
      (associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
        (ULift.up (chosenOuterOrder I)) ≫
        (wordEvaluationOperations X).app PUnit.unit (chosenOuterProfile I).profile) =
      (chosenRootWordInputRemovalIso X I m).hom ≫
        (originalFiniteWordMap X I m ≫ p ≫ wordConcatenationEvaluation X (Fintype.card I)) :=
    h'.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (p ≫ wordConcatenationEvaluation X (Fintype.card I))) hunit).trans
        (Category.assoc _ _ _)))
  exact h''.trans (congrArg (fun k => (chosenRootWordInputRemovalIso X I m).hom ≫ k)
    (originalFiniteWordMap_evaluation X I m))



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenRootWordInputEvaluation

/- Source proof segment: ChosenWordSubstitution -/
section source_ChosenWordSubstitution
/-!
# Actual original chosen canonical word substitution and coefficient choices
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies

open CategoryTheory Limits MonoidalCategory
open OrderedProfile TensorWord
open CategoryTheory.FiniteTensor.UnitCopower

/-- The original finite root input index and every original
chosen canonical Fin(m i) inner profile, including empty inputs. -/
def chosenWordSubstitution (I : FintypeCat.{0}) (m : I → ℕ) : ColoredSubstitutionData PUnit.{1} where
  outputColor := PUnit.unit
  inner := ⟨I, fun i => (chosenCanonical (m i)).profile.toColoredProfile⟩

/-- Actual root and every original inner source operation order,
lifted to the original coefficient universe. -/
def chosenWordCoefficients (I : FintypeCat.{0}) (m : I → ℕ) :
    ∀ o : (associativeFactors.{us} (chosenWordSubstitution I m)).index,
      (associativeFactors.{us} (chosenWordSubstitution I m)).obj o
  | none => ULift.up (chosenOuterOrder I)
  | some i => ULift.up (chosenCanonical (m i)).order

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen word substitution construction. -/
local instance chosenWordSubstitutionFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The exact count transport from the original Fin(n) profile
word count to the supplied original word degree n. -/
def chosenWordCountIso (X : C) (n : ℕ) :
    TensorPower.tensorPowObj X (Nat.card (Fin n)) ≅ TensorPower.tensorPowObj X n :=
  eqToIso (congrArg (TensorPower.tensorPowObj X) (Nat.card_fin n))

/-- Original canonical chosen input tensors become the original
binary power at the supplied degree, through the actual chosen
profile comparison and exact original count transport. -/
def chosenWordInnerPowerIso (X : C) (n : ℕ) :
    (FiniteTensor.tensor (V := C)).obj
      ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj (chosenCanonical n).profile) ≅
        TensorPower.tensorPowObj X n :=
  chosenAssociativeOrderedPowerIso.{u, v, us} X (chosenCanonical n).profile (ULift.up (chosenCanonical n).order) ≪≫
    chosenWordCountIso X n

/-- Remove only the original inner coefficient unit, then use
the actual chosen Fin(n) source comparison and original count transport. -/
def chosenWordInnerSourceIso (X : C) (n : ℕ) :
    (coefficientLeafTensorFunctor
      ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj (chosenCanonical n).profile)).obj (unitObject C) ≅
        TensorPower.tensorPowObj X n :=
  unitCoefficientTensorIso _ ≪≫ chosenWordInnerPowerIso.{u, v, us} X n

/-- The actual original root singleton tensor unitor and every
original inner coefficient-unit/Fin(n) tensor comparison, on the
unchanged original Option I input index. -/
def chosenWordBlockFactorsIso (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj
      (InputCopies.unitNestedFactors X (chosenWordSubstitution I m)) ≅
        wordInputSourceFactors X I m :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option I))
    (fun o => match o with
      | none => (FiniteTensor.singletonIso (V := C)).app (unitObject C)
      | some i => chosenWordInnerSourceIso.{u, v, us} X (m i))

/-- The actual original flattened root/inner unit input source
becomes the exact ORIGINAL wordInputSourceFactors tensor domain. -/
def chosenWordBlockSourceIso (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteTensor.tensor (V := C)).obj
      ((FiniteFamily.flatten (C := C)).obj (InputCopies.unitNestedFactors X (chosenWordSubstitution I m))) ≅
    (FiniteTensor.tensor (V := C)).obj (wordInputSourceFactors X I m) :=
  (FiniteTensor.flattenIso (V := C)).app (InputCopies.unitNestedFactors X (chosenWordSubstitution I m)) ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (chosenWordBlockFactorsIso.{u, v, us} X I m)

/-- The actual original assembled root coefficient and each
original chosen inner coefficient/profile injection. -/
def chosenWordAssembledInputs (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteTensor.tensor (V := C)).obj
      ((FiniteFamily.flatten (C := C)).obj (InputCopies.unitNestedFactors X (chosenWordSubstitution I m))) ⟶
    (analyticSummand (associativeOperad C).toCollection
      (profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X))).obj
        (chosenOuterProfile I).profile :=
  InputCopies.assembledTensorInjection X (chosenWordSubstitution I m) (chosenWordCoefficients.{us} I m)



end CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies
end
end
end source_ChosenWordSubstitution

/- Source proof segment: ChosenWordInnerCopy -/
section source_ChosenWordInnerCopy
/-!
# Original chosen inner coefficient/profile copies and original word degrees
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies

open CategoryTheory Limits MonoidalCategory
open OrderedProfile TensorWord
open CategoryTheory.FiniteTensor.UnitCopower

private theorem originalDependentInjectionTransport {V : Type*} [Category* V]
    (A : ℕ → V) {W : V} (j : ∀ n, A n ⟶ W) {n m : ℕ} (h : n = m) :
    eqToHom (congrArg A h) ≫ j m = j n := by
  cases h
  exact Category.id_comp _

private theorem originalCopyThroughIso {V : Type*} [Category* V]
    {D A B : V} (e : A ≅ B) (q : D ⟶ A) (b : D ⟶ B)
    (h : q ≫ e.hom = b) : q = b ≫ e.inv := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem originalInnerCountInsertion {V : Type*} [Category* V]
    {D A B W : V} (u : D ⟶ A) (p : A ⟶ B) (c : B ⟶ W)
    {Q : V} (j : W ⟶ Q) (k : B ⟶ Q) (h : c ≫ j = k) :
    u ≫ (p ≫ k) = ((u ≫ p) ≫ c) ≫ j := by
  rw [Category.assoc, Category.assoc, h]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen word inner copy construction. -/
local instance chosenWordInnerCopyFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The original dependent power carrier transport retains the
actual supplied word-degree coproduct injection. -/
theorem chosenWordCountIso_wordι (X : C) (n : ℕ) :
    (chosenWordCountIso X n).hom ≫ tensorWordι X n = tensorWordι X (Nat.card (Fin n)) :=
  originalDependentInjectionTransport (TensorPower.tensorPowObj X) (tensorWordι X) (Nat.card_fin n)

/-- The ACTUAL original chosen Fin(n) coefficient copy followed
by its original profile quotient and chosen word carrier map is
the original unit removal and power comparison, before count transport. -/
theorem chosenWordInnerCopy_originalCount (X : C) (n : ℕ) :
    associativeProfileCoefficientInjection X (chosenCanonical n).profile
        (ULift.up (chosenCanonical n).order) ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) (chosenCanonical n).profile ≫
      (chosenAssociativeTensorWordsIso X).hom =
    (unitCoefficientTensorIso
      ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj (chosenCanonical n).profile)).hom ≫
      (chosenAssociativeOrderedPowerIso X (chosenCanonical n).profile (ULift.up (chosenCanonical n).order)).hom ≫
      tensorWordι X (Nat.card (Fin n)) :=
  chosenAssociativeTensorWordsIso_coefficient X (chosenCanonical n).profile (ULift.up (chosenCanonical n).order)

/-- The same actual original inner coefficient/profile injection
has the supplied original word degree n after its exact original
Nat.card(Fin n) transport, with no enumeration identity assumption. -/
theorem chosenWordInnerCopy_word (X : C) (n : ℕ) :
    associativeProfileCoefficientInjection X (chosenCanonical n).profile
        (ULift.up (chosenCanonical n).order) ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) (chosenCanonical n).profile ≫
      (chosenAssociativeTensorWordsIso X).hom =
    (chosenWordInnerSourceIso.{u, v, us} X n).hom ≫ tensorWordι X n := by
  let u := (unitCoefficientTensorIso
    ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj (chosenCanonical n).profile)).hom
  let p := (chosenAssociativeOrderedPowerIso.{u, v, us} X (chosenCanonical n).profile
    (ULift.up (chosenCanonical n).order)).hom
  let c := (chosenWordCountIso X n).hom
  let j := tensorWordι X n
  let k := tensorWordι X (Nat.card (Fin n))
  have h := chosenWordInnerCopy_originalCount X n
  have hc : c ≫ j = k := chosenWordCountIso_wordι X n
  exact h.trans ((originalInnerCountInsertion u p c j k hc).trans
    (congrArg (· ≫ j) (Category.assoc u p c)))

/-- The actual original inner input copy returns from its chosen
word injection through the ACTUAL inverse original free-word carrier
map. No operation or algebra comparison is a premise. -/
theorem chosenWordInnerCopy_return (X : C) (n : ℕ) :
    associativeProfileCoefficientInjection X (chosenCanonical n).profile
        (ULift.up (chosenCanonical n).order) ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) (chosenCanonical n).profile =
    (chosenWordInnerSourceIso.{u, v, us} X n).hom ≫ tensorWordι X n ≫
      (chosenWordCarrierIso X).inv PUnit.unit := by
  let e := chosenAssociativeTensorWordsIso X
  let q := associativeProfileCoefficientInjection X (chosenCanonical n).profile
    (ULift.up (chosenCanonical n).order) ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) (chosenCanonical n).profile
  let b := (chosenWordInnerSourceIso.{u, v, us} X n).hom ≫ tensorWordι X n
  have h : q ≫ e.hom = b := (Category.assoc _ _ _).trans (chosenWordInnerCopy_word X n)
  exact (originalCopyThroughIso e q b h).trans (Category.assoc _ _ _)




end CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies
end
end
end source_ChosenWordInnerCopy

/- Source proof segment: ChosenWordCopyFactors -/
section source_ChosenWordCopyFactors
/-!
# Exact original chosen root coefficient and inner word-copy factor maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies

open CategoryTheory Limits MonoidalCategory
open OrderedProfile TensorWord
open CategoryTheory.FiniteTensor.UnitCopower

private theorem originalRootCoefficientIdentity {V : Type*} [Category* V]
    {A B C : V} (u : A ⟶ B) (i : B ⟶ C) : u ≫ (𝟙 B ≫ i) = u ≫ i := by
  rw [Category.id_comp]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen word copy factors construction. -/
local instance chosenWordCopyFactorsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual original chosen outer coefficient copy and each
original inverse carrier map, on the unchanged original root input index. -/
def chosenWordOuterCopyFactors (X : C) (I : FintypeCat.{0}) :
    wordInputTargetFactors X I ⟶
      (analyticFactors (associativeOperad C).toCollection
        (profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X))).obj
          (chosenOuterProfile I).profile where
  equiv := Equiv.refl (Option I)
  hom o := match o with
    | none => Sigma.ι (fun _ : ULift.{us} (LinearOrder I) => unitObject C) (ULift.up (chosenOuterOrder I))
    | some _ => (chosenWordCarrierIso X).inv PUnit.unit

/-- The displayed original outer factor map is exactly the
original coefficient-copy factor followed by the original carrier map. -/
theorem chosenWordOuterCopyFactors_source (X : C) (I : FintypeCat.{0}) :
    InputCopies.innerCopyFactors (tensorWordObj X) (chosenOuterProfile I).profile
        (ULift.up (chosenOuterOrder I)) ≫
      (analyticFactorsCarrierMap (associativeOperad C).toCollection (chosenWordCarrierIso X).inv).app
        (chosenOuterProfile I).profile = chosenWordOuterCopyFactors X I := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (Category.comp_id _)
    | some i =>
      exact heq_of_eq (Category.id_comp _)

/-- Tensoring the original chosen outer coefficient/word carrier
factors gives precisely the actual original profile coefficient injection
and original free-word inverse summand carrier map. -/
theorem chosenWordOuterCopyFactors_tensor (X : C) (I : FintypeCat.{0}) :
    (FiniteTensor.tensor (V := C)).map (chosenWordOuterCopyFactors X I) =
      associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
        (ULift.up (chosenOuterOrder I)) ≫
      (analyticSummandCarrierMap (associativeOperad C).toCollection (chosenWordCarrierIso X).inv).app
        (chosenOuterProfile I).profile := by
  let T := FiniteTensor.tensor (V := C)
  have h := congrArg T.map (chosenWordOuterCopyFactors_source X I).symm
  exact h.trans ((T.map_comp _ _).trans
    (congrArg (· ≫
      (analyticSummandCarrierMap (associativeOperad C).toCollection (chosenWordCarrierIso X).inv).app
        (chosenOuterProfile I).profile)
      (InputCopies.innerCopyFactors_tensor (tensorWordObj X) (chosenOuterProfile I).profile
        (ULift.up (chosenOuterOrder I)))))

/-- Every original assembled inner coefficient/profile copy is
the original unit removal and actual chosen word-power map, original
word-degree input injection, and actual original inverse carrier map.
The root is the original singleton tensor unitor and coefficient copy. -/
theorem chosenWordAssembledFactors (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    InputCopies.assembledCopies X (chosenWordSubstitution I m) (chosenWordCoefficients.{us} I m) =
      (chosenWordBlockFactorsIso.{u, v, us} X I m).hom ≫
        wordInputInjectionFactors X I m ≫ chosenWordOuterCopyFactors X I := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (originalRootCoefficientIdentity
        ((FiniteTensor.singletonIso (V := C)).hom.app (unitObject C))
        (Sigma.ι (fun _ : ULift.{us} (LinearOrder I) => unitObject C)
          (ULift.up (chosenOuterOrder I)))).symm
    | some i =>
      exact heq_of_eq (chosenWordInnerCopy_return X (m i))




end CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies
end
end
end source_ChosenWordCopyFactors

/- Source proof segment: ChosenWordAssembledInputs -/
section source_ChosenWordAssembledInputs
/-!
# Original assembled chosen coefficient/input tensor copies equal original word-input copies
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies

open CategoryTheory Limits MonoidalCategory
open OrderedProfile TensorWord
open CategoryTheory.FiniteTensor.UnitCopower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen word assembled inputs construction. -/
local instance chosenWordAssembledInputsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The ACTUAL original assembled input map agrees exactly with
the original chosen word input copies, chosen root coefficient copy,
and original inverse free-word summand carrier map. The source is the
actual original root/inner normalization isomorphism, and the target
of that isomorphism remains the ORIGINAL wordInputSourceFactors tensor. -/
theorem chosenWordAssembledInputs_eq_wordInputs
    (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    chosenWordAssembledInputs X I m =
      (chosenWordBlockSourceIso.{u, v, us} X I m).hom ≫
        wordInputInjection X I m ≫
        associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
          (ULift.up (chosenOuterOrder I)) ≫
        (analyticSummandCarrierMap (associativeOperad C).toCollection (chosenWordCarrierIso X).inv).app
          (chosenOuterProfile I).profile := by
  let T := FiniteTensor.tensor (V := C)
  let s := chosenWordSubstitution I m
  let a := (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s)
  let b0 := (chosenWordBlockFactorsIso.{u, v, us} X I m).hom
  let c0 := wordInputInjectionFactors X I m
  let d0 := chosenWordOuterCopyFactors X I
  let f0 := InputCopies.assembledCopies X s (chosenWordCoefficients.{us} I m)
  let c := wordInputInjection X I m
  let d := associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
    (ULift.up (chosenOuterOrder I))
  let e := (analyticSummandCarrierMap (associativeOperad C).toCollection (chosenWordCarrierIso X).inv).app
    (chosenOuterProfile I).profile
  have hmap : T.map f0 = T.map b0 ≫ (T.map c0 ≫ T.map d0) :=
    (congrArg T.map (chosenWordAssembledFactors X I m)).trans
      ((T.map_comp _ _).trans (congrArg (T.map b0 ≫ ·) (T.map_comp _ _)))
  have houter : T.map d0 = d ≫ e := chosenWordOuterCopyFactors_tensor X I
  have hfull : T.map f0 = T.map b0 ≫ (c ≫ (d ≫ e)) :=
    hmap.trans (congrArg (fun f => T.map b0 ≫ (c ≫ f)) houter)
  exact (congrArg (a ≫ ·) hfull).trans (Category.assoc _ _ _).symm

/-- Exact raw ORIGINAL root/inner coefficient-copy input equation:
the original flattened nested copy map, original operation tensor
flattening and original profile injections give the original chosen
word input composite. This retains the original substitution coefficients
and all original leaves, including nullary and unary profiles. -/
theorem chosenWordRawCopies_eq_wordInputs
    (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map
          (InputCopies.nestedCopies X (chosenWordSubstitution I m) (chosenWordCoefficients.{us} I m))) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app
        (nestedOperationFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X)
          (chosenWordSubstitution I m)) ≫
      (FiniteTensor.tensor (V := C)).map
        (operationInjectionFactors (associativeOperad C).toCollection (fun _ : PUnit.{1} => X)
          (chosenWordSubstitution I m)) =
    (chosenWordBlockSourceIso.{u, v, us} X I m).hom ≫
      wordInputInjection X I m ≫
      associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
        (ULift.up (chosenOuterOrder I)) ≫
      (analyticSummandCarrierMap (associativeOperad C).toCollection (chosenWordCarrierIso X).inv).app
        (chosenOuterProfile I).profile :=
  (InputCopies.nestedCopies_tensor_assembled X (chosenWordSubstitution I m)
    (chosenWordCoefficients.{us} I m)).trans (chosenWordAssembledInputs_eq_wordInputs X I m)




end CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies
end
end
end source_ChosenWordAssembledInputs

/- Source proof segment: OriginalConstantFiniteBlocks -/
section source_OriginalConstantFiniteBlocks
/-!
# Original constant-input blocks in the produced finite flattening

The original inner finite index and its actual enumeration are retained.
The supplied inner count is used only through its proved cardinal equality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorWord

variable {C : Type u}

private theorem constantFunction_heq (X : C) {a b : ℕ} (h : a = b) :
    HEq (fun _ : Fin a => X) (fun _ : Fin b => X) := by
  cases h
  rfl

/-- The original enumeration on each constant finite input retains
its actual index type and exact cardinality transport. -/
theorem constantFinFamily_orderedFamily_heq (X : C) (n : ℕ) :
    HEq (orderedFamily (constantFinFamily n X)) (fun _ : Fin n => X) :=
  constantFunction_heq X (constantFinFamily_arity n X)

private theorem snoc_constant_eq (B : Blocks C) (X : C) {a b : ℕ} (h : a = b) :
    Blocks.snoc B (fun _ : Fin a => X) = Blocks.snoc B (fun _ : Fin b => X) := by
  cases h
  rfl

/-- The actual original finite blocks are the original homogeneous
word blocks, preserving every supplied inner count including zero. -/
theorem blocksOfConstantFinFamily (X : C) : ∀ {n : ℕ} (m : Fin n → ℕ),
    blocksOfFamily (fun i => constantFinFamily (m i) X) = originalWordBlocks X m
  | 0, _ => rfl
  | n + 1, m => by
      change Blocks.snoc (blocksOfFamily (fun i : Fin n => constantFinFamily (m i.castSucc) X))
        (fun _ : Fin (arity (constantFinFamily (m (Fin.last n)) X)) => X) =
        Blocks.snoc (originalWordBlocks X (fun i : Fin n => m i.castSucc))
          (fun _ : Fin (m (Fin.last n)) => X)
      rw [blocksOfConstantFinFamily X (fun i : Fin n => m i.castSucc)]
      exact snoc_constant_eq _ X (constantFinFamily_arity (m (Fin.last n)) X)



end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_OriginalConstantFiniteBlocks

/- Source proof segment: OriginalConstantFinitePositions -/
section source_OriginalConstantFinitePositions
/-!
# Exact original positions of constant finite tensor blocks

The outer block positions and every original inner finite enumeration
are retained. Count transports are established from the actual blocks.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorWord

variable {C : Type u}

private theorem equiv_finDomain_heq {a b : ℕ} {D : Type*} (h : a = b)
    (e : Fin b ≃ D) : HEq ((finCongr h).trans e) e := by
  cases h
  rfl

/-- The actual source enumeration of each original inner Fin input
is the retained original permutation with its domain-count transport. -/
theorem enumeration_constantFinFamily_heq (X : C) (n : ℕ) :
    HEq (enumeration (constantFinFamily n X)) (originalFinInputPermutation n) := by
  exact (equiv_finDomain_heq (constantFinFamily_arity n X).symm
    (enumeration (constantFinFamily n X))).symm

/-- The actual flattened original blocks retain the supplied total count. -/
theorem blocksOfConstantFinFamily_total (X : C) {n : ℕ} (m : Fin n → ℕ) :
    (blocksOfFamily (fun i => constantFinFamily (m i) X)).totalArity = orderedBlockLength m :=
  (congrArg Blocks.totalArity (blocksOfConstantFinFamily X m)).trans (originalWordBlocks_total X m)

private theorem flattenedPositionsEquiv_snoc {n : ℕ} (F : Fin (n + 1) → FiniteFamily C) :
    flattenedPositionsEquiv F =
      finSumFinEquiv.symm.trans
        ((Equiv.sumCongr (flattenedPositionsEquiv (Fin.init F))
          (enumeration (F (Fin.last n)))).trans (positionsSnocEquiv F)) := by
  apply Equiv.ext
  intro j
  change positionsSnocEquiv F
      ((Equiv.sumCongr (blockPositionsEquiv (Fin.init F)) (enumeration (F (Fin.last n))))
        ((Equiv.sumCongr (blocksOfFamily (Fin.init F)).positionEquiv (Equiv.refl _))
          (finSumFinEquiv.symm j))) =
    positionsSnocEquiv F
      ((Equiv.sumCongr (flattenedPositionsEquiv (Fin.init F)) (enumeration (F (Fin.last n))))
        (finSumFinEquiv.symm j))
  cases finSumFinEquiv.symm j with
  | inl q => rfl
  | inr q => rfl

private theorem concatEquiv_heq {a a' b b' : ℕ} {A B D : Type*}
    (ha : a = a') (hb : b = b')
    (e : Fin a ≃ A) (e' : Fin a' ≃ A) (he : HEq e e')
    (f : Fin b ≃ B) (f' : Fin b' ≃ B) (hf : HEq f f')
    (q : A ⊕ B ≃ D) :
    HEq (finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans q))
      (finSumFinEquiv.symm.trans ((Equiv.sumCongr e' f').trans q)) := by
  cases ha
  cases hb
  cases eq_of_heq he
  cases eq_of_heq hf
  rfl

private theorem positionsSnocEquiv_constant (X : C) {n : ℕ} (m : Fin (n + 1) → ℕ) :
    positionsSnocEquiv (fun i => constantFinFamily (m i) X) = blockSigmaLastEquiv m := by
  apply Equiv.ext
  intro p
  cases p with
  | inl p => rfl
  | inr p => rfl

/-- Every original inner Fin input permutation, at its actual supplied count. -/
def originalInnerWordPermutation {n : ℕ} (m : Fin n → ℕ) :
    (Σ i : Fin n, Fin (m i)) ≃ (Σ i : Fin n, Fin (m i)) :=
  Equiv.sigmaCongrRight (fun i => originalFinInputPermutation (m i))

private theorem orderedBlockPositionEquiv_inner_snoc {n : ℕ} (m : Fin (n + 1) → ℕ) :
    (orderedBlockPositionEquiv m).trans (originalInnerWordPermutation m) =
      finSumFinEquiv.symm.trans
        ((Equiv.sumCongr
          ((orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)).trans
            (originalInnerWordPermutation (fun i : Fin n => m i.castSucc)))
          (originalFinInputPermutation (m (Fin.last n)))).trans (blockSigmaLastEquiv m)) := by
  apply Equiv.ext
  intro j
  change originalInnerWordPermutation m
      (blockSigmaLastEquiv m
        ((Equiv.sumCongr (orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)) (Equiv.refl _))
          (finSumFinEquiv.symm j))) =
    blockSigmaLastEquiv m
      ((Equiv.sumCongr
        ((orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)).trans
          (originalInnerWordPermutation (fun i : Fin n => m i.castSucc)))
        (originalFinInputPermutation (m (Fin.last n)))) (finSumFinEquiv.symm j))
  cases finSumFinEquiv.symm j with
  | inl p => rfl
  | inr p => rfl

/-- The original block-word enumeration retains every original inner
finite permutation and every original total-count transport. -/
theorem flattenedPositionsEquiv_constantFinFamily_heq (X : C) :
    ∀ {n : ℕ} (m : Fin n → ℕ),
    HEq (flattenedPositionsEquiv (fun i => constantFinFamily (m i) X))
      ((orderedBlockPositionEquiv m).trans (originalInnerWordPermutation m))
  | 0, m => by
      apply heq_of_eq
      apply Equiv.ext
      intro j
      exact j.elim0
  | n + 1, m => by
      rw [flattenedPositionsEquiv_snoc, positionsSnocEquiv_constant]
      have h := concatEquiv_heq
        (blocksOfConstantFinFamily_total X (fun i : Fin n => m i.castSucc))
        (constantFinFamily_arity (m (Fin.last n)) X)
        (flattenedPositionsEquiv (fun i : Fin n => constantFinFamily (m i.castSucc) X))
        ((orderedBlockPositionEquiv (fun i : Fin n => m i.castSucc)).trans
          (originalInnerWordPermutation (fun i : Fin n => m i.castSucc)))
        (flattenedPositionsEquiv_constantFinFamily_heq X (fun i : Fin n => m i.castSucc))
        (enumeration (constantFinFamily (m (Fin.last n)) X))
        (originalFinInputPermutation (m (Fin.last n)))
        (enumeration_constantFinFamily_heq X (m (Fin.last n))) (blockSigmaLastEquiv m)
      exact h.trans (heq_of_eq (orderedBlockPositionEquiv_inner_snoc m).symm)



end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_OriginalConstantFinitePositions

/- Source proof segment: OriginalLeafWordPositions -/
section source_OriginalLeafWordPositions
/-!
# The original nested finite word positions are the chosen lexicographic positions

Every original outer input and each original inner finite permutation
is retained in the source dependent sum.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorWord
open CategoryTheory.Operad.Tensor.Associative

attribute [local instance] FintypeCat.fintype

variable {C : Type u}

/-- The original finite family of original constant finite word inputs. -/
def originalLeafBlocks (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    FiniteFamily (FiniteFamily C) :=
  ⟨I, fun i => constantFinFamily (m i) X⟩

/-- The original finite flattening has its original ordered constant blocks. -/
theorem originalLeafBlocks_blocks (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    blocksOfFiniteFamily (originalLeafBlocks X I m) =
      originalWordBlocks X (originalEnumeratedBlockLengths I m) :=
  blocksOfConstantFinFamily X (originalEnumeratedBlockLengths I m)

/-- The actual original finite block word retains the exact total supplied count. -/
theorem originalLeafBlocks_total (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (blocksOfFiniteFamily (originalLeafBlocks X I m)).totalArity =
      orderedBlockLength (originalEnumeratedBlockLengths I m) :=
  blocksOfConstantFinFamily_total X (originalEnumeratedBlockLengths I m)

private theorem equiv_trans_finDomain_heq {a b : ℕ} {A D : Type*}
    (h : a = b) (e : Fin a ≃ A) (e' : Fin b ≃ A) (he : HEq e e')
    (q : A ≃ D) : HEq (e.trans q) (e'.trans q) := by
  cases h
  cases eq_of_heq he
  rfl

private theorem originalLeafBlocks_outerPositions (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    originalOuterPositionsEquiv (originalLeafBlocks X I m) =
      Equiv.sigmaCongrLeft (β := fun i : I => Fin (m i)) (originalFiniteInputEnumeration I) := by
  apply Equiv.ext
  intro p
  rfl

private theorem originalLeafBlocks_orderedPositions (I : FintypeCat.{0}) (m : I → ℕ) :
    ((orderedBlockPositionEquiv (originalEnumeratedBlockLengths I m)).trans
      (originalInnerWordPermutation (originalEnumeratedBlockLengths I m))).trans
        (Equiv.sigmaCongrLeft (β := fun i : I => Fin (m i)) (originalFiniteInputEnumeration I)) =
      OrderedProfile.chosenLexicographicInputEquiv I m := by
  apply Equiv.ext
  intro p
  rfl

/-- The actual source nested-position equivalence is the original
chosen lexicographic equivalence, with its proved original count transport. -/
theorem originalLeafBlocks_nestedPositions_heq (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    HEq (nestedPositionsEquiv (originalLeafBlocks X I m))
      (OrderedProfile.chosenLexicographicInputEquiv I m) := by
  unfold nestedPositionsEquiv
  rw [originalLeafBlocks_outerPositions]
  have h := equiv_trans_finDomain_heq (originalLeafBlocks_total X I m)
    (flattenedPositionsEquiv (fun j => constantFinFamily
      (originalEnumeratedBlockLengths I m j) X))
    ((orderedBlockPositionEquiv (originalEnumeratedBlockLengths I m)).trans
      (originalInnerWordPermutation (originalEnumeratedBlockLengths I m)))
    (flattenedPositionsEquiv_constantFinFamily_heq X (originalEnumeratedBlockLengths I m))
    (Equiv.sigmaCongrLeft (β := fun i : I => Fin (m i)) (originalFiniteInputEnumeration I))
  exact h.trans (heq_of_eq (originalLeafBlocks_orderedPositions I m))

private theorem equiv_precast_heq {a b : ℕ} {D : Type*} (h : a = b) (e : Fin b ≃ D) :
    HEq ((finCongr h).trans e) e := by
  cases h
  rfl

/-- Exact typed original dependent-sum readback of the actual nested tensor positions. -/
theorem originalLeafBlocks_nestedPositions (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    nestedPositionsEquiv (originalLeafBlocks X I m) =
      (finCongr (originalLeafBlocks_total X I m)).trans
        (OrderedProfile.chosenLexicographicInputEquiv I m) :=
  eq_of_heq ((originalLeafBlocks_nestedPositions_heq X I m).trans
    (equiv_precast_heq (originalLeafBlocks_total X I m)
      (OrderedProfile.chosenLexicographicInputEquiv I m)).symm)

variable [Category.{v} C]

/-- The actual original flatten-to-word permutation is the original total
input enumeration followed by the inverse chosen lexicographic input map. -/
theorem originalLeafBlocks_flattenWordEquiv (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (flattenWordEquiv (originalLeafBlocks X I m)).trans
        (finCongr (originalLeafBlocks_total X I m)) =
      (enumeration (flattenedOriginalFamily (originalLeafBlocks X I m))).trans
        (OrderedProfile.chosenLexicographicInputEquiv I m).symm := by
  apply Equiv.ext
  intro p
  apply (OrderedProfile.chosenLexicographicInputEquiv I m).injective
  change OrderedProfile.chosenLexicographicInputEquiv I m
      (Fin.cast (originalLeafBlocks_total X I m)
        ((nestedPositionsEquiv (originalLeafBlocks X I m)).symm
          (enumeration (flattenedOriginalFamily (originalLeafBlocks X I m)) p))) =
    OrderedProfile.chosenLexicographicInputEquiv I m
      ((OrderedProfile.chosenLexicographicInputEquiv I m).symm
        (enumeration (flattenedOriginalFamily (originalLeafBlocks X I m)) p))
  change ((finCongr (originalLeafBlocks_total X I m)).trans
      (OrderedProfile.chosenLexicographicInputEquiv I m))
        ((nestedPositionsEquiv (originalLeafBlocks X I m)).symm
          (enumeration (flattenedOriginalFamily (originalLeafBlocks X I m)) p)) = _
  rw [← originalLeafBlocks_nestedPositions]
  exact ((nestedPositionsEquiv (originalLeafBlocks X I m)).apply_symm_apply _).trans
    ((OrderedProfile.chosenLexicographicInputEquiv I m).apply_symm_apply _).symm



end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_OriginalLeafWordPositions

/- Source proof segment: ChosenTotalInputPermutation -/
section source_ChosenTotalInputPermutation
/-!
# The actual chosen total profile input map retains the lexicographic permutation

The original increasing order map is normalized by its two original
finite input enumerations. No chosen Fin enumeration is an identity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory MonoidalCategory OrderedTensor TensorWord

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C]

/-- The actual original input-family map from the chosen total
lexicographic profile to the source chosen canonical word profile. -/
def chosenTotalInputHom (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    flattenedOriginalFamily (originalLeafBlocks X I m) ⟶
      constantFinFamily (Nat.card (Σ i : I, Fin (m i))) X :=
  (analyticInputFamily (fun _ : PUnit.{1} => X)).map
    (OrderedProfile.forget.map
      (OrderedProfile.chosenCanonicalIso (OrderedProfile.chosenLexicographicProfile I m)).hom)

/-- The original total input map is its actual increasing input
enumeration followed by the retained original canonical Fin permutation. -/
theorem chosenTotalInputHom_equiv (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (chosenTotalInputHom X I m).equiv =
      (OrderedProfile.enumeration (OrderedProfile.chosenLexicographicProfile I m)).toEquiv.symm.trans
        (originalFinInputPermutation (Nat.card (Σ i : I, Fin (m i)))) := by
  apply Equiv.ext
  intro p
  let N := Nat.card (Σ i : I, Fin (m i))
  let Q := OrderedProfile.chosenLexicographicProfile I m
  let j : Fin N := (OrderedProfile.enumeration Q).toEquiv.symm p
  change (OrderedProfile.enumeration (OrderedProfile.chosenCanonical N)).toEquiv
      (Fin.cast (OrderedProfile.count_chosenCanonical N).symm j) =
    originalFinInputPermutation N j
  have h := congrArg (fun e => e (Fin.cast (OrderedProfile.count_chosenCanonical N).symm j))
    (OrderedProfile.enumeration_chosenCanonical N)
  have hcast : Fin.cast (OrderedProfile.count_chosenCanonical N)
      (Fin.cast (OrderedProfile.count_chosenCanonical N).symm j) = j := by
    apply Fin.ext
    rfl
  exact h.trans (congrArg (originalFinInputPermutation N) hcast)

private theorem chosenTotalInputHom_targetRank (X : C) (I : FintypeCat.{0}) (m : I → ℕ)
    (p : Σ i : I, Fin (m i)) :
    (enumeration (constantFinFamily (Nat.card (Σ i : I, Fin (m i))) X)).symm
        ((chosenTotalInputHom X I m).equiv p) =
      Fin.cast (constantFinFamily_arity (Nat.card (Σ i : I, Fin (m i))) X).symm
        ((OrderedProfile.enumeration (OrderedProfile.chosenLexicographicProfile I m)).toEquiv.symm p) := by
  have h := congrArg (fun e =>
      (enumeration (constantFinFamily (Nat.card (Σ i : I, Fin (m i))) X)).symm (e p))
    (chosenTotalInputHom_equiv X I m)
  exact h.trans
    ((enumeration (constantFinFamily (Nat.card (Σ i : I, Fin (m i))) X)).symm_apply_apply _)

private theorem chosenTotalEnumeration_inverse (I : FintypeCat.{0}) (m : I → ℕ)
    (p : Σ i : I, Fin (m i)) :
    (OrderedProfile.enumeration (OrderedProfile.chosenLexicographicProfile I m)).toEquiv.symm p =
      Fin.cast (OrderedProfile.chosenLexicographic_count I m).symm
        ((OrderedProfile.chosenLexicographicInputEquiv I m).symm p) := by
  have h := congrArg (fun e => e.symm p) (OrderedProfile.enumeration_chosenLexicographic I m)
  exact h

/-- The actual normalized chosen-profile permutation is the original
finite flatten-to-word permutation with its exact target-count transport. -/
theorem chosenTotalInputHom_enumerated (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    enumeratedEquiv (chosenTotalInputHom X I m) =
      (flattenWordEquiv (originalLeafBlocks X I m)).trans
        (finCongr ((originalLeafBlocks_total X I m).trans
          ((OrderedProfile.chosenLexicographic_count I m).symm.trans
            (constantFinFamily_arity (Nat.card (Σ i : I, Fin (m i))) X).symm))) := by
  apply Equiv.ext
  intro p
  apply Fin.ext
  let q := enumeration (flattenedOriginalFamily (originalLeafBlocks X I m)) p
  have h1 := congrArg Fin.val (chosenTotalInputHom_targetRank X I m q)
  have h2 := congrArg Fin.val (chosenTotalEnumeration_inverse I m q)
  have h3 := congrArg (fun e => (e p).val) (originalLeafBlocks_flattenWordEquiv X I m)
  exact h1.trans (h2.trans h3.symm)

private theorem equiv_postcast_heq {a b c : ℕ} (h : b = c) (e : Fin a ≃ Fin b) :
    HEq (e.trans (finCongr h)) e := by
  cases h
  rfl

/-- The actual original chosen total profile map has exactly the
original flattening permutation, preserving its source count transports. -/
theorem chosenTotalInputHom_enumerated_heq (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    HEq (enumeratedEquiv (chosenTotalInputHom X I m))
      (flattenWordEquiv (originalLeafBlocks X I m)) :=
  (heq_of_eq (chosenTotalInputHom_enumerated X I m)).trans
    (equiv_postcast_heq _ _)



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenTotalInputPermutation

/- Source proof segment: OriginalLeafBlockTensorFlatten -/
section source_OriginalLeafBlockTensorFlatten
/-!
# Original finite leaf flattening recovers the actual word-power block map

Only the constructed monoidal comparisons and the original constant-input
object equalities are used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorPower TensorWord

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original unchanged-index inner constant-tensor comparisons
to the original binary powers. -/
def originalLeafPowerComparisons (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteFamily.map finiteTensorFunctor).obj (originalLeafBlocks X I m) ⟶
      originalFiniteBlockFamily X I m :=
  fixedIndexHom I (fun i => eqToHom (finiteTensorFunctor_constant_obj (m i) X))

omit [MonoidalCategory C] [SymmetricCategory C] in
private theorem fixedIndexHom_eqToHom (I : FintypeCat.{0}) {A B : I → C} (h : A = B) :
    fixedIndexHom I (fun i => eqToHom (congrFun h i)) =
      eqToHom (congrArg (fun F : I → C => (⟨I, F⟩ : FiniteFamily C)) h) := by
  cases h
  rfl

/-- The original family of actual inner tensors equals the original
binary-power family through the source constant-tensor comparisons. -/
theorem originalLeafPowerFamilyEq (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteFamily.map finiteTensorFunctor).obj (originalLeafBlocks X I m) =
      originalFiniteBlockFamily X I m :=
  congrArg (fun F : I → C => (⟨I, F⟩ : FiniteFamily C))
    (funext (fun i => finiteTensorFunctor_constant_obj (m i) X))

/-- Tensoring the actual original inner comparisons gives their
exact original object-equality map. -/
theorem originalLeafPowerComparisons_map (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    finiteTensorFunctor.map (originalLeafPowerComparisons X I m) =
      eqToHom (congrArg finiteTensorFunctor.obj (originalLeafPowerFamilyEq X I m)) := by
  have h : originalLeafPowerComparisons X I m = eqToHom (originalLeafPowerFamilyEq X I m) :=
    fixedIndexHom_eqToHom I (funext (fun i => finiteTensorFunctor_constant_obj (m i) X))
  rw [h, eqToHom_map]

omit [SymmetricCategory C] in
/-- The actual original flattened block input tensor is its supplied
total binary power, with the original block equality retained. -/
theorem originalLeafWordInputObjEq (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    obj (blocksOfFiniteFamily (originalLeafBlocks X I m)).inputs =
      tensorPowObj X (orderedBlockLength (originalEnumeratedBlockLengths I m)) :=
  (blocks_obj_transport (originalLeafBlocks_blocks X I m)).trans
    (originalWordBlocks_inputTensor X (originalEnumeratedBlockLengths I m))

omit [SymmetricCategory C] in
private theorem blocksFlatten_heq {B B' : Blocks C} (h : B = B') :
    HEq B.flattenIso.hom B'.flattenIso.hom := by
  cases h
  rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
private theorem threeEqualityMaps_heq {A B D E F : C} (f : A ⟶ B)
    (h1 : B = D) (h2 : D = E) (h3 : E = F) :
    HEq ((f ≫ eqToHom h1) ≫ eqToHom h2 ≫ eqToHom h3) f := by
  rw [eqToHom_trans]
  exact (comp_eqToHom_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The original block flattening followed by the original inner
power comparisons is the original word-block power flattening. -/
theorem originalLeafFamilyBlocks_power (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (finiteFamilyBlocksIso (originalLeafBlocks X I m)).hom ≫
        finiteTensorFunctor.map (originalLeafPowerComparisons X I m) ≫
        (originalFiniteWordSourceIso X I m).hom =
      eqToHom (originalLeafWordInputObjEq X I m) ≫
        (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).hom := by
  have hnormal :
      (finiteFamilyBlocksIso (originalLeafBlocks X I m)).hom ≫
          eqToHom (congrArg finiteTensorFunctor.obj (originalLeafPowerFamilyEq X I m)) ≫
          (originalFiniteWordSourceIso X I m).hom =
        eqToHom (originalLeafWordInputObjEq X I m) ≫
          (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).hom := by
    apply eq_of_heq
    change HEq
      (((blocksOfFiniteFamily (originalLeafBlocks X I m)).flattenIso.hom ≫
          eqToHom (blocksOfFamily_tensors
            ((originalLeafBlocks X I m).obj ∘ enumeration (originalLeafBlocks X I m)))) ≫
        eqToHom (congrArg finiteTensorFunctor.obj (originalLeafPowerFamilyEq X I m)) ≫
          eqToHom (orderedBlockTensor_eq_ordered X (originalEnumeratedBlockLengths I m)).symm)
      (eqToHom (originalLeafWordInputObjEq X I m) ≫
        (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).hom)
    have hraw := (blocksFlatten_heq (originalLeafBlocks_blocks X I m)).trans
      ((originalWordBlocks_flatten_heq X (originalEnumeratedBlockLengths I m)).trans
        (heq_of_eq (congrArg Iso.hom
          (originalWordBlockPowerIso_eq X (originalEnumeratedBlockLengths I m)))).symm)
    apply HEq.trans (b := (blocksOfFiniteFamily (originalLeafBlocks X I m)).flattenIso.hom)
    · exact threeEqualityMaps_heq _ _ _ _
    · exact hraw.trans (eqToHom_comp_heq _ _).symm
  have hstep := congrArg (fun f => (finiteFamilyBlocksIso (originalLeafBlocks X I m)).hom ≫
      f ≫ (originalFiniteWordSourceIso X I m).hom) (originalLeafPowerComparisons_map X I m)
  exact hstep.trans hnormal

omit [MonoidalCategory C] [SymmetricCategory C] in
private theorem originalFlattenCancellation {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D)
    (c : D ⟶ E) (d : E ⟶ F) {N : C} (q : B ⟶ N) (e : N ≅ F)
    (h : b ≫ c ≫ d = q ≫ e.hom) :
    (a ≫ b) ≫ c ≫ d ≫ e.inv = a ≫ q := by
  calc
    (a ≫ b) ≫ c ≫ d ≫ e.inv = a ≫ (b ≫ c ≫ d) ≫ e.inv := by
      simp only [Category.assoc]
    _ = a ≫ (q ≫ e.hom) ≫ e.inv := by rw [h]
    _ = a ≫ q := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual source finite flattening and original power comparisons,
followed by the original block-concatenation inverse, retain the exact
original total-input permutation map. -/
theorem originalLeafFlatten_power_inverse (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (finiteFlattenIso (originalLeafBlocks X I m)).hom ≫
        finiteTensorFunctor.map (originalLeafPowerComparisons X I m) ≫
        (originalFiniteWordSourceIso X I m).hom ≫
        (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv =
      (flattenToWordIso (originalLeafBlocks X I m)).hom ≫
        eqToHom (originalLeafWordInputObjEq X I m) := by
  exact originalFlattenCancellation
    (flattenToWordIso (originalLeafBlocks X I m)).hom
    (finiteFamilyBlocksIso (originalLeafBlocks X I m)).hom
    (finiteTensorFunctor.map (originalLeafPowerComparisons X I m))
    (originalFiniteWordSourceIso X I m).hom
    (eqToHom (originalLeafWordInputObjEq X I m))
    (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m))
    (originalLeafFamilyBlocks_power X I m)



end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_OriginalLeafBlockTensorFlatten

/- Source proof segment: WordPowerCarrierNaturality -/
section source_WordPowerCarrierNaturality
/-!
# Original finite tensor-power and word carrier maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.StrandNaturality

open CategoryTheory Limits MonoidalCategory

private theorem powerCarrierFromComponents {V : Type*} [Category* V]
    {A B X Y : V} (f : A ⟶ B) (g : X ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (a' : A ⟶ X) (b' : B ⟶ Y)
    (ha : a = a') (hb : b = b') (h : f ≫ b' = a' ≫ g) : f ≫ b = a ≫ g := by
  rw [ha, hb]
  exact h

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the word power carrier naturality construction. -/
local instance wordPowerCarrierNaturalityFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The original finite-word carrier map is exactly the source
binary finite tensor functor's constant original input map. -/
theorem wordTensorCarrierMap_source {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (wordTensorCarrierMap f).app (Discrete.mk n) =
      (OrderedTensor.finiteTensorPowerFunctor (C := C) n).map f := rfl

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The original finite word/power comparison has its actual
source object identification, with no chosen-rank identity hypothesis. -/
theorem associativeWordPowerIso_hom_app (X : C) (n : Discrete ℕ) :
    (associativeWordPowerIso X).hom.app n =
      eqToHom (OrderedTensor.finiteTensorFunctor_constant_obj n.as X) := by
  change 𝟙 _ ≫ eqToHom (OrderedTensor.finiteTensorFunctor_constant_obj n.as X) = _
  exact Category.id_comp _

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- Every original carrier map commutes with the original
source finite tensor/power comparison at every word length. -/
theorem associativeWordPowerIso_carrier {X Y : C} (f : X ⟶ Y) (n : Discrete ℕ) :
    (wordTensorCarrierMap f).app n ≫ (associativeWordPowerIso Y).hom.app n =
      (associativeWordPowerIso X).hom.app n ≫ TensorPower.tensorPowMap f n.as :=
  powerCarrierFromComponents _ _ _ _ _ _ (associativeWordPowerIso_hom_app X n)
    (associativeWordPowerIso_hom_app Y n)
    (OrderedTensor.finiteTensorPower_comparison_naturality n.as f)



end CategoryTheory.Operad.Tensor.Associative.StrandNaturality
end
end
end source_WordPowerCarrierNaturality

/- Source proof segment: ChosenTotalInputTensorMap -/
section source_ChosenTotalInputTensorMap
/-!
# The actual chosen total tensor map is the original flattened word map

All original input permutations and equality components are compared
before transporting their original source and target tensor carriers.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory MonoidalCategory OrderedTensor TensorPower TensorWord

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
private theorem originalLeafBlocks_inputs (X : C) (I : FintypeCat.{0}) (m : I → ℕ)
    (j : Fin (blocksOfFiniteFamily (originalLeafBlocks X I m)).totalArity) :
    (blocksOfFiniteFamily (originalLeafBlocks X I m)).inputs j = X :=
  (blocks_inputs_transport (originalLeafBlocks_blocks X I m) j).trans
    (originalWordBlocks_inputs X (originalEnumeratedBlockLengths I m) _)

omit [MonoidalCategory C] [SymmetricCategory C] in
private theorem equalityMap_identity_heq {A B : C} (h : A = B) :
    HEq (eqToHom h) (𝟙 A) := by
  cases h
  rfl

/-- The actual source chosen total finite tensor map is exactly
the original total-input flattening map, with all original counts retained. -/
theorem chosenTotalInputHom_map_heq (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    HEq (finiteTensorFunctor.map (chosenTotalInputHom X I m))
      (flattenToWord (originalLeafBlocks X I m)) := by
  let N := Nat.card (Σ i : I, Fin (m i))
  let B := blocksOfFiniteFamily (originalLeafBlocks X I m)
  let hcount : arity (constantFinFamily N X) = B.totalArity :=
    (constantFinFamily_arity N X).trans
      ((OrderedProfile.chosenLexicographic_count I m).trans (originalLeafBlocks_total X I m).symm)
  change HEq (mapEquiv (enumeratedEquiv (chosenTotalInputHom X I m))
      (enumeratedMap (chosenTotalInputHom X I m)))
    (mapEquiv (flattenWordEquiv (originalLeafBlocks X I m))
      (fun i => eqToHom (flattenWord_objects (originalLeafBlocks X I m) i)))
  apply mapEquiv_input_heq rfl hcount
    (orderedFamily (flattenedOriginalFamily (originalLeafBlocks X I m)))
    (orderedFamily (flattenedOriginalFamily (originalLeafBlocks X I m)))
    (orderedFamily (constantFinFamily N X)) B.inputs
    (fun _ => rfl) (fun i => (originalLeafBlocks_inputs X I m (Fin.cast hcount i)).symm)
    (enumeratedEquiv (chosenTotalInputHom X I m))
    (flattenWordEquiv (originalLeafBlocks X I m))
    (chosenTotalInputHom_enumerated_heq X I m)
  intro i
  have h1 : HEq (enumeratedMap (chosenTotalInputHom X I m) i) (𝟙 X) := by
    change HEq (eqToHom (rfl : X = X) ≫ eqToHom (rfl : X = X)) (𝟙 X)
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  have h2 : HEq (eqToHom (flattenWord_objects (originalLeafBlocks X I m) i)) (𝟙 X) :=
    equalityMap_identity_heq _
  exact h1.trans h2.symm

/-- The actual original chosen total finite input tensor reaches
the total binary word power through the original flatten permutation
and the original exact total-count transport. -/
theorem chosenTotalInputHom_map_power (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    finiteTensorFunctor.map (chosenTotalInputHom X I m) ≫
        eqToHom (finiteTensorFunctor_constant_obj (Nat.card (Σ i : I, Fin (m i))) X) =
      (flattenToWordIso (originalLeafBlocks X I m)).hom ≫
        eqToHom (originalLeafWordInputObjEq X I m) ≫
        eqToHom (congrArg (tensorPowObj X) (OrderedProfile.chosenLexicographic_count I m).symm) := by
  have hr : HEq
      ((flattenToWordIso (originalLeafBlocks X I m)).hom ≫
        eqToHom (originalLeafWordInputObjEq X I m) ≫
        eqToHom (congrArg (tensorPowObj X) (OrderedProfile.chosenLexicographic_count I m).symm))
      (flattenToWord (originalLeafBlocks X I m)) := by
    rw [eqToHom_trans]
    exact (comp_eqToHom_heq _ _).trans
      (heq_of_eq (flattenToWordIso_hom (originalLeafBlocks X I m)))
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans ((chosenTotalInputHom_map_heq X I m).trans hr.symm)



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenTotalInputTensorMap

/- Source proof segment: ChosenTotalWordFlatten -/
section source_ChosenTotalWordFlatten
/-!
# The actual chosen total word tensor map is the original finite block flattening

The original outer enumeration, every original inner Fin permutation,
and the exact total dependent-sum cardinality transport are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory OrderedTensor TensorPower TensorWord

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen total word flatten construction. -/
local instance chosenTotalWordFlattenFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual chosen total operation-order tensor map retains its
original increasing profile/input map and source constant-power comparison. -/
theorem chosenTotalOrderedPowerIso_source (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (chosenAssociativeOrderedPowerIso X (OrderedProfile.chosenLexicographicProfile I m).profile
      ((ULift.up (OrderedProfile.chosenLexicographicProfile I m).order) :
        liftedOrderFunctor.{us}.obj (OrderedProfile.chosenLexicographicProfile I m).profile)).hom =
      finiteTensorFunctor.map (chosenTotalInputHom X I m) ≫
        eqToHom (finiteTensorFunctor_constant_obj (Nat.card (Σ i : I, Fin (m i))) X) := by
  let Q := OrderedProfile.chosenLexicographicProfile I m
  change (chosenOrderedTensorLengthIso X).hom.app Q ≫
      (associativeWordPowerIso X).hom.app (Discrete.mk (OrderedProfile.count Q)) = _
  exact congrArg₂ (fun f g => f ≫ g)
    (StrandNaturality.chosenOrderedTensorLengthIso_hom_app X Q)
    (StrandNaturality.associativeWordPowerIso_hom_app X (Discrete.mk (OrderedProfile.count Q)))

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual source chosen lexicographic total tensor map equals
the original finite leaf flattening, unchanged-index inner power maps,
and original block-word concatenation inverse. All original empty and
unary inputs and the exact dependent-sum cardinality transport are retained. -/
theorem chosenTotalOrderedPowerIso_flatten (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (chosenAssociativeOrderedPowerIso X (OrderedProfile.chosenLexicographicProfile I m).profile
      ((ULift.up (OrderedProfile.chosenLexicographicProfile I m).order) :
        liftedOrderFunctor.{us}.obj (OrderedProfile.chosenLexicographicProfile I m).profile)).hom =
      ((FiniteTensor.flattenIso (V := C)).hom.app (originalLeafBlocks X I m) ≫
        (FiniteTensor.tensor (V := C)).map (originalLeafPowerComparisons X I m) ≫
        (originalFiniteWordSourceIso X I m).hom ≫
        (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv) ≫
        eqToHom (congrArg (tensorPowObj X) (OrderedProfile.chosenLexicographic_count I m).symm) := by
  let q := eqToHom (congrArg (tensorPowObj X) (OrderedProfile.chosenLexicographic_count I m).symm)
  have h1 := chosenTotalOrderedPowerIso_source X I m
  have h2 := chosenTotalInputHom_map_power X I m
  have h3 := congrArg (fun f => f ≫ q) (originalLeafFlatten_power_inverse X I m)
  exact h1.trans (h2.trans ((Category.assoc _ _ _).symm.trans h3.symm))



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenTotalWordFlatten

/- Source proof segment: ChosenCanonicalFreeWordEvaluation -/
section source_ChosenCanonicalFreeWordEvaluation
/-!
# Original canonical-root free operations evaluate by original word concatenation
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory OrderedTensor TensorPower TensorWord
open CategoryTheory.FiniteTensor.UnitCopower ChosenWordCopies

private theorem inverseFlattenWord {V : Type*} [Category* V]
    {A B L N Q : V} (e : A ≅ B) (p : A ⟶ N) (j : B ⟶ L)
    (c : L ⟶ N) (iN : N ⟶ Q) (iL : L ⟶ Q)
    (hp : p = e.hom ≫ (j ≫ c)) (hc : c ≫ iN = iL) :
    e.inv ≫ (p ≫ iN) = j ≫ iL := by
  rw [hp]
  simp only [Category.assoc]
  rw [e.inv_hom_id_assoc, hc]

/-- The actual associative substitution of the original chosen
root and every original chosen inner coefficient is exactly the
actual chosen lexicographic order on the original dependent sum. -/
theorem chosenWordLexicographic (I : FintypeCat.{0}) (m : I → ℕ) :
    associativeLexicographic.{us} (chosenWordSubstitution I m) (chosenWordCoefficients.{us} I m) =
      ULift.up (OrderedProfile.chosenLexicographicProfile I m).order := by
  apply ULift.ext
  apply LinearOrder.ext
  intro a b
  rfl

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen canonical free word evaluation construction. -/
local instance chosenCanonicalFreeWordEvaluationFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

omit [SymmetricCategory C] [MonoidalClosed C] in
private theorem countTransportWordInjection (X : C) {n m : ℕ} (h : n = m) :
    eqToHom (congrArg (tensorPowObj X) h) ≫ tensorWordι X m = tensorWordι X n := by
  cases h
  exact Category.id_comp _

omit [MonoidalClosed C] in
/-- The original total-leaf flatten inverse and actual chosen
total operation map recover the original finite block power map
and original concatenated word injection, with every strand and
the original total count transport retained. -/
theorem chosenTotalLeafWordConcatenation (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (FiniteTensor.flattenIso (V := C)).inv.app (originalLeafBlocks X I m) ≫
      (chosenAssociativeOrderedPowerIso X (OrderedProfile.chosenLexicographicProfile I m).profile
        ((ULift.up (OrderedProfile.chosenLexicographicProfile I m).order) :
          liftedOrderFunctor.{us}.obj (OrderedProfile.chosenLexicographicProfile I m).profile)).hom ≫
      tensorWordι X (Nat.card (Σ i : I, Fin (m i))) =
    (FiniteTensor.tensor (V := C)).map (originalLeafPowerComparisons X I m) ≫
      (originalFiniteWordSourceIso X I m).hom ≫
      (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv ≫
      tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m)) := by
  let e := (FiniteTensor.flattenIso (V := C)).app (originalLeafBlocks X I m)
  let p := (chosenAssociativeOrderedPowerIso X (OrderedProfile.chosenLexicographicProfile I m).profile
    ((ULift.up (OrderedProfile.chosenLexicographicProfile I m).order) :
      liftedOrderFunctor.{us}.obj (OrderedProfile.chosenLexicographicProfile I m).profile)).hom
  let j := (FiniteTensor.tensor (V := C)).map (originalLeafPowerComparisons X I m) ≫
    (originalFiniteWordSourceIso X I m).hom ≫
    (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv
  let c := eqToHom (congrArg (tensorPowObj X) (OrderedProfile.chosenLexicographic_count I m).symm)
  have hp : p = e.hom ≫ (j ≫ c) := by
    exact (chosenTotalOrderedPowerIso_flatten.{u, v, us} X I m).trans
      (Category.assoc e.hom j c)
  have hc : c ≫ tensorWordι X (Nat.card (Σ i : I, Fin (m i))) =
      tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m)) :=
    countTransportWordInjection X (OrderedProfile.chosenLexicographic_count I m).symm
  have h := inverseFlattenWord e p j c (tensorWordι X (Nat.card (Σ i : I, Fin (m i))))
    (tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m))) hp hc
  exact h.trans
    ((Category.assoc ((FiniteTensor.tensor (V := C)).map (originalLeafPowerComparisons X I m))
      ((originalFiniteWordSourceIso X I m).hom ≫
        (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv)
      (tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m)))).trans
      (congrArg (fun k => (FiniteTensor.tensor (V := C)).map
        (originalLeafPowerComparisons X I m) ≫ k)
        (Category.assoc _ _ _)))

/-- The actual original assembled root and inner free operation
is the original finite block concatenation under the exact source
unit/input normalization, including all empty and unary blocks. -/
theorem chosenAssembledFreeWordConcatenation (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    chosenWordAssembledInputs X I m ≫
      freeOperation.{0, v, u, us} (associativeOperad C) (fun _ : PUnit.{1} => X)
        (OrderedProfile.chosenOuterProfile I).profile ≫
      (chosenAssociativeTensorWordsIso X).hom =
    (FiniteTensor.flattenIso (V := C)).hom.app
        (InputCopies.unitNestedFactors X (chosenWordSubstitution I m)) ≫
      (FiniteTensor.tensor (V := C)).map
        (UnitWordNormalization.blockUnitCollapse X (chosenWordSubstitution I m)) ≫
      (unitCoefficientTensorIso
        (UnitWordNormalization.evaluatedLeaves X (chosenWordSubstitution I m))).hom ≫
      (FiniteTensor.tensor (V := C)).map (originalLeafPowerComparisons X I m) ≫
      (originalFiniteWordSourceIso X I m).hom ≫
      (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv ≫
      tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m)) := by
  let s := chosenWordSubstitution I m
  let T := FiniteTensor.tensor (V := C)
  let p := (chosenAssociativeOrderedPowerIso X (OrderedProfile.chosenLexicographicProfile I m).profile
    ((ULift.up (OrderedProfile.chosenLexicographicProfile I m).order) :
      liftedOrderFunctor.{us}.obj (OrderedProfile.chosenLexicographicProfile I m).profile)).hom
  let i := tensorWordι X (Nat.card (Σ k : I, Fin (m k)))
  let r := (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s)
  let b := T.map (UnitWordNormalization.blockUnitCollapse X s)
  let u := (unitCoefficientTensorIso (UnitWordNormalization.evaluatedLeaves X s)).hom
  let e := (FiniteTensor.flattenIso (V := C)).app (originalLeafBlocks X I m)
  let j := T.map (originalLeafPowerComparisons X I m) ≫
    (originalFiniteWordSourceIso X I m).hom ≫
    (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv ≫
    tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m))
  have ha : chosenWordAssembledInputs X I m ≫
      freeOperation.{0, v, u, us} (associativeOperad C) (fun _ : PUnit.{1} => X)
        (OrderedProfile.chosenOuterProfile I).profile ≫
      (chosenAssociativeTensorWordsIso X).hom =
        UnitWordNormalization.totalInputNormalizer X s ≫ (p ≫ i) := by
    have h := chosenAssembledFreeWordEvaluation.{u, v, us} X s.inner (chosenWordCoefficients.{us} I m)
    change chosenWordAssembledInputs X I m ≫
      freeOperation.{0, v, u, us} (associativeOperad C) (fun _ : PUnit.{1} => X)
        (OrderedProfile.chosenOuterProfile I).profile ≫
      (chosenAssociativeTensorWordsIso X).hom =
      UnitWordNormalization.totalInputNormalizer X s ≫
        (chosenAssociativeOrderedPowerIso X (profileInputs s.totalProfile)
          (associativeLexicographic.{us} s (chosenWordCoefficients.{us} I m))).hom ≫
        tensorWordι X (Nat.card s.totalProfile.inputs) at h
    rw [chosenWordLexicographic I m] at h
    exact h
  have hn : UnitWordNormalization.totalInputNormalizer X s = r ≫ (b ≫ (u ≫ e.inv)) :=
    UnitWordNormalization.unitSourceIso_block_normalization_original X s
  have hc : e.inv ≫ (p ≫ i) = j := chosenTotalLeafWordConcatenation.{u, v, us} X I m
  have h : UnitWordNormalization.totalInputNormalizer X s ≫ (p ≫ i) = r ≫ (b ≫ (u ≫ j)) :=
    (congrArg (· ≫ (p ≫ i)) hn).trans
      ((Category.assoc _ _ _).trans
        (congrArg (r ≫ ·) ((Category.assoc _ _ _).trans
          (congrArg (b ≫ ·) ((Category.assoc _ _ _).trans (congrArg (u ≫ ·) hc))))))
  exact ha.trans h





end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenCanonicalFreeWordEvaluation

/- Source proof segment: ChosenWordInnerPowerAlignment -/
section source_ChosenWordInnerPowerAlignment
/-!
# The original chosen inner Fin word comparison is the source constant-power map

The actual chosen outer order on the original Fin input is its chosen
canonical order. Every original count transport is retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies

open CategoryTheory Limits MonoidalCategory OrderedTensor TensorPower TensorWord
open OrderedProfile

attribute [local instance] FintypeCat.fintype

/-- The actual source chosen outer Fin order equals the original
chosen canonical Fin order, without identifying either enumeration with identity. -/
theorem chosenOuterOrder_fin (n : ℕ) :
    chosenOuterOrder (FintypeCat.of (Fin n)) = (chosenCanonical n).order := by
  apply LinearOrder.ext
  intro a b
  rfl

/-- The original chosen outer Fin profile is the original chosen
canonical Fin profile, with its actual source order unchanged. -/
theorem chosenOuterProfile_fin (n : ℕ) :
    chosenOuterProfile (FintypeCat.of (Fin n)) = chosenCanonical n :=
  congrArg (fun o : LinearOrder (Fin n) =>
    ({ profile := (chosenCanonical n).profile, order := o } : OrderedProfile)) (chosenOuterOrder_fin n)

private theorem threeEqualityMaps {V : Type*} [Category* V]
    {A B D E : V} (h1 : A = B) (h2 : B = D) (h3 : D = E) (h4 : A = E) :
    (eqToHom h1 ≫ eqToHom h2) ≫ eqToHom h3 = eqToHom h4 := by
  rw [Category.assoc, eqToHom_trans, eqToHom_trans]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen word inner power alignment construction. -/
local instance chosenWordInnerPowerAlignmentFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The original selected inner power comparison retains its
exact original source ordered-power map and count transport. -/
theorem chosenWordInnerPowerIso_route (X : C) (n : ℕ) :
    (chosenWordInnerPowerIso.{u, v, us} X n).hom =
      (chosenAssociativeOrderedPowerIso.{u, v, us} X (chosenCanonical n).profile
        (ULift.up (chosenCanonical n).order)).hom ≫
        eqToHom (congrArg (tensorPowObj X) (Nat.card_fin n)) := rfl

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual chosen inner Fin power map is exactly the original
source constant-Fin tensor/power equality map, retaining the
cardinality-to-Nat.card-to-supplied-degree transports. -/
theorem chosenWordInnerPowerIso_hom (X : C) (n : ℕ) :
    (chosenWordInnerPowerIso.{u, v, us} X n).hom =
      eqToHom (finiteTensorFunctor_constant_obj n X) := by
  let I := FintypeCat.of (Fin n)
  let q := eqToHom (congrArg (tensorPowObj X) (Nat.card_fin n))
  have ho := congrArg (fun o : LinearOrder (Fin n) =>
    (chosenAssociativeOrderedPowerIso.{u, v, us} X (chosenCanonical n).profile (ULift.up o)).hom)
      (chosenOuterOrder_fin n)
  have h := congrArg (fun f => f ≫ q) (chosenOuterPowerComparison.{u, v, us} X I)
  have hc :
      (eqToHom (obj_constant X (@Fintype.card I (@FintypeCat.fintype I))) ≫
        eqToHom (congrArg (tensorPowObj X) (@Fintype.card_eq_nat_card I (@FintypeCat.fintype I)))) ≫ q =
      eqToHom (finiteTensorFunctor_constant_obj n X) :=
    threeEqualityMaps _ _ _ _
  exact (chosenWordInnerPowerIso_route X n).trans
    ((congrArg (fun f => f ≫ q) ho.symm).trans (h.trans hc))



end CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies
end
end
end source_ChosenWordInnerPowerAlignment

/- Source proof segment: ChosenBlockPowerAlignment -/
section source_ChosenBlockPowerAlignment
/-!
# Actual original chosen block power comparisons agree with source unit removal

The original Option-I component maps are identified before applying
the produced finite tensor. Unit removal uses its proved naturality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies

open CategoryTheory Limits MonoidalCategory OrderedTensor TensorWord

attribute [local instance] FintypeCat.fintype

private theorem unitBlockTensorJoin {V : Type*} [Category* V]
    {A B D E F G H : V} (f : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E)
    (c : B ⟶ F) (d : F ⟶ E) (u : E ⟶ G) (v : F ⟶ H) (w : H ⟶ G)
    (h1 : a ≫ b = c ≫ d) (h2 : d ≫ u = v ≫ w) :
    (f ≫ a) ≫ (b ≫ u) = f ≫ c ≫ v ≫ w := by
  rw [Category.assoc, ← Category.assoc a b, h1, Category.assoc c d, h2]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen block power alignment construction. -/
local instance chosenBlockPowerAlignmentFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual original chosen block comparisons and root identity
family map are precisely actual block unit collapse followed by every
original constant-Fin power comparison, on the unchanged Option-I index. -/
theorem chosenWordBlockFactorsIso_unitMaps (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (chosenWordBlockFactorsIso.{u, v, us} X I m).hom ≫ (chosenRootWordSourceFactorsIso X I m).hom =
      UnitWordNormalization.blockUnitCollapse X (chosenWordSubstitution I m) ≫
        coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C))
          (originalLeafPowerComparisons X I m) := by
  apply FiniteFamily.Hom_ext
  · ext o
    cases o <;> rfl
  · intro o
    cases o with
    | none =>
        with_unfolding_all
          change HEq
            ((FiniteTensor.singletonIso (V := C)).hom.app
              (FiniteTensor.UnitCopower.unitObject C) ≫ 𝟙 _)
            ((FiniteTensor.singletonIso (V := C)).hom.app
              (FiniteTensor.UnitCopower.unitObject C) ≫ 𝟙 _)
          rfl
    | some i =>
        with_unfolding_all
          change HEq
            (((unitCoefficientTensorIso (constantFinFamily (m i) X)).hom ≫
              (chosenWordInnerPowerIso.{u, v, us} X (m i)).hom) ≫ 𝟙 _)
            ((unitCoefficientTensorIso (constantFinFamily (m i) X)).hom ≫
              eqToHom (finiteTensorFunctor_constant_obj (m i) X))
          exact heq_of_eq ((Category.comp_id _).trans
            (congrArg (fun f => (unitCoefficientTensorIso (constantFinFamily (m i) X)).hom ≫ f)
              (chosenWordInnerPowerIso_hom X (m i))))

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The actual chosen original block source comparison followed by
original root unit removal agrees with original finite flattening,
actual block unit collapse, source unit removal, and every original
inner constant-Fin power comparison. Empty root and inner inputs are retained. -/
theorem chosenWordBlockSourceIso_unitRemoval (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    (chosenWordBlockSourceIso.{u, v, us} X I m).hom ≫ (chosenRootWordInputRemovalIso X I m).hom =
      (FiniteTensor.flattenIso (V := C)).hom.app
        (InputCopies.unitNestedFactors X (chosenWordSubstitution I m)) ≫
      (FiniteTensor.tensor (V := C)).map
        (UnitWordNormalization.blockUnitCollapse X (chosenWordSubstitution I m)) ≫
      (unitCoefficientTensorIso
        (UnitWordNormalization.evaluatedLeaves X (chosenWordSubstitution I m))).hom ≫
      (FiniteTensor.tensor (V := C)).map (originalLeafPowerComparisons X I m) := by
  let T := FiniteTensor.tensor (V := C)
  let a := (chosenWordBlockFactorsIso.{u, v, us} X I m).hom
  let b := (chosenRootWordSourceFactorsIso X I m).hom
  let c := UnitWordNormalization.blockUnitCollapse X (chosenWordSubstitution I m)
  let d := coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C))
    (originalLeafPowerComparisons X I m)
  have hmaps : T.map a ≫ T.map b = T.map c ≫ T.map d :=
    (T.map_comp a b).symm.trans
      ((congrArg T.map (chosenWordBlockFactorsIso_unitMaps X I m)).trans (T.map_comp c d))
  have hunit := unitCoefficientTensorIso_naturality (originalLeafPowerComparisons X I m)
  exact unitBlockTensorJoin
    ((FiniteTensor.flattenIso (V := C)).hom.app
      (InputCopies.unitNestedFactors X (chosenWordSubstitution I m)))
    (T.map a) (T.map b) (T.map c) (T.map d)
    (unitCoefficientTensorIso (originalFiniteBlockFamily X I m)).hom
    (unitCoefficientTensorIso
      (UnitWordNormalization.evaluatedLeaves X (chosenWordSubstitution I m))).hom
    (T.map (originalLeafPowerComparisons X I m)) hmaps hunit



end CategoryTheory.Operad.Tensor.Associative.ChosenWordCopies
end
end
end source_ChosenBlockPowerAlignment

/- Source proof segment: ChosenRootFreeWordInputEvaluation -/
section source_ChosenRootFreeWordInputEvaluation
/-!
# Actual original free As operations on all original copied word inputs
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory OrderedTensor TensorWord
open CategoryTheory.FiniteTensor.UnitCopower OrderedProfile ChosenWordCopies

private theorem copiedOperationFromOriginalNormalization {V : Type*} [Category* V]
    {S D A B F Q R T U L Z : V} (e : S ≅ D)
    (i : D ⟶ A) (c : A ⟶ B) (v : B ⟶ F) (f : F ⟶ Q) (w : Q ⟶ Z)
    (assembled : S ⟶ F) (op : B ⟶ Z) (rem : D ⟶ L) (j : L ⟶ Z)
    (r : S ⟶ R) (b : R ⟶ T) (u : T ⟶ U) (p : U ⟶ L)
    (hcop : assembled = e.hom ≫ (i ≫ (c ≫ v)))
    (hop : op = v ≫ (f ≫ w))
    (heval : assembled ≫ (f ≫ w) = r ≫ (b ≫ (u ≫ (p ≫ j))))
    (hnorm : e.hom ≫ rem = r ≫ (b ≫ (u ≫ p))) :
    i ≫ (c ≫ op) = rem ≫ j := by
  apply (cancel_epi e.hom).1
  have hi : e.hom ≫ (i ≫ (c ≫ op)) = assembled ≫ (f ≫ w) := by
    rw [hop, ← Category.assoc c v (f ≫ w), ← Category.assoc i (c ≫ v) (f ≫ w),
      ← Category.assoc e.hom (i ≫ (c ≫ v)) (f ≫ w), ← hcop]
  have hn : r ≫ (b ≫ (u ≫ (p ≫ j))) = (e.hom ≫ rem) ≫ j := by
    rw [hnorm]
    simp only [Category.assoc]
  exact hi.trans (heval.trans (hn.trans (Category.assoc _ _ _)))

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen root free word input evaluation construction. -/
local instance chosenRootFreeWordInputEvaluationFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- Every original copied finite word input, including each
empty and unary input, evaluates the ACTUAL constructed free As
operation by original block concatenation through the proved
source strand adjustment. No operation preservation is assumed. -/
theorem chosenRootWordInputs_freeOperation (X : C) (I : FintypeCat.{0}) (m : I → ℕ) :
    wordInputInjection X I m ≫
      associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
        (ULift.up (chosenOuterOrder I)) ≫
      (conjugatedFreeWordOperations X).app PUnit.unit (chosenOuterProfile I).profile =
    (chosenRootWordInputRemovalIso X I m).hom ≫
      (originalFiniteWordSourceIso X I m).hom ≫
      (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv ≫
      tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m)) := by
  let T := FiniteTensor.tensor (V := C)
  let s := chosenWordSubstitution I m
  let e := chosenWordBlockSourceIso.{u, v, us} X I m
  let i := wordInputInjection X I m
  let c := associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
    (ULift.up (chosenOuterOrder I))
  let v := (analyticSummandCarrierMap (associativeOperad C).toCollection (chosenWordCarrierIso X).inv).app
    (chosenOuterProfile I).profile
  let f := freeOperation.{0, v, u, us} (associativeOperad C) (fun _ : PUnit.{1} => X)
    (chosenOuterProfile I).profile
  let w := (chosenAssociativeTensorWordsIso X).hom
  let assembled := chosenWordAssembledInputs X I m
  let op := (conjugatedFreeWordOperations X).app PUnit.unit (chosenOuterProfile I).profile
  let rem := (chosenRootWordInputRemovalIso X I m).hom
  let j := (originalFiniteWordSourceIso X I m).hom ≫
    (originalWordBlockPowerIso X (originalEnumeratedBlockLengths I m)).inv ≫
    tensorWordι X (orderedBlockLength (originalEnumeratedBlockLengths I m))
  let r := (FiniteTensor.flattenIso (V := C)).hom.app (InputCopies.unitNestedFactors X s)
  let b := T.map (UnitWordNormalization.blockUnitCollapse X s)
  let u := (unitCoefficientTensorIso (UnitWordNormalization.evaluatedLeaves X s)).hom
  let p := T.map (originalLeafPowerComparisons X I m)
  have hcop : assembled = e.hom ≫ (i ≫ (c ≫ v)) :=
    chosenWordAssembledInputs_eq_wordInputs X I m
  have hop : op = v ≫ (f ≫ w) := conjugatedFreeWordOperations_app X (chosenOuterProfile I).profile
  have heval : assembled ≫ (f ≫ w) = r ≫ (b ≫ (u ≫ (p ≫ j))) :=
    chosenAssembledFreeWordConcatenation X I m
  have hnorm : e.hom ≫ rem = r ≫ (b ≫ (u ≫ p)) :=
    chosenWordBlockSourceIso_unitRemoval X I m
  exact copiedOperationFromOriginalNormalization e i c v f w assembled op rem j r b u p hcop hop heval hnorm



end CategoryTheory.Operad.Tensor.Associative
end
end
end source_ChosenRootFreeWordInputEvaluation

/- Source proof segment: AssociativeOperationWordBasisExt -/
section source_AssociativeOperationWordBasisExt
/-!
# Actual original coefficient and word-input copies detect full As operations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative operation word basis ext construction. -/
local instance associativeOperationWordBasisExtFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)

/-- Full original As operation maps on word inputs agree if
every original lifted order coefficient and every original finite
word degree tuple agree under their ACTUAL finite tensor injections. -/
theorem associativeWordOperation_hom_ext (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) {Z : C}
    {f g : (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)).obj P ⟶ Z}
    (h : ∀ (o : liftedOrderFunctor.{us}.obj P) (m : P.inputs → ℕ),
      wordInputInjection X P.inputs m ≫
        associativeProfileCoefficientInjection (TensorWord.tensorWordObj X) P o ≫ f =
      wordInputInjection X P.inputs m ≫
        associativeProfileCoefficientInjection (TensorWord.tensorWordObj X) P o ≫ g) : f = g := by
  apply associativeCoefficientOperation_hom_ext (TensorWord.tensorWordObj X) P
  intro o
  apply wordInputCoefficientTensor_hom_ext X P.inputs
  intro m
  exact h o m

/-- The original equivariant As operation families on word
inputs are determined by ALL original coefficient and finite word
input tuples; the source coproduct and tensor colimits are proved. -/
theorem associativeWordOperations_ext (X : C)
    {a b : Operations (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)
      (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)}
    (h : ∀ (P : AnalyticIndex PUnit.{1} PUnit.unit)
      (o : liftedOrderFunctor.{us}.obj P) (m : P.inputs → ℕ),
      wordInputInjection X P.inputs m ≫ associativeProfileCoefficientInjection (TensorWord.tensorWordObj X) P o ≫
          a.app PUnit.unit P =
      wordInputInjection X P.inputs m ≫ associativeProfileCoefficientInjection (TensorWord.tensorWordObj X) P o ≫
          b.app PUnit.unit P) : a = b := by
  apply Operations.ext
  funext d
  cases d
  funext P
  exact associativeWordOperation_hom_ext X P (h P)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOperationWordBasisExt

/- Source proof segment: AssociativeChosenRootReduction -/
section source_AssociativeChosenRootReduction
/-!
# Original associative root-order relabeling detects all word operations
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory OrderedProfile TensorWord

private theorem coefficientRelabelFromOriginalSquares {V : Type*} [Category* V]
    {A B D E R S U Z : V} (eP : B ≅ R) (eQ : D ≅ S)
    (cP : A ⟶ B) (cQ : E ⟶ D) (d : B ⟶ D) (p : A ⟶ E)
    (uP : A ⟶ U) (uQ : E ⟶ Z) (iP : U ⟶ R) (iQ : Z ⟶ S)
    (t : U ⟶ Z) (s : R ⟶ S)
    (hn : d ≫ eQ.hom = eP.hom ≫ s)
    (hP : cP ≫ eP.hom = uP ≫ iP) (hQ : cQ ≫ eQ.hom = uQ ≫ iQ)
    (hs : iP ≫ s = t ≫ iQ) (hu : p ≫ uQ = uP ≫ t) :
    cP ≫ d = p ≫ cQ := by
  apply (cancel_mono eQ.hom).1
  rw [Category.assoc cP d eQ.hom, hn, ← Category.assoc cP eP.hom s,
    hP, Category.assoc uP iP s, hs, ← Category.assoc uP t iQ, ← hu,
    Category.assoc p uQ iQ, ← hQ, ← Category.assoc p cQ eQ.hom]

/-- Increasingly relabel the supplied original operation order
to the actual chosen outer order on its original finite input type. -/
def chosenRootRelabel (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : liftedOrderFunctor.{us}.obj P) : P ⟶ (chosenOuterProfile P.inputs).profile :=
  OrderedProfile.forget.map
    (homOfCountEq (⟨P, o.down⟩ : OrderedProfile) (chosenOuterProfile P.inputs) rfl)

/-- The actual source associative coefficient action sends the
supplied original root order to the actual chosen source root order. -/
theorem chosenRootRelabel_order (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : liftedOrderFunctor.{us}.obj P) :
    (liftedOrderFunctor.map (chosenRootRelabel P o)) o = ULift.up (chosenOuterOrder P.inputs) := by
  apply ULift.ext
  exact (liftedOrderFunctor_map_down (chosenRootRelabel P o) o).trans
    (orderFunctor_map_order
      (homOfCountEq (⟨P, o.down⟩ : OrderedProfile) (chosenOuterProfile P.inputs) rfl))

section GenericTensor

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

/-- Original coefficient injections and every original leaf
input bijection commute with the actual profile tensor map. -/
theorem associativeProfileCoefficientInjection_relabel (X : C)
    {P Q : AnalyticIndex PUnit.{1} PUnit.unit} (f : P ⟶ Q)
    (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection X P o ≫
        (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (fun _ : PUnit.{1} => X)).map f =
      (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C))
          ((analyticInputFamily (fun _ : PUnit.{1} => X)).map f)) ≫
        associativeProfileCoefficientInjection X Q ((liftedOrderFunctor.map f) o) := by
  let T := FiniteTensor.tensor (V := C)
  let eP := associativeProfileTensorIso X P
  let eQ := associativeProfileTensorIso X Q
  let cP := associativeProfileCoefficientInjection X P o
  let cQ := associativeProfileCoefficientInjection X Q ((liftedOrderFunctor.map f) o)
  let d := (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
    (fun _ : PUnit.{1} => X)).map f
  let l := (analyticInputFamily (fun _ : PUnit.{1} => X)).map f
  let p := T.map (coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) l)
  let t := T.map l
  let uP := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).hom
  let uQ := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj Q)).hom
  let iP := Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj P =>
    T.obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) o
  let iQ := Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj Q =>
    T.obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj Q)) ((liftedOrderFunctor.map f) o)
  let s :
      (∐ (fun _ : liftedOrderFunctor.{us}.obj P =>
        T.obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P))) ⟶
      (∐ (fun _ : liftedOrderFunctor.{us}.obj Q =>
        T.obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj Q))) :=
    Sigma.map' (liftedOrderFunctor.map f) (fun _ => t)
  have hn : d ≫ eQ.hom = eP.hom ≫ s := associativeProfileTensorIso_naturality X f
  have hP : cP ≫ eP.hom = uP ≫ iP := associativeProfileCoefficientInjection_β X P o
  have hQ : cQ ≫ eQ.hom = uQ ≫ iQ :=
    associativeProfileCoefficientInjection_β X Q ((liftedOrderFunctor.map f) o)
  have hs : iP ≫ s = t ≫ iQ :=
    Sigma.ι_comp_map'
      (f := fun _ : liftedOrderFunctor.{us}.obj Q =>
        T.obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj Q))
      (g := fun _ : liftedOrderFunctor.{us}.obj P =>
        T.obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P))
      (liftedOrderFunctor.map f) (fun _ => t) o
  have hu : p ≫ uQ = uP ≫ t := unitCoefficientTensorIso_naturality l
  exact coefficientRelabelFromOriginalSquares eP eQ cP cQ d p uP uQ iP iQ t s hn hP hQ hs hu

end GenericTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative chosen root reduction construction. -/
local instance associativeChosenRootReductionFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)

/-- The actual chosen root coefficient operations determine
every original associative word operation. All other original root
orders and profiles are reduced by their actual source relabeling. -/
theorem associativeWordOperations_eq_of_chosenRoot (X : C)
    {a b : Operations (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => tensorWordObj X) (fun _ : PUnit.{1} => tensorWordObj X)}
    (h : ∀ I : FintypeCat.{0},
      associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
          (ULift.up (chosenOuterOrder I)) ≫ a.app PUnit.unit (chosenOuterProfile I).profile =
      associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile I).profile
          (ULift.up (chosenOuterOrder I)) ≫ b.app PUnit.unit (chosenOuterProfile I).profile) : a = b := by
  apply Operations.ext
  funext d
  cases d
  funext P
  apply associativeCoefficientOperation_hom_ext (tensorWordObj X) P
  intro o
  let f := chosenRootRelabel P o
  let l := (analyticInputFamily (fun _ : PUnit.{1} => tensorWordObj X)).map f
  let p := (FiniteTensor.tensor (V := C)).map
    (coefficientLeafMap (𝟙 (FiniteTensor.UnitCopower.unitObject C)) l)
  let cP := associativeProfileCoefficientInjection (tensorWordObj X) P o
  let cQ := associativeProfileCoefficientInjection (tensorWordObj X) (chosenOuterProfile P.inputs).profile
    (ULift.up (chosenOuterOrder P.inputs))
  let t := (analyticSummand (FiniteTensor.UnitCopower.associativeOperad C).toCollection
    (fun _ : PUnit.{1} => tensorWordObj X)).map f
  have hc : cP ≫ t = p ≫ cQ :=
    (associativeProfileCoefficientInjection_relabel (tensorWordObj X) f o).trans
      (congrArg (fun k => p ≫ associativeProfileCoefficientInjection (tensorWordObj X)
        (chosenOuterProfile P.inputs).profile k) (chosenRootRelabel_order P o))
  have ha : cP ≫ a.app PUnit.unit P = p ≫ (cQ ≫ a.app PUnit.unit (chosenOuterProfile P.inputs).profile) :=
    (congrArg (cP ≫ ·) (a.equivariance PUnit.unit f).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a.app PUnit.unit (chosenOuterProfile P.inputs).profile) hc).trans
          (Category.assoc _ _ _)))
  have hb : cP ≫ b.app PUnit.unit P = p ≫ (cQ ≫ b.app PUnit.unit (chosenOuterProfile P.inputs).profile) :=
    (congrArg (cP ≫ ·) (b.equivariance PUnit.unit f).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ b.app PUnit.unit (chosenOuterProfile P.inputs).profile) hc).trans
          (Category.assoc _ _ _)))
  exact ha.trans ((congrArg (p ≫ ·) (h P.inputs)).trans hb.symm)





end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeChosenRootReduction

/- Source proof segment: AssociativeFreeOperationsAreWordEvaluation -/
section source_AssociativeFreeOperationsAreWordEvaluation
/-!
# Actual original free associative tensor operations are original word evaluation
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory TensorWord OrderedProfile

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative free operations are word evaluation construction. -/
local instance associativeFreeOperationsAreWordEvaluationFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The ACTUAL original free associative tensor algebra operation
family, carried to the original words by its proved source strand
isomorphism, equals the actual public tensor-word evaluation family.
Every original operation/order/input map is covered by genuine
coefficient and word-input colimit extensionality. -/
theorem conjugatedFreeWordOperations_eq_wordEvaluationOperations (X : C) :
    conjugatedFreeWordOperations X = wordEvaluationOperations X := by
  apply associativeWordOperations_eq_of_chosenRoot X
  intro I
  apply wordInputCoefficientTensor_hom_ext X I
  intro m
  exact (chosenRootWordInputs_freeOperation X I m).trans
    (chosenRootWordInputs_evaluation X I m).symm

/-- The ACTUAL original free operadic action equals the original
word-monoid extension after the proved source strand map; this
follows by descending the full actual operation equality. -/
theorem conjugatedFreeWordAction_eq_wordEvaluationAction (X : C) :
    conjugatedFreeWordAction X = wordEvaluationAction X :=
  (conjugatedFreeWordOperations_desc X).symm.trans
    ((congrArg Operations.desc (conjugatedFreeWordOperations_eq_wordEvaluationOperations X)).trans
      (wordEvaluationOperations_desc X))

/-- Every original finite-profile operation, including nullary
and unary operations, is the actual tensor-word evaluation operation. -/
theorem conjugatedFreeWordOperations_app_eq (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    (conjugatedFreeWordOperations X).app PUnit.unit P =
      (wordEvaluationOperations X).app PUnit.unit P :=
  congrArg (fun a => a.app PUnit.unit P) (conjugatedFreeWordOperations_eq_wordEvaluationOperations X)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeFreeOperationsAreWordEvaluation

/- Source proof segment: ProfileCoefficientCarrierNaturality -/
section source_ProfileCoefficientCarrierNaturality
/-!
# Original associative coefficient injections are natural in the original carrier
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.StrandNaturality

open CategoryTheory Limits FiniteFamily
open CategoryTheory.FiniteTensor.UnitCopower

private theorem profileCopyNaturality {V : Type*} [Category* V]
    {DX DY SX SY AX AY : V} (u : DX ⟶ DY) (ix : DX ⟶ SX) (iy : DY ⟶ SY)
    (a : SX ⟶ SY) (px : SX ⟶ AX) (py : SY ⟶ AY) (t : AX ⟶ AY)
    (hi : u ≫ iy = ix ≫ a) (hp : px ≫ t = a ≫ py) :
    u ≫ (iy ≫ py) = ix ≫ (px ≫ t) := by
  rw [← Category.assoc u iy, hi, Category.assoc ix a, ← hp]

private theorem normalizedCopyNaturality {V : Type*} [Category* V]
    {TX TY DX DY AX AY : V} (ex : DX ≅ TX) (ey : DY ≅ TY)
    (f : TX ⟶ TY) (u : DX ⟶ DY) (jx : DX ⟶ AX) (jy : DY ⟶ AY) (t : AX ⟶ AY)
    (he : f ≫ ey.inv = ex.inv ≫ u) (hj : u ≫ jy = jx ≫ t) :
    f ≫ (ey.inv ≫ jy) = (ex.inv ≫ jx) ≫ t := by
  rw [← Category.assoc f ey.inv, he, Category.assoc ex.inv u, hj, Category.assoc ex.inv jx]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual original unit coefficient and input carrier map
commute with every original coefficient-copy factor injection. -/
theorem coefficientCopyFactors_carrier {X Y : C} (f : X ⟶ Y)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    coefficientLeafMap (𝟙 (unitObject C))
        ((analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f)).app P) ≫
      InputCopies.innerCopyFactors Y P o =
    InputCopies.innerCopyFactors X P o ≫
      (analyticFactorsCarrierMap (associativeOperad C).toCollection
        (fun _ : PUnit.{1} => f)).app P := by
  apply FiniteFamily.Hom_ext
  · ext i
    cases i <;> rfl
  · intro i
    cases i with
    | none =>
      exact heq_of_eq ((Category.id_comp _).trans (Category.comp_id _).symm)
    | some i =>
      exact heq_of_eq ((Category.comp_id f).trans (Category.id_comp f).symm)

/-- The original associative coefficient/input tensor-copy
injection is natural under every original carrier map. -/
theorem profileCoefficientInjection_carrier {X Y : C} (f : X ⟶ Y)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap (𝟙 (unitObject C))
          ((analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f)).app P)) ≫
      associativeProfileCoefficientInjection Y P o =
    associativeProfileCoefficientInjection X P o ≫
      (analyticSummandCarrierMap (associativeOperad C).toCollection
        (fun _ : PUnit.{1} => f)).app P := by
  let T := FiniteTensor.tensor (V := C)
  let l := (analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f)).app P
  have h := (T.map_comp _ _).symm.trans
    ((congrArg T.map (coefficientCopyFactors_carrier f P o)).trans (T.map_comp _ _))
  have hx := InputCopies.innerCopyFactors_tensor X P o
  have hy := InputCopies.innerCopyFactors_tensor Y P o
  exact (congrArg (fun q => T.map (coefficientLeafMap (𝟙 (unitObject C)) l) ≫ q) hy.symm).trans
    (h.trans (congrArg (fun q => q ≫
      (analyticSummandCarrierMap (associativeOperad C).toCollection
        (fun _ : PUnit.{1} => f)).app P) hx))

/-- Every original coefficient copy followed by the actual profile
quotient injection is natural under the original carrier map. -/
theorem profileCoefficientQuotient_carrier {X Y : C} (f : X ⟶ Y)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    (FiniteTensor.tensor (V := C)).map
        (coefficientLeafMap (𝟙 (unitObject C))
          ((analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f)).app P)) ≫
      associativeProfileCoefficientInjection Y P o ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => Y) P =
    associativeProfileCoefficientInjection X P o ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P ≫
      profileMap (associativeOperad C).toCollection (fun _ : PUnit.{1} => f) PUnit.unit :=
  profileCopyNaturality _ _ _ _ _ _ _ (profileCoefficientInjection_carrier f P o)
    (profileι_map (associativeOperad C).toCollection (fun _ : PUnit.{1} => f) P)

/-- The original input tensor's actual ordered coefficient-copy
profile injection, with its original unit coefficient removed. -/
def normalizedProfileCoefficientInjection (X : C) (P : AnalyticIndex PUnit.{1} PUnit.unit)
    (o : liftedOrderFunctor.{us}.obj P) :
    (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P) ⟶
      profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) PUnit.unit :=
  (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)).inv ≫
    associativeProfileCoefficientInjection X P o ≫
    profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P

/-- The actual normalized original ordered-profile injection is
natural under each original carrier map, with the original finite
input map retained. -/
theorem normalizedProfileCoefficientInjection_carrier {X Y : C} (f : X ⟶ Y)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    (inputTensorCarrierMap f).app P ≫ normalizedProfileCoefficientInjection Y P o =
      normalizedProfileCoefficientInjection X P o ≫
        profileMap (associativeOperad C).toCollection (fun _ : PUnit.{1} => f) PUnit.unit :=
  normalizedCopyNaturality
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P))
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => Y)).obj P))
    ((inputTensorCarrierMap f).app P)
    ((FiniteTensor.tensor (V := C)).map
      (coefficientLeafMap (𝟙 (unitObject C))
        ((analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f)).app P)))
    (associativeProfileCoefficientInjection X P o ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P)
    (associativeProfileCoefficientInjection Y P o ≫
      profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => Y) P)
    (profileMap (associativeOperad C).toCollection (fun _ : PUnit.{1} => f) PUnit.unit)
    (unitCoefficientTensorIso_inv_naturality
      ((analyticInputCarrierMap (d := PUnit.unit) (fun _ : PUnit.{1} => f)).app P))
    ((profileCoefficientQuotient_carrier f P o).trans (Category.assoc _ _ _).symm)



end CategoryTheory.Operad.Tensor.Associative.StrandNaturality
end
end
end source_ProfileCoefficientCarrierNaturality

/- Source proof segment: ChosenWordCopyNaturality -/
section source_ChosenWordCopyNaturality
/-!
# The source-corrected word comparison is natural on original coefficient copies
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.StrandNaturality

open CategoryTheory Limits MonoidalCategory

private theorem compositeCarrierSquare {V : Type*} [Category* V]
    {A B X Y PX PY : V} (f : A ⟶ B) (ax : A ⟶ X) (ay : B ⟶ Y)
    (w : X ⟶ Y) (bx : X ⟶ PX) (bY : Y ⟶ PY) (p : PX ⟶ PY)
    (ha : f ≫ ay = ax ≫ w) (hb : w ≫ bY = bx ≫ p) :
    f ≫ (ay ≫ bY) = (ax ≫ bx) ≫ p := by
  rw [← Category.assoc f ay, ha, Category.assoc ax w, hb, Category.assoc ax bx]

private theorem removeUnitFromCoefficientBeta {V : Type*} [Category* V]
    {D T A W : V} (u : D ≅ T) (i : D ⟶ A) (g : A ⟶ W) (p : T ⟶ W)
    (h : i ≫ g = u.hom ≫ p) : (u.inv ≫ i) ≫ g = p := by
  rw [Category.assoc u.inv i, h, u.inv_hom_id_assoc]

private theorem carrierNaturalityOnInjection {V : Type*} [Category* V]
    {TX TY QX QY WX WY PX PY : V}
    (nx : TX ⟶ QX) (ny : TY ⟶ QY) (c : QX ⟶ QY) (f : TX ⟶ TY)
    (gx : QX ⟶ WX) (gy : QY ⟶ WY) (px : TX ⟶ PX) (py : TY ⟶ PY)
    (ix : PX ⟶ WX) (iy : PY ⟶ WY) (p : PX ⟶ PY) (w : WX ⟶ WY)
    (hn : nx ≫ c = f ≫ ny) (hx : nx ≫ gx = px ≫ ix)
    (hy : ny ≫ gy = py ≫ iy) (hp : f ≫ py = px ≫ p) (hw : p ≫ iy = ix ≫ w) :
    nx ≫ (c ≫ gy) = nx ≫ (gx ≫ w) := by
  rw [← Category.assoc nx c, hn, Category.assoc f ny, hy,
    ← Category.assoc f py, hp, Category.assoc px p, hw,
    ← Category.assoc px ix, ← hx, Category.assoc nx gx]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen word copy naturality construction. -/
local instance chosenWordCopyNaturalityFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

omit [MonoidalClosed C] [HasColimitsOfSize.{us, us} C] in
/-- The source chosen increasing input/power comparison is
natural under each original carrier map, with its actual chosen
canonical profile map unchanged. -/
theorem chosenAssociativeOrderedPowerIso_carrier {X Y : C} (f : X ⟶ Y)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    (inputTensorCarrierMap f).app P ≫ (chosenAssociativeOrderedPowerIso Y P o).hom =
      (chosenAssociativeOrderedPowerIso X P o).hom ≫ TensorPower.tensorPowMap f (Nat.card P.inputs) := by
  let J := LiftedOrderFiber.orderedEquivalence.functor.obj ⟨P, Discrete.mk o⟩
  let n := OrderedProfile.countFunctor.obj J
  exact compositeCarrierSquare
    ((inputTensorCarrierMap f).app P)
    ((chosenOrderedTensorLengthIso X).hom.app J) ((chosenOrderedTensorLengthIso Y).hom.app J)
    ((wordTensorCarrierMap f).app n)
    ((associativeWordPowerIso X).hom.app n) ((associativeWordPowerIso Y).hom.app n)
    (TensorPower.tensorPowMap f (Nat.card P.inputs))
    (chosenOrderedTensorLengthIso_carrier f J) (associativeWordPowerIso_carrier f n)

/-- Every original normalized coefficient/profile injection
reaches its actual chosen increasing original word injection. -/
theorem normalizedProfileCoefficientInjection_chosenWord (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    normalizedProfileCoefficientInjection X P o ≫ (chosenAssociativeTensorWordsIso X).hom =
      (chosenAssociativeOrderedPowerIso X P o).hom ≫ TensorWord.tensorWordι X (Nat.card P.inputs) :=
  removeUnitFromCoefficientBeta
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P))
    (associativeProfileCoefficientInjection X P o ≫
      profileι (FiniteTensor.UnitCopower.associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P)
    (chosenAssociativeTensorWordsIso X).hom
    ((chosenAssociativeOrderedPowerIso X P o).hom ≫ TensorWord.tensorWordι X (Nat.card P.inputs))
    ((Category.assoc _ _ _).trans (chosenAssociativeTensorWordsIso_coefficient X P o))

/-- Carrier naturality of the corrected complete quotient/word
comparison after every actual original normalized profile coefficient
copy; it uses actual source maps and the original tensor-word map. -/
theorem chosenTensorWordsIso_copy_carrier {X Y : C} (f : X ⟶ Y)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    normalizedProfileCoefficientInjection X P o ≫
        (profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (fun _ : PUnit.{1} => f) PUnit.unit ≫ (chosenAssociativeTensorWordsIso Y).hom) =
      normalizedProfileCoefficientInjection X P o ≫
        ((chosenAssociativeTensorWordsIso X).hom ≫ TensorWord.tensorWordMap f) :=
  carrierNaturalityOnInjection
    (normalizedProfileCoefficientInjection X P o) (normalizedProfileCoefficientInjection Y P o)
    (profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => f) PUnit.unit)
    ((inputTensorCarrierMap f).app P)
    (chosenAssociativeTensorWordsIso X).hom (chosenAssociativeTensorWordsIso Y).hom
    (chosenAssociativeOrderedPowerIso X P o).hom (chosenAssociativeOrderedPowerIso Y P o).hom
    (TensorWord.tensorWordι X (Nat.card P.inputs)) (TensorWord.tensorWordι Y (Nat.card P.inputs))
    (TensorPower.tensorPowMap f (Nat.card P.inputs)) (TensorWord.tensorWordMap f)
    (normalizedProfileCoefficientInjection_carrier f P o).symm
    (normalizedProfileCoefficientInjection_chosenWord X P o)
    (normalizedProfileCoefficientInjection_chosenWord Y P o)
    (chosenAssociativeOrderedPowerIso_carrier f P o)
    (TensorWord.tensorWordMap_ι f (Nat.card P.inputs)).symm




end CategoryTheory.Operad.Tensor.Associative.StrandNaturality
end
end
end source_ChosenWordCopyNaturality

/- Source proof segment: ProfileCopyDetection -/
section source_ProfileCopyDetection
/-!
# Original normalized coefficient/profile copies detect complete quotient maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.StrandNaturality

open CategoryTheory Limits
open CategoryTheory.FiniteTensor.UnitCopower

private theorem coefficientCopyInverse {V : Type*} [Category* V]
    {D T A S : V} (u : D ≅ T) (e : A ≅ S) (i : D ⟶ A) (j : T ⟶ S)
    (h : i ≫ e.hom = u.hom ≫ j) : j ≫ e.inv = u.inv ≫ i := by
  apply (cancel_mono e.hom).1
  rw [Category.assoc j e.inv, e.inv_hom_id, Category.comp_id,
    Category.assoc u.inv i, h, u.inv_hom_id_assoc]

private theorem weightedCopyTest {V : Type*} [Category* V]
    {T D S U W : V} (e : S ≅ D) (u : U ≅ T) (i : U ⟶ S) (j : T ⟶ D)
    (a b : S ⟶ W) (hj : j ≫ e.inv = u.inv ≫ i)
    (h : (u.inv ≫ i) ≫ a = (u.inv ≫ i) ≫ b) :
    j ≫ (e.inv ≫ a) = j ≫ (e.inv ≫ b) := by
  rw [← Category.assoc j e.inv a, ← Category.assoc j e.inv b, hj]
  exact h

variable {C : Type u} [Category.{v} C] [FiniteTensor C]
variable [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C]

local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- Maps out of the actual complete associative weighted quotient
are detected by every original normalized finite input/coefficient
copy. The proof uses the constructed profile and coefficient copower
colimit isomorphisms, with no detection outcome as a hypothesis. -/
theorem normalizedProfileCoefficientInjection_hom_ext (X : C) {Z : C}
    {a b : profileCoinvariants (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) PUnit.unit ⟶ Z}
    (h : ∀ (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P),
      normalizedProfileCoefficientInjection X P o ≫ a =
        normalizedProfileCoefficientInjection X P o ≫ b) : a = b := by
  apply colimit.hom_ext
  intro P
  let p := profileι (associativeOperad C).toCollection (fun _ : PUnit.{1} => X) P
  let e := associativeProfileTensorIso X P
  change p ≫ a = p ≫ b
  apply (cancel_epi e.inv).1
  apply Sigma.hom_ext
  intro o
  let u := unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)
  let i := associativeProfileCoefficientInjection X P o
  let j := Sigma.ι (fun _ : liftedOrderFunctor.{us}.obj P =>
    (FiniteTensor.tensor (V := C)).obj ((analyticInputFamily (fun _ : PUnit.{1} => X)).obj P)) o
  have hj : j ≫ e.inv = u.inv ≫ i :=
    coefficientCopyInverse u e i j (associativeProfileCoefficientInjection_β X P o)
  have ht : (u.inv ≫ i) ≫ (p ≫ a) = (u.inv ≫ i) ≫ (p ≫ b) := by
    simpa only [u, i, p, normalizedProfileCoefficientInjection, Category.assoc] using h P o
  exact weightedCopyTest e u i j (p ≫ a) (p ≫ b) hj ht



end CategoryTheory.Operad.Tensor.Associative.StrandNaturality
end
end
end source_ProfileCopyDetection

/- Source proof segment: ChosenTensorWordsCarrierNaturality -/
section source_ChosenTensorWordsCarrierNaturality
/-!
# Full original carrier naturality of the source-corrected associative word isomorphism
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v us

namespace CategoryTheory.Operad.Tensor.Associative.StrandNaturality

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the chosen tensor words carrier naturality construction. -/
local instance chosenTensorWordsCarrierNaturalityFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The source-corrected complete associative coefficient-weighted
profile quotient/word carrier isomorphism is natural under EVERY
original carrier map. Original coefficient/profile copies detect
the equality, and their exact chosen input-order maps are retained. -/
theorem chosenAssociativeTensorWordsIso_naturality {X Y : C} (f : X ⟶ Y) :
    profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => f) PUnit.unit ≫ (chosenAssociativeTensorWordsIso Y).hom =
      (chosenAssociativeTensorWordsIso X).hom ≫ TensorWord.tensorWordMap f := by
  apply normalizedProfileCoefficientInjection_hom_ext X
  intro P o
  exact chosenTensorWordsIso_copy_carrier f P o



end CategoryTheory.Operad.Tensor.Associative.StrandNaturality
end
end
end source_ChosenTensorWordsCarrierNaturality

/- Source proof segment: WordEvaluationAlgebra -/
section source_WordEvaluationAlgebra
/-!
# Actual word evaluation is the original free associative tensor algebra
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory TensorWord TensorPower OrderedProfile
open CategoryTheory.FiniteTensor.UnitCopower ChosenWordCopies

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the word evaluation algebra construction. -/
local instance wordEvaluationAlgebraFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- Original word-monoid evaluation satisfies the operadic unit
law because the ACTUAL free As action is its proved original action. -/
theorem wordEvaluationAction_unit (X : C) :
    (profileUnit (associativeOperad.{us, v, u} C)).app (fun _ : PUnit.{1} => tensorWordObj X) ≫
      wordEvaluationAction X = 𝟙 (fun _ : PUnit.{1} => tensorWordObj X) := by
  rw [← conjugatedFreeWordAction_eq_wordEvaluationAction X]
  exact (conjugatedFreeWordEMAlgebra X).unit

/-- Original word evaluation satisfies the full original
operadic substitution law, derived from the ACTUAL free action. -/
theorem wordEvaluationAction_assoc (X : C) :
    profileMultiplication.{0, v, u, us} (associativeOperad.{us, v, u} C)
        (fun _ : PUnit.{1} => tensorWordObj X) ≫ wordEvaluationAction X =
      profileMap (associativeOperad.{us, v, u} C).toCollection (wordEvaluationAction X) ≫
        wordEvaluationAction X := by
  rw [← conjugatedFreeWordAction_eq_wordEvaluationAction X]
  exact (conjugatedFreeWordEMAlgebra X).assoc

/-- The actual original word evaluation maps form an As tensor
algebra, with the unit and every substitution law proved from the
source free operadic algebra. No algebra-law outcome is assumed. -/
def wordEvaluationAlgebra (X : C) : Algebra (associativeOperad.{us, v, u} C) :=
  Algebra.ofAction.{0, v, u, us} (associativeOperad.{us, v, u} C)
    (fun _ : PUnit.{1} => tensorWordObj X) (wordEvaluationAction X)
    (wordEvaluationAction_unit X) (wordEvaluationAction_assoc X)

/-- Every original operation is the actual word evaluation
operation; this is the defining full operation family. -/
theorem wordEvaluationAlgebra_operations (X : C) :
    (wordEvaluationAlgebra X).operations = wordEvaluationOperations X := rfl

/-- The original descended action is the actual word extension. -/
theorem wordEvaluationAlgebra_action (X : C) :
    (wordEvaluationAlgebra X).action = wordEvaluationAction X :=
  Algebra.ofAction_action.{0, v, u, us} (associativeOperad.{us, v, u} C)
    (fun _ : PUnit.{1} => tensorWordObj X) (wordEvaluationAction X)
    (wordEvaluationAction_unit X) (wordEvaluationAction_assoc X)

private theorem wordEvaluationAlgebra_action_conjugated (X : C) :
    (wordEvaluationAlgebra X).action = (conjugatedFreeWordAlgebra X).action :=
  (wordEvaluationAlgebra_action X).trans
    ((conjugatedFreeWordAction_eq_wordEvaluationAction X).symm.trans
      (conjugatedFreeWordAlgebra_action X).symm)

/-- The original corrected carrier map gives an operation-
preserving map from the ACTUAL free As algebra to word evaluation. -/
def wordEvaluationAlgebraHom (X : C) :
    freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X) ⟶
      wordEvaluationAlgebra X :=
  Algebra.Hom.ofActionEquation _ _ (chosenWordCarrierIso X).hom (by
    exact (congrArg (profileMap (associativeOperad.{us, v, u} C).toCollection
      (chosenWordCarrierIso X).hom ≫ ·) (wordEvaluationAlgebra_action_conjugated X)).trans
        (Algebra.action_naturality (conjugatedFreeWordAlgebraHom X)).symm)

/-- The exact inverse original carrier map preserves every
original tensor operation of the actual word evaluation algebra. -/
def wordEvaluationAlgebraInv (X : C) :
    wordEvaluationAlgebra X ⟶
      freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X) :=
  Algebra.Hom.ofActionEquation _ _ (chosenWordCarrierIso X).inv (by
    exact (Algebra.action_naturality (conjugatedFreeWordAlgebraInv X)).symm.trans
      (congrArg (· ≫ (chosenWordCarrierIso X).inv) (wordEvaluationAlgebra_action_conjugated X).symm))

/-- The ACTUAL free associative tensor algebra is the original
word-monoid evaluation algebra, with the original corrected carrier
maps, full operation preservation, and both original inverse laws. -/
def wordEvaluationAlgebraIso (X : C) :
    freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X) ≅
      wordEvaluationAlgebra X where
  hom := wordEvaluationAlgebraHom X
  inv := wordEvaluationAlgebraInv X
  hom_inv_id := Algebra.Hom.ext (chosenWordCarrierIso X).hom_inv_id
  inv_hom_id := Algebra.Hom.ext (chosenWordCarrierIso X).inv_hom_id

@[simp]
theorem wordEvaluationAlgebraIso_hom_carrier (X : C) :
    (wordEvaluationAlgebraIso X).hom.hom = (chosenWordCarrierIso X).hom := rfl

@[simp]
theorem wordEvaluationAlgebraIso_inv_carrier (X : C) :
    (wordEvaluationAlgebraIso X).inv.hom = (chosenWordCarrierIso X).inv := rfl

/-- Both the original coefficient and all original input-order
maps are retained in each actual word evaluation operation. -/
theorem wordEvaluationAlgebra_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection (tensorWordObj X) P o ≫
      (wordEvaluationAlgebra X).operations.app PUnit.unit P =
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => tensorWordObj X)).obj P)).hom ≫
      (chosenAssociativeOrderedPowerIso (tensorWordObj X) P o).hom ≫
      wordConcatenationEvaluation X (Nat.card P.inputs) :=
  wordEvaluationOperations_coefficient X P o

private theorem wordEvaluationCountTransport (X : C) {n m : ℕ} (h : n = m) :
    eqToHom (congrArg (tensorPowObj (tensorWordObj X)) h) ≫ wordConcatenationEvaluation X m =
      wordConcatenationEvaluation X n := by
  cases h
  exact Category.id_comp _

/-- Original chosen canonical coefficients evaluate by the
original finite word evaluator at the supplied word count, with
the actual source count transport retained. -/
theorem wordEvaluationAlgebra_chosen_coefficient (X : C) (n : ℕ) :
    associativeProfileCoefficientInjection (tensorWordObj X) (chosenCanonical n).profile
      (ULift.up (chosenCanonical n).order) ≫
      (wordEvaluationAlgebra X).operations.app PUnit.unit (chosenCanonical n).profile =
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => tensorWordObj X)).obj
      (chosenCanonical n).profile)).hom ≫
      (chosenWordInnerPowerIso.{u, v, us} (tensorWordObj X) n).hom ≫ wordConcatenationEvaluation X n := by
  let u := (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => tensorWordObj X)).obj
    (chosenCanonical n).profile)).hom
  let p := (chosenAssociativeOrderedPowerIso (tensorWordObj X) (chosenCanonical n).profile
    ((ULift.up (chosenCanonical n).order) : liftedOrderFunctor.{us}.obj (chosenCanonical n).profile)).hom
  let c := (chosenWordCountIso (tensorWordObj X) n).hom
  have hc : c ≫ wordConcatenationEvaluation X n = wordConcatenationEvaluation X (Nat.card (Fin n)) :=
    wordEvaluationCountTransport X (Nat.card_fin n)
  have hp : p ≫ wordConcatenationEvaluation X (Nat.card (Fin n)) =
      (chosenWordInnerPowerIso.{u, v, us} (tensorWordObj X) n).hom ≫ wordConcatenationEvaluation X n :=
    (congrArg (p ≫ ·) hc.symm).trans (Category.assoc _ _ _).symm
  exact (wordEvaluationAlgebra_coefficient X (chosenCanonical n).profile
    (ULift.up (chosenCanonical n).order)).trans (congrArg (u ≫ ·) hp)

/-- The original nullary operation is the original degree-zero
word unit, after its actual tensor-unit input comparison. -/
theorem wordEvaluationAlgebra_nullary (X : C) :
    associativeProfileCoefficientInjection (tensorWordObj X) (chosenCanonical 0).profile
      (ULift.up (chosenCanonical 0).order) ≫
      (wordEvaluationAlgebra X).operations.app PUnit.unit (chosenCanonical 0).profile =
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => tensorWordObj X)).obj
      (chosenCanonical 0).profile)).hom ≫
      (chosenWordInnerPowerIso.{u, v, us} (tensorWordObj X) 0).hom ≫ tensorWordOne X := by
  simpa only [wordConcatenationEvaluation_zero] using wordEvaluationAlgebra_chosen_coefficient X 0

/-- The original unary operation evaluates through its actual
source input comparison and the original word-carrier unitor. -/
theorem wordEvaluationAlgebra_unary (X : C) :
    associativeProfileCoefficientInjection (tensorWordObj X) (chosenCanonical 1).profile
      (ULift.up (chosenCanonical 1).order) ≫
      (wordEvaluationAlgebra X).operations.app PUnit.unit (chosenCanonical 1).profile =
    (unitCoefficientTensorIso ((analyticInputFamily (fun _ : PUnit.{1} => tensorWordObj X)).obj
      (chosenCanonical 1).profile)).hom ≫
      (chosenWordInnerPowerIso.{u, v, us} (tensorWordObj X) 1).hom ≫ (λ_ (tensorWordObj X)).hom := by
  simpa only [wordConcatenationEvaluation_one] using wordEvaluationAlgebra_chosen_coefficient X 1

/-- The actual original unary operad-unit insertion is the
identity on the original word carrier. -/
theorem wordEvaluationAlgebra_operadic_unit (X : C) :
    unitInsertion (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => tensorWordObj X) PUnit.unit ≫
      (wordEvaluationAlgebra X).operations.app PUnit.unit (AnalyticIndex.unary PUnit.unit) =
        𝟙 (tensorWordObj X) := (wordEvaluationAlgebra X).unit PUnit.unit

/-- The original free-algebra map on a supplied original carrier
map, carried through both actual corrected word algebra isomorphisms. -/
def wordEvaluationAlgebraMap {X Y : C} (f : X ⟶ Y) : wordEvaluationAlgebra X ⟶ wordEvaluationAlgebra Y :=
  (wordEvaluationAlgebraIso X).inv ≫
    (freeAlgebraFunctor.{0, v, u, us} (associativeOperad.{us, v, u} C)).map (fun _ : PUnit.{1} => f) ≫
      (wordEvaluationAlgebraIso Y).hom

/-- Every original free-algebra carrier map becomes exactly the
original public tensor-word map, through the proved natural source
strand correction. No algebra-map comparison is assumed. -/
theorem wordEvaluationAlgebraMap_carrier {X Y : C} (f : X ⟶ Y) :
    (wordEvaluationAlgebraMap f).hom = fun _ : PUnit.{1} => tensorWordMap f := by
  funext d
  cases d
  change (chosenAssociativeTensorWordsIso X).inv ≫
    (profileMap (associativeOperad.{us, v, u} C).toCollection (fun _ : PUnit.{1} => f) PUnit.unit ≫
      (chosenAssociativeTensorWordsIso Y).hom) = tensorWordMap f
  rw [StrandNaturality.chosenAssociativeTensorWordsIso_naturality f,
    (chosenAssociativeTensorWordsIso X).inv_hom_id_assoc]

/-- The original tensor-word maps form the actual original
word-evaluation algebra functor, preserving every original operation. -/
def wordEvaluationAlgebraFunctor : C ⥤ Algebra (associativeOperad.{us, v, u} C) where
  obj := wordEvaluationAlgebra
  map f := wordEvaluationAlgebraMap f
  map_id X := by
    apply Algebra.Hom.ext
    rw [wordEvaluationAlgebraMap_carrier]
    funext d
    exact tensorWordMap_id X
  map_comp f g := by
    apply Algebra.Hom.ext
    rw [wordEvaluationAlgebraMap_carrier]
    change (fun _ : PUnit.{1} => tensorWordMap (f ≫ g)) =
      (wordEvaluationAlgebraMap f).hom ≫ (wordEvaluationAlgebraMap g).hom
    rw [wordEvaluationAlgebraMap_carrier, wordEvaluationAlgebraMap_carrier]
    funext d
    exact (tensorWordMap_comp f g).symm

/-- The actual one-color free As functor on original carriers. -/
def freeAsWordFamilyFunctor : C ⥤ Algebra (associativeOperad.{us, v, u} C) where
  obj X := freeAlgebra.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X)
  map f := (freeAlgebraFunctor.{0, v, u, us} (associativeOperad.{us, v, u} C)).map (fun _ : PUnit.{1} => f)
  map_id X := (freeAlgebraFunctor.{0, v, u, us} (associativeOperad.{us, v, u} C)).map_id
    (fun _ : PUnit.{1} => X)
  map_comp f g := (freeAlgebraFunctor.{0, v, u, us} (associativeOperad.{us, v, u} C)).map_comp
    (fun _ : PUnit.{1} => f) (fun _ : PUnit.{1} => g)

/-- The full free As algebra isomorphism is natural in every
original carrier map, with the original public word functor maps. -/
def freeAsWordAlgebraIso : freeAsWordFamilyFunctor (C := C) ≅ wordEvaluationAlgebraFunctor :=
  NatIso.ofComponents (fun X => wordEvaluationAlgebraIso.{u, v, us} X) (by
    intro X Y f
    apply Algebra.Hom.ext
    change profileMap (associativeOperad.{us, v, u} C).toCollection (fun _ : PUnit.{1} => f) ≫
        (chosenWordCarrierIso Y).hom =
      (chosenWordCarrierIso X).hom ≫ (wordEvaluationAlgebraMap f).hom
    rw [wordEvaluationAlgebraMap_carrier]
    funext d
    cases d
    exact StrandNaturality.chosenAssociativeTensorWordsIso_naturality f)








end CategoryTheory.Operad.Tensor.Associative
end
end
end source_WordEvaluationAlgebra

/- Source proof segment: AssociativeOriginalFreeWordOperations -/
section source_AssociativeOriginalFreeWordOperations
/-!
# Original free associative operation maps in tensor-word coordinates

These readbacks display the original weighted free operations and
the actual source input/output carrier maps. The profile enumeration
and its strand correction remain in the statement.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative original free word operations construction. -/
local instance associativeOriginalFreeWordOperationsFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original coefficient-weighted free operation, with the
actual corrected word isomorphisms on its inputs and output,
is the original tensor-word evaluation operation at every profile. -/
theorem originalFreeOperation_word_coordinates (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) :
    (analyticSummandCarrierMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (chosenWordCarrierIso X).inv).app P ≫
      freeOperation.{0, v, u, us} (FiniteTensor.UnitCopower.associativeOperad C)
        (fun _ : PUnit.{1} => X) P ≫
      (chosenWordCarrierIso X).hom PUnit.unit =
      (wordEvaluationOperations X).app PUnit.unit P :=
  (conjugatedFreeWordOperations_app X P).symm.trans
    (conjugatedFreeWordOperations_app_eq X P)

/-- Every original order coefficient copy of the free operation
evaluates by the exact increasingly ordered word inputs and the
original word concatenation, including the empty input family. -/
theorem originalFreeOperation_word_coefficient (X : C)
    (P : AnalyticIndex PUnit.{1} PUnit.unit) (o : liftedOrderFunctor.{us}.obj P) :
    associativeProfileCoefficientInjection (TensorWord.tensorWordObj X) P o ≫
      ((analyticSummandCarrierMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
          (chosenWordCarrierIso X).inv).app P ≫
        freeOperation.{0, v, u, us} (FiniteTensor.UnitCopower.associativeOperad C)
          (fun _ : PUnit.{1} => X) P ≫
        (chosenWordCarrierIso X).hom PUnit.unit) =
      (unitCoefficientTensorIso
        ((analyticInputFamily (fun _ : PUnit.{1} => TensorWord.tensorWordObj X)).obj P)).hom ≫
      (chosenAssociativeOrderedPowerIso (TensorWord.tensorWordObj X) P o).hom ≫
      TensorWord.wordConcatenationEvaluation X (Nat.card P.inputs) :=
  (congrArg (associativeProfileCoefficientInjection (TensorWord.tensorWordObj X) P o ≫ ·)
      (originalFreeOperation_word_coordinates X P)).trans
    (wordEvaluationOperations_coefficient X P o)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOriginalFreeWordOperations

/- Source proof segment: CorrectedAssociativeWordMonoid -/
section source_CorrectedAssociativeWordMonoid
/-!
# The tensor-word free monoid on the exact corrected As carrier

The carrier is the original operation-weighted profile coinvariant.
Its original free operations are identified with word evaluation
through this same chosen strand correction, not an enumeration
identity. The word of degree zero is retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem originalMonoidRestriction {V : Type*} [Category* V]
    {X W A M : V} (g : X ⟶ W) (i : W ⟶ A) (f : A ⟶ M) :
    g ≫ (i ≫ f ≫ 𝟙 M) = (g ≫ i) ≫ f := by
  simp only [Category.comp_id, Category.assoc]

private theorem originalMonoidExtension {V : Type*} [Category* V]
    {A W M : V} (i : A ⟶ W) (f : W ⟶ M) :
    i ≫ f ≫ 𝟙 M = i ≫ f := by
  simp only [Category.comp_id]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the corrected associative word monoid construction. -/
local instance correctedAssociativeWordMonoidFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual free As profile carrier, with the tensor-word
monoid structure carried through the exact source strand correction.
All original free operations use this same correction by
`originalFreeOperation_word_coefficient`. -/
def correctedAssociativeWordMon (X : C) : Mon C :=
  let : MonObj (profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) PUnit.unit) :=
    MonObj.ofIso (chosenAssociativeTensorWordsIso X).symm
  Mon.mk (profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
    (fun _ : PUnit.{1} => X) PUnit.unit)

/-- The exact source carrier map and inverse preserve the actual
tensor-word multiplication and unit. -/
def correctedAssociativeWordMonIso (X : C) :
    correctedAssociativeWordMon X ≅ TensorWord.tensorWordMon X := by
  let e := chosenAssociativeTensorWordsIso X
  let : MonObj (profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => X) PUnit.unit) := MonObj.ofIso e.symm
  let : IsMonHom e.inv := CategoryTheory.isMonHom_ofIso e.symm
  exact (Mon.mkIso' e.symm).symm

@[simp]
theorem correctedAssociativeWordMonIso_hom_carrier (X : C) :
    (correctedAssociativeWordMonIso X).hom.hom = (chosenAssociativeTensorWordsIso X).hom := rfl

@[simp]
theorem correctedAssociativeWordMonIso_inv_carrier (X : C) :
    (correctedAssociativeWordMonIso X).inv.hom = (chosenAssociativeTensorWordsIso X).inv := rfl

/-- The original degree-zero tensor-unit summand is the monoid
unit on the actual operation-weighted free carrier. -/
theorem correctedAssociativeWordMon_one (X : C) :
    (correctedAssociativeWordMon X).mon.one =
      TensorWord.tensorWordOne X ≫ (chosenAssociativeTensorWordsIso X).inv := rfl

/-- Its multiplication is the original word concatenation with
the actual input and output carrier comparisons. -/
theorem correctedAssociativeWordMon_mul (X : C) :
    (correctedAssociativeWordMon X).mon.mul =
      ((chosenAssociativeTensorWordsIso X).hom ⊗ₘ (chosenAssociativeTensorWordsIso X).hom) ≫
        TensorWord.tensorWordMul X ≫ (chosenAssociativeTensorWordsIso X).inv := rfl

/-- The actual tensor-word generator on the source free carrier. -/
def correctedAssociativeWordGenerator (X : C) : X ⟶ (correctedAssociativeWordMon X).X :=
  TensorWord.tensorWordGenerator X ≫ (chosenAssociativeTensorWordsIso X).inv

/-- The full free-monoid universal property on the actual source
As carrier, using the exact same correction as every original
operation. Both maps are the original restriction/word extension. -/
def correctedAssociativeWordHomEquiv (X : C) (M : Mon C) :
    (correctedAssociativeWordMon X ⟶ M) ≃ (X ⟶ M.X) :=
  ((correctedAssociativeWordMonIso X).homCongr (Iso.refl M)).trans
    (TensorWord.tensorWordHomEquiv X M).symm

/-- The forward map restricts the actual monoid morphism along
the original source tensor-word generator. -/
theorem correctedAssociativeWordHomEquiv_apply (X : C) (M : Mon C)
    (f : correctedAssociativeWordMon X ⟶ M) :
    correctedAssociativeWordHomEquiv X M f = correctedAssociativeWordGenerator X ≫ f.hom := by
  change TensorWord.tensorWordGenerator X ≫
    ((correctedAssociativeWordMonIso X).inv.hom ≫ f.hom ≫ 𝟙 M.X) = _
  exact originalMonoidRestriction (TensorWord.tensorWordGenerator X)
    (correctedAssociativeWordMonIso X).inv.hom f.hom

/-- The inverse is the original actual word extension after the
source carrier comparison; it preserves multiplication and the
degree-zero unit by the true monoid isomorphism. -/
theorem correctedAssociativeWordHomEquiv_symm_apply (X : C) (M : Mon C) (f : X ⟶ M.X) :
    ((correctedAssociativeWordHomEquiv X M).symm f).hom =
      (chosenAssociativeTensorWordsIso X).hom ≫ TensorWord.tensorWordLift M f := by
  change (correctedAssociativeWordMonIso X).hom.hom ≫
    TensorWord.tensorWordLift M f ≫ 𝟙 M.X = _
  exact originalMonoidExtension (correctedAssociativeWordMonIso X).hom.hom
    (TensorWord.tensorWordLift M f)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_CorrectedAssociativeWordMonoid

/- Source proof segment: AssociativeOperadicWordGenerator -/
section source_AssociativeOperadicWordGenerator
/-!
# The original operadic free generator is the original word generator

The comparison uses actual multiplication and naturality, together
with the original unit equations. No finite enumeration is replaced
by an identity and no unit comparison is supplied as a premise.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem originalSourceUnitMap {V : Type*} [Category* V]
    {A W B TW D : V} (e : A ≅ W) (p : A ⟶ B) (k : B ⟶ TW)
    (h : W ⟶ TW) (a : TW ⟶ W) (q : B ⟶ D) (m : D ⟶ A) (b : A ⟶ D)
    (hn : p ≫ k = e.hom ≫ h) (ha : k ≫ a = q ≫ m ≫ e.hom)
    (hc : p ≫ q = b) (hu : b ≫ m = 𝟙 A) : h ≫ a = 𝟙 W := by
  apply (cancel_epi e.hom).1
  calc
    e.hom ≫ (h ≫ a) = p ≫ (k ≫ a) := by rw [← Category.assoc, ← hn, Category.assoc]
    _ = p ≫ (q ≫ m ≫ e.hom) := congrArg (p ≫ ·) ha
    _ = b ≫ m ≫ e.hom := by rw [← Category.assoc p q, hc]
    _ = e.hom ≫ 𝟙 W := by rw [← Category.assoc b m, hu, Category.id_comp, Category.comp_id]

private theorem originalGeneratorUniqueness {V : Type*} [Category* V]
    {X W TW : V} (g u : X ⟶ W) (h e : W ⟶ TW) (a : TW ⟶ W)
    (hn : u ≫ h = g ≫ e) (hu : e ≫ a = 𝟙 W) (hg : h ≫ a = 𝟙 W) : g = u := by
  calc
    g = g ≫ (e ≫ a) := by rw [hu, Category.comp_id]
    _ = u ≫ (h ≫ a) := by rw [← Category.assoc, ← hn, Category.assoc]
    _ = u := by rw [hg, Category.comp_id]

private theorem originalCarrierGeneratorInverse {V : Type*} [Category* V]
    {X A W : V} (g : X ⟶ A) (e : A ≅ W) (u : X ⟶ W)
    (h : g ≫ e.hom = u) : u ≫ e.inv = g := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the associative operadic word generator construction. -/
local instance associativeOperadicWordGeneratorFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original free operadic unit reaches the actual original
degree-one tensor-word generator through the exact source
strand-corrected carrier map. -/
theorem operadicWordGenerator_eq (X : C) :
    (profileUnit (FiniteTensor.UnitCopower.associativeOperad C)).app
        (fun _ : PUnit.{1} => X) PUnit.unit ≫
      (chosenAssociativeTensorWordsIso X).hom = TensorWord.tensorWordGenerator X := by
  let O := FiniteTensor.UnitCopower.associativeOperad C
  let A : PUnit.{1} → C := fun _ => X
  let eta := (profileUnit O).app A
  let e := chosenAssociativeTensorWordsIso X
  let g : X ⟶ TensorWord.tensorWordObj X := eta PUnit.unit ≫ e.hom
  let G : A ⟶ (fun _ : PUnit.{1} => TensorWord.tensorWordObj X) := fun _ => g
  let q := profileMap O.toCollection (chosenWordCarrierIso X).inv PUnit.unit
  let p := profileMap O.toCollection G PUnit.unit
  let k := (chosenAssociativeTensorWordsIso (TensorWord.tensorWordObj X)).hom
  let m := profileMultiplication.{0, v, u, us} O A PUnit.unit
  let b := profileMap O.toCollection eta PUnit.unit
  let a := TensorWord.tensorWordLift (TensorWord.tensorWordMon X)
    (𝟙 (TensorWord.tensorWordObj X))
  have hG : G ≫ (chosenWordCarrierIso X).inv = eta := by
    funext d
    cases d
    change (eta PUnit.unit ≫ e.hom) ≫ e.inv = eta PUnit.unit
    exact originalCarrierGeneratorInverse (eta PUnit.unit) e (eta PUnit.unit ≫ e.hom) rfl
  have hc : p ≫ q = b :=
    (congrFun (profileMap_comp O.toCollection G (chosenWordCarrierIso X).inv) PUnit.unit).symm.trans
      (congrFun (congrArg (profileMap O.toCollection) hG) PUnit.unit)
  have hn : p ≫ k = e.hom ≫ TensorWord.tensorWordMap g :=
    StrandNaturality.chosenAssociativeTensorWordsIso_naturality g
  have ha : k ≫ a = q ≫ m ≫ e.hom :=
    (congrFun (conjugatedFreeWordAction_eq_wordEvaluationAction X) PUnit.unit).symm
  have hu : b ≫ m = 𝟙 (profileCoinvariants O.toCollection A PUnit.unit) := by
    let E := Pi.eval (fun _ : PUnit.{1} => C) PUnit.unit
    exact (E.map_comp (profileMap O.toCollection eta)
      (profileMultiplication.{0, v, u, us} O A)).symm.trans
        ((congrArg E.map (profileMultiplication_right_unit.{0, v, u, us} O A)).trans
          (E.map_id (profileCoinvariants O.toCollection A)))
  have hg : TensorWord.tensorWordMap g ≫ a = 𝟙 (TensorWord.tensorWordObj X) :=
    originalSourceUnitMap e p k (TensorWord.tensorWordMap g) a q m b hn ha hc hu
  exact originalGeneratorUniqueness g (TensorWord.tensorWordGenerator X)
    (TensorWord.tensorWordMap g) (TensorWord.tensorWordGenerator (TensorWord.tensorWordObj X)) a
    (TensorWord.tensorWordGenerator_naturality g)
    (TensorWord.tensorWordAdjunction_right_triangle (TensorWord.tensorWordMon X)) hg

/-- The source free-monoid generator is exactly the original
operadic free generator, including its original unary coefficient
insertion and profile injection. -/
theorem correctedAssociativeWordGenerator_eq_operadicUnit (X : C) :
    correctedAssociativeWordGenerator X =
      (profileUnit (FiniteTensor.UnitCopower.associativeOperad C)).app
        (fun _ : PUnit.{1} => X) PUnit.unit :=
  originalCarrierGeneratorInverse
    ((profileUnit (FiniteTensor.UnitCopower.associativeOperad C)).app
      (fun _ : PUnit.{1} => X) PUnit.unit)
    (chosenAssociativeTensorWordsIso X) (TensorWord.tensorWordGenerator X) (operadicWordGenerator_eq X)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_AssociativeOperadicWordGenerator

/- Source proof segment: WordEvaluationAlgebraHom -/
section source_WordEvaluationAlgebraHom
/-!
# Full original word algebra Hom equivalence
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory TensorWord
open CategoryTheory.FiniteTensor.UnitCopower

private theorem homCongrSourceRightIdentity {V : Type*} [Category* V]
    {A W B : V} (e : A ≅ W) (h : W ⟶ B) :
    (Iso.homCongr e.symm (Iso.refl B)) h = e.hom ≫ h :=
  congrArg (e.hom ≫ ·) (Category.comp_id h)

private theorem fourMapTargetAssociativity {V : Type*} [Category* V]
    {A B C D E : V} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) :
    a ≫ (b ≫ (c ≫ d)) = (a ≫ (b ≫ c)) ≫ d := by
  simp only [Category.assoc]

/-- Reconstruct the original one-color carrier family map from
its map at the original color, retaining the dependent target family. -/
def singleColorCarrierMap {C : Type u} [Category.{v} C] {X : C}
    (A : PUnit.{1} → C) (f : X ⟶ A PUnit.unit) : (fun _ : PUnit.{1} => X) ⟶ A :=
  fun d => match d with
    | PUnit.unit => f

/-- Evaluation at the original color and the actual dependent
one-color reconstruction are inverse carrier-map operations. -/
def singleColorCarrierHomEquiv {C : Type u} [Category.{v} C] (X : C) (A : PUnit.{1} → C) :
    ((fun _ : PUnit.{1} => X) ⟶ A) ≃ (X ⟶ A PUnit.unit) where
  toFun f := f PUnit.unit
  invFun f := singleColorCarrierMap A f
  left_inv f := by
    funext d
    cases d
    rfl
  right_inv _ := rfl

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the word evaluation algebra hom construction. -/
local instance wordEvaluationAlgebraHomFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : Small.{us} PUnit.{1} := inferInstance
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The full original word-evaluation algebra Hom equivalence
uses the ACTUAL free algebra isomorphism and actual original
extension/restriction bijection, with both inverse laws proved. -/
def wordEvaluationAlgebraHomEquiv (X : C) (B : Algebra (associativeOperad.{us, v, u} C)) :
    (wordEvaluationAlgebra X ⟶ B) ≃ (X ⟶ B.carrier PUnit.unit) :=
  (Iso.homCongr (wordEvaluationAlgebraIso X).symm (Iso.refl B)).trans
    ((tensorFreeHomEquiv.{0, v, u, us} (associativeOperad.{us, v, u} C)
      (fun _ : PUnit.{1} => X) B).trans (singleColorCarrierHomEquiv X B.carrier))

/-- Actual forward restriction is the original unary generator,
the original corrected free-to-word carrier map, and the supplied
full operation-preserving word algebra map, at the original color. -/
theorem wordEvaluationAlgebraHomEquiv_apply (X : C) (B : Algebra (associativeOperad.{us, v, u} C))
    (h : wordEvaluationAlgebra X ⟶ B) :
    wordEvaluationAlgebraHomEquiv X B h =
      (profileUnit (associativeOperad.{us, v, u} C)).app (fun _ : PUnit.{1} => X) PUnit.unit ≫
        ((chosenWordCarrierIso X).hom PUnit.unit ≫ h.hom PUnit.unit) := by
  let r := tensorFreeHomEquiv.{0, v, u, us} (associativeOperad.{us, v, u} C)
    (fun _ : PUnit.{1} => X) B
  let s := singleColorCarrierHomEquiv X B.carrier
  exact congrArg (fun k => s (r k)) (homCongrSourceRightIdentity (wordEvaluationAlgebraIso X) h)

/-- The original algebra Hom restriction is precisely restriction
along the original PUBLIC tensor-word generator, through the proved
actual operadic generator comparison. -/
theorem wordEvaluationAlgebraHomEquiv_apply_generator (X : C)
    (B : Algebra (associativeOperad.{us, v, u} C)) (h : wordEvaluationAlgebra X ⟶ B) :
    wordEvaluationAlgebraHomEquiv X B h = tensorWordGenerator X ≫ h.hom PUnit.unit :=
  (wordEvaluationAlgebraHomEquiv_apply X B h).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ h.hom PUnit.unit) (operadicWordGenerator_eq X)))

/-- Actual inverse extension is the original inverse word
algebra isomorphism followed by the original free-algebra lift
of the supplied generator map, with its original carrier family. -/
theorem wordEvaluationAlgebraHomEquiv_symm_apply (X : C)
    (B : Algebra (associativeOperad.{us, v, u} C)) (f : X ⟶ B.carrier PUnit.unit) :
    (wordEvaluationAlgebraHomEquiv X B).symm f =
      (wordEvaluationAlgebraIso X).inv ≫
        freeAlgebraLift.{0, v, u, us} (associativeOperad.{us, v, u} C) B
          (singleColorCarrierMap B.carrier f) := by
  change (wordEvaluationAlgebraIso X).inv ≫
      (freeAlgebraLift.{0, v, u, us} (associativeOperad.{us, v, u} C) B
        (singleColorCarrierMap B.carrier f) ≫ 𝟙 B) = _
  rw [Category.comp_id]

/-- The original inverse lift has the exact original corrected
word-to-free carrier map, original profile map on the supplied
generator family and the target's actual original algebra action. -/
theorem wordEvaluationAlgebraHomEquiv_symm_carrier (X : C)
    (B : Algebra (associativeOperad.{us, v, u} C)) (f : X ⟶ B.carrier PUnit.unit) :
    ((wordEvaluationAlgebraHomEquiv X B).symm f).hom =
      (chosenWordCarrierIso X).inv ≫
        profileMap (associativeOperad.{us, v, u} C).toCollection
          (singleColorCarrierMap B.carrier f) ≫ B.action := by
  rw [wordEvaluationAlgebraHomEquiv_symm_apply]
  rfl

/-- The full word algebra restriction/extension bijection is
natural under every original full target algebra map. -/
theorem wordEvaluationAlgebraHomEquiv_target (X : C)
    {B D : Algebra (associativeOperad.{us, v, u} C)}
    (h : wordEvaluationAlgebra X ⟶ B) (g : B ⟶ D) :
    wordEvaluationAlgebraHomEquiv X D (h ≫ g) =
      wordEvaluationAlgebraHomEquiv X B h ≫ g.hom PUnit.unit := by
  have hv := fourMapTargetAssociativity
    ((profileUnit (associativeOperad.{us, v, u} C)).app (fun _ : PUnit.{1} => X))
    (chosenWordCarrierIso X).hom h.hom g.hom
  exact (wordEvaluationAlgebraHomEquiv_apply X D (h ≫ g)).trans
    ((congrFun hv PUnit.unit).trans
      (congrArg (· ≫ g.hom PUnit.unit) (wordEvaluationAlgebraHomEquiv_apply X B h).symm))

/-- The actual free operadic multiplication, in the original
corrected word coordinates, is the original word evaluation action. -/
theorem profileMultiplication_wordEvaluation (X : C) :
    profileMultiplication.{0, v, u, us} (associativeOperad.{us, v, u} C)
        (fun _ : PUnit.{1} => X) ≫ (chosenWordCarrierIso X).hom =
      profileMap (associativeOperad.{us, v, u} C).toCollection (chosenWordCarrierIso X).hom ≫
        wordEvaluationAction X :=
  (congrArg (· ≫ (chosenWordCarrierIso X).hom)
    (freeAlgebra_action.{0, v, u, us} (associativeOperad.{us, v, u} C) (fun _ : PUnit.{1} => X)).symm).trans
      ((Algebra.action_naturality (wordEvaluationAlgebraHom X)).trans
        (congrArg (profileMap (associativeOperad.{us, v, u} C).toCollection
          (chosenWordCarrierIso X).hom ≫ ·) (wordEvaluationAlgebra_action X)))







end CategoryTheory.Operad.Tensor.Associative
end
end
end source_WordEvaluationAlgebraHom

/- Source proof segment: CorrectedAssociativeWordAdjunction -/
section source_CorrectedAssociativeWordAdjunction
/-!
# The actual free-monoid adjunction on the corrected As carrier
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem originalIsoMapId {V : Type*} [Category* V] {A W : V} (e : A ≅ W) :
    e.hom ≫ 𝟙 W ≫ e.inv = 𝟙 A := by simp only [Category.id_comp, e.hom_inv_id]

private theorem originalIsoMapComp {V : Type*} [Category* V] {A B D W Z Q : V}
    (e : A ≅ W) (f : B ≅ Z) (g : D ≅ Q) (h : W ⟶ Z) (k : Z ⟶ Q) :
    e.hom ≫ (h ≫ k) ≫ g.inv = (e.hom ≫ h ≫ f.inv) ≫ (f.hom ≫ k ≫ g.inv) := by
  simp only [Category.assoc, f.inv_hom_id_assoc]

private theorem originalIsoMapNatural {V : Type*} [Category* V] {A B W Z : V}
    (e : A ≅ W) (f : B ≅ Z) (h : W ⟶ Z) :
    (e.hom ≫ h ≫ f.inv) ≫ f.hom = e.hom ≫ h := by
  simp only [Category.assoc, f.inv_hom_id, Category.comp_id]

private theorem originalIsoCarrierMap {V : Type*} [Category* V] {A B W Z : V}
    (e : A ≅ W) (f : B ≅ Z) (p : A ⟶ B) (h : W ⟶ Z)
    (hn : p ≫ f.hom = e.hom ≫ h) : e.hom ≫ h ≫ f.inv = p := by
  rw [← Category.assoc, ← hn, Category.assoc, f.hom_inv_id, Category.comp_id]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the corrected associative word adjunction construction. -/
local instance correctedAssociativeWordAdjunctionFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The actual free As profile carriers and source tensor-word
monoid structures form a functor, through the exact source carrier
comparison and the original tensor-word functor maps. -/
def correctedAssociativeWordFunctor : C ⥤ Mon C where
  obj := correctedAssociativeWordMon
  map {X Y} f := (correctedAssociativeWordMonIso X).hom ≫
    (TensorWord.tensorWordFunctor (C := C)).map f ≫ (correctedAssociativeWordMonIso Y).inv
  map_id X := by
    exact (congrArg (fun h => (correctedAssociativeWordMonIso X).hom ≫ h ≫
      (correctedAssociativeWordMonIso X).inv) (TensorWord.tensorWordFunctor.map_id X)).trans
        (originalIsoMapId (correctedAssociativeWordMonIso X))
  map_comp {X Y Z} f g := by
    exact (congrArg (fun h => (correctedAssociativeWordMonIso X).hom ≫ h ≫
      (correctedAssociativeWordMonIso Z).inv) (TensorWord.tensorWordFunctor.map_comp f g)).trans
        (originalIsoMapComp (correctedAssociativeWordMonIso X) (correctedAssociativeWordMonIso Y)
          (correctedAssociativeWordMonIso Z) (TensorWord.tensorWordFunctor.map f)
          (TensorWord.tensorWordFunctor.map g))

/-- Its actual carrier map is exactly the original operadic
profile-coinvariant map, with no map comparison supplied as a premise. -/
theorem correctedAssociativeWordFunctor_map_carrier {X Y : C} (f : X ⟶ Y) :
    ((correctedAssociativeWordFunctor (C := C)).map f).hom =
      profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => f) PUnit.unit := by
  change (chosenAssociativeTensorWordsIso X).hom ≫ TensorWord.tensorWordMap f ≫
    (chosenAssociativeTensorWordsIso Y).inv = _
  exact originalIsoCarrierMap (chosenAssociativeTensorWordsIso X) (chosenAssociativeTensorWordsIso Y)
    (profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
      (fun _ : PUnit.{1} => f) PUnit.unit) (TensorWord.tensorWordMap f)
    (StrandNaturality.chosenAssociativeTensorWordsIso_naturality f)

/-- The exact original source monoid isomorphisms form a natural
isomorphism to the original free tensor-word monoid functor. -/
def correctedAssociativeWordFunctorIso :
    correctedAssociativeWordFunctor (C := C) ≅ TensorWord.tensorWordFunctor :=
  NatIso.ofComponents correctedAssociativeWordMonIso (by
    intro X Y f
    change ((correctedAssociativeWordMonIso X).hom ≫ TensorWord.tensorWordFunctor.map f ≫
      (correctedAssociativeWordMonIso Y).inv) ≫ (correctedAssociativeWordMonIso Y).hom = _
    exact originalIsoMapNatural (correctedAssociativeWordMonIso X) (correctedAssociativeWordMonIso Y)
      (TensorWord.tensorWordFunctor.map f))

/-- The actual operation-weighted source As carrier, with its
proved tensor-word operations, is the free unital monoid functor. -/
def correctedAssociativeWordAdjunction : correctedAssociativeWordFunctor (C := C) ⊣ Mon.forget C :=
  TensorWord.tensorWordAdjunction.ofNatIsoLeft correctedAssociativeWordFunctorIso.symm

/-- The adjunction generator is the ACTUAL original unary
operadic unit insertion into its original profile coinvariant. -/
theorem correctedAssociativeWordAdjunction_unit (X : C) :
    correctedAssociativeWordAdjunction.unit.app X =
      (profileUnit (FiniteTensor.UnitCopower.associativeOperad C)).app
        (fun _ : PUnit.{1} => X) PUnit.unit := by
  change TensorWord.tensorWordAdjunction.unit.app X ≫
    (correctedAssociativeWordMonIso X).inv.hom = _
  exact (congrArg (· ≫ (correctedAssociativeWordMonIso X).inv.hom)
    (TensorWord.tensorWordAdjunction_unit X)).trans
      (correctedAssociativeWordGenerator_eq_operadicUnit X)

/-- The counit is the actual original word-monoid extension,
after the proved source carrier comparison. -/
theorem correctedAssociativeWordAdjunction_counit (M : Mon C) :
    correctedAssociativeWordAdjunction.counit.app M =
      (correctedAssociativeWordMonIso M.X).hom ≫ TensorWord.tensorWordLiftHom M (𝟙 M.X) := rfl

/-- Its induced monad has every original source profile carrier,
with all monad laws from the actual constructed free adjunction. -/
def correctedAssociativeWordMonad : Monad C := correctedAssociativeWordAdjunction.toMonad

theorem correctedAssociativeWordMonad_obj (X : C) :
    correctedAssociativeWordMonad.obj X =
      profileCoinvariants (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => X) PUnit.unit := rfl

theorem correctedAssociativeWordMonad_map {X Y : C} (f : X ⟶ Y) :
    correctedAssociativeWordMonad.map f =
      profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => f) PUnit.unit := correctedAssociativeWordFunctor_map_carrier f

theorem correctedAssociativeWordMonad_unit (X : C) :
    correctedAssociativeWordMonad.η.app X =
      (profileUnit (FiniteTensor.UnitCopower.associativeOperad C)).app
        (fun _ : PUnit.{1} => X) PUnit.unit := correctedAssociativeWordAdjunction_unit X






end CategoryTheory.Operad.Tensor.Associative
end
end
end source_CorrectedAssociativeWordAdjunction

/- Source proof segment: AdjunctionLeftIsoMonad -/
section source_AdjunctionLeftIsoMonad
/-!
# Monad comparison for an actual isomorphism of left adjoints
-/

@[expose] public section
set_option autoImplicit false
universe u v w z

namespace CategoryTheory.Adjunction

open CategoryTheory

variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{z} D]
variable {F G : C ⥤ D} {U : D ⥤ C}

/-- Transporting an adjunction through a natural isomorphism of
its left adjoint transports its induced monad through the actual
whiskered isomorphism. Both unit and multiplication squares follow
from the original unit, counit, and counit naturality. -/
def monadIsoOfNatIsoLeft (adj : F ⊣ U) (e : G ≅ F) :
    (adj.ofNatIsoLeft e.symm).toMonad ≅ adj.toMonad := by
  refine MonadIso.mk (Functor.isoWhiskerRight e U) ?_ ?_
  · intro X
    change (adj.unit.app X ≫ U.map (e.inv.app X)) ≫ U.map (e.hom.app X) = adj.unit.app X
    rw [Category.assoc, ← U.map_comp, e.inv_hom_id_app, U.map_id]
    exact Category.comp_id (adj.unit.app X)
  · intro X
    change U.map (e.hom.app (U.obj (G.obj X)) ≫ adj.counit.app (G.obj X)) ≫ U.map (e.hom.app X) =
      (U.map (G.map (U.map (e.hom.app X))) ≫ U.map (e.hom.app (U.obj (F.obj X)))) ≫
        U.map (adj.counit.app (F.obj X))
    have hc : F.map (U.map (e.hom.app X)) ≫ adj.counit.app (F.obj X) =
        adj.counit.app (G.obj X) ≫ e.hom.app X := by
      simpa only [Functor.comp_map, Functor.id_map] using adj.counit.naturality (e.hom.app X)
    have hd : (e.hom.app (U.obj (G.obj X)) ≫ adj.counit.app (G.obj X)) ≫ e.hom.app X =
        (G.map (U.map (e.hom.app X)) ≫ e.hom.app (U.obj (F.obj X))) ≫
          adj.counit.app (F.obj X) := by
      rw [e.hom.naturality (U.map (e.hom.app X))]
      simp only [Category.assoc]
      rw [hc]
    simp only [← U.map_comp]
    exact congrArg U.map hd

@[simp]
theorem monadIsoOfNatIsoLeft_hom_app (adj : F ⊣ U) (e : G ≅ F) (X : C) :
    (monadIsoOfNatIsoLeft adj e).hom.app X = U.map (e.hom.app X) := rfl

@[simp]
theorem monadIsoOfNatIsoLeft_inv_app (adj : F ⊣ U) (e : G ≅ F) (X : C) :
    (monadIsoOfNatIsoLeft adj e).inv.app X = U.map (e.inv.app X) := rfl



end CategoryTheory.Adjunction
end
end source_AdjunctionLeftIsoMonad

/- Source proof segment: CorrectedAssociativeWordMonadComparison -/
section source_CorrectedAssociativeWordMonadComparison
/-!
# The actual corrected source free-monoid monad is the tensor-word monad
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v us

namespace CategoryTheory.Operad.Tensor.Associative

open CategoryTheory Limits MonoidalCategory

private theorem originalMonadMultiplicationReadback {V : Type*} [Category* V]
    {M N : Monad V} (e : M ≅ N) (X : V) (g : M.obj X ⟶ N.obj X)
    (p : M.obj (M.obj X) ⟶ M.obj (N.obj X))
    (k : M.obj (N.obj X) ⟶ N.obj (N.obj X)) (a : N.obj (N.obj X) ⟶ N.obj X)
    (hg : e.hom.app X = g) (hp : M.map (e.hom.app X) = p)
    (hk : e.hom.app (N.obj X) = k) (ha : N.μ.app X = a) :
    M.μ.app X ≫ g = p ≫ k ≫ a := by
  calc
    M.μ.app X ≫ g = M.μ.app X ≫ e.hom.app X := congrArg (M.μ.app X ≫ ·) hg.symm
    _ = (M.map (e.hom.app X) ≫ e.hom.app (N.obj X)) ≫ N.μ.app X := e.hom.app_μ X
    _ = p ≫ k ≫ a := by rw [hp, hk, ha, Category.assoc]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{us, us} C]

/-- Use the source symmetric finite tensor for the corrected associative word monad comparison construction. -/
local instance correctedAssociativeWordMonadComparisonFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance (d : PUnit.{1}) : HasColimitsOfShape (AnalyticIndex PUnit.{1} d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original source free-monoid monad and the original
tensor-word monad are isomorphic through the exact same source
strand correction as every original operadic operation and generator. -/
def correctedAssociativeWordMonadIso :
    correctedAssociativeWordMonad (C := C) ≅ TensorWord.tensorWordMonad :=
  TensorWord.tensorWordAdjunction.monadIsoOfNatIsoLeft correctedAssociativeWordFunctorIso

@[simp]
theorem correctedAssociativeWordMonadIso_hom_app (X : C) :
    correctedAssociativeWordMonadIso.hom.app X = (chosenAssociativeTensorWordsIso X).hom := rfl

@[simp]
theorem correctedAssociativeWordMonadIso_inv_app (X : C) :
    correctedAssociativeWordMonadIso.inv.app X = (chosenAssociativeTensorWordsIso X).inv := rfl

/-- Actual monad multiplication is the original word-of-word
flattening, after the original source profile maps and its exact
corrected word comparison. This is the true monad-morphism square. -/
theorem correctedAssociativeWordMonad_multiplication_word (X : C) :
    correctedAssociativeWordMonad.μ.app X ≫ (chosenAssociativeTensorWordsIso X).hom =
      profileMap (FiniteTensor.UnitCopower.associativeOperad C).toCollection
        (fun _ : PUnit.{1} => (chosenAssociativeTensorWordsIso X).hom) PUnit.unit ≫
      (chosenAssociativeTensorWordsIso (TensorWord.tensorWordObj X)).hom ≫
      TensorWord.tensorWordLift (TensorWord.tensorWordMon X) (𝟙 (TensorWord.tensorWordObj X)) := by
  let M := correctedAssociativeWordMonad (C := C)
  let N := TensorWord.tensorWordMonad (C := C)
  let e := correctedAssociativeWordMonadIso (C := C)
  let O := FiniteTensor.UnitCopower.associativeOperad C
  have hp : M.map (e.hom.app X) =
      profileMap O.toCollection (fun _ : PUnit.{1} => (chosenAssociativeTensorWordsIso X).hom) PUnit.unit :=
    (correctedAssociativeWordMonad_map (e.hom.app X)).trans
      (congrArg (fun f : M.obj X ⟶ N.obj X =>
        profileMap O.toCollection (fun _ : PUnit.{1} => f) PUnit.unit)
          (correctedAssociativeWordMonadIso_hom_app X))
  exact originalMonadMultiplicationReadback e X (chosenAssociativeTensorWordsIso X).hom
    (profileMap O.toCollection (fun _ : PUnit.{1} => (chosenAssociativeTensorWordsIso X).hom) PUnit.unit)
    (chosenAssociativeTensorWordsIso (TensorWord.tensorWordObj X)).hom
    (TensorWord.tensorWordLift (TensorWord.tensorWordMon X) (𝟙 (TensorWord.tensorWordObj X)))
    (correctedAssociativeWordMonadIso_hom_app X) hp
    (correctedAssociativeWordMonadIso_hom_app (TensorWord.tensorWordObj X))
    (TensorWord.tensorWordMonad_multiplication X)




end CategoryTheory.Operad.Tensor.Associative
end
end
end source_CorrectedAssociativeWordMonadComparison
