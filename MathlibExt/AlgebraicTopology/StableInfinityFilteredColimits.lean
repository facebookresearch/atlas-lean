/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityFiniteDiagrams
public import MathlibExt.AlgebraicTopology.SimplicialCovariantModels
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Actual filtered-colimit and compactness tests

A cofinal index retains the entire infinity category, an actual ordinary
cardinal-filtered index model, and its cofinal map. Cofinality tests the
actual source slices by weak homotopy equivalence, taking groupoid
completion rather than an equivalence-edge core. Thus general coherent
index diagrams are represented through their specified cofinal models.

Compactness tests the canonical map between the two left-slice pullbacks:
one over the original index and one over its universal colimit cocone.
The second pullback has the mapping space to the apex as its homotopy
colimit. No arbitrary mapping-space diagram or colimit comparison map
is an input. The cofinal-model and compactness characterizations are
separate source theorems.

References: Lurie, Higher Topos Theory, Section 5.3;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2.4 and 9.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityFilteredColimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open StableInfinityMappingSpaces StableInfinityFiniteDiagrams SimplicialCovariantModels QuasicategoricalModels
open scoped Simplicial Cardinal

universe u

/-- The source cardinal is genuinely uncountable and regular. -/
structure UncountableRegularCardinal where
  value : Cardinal.{0}
  uncountable : ℵ₀ < value
  regular : value.IsRegular

/-- Ordinary cardinal-filteredness uses every actual small diagram and its native cocone. -/
def IsKappaFilteredCategory (k : Cardinal.{0}) (I : Type) [Category.{0} I] : Prop :=
  ∀ (J : Type) [Category.{0} J], Cardinal.mk J < k →
    Cardinal.mk (Σ x : J, Σ y : J, x ⟶ y) < k →
      ∀ F : J ⥤ I, Nonempty (Cocone F)

/-- Contractibility is the actual weak comparison with the terminal zero-simplex. -/
def IsWeaklyContractible (X : SSet.{u}) : Prop :=
  WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from X)

/-- The true cofinality test is the entire under-category over each source object. -/
def IsCofinal {I J : SSet.{u}} (f : I ⟶ J) : Prop :=
  ∀ x : J _⦋0⦌,
    IsWeaklyContractible (pullback (targetProjection J x) f)

/-- General coherent filtered diagrams retain their actual cofinal model maps. -/
structure CofinalKappaIndex (k : Cardinal.{0}) (J : SSet.{0}) where
  index : Type
  [category : Category.{0} index]
  filtered : IsKappaFilteredCategory k index
  map : nerve index ⟶ J
  cofinal : IsCofinal map

attribute [instance] CofinalKappaIndex.category

/-- The indexed diagram is the actual cofinal source map followed by the original diagram. -/
def indexedDiagram {k : Cardinal.{0}} {J : SSet.{0}}
    (M : CofinalKappaIndex k J) {C : SSet.{u}}
    (d : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{u}).obj J ⟶ C) : indexNerve M.index ⟶ C :=
  (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{u}).map M.map ≫ d

/-- Extract the entire original universal cocone diagram from its native fibre vertex. -/
def coconeDiagram {I : Type} [Category.{0} I] (C : SSet.{u})
    (d : indexNerve I ⟶ C) (c : (rightCones C d) _⦋0⦌) :
    indexNerve (WithTerminal I) ⟶ C :=
  (mappingZero (indexNerve (WithTerminal I)) C).symm
    ((pullback.fst (precomposition (indexMap (WithTerminal.incl (C := I))) C)
      (diagramPoint C d)).app (op ⦋0⦌) c)

/-- The extraction retains the actual source diagram on every simplex. -/
theorem coconeDiagram_restriction {I : Type} [Category.{0} I] (C : SSet.{u})
    (d : indexNerve I ⟶ C) (c : (rightCones C d) _⦋0⦌) :
    indexMap (WithTerminal.incl (C := I)) ≫ coconeDiagram C d c = d := by
  apply (mappingZero (indexNerve I) C).injective
  rw [← mappingZero_precomposition]
  dsimp only [coconeDiagram]
  rw [Equiv.apply_symm_apply]
  have h := congrArg (fun f => f.app (op ⦋0⦌) c)
    (pullback.condition (f := precomposition (indexMap (WithTerminal.incl (C := I))) C)
      (g := diagramPoint C d))
  exact h

/-- The canonical left-slice pullback map from the index to its actual colimit cocone. -/
def mappingColimitComparison {I : Type} [Category.{0} I] (C : SSet.{u})
    (x : C _⦋0⦌) (d : indexNerve I ⟶ C) (c : (rightCones C d) _⦋0⦌) :
    pullback (targetProjection C x) d ⟶
      pullback (targetProjection C x) (coconeDiagram C d c) :=
  pullback.map (targetProjection C x) d (targetProjection C x) (coconeDiagram C d c)
    (𝟙 (leftSlice C x)) (indexMap (WithTerminal.incl (C := I))) (𝟙 C)
    (by simp) (by simpa using (coconeDiagram_restriction C d c).symm)

/-- Compactness is preservation of these actual full homotopy-colimit comparison maps. -/
def IsKappaCompactVertex (k : Cardinal.{0}) (C : SSet.{u}) (x : C _⦋0⦌) : Prop :=
  ∀ (J : SSet.{0}) [SSet.Quasicategory J] (M : CofinalKappaIndex k J)
    (d : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{u}).obj J ⟶ C)
    (c : (rightCones C (indexedDiagram M d)) _⦋0⦌),
    IsInitialObject (rightCones C (indexedDiagram M d)) c →
      WeakEquivalence (mappingColimitComparison C x (indexedDiagram M d) c)

/-- Colimit preservation is a condition on the actual image of the entire universal cocone. -/
def PreservesKappaFilteredColimits (k : Cardinal.{0}) {C D : SSet.{u}} (f : C ⟶ D) : Prop :=
  ∀ (J : SSet.{0}) [SSet.Quasicategory J] (M : CofinalKappaIndex k J)
    (d : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{u}).obj J ⟶ C)
    (c : (rightCones C (indexedDiagram M d)) _⦋0⦌),
    IsInitialObject (rightCones C (indexedDiagram M d)) c →
      ∃ c' : (rightCones D (indexedDiagram M d ≫ f)) _⦋0⦌,
        IsInitialObject (rightCones D (indexedDiagram M d ≫ f)) c' ∧
          coconeDiagram D (indexedDiagram M d ≫ f) c' = coconeDiagram C (indexedDiagram M d) c ≫ f

end MathlibExt.AlgebraicTopology.StableInfinityFilteredColimits
