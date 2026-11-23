/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopPair.CoproductColimits
public import MathlibExt.Topology.Category.TopPair.Excision
public import MathlibExt.CategoryTheory.NatIso
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicTopology.EilenbergSteenrod
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Eilenberg–Steenrod theories

General Eilenberg–Steenrod structures for homology and cohomology theories on
topological pairs, including exactness, excision, additivity and dimension
axioms and their functorial evaluation interfaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u v

namespace TopPair

/-- The raw, integer-graded data underlying a homology theory. -/
abbrev HomologyTheoryData
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  TopPair.HomologyPretheory.{w} C (ComplexShape.down ℤ)

namespace HomologyTheoryData

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The map `H_n(A) ⟶ H_n(X)` associated to a pair `(X,A)`. -/
def subspaceMap (E : HomologyTheoryData.{w} C) (n : ℤ) (X : TopPair.{w}) :
    (E.H n).obj X.snd ⟶ (E.H n).obj X.fst :=
  (E.H n).map X.map

/-- The map `H_n(X) ⟶ H_n(X,A)` associated to a pair `(X,A)`. -/
def toRelative (E : HomologyTheoryData.{w} C) (n : ℤ) (X : TopPair.{w}) :
    (E.H n).obj X.fst ⟶ (E.Hₚ n).obj X :=
  (E.iso n).hom.app X.fst ≫ (E.Hₚ n).map (TopPair.j X)

/-- The connecting map `H_n(X,A) ⟶ H_{n-1}(A)`. -/
def boundary (E : HomologyTheoryData.{w} C) (n : ℤ) (X : TopPair.{w}) :
    (E.Hₚ n).obj X ⟶ (E.H (n - 1)).obj X.snd :=
  (E.δ n (n - 1)).app X

/-- The second projection sends a pair map to its subspace map. -/
@[simp, nolint simpNF]
theorem proj₂_map_snd {P Q : TopPair.{w}} (f : P ⟶ Q) :
    proj₂.map f = TopPair.Hom.snd f :=
  rfl

/-- Naturality of the LES connecting map against maps of pairs. -/
theorem boundary_naturality (E : HomologyTheoryData.{w} C) (n : ℤ)
    {P Q : TopPair.{w}} (f : P ⟶ Q) :
    (E.Hₚ n).map f ≫ E.boundary n Q =
      E.boundary n P ≫ (E.H (n - 1)).map (TopPair.Hom.snd f) := by
  have h := (E.δ n (n - 1)).naturality f
  rw [Functor.comp_map, proj₂_map_snd] at h
  unfold boundary
  exact h

/-- The coefficient object in degree `n`. -/
def coefficientObject (E : HomologyTheoryData.{w} C) (n : ℤ) : C :=
  (E.H n).obj (TopCat.of PUnit)

/-- Five consecutive terms of the homology sequence of a pair. -/
def pairSequence (E : HomologyTheoryData.{w} C) (n : ℤ) (X : TopPair.{w}) :
    ComposableArrows C 4 :=
  ComposableArrows.mk₄
    (E.boundary n X)
    (E.subspaceMap (n - 1) X)
    (E.toRelative (n - 1) X)
    (E.boundary (n - 1) X)

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of raw theory data induces an isomorphism of pair sequences. -/
noncomputable def pairSequenceIso {E F : HomologyTheoryData.{w} C} (e : E ≅ F)
    (n : ℤ) (X : TopPair.{w}) : E.pairSequence n X ≅ F.pairSequence n X := by
  haveI : IsIso e.hom := inferInstance
  letI (k : ℤ) : IsIso (e.hom.homₚ k) := by infer_instance
  letI (k : ℤ) : IsIso (e.hom.hom k) := by infer_instance
  exact ComposableArrows.isoMk₄
    ((asIso (e.hom.homₚ n)).app X)
    ((asIso (e.hom.hom (n - 1))).app X.snd)
    ((asIso (e.hom.hom (n - 1))).app X.fst)
    ((asIso (e.hom.homₚ (n - 1))).app X)
    ((asIso (e.hom.hom ((n - 1) - 1))).app X.snd)
    (by
      change (E.δ n (n - 1)).app X ≫ (e.hom.hom (n - 1)).app X.snd =
        (e.hom.homₚ n).app X ≫ (F.δ n (n - 1)).app X
      exact e.hom.w_app n (n - 1) X)
    (by
      change (E.H (n - 1)).map X.map ≫ (e.hom.hom (n - 1)).app X.fst =
        (e.hom.hom (n - 1)).app X.snd ≫ (F.H (n - 1)).map X.map
      exact (e.hom.hom (n - 1)).naturality X.map)
    (by
      change E.toRelative (n - 1) X ≫ (e.hom.homₚ (n - 1)).app X =
        (e.hom.hom (n - 1)).app X.fst ≫ F.toRelative (n - 1) X
      simp only [toRelative]
      calc
        ((E.iso (n - 1)).hom.app X.fst ≫ (E.Hₚ (n - 1)).map (TopPair.j X)) ≫
              (e.hom.homₚ (n - 1)).app X =
            (E.iso (n - 1)).hom.app X.fst ≫
              ((e.hom.homₚ (n - 1)).app (TopPair.ofTopCat X.fst) ≫
                (F.Hₚ (n - 1)).map (TopPair.j X)) := by
                rw [Category.assoc, NatTrans.naturality]
                rfl
        _ = ((e.hom.hom (n - 1)).app X.fst ≫ (F.iso (n - 1)).hom.app X.fst) ≫
              (F.Hₚ (n - 1)).map (TopPair.j X) := by
                rw [← Category.assoc, e.hom.iso_comm_app]
        _ = (e.hom.hom (n - 1)).app X.fst ≫
              ((F.iso (n - 1)).hom.app X.fst ≫
                (F.Hₚ (n - 1)).map (TopPair.j X)) := by simp)
    (by
      change (E.δ (n - 1) ((n - 1) - 1)).app X ≫
          (e.hom.hom ((n - 1) - 1)).app X.snd =
        (e.hom.homₚ (n - 1)).app X ≫
          (F.δ (n - 1) ((n - 1) - 1)).app X
      exact e.hom.w_app (n - 1) ((n - 1) - 1) X)

/-- Exactness of the homology sequence of every pair. -/
class IsExact (E : HomologyTheoryData.{w} C) : Prop where
  exact_pairSequence (n : ℤ) (X : TopPair.{w}) : (E.pairSequence n X).Exact

/-- Excision for excisive triads: `(B,A ∩ B) ⟶ (X,A)` induces an isomorphism. -/
class IsExcisive (E : HomologyTheoryData.{w} C) : Prop where
  isIso_map_excision (n : ℤ) (X : TopCat.{w}) (A B : Set X)
      (h : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    IsIso ((E.Hₚ n).map (TopPair.excisionHom X A B))

theorem IsExcisive.isIso_map_excision_compl (E : HomologyTheoryData.{w} C) [E.IsExcisive]
    (n : ℤ) (X : TopCat.{w}) (A U : Set X) (h : closure U ⊆ interior A) :
    IsIso ((E.Hₚ n).map (TopPair.excisionHom X A Uᶜ)) :=
  IsExcisive.isIso_map_excision n X A Uᶜ
    (TopPair.interiorsCover_compl_of_closure_subset_interior X A U h)

/-- The disjoint-union axiom for a homology theory. -/
class IsAdditive (E : HomologyTheoryData.{w} C) : Prop where
  preservesDiscreteCoproducts (n : ℤ) (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (E.Hₚ n)

/-- The dimension axiom, with the coefficient object left as `H_0(pt)`. -/
class SatisfiesDimensionAxiom (E : HomologyTheoryData.{w} C) : Prop where
  isZero_point (n : ℤ) (hn : n ≠ 0) :
    IsZero ((E.H n).obj (TopCat.of PUnit))

/-- Exactness as an object property of raw theory data. -/
abbrev isExact : ObjectProperty (HomologyTheoryData.{w} C) := IsExact
/-- Excision as an object property of raw theory data. -/
abbrev isExcisive : ObjectProperty (HomologyTheoryData.{w} C) := IsExcisive
/-- Additivity as an object property of raw theory data. -/
abbrev isAdditive : ObjectProperty (HomologyTheoryData.{w} C) := IsAdditive
/-- The dimension axiom as an object property of raw theory data. -/
abbrev satisfiesDimensionAxiom : ObjectProperty (HomologyTheoryData.{w} C) :=
  SatisfiesDimensionAxiom

instance : ObjectProperty.IsClosedUnderIsomorphisms (isExact (C := C)) where
  of_iso e h :=
    ⟨fun n X => ComposableArrows.exact_of_iso (pairSequenceIso e n X)
      (h.exact_pairSequence n X)⟩

instance : ObjectProperty.IsClosedUnderIsomorphisms (isExcisive (C := C)) where
  of_iso e h := ⟨fun n X A B hcover => by
    have : IsIso e.hom := inferInstance
    have : IsIso (e.hom.homₚ n) := by infer_instance
    have : IsIso ((e.hom.homₚ n).app (excisionSource X A B)) := by infer_instance
    have : IsIso ((e.hom.homₚ n).app (excisionTarget X A)) := by infer_instance
    have := h.isIso_map_excision n X A B hcover
    exact IsIso.of_isIso_fac_left
      ((e.hom.homₚ n).naturality (excisionHom X A B)).symm⟩

instance : ObjectProperty.IsClosedUnderIsomorphisms (isAdditive (C := C)) where
  of_iso e h := ⟨fun n J => by
    have : IsIso e.hom := inferInstance
    have : IsIso (e.hom.homₚ n) := by infer_instance
    let := h.preservesDiscreteCoproducts n J
    exact preservesColimitsOfShape_of_natIso (asIso (e.hom.homₚ n))⟩

instance : ObjectProperty.IsClosedUnderIsomorphisms
    (satisfiesDimensionAxiom (C := C)) where
  of_iso e h := ⟨fun n hn => by
    have : IsIso e.hom := inferInstance
    have : IsIso (e.hom.hom n) := by infer_instance
    exact (h.isZero_point n hn).of_iso
      ((asIso (e.hom.hom n)).app (TopCat.of PUnit)).symm⟩

/-- The property defining generalized homology theories. -/
abbrev isGeneralizedHomologyTheory : ObjectProperty (HomologyTheoryData.{w} C) :=
  HomologyPretheory.isHomotopyInvariant C (ComplexShape.down ℤ) ⊓
    (isExact ⊓ (isExcisive ⊓ isAdditive))

/-- The property defining ordinary homology theories. -/
abbrev isOrdinaryHomologyTheory : ObjectProperty (HomologyTheoryData.{w} C) :=
  isGeneralizedHomologyTheory ⊓ satisfiesDimensionAxiom

end HomologyTheoryData

namespace HomologyPretheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

@[simp, nolint simpNF]
lemma Hom.id_hom (E : HomologyPretheory.{w} C c) (i : ι) :
    (𝟙 E : E ⟶ E).hom i = 𝟙 (E.H i) := by
  simp

@[simp, nolint simpNF]
lemma Hom.comp_hom {E F G : HomologyPretheory.{w} C c}
    (f : E ⟶ F) (g : F ⟶ G) (i : ι) :
    (f ≫ g).hom i = f.hom i ≫ g.hom i := by
  simp

end HomologyPretheory

/-- An integer-graded generalized homology theory satisfying the Eilenberg--Steenrod
axioms other than dimension. Additivity is included. -/
abbrev GeneralizedHomologyTheory
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  (HomologyTheoryData.isGeneralizedHomologyTheory (C := C)).FullSubcategory

/-- An ordinary homology theory: a generalized theory satisfying dimension. -/
abbrev OrdinaryHomologyTheory
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  (HomologyTheoryData.isOrdinaryHomologyTheory (C := C)).FullSubcategory

namespace GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Bundle raw data equipped with the generalized Eilenberg--Steenrod axioms. -/
def of (E : HomologyTheoryData C) [E.IsHomotopyInvariant] [E.IsExact]
    [E.IsExcisive] [E.IsAdditive] : GeneralizedHomologyTheory C :=
  ⟨E, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩⟩

/-- Evaluate a generalized theory on relative degree-`n` homology. -/
def hₚFunctor (n : ℤ) : GeneralizedHomologyTheory.{u, v, w} C ⥤ (TopPair.{w} ⥤ C) :=
  (HomologyTheoryData.isGeneralizedHomologyTheory (C := C)).ι ⋙
    HomologyPretheory.hₚFunctor n

/-- Evaluate a generalized theory on absolute degree-`n` homology. -/
def hFunctor (n : ℤ) : GeneralizedHomologyTheory.{u, v, w} C ⥤ (TopCat.{w} ⥤ C) :=
  (HomologyTheoryData.isGeneralizedHomologyTheory (C := C)).ι ⋙
    HomologyPretheory.hFunctor n

/-- Relative degree-`n` homology as a functor of pairs. -/
abbrev Hₚ (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) : TopPair.{w} ⥤ C :=
  (hₚFunctor n).obj E

/-- Absolute degree-`n` homology as a functor of spaces. -/
abbrev H (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) : TopCat.{w} ⥤ C :=
  (hFunctor n).obj E

instance (E : GeneralizedHomologyTheory C) : E.obj.IsHomotopyInvariant := E.property.1
instance (E : GeneralizedHomologyTheory C) : E.obj.IsExact := E.property.2.1
instance (E : GeneralizedHomologyTheory C) : E.obj.IsExcisive := E.property.2.2.1
instance (E : GeneralizedHomologyTheory C) : E.obj.IsAdditive := E.property.2.2.2

end GeneralizedHomologyTheory

namespace OrdinaryHomologyTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Bundle raw data equipped with all ordinary Eilenberg--Steenrod axioms. -/
def of (E : HomologyTheoryData C) [E.IsHomotopyInvariant] [E.IsExact]
    [E.IsExcisive] [E.IsAdditive] [E.SatisfiesDimensionAxiom] :
    OrdinaryHomologyTheory C :=
  ⟨E, ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩⟩

instance (E : OrdinaryHomologyTheory C) : E.obj.IsHomotopyInvariant := E.property.1.1
instance (E : OrdinaryHomologyTheory C) : E.obj.IsExact := E.property.1.2.1
instance (E : OrdinaryHomologyTheory C) : E.obj.IsExcisive := E.property.1.2.2.1
instance (E : OrdinaryHomologyTheory C) : E.obj.IsAdditive := E.property.1.2.2.2
instance (E : OrdinaryHomologyTheory C) : E.obj.SatisfiesDimensionAxiom := E.property.2

/-- Forget the dimension axiom. -/
def forgetDimension : OrdinaryHomologyTheory C ⥤ GeneralizedHomologyTheory C :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

/-- Evaluate an ordinary theory on relative degree-`n` homology. -/
def hₚFunctor (n : ℤ) : OrdinaryHomologyTheory.{u, v, w} C ⥤ (TopPair.{w} ⥤ C) :=
  forgetDimension ⋙ GeneralizedHomologyTheory.hₚFunctor n

/-- Evaluate an ordinary theory on absolute degree-`n` homology. -/
def hFunctor (n : ℤ) : OrdinaryHomologyTheory.{u, v, w} C ⥤ (TopCat.{w} ⥤ C) :=
  forgetDimension ⋙ GeneralizedHomologyTheory.hFunctor n

/-- Relative degree-`n` homology as a functor of pairs. -/
abbrev Hₚ (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) : TopPair.{w} ⥤ C :=
  (hₚFunctor n).obj E

/-- Absolute degree-`n` homology as a functor of spaces. -/
abbrev H (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) : TopCat.{w} ⥤ C :=
  (hFunctor n).obj E

end OrdinaryHomologyTheory

/-- The raw, integer-graded data underlying a cohomology theory. -/
abbrev CohomologyTheoryData
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  (HomologyTheoryData.{w} Cᵒᵖ)ᵒᵖ

namespace CohomologyTheoryData

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Relative cohomology for raw cohomology-theory data. -/
abbrev Hₚ (E : CohomologyTheoryData.{w} C) (n : ℤ) : TopPair.{w}ᵒᵖ ⥤ C :=
  (E.unop.Hₚ n).leftOp

/-- Absolute cohomology for raw cohomology-theory data. -/
abbrev H (E : CohomologyTheoryData.{w} C) (n : ℤ) : TopCat.{w}ᵒᵖ ⥤ C :=
  (E.unop.H n).leftOp

/-- A morphism of raw cohomology data induces relative cohomology maps. -/
def homₚ {E F : CohomologyTheoryData.{w} C} (f : E ⟶ F) (n : ℤ) :
    E.Hₚ n ⟶ F.Hₚ n :=
  (f.unop.homₚ n).leftOp

/-- A morphism of raw cohomology data induces absolute cohomology maps. -/
def hom {E F : CohomologyTheoryData.{w} C} (f : E ⟶ F) (n : ℤ) :
    E.H n ⟶ F.H n :=
  (f.unop.hom n).leftOp

/-- Evaluation of raw cohomology data in relative degree `n`. -/
def hₚFunctor (n : ℤ) : CohomologyTheoryData.{w} C ⥤ (TopPair.{w}ᵒᵖ ⥤ C) where
  obj E := E.Hₚ n
  map f := homₚ f n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation of raw cohomology data in absolute degree `n`. -/
def hFunctor (n : ℤ) : CohomologyTheoryData.{w} C ⥤ (TopCat.{w}ᵒᵖ ⥤ C) where
  obj E := E.H n
  map f := hom f n
  map_id _ := by
    ext X
    simp [hom]
  map_comp _ _ := by
    ext X
    simp [hom]

end CohomologyTheoryData

/-- A generalized cohomology theory, implemented by categorical duality but exposed
with the conventional contravariant variance. -/
abbrev GeneralizedCohomologyTheory
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  (GeneralizedHomologyTheory Cᵒᵖ)ᵒᵖ

/-- An ordinary cohomology theory. -/
abbrev OrdinaryCohomologyTheory
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  (OrdinaryHomologyTheory Cᵒᵖ)ᵒᵖ

namespace GeneralizedCohomologyTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Categorical dual of `GeneralizedHomologyTheory.of`. -/
def of (E : HomologyTheoryData.{w} Cᵒᵖ) [E.IsHomotopyInvariant] [E.IsExact]
    [E.IsExcisive] [E.IsAdditive] : GeneralizedCohomologyTheory C :=
  Opposite.op (GeneralizedHomologyTheory.of E)

/-- Unwrapping recovers the underlying data. -/
@[simp]
lemma unop_obj_of (E : HomologyTheoryData.{w} Cᵒᵖ) [E.IsHomotopyInvariant] [E.IsExact]
    [E.IsExcisive] [E.IsAdditive] : (of E).unop.obj = E :=
  rfl

/-- The forgetful functor to raw cohomology data. -/
def forgetData : GeneralizedCohomologyTheory C ⥤ CohomologyTheoryData C :=
  (HomologyTheoryData.isGeneralizedHomologyTheory (C := Cᵒᵖ)).ι.op

/-- Relative cohomology is contravariant in topological pairs. -/
def Hₚ (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) : TopPair.{w}ᵒᵖ ⥤ C :=
  (E.unop.obj.Hₚ n).leftOp

/-- Absolute cohomology is contravariant in spaces. -/
def H (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) : TopCat.{w}ᵒᵖ ⥤ C :=
  (E.unop.obj.H n).leftOp

/-- Contravariant comparison along a map of pairs, followed by degree transport. -/
def relativeComparison (E : GeneralizedCohomologyTheory.{u, v, w} C)
    {P Q : TopPair.{w}} (f : P ⟶ Q) {m n : ℤ} (h : m = n) :
    (E.Hₚ m).obj (Opposite.op Q) ⟶ (E.Hₚ n).obj (Opposite.op P) :=
  (E.Hₚ m).map f.op ≫
    eqToHom (congrArg (fun k ↦ (E.Hₚ k).obj (Opposite.op P)) h)

/-- Same-degree comparison is the contravariant functor map. -/
@[simp]
theorem relativeComparison_rfl
    (E : GeneralizedCohomologyTheory.{u, v, w} C)
    {P Q : TopPair.{w}} (f : P ⟶ Q) (n : ℤ) :
    E.relativeComparison f (m := n) (n := n) rfl =
      (E.Hₚ n).map f.op := by
  simp [relativeComparison]

/-- The additive absolute/empty-relative comparison in cohomological variance. -/
noncomputable def absoluteRelativeIso
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    E.H n ≅ TopPair.incl.op ⋙ E.Hₚ n :=
  (CategoryTheory.NatIso.leftOp (E.unop.obj.iso n)).symm
/-- The cohomological product axiom, dual to homological disjoint-union additivity. -/
instance (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) (J : Type w) :
    PreservesLimitsOfShape (Discrete J) (E.Hₚ n) := by
  have := HomologyTheoryData.IsAdditive.preservesDiscreteCoproducts
    (E := E.unop.obj) n J
  apply preservesLimitsOfShape_leftOp

/-- The connecting morphism `H^n(A) ⟶ H^(n+1)(X,A)`. -/
def coboundary (E : GeneralizedCohomologyTheory C) (n : ℤ) :
    TopPair.proj₂.op ⋙ E.H n ⟶ E.Hₚ (n + 1) :=
  (E.unop.obj.δ (n + 1) n).leftOp

/-- A morphism of cohomology theories induces natural maps in the conventional direction. -/
def homₚ {E F : GeneralizedCohomologyTheory C} (f : E ⟶ F) (n : ℤ) :
    E.Hₚ n ⟶ F.Hₚ n :=
  (f.unop.hom.homₚ n).leftOp

/-- A morphism of cohomology theories induces natural maps on absolute cohomology. -/
def hom {E F : GeneralizedCohomologyTheory C} (f : E ⟶ F) (n : ℤ) :
    E.H n ⟶ F.H n :=
  (f.unop.hom.hom n).leftOp

/-- The absolute-relative comparison is natural in the additive theory. -/
@[reassoc]
theorem absoluteRelativeIso_hom_naturality
    {E F : GeneralizedCohomologyTheory.{u, v, w} C}
    (f : E ⟶ F) (n : ℤ) :
    hom f n ≫ (absoluteRelativeIso F n).hom =
      (absoluteRelativeIso E n).hom ≫
        TopPair.incl.op.whiskerLeft (homₚ f n) := by
  have h :
      (F.unop.obj.iso n).inv ≫ f.unop.hom.hom n =
        TopPair.incl.whiskerLeft (f.unop.hom.homₚ n) ≫
          (E.unop.obj.iso n).inv := by
    apply (cancel_epi (F.unop.obj.iso n).hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← Category.assoc, f.unop.hom.iso_comm]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg NatTrans.leftOp h
/-- Evaluation at relative cohomological degree `n`. -/
def hₚFunctor (n : ℤ) : GeneralizedCohomologyTheory.{u, v, w} C ⥤ (TopPair.{w}ᵒᵖ ⥤ C) where
  obj E := E.Hₚ n
  map f := homₚ f n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation at absolute cohomological degree `n`. -/
def hFunctor (n : ℤ) : GeneralizedCohomologyTheory.{u, v, w} C ⥤ (TopCat.{w}ᵒᵖ ⥤ C) where
  obj E := E.H n
  map f := hom f n
  map_id E := by
    ext X
    simp [hom]
    rfl
  map_comp f g := by
    ext X
    simp [hom]
    rfl
/-- Relative cohomology maps preserve identity morphisms. -/
@[simp]
lemma homₚ_id (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    homₚ (𝟙 E) n = 𝟙 (E.Hₚ n) :=
  rfl

/-- Relative cohomology maps preserve composition. -/
@[simp]
lemma homₚ_comp {E F G : GeneralizedCohomologyTheory.{u, v, w} C}
    (f : E ⟶ F) (g : F ⟶ G) (n : ℤ) :
    homₚ (f ≫ g) n = homₚ f n ≫ homₚ g n :=
  rfl

/-- Absolute cohomology maps preserve identity morphisms. -/
@[simp]
lemma hom_id (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    hom (𝟙 E) n = 𝟙 (E.H n) :=
  (hFunctor n).map_id E

/-- Absolute cohomology maps preserve composition. -/
@[simp]
lemma hom_comp {E F G : GeneralizedCohomologyTheory.{u, v, w} C}
    (f : E ⟶ F) (g : F ⟶ G) (n : ℤ) :
    hom (f ≫ g) n = hom f n ≫ hom g n :=
  (hFunctor n).map_comp f g

/-- Morphisms of generalized cohomology theories commute with coboundaries. -/
@[reassoc]
theorem coboundary_naturality
    {E F : GeneralizedCohomologyTheory.{u, v, w} C}
    (f : E ⟶ F) (n : ℤ) :
    Functor.whiskerLeft TopPair.proj₂.op (hom f n) ≫ F.coboundary n =
      E.coboundary n ≫ homₚ f (n + 1) := by
  ext X
  apply Quiver.Hom.op_inj
  exact f.unop.hom.w_app (n + 1) n X.unop

end GeneralizedCohomologyTheory

namespace OrdinaryCohomologyTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Categorical dual of `OrdinaryHomologyTheory.of`. -/
def of (E : HomologyTheoryData.{w} Cᵒᵖ) [E.IsHomotopyInvariant] [E.IsExact]
    [E.IsExcisive] [E.IsAdditive] [E.SatisfiesDimensionAxiom] :
    OrdinaryCohomologyTheory C :=
  Opposite.op (OrdinaryHomologyTheory.of E)

/-- Unwrapping recovers the underlying data. -/
@[simp]
lemma unop_obj_of (E : HomologyTheoryData.{w} Cᵒᵖ) [E.IsHomotopyInvariant] [E.IsExact]
    [E.IsExcisive] [E.IsAdditive] [E.SatisfiesDimensionAxiom] :
    (of E).unop.obj = E :=
  rfl

/-- Forget the dimension axiom from an ordinary cohomology theory. -/
def forgetDimension : OrdinaryCohomologyTheory C ⥤ GeneralizedCohomologyTheory C :=
  (OrdinaryHomologyTheory.forgetDimension (C := Cᵒᵖ)).op

/-- Relative degree-`n` cohomology as a functor of pairs. -/
abbrev Hₚ (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) : TopPair.{w}ᵒᵖ ⥤ C :=
  GeneralizedCohomologyTheory.Hₚ (forgetDimension.obj E) n

/-- Absolute degree-`n` cohomology as a functor of spaces. -/
abbrev H (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) : TopCat.{w}ᵒᵖ ⥤ C :=
  GeneralizedCohomologyTheory.H (forgetDimension.obj E) n

/-- Evaluate an ordinary theory on relative degree-`n` cohomology. -/
def hₚFunctor (n : ℤ) : OrdinaryCohomologyTheory.{u, v, w} C ⥤ (TopPair.{w}ᵒᵖ ⥤ C) :=
  forgetDimension ⋙ GeneralizedCohomologyTheory.hₚFunctor n

/-- Evaluate an ordinary theory on absolute degree-`n` cohomology. -/
def hFunctor (n : ℤ) : OrdinaryCohomologyTheory.{u, v, w} C ⥤ (TopCat.{w}ᵒᵖ ⥤ C) :=
  forgetDimension ⋙ GeneralizedCohomologyTheory.hFunctor n

end OrdinaryCohomologyTheory

end TopPair
