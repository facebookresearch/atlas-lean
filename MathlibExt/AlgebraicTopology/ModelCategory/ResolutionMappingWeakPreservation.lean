/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import MathlibExt.AlgebraicTopology.ModelCategory.BrownSourceFunctor
public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.ReedyFiniteTensorBoundaryClasses
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Covariant Brown weak preservation from actual trivial-fibration maps

The original fibrant Brown factorization proves weak preservation on fibrant
objects from the actual trivial-fibration mapping law. No global tensor or
adjunction is required for this source calculation.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC uD vD

open CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]

/-- Brown's original fibrant factorization yields target weak preservation from true
trivial-fibration maps. -/
theorem targetFunctor_weak_of_trivialFibrations
    (F : C ⥤ D)
    (hF : ∀ {X Y : C} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p],
      WeakEquivalence (F.map p))
    {X Y : C} (p : X ⟶ Y) [WeakEquivalence p] [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence (F.map p) := by
  let h : FibrantBrownFactorization p := Classical.choice inferInstance
  let _ : WeakEquivalence (F.map h.p) := hF h.p
  let _ : WeakEquivalence (F.map h.r) := hF h.r
  have hir : F.map h.i ≫ F.map h.r = 𝟙 (F.obj X) := by
    rw [← F.map_comp, h.i_r, F.map_id]
  let _ : WeakEquivalence (F.map h.i) := weakEquivalence_of_postcomp_of_fac hir
  rw [← h.fac, F.map_comp]
  infer_instance

end HomotopicalAlgebra

end
end
end

section



/-!
# Original initial and terminal canonical resolution Hom objects

The actual structured functor Hom has a unique simplex whenever its coefficient
source is initial or its coefficient target is terminal. This proves the genuine
terminal mapping-object properties needed to identify ordinary precomposition
and postcomposition with their supplied mapping pullback corners.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC

open CategoryTheory Limits

namespace HomotopicalAlgebra.ResolutionHomInitialTerminal

variable {C : Type uC} [Category.{vC} C]

/-- Every terminal-target simplex is the complete original family of terminal coefficient maps. -/
def terminalSimplex (F T : SimplicialObject C) (hT : ∀ k, IsTerminal (T.obj k))
    (n : SimplexCategoryᵒᵖ) : (Functor.functorHom F T).obj n where
  app k _ := (hT k).from (F.obj k)
  naturality _ _ := (hT _).hom_ext _ _

/-- Every initial-source simplex is the complete original family of initial coefficient maps. -/
def initialSimplex (I B : SimplicialObject C) (hI : ∀ k, IsInitial (I.obj k))
    (n : SimplexCategoryᵒᵖ) : (Functor.functorHom I B).obj n where
  app k _ := (hI k).to (B.obj k)
  naturality _ _ := (hI _).hom_ext _ _

/-- The actual canonical Hom to an objectwise terminal diagram is terminal as a simplicial set. -/
def terminalHom_of_components (F T : SimplicialObject C) (hT : ∀ k, IsTerminal (T.obj k)) :
    IsTerminal (SimplicialCategory.sHom F T) :=
  IsTerminal.ofUniqueHom
    (fun K =>
      { app n := ↾fun _ => terminalSimplex F T hT n
        naturality n m f := by
          ext x
          apply Functor.functorHom_ext
          intro k g
          exact (hT k).hom_ext _ _ })
    (by
      intro K f
      ext n x
      apply Functor.functorHom_ext
      intro k g
      exact (hT k).hom_ext _ _)

/-- The actual canonical Hom from an objectwise initial diagram is terminal as a simplicial set. -/
def initialHomOfComponents (I B : SimplicialObject C) (hI : ∀ k, IsInitial (I.obj k)) :
    IsTerminal (SimplicialCategory.sHom I B) :=
  IsTerminal.ofUniqueHom
    (fun K =>
      { app n := ↾fun _ => initialSimplex I B hI n
        naturality n m f := by
          ext x
          apply Functor.functorHom_ext
          intro k g
          exact (hI k).hom_ext _ _ })
    (by
      intro K f
      ext n x
      apply Functor.functorHom_ext
      intro k g
      exact (hI k).hom_ext _ _)

variable [HasInitial C] [HasTerminal C]

omit [HasInitial C] in
/-- Every original terminal diagram gives the same actual terminal canonical Hom. -/
def terminalHom (F T : SimplicialObject C) (hT : IsTerminal T) :
    IsTerminal (SimplicialCategory.sHom F T) :=
  terminalHom_of_components F T (fun k =>
    IsTerminal.isTerminalObj ((evaluation SimplexCategoryᵒᵖ C).obj k) T hT)

omit [HasTerminal C] in
/-- Every original initial diagram gives the same actual terminal canonical Hom. -/
def initialHom (I B : SimplicialObject C) (hI : IsInitial I) :
    IsTerminal (SimplicialCategory.sHom I B) :=
  initialHomOfComponents I B (fun k =>
    IsInitial.isInitialObj ((evaluation SimplexCategoryᵒᵖ C).obj k) I hI)

omit [HasInitial C] in
/-- The native terminal-target pullback corner is exactly the original canonical precomposition map.
-/
def terminalCorner {A A' : SimplicialObject C} (i : A ⟶ A') (B : SimplicialObject C) :
    (SimplicialCategory.sHomFunctor (SimplicialObject C)).PullbackObjObj i (terminal.from B) where
  pt := SimplicialCategory.sHom A B
  fst := 𝟙 _
  snd := (terminalHom A' (⊤_ (SimplicialObject C)) terminalIsTerminal).from _
  isPullback := by
    let _ : IsIso (𝟙 (SimplicialCategory.sHom A B)) := (Iso.refl _).isIso_hom
    let _ : IsIso (((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app
        (⊤_ (SimplicialObject C))) :=
      isIso_of_isTerminal (terminalHom A' _ terminalIsTerminal) (terminalHom A _ terminalIsTerminal)
          _
    exact IsPullback.of_horiz_isIso (fst := 𝟙 (SimplicialCategory.sHom A B))
      (g := ((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app
        (⊤_ (SimplicialObject C))) ⟨(terminalHom A _ terminalIsTerminal).hom_ext _ _⟩
  π := ((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app B
  π_snd := (terminalHom A' _ terminalIsTerminal).hom_ext _ _

omit [HasTerminal C] in
/-- The native initial-source pullback corner is exactly the original canonical postcomposition map.
-/
def initialCorner (A : SimplicialObject C) {B B' : SimplicialObject C} (p : B ⟶ B') :
    (SimplicialCategory.sHomFunctor (SimplicialObject C)).PullbackObjObj (initial.to A) p where
  pt := SimplicialCategory.sHom A B'
  fst := (initialHom (⊥_ (SimplicialObject C)) B initialIsInitial).from _
  snd := 𝟙 _
  isPullback := by
    let _ : IsIso (𝟙 (SimplicialCategory.sHom A B')) := (Iso.refl _).isIso_hom
    let _ : IsIso (((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj
        (.op (⊥_ (SimplicialObject C)))).map p) :=
      isIso_of_isTerminal (initialHom _ B initialIsInitial) (initialHom _ B' initialIsInitial) _
    exact IsPullback.of_vert_isIso (snd := 𝟙 (SimplicialCategory.sHom A B'))
      (f := ((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj
        (.op (⊥_ (SimplicialObject C)))).map p) ⟨(initialHom _ B' initialIsInitial).hom_ext _ _⟩
  π := ((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj (.op A)).map p
  π_fst := (initialHom _ B initialIsInitial).hom_ext _ _

omit [HasInitial C] in
/-- The full terminal corner retains the exact original source mapping function. -/
theorem terminalCorner_π {A A' : SimplicialObject C} (i : A ⟶ A') (B : SimplicialObject C) :
    (terminalCorner i B).π =
        ((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app B := rfl

omit [HasTerminal C] in
/-- The full initial corner retains the exact original target mapping function. -/
theorem initialCorner_π (A : SimplicialObject C) {B B' : SimplicialObject C} (p : B ⟶ B') :
    (initialCorner A p).π =
        ((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj (.op A)).map p := rfl

end HomotopicalAlgebra.ResolutionHomInitialTerminal

end
end
end

section



/-!
# Actual simplicial trivial fibrations from all original boundary lifts

The original boundary family generates the monomorphism lifting class. The
actual selected model's weak factorization system therefore identifies all
boundary lifts with its same trivial fibrations, in every simplicial universe.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

/-- All actual standard-boundary lifting properties characterize the same original trivial
fibration. -/
theorem boundaryLifting_iff_trivialFibration {X Y : SSet.{u}} (p : X ⟶ Y) :
    (∀ n : ℕ, HasLiftingProperty (boundary.{u} n).ι p) ↔ trivialFibrations SSet.{u} p := by
  constructor
  · intro h
    have hi : I.rlp p := by
      intro A B i hi
      obtain ⟨n⟩ := hi
      exact h n
    rw [← rlp_eq_of_wfs (cofibrations SSet.{u}) (trivialFibrations SSet.{u})]
    rw [cofibrations_eq, SSet.rlp_monomorphisms]
    exact hi
  · intro hp n
    let _ : Fibration p := (fibration_iff _).mpr hp.1
    let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr hp.2
    let _ : Cofibration (boundary.{u} n).ι := cofibration_of_mono _
    infer_instance

end SSet.modelCategoryQuillen

end
end
end

section



/-!
# Genuine boundary lifting for canonical simplicial resolution mapping corners

The proved original finite boundary pushout products and complete Arrow/Lift
transposition yield actual mapping trivial fibrations. Both branches preserve
the supplied original mapping pullback square. No full simplicial Reedy model
action or final function-complex preservation outcome is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.ResolutionMappingBoundary

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {A A' B B' : SimplicialObject C} {i : A ⟶ A'} {p : B ⟶ B'}
  (sq : (SimplicialCategory.sHomFunctor (SimplicialObject C)).PullbackObjObj i p)

open GeneratedFramingModels FiniteResolutionTensor ReedyFiniteTensorGeometry

/-- A true original Reedy trivial cofibration gives the supplied actual mapping trivial fibration.
-/
theorem trivial_left :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) i →
      Fibration p → trivialFibrations SSet.{vC} sq.π := by
  let _ := simplicialModel d
  intro hi hp
  apply (SSet.modelCategoryQuillen.boundaryLifting_iff_trivialFibration sq.π).mp
  intro n
  have hir : ReedyStructure.latchingClass SimplexCategory.reedyOp (trivialCofibrations C) i := by
    rw [← simplicial_trivialCofibrations_eq d]
    exact hi
  have hpp : trivialCofibrations (SimplicialObject C)
      (pushoutProduct i (SSet.boundary.{vC} n).ι) := by
    rw [simplicial_trivialCofibrations_eq d]
    exact nativeBoundaryPushoutProduct_reedyTrivialCofibration i hir n
  let _ : Cofibration (pushoutProduct i (SSet.boundary.{vC} n).ι) := (cofibration_iff _).mpr hpp.1
  let _ : WeakEquivalence (pushoutProduct i (SSet.boundary.{vC} n).ι) :=
    (weakEquivalence_iff _).mpr hpp.2
  let _ : Fibration p := hp
  exact (hasLiftingProperty_iff sq).mp inferInstance

/-- A true original Reedy trivial fibration gives the supplied actual mapping trivial fibration. -/
theorem trivial_right :
    letI := simplicialModel d
    Cofibration i →
      trivialFibrations (SimplicialObject C) p → trivialFibrations SSet.{vC} sq.π := by
  let _ := simplicialModel d
  intro hi hp
  apply (SSet.modelCategoryQuillen.boundaryLifting_iff_trivialFibration sq.π).mp
  intro n
  have hir : ReedyStructure.latchingClass SimplexCategory.reedyOp (cofibrations C) i := by
    rw [← simplicial_cofibrations_eq d]
    exact (cofibration_iff _).mp hi
  have hpp : cofibrations (SimplicialObject C) (pushoutProduct i (SSet.boundary.{vC} n).ι) := by
    rw [simplicial_cofibrations_eq d]
    exact nativeBoundaryPushoutProduct_reedyCofibration i hir n
  let _ : Cofibration (pushoutProduct i (SSet.boundary.{vC} n).ι) := (cofibration_iff _).mpr hpp
  let _ : Fibration p := (fibration_iff _).mpr hp.1
  let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr hp.2
  exact (hasLiftingProperty_iff sq).mp inferInstance

end HomotopicalAlgebra.ResolutionMappingBoundary

end
end
end

section



/-!
# Actual weak preservation of canonical resolution mapping functions

The native terminal and initial mapping corners identify the original
precomposition and postcomposition maps. The proved boundary lifting branches
give their genuine trivial-fibration laws, then the original Brown source and
target factorizations give weak preservation at cofibrant and fibrant endpoints.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.ResolutionMappingWeakPreservation

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFramingModels ResolutionHomInitialTerminal

/-- The original precomposition by a true Reedy trivial cofibration is a genuine simplicial trivial
fibration. -/
theorem precomp_trivial {A A' : SimplicialObject C} (i : A ⟶ A') (B : SimplicialObject C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) i → IsFibrant B →
      trivialFibrations SSet.{vC}
          (((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app B) := by
  let _ := simplicialModel d
  intro hi hB
  let _ : IsFibrant B := hB
  exact ResolutionMappingBoundary.trivial_left d (terminalCorner i B) hi inferInstance

/-- The original postcomposition by a true Reedy trivial fibration is a genuine simplicial trivial
fibration. -/
theorem postcomp_trivial (A : SimplicialObject C) {B B' : SimplicialObject C} (p : B ⟶ B') :
    letI := simplicialModel d
    IsCofibrant A → trivialFibrations (SimplicialObject C) p →
      trivialFibrations SSet.{vC}
        (((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj (.op A)).map p) := by
  let _ := simplicialModel d
  intro hA hp
  exact ResolutionMappingBoundary.trivial_right d (initialCorner A p) hA hp

/-- Every original weak source map between actual cofibrant diagrams gives the same weak
precomposition map. -/
theorem precomp_weak {A A' : SimplicialObject C} (i : A ⟶ A') (B : SimplicialObject C) :
    letI := simplicialModel d
    WeakEquivalence i → IsCofibrant A → IsCofibrant A' → IsFibrant B →
      WeakEquivalence (((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app B) := by
  let _ := simplicialModel d
  intro hi hA hA' hB
  let _ : WeakEquivalence i := hi
  let _ : IsCofibrant A := hA
  let _ : IsCofibrant A' := hA'
  change WeakEquivalence
      (((SimplicialCategory.sHomFunctor (SimplicialObject C)).flip.obj B).map i.op)
  apply sourceFunctor_weak_of_trivialCofibrations
  intro X Y j _ _
  exact (weakEquivalence_iff _).mpr ((precomp_trivial d j B (mem_trivialCofibrations j) hB).2)

/-- Every original weak target map between actual fibrant diagrams gives the same weak
postcomposition map. -/
theorem postcomp_weak (A : SimplicialObject C) {B B' : SimplicialObject C} (p : B ⟶ B') :
    letI := simplicialModel d
    IsCofibrant A → WeakEquivalence p → IsFibrant B → IsFibrant B' →
      WeakEquivalence
          (((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj (.op A)).map p) := by
  let _ := simplicialModel d
  intro hA hp hB hB'
  let _ : WeakEquivalence p := hp
  let _ : IsFibrant B := hB
  let _ : IsFibrant B' := hB'
  apply targetFunctor_weak_of_trivialFibrations
  intro X Y q _ _
  exact (weakEquivalence_iff _).mpr ((postcomp_trivial d A q hA (mem_trivialFibrations q)).2)

end HomotopicalAlgebra.ResolutionMappingWeakPreservation

end
end
end
