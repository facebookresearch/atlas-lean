/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Functorial path objects for native enriched diagrams

The native enriched projective model’s chosen `J`-factorization, at its
realized generator cardinal and ordinal bottom, factors the diagonal
`X ⟶ X ⨯ X` into a trivial-cofibration unit and a fibration of joint endpoints.
This gives a functorial very good path object, and native fibrancy makes each
endpoint a trivial fibration. The construction preserves weak equivalences
and retains the original middle functor and both factor maps. The path object
is fibrant, and is cofibrant when `X` is cofibrant.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed ZeroObject

namespace HomotopicalAlgebra.EnrichedProjective.Native.Path
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
attribute [local instance] Native.modelCategory

private theorem nativeFiniteLimits : HasFiniteLimits (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  (Native.modelCategory (B := B) (A := A)).cm1a
attribute [local instance] nativeFiniteLimits

/-- The actual native product functor retains both complete original map components. -/
def square : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A where
  obj X := X ⨯ X
  map f := prod.map f f
  map_id X := prod.map_id_id
  map_comp f g := by
    apply prod.hom_ext <;> simp

/-- The genuine native diagonal is the original object map into its actual binary product. -/
def diagonal : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) ⟶ square (A := A) where
  app X := prod.lift (𝟙 X) (𝟙 X)
  naturality X Y f := by
    apply prod.hom_ext <;> simp [square]

/-- The entire original diagonal Arrow functor retains both sides of every source map. -/
def diagonalArrow : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  obj X := Arrow.mk (diagonal.app X)
  map f := Arrow.homMk f (square.map f) (diagonal.naturality f)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- The native path functor is the SAME original J/κ/B middle functor on the genuine diagonal. -/
def pathFunctor : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A :=
  diagonalArrow ⋙ (Native.fibrantFactorizationData (B := B) (A := A)).Z

/-- The entire original J first map is the actual natural path unit. -/
def unit : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) ⟶ pathFunctor (A := A) :=
  Functor.whiskerLeft diagonalArrow (Native.fibrantFactorizationData (B := B) (A := A)).i

/-- The complete original J second map is the natural joint endpoint map. -/
def endpoints : pathFunctor (A := A) ⟶ square (A := A) :=
  Functor.whiskerLeft diagonalArrow (Native.fibrantFactorizationData (B := B) (A := A)).p

/-- The first endpoint is the original joint endpoint followed by the actual first projection. -/
def first : pathFunctor (A := A) ⟶ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  app X := endpoints.app X ≫ prod.fst
  naturality X Y f := by
    change pathFunctor.map f ≫ (endpoints.app Y ≫ (prod.fst : Y ⨯ Y ⟶ Y)) =
      (endpoints.app X ≫ (prod.fst : X ⨯ X ⟶ X)) ≫ f
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ (prod.fst : Y ⨯ Y ⟶ Y)) (endpoints.naturality f)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun g => endpoints.app X ≫ g) (prod.map_fst f f)).trans
            (Category.assoc _ _ _).symm)))

/-- The second endpoint retains the same original path and actual second projection. -/
def second : pathFunctor (A := A) ⟶ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  app X := endpoints.app X ≫ prod.snd
  naturality X Y f := by
    change pathFunctor.map f ≫ (endpoints.app Y ≫ (prod.snd : Y ⨯ Y ⟶ Y)) =
      (endpoints.app X ≫ (prod.snd : X ⨯ X ⟶ X)) ≫ f
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ (prod.snd : Y ⨯ Y ⟶ Y)) (endpoints.naturality f)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun g => endpoints.app X ≫ g) (prod.map_snd f f)).trans
            (Category.assoc _ _ _).symm)))

/-- The whole original J intermediate functor is unchanged. -/
theorem pathFunctor_original : pathFunctor (B := B) (A := A) =
    diagonalArrow ⋙ (Native.fibrantFactorizationData (B := B) (A := A)).Z := rfl

/-- Every arbitrary source map retains the complete original diagonal Arrow map. -/
theorem pathFunctor_map_original {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A}
    (f : X ⟶ Y) :
    pathFunctor.map f = (Native.fibrantFactorizationData (B := B) (A := A)).Z.map
      (diagonalArrow.map f) := rfl

/-- The exact original J maps factor the same caller diagonal. -/
theorem fac (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    unit.app X ≫ endpoints.app X = diagonal.app X :=
  (Native.fibrantFactorizationData (B := B) (A := A)).fac_app

/-- Both original endpoint composites are literal identity sections. -/
theorem unit_first (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    unit.app X ≫ first.app X = 𝟙 X := by
  change unit.app X ≫ (endpoints.app X ≫ (prod.fst : X ⨯ X ⟶ X)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (prod.fst : X ⨯ X ⟶ X)) (fac X)).trans
      (prod.lift_fst _ _))

theorem unit_second (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    unit.app X ≫ second.app X = 𝟙 X := by
  change unit.app X ≫ (endpoints.app X ≫ (prod.snd : X ⨯ X ⟶ X)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (prod.snd : X ⨯ X ⟶ X)) (fac X)).trans
      (prod.lift_snd _ _))

/-- The exact original J unit has the actual full trivial-cofibration class. -/
theorem unit_mem_trivialCofibrations (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) (unit.app X) :=
  (Native.fibrantFactorizationData (B := B) (A := A)).hi _

/-- The same original unit is a genuine native weak equivalence. -/
theorem unit_mem_weakEquivalences (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (unit.app X) :=
  (unit_mem_trivialCofibrations X).2

/-- The complete joint endpoint map has the original native fibration class. -/
theorem endpoints_mem_fibrations (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) (endpoints.app X) :=
  (Native.fibrantFactorizationData (B := B) (A := A)).hp _

/-- The actual original unit naturality preserves weak source maps through the path functor. -/
theorem pathFunctor_map_mem_weakEquivalences
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (pathFunctor.map f) := by
  apply (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).of_precomp
    (unit.app X) (pathFunctor.map f) (unit_mem_weakEquivalences X)
  rw [← unit.naturality]
  exact (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem _ _ hf
    (unit_mem_weakEquivalences Y)


/-- Package the SAME chosen original J factorization as an actual native path object. -/
def pathObject (X : EnrichedFunctorCat PointedCGWH.{u, v} A) : PathObject X where
  P := pathFunctor.obj X
  p₀ := first.app X
  p₁ := second.app X
  ι := unit.app X
  ι_p₀ := unit_first X
  ι_p₁ := unit_second X
  weakEquivalence_ι := (weakEquivalence_iff _).2 (unit_mem_weakEquivalences X)

/-- Its entire middle object and both original endpoint maps are the returned path functor data. -/
theorem pathObject_fields (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (pathObject X).P = pathFunctor.obj X ∧ (pathObject X).ι = unit.app X ∧
      (pathObject X).p₀ = first.app X ∧ (pathObject X).p₁ = second.app X :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The original path package is very good through the same exact first and second maps. -/
theorem pathObject_isVeryGood (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (pathObject X).IsVeryGood := by
  refine { fibration_p := ?_, cofibration_ι := ?_ }
  · change Fibration (prod.lift (first.app X) (second.app X))
    have h : prod.lift (first.app X) (second.app X) = endpoints.app X := by
      apply prod.hom_ext
      · exact prod.lift_fst _ _
      · exact prod.lift_snd _ _
    rw [h]
    exact (fibration_iff _).2 (endpoints_mem_fibrations X)
  · exact (cofibration_iff _).2 (unit_mem_trivialCofibrations X).1

/-- The first original endpoint is weak by its identity section and the original unit. -/
theorem first_mem_weakEquivalences (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (first.app X) := by
  apply (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).of_precomp
    (unit.app X) (first.app X) (unit_mem_weakEquivalences X)
  exact (by
    rw [unit_first]
    exact (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).id_mem X)

/-- The second original endpoint is weak through the same original path-object unit. -/
theorem second_mem_weakEquivalences (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (second.app X) := by
  apply (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).of_precomp
    (unit.app X) (second.app X) (unit_mem_weakEquivalences X)
  exact (by
    rw [unit_second]
    exact (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).id_mem X)

/-- Actual native fibrancy makes the first original product endpoint a fibration. -/
theorem first_mem_fibrations (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) (first.app X) := by
  let _ : IsFibrant X := Native.allObjectsFibrant X
  have hproj : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (prod.fst : X ⨯ X ⟶ X) := (fibration_iff _).1 inferInstance
  exact (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem
    (endpoints.app X) (prod.fst : X ⨯ X ⟶ X) (endpoints_mem_fibrations X) hproj

/-- The same genuine native fibrancy gives the second original endpoint fibration. -/
theorem second_mem_fibrations (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) (second.app X) := by
  let _ : IsFibrant X := Native.allObjectsFibrant X
  have hproj : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (prod.snd : X ⨯ X ⟶ X) := (fibration_iff _).1 inferInstance
  exact (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem
    (endpoints.app X) (prod.snd : X ⨯ X ⟶ X) (endpoints_mem_fibrations X) hproj

/-- Both original endpoints are TF under the actual native fibrancy condition. -/
theorem endpoints_mem_trivialFibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) (first.app X) ∧
      trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) (second.app X) :=
  ⟨⟨first_mem_fibrations X, first_mem_weakEquivalences X⟩,
    ⟨second_mem_fibrations X, second_mem_weakEquivalences X⟩⟩

omit B in
/-- The original whole Arrow map retains both the source and actual product map. -/
theorem diagonalArrow_map_fields {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A}
    (f : X ⟶ Y) :
    (diagonalArrow.map f).left = f ∧ (diagonalArrow.map f).right = prod.map f f :=
  ⟨rfl, rfl⟩

/-- The actual entire Arrow-valued factorization has precisely the original Z/i/p and κ data. -/
theorem pathFunctor_obj_original (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    pathFunctor.obj X = (Native.fibrantFactorizationData (B := B) (A := A)).Z.obj
      (Arrow.mk (diagonal.app X)) := rfl

/-- The original first natural transformation remains the actual path unit. -/
theorem unit_original (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    unit.app X = (Native.fibrantFactorizationData (B := B) (A := A)).i.app
      (Arrow.mk (diagonal.app X)) := rfl

/-- The original second natural transformation is retained as the entire joint endpoint map. -/
theorem endpoints_original (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    endpoints.app X = (Native.fibrantFactorizationData (B := B) (A := A)).p.app
      (Arrow.mk (diagonal.app X)) := rfl

/-- The full original J middle Arrow functor remains the same arbitrary full diagram action. -/
theorem pathFunctor_Arrow_original : (pathFunctor (B := B) (A := A)).mapArrow =
    (diagonalArrow (A := A) ⋙
      (Native.fibrantFactorizationData (B := B) (A := A)).Z).mapArrow := rfl

/-- Unit naturality retains both source and complete original path maps. -/
theorem unit_naturality {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    f ≫ unit.app Y = unit.app X ≫ pathFunctor.map f := unit.naturality f

/-- Joint endpoint naturality includes both actual product-map components. -/
theorem endpoints_naturality {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A}
    (f : X ⟶ Y) :
    pathFunctor.map f ≫ endpoints.app Y = endpoints.app X ≫ prod.map f f :=
  endpoints.naturality f

/-- The first endpoint retains the full source-map naturality square. -/
theorem first_naturality {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    pathFunctor.map f ≫ first.app Y = first.app X ≫ f := first.naturality f

/-- The second endpoint retains the full same-source-map naturality square. -/
theorem second_naturality {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    pathFunctor.map f ≫ second.app Y = second.app X ≫ f := second.naturality f

/-- The entire original factorization is the genuine diagonal natural transformation. -/
theorem factorization_original : unit (B := B) (A := A) ≫ endpoints = diagonal := by
  apply NatTrans.ext
  exact funext fun X => fac X

/-- The actual returned path is fibrant by original joint endpoints and native level fibrancy. -/
theorem path_isFibrant (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsFibrant (pathFunctor.obj X) := by
  let _ : IsFibrant X := Native.allObjectsFibrant X
  let _ : (pathObject X).IsVeryGood := pathObject_isVeryGood X
  exact inferInstanceAs (IsFibrant (pathObject X).P)

/-- For a genuinely cofibrant native source the original J unit retains path cofibrancy. -/
theorem path_isCofibrant (X : EnrichedFunctorCat PointedCGWH.{u, v} A) [IsCofibrant X] :
    IsCofibrant (pathFunctor.obj X) := by
  let _ : (pathObject X).IsVeryGood := pathObject_isVeryGood X
  exact inferInstanceAs (IsCofibrant (pathObject X).P)

end HomotopicalAlgebra.EnrichedProjective.Native.Path
