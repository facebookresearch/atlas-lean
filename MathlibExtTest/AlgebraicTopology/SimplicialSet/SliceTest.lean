/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Slice
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
# Tests for path slices and path mapping spaces

Consumer checks for the public declarations of
`MathlibExt/AlgebraicTopology/SimplicialSet/Slice.lean`: the
(reused, landed) path object `SSet.pathSpace` and its evaluations
`SSet.eval₀`/`SSet.eval₁`, the path over/under slices
(`SSet.pathSliceOver`/`SSet.pathSliceUnder`) and their universal
properties, functoriality in the ambient simplicial set, the
left/right path mapping spaces and their identification with the
fiber of the endpoint pair map, and the inner-fibration /
quasicategory instances for quasicategorical ambient simplicial
sets. These are the path-object (exponential) slices, not the
join slices; see the header of `Slice.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalClosed Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SliceTest

variable {X Y : SSet.{u}}

/-- The evaluation isomorphism `(ihom Δ[0]).obj X ≅ X`. -/
example : (ihom (Δ[0] : SSet.{u})).obj X ≅ X := SSet.evalDeltaZeroIso X

/-- Precomposition with an isomorphism gives an isomorphism of
internal homs. -/
example {A B : SSet.{u}} (e : A ≅ B) : (ihom B).obj X ≅ (ihom A).obj X :=
  SSet.preIso e X

example : SSet.{u} := SSet.pathSpace X

example : SSet.pathSpace X = (ihom (Δ[1] : SSet.{u})).obj X := rfl

example : SSet.pathSpace X ⟶ X := (SSet.eval₀ (X := X))

example : SSet.pathSpace X ⟶ X := (SSet.eval₁ (X := X))

example : SSet.pathSpace X ⟶ X ⨯ X := SSet.pathPair X

/-- The imported evaluations are precomposition with the vertex
inclusions, followed by evaluation at `Δ[0]`. -/
example : (SSet.eval₀ : SSet.pathSpace X ⟶ X) =
    (MonoidalClosed.pre (SSet.stdSimplex.δ (1 : Fin 2))).app X ≫
      (SSet.evalDeltaZeroIso X).hom :=
  SSet.pathSpace_eval₀_eq X

example : (SSet.eval₁ : SSet.pathSpace X ⟶ X) =
    (MonoidalClosed.pre (SSet.stdSimplex.δ (0 : Fin 2))).app X ≫
      (SSet.evalDeltaZeroIso X).hom :=
  SSet.pathSpace_eval₁_eq X

/-- Naturality of the evaluations and of the pair map. -/
example (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{u})).map f ≫ (SSet.eval₀ (X := Y)) =
      (SSet.eval₀ (X := X)) ≫ f :=
  SSet.pathSpace_map_eval₀ f

example (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{u})).map f ≫ (SSet.eval₁ (X := Y)) =
      (SSet.eval₁ (X := X)) ≫ f :=
  SSet.pathSpace_map_eval₁ f

example (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{u})).map f ≫ SSet.pathPair Y =
      SSet.pathPair X ≫ prod.map f f :=
  SSet.pathPair_natural f

/-- The pair map is the pair of evaluations. -/
example : SSet.pathPair X ≫ prod.fst = (SSet.eval₀ (X := X)) :=
  SSet.pathPair_fst X

example : SSet.pathPair X ≫ prod.snd = (SSet.eval₁ (X := X)) :=
  SSet.pathPair_snd X

variable (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- Over and under slices at a vertex given by a map `Δ[0] ⟶ X`. -/
example : SSet.{u} := SSet.pathSliceOver x

example : SSet.{u} := SSet.pathSliceUnder x

/-- Vertices can also be given as `0`-simplices, via `SSet.const`. -/
example (v : X _⦋0⦌) : SSet.{u} := SSet.pathSliceOver (SSet.const v)

example (v : X _⦋0⦌) : SSet.{u} := SSet.pathSliceUnder (SSet.const v)

example : SSet.pathSliceOver x ⟶ SSet.pathSpace X := SSet.pathSliceOver.fst x

example : SSet.pathSliceOver x ⟶ (Δ[0] : SSet.{u}) := SSet.pathSliceOver.snd x

example : SSet.pathSliceOver x ⟶ X := SSet.pathSliceOver.proj x

example : SSet.pathSliceUnder x ⟶ SSet.pathSpace X := SSet.pathSliceUnder.fst x

example : SSet.pathSliceUnder x ⟶ X := SSet.pathSliceUnder.proj x

/-- The defining pullback equations of the slices. -/
example : SSet.pathSliceOver.fst x ≫ (SSet.eval₁ (X := X)) =
    SSet.pathSliceOver.snd x ≫ x :=
  SSet.pathSliceOver.condition x

example : SSet.pathSliceUnder.fst x ≫ (SSet.eval₀ (X := X)) =
    SSet.pathSliceUnder.snd x ≫ x :=
  SSet.pathSliceUnder.condition x

/-- Maps into a slice are paths with constant endpoint. -/
example (Z : SSet.{u}) :
    (Z ⟶ SSet.pathSliceOver x) ≃
      {f : Z ⟶ SSet.pathSpace X //
        f ≫ (SSet.eval₁ (X := X)) = SSet.toDeltaZero Z ≫ x} :=
  SSet.pathSliceOver.homEquiv x Z

example (Z : SSet.{u}) :
    (Z ⟶ SSet.pathSliceUnder x) ≃
      {f : Z ⟶ SSet.pathSpace X //
        f ≫ (SSet.eval₀ (X := X)) = SSet.toDeltaZero Z ≫ x} :=
  SSet.pathSliceUnder.homEquiv x Z

/-- A vertex of the over-slice, read through `homEquiv`, is a path
ending at the given vertex. -/
example (p : (Δ[0] : SSet.{u}) ⟶ SSet.pathSpace X)
    (hp : p ≫ (SSet.eval₁ (X := X)) = SSet.toDeltaZero (Δ[0] : SSet.{u}) ≫ x) :
    (Δ[0] : SSet.{u}) ⟶ SSet.pathSliceOver x :=
  (SSet.pathSliceOver.homEquiv x (Δ[0] : SSet.{u})).symm ⟨p, hp⟩

/-- The lift into a slice has the expected underlying path and
projection. -/
example (Z : SSet.{u}) (f : Z ⟶ SSet.pathSpace X)
    (hf : f ≫ (SSet.eval₁ (X := X)) = SSet.toDeltaZero Z ≫ x) :
    SSet.pathSliceOver.lift x f hf ≫ SSet.pathSliceOver.fst x = f :=
  SSet.pathSliceOver.lift_fst x f hf

example (Z : SSet.{u}) (f : Z ⟶ SSet.pathSpace X)
    (hf : f ≫ (SSet.eval₁ (X := X)) = SSet.toDeltaZero Z ≫ x) :
    SSet.pathSliceOver.lift x f hf ≫ SSet.pathSliceOver.proj x =
      f ≫ (SSet.eval₀ (X := X)) :=
  SSet.pathSliceOver.lift_proj x f hf

/-- Functoriality of the slices in `X`, characterized by the
underlying path and by the projection. -/
example (f : X ⟶ Y) : SSet.pathSliceOver x ⟶ SSet.pathSliceOver (x ≫ f) :=
  SSet.pathSliceOver.map x f

example (f : X ⟶ Y) :
    SSet.pathSliceOver.map x f ≫ SSet.pathSliceOver.fst (x ≫ f) =
      SSet.pathSliceOver.fst x ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  SSet.pathSliceOver.map_fst x f

example (f : X ⟶ Y) :
    SSet.pathSliceOver.map x f ≫ SSet.pathSliceOver.proj (x ≫ f) =
      SSet.pathSliceOver.proj x ≫ f :=
  SSet.pathSliceOver.map_proj x f

example (f : X ⟶ Y) : SSet.pathSliceUnder x ⟶ SSet.pathSliceUnder (x ≫ f) :=
  SSet.pathSliceUnder.map x f

example (f : X ⟶ Y) :
    SSet.pathSliceUnder.map x f ≫ SSet.pathSliceUnder.proj (x ≫ f) =
      SSet.pathSliceUnder.proj x ≫ f :=
  SSet.pathSliceUnder.map_proj x f

/-- Left and right mapping spaces, and the fiber presentation. -/
example : SSet.{u} := SSet.pathMappingSpaceRight x y

example : SSet.{u} := SSet.pathMappingSpaceLeft x y

example : SSet.{u} := SSet.pathMappingSpaceFiber x y

example : SSet.{u} := SSet.pathMappingSpace x y

example : SSet.pathMappingSpace x y = SSet.pathMappingSpaceRight x y := rfl

example : SSet.pathMappingSpaceRight x y ⟶ SSet.pathSpace X :=
  SSet.pathMappingSpaceRight.toPath x y

example : SSet.pathMappingSpaceLeft x y ⟶ SSet.pathSpace X :=
  SSet.pathMappingSpaceLeft.toPath x y

example : SSet.pathMappingSpaceFiber x y ⟶ SSet.pathSpace X :=
  SSet.pathMappingSpaceFiber.fst x y

/-- The underlying path of a mapping-space point really has
endpoints `x` and `y`. -/
example : SSet.pathMappingSpaceRight.toPath x y ≫ (SSet.eval₀ (X := X)) =
    SSet.toDeltaZero (SSet.pathMappingSpaceRight x y) ≫ x :=
  SSet.pathMappingSpaceRight.toPath_src x y

example : SSet.pathMappingSpaceRight.toPath x y ≫ (SSet.eval₁ (X := X)) =
    SSet.toDeltaZero (SSet.pathMappingSpaceRight x y) ≫ y :=
  SSet.pathMappingSpaceRight.toPath_tgt x y

example : SSet.pathMappingSpaceLeft.toPath x y ≫ (SSet.eval₀ (X := X)) =
    SSet.toDeltaZero (SSet.pathMappingSpaceLeft x y) ≫ x :=
  SSet.pathMappingSpaceLeft.toPath_src x y

example : SSet.pathMappingSpaceLeft.toPath x y ≫ (SSet.eval₁ (X := X)) =
    SSet.toDeltaZero (SSet.pathMappingSpaceLeft x y) ≫ y :=
  SSet.pathMappingSpaceLeft.toPath_tgt x y

/-- Maps into a mapping space are paths with both endpoints
constant. -/
example (Z : SSet.{u}) :
    (Z ⟶ SSet.pathMappingSpaceRight x y) ≃
      {f : Z ⟶ SSet.pathSpace X //
        f ≫ (SSet.eval₀ (X := X)) = SSet.toDeltaZero Z ≫ x ∧
          f ≫ (SSet.eval₁ (X := X)) = SSet.toDeltaZero Z ≫ y} :=
  SSet.pathMappingSpaceRight.homEquiv x y Z

example (Z : SSet.{u}) :
    (Z ⟶ SSet.pathMappingSpaceLeft x y) ≃
      {f : Z ⟶ SSet.pathSpace X //
        f ≫ (SSet.eval₀ (X := X)) = SSet.toDeltaZero Z ≫ x ∧
          f ≫ (SSet.eval₁ (X := X)) = SSet.toDeltaZero Z ≫ y} :=
  SSet.pathMappingSpaceLeft.homEquiv x y Z

/-- The three presentations of the mapping space in the
path-object model are canonically isomorphic. -/
example : SSet.pathMappingSpaceLeft x y ≅ SSet.pathMappingSpaceRight x y :=
  SSet.pathMappingSpaceLeftIsoRight x y

example : SSet.pathMappingSpaceRight x y ≅ SSet.pathMappingSpaceFiber x y :=
  SSet.pathMappingSpaceRightIsoFiber x y

example : SSet.pathMappingSpaceLeft x y ≅ SSet.pathMappingSpaceFiber x y :=
  SSet.pathMappingSpaceLeftIsoFiber x y

/-- Functoriality of the mapping spaces in `X`. -/
example (f : X ⟶ Y) :
    SSet.pathMappingSpaceRight x y ⟶
      SSet.pathMappingSpaceRight (x ≫ f) (y ≫ f) :=
  SSet.pathMappingSpaceRight.map x y f

example (f : X ⟶ Y) :
    SSet.pathMappingSpaceRight.map x y f ≫
        SSet.pathMappingSpaceRight.toPath (x ≫ f) (y ≫ f) =
      SSet.pathMappingSpaceRight.toPath x y ≫
        (ihom (Δ[1] : SSet.{u})).map f :=
  SSet.pathMappingSpaceRight.map_toPath x y f

example (f : X ⟶ Y) :
    SSet.pathMappingSpaceLeft x y ⟶
      SSet.pathMappingSpaceLeft (x ≫ f) (y ≫ f) :=
  SSet.pathMappingSpaceLeft.map x y f

/-- The slices are base changes of the endpoint pair map along
the graph of the vertex. -/
example : SSet.pathSliceOver x ≅
    pullback (SSet.pathPair X)
      (prod.lift (𝟙 X) (SSet.toDeltaZero X ≫ x)) :=
  SSet.pathSliceOverIsoPairPullback x

example : SSet.pathSliceUnder x ≅
    pullback (SSet.pathPair X)
      (prod.lift (SSet.toDeltaZero X ≫ x) (𝟙 X)) :=
  SSet.pathSliceUnderIsoPairPullback x

/-- The boundary of `Δ[1]` is the coproduct of its two vertices,
and accordingly `(ihom ∂Δ[1]).obj X ≅ X ⨯ X`. -/
example : IsColimit SSet.boundaryOneCofan :=
  SSet.boundaryOneCofanIsColimit

example : (ihom (∂Δ[1] : SSet.{u})).obj X ≅ X ⨯ X :=
  SSet.ihomBoundaryOneIso X

example : (SSet.ihomBoundaryOneIso X).hom ≫ prod.fst =
    SSet.boundaryEvalSrc X :=
  SSet.ihomBoundaryOneIso_hom_fst X

example : (SSet.ihomBoundaryOneIso X).hom ≫ prod.snd =
    SSet.boundaryEvalTgt X :=
  SSet.ihomBoundaryOneIso_hom_snd X

/-- Under `(ihom ∂Δ[1]).obj X ≅ X ⨯ X`, the pair map is
precomposition with the boundary inclusion. -/
example : SSet.pathPair X =
    (MonoidalClosed.pre (SSet.boundary 1).ι).app X ≫
      (SSet.ihomBoundaryOneIso X).hom :=
  SSet.pathPair_eq X

section QuasicategoryAmbient

variable [SSet.Quasicategory X]

/-- For a quasicategory, the evaluations and the pair map are
inner fibrations. -/
example : SSet.InnerFibration ((SSet.eval₀ (X := X))) := inferInstance

example : SSet.InnerFibration ((SSet.eval₁ (X := X))) := inferInstance

example : SSet.InnerFibration (SSet.pathPair X) := inferInstance

example : SSet.InnerFibration (SSet.pathSliceOver.snd x) := inferInstance

example : SSet.InnerFibration (SSet.pathSliceUnder.snd x) := inferInstance

example : SSet.InnerFibration (SSet.pathMappingSpaceFiber.snd x y) :=
  inferInstance

/-- The slice projections are inner fibrations. -/
example : SSet.InnerFibration (SSet.pathSliceOver.proj x) := inferInstance

example : SSet.InnerFibration (SSet.pathSliceUnder.proj x) := inferInstance

/-- For a quasicategory, the slices and mapping spaces are
quasicategories. -/
example : SSet.Quasicategory (SSet.pathSliceOver x) := inferInstance

example : SSet.Quasicategory (SSet.pathSliceUnder x) := inferInstance

example : SSet.Quasicategory (SSet.pathMappingSpaceFiber x y) :=
  inferInstance

example : SSet.Quasicategory (SSet.pathMappingSpaceRight x y) :=
  inferInstance

example : SSet.Quasicategory (SSet.pathMappingSpaceLeft x y) :=
  inferInstance

example : SSet.Quasicategory (SSet.pathMappingSpace x y) := inferInstance

end QuasicategoryAmbient

/-- Every standard simplex is a quasicategory (the single
instance from `StdSimplexQuasicategory.lean`, covering `Δ[0]`). -/
example (n : ℕ) : SSet.Quasicategory (Δ[n] : SSet.{u}) := inferInstance

/-- `Δ[0]` is a quasicategory, hence its own path slices and path
mapping spaces are quasicategories. -/
example : SSet.Quasicategory (Δ[0] : SSet.{u}) := inferInstance

example (x y : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u})) :
    SSet.Quasicategory (SSet.pathMappingSpace x y) := inferInstance

/-- A concrete quasicategory: the nerve of the walking arrow. Its
slices over the two vertices and the mapping space between them
are quasicategories. -/
example (x y : (Δ[0] : SSet.{u}) ⟶ nerve (ULift.{u} (Fin 2))) :
    SSet.Quasicategory (SSet.pathSliceOver x) ∧
      SSet.Quasicategory (SSet.pathMappingSpace x y) :=
  ⟨inferInstance, inferInstance⟩

/-- Being a quasicategory transports along isomorphisms, as used
for the left/right mapping spaces. -/
example (x y : (Δ[0] : SSet.{u}) ⟶ nerve (ULift.{u} (Fin 2))) :
    SSet.Quasicategory (SSet.pathMappingSpaceLeft x y) :=
  SSet.quasicategory_of_iso (SSet.pathMappingSpaceLeftIsoFiber x y)

/-- A vertex of `Δ[1]` as a point in a slice: the target face
inclusion itself is a vertex of `X = Δ[1]`. -/
example : SSet.{u} :=
  SSet.pathSliceOver (X := (Δ[1] : SSet.{u})) (SSet.stdSimplex.δ 0)

example : SSet.{u} :=
  SSet.pathMappingSpace (X := (Δ[1] : SSet.{u}))
    (SSet.stdSimplex.δ 1) (SSet.stdSimplex.δ 0)

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SliceTest
