/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicCycleProducts
public import MathlibExt.AlgebraicGeometry.PointedMotivicQuotients
public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Tate multiplication, coefficients and derived tensor maps

Nonnegative Tate multiplication is the literal shuffle/external-cycle
chain map, transported by negative-index extension and Mathlib's native
tensor/shift isomorphisms. All integer weights retain the published zero
convention. Coefficient multiplication is fixed on every pure local tensor
and every coefficient element entering the constant sheaf.

The derived tensor uses actual augmented K-flat complexes and the native
total complex. Its canonical map to ordinary tensor is the image of those
augmentations. It is not a freely supplied cohomology pairing.

Sources: Mazza--Voevodsky--Weibel, Constructions 3.10--3.11, Corollary
3.12 and Lecture 8; Voevodsky arXiv:math/0107109v1, Section 2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicTensorOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicCycleProducts PointedMotivicQuotients
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  (N : NisTensorSystem k) [N.functor.Additive]
  [∀ F, (N.functor.obj F).Additive]

/-- Both native tensor-shift isomorphisms, with their Koszul signs. -/
def tensorShiftIso (F H : CochainComplex (NisModules (k := k)) ℤ)
    (a b : ℤ) : cochainTensor N (F⟦a⟧) (H⟦b⟧) ≅
      (cochainTensor N F H)⟦a + b⟧ :=
  CochainComplex.mapBifunctorShift₁Iso F (H⟦b⟧) N.functor a ≪≫
    (shiftFunctor _ a).mapIso
      (CochainComplex.mapBifunctorShift₂Iso F H N.functor b) ≪≫
    ((shiftFunctorAdd' _ b a (a + b) (by omega)).app
      (cochainTensor N F H)).symm

/-- The summand normalization of a comparison between the tensor of negative-index
extensions and the negative-index extension of the tensor: on the `(a, b)` summand it is
the native tensor summand, transported along the extension isomorphisms. It is stated
once as a definition so that the structure below does not repeat this statement in each
of its generated declarations. -/
def IsSummandNormalized
    (iso : ∀ F H : ChainComplex (NisModules (k := k)) ℕ,
      cochainTensor N (F.extend negativeEmbedding) (H.extend negativeEmbedding) ≅
        (HomologicalComplex.mapBifunctor F H N.functor
          (ComplexShape.down ℕ)).extend negativeEmbedding) : Prop :=
  ∀ (F H : ChainComplex (NisModules (k := k)) ℕ) (a b : ℕ),
    HomologicalComplex.ιMapBifunctor (F.extend negativeEmbedding)
      (H.extend negativeEmbedding) N.functor (ComplexShape.up ℤ)
      (-(a : ℤ)) (-(b : ℤ)) (-((a + b : ℕ) : ℤ)) (by dsimp; omega) ≫
      (iso F H).hom.f (-((a + b : ℕ) : ℤ)) ≫
      ((HomologicalComplex.mapBifunctor F H N.functor
        (ComplexShape.down ℕ)).extendXIso negativeEmbedding (zero_sub _)).hom =
    ((N.functor.map (F.extendXIso negativeEmbedding (zero_sub _)).hom).app
      ((H.extend negativeEmbedding).X (-(b : ℤ))) ≫
      (N.functor.obj (F.X a)).map
        (H.extendXIso negativeEmbedding (zero_sub _)).hom) ≫
      HomologicalComplex.ιMapBifunctor F H N.functor
        (ComplexShape.down ℕ) a b (a + b) rfl

/-- Tensor and negative-index extension agree on every native summand.
The normalization rules out changing a shuffle by an arbitrary scalar. -/
structure NegativeTensorComparison where
  iso : ∀ F H : ChainComplex (NisModules (k := k)) ℕ,
    cochainTensor N (F.extend negativeEmbedding) (H.extend negativeEmbedding) ≅
      (HomologicalComplex.mapBifunctor F H N.functor
        (ComplexShape.down ℕ)).extend negativeEmbedding
  summand : IsSummandNormalized N iso

variable {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R))

/-- The actual unshifted singular chain complex of the reduced torus. -/
abbrev torusChains (q : ℕ) :=
  (AlgebraicTopology.alternatingFaceMapComplex (NisModules (k := k))).obj
    (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T q)

/-- The completed source expression for nonnegative Tate multiplication. -/
def naturalMultiplication {J : TorusConcatenation A}
    (M : SingularCycleProduct (S := S) N T J) (Z : EilenbergZilberModel N)
    (V : NegativeTensorComparison N) (q r : ℕ) :
    cochainTensor N
      (naturalTateComplex (D := D) (G := G) (P := P) (E := E)
        (C := C) (A := A) (R := R) (S := S) T q)
      (naturalTateComplex (D := D) (G := G) (P := P) (E := E)
        (C := C) (A := A) (R := R) (S := S) T r) ⟶
      naturalTateComplex (D := D) (G := G) (P := P) (E := E)
        (C := C) (A := A) (R := R) (S := S) T (q + r) :=
  (tensorShiftIso N ((torusChains (S := S) T q).extend negativeEmbedding)
    ((torusChains (S := S) T r).extend negativeEmbedding) (-(q : ℤ)) (-(r : ℤ))).hom ≫
    eqToHom (congrArg (fun a : ℤ =>
      (cochainTensor N ((torusChains (S := S) T q).extend negativeEmbedding)
        ((torusChains (S := S) T r).extend negativeEmbedding))⟦a⟧)
      (show -(q : ℤ) + -(r : ℤ) = -((q + r : ℕ) : ℤ) from by omega)) ≫
    ((V.iso (torusChains (S := S) T q)
      (torusChains (S := S) T r)).hom)⟦-((q + r : ℕ) : ℤ)⟧' ≫
    ((negativeEmbedding.extendFunctor (NisModules (k := k))).map
      (unshiftedMultiplication (S := S) N T M Z q r))⟦-((q + r : ℕ) : ℤ)⟧'

/-- All integer-weight multiplication, with zero source at a negative weight. -/
def tateMultiplication {J : TorusConcatenation A}
    (M : SingularCycleProduct (S := S) N T J) (Z : EilenbergZilberModel N)
    (V : NegativeTensorComparison N) (q r : ℤ) :
    cochainTensor N
      (tateComplex (D := D) (G := G) (P := P) (E := E)
        (C := C) (A := A) (R := R) (S := S) T q)
      (tateComplex (D := D) (G := G) (P := P) (E := E)
        (C := C) (A := A) (R := R) (S := S) T r) ⟶
      tateComplex (D := D) (G := G) (P := P) (E := E)
        (C := C) (A := A) (R := R) (S := S) T (q + r) := by
  by_cases hq : 0 ≤ q
  · by_cases hr : 0 ≤ r
    · simpa only [tateComplex, ite_eq_left hq, ite_eq_left hr,
        ite_eq_left (add_nonneg hq hr), Int.toNat_add hq hr] using
          naturalMultiplication N T M Z V q.toNat r.toNat
    · exact 0
  · exact 0

variable
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)

/-- A local Tate section and an actual constant coefficient enter the
specified coefficient complex through both published tensor isomorphisms. -/
def coefficientElement (V : ModuleCat.{1} ℤ) (q n : ℤ)
    (U : (SmoothScheme k)ᵒᵖ)
    (x : ((tateComplex (D := D) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R) (S := S) T q).X n).obj.obj U) (v : V) :
    (((B.weightFunctor q).obj V).X n).obj.obj U :=
  ((B.termIso V q n).inv.hom.app U)
    (tensorElement N _ _ U x (constantElement V U v))

/-- The pure-tensor normalization of coefficient multiplication maps: on the tensor of two
local coefficient elements, the map is Tate multiplication of the local sections tensored
with the specified bilinear coefficient map. -/
def IsPureTensorNormalized {J : TorusConcatenation A}
    (M : SingularCycleProduct (S := S) N T J) (Z : EilenbergZilberModel N)
    (V : NegativeTensorComparison N)
    (map : ∀ (A₁ A₂ A₃ : ModuleCat.{1} ℤ)
      (_μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃) (q r : ℤ),
      cochainTensor N ((B.weightFunctor q).obj A₁)
        ((B.weightFunctor r).obj A₂) ⟶
        (B.weightFunctor (q + r)).obj A₃) : Prop :=
  ∀ (A₁ A₂ A₃ : ModuleCat.{1} ℤ)
    (μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃) (q r i j : ℤ)
    (U : (SmoothScheme k)ᵒᵖ)
    (x : ((tateComplex (D := D) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R) (S := S) T q).X i).obj.obj U)
    (y : ((tateComplex (D := D) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R) (S := S) T r).X j).obj.obj U)
    (a : A₁) (b : A₂),
    (((map A₁ A₂ A₃ μ q r).f (i + j)).hom.app U)
      ((HomologicalComplex.ιMapBifunctor
        ((B.weightFunctor q).obj A₁) ((B.weightFunctor r).obj A₂)
        N.functor (ComplexShape.up ℤ) i j (i + j) rfl).hom.app U
        (tensorElement N _ _ U (coefficientElement N T B A₁ q i U x a)
          (coefficientElement N T B A₂ r j U y b))) =
      coefficientElement N T B A₃ (q + r) (i + j) U
        ((((tateMultiplication N T M Z V q r).f (i + j)).hom.app U)
          ((HomologicalComplex.ιMapBifunctor
            (tateComplex (D := D) (G := G) (P := P) (E := E)
              (C := C) (A := A) (R := R) (S := S) T q)
            (tateComplex (D := D) (G := G) (P := P) (E := E)
              (C := C) (A := A) (R := R) (S := S) T r)
            N.functor (ComplexShape.up ℤ) i j (i + j) rfl).hom.app U
            (tensorElement N _ _ U x y)))
        (μ (TensorProduct.tmul ℤ a b))

/-- Coefficient products for arbitrary abelian coefficients and a
specified bilinear coefficient map, fixed on every pure local tensor. -/
structure CoefficientMultiplicationSystem {J : TorusConcatenation A}
    (M : SingularCycleProduct (S := S) N T J) (Z : EilenbergZilberModel N)
    (V : NegativeTensorComparison N) where
  map : ∀ (A₁ A₂ A₃ : ModuleCat.{1} ℤ)
    (_μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃) (q r : ℤ),
    cochainTensor N ((B.weightFunctor q).obj A₁)
      ((B.weightFunctor r).obj A₂) ⟶
      (B.weightFunctor (q + r)).obj A₃
  pure_tensor : IsPureTensorNormalized N T B M Z V map

/-- K-flatness is tested on the actual tensor total complex with every
acyclic Nisnevich module complex. -/
def IsKFlat (F : CochainComplex (NisModules (k := k)) ℤ) : Prop :=
  ∀ H : CochainComplex (NisModules (k := k)) ℤ,
    (∀ n : ℤ, IsZero (H.homology n)) →
      ∀ n : ℤ, IsZero ((cochainTensor N F H).homology n) ∧
        IsZero ((cochainTensor N H F).homology n)

/-- The actual augmented K-flat replacement, without cup-product laws. -/
structure KFlatResolutionSystem where
  functor : CochainComplex (NisModules (k := k)) ℤ ⥤
    CochainComplex (NisModules (k := k)) ℤ
  augmentation : functor ⟶ 𝟭 _
  quasi : ∀ F, QuasiIso (augmentation.app F)
  flat : ∀ F, IsKFlat N (functor.obj F)

attribute [local instance] HasDerivedCategory.standard

/-- Naturality of a realization of the derived tensor product by K-flat tensor complexes:
it is compatible with the maps induced on both factors by every pair of cochain maps. -/
def IsRealizationNatural (F : KFlatResolutionSystem N)
    (functor : DerivedCategory (NisModules (k := k)) ⥤
      DerivedCategory (NisModules (k := k)) ⥤
        DerivedCategory (NisModules (k := k)))
    (realization : ∀ A₁ A₂ : CochainComplex (NisModules (k := k)) ℤ,
      (functor.obj (DerivedCategory.Q.obj A₁)).obj (DerivedCategory.Q.obj A₂) ≅
        DerivedCategory.Q.obj (cochainTensor N (F.functor.obj A₁) (F.functor.obj A₂))) : Prop :=
  ∀ (A₁ A₂ B₁ B₂ : CochainComplex (NisModules (k := k)) ℤ)
    (a : A₁ ⟶ B₁) (b : A₂ ⟶ B₂),
    (functor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj A₂) ≫
      (functor.obj (DerivedCategory.Q.obj B₁)).map (DerivedCategory.Q.map b) ≫
      (realization B₁ B₂).hom =
    (realization A₁ A₂).hom ≫ DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (F.functor.map a) (F.functor.map b)
        N.functor (ComplexShape.up ℤ))

/-- Derived tensor is realized by those actual K-flat tensor complexes,
and every cochain map is fixed by the replacement functor maps. -/
structure DerivedTensorSource (F : KFlatResolutionSystem N) where
  functor : DerivedCategory (NisModules (k := k)) ⥤
    DerivedCategory (NisModules (k := k)) ⥤
      DerivedCategory (NisModules (k := k))
  realization : ∀ A₁ A₂ : CochainComplex (NisModules (k := k)) ℤ,
    (functor.obj (DerivedCategory.Q.obj A₁)).obj (DerivedCategory.Q.obj A₂) ≅
      DerivedCategory.Q.obj (cochainTensor N (F.functor.obj A₁) (F.functor.obj A₂))
  naturality : IsRealizationNatural N F functor realization

/-- The canonical derived-to-ordinary tensor comparison, using the
specified K-flat augmentation on both factors. -/
def tensorComparison (F : KFlatResolutionSystem N) (D : DerivedTensorSource N F)
    (A₁ A₂ : CochainComplex (NisModules (k := k)) ℤ) :
    (D.functor.obj (DerivedCategory.Q.obj A₁)).obj (DerivedCategory.Q.obj A₂) ⟶
      DerivedCategory.Q.obj (cochainTensor N A₁ A₂) :=
  (D.realization A₁ A₂).hom ≫ DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (F.augmentation.app A₁)
      (F.augmentation.app A₂) N.functor (ComplexShape.up ℤ))

/-- The coefficient multiplication in the derived category is the
canonical tensor comparison followed by the fixed cochain multiplication. -/
def derivedCoefficientMultiplication {J : TorusConcatenation A}
    {M : SingularCycleProduct (S := S) N T J} {Z : EilenbergZilberModel N}
    {V : NegativeTensorComparison N}
    (L : CoefficientMultiplicationSystem N T B M Z V)
    (F : KFlatResolutionSystem N) (D₁ : DerivedTensorSource N F)
    (A₁ A₂ A₃ : ModuleCat.{1} ℤ) (μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃)
    (q r : ℤ) :=
  tensorComparison N F D₁ ((B.weightFunctor q).obj A₁)
    ((B.weightFunctor r).obj A₂) ≫
    DerivedCategory.Q.map (L.map A₁ A₂ A₃ μ q r)

end MathlibExt.AlgebraicGeometry.MotivicTensorOperations
