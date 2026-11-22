/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.LanComparison

/-!
# Free objects under sequential-to-symmetric induction

Sequential-to-symmetric induction carries a free enriched sequential spectrum
to the free symmetric spectrum at the corresponding index. The natural
isomorphism is obtained by transporting the left Kan extension comparison.
Its forward and inverse maps are natural in coefficients and enriched source
arrows, and the comparison is compatible with the induction adjunction unit.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.NatIso.SourceSquareTransport
universe uC vC
variable {C : Type uC} [Category.{vC} C]

/-- Two complete original map squares paste using the full original intermediate and target arrows. -/
private theorem paste_squares {A B D E H I : C}
    (p : A ⟶ B) (q : B ⟶ D) (r : D ⟶ E)
    (a : A ⟶ H) (b : H ⟶ I) (c : I ⟶ E) (t : H ⟶ D)
    (h₁ : p ≫ q = a ≫ t) (h₂ : t ≫ r = b ≫ c) :
    p ≫ q ≫ r = a ≫ b ≫ c :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ r) h₁).trans
      ((Category.assoc _ _ _).trans (congrArg (fun f => a ≫ f) h₂)))

end CategoryTheory.NatIso.SourceSquareTransport

namespace CategoryTheory.NatIso.SourceSquareTransport
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {V L : C ⥤ D}

/-- The full original forward natural comparison transports every complete source square. -/
private theorem hom_source_square (i : V ≅ L) {X Y : C} {P Q : D} (f : X ⟶ Y)
    (p : L.obj X ⟶ P) (q : L.obj Y ⟶ Q) (g : P ⟶ Q)
    (h : L.map f ≫ q = p ≫ g) :
    V.map f ≫ (i.hom.app Y ≫ q) = (i.hom.app X ≫ p) ≫ g :=
  (paste_squares (V.map f) (i.hom.app Y) q (i.hom.app X) p g
    (L.map f) (i.hom.naturality f) h).trans (Category.assoc _ _ _).symm

/-- The full original inverse natural comparison transports every complete inverse source square. -/
private theorem inv_source_square (i : V ≅ L) {X Y : C} {P Q : D} (f : X ⟶ Y)
    (p : P ⟶ L.obj X) (q : Q ⟶ L.obj Y) (g : P ⟶ Q)
    (h : g ≫ q = p ≫ L.map f) :
    g ≫ (q ≫ i.inv.app Y) = (p ≫ i.inv.app X) ≫ V.map f :=
  (paste_squares g q (i.inv.app Y) p (i.inv.app X) (V.map f)
    (L.map f) h (i.inv.naturality f)).trans (Category.assoc _ _ _).symm

end CategoryTheory.NatIso.SourceSquareTransport

namespace CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparison.Transport
open CategoryTheory.NatIso.SourceSquareTransport
universe uV vV uA uB
open EnrichedFunctorCat
variable {Bv : Type uV} [Category.{vV} Bv] [MonoidalCategory Bv]
  [BraidedCategory Bv] [MonoidalClosed Bv]
  {A : Type uA} [EnrichedCategory Bv A]
  {B : Type uB} [EnrichedCategory Bv B]
  (j : EnrichedFunctor Bv A B)

/-- Transport the entire original free family, its two map functions and every source square. -/
private def transportData (D : LeftKanFreeComparison.FullMapFamilies.Data j)
    (T : EnrichedFunctorCat Bv A ⥤ EnrichedFunctorCat Bv B) (i : T ≅ D.originalLan) :
    LeftKanFreeComparison.FullMapFamilies.Data j where
  originalLan := T
  comparison a := (isoWhiskerLeft (Free.functor a) i) ≪≫ D.comparison a
  homMap a X := i.hom.app (Free.object a X) ≫ D.homMap a X
  invMap a X := D.invMap a X ≫ i.inv.app (Free.object a X)
  homEquation a X := congrArg (fun q => i.hom.app (Free.object a X) ≫ q) (D.homEquation a X)
  invEquation a X := congrArg (fun q => q ≫ i.inv.app (Free.object a X)) (D.invEquation a X)
  homSource e X := hom_source_square i (Free.sourceMap e X)
    (D.homMap _ X) (D.homMap _ X) (Free.sourceMap (e ≫ j.map _ _) X) (D.homSource e X)
  invSource e X := inv_source_square i (Free.sourceMap e X)
    (D.invMap _ X) (D.invMap _ X) (Free.sourceMap (e ≫ j.map _ _) X) (D.invSource e X)

/-- The transported complete free comparison retains the entire original composite NatIso value. -/
private theorem transportData_comparison (D : LeftKanFreeComparison.FullMapFamilies.Data j)
    (T : EnrichedFunctorCat Bv A ⥤ EnrichedFunctorCat Bv B) (i : T ≅ D.originalLan) (a : A) :
    (transportData j D T i).comparison a = (isoWhiskerLeft (Free.functor a) i) ≪≫ D.comparison a := rfl

/-- The entire transported comparison family is the same original complete composite family. -/
private theorem transportData_comparison_family (D : LeftKanFreeComparison.FullMapFamilies.Data j)
    (T : EnrichedFunctorCat Bv A ⥤ EnrichedFunctorCat Bv B) (i : T ≅ D.originalLan) :
    (fun a => (transportData j D T i).comparison a) =
      (fun a => (isoWhiskerLeft (Free.functor a) i) ≪≫ D.comparison a) := rfl

/-- The complete transported forward family is explicitly typed at the original free-functor objects. -/
private theorem transportData_hom_app (D : LeftKanFreeComparison.FullMapFamilies.Data j)
    (T : EnrichedFunctorCat Bv A ⥤ EnrichedFunctorCat Bv B) (i : T ≅ D.originalLan)
    (a : A) (X : Bv) :
    ((transportData j D T i).comparison a).hom.app X =
      i.hom.app ((Free.functor a).obj X) ≫ D.homMap a X :=
  (transportData j D T i).homEquation a X

/-- The complete transported inverse family is explicitly typed at the original free-functor objects. -/
private theorem transportData_inv_app (D : LeftKanFreeComparison.FullMapFamilies.Data j)
    (T : EnrichedFunctorCat Bv A ⥤ EnrichedFunctorCat Bv B) (i : T ≅ D.originalLan)
    (a : A) (X : Bv) :
    ((transportData j D T i).comparison a).inv.app X =
      D.invMap a X ≫ i.inv.app ((Free.functor a).obj X) :=
  (transportData j D T i).invEquation a X

/-- Every complete forward comparison retains all original source arrows and coefficients. -/
private theorem transportData_hom_source (D : LeftKanFreeComparison.FullMapFamilies.Data j)
    (T : EnrichedFunctorCat Bv A ⥤ EnrichedFunctorCat Bv B) (i : T ≅ D.originalLan)
    {a a' : A} (e : 𝟙_ Bv ⟶ (a ⟶[Bv] a')) (X : Bv) :
    T.map (Free.sourceMap e X) ≫ ((transportData j D T i).comparison a).hom.app X =
      ((transportData j D T i).comparison a').hom.app X ≫ Free.sourceMap (e ≫ j.map a a') X := by
  have h := (transportData j D T i).homSource e X
  have hA := (transportData j D T i).homEquation a X
  have hB := (transportData j D T i).homEquation a' X
  exact (congrArg (fun q => T.map (Free.sourceMap e X) ≫ q) hA).trans
    (h.trans (congrArg (fun q => q ≫ Free.sourceMap (e ≫ j.map a a') X) hB.symm))

/-- Every complete inverse comparison retains all original source arrows and coefficients. -/
private theorem transportData_inv_source (D : LeftKanFreeComparison.FullMapFamilies.Data j)
    (T : EnrichedFunctorCat Bv A ⥤ EnrichedFunctorCat Bv B) (i : T ≅ D.originalLan)
    {a a' : A} (e : 𝟙_ Bv ⟶ (a ⟶[Bv] a')) (X : Bv) :
    Free.sourceMap (e ≫ j.map a a') X ≫ ((transportData j D T i).comparison a).inv.app X =
      ((transportData j D T i).comparison a').inv.app X ≫ T.map (Free.sourceMap e X) := by
  have h := (transportData j D T i).invSource e X
  have hA := (transportData j D T i).invEquation a X
  have hB := (transportData j D T i).invEquation a' X
  exact (congrArg (fun q => Free.sourceMap (e ≫ j.map a a') X ≫ q) hA).trans
    (h.trans (congrArg (fun q => q ≫ T.map (Free.sourceMap e X)) hB.symm))

end CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparison.Transport


namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
open CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparison.Transport
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The complete actual induction transport retains every native free index, coefficient and source map. -/
def nativeFreeComparisonData : EnrichedFunctorCat.LeftKanFreeComparison.FullMapFamilies.Data
    sequentialSymmetricOperatorIndexFunctor.{u, v} :=
  transportData sequentialSymmetricOperatorIndexFunctor.{u, v}
    NativeIndexKanComposition.sequentialSymmetricFreeData.{u, v} V.{u, v}
    nativeLanComparison.{u, v}

/-- Every original balanced-induction free functor retains the full native index and every original coefficient. -/
def nativeFreeComparison (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    EnrichedFunctorCat.Free.functor n ⋙ V.{u, v} ≅
      EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj n) :=
  nativeFreeComparisonData.comparison n

/-- The entire actual free NatIso retains both original composite maps and all original
inverse and naturality fields. -/
theorem nativeFreeComparison_eq (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    nativeFreeComparison n =
      (isoWhiskerLeft (EnrichedFunctorCat.Free.functor n) nativeLanComparison.{u, v}) ≪≫
        NativeIndexKanComposition.sequentialSymmetricFreeData.{u, v}.comparison n :=
  transportData_comparison sequentialSymmetricOperatorIndexFunctor.{u, v}
    NativeIndexKanComposition.sequentialSymmetricFreeData.{u, v} V.{u, v}
    nativeLanComparison.{u, v} n

/-- Every original complete free comparison value is retained in the entire original index family. -/
theorem nativeFreeComparison_family_eq :
    (fun n : PointedCGWH.Spectra.Sequential.Index.{u, v} => nativeFreeComparison n) =
      (fun n => (isoWhiskerLeft (EnrichedFunctorCat.Free.functor n) nativeLanComparison.{u, v}) ≪≫
        NativeIndexKanComposition.sequentialSymmetricFreeData.{u, v}.comparison n) :=
  transportData_comparison_family sequentialSymmetricOperatorIndexFunctor.{u, v}
    NativeIndexKanComposition.sequentialSymmetricFreeData.{u, v} V.{u, v}
    nativeLanComparison.{u, v}

/-- The whole original free forward map is the actual induction comparison and native coend/free map. -/
theorem nativeFreeComparison_hom_app (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    (K : PointedCGWH.{u, v}) :
    (nativeFreeComparison n).hom.app K =
      nativeLanComparison.hom.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
        NativeIndexKanComposition.sequentialSymmetricFreeData.homMap n K :=
  (congrArg (fun q : EnrichedFunctorCat.Free.functor n ⋙ V.{u, v} ≅
      EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj n) =>
    q.hom.app K) (nativeFreeComparison_eq n)).trans
      (congrArg (fun q => nativeLanComparison.hom.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫ q)
        (NativeIndexKanComposition.sequentialSymmetricFreeData.homEquation n K))

/-- The whole original free inverse map is the actual native inverse coend/free map and inverse induction comparison. -/
theorem nativeFreeComparison_inv_app (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    (K : PointedCGWH.{u, v}) :
    (nativeFreeComparison n).inv.app K =
      NativeIndexKanComposition.sequentialSymmetricFreeData.invMap n K ≫
        nativeLanComparison.inv.app ((EnrichedFunctorCat.Free.functor n).obj K) :=
  (congrArg (fun q : EnrichedFunctorCat.Free.functor n ⋙ V.{u, v} ≅
      EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj n) =>
    q.inv.app K) (nativeFreeComparison_eq n)).trans
      (congrArg (fun q => q ≫ nativeLanComparison.inv.app ((EnrichedFunctorCat.Free.functor n).obj K))
        (NativeIndexKanComposition.sequentialSymmetricFreeData.invEquation n K))

/-- Every original coefficient map preserves the entire forward balanced-induction/free comparison. -/
theorem nativeFreeComparison_hom_naturality (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    {K L : PointedCGWH.{u, v}} (f : K ⟶ L) :
    (EnrichedFunctorCat.Free.functor n ⋙ V).map f ≫ (nativeFreeComparison n).hom.app L =
      (nativeFreeComparison n).hom.app K ≫
        (EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).map f :=
  (nativeFreeComparison n).hom.naturality f

/-- Every original coefficient map preserves the entire inverse balanced-induction/free comparison. -/
theorem nativeFreeComparison_inv_naturality (n : PointedCGWH.Spectra.Sequential.Index.{u, v})
    {K L : PointedCGWH.{u, v}} (f : K ⟶ L) :
    (EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).map f ≫
      (nativeFreeComparison n).inv.app L =
    (nativeFreeComparison n).inv.app K ≫ (EnrichedFunctorCat.Free.functor n ⋙ V).map f :=
  (nativeFreeComparison n).inv.naturality f

/-- Every original enriched source arrow preserves the full forward free comparison on every coefficient. -/
theorem nativeFreeComparison_hom_source {a a' : PointedCGWH.Spectra.Sequential.Index.{u, v}}
    (e : 𝟙_ (PointedCGWH.{u, v}) ⟶ (a ⟶[PointedCGWH.{u, v}] a')) (K : PointedCGWH.{u, v}) :
    V.map (EnrichedFunctorCat.Free.sourceMap
      (V := PointedCGWH.{u, v}) (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
      (a := a) (a' := a') e K) ≫ (nativeFreeComparison a).hom.app K =
      (nativeFreeComparison a').hom.app K ≫ EnrichedFunctorCat.Free.sourceMap
        (V := PointedCGWH.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        (a := sequentialSymmetricOperatorIndexFunctor.{u, v}.obj a)
        (a' := sequentialSymmetricOperatorIndexFunctor.{u, v}.obj a')
        (e ≫ sequentialSymmetricOperatorIndexFunctor.map a a') K := by
  exact transportData_hom_source sequentialSymmetricOperatorIndexFunctor.{u, v}
    NativeIndexKanComposition.sequentialSymmetricFreeData.{u, v} V.{u, v}
    nativeLanComparison.{u, v} e K

/-- Every original enriched source arrow preserves the full inverse free comparison on every coefficient. -/
theorem nativeFreeComparison_inv_source {a a' : PointedCGWH.Spectra.Sequential.Index.{u, v}}
    (e : 𝟙_ (PointedCGWH.{u, v}) ⟶ (a ⟶[PointedCGWH.{u, v}] a')) (K : PointedCGWH.{u, v}) :
    EnrichedFunctorCat.Free.sourceMap
      (V := PointedCGWH.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      (a := sequentialSymmetricOperatorIndexFunctor.{u, v}.obj a)
      (a' := sequentialSymmetricOperatorIndexFunctor.{u, v}.obj a')
      (e ≫ sequentialSymmetricOperatorIndexFunctor.map a a') K ≫
      (nativeFreeComparison a).inv.app K =
      (nativeFreeComparison a').inv.app K ≫ V.map (EnrichedFunctorCat.Free.sourceMap
        (V := PointedCGWH.{u, v}) (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
        (a := a) (a' := a') e K) := by
  exact transportData_inv_source sequentialSymmetricOperatorIndexFunctor.{u, v}
    NativeIndexKanComposition.sequentialSymmetricFreeData.{u, v} V.{u, v}
    nativeLanComparison.{u, v} e K

/-- Both whole original free comparison directions recover every original index and coefficient map. -/
theorem nativeFreeComparison_inverses (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    (nativeFreeComparison n).hom.app K ≫ (nativeFreeComparison n).inv.app K =
      𝟙 (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ∧
    (nativeFreeComparison n).inv.app K ≫ (nativeFreeComparison n).hom.app K =
      𝟙 ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K) :=
  ⟨(nativeFreeComparison n).hom_inv_id_app K, (nativeFreeComparison n).inv_hom_id_app K⟩

/-- The full original unit comparison holds at every original free source and arbitrary original coefficient. -/
theorem nativeLanComparison_free_unit (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
      nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map
        (nativeLanComparison.hom.app ((EnrichedFunctorCat.Free.functor n).obj K)) =
      NativeIndexKanComposition.sequentialSymmetricAdjunction.unit.app
        ((EnrichedFunctorCat.Free.functor n).obj K) :=
  nativeLanComparison_unit ((EnrichedFunctorCat.Free.functor n).obj K)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
