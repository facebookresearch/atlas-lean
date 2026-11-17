/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectrumHoClosedModels
public import MathlibExt.CategoryTheory.NativeDGNerveModels
public import MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Native spectra of full shifted DG Hom complexes

Every q-th comparison space is the actual zero-pointed good truncation
and Dold--Kan realization of the full complex H[q]. All cochain degrees,
differentials, homogeneous module actions and shifted mapping parameters
are retained. The source tensor is Mathlib's full Koszul tensor-shift
isomorphism followed by the native Alexander--Whitney lax maps.

Point-set spectrum rectification retains these operations by actual
based simplicial homotopies, rather than incorrectly strengthening
Alexander--Whitney coherence to strict symmetric identities. Spectrum
structure maps use the native circle coefficient 1 and these same maps.

DG spectralization uses the same two-opposite convention as the actual
DG coherent nerve. The all-perfect-test end is the full native DG
functor Hom complex over the chosen genuine small perfect source.
No tangent or RHom endpoint is an input.

Sources: HA Construction 1.3.1.13; Keller, Deriving DG categories §§1--3;
HSS Sections 2.2/3.1; Schwede--Shipley, Equivalences of monoidal model
categories. Native Tau/Mathlib pins and Apache notices remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeShiftedDGSpectrumModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource MathlibExt.DGSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels QuasicategoricalModels
open MathlibExt.CategoryTheory.DGModelContracts MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
open NativeDerivedSpectrumModels StableSpectraInfinitySource NativeSpectrumHoClosedModels
open NativeSpectrumFunctionEvaluation NativeSZeroFoldModels NativeMotivePresheafSources
open StableInfinityMappingSpaces
open scoped Simplicial MonoidalClosed

variable (k : Type) [CommRing k]

/-- The basepoint is the original zero in the native simplicial module, not an adjoined point. -/
def cochainZeroPoint (K : Cochains k) :
    (Δ[0] : SSet.{0}) ⟶ simplicialModule K ⋙ forget (ModuleCat k) where
  app n := ↾fun _ => 0
  naturality n m f := by
    ext x
    exact (map_zero ((simplicialModule K).map f).hom).symm

def pointedCochain (K : Cochains k) : PointedSSet.{0} := Under.mk (cochainZeroPoint k K)

theorem cochainZeroPoint_natural {K L : Cochains k} (f : K ⟶ L) :
    cochainZeroPoint k K ≫ Functor.whiskerRight
      (Idempotents.DoldKan.Γ.map ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map f))
      (forget (ModuleCat k)) = cochainZeroPoint k L := by
  ext n x
  change ((Idempotents.DoldKan.Γ.map
    ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map f)).app n).hom 0 = 0
  exact map_zero _

def pointedCochainFunctor : Cochains k ⥤ PointedSSet.{0} where
  obj K := pointedCochain k K
  map f := Under.homMk (Functor.whiskerRight
    (Idempotents.DoldKan.Γ.map ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map f))
      (forget (ModuleCat k))) (cochainZeroPoint_natural k f)
  map_id K := by
    ext n x
    change (((Idempotents.DoldKan.Γ.map
      ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map (𝟙 K))).app n).hom x) = x
    rw [(ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map_id,
      Idempotents.DoldKan.Γ.map_id]
    rfl
  map_comp f g := by
    ext n x
    change (((Idempotents.DoldKan.Γ.map
      ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map (f ≫ g))).app n).hom x) =
      (((Idempotents.DoldKan.Γ.map ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map g)).app n).hom
        (((Idempotents.DoldKan.Γ.map ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map f)).app n).hom x))
    rw [(ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat k)).map_comp,
      Idempotents.DoldKan.Γ.map_comp]
    rfl

def pointedCochainUnderlyingIso (K : Cochains k) : (pointedCochain k K).right ≅ (cochainToSSet k).obj K :=
  eqToIso (cochainToSSet_obj k K).symm

/-- ALL spectrum levels use the full shifted complex before good truncation. -/
def pointedShiftedFunctor (q : ℤ) : Cochains k ⥤ PointedSSet.{0} :=
  shiftFunctor (Cochains k) q ⋙ pointedCochainFunctor k

/-- The actual two native tensor-shift comparisons retain their Koszul signs. -/
def cochainTensorShiftIso (K L : Cochains k) (p q : ℤ) :
    K⟦p⟧ ⊗ L⟦q⟧ ≅ (K ⊗ L)⟦p + q⟧ :=
  CochainComplex.mapBifunctorShift₁Iso K (L⟦q⟧) (curriedTensor (ModuleCat k)) p ≪≫
    (shiftFunctor (Cochains k) p).mapIso
      (CochainComplex.mapBifunctorShift₂Iso K L (curriedTensor (ModuleCat k)) q) ≪≫
    ((shiftFunctorAdd' (Cochains k) q p (p + q) (by omega)).app (K ⊗ L)).symm

def mixedCochainTensorDomain (p q : ℤ) : Cochains k × Cochains k ⥤ PointedSSet.{0} where
  obj KL := (pointedShiftedFunctor k p).obj KL.1 ⊗ (pointedShiftedFunctor k q).obj KL.2
  map f := (pointedShiftedFunctor k p).map f.1 ⊗ₘ (pointedShiftedFunctor k q).map f.2
  map_id KL := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]

def mixedCochainTensorTarget (p q : ℤ) : Cochains k × Cochains k ⥤ PointedSSet.{0} :=
  _root_.CategoryTheory.MonoidalCategory.tensor (Cochains k) ⋙ pointedShiftedFunctor k (p + q)

/-- The based tensor map is exactly native AW/good truncation and the full Koszul shift isomorphism. -/
structure DoldKanTensorSource (p q : ℤ) where
  comparison : mixedCochainTensorDomain k p q ⟶ mixedCochainTensorTarget k p q
  generators : ∀ (K L : Cochains k) (n : SimplexCategoryᵒᵖ)
    (x : ((pointedShiftedFunctor k p).obj K).right.obj n)
    (y : ((pointedShiftedFunctor k q).obj L).right.obj n),
    (comparison.app (K, L)).right.app n (PointedSSet.smashMk x y) =
      (((cochainToSSet k).map (cochainTensorShiftIso k K L p q).hom) ≫
        (pointedCochainUnderlyingIso k ((K ⊗ L)⟦p + q⟧)).inv).app n
        ((Functor.LaxMonoidal.μ (cochainToSSet k) (K⟦p⟧) (L⟦q⟧)).app n
          (((pointedCochainUnderlyingIso k (K⟦p⟧)).hom.app n x),
            ((pointedCochainUnderlyingIso k (L⟦q⟧)).hom.app n y)))

/-- Actual based homotopies retain every native source and parameter simplex. -/
structure PointedMapHomotopy {X Y : PointedSSet.{0}} (f g : X ⟶ Y) where
  map : X.right ⊗ (Δ[1] : SSet.{0}) ⟶ Y.right
  source : (MonoidalClosed.curry map).app (op ⦋0⦌)
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)) = mappingZero _ _ f.right
  target : (MonoidalClosed.curry map).app (op ⦋0⦌)
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) = mappingZero _ _ g.right
  basepoint : ∀ (n : SimplexCategoryᵒᵖ) (t : (Δ[1] : SSet.{0}).obj n),
    map.app n (X.point n, t) = Y.point n

def circleGenerator : PointedSSet.circle.right _⦋1⦌ :=
  MathlibExt.SpectraSource.SSet.S1.quotient.app (op ⦋1⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))

def unitShiftCoefficient : ((𝟙_ (Cochains k))⟦(1 : ℤ)⟧).X (-1) :=
  (((𝟙_ (Cochains k)).shiftFunctorObjXIso (1 : ℤ) (-1) 0 (by omega)).inv).hom
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat k))).inv (1 : k))

def cochainSimplexToModule (K : Cochains k) (n : SimplexCategoryᵒᵖ)
    (x : ((cochainToSSet k).obj K).obj n) : (simplicialModule K).obj n :=
  (eqToHom (cochainToSSet_obj k K)).app n x

/-- The suspension parameter is the original circle and native normalized coefficient 1. -/
structure CochainCircleSource where
  map : PointedSSet.circle ⟶ (pointedShiftedFunctor k (1 : ℤ)).obj (𝟙_ (Cochains k))
  coefficient : (coefficientMap ((𝟙_ (Cochains k))⟦(1 : ℤ)⟧) 1).hom
    (map.right.app (op ⦋1⦌) circleGenerator) =
    unitShiftCoefficient k

def cochainSuspensionMap (D : ∀ p q : ℤ, DoldKanTensorSource k p q) (C : CochainCircleSource k)
    (K : Cochains k) (q : ℕ) :
    PointedSSet.circle ⊗ (pointedShiftedFunctor k (q : ℤ)).obj K ⟶
      (pointedShiftedFunctor k (1 + (q : ℤ))).obj K :=
  C.map ▷ _ ≫ (D 1 q).comparison.app (𝟙_ (Cochains k), K) ≫
    (pointedShiftedFunctor k (1 + (q : ℤ))).map (λ_ K).hom

def shiftedUnitVertex : ((pointedShiftedFunctor k (0 : ℤ)).obj (𝟙_ (Cochains k))).right _⦋0⦌ :=
  ((cochainToSSet k).map ((shiftFunctorZero (Cochains k) ℤ).inv.app (𝟙_ (Cochains k)))).app (op ⦋0⦌)
    ((SSet.unitHomEquiv _).toFun (Functor.LaxMonoidal.ε (cochainToSSet k))) |>
    (pointedCochainUnderlyingIso k ((𝟙_ (Cochains k))⟦(0 : ℤ)⟧)).inv.app (op ⦋0⦌)

/-- The point-set source functor is normalized in every level, every mixed shift
and every sphere structure map; coherence is retained by actual based homotopies. -/
structure CochainSpectrumSource where
  functor : Cochains k ⥤ SymmetricSpectrum
  lax : functor.LaxMonoidal
  comparison : ∀ q : ℕ, pointedShiftedFunctor k (q : ℤ) ⟶ functor ⋙ SymmetricSpectrum.evaluation q
  weak : ∀ (K : Cochains k) (q : ℕ), WeakEquivalence ((comparison q).app K).right
  dktensor : ∀ p q : ℤ, DoldKanTensorSource k p q
  circle : CochainCircleSource k
  unit : letI := lax
    PointedMapHomotopy
      (sphereLevelZeroIso.inv ≫ (SymmetricSpectrum.evaluation 0).map (Functor.LaxMonoidal.ε functor))
      (pointedUnitMap ((pointedShiftedFunctor k 0).obj (𝟙_ (Cochains k))) (shiftedUnitVertex k) ≫
        (comparison 0).app (𝟙_ (Cochains k)))
  tensor : letI := lax
    ∀ (K L : Cochains k) (p q : ℕ), PointedMapHomotopy
      (((comparison p).app K ⊗ₘ (comparison q).app L) ≫
        levelTensorInsertion (functor.obj K) (functor.obj L) p q ≫
        (SymmetricSpectrum.evaluation (p + q)).map (Functor.LaxMonoidal.μ functor K L))
      ((dktensor p q).comparison.app (K, L) ≫
        eqToHom (congrArg (fun i : ℤ => (pointedShiftedFunctor k i).obj (K ⊗ L))
          (by omega : (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ))) ≫ (comparison (p + q)).app (K ⊗ L))
  suspension : ∀ (K : Cochains k) (q : ℕ), PointedMapHomotopy
    (PointedSSet.circle ◁ (comparison q).app K ≫ (functor.obj K).smashPowStructureMap q)
    (cochainSuspensionMap k dktensor circle K q ≫
      eqToHom (congrArg (fun i : ℤ => (pointedShiftedFunctor k i).obj K)
        (by omega : 1 + (q : ℤ) = ((1 + q : ℕ) : ℤ))) ≫ (comparison (1 + q)).app K)
  tensor_natural : letI := lax
    ∀ (K K' L L' : Cochains k) (f : K ⟶ K') (g : L ⟶ L') (p q : ℕ)
      (n : SimplexCategoryᵒᵖ)
      (x : (((pointedShiftedFunctor k p).obj K) ⊗ ((pointedShiftedFunctor k q).obj L)).right.obj n)
      (t : (Δ[1] : SSet.{0}).obj n),
    (tensor K' L' p q).map.app n
      ((((pointedShiftedFunctor k p).map f ⊗ₘ (pointedShiftedFunctor k q).map g).right.app n x), t) =
      ((SymmetricSpectrum.evaluation (p + q)).map (functor.map (f ⊗ₘ g))).right.app n
        ((tensor K L p q).map.app n (x, t))
  suspension_natural : ∀ (K L : Cochains k) (f : K ⟶ L) (q : ℕ) (n : SimplexCategoryᵒᵖ)
    (x : (PointedSSet.circle ⊗ (pointedShiftedFunctor k q).obj K).right.obj n)
    (t : (Δ[1] : SSet.{0}).obj n),
    (suspension L q).map.app n (((PointedSSet.circle ◁ (pointedShiftedFunctor k q).map f).right.app n x), t) =
      ((SymmetricSpectrum.evaluation (1 + q)).map (functor.map f)).right.app n ((suspension K q).map.app n (x, t))

variable {k}

/-- Every Hom spectrum is the native image of the entire original DG Hom complex. -/
def dgHomSpectrum (T : CochainSpectrumSource k) {C : Type} [DGCategory k C] (X Y : C) : SymmetricSpectrum :=
  T.functor.obj (dgHomComplex k X Y)

/-- The same two opposites as the actual DG nerve retain the original DG/Koszul/AW order. -/
def DGSpectralCategory (T : CochainSpectrumSource k) (C : Type) [DGCategory k C] : Type :=
  letI := T.lax
  (TransportEnrichment T.functor Cᵒᵖ)ᵒᵖ

@[instance_reducible]
def DGSpectralCategory.enrichment (T : CochainSpectrumSource k) (C : Type) [DGCategory k C] :
    EnrichedCategory SymmetricSpectrum (DGSpectralCategory T C) :=
  letI := T.lax
  inferInstanceAs (EnrichedCategory SymmetricSpectrum (TransportEnrichment T.functor Cᵒᵖ)ᵒᵖ)

/-- ALL perfect test objects and their full right-module DG action are retained. -/
def allPerfectTestHomSpectrum (T : CochainSpectrumSource k) {C : DGCat k}
    (P : SmallPerfectModel C) (X Y : P.category) : SymmetricSpectrum :=
  T.functor.obj (dgHomComplex k ((dgYoneda k).obj X) ((dgYoneda k).obj Y))

def allPerfectTestYonedaSpectrumMap (T : CochainSpectrumSource k) {C : DGCat k}
    (P : SmallPerfectModel C) (X Y : P.category) :
    dgHomSpectrum T X Y ⟶ allPerfectTestHomSpectrum T P X Y :=
  T.functor.map ((dgYoneda k).map X Y)

/-- Full DG Yoneda is an actual isomorphism on complexes, hence on the entire native spectrum. -/
theorem allPerfectTestYonedaSpectrumMap_isIso (T : CochainSpectrumSource k) {C : DGCat k}
    (P : SmallPerfectModel C) (X Y : P.category) : IsIso (allPerfectTestYonedaSpectrumMap T P X Y) := by
  have : IsIso ((dgYoneda k).map X Y) := isIso_map_dgYoneda k X Y
  unfold allPerfectTestYonedaSpectrumMap
  infer_instance

def shiftedDGVertex {C : Type} [DGCategory k C] (X : C) (q : ℤ) :
    (dgNerve (k := k) (DGShiftClosure C)) _⦋0⦌ :=
  (SimplicialNerve.vertexEquiv (DGSimplicial (k := k) (DGShiftClosure C))).symm
    (ForgetEnrichment.of SSet.{0} (DGSimplicialCategory.of k (⟨X, q⟩ : DGShiftClosure C)))

/-- Mapping comparisons retain every shift of the target in the actual full native DG shift closure. -/
structure DGShiftMappingComparison {C : Type} [DGCategory k C] (X Y : C) (q : ℕ) where
  map : ((pointedShiftedFunctor k q).obj (dgHomComplex k X Y)).right ⟶
    mappingSpace (dgNerve (k := k) (DGShiftClosure C)) (shiftedDGVertex X 0) (shiftedDGVertex Y q)
  weak : WeakEquivalence map

end MathlibExt.AlgebraicTopology.NativeShiftedDGSpectrumModels
