/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixHeightNaturality
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixCyclic
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCyclicWorkingHeight
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesComparisonWorkingHeightNaturality

/-!
# Stable matrix trace chain maps under universe lifting

For a unital algebra over a commutative rational algebra, the cyclic trace chain map on the
positive tail of the stable matrix Chevalley–Eilenberg complex is determined by its finite
matrix stages.

Universe lifting preserves these trace maps. Their naturality under algebra homomorphisms
holds for coefficient algebras in independent carrier universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [Ring A] [Algebra k A]

/-- The cyclic trace chain map from the positive tail of the stable matrix Chevalley–Eilenberg
complex to the Connes complex. -/
def canonicalStableMatrixCyclicWeibelChainMap :
    ChainComplex.positiveTail (canonicalStableMatrixCEComplex k A) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A :=
  ChainComplex.positiveTailMap (canonicalStableMatrixCEIso k A).inv ≫
    stableMatrixCyclicWeibelChainMap k A

/-- The stable cyclic trace chain map restricts to the trace map on each finite matrix stage. -/
@[reassoc]
theorem canonicalStableMatrixCyclicWeibelChainMap_finite (m : ℕ) :
    ChainComplex.positiveTailMap (canonicalStableMatrixCEInclusion k A m) ≫
        canonicalStableMatrixCyclicWeibelChainMap k A = matrixCyclicWeibelChainMap k A m := by
  let e := canonicalStableMatrixCEIso k A
  let a : matrixComplex k A m ⟶ stableMatrixCEComplex k A :=
    colimit.ι (matrixComplexFunctor k A) m
  have ha : a ≫ e.hom = canonicalStableMatrixCEInclusion k A m :=
    colimitToCanonicalStableMatrixCE_ι k A m
  have h : canonicalStableMatrixCEInclusion k A m ≫ e.inv = a :=
    (congrArg (fun f => f ≫ e.inv) ha.symm).trans
      ((Category.assoc a e.hom e.inv).trans
        ((congrArg (fun f => a ≫ f) e.hom_inv_id).trans (Category.comp_id a)))
  let T := ChainComplex.positiveTailFunctor (ModuleCat.{max u v} k)
  have ht : ChainComplex.positiveTailMap (canonicalStableMatrixCEInclusion k A m) ≫
      ChainComplex.positiveTailMap e.inv = ChainComplex.positiveTailMap a :=
    (T.map_comp _ _).symm.trans (T.congr_map h)
  change ChainComplex.positiveTailMap (canonicalStableMatrixCEInclusion k A m) ≫
    (ChainComplex.positiveTailMap e.inv ≫ stableMatrixCyclicWeibelChainMap k A) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ stableMatrixCyclicWeibelChainMap k A) ht).trans
      (stableMatrixCyclicWeibelChainMap_ι k A m))

/-- The universe-lifted cyclic trace chain map on the positive tail of the stable matrix complex. -/
def canonicalStableMatrixCyclicWeibelChainMapAtHeight :
    ChainComplex.positiveTail (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A :=
  ((ChainComplex.positiveTailMapFunctorIso
    (ModuleCat.uliftFunctor.{max u v z, max u v} k)).app (canonicalStableMatrixCEComplex k A)).hom ≫
      ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (canonicalStableMatrixCyclicWeibelChainMap k A) ≫
          (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom

/-- Every finite trace is retained on the full-height canonical stable CE model. -/
@[reassoc]
theorem canonicalStableMatrixCyclicWeibelChainMapAtHeight_finite (m : ℕ) :
    ChainComplex.positiveTailMap (canonicalStableMatrixCEInclusionAtHeight.{u,v,z} k A m) ≫
        canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,z} k A =
      matrixCyclicWeibelChainMapAtHeight.{u,v,z} k A m := by
  let U := ModuleCat.uliftFunctor.{max u v z, max u v} k
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let eM := (ChainComplex.positiveTailMapFunctorIso U).app (matrixComplex k A m)
  let eC := (ChainComplex.positiveTailMapFunctorIso U).app (canonicalStableMatrixCEComplex k A)
  let a := canonicalStableMatrixCEInclusion k A m
  let t := canonicalStableMatrixCyclicWeibelChainMap k A
  let q := (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom
  have ha : canonicalStableMatrixCEInclusionAtHeight.{u,v,z} k A m = F.map a :=
    nativeLiftedComplexMapAtHeight_eq_uliftMap.{u,v,z} k (Matrix (Fin m) (Fin m) A)
      (canonicalStableMatrixLieInclusion k A m)
  have he : ChainComplex.positiveTailMap (F.map a) ≫ eC.hom =
      eM.hom ≫ F.map (ChainComplex.positiveTailMap a) :=
    (ChainComplex.positiveTailMapFunctorIso U).hom.naturality a
  have ht : F.map (ChainComplex.positiveTailMap a) ≫ F.map t =
      F.map (matrixCyclicWeibelChainMap k A m) :=
    (F.map_comp _ _).symm.trans (F.congr_map (canonicalStableMatrixCyclicWeibelChainMap_finite k A m))
  let c := ChainComplex.positiveTailMap (canonicalStableMatrixCEInclusionAtHeight.{u,v,z} k A m)
  let c' := ChainComplex.positiveTailMap (F.map a)
  have hc : c = c' := congrArg ChainComplex.positiveTailMap ha
  have h₁ : c ≫ eC.hom = eM.hom ≫ F.map (ChainComplex.positiveTailMap a) :=
    (congrArg (fun f => f ≫ eC.hom) hc).trans he
  change c ≫ (eC.hom ≫ F.map t ≫ q) = eM.hom ≫ F.map (matrixCyclicWeibelChainMap k A m) ≫ q
  exact (Category.assoc c eC.hom (F.map t ≫ q)).symm.trans
    ((congrArg (fun f => f ≫ (F.map t ≫ q)) h₁).trans
      ((Category.assoc eM.hom (F.map (ChainComplex.positiveTailMap a)) (F.map t ≫ q)).trans
        (congrArg (fun f => eM.hom ≫ f)
          ((Category.assoc (F.map (ChainComplex.positiveTailMap a)) (F.map t) q).symm.trans
            (congrArg (fun f => f ≫ q) ht)))))

variable {B : Type w} [Ring B] [Algebra k B]

/-- The canonical stable trace chain map preserves independent-universe coefficient maps. -/
private theorem canonicalStableMatrixCyclicWeibelChainMapAtHeight_naturality_proof (f : A →ₐ[k] B) :
    ChainComplex.positiveTailMap (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) ≫
        canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B =
      canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A
          f.toNonUnitalAlgHom := by
  let T : ChainComplex (ModuleCat.{max u v w z} k) ℕ ⥤
      ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    ChainComplex.positiveTailFunctor (ModuleCat.{max u v w z} k)
  let S := T.mapCocone (canonicalStableMatrixCECoconeAtHeight.{u,v,max u v w z} k A)
  have hS : IsColimit S := isColimitOfPreserves T
    (canonicalStableMatrixCEAtHeightIsColimit.{u,v,max u v w z} k A)
  apply hS.hom_ext
  intro m
  let KA : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    canonicalStableMatrixCEComplexAtHeight.{u,v,max u v w z} k A
  let KB : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    canonicalStableMatrixCEComplexAtHeight.{u,w,max u v w z} k B
  let CA : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,max u v w z} k A
  let CB : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,w,max u v w z} k B
  let PA : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    matrixComplexAtHeight.{u,v,max u v w z} k A m
  let PB : ChainComplex (ModuleCat.{max u v w z} k) ℕ :=
    matrixComplexAtHeight.{u,w,max u v w z} k B m
  let a : PA ⟶ KA := canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v w z} k A m
  let b : PB ⟶ KB := canonicalStableMatrixCEInclusionAtHeight.{u,w,max u v w z} k B m
  let c : KA ⟶ KB := canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f
  let t : PA ⟶ PB := matrixCoefficientMapAtHeight.{u,v,w,z} k A f m
  let wA : ChainComplex.positiveTail KA ⟶ CA :=
    canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A
  let wB : ChainComplex.positiveTail KB ⟶ CB :=
    canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B
  let mA : ChainComplex.positiveTail PA ⟶ CA :=
    matrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A m
  let mB : ChainComplex.positiveTail PB ⟶ CB :=
    matrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B m
  let q : CA ⟶ CB := ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A
    f.toNonUnitalAlgHom
  have hc : T.map a ≫ T.map c = T.map t ≫ T.map b :=
    (T.map_comp _ _).symm.trans
      ((T.congr_map (canonicalStableMatrixCoefficientCEMapAtHeight_inclusion.{u,v,w,z} k A f m)).trans
        (T.map_comp _ _))
  have hA : T.map a ≫ wA = mA :=
    canonicalStableMatrixCyclicWeibelChainMapAtHeight_finite.{u,v,max u v w z} k A m
  have hB : T.map b ≫ wB = mB :=
    canonicalStableMatrixCyclicWeibelChainMapAtHeight_finite.{u,w,max u v w z} k B m
  have hm : T.map t ≫ mB = mA ≫ q :=
    matrixCyclicWeibelChainMapAtHeight_naturality.{u,v,w,z} k A f m
  change T.map a ≫ (T.map c ≫ wB) = T.map a ≫ (wA ≫ q)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ wB) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => T.map t ≫ f) hB).trans
          (hm.trans
            ((congrArg (fun f => f ≫ q) hA.symm).trans (Category.assoc _ _ _))))))


/-- The canonical stable trace chain map preserves independent-universe coefficient maps. -/
@[reassoc]
theorem canonicalStableMatrixCyclicWeibelChainMapAtHeight_naturality (f : A →ₐ[k] B) :
    ChainComplex.positiveTailMap (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) ≫
        canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B =
      canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A
          f.toNonUnitalAlgHom :=
  canonicalStableMatrixCyclicWeibelChainMapAtHeight_naturality_proof k A f

end ChevalleyEilenberg
