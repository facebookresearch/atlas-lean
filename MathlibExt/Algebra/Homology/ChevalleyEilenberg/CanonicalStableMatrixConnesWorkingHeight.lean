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
# The signed stable matrix trace into the Connes quotient

Let k be a commutative ℚ-algebra and A an associative unital k-algebra.
The positive tail of C = C_*(Mat_∞(A)) has degree-n term C_(n+1)
and its inherited CE differential. The finite matrix trace maps give
a chain map W : positiveTail(C) → Cλ(A), where Cλ is the quotient
by the signed cyclic relation 1−t.

On a wedge X₀∧⋯∧X_n represented at a finite matrix stage, W_n is
(−1)^n times the generalized trace of the tail antisymmetrization:
∑_(σ∈S_n) sign(σ) [X₀ ⊗ X_(σ(0)+1) ⊗ ⋯ ⊗ X_(σ(n−1)+1)].
The generalized trace sums entries around all closed matrix-index
cycles. Equivalently, this is full antisymmetrization normalized
by 1/(n+1), together with the degree sign (−1)^n.

At H = max(u,v,z), lifting the CE terms and the Connes cokernel
gives W^H with the same finite-stage values. For a unital algebra
map f : A → B in an independent world w, put H = max(u,v,w,z).
Then Cλ^H(f) ∘ W_A^H = W_B^H ∘ positiveTail(C^H(f)).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ℚ-algebra k and an associative unital
k-algebra A, the finite matrix trace gives
W : positiveTail(C_*(Mat_∞(A))) → Cλ(A).
In degree n, its value is (−1)^n times the trace of the
coefficient-fixed tail antisymmetrization on a finite-stage wedge,
equivalently full antisymmetrization divided by n+1. -/
def canonicalStableMatrixCyclicWeibelChainMap :
    ChainComplex.positiveTail (canonicalStableMatrixCEComplex k A) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A :=
  ChainComplex.positiveTailMap (canonicalStableMatrixCEIso k A).inv ≫
    stableMatrixCyclicWeibelChainMap k A

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and m ≥ 0, the stable chain trace satisfies
W ∘ positiveTail(C_*(i_m)) = W_m.
Here W_m is the signed trace on the finite matrix CE positive tail,
and both sides have target Cλ(A). -/
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

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and H = max(u,v,z), termwise CE lifting and the
Connes cokernel comparison give the chain map
W^H : positiveTail(C_*^H(Mat_∞(A))) → Cλ^H(A).
Its components retain the normalization 1/(n+1) and sign (−1)^n. -/
def canonicalStableMatrixCyclicWeibelChainMapAtHeight :
    ChainComplex.positiveTail (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A :=
  ((ChainComplex.positiveTailMapFunctorIso
    (ModuleCat.uliftFunctor.{max u v z, max u v} k)).app (canonicalStableMatrixCEComplex k A)).hom ≫
      ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (canonicalStableMatrixCyclicWeibelChainMap k A) ≫
          (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A, H = max(u,v,z) and m ≥ 0, the chosen-height maps
satisfy W^H ∘ positiveTail(C_*^H(i_m)) = W_m^H.
The target is the Connes quotient at height H, and the equality
holds in every degree of the positive-tail complexes. -/
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

/-- For a commutative ℚ-algebra k, a unital algebra map
f : A → B and H = max(u,v,w,z), the lifted stable trace maps
satisfy Cλ^H(f) ∘ W_A^H = W_B^H ∘ positiveTail(C^H(f)).
The source is the lifted stable CE positive tail for A and the
target is the lifted Connes complex for B, with independent
algebra carrier worlds. -/
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


/-- For a commutative ℚ-algebra k, a unital algebra map
f : A → B and H = max(u,v,w,z), the signed stable trace satisfies
Cλ^H(f) ∘ W_A^H = W_B^H ∘ positiveTail(C^H(f)).
This square goes from the chosen-height stable CE positive tail
for A to Cλ^H(B), retaining both independent algebra worlds
and the additional height z. -/
@[reassoc]
theorem canonicalStableMatrixCyclicWeibelChainMapAtHeight_naturality (f : A →ₐ[k] B) :
    ChainComplex.positiveTailMap (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) ≫
        canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B =
      canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A
          f.toNonUnitalAlgHom :=
  canonicalStableMatrixCyclicWeibelChainMapAtHeight_naturality_proof k A f

end ChevalleyEilenberg
