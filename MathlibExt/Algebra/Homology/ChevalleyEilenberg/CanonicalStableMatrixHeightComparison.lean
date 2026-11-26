/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraWorkingHeightFunctor
public import MathlibExt.Algebra.Homology.HomologicalComplex.UliftPreorderColimit

/-!
# The finite-to-stable CE colimit isomorphism at a chosen universe height

Let k be a commutative ring, A an associative unital k-algebra and
H = max(u,v,z), where u,v are the ring and algebra worlds and z is
an arbitrary additional height. Lift each term of the finite matrix
CE complexes and of C_*(Mat_∞(A)) to H.

The diagram of lifted finite complexes is naturally isomorphic to the
termwise lift of the finite CE diagram. Its cocone of lifted finite
Lie inclusions is colimiting, so
colim_m C_*^H(Mat_m(A)) ≅ C_*^H(Mat_∞(A)).
The forward map restricts to the lifted CE inclusion at every finite
stage. The construction preserves the whole directed diagram and all
CE degrees.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), termwise lifting of m ↦ C_*(Mat_m(A))
is naturally isomorphic to m ↦ C_*^H(Mat_m(A)).
The transition maps on both sides are the lifted exterior powers
of top-left zero extension. -/
def matrixComplexFunctorULiftIso :
    matrixComplexFunctor k A ⋙
        (ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      matrixComplexFunctorAtHeight.{u,v,max u v z} k A :=
  NatIso.ofComponents (fun m => Iso.refl _) (by
    intro m n h
    change (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (matrixZeroCornerMap k A (leOfHom h))) ≫ 𝟙 _ =
      𝟙 _ ≫ matrixZeroCornerMapAtHeight.{u,v,max u v z} k A (leOfHom h)
    rw [Category.comp_id, Category.id_comp]
    exact (nativeLiftedComplexMapAtHeight_eq_uliftMap.{u,v,max u v z} k
      (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A (leOfHom h))).symm)

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), the lifted finite Lie inclusions give a cocone
C_*^H(Mat_m(A)) → C_*^H(Mat_∞(A)).
Its degree-n component applies the nth exterior inclusion and then
the chosen carrier lift. -/
def canonicalStableMatrixCECoconeAtHeight :
    Cocone (matrixComplexFunctorAtHeight.{u,v,max u v z} k A) where
  pt := canonicalStableMatrixCEComplexAtHeight.{u,v,max u v z} k A
  ι :=
    { app := canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A
      naturality m n h := by
        change matrixZeroCornerMapAtHeight.{u,v,max u v z} k A (leOfHom h) ≫
            canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A n =
          canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A m ≫ 𝟙 _
        rw [Category.comp_id]
        exact (nativeLiftedComplexMapAtHeight_comp.{u,v,v,v,max u v z} k
          (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A (leOfHom h))
          (canonicalStableMatrixLieInclusion k A n)).trans
            (congrArg (nativeLiftedComplexMapAtHeight.{u,v,v,max u v z} k
              (Matrix (Fin m) (Fin m) A))
              (canonicalStableMatrixLieInclusion_zeroCorner k A (leOfHom h))) }

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), the chosen-height stable CE colimit is
colim_(m∈ℕ) C_*^H(Mat_m(A)) in ChainComplex(ModuleCat^H(k),ℕ).
All finite-stage transitions are lifted zero-extension CE maps. -/
abbrev stableMatrixCEComplexAtHeight : ChainComplex (ModuleCat.{max u v z} k) ℕ :=
  colimit (matrixComplexFunctorAtHeight.{u,v,max u v z} k A)

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), the cocone of lifted finite Lie inclusions
defines colim_m C_*^H(Mat_m(A)) → C_*^H(Mat_∞(A)).
It is characterized by its composites with the finite colimit legs. -/
def colimitToCanonicalStableMatrixCEAtHeight :
    stableMatrixCEComplexAtHeight.{u,v,z} k A ⟶
      canonicalStableMatrixCEComplexAtHeight.{u,v,max u v z} k A :=
  colimit.desc _ (canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A)

/-- For a commutative ring k, an associative unital k-algebra A,
H = max(u,v,z) and m ≥ 0, the chosen-height comparison T^H satisfies
T^H ∘ ι_m^H = C_*^H(i_m).
Here ι_m^H is the finite colimit leg and i_m is the finite stable
matrix Lie inclusion. -/
@[reassoc]
theorem colimitToCanonicalStableMatrixCEAtHeight_ι (m : ℕ) :
    colimit.ι (matrixComplexFunctorAtHeight.{u,v,max u v z} k A) m ≫
        colimitToCanonicalStableMatrixCEAtHeight.{u,v,z} k A =
      canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A m :=
  colimit.ι_desc (canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A) m

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), the cocone of lifted finite CE inclusions
with point C_*^H(Mat_∞(A)) is a colimit cocone.
Termwise universe lifting preserves this directed complex colimit. -/
def canonicalStableMatrixCEAtHeightIsColimit :
    IsColimit (canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A) := by
  let E := (ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ)
  let S := E.mapCocone (canonicalStableMatrixCECocone k A)
  let e := matrixComplexFunctorULiftIso.{u,v,z} k A
  have hS : IsColimit S := isColimitOfPreserves E (canonicalStableMatrixCEIsColimit k A)
  have hp : IsColimit ((Cocone.precompose e.inv).obj S) :=
    (IsColimit.precomposeHomEquiv e.symm S).symm hS
  have w : (Cocone.precompose e.inv).obj S ≅ canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A :=
    Cocone.ext (Iso.refl _) (by
      intro m
      change (𝟙 _ ≫ E.map (canonicalStableMatrixCEInclusion k A m)) ≫ 𝟙 _ =
        canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A m
      rw [Category.id_comp, Category.comp_id]
      exact (nativeLiftedComplexMapAtHeight_eq_uliftMap.{u,v,max u v z} k
        (Matrix (Fin m) (Fin m) A) (canonicalStableMatrixLieInclusion k A m)).symm)
  exact IsColimit.ofIsoColimit hp w

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), there is a chain isomorphism
colim_m C_*^H(Mat_m(A)) ≅ C_*^H(Mat_∞(A)).
Its forward map is the finite-stage inclusion comparison, with
independent ring, algebra and extra-height worlds. -/
def canonicalStableMatrixCEIsoAtHeight :
    stableMatrixCEComplexAtHeight.{u,v,z} k A ≅
      canonicalStableMatrixCEComplexAtHeight.{u,v,max u v z} k A :=
  (colimit.isColimit (matrixComplexFunctorAtHeight.{u,v,max u v z} k A)).coconePointUniqueUpToIso
    (canonicalStableMatrixCEAtHeightIsColimit.{u,v,z} k A)

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), the forward map of the chosen-height
finite-to-stable CE isomorphism is precisely the comparison
induced by the lifted finite-inclusion cocone. -/
theorem canonicalStableMatrixCEIsoAtHeight_hom :
    (canonicalStableMatrixCEIsoAtHeight.{u,v,z} k A).hom =
      colimitToCanonicalStableMatrixCEAtHeight.{u,v,z} k A := rfl

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), the comparison from the lifted finite CE
colimit to C_*^H(Mat_∞(A)) is an isomorphism of chain complexes.
It has the lifted finite CE inclusions as its restrictions. -/
instance colimitToCanonicalStableMatrixCEAtHeight_isIso :
    IsIso (colimitToCanonicalStableMatrixCEAtHeight.{u,v,z} k A) := by
  rw [← canonicalStableMatrixCEIsoAtHeight_hom]
  infer_instance

end ChevalleyEilenberg
