/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.ExteriorPowerDirectLimit
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixModule

/-!
# Stable matrix CE chains commute with the directed matrix colimit

Let k be a commutative ring and A an associative unital k-algebra.
In degree n, the finite matrix CE diagram is the diagram
m ↦ ⋀_k^n Mat_m(A), with maps the exterior powers of zero extension.
Since exterior powers preserve directed module colimits, the cocone
with point ⋀_k^n Mat_∞(A) is colimiting in every degree.

Consequently the finite-stage CE cocone is a colimit cocone of chain
complexes, and its comparison gives
colim_m C_*(Mat_m(A)) ≅ C_*(Mat_∞(A)).
The forward map restricts to ⋀^n i_m on each degree-n finite-stage
inclusion. The complexes are in ModuleCat^max(u,v)(k), with independent
ring and algebra worlds, and n,m range over all nonnegative degrees
and matrix sizes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ring k, an associative unital k-algebra A
and n ≥ 0, evaluating the finite matrix CE diagram in degree n
is naturally isomorphic to applying ⋀_k^n to the finite matrix
module diagram. At stage m the object is ⋀_k^n Mat_m(A), and a
zero-extension transition acts by its nth exterior power. -/
def matrixCEDegreeDiagramIso (n : ℕ) :
    matrixComplexFunctor k A ⋙ HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n ≅
      matrixModuleFunctor k A ⋙ ModuleCat.exteriorPowerFunctorAt k n :=
  NatIso.ofComponents (fun m => eqToIso (by rfl)) (by
    intro m p h
    change (matrixZeroCornerMap k A (leOfHom h)).f n ≫ 𝟙 _ =
      𝟙 _ ≫ ModuleCat.ofHom (exteriorPower.map n
        (Matrix.zeroExtendLinear (k := k) (A := A) (leOfHom h)))
    rw [Category.comp_id, Category.id_comp]
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change ((matrixZeroCornerMap k A (leOfHom h)).f n).hom (exteriorPower.ιMulti k n a) =
      exteriorPower.map n (Matrix.zeroExtendLinear (k := k) (A := A) (leOfHom h))
        (exteriorPower.ιMulti k n a)
    have hc := matrixZeroCornerMap_pure k A (leOfHom h) n a
    have he := exteriorPower.map_apply_ιMulti
      (Matrix.zeroExtendLinear (k := k) (A := A) (leOfHom h)) a
    have hf : (fun i => Matrix.zeroExtend (leOfHom h) (a i)) =
        (Matrix.zeroExtendLinear (k := k) (A := A) (leOfHom h)) ∘ a := by
      funext i
      exact (Matrix.zeroExtendLinear_apply (k := k) (leOfHom h) (a i)).symm
    exact hc.trans ((congrArg (exteriorPower.ιMulti k n) hf).trans he.symm))

/-- For a commutative ring k and an associative unital
k-algebra A, the cocone of finite CE inclusions
C_*(Mat_m(A)) → C_*(Mat_∞(A)) is a colimit cocone.
Its degree-n cocone is the exterior power of the directed matrix
module colimit, for every n ≥ 0. -/
def canonicalStableMatrixCEIsColimit : IsColimit (canonicalStableMatrixCECocone k A) :=
  HomologicalComplex.isColimitOfEval _ _ (fun n => by
    let E := ModuleCat.exteriorPowerFunctorAt k n
    let S := E.mapCocone (canonicalStableMatrixModuleCocone k A)
    let e := matrixCEDegreeDiagramIso k A n
    have hS : IsColimit S := isColimitOfPreserves E (canonicalStableMatrixModuleIsColimit k A)
    have hp : IsColimit ((Cocone.precompose e.hom).obj S) :=
      (IsColimit.precomposeHomEquiv e S).symm hS
    have w : (Cocone.precompose e.hom).obj S ≅
        (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n).mapCocone
          (canonicalStableMatrixCECocone k A) :=
      Cocone.ext (Iso.refl _) (by
        intro m
        change ModuleCat.ofHom
            (exteriorPower.map n (canonicalStableMatrixInclusion k A m :
              Matrix (Fin m) (Fin m) A →ₗ[k] canonicalStableMatrixAlgebra k A)) =
          (nativeComplexMap k (Matrix (Fin m) (Fin m) A)
            (canonicalStableMatrixLieInclusion k A m)).f n
        rw [nativeComplexMap_f]
        rfl)
    exact IsColimit.ofIsoColimit hp w)

/-- For a commutative ring k and an associative unital
k-algebra A, the finite-stage comparison is the chain isomorphism
colim_m C_*(Mat_m(A)) ≅ C_*(Mat_∞(A)).
It is determined by the CE maps of the finite Lie inclusions. -/
def canonicalStableMatrixCEIso : stableMatrixCEComplex k A ≅ canonicalStableMatrixCEComplex k A :=
  (colimit.isColimit (matrixComplexFunctor k A)).coconePointUniqueUpToIso
    (canonicalStableMatrixCEIsColimit k A)

/-- For a commutative ring k and an associative unital
k-algebra A, the forward morphism of
colim_m C_*(Mat_m(A)) ≅ C_*(Mat_∞(A)) is the map induced by
the cocone of finite CE inclusions. -/
theorem canonicalStableMatrixCEIso_hom :
    (canonicalStableMatrixCEIso k A).hom = colimitToCanonicalStableMatrixCE k A := rfl

/-- For a commutative ring k and an associative unital
k-algebra A, the chain map from the finite matrix CE colimit to
C_*(Mat_∞(A)), characterized by its finite-stage inclusions,
is an isomorphism. -/
instance colimitToCanonicalStableMatrixCE_isIso : IsIso (colimitToCanonicalStableMatrixCE k A) := by
  rw [← canonicalStableMatrixCEIso_hom]
  infer_instance

end ChevalleyEilenberg
