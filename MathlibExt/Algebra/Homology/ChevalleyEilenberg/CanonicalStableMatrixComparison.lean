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
# Chevalley–Eilenberg complexes commute with stable matrix colimits

For a unital algebra over a commutative ring, the Chevalley–Eilenberg complex of its stable
matrix Lie algebra is the directed colimit of the finite matrix complexes. Exterior powers
preserve the underlying directed module colimit, so the finite-stage comparison is an
isomorphism of chain complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The degree-n CE diagram is the exterior-power matrix module diagram. -/
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

/-- The finite matrix Chevalley–Eilenberg cocone on the stable matrix complex is colimiting. -/
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

/-- The canonical stable Lie CE model is the colimit of the finite matrix CE diagram. -/
def canonicalStableMatrixCEIso : stableMatrixCEComplex k A ≅ canonicalStableMatrixCEComplex k A :=
  (colimit.isColimit (matrixComplexFunctor k A)).coconePointUniqueUpToIso
    (canonicalStableMatrixCEIsColimit k A)

/-- The model isomorphism has exactly the finite-inclusion comparison as its hom. -/
theorem canonicalStableMatrixCEIso_hom :
    (canonicalStableMatrixCEIso k A).hom = colimitToCanonicalStableMatrixCE k A := rfl

/-- The comparison map is an isomorphism because both canonical CE cocones are colimit. -/
instance colimitToCanonicalStableMatrixCE_isIso : IsIso (colimitToCanonicalStableMatrixCE k A) := by
  rw [← canonicalStableMatrixCEIso_hom]
  infer_instance

end ChevalleyEilenberg
