/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedFunctor
public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedQuasiIso
public import MathlibExt.Algebra.Homology.NatIsoOfQuasiIsoAt

/-!
# Normalized to unnormalized simplicial homology comparison

For a fixed coefficient object in a category with homology, the normalized chain
inclusion `fromNormalizedChainComplex` is a quasi-isomorphism. Applying homology
gives canonical isomorphisms objectwise and a natural isomorphism between the
composites of the fixed-coefficient chain functors with Mathlib's homology functor.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomologicalComplex

namespace SSet

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The inclusion `fromNormalizedChainComplexNatTrans` at `X` is definitionally
`X.fromNormalizedChainComplex`. -/
@[simp]
theorem fromNormalizedChainComplexNatTrans_app (R : C) (X : SSet.{w}) :
    (fromNormalizedChainComplexNatTrans (C := C) R).app X =
      X.fromNormalizedChainComplex (C := C) R :=
  rfl

variable [CategoryWithHomology C]

/-- Objectwise canonical isomorphism from normalized to unnormalized simplicial
homology in degree `n`, obtained from the quasi-isomorphism
`X.fromNormalizedChainComplex R`. Its forward map is definitionally
`homologyMap (X.fromNormalizedChainComplex R) n`. -/
noncomputable def homologyIso_fromNormalizedChainComplex
    (X : SSet.{w}) (R : C) (n : ℕ) :
    (X.normalizedChainComplex (C := C) R).homology n ≅
      (X.chainComplex (C := C) R).homology n :=
  let _ : QuasiIso (X.fromNormalizedChainComplex (C := C) R) :=
    quasiIso_fromNormalizedChainComplex C X R
  isoOfQuasiIsoAt (X.fromNormalizedChainComplex (C := C) R) n

@[simp]
theorem homologyIso_fromNormalizedChainComplex_hom
    (X : SSet.{w}) (R : C) (n : ℕ) :
    (homologyIso_fromNormalizedChainComplex (C := C) X R n).hom =
      HomologicalComplex.homologyMap
        (X.fromNormalizedChainComplex (C := C) R) n :=
  rfl

/-- The whiskered natural transformation obtained by postcomposing
`fromNormalizedChainComplexNatTrans R` with Mathlib's homology functor.
Its component at `X` is `homologyMap (X.fromNormalizedChainComplex R) n`. -/
noncomputable def fromNormalizedHomologyNatTrans (R : C) (n : ℕ) :
    SSet.normalizedChainComplexFunctorObj (C := C) R ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n ⟶
      (SSet.chainComplexFunctor C).obj R ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n :=
  Functor.whiskerRight (fromNormalizedChainComplexNatTrans (C := C) R)
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)

@[simp]
theorem fromNormalizedHomologyNatTrans_app (R : C) (n : ℕ) (X : SSet.{w}) :
    (fromNormalizedHomologyNatTrans (C := C) R n).app X =
      HomologicalComplex.homologyMap
        (X.fromNormalizedChainComplex (C := C) R) n :=
  rfl

theorem fromNormalizedHomologyNatTrans_app_eq_map (R : C) (n : ℕ)
    (X : SSet.{w}) :
    (fromNormalizedHomologyNatTrans (C := C) R n).app X =
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map
        ((fromNormalizedChainComplexNatTrans (C := C) R).app X) :=
  rfl

/-- Natural isomorphism in the simplicial set between the normalized and
unnormalized fixed-coefficient chain functors postcomposed with homology.
Obtained by right-whiskering `fromNormalizedChainComplexNatTrans` with the
homology functor and promoting via `homologyNatIsoOfQuasiIsoAt`; the objectwise
`IsIso` comes from `QuasiIso`. -/
noncomputable def homologyNatIso_fromNormalizedChainComplex (R : C) (n : ℕ) :
    SSet.normalizedChainComplexFunctorObj (C := C) R ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n ≅
      (SSet.chainComplexFunctor C).obj R ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n :=
  HomologicalComplex.homologyNatIsoOfQuasiIsoAt
    (f := fromNormalizedChainComplexNatTrans (C := C) R) n
    (fun X => by
      have : QuasiIso ((fromNormalizedChainComplexNatTrans (C := C) R).app X) := by
        have h_eq : (fromNormalizedChainComplexNatTrans (C := C) R).app X =
            X.fromNormalizedChainComplex (C := C) R := rfl
        rw [h_eq]
        exact quasiIso_fromNormalizedChainComplex C X R
      infer_instance)

@[simp]
theorem homologyNatIso_fromNormalizedChainComplex_hom_app (R : C) (n : ℕ)
    (X : SSet.{w}) :
    (homologyNatIso_fromNormalizedChainComplex (C := C) R n).hom.app X =
      HomologicalComplex.homologyMap
        (X.fromNormalizedChainComplex (C := C) R) n :=
  rfl

theorem homologyNatIso_fromNormalizedChainComplex_hom_app_eq_fromNormalizedHomologyNatTrans
    (R : C) (n : ℕ) (X : SSet.{w}) :
    (homologyNatIso_fromNormalizedChainComplex (C := C) R n).hom.app X =
      (fromNormalizedHomologyNatTrans (C := C) R n).app X :=
  rfl

theorem homologyNatIso_fromNormalizedChainComplex_hom_app_eq_fromNormalizedChainComplexNatTrans
    (R : C) (n : ℕ) (X : SSet.{w}) :
    (homologyNatIso_fromNormalizedChainComplex (C := C) R n).hom.app X =
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map
        ((fromNormalizedChainComplexNatTrans (C := C) R).app X) :=
  rfl

/-- Variant with target expressed via `SSet.homology` abbreviation for
ergonomics, definitionally equal to `homologyIso_fromNormalizedChainComplex`. -/
noncomputable def normalizedHomologyIso (X : SSet.{w}) (R : C) (n : ℕ) :
    (X.normalizedChainComplex (C := C) R).homology n ≅
      X.homology (C := C) R n :=
  homologyIso_fromNormalizedChainComplex (C := C) X R n

@[simp]
theorem normalizedHomologyIso_hom (X : SSet.{w}) (R : C) (n : ℕ) :
    (normalizedHomologyIso (C := C) X R n).hom =
      HomologicalComplex.homologyMap
        (X.fromNormalizedChainComplex (C := C) R) n :=
  rfl

end SSet
