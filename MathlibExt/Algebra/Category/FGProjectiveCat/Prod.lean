/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChange
public import MathlibExt.Algebra.Category.FGModuleCat.Prod.Components
public import MathlibExt.Algebra.Category.FGModuleCat.Prod.Embeddings
public import MathlibExt.Algebra.Category.ModuleCat.Prod.Decomposition
public import MathlibExt.Algebra.Category.ModuleCat.Prod.FstAdjunctions
public import MathlibExt.Algebra.Category.ModuleCat.Prod.SndAdjunctions
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
# Finite projective modules over a product ring

For arbitrary rings `R` and `S`, the two idempotent component functors and
the two projection-restriction embeddings preserve finite projective
modules.  This file lifts them from `ModuleCat` to `FGProjectiveCat`, proves
additivity and exactness, and lifts the component/embedding and decomposition
isomorphisms.

Projectivity is obtained categorically.  Each module functor is one side of
adjunctions in both orientations, so its adjoint preserves epimorphisms and
the functor preserves projective objects.  Finiteness reuses the existing
`FGModuleCat` product lemmas.

For commutative rings, the component functors are naturally isomorphic to
base change along `RingHom.fst` and `RingHom.snd`, by uniqueness of left
adjoints.  This is the bridge used for functoriality of the product formula
on ring `K₀`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace ProdIdempotent

variable {R S : Type u} [Ring R] [Ring S]

/-- The `e = (1,0)` component of a projective product-ring module is
projective over the first factor. -/
theorem projective_eComponent_of_projective (M : ModuleCat.{u} (R × S))
    (hM : Module.Projective (R × S) M) :
    Module.Projective R
      ((eComponentFunctor (R := R) (S := S)).obj M) := by
  let _ : Module.Projective (R × S) M := hM
  have hProjectiveM : CategoryTheory.Projective M := inferInstance
  let hPreserves :
      (eComponentFunctor (R := R) (S := S)).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (eComponentFunctorAdj_prodEmbeddingFst R S)
  have hProjectiveComponent : CategoryTheory.Projective
      ((eComponentFunctor (R := R) (S := S)).obj M) :=
    hPreserves.projective_obj hProjectiveM
  let _ : CategoryTheory.Projective
      ((eComponentFunctor (R := R) (S := S)).obj M) := hProjectiveComponent
  exact inferInstance

/-- The `f = (0,1)` component of a projective product-ring module is
projective over the second factor. -/
theorem projective_fComponent_of_projective (M : ModuleCat.{u} (R × S))
    (hM : Module.Projective (R × S) M) :
    Module.Projective S
      ((fComponentFunctor (R := R) (S := S)).obj M) := by
  let _ : Module.Projective (R × S) M := hM
  have hProjectiveM : CategoryTheory.Projective M := inferInstance
  let hPreserves :
      (fComponentFunctor (R := R) (S := S)).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (fComponentFunctorAdj_prodEmbeddingSnd R S)
  have hProjectiveComponent : CategoryTheory.Projective
      ((fComponentFunctor (R := R) (S := S)).obj M) :=
    hPreserves.projective_obj hProjectiveM
  let _ : CategoryTheory.Projective
      ((fComponentFunctor (R := R) (S := S)).obj M) := hProjectiveComponent
  exact inferInstance

/-- Restriction along `RingHom.fst` sends projective first-factor modules to
projective modules over the product ring. -/
theorem projective_prodEmbeddingFst_of_projective (M : ModuleCat.{u} R)
    (hM : Module.Projective R M) :
    Module.Projective (R × S) ((ModuleCat.prodEmbeddingFst R S).obj M) := by
  let _ : Module.Projective R M := hM
  have hProjectiveM : CategoryTheory.Projective M := inferInstance
  let hPreserves :
      (ModuleCat.prodEmbeddingFst R S).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (prodEmbeddingFstAdj_eComponentFunctor R S)
  have hProjectiveEmbedding : CategoryTheory.Projective
      ((ModuleCat.prodEmbeddingFst R S).obj M) :=
    hPreserves.projective_obj hProjectiveM
  let _ : CategoryTheory.Projective
      ((ModuleCat.prodEmbeddingFst R S).obj M) := hProjectiveEmbedding
  exact inferInstance

/-- Restriction along `RingHom.snd` sends projective second-factor modules to
projective modules over the product ring. -/
theorem projective_prodEmbeddingSnd_of_projective (M : ModuleCat.{u} S)
    (hM : Module.Projective S M) :
    Module.Projective (R × S) ((ModuleCat.prodEmbeddingSnd R S).obj M) := by
  let _ : Module.Projective S M := hM
  have hProjectiveM : CategoryTheory.Projective M := inferInstance
  let hPreserves :
      (ModuleCat.prodEmbeddingSnd R S).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (prodEmbeddingSndAdj_fComponentFunctor R S)
  have hProjectiveEmbedding : CategoryTheory.Projective
      ((ModuleCat.prodEmbeddingSnd R S).obj M) :=
    hPreserves.projective_obj hProjectiveM
  let _ : CategoryTheory.Projective
      ((ModuleCat.prodEmbeddingSnd R S).obj M) := hProjectiveEmbedding
  exact inferInstance

/-- The first idempotent component functor on finite projective modules. -/
noncomputable def eComponentFunctorFGP :
    FGProjectiveCat.{u} (R × S) ⥤ FGProjectiveCat.{u} R :=
  (ModuleCat.isFGProjective (R := R)).lift
    (FGProjectiveCat.toModuleCat (R := R × S) ⋙
      eComponentFunctor (R := R) (S := S))
    (fun X =>
      ⟨finite_R_eSubmodule_of_finite X.property.1,
        projective_eComponent_of_projective X.obj X.property.2⟩)

/-- The second idempotent component functor on finite projective modules. -/
noncomputable def fComponentFunctorFGP :
    FGProjectiveCat.{u} (R × S) ⥤ FGProjectiveCat.{u} S :=
  (ModuleCat.isFGProjective (R := S)).lift
    (FGProjectiveCat.toModuleCat (R := R × S) ⋙
      fComponentFunctor (R := R) (S := S))
    (fun X =>
      ⟨finite_S_fSubmodule_of_finite X.property.1,
        projective_fComponent_of_projective X.obj X.property.2⟩)

@[simp]
lemma eComponentFunctorFGP_obj_obj (X : FGProjectiveCat.{u} (R × S)) :
    ((eComponentFunctorFGP (R := R) (S := S)).obj X).obj =
      (eComponentFunctor (R := R) (S := S)).obj X.obj :=
  rfl

@[simp]
lemma fComponentFunctorFGP_obj_obj (X : FGProjectiveCat.{u} (R × S)) :
    ((fComponentFunctorFGP (R := R) (S := S)).obj X).obj =
      (fComponentFunctor (R := R) (S := S)).obj X.obj :=
  rfl

@[simp]
lemma eComponentFunctorFGP_map_hom {X Y : FGProjectiveCat.{u} (R × S)}
    (f : X ⟶ Y) :
    ((eComponentFunctorFGP (R := R) (S := S)).map f).hom =
      (eComponentFunctor (R := R) (S := S)).map f.hom :=
  rfl

@[simp]
lemma fComponentFunctorFGP_map_hom {X Y : FGProjectiveCat.{u} (R × S)}
    (f : X ⟶ Y) :
    ((fComponentFunctorFGP (R := R) (S := S)).map f).hom =
      (fComponentFunctor (R := R) (S := S)).map f.hom :=
  rfl

instance eComponentFunctorFGP_additive :
    (eComponentFunctorFGP (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact (eComponentFunctor (R := R) (S := S)).map_add

instance fComponentFunctorFGP_additive :
    (fComponentFunctorFGP (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact (fComponentFunctor (R := R) (S := S)).map_add

instance eComponentFunctorFGP_isExact :
    (eComponentFunctorFGP (R := R) (S := S)).IsExact :=
  ExactCategory.isExact_splitSource _

instance fComponentFunctorFGP_isExact :
    (fComponentFunctorFGP (R := R) (S := S)).IsExact :=
  ExactCategory.isExact_splitSource _

end ProdIdempotent

namespace FGProjectiveCat

variable {R S : Type u} [Ring R] [Ring S]

/-- Embed first-factor finite projectives as product-ring modules through
`RingHom.fst`. -/
noncomputable def prodEmbeddingFst :
    FGProjectiveCat.{u} R ⥤ FGProjectiveCat.{u} (R × S) :=
  (ModuleCat.isFGProjective (R := R × S)).lift
    (toModuleCat (R := R) ⋙ ModuleCat.prodEmbeddingFst R S)
    (fun X =>
      ⟨FGModuleCat.isFG_restrictScalars
          (RingHom.fst R S) RingHom.isFinite_fst X.property.1,
        ProdIdempotent.projective_prodEmbeddingFst_of_projective X.obj X.property.2⟩)

/-- Embed second-factor finite projectives as product-ring modules through
`RingHom.snd`. -/
noncomputable def prodEmbeddingSnd :
    FGProjectiveCat.{u} S ⥤ FGProjectiveCat.{u} (R × S) :=
  (ModuleCat.isFGProjective (R := R × S)).lift
    (toModuleCat (R := S) ⋙ ModuleCat.prodEmbeddingSnd R S)
    (fun X =>
      ⟨FGModuleCat.isFG_restrictScalars
          (RingHom.snd R S) RingHom.isFinite_snd X.property.1,
        ProdIdempotent.projective_prodEmbeddingSnd_of_projective X.obj X.property.2⟩)

@[simp]
lemma prodEmbeddingFst_obj_obj (M : FGProjectiveCat.{u} R) :
    ((prodEmbeddingFst (R := R) (S := S)).obj M).obj =
      (ModuleCat.prodEmbeddingFst R S).obj M.obj :=
  rfl

@[simp]
lemma prodEmbeddingSnd_obj_obj (M : FGProjectiveCat.{u} S) :
    ((prodEmbeddingSnd (R := R) (S := S)).obj M).obj =
      (ModuleCat.prodEmbeddingSnd R S).obj M.obj :=
  rfl

@[simp]
lemma prodEmbeddingFst_map_hom {M N : FGProjectiveCat.{u} R} (f : M ⟶ N) :
    ((prodEmbeddingFst (R := R) (S := S)).map f).hom =
      (ModuleCat.prodEmbeddingFst R S).map f.hom :=
  rfl

@[simp]
lemma prodEmbeddingSnd_map_hom {M N : FGProjectiveCat.{u} S} (f : M ⟶ N) :
    ((prodEmbeddingSnd (R := R) (S := S)).map f).hom =
      (ModuleCat.prodEmbeddingSnd R S).map f.hom :=
  rfl

instance prodEmbeddingFst_additive :
    (prodEmbeddingFst (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact (ModuleCat.prodEmbeddingFst R S).map_add

instance prodEmbeddingSnd_additive :
    (prodEmbeddingSnd (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact (ModuleCat.prodEmbeddingSnd R S).map_add

instance prodEmbeddingFst_isExact :
    (prodEmbeddingFst (R := R) (S := S)).IsExact :=
  ExactCategory.isExact_splitSource _

instance prodEmbeddingSnd_isExact :
    (prodEmbeddingSnd (R := R) (S := S)).IsExact :=
  ExactCategory.isExact_splitSource _

end FGProjectiveCat

namespace ProdIdempotent

variable {R S : Type u} [Ring R] [Ring S]

/-- First component after first embedding recovers the original finite
projective module. -/
noncomputable def prodEmbeddingFst_eComponentFGPIso
    (N : FGProjectiveCat.{u} R) :
    (eComponentFunctorFGP (R := R) (S := S)).obj
        ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj N) ≅ N :=
  (ModuleCat.isFGProjective (R := R)).isoMk
    (prodEmbeddingFst_eComponentIso (R := R) (S := S) N.obj)

/-- Second component after second embedding recovers the original finite
projective module. -/
noncomputable def prodEmbeddingSnd_fComponentFGPIso
    (N : FGProjectiveCat.{u} S) :
    (fComponentFunctorFGP (R := R) (S := S)).obj
        ((FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj N) ≅ N :=
  (ModuleCat.isFGProjective (R := S)).isoMk
    (prodEmbeddingSnd_fComponentIso (R := R) (S := S) N.obj)

/-- The second component of a first-factor embedding is zero. -/
noncomputable def prodEmbeddingFst_fComponentFGPZeroIso
    (N : FGProjectiveCat.{u} R) :
    (fComponentFunctorFGP (R := R) (S := S)).obj
        ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj N) ≅
      FGProjectiveCat.of (R := S) PUnit :=
  (ModuleCat.isFGProjective (R := S)).isoMk
    (prodEmbeddingFst_fComponentZeroIso (R := R) (S := S) N.obj)

/-- The first component of a second-factor embedding is zero. -/
noncomputable def prodEmbeddingSnd_eComponentFGPZeroIso
    (N : FGProjectiveCat.{u} S) :
    (eComponentFunctorFGP (R := R) (S := S)).obj
        ((FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj N) ≅
      FGProjectiveCat.of (R := R) PUnit :=
  (ModuleCat.isFGProjective (R := R)).isoMk
    (prodEmbeddingSnd_eComponentZeroIso (R := R) (S := S) N.obj)

end ProdIdempotent

namespace FGProjectiveCat.Prod

variable {R S : Type u} [Ring R] [Ring S]

/-- Every finite projective module over `R × S` is the biproduct of its two
embedded idempotent components. -/
noncomputable def decompositionIso (X : FGProjectiveCat.{u} (R × S)) :
    X ≅
      ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj
          ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj X) ⊞
        (FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj
          ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj X)) := by
  let A := (FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj
    ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj X)
  let B := (FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj
    ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj X)
  let F := FGProjectiveCat.toModuleCat (R := R × S)
  let _ : PreservesBiproduct (pairFunction A B) F := inferInstance
  let _ : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  exact (ModuleCat.isFGProjective (R := R × S)).isoMk
    ((ProdIdempotent.prodDecompositionIso (M := X.obj)).trans
      (F.mapBiprod A B).symm)

end FGProjectiveCat.Prod

namespace ProdIdempotent

section BaseChangeComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extension of scalars along `fst` is the first idempotent component functor.
Both are left adjoint to restriction along `fst`. -/
noncomputable def extendScalarsFstIsoEComponent :
    ModuleCat.extendScalars (RingHom.fst R S) ≅
      eComponentFunctor (R := R) (S := S) :=
  Adjunction.leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj (RingHom.fst R S))
    (eComponentFunctorAdj_prodEmbeddingFst R S)

/-- Extension of scalars along `snd` is the second idempotent component functor.
Both are left adjoint to restriction along `snd`. -/
noncomputable def extendScalarsSndIsoFComponent :
    ModuleCat.extendScalars (RingHom.snd R S) ≅
      fComponentFunctor (R := R) (S := S) :=
  Adjunction.leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj (RingHom.snd R S))
    (fComponentFunctorAdj_prodEmbeddingSnd R S)

/-- The base-change/component comparison lifted to finite projective modules. -/
noncomputable def baseChangeFstIsoEComponentFGP :
    FGProjectiveCat.baseChange (RingHom.fst R S) ≅
      eComponentFunctorFGP (R := R) (S := S) :=
  NatIso.ofComponents
    (fun X => (ModuleCat.isFGProjective (R := R)).isoMk
      ((extendScalarsFstIsoEComponent (R := R) (S := S)).app X.obj))
    (by
      intro X Y f
      apply FGProjectiveCat.hom_ext
      exact congrArg (fun k => k.hom)
        ((extendScalarsFstIsoEComponent (R := R) (S := S)).hom.naturality f.hom))

/-- The base-change/component comparison lifted to finite projective modules. -/
noncomputable def baseChangeSndIsoFComponentFGP :
    FGProjectiveCat.baseChange (RingHom.snd R S) ≅
      fComponentFunctorFGP (R := R) (S := S) :=
  NatIso.ofComponents
    (fun X => (ModuleCat.isFGProjective (R := S)).isoMk
      ((extendScalarsSndIsoFComponent (R := R) (S := S)).app X.obj))
    (by
      intro X Y f
      apply FGProjectiveCat.hom_ext
      exact congrArg (fun k => k.hom)
        ((extendScalarsSndIsoFComponent (R := R) (S := S)).hom.naturality f.hom))

end BaseChangeComparison

end ProdIdempotent

end
