/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.UniverseScalarRestriction
public import MathlibExt.CategoryTheory.GradedObject.TensorAntidiagonal
public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Graded tensor comparison under scalar restriction

Let R be a commutative ring in universe u, W=max(u,v), and R̂ its canonical copy in W.
Restriction of scalars S from R̂ to R acts pointwise on ℕ-graded modules. For graded X,Y, the
degree-n tensor term is the finite sum over p+q=n. The module comparisons S(X_p)⊗_R
S(Y_q)≅S(X_p⊗_R̂ Y_q), together with preservation of these finite biproducts, give g:S_GX⊗_R
S_GY≅S_G(X⊗_R̂ Y).

On each bidegree summand, g is the module tensor comparison followed by the restricted graded
summand inclusion. The comparison is natural in both graded morphisms. Coefficient carriers
remain in W, with the lift height v independent of the scalar ring universe u.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


local instance highFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} (LiftedRing.{u,v} R)) :=
  Abelian.hasFiniteBiproducts
local instance lowFiniteBiproducts : HasFiniteBiproducts (Modules.{u,v} R) := Abelian.hasFiniteBiproducts

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. This functor S_G sends an ℕ-graded R̂-module X to the graded
R-module n↦S(X_n), and a graded morphism f to the family n↦S(f_n). It preserves identities and
composition degreewise without reindexing the grading. -/
abbrev gradedFunctor : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R))) ⥤
  (GradedObject ℕ (Modules.{u,v} R)) where
  obj X n := (toOriginal.{u,v} R).obj (X n)
  map f n := (toOriginal.{u,v} R).map (f n)
  map_id X := by funext n; exact (toOriginal.{u,v} R).map_id (X n)
  map_comp f g := by funext n; exact (toOriginal.{u,v} R).map_comp (f n) (g n)

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For ℕ-graded R̂-modules X,Y and n∈ℕ, this is the isomorphism
(S_GX⊗_R S_GY)_n≅S((X⊗_R̂ Y)_n). Both tensor terms are finite sums over p+q=n. The comparison
tensors the scalar module comparisons S(X_p)⊗S(Y_q)≅S(X_p⊗Y_q) across the antidiagonal and uses
the canonical finite-biproduct comparison for S. -/
def gradedTensorIsoComponent (X Y : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))) (n : ℕ) :
    ((gradedFunctor.{u,v} R).obj X ⊗ (gradedFunctor.{u,v} R).obj Y) n ≅
      (toOriginal.{u,v} R).obj ((X ⊗ Y) n) :=
  GradedObject.TensorAntidiagonal.iso ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) n ≪≫
    biproduct.mapIso (fun ij : GradedObject.TensorAntidiagonal.Index n =>
      tensorIso.{u,v} R (X ij.val.1) (Y ij.val.2)) ≪≫
    ((toOriginal.{u,v} R).mapBiproduct (fun ij : GradedObject.TensorAntidiagonal.Index n =>
      X ij.val.1 ⊗ Y ij.val.2)).symm ≪≫
    (toOriginal.{u,v} R).mapIso (GradedObject.TensorAntidiagonal.iso X Y n).symm

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For ℕ-graded R̂-modules X,Y, this is the graded isomorphism
g:S_GX⊗_R S_GY≅S_G(X⊗_R̂ Y) assembled from the finite-antidiagonal comparisons. For p+q=n, its
component satisfies ι_{p,q}≫g_n.hom=t_{X_p,Y_q}.hom≫S(ι_{p,q}), where t is the module scalar
tensor comparison. -/
def gradedTensorIso (X Y : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))) :
    (gradedFunctor.{u,v} R).obj X ⊗ (gradedFunctor.{u,v} R).obj Y ≅
      (gradedFunctor.{u,v} R).obj (X ⊗ Y) :=
  GradedObject.isoMk _ _ (gradedTensorIsoComponent.{u,v} R X Y)

@[reassoc (attr := simp)]
theorem ι_gradedTensorIso_hom (X Y : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))) (p q n : ℕ)
  (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫ (gradedTensorIso.{u,v} R X Y).hom n =
      (tensorIso.{u,v} R (X p) (Y q)).hom ≫
        (toOriginal.{u,v} R).map (GradedObject.Monoidal.ιTensorObj X Y p q n h) := by
  change GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫
      (gradedTensorIsoComponent.{u,v} R X Y n).hom = _
  simp only [gradedTensorIsoComponent, GradedObject.TensorAntidiagonal.iso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [GradedObject.TensorAntidiagonal.ι_toBiproduct_assoc,
    biproduct.mapIso_hom, biproduct.ι_map_assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
    ← Functor.map_comp, GradedObject.TensorAntidiagonal.ι_fromBiproduct]

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For graded R̂-module maps f:X→X′ and g:Y→Y′, write
t_{X,Y}:S_GX⊗_R S_GY≅S_G(X⊗_R̂ Y) for the graded tensor comparison. Then
(S_G(f)⊗S_G(g))≫t_{X′,Y′}.hom=t_{X,Y}.hom≫S_G(f⊗g). The equation holds in every degree with the
same antidiagonal indexing. -/
@[reassoc]
theorem gradedTensorIso_naturality {X Y X' Y' : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))}
  (f : X ⟶ X') (g : Y ⟶ Y') :
    ((gradedFunctor.{u,v} R).map f ⊗ₘ (gradedFunctor.{u,v} R).map g) ≫
      (gradedTensorIso.{u,v} R X' Y').hom =
    (gradedTensorIso.{u,v} R X Y).hom ≫ (gradedFunctor.{u,v} R).map (f ⊗ₘ g) := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  change GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫
      GradedObject.Monoidal.tensorHom ((gradedFunctor.{u,v} R).map f)
        ((gradedFunctor.{u,v} R).map g) n ≫ (gradedTensorIso.{u,v} R X' Y').hom n =
    GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫ (gradedTensorIso.{u,v} R X Y).hom n ≫
        (toOriginal.{u,v} R).map (GradedObject.Monoidal.tensorHom f g n)
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ι_gradedTensorIso_hom]
  have hs := congrArg (fun z => z ≫
    (toOriginal.{u,v} R).map (GradedObject.Monoidal.tensorHom f g n))
      (ι_gradedTensorIso_hom.{u,v} R X Y p q n h)
  refine Eq.trans ?_ hs.symm
  rw [tensorIso_naturality_assoc, Category.assoc, ← Functor.map_comp,
    ← GradedObject.Monoidal.ι_tensorHom, Functor.map_comp]

end ModuleCat.UniverseScalarRestriction
