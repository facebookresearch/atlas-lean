/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import MathlibExt.Algebra.Homology.Functor
public meta import Lean.Elab.Tactic.Omega

/-!
# The sum tensor of integer cochain complexes

Every term and variable map is the tensor bifunctor and direct-sum total. Its differential uses
the original first-factor degree sign. The ring and both carrier universes are independent; no
boundedness or supplied total is used.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v w

variable (R : Type u) [CommRing R]

/-- The tensor totalization provider for independent carrier universes. -/
local instance tensorHasMapBifunctorAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Compatibility name for clients compiled before the tensor provider was named. -/
abbrev instHasMapBifunctorModuleCatIntTensorBifunctorAtUp
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ) :=
  tensorHasMapBifunctorAt R P Q

/-- Totalization of the module tensor, on the full integer cochain grading. -/
def bifunctorAt : CochainComplex (ModuleCat.{v} R) ℤ ⥤
    CochainComplex (ModuleCat.{w} R) ℤ ⥤ CochainComplex (ModuleCat.{max v w} R) ℤ := by
  letI : ∀ (P : CochainComplex (ModuleCat.{v} R) ℤ)
      (Q : CochainComplex (ModuleCat.{w} R) ℤ),
      HomologicalComplex.HasMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ) :=
    fun P Q => by intro n; infer_instance
  exact (ModuleCat.tensorBifunctorAt R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)

/-- The full sum tensor complex. -/
def complexAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) :
    CochainComplex (ModuleCat.{max v w} R) ℤ :=
  ((bifunctorAt R).obj P).obj Q

/-- Place the original pure tensor in its total degree. -/
def mkAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : Q.X q) :
    (complexAt R P Q).X n :=
  (HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
    p q n h).hom (x ⊗ₜ[R] y)

/-- The simultaneous tensor map of the original two complex morphisms. -/
def mapAt {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    complexAt R P Q ⟶ complexAt R P' Q' :=
  HomologicalComplex.mapBifunctorMap f g (ModuleCat.tensorBifunctorAt R) (.up ℤ)

/-- Both original factor values are retained by the total map. -/
theorem mapAt_mk {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : Q.X q) :
    ((mapAt R f g).f n).hom (mkAt R P Q p q n h x y) =
      mkAt R P' Q' p q n h ((f.f p).hom x) ((g.f q).hom y) := by
  let F : ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤ ModuleCat.{max v w} R :=
    ModuleCat.tensorBifunctorAt R
  let A := ModuleCat.tensorObjAt R (P.X p) (Q.X q)
  let K := complexAt R P Q
  let L := complexAt R P' Q'
  let i : A ⟶ K.X n := HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p q n h
  let j : ModuleCat.tensorObjAt R (P'.X p) (Q'.X q) ⟶ L.X n :=
    HomologicalComplex.ιMapBifunctor P' Q' F (.up ℤ) p q n h
  let φ : K ⟶ L := mapAt R f g
  have hi : i ≫ φ.f n =
      ((F.map (f.f p)).app (Q.X q) ≫ (F.obj (P'.X p)).map (g.f q)) ≫ j := by
    exact (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := P) (K₂ := Q) (L₁ := P') (L₂ := Q') f g F (.up ℤ) p q n h).trans
        (Category.assoc _ _ _).symm
  have ht : (((F.map (f.f p)).app (Q.X q) ≫
      (F.obj (P'.X p)).map (g.f q)).hom (x ⊗ₜ[R] y)) =
      (f.f p).hom x ⊗ₜ[R] (g.f q).hom y := by
    change TensorProduct.map LinearMap.id (g.f q).hom
      (TensorProduct.map (f.f p).hom LinearMap.id (x ⊗ₜ[R] y)) = _
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  have hv := congrArg (fun m : A ⟶ L.X n => m.hom (x ⊗ₜ[R] y)) hi
  change (φ.f n).hom (i.hom (x ⊗ₜ[R] y)) =
    j.hom (((F.map (f.f p)).app (Q.X q) ≫
      (F.obj (P'.X p)).map (g.f q)).hom (x ⊗ₜ[R] y)) at hv
  rw [ht] at hv
  exact hv

/-- The two original single-variable tensor maps assemble their simultaneous map. -/
theorem mapAt_precomp_postcomp
    {P P' Q Q' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    mapAt R f (𝟙 Q) ≫ mapAt R (𝟙 P') g = mapAt R f g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((mapAt R (𝟙 P') g).f n).hom
      (((mapAt R f (𝟙 Q)).f n).hom (mkAt R P Q p q n hpq x y)) =
    ((mapAt R f g).f n).hom (mkAt R P Q p q n hpq x y)
  rw [mapAt_mk, mapAt_mk, mapAt_mk]
  rfl

/-- The total differential retains the cochain tensor signs in every degree. -/
theorem d_mkAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : Q.X q) :
    ((complexAt R P Q).d n (n + 1)).hom (mkAt R P Q p q n h x y) =
      mkAt R P Q (p + 1) q (n + 1) (by omega) ((P.d p (p + 1)).hom x) y +
        p.negOnePow • mkAt R P Q p (q + 1) (n + 1) (by omega) x
          ((Q.d q (q + 1)).hom y) := by
  let F : ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤ ModuleCat.{max v w} R :=
    ModuleCat.tensorBifunctorAt R
  let A := ModuleCat.tensorObjAt R (P.X p) (Q.X q)
  let K := complexAt R P Q
  let T := K.X (n + 1)
  let i : A ⟶ K.X n := HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p q n h
  let j₁ : ModuleCat.tensorObjAt R (P.X (p + 1)) (Q.X q) ⟶ T :=
    HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) (p + 1) q (n + 1) (by change p + 1 + q = n + 1; omega)
  let j₂ : ModuleCat.tensorObjAt R (P.X p) (Q.X (q + 1)) ⟶ T :=
    HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)
  have hε₁ : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = 1 := rfl
  have hε₂ : ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = p.negOnePow := rfl
  have hi : i ≫ K.d n (n + 1) =
      (F.map (P.d p (p + 1))).app (Q.X q) ≫ j₁ +
        p.negOnePow • ((F.obj (P.X p)).map (Q.d q (q + 1)) ≫ j₂) := by
    change HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p q n h ≫
      (HomologicalComplex.mapBifunctor P Q F (.up ℤ)).d n (n + 1) = _
    rw [HomologicalComplex.mapBifunctor.d_eq P Q F (.up ℤ) n (n + 1),
      Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq P Q F (.up ℤ)
        (i₁ := p) (i₁' := p + 1) (by simp) q (n + 1)
        (by change p + 1 + q = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P Q F (.up ℤ) p
        (i₂ := q) (i₂' := q + 1) (by simp) (n + 1)
        (by change p + (q + 1) = n + 1; omega),
      hε₁, hε₂, one_smul]
    rfl
  have hp : ((F.map (P.d p (p + 1))).app (Q.X q)).hom (x ⊗ₜ[R] y) =
      (P.d p (p + 1)).hom x ⊗ₜ[R] y := by
    change TensorProduct.map (P.d p (p + 1)).hom LinearMap.id (x ⊗ₜ[R] y) = _
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  have hq : ((F.obj (P.X p)).map (Q.d q (q + 1))).hom (x ⊗ₜ[R] y) =
      x ⊗ₜ[R] (Q.d q (q + 1)).hom y := by
    change TensorProduct.map LinearMap.id (Q.d q (q + 1)).hom (x ⊗ₜ[R] y) = _
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  let ev : (A ⟶ T) →+ T :=
    { toFun := fun m => m.hom (x ⊗ₜ[R] y)
      map_zero' := by simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
      map_add' := fun f g => by simp only [ModuleCat.hom_add, LinearMap.add_apply] }
  have hv := congrArg ev hi
  simp only [map_add, Units.smul_def, map_zsmul] at hv
  change (K.d n (n + 1)).hom (i.hom (x ⊗ₜ[R] y)) =
    j₁.hom (((F.map (P.d p (p + 1))).app (Q.X q)).hom (x ⊗ₜ[R] y)) +
      (p.negOnePow : ℤ) •
        j₂.hom (((F.obj (P.X p)).map (Q.d q (q + 1))).hom (x ⊗ₜ[R] y)) at hv
  rw [hp, hq] at hv
  exact hv

end CochainComplex.ModuleTensor
