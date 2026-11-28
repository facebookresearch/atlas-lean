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
public import MathlibExt.CategoryTheory.DGSource.CochainBifunctor
public meta import Lean.Elab.Tactic.Omega

/-!
# Full tensor products of integer cochain complexes

For a commutative ring R, the tensor complex of P and Q has degree-n term
⊕_{p+q=n} P^p ⊗_R Q^q. Its differential on a pure tensor is
d(x⊗y) = d_P(x)⊗y + (−1)^p x⊗d_Q(y), for x in P^p.

Both integer gradings are unrestricted. Simultaneous maps of the two
factors preserve the pure tensors and their total degrees.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v w

variable (R : Type u) [CommRing R]

/--
Let R be a commutative ring and P,Q integer cochain complexes of R-modules, whose carriers may
belong to independent universes. The family Pᵖ ⊗_R Qᑫ admits the coproducts and compatible
differential maps needed for totalization over p+q=n, with the cochain tensor sign (−1)ᵖ in
the second factor.
-/
local instance tensorHasMapBifunctorAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/--
For a commutative ring R, the full tensor totalization is a bifunctor on integer cochain
complexes of R-modules, allowing the two carrier universes to vary independently. It sends
(P,Q) to the complex with term ⊕_{p+q=n} Pᵖ ⊗_R Qᑫ and differential d_P⊗1 + (−1)ᵖ 1⊗d_Q.
-/
def bifunctorAt : CochainComplex (ModuleCat.{v} R) ℤ ⥤
    CochainComplex (ModuleCat.{w} R) ℤ ⥤ CochainComplex (ModuleCat.{max v w} R) ℤ := by
  letI : ∀ (P : CochainComplex (ModuleCat.{v} R) ℤ)
      (Q : CochainComplex (ModuleCat.{w} R) ℤ),
      HomologicalComplex.HasMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ) :=
    fun P Q => by intro n; infer_instance
  exact (ModuleCat.tensorBifunctorAt R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)

/--
Let R be a commutative ring and P,Q integer cochain complexes of R-modules, whose carriers may
belong to independent universes. Their tensor complex has degree-n module ⊕_{p+q=n} Pᵖ ⊗_R Qᑫ.
On the summand indexed by (p,q), its differential is d_P⊗1 + (−1)ᵖ 1⊗d_Q.
-/
def complexAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) :
    CochainComplex (ModuleCat.{max v w} R) ℤ :=
  ((bifunctorAt R).obj P).obj Q

/--
Let R be a commutative ring and P,Q integer cochain complexes of R-modules, whose carriers may
belong to independent universes. For p,q,n ∈ ℤ with p+q=n, x ∈ Pᵖ and y ∈ Qᑫ, mkAt inserts
x⊗_R y into the (p,q)-summand of the degree-n tensor complex.
-/
def mkAt (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : Q.X q) :
    (complexAt R P Q).X n :=
  (HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
    p q n h).hom (x ⊗ₜ[R] y)

/--
Let R be a commutative ring and P,Q integer cochain complexes of R-modules, whose carriers may
belong to independent universes. For morphisms f : P → P' and g : Q → Q' of the corresponding
module complexes, their simultaneous tensor map sends the summand Pᵖ ⊗_R Qᑫ to P'ᵖ ⊗_R Q'ᑫ by
fᵖ⊗gᑫ and preserves total degree p+q.
-/
def mapAt {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    complexAt R P Q ⟶ complexAt R P' Q' :=
  HomologicalComplex.mapBifunctorMap f g (ModuleCat.tensorBifunctorAt R) (.up ℤ)

/--
Let R be a commutative ring and P,Q integer cochain complexes of R-modules, whose carriers may
belong to independent universes. Let f : P → P' and g : Q → Q', and fix p+q=n with x ∈ Pᵖ,y ∈
Qᑫ. The degree-n tensor map satisfies (f⊗g)(mkAt(x,y)) = mkAt(fᵖ(x),gᑫ(y)) in the same
(p,q)-summand.
-/
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

/-- Simultaneous tensor maps are the composite of the separate first and second maps,
for independently indexed coefficient universes. This is the native bifunctor composition law. -/
theorem mapAt_precomp_postcomp
    {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    mapAt R f (𝟙 Q) ≫ mapAt R (𝟙 P') g = mapAt R f g := by
  simpa only [mapAt, Category.comp_id, Category.id_comp] using
    (HomologicalComplex.mapBifunctorMap_comp (ModuleCat.tensorBifunctorAt R) (.up ℤ)
      f (𝟙 P') (𝟙 Q) g).symm

/--
Let R be a commutative ring and P,Q integer cochain complexes of R-modules, whose carriers may
belong to independent universes. For p+q=n and x ∈ Pᵖ,y ∈ Qᑫ, the total differential in degree
n sends mkAt(x,y) to mkAt(d_P x,y) + (−1)ᵖ mkAt(x,d_Q y), in summands (p+1,q) and (p,q+1) of
degree n+1.
-/
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
    HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) (p + 1) q (n + 1)
      (by change p + 1 + q = n + 1; omega)
  let j₂ : ModuleCat.tensorObjAt R (P.X p) (Q.X (q + 1)) ⟶ T :=
    HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p (q + 1) (n + 1)
      (by change p + (q + 1) = n + 1; omega)
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
  simp only [Units.smul_def] at hv
  change (K.d n (n + 1)).hom (i.hom (x ⊗ₜ[R] y)) =
    j₁.hom (((F.map (P.d p (p + 1))).app (Q.X q)).hom (x ⊗ₜ[R] y)) +
      (p.negOnePow : ℤ) •
        j₂.hom (((F.obj (P.X p)).map (Q.d q (q + 1))).hom (x ⊗ₜ[R] y)) at hv
  rw [hp, hq] at hv
  exact hv

end CochainComplex.ModuleTensor
