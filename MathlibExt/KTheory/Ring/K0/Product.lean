/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import MathlibExt.Algebra.Category.FGProjectiveCat.Prod
public import MathlibExt.KTheory.Ring.K0.Projective
public import MathlibExt.KTheory.Exact.K0.Functor

/-!
# Algebraic `K₀` of a product ring

For arbitrary rings `R` and `S`, finite projective modules over `R × S`
split into their two central-idempotent components.  The exact component and
embedding functors induce mutually inverse additive maps

`RingK0 (R × S) ≃+ RingK0 R × RingK0 S`.

The construction uses only exact-category `K0.map`, its generator formula,
and the finite-projective biproduct decomposition.  In particular, no
noetherian or commutativity hypothesis is required for the equivalence.

For commutative rings, `prodEquiv_naturality` states naturality under arbitrary
pair maps `f.prodMap g`.  Commutativity is used only because the established
`RingK0.functor` base-change API is currently defined on `CommRingCat`.

No multiplicative equivalence, higher K-theory product theorem, spectrum
equivalence, or noncommutative base-change functor is asserted here.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe u

namespace AlgebraicKTheory
namespace RingK0

section Zero

variable {T : Type u} [Ring T]

private lemma mk_ofPUnit_eq_zero :
    (K0.mk (FGProjectiveCat.of (R := T) PUnit) : RingK0 T) = 0 := by
  apply K0.mk_eq_zero_of_isZero
  let _ : Subsingleton (FGProjectiveCat.of (R := T) PUnit : Type u) := inferInstance
  apply (IsZero.iff_id_eq_zero _).2
  apply FGProjectiveCat.hom_ext
  ext x

end Zero

section Maps

variable {R S : Type u} [Ring R] [Ring S]

/-- Map on `K₀` induced by embedding a first-factor finite projective module
through `RingHom.fst`. -/
noncomputable def prodFstEmbeddingHom : RingK0 R →+ RingK0 (R × S) :=
  K0.map (FGProjectiveCat.prodEmbeddingFst (R := R) (S := S))

/-- Map on `K₀` induced by embedding a second-factor finite projective module
through `RingHom.snd`. -/
noncomputable def prodSndEmbeddingHom : RingK0 S →+ RingK0 (R × S) :=
  K0.map (FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S))

/-- First idempotent component map on `K₀`. -/
noncomputable def prodFstComponentHom : RingK0 (R × S) →+ RingK0 R :=
  K0.map (ProdIdempotent.eComponentFunctorFGP (R := R) (S := S))

/-- Second idempotent component map on `K₀`. -/
noncomputable def prodSndComponentHom : RingK0 (R × S) →+ RingK0 S :=
  K0.map (ProdIdempotent.fComponentFunctorFGP (R := R) (S := S))

@[simp]
lemma prodFstEmbeddingHom_mk (M : FGProjectiveCat.{u} R) :
    prodFstEmbeddingHom (R := R) (S := S) (K0.mk M) =
      K0.mk ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj M) :=
  K0.map_mk _ M

@[simp]
lemma prodSndEmbeddingHom_mk (M : FGProjectiveCat.{u} S) :
    prodSndEmbeddingHom (R := R) (S := S) (K0.mk M) =
      K0.mk ((FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj M) :=
  K0.map_mk _ M

@[simp]
lemma prodFstComponentHom_mk (X : FGProjectiveCat.{u} (R × S)) :
    prodFstComponentHom (R := R) (S := S) (K0.mk X) =
      K0.mk ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj X) :=
  K0.map_mk _ X

@[simp]
lemma prodSndComponentHom_mk (X : FGProjectiveCat.{u} (R × S)) :
    prodSndComponentHom (R := R) (S := S) (K0.mk X) =
      K0.mk ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj X) :=
  K0.map_mk _ X

/-- Forward product map, given by the two idempotent components. -/
noncomputable def prodForwardHom : RingK0 (R × S) →+ RingK0 R × RingK0 S :=
  (prodFstComponentHom (R := R) (S := S)).prod
    (prodSndComponentHom (R := R) (S := S))

/-- Inverse product map, given by adding the two embedded classes. -/
noncomputable def prodInverseHom : RingK0 R × RingK0 S →+ RingK0 (R × S) :=
  (prodFstEmbeddingHom (R := R) (S := S)).coprod
    (prodSndEmbeddingHom (R := R) (S := S))

@[simp]
lemma prodForwardHom_mk (X : FGProjectiveCat.{u} (R × S)) :
    prodForwardHom (R := R) (S := S) (K0.mk X) =
      (K0.mk ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj X),
       K0.mk ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj X)) := by
  apply Prod.ext <;> simp [prodForwardHom]

@[simp]
lemma prodInverseHom_apply (a : RingK0 R) (b : RingK0 S) :
    prodInverseHom (R := R) (S := S) (a, b) =
      prodFstEmbeddingHom (R := R) (S := S) a +
        prodSndEmbeddingHom (R := R) (S := S) b :=
  rfl

end Maps

section ComponentEmbedding

variable {R S : Type u} [Ring R] [Ring S]

private lemma comp_fst_embFst_eq_id :
    (prodFstComponentHom (R := R) (S := S)).comp
        (prodFstEmbeddingHom (R := R) (S := S)) = AddMonoidHom.id _ := by
  apply K0.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
    prodFstEmbeddingHom_mk, prodFstComponentHom_mk]
  exact K0.mk_congr_of_iso (ProdIdempotent.prodEmbeddingFst_eComponentFGPIso M)

private lemma comp_fst_embSnd_eq_zero :
    (prodFstComponentHom (R := R) (S := S)).comp
        (prodSndEmbeddingHom (R := R) (S := S)) = 0 := by
  apply K0.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    prodSndEmbeddingHom_mk, prodFstComponentHom_mk]
  calc
    K0.mk ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj
        ((FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj M)) =
        K0.mk (FGProjectiveCat.of (R := R) PUnit) :=
      K0.mk_congr_of_iso (ProdIdempotent.prodEmbeddingSnd_eComponentFGPZeroIso M)
    _ = 0 := mk_ofPUnit_eq_zero

private lemma comp_snd_embFst_eq_zero :
    (prodSndComponentHom (R := R) (S := S)).comp
        (prodFstEmbeddingHom (R := R) (S := S)) = 0 := by
  apply K0.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    prodFstEmbeddingHom_mk, prodSndComponentHom_mk]
  calc
    K0.mk ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj
        ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj M)) =
        K0.mk (FGProjectiveCat.of (R := S) PUnit) :=
      K0.mk_congr_of_iso (ProdIdempotent.prodEmbeddingFst_fComponentFGPZeroIso M)
    _ = 0 := mk_ofPUnit_eq_zero

private lemma comp_snd_embSnd_eq_id :
    (prodSndComponentHom (R := R) (S := S)).comp
        (prodSndEmbeddingHom (R := R) (S := S)) = AddMonoidHom.id _ := by
  apply K0.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
    prodSndEmbeddingHom_mk, prodSndComponentHom_mk]
  exact K0.mk_congr_of_iso (ProdIdempotent.prodEmbeddingSnd_fComponentFGPIso M)

private lemma prodInverseHom_comp_prodForwardHom_eq :
    (prodInverseHom (R := R) (S := S)).comp
        (prodForwardHom (R := R) (S := S)) = AddMonoidHom.id _ := by
  apply K0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, prodForwardHom_mk,
    prodInverseHom_apply, prodFstEmbeddingHom_mk, prodSndEmbeddingHom_mk]
  rw [← K0.mk_biprod]
  exact K0.mk_congr_of_iso
    (FGProjectiveCat.Prod.decompositionIso (R := R) (S := S) X).symm

end ComponentEmbedding

section Equivalence

variable {R S : Type u} [Ring R] [Ring S]

/-- Additive product formula for projective-module algebraic `K₀`.

The theorem is valid for arbitrary rings.  The forward map takes idempotent
components and the inverse adds the two projection-restricted modules. -/
noncomputable def prodEquiv : RingK0 (R × S) ≃+ RingK0 R × RingK0 S where
  toFun := prodForwardHom (R := R) (S := S)
  invFun := prodInverseHom (R := R) (S := S)
  left_inv x := by
    exact DFunLike.congr_fun prodInverseHom_comp_prodForwardHom_eq x
  right_inv p := by
    obtain ⟨a, b⟩ := p
    apply Prod.ext
    · change prodFstComponentHom (R := R) (S := S)
        (prodFstEmbeddingHom (R := R) (S := S) a +
          prodSndEmbeddingHom (R := R) (S := S) b) = a
      rw [map_add]
      change ((prodFstComponentHom (R := R) (S := S)).comp
          (prodFstEmbeddingHom (R := R) (S := S))) a +
        ((prodFstComponentHom (R := R) (S := S)).comp
          (prodSndEmbeddingHom (R := R) (S := S))) b = a
      rw [comp_fst_embFst_eq_id, comp_fst_embSnd_eq_zero]
      simp
    · change prodSndComponentHom (R := R) (S := S)
        (prodFstEmbeddingHom (R := R) (S := S) a +
          prodSndEmbeddingHom (R := R) (S := S) b) = b
      rw [map_add]
      change ((prodSndComponentHom (R := R) (S := S)).comp
          (prodFstEmbeddingHom (R := R) (S := S))) a +
        ((prodSndComponentHom (R := R) (S := S)).comp
          (prodSndEmbeddingHom (R := R) (S := S))) b = b
      rw [comp_snd_embFst_eq_zero, comp_snd_embSnd_eq_id]
      simp
  map_add' := map_add (prodForwardHom (R := R) (S := S))

@[simp]
lemma prodEquiv_apply_mk (X : FGProjectiveCat.{u} (R × S)) :
    prodEquiv (R := R) (S := S) (K0.mk X) =
      (K0.mk ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj X),
       K0.mk ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj X)) :=
  prodForwardHom_mk X

@[simp]
lemma prodEquiv_symm_apply (a : RingK0 R) (b : RingK0 S) :
    (prodEquiv (R := R) (S := S)).symm (a, b) =
      prodFstEmbeddingHom (R := R) (S := S) a +
        prodSndEmbeddingHom (R := R) (S := S) b :=
  rfl

@[simp]
lemma prodEquiv_symm_apply_mk (M : FGProjectiveCat.{u} R)
    (N : FGProjectiveCat.{u} S) :
    (prodEquiv (R := R) (S := S)).symm (K0.mk M, K0.mk N) =
      K0.mk ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj M) +
        K0.mk ((FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj N) := by
  simp only [prodEquiv_symm_apply, prodFstEmbeddingHom_mk, prodSndEmbeddingHom_mk]

end Equivalence

section Naturality

variable {R S R' S' : Type u}
  [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- The first component map is base change along the first projection. -/
theorem prodFstComponentHom_eq_functor_map :
    prodFstComponentHom (R := R) (S := S) =
      (RingK0.functor.map (CommRingCat.ofHom (RingHom.fst R S))).hom.toAddMonoidHom := by
  change K0.map (ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)) =
    K0.map (FGProjectiveCat.baseChange (RingHom.fst R S))
  exact (K0.map_eq_of_iso
    (ProdIdempotent.baseChangeFstIsoEComponentFGP (R := R) (S := S))).symm

/-- The second component map is base change along the second projection. -/
theorem prodSndComponentHom_eq_functor_map :
    prodSndComponentHom (R := R) (S := S) =
      (RingK0.functor.map (CommRingCat.ofHom (RingHom.snd R S))).hom.toAddMonoidHom := by
  change K0.map (ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)) =
    K0.map (FGProjectiveCat.baseChange (RingHom.snd R S))
  exact (K0.map_eq_of_iso
    (ProdIdempotent.baseChangeSndIsoFComponentFGP (R := R) (S := S))).symm

/-- Naturality of the product decomposition under arbitrary pairs of
commutative ring maps.  The product map is applied first on the left; on the
right, the two factor maps are applied after splitting. -/
theorem prodEquiv_naturality (f : R →+* R') (g : S →+* S') :
    (prodEquiv (R := R') (S := S')).toAddMonoidHom.comp
        (RingK0.functor.map (CommRingCat.ofHom (f.prodMap g))).hom.toAddMonoidHom =
      (AddMonoidHom.prodMap
        (RingK0.functor.map (CommRingCat.ofHom f)).hom.toAddMonoidHom
        (RingK0.functor.map (CommRingCat.ofHom g)).hom.toAddMonoidHom).comp
          (prodEquiv (R := R) (S := S)).toAddMonoidHom := by
  rw [show (prodEquiv (R := R') (S := S')).toAddMonoidHom =
      prodForwardHom (R := R') (S := S') from rfl,
    show (prodEquiv (R := R) (S := S)).toAddMonoidHom =
      prodForwardHom (R := R) (S := S) from rfl]
  rw [show prodForwardHom (R := R') (S := S') =
      (prodFstComponentHom (R := R') (S := S')).prod
        (prodSndComponentHom (R := R') (S := S')) from rfl,
    show prodForwardHom (R := R) (S := S) =
      (prodFstComponentHom (R := R) (S := S)).prod
        (prodSndComponentHom (R := R) (S := S)) from rfl,
    prodFstComponentHom_eq_functor_map (R := R') (S := S'),
    prodSndComponentHom_eq_functor_map (R := R') (S := S'),
    prodFstComponentHom_eq_functor_map (R := R) (S := S),
    prodSndComponentHom_eq_functor_map (R := R) (S := S)]
  apply AddMonoidHom.ext
  intro x
  apply Prod.ext
  · change (RingK0.functor.map
        (CommRingCat.ofHom (RingHom.fst R' S')))
        ((RingK0.functor.map (CommRingCat.ofHom (f.prodMap g))) x) =
      (RingK0.functor.map (CommRingCat.ofHom f))
        ((RingK0.functor.map (CommRingCat.ofHom (RingHom.fst R S))) x)
    have hRing : (RingHom.fst R' S').comp (f.prodMap g) =
        f.comp (RingHom.fst R S) := by
      ext p
      rfl
    have hCat : (CommRingCat.ofHom (f.prodMap g) ≫
        CommRingCat.ofHom (RingHom.fst R' S')) =
        (CommRingCat.ofHom (RingHom.fst R S) ≫ CommRingCat.ofHom f) := by
      ext p
      exact congr_fun (congrArg DFunLike.coe hRing) p
    have hMap := congrArg (fun k => k x)
      (congrArg RingK0.functor.map hCat)
    simpa only [RingK0.functor.map_comp, CommRingCat.comp_apply] using hMap
  · change (RingK0.functor.map
        (CommRingCat.ofHom (RingHom.snd R' S')))
        ((RingK0.functor.map (CommRingCat.ofHom (f.prodMap g))) x) =
      (RingK0.functor.map (CommRingCat.ofHom g))
        ((RingK0.functor.map (CommRingCat.ofHom (RingHom.snd R S))) x)
    have hRing : (RingHom.snd R' S').comp (f.prodMap g) =
        g.comp (RingHom.snd R S) := by
      ext p
      rfl
    have hCat : (CommRingCat.ofHom (f.prodMap g) ≫
        CommRingCat.ofHom (RingHom.snd R' S')) =
        (CommRingCat.ofHom (RingHom.snd R S) ≫ CommRingCat.ofHom g) := by
      ext p
      exact congr_fun (congrArg DFunLike.coe hRing) p
    have hMap := congrArg (fun k => k x)
      (congrArg RingK0.functor.map hCat)
    simpa only [RingK0.functor.map_comp, CommRingCat.comp_apply] using hMap

/-- Pointwise form of `prodEquiv_naturality`. -/
theorem prodEquiv_naturality_apply (f : R →+* R') (g : S →+* S')
    (x : RingK0 (R × S)) :
    prodEquiv (R := R') (S := S')
        ((RingK0.functor.map (CommRingCat.ofHom (f.prodMap g))) x) =
      ((RingK0.functor.map (CommRingCat.ofHom f))
          (prodEquiv (R := R) (S := S) x).1,
       (RingK0.functor.map (CommRingCat.ofHom g))
          (prodEquiv (R := R) (S := S) x).2) :=
  DFunLike.congr_fun (prodEquiv_naturality f g) x

end Naturality

end RingK0
end AlgebraicKTheory

end
