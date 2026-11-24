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

public import MathlibExt.KTheory.Ring.K1.Basic
public import MathlibExt.KTheory.Ring.K1.StableDeterminantProperties

/-! # K₁ determinant homomorphism and natural transformation

For a commutative ring `R`, the stable determinant `StableGL.det : StableGL R →* Rˣ`
factors through the abelianization defining `K₁`.  Its additive version is
`K1.detHom`.  Functoriality via `StableGL.det_mapRingHom` and
`K1.functor_map_proj` yields a natural transformation
`K1.determinant : commRingFunctor ⟶ unitsFunctor`.  Surjectivity follows from
`StableGL.det_surjective`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory

noncomputable section

/-- `K₁` restricted from `RingCat` to `CommRingCat`. -/
noncomputable def K1.commRingFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat RingCat ⋙ K1.functor

/-- Units functor `CommRingCat ⥤ AddCommGrpCat` via `CommMonCat.units`
followed by `CommGrpCat.toAddCommGrp`. -/
noncomputable def K1.unitsFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp

/-- Determinant homomorphism `K₁ R →+ Additive Rˣ` induced by
`Abelianization.lift (StableGL.det)`. -/
noncomputable def K1.detHom (R : Type u) [CommRing R] : K1 R →+ Additive Rˣ :=
  (Abelianization.lift (StableGL.det (R := R))).toAdditive

@[simp]
theorem K1.detHom_proj {R : Type u} [CommRing R] (g : StableGL R) :
    K1.detHom (R := R) (K1.proj g) = Additive.ofMul (StableGL.det (R := R) g) :=
  rfl

@[simp]
theorem K1.detHom_mk {R : Type u} [CommRing R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.detHom (R := R) (K1.mk g) =
      Additive.ofMul (Matrix.GeneralLinearGroup.det g) := by
  change K1.detHom (R := R) (K1.proj (StableGL.of g)) = _
  rw [K1.detHom_proj, StableGL.det_of]

theorem K1.detHom_surjective (R : Type u) [CommRing R] :
    Function.Surjective (K1.detHom (R := R)) := by
  intro y
  obtain ⟨g, hg⟩ := StableGL.det_surjective (R := R) (Additive.toMul y)
  refine ⟨K1.proj g, ?_⟩
  calc K1.detHom (R := R) (K1.proj g)
      = Additive.ofMul (StableGL.det (R := R) g) := rfl
    _ = Additive.ofMul (Additive.toMul y) := by rw [hg]
    _ = y := ofMul_toMul y

/-- If the commutator subgroup equals the kernel of `StableGL.det`,
    then `K1.detHom` is injective. -/
theorem K1.detHom_injective_of_commutator_eq_ker {R : Type u} [CommRing R]
    (hCommKer : commutator (StableGL R) = MonoidHom.ker (StableGL.det (R := R))) :
    Function.Injective (K1.detHom (R := R)) := by
  have hLiftInjective : Function.Injective (Abelianization.lift (StableGL.det (R := R))) :=
    (QuotientGroup.injective_lift_iff (commutator (StableGL R)) (StableGL.det (R := R))
      (Abelianization.commutator_subset_ker _)).mpr hCommKer
  intro x y hxy
  have h1 : Additive.ofMul (Abelianization.lift (StableGL.det (R := R)) (Additive.toMul x)) =
      Additive.ofMul (Abelianization.lift (StableGL.det (R := R)) (Additive.toMul y)) := hxy
  have h2 : Abelianization.lift (StableGL.det (R := R)) (Additive.toMul x) =
      Abelianization.lift (StableGL.det (R := R)) (Additive.toMul y) := by
    have h := congrArg (Additive.toMul (α := Rˣ)) h1
    simpa using h
  have h3 : Additive.toMul x = Additive.toMul y := hLiftInjective h2
  exact (Additive.toMul (α := Abelianization (StableGL R))).injective h3

/-- Determinant natural transformation `K₁ ⇒ Units` on `CommRingCat`. -/
noncomputable def K1.determinant : K1.commRingFunctor.{u} ⟶ K1.unitsFunctor.{u} where
  app R := AddCommGrpCat.ofHom (K1.detHom R.carrier)
  naturality R S f := by
    apply AddCommGrpCat.hom_ext
    ext x
    obtain ⟨g, rfl⟩ := K1.proj_surjective R.carrier x
    have h_comm : (K1.commRingFunctor.map f) (K1.proj g) =
        K1.proj ((StableGL.functor.map (SemiRingCat.ofHom f.hom)) g) := by
      have h1 : (K1.commRingFunctor.map f) (K1.proj g) =
          (K1.functor.map (RingCat.ofHom f.hom)) (K1.proj g) := rfl
      rw [h1]
      exact K1.functor_map_proj f.hom g
    have h : (K1.commRingFunctor.map f ≫
        AddCommGrpCat.ofHom (K1.detHom S.carrier)) (K1.proj g) =
        (AddCommGrpCat.ofHom (K1.detHom R.carrier) ≫
          K1.unitsFunctor.map f) (K1.proj g) := by
      have hA : (K1.commRingFunctor.map f ≫
          AddCommGrpCat.ofHom (K1.detHom S.carrier)) (K1.proj g) =
          (K1.detHom S.carrier) ((K1.commRingFunctor.map f) (K1.proj g)) := rfl
      have hC : (K1.detHom S.carrier) ((K1.commRingFunctor.map f) (K1.proj g)) =
          (K1.detHom S.carrier)
            (K1.proj ((StableGL.functor.map (SemiRingCat.ofHom f.hom)) g)) := by
        rw [h_comm]
      have hD : (K1.detHom S.carrier)
            (K1.proj ((StableGL.functor.map (SemiRingCat.ofHom f.hom)) g)) =
          Additive.ofMul (StableGL.det (R := S.carrier)
            ((StableGL.functor.map (SemiRingCat.ofHom f.hom)) g)) := rfl
      have hE : Additive.ofMul (StableGL.det (R := S.carrier)
            ((StableGL.functor.map (SemiRingCat.ofHom f.hom)) g)) =
          Additive.ofMul ((StableGL.det (R := R.carrier) g).map f.hom.toMonoidHom) := by
        rw [StableGL.det_mapRingHom f.hom g]
      have hF : Additive.ofMul ((StableGL.det (R := R.carrier) g).map f.hom.toMonoidHom) =
          (K1.unitsFunctor.map f) (K1.detHom R.carrier (K1.proj g)) := rfl
      exact hA.trans (hC.trans (hD.trans (hE.trans hF)))
    exact h

@[simp]
theorem K1.determinant_app (R : CommRingCat.{u}) :
    K1.determinant.app R = AddCommGrpCat.ofHom (K1.detHom R.carrier) :=
  rfl

theorem K1.determinant_app_apply (R : CommRingCat.{u}) (x : K1 R.carrier) :
    K1.determinant.app R x = K1.detHom R.carrier x :=
  rfl

end

end AlgebraicKTheory

end
