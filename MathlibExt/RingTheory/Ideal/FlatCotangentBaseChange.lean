/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Flat base change for conormal modules

For a flat algebra extension `R → T`, the scalar extension of `I/I²` is
identified with the conormal module of the image of `I` in `T`. The tensor
right unitor transports Mathlib's cotangent base-change map to this image
ideal. The resulting formula sends each ideal class to its scalar image.

The rings may be non-Noetherian, and the ideal may be zero or the whole ring.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w

namespace Ideal.Cotangent

variable (R : Type u) [CommRing R]
  {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Every element of the mapped ideal pulls back into the original ideal
through the actual inverse algebra equivalence. -/
theorem mappedIdeal_le_comap_inverse (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.map e.toRingHom ≤ I.comap e.symm.toRingHom := by
  intro y hy
  obtain ⟨x, hx, he⟩ :=
    (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hy
  change e.symm y ∈ I
  rw [← he]
  change e.symm (e x) ∈ I
  rw [e.symm_apply_apply]
  exact hx

/-- Native cotangent transport through an actual algebra isomorphism. -/
def equivOfAlgEquiv (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent ≃ₗ[R] (I.map e.toRingHom).Cotangent :=
  { Ideal.mapCotangent I (I.map e.toRingHom) e.toAlgHom
      (fun x hx => Ideal.mem_map_of_mem e.toRingHom hx) with
    invFun := Ideal.mapCotangent (I.map e.toRingHom) I e.symm.toAlgHom
      (mappedIdeal_le_comap_inverse R e I)
    left_inv := by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I x
      change I.toCotangent ⟨e.symm (e x), by
        simpa only [e.symm_apply_apply] using x.property⟩ = I.toCotangent x
      apply congrArg I.toCotangent
      apply Subtype.ext
      exact e.symm_apply_apply x
    right_inv := by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (I.map e.toRingHom) x
      change (I.map e.toRingHom).toCotangent ⟨e (e.symm x), by
        simpa only [e.apply_symm_apply] using x.property⟩ = (I.map e.toRingHom).toCotangent x
      apply congrArg (I.map e.toRingHom).toCotangent
      apply Subtype.ext
      exact e.apply_symm_apply x }

/-- Every native ideal class is sent to the class of its actual algebra image. -/
theorem equivOfAlgEquiv_toCotangent (e : A ≃ₐ[R] B) (I : Ideal A) (x : I) :
    equivOfAlgEquiv R e I (I.toCotangent x) =
      (I.map e.toRingHom).toCotangent
        ⟨e x, Ideal.mem_map_of_mem e.toRingHom x.property⟩ := rfl

end Ideal.Cotangent

namespace Ideal

variable (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
  (I : Ideal R)

/-- The actual tensor-right algebra unitor sends the extended ideal
onto its image under the original scalar map. -/
theorem cotangent_rightUnitor_mappedIdeal :
    (I.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* T ⊗[R] R)).map
        (Algebra.TensorProduct.rid R T T).toRingHom = I.map (algebraMap R T) := by
  rw [Ideal.map_map]
  have h : (Algebra.TensorProduct.rid R T T).toRingHom.comp
      (Algebra.TensorProduct.includeRight.toRingHom : R →+* T ⊗[R] R) = algebraMap R T := by
    ext r
    change Algebra.TensorProduct.rid R T T ((1 : T) ⊗ₜ[R] r) = algebraMap R T r
    simp only [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
  rw [h]

variable [Module.Flat R T]

/-- Flat scalar extension identifies the native base-changed conormal module
with the cotangent of the actual mapped ideal in T. -/
def flatCotangentBaseChangeEquiv :
    T ⊗[R] I.Cotangent ≃ₗ[T] (I.map (algebraMap R T)).Cotangent :=
  let J := I.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* T ⊗[R] R)
  let e := Algebra.TensorProduct.rid R T T
  (I.tensorCotangentEquiv R T).trans
    ((Cotangent.equivOfAlgEquiv T e J).trans
      (Cotangent.equivOfEq (J.map e.toRingHom) (I.map (algebraMap R T))
        (cotangent_rightUnitor_mappedIdeal R T I)))

/-- The resulting map retains the original class and its actual scalar image in T. -/
theorem flatCotangentBaseChangeEquiv_tmul_toCotangent (t : T) (x : I) :
    flatCotangentBaseChangeEquiv R T I (t ⊗ₜ[R] I.toCotangent x) =
      t • (I.map (algebraMap R T)).toCotangent
        ⟨algebraMap R T x, Ideal.mem_map_of_mem (algebraMap R T) x.property⟩ := by
  rw [flatCotangentBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, Ideal.tensorCotangentEquiv_tmul, map_smul, map_smul,
    Cotangent.equivOfAlgEquiv_toCotangent, Cotangent.equivOfEq_toCotangent]
  congr 2
  apply Subtype.ext
  simp only [LinearEquiv.coe_ofEq_apply, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]

end Ideal
