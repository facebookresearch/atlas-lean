/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ClassGroup.FiniteIdeleContent

@[expose] public section

open IsDedekindDomain

/-- Source consumer with the original binders. -/
private theorem exactSource (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ φ : (FiniteAdeleRing R K)ˣ →* ClassGroup R, Function.Surjective φ ∧
      φ.ker = FiniteAdeleRing.unitIdeles R K ⊔
        (Units.map (algebraMap K (FiniteAdeleRing R K) : K →*
          FiniteAdeleRing R K)).range :=
  FiniteAdeleRing.exists_monoidHom_units_classGroup_surjective_ker_eq R K

/-- The content homomorphism is the named witness, and it kills unit
ideles. -/
example (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {x : (FiniteAdeleRing R K)ˣ} (hx : x ∈ FiniteAdeleRing.unitIdeles R K) :
    FiniteAdeleRing.contentHom R K x = 1 :=
  FiniteAdeleRing.contentHom_eq_one_of_mem_unitIdeles R K hx

/-- The identity idele is a unit idele, proved through the carrier
definition: both `1` and `1⁻¹ = 1` are integral at every finite place. -/
example (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    (1 : (FiniteAdeleRing R K)ˣ) ∈ FiniteAdeleRing.unitIdeles R K := by
  rw [FiniteAdeleRing.mem_unitIdeles_iff]
  exact ⟨fun v => by rw [Units.val_one]; exact one_mem _,
    fun v => by rw [inv_one, Units.val_one]; exact one_mem _⟩
