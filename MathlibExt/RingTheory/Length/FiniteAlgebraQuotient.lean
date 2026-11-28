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

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite scalar length of genuine finite algebra quotients

The actual base quotient acts on the original algebra quotient through the
canonical quotient scalar map. Its finite length supplies both Artinian and
Noetherian structures, and the original finite generators remain generators
over the quotient. The stock surjective scalar length identity returns the
finite length over the original base. No reducedness or Noetherian hypothesis
on the original base is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v

namespace Module

/-- Let `R`, `A` be commutative rings in independent universes, with `A` a finite
`R`-algebra. Let `I ⊆ R`, `J ⊆ A` be ideals such that `I` maps into `J` under the
algebra map. If the `R`-module `R/I` has finite composition length, then so does
`A/J` as an `R`-module. The quotient rings retain their given ideal structures. -/
theorem length_algebraQuotient_ne_top_of_base_quotient
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] (I : Ideal R) (J : Ideal A)
    (hIJ : I ≤ J.comap (algebraMap R A))
    (hI : Module.length R (R ⧸ I) ≠ ⊤) :
    Module.length R (A ⧸ J) ≠ ⊤ := by
  let Rbar := R ⧸ I
  let Q := A ⧸ J
  let : Algebra Rbar Q := Ideal.Quotient.algebraQuotientOfLEComap hIJ
  let : IsScalarTower R Rbar Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfinite := isFiniteLength_iff_isNoetherian_isArtinian.mp
    (Module.length_ne_top_iff.mp hI)
  let : IsNoetherianRing Rbar := isNoetherian_of_tower R hfinite.1
  let : IsArtinianRing Rbar := isArtinian_of_tower R hfinite.2
  let : Module.Finite R Q := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R J).toLinearMap J.mkQ_surjective
  let : Module.Finite Rbar Q := Module.Finite.of_restrictScalars_finite R Rbar Q
  have hQ : Module.length Rbar Q ≠ ⊤ := Module.length_ne_top
  have he : Module.length R Q = Module.length Rbar Q :=
    Module.length_eq_of_surjective (R := Rbar) (S := R) (M := Q) I.mkQ_surjective
  rwa [← he] at hQ

end Module
