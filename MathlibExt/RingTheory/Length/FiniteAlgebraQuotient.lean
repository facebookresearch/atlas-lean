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
public import MathlibExt.RingTheory.Length.AnnihilatorQuotient
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite scalar length of genuine finite algebra quotients

A finite algebra quotient is a finite module over the original base ring. If a
base ideal maps into the quotient ideal, it annihilates that module. The general
annihilating-quotient length theorem then gives finite composition length from
finite length of the base quotient, without Noetherianity or reducedness of the
original ring.
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
  letI : Module.Finite R (A ⧸ J) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R J).toLinearMap J.mkQ_surjective
  apply Module.length_ne_top_of_finite_of_ideal_le_annihilator R (A ⧸ J) I ?_ hI
  intro r hr
  rw [Module.mem_annihilator]
  intro q
  have hz : algebraMap R (A ⧸ J) r = 0 :=
    ((Ideal.Quotient.mkₐ R J).commutes r).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hr))
  simp only [Algebra.smul_def, hz, zero_mul]

end Module
