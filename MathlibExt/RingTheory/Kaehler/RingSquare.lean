/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Native Kähler transport for an actual square of ground-ring maps

The input is an actual pair of ring homomorphisms k→K and P→Q together with
their commuting algebra square. The induced dictionaries are constructed
from those maps and that equation. Native `KaehlerDifferential.map` then
gives the genuine semilinear differential map, retaining its actual
generator formula. All four carrier universes are independent.

The auxiliary subtype is an output of the native construction, with its
native generator proof; callers supply no differential map or comparison
certificate. Source: Stacks Project 92.6--92.7. Candidate source; UNEXECUTED.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace KaehlerDifferential

variable (k : Type u) (K : Type v) (P : Type w) (Q : Type t)
  [CommRing k] [CommRing K] [CommRing P] [CommRing Q]
  [Algebra k P] [Algebra K Q]

/-- The native semilinear differential map together with its generator equation,
constructed from the original commuting square of ground and algebra ring maps. -/
def mapOfRingSquareData (fk : k →+* K) (fP : P →+* Q)
    (hs : fP.comp (algebraMap k P) = (algebraMap K Q).comp fk) :
    { f : KaehlerDifferential k P →ₛₗ[fP] KaehlerDifferential K Q //
      ∀ p : P, f (KaehlerDifferential.D k P p) = KaehlerDifferential.D K Q (fP p) } := by
  letI : Algebra k K := fk.toAlgebra
  letI : Algebra P Q := fP.toAlgebra
  letI : Algebra k Q := ((algebraMap K Q).comp fk).toAlgebra
  letI : IsScalarTower k K Q := ⟨by
    intro r s q
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      RingHom.comp_apply, map_mul]
    exact mul_assoc _ _ _⟩
  letI : IsScalarTower k P Q := ⟨by
    intro r p q
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      RingHom.comp_apply, map_mul]
    have h := RingHom.congr_fun hs r
    change fP (algebraMap k P r) = algebraMap K Q (fk r) at h
    rw [h, mul_assoc]⟩
  letI : SMulCommClass K P Q := ⟨by
    intro r p q
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact mul_left_comm _ _ _⟩
  let l := KaehlerDifferential.map k K P Q
  refine ⟨
    { toFun := l
      map_add' := l.map_add
      map_smul' := ?_ }, ?_⟩
  · intro p ω
    have h : fP p • l ω = p • l ω := by
      simpa only [RingHom.algebraMap_toAlgebra] using
        IsScalarTower.algebraMap_smul (R := P) (A := Q) p (l ω)
    exact (l.map_smul p ω).trans h.symm
  · intro p
    exact KaehlerDifferential.map_D k K P Q p

/-- The actual semilinear map of native differentials for the original ground-ring square. -/
def mapOfRingSquare (fk : k →+* K) (fP : P →+* Q)
    (hs : fP.comp (algebraMap k P) = (algebraMap K Q).comp fk) :
    KaehlerDifferential k P →ₛₗ[fP] KaehlerDifferential K Q :=
  (mapOfRingSquareData k K P Q fk fP hs).val

@[simp]
theorem mapOfRingSquare_D (fk : k →+* K) (fP : P →+* Q)
    (hs : fP.comp (algebraMap k P) = (algebraMap K Q).comp fk) (p : P) :
    mapOfRingSquare k K P Q fk fP hs (KaehlerDifferential.D k P p) =
      KaehlerDifferential.D K Q (fP p) :=
  (mapOfRingSquareData k K P Q fk fP hs).property p

end KaehlerDifferential

end
