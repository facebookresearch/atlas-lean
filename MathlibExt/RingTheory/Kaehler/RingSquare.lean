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
# Kähler differential maps from commuting ring squares

Let k,P and K,Q be commutative rings with k-algebra P and K-algebra Q. Ring maps f_k : k → K
and f_P : P → Q satisfying f_P ∘ algebraMap(k,P) = algebraMap(K,Q) ∘ f_k induce an
f_P-semilinear map Ω_{P/k} → Ω_{Q/K}.

Its generator formula is d_{P/k}(p) ↦ d_{Q/K}(f_P(p)). The construction records both the map
and this equation, then exposes the underlying semilinear map. All four ring universes are
independent.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace KaehlerDifferential

variable (k : Type u) (K : Type v) (P : Type w) (Q : Type t)
  [CommRing k] [CommRing K] [CommRing P] [CommRing Q]
  [Algebra k P] [Algebra K Q]

/-- Semilinear Kähler map with its differential-generator equation.

For a commuting square of ring maps f_k : k → K and f_P : P → Q, construct an f_P-semilinear
map Ω_{P/k} → Ω_{Q/K} together with the equation f(d p)=d(f_P(p)) for every p ∈ P. -/
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

/-- Semilinear Kähler map of a commuting ring square.

For commutative rings and maps f_k,f_P commuting with the given algebra maps, mapOfRingSquare
is the induced f_P-semilinear differential map Ω_{P/k} → Ω_{Q/K}. -/
def mapOfRingSquare (fk : k →+* K) (fP : P →+* Q)
    (hs : fP.comp (algebraMap k P) = (algebraMap K Q).comp fk) :
    KaehlerDifferential k P →ₛₗ[fP] KaehlerDifferential K Q :=
  (mapOfRingSquareData k K P Q fk fP hs).val

/-- Differential-generator value of a ring-square map.

For p ∈ P, the induced map of Kähler differentials satisfies mapOfRingSquare(d_{P/k}p) =
d_{Q/K}(f_P(p)). -/
@[simp]
theorem mapOfRingSquare_D (fk : k →+* K) (fP : P →+* Q)
    (hs : fP.comp (algebraMap k P) = (algebraMap K Q).comp fk) (p : P) :
    mapOfRingSquare k K P Q fk fP hs (KaehlerDifferential.D k P p) =
      KaehlerDifferential.D K Q (fP p) :=
  (mapOfRingSquareData k K P Q fk fP hs).property p

end KaehlerDifferential

end
