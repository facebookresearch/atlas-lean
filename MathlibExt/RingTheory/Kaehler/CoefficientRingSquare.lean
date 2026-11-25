/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Kaehler.Coefficient
public import MathlibExt.RingTheory.Kaehler.RingSquare
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Actual ground-ring squares for extended differentials

An input square consists only of the original ring homomorphisms and the two
commuting squares k→P→A and K→Q→B. The native semilinear differential map
and the native semilinear tensor map construct the actual coefficient map
`a ⊗ dp ↦ fA(a) ⊗ d(fP(p))`. Its coefficient semilinearity is proved from
the native tensor formula, and the native extension adjunction constructs
the corresponding B-linear map after actual extension along A→B.

The coefficient map preserves identities and composites by the actual
differential generators. All six ring universes, and the extensionality
target module universe, are independent. No exactness, independence,
flatness or desired cotangent comparison is supplied by a caller.

This is the genuine degreewise transport provider. Canonical polynomial
ground-change maps, their full simplicial coherence and flat derived base
change remain separate obligations. Source: Stacks Project 92.6--92.7;
Loday 3.5.4, 3.5.6--3.5.8.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uk uK uP uQ uA uB uM

namespace KaehlerDifferential

variable (k : Type uk) (K : Type uK) (P : Type uP) (Q : Type uQ)
  (A : Type uA) (B : Type uB)
  [CommRing k] [CommRing K] [CommRing P] [CommRing Q] [CommRing A] [CommRing B]
  [Algebra k P] [Algebra K Q] [Algebra P A] [Algebra Q B]

/-- Only the original maps and actual commuting squares form the transport input. -/
structure CoefficientRingSquare where
  ground : k →+* K
  algebra : P →+* Q
  coefficient : A →+* B
  ground_commutes : algebra.comp (algebraMap k P) = (algebraMap K Q).comp ground
  augmentation_commutes : coefficient.comp (algebraMap P A) =
    (algebraMap Q B).comp algebra

variable {k K P Q A B}

/-- The actual identity diagram of the original ring tower. -/
def CoefficientRingSquare.id : CoefficientRingSquare k k P P A A where
  ground := RingHom.id k
  algebra := RingHom.id P
  coefficient := RingHom.id A
  ground_commutes := by ext r; rfl
  augmentation_commutes := by ext p; rfl

/-- Compose the actual maps and their original commuting equations. -/
def CoefficientRingSquare.comp
    {K' : Type*} {Q' : Type*} {B' : Type*}
    [CommRing K'] [CommRing Q'] [CommRing B'] [Algebra K' Q'] [Algebra Q' B']
    (s : CoefficientRingSquare k K P Q A B)
    (t : CoefficientRingSquare K K' Q Q' B B') :
    CoefficientRingSquare k K' P Q' A B' where
  ground := t.ground.comp s.ground
  algebra := t.algebra.comp s.algebra
  coefficient := t.coefficient.comp s.coefficient
  ground_commutes := by
    ext r
    change t.algebra (s.algebra (algebraMap k P r)) =
      algebraMap K' Q' (t.ground (s.ground r))
    have hs := RingHom.congr_fun s.ground_commutes r
    have ht := RingHom.congr_fun t.ground_commutes (s.ground r)
    change s.algebra (algebraMap k P r) = algebraMap K Q (s.ground r) at hs
    change t.algebra (algebraMap K Q (s.ground r)) =
      algebraMap K' Q' (t.ground (s.ground r)) at ht
    exact (congrArg t.algebra hs).trans ht
  augmentation_commutes := by
    ext p
    change t.coefficient (s.coefficient (algebraMap P A p)) =
      algebraMap Q' B' (t.algebra (s.algebra p))
    have hs := RingHom.congr_fun s.augmentation_commutes p
    have ht := RingHom.congr_fun t.augmentation_commutes (s.algebra p)
    change s.coefficient (algebraMap P A p) = algebraMap Q B (s.algebra p) at hs
    change t.coefficient (algebraMap Q B (s.algebra p)) =
      algebraMap Q' B' (t.algebra (s.algebra p)) at ht
    exact (congrArg t.coefficient hs).trans ht

/-- Native semilinear tensor map, with coefficient semilinearity earned on its actual tensors. -/
def coefficientMapOfRingSquare (s : CoefficientRingSquare k K P Q A B) :
    Coefficient k P A →ₛₗ[s.coefficient] Coefficient K Q B := by
  let f : A →ₛₗ[s.algebra] B :=
    { toFun := s.coefficient
      map_add' := s.coefficient.map_add
      map_smul' := by
        intro p a
        simp only [Algebra.smul_def, map_mul]
        have h := RingHom.congr_fun s.augmentation_commutes p
        change s.coefficient (algebraMap P A p) = algebraMap Q B (s.algebra p) at h
        exact congrArg (fun b => b * s.coefficient a) h }
  let d := mapOfRingSquare k K P Q s.ground s.algebra s.ground_commutes
  let T := TensorProduct.map f d
  exact
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul b ω =>
          change T ((a * b) ⊗ₜ[P] ω) = s.coefficient a • T (b ⊗ₜ[P] ω)
          rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
          change s.coefficient (a * b) ⊗ₜ[Q] d ω =
            s.coefficient a • (s.coefficient b ⊗ₜ[Q] d ω)
          rw [map_mul, TensorProduct.smul_tmul']
          rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

@[simp]
theorem coefficientMapOfRingSquare_tmul_D
    (s : CoefficientRingSquare k K P Q A B) (a : A) (p : P) :
    coefficientMapOfRingSquare s (a ⊗ₜ[P] KaehlerDifferential.D k P p) =
      s.coefficient a ⊗ₜ[Q] KaehlerDifferential.D K Q (s.algebra p) := by
  change s.coefficient a ⊗ₜ[Q]
    mapOfRingSquare k K P Q s.ground s.algebra s.ground_commutes
      (KaehlerDifferential.D k P p) = _
  rw [mapOfRingSquare_D]

/-- Differential tensors determine every actual semilinear coefficient map. -/
theorem coefficientSemilinear_hom_ext
    {C : Type*} [CommRing C] {M : Type uM} [AddCommGroup M] [Module C M]
    {σ : A →+* C} {f g : Coefficient k P A →ₛₗ[σ] M}
    (h : ∀ p : P, f ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p) =
      g ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p)) : f = g := by
  letI : Module A M := Module.compHom M σ
  let f' : Coefficient k P A →ₗ[A] M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smulₛₗ }
  let g' : Coefficient k P A →ₗ[A] M :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := g.map_smulₛₗ }
  letI : Algebra k A := ((algebraMap P A).comp (algebraMap k P)).toAlgebra
  letI : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' (by
    exact RingHom.algebraMap_toAlgebra _)
  have he : f' = g' := coefficient_hom_ext k P A h
  ext x
  exact LinearMap.congr_fun he x

@[simp]
theorem coefficientMapOfRingSquare_id :
    coefficientMapOfRingSquare (CoefficientRingSquare.id (k := k) (P := P) (A := A)) =
      (LinearMap.id : Coefficient k P A →ₗ[A] Coefficient k P A) := by
  apply coefficientSemilinear_hom_ext
  intro p
  rw [coefficientMapOfRingSquare_tmul_D]
  rfl

/-- The map of the actual composite diagram is the composite of the actual semilinear maps. -/
theorem coefficientMapOfRingSquare_comp
    {K' : Type*} {Q' : Type*} {B' : Type*}
    [CommRing K'] [CommRing Q'] [CommRing B'] [Algebra K' Q'] [Algebra Q' B']
    (s : CoefficientRingSquare k K P Q A B)
    (t : CoefficientRingSquare K K' Q Q' B B') :
    letI : RingHomCompTriple s.coefficient t.coefficient
        (t.coefficient.comp s.coefficient) := ⟨rfl⟩
    coefficientMapOfRingSquare (s.comp t) =
      (coefficientMapOfRingSquare t).comp (σ₁₃ := t.coefficient.comp s.coefficient)
        (coefficientMapOfRingSquare s) := by
  letI : RingHomCompTriple s.coefficient t.coefficient
      (t.coefficient.comp s.coefficient) := ⟨rfl⟩
  apply coefficientSemilinear_hom_ext
  intro p
  have hL := coefficientMapOfRingSquare_tmul_D (s.comp t) (1 : A) p
  have hS := coefficientMapOfRingSquare_tmul_D s (1 : A) p
  have hT := coefficientMapOfRingSquare_tmul_D t (s.coefficient 1) (s.algebra p)
  have hR := (congrArg (coefficientMapOfRingSquare t) hS).trans hT
  have hOne : t.coefficient (s.coefficient 1) = (1 : B') :=
    (congrArg t.coefficient s.coefficient.map_one).trans t.coefficient.map_one
  have hR' := hR.trans
    (congrArg (fun a : B' => a ⊗ₜ[Q'] KaehlerDifferential.D K' Q' (t.algebra (s.algebra p))) hOne)
  have hL' := hL.trans
    (congrArg (fun a : B' => a ⊗ₜ[Q'] KaehlerDifferential.D K' Q' (t.algebra (s.algebra p))) hOne)
  exact hL'.trans hR'.symm

/-- Native extension of scalars turns the actual semilinear map into the genuine B-linear map. -/
def coefficientBaseChangeMapOfRingSquare (s : CoefficientRingSquare k K P Q A B) :
    letI : Algebra A B := s.coefficient.toAlgebra
    (B ⊗[A] Coefficient k P A) →ₗ[B] Coefficient K Q B := by
  letI : Algebra A B := s.coefficient.toAlgebra
  letI : Module A (Coefficient K Q B) := Module.compHom (Coefficient K Q B) s.coefficient
  letI hTower : IsScalarTower A B (Coefficient K Q B) := IsScalarTower.of_compHom A B (Coefficient K Q B)
  let l : Coefficient k P A →ₗ[A] Coefficient K Q B :=
    { toFun := coefficientMapOfRingSquare s
      map_add' := (coefficientMapOfRingSquare s).map_add
      map_smul' := (coefficientMapOfRingSquare s).map_smulₛₗ }
  exact @LinearMap.liftBaseChange A (Coefficient k P A) (Coefficient K Q B) B
    _ _ _ _ _ _ _ _ hTower l

theorem coefficientBaseChangeMapOfRingSquare_tmul_D
    (s : CoefficientRingSquare k K P Q A B) (b : B) (a : A) (p : P) :
    letI : Algebra A B := s.coefficient.toAlgebra
    coefficientBaseChangeMapOfRingSquare s
      (b ⊗ₜ[A] (a ⊗ₜ[P] KaehlerDifferential.D k P p)) =
        (b * s.coefficient a) ⊗ₜ[Q] KaehlerDifferential.D K Q (s.algebra p) := by
  letI : Algebra A B := s.coefficient.toAlgebra
  dsimp only [coefficientBaseChangeMapOfRingSquare]
  simp only [LinearMap.liftBaseChange_tmul]
  change b • coefficientMapOfRingSquare s (a ⊗ₜ[P] KaehlerDifferential.D k P p) = _
  have h := congrArg (fun x : Coefficient K Q B => b • x)
    (coefficientMapOfRingSquare_tmul_D s a p)
  exact h.trans (TensorProduct.smul_tmul' b (s.coefficient a)
    (KaehlerDifferential.D K Q (s.algebra p)))

end KaehlerDifferential

end
