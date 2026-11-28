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
# Coefficient transport for Kähler differentials

Let k → P → A and K → Q → B be algebra towers of commutative rings. A CoefficientRingSquare
consists of ring maps f_k : k → K, f_P : P → Q and f_A : A → B commuting with both structural
squares.

For the extended differential modules Ω^A_{P/k}=A⊗[P]Ω_{P/k} and Ω^B_{Q/K}=B⊗[Q]Ω_{Q/K}, these
maps give an f_A-semilinear map a⊗d p ↦ f_A(a)⊗d(f_P(p)). It respects identity and composition
of squares. The generators 1_A⊗d p determine every semilinear map from the source module.

Giving B the A-action through f_A and extending scalars produces a B-linear map B⊗[A]Ω^A_{P/k}
→ Ω^B_{Q/K}, with b⊗(a⊗d p) ↦ (b·f_A(a))⊗d(f_P(p)). The six ring universes and the
extensionality target-module universe are independent.
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

/-- Commuting ring maps for extended differential transport.

For towers k → P → A and K → Q → B, specify ring maps on the ground, algebra and coefficient
rows and require the two structural squares to commute. -/
structure CoefficientRingSquare where
/-- Ring map on the ground row of a coefficient square.

The map f_k : k → K relates the two base rings of the differential modules. -/
  ground : k →+* K
/-- Ring map on the algebra row of a coefficient square.

The map f_P : P → Q relates the two algebras and is compatible with f_k by ground_commutes. -/
  algebra : P →+* Q
/-- Ring map on the coefficient row of a differential square.

The map f_A : A → B determines semilinearity of the coefficient differential map. -/
  coefficient : A →+* B
/-- Compatibility of the ground and algebra rows.

Require f_P ∘ algebraMap(k,P) = algebraMap(K,Q) ∘ f_k as ring maps k → Q. -/
  ground_commutes : algebra.comp (algebraMap k P) = (algebraMap K Q).comp ground
/-- Compatibility of the algebra and coefficient rows.

Require f_A ∘ algebraMap(P,A) = algebraMap(Q,B) ∘ f_P as ring maps P → B. -/
  augmentation_commutes : coefficient.comp (algebraMap P A) =
    (algebraMap Q B).comp algebra

variable {k K P Q A B}

/-- Identity square of an algebra-coefficient tower.

For k → P → A, use identity ring maps on all three rows to obtain the identity
CoefficientRingSquare. -/
def CoefficientRingSquare.id : CoefficientRingSquare k k P P A A where
  ground := RingHom.id k
  algebra := RingHom.id P
  coefficient := RingHom.id A
  ground_commutes := by ext r; rfl
  augmentation_commutes := by ext p; rfl

/-- Composition of coefficient ring squares.

For compatible squares s : (k,P,A) → (K,Q,B) and t : (K,Q,B) → (K',Q',B'), compose each row in
the order t ∘ s. Their two commutative-square equations compose as well. -/
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

/-- Semilinear map of extended Kähler differentials.

For a coefficient square s, construct Ω^A_{P/k} →ₛₗ[s.coefficient] Ω^B_{Q/K} by the
coefficient ring map and the semilinear Kähler map. Its tensor value is a⊗d p ↦
s.coefficient(a)⊗d(s.algebra(p)). -/
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

/-- Generator formula for a coefficient ring-square map.

For a ∈ A and p ∈ P, coefficientMapOfRingSquare s sends a⊗[P]d p to
s.coefficient(a)⊗[Q]d(s.algebra(p)). -/
@[simp]
theorem coefficientMapOfRingSquare_tmul_D
    (s : CoefficientRingSquare k K P Q A B) (a : A) (p : P) :
    coefficientMapOfRingSquare s (a ⊗ₜ[P] KaehlerDifferential.D k P p) =
      s.coefficient a ⊗ₜ[Q] KaehlerDifferential.D K Q (s.algebra p) := by
  change s.coefficient a ⊗ₜ[Q]
    mapOfRingSquare k K P Q s.ground s.algebra s.ground_commutes
      (KaehlerDifferential.D k P p) = _
  rw [mapOfRingSquare_D]

/-- Semilinear extensionality on differential generators.

Let σ : A → C be a ring map into a commutative ring and M a C-module in an independent
universe. Two σ-semilinear maps Ω^A_{P/k} → M are equal if they agree on 1_A⊗d p for every p ∈
P. -/
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

/-- Identity map on extended Kähler differentials.

The semilinear coefficient map of the identity ring square is the identity A-linear map on
A⊗[P]Ω_{P/k}. -/
@[simp]
theorem coefficientMapOfRingSquare_id :
    coefficientMapOfRingSquare (CoefficientRingSquare.id (k := k) (P := P) (A := A)) =
      (LinearMap.id : Coefficient k P A →ₗ[A] Coefficient k P A) := by
  apply coefficientSemilinear_hom_ext
  intro p
  rw [coefficientMapOfRingSquare_tmul_D]
  rfl

/-- Composition law for semilinear coefficient differential maps.

For composable squares s,t, coefficientMapOfRingSquare(s.comp t) is the composite of their
semilinear maps, with scalar homomorphism t.coefficient ∘ s.coefficient. -/
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

/-- Linear scalar extension of a coefficient differential map.

Give B its A-algebra structure through s.coefficient. The semilinear coefficient map extends
to the B-linear map B⊗[A]Ω^A_{P/k} → Ω^B_{Q/K}. -/
def coefficientBaseChangeMapOfRingSquare (s : CoefficientRingSquare k K P Q A B) :
    letI : Algebra A B := s.coefficient.toAlgebra
    (B ⊗[A] Coefficient k P A) →ₗ[B] Coefficient K Q B := by
  letI : Algebra A B := s.coefficient.toAlgebra
  letI : Module A (Coefficient K Q B) := Module.compHom (Coefficient K Q B) s.coefficient
  letI hTower : IsScalarTower A B (Coefficient K Q B) :=
    IsScalarTower.of_compHom A B (Coefficient K Q B)
  let l : Coefficient k P A →ₗ[A] Coefficient K Q B :=
    { toFun := coefficientMapOfRingSquare s
      map_add' := (coefficientMapOfRingSquare s).map_add
      map_smul' := (coefficientMapOfRingSquare s).map_smulₛₗ }
  exact @LinearMap.liftBaseChange A (Coefficient k P A) (Coefficient K Q B) B
    _ _ _ _ _ _ _ _ hTower l

/-- Two-coefficient tensor formula for extended differential transport.

With B viewed as an A-algebra through s.coefficient, b⊗[A](a⊗[P]d p) maps to
(b·s.coefficient(a))⊗[Q]d(s.algebra(p)). -/
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
