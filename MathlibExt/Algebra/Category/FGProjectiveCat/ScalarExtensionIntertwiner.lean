/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension
public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionCoherence

/-!
# Coefficient intertwiners of the original scalar extensions

For arbitrary associative unital rings, a coefficient `c` satisfying
`f(r) * c = c * g(r)` gives the original balanced quotient map
`s ⊗ x ↦ (s * c) ⊗ x`. Balance, outer linearity, module naturality and
the ordered coefficient composition laws are earned on the original
scalar-extension carriers. No natural map or comparison is assumed.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MulOpposite

universe uR uS uT uP uQ

namespace ModuleCat.RingHomScalarExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual coefficient condition needed to preserve the two original balanced relations. -/
@[expose] def Intertwines (f g : R →+* S) (c : S) : Prop := ∀ r, f r * c = c * g r

private def coefficientPairing (g : R →+* S) (c : S) (P : Type uP)
    [AddCommGroup P] [Module R P] : S →ₗ[ℤ] P →ₗ[ℤ] tensor g P :=
  (pure g P).comp (LinearMap.mulRight ℤ c)

private theorem coefficientPairing_balance (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : Type uP) [AddCommGroup P] [Module R P] :
    letI := rightModule f
    ∀ (r : R) (s : S) (p : P),
      coefficientPairing g c P (op r • s) p = coefficientPairing g c P s (r • p) := by
  let := rightModule f
  intro r s p
  change pure g P ((op r • s) * c) p = pure g P (s * c) (r • p)
  rw [rightModule_smul f, mul_assoc, hc r, ← mul_assoc]
  exact pure_balance g P r (s * c) p

private def intertwinerGround (f g : R →+* S) (c : S) (hc : Intertwines f g c)
    (P : Type uP) [AddCommGroup P] [Module R P] : tensor f P →ₗ[ℤ] tensor g P :=
  letI := rightModule f
  TensorProduct.Balanced.lift (coefficientPairing g c P) (coefficientPairing_balance f g c hc P)

private theorem intertwinerGround_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : Type uP) [AddCommGroup P] [Module R P]
    (s : S) (p : P) :
    intertwinerGround f g c hc P (pure f P s p) = pure g P (s * c) p := by
  let := rightModule f
  exact TensorProduct.Balanced.lift_mk (coefficientPairing g c P)
    (coefficientPairing_balance f g c hc P) s p

private def scalarAddHom (a : S) (X : Type*) [AddCommGroup X] [Module S X] : X →+ X where
  toFun x := a • x
  map_zero' := smul_zero a
  map_add' := smul_add a

private theorem intertwinerGround_smul (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : Type uP) [AddCommGroup P] [Module R P]
    (a : S) (x : tensor f P) :
    intertwinerGround f g c hc P (a • x) = a • intertwinerGround f g c hc P x := by
  let := rightModule f
  have h : (intertwinerGround f g c hc P).toAddMonoidHom.comp (scalarAddHom a (tensor f P)) =
      (scalarAddHom a (tensor g P)).comp (intertwinerGround f g c hc P).toAddMonoidHom := by
    apply TensorProduct.Balanced.addHom_ext ℤ R S P
    intro s p
    change intertwinerGround f g c hc P (a • pure f P s p) =
      a • intertwinerGround f g c hc P (pure f P s p)
    rw [smul_pure f, intertwinerGround_pure, intertwinerGround_pure, smul_pure g]
    exact congrArg (fun t : S => pure g P t p) (mul_assoc a s c)
  exact DFunLike.congr_fun h x

/-- The actual outer-linear quotient map induced by the original coefficient intertwiner. -/
def coefficientIntertwiner (f g : R →+* S) (c : S) (hc : Intertwines f g c)
    (P : Type uP) [AddCommGroup P] [Module R P] : tensor f P →ₗ[S] tensor g P := by
  exact
    { toFun := intertwinerGround f g c hc P
      map_add' := (intertwinerGround f g c hc P).map_add
      map_smul' := intertwinerGround_smul f g c hc P }

/-- The original pure coefficient is multiplied by the actual intertwiner on its right. -/
theorem coefficientIntertwiner_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : Type uP) [AddCommGroup P] [Module R P]
    (s : S) (p : P) :
    coefficientIntertwiner f g c hc P (pure f P s p) = pure g P (s * c) p :=
  intertwinerGround_pure f g c hc P s p

/-- The original coefficient map commutes with every original module morphism. -/
theorem coefficientIntertwiner_naturality (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) {P : Type uP} {Q : Type uQ}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (a : P →ₗ[R] Q) :
    (coefficientIntertwiner f g c hc Q).comp (linearMap f a) =
      (linearMap g a).comp (coefficientIntertwiner f g c hc P) := by
  apply linearMap_ext f P
  intro s p
  simp only [LinearMap.comp_apply, linearMap_pure, coefficientIntertwiner_pure]

/-- The zero coefficient always intertwines the actual source and target ring maps. -/
theorem Intertwines.zero (f g : R →+* S) : Intertwines f g 0 := by
  intro r
  simp

/-- Addition preserves the actual coefficient balance condition. -/
theorem Intertwines.add {f g : R →+* S} {c d : S}
    (hc : Intertwines f g c) (hd : Intertwines f g d) : Intertwines f g (c + d) := by
  intro r
  rw [mul_add, add_mul, hc r, hd r]

/-- The unit coefficient is the identity intertwiner of the actual ring homomorphism. -/
theorem Intertwines.one (f : R →+* S) : Intertwines f f 1 := by
  intro r
  simp

/-- Ordered coefficient multiplication composes the two actual balance conditions. -/
theorem Intertwines.mul {f g h : R →+* S} {c d : S}
    (hc : Intertwines f g c) (hd : Intertwines g h d) : Intertwines f h (c * d) := by
  intro r
  rw [← mul_assoc, hc r, mul_assoc, hd r, ← mul_assoc]

variable {T : Type uT} [Ring T]

/-- The actual pushed coefficient retains its original balance relation under a ring map. -/
theorem Intertwines.map {f g : R →+* S} {c : S} (hc : Intertwines f g c) (k : S →+* T) :
    Intertwines (k.comp f) (k.comp g) (k c) := by
  intro r
  exact (k.map_mul _ _).symm.trans ((congrArg k (hc r)).trans (k.map_mul _ _))

/-- The original coefficient relation restricts along the actual source ring homomorphism. -/
theorem Intertwines.precomp {f g : S →+* T} {c : T} (hc : Intertwines f g c) (k : R →+* S) :
    Intertwines (f.comp k) (g.comp k) c := fun r => hc (k r)

/-- Equal original ring maps have the actual unit coefficient relation. -/
theorem Intertwines.of_eq {f g : R →+* S} (h : f = g) : Intertwines f g 1 := by
  intro r
  simp only [mul_one, one_mul]
  exact DFunLike.congr_fun h r

/-- A zero original coefficient induces the actual zero quotient map. -/
theorem coefficientIntertwiner_zero (f g : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    coefficientIntertwiner f g 0 (Intertwines.zero f g) P = 0 := by
  apply linearMap_ext f P
  intro s p
  rw [coefficientIntertwiner_pure, mul_zero]
  exact DFunLike.congr_fun (pure g P).map_zero p

/-- Addition of original coefficients is addition of the actual quotient maps. -/
theorem coefficientIntertwiner_add (f g : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines f g d) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    coefficientIntertwiner f g (c + d) (hc.add hd) P =
      coefficientIntertwiner f g c hc P + coefficientIntertwiner f g d hd P := by
  apply linearMap_ext f P
  intro s p
  rw [LinearMap.add_apply, coefficientIntertwiner_pure, coefficientIntertwiner_pure,
    coefficientIntertwiner_pure, mul_add]
  exact DFunLike.congr_fun ((pure g P).map_add (s * c) (s * d)) p

/-- The original unit intertwiner is the identity on the same original scalar-extension carrier. -/
theorem coefficientIntertwiner_one (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    coefficientIntertwiner f f 1 (Intertwines.one f) P = LinearMap.id := by
  apply linearMap_ext f P
  intro s p
  rw [coefficientIntertwiner_pure, mul_one]
  rfl

/-- Composition retains the original ordered product of the two actual coefficients. -/
theorem coefficientIntertwiner_comp (f g h : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines g h d) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    (coefficientIntertwiner g h d hd P).comp (coefficientIntertwiner f g c hc P) =
      coefficientIntertwiner f h (c * d) (hc.mul hd) P := by
  apply linearMap_ext f P
  intro s p
  rw [LinearMap.comp_apply, coefficientIntertwiner_pure, coefficientIntertwiner_pure,
    coefficientIntertwiner_pure, mul_assoc]

end ModuleCat.RingHomScalarExtension

namespace FGProjectiveCat

open ModuleCat.RingHomScalarExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual coefficient map conjugated by the original finite-projective tensor coordinates. -/
def scalarExtensionIntertwiner (f g : R →+* S) (c : S) (hc : Intertwines f g c) :
    scalarExtension.{uR,uS,uP} f ⟶ scalarExtension g where
  app P := ConcreteCategory.ofHom
    ((scalarExtensionCarrierLinearEquiv g P).symm.toLinearMap.comp
      ((coefficientIntertwiner f g c hc P).comp
        (scalarExtensionCarrierLinearEquiv f P).toLinearMap))
  naturality {P Q} a := by
    apply FGProjectiveCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (scalarExtensionCarrierLinearEquiv g Q).injective
    simp only [hom_hom_comp, LinearMap.comp_apply]
    change scalarExtensionCarrierLinearEquiv g Q
        ((scalarExtensionCarrierLinearEquiv g Q).symm
          (coefficientIntertwiner f g c hc Q
            (scalarExtensionCarrierLinearEquiv f Q (((scalarExtension f).map a).hom.hom x)))) =
      scalarExtensionCarrierLinearEquiv g Q
        (((scalarExtension g).map a).hom.hom
          ((scalarExtensionCarrierLinearEquiv g P).symm
            (coefficientIntertwiner f g c hc P (scalarExtensionCarrierLinearEquiv f P x))))
    rw [LinearEquiv.apply_symm_apply]
    have hf := LinearMap.congr_fun (scalarExtensionCarrierLinearEquiv_naturality f a) x
    have hg := LinearMap.congr_fun (scalarExtensionCarrierLinearEquiv_naturality g a)
      ((scalarExtensionCarrierLinearEquiv g P).symm
        (coefficientIntertwiner f g c hc P (scalarExtensionCarrierLinearEquiv f P x)))
    change scalarExtensionCarrierLinearEquiv f Q
      (((scalarExtension f).map a).hom.hom x) =
      linearMap f a.hom.hom (scalarExtensionCarrierLinearEquiv f P x) at hf
    change scalarExtensionCarrierLinearEquiv g Q
      (((scalarExtension g).map a).hom.hom
        ((scalarExtensionCarrierLinearEquiv g P).symm
          (coefficientIntertwiner f g c hc P (scalarExtensionCarrierLinearEquiv f P x)))) =
      linearMap g a.hom.hom
        (scalarExtensionCarrierLinearEquiv g P
          ((scalarExtensionCarrierLinearEquiv g P).symm
            (coefficientIntertwiner f g c hc P (scalarExtensionCarrierLinearEquiv f P x)))) at hg
    rw [hf, hg, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (coefficientIntertwiner_naturality f g c hc a.hom.hom)
      (scalarExtensionCarrierLinearEquiv f P x)

/-- The whole original coordinate map of the finite-projective coefficient transformation. -/
theorem scalarExtensionIntertwiner_coordinates (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : FGProjectiveCat.{uP} R) (x : (scalarExtension f).obj P) :
    scalarExtensionCarrierLinearEquiv g P
        (((scalarExtensionIntertwiner f g c hc).app P).hom.hom x) =
      coefficientIntertwiner f g c hc P (scalarExtensionCarrierLinearEquiv f P x) := by
  change scalarExtensionCarrierLinearEquiv g P
    ((scalarExtensionCarrierLinearEquiv g P).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- Each pure class keeps its ordered original coefficient in the projective lift. -/
theorem scalarExtensionIntertwiner_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : FGProjectiveCat.{uP} R) (s : S) (p : P) :
    scalarExtensionCarrierLinearEquiv g P
      (((scalarExtensionIntertwiner f g c hc).app P).hom.hom
        ((scalarExtensionCarrierLinearEquiv f P).symm (pure f P s p))) = pure g P (s * c) p := by
  rw [scalarExtensionIntertwiner_coordinates, LinearEquiv.apply_symm_apply,
    coefficientIntertwiner_pure]

/-- The actual finite-projective zero coefficient transformation is zero. -/
theorem scalarExtensionIntertwiner_zero (f g : R →+* S) :
    scalarExtensionIntertwiner.{uR,uS,uP} f g 0 (Intertwines.zero f g) = 0 := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (scalarExtensionCarrierLinearEquiv g P).injective
  rw [scalarExtensionIntertwiner_coordinates, coefficientIntertwiner_zero]
  simp

/-- Coefficient addition gives addition of the original finite-projective transformations. -/
theorem scalarExtensionIntertwiner_add (f g : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines f g d) :
    scalarExtensionIntertwiner.{uR,uS,uP} f g (c + d) (hc.add hd) =
      scalarExtensionIntertwiner f g c hc + scalarExtensionIntertwiner f g d hd := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (scalarExtensionCarrierLinearEquiv g P).injective
  change scalarExtensionCarrierLinearEquiv g P
      (((scalarExtensionIntertwiner f g (c + d) (hc.add hd)).app P).hom.hom x) =
    scalarExtensionCarrierLinearEquiv g P
      ((((scalarExtensionIntertwiner f g c hc).app P).hom.hom x) +
        (((scalarExtensionIntertwiner f g d hd).app P).hom.hom x))
  rw [LinearEquiv.map_add, scalarExtensionIntertwiner_coordinates,
    scalarExtensionIntertwiner_coordinates, scalarExtensionIntertwiner_coordinates,
    coefficientIntertwiner_add]
  rfl

/-- The actual unit coefficient transformation is the identity of the same original functor. -/
theorem scalarExtensionIntertwiner_one (f : R →+* S) :
    scalarExtensionIntertwiner.{uR,uS,uP} f f 1 (Intertwines.one f) = 𝟙 (scalarExtension f) := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (scalarExtensionCarrierLinearEquiv f P).injective
  rw [scalarExtensionIntertwiner_coordinates, coefficientIntertwiner_one]
  rfl

/-- Composition preserves the original noncommutative order of coefficient transformations. -/
theorem scalarExtensionIntertwiner_comp (f g h : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines g h d) :
    scalarExtensionIntertwiner.{uR,uS,uP} f g c hc ≫ scalarExtensionIntertwiner g h d hd =
      scalarExtensionIntertwiner f h (c * d) (hc.mul hd) := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (scalarExtensionCarrierLinearEquiv h P).injective
  change scalarExtensionCarrierLinearEquiv h P
      (((scalarExtensionIntertwiner g h d hd).app P).hom.hom
        (((scalarExtensionIntertwiner f g c hc).app P).hom.hom x)) = _
  rw [scalarExtensionIntertwiner_coordinates, scalarExtensionIntertwiner_coordinates,
    scalarExtensionIntertwiner_coordinates]
  exact LinearMap.congr_fun (coefficientIntertwiner_comp f g h c d hc hd P)
    (scalarExtensionCarrierLinearEquiv f P x)

/-- The same coefficient transformation transported by the original canonical shrink functor. -/
def ringScalarExtensionIntertwiner (f g : R →+* S) (c : S) (hc : Intertwines f g c) :
    ringScalarExtension f ⟶ ringScalarExtension g :=
  Functor.whiskerRight (scalarExtensionIntertwiner f g c hc)
    (universeEquivalence.{uS,uR} S).functor

/-- Native coefficient maps retain both original shrink/tensor coordinates on the whole carrier. -/
theorem ringScalarExtensionIntertwiner_coordinates (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : FGProjectiveCat.{uR} R) (x : (ringScalarExtension f).obj P) :
    ringScalarExtensionCoordinates g P
      (((ringScalarExtensionIntertwiner f g c hc).app P).hom.hom x) =
      coefficientIntertwiner f g c hc P (ringScalarExtensionCoordinates f P x) := by
  let A := (scalarExtension f).obj P
  let B := (scalarExtension g).obj P
  let y : UniverseEquivalence.shrinkObject.{uS,uR} S A := x
  let sf := UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S A
  let sg := UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S B
  let η := (scalarExtensionIntertwiner f g c hc).app P
  have hy := UniverseEquivalence.shrinkFunctor_map_apply.{uS,uR} S η y
  have h₁ := congrArg (fun z : UniverseEquivalence.shrinkObject.{uS,uR} S B =>
    scalarExtensionCarrierLinearEquiv g P (sg z)) hy
  have h₂ := congrArg (scalarExtensionCarrierLinearEquiv g P)
    (sg.apply_symm_apply (η.hom.hom (sf y)))
  have hleft := ringScalarExtensionCoordinates_apply g P
    (((ringScalarExtensionIntertwiner f g c hc).app P).hom.hom x)
  have hright := congrArg (coefficientIntertwiner f g c hc P)
    (ringScalarExtensionCoordinates_apply f P x)
  exact hleft.trans (((h₁.trans h₂).trans
    (scalarExtensionIntertwiner_coordinates f g c hc P (sf y))).trans hright.symm)

/-- The native transformation retains the same ordered original pure-tensor coefficient. -/
theorem ringScalarExtensionIntertwiner_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : FGProjectiveCat.{uR} R) (s : S) (p : P) :
    ringScalarExtensionCoordinates g P
      (((ringScalarExtensionIntertwiner f g c hc).app P).hom.hom
        ((ringScalarExtensionCoordinates f P).symm (pure f P s p))) = pure g P (s * c) p := by
  rw [ringScalarExtensionIntertwiner_coordinates, LinearEquiv.apply_symm_apply,
    coefficientIntertwiner_pure]

/-- The actual native image inserts the same ordered pure class in original target coordinates. -/
theorem ringScalarExtensionIntertwiner_apply_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (P : FGProjectiveCat.{uR} R) (s : S) (p : P) :
    (((ringScalarExtensionIntertwiner f g c hc).app P).hom.hom
      ((ringScalarExtensionCoordinates f P).symm (pure f P s p))) =
        (ringScalarExtensionCoordinates g P).symm (pure g P (s * c) p) := by
  apply (ringScalarExtensionCoordinates g P).injective
  rw [ringScalarExtensionIntertwiner_pure, LinearEquiv.apply_symm_apply]

/-- The native zero coefficient transformation remains the original zero morphism. -/
theorem ringScalarExtensionIntertwiner_zero (f g : R →+* S) :
    ringScalarExtensionIntertwiner f g 0 (Intertwines.zero f g) = 0 := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (ringScalarExtensionCoordinates g P).injective
  rw [ringScalarExtensionIntertwiner_coordinates, coefficientIntertwiner_zero]
  simp

/-- Native addition preserves the actual coefficient sum in the original functor category. -/
theorem ringScalarExtensionIntertwiner_add (f g : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines f g d) :
    ringScalarExtensionIntertwiner f g (c + d) (hc.add hd) =
      ringScalarExtensionIntertwiner f g c hc + ringScalarExtensionIntertwiner f g d hd := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (ringScalarExtensionCoordinates g P).injective
  change ringScalarExtensionCoordinates g P
      (((ringScalarExtensionIntertwiner f g (c + d) (hc.add hd)).app P).hom.hom x) =
    ringScalarExtensionCoordinates g P
      ((((ringScalarExtensionIntertwiner f g c hc).app P).hom.hom x) +
        (((ringScalarExtensionIntertwiner f g d hd).app P).hom.hom x))
  rw [LinearEquiv.map_add, ringScalarExtensionIntertwiner_coordinates,
    ringScalarExtensionIntertwiner_coordinates, ringScalarExtensionIntertwiner_coordinates,
    coefficientIntertwiner_add]
  rfl

/-- The native unit coefficient transformation is the actual identity natural transformation. -/
theorem ringScalarExtensionIntertwiner_one (f : R →+* S) :
    ringScalarExtensionIntertwiner f f 1 (Intertwines.one f) = 𝟙 (ringScalarExtension f) := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (ringScalarExtensionCoordinates f P).injective
  rw [ringScalarExtensionIntertwiner_coordinates, coefficientIntertwiner_one]
  rfl

/-- The whole native coefficient maps retain their original ordered composition. -/
theorem ringScalarExtensionIntertwiner_comp (f g h : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines g h d) :
    ringScalarExtensionIntertwiner f g c hc ≫ ringScalarExtensionIntertwiner g h d hd =
      ringScalarExtensionIntertwiner f h (c * d) (hc.mul hd) := by
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (ringScalarExtensionCoordinates h P).injective
  change ringScalarExtensionCoordinates h P
      (((ringScalarExtensionIntertwiner g h d hd).app P).hom.hom
        (((ringScalarExtensionIntertwiner f g c hc).app P).hom.hom x)) = _
  rw [ringScalarExtensionIntertwiner_coordinates, ringScalarExtensionIntertwiner_coordinates,
    ringScalarExtensionIntertwiner_coordinates]
  exact LinearMap.congr_fun (coefficientIntertwiner_comp f g h c d hc hd P)
    (ringScalarExtensionCoordinates f P x)

end FGProjectiveCat

end
