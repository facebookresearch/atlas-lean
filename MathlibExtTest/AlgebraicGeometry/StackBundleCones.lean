/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.StackBundleCones
import MathlibExt.AlgebraicGeometry.AffineNormalConeMaps
import MathlibExt.AlgebraicGeometry.StackVirtualPullbacks

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.StackBundleCones

namespace StackBundleConesTest

section AdditiveQuotient

variable {R : Type} [CommRing R] {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {d : M →ₗ[R] N}

/-- Arrows of the quotient groupoid add translations, and the identity translates by zero. -/
example (a : AdditiveQuotient d) : (𝟙 a : a ⟶ a).translation = 0 := rfl

example {a b c : AdditiveQuotient d} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).translation = f.translation + g.translation := rfl

example {a b : AdditiveQuotient d} (f : a ⟶ b) : (inv f).translation = -f.translation := by
  rw [← Groupoid.inv_eq_inv]; rfl

/-- An arrow exists exactly when the values differ by the image of `d`. -/
example (a : AdditiveQuotient d) (m : M) : a ⟶ ⟨a.value + d m⟩ := ⟨m, rfl⟩

example {a b : AdditiveQuotient d} (f : a ⟶ b) : b.value - a.value ∈ LinearMap.range d :=
  ⟨f.translation, by rw [f.relation]; abel⟩

/-- For the zero differential the groupoid is discrete on values. -/
example {a b : AdditiveQuotient (0 : M →ₗ[R] N)} (f : a ⟶ b) : a.value = b.value := by
  rw [f.relation]; simp

end AdditiveQuotient

section ConeHomotheties

variable {A B D : Type} [CommRing A] [CommRing B] [Algebra A B] [CommRing D] [Algebra B D]
  {P : Algebra.Extension.{0} A B}

/-- Scaling by one is the identity homothety. -/
example (a : IntrinsicConePoint P D) : IsScaledConePoint P 1 a a := fun x ↦ by simp

/-- Scaling by zero lands on a zero cone point. -/
example (a b : IntrinsicConePoint P D) (h : IsScaledConePoint P 0 a b) :
    IsZeroConePoint P b := fun x ↦ by simpa using h x

/-- Homotheties compose multiplicatively: scaling by `2` twice is scaling by `4`. -/
example (a b c : IntrinsicConePoint P D) (h₁ : IsScaledConePoint P 2 a b)
    (h₂ : IsScaledConePoint P 2 b c) : IsScaledConePoint P 4 a c := fun x ↦ by
  rw [h₂ x, h₁ x, ← mul_assoc]; norm_num

/-- A zero cone point stays zero under every homothety. -/
example (r : D) (a b : IntrinsicConePoint P D) (ha : IsZeroConePoint P a)
    (h : IsScaledConePoint P r a b) : IsZeroConePoint P b := fun x ↦ by
  rw [h x, ha x, mul_zero]

/-- Change of coefficients acts on cone points by composition. -/
example {C : Type} [CommRing C] [Algebra B C] (φ : D →ₐ[B] C) (a : IntrinsicConePoint P D) :
    ((coneCoefficientFunctor P φ).obj a).map = φ.comp a.map := rfl

/-- Change of coefficients preserves homotheties, with the scalar pushed forward. -/
example {C : Type} [CommRing C] [Algebra B C] (φ : D →ₐ[B] C) (r : D)
    (a b : IntrinsicConePoint P D) (h : IsScaledConePoint P r a b) :
    IsScaledConePoint P (φ r) ((coneCoefficientFunctor P φ).obj a)
      ((coneCoefficientFunctor P φ).obj b) := fun x ↦ by
  change φ (b.map _) = φ r * φ (a.map _)
  rw [h x, map_mul]

end ConeHomotheties

section NormalMaps

open MathlibExt.AlgebraicGeometry.AffineNormalConeMaps

variable {k B : Type} [CommRing k] [CommRing B] [Algebra k B] (P : Algebra.Extension.{0} k B)

/-- The identity square sends every kernel element to itself. -/
example (x : P.ker) : kernelImage P P (RingHom.id _) (RingHom.id _) rfl x = x := rfl

/-- Composing with the identity normal map does not change the underlying ring map. -/
example (F : NormalMap P P (RingHom.id _) (RingHom.id _) rfl) :
    (compose P P P (identity P) F).map = F.map := rfl

example (F : NormalMap P P (RingHom.id _) (RingHom.id _) rfl) :
    (compose P P P F (identity P)).map = F.map := rfl

end NormalMaps

section ConicalValues

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  {P : Algebra.Extension.{0} A B}

/-- Scaling by `2` doubles every degree-one coordinate: a point with value `1` is sent to a point
with value `2`, never to the quadratic value `4`. -/
example [Algebra B ℚ] (a b : IntrinsicConePoint P ℚ) (h : IsScaledConePoint P (2 : ℚ) a b)
    (x : P.ker) (hx : a.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) = 1) :
    b.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) = 2 := by
  rw [h x, hx, mul_one]

example : (2 : ℚ) ≠ 4 := by norm_num

/-- A zero cone point takes no nonzero value on degree-one coordinates (so a nonzero constant
translation of the zero point is not a zero point). -/
example {D : Type} [CommRing D] [Algebra B D] (a : IntrinsicConePoint P D) (h : IsZeroConePoint P a)
    (x : P.ker) (c : D) (hc : c ≠ 0) :
    a.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) ≠ c := by
  rw [h x]; exact hc.symm

end ConicalValues

section ConeArrows

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  (P : Algebra.Extension.{0} A B) (D : IntrinsicConeDiagram P)

/-- A scaled arrow fixes its source coefficient: the target scalar `s` is sent to the source
scalar `r` by the arrow's coefficient map (in this direction), and the arrow tangents scale by
`r` in the source coefficient algebra. -/
example {R T : CommAlgCat.{0} B} (r : R) (s : T) {a a' : IntrinsicConePoint P R}
    {b b' : IntrinsicConePoint P T} (h : coneObject P D R a ⟶ coneObject P D T b)
    (h' : coneObject P D R a' ⟶ coneObject P D T b') (H : IsScaledConeArrow P D r s h h') :
    h.unop.base.hom s = r ∧ ∀ x, (show R from coneArrowTangent P D h' x) =
      r * (show R from coneArrowTangent P D h x) :=
  ⟨H.2.1, H.2.2⟩

/-- Both arrows of a scaled pair have the same coefficient map. -/
example {R T : CommAlgCat.{0} B} (r : R) (s : T) {a a' : IntrinsicConePoint P R}
    {b b' : IntrinsicConePoint P T} (h : coneObject P D R a ⟶ coneObject P D T b)
    (h' : coneObject P D R a' ⟶ coneObject P D T b') (H : IsScaledConeArrow P D r s h h') :
    h'.unop.base = h.unop.base := H.1

end ConeArrows

section VirtualPullbacks

open StackChowGroups StackVirtualPullbacks StackCycleGeometry StackCycleRelations

variable {S : Scheme.{0}} {scope : Stack S → Prop}

/-- The relative virtual pullback shifts the signed degree by the virtual rank, also in negative
degree, and is additive. -/
example {D : CycleConstructionData S scope} {K : KreschPresentation D} {F G : Stack S}
    {hF : scope F} {hG : scope G} {f : StackHom F G} {E : VectorBundleStack F}
    {star : ConditionStar f E} (R : RelativeVirtualPullbackData D K hF hG f E star)
    (T : TestFamily (scope := scope) f) (a b : RationalChowGroup D K T.target T.targetScope (-1)) :
    relativeVirtualPullback R T (-1) (a + b) =
      relativeVirtualPullback R T (-1) a + relativeVirtualPullback R T (-1) b :=
  map_add _ _ _

/-- The cone base change of a relative virtual pullback uses the test family's own square cell. -/
example {D : CycleConstructionData S scope} {K : KreschPresentation D} {F G : Stack S}
    {hF : scope F} {hG : scope G} {f : StackHom F G} {E : VectorBundleStack F}
    {star : ConditionStar f E} (R : RelativeVirtualPullbackData D K hF hG f E star)
    (T : TestFamily (scope := scope) f) : (R.baseChange T).commutes = T.square.commutes :=
  R.baseChange_commutes T

/-- A pasting of test families is a morphism of fibre diagrams: its cells paste to the cell of
the target family's square. -/
example {F G : Stack S} {f : StackHom F G} {P Q : TestFamily (scope := scope) f}
    (p : TestPasting P Q) (T : Over S) (x : Q.square.apex.Fibre T) :
    (Q.square.commutes.app T).hom.app x =
      (component f T).map ((p.overF.app T).inv.app x) ≫
        (P.square.commutes.app T).hom.app ((component p.source T).obj x) ≫
        (component P.map T).map ((p.commutes.app T).hom.app x) ≫
        (p.overG.app T).hom.app ((component Q.square.snd T).obj x) :=
  p.pasting T x

/-- The total-space map of a bundle-stack pullback is linear: on each affine point it induces an
equivalence of the quotient groupoids of the two-term presentations. -/
example {T X : Stack S} {p : StackHom T X} {E : VectorBundleStack X} (P : BundleStackPullback p E)
    (a : StackAffineModules.AffinePoint T) : ((P.linearMap.linear a).functor).IsEquivalence :=
  P.linearMap.equivalence a

end VirtualPullbacks

end StackBundleConesTest
