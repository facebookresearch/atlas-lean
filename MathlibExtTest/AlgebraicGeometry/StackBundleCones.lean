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
with value `2`, so the quadratic value `4` is rejected. -/
example [Algebra B ℚ] (a b : IntrinsicConePoint P ℚ) (h : IsScaledConePoint P (2 : ℚ) a b)
    (x : P.ker) (hx : a.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) = 1) :
    b.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) ≠ 4 := by
  rw [h x, hx]; norm_num

/-- A nonzero constant translation is not the identity scaling. -/
example {D : Type} [CommRing D] [Algebra B D] (a b : IntrinsicConePoint P D)
    (h : IsScaledConePoint P (1 : D) a b) (x : P.ker) (c : D) (hc : c ≠ 0) :
    b.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) ≠
      a.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) + c := by
  rw [h x, one_mul]; intro hb; exact hc (by simpa using hb)

/-- A zero cone point takes no nonzero value on degree-one coordinates (so a nonzero constant
translation of the zero point is not a zero point). -/
example {D : Type} [CommRing D] [Algebra B D] (a : IntrinsicConePoint P D) (h : IsZeroConePoint P a)
    (x : P.ker) (c : D) (hc : c ≠ 0) :
    a.map (MathlibExt.AlgebraicGeometry.AffineConeAtlas.normalDegreeOne P x) ≠ c := by
  rw [h x]; exact hc.symm

end ConicalValues

section ConeArrows

open MathlibExt.AlgebraicGeometry.AffineConeAtlas

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (P : Algebra.Extension.{0} A B)

/-- The canonical cone diagram: coefficient change by postcomposition. -/
def canonicalConeDiagram : IntrinsicConeDiagram P where
  functor :=
    { obj C := Cat.of (IntrinsicConePoint P C)
      map h := (coneCoefficientFunctor P h.hom).toCatHom
      map_id _ := rfl
      map_comp _ _ := rfl }
  object_eq _ := rfl
  map_eq h := by simp

variable {P}

/-- The coefficient-changing arrow of the canonical diagram with coefficient map `φ : T ⟶ R` and
tangent `t` (valued in the source coefficients `R`). -/
def coneArrow {R T : CommAlgCat.{0} B} (φ : T ⟶ R) (a : IntrinsicConePoint P R)
    (b : IntrinsicConePoint P T) (t : P.CotangentSpace →ₗ[B] R)
    (ht : ∀ x, a.map (normalCotangent P x) =
      φ.hom (b.map (normalCotangent P x)) + t (P.cotangentComplex x)) :
    coneObject P (canonicalConeDiagram P) R a ⟶ coneObject P (canonicalConeDiagram P) T b :=
  Quiver.Hom.op ⟨φ, ⟨t, ht⟩⟩

/-- The tangent reader returns the arrow's own tangent (not, for example, zero). -/
example {R T : CommAlgCat.{0} B} (φ : T ⟶ R) (a : IntrinsicConePoint P R)
    (b : IntrinsicConePoint P T) (t : P.CotangentSpace →ₗ[B] R)
    (ht : ∀ x, a.map (normalCotangent P x) =
      φ.hom (b.map (normalCotangent P x)) + t (P.cotangentComplex x)) (v : P.CotangentSpace) :
    coneArrowTangent P (canonicalConeDiagram P) (coneArrow φ a b t ht) v = t v := rfl

/-- An arrow and its `r`-scaled counterpart (tangent `r • t`, same coefficient map sending `s` to
`r`) form a scaled pair. -/
example {R T : CommAlgCat.{0} B} (φ : T ⟶ R) (r : R) (s : T) (hs : φ.hom s = r)
    (a a' : IntrinsicConePoint P R) (b b' : IntrinsicConePoint P T) (t : P.CotangentSpace →ₗ[B] R)
    (ht : ∀ x, a.map (normalCotangent P x) =
      φ.hom (b.map (normalCotangent P x)) + t (P.cotangentComplex x))
    (ht' : ∀ x, a'.map (normalCotangent P x) =
      φ.hom (b'.map (normalCotangent P x)) + (r • t) (P.cotangentComplex x)) :
    IsScaledConeArrow P (canonicalConeDiagram P) r s (coneArrow φ a b t ht)
      (coneArrow φ a' b' (r • t) ht') :=
  ⟨rfl, hs, fun _ ↦ rfl⟩

/-- An arrow with a nonzero tangent value is not its own `r`-scaling for `r ≠ 1` over a domain:
the predicate really reads the tangents. -/
example {R T : CommAlgCat.{0} B} [IsDomain R] (φ : T ⟶ R) (r : R) (hr : r ≠ 1) (s : T)
    (a : IntrinsicConePoint P R) (b : IntrinsicConePoint P T) (t : P.CotangentSpace →ₗ[B] R)
    (ht : ∀ x, a.map (normalCotangent P x) =
      φ.hom (b.map (normalCotangent P x)) + t (P.cotangentComplex x))
    (v : P.CotangentSpace) (hv : t v ≠ 0) :
    ¬ IsScaledConeArrow P (canonicalConeDiagram P) r s (coneArrow φ a b t ht)
      (coneArrow φ a b t ht) := by
  rintro ⟨-, -, H⟩
  have h1 : (1 - r) * t v = 0 := by
    have := H v
    change t v = r * t v at this
    rw [sub_mul, one_mul, ← this, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact hr (sub_eq_zero.mp h).symm
  · exact hv h

end ConeArrows

section VirtualPullbacks

open StackChowGroups StackVirtualPullbacks StackCycleGeometry StackCycleRelations

variable {S : Scheme.{0}} {scope : Stack S → Prop}

/-- The relative virtual pullback lands in degree `-1 - rank` from degree `-1`. -/
example {D : CycleConstructionData S scope} {K : KreschPresentation D} {F G : Stack S}
    {hF : scope F} {hG : scope G} {f : StackHom F G} {E : VectorBundleStack F}
    {star : ConditionStar f E} (R : RelativeVirtualPullbackData D K hF hG f E star)
    (T : TestFamily (scope := scope) f) (a : RationalChowGroup D K T.target T.targetScope (-1)) :
    RationalChowGroup D K T.square.apex T.sourceScope (-1 - E.virtualRank) :=
  relativeVirtualPullback R T (-1) a

/-- The refined Gysin map of a Gysin square lands in degree `-1 - c` from degree `-1`. -/
example {D : CycleConstructionData S scope} {K : KreschPresentation D} {F G : Stack S}
    {f : StackHom F G} {P Q : TestFamily (scope := scope) f} {p : TestPasting P Q} {c : ℕ}
    (N : GysinSquareData D K p c) (a : RationalChowGroup D K P.target P.targetScope (-1)) :
    RationalChowGroup D K Q.target Q.targetScope (-1 - c) :=
  N.targetMap (-1) a

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
    (a : StackAffineModules.AffinePoint T) :
    ((P.linearMap.diagramMap.linear a).functor).IsEquivalence :=
  P.linearMap.equivalence a

/-- Descent: on every restriction arrow, the comparison cell of a linear diagram map has zero
translation at a zero object (a shear, whose correction on a base arrow is a nonzero constant even
at the zero object, is excluded). -/
example {T X : Stack S} {n m : ℤ} {M : LinearBundleDiagram T n} {N : LinearBundleDiagram X m}
    {p : StackHom T X} (Φ : LinearDiagramMap M N p) {a b : StackAffineModules.AffinePoint T}
    (f : a ⟶ b) (q : M.pseudofunctor.obj (.mk (Opposite.op b)))
    (hq : ((eqToHom (M.objects b)).toFunctor.obj q).value = 0) :
    ((eqToHom (N.objects ((StackVectorBundles.affineMap p).obj a))).toFunctor.map
      ((Φ.trans.naturality f.op.toLoc).hom.toNatTrans.app q)).translation = 0 := by
  obtain ⟨h, hh⟩ := Φ.naturalityLinear f
  rw [hh q, hq, map_zero]

end VirtualPullbacks

end StackBundleConesTest
