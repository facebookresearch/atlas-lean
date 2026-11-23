/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry

/-!
# Normalized rational restriction rings under tilting

The original rational localization has its actual bounded universal
map, plus-ring fraction condition and all-rank rational point map.
Its tilted comparison uses the actual integral sharp numerators and
their actual images in the localized tilt. The comparison is an
isomorphism of two characteristic-p pairs, and its square is fixed by
the original map's prescribed tilt.

The resulting ring and plus-ring equivalences are extracted from those
actual inverse bounded maps. No ringed-space isomorphism between the
original and tilted characteristics is asserted.

Source: Scholze, arXiv:1111.4914v1, Theorem 1.8(i)--(iii), Theorem 6.3;
arXiv:1709.07343v4, Theorem 3.12.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.PerfectoidRationalTilting

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.RingTheory.CompleteHuberPairModels
open IntegralTiltModels AffineUntiltingGeometry PerfectoidLocalModels

variable (p : ℕ) [Fact p.Prime]

/-- Fractions in the actual plus ring of a continuous pair map. -/
def OriginalFractions (P : HuberPair) (T : Finset P.ring) (s : P.ring)
    {Q : HuberPair} (f : RingMap P Q) : Prop :=
  ∃ u : Q.ringˣ, (u : Q.ring) = f.hom s ∧
    ∀ t ∈ T, f.hom t * ((u⁻¹ : Q.ringˣ) : Q.ring) ∈ Q.plus

/-- An actual perfectoid rational localization before changing characteristic. -/
structure OriginalRationalModel (P : AffineUntilting p) where
  numerators : Finset P.pair.ring
  denominator : P.pair.ring
  open_ideal : IsOpen (Ideal.span (numerators : Set P.pair.ring) : Set P.pair.ring)
  affine : AffineUntilting p
  map : affine ⟶ P
  fractions : OriginalFractions P.pair.toHuberPair numerators denominator map.original
  universal : ∀ (C : HuberPair) (f : RingMap P.pair.toHuberPair C),
    OriginalFractions P.pair.toHuberPair numerators denominator f →
      ∃! g : RingMap affine.pair.toHuberPair C,
        g.hom.comp map.original.hom = f.hom
  point : affine.pair.toHuberPair.Space ≃ₜ
    {v : P.pair.toHuberPair.Space |
      ¬ v.1.relation.vle denominator 0 ∧
        ∀ a ∈ numerators, v.1.relation.vle a denominator}
  point_normalized : ∀ v, (point v).val = map.original.spa v

/-- The tilted rational algebra and comparison are fixed on all coefficients and maps: the original
rational domain is cut out by the sharps of the integral data `T, s`, and the tilted one by their
images in the tilt. -/
structure RationalTiltComparison (P : AffineUntilting p)
    (D : OriginalRationalModel p P) (T : Finset (IntegralRing p P.pair))
    (s : IntegralRing p P.pair) where
  original_numerators : (D.numerators : Set P.pair.ring) =
    sharp p P.pair '' (T : Set (IntegralRing p P.pair))
  original_denominator : D.denominator = sharp p P.pair s
  model : RationalModel p P.tilt.pair
  numerators : (model.numerators : Set P.tilt.pair.ring) =
    TiltModel.integralMap p P.pair P.tilt '' (T : Set (IntegralRing p P.pair))
  denominator : model.denominator = TiltModel.integralMap p P.pair P.tilt s
  comparison : D.affine.tilt.pair ≅ model.affine
  square : comparison.hom ≫ model.map = D.map.tilted

variable {p}

/-- The ring equivalence determined by the two actual inverse pair maps. -/
def ringEquiv {P Q : CharPPerfectoidPair p} (e : P ≅ Q) : P.ring ≃+* Q.ring where
  toFun := e.inv.hom
  invFun := e.hom.hom
  left_inv a := by
    have h := congrArg (fun f : P ⟶ P ↦ f.hom a) e.hom_inv_id
    exact h
  right_inv a := by
    have h := congrArg (fun f : Q ⟶ Q ↦ f.hom a) e.inv_hom_id
    exact h
  map_mul' := map_mul e.inv.hom
  map_add' := map_add e.inv.hom

/-- The same comparison on actual plus rings, using both plus-preserving maps. -/
def plusEquiv {P Q : CharPPerfectoidPair p} (e : P ≅ Q) : P.plus ≃+* Q.plus where
  toFun a := ⟨e.inv.hom a, e.inv.plus _ a.2⟩
  invFun a := ⟨e.hom.hom a, e.hom.plus _ a.2⟩
  left_inv a := Subtype.ext ((ringEquiv e).left_inv a)
  right_inv a := Subtype.ext ((ringEquiv e).right_inv a)
  map_mul' a b := Subtype.ext (map_mul e.inv.hom (a : P.ring) (b : P.ring))
  map_add' a b := Subtype.ext (map_add e.inv.hom (a : P.ring) (b : P.ring))

/-- Rational restriction is identified by its actual inverse bounded map. -/
def RationalTiltComparison.rings {P : AffineUntilting p}
    {D : OriginalRationalModel p P} {T : Finset (IntegralRing p P.pair)}
    {s : IntegralRing p P.pair} (E : RationalTiltComparison p P D T s) :
    D.affine.tilt.pair.ring ≃+* E.model.affine.ring := ringEquiv E.comparison

/-- The normalized rational plus-ring identification. -/
def RationalTiltComparison.plusRings {P : AffineUntilting p}
    {D : OriginalRationalModel p P} {T : Finset (IntegralRing p P.pair)}
    {s : IntegralRing p P.pair} (E : RationalTiltComparison p P D T s) :
    D.affine.tilt.pair.plus ≃+* E.model.affine.plus := plusEquiv E.comparison

end MathlibExt.AlgebraicGeometry.PerfectoidRationalTilting
