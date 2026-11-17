/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPowerThomModels
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Geometric finite-group classifying approximations

The regular representation is the literal polynomial affine space with
coordinates H times Fin(m). Its free open is the finite intersection
of the complements of the original fixed linear loci. Each quotient
is an actual finite constant-group torsor on that same free open, with
its action fixed on all scheme-valued coefficient coordinates.

Transition maps append the actual zero block. The classifying object
is the native filtered colimit of the original quotient schemes with a
disjoint basepoint. It is the geometric approximation object used for
B_et H; an ordinary Nisnevich bar construction is not substituted.

Source: Voevodsky, arXiv:math/0107109v1, Section 6 and Theorems 6.14/6.16.
The construction and comparison with the classifying functor remain
source-qualified requests on these explicit native objects and maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicGeometricClassifyingSpaces

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels MotivicFinitePermutationModels
open PointedMotivicModels PointedMotivicQuotients PointedMotivicQuotientMaps

variable {k H : Type} [Field k] [Group H] [Fintype H]

/-- Coordinates of m copies of the original regular representation. -/
abbrev regularRing (k H : Type) [Field k] (m : ℕ) := MvPolynomial (H × Fin m) k

/-- The actual coefficient affine scheme of the regular representation. -/
def regularAffine (m : ℕ) : Scheme.{0} := Spec (.of (regularRing k H m))

/-- Its original k structure map. -/
def regularBase (m : ℕ) : regularAffine (k := k) (H := H) m ⟶ Spec (.of k) :=
  Spec.algebraMap k (regularRing k H m)

/-- Every nonidentity component has its original fixed linear equations. -/
def fixedIdeal (m : ℕ) (h : H) : Ideal (regularRing k H m) :=
  Ideal.span (Set.range fun p : H × Fin m =>
    MvPolynomial.X p - MvPolynomial.X (h⁻¹ * p.1, p.2))

/-- The nonfixed open is the native union of its polynomial basic opens. -/
def nonFixedOpen (m : ℕ) (h : H) : (regularAffine (k := k) (H := H) m).Opens :=
  ⨆ p : H × Fin m,
    PrimeSpectrum.basicOpen (MvPolynomial.X p - MvPolynomial.X (h⁻¹ * p.1, p.2) : regularRing k H m)

/-- The original finite intersection defining the actual free locus. -/
def freeOpen (m : ℕ) : (regularAffine (k := k) (H := H) m).Opens := by
  classical
  exact Finset.univ.inf (fun h : H => if h = 1 then ⊤ else nonFixedOpen (k := k) m h)

/-- The actual open scheme, over the original coefficient field. -/
def freeSpace (m : ℕ) : Over (Spec (.of k)) :=
  Over.mk ((freeOpen (k := k) (H := H) m).ι ≫ regularBase (k := k) (H := H) m)

/-- Every transition is literal zero-extension of the old regular coordinates. -/
def zeroBlockRing (m : ℕ) : regularRing k H (m + 1) →ₐ[k] regularRing k H m :=
  MvPolynomial.aeval fun p : H × Fin (m + 1) =>
    Fin.lastCases 0 (fun j => MvPolynomial.X (p.1, j)) p.2

/-- The same original zero-extension as a native Spec map. -/
def zeroBlockMap (m : ℕ) : regularAffine (k := k) (H := H) m ⟶
    regularAffine (k := k) (H := H) (m + 1) :=
  Spec.map (CommRingCat.ofHom (zeroBlockRing (k := k) (H := H) m).toRingHom)

variable [C : ConstantGroupGeometry (k := k) (H := H)]

/-- A free quotient is on this exact open, with its full regular action fixed. -/
structure RegularFreeQuotient (m : ℕ) where
  quotient : FreeQuotient (k := k) (H := H)
  totalIso : quotient.total.scheme ≅ freeSpace (k := k) (H := H) m

/-- The original open embedding of the quotient's free total space. -/
def RegularFreeQuotient.openMap {m : ℕ} (U : RegularFreeQuotient (k := k) (H := H) m) :
    U.quotient.total.scheme.left ⟶ regularAffine (k := k) (H := H) m :=
  U.totalIso.hom.left ≫ (freeOpen (k := k) (H := H) m).ι

/-- Native polynomial coordinate on every original test scheme. -/
def RegularFreeQuotient.coordinate {m : ℕ} (U : RegularFreeQuotient (k := k) (H := H) m)
    (T : Over (Spec (.of k))) (v : T ⟶ U.quotient.total.scheme) (p : H × Fin m) : Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (regularRing k H m))).inv ≫
    (v.left ≫ U.openMap).appTop).hom (MvPolynomial.X p)

/-- The regular action is fixed at every component, test scheme and coordinate. -/
def RegularFreeQuotient.HasRegularAction {m : ℕ}
    (U : RegularFreeQuotient (k := k) (H := H) m) : Prop :=
  ∀ (T : Over (Spec (.of k))) (h : H) (v : T ⟶ U.quotient.total.scheme) (p : H × Fin m),
    U.coordinate T (U.quotient.actPoint T (MotivicPowerQuotientModels.componentPoint T h) v) p =
      U.coordinate T v (h⁻¹ * p.1, p.2)

/-- Arrows of free quotients retain both base and all group-valued total maps. -/
structure FreeQuotientArrow (U V : FreeQuotient (k := k) (H := H)) where
  total : U.total ⟶ V.total
  base : U.base ⟶ V.base
  projection : total ≫ V.projection = U.projection ≫ base
  equivariant : ∀ (T : Over (Spec (.of k))) (g : T ⟶ constantScheme (k := k) (H := H))
    (u : T ⟶ U.total.scheme),
    U.actPoint T g u ≫ total = V.actPoint T g (u ≫ total)

/-- The geometric approximation sequence uses the original zero-block maps. -/
structure GeometricApproximation where
  step : ∀ m : ℕ, RegularFreeQuotient (k := k) (H := H) m
  action : ∀ m : ℕ, (step m).HasRegularAction
  transition : ∀ m : ℕ, FreeQuotientArrow (step m).quotient (step (m + 1)).quotient
  affine_normalization : ∀ m : ℕ,
    (transition m).total.left ≫ (step (m + 1)).openMap =
      (step m).openMap ≫ zeroBlockMap (k := k) (H := H) m

/-- Actual quotient schemes and their original transition arrows. -/
def quotientSequence (A : GeometricApproximation (k := k) (H := H)) : ℕ ⥤ SmoothScheme k :=
  Functor.ofSequence (X := fun m => (A.step m).quotient.base) (fun m => (A.transition m).base)

/-- The native represented sequence retains those same whole scheme maps. -/
def pointedSequence (A : GeometricApproximation (k := k) (H := H)) :
    ℕ ⥤ PointedSpaces (k := k) :=
  Functor.ofSequence (X := fun m => representedPointed (A.step m).quotient.base)
    (fun m => representedMap (A.transition m).base)

/-- The geometric classifying object is this actual colimit, with disjoint basepoint. -/
def geometricClassifyingSpace (A : GeometricApproximation (k := k) (H := H)) :
    PointedSpaces (k := k) := colimit (pointedSequence A)

/-- Every finite stage enters through its actual native colimit cocone. -/
def stageMap (A : GeometricApproximation (k := k) (H := H)) (m : ℕ) :
    representedPointed (A.step m).quotient.base ⟶ geometricClassifyingSpace A :=
  colimit.ι (pointedSequence A) m

/-- The original regular vector at the identity, with all other coordinates zero. -/
def deltaVectorRing : regularRing k H 1 →ₐ[k] k := by
  classical
  exact MvPolynomial.aeval (fun p : H × Fin 1 => if p.1 = 1 then 1 else 0)

/-- The same identity vector as its actual native affine point. -/
def deltaVectorPoint : Spec (.of k) ⟶ regularAffine (k := k) (H := H) 1 :=
  Spec.map (CommRingCat.ofHom (deltaVectorRing (k := k) (H := H)).toRingHom)

/-- A basepoint is the actual trivial torsor represented by that fixed free vector. -/
structure BasedApproximation (P : SmoothProductSystem k)
    (A : GeometricApproximation (k := k) (H := H)) where
  lift : P.unit.scheme ⟶ (A.step 1).quotient.total.scheme
  normalization : lift.left ≫ (A.step 1).openMap =
    P.unitIso.hom ≫ deltaVectorPoint (k := k) (H := H)

/-- The classifying-space basepoint is the original free vector followed by the quotient cocone. -/
def basepointMap {P : SmoothProductSystem k} {A : GeometricApproximation (k := k) (H := H)}
    (B : BasedApproximation P A) : representedPointed P.unit ⟶ geometricClassifyingSpace A :=
  representedMap (B.lift ≫ (A.step 1).quotient.projection) ≫ stageMap A 1

/-- The original structural maps give the complete native projection cocone. -/
def structuralCocone (P : SmoothProductSystem k) (A : GeometricApproximation (k := k) (H := H)) :
    Cocone (pointedSequence A) where
  pt := representedPointed P.unit
  ι := NatTrans.ofSequence (fun m =>
    representedMap (MotivicFinitePowerCycles.unitMap P (A.step m).quotient.base)) (by
      intro m
      simp only [pointedSequence, Functor.ofSequence_map_homOfLE_succ,
        Functor.const_obj_map]
      rw [← representedMap_comp]
      apply congrArg representedMap
      apply Over.OverMorphism.ext
      change (A.transition m).base.left ≫
        ((A.step (m + 1)).quotient.base.scheme.hom ≫ P.unitIso.inv) =
          (A.step m).quotient.base.scheme.hom ≫ P.unitIso.inv
      rw [← Category.assoc, Over.w (A.transition m).base])

/-- The geometric classifying projection is the native map of that actual colimit cocone. -/
def geometricProjection (P : SmoothProductSystem k) (A : GeometricApproximation (k := k) (H := H)) :
    geometricClassifyingSpace A ⟶ representedPointed P.unit :=
  colimit.desc (pointedSequence A) (structuralCocone P A)

end MathlibExt.AlgebraicGeometry.MotivicGeometricClassifyingSpaces
