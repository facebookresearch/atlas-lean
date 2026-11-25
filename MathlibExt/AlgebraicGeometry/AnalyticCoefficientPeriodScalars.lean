/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticProEtaleCoefficientSources
public import MathlibExt.CategoryTheory.StructuralDeRhamPeriodSources
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.Topology.Instances.ZMod

/-!
# Continuous integral and rational period scalar maps

Integral Witt lifting is fixed on every finite Witt coordinate by the
native `WittVector.fromPadicInt` and the original prime-field tilt units.
The prime-field source must split every continuous finite coefficient
locally on the FULL pro-site; its values are fixed by all native tilt
projections on each such cover. These are source construction requests,
not desired comparison isomorphisms.

Rational coefficients are the full native `Qhat`, with no chosen global
integral lattice. Their p-inversion is the sheaf colimit, retaining
locally varying denominators. Every period scalar map below is
constructed from those units, native Witt sheafification, p-inversion and
the native theta-kernel completion.

References: Scholze, arXiv:1205.3463v2, Sections 6 and 8;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
Native Mathlib Witt-vector/Z_p comparison: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticCoefficientPeriodScalars

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProObjectSites AnalyticProEtaleCoefficientSources
open MathlibExt.CategoryTheory.SheafWittSource
open MathlibExt.CategoryTheory.UntiltingSheafSources
open MathlibExt.CategoryTheory.SheafScalarQuotients
open MathlibExt.CategoryTheory.SheafKernelCompletion

variable (p : ℕ) [Fact p.Prime] (X : AnalyticAdicSpace p) (P : PointRealization p X)
  [HasSheafify (proTopology p X P) CommRingCat.{1}]

abbrev rawIntegral := continuousRings p X P ℤ_[p] ⋙ liftRings
abbrev rawRational := continuousRings p X P ℚ_[p] ⋙ liftRings
abbrev rawPrime := continuousRings p X P (ZMod p) ⋙ liftRings

/-- Original coefficient inclusion on all continuous functions. -/
def integralRationalRaw : rawIntegral p X P ⟶ rawRational p X P where
  app U := CommRingCat.ofHom
    { toFun := fun (a : ULift.{1} C(P.functor.obj U.unop, ℤ_[p])) => ULift.up
        (show C(P.functor.obj U.unop, ℚ_[p]) from
          ⟨fun x => (a.down x : ℚ_[p]), continuous_subtype_val.comp a.down.continuous⟩)
      map_one' := rfl
      map_mul' a b := rfl
      map_zero' := rfl
      map_add' a b := rfl }
  naturality {U V} f := by ext a; rfl

def integralRational : Zhat p X P ⟶ Qhat p X P :=
  (presheafToSheaf (proTopology p X P) CommRingCat.{1}).map (integralRationalRaw p X P)

/-- This source is the sheafified p-inversion comparison, including varying local denominators. -/
structure RationalInversionSource where
  iso : localizeP p (Zhat p X P) ≅ Qhat p X P
  unit_source : localizePUnit p (Zhat p X P) ≫ iso.hom = integralRational p X P

variable (Rplus : Sheaf (proTopology p X P) CommRingCat.{1})

/-- Finite coefficients are pinned locally and in every native inverse-Frobenius projection. -/
structure PrimeTiltSource where
  scalar : rawPrime p X P ⟶ (tilt p Rplus).obj
  split : ∀ (U : (Proetale p X)ᵒᵖ) (a : C(P.functor.obj U.unop, ZMod p)),
    ∃ S : Sieve U.unop, S ∈ proTopology p X P U.unop ∧
      ∀ (V : Proetale p X) (f : V ⟶ U.unop), S f →
        ∃ z : ZMod p, ∀ x, a (P.functor.map f x) = z
  finite_source : ∀ (U : (Proetale p X)ᵒᵖ) (a : C(P.functor.obj U.unop, ZMod p))
    (V : Proetale p X) (f : V ⟶ U.unop) (z : ZMod p),
    (∀ x, a (P.functor.map f x) = z) → ∀ n : ℕ,
      (((tiltProjection p Rplus n).hom.app (op V)).hom)
        (((tilt p Rplus).obj.map f.op).hom ((scalar.app U).hom (ULift.up a))) = z.val

/-- Continuous Witt lifting is fixed on ALL coordinates by the completed native Z_p source. -/
structure IntegralWittSource (F : PrimeTiltSource p X P Rplus) where
  coefficient : ∀ (U : (Proetale p X)ᵒᵖ) (a : C(P.functor.obj U.unop, ℤ_[p])) (n : ℕ),
    C(P.functor.obj U.unop, ZMod p)
  coefficient_source : ∀ U a n x,
    coefficient U a n x = (WittVector.fromPadicInt p (a x)).coeff n
  raw : rawIntegral p X P ⟶ wittPresheaf p (tilt p Rplus)
  witt_source : ∀ U a n,
    ((raw.app U).hom (ULift.up a)).coeff n =
      (F.scalar.app U).hom (ULift.up (coefficient U a n))

namespace IntegralWittSource

variable {F : PrimeTiltSource p X P Rplus} (W : IntegralWittSource p X P Rplus F)
  (Q : RationalInversionSource p X P) (A : UntiltingData p Rplus)

/-- Native sheafification descends the fully coordinate-normalized original Witt map. -/
def integralToInf : Zhat p X P ⟶ inf p Rplus :=
  ((sheafificationAdjunction (proTopology p X P) CommRingCat.{1}).homEquiv
    (rawIntegral p X P) (inf p Rplus)).symm
      (W.raw ≫ toSheafify (proTopology p X P) (wittPresheaf p (tilt p Rplus)))

def integralToRationalInf : Zhat p X P ⟶ rationalInf p Rplus :=
  W.integralToInf ≫ localizePUnit p (inf p Rplus)

/-- Full rational coefficients; no integral module lattice enters this map. -/
def rationalToInf : Qhat p X P ⟶ rationalInf p Rplus :=
  Q.iso.inv ≫ localizePMap p W.integralToInf

def integralToPositive : Zhat p X P ⟶ A.deRhamPositive :=
  W.integralToRationalInf ≫
    completionUnit (rationalInf p Rplus) (completedRegular p Rplus) A.rationalTheta

def rationalToPositive : Qhat p X P ⟶ A.deRhamPositive :=
  rationalToInf (p := p) (X := X) (P := P) (Rplus := Rplus) (W := W) (Q := Q) ≫
    completionUnit (rationalInf p Rplus) (completedRegular p Rplus) A.rationalTheta

end IntegralWittSource

end MathlibExt.AlgebraicGeometry.AnalyticCoefficientPeriodScalars
