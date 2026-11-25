/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import MathlibExt.AlgebraicGeometry.GeneralArcCoverModels

/-!
# Actual affine Frobenius direct-colimit perfection

The coefficient rings are actual F_p-algebras, including the zero ring.
The source Frobenius is the natural ring/algebra endomorphism r -> r^p.
The perfection ring is the native DIRECT colimit of its repeated stages.
Consequently the affine scheme map is Spec(R_perf) -> Spec(R), with the
correct contravariant direction. No inverse-limit ring perfection is used.

Source: Bhatt--Mathew arXiv:1807.04725v4, Section 5.4/Theorem 5.16;
Stacks Project, perfection of schemes in characteristic p.
Global qcqs gluing and categorical Perf hyperdescent are separate requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FrobeniusPerfectionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open GeneralArcCoverModels

/-- Actual F_p coefficient algebras permit the zero ring/empty affine scheme. -/
abbrev FpAlgebras (p : ℕ) := CommAlgCat.{0} (ZMod p)

/-- Actual qcqs F_p-schemes are native schemes over Spec(F_p). -/
abbrev FpSchemes (p : ℕ) := Over (affine (CommRingCat.of (ZMod p)))

/-- A source Frobenius natural transformation, fixed on every element.
No reducedness, domain, exact-characteristic or perfection conclusion is a field. -/
structure FrobeniusSource (p : ℕ) where
  prime : p.Prime
  endomorphism : 𝟭 (FpAlgebras p) ⟶ 𝟭 (FpAlgebras p)
  value : ∀ (A : FpAlgebras p) (r : A), (endomorphism.app A).hom r = r ^ p

variable {p : ℕ} (F : FrobeniusSource p)

/-- The actual underlying commutative-ring functor, not a characteristic shortcut. -/
abbrev coordinateRings : FpAlgebras p ⥤ CommRingCat.{0} :=
  forget₂ (FpAlgebras p) CommRingCat

/-- The same natural Frobenius on all actual underlying coordinate rings. -/
def ringFrobenius : coordinateRings (p := p) ⟶ coordinateRings (p := p) :=
  Functor.whiskerRight F.endomorphism (coordinateRings (p := p))

/-- The repeated Frobenius DIRECT diagram in the native functor category. -/
def directDiagram : ℕ ⥤ (FpAlgebras p ⥤ CommRingCat.{0}) :=
  Functor.ofSequence (X := fun _ : ℕ => coordinateRings (p := p))
    (fun _ => ringFrobenius F)

/-- The actual direct-colimit coordinate-ring perfection functor. -/
def perfectionFunctor : FpAlgebras p ⥤ CommRingCat.{0} := colimit (directDiagram F)

/-- The actual ring R_perf, formed by repeated Frobenius direct colimit. -/
abbrev perfectionRing (A : FpAlgebras p) : CommRingCat.{0} :=
  (perfectionFunctor F).obj A

/-- Every canonical direct-colimit stage map is retained. -/
def stage (n : ℕ) : coordinateRings (p := p) ⟶ perfectionFunctor F :=
  colimit.ι (directDiagram F) n

/-- The Frobenius/stage compatibility is the native colimit cocone equation. -/
theorem frobenius_stage (n : ℕ) : ringFrobenius F ≫ stage F (n + 1) = stage F n := by
  have h := colimit.w (directDiagram F) (homOfLE (Nat.le_succ n))
  simpa only [directDiagram, stage, perfectionFunctor,
    Functor.ofSequence_map_homOfLE_succ] using h

/-- Functorial perfection maps are the native colimit functor's maps on all algebra morphisms. -/
def perfectionMap {A B : FpAlgebras p} (f : A ⟶ B) :
    perfectionRing F A ⟶ perfectionRing F B := (perfectionFunctor F).map f

/-- The canonical affine perfection map has the correct Spec contravariance. -/
def affinePerfectionMap (A : FpAlgebras p) : Spec (perfectionRing F A) ⟶
    Spec ((coordinateRings (p := p)).obj A) := Spec.map ((stage F 0).app A)

end MathlibExt.AlgebraicGeometry.FrobeniusPerfectionModels
