/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralFlagSchemes
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fin.Rev

/-!
# Actual determinantal Schubert and opposite Schubert subschemes

Rank equations are literal minors of E_q → C^n/F_p. Taking all dual rows
of the actual finite projective quotient gives the determinantal ideal
without selecting a global frame for that quotient. The ideal-sheaf model
is normalized after pullback to every affine algebra; this retains all
nilpotent scheme equations. Its Schubert scheme is the native subscheme
of that ideal, and its Richardson scheme is the native sum of the ideals.

Source: Brion, math/0410240v1, Proposition 1.1.3, section 1.2 and
Definition 1.2.4, X^w = w0 X_(w0 w). Native minor/ideal-sheaf/subscheme
primitives are Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0 (Joël Riou, Andrew Yang and Mathlib contributors; dependency
source headers are retained). No reduced point-set closure defines these
subschemes.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchubertRankSchemes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GeneralFlagSchemes
open scoped TensorProduct

def rankCount {n : ℕ} (w : Equiv.Perm (Fin n)) (p q : Fin (n + 1)) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ i.val < p.val ∧ (w i).val < q.val).card

def bruhatLE {n : ℕ} (v w : Equiv.Perm (Fin n)) : Prop :=
  ∀ p q : Fin (n + 1), rankCount w p q ≤ rankCount v p q

def length {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n ↦ ij.1 < ij.2 ∧ w ij.2 < w ij.1).card

def downwardCover {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  i < j ∧ bruhatLE (w * Equiv.swap i j) w ∧
    length (w * Equiv.swap i j) + 1 = length w

/-- A literal basis vector of the standard (or opposite) coordinate q-plane. -/
def coordinateVector (A : CommAlgCat.{0} ℂ) {n : ℕ} (q : Fin (n + 1))
    (opposite : Bool) (i : Fin q.val) : ExtendedSpace A n :=
  let j : Fin n := Fin.castLE (Nat.le_of_lt_succ q.isLt) i
  TensorProduct.tmul ℂ (1 : A) (Pi.single (if opposite then j.rev else j) 1)

/-- Literal minors on the actual quotient; rows are all actual A-linear
functionals, so this definition applies to a projective quotient. -/
def rankMinor (A : CommAlgCat.{0} ℂ) {n : ℕ}
    (N : Submodule A (ExtendedSpace A n)) (q : Fin (n + 1)) (r : ℕ) (opposite : Bool)
    (rows : Fin (r + 1) → Module.Dual A (ExtendedSpace A n ⧸ N))
    (cols : Fin (r + 1) ↪ Fin q.val) : A :=
  Matrix.det (fun i j : Fin (r + 1) ↦ rows i (N.mkQ (coordinateVector A q opposite (cols j))))

def rankIdeal (A : CommAlgCat.{0} ℂ) {n : ℕ}
    (N : Submodule A (ExtendedSpace A n)) (q : Fin (n + 1)) (r : ℕ) (opposite : Bool) : Ideal A :=
  Ideal.span (Set.range fun x :
    (Fin (r + 1) → Module.Dual A (ExtendedSpace A n ⧸ N)) ×
      (Fin (r + 1) ↪ Fin q.val) ↦ rankMinor A N q r opposite x.1 x.2)

def schubertAffineIdeal (A : CommAlgCat.{0} ℂ) {n : ℕ} {D : Shape n}
    (F : AffineFlag A n D) (w : Equiv.Perm (Fin n)) (opposite : Bool) : Ideal A :=
  let v := if opposite then Fin.revPerm * w else w
  ⨆ p : Step D, ⨆ q : Fin (n + 1),
    rankIdeal A (F.term p).toSubmodule q (q.val - rankCount v p.val q) opposite

/-- The literal affine ideal of an actual pulled-back ideal sheaf. -/
def affinePullbackIdeal {n : ℕ} {D : Shape n} (F : FlagSchemeModel n D)
    (I : F.scheme.left.IdealSheafData) (A : CommAlgCat.{0} ℂ)
    (f : affineScheme A ⟶ F.scheme) : Ideal A :=
  Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (Scheme.IdealSheafData.equivOfIsAffine (I.comap f.left))

structure SchubertIdealModel {n : ℕ} {D : Shape n} (F : FlagSchemeModel n D)
    (w : Equiv.Perm (Fin n)) (opposite : Bool) where
  ideal : F.scheme.left.IdealSheafData
  normalization : ∀ (A : CommAlgCat.{0} ℂ) (f : affineScheme A ⟶ F.scheme),
    affinePullbackIdeal F ideal A f = schubertAffineIdeal A (F.points A f) w opposite

def SchubertIdealModel.scheme {n : ℕ} {D : Shape n} {F : FlagSchemeModel n D}
    {w : Equiv.Perm (Fin n)} {opposite : Bool} (S : SchubertIdealModel F w opposite) :
    PerverseSheaves.ComplexScheme :=
  Over.mk (S.ideal.subschemeι ≫ F.scheme.hom)

def SchubertIdealModel.inclusion {n : ℕ} {D : Shape n} {F : FlagSchemeModel n D}
    {w : Equiv.Perm (Fin n)} {opposite : Bool} (S : SchubertIdealModel F w opposite) :
    S.scheme ⟶ F.scheme := Over.homMk S.ideal.subschemeι rfl

/-- Actual scheme-theoretic intersection, with the sum of both ideals. -/
def richardson {n : ℕ} {D : Shape n} {F : FlagSchemeModel n D}
    {v w : Equiv.Perm (Fin n)} (S : SchubertIdealModel F w false)
    (O : SchubertIdealModel F v true) : PerverseSheaves.ComplexScheme :=
  Over.mk ((S.ideal ⊔ O.ideal).subschemeι ≫ F.scheme.hom)

end MathlibExt.AlgebraicGeometry.SchubertRankSchemes
