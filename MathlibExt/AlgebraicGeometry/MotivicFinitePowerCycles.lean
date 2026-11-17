/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPermutationBundleModels
public import MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Literal finite external powers with ring coefficients

Finite products are the native iterated scheme products over the original
field. The zero-fold object is the original field spectrum presentation,
and its cycle is the identity graph with coefficient one. Higher powers
multiply every original coefficient and retain every integral product
component and its actual generic local-ring length. Pullback and target
maps use the original graph and correspondence composition sources.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3. The external
product source is the existing finite transfer product, including its
nonreduced/inseparable multiplicities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicFinitePowerCycles

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels

variable {k : Type} [Field k]

/-- The original integral support generators with actual ring coefficients. -/
abbrev CoefficientCycles (U X : SmoothScheme k) (R : Type 1) [CommRing R] :=
  Generator U X →₀ R

/-- Native scalar extension of all original integral cycle multiplicities. -/
def cycleWithCoefficient {U X : SmoothScheme k} (R : Type 1) [CommRing R]
    (z : Cycles U X) (c : R) : CoefficientCycles U X R :=
  z.sum fun g m => Finsupp.single g ((m : R) * c)

/-- Correspondence composition uses the original intersection geometry and all coefficients. -/
def composeCoefficient (D : CompositionSystem k) (R : Type 1) [CommRing R]
    {U X Y : SmoothScheme k} (a : CoefficientCycles U X R)
    (b : CoefficientCycles X Y R) : CoefficientCycles U Y R :=
  a.sum fun g r => b.sum fun h s =>
    cycleWithCoefficient R (D.geometry U X Y g h).cycle (r * s)

/-- External multiplication uses the actual product components, lengths and coefficient products. -/
def externalCoefficient {P : SmoothProductSystem k} (E : ExternalSystem P)
    (R : Type 1) [CommRing R] {U X V Y : SmoothScheme k}
    (a : CoefficientCycles U X R) (b : CoefficientCycles V Y R) :
    CoefficientCycles (P.obj U V) (P.obj X Y) R :=
  a.sum fun g r => b.sum fun h s =>
    cycleWithCoefficient R (E.geometry U X V Y g h).cycle (r * s)

/-- The coefficient identity is the original scheme identity graph. -/
def identityCoefficient (G : GraphSystem k) (R : Type 1) [CommRing R]
    (U : SmoothScheme k) : CoefficientCycles U U R :=
  cycleWithCoefficient R (graphCycle G (𝟙 U)) 1

/-- All finite powers use the same original native smooth product system. -/
def powerObj (P : SmoothProductSystem k) (X : SmoothScheme k) : ℕ → SmoothScheme k
  | 0 => P.unit
  | n + 1 => P.obj X (powerObj P X n)

/-- The native map to the original field-spectrum unit presentation. -/
def unitMap (P : SmoothProductSystem k) (X : SmoothScheme k) : X ⟶ P.unit :=
  Over.homMk (X.scheme.hom ≫ P.unitIso.inv) (by
    rw [P.unit_base]
    simp)

/-- The pair is computed by the actual Cartesian scheme lift. -/
def productLift (P : SmoothProductSystem k) {T X Y : SmoothScheme k}
    (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ P.obj X Y :=
  Over.homMk (pullback.lift f.left g.left (by rw [Over.w f, Over.w g]) ≫
    (P.geometry X Y).iso.inv) (by
      dsimp only [SmoothProductSystem.obj, productScheme] at *
      rw [← (P.geometry X Y).base_eq]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst_assoc]
      exact Over.w f)

/-- The first coordinate is the original first map. -/
theorem productLift_fst (P : SmoothProductSystem k) {T X Y : SmoothScheme k}
    (f : T ⟶ X) (g : T ⟶ Y) :
    productLift P f g ≫ (P.geometry X Y).fst = f := by
  apply Over.OverMorphism.ext
  change (pullback.lift f.left g.left _ ≫ (P.geometry X Y).iso.inv) ≫
    ((P.geometry X Y).iso.hom ≫ pullback.fst X.scheme.hom Y.scheme.hom) = f.left
  simp only [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- The second coordinate is the original second map. -/
theorem productLift_snd (P : SmoothProductSystem k) {T X Y : SmoothScheme k}
    (f : T ⟶ X) (g : T ⟶ Y) :
    productLift P f g ≫ (P.geometry X Y).snd = g := by
  apply Over.OverMorphism.ext
  change (pullback.lift f.left g.left _ ≫ (P.geometry X Y).iso.inv) ≫
    ((P.geometry X Y).iso.hom ≫ pullback.snd X.scheme.hom Y.scheme.hom) = g.left
  simp only [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- Native coordinate projections, including the genuinely empty zero-fold index. -/
def powerProjection (P : SmoothProductSystem k) (X : SmoothScheme k) :
    ∀ n : ℕ, Fin n → (powerObj P X n ⟶ X)
  | 0, j => Fin.elim0 j
  | n + 1, j => Fin.cases (P.geometry X (powerObj P X n)).fst
      (fun i => (P.geometry X (powerObj P X n)).snd ≫ powerProjection P X n i) j

/-- The full diagonal repeats the original scheme map in every coordinate. -/
def powerDiagonal (P : SmoothProductSystem k) (X : SmoothScheme k) :
    ∀ n : ℕ, X ⟶ powerObj P X n
  | 0 => unitMap P X
  | n + 1 => productLift P (𝟙 X) (powerDiagonal P X n)

/-- All diagonal coordinates are the actual identity, including every finite index. -/
theorem powerDiagonal_projection (P : SmoothProductSystem k) (X : SmoothScheme k)
    (n : ℕ) (j : Fin n) : powerDiagonal P X n ≫ powerProjection P X n j = 𝟙 X := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · exact productLift_fst P (𝟙 X) (powerDiagonal P X n)
    · change (productLift P (𝟙 X) (powerDiagonal P X n)) ≫
        ((P.geometry X (powerObj P X n)).snd ≫ powerProjection P X n i) = _
      rw [← Category.assoc, productLift_snd, ih]

/-- The whole product map uses both native functor coordinates. -/
def productMap (P : SmoothProductSystem k) {X X' Y Y' : SmoothScheme k}
    (f : X ⟶ X') (g : Y ⟶ Y') : P.obj X Y ⟶ P.obj X' Y' :=
  (P.tensor.map f).app Y ≫ (P.tensor.obj X').map g

/-- Finite power of the original cycle, before any quotient or operation theorem. -/
def externalPower {P : SmoothProductSystem k} (E : ExternalSystem P) (G : GraphSystem k)
    (R : Type 1) [CommRing R] {X Y : SmoothScheme k}
    (z : CoefficientCycles X Y R) :
    ∀ n : ℕ, CoefficientCycles (powerObj P X n) (powerObj P Y n) R
  | 0 => identityCoefficient G R P.unit
  | n + 1 => externalCoefficient E R z (externalPower E G R z n)

/-- Pulling the external power along product with U retains the original identity-U graph. -/
def externalPowerWithU {P : SmoothProductSystem k} (E : ExternalSystem P)
    (G : GraphSystem k) (R : Type 1) [CommRing R] {X Y : SmoothScheme k}
    (z : CoefficientCycles X Y R) (n : ℕ) (U : SmoothScheme k) :
    CoefficientCycles (P.obj (powerObj P X n) U) (P.obj (powerObj P Y n) U) R :=
  externalCoefficient E R (externalPower E G R z n) (identityCoefficient G R U)

end MathlibExt.AlgebraicGeometry.MotivicFinitePowerCycles
