/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticNygaardTowers
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.PicardGroup

/-!
# Classical Breuil--Kisin seeds from the actual conormal tower

For a perfect prism with p-torsionfree residue, the seed is the literal
inverse limit of the conormal modules for the products
phi(I) phi^2(I) ... phi^r(I). Transition maps are uniquely fixed by
p times transition = the native conormal inclusion.

The theta reduction is fixed on every finite p-power quotient by dividing
the actual residue of an ideal element by p^r. Thus its map is not a
chosen basis of a freely named line. Its scalar linearization is the
native extension/restriction adjunction map.

This is the classical p-torsionfree perfectoid-base slice of BMS,
arXiv:1802.03261v2, Proposition 6.5 and Remark 6.6. A base seed is free
there. Finite Nygaard quotient twists below use its actual tensor and
dual powers. General invertibility is a filtered statement, and no
unfiltered inverse of their Milnor limit is asserted.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticBreuilKisinSeeds

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)

/-- The actual iterated delta Frobenius, retaining every coefficient map. -/
def phiPower : ℕ → P.ring →+* P.ring
  | 0 => RingHom.id _
  | n + 1 => (DeltaRing.frobenius p P.ring).comp (phiPower n)

/-- The actual kernel products of the theta-tilde Witt projections. -/
def periodIdeal : ℕ → Ideal P.ring
  | 0 => P.ideal.map (phiPower p P 1)
  | n + 1 => periodIdeal n * P.ideal.map (phiPower p P (n + 2))

/-- Adjacent kernel products have their real inclusion. -/
theorem periodIdeal_step_le (n : ℕ) : periodIdeal p P (n + 1) ≤ periodIdeal p P n :=
  Ideal.mul_le_left

/-- Native conormal inclusion, before the source's p division. -/
def ordinaryTransition (n : ℕ) :
    (periodIdeal p P (n + 1)).Cotangent →ₗ[P.ring] (periodIdeal p P n).Cotangent :=
  Ideal.mapCotangent _ _ (AlgHom.id P.ring P.ring) (periodIdeal_step_le p P n)

/-- An actual p-divided conormal tower. Injectivity forces each displayed division uniquely. -/
structure DividedConormalTower where
  transition : ∀ n,
    (periodIdeal p P (n + 1)).Cotangent →ₗ[P.ring] (periodIdeal p P n).Cotangent
  normalization : ∀ (n : ℕ) (x : (periodIdeal p P (n + 1)).Cotangent),
    (p : P.ring) • transition n x = ordinaryTransition p P n x
  p_regular : ∀ n, Function.Injective
    (fun x : (periodIdeal p P n).Cotangent ↦ (p : P.ring) • x)

namespace DividedConormalTower

variable {p P} (T : DividedConormalTower p P)

/-- The actual compatible conormal families form the seed module. -/
def compatible : Submodule P.ring (∀ n : ℕ, (periodIdeal p P n).Cotangent) where
  carrier := {x | ∀ n, T.transition n (x (n + 1)) = x n}
  zero_mem' := by intro n; exact map_zero _
  add_mem' hx hy := by intro n; simp only [Pi.add_apply, map_add, hx n, hy n]
  smul_mem' a x hx := by intro n; simp only [Pi.smul_apply, map_smul, hx n]

/-- The literal inverse-limit carrier, rather than a chosen rank-one module. -/
abbrev SeedModule := ↥T.compatible

/-- The exact finite p-power residue ideal. -/
def residueIdeal : Ideal P.Residue := Ideal.span {(p : P.Residue)}

/-- Native adjacent residue reduction. -/
def residueTransition (n : ℕ) :
    (P.Residue ⧸ (residueIdeal (p := p) (P := P)) ^ (n + 2)) →+*
      (P.Residue ⧸ (residueIdeal (p := p) (P := P)) ^ (n + 1)) :=
  Ideal.Quotient.factor ((residueIdeal (p := p) (P := P)).pow_le_pow_right (by omega))

/-- The canonical finite theta coefficients of the fixed conormal tower. -/
structure ReductionData where
  coefficient : ∀ n,
    (periodIdeal p P n).Cotangent →ₗ[P.ring]
      (P.Residue ⧸ (residueIdeal (p := p) (P := P)) ^ (n + 1))
  divisible : ∀ (n : ℕ) (x : periodIdeal p P n),
    ∃ y : P.Residue, (p : P.Residue) ^ (n + 1) * y =
      Ideal.Quotient.mk P.ideal x.val
  coefficient_generator : ∀ (n : ℕ) (x : periodIdeal p P n) (y : P.Residue),
    (p : P.Residue) ^ (n + 1) * y = Ideal.Quotient.mk P.ideal x.val →
      coefficient n ((periodIdeal p P n).toCotangent x) =
        Ideal.Quotient.mk ((residueIdeal (p := p) (P := P)) ^ (n + 1)) y
  compatibility : ∀ (n : ℕ) (x : (periodIdeal p P (n + 1)).Cotangent),
    coefficient n (T.transition n x) =
      (residueTransition (p := p) (P := P)) n (coefficient (n + 1) x)
  reduction : T.SeedModule →ₗ[P.ring] P.Residue
  reduction_projection : ∀ (n : ℕ) (x : T.SeedModule),
    Ideal.Quotient.mk ((residueIdeal (p := p) (P := P)) ^ (n + 1)) (reduction x) =
      coefficient n (x.val n)

/-- Its actual scalar linearization is fixed by the native adjunction. -/
def ReductionData.linearized (D : T.ReductionData) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk P.ideal)).obj
      (ModuleCat.of P.ring T.SeedModule) ⟶ ModuleCat.of P.Residue P.Residue :=
  ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk P.ideal)).homEquiv _ _).symm
    (ModuleCat.ofHom D.reduction)

end DividedConormalTower

/-- The actual classical seed and canonical reduction, with source-qualified base freeness.
This is construction output, not a general unfiltered twist-invertibility assumption. -/
structure ClassicalSeed where
  tower : DividedConormalTower p P
  reduction : tower.ReductionData
  [free : Module.Free P.ring tower.SeedModule]
  [finite : Module.Finite P.ring tower.SeedModule]
  [invertible : Module.Invertible P.ring tower.SeedModule]
  [reduction_isIso : IsIso reduction.linearized]

/-- The actual seed used in signed finite-quotient tensor powers. -/
def ClassicalSeed.module (L : ClassicalSeed p P) : ModuleCat.{0} P.ring :=
  ModuleCat.of P.ring L.tower.SeedModule

end MathlibExt.AlgebraicGeometry.PrismaticBreuilKisinSeeds
