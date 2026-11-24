/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Actual Plucker bounds on theta-adic modification lattices

Coordinates are computed from a genuine integral lattice basis by its
native scalar extension and the existing full localization map. Every
minor is the determinant of actual vectors in the second lattice.
For a decreasing coweight, the r-th integrality exponent is the sum of
its smallest r entries; the top exterior line has the exact total
exponent. This retains negative weights and finite-projective lattices.

The definitions specialize to the original B_dR-plus and its true
filtration-one generator. Schubert representability and the comparison
with the geometric relative-position condition remain separate requests.
Source: Fargues--Scholze, arXiv:2102.13459v4, Section VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PeriodLatticePluckerBounds

open MathlibExt.LinearAlgebra.LocalizedLattices
open scoped TensorProduct

variable (R : Type) [CommRing R] (r : R) (n : ℕ)

def parameterUnit : (FractionRing R r)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := FractionRing R r) r).unit

def scalarLine (m : ℤ) : Submodule R (FractionRing R r) :=
  Submodule.span R {a | ∃ b : R,
    a = ((parameterUnit R r ^ m : (FractionRing R r)ˣ) : FractionRing R r) * algebraMap R _ b}

def tailSum (weight : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ n - k ≤ i.val), weight i

def IsDominant (weight : Fin n → ℤ) : Prop := Antitone weight

def DominanceLE (weight bound : Fin n → ℤ) : Prop :=
  tailSum n weight n = tailSum n bound n ∧
    ∀ k : ℕ, k ≤ n → tailSum n bound k ≤ tailSum n weight k

/-- The coordinate basis is the literal extended integral basis followed by full localization. -/
def coordinates (L : Lattice R r n) (e : Module.Basis (Fin n) R L.module) :
    Ambient R r n ≃ₗ[FractionRing R r] (Fin n → FractionRing R r) :=
  ((e.baseChange (FractionRing R r)).map
    (LinearEquiv.ofBijective (localizationMap R r n L.module) L.full)).equivFun

def minor (L M : Lattice R r n) (e : Module.Basis (Fin n) R L.module)
    (k : ℕ) (rows : Fin k → Fin n) (v : Fin k → M.module) : FractionRing R r :=
  Matrix.det (fun i j ↦ coordinates R r n L e (v j).val (rows i))

def determinantModule (L M : Lattice R r n) (e : Module.Basis (Fin n) R L.module) :
    Submodule R (FractionRing R r) :=
  Submodule.span R {a | ∃ v : Fin n → M.module, a = minor R r n L M e n id v}

/-- The actual closed Plucker conditions, with the normalized determinant component. -/
def IsBoundedBy (L M : Lattice R r n) (e : Module.Basis (Fin n) R L.module)
    (weight : Fin n → ℤ) : Prop :=
  IsDominant n weight ∧
    (∀ (k : ℕ), k ≤ n → ∀ (rows : Fin k → Fin n), Function.Injective rows →
      ∀ v : Fin k → M.module,
        minor R r n L M e k rows v ∈ scalarLine R r (tailSum n weight k)) ∧
    determinantModule R r n L M e = scalarLine R r (tailSum n weight n)

end MathlibExt.AlgebraicGeometry.PeriodLatticePluckerBounds
