/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_Residual.lean`,
`Theorems/Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff.lean`
and
`P2M/Sol/S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Valuation.RamificationGroup

import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

/-- A classical decidability instance for the algebraic closure of `ℚ`,
needed to form the group of points of a curve over it. -/
noncomputable instance instDecidableEqAlgebraicClosureRat :
    DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

namespace ValuationSubring

variable {L : Type*} [Field L]

/-- A valuation subring lies over the prime `q` when `q` is a non-unit
of the valuation subring. -/
def LiesOverPrime (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

variable (K : Type*) [Field K] [Algebra K L]

/-- The inertia subgroup of a valuation subring, viewed as a subgroup
of the full automorphism group. -/
def inertiaSubgroupIn (A : ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end ValuationSubring

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [Field S]
  [Field K] [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K]
  [Algebra S K] [IsScalarTower R S K]

noncomputable instance instSMulAlgEquiv : SMul (K ≃ₐ[S] K) (W'⁄K).Point :=
  ⟨fun σ P => Point.map σ.toAlgHom P⟩

lemma algEquiv_smul_def (σ : K ≃ₐ[S] K) (P : (W'⁄K).Point) :
    σ • P = Point.map σ.toAlgHom P :=
  rfl

noncomputable instance instDistribMulActionAlgEquiv :
    DistribMulAction (K ≃ₐ[S] K) (W'⁄K).Point where
  one_smul P := by cases P <;> rfl
  mul_smul σ τ P := by cases P <;> rfl
  smul_zero _ := rfl
  smul_add σ P Q := (Point.map σ.toAlgHom).map_add P Q

lemma algEquiv_smul_zsmul (σ : K ≃ₐ[S] K) (m : ℤ)
    (P : (W'⁄K).Point) : σ • (m • P) = m • (σ • P) :=
  (Point.map σ.toAlgHom).map_zsmul m P

lemma smul_mem_torsionBy {n : ℕ} (σ : K ≃ₐ[S] K) {P : (W'⁄K).Point}
    (hP : P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n) :
    σ • P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n := by
  rw [Submodule.mem_torsionBy_iff] at hP ⊢
  rw [← algEquiv_smul_zsmul, hP, smul_zero]

noncomputable instance instSMulTorsionBy (n : ℕ) :
    SMul (K ≃ₐ[S] K) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  ⟨fun σ P => ⟨σ • (P : (W'⁄K).Point), smul_mem_torsionBy σ P.property⟩⟩

noncomputable instance instDistribMulActionTorsionBy (n : ℕ) :
    DistribMulAction (K ≃ₐ[S] K)
      (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  one_smul P := Subtype.ext <| one_smul _ (P : (W'⁄K).Point)
  mul_smul σ τ P := Subtype.ext <| mul_smul σ τ (P : (W'⁄K).Point)
  smul_zero σ := Subtype.ext <| smul_zero (A := (W'⁄K).Point) σ
  smul_add σ P Q :=
    Subtype.ext <| smul_add σ (P : (W'⁄K).Point) (Q : (W'⁄K).Point)

noncomputable instance instModuleZModTorsionBy (n : ℕ) :
    Module (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  AddCommGroup.zmodModule fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ n x]
    exact Submodule.smul_torsionBy _ x

noncomputable instance instSMulCommClassAlgEquivZModTorsionBy (n : ℕ) :
    SMulCommClass (K ≃ₐ[S] K) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  smul_comm σ c x :=
    ZMod.map_smul
      (DistribSMul.toAddMonoidHom
        (Submodule.torsionBy ℤ (W'⁄K).Point n) σ) c x

/-- The Galois representation on `n`-torsion points, as a homomorphism
to module endomorphisms over `ZMod n`. -/
def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →* Module.End (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleEnd (ZMod n)
    (Submodule.torsionBy ℤ (W'⁄K).Point n)

@[simp] lemma galoisRepModuleEnd_apply (W' : Affine R) (n : ℕ)
    (σ : K ≃ₐ[S] K) (x : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRepModuleEnd (S := S) W' n σ x = σ • x :=
  rfl

/-- The representation on `n`-torsion points is unramified at `q` when
every inertia element at every valuation ring above `q` fixes every
`n`-torsion point. -/
def GaloisRepUnramifiedAt (W' : Affine R) (n : ℕ) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring K, A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn S,
    ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x = x

end WeierstrassCurve.Affine.Point

/-- A representation of the absolute Galois group of `ℚ` factors
through a finite level when some finite subextension already captures
its kernel. -/
def GaloisFactorsThroughFiniteLevel {M : Type*} [MulOneClass M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M) : Prop :=
  ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L, σ x = x) → ρ σ = 1

/-- A two-dimensional residual Galois representation of `ℚ`: a
two-dimensional vector space over a field `k` with a Galois action
factoring through a finite level. -/
structure ResidualGaloisRep (k : Type) [Field k] : Type 1 where
  /-- The underlying vector space. -/
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module k V]
  /-- The space is two-dimensional. -/
  finrank_eq : Module.finrank k V = 2
  /-- The Galois action. -/
  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End k V
  /-- The action factors through a finite level. -/
  factorsThroughFiniteLevel : GaloisFactorsThroughFiniteLevel ρ

attribute [instance] ResidualGaloisRep.instAddCommGroup
  ResidualGaloisRep.instModule

instance ResidualGaloisRep.instModuleFinite {k : Type} [Field k]
    (ρ : ResidualGaloisRep k) : Module.Finite k ρ.V :=
  Module.finite_of_finrank_eq_succ ρ.finrank_eq

namespace ResidualGaloisRep

variable {k : Type} [Field k]

/-- A residual representation is unramified at `q` when every inertia
element at every valuation ring above `q` acts trivially. -/
def IsUnramifiedAt (ρ : ResidualGaloisRep k) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ.ρ σ = 1

end ResidualGaloisRep

/-- The residual Galois representation attached to a Weierstrass curve
over `ℚ` at a prime `p`, acting on the `p`-torsion points. -/
def WeierstrassCurve.residualGaloisRepOf (W : WeierstrassCurve ℚ)
    (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (S := ℚ) (K := AlgebraicClosure ℚ) W p)) :
    ResidualGaloisRep (ZMod p) :=
  haveI hfin : Finite
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero
      (hcard ▸ pow_ne_zero 2 (Fact.out (p := p.Prime)).pos.ne')
  { V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p
    finrank_eq := by
      have hp : p.Prime := Fact.out
      have h := Module.natCard_eq_pow_finrank (K := ZMod p)
        (V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p)
      rw [hcard, Nat.card_zmod] at h
      exact (Nat.pow_right_injective hp.two_le h).symm
    ρ := WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (S := ℚ) (K := AlgebraicClosure ℚ) W p
    factorsThroughFiniteLevel := hker }

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in
/-- The residual representation attached to a curve is unramified at
`q` exactly when the Galois action on `p`-torsion points is
unramified at `q`. -/
theorem WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff
    (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (S := ℚ) (K := AlgebraicClosure ℚ) W p))
    (q : ℕ) :
    (W.residualGaloisRepOf p hcard hker).IsUnramifiedAt q ↔
      WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt
        (S := ℚ) (K := AlgebraicClosure ℚ) W p q := by
  refine forall_congr' fun A => forall_congr' fun _ =>
    forall_congr' fun σ => forall_congr' fun _ => ?_
  constructor
  · intro h x
    have hx : σ • x = x := LinearMap.congr_fun h x
    exact hx
  · intro h
    exact LinearMap.ext fun x => h x

end
