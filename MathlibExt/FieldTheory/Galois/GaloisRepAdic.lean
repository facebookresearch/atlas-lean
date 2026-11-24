/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_Adic.lean` and
`Definitions/Def_GaloisRep_ResidualEquiv.lean`
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

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import MathlibExt.FieldTheory.Galois.ResidualGaloisRep
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
public import MathlibExt.RingTheory.Valuation.LiesOverPrime
import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open scoped TensorProduct

universe u v

namespace ResidualGaloisRep

variable {k : Type u} [Field k]

/-- An equivalence of residual Galois representations: a linear equivalence
of the representation spaces intertwining the Galois actions. -/
public structure Equiv (ρ₁ ρ₂ : ResidualGaloisRep k) where
  /-- The linear equivalence of representation spaces. -/
  toLinearEquiv : ρ₁.V ≃ₗ[k] ρ₂.V
  /-- The equivalence intertwines the Galois actions. -/
  map_apply : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ₁.V),
    toLinearEquiv (ρ₁.ρ σ x) = ρ₂.ρ σ (toLinearEquiv x)

/-- Two residual Galois representations are equivalent when there is an
equivalence between them. -/
public def IsEquiv (ρ₁ ρ₂ : ResidualGaloisRep k) : Prop :=
  Nonempty (Equiv ρ₁ ρ₂)

namespace Equiv

/-- The identity equivalence of a residual Galois representation. -/
public def refl (ρ : ResidualGaloisRep k) : Equiv ρ ρ where
  toLinearEquiv := LinearEquiv.refl k ρ.V
  map_apply _ _ := rfl

/-- The inverse of an equivalence of residual Galois representations. -/
public def symm {ρ₁ ρ₂ : ResidualGaloisRep k} (e : Equiv ρ₁ ρ₂) :
    Equiv ρ₂ ρ₁ where
  toLinearEquiv := e.toLinearEquiv.symm
  map_apply σ x := by
    apply e.toLinearEquiv.injective
    rw [e.map_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The composite of equivalences of residual Galois representations. -/
public def trans {ρ₁ ρ₂ ρ₃ : ResidualGaloisRep k} (e₁₂ : Equiv ρ₁ ρ₂)
    (e₂₃ : Equiv ρ₂ ρ₃) : Equiv ρ₁ ρ₃ where
  toLinearEquiv := e₁₂.toLinearEquiv.trans e₂₃.toLinearEquiv
  map_apply σ x := by
    rw [LinearEquiv.trans_apply, e₁₂.map_apply, e₂₃.map_apply,
      LinearEquiv.trans_apply]

end Equiv

end ResidualGaloisRep

/-- A Galois action on a module over a local ring is adically continuous
when, at every finite level, it is trivial modulo that power of the maximal
ideal on vectors fixed by a finite level of the Galois group. -/
public def GaloisActionIsAdicContinuous (A : Type u) [CommRing A]
    [IsLocalRing A] {V : Type v} [AddCommGroup V] [Module A V]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V) :
    Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
    FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L, σ x = x) →
      ∀ v : V, ρ σ v - v ∈ (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A V)

/-- A two-dimensional adic Galois representation over a local ring: a free
finite module of rank two with an adically continuous Galois action. -/
public structure GaloisRepAdic (A : Type u) [CommRing A] [IsLocalRing A] :
    Type (max u v + 1) where
  /-- The underlying module. -/
  V : Type v
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module A V]
  [instFree : Module.Free A V]
  [instFinite : Module.Finite A V]
  /-- The module has rank two. -/
  finrank_eq : Module.finrank A V = 2
  /-- The Galois action. -/
  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V
  /-- The Galois action is adically continuous. -/
  isAdicContinuous : GaloisActionIsAdicContinuous A ρ

attribute [instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instModule
  GaloisRepAdic.instFree GaloisRepAdic.instFinite

namespace GaloisRepAdic

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- An adic Galois representation is unramified at `q` when every element
of an inertia subgroup over `q` acts trivially. -/
public def IsUnramifiedAt (ρ : GaloisRepAdic A) (q : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1

/-- The determinant of an adic Galois representation, as a character with
values in the units of the coefficient ring. -/
public noncomputable def det (ρ : GaloisRepAdic A) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ :=
  (LinearMap.det.comp ρ.ρ).toHomUnits

/-- The trace of a Galois element in an adic Galois representation. -/
public noncomputable def trace (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : A :=
  LinearMap.trace A ρ.V (ρ.ρ σ)

/-- Base change of an adic Galois representation along a local ring
homomorphism. -/
public noncomputable def baseChangeAlong {B : Type v} [CommRing B]
    [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic A) : GaloisRepAdic B :=
  letI : Algebra A B := φ.toAlgebra
  { V := B ⊗[A] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange B
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    isAdicContinuous := by
      intro n
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous n
      refine ⟨L, hL, fun σ hσ => ?_⟩
      have hmap : (IsLocalRing.maximalIdeal A ^ n).map φ ≤
          IsLocalRing.maximalIdeal B ^ n := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun a ha =>
          Ideal.mem_comap.mpr (haveI := hφ; map_nonunit φ a ha)) n
      have hpure : ∀ (b : B) (v : ρ.V),
          (ρ.ρ σ).baseChange B (b ⊗ₜ[A] v) - b ⊗ₜ[A] v ∈
            (IsLocalRing.maximalIdeal B ^ n) • (⊤ : Submodule B (B ⊗[A] ρ.V)) := by
        intro b v
        rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub]
        refine Submodule.smul_induction_on (p := fun x => b ⊗ₜ[A] x ∈
          (IsLocalRing.maximalIdeal B ^ n) • (⊤ : Submodule B (B ⊗[A] ρ.V)))
          (h1 σ hσ v) ?_ ?_
        · intro a ha w _
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
            ← smul_eq_mul, ← TensorProduct.smul_tmul']
          exact Submodule.smul_mem_smul (hmap (Ideal.mem_map_of_mem φ ha))
            Submodule.mem_top
        · intro x y hx hy
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hx hy
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
      | tmul b v => exact hpure b v
      | add x y hx hy =>
        rw [map_add, add_sub_add_comm]
        exact Submodule.add_mem _ hx hy }

/-- The residual representation of an adic Galois representation, obtained
by base change to the residue field. -/
public noncomputable def residual (ρ : GaloisRepAdic A) :
    ResidualGaloisRep (IsLocalRing.ResidueField A) :=
  { V := IsLocalRing.ResidueField A ⊗[A] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous 1
      refine ⟨L, hL, fun σ hσ => ?_⟩
      have hkill : ∀ x ∈ (IsLocalRing.maximalIdeal A ^ 1) • (⊤ : Submodule A ρ.V),
          ∀ c : IsLocalRing.ResidueField A, c ⊗ₜ[A] x = 0 := by
        intro x hx c
        refine Submodule.smul_induction_on
          (p := fun x => c ⊗ₜ[A] x = (0 : IsLocalRing.ResidueField A ⊗[A] ρ.V))
          hx ?_ ?_
        · intro a ha w _
          rw [pow_one] at ha
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
            IsLocalRing.ResidueField.algebraMap_eq,
            (IsLocalRing.residue_eq_zero_iff a).mpr ha, zero_mul,
            TensorProduct.zero_tmul]
        · intro x y hx hy
          rw [TensorProduct.tmul_add, hx, hy, add_zero]
      refine LinearMap.ext fun w => ?_
      rw [MonoidHom.coe_mk, OneHom.coe_mk]
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul c v =>
        rw [LinearMap.baseChange_tmul, Module.End.one_apply, ← sub_eq_zero,
          ← TensorProduct.tmul_sub]
        exact hkill _ (h1 σ hσ v) c
      | add x y hx hy => rw [map_add, map_add, hx, hy] }

/-- An equivalence of adic Galois representations. -/
public structure Equiv (ρ₁ ρ₂ : GaloisRepAdic A) where
  /-- The linear equivalence of representation spaces. -/
  toLinearEquiv : ρ₁.V ≃ₗ[A] ρ₂.V
  /-- The equivalence intertwines the Galois actions. -/
  map_apply : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ₁.V),
    toLinearEquiv (ρ₁.ρ σ x) = ρ₂.ρ σ (toLinearEquiv x)

/-- Two adic Galois representations are equivalent when there is an
equivalence between them. -/
public def IsEquiv (ρ₁ ρ₂ : GaloisRepAdic A) : Prop :=
  Nonempty (Equiv ρ₁ ρ₂)

namespace Equiv

/-- The identity equivalence of an adic Galois representation. -/
public def refl (ρ : GaloisRepAdic A) : Equiv ρ ρ :=
  { toLinearEquiv := LinearEquiv.refl A ρ.V
    map_apply := fun _ _ => rfl }

/-- The inverse of an equivalence of adic Galois representations. -/
public def symm {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂) : Equiv ρ₂ ρ₁ :=
  { toLinearEquiv := e.toLinearEquiv.symm
    map_apply := fun σ y => e.toLinearEquiv.injective (by
      rw [LinearEquiv.apply_symm_apply, e.map_apply,
        LinearEquiv.apply_symm_apply]) }

/-- The composite of equivalences of adic Galois representations. -/
public def trans {ρ₁ ρ₂ ρ₃ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (e' : Equiv ρ₂ ρ₃) : Equiv ρ₁ ρ₃ :=
  { toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
    map_apply := fun σ x => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e.map_apply,
        e'.map_apply] }

/-- Base change of an equivalence of adic Galois representations. -/
public noncomputable def baseChangeAlong {B : Type v} [CommRing B]
    [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ)
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂) :
    Equiv (ρ₁.baseChangeAlong φ hφ) (ρ₂.baseChangeAlong φ hφ) :=
  letI : Algebra A B := φ.toAlgebra
  { toLinearEquiv := e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V
    map_apply := fun σ x => by
      show e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V ((ρ₁.ρ σ).baseChange B x) =
        (ρ₂.ρ σ).baseChange B (e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, e.map_apply]
      | add x y hx hy => simp only [map_add, hx, hy] }

/-- The residual equivalence induced by an equivalence of adic Galois
representations. -/
public noncomputable def residual {ρ₁ ρ₂ : GaloisRepAdic A}
    (e : Equiv ρ₁ ρ₂) :
    ResidualGaloisRep.Equiv ρ₁.residual ρ₂.residual :=
  { toLinearEquiv :=
      e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V
    map_apply := fun σ x => by
      show e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V
          ((ρ₁.ρ σ).baseChange (IsLocalRing.ResidueField A) x) =
        (ρ₂.ρ σ).baseChange (IsLocalRing.ResidueField A)
          (e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, e.map_apply]
      | add x y hx hy => simp only [map_add, hx, hy] }

end Equiv

/-- The residual representation underlying an adic representation over a
field, viewed as an adic representation itself. -/
public def toResidualGaloisRep {k : Type u} [Field k] (ρ : GaloisRepAdic k) :
    ResidualGaloisRep k :=
  { V := ρ.V
    finrank_eq := ρ.finrank_eq
    ρ := ρ.ρ
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous 1
      refine ⟨L, hL, fun σ hσ => LinearMap.ext fun v => ?_⟩
      have hbot : IsLocalRing.maximalIdeal k = ⊥ :=
        (Ideal.eq_bot_or_top _).resolve_right
          (Ideal.IsMaximal.ne_top inferInstance)
      have h := h1 σ hσ v
      rw [hbot, pow_one, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at h
      exact h }

/-- An adic Galois representation over a field obtained from a residual
Galois representation. -/
public def ofResidualGaloisRep {k : Type u} [Field k]
    (ρ : ResidualGaloisRep k) : GaloisRepAdic k :=
  { V := ρ.V
    finrank_eq := ρ.finrank_eq
    ρ := ρ.ρ
    isAdicContinuous := by
      intro n
      obtain ⟨L, hL, h1⟩ := ρ.factorsThroughFiniteLevel
      refine ⟨L, hL, fun σ hσ v => ?_⟩
      rw [h1 σ hσ, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _ }

end GaloisRepAdic
