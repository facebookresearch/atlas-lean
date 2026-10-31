/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq.lean`
and
`P2M/Sol/S_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq.lean`
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

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped TensorProduct

universe u

namespace IsPushoutOfUnivAux

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']

private noncomputable def alphaR : S ⊗[R] R' →ₐ[R] S' :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S S')
    (IsScalarTower.toAlgHom R R' S') (fun _ _ => Commute.all _ _)

private lemma alphaR_tmul (s : S) (r : R') :
    (alphaR : S ⊗[R] R' →ₐ[R] S') (s ⊗ₜ r) =
      algebraMap S S' s * algebraMap R' S' r := by
  simp [alphaR, Algebra.TensorProduct.lift_tmul]

private lemma algebraMap_right_apply (r : R') :
    algebraMap R' (S ⊗[R] R') r = (1 : S) ⊗ₜ[R] r := rfl

private noncomputable def alpha : S ⊗[R] R' →ₐ[R'] S' :=
  { (alphaR : S ⊗[R] R' →ₐ[R] S').toRingHom with
    commutes' := fun r => by
      change (alphaR : S ⊗[R] R' →ₐ[R] S').toRingHom
          (algebraMap R' (S ⊗[R] R') r) = _
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algebraMap_right_apply, alphaR_tmul,
        map_one, one_mul] }

private lemma alpha_apply (x : S ⊗[R] R') :
    (alpha : S ⊗[R] R' →ₐ[R'] S') x = (alphaR : S ⊗[R] R' →ₐ[R] S') x := rfl

private lemma alpha_tmul (s : S) (r : R') :
    (alpha : S ⊗[R] R' →ₐ[R'] S') (s ⊗ₜ r) =
      algebraMap S S' s * algebraMap R' S' r := by
  rw [alpha_apply, alphaR_tmul]

private lemma alpha_comp_algebraMap :
    (alpha : S ⊗[R] R' →ₐ[R'] S').toRingHom.comp
        (algebraMap S (S ⊗[R] R')) = algebraMap S S' := by
  ext s
  change (alpha : S ⊗[R] R' →ₐ[R'] S') (algebraMap S (S ⊗[R] R') s) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    alpha_tmul, map_one, mul_one]

private lemma includeLeft_compat :
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] R').comp
        (algebraMap R S) =
      (algebraMap R' (S ⊗[R] R')).comp (algebraMap R R') := by
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply, algebraMap_right_apply]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

private theorem main
    (h : ∀ (T : Type u) [CommRing T] [Algebra R' T] (g : S →+* T),
      g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
        ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
    Algebra.IsPushout R S R' S' := by
  classical
  obtain ⟨β, hβ, -⟩ :=
    h (S ⊗[R] R') Algebra.TensorProduct.includeLeftRingHom includeLeft_compat
  have hcompat : (algebraMap S S').comp (algebraMap R S) =
      (algebraMap R' S').comp (algebraMap R R') := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hαβ : (alpha : S ⊗[R] R' →ₐ[R'] S').comp β = AlgHom.id R' S' := by
    refine (h S' (algebraMap S S') hcompat).unique ?_ ?_
    · change ((alpha : S ⊗[R] R' →ₐ[R'] S').toRingHom.comp β.toRingHom).comp
          (algebraMap S S') = _
      rw [RingHom.comp_assoc, hβ]
      ext s
      change (alpha : S ⊗[R] R' →ₐ[R'] S') (s ⊗ₜ 1) = _
      rw [alpha_tmul, map_one, mul_one]
    · rfl
  have hβα : ∀ x : S ⊗[R] R', β ((alpha : S ⊗[R] R' →ₐ[R'] S') x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s r =>
      rw [alpha_tmul, map_mul, AlgHom.commutes, algebraMap_right_apply]
      have hs : β (algebraMap S S' s) = s ⊗ₜ 1 := by
        have hcongr := congrArg (fun φ : S →+* S ⊗[R] R' => φ s) hβ
        simpa using hcongr
      rw [hs, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let e : (S ⊗[R] R') ≃ₐ[R'] S' :=
    AlgEquiv.ofAlgHom (alpha : S ⊗[R] R' →ₐ[R'] S') β hαβ (by ext x; exact hβα x)
  have he : e.toRingHom.comp (algebraMap S (S ⊗[R] R')) = algebraMap S S' :=
    alpha_comp_algebraMap
  have hpush : Algebra.IsPushout R R' S S' :=
    Algebra.IsPushout.of_equiv (h := TensorProduct.isPushout') e he
  exact hpush.symm

end IsPushoutOfUnivAux

namespace Algebra

/-- A square of algebras is a pushout when it satisfies the universal
property for algebra homomorphisms: for every `R'`-algebra `T` and every
`g : S →+* T` compatible with the maps from `R`, there is a unique
`R'`-algebra map `S' →ₐ[R'] T` extending `g`.

This is the hands-on criterion for recognizing pushouts (tensor products)
without computing the tensor product: it is used to identify fiber
products of schemes, base changes, and tensor-product decompositions from
their mapping properties. -/
theorem isPushout_of_forall_existsUnique_algHom_comp_eq
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (h : ∀ (T : Type u) [CommRing T] [Algebra R' T] (g : S →+* T),
      g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
        ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
    Algebra.IsPushout R S R' S' :=
  IsPushoutOfUnivAux.main h

end Algebra
