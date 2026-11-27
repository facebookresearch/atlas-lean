/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_archIdent_tmul_apply.lean`
and
`P2M/Sol/S_AutomorphicForm_archIdent_tmul_apply.lean`
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
The base-change map below is defined componentwise, directly from the
local completion factor, rather than through a bijectivity statement for
that factor.
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

open scoped TensorProduct NumberField.LiesOver

namespace NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The scalar map from `L` to the completion at `w`, as a `K`-algebra
homomorphism. -/
def scalarCompletionAlgHom (w : InfinitePlace L) : L →ₐ[K] w.Completion where
  toRingHom := algebraMap L w.Completion
  commutes' _ := rfl

/-- The local factor at an infinite place `w` of `L` lying over `v` of `K`:
it sends a pure tensor of a completion element and a scalar from `L` to the
product of their images in the completion at `w`. -/
def completionTensorFactor (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] : (v.Completion ⊗[K] L) →ₐ[v.Completion] w.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.Completion w.Completion)
    (scalarCompletionAlgHom w) (fun _ _ => Commute.all _ _)

@[simp]
theorem completionTensorFactor_tmul (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (c : v.Completion) (l : L) :
    completionTensorFactor v w (c ⊗ₜ[K] l) =
      algebraMap v.Completion w.Completion c * algebraMap L w.Completion l := by
  simp [completionTensorFactor, scalarCompletionAlgHom, Algebra.TensorProduct.lift_tmul,
    Algebra.ofId_apply]

theorem completionTensorFactor_one_tmul (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (l : L) :
    completionTensorFactor v w ((1 : v.Completion) ⊗ₜ[K] l) =
      algebraMap L w.Completion l := by
  rw [completionTensorFactor_tmul, map_one, one_mul]

end NumberField.InfinitePlace

namespace NumberField.InfiniteAdeleRing

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- The map from the infinite adele ring of `K` to the completion at `w`,
through the place below `w`, as a `K`-algebra homomorphism. -/
def adeleCompletionAlgHom (w : InfinitePlace L) :
    InfiniteAdeleRing K →ₐ[K] w.Completion where
  toFun a :=
    letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
    algebraMap (w.comap (algebraMap K L)).Completion w.Completion
      (a (w.comap (algebraMap K L)))
  map_one' := by exact map_one _
  map_mul' _ _ := by exact map_mul _ _ _
  map_zero' := by exact map_zero _
  map_add' _ _ := by exact map_add _ _ _
  commutes' x := by
    letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
    exact (IsScalarTower.algebraMap_apply K (w.comap (algebraMap K L)).Completion
      w.Completion x).symm

/-- The component at `w` of the archimedean base-change map, determined by
the scalar map from `L` and the adele coordinate map through the place
below `w`. -/
def archComponent (w : InfinitePlace L) :
    (L ⊗[K] InfiniteAdeleRing K) →ₐ[K] w.Completion :=
  letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
  Algebra.TensorProduct.lift (InfinitePlace.scalarCompletionAlgHom w)
    (adeleCompletionAlgHom w) (fun _ _ => Commute.all _ _)

/-- The component at `w` of the archimedean base-change map, as an
`L`-algebra homomorphism for the left-factor `L`-algebra structure on
`L ⊗[K] InfiniteAdeleRing K`. -/
def archComponentL (w : InfinitePlace L) :
    (L ⊗[K] InfiniteAdeleRing K) →ₐ[L] w.Completion where
  toRingHom := (archComponent (K := K) (L := L) w).toRingHom
  commutes' l := by
    show archComponent (K := K) (L := L) w (l ⊗ₜ[K] (1 : InfiniteAdeleRing K)) =
      algebraMap L w.Completion l
    simp [archComponent, Algebra.TensorProduct.lift_tmul,
      InfinitePlace.scalarCompletionAlgHom]

/-- The canonical archimedean base-change ring homomorphism from
`L ⊗[K] InfiniteAdeleRing K` to `InfiniteAdeleRing L` (the map underlying
the usual identification; bijectivity is not proved here). Its component at
each infinite place `w` of `L` transports the coordinate at the place of `K`
below `w` and multiplies by the image of the scalar from `L`. -/
def archBaseChange (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : (L ⊗[K] InfiniteAdeleRing K) →+* InfiniteAdeleRing L :=
  RingHom.pi fun w => (archComponent (K := K) (L := L) w).toRingHom

/-- The archimedean base-change map as an `L`-algebra homomorphism, for the
left-factor `L`-algebra structure on `L ⊗[K] InfiniteAdeleRing K`. -/
def archBaseChangeAlgHom (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    (L ⊗[K] InfiniteAdeleRing K) →ₐ[L] InfiniteAdeleRing L where
  toRingHom := archBaseChange K L
  commutes' l := by
    funext w
    show archComponent (K := K) (L := L) w (algebraMap L _ l) = _
    exact (archComponentL (K := K) (L := L) w).commutes' l

theorem archBaseChangeAlgHom_toRingHom :
    (archBaseChangeAlgHom K L).toRingHom = archBaseChange K L :=
  rfl

theorem archBaseChange_apply (z : L ⊗[K] InfiniteAdeleRing K) (w : InfinitePlace L) :
    archBaseChange K L z w = archComponent (K := K) (L := L) w z :=
  rfl

/-- On a pure tensor, the archimedean base-change map transports the
completion coordinate at the place below `w` and multiplies by the image of
the scalar. -/
public theorem archBaseChange_tmul_apply (x : L) (a : InfiniteAdeleRing K)
    (w : InfinitePlace L) :
    letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
    archBaseChange K L (x ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
          (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x := by
  letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
  rw [archBaseChange_apply]
  show archComponent (K := K) (L := L) w (x ⊗ₜ[K] a) = _
  rw [archComponent, Algebra.TensorProduct.lift_tmul]
  simp [InfinitePlace.scalarCompletionAlgHom, adeleCompletionAlgHom, mul_comm]

theorem archBaseChange_one_tmul_apply (a : InfiniteAdeleRing K) (w : InfinitePlace L) :
    letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
    archBaseChange K L ((1 : L) ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (a (w.comap (algebraMap K L))) := by
  letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
  rw [archBaseChange_tmul_apply, map_one, mul_one]

theorem archBaseChange_tmul_zero_apply (x : L) (w : InfinitePlace L) :
    archBaseChange K L (x ⊗ₜ (0 : InfiniteAdeleRing K)) w = 0 := by
  rw [TensorProduct.tmul_zero, map_zero]
  rfl

end NumberField.InfiniteAdeleRing

end
