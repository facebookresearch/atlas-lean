/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Coefficient and reindex maps for `GL`

This module provides the arbitrary-semiring, fully cross-universe
`Matrix.GeneralLinearGroup.mapRingHom` and the cross-index-universe
`Matrix.GeneralLinearGroup.reindexMulEquiv`.

The API is intentionally minimal: one canonical underlying-matrix `simp`
lemma, `id` and `comp` for the coefficient map, a non-`simp` equality to
the existing commutative `Matrix.GeneralLinearGroup.map`, one canonical
underlying-matrix `simp` lemma for reindexing, and coefficient-map
naturality as an equality of bundled `MonoidHom` values with an
element-level `simp` lemma derived from it. No commutativity or
determinant API is assumed. Proofs use bundled extensionality and
definitional reduction for robustness.

## Main definitions

* `Matrix.GeneralLinearGroup.mapRingHom` – arbitrary-semiring, fully
  cross-universe coefficient map via `Units.map` and `RingHom.mapMatrix`.
* `Matrix.GeneralLinearGroup.reindexMulEquiv` – cross-index-universe
  reindexing equivalence via `Units.mapEquiv` of `Matrix.reindexRingEquiv`.

## Main results

* `Matrix.GeneralLinearGroup.coe_mapRingHom` – underlying-matrix `simp` lemma.
* `Matrix.GeneralLinearGroup.mapRingHom_id` – `id` law.
* `Matrix.GeneralLinearGroup.mapRingHom_comp` – `comp` law.
* `Matrix.GeneralLinearGroup.mapRingHom_eq_map` – non-`simp` equality to the
  existing commutative map.
* `Matrix.GeneralLinearGroup.coe_reindexMulEquiv` – underlying-matrix `simp`
  lemma for reindexing.
* `Matrix.GeneralLinearGroup.reindexMulEquiv_mapRingHom` – coefficient-map
  naturality as bundled `MonoidHom` equality.
* `Matrix.GeneralLinearGroup.reindexMulEquiv_mapRingHom_apply` – element-level
  `simp` lemma derived from the bundled equality.

-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup

universe u v w uR vI wI

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {R : Type v} {S : Type w} [Semiring R] [Semiring S]

/-- Arbitrary-semiring, fully cross-universe coefficient map for `GL`.

Implemented as `Units.map` of `RingHom.mapMatrix`. -/
def mapRingHom (f : R →+* S) : GL n R →* GL n S :=
  Units.map f.mapMatrix.toMonoidHom

@[simp]
lemma coe_mapRingHom (f : R →+* S) (g : GL n R) :
    (↑(mapRingHom f g) : Matrix n n S) = (↑g : Matrix n n R).map f :=
  rfl

@[simp]
theorem mapRingHom_id :
    mapRingHom (R := R) (n := n) (RingHom.id R) = MonoidHom.id (GL n R) :=
  rfl

@[simp]
theorem mapRingHom_comp {T : Type uR} [Semiring T] (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom (n := n) f) :=
  rfl

/-- Non-`simp` equality to the existing commutative `GeneralLinearGroup.map`.

Both are definitionally `Units.map` of `RingHom.mapMatrix`; this lemma makes the
connection explicit without entering the `simp` set. -/
theorem mapRingHom_eq_map {R' : Type v} {S' : Type w} [CommRing R'] [CommRing S']
    {n' : Type u} [DecidableEq n'] [Fintype n'] (f : R' →+* S') :
    (mapRingHom (n := n') f) = (Matrix.GeneralLinearGroup.map (n := n') f) :=
  rfl

variable {m : Type vI} [DecidableEq m] [Fintype m]
variable {A : Type wI} [Semiring A]

/-- Cross-index-universe reindexing equivalence for `GL` via
`Units.mapEquiv` of `Matrix.reindexRingEquiv`. -/
def reindexMulEquiv (e : n ≃ m) : GL n A ≃* GL m A :=
  Units.mapEquiv (reindexRingEquiv A e).toMulEquiv

@[simp]
lemma coe_reindexMulEquiv (e : n ≃ m) (g : GL n A) :
    (↑(reindexMulEquiv e g) : Matrix m m A) = Matrix.reindex e e (↑g : Matrix n n A) :=
  rfl

/-- Coefficient-map naturality for reindexing as an equality of bundled
`MonoidHom` values: reindexing after a coefficient map equals the coefficient
map after reindexing, with source `GL n R` and target `GL m S`. -/
theorem reindexMulEquiv_mapRingHom {R' : Type v} {S' : Type w}
    [Semiring R'] [Semiring S'] {n' : Type u} {m' : Type vI}
    [DecidableEq n'] [DecidableEq m'] [Fintype n'] [Fintype m']
    (e : n' ≃ m') (f : R' →+* S') :
    (reindexMulEquiv (A := S') e).toMonoidHom.comp (mapRingHom (n := n') f) =
      (mapRingHom (n := m') f).comp (reindexMulEquiv (A := R') e).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  rfl

/-- Element-level naturality derived from the bundled `MonoidHom` equality. -/
@[simp]
theorem reindexMulEquiv_mapRingHom_apply {R' : Type v} {S' : Type w}
    [Semiring R'] [Semiring S'] {n' : Type u} {m' : Type vI}
    [DecidableEq n'] [DecidableEq m'] [Fintype n'] [Fintype m']
    (e : n' ≃ m') (f : R' →+* S') (g : GL n' R') :
    reindexMulEquiv (A := S') e (mapRingHom f g) =
      mapRingHom f (reindexMulEquiv (A := R') e g) :=
  DFunLike.congr_fun (reindexMulEquiv_mapRingHom e f) g

end GeneralLinearGroup
end Matrix
