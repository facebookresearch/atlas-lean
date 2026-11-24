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
# Coefficient and reindex maps for finite general linear groups

For a semiring `R` and a finite index type `n` (`Fintype n`) with decidable equality
(`DecidableEq n`), `GL n R` is the unit group of square matrices on `n`. A semiring
homomorphism `f : R →+* S` acts on
these groups by applying `f` entrywise, and an equivalence `e : n ≃ m` of finite index
types with decidable equality acts by reindexing both matrix axes.

Both constructions allow independent universes and arbitrary semirings. Applying a
coefficient map commutes with reindexing. When `R` and `S` are commutative rings, the
coefficient map agrees with Mathlib's `Matrix.GeneralLinearGroup.map`.
-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup

universe u v w uR vI wI

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {R : Type v} {S : Type w} [Semiring R] [Semiring S]

/-- For semirings `R`, `S` in independent universes and a finite index type `n`
with decidable equality, a semiring homomorphism `f : R →+* S` induces the group
homomorphism `GL n R →* GL n S` that applies `f` entrywise. -/
def mapRingHom (f : R →+* S) : GL n R →* GL n S :=
  Units.map f.mapMatrix.toMonoidHom

/-- For semirings `R`, `S`, a finite index type `n` with decidable equality,
`f : R →+* S`, and `g : GL n R`, the underlying matrix of `mapRingHom f g` is the
matrix obtained by applying `f` to every entry of `g`. -/
@[simp]
lemma coe_mapRingHom (f : R →+* S) (g : GL n R) :
    (↑(mapRingHom f g) : Matrix n n S) = (↑g : Matrix n n R).map f :=
  rfl

/-- For a semiring `R` and a finite index type `n` with decidable equality,
`mapRingHom (RingHom.id R)` is the identity group homomorphism of `GL n R`. -/
@[simp]
theorem mapRingHom_id :
    mapRingHom (R := R) (n := n) (RingHom.id R) = MonoidHom.id (GL n R) :=
  rfl

/-- For semirings `R`, `S`, `T`, a finite index type `n` with decidable
equality, and homomorphisms `f : R →+* S` and `g : S →+* T`, the coefficient map of
`g.comp f` is the group homomorphism `(mapRingHom g).comp (mapRingHom f)`. -/
@[simp]
theorem mapRingHom_comp {T : Type uR} [Semiring T] (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom (n := n) f) :=
  rfl

/-- For commutative rings `R`, `S`, a finite index type `n` with decidable
equality, and a ring homomorphism `f : R →+* S`, `mapRingHom f` equals Mathlib's
`GeneralLinearGroup.map f` as a homomorphism `GL n R →* GL n S`. This comparison
requires commutative rings; the entrywise construction itself works for semirings. -/
theorem mapRingHom_eq_map {R' : Type v} {S' : Type w} [CommRing R'] [CommRing S']
    {n' : Type u} [DecidableEq n'] [Fintype n'] (f : R' →+* S') :
    (mapRingHom (n := n') f) = (Matrix.GeneralLinearGroup.map (n := n') f) :=
  rfl

variable {m : Type vI} [DecidableEq m] [Fintype m]
variable {A : Type wI} [Semiring A]

/-- For a semiring `R`, finite index types `n`, `m` with decidable equality,
and an equivalence `e : n ≃ m`, simultaneous row and column reindexing induces a group
equivalence `GL n R ≃* GL m R`. The index universes can differ. -/
def reindexMulEquiv (e : n ≃ m) : GL n A ≃* GL m A :=
  Units.mapEquiv (reindexRingEquiv A e).toMulEquiv

/-- For a semiring `R`, finite index types `n`, `m` with decidable equality,
`e : n ≃ m`, and `g : GL n R`, the underlying matrix of `reindexMulEquiv e g` is
`Matrix.reindex e e ↑g`: entry `(i, j)` is `g (e.symm i) (e.symm j)`. -/
@[simp]
lemma coe_reindexMulEquiv (e : n ≃ m) (g : GL n A) :
    (↑(reindexMulEquiv e g) : Matrix m m A) = Matrix.reindex e e (↑g : Matrix n n A) :=
  rfl

/-- For semirings `R`, `S` and finite index types `n`, `m` with
decidable equality, let `f : R →+* S` and `e : n ≃ m`. Applying `f` at index type `n`
and then reindexing over `S` equals reindexing over `R` and then applying `f` at
index type `m`, as group homomorphisms `GL n R →* GL m S`. -/
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

/-- For semirings `R`, `S`, finite index types `n`, `m` with
decidable equality, `f : R →+* S`, `e : n ≃ m`, and `g : GL n R`, one has
`reindexMulEquiv e (mapRingHom f g) = mapRingHom f (reindexMulEquiv e g)` in `GL m S`. -/
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
