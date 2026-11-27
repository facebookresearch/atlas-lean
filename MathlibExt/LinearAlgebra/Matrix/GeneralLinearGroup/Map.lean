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
# Coefficient and index maps for general linear groups

Let R,S be semirings and n,m finite index types, with coefficient and index types allowed to
lie in independent universes. Write GL(n,R) for the group of invertible n×n matrices over R.
For e:n≃m, reindex_e(A)(i,j)=A(e⁻¹(i),e⁻¹(j)). For a semiring homomorphism f:R→S,
f_*(A)(i,j)=f(A(i,j)). Entrywise coefficient application gives mapRingHom f:GL(n,R)→GL(n,S),
and reindexing gives reindexMulEquiv e:GL(n,R)≃*GL(m,R). These operations commute, including
for noncommutative semirings and empty index sets.
-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup

universe u v w uR vI wI

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {R : Type v} {S : Type w} [Semiring R] [Semiring S]

/-- **Entrywise coefficient homomorphism on invertible matrices.**

Let R,S be semirings and n,m finite index types, with coefficient and index types allowed to
lie in independent universes. Write GL(n,R) for the group of invertible n×n matrices over R.
For a semiring homomorphism f:R→S, mapRingHom f:GL(n,R)→GL(n,S) sends an invertible matrix A
to the matrix with entries f(A(i,j)). Its inverse matrix is the entrywise image of A⁻¹.
-/
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

/-- **Coefficient map agrees with the commutative general-linear map.**

Let R,S be commutative rings, n a finite index type and f:R→+*S a ring homomorphism. The group
homomorphism mapRingHom f:GL(n,R)→GL(n,S) equals Matrix.GeneralLinearGroup.map f; both send A
to its entrywise image f(A(i,j)).
-/
theorem mapRingHom_eq_map {R' : Type v} {S' : Type w} [CommRing R'] [CommRing S']
    {n' : Type u} [DecidableEq n'] [Fintype n'] (f : R' →+* S') :
    (mapRingHom (n := n') f) = (Matrix.GeneralLinearGroup.map (n := n') f) :=
  rfl

variable {m : Type vI} [DecidableEq m] [Fintype m]
variable {A : Type wI} [Semiring A]

/-- **Reindexing equivalence of general linear groups.**

Let A be a semiring, n,m finite index types in independent universes and e:n≃m an equivalence.
The group equivalence reindexMulEquiv e:GL(n,A)≃*GL(m,A) sends M to the matrix with entry
M(e⁻¹(i),e⁻¹(j)).
-/
def reindexMulEquiv (e : n ≃ m) : GL n A ≃* GL m A :=
  Units.mapEquiv (reindexRingEquiv A e).toMulEquiv

@[simp]
lemma coe_reindexMulEquiv (e : n ≃ m) (g : GL n A) :
    (↑(reindexMulEquiv e g) : Matrix m m A) = Matrix.reindex e e (↑g : Matrix n n A) :=
  rfl

/-- **Coefficient maps commute with index reindexing.**

Let R,S be semirings and n,m finite index types, with coefficient and index types allowed to
lie in independent universes. Write GL(n,R) for the group of invertible n×n matrices over R.
For e:n≃m, reindex_e(A)(i,j)=A(e⁻¹(i),e⁻¹(j)). For a semiring homomorphism f:R→S,
f_*(A)(i,j)=f(A(i,j)). For e:n≃m and a semiring homomorphism f:R→S, reindex_e∘mapRingHom
f=mapRingHom f∘reindex_e as group homomorphisms GL(n,R)→GL(m,S).
-/
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

/-- **Reindexed coefficient image of an invertible matrix.**

Let R,S be semirings and n,m finite index types, with coefficient and index types allowed to
lie in independent universes. Write GL(n,R) for the group of invertible n×n matrices over R.
For e:n≃m, reindex_e(A)(i,j)=A(e⁻¹(i),e⁻¹(j)). For a semiring homomorphism f:R→S,
f_*(A)(i,j)=f(A(i,j)). For e:n≃m, a semiring homomorphism f:R→S and g∈GL(n,R), reindexMulEquiv
e (mapRingHom f g)=mapRingHom f (reindexMulEquiv e g).
-/
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
