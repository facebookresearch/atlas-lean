/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.HomTensorDifferential

/-!
# Support bounds for full Hom products and tensor totals

Let R be a commutative ring and P,J,U integer cochain complexes of R-modules in a common
carrier universe v. If P vanishes above N and J below L, then Hom(P,J) vanishes below
L−N. If J and U vanish below L and M, their coproduct tensor total vanishes below L+M.

Consequently, in degree n of Hom(P,J⊗U), every source coordinate outside the finite interval
[L+M−n,N] is zero. These are bounds on cochain degrees, without finite-generation or
projectivity conditions on the individual modules.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Let R be a commutative ring and P,J integer R-module cochain complexes in carrier universe v.
Suppose P^p=0 for p>N and J^j=0 for j<L. If a<L−N, then the full degree-a linear Hom cochain
object is zero. Each coordinate P^p → J^{p+a} has either zero source or zero target. -/
theorem linearComplex_isZero_X_of_bounds
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (N L a : ℤ)
    (hP : ∀ p : ℤ, N < p → IsZero (P.X p))
    (hJ : ∀ j : ℤ, j < L → IsZero (J.X j)) (ha : a < L - N) :
    IsZero ((linearComplex R P J).X a) := by
  letI : Subsingleton ((linearComplex R P J).X a) := ⟨fun f g => by
    apply Cochain.ext
    intro p q hpq
    by_cases hp : N < p
    · exact (hP p hp).eq_of_src _ _
    · have hq : q < L := by omega
      exact (hJ q hq).eq_of_tgt _ _⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- For a commutative ring R and integer R-module cochain complexes J,U in universe v, suppose
J^j=0 for j<L and U^b=0 for b<M. Then (J⊗U)^n is zero whenever n<L+M. Its coproduct summands
J^j⊗U^b have j+b=n, so one factor lies below its lower support bound. -/
theorem complexAt_isZero_X_of_lower_bounds
    (J U : CochainComplex (ModuleCat.{v} R) ℤ) (L M n : ℤ)
    (hJ : ∀ j : ℤ, j < L → IsZero (J.X j))
    (hU : ∀ b : ℤ, b < M → IsZero (U.X b)) (hn : n < L + M) :
    IsZero ((complexAt R J U).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro j b hjb
  have hCell : IsZero (ModuleCat.tensorObjAt R (J.X j) (U.X b)) := by
    by_cases hj : j < L
    · exact ((ModuleCat.tensorBifunctorAt R).flip.obj (U.X b)).map_isZero (hJ j hj)
    · have hb : b < M := by change j + b = n at hjb; omega
      exact ((ModuleCat.tensorBifunctorAt R).obj (J.X j)).map_isZero (hU b hb)
  exact hCell.eq_of_src _ _

/-- Let R be a commutative ring and P,J,U integer R-module cochain complexes in universe v.
Suppose P vanishes above N, J below L, and U below M. For a degree-n cochain z : P → J⊗U and
p+n=q, its coordinate z_{p,q} is zero if p<L+M−n or N<p. Thus only source indices p in
[L+M−n,N] can contribute to that full Hom degree. -/
theorem homTensor_right_coordinate_zero
    (P J U : CochainComplex (ModuleCat.{v} R) ℤ) (N L M n p q : ℤ)
    (hP : ∀ p : ℤ, N < p → IsZero (P.X p))
    (hJ : ∀ j : ℤ, j < L → IsZero (J.X j))
    (hU : ∀ b : ℤ, b < M → IsZero (U.X b))
    (hpn : p + n = q) (hp : p < L + M - n ∨ N < p)
    (z : Cochain P (complexAt R J U) n) : z.v p q hpn = 0 := by
  rcases hp with hp | hp
  · have hq : q < L + M := by omega
    exact (complexAt_isZero_X_of_lower_bounds R J U L M q hJ hU hq).eq_of_tgt _ _
  · exact (hP p hp).eq_of_src _ _

end CochainComplex.ModuleTensor
