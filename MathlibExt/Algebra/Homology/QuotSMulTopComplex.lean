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

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Complexes reduced modulo a ring element

Let R be a commutative ring and x∈R. The quotient Q_x(M)=M/xM is a module over R_x=R/(x). An
R-linear map f:M→N induces the R_x-linear map [m]↦[f(m)], whose restriction of scalars is the
R-linear quotient map. Quotient reduction preserves surjections and exact pairs M→N→P when the
second map is surjective.

For a chain complex C indexed by an additive right-cancellative semigroup with a distinguished
1, reduce each term to Q_x(C_i) and each differential to its quotient map. The carrier and index
universes are retained; the shape is j+1=i and consecutive differentials still compose to zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w z

namespace QuotSMulTop

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. For f:M→_R N, the induced map
Q_x(f):Q_x(M)→_{R_x}Q_x(N) sends [m] to [f(m)]. Its R_x-linearity follows from the surjective
scalar map R→R_x. -/
def mapLinear (x : R) (f : M →ₗ[R] N) :
    QuotSMulTop x M →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N :=
  (map x f).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. For f:M→_R N, restriction of Q_x(f) along R→R_x
equals the R-linear quotient reduction of f. Both maps have representative value [m]↦[f(m)]. -/
@[simp]
theorem mapLinear_restrictScalars (x : R) (f : M →ₗ[R] N) :
    (mapLinear x f).restrictScalars R = map x f :=
  rfl

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. For f:M→_R N and m∈M, Q_x(f)([m])=[f(m)] in N/xN. The
brackets are the module quotient projections by x-multiples. -/
@[simp]
theorem mapLinear_apply_mk (x : R) (f : M →ₗ[R] N) (m : M) :
    mapLinear x f (Submodule.Quotient.mk m) =
      (Submodule.Quotient.mk (f m) : QuotSMulTop x N) :=
  rfl

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. If f:M→_R N is surjective, then Q_x(f):M/xM→N/xN is
surjective as a function and an R_x-linear map. -/
theorem mapLinear_surjective (x : R) {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : Function.Surjective (mapLinear x f) :=
  map_surjective x hf

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. Let P be an R-module in universe z, f:M→N,g:N→P, with
im(f)=ker(g) and g surjective. Then im(Q_x(f))=ker(Q_x(g)) as quotient-module maps over R_x. -/
theorem mapLinear_exact
    {P : Type z} [AddCommGroup P] [Module R P]
    (x : R) {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (mapLinear x f) (mapLinear x g) :=
  map_exact x hfg hg

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. The induced map Q_x(0):M/xM→N/xN is the zero
R_x-linear map. Every representative [m] is sent to [0]. -/
@[simp]
theorem mapLinear_zero (x : R) :
    mapLinear x (0 : M →ₗ[R] N) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. For the identity of M, Q_x(id_M)=id_{M/xM}. Its value
on every quotient class [m] is [m]. -/
@[simp]
theorem mapLinear_id (x : R) :
    mapLinear x (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- Let R be a commutative ring in u, x∈R, and M,N R-modules with abelian carriers in independent
universes v,w. Put R_x=R/(x), Q_x(M)=M/xM. For an R-module P in z and maps f:M→N,g:N→P,
Q_x(g∘f)=Q_x(g)∘Q_x(f). Both quotient maps send [m] to [g(f(m))]. -/
@[simp]
theorem mapLinear_comp
    {P : Type z} [AddCommGroup P] [Module R P]
    (x : R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    mapLinear x (g.comp f) = (mapLinear x g).comp (mapLinear x f) := by
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

end QuotSMulTop

namespace ChainComplex

variable {R : Type u} [CommRing R]
variable {ι : Type w} [AddRightCancelSemigroup ι] [One ι]

/-- Let R be a commutative ring in u, C a chain complex of ModuleCat_v(R), and its index I an
additive right-cancellative semigroup in w with a distinguished 1. For x∈R, the reduced complex
has term C_i/xC_i and differential [m]↦[d_C(i,j)(m)] over R/(x). Its shape remains j+1=i. -/
def quotSMulTop (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) :
    ChainComplex (ModuleCat.{v} (R ⧸ Ideal.span {x})) ι where
  X i := ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (C.X i))
  d i j := ModuleCat.ofHom (QuotSMulTop.mapLinear x (C.d i j).hom)
  shape i j hij := by
    apply ModuleCat.hom_ext
    simp [C.shape i j hij]
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    have hzero := congrArg ModuleCat.Hom.hom (C.d_comp_d i j k)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at hzero
    rw [← QuotSMulTop.mapLinear_comp, hzero, QuotSMulTop.mapLinear_zero]

/-- Let R be a commutative ring in u, C a chain complex with carrier universe v and an additive
right-cancellative index semigroup I in w with a distinguished 1, x∈R, and i∈I. The i-th term of
the reduced complex is the R/(x)-module C_i/xC_i in the same carrier universe v. -/
@[simp]
theorem quotSMulTop_X (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) (i : ι) :
    (C.quotSMulTop x).X i =
      ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (C.X i)) :=
  rfl

/-- Let R be a commutative ring in u, C a chain complex in ModuleCat_v(R) on an additive
right-cancellative index semigroup I with 1 in w, and x∈R. For i,j∈I, its reduced differential
is the module morphism induced by Q_x(d_C(i,j)). -/
@[simp]
theorem quotSMulTop_d (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) (i j : ι) :
    (C.quotSMulTop x).d i j =
      ModuleCat.ofHom (QuotSMulTop.mapLinear x (C.d i j).hom) :=
  rfl

/-- Let R be a commutative ring in u and C a chain complex with carrier v on an additive
right-cancellative index semigroup I with 1 in w. For x∈R and i,j∈I, the linear map underlying
the reduced differential is Q_x(d_C(i,j)); it sends [m] to [d_C(i,j)(m)]. -/
@[simp]
theorem quotSMulTop_d_hom
    (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) (i j : ι) :
    ((C.quotSMulTop x).d i j).hom =
      QuotSMulTop.mapLinear x (C.d i j).hom :=
  rfl

end ChainComplex
