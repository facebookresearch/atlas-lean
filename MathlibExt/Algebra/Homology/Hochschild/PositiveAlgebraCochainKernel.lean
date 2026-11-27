/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricAlgebraComplex
public import MathlibExt.Algebra.Homology.Hochschild.PositiveAlgebraCochains
public import MathlibExt.Algebra.Homology.HomologicalComplexKernelHomology
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Algebra-linear cochains annihilating positive shuffle relations

Let `k` be a commutative ring, `A` a commutative `k`-algebra,
and `M` an `A`-module with compatible ground-ring action. The regular
algebra-linear Hochschild complex has a both-positive shuffle relation
subcomplex `R_*` and quotient `Q_*`. Lift these carriers to
`T=max(u,v,w)` and apply `Hom_A(-,M_T)`.

Restriction along `R_* → C_*` gives a relation-cochain map. Pullback
from `Q_*` is its kernel: precisely the `A`-linear cochains annihilating
all proper shuffle relations. Since `R_0=R_1=0`, pullback gives
isomorphisms on cohomology in degrees zero and one. The coefficient
module is arbitrary; neither its projectivity nor its flatness is required.

## References

* J.-L. Loday, *Cyclic Homology*, §4.2, for the shuffle relations defining Harrison cochains.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Let `k` be a commutative ring, `A` a commutative `k`-algebra, and
`M` an `A`-module with compatible commuting ground-ring action.
Write `C_*(A,M)` for the algebra-linear Hochschild chains,
`R_*(A,M)` for their both-positive shuffle relation complex, and
`Q_*(A,M)=C_*(A,M)/R_*(A,M)`. The quotient projection `C_*(A,M) → Q_*(A,M)` is the
categorical cokernel of the relation inclusion
`R_*(A,M) → C_*(A,M)` in algebra-linear chain complexes. -/
def algebraPositiveQuotientCoforkIsColimit :
    IsColimit (CokernelCofork.ofπ (algebraRawPositiveProjection k A M)
      (algebraPositiveRelationInclusion_projection k A M)) := by
  let c := CokernelCofork.ofπ (algebraRawPositiveProjection k A M)
    (algebraPositiveRelationInclusion_projection k A M)
  apply HomologicalComplex.isColimitOfEval (parallelPair (algebraPositiveRelationInclusion k A M) 0) c
  intro n
  refine (isColimitMapCoconeCoforkEquiv'
    (HomologicalComplex.eval (ModuleCat.{max u v w} A) (ComplexShape.down ℕ) n)
    (algebraPositiveRelationInclusion_projection k A M)).symm ?_
  apply ModuleCat.isColimitCokernelCofork
  · change Function.Exact (algebraPositiveRelations k A M n).subtype
      (algebraPositiveRelations k A M n).mkQ
    apply LinearMap.exact_iff.mpr
    rw [Submodule.ker_mkQ, Submodule.range_subtype]
  · exact Submodule.mkQ_surjective _

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. The complex `C_T` is the regular algebra-linear Hochschild
chain complex represented at the carrier height used for `A`-linear Hom. -/
def regularAlgebraRawForHom : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (algebraRawComplex k A A)

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. The complex `R_T` is the proper shuffle relation subcomplex
of the regular chains, represented at the same Hom carrier height. -/
def regularAlgebraRelationsForHom : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (algebraPositiveRelationComplex k A A)

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. The map `j : R_T → C_T` is the lifted inclusion of the
regular both-positive shuffle relations. -/
def regularAlgebraRelationInclusionForHom :
    regularAlgebraRelationsForHom.{u, v, w} k A ⟶ regularAlgebraRawForHom.{u, v, w} k A :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (algebraPositiveRelationInclusion k A A)

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. The map `q : C_T → Q_T` is the lifted regular-chain
projection to the quotient by both-positive shuffle relations. -/
def regularAlgebraPositiveProjectionForHom :
    regularAlgebraRawForHom.{u, v, w} k A ⟶ regularAlgebraPositiveQuotientForHom.{u, v, w} k A :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (algebraRawPositiveProjection k A A)

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. The relation inclusion followed by the quotient projection
has zero composite: `j ≫ q=0`. -/
@[reassoc]
theorem regularAlgebraRelationInclusion_projectionForHom :
    regularAlgebraRelationInclusionForHom.{u, v, w} k A ≫
      regularAlgebraPositiveProjectionForHom.{u, v, w} k A = 0 := by
  let F := (ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)
  change F.map (algebraPositiveRelationInclusion k A A) ≫
    F.map (algebraRawPositiveProjection k A A) = 0
  calc
    _ = F.map (algebraPositiveRelationInclusion k A A ≫ algebraRawPositiveProjection k A A) :=
      (F.map_comp _ _).symm
    _ = F.map 0 := congrArg
      (fun f : algebraPositiveRelationComplex k A A ⟶ algebraPositiveQuotientComplex k A A => F.map f)
      (algebraPositiveRelationInclusion_projection k A A)
    _ = 0 := F.map_zero _ _

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. The projection `q` exhibits `Q_T` as the cokernel of
`j`, since the carrier lift preserves this quotient. -/
def regularAlgebraPositiveCoforkIsColimit :
    IsColimit (CokernelCofork.ofπ (regularAlgebraPositiveProjectionForHom.{u, v, w} k A)
      (regularAlgebraRelationInclusion_projectionForHom.{u, v, w} k A)) := by
  let F := (ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)
  exact CokernelCofork.mapIsColimit _ (algebraPositiveQuotientCoforkIsColimit k A A) F

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. The raw regular cochain complex is `H_C`, with terms
`Hom_A(C_T,n,M_T)` and differential induced by precomposition
with the regular chain differential. -/
def nativeRawAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).obj
      (Opposite.op (regularAlgebraRawForHom.{u, v, w} k A))

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. The relation cochain complex is `H_R`, with terms
`Hom_A(R_T,n,M_T)` and differential induced by the relation
chain differential. -/
def nativeRelationAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).obj
      (Opposite.op (regularAlgebraRelationsForHom.{u, v, w} k A))

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. Precomposition by `j` gives the relation restriction
map `j^* : H_C → H_R`. -/
def nativeAlgebraRelationCochainMap :
    nativeRawAlgebraCochainComplex k A M ⟶ nativeRelationAlgebraCochainComplex k A M :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).map
      (regularAlgebraRelationInclusionForHom.{u, v, w} k A).op

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. Precomposition by `q` gives the quotient pullback
`q^* : H_Q → H_C`. -/
def nativePositiveAlgebraCochainInclusion :
    nativePositiveAlgebraCochainComplex k A M ⟶ nativeRawAlgebraCochainComplex k A M :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).map
      (regularAlgebraPositiveProjectionForHom.{u, v, w} k A).op

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. The quotient pullback followed by relation restriction
has zero composite: `q^* ≫ j^*=0`. -/
@[reassoc]
theorem nativePositiveAlgebraCochainInclusion_relation :
    nativePositiveAlgebraCochainInclusion k A M ≫ nativeAlgebraRelationCochainMap k A M = 0 := by
  let F := HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))
  change F.map (regularAlgebraPositiveProjectionForHom.{u, v, w} k A).op ≫
    F.map (regularAlgebraRelationInclusionForHom.{u, v, w} k A).op = 0
  have h : (regularAlgebraPositiveProjectionForHom.{u, v, w} k A).op ≫
      (regularAlgebraRelationInclusionForHom.{u, v, w} k A).op = 0 := by
    rw [← op_comp, regularAlgebraRelationInclusion_projectionForHom, op_zero]
  calc
    _ = F.map ((regularAlgebraPositiveProjectionForHom.{u, v, w} k A).op ≫
        (regularAlgebraRelationInclusionForHom.{u, v, w} k A).op) := (F.map_comp _ _).symm
    _ = F.map 0 := congrArg
      (fun f : Opposite.op (regularAlgebraPositiveQuotientForHom.{u, v, w} k A) ⟶
          Opposite.op (regularAlgebraRelationsForHom.{u, v, w} k A) => F.map f) h
    _ = 0 := F.map_zero _ _

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. The map `q^* : H_Q → H_C` is a kernel of `j^*` in
cochain complexes, with its kernel universal property inherited
from the chain cokernel and contravariant `A`-linear Hom. -/
def nativePositiveAlgebraCochainKernelIsLimit :
    IsLimit (KernelFork.ofι (nativePositiveAlgebraCochainInclusion k A M)
      (nativePositiveAlgebraCochainInclusion_relation k A M)) := by
  let F := HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))
  let c := KernelFork.ofι (regularAlgebraPositiveProjectionForHom.{u, v, w} k A).op
    (show (regularAlgebraPositiveProjectionForHom.{u, v, w} k A).op ≫
      (regularAlgebraRelationInclusionForHom.{u, v, w} k A).op = 0 by
        rw [← op_comp, regularAlgebraRelationInclusion_projectionForHom, op_zero])
  have hc : IsLimit c := CokernelCofork.IsColimit.ofπOp _ _
    (regularAlgebraPositiveCoforkIsColimit.{u, v, w} k A)
  exact KernelFork.mapIsLimit c hc F

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. There is a canonical cochain isomorphism
`H_Q ≅ ker(j^* : H_C → H_R)`. -/
def nativePositiveAlgebraCochainKernelIso :
    nativePositiveAlgebraCochainComplex k A M ≅ kernel (nativeAlgebraRelationCochainMap k A M) :=
  IsLimit.conePointUniqueUpToIso (nativePositiveAlgebraCochainKernelIsLimit k A M)
    (limit.isLimit (parallelPair (nativeAlgebraRelationCochainMap k A M) 0))

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. The kernel isomorphism followed by its inclusion in
`H_C` equals the quotient pullback `q^*`. -/
@[reassoc]
theorem nativePositiveAlgebraCochainKernelIso_hom_ι :
    (nativePositiveAlgebraCochainKernelIso k A M).hom ≫
      kernel.ι (nativeAlgebraRelationCochainMap k A M) = nativePositiveAlgebraCochainInclusion k A M :=
  IsLimit.conePointUniqueUpToIso_hom_comp (nativePositiveAlgebraCochainKernelIsLimit k A M)
    (limit.isLimit (parallelPair (nativeAlgebraRelationCochainMap k A M) 0)) WalkingParallelPair.zero

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. For `n≤1`, the component of the relation restriction
`j^*` is zero, since the both-positive relation terms `R_T,n`
are zero. -/
theorem nativeAlgebraRelationCochainMap_low (n : ℕ) (hn : n ≤ 1) :
    (nativeAlgebraRelationCochainMap k A M).f n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  have hx : x.val = 0 := by
    have hbot : x.val ∈ (⊥ : Submodule A (A ⊗[k] TensorPower k n A)) :=
      (algebraPositiveRelations_low k A A n hn).le x.property
    simpa only [Submodule.mem_bot] using hbot
  change φ.hom (ULift.up x.val) = 0
  rw [hx]
  exact map_zero φ.hom

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. Quotient pullback induces a canonical isomorphism
`H⁰(H_Q) ≅ H⁰(H_C)`. -/
def nativePositiveAlgebraCohomologyZeroIso :
    (nativePositiveAlgebraCochainComplex k A M).homology 0 ≅
      (nativeRawAlgebraCochainComplex k A M).homology 0 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 0).mapIso
      (nativePositiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyZeroIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. Quotient pullback induces a canonical isomorphism
`H¹(H_Q) ≅ H¹(H_C)`. -/
def nativePositiveAlgebraCohomologyOneIso :
    (nativePositiveAlgebraCochainComplex k A M).homology 1 ≅
      (nativeRawAlgebraCochainComplex k A M).homology 1 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 1).mapIso
      (nativePositiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyOneIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 1 (by omega))
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. The forward degree-zero cohomology isomorphism is
exactly `H⁰(q^*)`. -/
theorem nativePositiveAlgebraCohomologyZeroIso_hom :
    (nativePositiveAlgebraCohomologyZeroIso k A M).hom =
      HomologicalComplex.homologyMap (nativePositiveAlgebraCochainInclusion k A M) 0 := by
  change HomologicalComplex.homologyMap (nativePositiveAlgebraCochainKernelIso k A M).hom 0 ≫
    HomologicalComplex.homologyMap (kernel.ι (nativeAlgebraRelationCochainMap k A M)) 0 = _
  rw [← HomologicalComplex.homologyMap_comp, nativePositiveAlgebraCochainKernelIso_hom_ι]

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- Let `k` be a commutative ring and `A` a commutative `k`-algebra.
At height `T=max(u,v,w)`, let `C_T,R_T,Q_T` be the lifted regular
chains `C_*(A,A)`, their both-positive shuffle relations and their
quotient, with inclusion `j : R_T → C_T` and projection `q : C_T → Q_T`. For an `A`-module `M`, use its lifted carrier `M_T` and define
`H_C=Hom_A(C_T,M_T)`, `H_R=Hom_A(R_T,M_T)`, and
`H_Q=Hom_A(Q_T,M_T)` as nonnegative cochain complexes. The forward degree-one cohomology isomorphism is
exactly `H¹(q^*)`. -/
theorem nativePositiveAlgebraCohomologyOneIso_hom :
    (nativePositiveAlgebraCohomologyOneIso k A M).hom =
      HomologicalComplex.homologyMap (nativePositiveAlgebraCochainInclusion k A M) 1 := by
  change HomologicalComplex.homologyMap (nativePositiveAlgebraCochainKernelIso k A M).hom 1 ≫
    HomologicalComplex.homologyMap (kernel.ι (nativeAlgebraRelationCochainMap k A M)) 1 = _
  rw [← HomologicalComplex.homologyMap_comp, nativePositiveAlgebraCochainKernelIso_hom_ι]

/-- Let `k` be a commutative ring, `A` a commutative `k`-algebra,
and `M` an `A`-module with compatible `k`-action. Represent the
regular chains `C_*(A,A)`, their both-positive shuffle relation
complex `R_*`, quotient `Q_*`, and target `M` at the common height
`T=max(u,v,w)`. Set `H_C=Hom_A(C_*(A,A),M)`,
`H_R=Hom_A(R_*,M)`, and `H_Q=Hom_A(Q_*,M)` there. The presented proper-quotient cochain complex, identified
with `H_Q` by its degreewise carrier equivalences, is canonically
isomorphic to `ker(H_C → H_R)`, the relation annihilator. -/
def positiveAlgebraCochainKernelIso :
    positiveAlgebraCochainComplex k A M ≅ kernel (nativeAlgebraRelationCochainMap k A M) :=
  ((nativePositiveAlgebraCochainComplex k A M).changeObjectsIso
    (fun n => (positiveAlgebraCochainLevelEquiv k A M n).toModuleIso)).symm ≪≫
      nativePositiveAlgebraCochainKernelIso k A M

/-- Let `k` be a commutative ring, `A` a commutative `k`-algebra,
and `M` an `A`-module with compatible `k`-action. Represent the
regular chains `C_*(A,A)`, their both-positive shuffle relation
complex `R_*`, quotient `Q_*`, and target `M` at the common height
`T=max(u,v,w)`. Set `H_C=Hom_A(C_*(A,A),M)`,
`H_R=Hom_A(R_*,M)`, and `H_Q=Hom_A(Q_*,M)` there. The degree-zero cohomology of the presented quotient
cochain model is canonically isomorphic to `H⁰(H_C)`. -/
def positiveAlgebraCohomologyZeroIso :
    positiveAlgebraCohomology k A M 0 ≅ (nativeRawAlgebraCochainComplex k A M).homology 0 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 0).mapIso
      (positiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyZeroIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

/-- Let `k` be a commutative ring, `A` a commutative `k`-algebra,
and `M` an `A`-module with compatible `k`-action. Represent the
regular chains `C_*(A,A)`, their both-positive shuffle relation
complex `R_*`, quotient `Q_*`, and target `M` at the common height
`T=max(u,v,w)`. Set `H_C=Hom_A(C_*(A,A),M)`,
`H_R=Hom_A(R_*,M)`, and `H_Q=Hom_A(Q_*,M)` there. The degree-one cohomology of the presented quotient
cochain model is canonically isomorphic to `H¹(H_C)`. -/
def positiveAlgebraCohomologyOneIso :
    positiveAlgebraCohomology k A M 1 ≅ (nativeRawAlgebraCochainComplex k A M).homology 1 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 1).mapIso
      (positiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyOneIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 1 (by omega))
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

end ModuleCat.Algebra.Hochschild.Symmetric
