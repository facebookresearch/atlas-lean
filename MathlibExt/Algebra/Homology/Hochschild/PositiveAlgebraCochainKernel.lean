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
# Algebra-linear annihilator cochain complexes

Dualizing the inclusion of the proper relation complex and its
quotient by Hom_A(-, M) gives an annihilator kernel cochain complex.
The relation terms vanish in chain degrees zero and one, giving
the corresponding two cohomology comparisons. The construction
uses arbitrary target modules and finite cokernel preservation.
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

/-- The original relation inclusion and original quotient are an categorical cokernel. -/
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

/-- The original regular raw A-linear chain complex in the canonical Hom universe. -/
def regularAlgebraRawForHom : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (algebraRawComplex k A A)

/-- The regular proper relation complex in the same canonical Hom universe. -/
def regularAlgebraRelationsForHom : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (algebraPositiveRelationComplex k A A)

/-- The lifted regular relation inclusion. -/
def regularAlgebraRelationInclusionForHom :
    regularAlgebraRelationsForHom.{u, v, w} k A ⟶ regularAlgebraRawForHom.{u, v, w} k A :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (algebraPositiveRelationInclusion k A A)

/-- The lifted original quotient projection. -/
def regularAlgebraPositiveProjectionForHom :
    regularAlgebraRawForHom.{u, v, w} k A ⟶ regularAlgebraPositiveQuotientForHom.{u, v, w} k A :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (algebraRawPositiveProjection k A A)

/-- Native lifting preserves the vanishing composite. -/
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

/-- Native finite-colimit preservation transports the original cokernel. -/
def regularAlgebraPositiveCoforkIsColimit :
    IsColimit (CokernelCofork.ofπ (regularAlgebraPositiveProjectionForHom.{u, v, w} k A)
      (regularAlgebraRelationInclusion_projectionForHom.{u, v, w} k A)) := by
  let F := (ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)
  exact CokernelCofork.mapIsColimit _ (algebraPositiveQuotientCoforkIsColimit k A A) F

/-- Native Hom_A cochains on the original raw regular chain complex. -/
def nativeRawAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).obj
      (Opposite.op (regularAlgebraRawForHom.{u, v, w} k A))

/-- Native Hom_A cochains on the regular proper relation complex. -/
def nativeRelationAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).obj
      (Opposite.op (regularAlgebraRelationsForHom.{u, v, w} k A))

/-- The defining annihilator map is native precomposition with the original relation inclusion. -/
def nativeAlgebraRelationCochainMap :
    nativeRawAlgebraCochainComplex k A M ⟶ nativeRelationAlgebraCochainComplex k A M :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).map
      (regularAlgebraRelationInclusionForHom.{u, v, w} k A).op

/-- The quotient-induced cochain inclusion is native precomposition with the original quotient. -/
def nativePositiveAlgebraCochainInclusion :
    nativePositiveAlgebraCochainComplex k A M ⟶ nativeRawAlgebraCochainComplex k A M :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).map
      (regularAlgebraPositiveProjectionForHom.{u, v, w} k A).op

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The original quotient-induced cochain map lands in the annihilator kernel. -/
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

/-- Opposite cokernels and native Hom limit preservation earn the annihilator kernel property. -/
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

/-- Conventional Hom_A of the proper quotient is the kernel of the relation-cochain map. -/
def nativePositiveAlgebraCochainKernelIso :
    nativePositiveAlgebraCochainComplex k A M ≅ kernel (nativeAlgebraRelationCochainMap k A M) :=
  IsLimit.conePointUniqueUpToIso (nativePositiveAlgebraCochainKernelIsLimit k A M)
    (limit.isLimit (parallelPair (nativeAlgebraRelationCochainMap k A M) 0))

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The kernel identification retains the quotient-induced map as its forward inclusion. -/
@[reassoc]
theorem nativePositiveAlgebraCochainKernelIso_hom_ι :
    (nativePositiveAlgebraCochainKernelIso k A M).hom ≫
      kernel.ι (nativeAlgebraRelationCochainMap k A M) = nativePositiveAlgebraCochainInclusion k A M :=
  IsLimit.conePointUniqueUpToIso_hom_comp (nativePositiveAlgebraCochainKernelIsLimit k A M)
    (limit.isLimit (parallelPair (nativeAlgebraRelationCochainMap k A M) 0)) WalkingParallelPair.zero

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The defining relation-cochain map vanishes at the two original low degrees. -/
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

/-- The quotient-induced map gives the conventional low degree-zero cohomology comparison. -/
def nativePositiveAlgebraCohomologyZeroIso :
    (nativePositiveAlgebraCochainComplex k A M).homology 0 ≅
      (nativeRawAlgebraCochainComplex k A M).homology 0 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 0).mapIso
      (nativePositiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyZeroIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

/-- The quotient-induced map gives the conventional low degree-one cohomology comparison. -/
def nativePositiveAlgebraCohomologyOneIso :
    (nativePositiveAlgebraCochainComplex k A M).homology 1 ≅
      (nativeRawAlgebraCochainComplex k A M).homology 1 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 1).mapIso
      (nativePositiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyOneIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 1 (by omega))
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The degree-zero comparison is exactly homology of original quotient precomposition. -/
theorem nativePositiveAlgebraCohomologyZeroIso_hom :
    (nativePositiveAlgebraCohomologyZeroIso k A M).hom =
      HomologicalComplex.homologyMap (nativePositiveAlgebraCochainInclusion k A M) 0 := by
  change HomologicalComplex.homologyMap (nativePositiveAlgebraCochainKernelIso k A M).hom 0 ≫
    HomologicalComplex.homologyMap (kernel.ι (nativeAlgebraRelationCochainMap k A M)) 0 = _
  rw [← HomologicalComplex.homologyMap_comp, nativePositiveAlgebraCochainKernelIso_hom_ι]

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The degree-one comparison is exactly homology of original quotient precomposition. -/
theorem nativePositiveAlgebraCohomologyOneIso_hom :
    (nativePositiveAlgebraCohomologyOneIso k A M).hom =
      HomologicalComplex.homologyMap (nativePositiveAlgebraCochainInclusion k A M) 1 := by
  change HomologicalComplex.homologyMap (nativePositiveAlgebraCochainKernelIso k A M).hom 1 ≫
    HomologicalComplex.homologyMap (kernel.ι (nativeAlgebraRelationCochainMap k A M)) 1 = _
  rw [← HomologicalComplex.homologyMap_comp, nativePositiveAlgebraCochainKernelIso_hom_ι]

/-- The conventional original-world quotient cochain complex is the same annihilator kernel. -/
def positiveAlgebraCochainKernelIso :
    positiveAlgebraCochainComplex k A M ≅ kernel (nativeAlgebraRelationCochainMap k A M) :=
  ((nativePositiveAlgebraCochainComplex k A M).changeObjectsIso
    (fun n => (positiveAlgebraCochainLevelEquiv k A M n).toModuleIso)).symm ≪≫
      nativePositiveAlgebraCochainKernelIso k A M

/-- The conventional degree-zero proper-shuffle cohomology maps isomorphically to raw Hom_A cohomology. -/
def positiveAlgebraCohomologyZeroIso :
    positiveAlgebraCohomology k A M 0 ≅ (nativeRawAlgebraCochainComplex k A M).homology 0 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 0).mapIso
      (positiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyZeroIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

/-- The conventional degree-one proper-shuffle cohomology maps isomorphically to raw Hom_A cohomology. -/
def positiveAlgebraCohomologyOneIso :
    positiveAlgebraCohomology k A M 1 ≅ (nativeRawAlgebraCochainComplex k A M).homology 1 :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} A) (ComplexShape.up ℕ) 1).mapIso
      (positiveAlgebraCochainKernelIso k A M) ≪≫
    HomologicalComplex.kernelHomologyOneIso (nativeAlgebraRelationCochainMap k A M)
      (nativeAlgebraRelationCochainMap_low k A M 1 (by omega))
      (nativeAlgebraRelationCochainMap_low k A M 0 (by omega))

end ModuleCat.Algebra.Hochschild.Symmetric
