/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CompactParameterEvaluation
public import MathlibExt.Topology.Category.CGWH.GeneratedHomCompactOpen

/-!
# Joint evaluation of compact-open homotopy families

The existing generated/compact-open homeomorphism and generated-topology
lift turn an actual compact-open family into the native internal Hom.
For a locally compact parameter its evaluation is jointly continuous on
the ordinary product with the entire active source. The active source
is Hausdorff and compactly generated; it need not be locally compact.
The original family and every original evaluation value are retained.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u

namespace CGWH

variable {K A B : CGWH.{u, u}} [T2Space A]

private def compactOpenInternalHomRecipe (f : C(K, C(A, B))) :
    K ⟶ internalHom A B := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  let Raw := ContinuousMapGeneratedBy P A B
  let e : Raw ≃ₜ C(A, B) := generatedMapHomeomorphCompactOpenOfT2 A B
  let g : K → Raw := fun k => e.symm (f k)
  letI : IsGeneratedBy P K :=
    (isGeneratedBy_compactHausProbes_iff (Y := K)).2 inferInstance
  have hg : Continuous g := e.symm.continuous.comp f.continuous
  have h : Continuous
      ((WithGeneratedByTopology.equiv (X := P) (Y := Raw)).symm ∘ g) :=
    (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := P) g).mpr hg
  exact ConcreteCategory.ofHom
    (⟨(WithGeneratedByTopology.equiv (X := P) (Y := Raw)).symm ∘ g, h⟩ :
      C(K, WithGeneratedByTopology P Raw))

private theorem compactOpenInternalHomRecipe_apply
    (f : C(K, C(A, B))) (k : K) (a : A) :
    (WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} A B)
      (compactOpenInternalHomRecipe f k) :
        ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u} A B) a =
      f k a := by
  let e := generatedMapHomeomorphCompactOpenOfT2 A B
  change (e.symm (f k) :
    ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u} A B) a = f k a
  have h := congrArg (fun q : C(A, B) => q a) (e.apply_symm_apply (f k))
  exact h

/-- An actual compact-open family lifts to the native internal Hom by the
existing generated/compact-open homeomorphism. No extension or continuity
witness beyond the given continuous family is supplied. -/
public def internalHomFamilyOfCompactOpen (f : C(K, C(A, B))) :
    K ⟶ internalHom A B :=
  compactOpenInternalHomRecipe f

/-- The lifted family evaluates to the same original map at every point. -/
public theorem internalHomFamilyOfCompactOpen_apply
    (f : C(K, C(A, B))) (k : K) (a : A) :
    (WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} A B)
      (internalHomFamilyOfCompactOpen f k) :
        ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u} A B) a =
      f k a := by
  unfold internalHomFamilyOfCompactOpen
  exact compactOpenInternalHomRecipe_apply f k a

variable [LocallyCompactSpace K] [T2Space K]

/-- A locally compact compact-open parameter family evaluates jointly on
the original ordinary product. No local compactness of the active source
is required. In applications K is the actual interval or square. -/
public def compactOpenParameterEvaluationMap (f : C(K, C(A, B))) :
    C(K × A, B) :=
  compactParameterEvaluationMap (internalHomFamilyOfCompactOpen f)

/-- All parameter values, including all homotopy endpoints and boundary
values, are the original compact-open evaluations. -/
public theorem compactOpenParameterEvaluationMap_apply
    (f : C(K, C(A, B))) (k : K) (a : A) :
    compactOpenParameterEvaluationMap f (k, a) = f k a := by
  unfold compactOpenParameterEvaluationMap
  exact (compactParameterEvaluationMap_apply
    (internalHomFamilyOfCompactOpen f) k a).trans
      (internalHomFamilyOfCompactOpen_apply f k a)

end CGWH

end
