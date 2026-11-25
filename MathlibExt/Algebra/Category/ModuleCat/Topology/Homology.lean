/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Concrete homology quotients in `TopModuleCat`

The homology projection of a `TopModuleCat`-valued homological complex is
surjective on underlying carriers.  A cycle maps to zero exactly when its
included cochain is an explicit boundary from the predecessor degree.

If the middle term of the complex is discrete, then the selected homology
object is discrete.  This is proved by comparing selected cycles with the
explicit subspace kernel and selected homology with the explicit
quotient-topology cokernel.

These statements use the concrete quotient model of cokernels in
`TopModuleCat`; they do not infer surjectivity from a categorical epimorphism.

## Main declarations

* `HomologicalComplex.discreteTopology_homology`
* `HomologicalComplex.homologyπ_surjective`
* `HomologicalComplex.homologyπ_eq_zero_iff_exists_boundary`
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe u v w

namespace HomologicalComplex

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {ι : Type v} {c : ComplexShape ι}
variable (K : HomologicalComplex (TopModuleCat.{w} R) c)

/-- The abstract homology quotient and the concrete `TopModuleCat` cokernel
are isomorphic compatibly with their quotient maps. -/
private theorem exists_homology_coker_iso (i j : ι) (hPrev : c.prev j = i) :
    ∃ e : K.homology j ≅ TopModuleCat.coker (K.toCycles i j),
      TopModuleCat.cokerπ (K.toCycles i j) = K.homologyπ j ≫ e.hom := by
  let hCoker := K.homologyIsCokernel i j hPrev
  let hConcrete := TopModuleCat.isColimitCoker (K.toCycles i j)
  let e := IsColimit.coconePointUniqueUpToIso hCoker hConcrete
  have hbase := IsColimit.comp_coconePointUniqueUpToIso_hom
    hCoker hConcrete WalkingParallelPair.one
  have hHomologyLeg :
      ((CokernelCofork.ofπ (K.homologyπ j)
        (K.toCycles_comp_homologyπ i j)).ι.app
          WalkingParallelPair.one) = K.homologyπ j := rfl
  have hConcreteLeg :
      ((CokernelCofork.ofπ
        (TopModuleCat.cokerπ (K.toCycles i j))
        (TopModuleCat.comp_cokerπ (K.toCycles i j))).ι.app
          WalkingParallelPair.one) =
        TopModuleCat.cokerπ (K.toCycles i j) := rfl
  refine ⟨e, ?_⟩
  rw [hHomologyLeg, hConcreteLeg] at hbase
  exact hbase.symm

/-- If the middle term of a `TopModuleCat`-valued homological complex is
discrete, then its categorically selected homology object is discrete. -/
theorem discreteTopology_homology (i : ι)
    [DiscreteTopology (K.X i)] :
    DiscreteTopology (K.homology i) := by
  have hKer : DiscreteTopology
      (TopModuleCat.ker (K.d i (c.next i))) := by
    change DiscreteTopology (K.d i (c.next i)).hom.ker
    infer_instance
  let eCycles : TopModuleCat.ker (K.d i (c.next i)) ≅ K.cycles i :=
    IsLimit.conePointUniqueUpToIso
      (TopModuleCat.isLimitKer (K.d i (c.next i)))
      (K.cyclesIsKernel i (c.next i) rfl)
  let _ : DiscreteTopology (K.cycles i) :=
    eCycles.toContinuousLinearEquiv.toHomeomorph.discreteTopology_iff.mp hKer
  have hCoker : DiscreteTopology
      (TopModuleCat.coker (K.toCycles (c.prev i) i)) := by
    change DiscreteTopology
      (K.cycles i ⧸ (K.toCycles (c.prev i) i).hom.range)
    exact QuotientAddGroup.discreteTopology_iff.mpr (isOpen_discrete _)
  let eHomology : K.homology i ≅
      TopModuleCat.coker (K.toCycles (c.prev i) i) :=
    IsColimit.coconePointUniqueUpToIso
      (K.homologyIsCokernel (c.prev i) i rfl)
      (TopModuleCat.isColimitCoker (K.toCycles (c.prev i) i))
  exact eHomology.toContinuousLinearEquiv.toHomeomorph.discreteTopology_iff.mpr
    hCoker

/-- The homology projection of a `TopModuleCat`-valued homological complex is
surjective on underlying carriers when `i` is the predecessor of `j`. -/
theorem homologyπ_surjective (i j : ι) (hPrev : c.prev j = i) :
    Function.Surjective (K.homologyπ j) := by
  obtain ⟨e, hcomparison⟩ := K.exists_homology_coker_iso i j hPrev
  intro x
  obtain ⟨z, hz⟩ := TopModuleCat.cokerπ_surjective
    (K.toCycles i j) (e.hom x)
  refine ⟨z, ?_⟩
  have hz' : e.hom (K.homologyπ j z) = e.hom x := by
    rw [← ConcreteCategory.comp_apply, ← hcomparison]
    exact hz
  have hz'' := congrArg (fun y => e.inv y) hz'
  simpa only [← ConcreteCategory.comp_apply, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ConcreteCategory.id_apply] using hz''

/-- A cycle has zero homology class exactly when its included cochain is the
differential of a cochain in the predecessor degree. -/
theorem homologyπ_eq_zero_iff_exists_boundary
    (i j : ι) (hPrev : c.prev j = i) (z : K.cycles j) :
    K.homologyπ j z = 0 ↔
      ∃ b : K.X i, (K.iCycles j).hom z = (K.d i j).hom b := by
  constructor
  · intro hz
    obtain ⟨e, hcomparison⟩ := K.exists_homology_coker_iso i j hPrev
    have hcoker : (TopModuleCat.cokerπ (K.toCycles i j)).hom z = 0 := by
      rw [hcomparison, TopModuleCat.hom_comp,
        ContinuousLinearMap.comp_apply, hz, map_zero]
    have hmk : Submodule.mkQ (K.toCycles i j).hom.range z = 0 := by
      rw [← TopModuleCat.hom_cokerπ]
      exact hcoker
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero
      (p := (K.toCycles i j).hom.range)).mp
      (by rw [← Submodule.mkQ_apply]; exact hmk)
    refine ⟨b, ?_⟩
    rw [← hb]
    exact ConcreteCategory.congr_hom (K.toCycles_i i j) b
  · rintro ⟨b, hb⟩
    have hzcycles : z = (K.toCycles i j).hom b := by
      apply (ModuleCat.mono_iff_injective
        ((forget₂ (TopModuleCat R) (ModuleCat R)).map (K.iCycles j))).mp
          inferInstance
      change (K.iCycles j).hom z =
        (K.iCycles j).hom ((K.toCycles i j).hom b)
      rw [hb]
      exact (ConcreteCategory.congr_hom (K.toCycles_i i j) b).symm
    rw [hzcycles, ← ConcreteCategory.comp_apply,
      HomologicalComplex.toCycles_comp_homologyπ]
    rfl

end HomologicalComplex
