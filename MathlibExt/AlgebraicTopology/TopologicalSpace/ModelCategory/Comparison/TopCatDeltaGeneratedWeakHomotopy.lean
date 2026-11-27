/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyIdentities
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import Mathlib.Topology.Category.DeltaGenerated

/-!
# Weak homotopy comparison for delta-generated coreflection

For every topological space `X`, the delta-generated coreflection counit
`δX → X` becomes an isomorphism after applying the singular-complex functor.
Consequently this counit is a weak homotopy equivalence. The statements apply
uniformly in the space universe.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Topology

namespace TopCat

private theorem coreflectionCounit_injective (X : TopCat.{u}) :
    Function.Injective
      (DeltaGenerated.coreflectorAdjunction.counit.app X).hom := by
  exact WithGeneratedByTopology.equiv.injective

/--
The singular-complex functor sends the delta-generated coreflection counit of
any topological space to an isomorphism.
-/
theorem toSSet_map_coreflectionCounit_isIso (X : TopCat.{u}) :
    IsIso (TopCat.toSSet.map
      (DeltaGenerated.coreflectorAdjunction.counit.app X)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [CategoryTheory.isIso_iff_bijective]
  constructor
  · intro a b hab
    apply ((DeltaGenerated.deltaGeneratedToTop.obj
      (TopCat.toDeltaGenerated.obj X)).toSSetObjEquiv n).injective
    apply ContinuousMap.ext
    intro z
    apply coreflectionCounit_injective X
    have ha :
        (X.toSSetObjEquiv n)
          ((TopCat.toSSet.map
            (DeltaGenerated.coreflectorAdjunction.counit.app X)).app n a) =
          (DeltaGenerated.coreflectorAdjunction.counit.app X).hom.comp
            ((DeltaGenerated.deltaGeneratedToTop.obj
              (TopCat.toDeltaGenerated.obj X)).toSSetObjEquiv n a) := rfl
    have hb :
        (X.toSSetObjEquiv n)
          ((TopCat.toSSet.map
            (DeltaGenerated.coreflectorAdjunction.counit.app X)).app n b) =
          (DeltaGenerated.coreflectorAdjunction.counit.app X).hom.comp
            ((DeltaGenerated.deltaGeneratedToTop.obj
              (TopCat.toDeltaGenerated.obj X)).toSSetObjEquiv n b) := rfl
    have hmaps :
        (DeltaGenerated.coreflectorAdjunction.counit.app X).hom.comp
            ((DeltaGenerated.deltaGeneratedToTop.obj
              (TopCat.toDeltaGenerated.obj X)).toSSetObjEquiv n a) =
          (DeltaGenerated.coreflectorAdjunction.counit.app X).hom.comp
            ((DeltaGenerated.deltaGeneratedToTop.obj
              (TopCat.toDeltaGenerated.obj X)).toSSetObjEquiv n b) := by
      rw [← ha, ← hb, hab]
    exact ContinuousMap.congr_fun hmaps z
  · intro s
    let g := X.toSSetObjEquiv n s
    let gCore : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)),
        DeltaGenerated.deltaGeneratedToTop.obj
          (TopCat.toDeltaGenerated.obj X)) :=
      ⟨(WithGeneratedByTopology.equiv
          (X := fun n : ℕ => Fin n → ℝ)).symm ∘ g, by
        exact (Topology.IsGeneratedBy.equiv_symm_comp_continuous_iff
          (X := fun n : ℕ => Fin n → ℝ) g).2 g.continuous⟩
    let t := ((DeltaGenerated.deltaGeneratedToTop.obj
      (TopCat.toDeltaGenerated.obj X)).toSSetObjEquiv n).symm gCore
    refine ⟨t, (X.toSSetObjEquiv n).injective ?_⟩
    change (DeltaGenerated.coreflectorAdjunction.counit.app X).hom.comp
      (((DeltaGenerated.deltaGeneratedToTop.obj
        (TopCat.toDeltaGenerated.obj X)).toSSetObjEquiv n) t) = g
    rw [Equiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro z
    rfl

/--
The delta-generated coreflection counit `δX → X` is a weak homotopy equivalence
for every topological space `X`.
-/
theorem coreflectionCounit_mem_weakHomotopyEquivalences (X : TopCat.{u}) :
    weakHomotopyEquivalences
      (DeltaGenerated.coreflectorAdjunction.counit.app X) := by
  let _ : IsIso (toSSet.map
      (DeltaGenerated.coreflectorAdjunction.counit.app X)) :=
    toSSet_map_coreflectionCounit_isIso X
  let _ : SSet.KanComplex
      (toSSet.obj
        ((TopCat.toDeltaGenerated ⋙
          DeltaGenerated.deltaGeneratedToTop).obj X)) :=
    toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      (toSSet.obj ((𝟭 TopCat).obj X)) :=
    toSSet_obj_kanComplex _
  rw [mem_weakHomotopyEquivalences_iff]
  exact SSet.KanComplex.W.ofIso
    (asIso (toSSet.map
      (DeltaGenerated.coreflectorAdjunction.counit.app X)))

end TopCat
