/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneChainQuasiIso
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject

/-!
# Simplicial chains of the realization--singular unit

The canonical unit from a simplicial set to the singular complex of its
realization induces a quasi-isomorphism on unnormalized chains with arbitrary
module coefficients over an arbitrary ring.

The proof factors the literal unit as an anodyne extension followed by a Kan
fibration.  The left factor is handled by the anodyne-chain theorem.  The
right factor is first recognized as a weak equivalence between Kan complexes
using realization weakness and then handled by the simplicial Whitehead
theorem.  No arbitrary weak-equivalence-to-chain theorem is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra HomologicalComplex MorphismProperty

universe u

namespace SSet.RealizationUnitChains

private theorem anodyneExtensions_le_realizationWeakEquivalences :
    SSet.anodyneExtensions.{u} ≤
      SSet.realizationWeakEquivalences.{u} := by
  intro X Y f hf
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  apply TopCat.horn_llp_le_weakHomotopyEquivalences
  rw [SSet.anodyneExtensions_eq_llp_rlp] at hf
  intro A B p hp
  exact (sSetTopAdj.hasLiftingProperty_iff f p).mpr
    (hf _ ((TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hp))

open scoped SSet.modelCategoryQuillen in
/-- The realization--singular unit induces a quasi-isomorphism on simplicial
chains with coefficients in an arbitrary module over an arbitrary ring. -/
theorem _root_.SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app
    {R : Type u} [Ring R] (A : ModuleCat.{u} R) (X : SSet.{u}) :
    QuasiIso
      (SSet.chainComplexMap (sSetTopAdj.unit.app X) A) := by
  let d := SSet.modelCategoryQuillen.anodyneFactorizationData
    (sSetTopAdj.unit.app X)
  have hiWeak : SSet.realizationWeakEquivalences d.i :=
    anodyneExtensions_le_realizationWeakEquivalences d.i d.hi
  have hUnit : SSet.realizationWeakEquivalences
      (sSetTopAdj.unit.app X) :=
    SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X
  have hComp : SSet.realizationWeakEquivalences (d.i ≫ d.p) := by
    rw [d.fac]
    exact hUnit
  have hpWeak : SSet.realizationWeakEquivalences d.p :=
    SSet.realizationWeakEquivalences.of_precomp d.i d.p hiWeak hComp
  let _ : SSet.KanComplex
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj X) := by
    change SSet.KanComplex
      (TopCat.toSSet.obj (SSet.toTop.obj X))
    exact TopCat.toSSet_obj_kanComplex _
  let _ : Fibration d.p := ⟨d.hp⟩
  let _ : SSet.KanComplex d.Z := isFibrant_of_fibration d.p
  have hpW : SSet.KanComplex.W d.p :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence d.p).mpr hpWeak
  have hiChain : QuasiIso (SSet.chainComplexMap d.i A) :=
    SSet.anodyneExtensions.quasiIso_chainComplexMap A d.hi
  have hpChain : QuasiIso (SSet.chainComplexMap d.p A) :=
    hpW.quasiIso_chainComplexMap A
  have hComposite : QuasiIso
      (SSet.chainComplexMap d.i A ≫
        SSet.chainComplexMap d.p A) :=
    quasiIso_comp _ _ (hφ := hiChain) (hφ' := hpChain)
  change QuasiIso
    (((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj A).map
      (sSetTopAdj.unit.app X))
  rw [← d.fac, Functor.map_comp]
  exact hComposite

end SSet.RealizationUnitChains
