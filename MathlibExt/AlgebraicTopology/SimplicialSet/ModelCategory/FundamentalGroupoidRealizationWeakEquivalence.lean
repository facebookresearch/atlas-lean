/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneFundamentalGroupoid
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject

/-!
# Fundamental groupoids and realization weak equivalences

In every universe, a realization weak equivalence of simplicial sets induces
an equivalence of fundamental groupoids.  The proof compares functorial
anodyne fibrant replacements and then uses the established comparison between
realization weak equivalences and weak equivalences of Kan complexes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MorphismProperty Simplicial
open scoped Simplicial

namespace SSet

private theorem anodyneExtensions_le_realizationWeakEquivalences :
    SSet.anodyneExtensions.{u} ≤
      SSet.realizationWeakEquivalences.{u} := by
  intro X Y i hi
  rw [SSet.mem_realizationWeakEquivalences_iff]
  apply (TopCat.mem_weakHomotopyEquivalences_iff _).mp
  apply TopCat.horn_llp_le_weakHomotopyEquivalences
  rw [SSet.anodyneExtensions_eq_llp_rlp] at hi
  intro A B p hp
  exact (sSetTopAdj.hasLiftingProperty_iff i p).mpr
    (hi _ ((TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hp))

namespace realizationWeakEquivalences

/-- A realization weak equivalence induces an equivalence of
simplicial fundamental groupoids. -/
theorem isEquivalence_mapFundamentalGroupoid
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) :
    (SSet.mapFundamentalGroupoid f).IsEquivalence := by
  let _ : CategoryWithFibrations SSet.{u} :=
    SSet.modelCategoryQuillen.instCategoryWithFibrations
  let data := SSet.modelCategoryQuillen.anodyneFunctorialFactorizationData
  let dX := data.factorizationData (terminal.from X)
  let dY := data.factorizationData (terminal.from Y)
  let phi : Arrow.mk (terminal.from X) ⟶ Arrow.mk (terminal.from Y) :=
    Arrow.homMk f (𝟙 _) (by simp)
  let Rf : dX.Z ⟶ dY.Z := data.mapZ phi
  have hNat : dX.i ≫ Rf = f ≫ dY.i := data.i_mapZ phi
  have hjX : SSet.realizationWeakEquivalences dX.i :=
    anodyneExtensions_le_realizationWeakEquivalences dX.i dX.hi
  have hjY : SSet.realizationWeakEquivalences dY.i :=
    anodyneExtensions_le_realizationWeakEquivalences dY.i dY.hi
  have hRight : SSet.realizationWeakEquivalences (f ≫ dY.i) :=
    SSet.realizationWeakEquivalences.comp_mem f dY.i hf hjY
  have hLeft : SSet.realizationWeakEquivalences (dX.i ≫ Rf) := by
    rw [hNat]
    exact hRight
  have hRf : SSet.realizationWeakEquivalences Rf :=
    SSet.realizationWeakEquivalences.of_precomp dX.i Rf hjX hLeft
  let _ : Fibration dX.p := ⟨dX.hp⟩
  let _ : Fibration dY.p := ⟨dY.hp⟩
  let _ : SSet.KanComplex (⊤_ SSet.{u}) := by
    exact (isFibrant_iff_of_isTerminal (𝟙 _) terminalIsTerminal).2
      (by infer_instance)
  let _ : SSet.KanComplex dX.Z := isFibrant_of_fibration dX.p
  let _ : SSet.KanComplex dY.Z := isFibrant_of_fibration dY.p
  have hRfW : SSet.KanComplex.W Rf :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence Rf).mpr hRf
  let F := SSet.mapFundamentalGroupoid f
  let UX := SSet.mapFundamentalGroupoid dX.i
  let UY := SSet.mapFundamentalGroupoid dY.i
  let RF := SSet.mapFundamentalGroupoid Rf
  let squareIso : F ⋙ UY ≅ UX ⋙ RF :=
    SSet.mapFundamentalGroupoidComp f dY.i ≪≫
      SSet.congrMapFundamentalGroupoidOfEq hNat.symm ≪≫
        (SSet.mapFundamentalGroupoidComp dX.i Rf).symm
  let _ : UX.IsEquivalence :=
    dX.hi.isEquivalence_mapFundamentalGroupoid
  let _ : UY.IsEquivalence :=
    dY.hi.isEquivalence_mapFundamentalGroupoid
  let _ : RF.IsEquivalence := hRfW.isEquivalence_mapFundamentalGroupoid
  let _ : (UX ⋙ RF).IsEquivalence := inferInstance
  let _ : (F ⋙ UY).IsEquivalence :=
    Functor.isEquivalence_of_iso squareIso.symm
  exact Functor.isEquivalence_of_comp_right F UY

end realizationWeakEquivalences

/-- The realization--singular unit induces an equivalence of simplicial
fundamental groupoids. -/
theorem sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid
    (X : SSet.{u}) :
    (SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X)).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
    (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X)

end SSet

end
