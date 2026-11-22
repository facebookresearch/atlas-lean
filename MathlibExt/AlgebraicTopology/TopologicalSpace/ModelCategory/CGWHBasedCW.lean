/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.SubcomplexModelCofibration
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHRealizationLifting

/-!
# Classical based CW spaces are model cofibrant in pointed CGWH

The chosen basepoint is an original zero cell of the original Hausdorff CW
space. Its complete classical cell maps and infinite skeletons prove the
model cofibration and pointed-model cofibrancy, independently of spectra.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open scoped CGWH.modelCategory CGWH.limits

namespace PointedCGWH.ClassicalCW

open Topology.CWComplex

/-- The actual chosen zero cell is a classical singleton subcomplex, without
any finiteness restriction on the surrounding CW space. -/
private def zeroCellSubcomplex (X : TopCat.{v}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (j : cell (Set.univ : Set X) 0) : Subcomplex (Set.univ : Set X) where
  carrier := {map (C := Set.univ) 0 j ![]}
  I n := {k | (⟨n, k⟩ : Σ n, cell (Set.univ : Set X) n) = ⟨0, j⟩}
  closed' := isClosed_singleton
  union' := by
    rw [Set.empty_union]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨⟨k, hk⟩, hx⟩
      have hN : n = 0 := congrArg Sigma.fst hk
      subst n
      have hK : k = j := eq_of_heq (Sigma.mk.inj_iff.mp hk).2
      subst k
      simpa only [RelCWComplex.openCell_zero_eq_singleton] using hx
    · intro hx
      apply Set.mem_iUnion.mpr
      refine ⟨0, Set.mem_iUnion.mpr ⟨⟨j, rfl⟩, ?_⟩⟩
      simpa only [RelCWComplex.openCell_zero_eq_singleton] using hx

private theorem zeroCellSubcomplex_carrier (X : TopCat.{v}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (j : cell (Set.univ : Set X) 0) :
    (zeroCellSubcomplex X j : Set X) = {map (C := Set.univ) 0 j ![]} := rfl

/-- Every actual CGWH trivial fibration retains all realized-boundary lifts
under the same full underlying topological functor. -/
private theorem trivialFibration_underlying_boundaryRLP {E F : CGWH.{u, v}}
    (p : E ⟶ F) (hp : trivialFibrations CGWH.{u, v} p) :
    TopCat.realizedBoundaryInclusions.rlp (CGWH.cgwhToTop.map p) := by
  have hR : CGWH.realizedBoundaryInclusions.rlp p :=
    (CGWH.cofibrantGenerationData.I_rlp).symm ▸ hp
  rw [CGWH.realizedBoundaryInclusions_rlp,
    CompactlyGenerated.realizedBoundaryInclusions_rlp] at hR
  exact hR


open Topology.CWComplex

/-- The named original CGWH point is the actual singleton zero-cell subspace. -/
private def zeroCellPointIso (X : TopCat.{v}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (j : cell (Set.univ : Set X) 0) :
    CGWH.cgwhToTop.obj CGWH.point.{u, v} ≅ TopCat.of (zeroCellSubcomplex X j : Set X) where
  hom := TopCat.ofHom
    ⟨fun _ => ⟨map (C := Set.univ) 0 j ![], by
      change map (C := Set.univ) 0 j ![] = map (C := Set.univ) 0 j ![]
      rfl⟩, continuous_const⟩
  inv := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  hom_inv_id := by
    apply TopCat.ext
    intro x
    change (PUnit.unit : PUnit.{v + 1}) = x
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    change map (C := Set.univ) 0 j ![] = x.val
    exact x.property.symm

/-- The full point-subcomplex isomorphism retains the same original basepoint map. -/
private theorem zeroCellPointIso_hom_comp
    (M : PointedCGWH.{u, v}) [T2Space (CGWH.cgwhToTop.obj M.right)]
    [CWComplex (Set.univ : Set (CGWH.cgwhToTop.obj M.right))]
    (j : cell (Set.univ : Set (CGWH.cgwhToTop.obj M.right)) 0)
    (hj : ∀ x : CGWH.point.{u, v}, M.hom x = map (C := Set.univ) 0 j ![]) :
    (zeroCellPointIso.{u, v} (CGWH.cgwhToTop.obj M.right) j).hom ≫
      subcomplexInclusion (zeroCellSubcomplex (CGWH.cgwhToTop.obj M.right) j) =
        CGWH.cgwhToTop.map M.hom := by
  apply TopCat.ext
  intro x
  exact (hj x).symm

/-- The original based CW zero-cell inclusion is a genuine CGWH model cofibration.
The proof retains every classical characteristic map and every infinite skeleton. -/
theorem classicalBasepoint_cofibration
    (M : PointedCGWH.{u, v}) [T2Space (CGWH.cgwhToTop.obj M.right)]
    [CWComplex (Set.univ : Set (CGWH.cgwhToTop.obj M.right))]
    (j : cell (Set.univ : Set (CGWH.cgwhToTop.obj M.right)) 0)
    (hj : ∀ x : CGWH.point.{u, v}, M.hom x = map (C := Set.univ) 0 j ![]) :
    cofibrations CGWH.{u, v} M.hom := by
  let U := CGWH.cgwhToTop.{u, v}
  let X := U.obj M.right
  let _ : T2Space X := inferInstanceAs (T2Space (CGWH.cgwhToTop.obj M.right))
  let _ : CWComplex (Set.univ : Set X) :=
    inferInstanceAs (CWComplex (Set.univ : Set (CGWH.cgwhToTop.obj M.right)))
  let A := zeroCellSubcomplex X j
  let e : Arrow.mk (U.map M.hom) ≅ Arrow.mk (subcomplexInclusion A) :=
    Arrow.isoMk (zeroCellPointIso.{u, v} X j) (Iso.refl X)
      ((zeroCellPointIso_hom_comp.{u, v} M j hj).trans (Category.comp_id _).symm)
  have hA := Topology.CWComplex.subcomplexInclusion_mem_realizedBoundaryLLP X A
  rw [← trivialFibrations_llp]
  intro E F p hp
  let _ : HasLiftingProperty (subcomplexInclusion A) (U.map p) :=
    hA (U.map p) (trivialFibration_underlying_boundaryRLP p hp)
  have hBase : HasLiftingProperty (U.map M.hom) (U.map p) :=
    HasLiftingProperty.of_arrow_iso_left e.symm (U.map p)
  exact (Functor.hasLiftingProperty_map_iff_of_full_faithful U M.hom p).mp hBase

/-- Every classical Hausdorff based CW coefficient is cofibrant in the actual
pointed model, with its named basepoint retained as its original zero cell. -/
theorem classicalBasedCW_isCofibrant
    (M : PointedCGWH.{u, v}) [T2Space (CGWH.cgwhToTop.obj M.right)]
    [CWComplex (Set.univ : Set (CGWH.cgwhToTop.obj M.right))]
    (j : cell (Set.univ : Set (CGWH.cgwhToTop.obj M.right)) 0)
    (hj : ∀ x : CGWH.point.{u, v}, M.hom x = map (C := Set.univ) 0 j ![]) :
    IsCofibrant M :=
  (PointedCGWH.isCofibrant_iff M).mpr (classicalBasepoint_cofibration M j hj)


end PointedCGWH.ClassicalCW
