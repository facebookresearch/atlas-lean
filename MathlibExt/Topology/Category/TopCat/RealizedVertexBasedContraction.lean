/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ContractionLoopHomotopyEquiv
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyProduct
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

/-!
# Based contractions at original realized vertices

Terminal weakness makes the actual compact-open path-endpoint map weak.
The endpoint map is also a fibration in the selected TopCat model structure.
The realization of an original vertex is a cofibration, so its lifting square
gives paths from every original total point to that vertex, constant at the vertex.
Uncurrying this family gives a based contraction on the entire realization.

The construction needs no path lifting for an external map, replacement total
space, chosen contraction, or restriction to a connected component.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open scoped Simplicial

universe u

namespace TopCat

/-- Terminal weakness makes the original full path-endpoint map weak. -/
theorem pathEndpoints_mem_weakHomotopyEquivalences_of_total_conull
    (E : TopCat.{u}) (hE : weakHomotopyEquivalences (terminal.from E)) :
    weakHomotopyEquivalences (pathEndpoints E) := by
  let t : E ⟶ (⊤_ TopCat.{u}) := terminal.from E
  let e : (⊤_ TopCat.{u}) ⨯ (⊤_ TopCat.{u}) ≅ (⊤_ TopCat.{u}) :=
    prod.rightUnitor _
  have hProduct : weakHomotopyEquivalences (prod.map t t) :=
    weakHomotopyEquivalences.prodMap hE hE
  have hProductComposite : weakHomotopyEquivalences (prod.map t t ≫ e.hom) :=
    weakHomotopyEquivalences.comp_mem _ _ hProduct
      (weakHomotopyEquivalences.of_isIso e.hom)
  have hProductEq : prod.map t t ≫ e.hom = terminal.from (E ⨯ E) :=
    terminal.hom_ext _ _
  have hProductTerminal : weakHomotopyEquivalences (terminal.from (E ⨯ E)) :=
    hProductEq ▸ hProductComposite
  have hPathComposite : weakHomotopyEquivalences (pathEvalZero E ≫ t) :=
    weakHomotopyEquivalences.comp_mem _ _ (pathEvalZero_mem_weakHomotopyEquivalences E) hE
  have hPathEq : pathEvalZero E ≫ t = terminal.from (pathObject E) :=
    terminal.hom_ext _ _
  have hPathTerminal : weakHomotopyEquivalences (terminal.from (pathObject E)) :=
    hPathEq ▸ hPathComposite
  have hEndpointsEq : pathEndpoints E ≫ terminal.from (E ⨯ E) =
      terminal.from (pathObject E) := terminal.hom_ext _ _
  exact weakHomotopyEquivalences.of_postcomp (pathEndpoints E)
    (terminal.from (E ⨯ E)) hProductTerminal (hEndpointsEq.symm ▸ hPathTerminal)

end TopCat

namespace SSet

/-- The actual vertex cofibration yields a contraction fixing that vertex at all times. -/
def basedContractionAtRealizedVertex (K : SSet.{u}) (x : K _⦋0⦌)
    (hK : TopCat.weakHomotopyEquivalences (terminal.from (toTop.obj K))) :
    TopCat.BasedContraction (toTop.obj K) (realizedVertex x) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory.{u}
  let E : TopCat.{u} := toTop.obj K
  let P : TopCat.{u} := toTop.obj (Δ[0] : SSet.{u})
  let e : E := realizedVertex x
  let f : (Δ[0] : SSet.{u}) ⟶ K := yonedaEquiv.symm x
  let i : P ⟶ E := toTop.map f
  let _ : Mono f := stdSimplex.isTerminalObj₀.mono_from f
  let _ : Cofibration i := by
    apply (cofibration_iff i).mpr
    exact toTop_map_mem_realizedBoundaryLLP.{u} f
  have hi : ∀ a : P, i a = e := by
    intro a
    exact congrArg (fun q : P => i q) (Subsingleton.elim a (default : P))
  let a : P ⟶ TopCat.pathObject E :=
    TopCat.const (ContinuousMap.const TopCat.I.{u} e)
  let b : E ⟶ E ⨯ E := prod.lift (𝟙 E) (TopCat.const e)
  let _ : Fibration (TopCat.pathEndpoints E) :=
    TopCat.modelCategory.pathEndpoints_fibration.{u} E
  let _ : WeakEquivalence (TopCat.pathEndpoints E) := by
    apply (weakEquivalence_iff (TopCat.pathEndpoints E)).mpr
    exact TopCat.pathEndpoints_mem_weakHomotopyEquivalences_of_total_conull.{u} E hK
  let _ : HasLiftingProperty i (TopCat.pathEndpoints E) :=
    ModelCategory.cm4b i (TopCat.pathEndpoints E)
  let sq : CommSq a i (TopCat.pathEndpoints E) b := by
    constructor
    apply prod.hom_ext
    · calc
        _ = a ≫ TopCat.pathEvalZero E := by
          simp only [TopCat.pathEndpoints, Category.assoc, prod.lift_fst]
        _ = TopCat.const e := rfl
        _ = i := by
          apply TopCat.hom_ext
          apply ContinuousMap.ext
          intro q
          exact (hi q).symm
        _ = (i ≫ b) ≫ prod.fst := by
          simp only [b, Category.assoc, prod.lift_fst, Category.comp_id]
    · calc
        _ = a ≫ TopCat.pathEvalOne E := by
          simp only [TopCat.pathEndpoints, Category.assoc, prod.lift_snd]
        _ = TopCat.const e := rfl
        _ = (i ≫ b) ≫ prod.snd := by
          simp only [b, Category.assoc, prod.lift_snd]
          rfl
  let g : E ⟶ TopCat.pathObject E := sq.lift
  have hZero : g ≫ TopCat.pathEvalZero E = 𝟙 E := by
    calc
      _ = (g ≫ TopCat.pathEndpoints E) ≫ prod.fst := by
        simp only [TopCat.pathEndpoints, Category.assoc, prod.lift_fst]
      _ = b ≫ prod.fst := congrArg (· ≫ prod.fst) sq.fac_right
      _ = 𝟙 E := prod.lift_fst _ _
  have hOne : g ≫ TopCat.pathEvalOne E = TopCat.const e := by
    calc
      _ = (g ≫ TopCat.pathEndpoints E) ≫ prod.snd := by
        simp only [TopCat.pathEndpoints, Category.assoc, prod.lift_snd]
      _ = b ≫ prod.snd := congrArg (· ≫ prod.snd) sq.fac_right
      _ = TopCat.const e := prod.lift_snd _ _
  have hFixed : g e = ContinuousMap.const TopCat.I.{u} e := by
    have h := ConcreteCategory.congr_hom sq.fac_left (default : P)
    change g (i (default : P)) = ContinuousMap.const TopCat.I.{u} e at h
    exact (congrArg (fun q : E => g q) (hi (default : P)).symm).trans h
  let H : ContinuousMap.Homotopy (ContinuousMap.id E) (ContinuousMap.const E e) :=
    { toFun := fun z => g z.2 (TopCat.I.homeomorph.symm z.1)
      continuous_toFun := by
        exact continuous_eval.comp
          ((g.hom.continuous.comp continuous_snd).prodMk
            (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
      map_zero_left q := by
        have hI : TopCat.I.homeomorph.symm (0 : unitInterval) = (0 : TopCat.I.{u}) := by
          apply TopCat.I.homeomorph.injective
          simp
        exact (congrArg (fun t : TopCat.I.{u} => g q t) hI).trans
          (ConcreteCategory.congr_hom hZero q)
      map_one_left q := by
        have hI : TopCat.I.homeomorph.symm (1 : unitInterval) = (1 : TopCat.I.{u}) := by
          apply TopCat.I.homeomorph.injective
          simp
        exact (congrArg (fun t : TopCat.I.{u} => g q t) hI).trans
          (ConcreteCategory.congr_hom hOne q) }
  refine { homotopy := H, fixed := ?_ }
  intro t
  exact congrArg
    (fun p : C(TopCat.I.{u}, E) => p (TopCat.I.homeomorph.symm t)) hFixed

end SSet

end
