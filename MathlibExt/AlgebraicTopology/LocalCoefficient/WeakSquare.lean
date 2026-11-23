/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularHomology

/-!
# Original all-integer coefficient comparison across an actual weak square

A strict original square with weak source and target comparison maps has
a derived weak map on its ACTUAL ending-path fibers. Ordinary integral
homology and terminal uniqueness transfer the actual terminal maps. The
existing one-fiber criterion then proves the original all-system chain
map, including nonflat systems. No right-cancellation assertion for
arbitrary all-system equivalences is used.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace TopCat

private theorem localCoefficientHomologyEquivalence_of_weakFiberMap
    {X Y X' Y' : TopCat.{u}} [PathConnectedSpace Y]
    (f : X ⟶ Y) (g : X' ⟶ Y') (y : Y) (z : Y')
    (m : homotopyFiber f y ⟶ homotopyFiber g z)
    (hm : weakHomotopyEquivalences m)
    (hg : IsLocalCoefficientHomologyEquivalence g) :
    IsLocalCoefficientHomologyEquivalence f := by
  have hterminal (n : ℕ) :
      IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
        (terminal.from (homotopyFiber f y))) := by
    let H := AlgebraicTopology.singularIntegralHomologyFunctor n
    letI : IsIso (H.map m) :=
      hm.isIso_singularHomologyFunctor_map AlgebraicTopology.singularIntegralCoefficients.{u} n
    letI : IsIso (H.map (terminal.from (homotopyFiber g z))) :=
      homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence g hg z n
    have hmap : m ≫ terminal.from (homotopyFiber g z) =
        terminal.from (homotopyFiber f y) := Subsingleton.elim _ _
    have hH : H.map (terminal.from (homotopyFiber f y)) =
        H.map m ≫ H.map (terminal.from (homotopyFiber g z)) :=
      (congrArg H.map hmap).symm.trans (H.map_comp _ _)
    rw [hH]
    infer_instance
  intro L n
  let k := localCoefficientPullbackChainMap f L
  letI : QuasiIso k :=
    localCoefficientPullbackChainMap_quasiIso_of_homotopyFiber f y hterminal L
  change IsIso (HomologicalComplex.homologyMap k n)
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap k n).mp inferInstance

/-- Both actual weak comparison maps and the ORIGINAL strict square
transfer every integer target local system to the ORIGINAL source map.
The actual target is path connected; no CW, Kan or flatness input is needed. -/
public theorem localCoefficientHomologyEquivalence_of_weakSquare
    {X Y X' Y' : TopCat.{u}} [PathConnectedSpace Y]
    {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : X ⟶ X') (t : Y ⟶ Y') (comm : f ≫ t = s ≫ g)
    (hs : weakHomotopyEquivalences s) (ht : weakHomotopyEquivalences t)
    (hg : IsLocalCoefficientHomologyEquivalence g) :
    IsLocalCoefficientHomologyEquivalence f := by
  let y : Y := Classical.arbitrary Y
  exact localCoefficientHomologyEquivalence_of_weakFiberMap f g y (t y)
    (homotopyFiberMapOfSquare s t comm y)
    (homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences s t comm y hs ht) hg

/-- An ORIGINAL whole homotopy transfers all integer local systems at a
path-connected target. The actual homotopy-fiber transport, integral
terminal maps and original pullback chain map are used; the source and
its point trace are not changed. -/
public theorem IsLocalCoefficientHomologyEquivalence.of_homotopy
    {X Y : TopCat.{u}} [PathConnectedSpace Y] {f g : X ⟶ Y}
    (hg : IsLocalCoefficientHomologyEquivalence g)
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    IsLocalCoefficientHomologyEquivalence f := by
  let y : Y := Classical.arbitrary Y
  let K : ContinuousMap.Homotopy f.hom ((𝟙 X) ≫ g).hom :=
    H.cast rfl (congrArg TopCat.Hom.hom (Category.id_comp g).symm)
  exact localCoefficientHomologyEquivalence_of_weakFiberMap f g y y
    (homotopyFiberMapOfHomotopy (𝟙 X) f g y K.symm)
    (homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences (𝟙 X) f g y K.symm
      (weakHomotopyEquivalences.id_mem X)) hg

end TopCat

end
