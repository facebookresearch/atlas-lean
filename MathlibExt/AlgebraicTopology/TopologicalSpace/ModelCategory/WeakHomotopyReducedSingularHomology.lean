/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Reduced
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularChains

/-!
# Reduced singular homology of weak homotopy equivalences

A weak homotopy equivalence of spaces induces an isomorphism on the existing
reduced singular-homology functor in every degree, including degree zero. The
proof transports the ordinary homology isomorphism through the augmentation
kernels; it assumes neither connectedness nor nonemptiness.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicTopology CategoryTheory HomologicalComplex Limits

universe w v u

namespace TopCat.weakHomotopyEquivalences

/-- A weak homotopy equivalence induces an isomorphism on reduced singular
homology in every degree, including degree zero. -/
theorem isIso_reducedSingularHomologyFunctor_map
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    {X Y : TopCat.{w}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) (A : C) (n : ℕ) :
    IsIso ((reducedSingularHomologyFunctor C A n).map f) := by
  let H := (singularHomologyFunctor C n).obj A
  let P := pointSingularHomologyFunctor C A n
  let aug := singularHomologyAugmentation C A n
  let p := H.map f
  let q := P.map f
  have hChain : QuasiIso
      (((singularChainComplexFunctor C).obj A).map f) :=
    hf.quasiIso_singularChainComplexMap A
  let _ : QuasiIso
      (((singularChainComplexFunctor C).obj A).map f) := hChain
  have hp : IsIso p := by
    change IsIso (homologyMap
      (((singularChainComplexFunctor C).obj A).map f) n)
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance
  have hq : IsIso q := by
    dsimp only [q, P, pointSingularHomologyFunctor]
    infer_instance
  let _ : IsIso p := hp
  let _ : IsIso q := hq
  have hw : aug.app X ≫ q = p ≫ aug.app Y := by
    dsimp only [aug, q, p, P, H]
    exact ((singularHomologyAugmentation C A n).naturality f).symm
  let k := kernel.map (aug.app X) (aug.app Y) p q hw
  let _ : IsIso k := by
    dsimp only [k]
    infer_instance
  let eX := reducedSingularHomologyObjIso C A n X
  let eY := reducedSingularHomologyObjIso C A n Y
  let r := (reducedSingularHomologyFunctor C A n).map f
  have heX : eX.inv ≫ (reducedSingularHomologyι C A n).app X =
      kernel.ι (aug.app X) := by
    dsimp only [eX, aug]
    rw [← reducedSingularHomologyObjIso_hom_ι]
    simp only [Iso.inv_hom_id_assoc]
  have heY : eY.hom ≫ kernel.ι (aug.app Y) =
      (reducedSingularHomologyι C A n).app Y := by
    dsimp only [eY, aug]
    exact reducedSingularHomologyObjIso_hom_ι C A n Y
  have hredNat : r ≫ (reducedSingularHomologyι C A n).app Y =
      (reducedSingularHomologyι C A n).app X ≫ p := by
    dsimp only [r, p, H]
    exact (reducedSingularHomologyι C A n).naturality f
  have hconj : eX.inv ≫ r ≫ eY.hom = k := by
    apply (cancel_mono (kernel.ι (aug.app Y))).1
    calc
      (eX.inv ≫ r ≫ eY.hom) ≫ kernel.ι (aug.app Y) =
          eX.inv ≫ (r ≫ (eY.hom ≫ kernel.ι (aug.app Y))) := by
        simp only [Category.assoc]
      _ = eX.inv ≫ (r ≫ (reducedSingularHomologyι C A n).app Y) := by
        rw [heY]
      _ = eX.inv ≫ ((reducedSingularHomologyι C A n).app X ≫ p) := by
        rw [hredNat]
      _ = (eX.inv ≫ (reducedSingularHomologyι C A n).app X) ≫ p := by
        rw [Category.assoc]
      _ = kernel.ι (aug.app X) ≫ p := by rw [heX]
      _ = k ≫ kernel.ι (aug.app Y) := by
        dsimp only [k]
        rw [kernel.lift_ι]
  have hr : r = eX.hom ≫ k ≫ eY.inv := by
    apply (cancel_epi eX.inv).1
    apply (cancel_mono eY.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using hconj
  change IsIso r
  rw [hr]
  infer_instance

end TopCat.weakHomotopyEquivalences
