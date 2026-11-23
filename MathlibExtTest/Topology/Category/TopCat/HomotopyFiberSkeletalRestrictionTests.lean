/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.HomotopyFiberSkeletalRestriction

/-!
# Consumers of actual skeletal homotopy-fiber restriction maps

The compact-family client recovers both original coordinates from its factor.
The transition client retains the fixed original point and its actual map
to the full homotopy fiber while deriving weakness from two local comparisons.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

example {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    (A : X.Subcomplex) [SSet.Finite (A : SSet.{u})]
    (a : SSet.toTop.obj (A : SSet.{u})) {K : TopCat.{u}} [CompactSpace K]
    (d₀ : ℕ) (f : K ⟶ TopCat.homotopyFiber p (SSet.toTop.map A.ι a)) :
    ∃ (d : ℕ) (_ : d₀ ≤ d) (hA : A ≤ X.skeleton d)
      (g : K ⟶ TopCat.homotopyFiber
        (pullback.snd p (SSet.toTop.map (X.skeleton d).ι))
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hA) a)),
      g ≫ TopCat.homotopyFiberToTotal
          (pullback.snd p (SSet.toTop.map (X.skeleton d).ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hA) a) ≫
          pullback.fst p (SSet.toTop.map (X.skeleton d).ι) =
        f ≫ TopCat.homotopyFiberToTotal p (SSet.toTop.map A.ι a) ∧
      g ≫ TopCat.homotopyFiberPath
          (pullback.snd p (SSet.toTop.map (X.skeleton d).ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hA) a) ≫
          TopCat.pathObjectMap (SSet.toTop.map (X.skeleton d).ι) =
        f ≫ TopCat.homotopyFiberPath p (SSet.toTop.map A.ι a) := by
  obtain ⟨d, hd, hA, g, hg⟩ := TopCat.exists_skeleton_homotopyFiber_factor p A a d₀ f
  refine ⟨d, hd, hA, g, ?_, ?_⟩
  · rw [← TopCat.subcomplexHomotopyFiberMap_toTotal, ← Category.assoc, hg]
  · rw [← TopCat.subcomplexHomotopyFiberMap_path, ← Category.assoc, hg]

example {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    {A B C : X.Subcomplex} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : SSet.toTop.obj (A : SSet.{u}))
    (hB : TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map B.ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a)))
    (hC : TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map C.ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) a))) :
    TopCat.weakHomotopyEquivalences (TopCat.subcomplexHomotopyFiberTransition p hAB hBC a) ∧
      TopCat.subcomplexHomotopyFiberTransition p hAB hBC a ≫
        TopCat.subcomplexHomotopyFiberMap p (hAB.trans hBC) a =
        TopCat.subcomplexHomotopyFiberMap p hAB a :=
  ⟨TopCat.subcomplexHomotopyFiberTransition_mem_of_comparisons p hAB hBC a hB hC,
    TopCat.subcomplexHomotopyFiberTransition_map p hAB hBC a⟩

example {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    {A B : X.Subcomplex} (hAB : A ≤ B) (a : SSet.toTop.obj (A : SSet.{u})) :
    Mono (TopCat.subcomplexHomotopyFiberMap p hAB a) := inferInstance

example {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    {B C : X.Subcomplex} (hBC : B ≤ C) :
    IsPullback (TopCat.subcomplexRestrictionMap p hBC) (pullback.snd p (SSet.toTop.map B.ι))
      (pullback.snd p (SSet.toTop.map C.ι)) (SSet.toTop.map (SSet.Subcomplex.homOfLE hBC)) :=
  TopCat.subcomplexRestrictionMap_isPullback p hBC

#print axioms TopCat.subcomplexHomotopyFiberMap
#print axioms TopCat.exists_skeleton_homotopyFiber_factor
#print axioms TopCat.subcomplexHomotopyFiberTransition_mem_of_comparisons
