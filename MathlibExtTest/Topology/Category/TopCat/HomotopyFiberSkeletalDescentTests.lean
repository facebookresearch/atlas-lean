/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.HomotopyFiberSkeletalDescent

/-!
# Consumers of canonical skeletal quasifibration descent

The first client uses the literal `n + 1` bound for the topological
`n`-skeleton and concludes weakness of the original constant-path comparison.
The second checks the derived actual stage-to-global map and total coordinate.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

example {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    (hstage : ∀ (n : ℕ) (b : SSet.toTop.obj (X.skeleton (n + 1) : SSet.{u})),
      TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
        (pullback.snd p (SSet.toTop.map (X.skeleton (n + 1)).ι)) b))
    (b : SSet.toTop.obj X) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber p b) ∧
      TopCat.strictFiberToHomotopyFiber p b ≫ TopCat.homotopyFiberToTotal p b =
        pullback.fst p (TopCat.const (X := TopCat.of PUnit) b) :=
  ⟨TopCat.strictFiberToHomotopyFiber_mem_of_skeletons p hstage b,
    TopCat.strictFiberToHomotopyFiber_toTotal p b⟩

example {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    (A : X.Subcomplex) [SSet.Finite (A : SSet.{u})] (a : SSet.toTop.obj (A : SSet.{u}))
    {d₀ : ℕ} (hA₀ : A ≤ X.skeleton d₀)
    (hstage : ∀ n : ℕ, TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map (X.skeleton (d₀ + n)).ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE
        (hA₀.trans (X.skeleton.monotone (Nat.le_add_right d₀ n)))) a))) :
    TopCat.weakHomotopyEquivalences (TopCat.subcomplexHomotopyFiberMap p hA₀ a) ∧
      TopCat.subcomplexHomotopyFiberMap p hA₀ a ≫
        TopCat.homotopyFiberToTotal p (SSet.toTop.map A.ι a) =
      TopCat.homotopyFiberToTotal (pullback.snd p (SSet.toTop.map (X.skeleton d₀).ι))
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hA₀) a) ≫
        pullback.fst p (SSet.toTop.map (X.skeleton d₀).ι) :=
  ⟨TopCat.subcomplexHomotopyFiberMap_mem_of_skeletalRestrictions p A a hA₀ hstage,
    TopCat.subcomplexHomotopyFiberMap_toTotal p hA₀ a⟩

#print axioms TopCat.subcomplexHomotopyFiberMap_mem_of_skeletalRestrictions
#print axioms TopCat.strictFiberToHomotopyFiber_mem_of_skeletalRestrictions
#print axioms TopCat.strictFiberToHomotopyFiber_mem_of_skeletons
