/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopy

@[expose] public section

/-!
# Realized horn Homotopy client test

Downstream clients for the universe-polymorphic retraction, zero/one/fixed
endpoint laws, and packaged `SSet.realizedHornHomotopy`, with no new proof.
No HomotopyEquiv, weak-equivalence, fibration, filling, product, colimit, or
model-category claim.
-/

set_option autoImplicit false

noncomputable section

universe u

open scoped Simplicial unitInterval

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornHomotopyTests

noncomputable def realizedHornHomotopy_client (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (((SSet.toTop.map (SSet.horn n k).ι).hom).comp
        (SSet.realizedHornRetract n k hn)) :=
  SSet.realizedHornHomotopy n k hn

theorem retract_ι_symbolic
    (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (x : SSet.toTop.{u}.obj (SSet.horn.{u} n k)) :
    SSet.realizedHornRetract n k hn
      (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι x) = x :=
  SSet.realizedHornRetract_ι n k hn x

theorem homotopy_zero_symbolic
    (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (x : SSet.toTop.{u}.obj (Δ[n] : SSet.{u})) :
    SSet.realizedHornHomotopyMap n k hn (0, x) = x :=
  SSet.realizedHornHomotopyMap_zero n k hn x

theorem homotopy_one_symbolic
    (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (x : SSet.toTop.{u}.obj (Δ[n] : SSet.{u})) :
    SSet.realizedHornHomotopyMap n k hn (1, x) =
      SSet.toTop.{u}.map (SSet.horn.{u} n k).ι
        (SSet.realizedHornRetract n k hn x) :=
  SSet.realizedHornHomotopyMap_one n k hn x

theorem homotopy_fix_symbolic
    (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (y : SSet.toTop.{u}.obj (SSet.horn.{u} n k))
    (t : unitInterval) :
    SSet.realizedHornHomotopyMap n k hn
        (t, SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y) =
      SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y :=
  SSet.realizedHornHomotopyMap_fix n k hn y t

noncomputable def packagedHomotopy_symbolic
    (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (((SSet.toTop.{u}.map (SSet.horn.{u} n k).ι).hom).comp
        (SSet.realizedHornRetract n k hn)) :=
  SSet.realizedHornHomotopy n k hn

noncomputable def packagedHomotopy_one_zero_u1 :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (((SSet.toTop.{1}.map
        (SSet.horn.{1} 1 (⟨0, by decide⟩ : Fin (1 + 1))).ι).hom).comp
        (SSet.realizedHornRetract 1
          (⟨0, by decide⟩ : Fin (1 + 1)) (by decide))) :=
  SSet.realizedHornHomotopy 1 _ (by decide)

#print axioms SSet.realizedHornHomotopy
#print axioms realizedHornHomotopy_client

#print axioms SSet.realizedHornRetract_ι
#print axioms SSet.realizedHornHomotopyMap_fix

end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornHomotopyTests
