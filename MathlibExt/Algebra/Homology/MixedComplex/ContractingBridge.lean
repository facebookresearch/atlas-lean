/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.MixedComplex.OfBoundaryHomotopy

/-!
# Mixed complexes from contracted chain-map bridges

A contraction of an intermediate complex gives a homotopy from zero
to zero by composition with two chain maps. Their composites satisfy
the square-zero condition, so the boundary-homotopy construction
defines the corresponding mixed complex.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive HomologicalComplex

universe u v

namespace MixedComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {L K : ChainComplex C ℕ}
  (u : K ⟶ L) (v : L ⟶ K) (H : Homotopy (𝟙 K) 0)

/-- The original contracted degree-one component. -/
def contractingBridgeB (n : ℕ) : L.X n ⟶ L.X (n + 1) :=
  v.f n ≫ H.hom n (n + 1) ≫ u.f (n + 1)

/-- Native composition and the zero chain-map composite give a zero homotopy. -/
def contractingBridgeHomotopy (hvu : v ≫ u = 0) : Homotopy (0 : L ⟶ L) 0 :=
  (Homotopy.ofEq (by simpa only [Category.comp_id] using hvu.symm)).trans
    (((H.compLeft v).compRight u).trans (Homotopy.ofEq
      (by rw [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp])))

/-- The native composed homotopy retains exactly the original contracted degree-one map. -/
@[simp]
theorem contractingBridgeHomotopy_hom (hvu : v ≫ u = 0) (n : ℕ) :
    (contractingBridgeHomotopy u v H hvu).hom n (n + 1) = contractingBridgeB u v H n := by
  simp only [contractingBridgeHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compRight_hom, Homotopy.compLeft_hom, Pi.add_apply,
    Pi.zero_apply, zero_add, add_zero, contractingBridgeB, Category.assoc]

/-- The other actual zero composite earns the square of the contracted component. -/
theorem contractingBridgeB_sq (huv : u ≫ v = 0) (n : ℕ) :
    contractingBridgeB u v H n ≫ contractingBridgeB u v H (n + 1) = 0 := by
  have hz : u.f (n + 1) ≫ v.f (n + 1) = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply] using
      congrArg (fun f => f.f (n + 1)) huv
  calc
    contractingBridgeB u v H n ≫ contractingBridgeB u v H (n + 1) =
        v.f n ≫ H.hom n (n + 1) ≫ (u.f (n + 1) ≫ v.f (n + 1)) ≫
          H.hom (n + 1) (n + 2) ≫ u.f (n + 2) := by
      simp only [contractingBridgeB, Category.assoc]
    _ = 0 := by rw [hz]; simp only [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

/-- The existing boundary-homotopy API constructs the mixed complex on the original chain complex. -/
def ofContractingBridge (huv : u ≫ v = 0) (hvu : v ≫ u = 0) : MixedComplex C :=
  ofBoundaryHomotopy L (contractingBridgeHomotopy u v H hvu) (fun n => by
    rw [contractingBridgeHomotopy_hom, contractingBridgeHomotopy_hom]
    exact contractingBridgeB_sq u v H huv n)

@[simp]
theorem ofContractingBridge_underlying (huv : u ≫ v = 0) (hvu : v ≫ u = 0) :
    (ofContractingBridge u v H huv hvu).underlying = L := rfl

/-- The native construction retains the exact original contracted degree-one operator. -/
@[simp]
theorem ofContractingBridge_B (huv : u ≫ v = 0) (hvu : v ≫ u = 0) (n : ℕ) :
    (ofContractingBridge u v H huv hvu).B n =
      v.f n ≫ H.hom n (n + 1) ≫ u.f (n + 1) := by
  dsimp only [ofContractingBridge]
  rw [ofBoundaryHomotopy_B, contractingBridgeHomotopy_hom]
  rfl

end MixedComplex
