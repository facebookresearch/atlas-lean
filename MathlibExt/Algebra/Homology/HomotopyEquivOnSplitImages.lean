/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Chain homotopy equivalences on compatible retracts

Let f : K → L have a right inverse g with g ≫ f = 𝟙 L, and let f ≫ g be chain-homotopic to 𝟙
K. Suppose K' and L' are retracts of K and L with inclusions i_K, i_L and retractions p_K,
p_L. If f commutes with the two retract projectors, (p_K ≫ i_K) ≫ f = f ≫ (p_L ≫ i_L), the
maps i_K ≫ f ≫ p_L and i_L ≫ g ≫ p_K give a chain homotopy equivalence K' ≃ L'.

The inverse-after-forward identity follows from the right-inverse and projector equations. The
other composite is homotopic to the identity by precomposing and postcomposing the homotopy on
K. These constructions hold in a preadditive category for any common complex shape.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι}
  {K L K' L' : HomologicalComplex C c}

/-- In a preadditive category C, let K, L, K' and L' be complexes of a common shape c on an
arbitrary index type. For maps f : K ⟶ L, i_K : K' ⟶ K and p_L : L ⟶ L', define
splitImageForward f i_K p_L : K' ⟶ L' as i_K ≫ f ≫ p_L. -/
def splitImageForward (f : K ⟶ L) (iK : K' ⟶ K) (pL : L ⟶ L') : K' ⟶ L' := iK ≫ f ≫ pL

/-- In a preadditive category C, let K, L, K' and L' be complexes of a common shape c on an
arbitrary index type. For maps g : L ⟶ K, i_L : L' ⟶ L and p_K : K ⟶ K', define
splitImageInverse g i_L p_K : L' ⟶ K' as i_L ≫ g ≫ p_K. -/
def splitImageInverse (g : L ⟶ K) (iL : L' ⟶ L) (pK : K ⟶ K') : L' ⟶ K' := iL ≫ g ≫ pK

/-- In a preadditive category C, let K, L, K' and L' be complexes of a common shape c on an
arbitrary index type. Let f : K ⟶ L and g : L ⟶ K satisfy g ≫ f = 𝟙 L. Let i_K : K' ⟶ K, p_K :
K ⟶ K', i_L : L' ⟶ L and p_L : L ⟶ L' satisfy i_L ≫ p_L = 𝟙 L' and (p_K ≫ i_K) ≫ f = f ≫ (p_L
≫ i_L). Then (i_L ≫ g ≫ p_K) ≫ (i_K ≫ f ≫ p_L) = 𝟙 L'. -/
@[reassoc]
theorem splitImageInverse_forward (f : K ⟶ L) (g : L ⟶ K) (hg : g ≫ f = 𝟙 L)
    (iK : K' ⟶ K) (pK : K ⟶ K') (iL : L' ⟶ L) (pL : L ⟶ L')
    (hL : iL ≫ pL = 𝟙 L') (hprojector : (pK ≫ iK) ≫ f = f ≫ (pL ≫ iL)) :
    splitImageInverse g iL pK ≫ splitImageForward f iK pL = 𝟙 L' := by
  calc
    _ = iL ≫ g ≫ ((pK ≫ iK) ≫ f) ≫ pL := by
      simp only [splitImageInverse, splitImageForward, Category.assoc]
    _ = iL ≫ g ≫ (f ≫ (pL ≫ iL)) ≫ pL := by rw [hprojector]
    _ = iL ≫ (g ≫ f) ≫ pL ≫ (iL ≫ pL) := by simp only [Category.assoc]
    _ = 𝟙 L' := by simp only [hg, hL, Category.id_comp, Category.comp_id]

/-- In a preadditive category C, let K, L, K' and L' be complexes of a common shape c on an
arbitrary index type. Let f : K ⟶ L and g : L ⟶ K have a homotopy f ≫ g ∼ 𝟙 K. For maps i_K,
p_K, i_L, p_L with i_K ≫ p_K = 𝟙 K' and (p_K ≫ i_K) ≫ f = f ≫ (p_L ≫ i_L), there is a homotopy
(i_K ≫ f ≫ p_L) ≫ (i_L ≫ g ≫ p_K) ∼ 𝟙 K'. It is obtained by composing the ambient homotopy
with i_K and p_K. -/
def splitImageHomotopy (f : K ⟶ L) (g : L ⟶ K) (h : Homotopy (f ≫ g) (𝟙 K))
    (iK : K' ⟶ K) (pK : K ⟶ K') (hK : iK ≫ pK = 𝟙 K')
    (iL : L' ⟶ L) (pL : L ⟶ L') (hprojector : (pK ≫ iK) ≫ f = f ≫ (pL ≫ iL)) :
    Homotopy (splitImageForward f iK pL ≫ splitImageInverse g iL pK) (𝟙 K') := by
  have hmap : (iK ≫ (f ≫ g)) ≫ pK = splitImageForward f iK pL ≫ splitImageInverse g iL pK := by
    symm
    calc
      _ = iK ≫ (f ≫ (pL ≫ iL)) ≫ g ≫ pK := by
        simp only [splitImageForward, splitImageInverse, Category.assoc]
      _ = iK ≫ ((pK ≫ iK) ≫ f) ≫ g ≫ pK := by rw [hprojector]
      _ = ((iK ≫ pK) ≫ iK) ≫ f ≫ g ≫ pK := by simp only [Category.assoc]
      _ = (iK ≫ (f ≫ g)) ≫ pK := by
        rw [hK, Category.id_comp]
        simp only [Category.assoc]
  have hid : (iK ≫ 𝟙 K) ≫ pK = 𝟙 K' := by
    rw [Category.comp_id]
    exact hK
  exact (Homotopy.ofEq hmap.symm).trans
    (((h.compLeft iK).compRight pK).trans (Homotopy.ofEq hid))

/-- In a preadditive category C, let K, L, K' and L' be complexes of a common shape c on an
arbitrary index type. Let f : K ⟶ L and g : L ⟶ K satisfy g ≫ f = 𝟙 L and f ≫ g ∼ 𝟙 K. Suppose
i_K : K' ⟶ K, p_K : K ⟶ K', i_L : L' ⟶ L and p_L : L ⟶ L' satisfy i_K ≫ p_K = 𝟙 K', i_L ≫ p_L
= 𝟙 L' and (p_K ≫ i_K) ≫ f = f ≫ (p_L ≫ i_L). They define a HomotopyEquiv K' L' with forward
map i_K ≫ f ≫ p_L and inverse i_L ≫ g ≫ p_K. -/
def homotopyEquivOnSplitImages (f : K ⟶ L) (g : L ⟶ K) (hg : g ≫ f = 𝟙 L)
    (h : Homotopy (f ≫ g) (𝟙 K))
    (iK : K' ⟶ K) (pK : K ⟶ K') (hK : iK ≫ pK = 𝟙 K')
    (iL : L' ⟶ L) (pL : L ⟶ L') (hL : iL ≫ pL = 𝟙 L')
    (hprojector : (pK ≫ iK) ≫ f = f ≫ (pL ≫ iL)) : HomotopyEquiv K' L' where
  hom := splitImageForward f iK pL
  inv := splitImageInverse g iL pK
  homotopyHomInvId := splitImageHomotopy f g h iK pK hK iL pL hprojector
  homotopyInvHomId := Homotopy.ofEq (splitImageInverse_forward f g hg iK pK iL pL hL hprojector)

end HomologicalComplex
