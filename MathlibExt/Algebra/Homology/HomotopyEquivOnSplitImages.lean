/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Actual homotopy equivalences on compatible split images

A full chain homotopy equivalence with an exact right inverse
restricts to two actual split image complexes when its forward map commutes
with their actual image projectors. The inverse is the full inverse
sandwiched between the original inclusion and projection maps. The native
full homotopy is restricted and projected. Neither the full inverse nor the
homotopy is required to commute with the projectors. No desired image
homotopy equivalence, contraction or homology isomorphism is supplied.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι}
  {K L K' L' : HomologicalComplex C c}

/-- The actual restricted forward map of the original compatible image complexes. -/
def splitImageForward (f : K ⟶ L) (iK : K' ⟶ K) (pL : L ⟶ L') : K' ⟶ L' := iK ≫ f ≫ pL

/-- The actual projected original full inverse. -/
def splitImageInverse (g : L ⟶ K) (iL : L' ⟶ L) (pK : K ⟶ K') : L' ⟶ K' := iL ≫ g ≫ pK

/-- The original exact right inverse and the actual projector compatibility give an exact right inverse on images. -/
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

/-- Restricting and projecting the actual native full homotopy gives the actual image homotopy. -/
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

/-- The original split images inherit the proved full homotopy equivalence. -/
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
