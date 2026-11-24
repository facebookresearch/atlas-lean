/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.ConcreteCycleClass
public import MathlibExt.Algebra.Homology.Homotopy.HomologyDegree

/-!
# Homology classes and homotopy-degree maps

The cycle map and homology projection characterize the degreewise homology
map associated to a homotopy. This module gives the corresponding formulas
for module elements using the chosen cycles and homology objects.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace Homotopy

variable {k : Type u} [Ring k] {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} k) c}
  (H : Homotopy (0 : K ⟶ L) 0) {i j : ι} (hji : c.Rel j i)
  [K.HasHomology i] [L.HasHomology j]

/-- The original homotopy component takes the original concrete cycle to a genuine target cycle. -/
theorem moduleCat_component_cycle (x : K.X i) (hx : (K.sc i).g x = 0) :
    (L.sc j).g (H.hom i j x) = 0 := by
  by_cases hji : c.Rel j i
  · let z : (K.sc i).cycles := (K.sc i).cyclesMk x hx
    have hz : (K.sc i).iCycles z = x := ShortComplex.i_cyclesMk (K.sc i) x hx
    have h : H.hom i j x = L.iCycles j (H.cyclesDegreeMap hji z) := by
      have hi := ConcreteCategory.congr_hom (H.cyclesDegreeMap_i hji) z
      change L.iCycles j (H.cyclesDegreeMap hji z) = H.hom i j ((K.sc i).iCycles z) at hi
      exact (hi.trans (congrArg (H.hom i j).hom hz)).symm
    rw [h]
    have hzcycle := ConcreteCategory.congr_hom (L.iCycles_d j (c.next j))
      (H.cyclesDegreeMap hji z)
    change (L.sc j).g (L.iCycles j (H.cyclesDegreeMap hji z)) = 0 at hzcycle
    exact hzcycle
  · change (L.sc j).g.hom ((H.hom i j).hom x) = 0
    rw [H.zero i j hji, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact (L.sc j).g.hom.map_zero

/-- The original native degree cycle map gives the native constructor of the same actual component. -/
theorem cyclesDegreeMap_moduleCat_cyclesMk (x : K.X i) (hx : (K.sc i).g x = 0) :
    H.cyclesDegreeMap hji ((K.sc i).cyclesMk x hx) =
      (L.sc j).cyclesMk (H.hom i j x) (H.moduleCat_component_cycle x hx) := by
  apply (ModuleCat.mono_iff_injective (L.sc j).iCycles).mp inferInstance
  have h := ConcreteCategory.congr_hom (H.cyclesDegreeMap_i hji) ((K.sc i).cyclesMk x hx)
  change (L.sc j).iCycles.hom (H.cyclesDegreeMap hji ((K.sc i).cyclesMk x hx)) =
    (H.hom i j).hom ((K.sc i).iCycles.hom ((K.sc i).cyclesMk x hx)) at h
  have hK := HomologicalComplex.moduleCat_iCycles_cyclesMk K i x hx
  have hL := HomologicalComplex.moduleCat_iCycles_cyclesMk L j (H.hom i j x)
    (H.moduleCat_component_cycle x hx)
  exact (h.trans (congrArg (H.hom i j).hom hK)).trans hL.symm

/-- The actual degree homology map sends the literal original cycle class through its original component. -/
theorem homologyDegreeMap_moduleCatCycleClass (x : K.X i) (hx : (K.sc i).g x = 0) :
    H.homologyDegreeMap hji (HomologicalComplex.moduleCatCycleClass K i x hx) =
      HomologicalComplex.moduleCatCycleClass L j (H.hom i j x)
        (H.moduleCat_component_cycle x hx) := by
  have h := ConcreteCategory.congr_hom (H.homologyπ_homologyDegreeMap hji) ((K.sc i).cyclesMk x hx)
  change H.homologyDegreeMap hji ((K.sc i).homologyπ ((K.sc i).cyclesMk x hx)) =
    (L.sc j).homologyπ (H.cyclesDegreeMap hji ((K.sc i).cyclesMk x hx)) at h
  rw [H.cyclesDegreeMap_moduleCat_cyclesMk hji x hx] at h
  exact h

end Homotopy
