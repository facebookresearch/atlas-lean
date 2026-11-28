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
# Degree maps from a self-homotopy of zero

A self-homotopy H of the zero map between module complexes has components
in the reversed differential degrees. On a reverse edge i→j it maps cycles
in degree i to cycles in degree j, and the induced homology map is
represented by that same component on concrete elements.
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

/--
Let k be a ring and K,L module complexes of shape c. Let H be a homotopy from the zero
morphism K→L to itself. Fix i,j with c.Rel j i, and assume K has homology at i and L at j. For
a cycle x∈Kᵢ, H.hom i j(x)∈Lⱼ is also a cycle: d_L at j annihilates it.
-/
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

/--
Let k be a ring and K,L module complexes of shape c. Let H be a homotopy from the zero
morphism K→L to itself. Fix i,j with c.Rel j i, and assume K has homology at i and L at j. The
degree map Zᵢ(K)→Zⱼ(L) induced by H sends the cycle of x to the cycle of H.hom i j(x). Thus it
retains the concrete component value.
-/
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

/--
Let k be a ring and K,L module complexes of shape c. Let H be a homotopy from the zero
morphism K→L to itself. Fix i,j with c.Rel j i, and assume K has homology at i and L at j. The
induced degree map Hᵢ(K)→Hⱼ(L) sends a concrete cycle class [x] to [H.hom i j(x)].
-/
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
