/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Degree-one homology maps from homotopies of zero

A homotopy from zero to zero anticommutes with the differentials and sends
cycles to cycles and boundaries to boundaries. Its components induce
degree-one maps on homology, using the homology objects in the two
relevant degrees.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v w

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K L M : HomologicalComplex C c}
  (H : Homotopy (0 : K ⟶ L) 0) {i j : ι} (hji : c.Rel j i)

include hji in
/-- A component of a zero homotopy takes an actual source cycle to a target cycle. -/
theorem homologyDegreeMap_isCycle {A : C} (k : A ⟶ K.X i)
    (hk : k ≫ K.d i (c.next i) = 0) :
    (k ≫ H.hom i j) ≫ L.d j i = 0 := by
  have hc := H.comm i
  rw [HomologicalComplex.zero_f_apply, add_zero, prevD_eq H.hom hji] at hc
  have h := congrArg (fun a : K.X i ⟶ L.X i => k ≫ a) hc
  have hd : k ≫ dNext i H.hom = 0 := by
    change k ≫ (K.d i (c.next i) ≫ H.hom (c.next i) i) = 0
    rw [← Category.assoc, hk, zero_comp]
  rw [comp_zero, Preadditive.comp_add, hd, zero_add] at h
  simpa only [Category.assoc] using h.symm

variable [K.HasHomology i] [L.HasHomology j]

/-- The cycle map in degree one induced by the homotopy component. -/
def cyclesDegreeMap : K.cycles i ⟶ L.cycles j :=
  L.liftCycles (K.iCycles i ≫ H.hom i j) i (c.next_eq' hji)
    (H.homologyDegreeMap_isCycle hji (K.iCycles i) (K.iCycles_d i (c.next i)))

/-- The cycle map has exactly the original homotopy component after cycle inclusion. -/
@[reassoc (attr := simp)]
theorem cyclesDegreeMap_i :
    H.cyclesDegreeMap hji ≫ L.iCycles j = K.iCycles i ≫ H.hom i j :=
  L.liftCycles_i _ _ _ _

include hji in
omit [K.HasHomology i] [L.HasHomology j] in
private theorem d_comp_component :
    K.d j i ≫ H.hom i j = (-H.hom j (c.prev j)) ≫ L.d (c.prev j) j := by
  have h := H.comm j
  rw [HomologicalComplex.zero_f_apply, add_zero, dNext_eq H.hom hji] at h
  change 0 = K.d j i ≫ H.hom i j + H.hom j (c.prev j) ≫ L.d (c.prev j) j at h
  simpa only [Preadditive.neg_comp] using eq_neg_of_add_eq_zero_left h.symm

/-- A boundary sent through the original homotopy component has zero target homology class. -/
@[reassoc]
theorem toCycles_cyclesDegreeMap_homologyπ_eq_zero :
    K.toCycles j i ≫ H.cyclesDegreeMap hji ≫ L.homologyπ j = 0 := by
  let k : K.X j ⟶ L.X j := K.d j i ≫ H.hom i j
  have hk : k ≫ L.d j i = 0 := by
    dsimp only [k]
    rw [d_comp_component H hji, Category.assoc, L.d_comp_d, comp_zero]
  have hCycles : K.toCycles j i ≫ H.cyclesDegreeMap hji =
      L.liftCycles k i (c.next_eq' hji) hk := by
    apply (cancel_mono (L.iCycles j)).1
    simp only [Category.assoc, cyclesDegreeMap_i, toCycles_i_assoc, liftCycles_i, k]
  rw [← Category.assoc, hCycles]
  exact L.liftCycles_homologyπ_eq_zero_of_boundary k i (c.next_eq' hji)
    (-H.hom j (c.prev j)) (d_comp_component H hji)

private theorem toCycles_cyclesDegreeMap_homologyπ :
    K.toCycles j i ≫ H.cyclesDegreeMap hji ≫ L.homologyπ j = 0 :=
  H.toCycles_cyclesDegreeMap_homologyπ_eq_zero hji

/-- The original component descends to the existing local homology objects. -/
def homologyDegreeMap : K.homology i ⟶ L.homology j :=
  (K.homologyIsCokernel j i (c.prev_eq' hji)).desc
    (CokernelCofork.ofπ (H.cyclesDegreeMap hji ≫ L.homologyπ j)
      (H.toCycles_cyclesDegreeMap_homologyπ_eq_zero hji))

/-- The induced map sends a cycle to the class of its original homotopy component. -/
@[reassoc (attr := simp)]
theorem homologyπ_homologyDegreeMap :
    K.homologyπ i ≫ H.homologyDegreeMap hji =
      H.cyclesDegreeMap hji ≫ L.homologyπ j :=
  Cofork.IsColimit.π_desc (K.homologyIsCokernel j i (c.prev_eq' hji))

/-- An arbitrary cycle representative is sent through the homotopy component. -/
theorem homologyDegreeMap_cycle_representative {A : C} (k : A ⟶ K.X i)
    (hk : k ≫ K.d i (c.next i) = 0) :
    (K.liftCycles k (c.next i) rfl hk ≫ K.homologyπ i) ≫
        H.homologyDegreeMap hji =
      L.liftCycles (k ≫ H.hom i j) i (c.next_eq' hji)
        (H.homologyDegreeMap_isCycle hji k hk) ≫ L.homologyπ j := by
  have hCycles : K.liftCycles k (c.next i) rfl hk ≫ H.cyclesDegreeMap hji =
      L.liftCycles (k ≫ H.hom i j) i (c.next_eq' hji)
        (H.homologyDegreeMap_isCycle hji k hk) := by
    apply (cancel_mono (L.iCycles j)).1
    simp only [Category.assoc, cyclesDegreeMap_i, liftCycles_i_assoc, liftCycles_i]
  rw [Category.assoc, homologyπ_homologyDegreeMap, ← Category.assoc, hCycles]

section Naturality

variable {K' L' : HomologicalComplex C c} [K'.HasHomology i] [L'.HasHomology j]
  (H' : Homotopy (0 : K' ⟶ L') 0) (a : K' ⟶ K) (b : L ⟶ L')
  (hComponent : H'.hom i j = a.f i ≫ H.hom i j ≫ b.f j)

include hComponent in
/-- Compatible original morphisms induce the simultaneous cycle-map square. -/
theorem cyclesDegreeMap_naturality :
    cyclesMap a i ≫ H.cyclesDegreeMap hji ≫ cyclesMap b j =
      H'.cyclesDegreeMap hji := by
  apply (cancel_mono (L'.iCycles j)).1
  simp only [Category.assoc, cyclesMap_i, cyclesDegreeMap_i_assoc,
    cyclesDegreeMap_i, cyclesMap_i_assoc, hComponent]

include hComponent in
/-- The induced degree map is natural in both the source and target complex. -/
theorem homologyDegreeMap_naturality :
    homologyMap a i ≫ H.homologyDegreeMap hji ≫ homologyMap b j =
      H'.homologyDegreeMap hji := by
  apply (cancel_epi (K'.homologyπ i)).1
  calc
    _ = (cyclesMap a i ≫ H.cyclesDegreeMap hji ≫ cyclesMap b j) ≫
        L'.homologyπ j := by
      simp only [Category.assoc, homologyπ_naturality_assoc,
        homologyπ_homologyDegreeMap_assoc,
        homologyπ_naturality]
    _ = H'.cyclesDegreeMap hji ≫ L'.homologyπ j := by
      rw [cyclesDegreeMap_naturality H hji H' a b hComponent]
    _ = K'.homologyπ i ≫ H'.homologyDegreeMap hji :=
      (H'.homologyπ_homologyDegreeMap hji).symm

end Naturality

/-- Raw component square-zero gives square-zero on the homology objects. -/
theorem homologyDegreeMap_comp_eq_zero {k : ι} (hkj : c.Rel k j)
    [M.HasHomology k] (H' : Homotopy (0 : L ⟶ M) 0)
    (hSquare : H.hom i j ≫ H'.hom j k = 0) :
    H.homologyDegreeMap hji ≫ H'.homologyDegreeMap hkj = 0 := by
  have hCycles : H.cyclesDegreeMap hji ≫ H'.cyclesDegreeMap hkj = 0 := by
    apply (cancel_mono (M.iCycles k)).1
    simp only [Category.assoc, cyclesDegreeMap_i, cyclesDegreeMap_i_assoc,
      hSquare, comp_zero, zero_comp]
  apply (cancel_epi (K.homologyπ i)).1
  calc
    _ = (H.cyclesDegreeMap hji ≫ H'.cyclesDegreeMap hkj) ≫ M.homologyπ k := by
      simp only [Category.assoc, homologyπ_homologyDegreeMap_assoc,
        homologyπ_homologyDegreeMap]
    _ = 0 := by rw [hCycles, zero_comp]
    _ = K.homologyπ i ≫ 0 := comp_zero.symm

section Intertwining

variable {K' L' : HomologicalComplex C c} [K'.HasHomology i] [L'.HasHomology j]
  (H' : Homotopy (0 : K' ⟶ L') 0) (a : K ⟶ K') (b : L ⟶ L')
  (hComponent : a.f i ≫ H'.hom i j = H.hom i j ≫ b.f j)

include hComponent in
/-- An actual component-intertwining square descends to the canonical cycle objects. -/
theorem cyclesDegreeMap_naturality_square :
    cyclesMap a i ≫ H'.cyclesDegreeMap hji = H.cyclesDegreeMap hji ≫ cyclesMap b j := by
  apply (cancel_mono (L'.iCycles j)).1
  calc
    _ = K.iCycles i ≫ (a.f i ≫ H'.hom i j) := by
      simp only [Category.assoc, cyclesDegreeMap_i, cyclesMap_i_assoc]
    _ = K.iCycles i ≫ (H.hom i j ≫ b.f j) := congrArg (K.iCycles i ≫ ·) hComponent
    _ = (H.cyclesDegreeMap hji ≫ cyclesMap b j) ≫ L'.iCycles j := by
      simp only [Category.assoc, cyclesMap_i, cyclesDegreeMap_i_assoc]

include hComponent in
/-- The component-intertwining square gives naturality on the homology objects. -/
theorem homologyDegreeMap_naturality_square :
    homologyMap a i ≫ H'.homologyDegreeMap hji =
      H.homologyDegreeMap hji ≫ homologyMap b j := by
  apply (cancel_epi (K.homologyπ i)).1
  calc
    _ = (cyclesMap a i ≫ H'.cyclesDegreeMap hji) ≫ L'.homologyπ j := by
      simp only [Category.assoc, homologyπ_naturality_assoc,
        homologyπ_homologyDegreeMap]
    _ = (H.cyclesDegreeMap hji ≫ cyclesMap b j) ≫ L'.homologyπ j :=
      congrArg (· ≫ L'.homologyπ j)
        (cyclesDegreeMap_naturality_square H hji H' a b hComponent)
    _ = K.homologyπ i ≫ H.homologyDegreeMap hji ≫ homologyMap b j := by
      simp only [Category.assoc, homologyπ_homologyDegreeMap_assoc,
        homologyπ_naturality]

end Intertwining

end Homotopy
