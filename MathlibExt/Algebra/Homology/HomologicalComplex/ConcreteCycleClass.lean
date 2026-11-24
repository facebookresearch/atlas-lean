/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import MathlibExt.Algebra.Homology.ZeroDifferentialHomology

/-!
# Classes of module cycles in homology

An element with zero differential defines a cycle and hence a homology
class through the canonical homology projection. The element formulas are
natural in chain maps and compatible with the coordinates for complexes
whose differentials vanish.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {k : Type u} [Ring k] {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} k) c}

/-- The native homology class of an actual original cycle element. -/
def moduleCatCycleClass (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι)
    [K.HasHomology i] (x : K.X i) (hx : (K.sc i).g x = 0) : K.homology i :=
  (K.sc i).homologyπ ((K.sc i).cyclesMk x hx)

/-- The native cycles constructor retains its actual module middle element. -/
theorem moduleCat_iCycles_cyclesMk (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι)
    [K.HasHomology i] (x : K.X i) (hx : (K.sc i).g x = 0) :
    (K.sc i).iCycles.hom ((K.sc i).cyclesMk x hx) = x := by
  exact ShortComplex.i_cyclesMk (K.sc i) x hx

/-- Native cycles are determined by their actual original middle element. -/
theorem moduleCat_cyclesMk_liftCycles (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι)
    [K.HasHomology i] {N : ModuleCat.{v} k} (f : N ⟶ K.X i)
    (hf : f ≫ (K.sc i).g = 0) (x : N) :
    (K.sc i).cyclesMk (f x) (ConcreteCategory.congr_hom hf x) =
      (K.sc i).liftCycles f hf x := by
  apply (ModuleCat.mono_iff_injective (K.sc i).iCycles).mp inferInstance
  rw [moduleCat_iCycles_cyclesMk]
  exact (ConcreteCategory.congr_hom (ShortComplex.liftCycles_i (K.sc i) f hf) x).symm

/-- The concrete class is the literal canonical lifted-cycle projection. -/
theorem moduleCatCycleClass_liftCycles (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι)
    [K.HasHomology i] {N : ModuleCat.{v} k} (f : N ⟶ K.X i)
    (hf : f ≫ (K.sc i).g = 0) (x : N) :
    moduleCatCycleClass K i (f x) (ConcreteCategory.congr_hom hf x) =
      ((K.sc i).liftCycles f hf ≫ (K.sc i).homologyπ) x := by
  rw [moduleCatCycleClass, moduleCat_cyclesMk_liftCycles]
  rfl

/-- Every actual chain map transports the native cycle class of its literal original element. -/
theorem moduleCatCycleClass_naturality (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] (x : K.X i) (hx : (K.sc i).g x = 0) :
    homologyMap f i (moduleCatCycleClass K i x hx) =
      moduleCatCycleClass L i (f.f i x) (by
        have h := ConcreteCategory.congr_hom (f.comm i (c.next i)) x
        change (L.sc i).g (f.f i x) = f.f (c.next i) ((K.sc i).g x) at h
        rw [hx] at h
        exact h.trans (f.f (c.next i)).hom.map_zero) := by
  let g := (shortComplexFunctor (ModuleCat.{v} k) c i).map f
  have hc : ShortComplex.cyclesMap g ((K.sc i).cyclesMk x hx) =
      (L.sc i).cyclesMk (f.f i x) (by
        have h := ConcreteCategory.congr_hom g.comm₂₃ x
        change (L.sc i).g (f.f i x) = f.f (c.next i) ((K.sc i).g x) at h
        rw [hx] at h
        exact h.trans (f.f (c.next i)).hom.map_zero) := by
    apply (ModuleCat.mono_iff_injective (L.sc i).iCycles).mp inferInstance
    rw [moduleCat_iCycles_cyclesMk]
    have h := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i g) ((K.sc i).cyclesMk x hx)
    change (L.sc i).iCycles.hom (ShortComplex.cyclesMap g ((K.sc i).cyclesMk x hx)) =
      (f.f i).hom ((K.sc i).iCycles.hom ((K.sc i).cyclesMk x hx)) at h
    rw [moduleCat_iCycles_cyclesMk] at h
    exact h
  have h := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality g)
    ((K.sc i).cyclesMk x hx)
  change (homologyMap f i).hom
      ((K.sc i).homologyπ.hom ((K.sc i).cyclesMk x hx)) =
    (L.sc i).homologyπ.hom (ShortComplex.cyclesMap g ((K.sc i).cyclesMk x hx)) at h
  rw [hc] at h
  exact h

/-- The existing original zero-differential class is the actual native class of its original element. -/
theorem zeroDifferentialClassMap_eq_moduleCatCycleClass
    (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι) [K.HasHomology i]
    (h : ∀ j l, K.d j l = 0) (x : K.X i) :
    zeroDifferentialClassMap K i h x =
      moduleCatCycleClass K i x (by
        change (K.d i (c.next i)).hom x = 0
        rw [h, ModuleCat.hom_zero, LinearMap.zero_apply]) := by
  have hf : (𝟙 (K.sc i).X₂) ≫ (K.sc i).g = 0 := by
    rw [Category.id_comp]
    exact h _ _
  have hc := moduleCat_cyclesMk_liftCycles K i (𝟙 (K.sc i).X₂) hf x
  change (K.sc i).cyclesMk x _ = (K.sc i).liftCycles (𝟙 (K.sc i).X₂) hf x at hc
  change (K.sc i).homologyπ.hom ((K.sc i).liftCycles (𝟙 (K.sc i).X₂) hf x) =
    (K.sc i).homologyπ.hom ((K.sc i).cyclesMk x _)
  exact congrArg (K.sc i).homologyπ.hom hc.symm

/-- The actual native class of the zero cycle is zero. -/
theorem moduleCatCycleClass_zero (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι)
    [K.HasHomology i] (h : (K.sc i).g (0 : K.X i) = 0) :
    moduleCatCycleClass K i 0 h = 0 := by
  let y : (K.sc i).cycles := (K.sc i).cyclesMk (0 : K.X i) h
  have hy : y = 0 := by
    apply (ModuleCat.mono_iff_injective (K.sc i).iCycles).mp inferInstance
    have hp := moduleCat_iCycles_cyclesMk K i (0 : K.X i) h
    exact hp.trans ((K.sc i).iCycles.hom.map_zero).symm
  change (K.sc i).homologyπ.hom y = 0
  exact (congrArg (K.sc i).homologyπ.hom hy).trans (K.sc i).homologyπ.hom.map_zero

/-- Scalar multiplication of an original cycle gives scalar multiplication of its actual native class. -/
theorem moduleCatCycleClass_smul (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι)
    [K.HasHomology i] (r : k) (x : K.X i) (hx : (K.sc i).g x = 0) :
    moduleCatCycleClass K i (r • x)
        (((K.sc i).g.hom.map_smul r x).trans (by rw [hx, smul_zero])) =
      r • moduleCatCycleClass K i x hx := by
  let y : (K.sc i).cycles := (K.sc i).cyclesMk x hx
  let z : (K.sc i).cycles := (K.sc i).cyclesMk (r • x)
    (((K.sc i).g.hom.map_smul r x).trans (by rw [hx, smul_zero]))
  have hz : z = r • y := by
    apply (ModuleCat.mono_iff_injective (K.sc i).iCycles).mp inferInstance
    have hp := moduleCat_iCycles_cyclesMk K i (r • x)
      (((K.sc i).g.hom.map_smul r x).trans (by rw [hx, smul_zero]))
    have hy := moduleCat_iCycles_cyclesMk K i x hx
    exact hp.trans (((K.sc i).iCycles.hom.map_smul r y).trans (congrArg (r • ·) hy)).symm
  change (K.sc i).homologyπ.hom z = r • (K.sc i).homologyπ.hom y
  exact (congrArg (K.sc i).homologyπ.hom hz).trans ((K.sc i).homologyπ.hom.map_smul r y)

end HomologicalComplex
