/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentTranslation
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Adjunction.Limits
import MathlibExt.CategoryTheory.CategoryHomology.ClassifyingSpaceSingular
import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization

/-!
# Realized component translations with the literal identity zero branch

Every original Grothendieck class is retained. The forward and inverse maps
are realizations of the computed restricted translation functors. At zero
both maps are identity, and both homotopies are chosen to be constant. This
supplies the actual two point-relative families when the component spaces
are joined into the entire disjoint union.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject Algebra
open scoped Simplicial Topology

universe u v

public section

namespace CategoryTheory.SInverseS.ComponentTranslation

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The ordinary realization of the whole specified original class category. -/
abbrev componentSpace (g : GrothendieckAddGroup (Skeleton C)) :=
  SSet.toTop.obj (CategoryTheory.nerve (Component g))

/-- The ordinary realization of the literal categorical zero component. -/
abbrev zeroSpace :=
  SSet.toTop.obj (CategoryTheory.nerve (ZeroComponent (C := C)))

/-- The actual realized forward restricted translation on every class. -/
def componentForward (g : GrothendieckAddGroup (Skeleton C)) :
    C((componentSpace (C := C)) g, zeroSpace (C := C)) :=
  (SSet.toTop.map (CategoryTheory.nerveMap (toZero g))).hom

/-- The actual realized inverse restricted translation on every class. -/
def componentInverse (g : GrothendieckAddGroup (Skeleton C)) :
    C(zeroSpace (C := C), (componentSpace (C := C)) g) :=
  (SSet.toTop.map (CategoryTheory.nerveMap (fromZero g))).hom

/-- The selected zero-component map is literally identity. -/
theorem componentForward_zero :
    componentForward (C := C) 0 = ContinuousMap.id (zeroSpace (C := C)) := by
  simp only [componentForward, toZero_zero, nerveMap_id, Functor.map_id, TopCat.hom_id]

/-- The selected zero-component inverse is the same identity map. -/
theorem componentInverse_zero :
    componentInverse (C := C) 0 = ContinuousMap.id (zeroSpace (C := C)) := by
  simp only [componentInverse, fromZero_zero, nerveMap_id, Functor.map_id, TopCat.hom_id]

private def rawComponentLeftHomotopy (g : GrothendieckAddGroup (Skeleton C)) :
    ContinuousMap.Homotopy (((componentInverse (C := C)) g).comp ((componentForward (C := C)) g))
      (ContinuousMap.id ((componentSpace (C := C)) g)) := by
  have h := SSet.realizeHomotopy
    (CategoryTheory.nerve (Component g)) (CategoryTheory.nerve (Component g))
    (𝟙 _) (CategoryTheory.nerveMap (toZero g) ≫ CategoryTheory.nerveMap (fromZero g))
    (forwardInverseNerveHomotopy g)
  simpa only [componentForward, componentInverse, Functor.map_comp, Functor.map_id,
    TopCat.hom_comp, TopCat.hom_id] using h.symm

private def rawComponentRightHomotopy (g : GrothendieckAddGroup (Skeleton C)) :
    ContinuousMap.Homotopy (((componentForward (C := C)) g).comp ((componentInverse (C := C)) g))
      (ContinuousMap.id (zeroSpace (C := C))) := by
  have h := SSet.realizeHomotopy
    (CategoryTheory.nerve (ZeroComponent (C := C)))
    (CategoryTheory.nerve (ZeroComponent (C := C)))
    (𝟙 _) (CategoryTheory.nerveMap (fromZero g) ≫ CategoryTheory.nerveMap (toZero g))
    (inverseForwardNerveHomotopy g)
  simpa only [componentForward, componentInverse, Functor.map_comp, Functor.map_id,
    TopCat.hom_comp, TopCat.hom_id] using h.symm

/-- The first actual inverse family; its zero branch is a constant homotopy. -/
def componentLeftHomotopy (g : GrothendieckAddGroup (Skeleton C)) :
    ContinuousMap.Homotopy (((componentInverse (C := C)) g).comp ((componentForward (C := C)) g))
      (ContinuousMap.id ((componentSpace (C := C)) g)) := by
  classical
  by_cases h : g = 0
  · subst g
    exact (ContinuousMap.Homotopy.refl (ContinuousMap.id (zeroSpace (C := C)))).cast
      (by rw [(componentForward_zero (C := C)), (componentInverse_zero (C := C))]; rfl) rfl
  · exact (rawComponentLeftHomotopy (C := C)) g

/-- The other actual inverse family, with the same constant zero branch. -/
def componentRightHomotopy (g : GrothendieckAddGroup (Skeleton C)) :
    ContinuousMap.Homotopy (((componentForward (C := C)) g).comp ((componentInverse (C := C)) g))
      (ContinuousMap.id (zeroSpace (C := C))) := by
  classical
  by_cases h : g = 0
  · subst g
    exact (ContinuousMap.Homotopy.refl (ContinuousMap.id (zeroSpace (C := C)))).cast
      (by rw [(componentForward_zero (C := C)), (componentInverse_zero (C := C))]; rfl) rfl
  · exact (rawComponentRightHomotopy (C := C)) g

/-- Every point of the zero branch stays stationary for every time in the first family. -/
theorem componentLeftHomotopy_zero_apply (t : unitInterval) (z : zeroSpace (C := C)) :
    componentLeftHomotopy (C := C) 0 (t, z) = z := by
  classical
  simp only [componentLeftHomotopy]
  rfl

/-- Every point of the zero branch stays stationary in the other family as well. -/
theorem componentRightHomotopy_zero_apply (t : unitInterval) (z : zeroSpace (C := C)) :
    componentRightHomotopy (C := C) 0 (t, z) = z := by
  classical
  simp only [componentRightHomotopy]
  rfl

/-- The full classwise homotopy equivalence uses exactly the computed translation maps. -/
def componentHomotopyEquiv (g : GrothendieckAddGroup (Skeleton C)) :
    ContinuousMap.HomotopyEquiv ((componentSpace (C := C)) g) (zeroSpace (C := C)) where
  toFun := (componentForward (C := C)) g
  invFun := (componentInverse (C := C)) g
  left_inv := ⟨(componentLeftHomotopy (C := C)) g⟩
  right_inv := ⟨(componentRightHomotopy (C := C)) g⟩

private def sigmaMap {I : Type u} {X Y : I → Type (max u v)}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) : C((Σ i, X i), (Σ i, Y i)) :=
  ContinuousMap.sigma (fun i => (ContinuousMap.sigmaMk i).comp (f i))

private def sigmaHomotopy {I : Type u} {X Y : I → Type (max u v)}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    {f g : ∀ i, C(X i, Y i)} (h : ∀ i, ContinuousMap.Homotopy (f i) (g i)) :
    ContinuousMap.Homotopy (sigmaMap f) (sigmaMap g) where
  toContinuousMap := by
    let F : C((Σ i, X i × unitInterval), (Σ i, Y i)) :=
      ContinuousMap.sigma (fun i => (ContinuousMap.sigmaMk i).comp
        ((h i).toContinuousMap.comp
          ⟨Homeomorph.prodComm (X i) unitInterval,
            (Homeomorph.prodComm (X i) unitInterval).continuous⟩))
    let e : unitInterval × (Σ i, X i) ≃ₜ (Σ i, X i × unitInterval) :=
      (Homeomorph.prodComm unitInterval (Σ i, X i)).trans
        (Homeomorph.sigmaProdDistrib (X := X) (Y := unitInterval))
    exact F.comp ⟨e, e.continuous⟩
  map_zero_left := by
    rintro ⟨i, x⟩
    change Sigma.mk i (h i (0, x)) = Sigma.mk i (f i x)
    exact congrArg (Sigma.mk i) ((h i).map_zero_left x)
  map_one_left := by
    rintro ⟨i, x⟩
    change Sigma.mk i (h i (1, x)) = Sigma.mk i (g i x)
    exact congrArg (Sigma.mk i) ((h i).map_one_left x)

/-- The disjoint union contains every original component, including the distinguished zero pair. -/
abbrev totalComponentSpace := Σ g : GrothendieckAddGroup (Skeleton C), (componentSpace (C := C)) g

/-- The complete constant family of zero-component spaces, indexed by the entire group. -/
abbrev totalZeroSpace := Σ _ : GrothendieckAddGroup (Skeleton C), zeroSpace (C := C)

/-- The entire forward map retains each original class label. -/
def totalComponentForward : C(totalComponentSpace (C := C), totalZeroSpace (C := C)) :=
  sigmaMap (fun g => (componentForward (C := C)) g)

/-- The entire inverse map uses the actual inverse in each original class. -/
def totalComponentInverse : C(totalZeroSpace (C := C), totalComponentSpace (C := C)) :=
  sigmaMap (fun g => (componentInverse (C := C)) g)

/-- The first full inverse homotopy is the actual joined family of component homotopies. -/
def totalComponentLeftHomotopy :
    ContinuousMap.Homotopy ((totalComponentInverse (C := C)).comp (totalComponentForward (C := C)))
      (ContinuousMap.id (totalComponentSpace (C := C))) :=
  sigmaHomotopy (fun g => (componentLeftHomotopy (C := C)) g)

/-- The other full inverse homotopy retains every class as well. -/
def totalComponentRightHomotopy :
    ContinuousMap.Homotopy ((totalComponentForward (C := C)).comp (totalComponentInverse (C := C)))
      (ContinuousMap.id (totalZeroSpace (C := C))) :=
  sigmaHomotopy (fun g => (componentRightHomotopy (C := C)) g)

/-- The actual distinguished zero vertex in the ordinary categorical zero component. -/
def zeroSpacePoint : zeroSpace (C := C) :=
  SSet.realizedVertex (X := CategoryTheory.nerve (ZeroComponent (C := C)))
    (ComposableArrows.mk₀ (zeroComponentBaseObject (C := C)))

private theorem zeroSpacePoint_computation : zeroSpacePoint (C := C) =
    SSet.realizedVertex (X := CategoryTheory.nerve (ZeroComponent (C := C)))
      (ComposableArrows.mk₀ (zeroComponentBaseObject (C := C))) := rfl

/-- The original zero point is its actual realized categorical vertex. -/
theorem zeroSpacePoint_eq_realizedVertex : zeroSpacePoint (C := C) =
    SSet.realizedVertex (X := CategoryTheory.nerve (ZeroComponent (C := C)))
      (ComposableArrows.mk₀ (zeroComponentBaseObject (C := C))) := zeroSpacePoint_computation

/-- The original unit in the full disjoint union of classes. -/
def totalComponentPoint : totalComponentSpace (C := C) := ⟨0, (zeroSpacePoint (C := C))⟩

/-- The original (0,unit) point in the complete constant family. -/
def totalZeroPoint : totalZeroSpace (C := C) := ⟨0, (zeroSpacePoint (C := C))⟩

/-- The complete forward map retains the specified original unit exactly. -/
theorem totalComponentForward_point :
    (totalComponentForward (C := C)) (totalComponentPoint (C := C)) =
        (totalZeroPoint (C := C)) := by
  change (⟨0, componentForward (C := C) 0 (zeroSpacePoint (C := C))⟩ :
      totalZeroSpace (C := C)) = (⟨0, zeroSpacePoint (C := C)⟩ : totalZeroSpace (C := C))
  rw [(componentForward_zero (C := C))]
  rfl

/-- The complete inverse map returns that same original unit. -/
theorem totalComponentInverse_point :
    (totalComponentInverse (C := C)) (totalZeroPoint (C := C)) =
        (totalComponentPoint (C := C)) := by
  change (⟨0, componentInverse (C := C) 0 (zeroSpacePoint (C := C))⟩ :
      totalComponentSpace (C := C)) =
    (⟨0, zeroSpacePoint (C := C)⟩ : totalComponentSpace (C := C))
  rw [(componentInverse_zero (C := C))]
  rfl

/-- The first global inverse family is stationary at the original unit for every time. -/
def totalComponentLeftHomotopyRel :
    ContinuousMap.HomotopyRel ((totalComponentInverse (C := C)).comp
        (totalComponentForward (C := C)))
      (ContinuousMap.id (totalComponentSpace (C := C))) {(totalComponentPoint (C := C))} where
  toHomotopy := (totalComponentLeftHomotopy (C := C))
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change (⟨0, componentLeftHomotopy (C := C) 0 (t, zeroSpacePoint (C := C))⟩ :
        totalComponentSpace (C := C)) =
      (totalComponentInverse (C := C)) ((totalComponentForward (C := C))
          (totalComponentPoint (C := C)))
    rw [(componentLeftHomotopy_zero_apply (C := C)), (totalComponentForward_point (C := C)),
      (totalComponentInverse_point (C := C))]
    rfl

/-- The other global inverse family is stationary at (0,unit) for every time. -/
def totalComponentRightHomotopyRel :
    ContinuousMap.HomotopyRel ((totalComponentForward (C := C)).comp
        (totalComponentInverse (C := C)))
      (ContinuousMap.id (totalZeroSpace (C := C))) {(totalZeroPoint (C := C))} where
  toHomotopy := (totalComponentRightHomotopy (C := C))
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change (⟨0, componentRightHomotopy (C := C) 0 (t, zeroSpacePoint (C := C))⟩ :
        totalZeroSpace (C := C)) =
      (totalComponentForward (C := C)) ((totalComponentInverse (C := C)) (totalZeroPoint (C := C)))
    rw [(componentRightHomotopy_zero_apply (C := C)), (totalComponentInverse_point (C := C)),
      (totalComponentForward_point (C := C))]
    rfl

/-- The entire disjoint union is equivalent to the full constant zero-component family. -/
def totalComponentHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (totalComponentSpace (C := C)) (totalZeroSpace (C := C)) where
  toFun := (totalComponentForward (C := C))
  invFun := (totalComponentInverse (C := C))
  left_inv := ⟨(totalComponentLeftHomotopyRel (C := C)).toHomotopy⟩
  right_inv := ⟨(totalComponentRightHomotopyRel (C := C)).toHomotopy⟩

private def sigmaConstHomeomorph (G Z : Type*) [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace Z] : (Σ _ : G, Z) ≃ₜ G × Z where
  toEquiv := Equiv.sigmaEquivProd G Z
  continuous_toFun := continuous_sigma (fun _ => continuous_const.prodMk continuous_id)
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hN : ({p.1} : Set G) ∈ 𝓝 p.1 :=
      (isOpen_discrete _).mem_nhds (Set.mem_singleton p.1)
    have hFirst : ∀ᶠ t : G × Z in 𝓝 p, t.1 = p.1 :=
      (continuous_fst.continuousAt.tendsto.eventually hN).mono
        (fun t ht => Set.mem_singleton_iff.mp ht)
    let j : C(Z, (Σ _ : G, Z)) :=
      ContinuousMap.sigmaMk (X := fun _ : G => Z) p.1
    have h : ContinuousAt (fun t : G × Z => (⟨p.1, t.2⟩ : Σ _ : G, Z)) p :=
      (j.continuous.comp (continuous_snd : Continuous (fun t : G × Z => t.2))).continuousAt
    apply h.congr_of_eventuallyEq
    filter_upwards [hFirst] with t ht
    cases t with
    | mk g z =>
      dsimp at ht
      subst g
      rfl

/-- Original Grothendieck class labels carry their specified discrete topology. -/
local instance grothendieckTopology :
    TopologicalSpace (GrothendieckAddGroup (Skeleton C)) := ⊥

local instance grothendieckTopology_discrete :
    DiscreteTopology (GrothendieckAddGroup (Skeleton C)) := ⟨rfl⟩

/-- The entire original Grothendieck group with its specified discrete topology. -/
abbrev grothendieckDiscreteSpace : TopCat.{u} :=
  TopCat.of (GrothendieckAddGroup (Skeleton C))

/-- The computed group-space topology is discrete; consumers need no unfolding of its recipe. -/
theorem grothendieckDiscreteSpace_discrete :
    DiscreteTopology (grothendieckDiscreteSpace (C := C)) :=
  grothendieckTopology_discrete

/-- The full discrete-group product with the literal original zero component. -/
abbrev componentProductSpace : TopCat.{max u v} :=
  TopCat.of (GrothendieckAddGroup (Skeleton C) × zeroSpace (C := C))

/-- The full constant zero-component family is the actual discrete-group product. -/
def totalZeroProductHomeomorph : totalZeroSpace (C := C) ≃ₜ componentProductSpace (C := C) :=
  sigmaConstHomeomorph (GrothendieckAddGroup (Skeleton C)) (zeroSpace (C := C))

/-- The original (0,unit) product point. -/
def componentProductPoint : componentProductSpace (C := C) := ⟨0, (zeroSpacePoint (C := C))⟩

private theorem totalZeroProductHomeomorph_point_computation :
    totalZeroProductHomeomorph (C := C) (totalZeroPoint (C := C)) =
      componentProductPoint (C := C) := rfl

private theorem totalZeroProductHomeomorph_symm_point_computation :
    (totalZeroProductHomeomorph (C := C)).symm (componentProductPoint (C := C)) =
      totalZeroPoint (C := C) := rfl

/-- The product comparison retains the original (0,unit) point exactly. -/
theorem totalZeroProductHomeomorph_point :
    (totalZeroProductHomeomorph (C := C)) (totalZeroPoint (C := C)) =
      (componentProductPoint (C := C)) := totalZeroProductHomeomorph_point_computation

/-- The inverse product comparison returns the same zero-component unit. -/
theorem totalZeroProductHomeomorph_symm_point :
    (totalZeroProductHomeomorph (C := C)).symm (componentProductPoint (C := C)) =
      (totalZeroPoint (C := C)) := totalZeroProductHomeomorph_symm_point_computation

private theorem componentProductPoint_pair_computation : componentProductPoint (C := C) =
    ((0 : GrothendieckAddGroup (Skeleton C)), zeroSpacePoint (C := C)) := rfl

/-- The original product unit retains its literal zero label and zero-space point. -/
theorem componentProductPoint_eq_zeroPair : componentProductPoint (C := C) =
    ((0 : GrothendieckAddGroup (Skeleton C)), zeroSpacePoint (C := C)) :=
  componentProductPoint_pair_computation

/-- The entire forward map uses the original translation in every component. -/
def componentProductForward :
    C(totalComponentSpace (C := C), componentProductSpace (C := C)) :=
  (⟨totalZeroProductHomeomorph (C := C),
    (totalZeroProductHomeomorph (C := C)).continuous⟩ :
      C(totalZeroSpace (C := C),
          componentProductSpace (C := C))).comp (totalComponentForward (C := C))

/-- The entire inverse retains every original group class and its computed translation. -/
def componentProductInverse :
    C(componentProductSpace (C := C), totalComponentSpace (C := C)) :=
  (totalComponentInverse (C := C)).comp
    (⟨(totalZeroProductHomeomorph (C := C)).symm,
      (totalZeroProductHomeomorph (C := C)).symm.continuous⟩ :
        C(componentProductSpace (C := C), totalZeroSpace (C := C)))

/-- The whole forward map preserves the original specified unit. -/
theorem componentProductForward_point :
    (componentProductForward (C := C)) (totalComponentPoint (C := C)) =
        (componentProductPoint (C := C)) := by
  change (totalZeroProductHomeomorph (C := C))
      ((totalComponentForward (C := C)) (totalComponentPoint (C := C))) = _
  rw [(totalComponentForward_point (C := C)), (totalZeroProductHomeomorph_point (C := C))]

/-- The whole inverse preserves the same specified unit. -/
theorem componentProductInverse_point :
    (componentProductInverse (C := C)) (componentProductPoint (C := C)) =
        (totalComponentPoint (C := C)) := by
  change (totalComponentInverse (C := C))
      ((totalZeroProductHomeomorph (C := C)).symm (componentProductPoint (C := C))) = _
  rw [(totalZeroProductHomeomorph_symm_point (C := C)), (totalComponentInverse_point (C := C))]

private theorem componentProductLeftMap_eq :
    (totalComponentInverse (C := C)).comp (totalComponentForward (C := C)) =
      (componentProductInverse (C := C)).comp (componentProductForward (C := C)) := by
  apply ContinuousMap.ext
  intro x
  change (totalComponentInverse (C := C)) ((totalComponentForward (C := C)) x) =
    (totalComponentInverse (C := C))
      ((totalZeroProductHomeomorph (C := C)).symm
          ((totalZeroProductHomeomorph (C := C)) ((totalComponentForward (C := C)) x)))
  rw [Homeomorph.symm_apply_apply]

/-- The actual first whole inverse family remains relative to the original unit. -/
def componentProductLeftHomotopyRel :
    ContinuousMap.HomotopyRel ((componentProductInverse (C := C)).comp
        (componentProductForward (C := C)))
      (ContinuousMap.id (totalComponentSpace (C := C))) {(totalComponentPoint (C := C))} :=
  (totalComponentLeftHomotopyRel (C := C)).cast (componentProductLeftMap_eq (C := C)) rfl

private def componentProductRightHomotopy :
    ContinuousMap.Homotopy ((componentProductForward (C := C)).comp
        (componentProductInverse (C := C)))
      (ContinuousMap.id (componentProductSpace (C := C))) := by
  let e := totalZeroProductHomeomorph (C := C)
  let f : C(totalZeroSpace (C := C), componentProductSpace (C := C)) := ⟨e, e.continuous⟩
  let g : C(componentProductSpace (C := C), totalZeroSpace (C := C)) :=
    ⟨e.symm, e.symm.continuous⟩
  let h := (ContinuousMap.Homotopy.refl f).comp
    ((totalComponentRightHomotopy (C := C)).compContinuousMap g)
  refine h.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    rfl
  · apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply x

/-- The other actual whole inverse family is relative to the original (0,unit) product point. -/
def componentProductRightHomotopyRel :
    ContinuousMap.HomotopyRel ((componentProductForward (C := C)).comp
        (componentProductInverse (C := C)))
      (ContinuousMap.id (componentProductSpace (C := C))) {(componentProductPoint (C := C))} where
  toHomotopy := (componentProductRightHomotopy (C := C))
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change (totalZeroProductHomeomorph (C := C))
      ((totalComponentRightHomotopy (C := C)) (t,
          (totalZeroProductHomeomorph (C := C)).symm (componentProductPoint (C := C)))) =
        (componentProductForward (C := C))
            ((componentProductInverse (C := C)) (componentProductPoint (C := C)))
    rw [(totalZeroProductHomeomorph_symm_point (C := C)), (componentProductInverse_point (C := C)),
      (componentProductForward_point (C := C))]
    change (totalZeroProductHomeomorph (C := C))
      (⟨0, componentRightHomotopy (C := C) 0 (t, zeroSpacePoint (C := C))⟩ :
        totalZeroSpace (C := C)) = (componentProductPoint (C := C))
    rw [(componentRightHomotopy_zero_apply (C := C))]
    exact totalZeroProductHomeomorph_point (C := C)

/-- The entire class family has the full based discrete-group product, with both actual families. -/
def componentProductHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (totalComponentSpace (C := C))
        (componentProductSpace (C := C)) where
  toFun := (componentProductForward (C := C))
  invFun := (componentProductInverse (C := C))
  left_inv := ⟨(componentProductLeftHomotopyRel (C := C)).toHomotopy⟩
  right_inv := ⟨(componentProductRightHomotopyRel (C := C)).toHomotopy⟩

private def wholeClassNerveIso :
    CategoryTheory.nerve (ComponentTotal (C := C)) ≅ CategoryTheory.nerve (Pair C) where
  hom := CategoryTheory.nerveMap (componentDecompositionIsoCat (C := C)).functor
  inv := CategoryTheory.nerveMap (componentDecompositionIsoCat (C := C)).inverse
  hom_inv_id := by
    rw [nerveMap_comp, ← (componentDecompositionIsoCat (C := C)).unit_eq, nerveMap_id]
  inv_hom_id := by
    rw [nerveMap_comp, (componentDecompositionIsoCat (C := C)).counit_eq, nerveMap_id]

/-- The entire original nerve cofan uses exactly its original class inclusions. -/
def originalClassNerveCofan : Cofan (fun g => CategoryTheory.nerve (Component (C := C) g)) :=
  Cofan.mk (CategoryTheory.nerve (Pair C))
    (fun g => CategoryTheory.nerveMap (componentProperty g).ι)

private theorem originalClassNerveCofan_eq_mk_computed :
    originalClassNerveCofan (C := C) =
      Cofan.mk (CategoryTheory.nerve (Pair C))
        (fun g : GrothendieckAddGroup (Skeleton C) =>
          CategoryTheory.nerveMap (componentProperty (C := C) g).ι) := rfl

/-- The canonical class cofan has exactly the original pair nerve and original
class-inclusion legs. This equality does not expose its implementation. -/
public theorem originalClassNerveCofan_eq_mk :
    originalClassNerveCofan (C := C) =
      Cofan.mk (CategoryTheory.nerve (Pair C))
        (fun g : GrothendieckAddGroup (Skeleton C) =>
          CategoryTheory.nerveMap (componentProperty (C := C) g).ι) :=
  originalClassNerveCofan_eq_mk_computed (C := C)

/-- The stock decomposition and its canonical class dictionary prove this actual cofan is
colimiting. -/
def originalClassNerveCofanIsColimit : IsColimit (originalClassNerveCofan (C := C)) := by
  let f := fun g : GrothendieckAddGroup (Skeleton C) => CategoryTheory.nerve (Component g)
  let c : Cofan f := Cofan.mk (∐ f) (Limits.Sigma.ι f)
  have hc : IsColimit c := coproductIsCoproduct f
  let e : (∐ f) ≅ CategoryTheory.nerve (Pair C) :=
    (NerveDecomposition.nerveSigmaIso (C := fun g => Component (C := C) g)).trans
      (wholeClassNerveIso (C := C))
  apply hc.ofIsoColimit
  refine Cocone.ext e ?_
  rintro ⟨g⟩
  change Limits.Sigma.ι f g ≫
      ((NerveDecomposition.nerveSigmaIso (C := fun g => Component (C := C) g)).hom ≫
        (wholeClassNerveIso (C := C)).hom) =
    CategoryTheory.nerveMap (componentProperty g).ι
  rw [← Category.assoc, NerveDecomposition.nerveSigmaIso_ι]
  change CategoryTheory.nerveMap (CategoryTheory.Sigma.incl g) ≫
      CategoryTheory.nerveMap (componentDecompositionIsoCat (C := C)).functor =
    CategoryTheory.nerveMap (componentProperty g).ι
  rw [nerveMap_comp, componentDecompositionIsoCat_incl]

/-- The original geometric realization of the whole stabilized-pair category. -/
abbrev originalSpace := SSet.toTop.obj (CategoryTheory.nerve (Pair C))

/-- The realization cofan retains every entire original class inclusion. -/
def originalClassRealizationCofan : Cofan (fun g => componentSpace (C := C) g) :=
  Cofan.mk (originalSpace (C := C))
    (fun g => SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι))

/-- Actual geometric realization preserves the above cofan by its existing left adjunction. -/
def originalClassRealizationCofanIsColimit :
    IsColimit (originalClassRealizationCofan (C := C)) := by
  have h : IsColimit (Cofan.mk (CategoryTheory.nerve (Pair C))
      (fun g : GrothendieckAddGroup (Skeleton C) =>
        CategoryTheory.nerveMap (componentProperty g).ι)) :=
    originalClassNerveCofanIsColimit (C := C)
  exact isColimitCofanMkObjOfIsColimit
    (SSet.toTop : SSet.{max u v} ⥤ TopCat.{max u v})
    (fun g => CategoryTheory.nerve (Component (C := C) g))
    (fun g => CategoryTheory.nerveMap (componentProperty g).ι) h

/-- The whole class realization family is homeomorphic to the original whole space. -/
def originalClassRealizationIso : TopCat.of (totalComponentSpace (C := C)) ≅
    (originalSpace (C := C)) :=
  (TopCat.sigmaCofanIsColimit.{u, v} (fun g => componentSpace (C := C) g)).coconePointUniqueUpToIso
    (originalClassRealizationCofanIsColimit (C := C))

/-- On each entire class, this is exactly the actual realized original inclusion. -/
theorem originalClassRealizationIso_ι (g : GrothendieckAddGroup (Skeleton C)) :
    TopCat.sigmaι (fun g => componentSpace (C := C) g) g ≫
        (originalClassRealizationIso (C := C)).hom =
      SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (TopCat.sigmaCofanIsColimit.{u, v} (fun g => componentSpace (C := C) g))
    (originalClassRealizationCofanIsColimit (C := C)) ⟨g⟩

/-- The literal original pair (0,0), realized in the original whole space. -/
def originalSpacePoint : originalSpace (C := C) :=
  SSet.realizedVertex (X := CategoryTheory.nerve (Pair C))
    (ComposableArrows.mk₀ (⟨0, 0⟩ : Pair C))

private theorem originalSpacePoint_computation : originalSpacePoint (C := C) =
    SSet.realizedVertex (X := CategoryTheory.nerve (Pair C))
      (ComposableArrows.mk₀ (⟨0, 0⟩ : Pair C)) := rfl

/-- The original ambient point is the actual realized pair (0,0). -/
theorem originalSpacePoint_eq_realizedVertex : originalSpacePoint (C := C) =
    SSet.realizedVertex (X := CategoryTheory.nerve (Pair C))
      (ComposableArrows.mk₀ (⟨0, 0⟩ : Pair C)) := originalSpacePoint_computation

private theorem zeroInclusion_obj_base :
    (componentProperty (C := C) 0).ι.obj (zeroComponentBaseObject (C := C)) =
      (⟨0, 0⟩ : Pair C) := rfl

/-- The actual whole-space comparison preserves the original unit, without a replacement path. -/
theorem originalClassRealizationIso_point :
    (originalClassRealizationIso (C := C)).hom (totalComponentPoint (C := C)) =
        (originalSpacePoint (C := C)) := by
  have h := ConcreteCategory.congr_hom (originalClassRealizationIso_ι (C := C) 0)
      (zeroSpacePoint (C := C))
  change (originalClassRealizationIso (C := C)).hom (totalComponentPoint (C := C)) =
    SSet.toTop.map (CategoryTheory.nerveMap (componentProperty (C := C) 0).ι)
        (zeroSpacePoint (C := C)) at h
  refine h.trans ?_
  let v := ComposableArrows.mk₀ (zeroComponentBaseObject (C := C))
  let f := CategoryTheory.nerveMap (componentProperty (C := C) 0).ι
  have hVertex : f.app (Opposite.op ⦋0⦌) v = ComposableArrows.mk₀ (⟨0, 0⟩ : Pair C) :=
    (nerveMap_app_mk₀ (componentProperty (C := C) 0).ι
      (zeroComponentBaseObject (C := C))).trans
        (congrArg ComposableArrows.mk₀ (zeroInclusion_obj_base (C := C)))
  exact (SSet.realizedVertex_naturality f v).symm.trans
    (congrArg (SSet.realizedVertex (X := CategoryTheory.nerve (Pair C))) hVertex)

/-- The inverse whole-space comparison returns the same actual unit. -/
theorem originalClassRealizationIso_inv_point :
    (originalClassRealizationIso (C := C)).inv (originalSpacePoint (C := C)) =
        (totalComponentPoint (C := C)) := by
  have h := congrArg (originalClassRealizationIso (C := C)).inv
    (originalClassRealizationIso_point (C := C))
  exact h.symm.trans (ConcreteCategory.congr_hom
      (originalClassRealizationIso (C := C)).hom_inv_id _)

private theorem originalClassRealizationIso_inv_hom_apply
    (x : totalComponentSpace (C := C)) :
    (originalClassRealizationIso (C := C)).inv
      ((originalClassRealizationIso (C := C)).hom x) = x := by
  have h := ConcreteCategory.congr_hom (originalClassRealizationIso (C := C)).hom_inv_id x
  change (originalClassRealizationIso (C := C)).inv
    ((originalClassRealizationIso (C := C)).hom x) = x at h
  exact h

/-- The full original space maps to the full discrete-group product by the actual component
translations. -/
def originalProductForward : C(originalSpace (C := C), componentProductSpace (C := C)) :=
  (componentProductForward (C := C)).comp (originalClassRealizationIso (C := C)).inv.hom

/-- The full product returns through the same inverse translations and original inclusions. -/
def originalProductInverse : C(componentProductSpace (C := C), originalSpace (C := C)) :=
  (originalClassRealizationIso (C := C)).hom.hom.comp (componentProductInverse (C := C))

/-- The original forward map retains the specified pair (0,0) exactly. -/
theorem originalProductForward_point :
    (originalProductForward (C := C)) (originalSpacePoint (C := C)) =
        (componentProductPoint (C := C)) := by
  change (componentProductForward (C := C))
      ((originalClassRealizationIso (C := C)).inv (originalSpacePoint (C := C))) = _
  rw [(originalClassRealizationIso_inv_point (C := C)), (componentProductForward_point (C := C))]

/-- The original inverse map returns the same (0,0) pair exactly. -/
theorem originalProductInverse_point :
    (originalProductInverse (C := C)) (componentProductPoint (C := C)) =
        (originalSpacePoint (C := C)) := by
  change (originalClassRealizationIso (C := C)).hom
      ((componentProductInverse (C := C)) (componentProductPoint (C := C))) = _
  rw [(componentProductInverse_point (C := C)), (originalClassRealizationIso_point (C := C))]

private def originalProductLeftHomotopy :
    ContinuousMap.Homotopy ((originalProductInverse (C := C)).comp
        (originalProductForward (C := C)))
      (ContinuousMap.id (originalSpace (C := C))) := by
  let e := TopCat.homeoOfIso (originalClassRealizationIso (C := C))
  let f : C(totalComponentSpace (C := C), originalSpace (C := C)) := ⟨e, e.continuous⟩
  let g : C(originalSpace (C := C), totalComponentSpace (C := C)) :=
    ⟨e.symm, e.symm.continuous⟩
  let h := (ContinuousMap.Homotopy.refl f).comp
    ((componentProductLeftHomotopyRel (C := C)).toHomotopy.compContinuousMap g)
  refine h.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    rfl
  · apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply x

/-- The first full inverse family is relative to the literal original (0,0) pair. -/
def originalProductLeftHomotopyRel :
    ContinuousMap.HomotopyRel ((originalProductInverse (C := C)).comp
        (originalProductForward (C := C)))
      (ContinuousMap.id (originalSpace (C := C))) {(originalSpacePoint (C := C))} where
  toHomotopy := (originalProductLeftHomotopy (C := C))
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change (originalClassRealizationIso (C := C)).hom
      ((componentProductLeftHomotopyRel (C := C))
        (t, (originalClassRealizationIso (C := C)).inv (originalSpacePoint (C := C)))) =
          (originalProductInverse (C := C))
              ((originalProductForward (C := C)) (originalSpacePoint (C := C)))
    rw [(originalClassRealizationIso_inv_point (C := C)), (originalProductForward_point (C := C)),
      (originalProductInverse_point (C := C))]
    have hFixed : (componentProductLeftHomotopyRel (C := C))
        (t, totalComponentPoint (C := C)) = totalComponentPoint (C := C) :=
      (componentProductLeftHomotopyRel (C := C)).eq_snd t
        (Set.mem_singleton (totalComponentPoint (C := C)))
    rw [hFixed]
    exact (originalClassRealizationIso_point (C := C))

private theorem originalProductRightMap_eq :
    (componentProductForward (C := C)).comp (componentProductInverse (C := C)) =
      (originalProductForward (C := C)).comp (originalProductInverse (C := C)) := by
  apply ContinuousMap.ext
  intro x
  change (componentProductForward (C := C)) ((componentProductInverse (C := C)) x) =
    (componentProductForward (C := C))
      ((originalClassRealizationIso (C := C)).inv
          ((originalClassRealizationIso (C := C)).hom ((componentProductInverse (C := C)) x)))
  exact (congrArg (componentProductForward (C := C))
    (originalClassRealizationIso_inv_hom_apply (C := C)
      (componentProductInverse (C := C) x))).symm

/-- The other full inverse family is relative to the original (0,(0,0)) product point. -/
def originalProductRightHomotopyRel :
    ContinuousMap.HomotopyRel ((originalProductForward (C := C)).comp
        (originalProductInverse (C := C)))
      (ContinuousMap.id (componentProductSpace (C := C))) {(componentProductPoint (C := C))} :=
  (componentProductRightHomotopyRel (C := C)).cast (originalProductRightMap_eq (C := C)) rfl

/-- The entire original stabilized-pair space has the full based discrete-group product. -/
def originalProductHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (originalSpace (C := C)) (componentProductSpace (C := C)) where
  toFun := (originalProductForward (C := C))
  invFun := (originalProductInverse (C := C))
  left_inv := ⟨(originalProductLeftHomotopyRel (C := C)).toHomotopy⟩
  right_inv := ⟨(originalProductRightHomotopyRel (C := C)).toHomotopy⟩

/-- Every original class realization is path-connected by the existing generic nerve theorem. -/
theorem componentSpace_pathConnected (g : GrothendieckAddGroup (Skeleton C)) :
    PathConnectedSpace ((componentSpace (C := C)) g) := by
  let : IsConnected (Component g) := component_isConnected g
  let : (CategoryTheory.nerve (Component g)).IsConnected :=
    CategoryTheory.nerve_isConnected_of_category_isConnected
  exact SSet.pathConnectedSpace_realization_of_isConnected
    (CategoryTheory.nerve (Component g))

/-- Each original component inclusion is an actual embedding of its realization. -/
theorem originalClassInclusion_isEmbedding (g : GrothendieckAddGroup (Skeleton C)) :
    Topology.IsEmbedding
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) :
        (componentSpace (C := C)) g → originalSpace (C := C)) := by
  let e := TopCat.homeoOfIso (originalClassRealizationIso (C := C))
  have h : Topology.IsEmbedding (fun z : (componentSpace (C := C)) g => e (Sigma.mk g z)) :=
    e.isEmbedding.comp Topology.IsEmbedding.sigmaMk
  have hMap : (fun z : (componentSpace (C := C)) g => e (Sigma.mk g z)) =
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) :
        componentSpace (C := C) g → originalSpace (C := C)) :=
    funext (fun z => ConcreteCategory.congr_hom (originalClassRealizationIso_ι (C := C) g) z)
  exact hMap ▸ h

/-- The actual categorical zero-component inclusion has exactly the original path-component
range. -/
theorem originalZeroClass_range_eq_pathComponent :
    Set.range (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty (C := C) 0).ι) :
      zeroSpace (C := C) → originalSpace (C := C)) =
          pathComponent (originalSpacePoint (C := C)) := by
  let F : C(zeroSpace (C := C), originalSpace (C := C)) :=
    (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty (C := C) 0).ι)).hom
  let e := TopCat.homeoOfIso (originalClassRealizationIso (C := C))
  have hPoint : F (zeroSpacePoint (C := C)) = (originalSpacePoint (C := C)) := by
    have h := ConcreteCategory.congr_hom (originalClassRealizationIso_ι (C := C) 0)
        (zeroSpacePoint (C := C))
    exact h.symm.trans (originalClassRealizationIso_point (C := C))
  apply Set.Subset.antisymm
  · let : PathConnectedSpace (zeroSpace (C := C)) := (componentSpace_pathConnected (C := C)) 0
    have hRange : IsPathConnected (Set.range F) := isPathConnected_range F.continuous
    exact hRange.subset_pathComponent ⟨(zeroSpacePoint (C := C)), hPoint⟩
  · intro y hy
    have hJoined : Joined (totalComponentPoint (C := C)) (e.symm y) := by
      have hBase : e.symm (originalSpacePoint (C := C)) = totalComponentPoint (C := C) := by
        change (originalClassRealizationIso (C := C)).inv (originalSpacePoint (C := C)) = _
        exact originalClassRealizationIso_inv_point (C := C)
      have h := (mem_pathComponent_iff.mp hy).map e.symm.continuous
      exact hBase ▸ h
    let label : C(totalComponentSpace (C := C), grothendieckDiscreteSpace (C := C)) :=
      ContinuousMap.sigma (fun g => ContinuousMap.const ((componentSpace (C := C)) g) g)
    have hLabel : Joined (0 : GrothendieckAddGroup (Skeleton C)) (e.symm y).1 :=
      hJoined.map label.continuous
    have hTag : (e.symm y).1 = 0 := by
      have hMem := pathComponent_subset_component (0 : GrothendieckAddGroup (Skeleton C))
        (mem_pathComponent_iff.mpr hLabel)
      simpa only [connectedComponent_eq_singleton, Set.mem_singleton_iff] using hMem
    cases hv : e.symm y with
    | mk g z =>
      have hg : g = 0 := by simpa only [hv] using hTag
      subst g
      refine ⟨z, ?_⟩
      have hV := congrArg e hv
      have hF := ConcreteCategory.congr_hom (originalClassRealizationIso_ι (C := C) 0) z
      exact hF.symm.trans (hV.symm.trans (e.apply_symm_apply y))

/-- The literal original zero space is homeomorphic to the actual path component of (0,0). -/
def zeroPathComponentHomeomorph :
    zeroSpace (C := C) ≃ₜ pathComponent (originalSpacePoint (C := C)) :=
  (originalClassInclusion_isEmbedding (C := C) 0).toHomeomorph.trans
    (Homeomorph.setCongr (originalZeroClass_range_eq_pathComponent (C := C)))

private theorem zeroPathComponentHomeomorph_apply_computation (z : zeroSpace (C := C)) :
    (zeroPathComponentHomeomorph (C := C) z : originalSpace (C := C)) =
      SSet.toTop.map (CategoryTheory.nerveMap (componentProperty (C := C) 0).ι) z := rfl

/-- The zero-path-component homeomorphism is the actual original inclusion on underlying points. -/
theorem zeroPathComponentHomeomorph_apply (z : zeroSpace (C := C)) :
    ((zeroPathComponentHomeomorph (C := C)) z : originalSpace (C := C)) =
      SSet.toTop.map (CategoryTheory.nerveMap (componentProperty (C := C) 0).ι) z :=
  zeroPathComponentHomeomorph_apply_computation z

/-- Its specified basepoint is the literal original (0,0) point. -/
theorem zeroPathComponentHomeomorph_point :
    (zeroPathComponentHomeomorph (C := C)) (zeroSpacePoint (C := C)) =
      ⟨(originalSpacePoint (C := C)), mem_pathComponent_self (originalSpacePoint (C := C))⟩ := by
  apply Subtype.ext
  rw [(zeroPathComponentHomeomorph_apply (C := C))]
  have h := ConcreteCategory.congr_hom (originalClassRealizationIso_ι (C := C) 0)
      (zeroSpacePoint (C := C))
  exact h.symm.trans (originalClassRealizationIso_point (C := C))

/-- Every original group label is retained on the whole realization of its actual class. -/
theorem originalProductForward_class (g : GrothendieckAddGroup (Skeleton C))
    (z : (componentSpace (C := C)) g) :
    (originalProductForward (C := C))
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) z) =
        (g, (componentForward (C := C)) g z) := by
  have h := ConcreteCategory.congr_hom (originalClassRealizationIso_ι (C := C) g) z
  rw [← h]
  change (componentProductForward (C := C))
    ((originalClassRealizationIso (C := C)).inv
        ((originalClassRealizationIso (C := C)).hom (Sigma.mk g z))) = _
  rw [originalClassRealizationIso_inv_hom_apply]
  rfl

/-- The whole inverse returns the actual original class inclusion of the computed inverse
translation. -/
theorem originalProductInverse_class (g : GrothendieckAddGroup (Skeleton C))
    (z : zeroSpace (C := C)) :
    (originalProductInverse (C := C)) (g, z) =
      SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι)
          ((componentInverse (C := C)) g z) :=
  ConcreteCategory.congr_hom (originalClassRealizationIso_ι (C := C) g)
      ((componentInverse (C := C)) g z)

end CategoryTheory.SInverseS.ComponentTranslation
