/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ShortComplex.CyclesImage
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Cycles and homology sequences for every complex shape

The data and natural maps exist for arbitrary index pairs. The next
and prev witnesses identify the outgoing kernel and incoming boundaries
for exactness. The proof layer forwards through canonical short-complex data;
no separate natural-index or integer-index proof is used.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}

/-- The differential square as an arrow functor, for arbitrary index pairs. -/
def cyclesImageArrowFunctor (i j : ι) : HomologicalComplex C c ⥤ Arrow C :=
  shortComplexFunctor' C c (c.prev i) i j ⋙ ShortComplex.gFunctor

/-- The cycles inclusion as its natural transformation. -/
def cyclesInclusionNatTrans (i : ι) : cyclesFunctor C c i ⟶ eval C c i where
  app K := K.iCycles i
  naturality K L φ := cyclesMap_i φ i

/-- Cycles and the outgoing image, with no shape witness needed for the data. -/
def cyclesImageSequence (K : HomologicalComplex C c) (i j : ι) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (Abelian.factorThruImage (K.d i j)) (by
    have h : (K.iCycles i ≫ Abelian.factorThruImage (K.d i j)) ≫
        Abelian.image.ι (K.d i j) = 0 := by
      rw [Category.assoc, Abelian.image.fac]
      exact K.iCycles_d i j
    exact zero_of_comp_mono _ h)

/-- The concrete-degree comparison identifies this data with the generic sequence. -/
def cyclesImageSequenceIso (K : HomologicalComplex C c) (i j : ι)
    (hj : c.next i = j) :
    cyclesImageSequence K i j ≅ ShortComplex.cyclesImageSES (K.sc' (c.prev i) i j) := by
  let e := K.cyclesIsoSc' (c.prev i) i j rfl hj
  refine ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) ?_ ?_
  · change e.hom ≫ (K.sc' (c.prev i) i j).iCycles = K.iCycles i ≫ 𝟙 _
    exact (K.cyclesIsoSc'_hom_iCycles (c.prev i) i j rfl hj).trans
      (Category.comp_id _).symm
  · change (𝟙 (K.X i)) ≫ Abelian.factorThruImage (K.d i j) =
      Abelian.factorThruImage (K.d i j) ≫ 𝟙 _
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Exactness forwards through the cycles/kernel comparison. -/
theorem cyclesImageSequence_shortExact (K : HomologicalComplex C c) (i j : ι)
    (hj : c.next i = j) : (cyclesImageSequence K i j).ShortExact :=
  ShortComplex.shortExact_of_iso (cyclesImageSequenceIso K i j hj).symm
    (ShortComplex.cyclesImageSES_shortExact (K.sc' (c.prev i) i j))

/-- The generic short-exact universal property gives the kernel certificate. -/
def cyclesImageSequenceIsKernel (K : HomologicalComplex C c) (i j : ι)
    (hj : c.next i = j) :
    IsLimit (KernelFork.ofι (cyclesImageSequence K i j).f
      (cyclesImageSequence K i j).zero) :=
  (cyclesImageSequence_shortExact K i j hj).fIsKernel

/-- Projectivity of the outgoing image gives its noncanonical splitting. -/
def cyclesImageSequenceSplitting (K : HomologicalComplex C c) (i j : ι)
    (hj : c.next i = j) [Projective (Abelian.image (K.d i j))] :
    (cyclesImageSequence K i j).Splitting :=
  letI : Projective (cyclesImageSequence K i j).X₃ := by
    change Projective (Abelian.image (K.d i j))
    infer_instance
  (cyclesImageSequence_shortExact K i j hj).splittingOfProjective

/-- The first sequence's differential and cycle maps form an functor. -/
def cyclesImageSequenceFunctor (i j : ι) : HomologicalComplex C c ⥤ ShortComplex C :=
  (ShortComplex.functorEquivalence (HomologicalComplex C c) C).functor.obj
    (ShortComplex.mk (cyclesInclusionNatTrans (C := C) (c := c) i)
      (Functor.whiskerLeft (cyclesImageArrowFunctor (C := C) (c := c) i j)
        (Abelian.factorThruImageNatTrans (C := C))) (by
          apply NatTrans.ext
          funext K
          change K.iCycles i ≫ Abelian.factorThruImage (K.d i j) = 0
          exact (cyclesImageSequence K i j).zero))

/-- The first functor retains the literal sequence data. -/
theorem cyclesImageSequenceFunctor_obj (K : HomologicalComplex C c) (i j : ι) :
    (cyclesImageSequenceFunctor (C := C) (c := c) i j).obj K =
      cyclesImageSequence K i j := rfl

/-- The kernel, domain and image maps retain the complex map in the middle. -/
theorem cyclesImageSequenceFunctor_map_τ₂ {K L : HomologicalComplex C c}
    (φ : K ⟶ L) (i j : ι) :
    ((cyclesImageSequenceFunctor (C := C) (c := c) i j).map φ).τ₂ = φ.f i := rfl

/-- The boundary map uses the short-complex map and outgoing kernel/cycles comparison. -/
def boundaryCyclesMap (K : HomologicalComplex C c) (i j : ι) :
    Abelian.image (K.d i j) ⟶ K.cycles j :=
  let S := K.sc' i j (c.next j)
  ShortComplex.boundaryCyclesMap S ≫
    (S.isoCyclesOfIsLimit (kf := KernelFork.ofι (K.iCycles j) (K.iCycles_d j (c.next j))) (K.cyclesIsKernel j (c.next j) rfl)).inv

/-- The boundary map followed by the cycles inclusion is the image inclusion. -/
@[reassoc]
theorem boundaryCyclesMap_i (K : HomologicalComplex C c) (i j : ι) :
    boundaryCyclesMap K i j ≫ K.iCycles j = Abelian.image.ι (K.d i j) := by
  let S := K.sc' i j (c.next j)
  change (ShortComplex.boundaryCyclesMap S ≫
    (S.isoCyclesOfIsLimit (kf := KernelFork.ofι (K.iCycles j) (K.iCycles_d j (c.next j))) (K.cyclesIsKernel j (c.next j) rfl)).inv) ≫
      K.iCycles j = Abelian.image.ι (K.d i j)
  let e : K.cycles j ≅ S.cycles :=
    S.isoCyclesOfIsLimit (kf := KernelFork.ofι (K.iCycles j) (K.iCycles_d j (c.next j)))
      (K.cyclesIsKernel j (c.next j) rfl)
  have he : e.inv ≫ K.iCycles j = S.iCycles :=
    S.isoCyclesOfIsLimit_inv_ι
      (kf := KernelFork.ofι (K.iCycles j) (K.iCycles_d j (c.next j)))
      (K.cyclesIsKernel j (c.next j) rfl)
  exact (Category.assoc (ShortComplex.boundaryCyclesMap S) e.inv (K.iCycles j)).trans
    ((congrArg (fun t : S.cycles ⟶ K.X j => ShortComplex.boundaryCyclesMap S ≫ t) he).trans
      (ShortComplex.boundaryCyclesMap_i S))

/-- The differential's map onto its image followed by the boundary map is toCycles. -/
@[reassoc]
theorem factorThruImage_boundaryCyclesMap (K : HomologicalComplex C c) (i j : ι) :
    Abelian.factorThruImage (K.d i j) ≫ boundaryCyclesMap K i j = K.toCycles i j := by
  apply (cancel_mono (K.iCycles j)).1
  simpa only [Category.assoc, boundaryCyclesMap_i, Abelian.image.fac]
    using (K.toCycles_i i j).symm

/-- Boundaries give zero under the homology quotient in every shape. -/
@[reassoc]
theorem boundaryCyclesMap_homologyπ (K : HomologicalComplex C c) (i j : ι) :
    boundaryCyclesMap K i j ≫ K.homologyπ j = 0 := by
  apply (cancel_epi (Abelian.factorThruImage (K.d i j))).1
  simpa only [← Category.assoc, factorThruImage_boundaryCyclesMap,
    CategoryTheory.Limits.comp_zero] using (K.toCycles_comp_homologyπ i j)

/-- The incoming-image, cycles, and homology data for arbitrary index pairs. -/
def boundariesCyclesHomologySequence (K : HomologicalComplex C c) (i j : ι) :
    ShortComplex C :=
  ShortComplex.mk (boundaryCyclesMap K i j) (K.homologyπ j)
    (boundaryCyclesMap_homologyπ K i j)

/-- The incoming-index witness earns the boundary-map comparison. -/
@[reassoc]
theorem boundaryCyclesMap_cyclesIsoSc'_hom (K : HomologicalComplex C c) (i j : ι)
    (hi : c.prev j = i) :
    boundaryCyclesMap K i j ≫ (K.cyclesIsoSc' i j (c.next j) hi rfl).hom =
      ShortComplex.boundaryCyclesMap (K.sc' i j (c.next j)) := by
  let S := K.sc' i j (c.next j)
  apply (cancel_mono S.iCycles).1
  have hLeft : (boundaryCyclesMap K i j ≫
      (K.cyclesIsoSc' i j (c.next j) hi rfl).hom) ≫ S.iCycles =
        Abelian.image.ι (K.d i j) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t : K.cycles j ⟶ K.X j => boundaryCyclesMap K i j ≫ t)
        (K.cyclesIsoSc'_hom_iCycles i j (c.next j) hi rfl)).trans
          (boundaryCyclesMap_i K i j))
  exact hLeft.trans (ShortComplex.boundaryCyclesMap_i S).symm

/-- Cycle/homology isos compare the concrete incoming data to the generic sequence. -/
def boundariesCyclesHomologySequenceIso (K : HomologicalComplex C c) (i j : ι)
    (hi : c.prev j = i) : boundariesCyclesHomologySequence K i j ≅
      ShortComplex.imageCyclesHomologySES (K.sc' i j (c.next j)) := by
  let eC := K.cyclesIsoSc' i j (c.next j) hi rfl
  let eH := K.homologyIsoSc' i j (c.next j) hi rfl
  refine ShortComplex.isoMk (Iso.refl _) eC eH ?_ ?_
  · change (𝟙 _) ≫ ShortComplex.boundaryCyclesMap (K.sc' i j (c.next j)) =
      boundaryCyclesMap K i j ≫ eC.hom
    exact (Category.id_comp _).trans (boundaryCyclesMap_cyclesIsoSc'_hom K i j hi).symm
  · change eC.hom ≫ (K.sc' i j (c.next j)).homologyπ = K.homologyπ j ≫ eH.hom
    exact (K.π_homologyIsoSc'_hom i j (c.next j) hi rfl).symm

/-- Incoming boundaries, cycles and homology are short exact at the incoming index. -/
theorem boundariesCyclesHomologySequence_shortExact (K : HomologicalComplex C c) (i j : ι)
    (hi : c.prev j = i) : (boundariesCyclesHomologySequence K i j).ShortExact :=
  ShortComplex.shortExact_of_iso (boundariesCyclesHomologySequenceIso K i j hi).symm
    (ShortComplex.imageCyclesHomologySES_shortExact (K.sc' i j (c.next j)))

/-- Complex maps commute with the boundary inclusion. -/
@[reassoc]
theorem boundaryCyclesMap_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) (i j : ι) :
    (Abelian.im (C := C)).map
        ((cyclesImageArrowFunctor (C := C) (c := c) i j).map φ) ≫ boundaryCyclesMap L i j =
      boundaryCyclesMap K i j ≫ cyclesMap φ j := by
  let S : ShortComplex C := K.sc' i j (c.next j)
  let T : ShortComplex C := L.sc' i j (c.next j)
  let ψ : S ⟶ T := (shortComplexFunctor' C c i j (c.next j)).map φ
  let eK : K.cycles j ≅ S.cycles :=
    S.isoCyclesOfIsLimit (kf := KernelFork.ofι (K.iCycles j) (K.iCycles_d j (c.next j)))
      (K.cyclesIsKernel j (c.next j) rfl)
  let eL : L.cycles j ≅ T.cycles :=
    T.isoCyclesOfIsLimit (kf := KernelFork.ofι (L.iCycles j) (L.iCycles_d j (c.next j)))
      (L.cyclesIsKernel j (c.next j) rfl)
  let square : Arrow.mk S.f ⟶ Arrow.mk T.f :=
    Arrow.homMk ψ.τ₁ ψ.τ₂ ψ.comm₁₂
  let m : Abelian.image S.f ⟶ Abelian.image T.f :=
    (Abelian.im (C := C)).map square
  have heK : eK.inv ≫ K.iCycles j = S.iCycles :=
    S.isoCyclesOfIsLimit_inv_ι
      (kf := KernelFork.ofι (K.iCycles j) (K.iCycles_d j (c.next j)))
      (K.cyclesIsKernel j (c.next j) rfl)
  have heL : eL.inv ≫ L.iCycles j = T.iCycles :=
    T.isoCyclesOfIsLimit_inv_ι
      (kf := KernelFork.ofι (L.iCycles j) (L.iCycles_d j (c.next j)))
      (L.cyclesIsKernel j (c.next j) rfl)
  have hCycles : ShortComplex.cyclesMap ψ ≫ eL.inv = eK.inv ≫ cyclesMap φ j := by
    apply (cancel_mono (L.iCycles j)).1
    have hLeft : (ShortComplex.cyclesMap ψ ≫ eL.inv) ≫ L.iCycles j =
        S.iCycles ≫ φ.f j :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t : T.cycles ⟶ L.X j => ShortComplex.cyclesMap ψ ≫ t) heL).trans
          (ShortComplex.cyclesMap_i ψ))
    have hRight : (eK.inv ≫ cyclesMap φ j) ≫ L.iCycles j = S.iCycles ≫ φ.f j :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t : K.cycles j ⟶ L.X j => eK.inv ≫ t) (cyclesMap_i φ j)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun t : S.cycles ⟶ K.X j => t ≫ φ.f j) heK)))
    exact hLeft.trans hRight.symm
  have hBoundary : m ≫ ShortComplex.boundaryCyclesMap T =
      ShortComplex.boundaryCyclesMap S ≫ ShortComplex.cyclesMap ψ :=
    ShortComplex.boundaryCyclesMap_naturality ψ
  change m ≫ (ShortComplex.boundaryCyclesMap T ≫ eL.inv) =
    (ShortComplex.boundaryCyclesMap S ≫ eK.inv) ≫ cyclesMap φ j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t : Abelian.image S.f ⟶ T.cycles => t ≫ eL.inv) hBoundary).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t : S.cycles ⟶ L.cycles j => ShortComplex.boundaryCyclesMap S ≫ t)
          hCycles).trans (Category.assoc _ _ _).symm)))

/-- The differential image maps naturally to cycles in every complex shape. -/
def boundaryCyclesNatTrans (i j : ι) :
    cyclesImageArrowFunctor (C := C) (c := c) i j ⋙ Abelian.im ⟶ cyclesFunctor C c j where
  app K := boundaryCyclesMap K i j
  naturality K L φ := boundaryCyclesMap_naturality φ i j

/-- The image, cycles and homology maps packaged as a sequence functor. -/
def boundariesCyclesHomologySequenceFunctor (i j : ι) :
    HomologicalComplex C c ⥤ ShortComplex C :=
  (ShortComplex.functorEquivalence (HomologicalComplex C c) C).functor.obj
    (ShortComplex.mk (boundaryCyclesNatTrans (C := C) (c := c) i j)
      (natTransHomologyπ C c j) (by
        apply NatTrans.ext
        funext K
        change boundaryCyclesMap K i j ≫ K.homologyπ j = 0
        exact boundaryCyclesMap_homologyπ K i j))

/-- The packaged functor preserves the literal incoming sequence data. -/
theorem boundariesCyclesHomologySequenceFunctor_obj (K : HomologicalComplex C c) (i j : ι) :
    (boundariesCyclesHomologySequenceFunctor (C := C) (c := c) i j).obj K =
      boundariesCyclesHomologySequence K i j := rfl

/-- Its cycle component is the cycles map. -/
theorem boundariesCyclesHomologySequenceFunctor_map_τ₂ {K L : HomologicalComplex C c}
    (φ : K ⟶ L) (i j : ι) :
    ((boundariesCyclesHomologySequenceFunctor (C := C) (c := c) i j).map φ).τ₂ =
      cyclesMap φ j := rfl

/-- Its homology component is the homology map. -/
theorem boundariesCyclesHomologySequenceFunctor_map_τ₃ {K L : HomologicalComplex C c}
    (φ : K ⟶ L) (i j : ι) :
    ((boundariesCyclesHomologySequenceFunctor (C := C) (c := c) i j).map φ).τ₃ =
      homologyMap φ j := rfl

/-- The boundary sequence's image component preserves the differential square. -/
@[reassoc]
theorem boundariesCyclesHomologySequenceFunctor_map_image_ι
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (i j : ι) :
    ((boundariesCyclesHomologySequenceFunctor (C := C) (c := c) i j).map φ).τ₁ ≫
        Abelian.image.ι (L.d i j) = Abelian.image.ι (K.d i j) ≫ φ.f j := by
  let a := (cyclesImageArrowFunctor (C := C) (c := c) i j).map φ
  change ((Abelian.kernelImageSESFunctor (C := C)).map a).τ₃ ≫
    Abelian.image.ι (L.d i j) = Abelian.image.ι (K.d i j) ≫ φ.f j
  exact Abelian.kernelImageSESFunctor_map_image_ι a

end HomologicalComplex
