/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod
public import MathlibExt.Topology.Category.TopPair.HomotopyEquiv

/-!
# Homotopy invariance for topological pairs

Homotopy-invariance isomorphisms for topological pairs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.HomologyPretheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
variable {X Y Z : TopPair.{w}}

/-- A pair homotopy equivalence induces an isomorphism for any homotopy-invariant
homology pretheory. -/
noncomputable def relativeIsoOfHomotopyEquiv
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (i : ι) :
    (E.Hₚ i).obj X ≅ (E.Hₚ i).obj Y where
  hom := (E.Hₚ i).map e.hom
  inv := (E.Hₚ i).map e.inv
  hom_inv_id := by
    rw [← Functor.map_comp, HomologyPretheory.map_eq_of_homotopy E e.homotopyHomInvId i,
      (E.Hₚ i).map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, HomologyPretheory.map_eq_of_homotopy E e.homotopyInvHomId i,
      (E.Hₚ i).map_id]

@[simp]
lemma relativeIsoOfHomotopyEquiv_hom
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (i : ι) :
    (E.relativeIsoOfHomotopyEquiv e i).hom = (E.Hₚ i).map e.hom :=
  rfl

@[simp]
lemma relativeIsoOfHomotopyEquiv_inv
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (i : ι) :
    (E.relativeIsoOfHomotopyEquiv e i).inv = (E.Hₚ i).map e.inv :=
  rfl

@[simp]
lemma relativeIsoOfHomotopyEquiv_refl
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (X : TopPair.{w}) (i : ι) :
    E.relativeIsoOfHomotopyEquiv (HomotopyEquiv.refl X) i = Iso.refl _ := by
  apply Iso.ext
  simp only [relativeIsoOfHomotopyEquiv]
  exact (E.Hₚ i).map_id X

@[simp]
lemma relativeIsoOfHomotopyEquiv_symm
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (i : ι) :
    E.relativeIsoOfHomotopyEquiv e.symm i = (E.relativeIsoOfHomotopyEquiv e i).symm := by
  apply Iso.ext
  rfl

@[simp]
lemma relativeIsoOfHomotopyEquiv_trans
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (f : TopPair.HomotopyEquiv Y Z) (i : ι) :
    E.relativeIsoOfHomotopyEquiv (e.trans f) i =
      (E.relativeIsoOfHomotopyEquiv e i).trans (E.relativeIsoOfHomotopyEquiv f i) := by
  apply Iso.ext
  simp only [relativeIsoOfHomotopyEquiv, HomotopyEquiv.trans]
  exact (E.Hₚ i).map_comp e.hom f.hom

lemma relativeIsoOfHomotopyEquiv_hom_naturality
    {E F : HomologyPretheory.{w} C c} [E.IsHomotopyInvariant] [F.IsHomotopyInvariant]
    (α : E ⟶ F) (e : TopPair.HomotopyEquiv X Y) (i : ι) :
    (α.homₚ i).app X ≫ (F.relativeIsoOfHomotopyEquiv e i).hom =
      (E.relativeIsoOfHomotopyEquiv e i).hom ≫ (α.homₚ i).app Y :=
  ((α.homₚ i).naturality e.hom).symm

lemma relativeIsoOfHomotopyEquiv_inv_naturality
    {E F : HomologyPretheory.{w} C c} [E.IsHomotopyInvariant] [F.IsHomotopyInvariant]
    (α : E ⟶ F) (e : TopPair.HomotopyEquiv X Y) (i : ι) :
    (α.homₚ i).app Y ≫ (F.relativeIsoOfHomotopyEquiv e i).inv =
      (E.relativeIsoOfHomotopyEquiv e i).inv ≫ (α.homₚ i).app X :=
  ((α.homₚ i).naturality e.inv).symm

variable {X Y Z : TopCat.{w}}

/-- Homotopic maps of spaces induce equal maps on absolute homology for any
homotopy-invariant pretheory. -/
theorem absoluteMap_eq_of_homotopy
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (i : ι) :
    (E.H i).map f = (E.H i).map g := by
  apply (cancel_mono ((E.iso i).hom.app Y)).mp
  rw [(E.iso i).hom.naturality f, (E.iso i).hom.naturality g]
  exact congrArg (fun k => (E.iso i).hom.app X ≫ k)
    (HomologyPretheory.map_eq_of_homotopy E (TopPair.Homotopy.ofTopCat H) i)

/-- A homotopy equivalence of spaces induces an isomorphism for any
homotopy-invariant homology pretheory. -/
noncomputable def absoluteIsoOfHomotopyEquiv
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ι) :
    (E.H i).obj X ≅ (E.H i).obj Y where
  hom := (E.H i).map (TopCat.ofHom e.toFun)
  inv := (E.H i).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← (E.H i).map_comp]
    let H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) :=
      e.left_inv.some
    rw [E.absoluteMap_eq_of_homotopy H i, (E.H i).map_id]
  inv_hom_id := by
    rw [← (E.H i).map_comp]
    let H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) :=
      e.right_inv.some
    rw [E.absoluteMap_eq_of_homotopy H i, (E.H i).map_id]

@[simp]
lemma absoluteIsoOfHomotopyEquiv_hom
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ι) :
    (E.absoluteIsoOfHomotopyEquiv e i).hom =
      (E.H i).map (TopCat.ofHom e.toFun) :=
  rfl

@[simp]
lemma absoluteIsoOfHomotopyEquiv_inv
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ι) :
    (E.absoluteIsoOfHomotopyEquiv e i).inv =
      (E.H i).map (TopCat.ofHom e.invFun) :=
  rfl

@[simp]
lemma absoluteIsoOfHomotopyEquiv_refl
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (X : TopCat.{w}) (i : ι) :
    E.absoluteIsoOfHomotopyEquiv (ContinuousMap.HomotopyEquiv.refl X) i =
      Iso.refl _ := by
  apply Iso.ext
  simp only [absoluteIsoOfHomotopyEquiv_hom]
  exact (E.H i).map_id X

@[simp]
lemma absoluteIsoOfHomotopyEquiv_symm
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ι) :
    E.absoluteIsoOfHomotopyEquiv e.symm i =
      (E.absoluteIsoOfHomotopyEquiv e i).symm := by
  apply Iso.ext
  simp only [Iso.symm_hom, absoluteIsoOfHomotopyEquiv_hom,
    absoluteIsoOfHomotopyEquiv_inv]
  rfl

@[simp]
lemma absoluteIsoOfHomotopyEquiv_trans
    (E : HomologyPretheory.{w} C c) [E.IsHomotopyInvariant]
    (e : ContinuousMap.HomotopyEquiv X Y)
    (f : ContinuousMap.HomotopyEquiv Y Z) (i : ι) :
    E.absoluteIsoOfHomotopyEquiv (e.trans f) i =
      (E.absoluteIsoOfHomotopyEquiv e i).trans
        (E.absoluteIsoOfHomotopyEquiv f i) := by
  apply Iso.ext
  simp only [absoluteIsoOfHomotopyEquiv_hom, Iso.trans_hom]
  change (E.H i).map
      (TopCat.ofHom e.toFun ≫ TopCat.ofHom f.toFun) = _
  exact (E.H i).map_comp _ _

lemma absoluteIsoOfHomotopyEquiv_hom_naturality
    {E F : HomologyPretheory.{w} C c} [E.IsHomotopyInvariant]
    [F.IsHomotopyInvariant] (α : E ⟶ F)
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ι) :
    (α.hom i).app X ≫ (F.absoluteIsoOfHomotopyEquiv e i).hom =
      (E.absoluteIsoOfHomotopyEquiv e i).hom ≫ (α.hom i).app Y := by
  simp only [absoluteIsoOfHomotopyEquiv_hom]
  exact ((α.hom i).naturality (TopCat.ofHom e.toFun)).symm

lemma absoluteIsoOfHomotopyEquiv_inv_naturality
    {E F : HomologyPretheory.{w} C c} [E.IsHomotopyInvariant]
    [F.IsHomotopyInvariant] (α : E ⟶ F)
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ι) :
    (α.hom i).app Y ≫ (F.absoluteIsoOfHomotopyEquiv e i).inv =
      (E.absoluteIsoOfHomotopyEquiv e i).inv ≫ (α.hom i).app X := by
  simp only [absoluteIsoOfHomotopyEquiv_inv]
  exact ((α.hom i).naturality (TopCat.ofHom e.invFun)).symm

end TopPair.HomologyPretheory

namespace TopPair.HomologyTheoryData

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : TopPair.{w}}

/-- Wrapper for integer grading; see `HomologyPretheory.relativeIsoOfHomotopyEquiv`. -/
noncomputable abbrev relativeIsoOfHomotopyEquiv
    (E : HomologyTheoryData.{w} C) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (n : ℤ) :
    (E.Hₚ n).obj X ≅ (E.Hₚ n).obj Y :=
  HomologyPretheory.relativeIsoOfHomotopyEquiv E e n

@[simp]
lemma relativeIsoOfHomotopyEquiv_hom
    (E : HomologyTheoryData.{w} C) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (n : ℤ) :
    (E.relativeIsoOfHomotopyEquiv e n).hom = (E.Hₚ n).map e.hom :=
  rfl

@[simp]
lemma relativeIsoOfHomotopyEquiv_inv
    (E : HomologyTheoryData.{w} C) [E.IsHomotopyInvariant]
    (e : TopPair.HomotopyEquiv X Y) (n : ℤ) :
    (E.relativeIsoOfHomotopyEquiv e n).inv = (E.Hₚ n).map e.inv :=
  rfl

end TopPair.HomologyTheoryData
