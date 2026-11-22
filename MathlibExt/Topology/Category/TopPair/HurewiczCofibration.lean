/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyExtension
import MathlibExt.Topology.Category.TopCat.BinaryClosedGlue
public import MathlibExt.Topology.Category.TopPair.Product

/-!
# Hurewicz cofibrations of embedded topological pairs

For an embedded pair `A ⟶ X`, this file identifies a closed Hurewicz
cofibration with a chosen retraction of `X × I` onto
`A × I ∪ X × {0}`.  The forward construction glues the prescribed homotopy
on the closed side to the initial map on the closed bottom.  The reverse
construction applies the homotopy-extension property to the canonical side
and bottom maps.

The target of the induced extension may live in an independent universe.
Closedness remains an explicit field and conclusion: HEP alone is not claimed
to imply a closed embedding in arbitrary topological spaces.

No NDR, pushout, delta-generated, or model-category claim is made here.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u v

namespace TopPair

/-- The topological pair `({0} ⟶ I)`. -/
abbrev intervalZeroPair : TopPair.{u} :=
  TopPair.ofSubset ({(0 : TopCat.I.{u})} : Set TopCat.I.{u})

/-- The cylinder pair of `P`: its subspace is
`range(P.map) × I ∪ P.fst × {0}`. -/
abbrev hurewiczCylinderPair (P : TopPair.{u}) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (P.fst × TopCat.I.{u}))
    ((Set.range P.map).unionProd
      ({(0 : TopCat.I.{u})} : Set TopCat.I.{u}))

@[simp]
theorem range_intervalZeroPair_map :
    Set.range (intervalZeroPair.{u}).map =
      ({(0 : TopCat.I.{u})} : Set TopCat.I.{u}) := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact s.2
  · intro ht
    exact ⟨⟨t, ht⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the literal cylinder boundary. -/
@[simp]
theorem mem_range_hurewiczCylinderPair_map
    (P : TopPair.{u}) (z : (hurewiczCylinderPair P).fst) :
    z ∈ Set.range (hurewiczCylinderPair P).map ↔
      z.1 ∈ Set.range P.map ∨ z.2 = 0 := by
  change (∃ y : {x : P.fst × TopCat.I.{u} //
      x ∈ (Set.range P.map).unionProd
        ({(0 : TopCat.I.{u})} : Set TopCat.I.{u})}, y.1 = z) ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    simpa only [Set.mem_unionProd, Set.mem_singleton_iff] using y.2
  · intro hz
    refine ⟨⟨z, ?_⟩, rfl⟩
    simpa only [Set.mem_unionProd, Set.mem_singleton_iff] using hz

/-- The side `A × I` inside the cylinder boundary. -/
def hurewiczCylinderSide (P : TopPair.{u}) :
    Set (hurewiczCylinderPair P).snd :=
  {z | z.1.1 ∈ Set.range P.map}

/-- The bottom `X × {0}` inside the cylinder boundary. -/
def hurewiczCylinderBottom (P : TopPair.{u}) :
    Set (hurewiczCylinderPair P).snd :=
  {z | z.1.2 = 0}

@[simp]
theorem mem_hurewiczCylinderSide
    (P : TopPair.{u}) (z : (hurewiczCylinderPair P).snd) :
    z ∈ hurewiczCylinderSide P ↔ z.1.1 ∈ Set.range P.map := by
  rfl

@[simp]
theorem mem_hurewiczCylinderBottom
    (P : TopPair.{u}) (z : (hurewiczCylinderPair P).snd) :
    z ∈ hurewiczCylinderBottom P ↔ z.1.2 = 0 := by
  rfl

/-- A point of the cylinder side. -/
def hurewiczCylinderSidePoint (P : TopPair.{u})
    (t : TopCat.I.{u}) (a : P.snd) : (hurewiczCylinderPair P).snd :=
  ⟨(P.map a, t), Set.mem_unionProd.mpr (Or.inl ⟨a, rfl⟩)⟩

/-- A point of the cylinder bottom. -/
def hurewiczCylinderBottomPoint (P : TopPair.{u})
    (x : P.fst) : (hurewiczCylinderPair P).snd :=
  ⟨(x, 0), Set.mem_unionProd.mpr (Or.inr rfl)⟩

@[simp]
theorem hurewiczCylinderSidePoint_mem (P : TopPair.{u})
    (t : TopCat.I.{u}) (a : P.snd) :
    hurewiczCylinderSidePoint P t a ∈ hurewiczCylinderSide P := by
  change P.map a ∈ Set.range P.map
  exact ⟨a, rfl⟩

@[simp]
theorem hurewiczCylinderBottomPoint_mem (P : TopPair.{u}) (x : P.fst) :
    hurewiczCylinderBottomPoint P x ∈ hurewiczCylinderBottom P := by
  change (0 : TopCat.I.{u}) = 0
  rfl

private theorem isClosed_hurewiczCylinderSide
    (P : TopPair.{u}) (hP : IsClosed (Set.range P.map)) :
    IsClosed (hurewiczCylinderSide P) := by
  exact hP.preimage (continuous_fst.comp continuous_subtype_val)

private theorem isClosed_hurewiczCylinderBottom (P : TopPair.{u}) :
    IsClosed (hurewiczCylinderBottom P) := by
  have hzero : IsClosed ({(0 : TopCat.I.{u})} : Set TopCat.I.{u}) := by
    have heq : ({(0 : TopCat.I.{u})} : Set TopCat.I.{u}) =
        TopCat.I.homeomorph ⁻¹' ({0} : Set unitInterval) := by
      ext t
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro ht
        rw [ht, TopCat.I.homeomorph_zero]
      · intro ht
        apply TopCat.I.ext
        simpa only [TopCat.I.homeomorph_zero] using ht
    rw [heq]
    exact isClosed_singleton.preimage TopCat.I.homeomorph.continuous
  change IsClosed
    ((fun z : (hurewiczCylinderPair P).snd => z.1.2) ⁻¹'
      ({(0 : TopCat.I.{u})} : Set TopCat.I.{u}))
  exact hzero.preimage (continuous_snd.comp continuous_subtype_val)

private theorem hurewiczCylinder_side_union_bottom
    (P : TopPair.{u}) :
    hurewiczCylinderSide P ∪ hurewiczCylinderBottom P = Set.univ := by
  ext z
  constructor
  · intro
    trivial
  · intro
    rcases Set.mem_unionProd.mp z.2 with hz | hz
    · exact Or.inl ((mem_hurewiczCylinderSide P z).2 hz)
    · exact Or.inr ((mem_hurewiczCylinderBottom P z).2 hz)

/-- Chosen closed cylinder-retraction data for an embedded topological pair. -/
structure HurewiczCofibrationData (P : TopPair.{u}) where
  /-- The embedded image is closed. -/
  isClosed_range : IsClosed (Set.range P.map)
  /-- Retraction from `X × I` onto `A × I ∪ X × {0}`. -/
  cylinderRetraction :
    (hurewiczCylinderPair P).fst ⟶ (hurewiczCylinderPair P).snd
  /-- The cylinder-boundary inclusion followed by the retraction is the
  identity. -/
  inclusion_comp_retraction :
    (hurewiczCylinderPair P).map ≫ cylinderRetraction = 𝟙 _

namespace HurewiczCofibrationData

variable {P : TopPair.{u}}

/-- Two choices of closed cylinder-retraction data with the same retraction
are equal; the remaining fields are properties. -/
@[ext]
theorem ext {d e : HurewiczCofibrationData P}
    (h : ∀ z, d.cylinderRetraction z = e.cylinderRetraction z) :
    d = e := by
  obtain ⟨_, r₁, _⟩ := d
  obtain ⟨_, r₂, _⟩ := e
  have hr : r₁ = r₂ := by
    ext z
    exact h z
  subst hr
  rfl

/-- The chosen cylinder retraction fixes every boundary point. -/
@[simp]
theorem cylinderRetraction_boundary (d : HurewiczCofibrationData P)
    (z : (hurewiczCylinderPair P).snd) :
    d.cylinderRetraction ((hurewiczCylinderPair P).map z) = z := by
  have h := ConcreteCategory.congr_hom d.inclusion_comp_retraction z
  simpa only [TopCat.comp_app, TopCat.id_app] using h

/-- The pair map is a closed embedding. -/
theorem isClosedEmbedding_map (d : HurewiczCofibrationData P) :
    IsClosedEmbedding P.map :=
  ⟨P.isEmbedding_map, d.isClosed_range⟩

private def boundaryVal (S : Set (hurewiczCylinderPair P).snd) :
    C(S, P.fst × TopCat.I.{u}) where
  toFun z := z.1.1
  continuous_toFun := continuous_subtype_val.comp continuous_subtype_val

private def sideToRange :
    C(hurewiczCylinderSide P, Set.range P.map) where
  toFun z := ⟨z.1.1.1, (mem_hurewiczCylinderSide P z.1).1 z.2⟩
  continuous_toFun :=
    (continuous_fst.comp (boundaryVal (hurewiczCylinderSide P)).continuous).subtype_mk _

private def sideToSubspace : C(hurewiczCylinderSide P, P.snd) :=
  { toFun := fun z => P.isEmbedding_map.toHomeomorph.symm (sideToRange z)
    continuous_toFun := P.isEmbedding_map.toHomeomorph.symm.continuous.comp
      sideToRange.continuous }

private def topIToUnitInterval : C(TopCat.I.{u}, unitInterval) :=
  ⟨TopCat.I.homeomorph, TopCat.I.homeomorph.continuous⟩

private def unitIntervalToTopI : C(unitInterval, TopCat.I.{u}) :=
  ⟨TopCat.I.homeomorph.symm, TopCat.I.homeomorph.symm.continuous⟩

private def sideMap
    {Y : Type v} [TopologicalSpace Y]
    (H : C(unitInterval × P.snd, Y)) :
    C(hurewiczCylinderSide P, Y) :=
  H.comp
    ((topIToUnitInterval.comp
      (ContinuousMap.snd.comp (boundaryVal (hurewiczCylinderSide P)))).prodMk
      sideToSubspace)

private def bottomMap
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) : C(hurewiczCylinderBottom P, Y) :=
  f.comp (ContinuousMap.fst.comp (boundaryVal (hurewiczCylinderBottom P)))

private theorem sideMap_eq_bottomMap
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a))
    (z : (hurewiczCylinderPair P).snd)
    (hzs : z ∈ hurewiczCylinderSide P)
    (hzb : z ∈ hurewiczCylinderBottom P) :
    sideMap H ⟨z, hzs⟩ = bottomMap f ⟨z, hzb⟩ := by
  let a : P.snd := P.isEmbedding_map.toHomeomorph.symm
    ⟨z.1.1, (mem_hurewiczCylinderSide P z).1 hzs⟩
  have ha : P.map a = z.1.1 := by
    exact congrArg Subtype.val
      (P.isEmbedding_map.toHomeomorph.apply_symm_apply
        ⟨z.1.1, (mem_hurewiczCylinderSide P z).1 hzs⟩)
  have ht : z.1.2 = 0 := (mem_hurewiczCylinderBottom P z).1 hzb
  change H (TopCat.I.homeomorph z.1.2, a) = f z.1.1
  rw [ht, TopCat.I.homeomorph_zero, h0 a, ha]

private theorem exists_boundaryMap
    (d : HurewiczCofibrationData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a)) :
    ∃ G : C((hurewiczCylinderPair P).snd, Y),
      G.restrict (hurewiczCylinderSide P) = sideMap H ∧
        G.restrict (hurewiczCylinderBottom P) = bottomMap f := by
  exact TopCat.exists_continuousMap_glue_of_closed_cover
    (X := TopCat.of (hurewiczCylinderPair P).snd) (Z := TopCat.of Y)
    (s := hurewiczCylinderSide P) (t := hurewiczCylinderBottom P)
    (isClosed_hurewiczCylinderSide P d.isClosed_range)
    (isClosed_hurewiczCylinderBottom P)
    (hurewiczCylinder_side_union_bottom P)
    (sideMap H) (bottomMap f) (sideMap_eq_bottomMap f H h0)

private noncomputable def boundaryMap
    (d : HurewiczCofibrationData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a)) :
    C((hurewiczCylinderPair P).snd, Y) :=
  Classical.choose (exists_boundaryMap d f H h0)

private theorem boundaryMap_restrict_side
    (d : HurewiczCofibrationData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a)) :
    (boundaryMap d f H h0).restrict (hurewiczCylinderSide P) =
      sideMap H :=
  (Classical.choose_spec (exists_boundaryMap d f H h0)).1

private theorem boundaryMap_restrict_bottom
    (d : HurewiczCofibrationData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a)) :
    (boundaryMap d f H h0).restrict (hurewiczCylinderBottom P) =
      bottomMap f :=
  (Classical.choose_spec (exists_boundaryMap d f H h0)).2

private theorem boundaryMap_side_apply
    (d : HurewiczCofibrationData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a))
    (t : TopCat.I.{u}) (a : P.snd) :
    boundaryMap d f H h0 (hurewiczCylinderSidePoint P t a) =
      H (TopCat.I.homeomorph t, a) := by
  have h := DFunLike.congr_fun (boundaryMap_restrict_side d f H h0)
    ⟨hurewiczCylinderSidePoint P t a,
      hurewiczCylinderSidePoint_mem P t a⟩
  rw [ContinuousMap.restrict_apply] at h
  calc
    boundaryMap d f H h0 (hurewiczCylinderSidePoint P t a) =
        sideMap H
          ⟨hurewiczCylinderSidePoint P t a,
            hurewiczCylinderSidePoint_mem P t a⟩ := h
    _ = H (TopCat.I.homeomorph t, a) := by
      let zSide : hurewiczCylinderSide P :=
        ⟨hurewiczCylinderSidePoint P t a,
          hurewiczCylinderSidePoint_mem P t a⟩
      let r : Set.range P.map := sideToRange zSide
      have hr : r.1 = P.map a := rfl
      have hInv : P.isEmbedding_map.toHomeomorph.symm r = a := by
        apply P.isEmbedding_map.injective
        have h := congrArg Subtype.val
          (P.isEmbedding_map.toHomeomorph.apply_symm_apply r)
        exact h.trans hr
      change H (TopCat.I.homeomorph t,
        P.isEmbedding_map.toHomeomorph.symm r) = H (TopCat.I.homeomorph t, a)
      rw [hInv]

private theorem boundaryMap_bottom_apply
    (d : HurewiczCofibrationData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a))
    (x : P.fst) :
    boundaryMap d f H h0 (hurewiczCylinderBottomPoint P x) = f x := by
  have h := DFunLike.congr_fun (boundaryMap_restrict_bottom d f H h0)
    ⟨hurewiczCylinderBottomPoint P x,
      hurewiczCylinderBottomPoint_mem P x⟩
  rw [ContinuousMap.restrict_apply] at h
  calc
    boundaryMap d f H h0 (hurewiczCylinderBottomPoint P x) =
        bottomMap f
          ⟨hurewiczCylinderBottomPoint P x,
            hurewiczCylinderBottomPoint_mem P x⟩ := h
    _ = f x := rfl

/-- Closed cylinder-retraction data gives an explicit homotopy extension into
an arbitrary target universe. -/
noncomputable opaque homotopyExtension
    (d : HurewiczCofibrationData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a)) :
    Topology.HomotopyExtensionData P.map.hom f H h0 := by
  refine
    { extension := boundaryMap d f H h0 |>.comp
        (d.cylinderRetraction.hom.comp
          (ContinuousMap.snd.prodMk
            (unitIntervalToTopI.comp ContinuousMap.fst)))
      extension_zero := ?_
      extension_subspace := ?_ }
  · intro x
    let z := hurewiczCylinderBottomPoint P x
    have hr := d.cylinderRetraction_boundary z
    change boundaryMap d f H h0 (d.cylinderRetraction (x, 0)) = f x
    change boundaryMap d f H h0
      (d.cylinderRetraction ((hurewiczCylinderPair P).map z)) = f x
    rw [hr]
    exact boundaryMap_bottom_apply d f H h0 x
  · intro t a
    let z := hurewiczCylinderSidePoint P (TopCat.I.homeomorph.symm t) a
    have hr := d.cylinderRetraction_boundary z
    change boundaryMap d f H h0
      (d.cylinderRetraction (P.map a, TopCat.I.homeomorph.symm t)) = H (t, a)
    change boundaryMap d f H h0
      (d.cylinderRetraction ((hurewiczCylinderPair P).map z)) = H (t, a)
    rw [hr]
    simpa only [TopCat.I.homeomorph.apply_symm_apply] using
      boundaryMap_side_apply d f H h0 (TopCat.I.homeomorph.symm t) a

/-- Closed cylinder-retraction data implies the cross-universe HEP. -/
theorem hasHomotopyExtensionProperty (d : HurewiczCofibrationData P) :
    Topology.HasHomotopyExtensionProperty.{u, v} P.map.hom := by
  intro Y _ f H h0
  exact ⟨d.homotopyExtension f H h0⟩

/-- Closed cylinder-retraction data implies the same-universe TopCat HEP. -/
theorem isHurewiczCofibration (d : HurewiczCofibrationData P) :
    TopCat.IsHurewiczCofibration P.map :=
  d.hasHomotopyExtensionProperty

end HurewiczCofibrationData

private def hurewiczCylinderBottomMap (P : TopPair.{u}) :
    C(P.fst, (hurewiczCylinderPair P).snd) where
  toFun x := ⟨(x, 0), Set.mem_unionProd.mpr (Or.inr rfl)⟩
  continuous_toFun := by
    exact (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : P.fst => (0 : TopCat.I.{u})))).subtype_mk _

private def hurewiczCylinderSideHomotopy (P : TopPair.{u}) :
    C(unitInterval × P.snd, (hurewiczCylinderPair P).snd) where
  toFun p := ⟨(P.map p.2, TopCat.I.homeomorph.symm p.1),
    Set.mem_unionProd.mpr (Or.inl ⟨p.2, rfl⟩)⟩
  continuous_toFun := by
    exact ((P.map.hom.continuous.comp continuous_snd).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_fst)).subtype_mk _

/-- Construct closed cylinder-retraction data from closedness and HEP. -/
noncomputable opaque HurewiczCofibrationData.ofIsClosedEmbeddingOfHEP
    {P : TopPair.{u}} (hclosed : IsClosedEmbedding P.map)
    (hhep : TopCat.IsHurewiczCofibration P.map) :
    HurewiczCofibrationData P := by
  have h0 (a : P.snd) :
      hurewiczCylinderSideHomotopy P (0, a) =
        hurewiczCylinderBottomMap P (P.map a) := by
    apply Subtype.ext
    rfl
  let e := Classical.choice (hhep (hurewiczCylinderBottomMap P)
    (hurewiczCylinderSideHomotopy P) h0)
  let topIToUnit : C(TopCat.I.{u}, unitInterval) :=
    ⟨TopCat.I.homeomorph, TopCat.I.homeomorph.continuous⟩
  let swap : C(P.fst × TopCat.I.{u}, unitInterval × P.fst) :=
    (topIToUnit.comp ContinuousMap.snd).prodMk ContinuousMap.fst
  let r : (hurewiczCylinderPair P).fst ⟶
      (hurewiczCylinderPair P).snd :=
    TopCat.ofHom (e.extension.comp swap)
  refine
    { isClosed_range := hclosed.isClosed_range
      cylinderRetraction := r
      inclusion_comp_retraction := ?_ }
  apply TopCat.hom_ext
  ext z
  apply Subtype.ext
  rcases Set.mem_unionProd.mp z.2 with hz | hz
  · rcases hz with ⟨a, ha⟩
    have he := e.extension_subspace (TopCat.I.homeomorph z.1.2) a
    have he' := congrArg Subtype.val he
    change (e.extension (TopCat.I.homeomorph z.1.2, P.map a)).1 =
      (P.map a, TopCat.I.homeomorph.symm (TopCat.I.homeomorph z.1.2)) at he'
    rw [TopCat.I.homeomorph.symm_apply_apply] at he'
    change (e.extension (TopCat.I.homeomorph z.1.2, z.1.1)).1 = z.1
    calc
      (e.extension (TopCat.I.homeomorph z.1.2, z.1.1)).1 =
          (e.extension (TopCat.I.homeomorph z.1.2, P.map a)).1 :=
        congrArg (fun x => (e.extension (TopCat.I.homeomorph z.1.2, x)).1) ha.symm
      _ = z.1 := he'.trans (Prod.ext ha rfl)
  · have ht : z.1.2 = 0 := by
      exact hz
    have he := e.extension_zero z.1.1
    have he' := congrArg Subtype.val he
    change (e.extension (0, z.1.1)).1 = (z.1.1, 0) at he'
    change (e.extension (TopCat.I.homeomorph z.1.2, z.1.1)).1 = z.1
    rw [ht, TopCat.I.homeomorph_zero]
    exact he'.trans (Prod.ext rfl ht.symm)

/-- Closed cylinder-retraction data is equivalent to a closed pair embedding
with the Hurewicz homotopy-extension property. -/
theorem hurewiczCofibrationData_iff (P : TopPair.{u}) :
    Nonempty (HurewiczCofibrationData P) ↔
      IsClosedEmbedding P.map ∧ TopCat.IsHurewiczCofibration P.map := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.isClosedEmbedding_map, d.isHurewiczCofibration⟩
  · rintro ⟨hclosed, hhep⟩
    exact ⟨HurewiczCofibrationData.ofIsClosedEmbeddingOfHEP hclosed hhep⟩

end TopPair

end
