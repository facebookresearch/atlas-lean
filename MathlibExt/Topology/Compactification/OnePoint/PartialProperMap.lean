/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Actual open proper restriction of a pointed one-point map

A continuous map between one-point compactifications preserving infinity
restricts to a proper continuous map from its actual open finite-value domain.
The domain is the original preimage of the finite part, and the map has the
same original finite values. Every point outside the domain maps to infinity.
No partial map, inverse, domain model or properness proof is a supplied field.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology
open scoped OnePoint

universe uX uY uZ

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

continuous one-point maps preserving the additional point. -/
structure PointedOnePointMap (X : Type uX) (Y : Type uY)
    [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The original continuous extension. -/
  extension : C(OnePoint X, OnePoint Y)
  /-- Its actual value at the additional point. -/
  map_infty : extension ∞ = ∞

namespace OnePoint

variable {X : Type uX} [TopologicalSpace X]

/-- Let `X` be a topological space. The finite part of the one-point extension is the complement of
infinity.

The finite part, with the inclusion, has the same topology as X. -/
def finitePartHomeomorph {X : Type uX} [TopologicalSpace X] :
    X ≃ₜ {p : OnePoint X // p ∈ (({∞} : Set (OnePoint X))ᶜ)} :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr OnePoint.compl_infty.symm)

end OnePoint

namespace PointedOnePointMap

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

Equality of the continuous extensions determines a pointed one-point map completely. -/
@[ext]
theorem ext {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : PointedOnePointMap X Y} (h : f.extension = g.extension) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

Pointwise equality of the extensions is ordinary pointed-map extensionality. -/
theorem ext_apply {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : PointedOnePointMap X Y} (h : ∀ x, f.extension x = g.extension x) : f = g :=
  ext (ContinuousMap.ext h)

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Let `X` be a topological space. The pointed map is continuous on the one-point extensions and
preserves infinity.

The identity extension is pointed. -/
def id (X : Type uX) [TopologicalSpace X] : PointedOnePointMap X X :=
  ⟨ContinuousMap.id (OnePoint X), rfl⟩

/-- Let `X`, `Y`, `Z` be topological spaces. The pointed map is continuous on the one-point
extensions and preserves infinity.

Pointed composition is the same ordinary continuous-map composition. -/
def comp (g : PointedOnePointMap Y Z) (f : PointedOnePointMap X Y) : PointedOnePointMap X Z :=
  ⟨g.extension.comp f.extension, by change g.extension (f.extension ∞) = ∞; rw [f.map_infty, g.map_infty]⟩

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

The open domain consists precisely of the points with finite image. -/
def domain (f : PointedOnePointMap X Y) : Set X :=
  ((↑) : X → OnePoint X) ⁻¹' (f.extension ⁻¹' ({∞} : Set (OnePoint Y))ᶜ)

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

This domain is open in the X. -/
theorem domain_isOpen (f : PointedOnePointMap X Y) : IsOpen f.domain :=
  (OnePoint.isClosed_infty.isOpen_compl.preimage f.extension.continuous).preimage OnePoint.continuous_coe

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

The whole finite-value preimage contains no additional source point. -/
theorem finitePreimage_subset_range (f : PointedOnePointMap X Y) :
    f.extension ⁻¹' ({∞} : Set (OnePoint Y))ᶜ ⊆ Set.range ((↑) : X → OnePoint X) := by
  intro p hp
  rw [← OnePoint.compl_infty]
  intro hpoint
  have hpoint : p = ∞ := hpoint
  subst p
  exact hp f.map_infty

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

The finite-value domain is the finite preimage with the same subspace topology. -/
def domainHomeomorph (f : PointedOnePointMap X Y) :
    f.domain ≃ₜ (f.extension ⁻¹' ({∞} : Set (OnePoint Y))ᶜ) :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange f.finitePreimage_subset_range

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

The finite restriction, built from the existing preimage and finite-part factories. -/
def partialMap (f : PointedOnePointMap X Y) : C(f.domain, Y) where
  toFun x := (OnePoint.finitePartHomeomorph (X := Y)).symm
    (f.extension.restrictPreimage ({∞} : Set (OnePoint Y))ᶜ (f.domainHomeomorph x))
  continuous_toFun := (OnePoint.finitePartHomeomorph (X := Y)).symm.continuous.comp
    ((f.extension.restrictPreimage ({∞} : Set (OnePoint Y))ᶜ).continuous.comp
      f.domainHomeomorph.continuous)

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

Its finite values are exactly those of the continuous extension. -/
theorem partialMap_coe (f : PointedOnePointMap X Y) (x : f.domain) :
    (f.partialMap x : OnePoint Y) = f.extension (x : X) := by
  let q : {p : OnePoint Y // p ∈ (({∞} : Set (OnePoint Y))ᶜ)} :=
    f.extension.restrictPreimage ({∞} : Set (OnePoint Y))ᶜ (f.domainHomeomorph x)
  have h := (OnePoint.finitePartHomeomorph (X := Y)).apply_symm_apply q
  change ((OnePoint.finitePartHomeomorph (X := Y)).symm q : OnePoint Y) =
    f.extension (x : X)
  exact congrArg Subtype.val h

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity.

Every point outside the domain maps to infinity. -/
theorem outside_domain (f : PointedOnePointMap X Y) (x : X) (hx : x ∉ f.domain) :
    f.extension x = ∞ := by
  change ¬ f.extension (x : OnePoint X) ≠ ∞ at hx
  exact Classical.not_not.mp hx

section Proper

variable [LocallyCompactSpace Y] [T2Space Y]

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `Y` is locally compact and Hausdorff.

The restriction to the finite open domain is a proper continuous map. -/
theorem partialMap_isProperMap (f : PointedOnePointMap X Y) : IsProperMap f.partialMap := by
  have hproper : IsProperMap f.extension := f.extension.continuous.isProperMap
  have hrestricted := hproper.restrictPreimage ({∞} : Set (OnePoint Y))ᶜ
  change IsProperMap ((OnePoint.finitePartHomeomorph (X := Y)).symm ∘
    (f.extension.restrictPreimage ({∞} : Set (OnePoint Y))ᶜ) ∘ f.domainHomeomorph)
  exact (OnePoint.finitePartHomeomorph (X := Y)).symm.isProperMap.comp
    (hrestricted.comp f.domainHomeomorph.isProperMap)

end Proper

end PointedOnePointMap


namespace PointedOnePointMap

variable {X : Type uX} {Y : Type uY}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Specify a subset `U ⊆ X` and a continuous map `g : U → Y`.

The finite map, extended by infinity off its supplied domain and at infinity. -/
def openProperExtensionFun (U : Set X) (g : C(U, Y)) : OnePoint X → OnePoint Y := by
  classical
  exact fun p => p.elim ∞ (fun x => if hx : x ∈ U then (g ⟨x, hx⟩ : OnePoint Y) else ∞)

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Specify a subset `U ⊆ X` and a continuous map `g : U → Y`.

A finite target subset pulls back to the open-domain map's finite preimage. -/
theorem openProperExtensionFun_preimage (U : Set X) (g : C(U, Y))
    (s : Set (OnePoint Y)) (hs : ∞ ∉ s) :
    openProperExtensionFun U g ⁻¹' s =
      ((↑) : X → OnePoint X) '' (Subtype.val '' (g ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' s))) := by
  ext p
  cases p using OnePoint.rec with
  | infty =>
      constructor
      · intro hp
        change openProperExtensionFun U g ∞ ∈ s at hp
        exact (hs (by simpa only [openProperExtensionFun, OnePoint.elim_infty] using hp)).elim
      · intro hp
        exact (OnePoint.infty_notMem_image_coe hp).elim
  | coe x =>
      constructor
      · intro hp
        change openProperExtensionFun U g (x : OnePoint X) ∈ s at hp
        by_cases hx : x ∈ U
        · refine ⟨x, ⟨⟨x, hx⟩, ?_, rfl⟩, rfl⟩
          change (g ⟨x, hx⟩ : OnePoint Y) ∈ s
          simpa only [openProperExtensionFun, OnePoint.elim_some, dite_eq_left hx] using hp
        · exact (hs (by simpa only [openProperExtensionFun, OnePoint.elim_some, dite_eq_right hx]
            using hp)).elim
      · rintro ⟨z, ⟨u, hu, huz⟩, hzx⟩
        have hux : (u : X) = x := huz.trans (OnePoint.coe_injective hzx)
        rw [← hux]
        change openProperExtensionFun U g ((u : X) : OnePoint X) ∈ s
        change (g u : OnePoint Y) ∈ s at hu
        simpa only [openProperExtensionFun, OnePoint.elim_some, dite_eq_left u.property, Subtype.eta]
          using hu

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`.

Proper compact preimages and an open domain make the infinity extension continuous. -/
theorem openProperExtensionFun_continuous [T2Space X]
    (U : Set X) (hU : IsOpen U) (g : C(U, Y)) (hg : IsProperMap g) :
    Continuous (openProperExtensionFun U g) := by
  apply continuous_iff_isClosed.mpr
  intro s hs
  by_cases hinfty : ∞ ∈ s
  · have hopen : IsOpen (g ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' sᶜ)) :=
      (hs.isOpen_compl.preimage OnePoint.continuous_coe).preimage g.continuous
    have himage : IsOpen (Subtype.val '' (g ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' sᶜ))) :=
      hU.isOpenMap_subtype_val _ hopen
    have hpre : IsOpen (openProperExtensionFun U g ⁻¹' sᶜ) := by
      rw [openProperExtensionFun_preimage U g sᶜ (by intro h; exact h hinfty)]
      exact OnePoint.isOpen_image_coe.mpr himage
    exact isOpen_compl_iff.mp (by simpa only [preimage_compl] using hpre)
  · have hcompact : IsCompact (((↑) : Y → OnePoint Y) ⁻¹' s) :=
      ((OnePoint.isClosed_iff_of_notMem hinfty).mp hs).2
    have hdomain : IsCompact (g ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' s)) :=
      hg.isCompact_preimage hcompact
    have himage : IsCompact (Subtype.val '' (g ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' s))) :=
      hdomain.image continuous_subtype_val
    rw [openProperExtensionFun_preimage U g s hinfty]
    exact OnePoint.isClosed_image_coe.mpr ⟨himage.isClosed, himage⟩

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`.

Extend the proper map on an open subset by infinity outside that subset. -/
def ofOpenProperMap [T2Space X] (U : Set X) (hU : IsOpen U)
    (g : C(U, Y)) (hg : IsProperMap g) : PointedOnePointMap X Y where
  extension := ⟨openProperExtensionFun U g, openProperExtensionFun_continuous U hU g hg⟩
  map_infty := rfl

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`.

The extension retains every finite value on the open domain. -/
theorem ofOpenProperMap_extension_coe [T2Space X] (U : Set X) (hU : IsOpen U)
    (g : C(U, Y)) (hg : IsProperMap g) (x : U) :
    (ofOpenProperMap U hU g hg).extension (x : X) = (g x : OnePoint Y) := by
  change openProperExtensionFun U g ((x : X) : OnePoint X) = (g x : OnePoint Y)
  simp only [openProperExtensionFun, OnePoint.elim_some, dite_eq_left x.property, Subtype.eta]

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`.

Every point outside the supplied open domain is sent to infinity. -/
theorem ofOpenProperMap_extension_of_notMem [T2Space X] (U : Set X) (hU : IsOpen U)
    (g : C(U, Y)) (hg : IsProperMap g) (x : X) (hx : x ∉ U) :
    (ofOpenProperMap U hU g hg).extension x = ∞ := by
  change openProperExtensionFun U g (x : OnePoint X) = ∞
  simp only [openProperExtensionFun, OnePoint.elim_some, dite_eq_right hx]

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`.

Recover the exact open subset from the extension's finite-value locus. -/
theorem domain_ofOpenProperMap [T2Space X] (U : Set X) (hU : IsOpen U)
    (g : C(U, Y)) (hg : IsProperMap g) :
    (ofOpenProperMap U hU g hg).domain = U := by
  ext x
  by_cases hx : x ∈ U <;>
    simp [domain, ofOpenProperMap, openProperExtensionFun, hx]

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`.

Recover the map after transporting along the exact domain equality. -/
theorem partialMap_ofOpenProperMap [T2Space X] (U : Set X) (hU : IsOpen U)
    (g : C(U, Y)) (hg : IsProperMap g) :
    (ofOpenProperMap U hU g hg).partialMap.comp
      (⟨(Homeomorph.setCongr (domain_ofOpenProperMap U hU g hg)).symm,
        (Homeomorph.setCongr (domain_ofOpenProperMap U hU g hg)).symm.continuous⟩) = g := by
  apply ContinuousMap.ext
  intro x
  apply OnePoint.coe_injective
  rw [ContinuousMap.comp_apply, partialMap_coe]
  change (ofOpenProperMap U hU g hg).extension (x : X) = (g x : OnePoint Y)
  exact ofOpenProperMap_extension_coe U hU g hg x

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Assume `Y` is locally compact and Hausdorff.

Reconstruct each pointed map from its open proper restriction. -/
theorem ofOpenProperMap_partialMap [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    (f : PointedOnePointMap X Y) :
    ofOpenProperMap f.domain f.domain_isOpen f.partialMap f.partialMap_isProperMap = f := by
  apply ext_apply
  intro p
  cases p using OnePoint.rec with
  | infty => rw [(ofOpenProperMap _ _ _ _).map_infty, f.map_infty]
  | coe x =>
      by_cases hx : x ∈ f.domain
      · rw [ofOpenProperMap_extension_coe f.domain f.domain_isOpen f.partialMap
          f.partialMap_isProperMap ⟨x, hx⟩]
        exact f.partialMap_coe ⟨x, hx⟩
      · rw [ofOpenProperMap_extension_of_notMem f.domain f.domain_isOpen f.partialMap
          f.partialMap_isProperMap x hx]
        exact (f.outside_domain x hx).symm

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`. The compared pointed map has finite domain `U` and agrees with `g`
at every point of `U`.

Exact domain and finite values uniquely determine the pointed extension. -/
theorem ofOpenProperMap_unique [T2Space X] (U : Set X) (hU : IsOpen U)
    (g : C(U, Y)) (hg : IsProperMap g) (f : PointedOnePointMap X Y)
    (hdom : f.domain = U) (hvalue : ∀ x : U, (g x : OnePoint Y) = f.extension (x : X)) :
    f = ofOpenProperMap U hU g hg := by
  apply ext_apply
  intro p
  cases p using OnePoint.rec with
  | infty => rw [f.map_infty, (ofOpenProperMap _ _ _ _).map_infty]
  | coe x =>
      by_cases hx : x ∈ U
      · rw [ofOpenProperMap_extension_coe U hU g hg ⟨x, hx⟩]
        exact (hvalue ⟨x, hx⟩).symm
      · have hfx : x ∉ f.domain := by simpa only [hdom] using hx
        rw [f.outside_domain x hfx, ofOpenProperMap_extension_of_notMem U hU g hg x hx]

/-- Let `X`, `Y` be topological spaces. The pointed map is continuous on the one-point extensions
and preserves infinity. Assume `X` is Hausdorff. Specify an open subset `U ⊆ X` and a proper
continuous map `g : U → Y`.

Every proper continuous open-domain map has its unique pointed extension. -/
theorem existsUnique_ofOpenProperMap [T2Space X] (U : Set X) (hU : IsOpen U)
    (g : C(U, Y)) (hg : IsProperMap g) :
    ∃! f : PointedOnePointMap X Y, f.domain = U ∧
      ∀ x : U, (g x : OnePoint Y) = f.extension (x : X) := by
  refine ⟨ofOpenProperMap U hU g hg, ⟨domain_ofOpenProperMap U hU g hg, ?_⟩, ?_⟩
  · intro x
    exact (ofOpenProperMap_extension_coe U hU g hg x).symm
  · intro f hf
    exact ofOpenProperMap_unique U hU g hg f hf.1 hf.2

end PointedOnePointMap

end
