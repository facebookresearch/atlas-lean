/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Finite closed-colimit gluing in `TopCat`

Reusable finite gluing: a finite `TopCat` cocone whose underlying
`Type` cocone is colimiting and whose legs are closed embeddings is
colimiting in `TopCat`. Built from `TopCat.nonempty_isColimit_iff_eq_coinduced`,
`Types.jointly_surjective_of_isColimit`, finite closed unions, and
`Topology.IsClosedEmbedding`. Diagram-specific boundary/horn facts live
outside this file.

Additionally provides the generic finite closed-colimit descent for a
map out of a colimit: if `c` is a finite colimit cocone and each
composite `c.ι ≫ f` is a closed embedding, then `f` is a closed
embedding once global injectivity is supplied. The inducing part uses
the sup-coinduced colimit topology (`nonempty_isColimit_iff_eq_coinduced`
/ `coinduced_of_isColimit` + `isClosed_sup_coinduced_iff` /
`isClosed_iff_of_isColimit` via `TopologicalSpace.ext_isClosed`); the
closed-range part uses the finite union of the composite ranges
(`Types.jointly_surjective_of_isColimit` for the cover
`S = ⋃ ι '' (ι⁻¹' S)` / `range f = ⋃ range (f∘ι)` and
`isClosed_iUnion_of_finite` + `IsClosedEmbedding.isClosedMap` /
`isClosed_range`). Finiteness is necessary for the finite closed union;
global injectivity (or an equivalent separation hypothesis) is necessary
to recover `S = f⁻¹' (f '' S)` and `range f = ⋃ range (f∘ι)` as a
closed set without collapsing fibers; the legwise closed-embedding
hypothesis is necessary to obtain closed images of preimages.
-/

@[expose] public section

universe v u w

open CategoryTheory Limits Topology

namespace TopCat

section FiniteClosedColimit

variable {J : Type v} [Category.{w} J] [Finite J]
variable {F : J ⥤ TopCat.{u}} (c : Cocone F)

omit [Finite J] in
/-- Closed sets in the sup-coinduced topology are those whose preimages are
closed. This is `isClosed_iSup_iff` + `isClosed_coinduced` for the
colimit coinduced family. -/
lemma isClosed_sup_coinduced_iff (S : Set c.pt) :
    @IsClosed _ (⨆ j, (F.obj j).str.coinduced (c.ι.app j : F.obj j → c.pt)) S ↔
      ∀ j, IsClosed ((c.ι.app j : F.obj j → c.pt) ⁻¹' S) := by
  simp [isClosed_iSup_iff, isClosed_coinduced]

omit [Finite J] in
/-- Covering equality for a Type-colimit cocone: every subset is the union of
its trace on each leg. Uses `Types.jointly_surjective_of_isColimit` for the
underlying `Type` cocone to get `⋃ range = univ` and hence
`S = ⋃ j, ι j '' (ι j ⁻¹' S)`. -/
lemma coconePoint_cover_eq_biUnion_images
    (hcType : IsColimit ((forget TopCat).mapCocone c))
    (S : Set c.pt) :
    S = ⋃ j, (c.ι.app j : F.obj j → c.pt) '' ((c.ι.app j : F.obj j → c.pt) ⁻¹' S) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
  constructor
  · intro hx
    obtain ⟨j, y, rfl⟩ :=
      CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hcType x
    exact ⟨j, y, by simpa [hx], rfl⟩
  · rintro ⟨j, y, hy, rfl⟩
    exact hy

/-- If each leg is a closed embedding and each preimage is closed, the set
itself is closed. Write `S` as the finite union of closed images via the
cover equality, using `IsClosedEmbedding.isClosedMap` and
`isClosed_iUnion_of_finite` for the finite index. -/
lemma isClosed_of_forall_preimage_isClosed
    (hcType : IsColimit ((forget TopCat).mapCocone c))
    (hclosed : ∀ j, IsClosedEmbedding (c.ι.app j : F.obj j → c.pt))
    {S : Set c.pt} (hS : ∀ j, IsClosed ((c.ι.app j : F.obj j → c.pt) ⁻¹' S)) :
    IsClosed S := by
  have hEq := coconePoint_cover_eq_biUnion_images c hcType S
  rw [hEq]
  have hIm : ∀ j,
      IsClosed ((c.ι.app j : F.obj j → c.pt) '' ((c.ι.app j : F.obj j → c.pt) ⁻¹' S)) :=
    fun j => (hclosed j).isClosedMap _ (hS j)
  exact isClosed_iUnion_of_finite hIm

/-- Finite closed-gluing: a finite `TopCat` cocone is colimiting when
its image in `Type` is colimiting and each leg is a closed embedding.
The statement is the reusable packet for both realized boundary and horn
comparisons, via `nonempty_isColimit_iff_eq_coinduced` reduced to the
topology equality `c.pt.str = ⨆ coinduced` proved by closed-set
extensionality `TopologicalSpace.ext_isClosed` with
`isClosed_sup_coinduced_iff`. The forward direction is the direct
continuity preimage `hS.preimage (c.ι.app j).hom.continuous`; the
converse uses finite gluing `isClosed_of_forall_preimage_isClosed`.
Keep diagram-specific facts out of this file. -/
noncomputable def isColimit_of_isColimit_forget_of_isClosedEmbedding
    (hcType : IsColimit ((forget TopCat).mapCocone c))
    (hclosed : ∀ j, IsClosedEmbedding (c.ι.app j : F.obj j → c.pt)) :
    IsColimit c := by
  apply Nonempty.some
  rw [nonempty_isColimit_iff_eq_coinduced c hcType]
  apply TopologicalSpace.ext_isClosed
  intro S
  constructor
  · intro hS
    exact (isClosed_sup_coinduced_iff c S).2 fun j =>
      hS.preimage (c.ι.app j).hom.continuous
  · intro hS
    exact isClosed_of_forall_preimage_isClosed c hcType hclosed
      ((isClosed_sup_coinduced_iff c S).1 hS)

/-!
### Generic finite closed-colimit descent

For a finite colimit cocone `c` over `F : J ⥤ TopCat`, a map
`f : c.pt ⟶ Y` whose composites `c.ι ≫ f` are all closed embeddings is
itself a closed embedding once global injectivity is supplied.

* Inducing part: `c.pt.str = ⨆ coinduced (c.ι)` from
  `nonempty_isColimit_iff_eq_coinduced` / `coinduced_of_isColimit` and
  `isClosed_sup_coinduced_iff` (`isClosed_iff_of_isColimit`), compared
  with the induced topology `induced f` via `TopologicalSpace.ext_isClosed`
  and `isClosed_induced_iff`. For `S ⊆ c.pt`, `IsClosed S` in the
  colimit topology is `∀ j, IsClosed (ι⁻¹' S)`. With `f` injective,
  `ι⁻¹' S = (f∘ι)⁻¹' (f '' S)`, and with each `f∘ι` a closed embedding,
  `IsClosed (ι⁻¹' S)` is equivalent to `IsClosed ((f∘ι) '' (ι⁻¹' S))`.
  The finite union `f '' S = ⋃ (f∘ι) '' (ι⁻¹' S)` (via
  `coconePoint_cover_eq_biUnion_images` / `Types.jointly_surjective_of_isColimit`
  and `isClosed_iUnion_of_finite`) is then closed, giving
  `S = f⁻¹' (f '' S)` with closed `f '' S`, i.e. `S` is induced-closed.
* Closed-range part: `range f = ⋃ range (f∘ι)` (joint surjectivity of the
  Type-colimit) is a finite union of the closed ranges of the
  `f∘ι` (`IsClosedEmbedding.isClosed_range` + `isClosed_iUnion_of_finite`).

Hypothesis necessity (documented for the strongest sound signature that
`4.33` supports):
* `Finite J` – needed for `isClosed_iUnion_of_finite`; an infinite
  coproduct of closed embeddings need not have closed range (e.g. infinite
  discrete `∐ {pt} → ℝ` accumulating).
* `IsColimit c` (equivalently `c.pt.str = ⨆ coinduced` given the
  Type-colimit) – needed to identify closed sets with
  `∀ j, IsClosed (ι⁻¹' S)` via `nonempty_isColimit_iff_eq_coinduced`;
  without the colimit topology the gluing need not be inducing (e.g.
  indiscrete vs. colimit topology on same point set).
* `∀ j, IsClosedEmbedding (c.ι ≫ f)` – needed to promote
  `IsClosed (ι⁻¹' S)` to `IsClosed ((f∘ι) '' (ι⁻¹' S))` via
  `IsClosedEmbedding.isClosedMap`; without legwise closedness the finite
  union need not be closed.
* `Function.Injective f` (or an equivalent precise separation hypothesis
  such as `IsEmbedding f` or `IsInducing f ∧ Injective`) – needed for
  `S = f⁻¹' (f '' S)` and for `IsClosedEmbedding` to be possible at all;
  collapsing example: `J = discrete 2`, `F _ = ⊤` (singleton), `c.pt = 2`,
  `Y = ⊤`, `f` collapses both points, each `f∘ι` is a closed embedding
  (singleton → point) but `f` is not injective and not a closed embedding.
  The lemma is scaffold-free and generic over any finite `J`; it does not
  specialize to simplicial boundaries.
-/

section Descent

variable {Y : TopCat.{u}} (f : c.pt ⟶ Y)

omit [Finite J] in
/-- Range of `f` is the finite union of the ranges of the composites
`c.ι ≫ f`, via `Types.jointly_surjective_of_isColimit`. -/
lemma range_eq_biUnion_range_comp
    (hcType : IsColimit ((forget TopCat).mapCocone c)) :
    Set.range (f : c.pt → Y) = ⋃ j, Set.range (c.ι.app j ≫ f : F.obj j → Y) := by
  ext y
  simp only [Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨j, z, rfl⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hcType x
    exact ⟨j, z, rfl⟩
  · rintro ⟨j, z, rfl⟩
    exact ⟨(c.ι.app j) z, rfl⟩

omit [Finite J] in
/-- Image of an arbitrary `S ⊆ c.pt` under `f` is the finite union of the
images of its traces, via the colimit cover. -/
lemma image_eq_biUnion_image_comp_preimage
    (hcType : IsColimit ((forget TopCat).mapCocone c))
    (S : Set c.pt) :
    (f : c.pt → Y) '' S =
      ⋃ j, (c.ι.app j ≫ f : F.obj j → Y) '' ((c.ι.app j : F.obj j → c.pt) ⁻¹' S) := by
  ext y
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, z, rfl⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hcType x
    exact ⟨j, z, hx, rfl⟩
  · rintro ⟨j, z, hz, rfl⟩
    exact ⟨(c.ι.app j) z, hz, rfl⟩

/-- Closed range: `range f` is a finite union of the closed ranges of the
`f∘ι`. Uses `range_eq_biUnion_range_comp` and `isClosed_iUnion_of_finite`. -/
lemma isClosed_range_of_isColimit
    (hcType : IsColimit ((forget TopCat).mapCocone c))
    (hf : ∀ j, IsClosedEmbedding (c.ι.app j ≫ f : F.obj j → Y)) :
    IsClosed (Set.range (f : c.pt → Y)) := by
  rw [range_eq_biUnion_range_comp (c := c) (f := f) hcType]
  exact isClosed_iUnion_of_finite fun j => (hf j).isClosed_range

/-- Inducing part of descent: `f` is inducing when `c` is colimiting,
`f` is globally injective, and each `f∘ι` is a closed embedding.
Proved by `TopologicalSpace.ext_isClosed` comparing `c.pt.str` with
`induced f`: the colimit side is `∀ j, IsClosed (ι⁻¹' S)` via
`nonempty_isColimit_iff_eq_coinduced` / `isClosed_sup_coinduced_iff`
(`isClosed_iff_of_isColimit`), the induced side is
`∃ T closed, S = f⁻¹' T` via `isClosed_induced_iff`; the bridge is
`S = f⁻¹' (f '' S)` (injectivity) and
`f '' S = ⋃ (f∘ι) '' (ι⁻¹' S)` (joint surjectivity + cover) which is
closed as a finite union of `IsClosedEmbedding.isClosedMap` images. -/
lemma isInducing_of_isColimit
    (hc : IsColimit c)
    (hinj : Function.Injective (f : c.pt → Y))
    (hf : ∀ j, IsClosedEmbedding (c.ι.app j ≫ f : F.obj j → Y)) :
    IsInducing (f : c.pt → Y) := by
  have hcType : IsColimit ((forget TopCat).mapCocone c) :=
    isColimitOfPreserves (forget TopCat) hc
  have h_sup : c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j : F.obj j → c.pt) :=
    ((TopCat.nonempty_isColimit_iff_eq_coinduced c hcType).mp ⟨hc⟩)
  have h_eq : (inferInstance : TopologicalSpace c.pt) =
      TopologicalSpace.induced (f : c.pt → Y) (inferInstance : TopologicalSpace Y) := by
    apply TopologicalSpace.ext_isClosed
    intro S
    have h_orig : IsClosed (S : Set c.pt) ↔
        ∀ j, IsClosed ((c.ι.app j : F.obj j → c.pt) ⁻¹' S) := by
      rw [h_sup]
      exact isClosed_sup_coinduced_iff c S
    have h_induced :
        IsClosed[TopologicalSpace.induced (f : c.pt → Y) inferInstance] (S : Set c.pt) ↔
        ∃ T : Set Y, IsClosed T ∧ (f : c.pt → Y) ⁻¹' T = S := by
      exact isClosed_induced_iff
    constructor
    · intro hS
      rw [h_induced]
      refine ⟨(f : c.pt → Y) '' S, ?_, ?_⟩
      · have hS_pre : ∀ j, IsClosed ((c.ι.app j : F.obj j → c.pt) ⁻¹' S) :=
          h_orig.mp hS
        have h_image_eq := image_eq_biUnion_image_comp_preimage (c := c) (f := f) hcType S
        rw [h_image_eq]
        exact isClosed_iUnion_of_finite fun j => (hf j).isClosedMap _ (hS_pre j)
      · exact Set.preimage_image_eq S hinj
    · intro hS
      rw [h_induced] at hS
      obtain ⟨T, hT, hT_eq⟩ := hS
      rw [← hT_eq]
      exact hT.preimage f.hom.continuous
      -- alternative route via h_orig: each (f∘ι)⁻¹' T is closed, hence ∀ j, IsClosed (ι⁻¹' S)
      -- follows from continuity of f∘ι and hT, giving IsClosed S via h_orig.mpr.
      -- The preimage argument above is the direct continuity proof.
  exact ⟨h_eq⟩

/-- Embedding part: `IsInducing + Injective`. -/
lemma isEmbedding_of_isColimit
    (hc : IsColimit c)
    (hinj : Function.Injective (f : c.pt → Y))
    (hf : ∀ j, IsClosedEmbedding (c.ι.app j ≫ f : F.obj j → Y)) :
    IsEmbedding (f : c.pt → Y) :=
  ⟨isInducing_of_isColimit (c := c) (f := f) hc hinj hf, hinj⟩

/-- Generic finite closed-colimit descent: a map out of a finite
`TopCat` colimit whose composites with the colimit legs are closed
embeddings is itself a closed embedding once it is globally injective.
The proof splits as the inducing part (`isInducing_of_isColimit` via the
sup-coinduced topology) and the closed-range part
(`isClosed_range_of_isColimit` via the finite union of composite ranges).
This is the smallest reusable current-Mathlib lemma that closes the
boundary worker's genuine API gap without specializing to simplicial
boundaries; `Boundary.lean` is untouched in this worker. -/
theorem isClosedEmbedding_of_isColimit
    (hc : IsColimit c)
    (hinj : Function.Injective (f : c.pt → Y))
    (hf : ∀ j, IsClosedEmbedding (c.ι.app j ≫ f : F.obj j → Y)) :
    IsClosedEmbedding (f : c.pt → Y) where
  toIsEmbedding := isEmbedding_of_isColimit (c := c) (f := f) hc hinj hf
  isClosed_range := by
    have hcType : IsColimit ((forget TopCat).mapCocone c) :=
      isColimitOfPreserves (forget TopCat) hc
    exact isClosed_range_of_isColimit (c := c) (f := f) hcType hf

end Descent

end FiniteClosedColimit

end TopCat
