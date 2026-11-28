/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Closed-set gluing for colimits with finitely many objects

Let F : J ⥤ TopCat and c a cocone, with J having finitely many objects. If the underlying set
cocone is colimiting and each leg is a closed embedding, c is a topological colimit. A subset
of its vertex is closed exactly when its preimage along every leg is closed: the converse
follows from the finite union of the closed leg images of those preimages.

For a map f from a colimit vertex, the range and every subset image are unions of their images
along the cocone legs. Finitely many closed-embedding composites make range(f) closed. If c is
a topological colimit and f is globally injective, those composites also determine the induced
topology, hence f is a closed embedding. The space, indexing-object and indexing-morphism
universes are independent.
-/

@[expose] public section

universe v u w

open CategoryTheory Limits Topology

namespace TopCat

section FiniteClosedColimit

variable {J : Type v} [Category.{w} J] [Finite J]
variable {F : J ⥤ TopCat.{u}} (c : Cocone F)

omit [Finite J] in
/-- Closed sets in a supremum of coinduced cocone topologies.

For any index category J and cocone c, a subset S is closed in the topology sup_j
coinduced(c.ι_j) exactly when every preimage c.ι_j⁻¹(S) is closed in F(j). No finiteness or
colimit assumption is needed. -/
lemma isClosed_sup_coinduced_iff (S : Set c.pt) :
    @IsClosed _ (⨆ j, (F.obj j).str.coinduced (c.ι.app j : F.obj j → c.pt)) S ↔
      ∀ j, IsClosed ((c.ι.app j : F.obj j → c.pt) ⁻¹' S) := by
  simp [isClosed_iSup_iff, isClosed_coinduced]

omit [Finite J] in
/-- Subset cover by traces along a set-colimit cocone.

If the underlying set cocone of c is colimiting, every S ⊆ c.pt satisfies S = ⋃_j
c.ι_j(c.ι_j⁻¹(S)). This uses joint surjectivity of the legs and allows any index category. -/
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

/-- Closed-set gluing along finitely many closed cocone embeddings.

Assume J has finitely many objects, the underlying set cocone is colimiting and every leg is a
closed embedding. If every leg preimage of S is closed, then S is closed in c.pt, as the
finite union of the corresponding closed images. -/
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

/-- Topological colimit from a set colimit and closed embedding legs.

For a cocone over a category J with finitely many objects, a colimit after forgetting to sets
and closed embedding of every leg imply IsColimit c in TopCat. Their closed-set gluing
identifies the vertex topology with the final cocone topology. -/
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
## Descent of closed embeddings from a finite-object colimit

Let c be a topological colimit over a category with finitely many objects and f : c.pt → Y a
continuous map. Suppose every c.ι_j ≫ f is a closed embedding and f is injective. The colimit
topology detects closed sets through the legs, and a closed subset S has f(S) equal to the
finite union of its closed component images. Since S=f⁻¹(f(S)), the source topology is induced
by f.

The range of f is also the finite union of the composite ranges, so it is closed. These two
conclusions give a closed embedding. The range-closedness conclusion alone uses the underlying
set colimit and the composite closed embeddings, without global injectivity.
-/

section Descent

variable {Y : TopCat.{u}} (f : c.pt ⟶ Y)

omit [Finite J] in
/-- Range cover by composites with set-colimit legs.

For a map f : c.pt → Y and an underlying set colimit, range(f) = ⋃_j range(c.ι_j ≫ f). The
identity does not require a finite object set. -/
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
/-- Subset-image cover by composites with set-colimit legs.

For an underlying set colimit and S ⊆ c.pt, f(S) = ⋃_j (c.ι_j ≫ f)(c.ι_j⁻¹(S)). This holds for
any indexing category and continuous map f. -/
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

/-- Closed range from finitely many closed composite embeddings.

Assume J has finitely many objects, the underlying set cocone is colimiting and each c.ι_j ≫ f
is a closed embedding. Then range(f) is closed, as the finite union of the closed composite
ranges. -/
lemma isClosed_range_of_isColimit
    (hcType : IsColimit ((forget TopCat).mapCocone c))
    (hf : ∀ j, IsClosedEmbedding (c.ι.app j ≫ f : F.obj j → Y)) :
    IsClosed (Set.range (f : c.pt → Y)) := by
  rw [range_eq_biUnion_range_comp (c := c) (f := f) hcType]
  exact isClosed_iUnion_of_finite fun j => (hf j).isClosed_range

/-- Inducing topology from a finite-object colimit and composite closed embeddings.

For a topological colimit c over J with finitely many objects, if f is injective and every
c.ι_j ≫ f is a closed embedding, then f is inducing. Closed sets are detected on the legs and
reconstructed as preimages of their closed images under f. -/
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

/-- Embedding descended from composite closed embeddings.

For a finite-object topological colimit c, a globally injective f with all c.ι_j ≫ f closed
embeddings is an embedding, combining the induced-topology conclusion with injectivity. -/
lemma isEmbedding_of_isColimit
    (hc : IsColimit c)
    (hinj : Function.Injective (f : c.pt → Y))
    (hf : ∀ j, IsClosedEmbedding (c.ι.app j ≫ f : F.obj j → Y)) :
    IsEmbedding (f : c.pt → Y) :=
  ⟨isInducing_of_isColimit (c := c) (f := f) hc hinj hf, hinj⟩

/-- Closed embedding descended from a finite-object topological colimit.

Let c be a topological colimit over J with finitely many objects. If f : c.pt → Y is injective
and every composite with a cocone leg is a closed embedding, then f is a closed embedding. Its
topology is induced and its range is closed by the finite union formula. -/
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
