/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Types.Monomorphisms
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingTransfinite

/-!
# Closed T1-embeddings in `TopCat`

A closed T1-embedding is a closed embedding `f : X → Y` satisfying the
standard relative-T1 condition: every point of the codomain outside the
range is closed as a singleton. Explicitly,
`∀ y ∉ Set.range f, IsClosed ({y} : Set Y)`.

This strengthens `Topology.IsClosedEmbedding` by requiring the complement
of the image to be T1 pointwise; points inside the image need not have
closed singletons unless the domain is T1. The morphism property
`TopCat.closedT1Embeddings` is defined via `IsClosedT1Embedding` on the
underlying map, with thin adapters for `IsMultiplicative` and
`RespectsIso` over the `IsClosedT1Embedding` APIs (`id`, `comp`,
`Homeomorph.isClosedT1Embedding`). Comparison lemmas to
`TopCat.closedEmbeddings` and to the native monomorphism property are
provided.

Finite-set consequence: any finite set disjoint from the range is closed,
as a finite union of closed singletons (`Set.Finite.isClosed_biUnion`).

Stability: `closedT1Embeddings` is stable under cobase change (pushout)
via the modern `Limits.Types` pushout APIs for closed embeddings
(`TopCat.isClosedEmbedding_of_isPushout`) plus the relative-T1
singleton argument, and stable under transfinite composition
(and hence sequential colimits) via `TopCat.isClosed_iff_of_isColimit`,
`Types.FilteredColimit.isColimit_eq_iff'`, and `SuccOrder.limitRecOn`,
as needed by `TopSmallObjectCardinal`. No cofibration, model-structure,
or realization results are duplicated.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

/-! ### Sierpinski test space for the T1 pushout argument -/

private inductive SierpinskiTest : Type u where
  | bot : SierpinskiTest
  | top : SierpinskiTest
  deriving DecidableEq

private instance : TopologicalSpace (SierpinskiTest : Type u) where
  IsOpen s := s = ∅ ∨ s = ({SierpinskiTest.top} : Set SierpinskiTest) ∨ s = Set.univ
  isOpen_univ := Or.inr (Or.inr rfl)
  isOpen_inter s t hs ht := by
    rcases hs with rfl | rfl | rfl
    · simp
    · rcases ht with rfl | rfl | rfl
      · simp
      · simp
      · simp
    · rcases ht with rfl | rfl | rfl
      · simp
      · simp
      · simp
  isOpen_sUnion S hS := by
    have h_mem : ∀ s ∈ S, s = ∅ ∨ s = ({SierpinskiTest.top} : Set SierpinskiTest) ∨
      s = Set.univ := hS
    by_cases h_univ : (Set.univ : Set SierpinskiTest) ∈ S
    · have h_eq : ⋃₀ S = Set.univ := by
        ext x
        simp only [Set.mem_sUnion]
        constructor
        · intro _; trivial
        · intro _; exact ⟨Set.univ, h_univ, trivial⟩
      rw [h_eq]
      right; right; rfl
    · by_cases h_top : ({SierpinskiTest.top} : Set SierpinskiTest) ∈ S
      · have h_eq : ⋃₀ S = ({SierpinskiTest.top} : Set SierpinskiTest) := by
          ext x
          simp only [Set.mem_sUnion, Set.mem_singleton_iff]
          constructor
          · rintro ⟨s, hs, hx⟩
            have hs_eq := h_mem s hs
            rcases hs_eq with rfl | rfl | rfl
            · simp at hx
            · exact hx
            · exfalso; exact h_univ hs
          · intro hx
            exact ⟨{SierpinskiTest.top}, h_top, hx⟩
        rw [h_eq]
        right; left; rfl
      · have h_eq : ⋃₀ S = ∅ := by
          ext x
          simp only [Set.mem_sUnion, Set.mem_empty_iff_false]
          constructor
          · rintro ⟨s, hs, hx⟩
            have hs_eq := h_mem s hs
            rcases hs_eq with rfl | rfl | rfl
            · simp at hx
            · exact absurd hs h_top
            · exact absurd hs h_univ
          · intro hx
            simp at hx
        rw [h_eq]
        left; rfl

private def sierpinskiTopCat : TopCat.{u} := TopCat.of (SierpinskiTest : Type u)

namespace Topology

/-- A closed T1-embedding is a closed embedding `f : X → Y` such that every
point of the codomain outside the range is closed. This is the standard
relative-T1 condition: `∀ y ∉ Set.range f, IsClosed ({y} : Set Y)`. -/
@[fun_prop, mk_iff]
structure IsClosedT1Embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop extends IsClosedEmbedding f where
  isClosed_singleton_of_notMem_range : ∀ y, y ∉ Set.range f → IsClosed ({y} : Set Y)

namespace IsClosedT1Embedding

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {g : Y → Z}

@[fun_prop]
theorem isClosedEmbedding (hf : IsClosedT1Embedding f) : IsClosedEmbedding f :=
  hf.toIsClosedEmbedding

theorem isEmbedding (hf : IsClosedT1Embedding f) : IsEmbedding f :=
  hf.toIsClosedEmbedding.toIsEmbedding

theorem isInducing (hf : IsClosedT1Embedding f) : IsInducing f :=
  hf.isEmbedding.isInducing

theorem continuous (hf : IsClosedT1Embedding f) : Continuous f :=
  hf.isEmbedding.continuous

protected theorem id : IsClosedT1Embedding (id : X → X) where
  toIsClosedEmbedding := IsClosedEmbedding.id
  isClosed_singleton_of_notMem_range := by
    intro y hy
    exfalso
    exact hy ⟨y, rfl⟩

theorem comp (hg : IsClosedT1Embedding g) (hf : IsClosedT1Embedding f) :
    IsClosedT1Embedding (g ∘ f) where
  toIsClosedEmbedding := hg.toIsClosedEmbedding.comp hf.toIsClosedEmbedding
  isClosed_singleton_of_notMem_range := by
    intro z hz
    rw [Set.range_comp] at hz
    by_cases hzg : z ∈ Set.range g
    · obtain ⟨y, rfl⟩ := hzg
      have hy_notmem : y ∉ Set.range f := by
        intro hy_mem
        exact hz (Set.mem_image_of_mem g hy_mem)
      have hy_closed : IsClosed ({y} : Set Y) :=
        hf.isClosed_singleton_of_notMem_range y hy_notmem
      have hg_closedMap : IsClosedMap g := hg.toIsClosedEmbedding.isClosedMap
      have h_image_closed : IsClosed (g '' {y}) := hg_closedMap _ hy_closed
      simpa [Set.image_singleton] using h_image_closed
    · exact hg.isClosed_singleton_of_notMem_range z hzg

theorem isClosed_of_finite_disjoint_range (hf : IsClosedT1Embedding f)
    {s : Set Y} (hs : s.Finite) (hdisj : Disjoint s (Set.range f)) : IsClosed s := by
  have h_singleton : ∀ x ∈ s, IsClosed ({x} : Set Y) := by
    intro x hx
    exact hf.isClosed_singleton_of_notMem_range x ((Set.disjoint_left.mp hdisj) hx)
  have h_biUnion_closed : IsClosed (⋃ x ∈ s, ({x} : Set Y)) :=
    hs.isClosed_biUnion h_singleton
  simpa [Set.biUnion_of_singleton] using h_biUnion_closed

/-- Every homeomorphism is a closed T1-embedding. The range is `univ`, so the
relative-T1 condition holds vacuously. -/
theorem of_homeomorph (h : X ≃ₜ Y) : IsClosedT1Embedding (h : X → Y) where
  toIsClosedEmbedding := h.isClosedEmbedding
  isClosed_singleton_of_notMem_range := by
    intro y hy
    exfalso
    exact hy ⟨h.symm y, by simp⟩

alias homeomorph_isClosedT1Embedding := of_homeomorph

end IsClosedT1Embedding

end Topology

namespace TopCat

/-- Morphism property of being a closed T1-embedding in `TopCat`. -/
def closedT1Embeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f => Topology.IsClosedT1Embedding f.hom

@[simp]
lemma closedT1Embeddings_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedT1Embeddings f ↔ Topology.IsClosedT1Embedding f.hom :=
  Iff.rfl

@[simp]
lemma mem_closedT1Embeddings {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedT1Embeddings f ↔ Topology.IsClosedT1Embedding (f : X → Y) :=
  Iff.rfl

/-- Every closed T1-embedding is a closed embedding. This is the comparison
`closedT1Embeddings ≤ closedEmbeddings` (up to the definition of `closedEmbeddings`
as `IsClosedEmbedding` on the underlying map). -/
lemma closedT1Embeddings_le_isClosedEmbedding {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : closedT1Embeddings f) : IsClosedEmbedding f.hom :=
  hf.toIsClosedEmbedding

lemma closedT1Embeddings_le_closedEmbeddings :
    (closedT1Embeddings : MorphismProperty TopCat.{u}) ≤ closedEmbeddings :=
  fun _ _ _ hf => hf.toIsClosedEmbedding

lemma closedT1Embeddings_le_monomorphisms :
    (closedT1Embeddings : MorphismProperty TopCat.{u}) ≤
      CategoryTheory.MorphismProperty.monomorphisms TopCat := by
  intro X Y f hf
  exact (TopCat.mono_iff_injective f).mpr hf.injective

instance : closedT1Embeddings.IsMultiplicative where
  id_mem _ := Topology.IsClosedT1Embedding.id
  comp_mem _ _ hf hg := hg.comp hf

instance : closedT1Embeddings.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f _ =>
    Topology.IsClosedT1Embedding.of_homeomorph (TopCat.homeoOfIso (asIso f))

section CobaseChange

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- Pushout stability for closed T1-embeddings.

Reuses the accepted closed-embedding pushout theorem
`TopCat.isClosedEmbedding_of_isPushout` for the `IsClosedEmbedding`
half. For the relative-T1 condition, let `y ∈ X₄` with `y ∉ Set.range b`.
Then `b ⁻¹' {y} = ∅` and `(t ≫ r) ⁻¹' {y} = ∅` (since
`Set.range (t ≫ r) ⊆ Set.range b`), both closed. The remaining
preimage `r ⁻¹' {y}` is the fiber over `y` in `X₂`. Any `x ∈ r ⁻¹' {y}`
satisfies `x ∉ Set.range t` (otherwise `y = r (t s) = b (l s) ∈
Set.range b`), and `r` is injective on `X₂ \ Set.range t` – the
generating relation for the `Type` pushout only identifies
`inl (t s)` with `inr (l s)` – so `r ⁻¹' {y}` is at most a
singleton outside `Set.range t`. Hence it is either `∅` or `{x}` with
`x ∉ Set.range t`, closed by `ht`'s T1 condition. The three preimages
being closed gives `IsClosed {y}` in the colimit via
`TopCat.isClosed_iff_of_isColimit`. The complement-injectivity of `r`
is proved via the Sierpinski test space and the pushout universal
property. -/
lemma isClosedT1Embedding_of_isPushout (sq : IsPushout t l r b)
    (ht : Topology.IsClosedT1Embedding t.hom) :
    Topology.IsClosedT1Embedding b.hom where
  toIsClosedEmbedding := TopCat.isClosedEmbedding_of_isPushout sq ht.toIsClosedEmbedding
  isClosed_singleton_of_notMem_range := by
    intro y hy
    have hb_inj : Function.Injective b.hom := by
      have hMap : IsPushout ((forget TopCat).map t) ((forget TopCat).map l)
          ((forget TopCat).map r) ((forget TopCat).map b) :=
        sq.map (forget TopCat)
      exact CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit
        hMap.isColimit ht.injective
    have h_b_preimage : b.hom ⁻¹' ({y} : Set X₄) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      exact ⟨fun h => hy ⟨x, h⟩, fun h => False.elim h⟩
    have h_comp_range_subset : Set.range (t ≫ r).hom ⊆ Set.range b.hom := by
      intro y' hy'
      obtain ⟨s, hs⟩ := hy'
      have h_eq : (t ≫ r).hom s = (l ≫ b).hom s := by
        change (t ≫ r) s = (l ≫ b) s
        rw [sq.w]
      rw [h_eq] at hs
      exact ⟨l.hom s, hs⟩
    have h_comp_preimage : (t ≫ r).hom ⁻¹' ({y} : Set X₄) = ∅ := by
      ext s
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      exact ⟨fun h => hy (h_comp_range_subset ⟨s, h⟩), fun h => False.elim h⟩
    have h_r_preimage_closed : IsClosed (r.hom ⁻¹' ({y} : Set X₄)) := by
      have h_mem_outside : ∀ x ∈ r.hom ⁻¹' ({y} : Set X₄), x ∉ Set.range t.hom := by
        intro x hx
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
        intro hx_mem
        obtain ⟨s, rfl⟩ := hx_mem
        have h_y_eq : y = b.hom (l.hom s) := by
          calc y = r.hom (t.hom s) := hx.symm
            _ = (t ≫ r).hom s := rfl
            _ = (l ≫ b).hom s := by rw [sq.w]
            _ = b.hom (l.hom s) := rfl
        exact hy ⟨l.hom s, h_y_eq.symm⟩
      have h_subsingleton : Set.Subsingleton (r.hom ⁻¹' ({y} : Set X₄)) := by
        intro x₁ hx₁ x₂ hx₂
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx₁ hx₂
        have hx₁_out : x₁ ∉ Set.range t.hom := h_mem_outside x₁ (by simp [hx₁])
        have hx₂_out : x₂ ∉ Set.range t.hom := h_mem_outside x₂ (by simp [hx₂])
        have h_eq : r.hom x₁ = r.hom x₂ := by rw [hx₁, hx₂]
        have h_inj_compl : ∀ a₀ b₀ : X₂, a₀ ∉ Set.range t.hom → b₀ ∉ Set.range t.hom →
          r.hom a₀ = r.hom b₀ → a₀ = b₀ := by
          intro a₀ b₀ ha hb heq
          by_contra h_neq
          -- Sierpinski test space argument for complement injectivity.
          classical
          have : DecidableEq X₂ := Classical.typeDecidableEq X₂
          let S : TopCat.{u} := sierpinskiTopCat.{u}
          let f : X₂ ⟶ S :=
            TopCat.ofHom
              { toFun := fun x =>
                if x = a₀ then (SierpinskiTest.bot : SierpinskiTest)
                  else (SierpinskiTest.top : SierpinskiTest)
                continuous_toFun := by
                  have h_closed : IsClosed ({a₀} : Set X₂) :=
                    ht.isClosed_singleton_of_notMem_range a₀ ha
                  have h_open_compl : IsOpen ((Set.univ : Set X₂) \ {a₀}) := by
                    simpa [Set.compl_eq_univ_sdiff] using h_closed.isOpen_compl
                  rw [continuous_def]
                  intro s hs
                  have h_cases : s = ∅ ∨ s = ({SierpinskiTest.top} : Set SierpinskiTest) ∨
                    s = Set.univ := hs
                  rcases h_cases with rfl | rfl | rfl
                  · simp only [Set.preimage_empty]
                    exact isOpen_empty
                  · have h_eq_preimage :
                      (fun x : X₂ => if x = a₀ then (SierpinskiTest.bot : SierpinskiTest)
                        else (SierpinskiTest.top : SierpinskiTest)) ⁻¹'
                        ({SierpinskiTest.top} : Set SierpinskiTest) =
                      (Set.univ : Set X₂) \ {a₀} := by
                      ext x
                      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
                        Set.mem_univ, true_and, Set.mem_singleton_iff]
                      by_cases hxa : x = a₀
                      · simp [hxa]
                      · simp [hxa]
                    rw [h_eq_preimage]
                    exact h_open_compl
                  · simp only [Set.preimage_univ]
                    exact isOpen_univ }
          let g : X₃ ⟶ S :=
            TopCat.ofHom
              { toFun := fun _ => (SierpinskiTest.top : SierpinskiTest)
                continuous_toFun := continuous_const }
          have h_eq_fg : t ≫ f = l ≫ g := by
            apply ConcreteCategory.ext
            simp only [DFunLike.ext_iff, ← funext_iff]
            apply funext; intro s
            change (if t s = a₀ then (SierpinskiTest.bot : SierpinskiTest)
              else (SierpinskiTest.top : SierpinskiTest)) =
              (SierpinskiTest.top : SierpinskiTest)
            have h_ne : t s ≠ a₀ := by
              intro h_eq
              exact ha ⟨s, h_eq⟩
            rw [ite_eq_right h_ne]
          have h_fa : f.hom a₀ = SierpinskiTest.bot := by
            change (if a₀ = a₀ then (SierpinskiTest.bot : SierpinskiTest)
              else (SierpinskiTest.top : SierpinskiTest)) = SierpinskiTest.bot
            rw [ite_eq_left rfl]
          have h_fb : f.hom b₀ = SierpinskiTest.top := by
            change (if b₀ = a₀ then (SierpinskiTest.bot : SierpinskiTest)
              else (SierpinskiTest.top : SierpinskiTest)) = SierpinskiTest.top
            have hb_ne_a : b₀ ≠ a₀ := fun h_eq' => h_neq h_eq'.symm
            rw [ite_eq_right hb_ne_a]
          have h_bot_ne_top : SierpinskiTest.bot ≠ SierpinskiTest.top := by
            intro h
            cases h
          have h_f_eq : f.hom a₀ = f.hom b₀ := by
            let cone : PushoutCocone t l := PushoutCocone.mk f g h_eq_fg
            let h : X₄ ⟶ S := sq.isColimit.desc cone
            have h_r : r ≫ h = f := by
              have h1 := sq.isColimit.fac cone WalkingSpan.left
              exact h1
            have h_b : b ≫ h = g := by
              have h1 := sq.isColimit.fac cone WalkingSpan.right
              exact h1
            have h_r_a : h.hom (r.hom a₀) = f.hom a₀ := by
              have h_eq : (r ≫ h).hom a₀ = f.hom a₀ := by
                rw [show (r ≫ h).hom = f.hom from congrArg (fun (k : X₂ ⟶ S) => k.hom) h_r]
              exact h_eq
            have h_r_b : h.hom (r.hom b₀) = f.hom b₀ := by
              have h_eq : (r ≫ h).hom b₀ = f.hom b₀ := by
                rw [show (r ≫ h).hom = f.hom from congrArg (fun (k : X₂ ⟶ S) => k.hom) h_r]
              exact h_eq
            have h_r_eq : r.hom a₀ = r.hom b₀ := heq
            calc f.hom a₀ = h.hom (r.hom a₀) := h_r_a.symm
              _ = h.hom (r.hom b₀) := by rw [h_r_eq]
              _ = f.hom b₀ := h_r_b
          rw [h_fa, h_fb] at h_f_eq
          exact absurd h_f_eq h_bot_ne_top
        exact h_inj_compl x₁ x₂ hx₁_out hx₂_out h_eq
      rcases Set.eq_empty_or_nonempty (r.hom ⁻¹' ({y} : Set X₄)) with h_empty | h_nonempty
      · rw [h_empty]
        exact isClosed_empty
      · obtain ⟨x₀, hx₀⟩ := h_nonempty
        have h_eq_singleton : r.hom ⁻¹' ({y} : Set X₄) = {x₀} := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
          constructor
          · intro hx
            have hx_mem : x ∈ r.hom ⁻¹' ({y} : Set X₄) := hx
            exact h_subsingleton hx_mem hx₀
          · intro hx
            rw [hx, hx₀]
        rw [h_eq_singleton]
        exact ht.isClosed_singleton_of_notMem_range x₀ (h_mem_outside x₀ (by simp [hx₀]))
    have h_isColimit := sq.isColimit
    have h_transport : IsClosed ({y} : Set X₄) ↔ IsClosed ({y} : Set sq.cocone.pt) := by
      rfl
    have h_closed : IsClosed ({y} : Set X₄) := by
      rw [h_transport,
        TopCat.isClosed_iff_of_isColimit sq.cocone h_isColimit ({y} : Set sq.cocone.pt)]
      intro j
      cases j with
      | none =>
        change IsClosed ((t ≫ r).hom ⁻¹' ({y} : Set X₄))
        rw [h_comp_preimage]
        exact isClosed_empty
      | some x =>
        cases x with
        | left =>
          change IsClosed (r.hom ⁻¹' ({y} : Set X₄))
          exact h_r_preimage_closed
        | right =>
          change IsClosed (b.hom ⁻¹' ({y} : Set X₄))
          rw [h_b_preimage]
          exact isClosed_empty
    exact h_closed

instance : closedT1Embeddings.{u}.IsStableUnderCobaseChange where
  of_isPushout {A A' B B'} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
      (sq : IsPushout g f f' g') (hf : closedT1Embeddings f) :
      closedT1Embeddings f' :=
    isClosedT1Embedding_of_isPushout sq.flip hf

end CobaseChange

section Transfinite

universe v

open CategoryTheory.MorphismProperty

lemma closedT1Embeddings_le_inverseImage_monomorphisms :
    closedT1Embeddings.{u} ≤
      (MorphismProperty.monomorphisms (Type u)).inverseImage (forget TopCat.{u}) :=
  le_trans closedT1Embeddings_le_closedEmbeddings closedEmbeddings_le_inverseImage_monomorphisms

variable {J : Type v} [LinearOrder J]

private lemma isClosedT1Embedding_of_isIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f] :
    Topology.IsClosedT1Embedding f.hom :=
  Topology.IsClosedT1Embedding.of_homeomorph (TopCat.homeoOfIso (asIso f))

variable [OrderBot J]

private lemma isClosedT1Embedding_of_transfiniteCompositionOfShape_aux
    {X : J ⥤ TopCat.{u}} {c : Cocone X} (hc : IsColimit c)
    (hX : ∀ (j : J), Topology.IsClosedT1Embedding (X.map (homOfLE (bot_le : (⊥ : J) ≤ j))).hom)
    (h' : ∀ ⦃j j' : J⦄ (f : j ⟶ j'), Function.Injective (X.map f).hom) :
    Topology.IsClosedT1Embedding (c.ι.app (⊥ : J)).hom := by
  have inj (j : J) : Function.Injective (c.ι.app j).hom := fun x₁ x₂ h => by
    obtain ⟨k, g, hk⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
          (isColimitOfPreserves (forget TopCat.{u}) hc) _ _).1 h
    exact h' _ hk
  have hX_closed : ∀ (j : J), IsClosedEmbedding (X.map (homOfLE (bot_le : (⊥ : J) ≤ j))).hom :=
    fun j => (hX j).toIsClosedEmbedding
  have h_closedEmbedding : IsClosedEmbedding (c.ι.app (⊥ : J)).hom := by
    have closed {F : Set (X.obj ⊥)} (hF : IsClosed F) : IsClosed (c.ι.app (⊥ : J) '' F) := by
      rw [isClosed_iff_of_isColimit c hc]
      intro j
      have h_eq : (c.ι.app j).hom ⁻¹' (c.ι.app (⊥ : J) '' F) =
        (X.map (homOfLE (bot_le : (⊥ : J) ≤ j))).hom '' F := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, homOfLE_leOfHom]
        constructor
        · rintro ⟨y, hy, h⟩
          refine ⟨y, hy, inj _ ?_⟩
          rw [← h]
          exact ConcreteCategory.congr_hom
            ((forget TopCat.{u}).congr_map (c.w (homOfLE (bot_le : (⊥ : J) ≤ j)))) y
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, ConcreteCategory.congr_hom
            ((forget TopCat.{u}).congr_map (c.w (homOfLE (bot_le : (⊥ : J) ≤ j))).symm) y⟩
      rw [h_eq]
      exact (hX_closed j).isClosedMap _ hF
    refine
      { eq_induced := by
          rw [TopologicalSpace.ext_iff_isClosed]
          intro F
          simp only [isClosed_induced_iff]
          constructor
          · intro hF
            exact ⟨c.ι.app (⊥ : J) '' F, closed hF, (inj ⊥).preimage_image F⟩
          · rintro ⟨V, hV, rfl⟩
            exact IsClosed.preimage (by continuity) hV
        injective := inj ⊥
        isClosed_range := by simpa using closed isClosed_univ }
  refine ⟨h_closedEmbedding, ?_⟩
  intro y hy
  have h_y_closed : IsClosed ({y} : Set c.pt) := by
    rw [isClosed_iff_of_isColimit c hc]
    intro j
    have h_preimage_subsingleton : Set.Subsingleton ((c.ι.app j).hom ⁻¹' ({y} : Set c.pt)) := by
      intro x₁ hx₁ x₂ hx₂
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx₁ hx₂
      have h_eq : (c.ι.app j).hom x₁ = (c.ι.app j).hom x₂ := by rw [hx₁, hx₂]
      exact inj j h_eq
    have h_preimage_outside : ∀ x ∈ (c.ι.app j).hom ⁻¹' ({y} : Set c.pt),
        x ∉ Set.range (X.map (homOfLE (bot_le : (⊥ : J) ≤ j))).hom := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      intro hx_mem
      obtain ⟨x₀, hx₀⟩ := hx_mem
      have h_y_in_range : y ∈ Set.range (c.ι.app (⊥ : J)).hom := by
        have h_congr :
          (c.ι.app j).hom ((X.map (homOfLE (bot_le : (⊥ : J) ≤ j))).hom x₀) =
            (c.ι.app (⊥ : J)).hom x₀ := by
          have h_w := (forget TopCat.{u}).congr_map (c.w (homOfLE (bot_le : (⊥ : J) ≤ j)))
          exact ConcreteCategory.congr_hom h_w x₀
        rw [hx₀] at h_congr
        rw [hx] at h_congr
        exact ⟨x₀, h_congr.symm⟩
      exact hy h_y_in_range
    rcases Set.eq_empty_or_nonempty ((c.ι.app j).hom ⁻¹' ({y} : Set c.pt)) with h_empty | h_nonempty
    · rw [h_empty]
      exact isClosed_empty
    · obtain ⟨x₀, hx₀⟩ := h_nonempty
      have h_eq_singleton : (c.ι.app j).hom ⁻¹' ({y} : Set c.pt) = {x₀} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
        constructor
        · intro hx
          exact h_preimage_subsingleton hx hx₀
        · intro hx
          rw [hx, hx₀]
      rw [h_eq_singleton]
      exact (hX j).isClosed_singleton_of_notMem_range x₀ (h_preimage_outside x₀ (by simp [hx₀]))
  exact h_y_closed

lemma isClosedT1Embedding_of_transfiniteCompositionOfShape
    [WellFoundedLT J] [SuccOrder J] {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : closedT1Embeddings.{u}.TransfiniteCompositionOfShape J f) :
    Topology.IsClosedT1Embedding f.hom := by
  have inj : ∀ ⦃j j' : J⦄ (g : j ⟶ j'), Function.Injective (hf.F.map g).hom := by
    intro j j' g
    exact
      ((CategoryTheory.mono_iff_injective _).mp
        ((MorphismProperty.monomorphisms (Type u)).transfiniteCompositionsOfShape_le _ _
          ((((hf.ici j).iic ⟨j', leOfHom g⟩).ofLE
              closedT1Embeddings_le_inverseImage_monomorphisms).map.mem)))
  simp only [← hf.fac, Functor.const_obj_obj, hom_comp, ContinuousMap.coe_comp]
  refine IsClosedT1Embedding.comp
    (isClosedT1Embedding_of_transfiniteCompositionOfShape_aux hf.isColimit (fun j => ?_) inj)
    (isClosedT1Embedding_of_isIso _)
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using Topology.IsClosedT1Embedding.id
  | succ j hj hj' =>
    rw [← homOfLE_comp (bot_le : (⊥ : J) ≤ j) (Order.le_succ j), Functor.map_comp]
    exact (hf.map_mem j hj).comp hj'
  | isSuccLimit j hj hj' =>
    let : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, hj.bot_lt⟩
        bot_le := fun ⟨_, _⟩ => bot_le }
    exact
      isClosedT1Embedding_of_transfiniteCompositionOfShape_aux
        (hf.F.isColimitOfIsWellOrderContinuous j hj) (fun ⟨i, hi⟩ => hj' i hi)
        (fun _ _ g => inj (homOfLE (leOfHom g)))

instance : closedT1Embeddings.{u}.IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    ⟨fun _ _ _ ⟨hf⟩ => isClosedT1Embedding_of_transfiniteCompositionOfShape hf⟩

end Transfinite

end TopCat
