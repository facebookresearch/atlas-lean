/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Regular
public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexAttachmentCompat
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement

/-!
# Compact Hausdorff realization of finite simplicial sets

If `T : SSet.{u}` has finitely many nondegenerate simplices, its geometric realization is
compact and Hausdorff. Compactness follows from the surjective realization map from the finite
disjoint union of real standard simplices indexed by those nondegenerate simplices. The finite
face-attachment construction supplies Hausdorffness.

For arbitrary topological spaces, a quotient of a compact Hausdorff space is Hausdorff when
its equality relation is closed in the product of the source with itself.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopCat
open scoped Simplicial

namespace SSet


private lemma isCompact_univ_sigmaStdSimplex (T : SSet.{u}) [T.Finite] :
    IsCompact (Set.univ : Set (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1)))) := by
  have hEq : (Set.univ : Set (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1)))) =
      ⋃ s : T.N, Sigma.mk s '' Set.univ := by
    ext ⟨s, x⟩
    simp
  rw [hEq]
  apply isCompact_iUnion
  intro s
  apply IsCompact.image isCompact_univ continuous_sigmaMk

private instance compactSpace_sigmaStdSimplex (T : SSet.{u}) [T.Finite] :
    CompactSpace (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) where
  isCompact_univ := isCompact_univ_sigmaStdSimplex (T := T)

private instance stdSimplexT2 (n : ℕ) :
    T2Space (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).t2Space

private instance t2Space_sigmaStdSimplex (T : SSet.{u}) [T.Finite] :
    T2Space (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
  Sigma.t2Space


/-- For `T : SSet.{u}` with `T.Finite`, the space `SSet.toTop.obj T` is compact. Here finiteness
means finitely many nondegenerate simplices across all dimensions; their real standard
simplices form a finite compact disjoint union surjecting continuously onto the realization. -/
instance (T : SSet.{u}) [T.Finite] : CompactSpace (SSet.toTop.obj T) where
  isCompact_univ := by
    have hSigmaCompact := isCompact_univ_sigmaStdSimplex (T := T)
    have hCont := (isQuotientMap_sigmaToTop T).continuous
    have hSurj := surjective_sigmaToTop (T := T)
    have hRange : Set.range (sigmaToTop (T := T)) = Set.univ :=
      Set.range_eq_univ.mpr hSurj
    have hImage : IsCompact (sigmaToTop (T := T) '' Set.univ) :=
      hSigmaCompact.image hCont
    rw [Set.image_univ] at hImage
    rwa [hRange] at hImage

private instance t2Space_toTop_boundary (n : ℕ) :
    T2Space (SSet.toTop.obj (SSet.boundary.{u} n)) := by
  have : T2Space (SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)) :=
    (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  have hClosed :=
    TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (SSet.boundary.closedT1Embeddings_toTop_map_ι.{u} n)
  exact hClosed.isEmbedding.t2Space

private theorem compactSpace_of_isPushout {X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    [CompactSpace X₂] [CompactSpace X₃] (h : IsPushout t l r b) :
    CompactSpace X₄ :=
  Function.Surjective.compactSpace
    (Continuous.sumElim r.hom.continuous b.hom.continuous)
    (TopCat.isQuotientMap_sumElim_of_isPushout h).surjective

end SSet

private theorem pushout_sumElim_kernel_five {S X₁ X₂ : Type u}
    (f : S ⟶ X₁) (g : S ⟶ X₂) (hInj : Function.Injective f)
    (p q : X₁ ⊕ X₂) :
    Sum.elim (Types.Pushout.inl f g) (Types.Pushout.inr f g) p =
      Sum.elim (Types.Pushout.inl f g) (Types.Pushout.inr f g) q ↔
      (∃ x₁ y₁ : X₁, p = Sum.inl x₁ ∧ q = Sum.inl y₁ ∧ x₁ = y₁) ∨
      (∃ s₁ s₂ : S, g s₁ = g s₂ ∧ p = Sum.inl (f s₁) ∧ q = Sum.inl (f s₂)) ∨
      (∃ x₂ y₂ : X₂, p = Sum.inr x₂ ∧ q = Sum.inr y₂ ∧ x₂ = y₂) ∨
      (∃ s : S, p = Sum.inl (f s) ∧ q = Sum.inr (g s)) ∨
        ∃ s : S, p = Sum.inr (g s) ∧ q = Sum.inl (f s) := by
  have : Mono f := (mono_iff_injective f).2 hInj
  cases p with
  | inl x₁ =>
    cases q with
    | inl y₁ =>
      change Types.Pushout.inl f g x₁ = Types.Pushout.inl f g y₁ ↔ _
      have hQ : (Types.Pushout.inl f g x₁ = Types.Pushout.inl f g y₁) ↔
          Types.Pushout.Rel' f g (Sum.inl x₁) (Sum.inl y₁) :=
        Types.Pushout.quot_mk_eq_iff f g _ _
      rw [hQ, Types.Pushout.inl_rel'_inl_iff]
      constructor
      · rintro (hEq | ⟨s₁, s₂, hgs, h₁, h₂⟩)
        · exact Or.inl ⟨x₁, y₁, rfl, rfl, hEq⟩
        · exact Or.inr (Or.inl ⟨s₁, s₂, hgs, congrArg Sum.inl h₁,
            congrArg Sum.inl h₂⟩)
      · rintro (⟨a, b, h₁, h₂, h₃⟩ | ⟨s₁, s₂, hgs, h₁, h₂⟩ |
          ⟨a, b, h₁, h₂, h₃⟩ | ⟨s, h₁, h₂⟩ | ⟨s, h₁, h₂⟩)
        · have ha : x₁ = a := by injection h₁
          have hb : y₁ = b := by injection h₂
          exact Or.inl (ha.trans (h₃.trans hb.symm))
        · have hx : x₁ = f s₁ := by injection h₁
          have hy : y₁ = f s₂ := by injection h₂
          exact Or.inr ⟨s₁, s₂, hgs, hx, hy⟩
        · cases h₁
        · cases h₂
        · cases h₁
    | inr y₂ =>
      change Types.Pushout.inl f g x₁ = Types.Pushout.inr f g y₂ ↔ _
      have hQ : (Types.Pushout.inl f g x₁ = Types.Pushout.inr f g y₂) ↔
          Types.Pushout.Rel' f g (Sum.inl x₁) (Sum.inr y₂) :=
        Types.Pushout.quot_mk_eq_iff f g _ _
      rw [hQ, Types.Pushout.inl_rel'_inr_iff]
      constructor
      · rintro ⟨s, h₁, h₂⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, congrArg Sum.inl h₁,
          congrArg Sum.inr h₂⟩)))
      · rintro (⟨a, b, h₁, h₂, h₃⟩ | ⟨s₁, s₂, hgs, h₁, h₂⟩ |
          ⟨a, b, h₁, h₂, h₃⟩ | ⟨s, h₁, h₂⟩ | ⟨s, h₁, h₂⟩)
        · cases h₂
        · cases h₂
        · cases h₁
        · have hx : x₁ = f s := by injection h₁
          have hy : y₂ = g s := by injection h₂
          exact ⟨s, hx, hy⟩
        · cases h₁
  | inr x₂ =>
    cases q with
    | inl y₁ =>
      change Types.Pushout.inr f g x₂ = Types.Pushout.inl f g y₁ ↔ _
      have hQ : (Types.Pushout.inr f g x₂ = Types.Pushout.inl f g y₁) ↔
          Types.Pushout.Rel' f g (Sum.inr x₂) (Sum.inl y₁) :=
        Types.Pushout.quot_mk_eq_iff f g _ _
      have hSymm : Types.Pushout.Rel' f g (Sum.inr x₂) (Sum.inl y₁) ↔
          Types.Pushout.Rel' f g (Sum.inl y₁) (Sum.inr x₂) :=
        ⟨fun h => Types.Pushout.Rel'.symm h,
          fun h => Types.Pushout.Rel'.symm h⟩
      rw [hQ, hSymm, Types.Pushout.inl_rel'_inr_iff]
      constructor
      · rintro ⟨s, h₁, h₂⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, congrArg Sum.inr h₂,
          congrArg Sum.inl h₁⟩)))
      · rintro (⟨a, b, h₁, h₂, h₃⟩ | ⟨s₁, s₂, hgs, h₁, h₂⟩ |
          ⟨a, b, h₁, h₂, h₃⟩ | ⟨s, h₁, h₂⟩ | ⟨s, h₁, h₂⟩)
        · cases h₁
        · cases h₁
        · cases h₂
        · cases h₁
        · have hx : x₂ = g s := by injection h₁
          have hy : y₁ = f s := by injection h₂
          exact ⟨s, hy, hx⟩
    | inr y₂ =>
      change Types.Pushout.inr f g x₂ = Types.Pushout.inr f g y₂ ↔ _
      have hQ : (Types.Pushout.inr f g x₂ = Types.Pushout.inr f g y₂) ↔
          Types.Pushout.Rel' f g (Sum.inr x₂) (Sum.inr y₂) :=
        Types.Pushout.quot_mk_eq_iff f g _ _
      rw [hQ, Types.Pushout.inr_rel'_inr_iff]
      constructor
      · intro hEq
        exact Or.inr (Or.inr (Or.inl ⟨x₂, y₂, rfl, rfl, hEq⟩))
      · rintro (⟨a, b, h₁, h₂, h₃⟩ | ⟨s₁, s₂, hgs, h₁, h₂⟩ |
          ⟨a, b, h₁, h₂, h₃⟩ | ⟨s, h₁, h₂⟩ | ⟨s, h₁, h₂⟩)
        · cases h₁
        · cases h₁
        · have ha : x₂ = a := by injection h₁
          have hb : y₂ = b := by injection h₂
          exact ha.trans (h₃.trans hb.symm)
        · cases h₁
        · cases h₂

private theorem pushout_sumElim_kernel_closed {S X₁ X₂ : Type u}
    [TopologicalSpace S] [TopologicalSpace X₁] [TopologicalSpace X₂]
    [CompactSpace S] [T2Space X₁] [T2Space X₂]
    (f : S ⟶ X₁) (g : S ⟶ X₂)
    (hf : Continuous f) (hg : Continuous g)
    (hInj : Function.Injective f) :
    IsClosed (Set.ofPred (fun (p : (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) =>
      Sum.elim (Types.Pushout.inl f g) (Types.Pushout.inr f g) p.1 =
        Sum.elim (Types.Pushout.inl f g) (Types.Pushout.inr f g) p.2)) := by
  have hDiag1 : IsClosed (Set.ofPred (fun p : (X₁ × X₁) => p.1 = p.2)) :=
    isClosed_eq continuous_fst continuous_snd
  have hDiag2 : IsClosed (Set.ofPred (fun p : (X₂ × X₂) => p.1 = p.2)) :=
    isClosed_eq continuous_fst continuous_snd
  have hMap11 : Topology.IsClosedEmbedding
      (Prod.map Sum.inl Sum.inl : (X₁ × X₁) → (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) :=
    Topology.IsClosedEmbedding.prodMap Topology.IsClosedEmbedding.inl
      Topology.IsClosedEmbedding.inl
  have hMap22 : Topology.IsClosedEmbedding
      (Prod.map Sum.inr Sum.inr : (X₂ × X₂) → (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) :=
    Topology.IsClosedEmbedding.prodMap Topology.IsClosedEmbedding.inr
      Topology.IsClosedEmbedding.inr
  have hD1 : IsClosed
      ((Prod.map Sum.inl Sum.inl) '' (Set.ofPred (fun p : (X₁ × X₁) => p.1 = p.2))) :=
    hMap11.isClosedMap _ hDiag1
  have hD2 : IsClosed
      ((Prod.map Sum.inr Sum.inr) '' (Set.ofPred (fun p : (X₂ × X₂) => p.1 = p.2))) :=
    hMap22.isClosedMap _ hDiag2
  have hG : IsClosed (Set.ofPred (fun p : (S × S) => g p.1 = g p.2)) :=
    isClosed_eq (hg.comp continuous_fst) (hg.comp continuous_snd)
  have hGcomp : IsCompact (Set.ofPred (fun p : (S × S) => g p.1 = g p.2)) :=
    hG.isCompact
  have hContE : Continuous
      (Prod.map (Sum.inl ∘ f) (Sum.inl ∘ f) :
        (S × S) → (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) :=
    (continuous_inl.comp hf).prodMap (continuous_inl.comp hf)
  have hE : IsClosed
      ((Prod.map (Sum.inl ∘ f) (Sum.inl ∘ f)) ''
        (Set.ofPred (fun p : (S × S) => g p.1 = g p.2))) :=
    (hGcomp.image hContE).isClosed
  have hContC1 : Continuous
      (fun s : S => (Sum.inl (f s), Sum.inr (g s)) :
        S → (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) :=
    (continuous_inl.comp hf).prodMk (continuous_inr.comp hg)
  have hC1 : IsClosed
      (Set.range (fun s : S => (Sum.inl (f s), Sum.inr (g s)) :
        S → (X₁ ⊕ X₂) × (X₁ ⊕ X₂))) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hContC1).isClosed
  have hContC2 : Continuous
      (fun s : S => (Sum.inr (g s), Sum.inl (f s)) :
        S → (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) :=
    (continuous_inr.comp hg).prodMk (continuous_inl.comp hf)
  have hC2 : IsClosed
      (Set.range (fun s : S => (Sum.inr (g s), Sum.inl (f s)) :
        S → (X₁ ⊕ X₂) × (X₁ ⊕ X₂))) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hContC2).isClosed
  have hEq : (Set.ofPred (fun (p : (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) =>
      Sum.elim (Types.Pushout.inl f g) (Types.Pushout.inr f g) p.1 =
        Sum.elim (Types.Pushout.inl f g) (Types.Pushout.inr f g) p.2)) =
      ((Prod.map Sum.inl Sum.inl) '' (Set.ofPred (fun p : (X₁ × X₁) => p.1 = p.2)) ∪
        (((Prod.map (Sum.inl ∘ f) (Sum.inl ∘ f)) ''
          (Set.ofPred (fun p : (S × S) => g p.1 = g p.2))) ∪
          (((Prod.map Sum.inr Sum.inr) '' (Set.ofPred (fun p : (X₂ × X₂) => p.1 = p.2))) ∪
            (Set.range (fun s : S => (Sum.inl (f s), Sum.inr (g s)) :
              S → (X₁ ⊕ X₂) × (X₁ ⊕ X₂)) ∪
              Set.range (fun s : S => (Sum.inr (g s), Sum.inl (f s)) :
                S → (X₁ ⊕ X₂) × (X₁ ⊕ X₂)))))) := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image,
      Set.mem_range]
    rw [pushout_sumElim_kernel_five f g hInj a b]
    constructor
    · rintro (⟨x₁, y₁, ha, hb, hxy⟩ | ⟨s₁, s₂, hgs, ha, hb⟩ |
        ⟨x₂, y₂, ha, hb, hxy⟩ | ⟨s, ha, hb⟩ | ⟨s, ha, hb⟩)
      · exact Or.inl ⟨(x₁, y₁), hxy, Prod.ext ha.symm hb.symm⟩
      · exact Or.inr (Or.inl ⟨(s₁, s₂), hgs, Prod.ext ha.symm hb.symm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(x₂, y₂), hxy, Prod.ext ha.symm hb.symm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, Prod.ext ha.symm hb.symm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, Prod.ext ha.symm hb.symm⟩)))
    · rintro (⟨⟨x₁, x₂⟩, hx, hmap⟩ | ⟨⟨s₁, s₂⟩, hgs, hmap⟩ |
        ⟨⟨y₁, y₂⟩, hx, hmap⟩ | ⟨s, hmap⟩ | ⟨s, hmap⟩)
      · exact Or.inl ⟨x₁, x₂, (congrArg Prod.fst hmap).symm,
          (congrArg Prod.snd hmap).symm, hx⟩
      · exact Or.inr (Or.inl ⟨s₁, s₂, hgs,
          (congrArg Prod.fst hmap).symm, (congrArg Prod.snd hmap).symm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨y₁, y₂,
          (congrArg Prod.fst hmap).symm, (congrArg Prod.snd hmap).symm, hx⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s,
          (congrArg Prod.fst hmap).symm, (congrArg Prod.snd hmap).symm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s,
          (congrArg Prod.fst hmap).symm, (congrArg Prod.snd hmap).symm⟩)))
  rw [hEq]
  exact hD1.union (hE.union (hD2.union (hC1.union hC2)))

/-- Let `X,Y` be topological spaces, with `X` compact and Hausdorff. Let `q:X→Y` be a quotient
map, and assume the relation `{(x,x')∈X×X | q(x)=q(x')}` is closed in `X×X`. Then `Y` is
Hausdorff (`T2Space Y`). -/
theorem t2Space_of_compact_quotient_closed_kernel
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X]
    {q : X → Y} (hq : Topology.IsQuotientMap q)
    (hK : IsClosed (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))) : T2Space Y := by
  have hsurj : Function.Surjective q := hq.surjective
  refine (t2Space_iff_nhds).mpr ?_
  intro y1 y2 hne
  obtain ⟨a1, ha1⟩ := hsurj y1
  obtain ⟨a2, ha2⟩ := hsurj y2
  have hqq : q a1 ≠ q a2 := by
    intro heq
    exact hne (ha1.symm.trans (heq.trans ha2))
  have hF1 : IsClosed (Set.ofPred (fun (x : X) => q x = q a1)) :=
    hK.preimage (Continuous.prodMk_left a1)
  have hF2 : IsClosed (Set.ofPred (fun (x : X) => q x = q a2)) :=
    hK.preimage (Continuous.prodMk_left a2)
  have hFdisj :
      Disjoint (Set.ofPred (fun (x : X) => q x = q a1))
        (Set.ofPred (fun (x : X) => q x = q a2)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hqq (hx1.symm.trans hx2)
  obtain ⟨U1, U2, hU1open, hU2open, hF1U1, hF2U2, hUdisj⟩ :=
    normal_separation hF1 hF2 hFdisj
  have hC1 : IsClosed (U1ᶜ) := hU1open.isClosed_compl
  have hC2 : IsClosed (U2ᶜ) := hU2open.isClosed_compl
  have hPre1 : IsClosed (Prod.snd ⁻¹' U1ᶜ) :=
    hC1.preimage (continuous_snd : Continuous (fun p : X × X => p.2))
  have hPre2 : IsClosed (Prod.fst ⁻¹' U2ᶜ) :=
    hC2.preimage (continuous_fst : Continuous (fun p : X × X => p.1))
  have hInter1 : IsClosed (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))) :=
    hPre1.inter hK
  have hInter2 : IsClosed (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))) :=
    hPre2.inter hK
  have hS1 :
      IsClosed (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2)))) :=
    isClosedMap_fst_of_compactSpace _ hInter1
  have hS2 :
      IsClosed (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2)))) :=
    isClosedMap_snd_of_compactSpace _ hInter2
  have hV1open :
      IsOpen (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    hS1.isOpen_compl
  have hV2open :
      IsOpen (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    hS2.isOpen_compl
  have hF1V1 : (Set.ofPred (fun (x : X) => q x = q a1)) ⊆
      (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ := by
    intro x hx hxS
    obtain ⟨p, hp, hpx⟩ := hxS
    have hKeq : q p.1 = q p.2 := hp.2
    have hqx : q p.1 = q x := by rw [hpx]
    have hp2F : q p.2 = q a1 := hKeq.symm.trans (hqx.trans hx)
    exact hp.1 (hF1U1 hp2F)
  have hF2V2 : (Set.ofPred (fun (x : X) => q x = q a2)) ⊆
      (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ := by
    intro x hx hxS
    obtain ⟨p, hp, hpx⟩ := hxS
    have hKeq : q p.1 = q p.2 := hp.2
    have hqx : q p.2 = q x := by rw [hpx]
    have hp1F : q p.1 = q a2 := hKeq.trans (hqx.trans hx)
    exact hp.1 (hF2U2 hp1F)
  have hV1U1 :
      (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ ⊆ U1 := by
    intro x hxV
    by_contra hxU
    have hxmem : x ∈ U1ᶜ := hxU
    have hpair :
        (x, x) ∈ Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2)) := ⟨hxmem, rfl⟩
    have hxS :
        x ∈ Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))) :=
      ⟨(x, x), hpair, rfl⟩
    exact hxV hxS
  have hV2U2 :
      (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ ⊆ U2 := by
    intro x hxV
    by_contra hxU
    have hxmem : x ∈ U2ᶜ := hxU
    have hpair :
        (x, x) ∈ Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2)) := ⟨hxmem, rfl⟩
    have hxS :
        x ∈ Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))) :=
      ⟨(x, x), hpair, rfl⟩
    exact hxV hxS
  have hVdisj : Disjoint
      (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ
      (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    hUdisj.mono hV1U1 hV2U2
  have hSub1 : (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ ⊆
      q ⁻¹' (q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hSub2 : (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ ⊆
      q ⁻¹' (q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hSat1 :
      q ⁻¹' (q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) ⊆
      (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ := by
    intro x hx hxS
    obtain ⟨a, haV, haeq⟩ := hx
    obtain ⟨p, hp, hpx⟩ := hxS
    have hKeq : q p.1 = q p.2 := hp.2
    have hqx : q p.1 = q x := by rw [hpx]
    have hpa : q p.2 = q x := hKeq.symm.trans hqx
    have hAeq : q a = q p.2 := haeq.trans hpa.symm
    have hpair :
        (a, p.2) ∈ Prod.snd ⁻¹' U1ᶜ ∩
          (Set.ofPred (fun (p : X × X) => q p.1 = q p.2)) := ⟨hp.1, hAeq⟩
    have haS :
        a ∈ Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))) :=
      ⟨(a, p.2), hpair, rfl⟩
    exact haV haS
  have hSat2 :
      q ⁻¹' (q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) ⊆
      (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ := by
    intro x hx hxS
    obtain ⟨a, haV, haeq⟩ := hx
    obtain ⟨p, hp, hpx⟩ := hxS
    have hKeq : q p.1 = q p.2 := hp.2
    have hqx : q p.2 = q x := by rw [hpx]
    have hpa : q p.1 = q x := hKeq.trans hqx
    have hAeq : q p.1 = q a := hpa.trans haeq.symm
    have hpair :
        (p.1, a) ∈ Prod.fst ⁻¹' U2ᶜ ∩
          (Set.ofPred (fun (p : X × X) => q p.1 = q p.2)) := ⟨hp.1, hAeq⟩
    have haS :
        a ∈ Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))) :=
      ⟨(p.1, a), hpair, rfl⟩
    exact haV haS
  have hEq1 :
      q ⁻¹' (q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) =
      (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    le_antisymm hSat1 hSub1
  have hEq2 :
      q ⁻¹' (q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) =
      (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    le_antisymm hSat2 hSub2
  have hPreOpen1 :
      IsOpen (q ⁻¹' (q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ)) :=
    hEq1.symm ▸ hV1open
  have hPreOpen2 :
      IsOpen (q ⁻¹' (q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ)) :=
    hEq2.symm ▸ hV2open
  have hQ1open :
      IsOpen (q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) :=
    (hq.isCoinducing.isOpen_preimage).mp hPreOpen1
  have hQ2open :
      IsOpen (q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) :=
    (hq.isCoinducing.isOpen_preimage).mp hPreOpen2
  have ha1V :
      a1 ∈ (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    hF1V1 rfl
  have ha2V :
      a2 ∈ (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    hF2V2 rfl
  have hy1mem :
      y1 ∈ q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    ⟨a1, ha1V, ha1⟩
  have hy2mem :
      y2 ∈ q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
    ⟨a2, ha2V, ha2⟩
  have hQ1mem :
      q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ ∈ nhds y1 :=
    hQ1open.mem_nhds hy1mem
  have hQ2mem :
      q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ ∈ nhds y2 :=
    hQ2open.mem_nhds hy2mem
  have hQdisj : Disjoint
      (q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ)
      (q '' (Prod.snd '' (Prod.fst ⁻¹' U2ᶜ ∩
        (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    obtain ⟨a, haV, haeq⟩ := hy1
    obtain ⟨b, hbV, hbeq⟩ := hy2
    have hbPre :
        b ∈ q ⁻¹' (q '' (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩
          (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ) :=
      ⟨a, haV, haeq.trans hbeq.symm⟩
    have hbV1 :
        b ∈ (Prod.fst '' (Prod.snd ⁻¹' U1ᶜ ∩ (Set.ofPred (fun (p : X × X) => q p.1 = q p.2))))ᶜ :=
      hEq1 ▸ hbPre
    exact (Set.disjoint_left.mp hVdisj) hbV1 hbV
  exact ⟨_, hQ1mem, _, hQ2mem, hQdisj⟩

private theorem t2Space_of_pushout_compact_injective {X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    [CompactSpace X₁] [CompactSpace X₂] [CompactSpace X₃]
    [T2Space X₂] [T2Space X₃]
    (h : IsPushout t l r b) (ht : Function.Injective t.hom) :
    T2Space X₄ := by
  have : CompactSpace X₄ := SSet.compactSpace_of_isPushout h
  have htType : Function.Injective ((forget TopCat).map t) := ht
  have hT := h.map (forget TopCat)
  have hC := IsPushout.of_isColimit
    (Types.Pushout.isColimitCocone ((forget TopCat).map t) ((forget TopCat).map l))
  let e : (forget TopCat).obj X₄ ≅
    Types.Pushout ((forget TopCat).map t) ((forget TopCat).map l) :=
    hT.isoIsPushout _ _ hC
  have hFaceL : (forget TopCat).map r ≫ e.hom =
      Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l) := by
    simp [e]
  have hFaceR : (forget TopCat).map b ≫ e.hom =
      Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l) := by
    simp [e]
  have he_inj : Function.Injective e.hom := by
    intro a b hab
    have h1 : e.inv (e.hom a) = e.inv (e.hom b) := congrArg e.inv hab
    have ha : e.inv (e.hom a) = a :=
      ConcreteCategory.congr_hom e.hom_inv_id a
    have hb : e.inv (e.hom b) = b :=
      ConcreteCategory.congr_hom e.hom_inv_id b
    rw [ha] at h1
    rw [hb] at h1
    exact h1
  have hPoint : ∀ p : (↥X₂ ⊕ ↥X₃),
      e.hom (Sum.elim r b p) =
        Sum.elim (Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l))
          (Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l)) p := by
    intro p
    cases p with
    | inl x₂ =>
      simp only [Sum.elim_inl]
      have h1 := ConcreteCategory.congr_hom hFaceL x₂
      simpa using h1
    | inr x₃ =>
      simp only [Sum.elim_inr]
      have h1 := ConcreteCategory.congr_hom hFaceR x₃
      simpa using h1
  have hIff : ∀ x y : (↥X₂ ⊕ ↥X₃),
      (Sum.elim r b x = Sum.elim r b y ↔
        Sum.elim (Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l))
          (Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l)) x =
        Sum.elim (Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l))
          (Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l)) y) := by
    intro x y
    constructor
    · intro hab
      have hcon := congrArg e.hom hab
      rwa [hPoint x, hPoint y] at hcon
    · intro hab
      have hcon : e.hom (Sum.elim r b x) = e.hom (Sum.elim r b y) := by
        rwa [hPoint x, hPoint y]
      exact he_inj hcon
  have hKer : (Set.ofPred (fun p : ((↥X₂ ⊕ ↥X₃) × (↥X₂ ⊕ ↥X₃)) =>
      Sum.elim r b p.1 = Sum.elim r b p.2)) =
      (Set.ofPred (fun p : ((↥X₂ ⊕ ↥X₃) × (↥X₂ ⊕ ↥X₃)) =>
      Sum.elim (Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l))
        (Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l)) p.1 =
      Sum.elim (Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l))
        (Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l)) p.2)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq]
    exact hIff a b
  have hCan : IsClosed (Set.ofPred (fun p : ((↥X₂ ⊕ ↥X₃) × (↥X₂ ⊕ ↥X₃)) =>
      Sum.elim (Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l))
        (Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l)) p.1 =
      Sum.elim (Types.Pushout.inl ((forget TopCat).map t) ((forget TopCat).map l))
        (Types.Pushout.inr ((forget TopCat).map t) ((forget TopCat).map l)) p.2)) :=
    pushout_sumElim_kernel_closed ((forget TopCat).map t) ((forget TopCat).map l)
      t.hom.continuous l.hom.continuous htType
  have hArb : IsClosed (Set.ofPred (fun p : ((↥X₂ ⊕ ↥X₃) × (↥X₂ ⊕ ↥X₃)) =>
      Sum.elim r b p.1 = Sum.elim r b p.2)) := by
    rw [hKer]
    exact hCan
  exact t2Space_of_compact_quotient_closed_kernel
    (TopCat.isQuotientMap_sumElim_of_isPushout h) hArb

namespace SSet

/-- For `K : SSet.{u}` with finitely many nondegenerate simplices, `SSet.toTop.obj K` is
Hausdorff. Its finite attachment chain from the empty subcomplex along realized boundary
inclusions preserves the Hausdorff property. -/
instance (K : SSet.{u}) [K.Finite] : T2Space (SSet.toTop.obj K) := by
  obtain ⟨k, C, hC0, hCk, _hmono, hstep⟩ :=
    SSet.boundary.exists_finite_attachment_chain_of_le_of_finite
      (⊥ : K.Subcomplex) ⊤ bot_le
  have hInitSSet : IsInitial (((⊥ : K.Subcomplex)) : SSet.{u}) :=
    SSet.Subcomplex.isInitialBot
  have hInitTop :
      IsInitial (SSet.toTop.obj (((⊥ : K.Subcomplex)) : SSet.{u})) :=
    hInitSSet.isInitialObj (G := SSet.toTop)
  have hIso :
      SSet.toTop.obj (((⊥ : K.Subcomplex)) : SSet.{u}) ≅ TopCat.of PEmpty :=
    hInitTop.uniqueUpToIso TopCat.isInitialPEmpty
  have : T2Space (TopCat.of PEmpty) := DiscreteTopology.toT2Space
  have hBot : T2Space (SSet.toTop.obj (((⊥ : K.Subcomplex)) : SSet.{u})) :=
    (TopCat.homeoOfIso hIso).symm.t2Space
  have hAll : ∀ j : Fin (k + 1),
      T2Space (SSet.toTop.obj (((C j : K.Subcomplex)) : SSet.{u})) := by
    intro j
    refine Fin.induction ?_ (fun i ih => ?_) j
    · have h0 : (0 : Fin (k + 1)) = ⟨0, Nat.zero_lt_succ k⟩ := by ext; simp
      rw [h0, hC0]
      exact hBot
    · have eLo : i.castSucc =
          (⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩ : Fin (k + 1)) := by
        ext; simp
      have eHi : i.succ =
          (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (k + 1)) := by
        ext; simp
      obtain ⟨n, t, b, hle, hPush, _hlt, _hleJ⟩ := hstep i.val i.isLt
      rw [eLo] at ih
      rw [eHi]
      have : T2Space (SSet.toTop.obj ((Δ[n] : SSet.{u}))) :=
        (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
      have hMap : IsPushout (SSet.toTop.{u}.map t)
          (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι)
          (SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE hle))
          (SSet.toTop.{u}.map b) :=
        hPush.map SSet.toTop.{u}
      have hInj :
          Function.Injective (SSet.toTop.map (SSet.boundary.{u} n).ι).hom :=
        (TopCat.closedT1Embeddings_le_isClosedEmbedding _
          (SSet.boundary.closedT1Embeddings_toTop_map_ι.{u} n)).isEmbedding.injective
      exact _root_.t2Space_of_pushout_compact_injective hMap.flip hInj
  have hFin : Fin.last k = (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
    ext; simp
  have hTop : T2Space (SSet.toTop.obj (((⊤ : K.Subcomplex)) : SSet.{u})) := by
    have hLast := hAll (Fin.last k)
    rw [hFin, hCk] at hLast
    exact hLast
  exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.Subcomplex.topIso K))).t2Space

end SSet
