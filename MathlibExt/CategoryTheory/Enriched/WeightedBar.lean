/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monad.SimplicialReplacementBridge

/-!
# Strict ordinary weighted bar: degreewise coproduct prefix

This module is the strict ordinary prefix of the enriched weighted bar, not the genuine
enriched construction. For a small indexing category `J`, a contravariant ordinary
weight `W : Jᵒᵖ ⥤ Type`, and a covariant diagram `F : J ⥤ C` into a category with the
needed coproducts, degree `n` is the coproduct of `F`-values at left endpoints indexed
over weighted chains `(s, w)` with `w : W` over the right endpoint of `s`. Putting the
weight at the right endpoint and the diagram at the left is the orientation that makes
both outer operators honest: `d₀` acts on diagram coefficients by the first arrow,
`d_last` acts on weight elements by the last arrow, and `s₀` is the identity on both
sides. The swapped placement would demand a covariant action from the contravariant
weight and is not provided.

Provenance (paper-level, no section claimed): M. Shulman, `Homotopy limits and
colimits and enriched homotopy theory`, arXiv:math/0610194
(https://arxiv.org/abs/math/0610194). This module implements only the strict
ordinary restriction: ordinary weights `W : Jᵒᵖ ⥤ Type` and coproducts in place
of enriched copowers/coends. Notation map: source `B_•(W, J, F)` ~ Lean
`wbarObj` / `wbarData` / `wbarSimplicial`; source weight/diagram/indexing
correspond to Lean `W` / `F` / `J`; source outer faces/degeneracy correspond to
Lean `wbarFaceZero` / `wbarFaceLast` / `wbarDegZero`, with total operators
`wbarδ` / `wbarσ` in `WeightedBarData`.

Provided API, all degreewise and each with a named coproduct-inclusion computation
lemma: the weighted index type `WIdx`, definitional endpoint preservations,
`wbarObj` / `wbarIncl` / `wbarDesc`, functoriality `wbarMapF` / `wbarMapW` in both
variables, the justified outer operators `wbarFaceZero` / `wbarFaceLast` /
`wbarDegZero`, the `wbarMapFIso` comparison isomorphism, and the pointwise
`wbarSectionComp` family in the spirit of `bridgeConstComp`.

Reuse: `SrepIdx`, the `srepDropFirst` / `srepDropLast` / `srepDupFirst` chain maps, the
`Sigma` universal API, the `srepFaceZeroComponent` /
`srepFaceLastComponent` / `srepDegZeroComponent` operators, and the
`barIdObjIso` / `bridgeConstComp` iso-not-defeq discipline: comparisons are exposed as
maps and isomorphisms, never definitional identifications.

Scope (this file only): the strict omit/duplicate chain identities are
in `StrictOmitDupChain`; interior assembly is in `WeightedBarInner`, the six
simplicial relations and `SimplicialObject.Data` packaging are in
`WeightedBarData`, genuine promotion is in `WeightedBarSimplicial`, separate
diagram/weight naturality is in `WeightedBarMapF` / `WeightedBarMapW` with the
mixed square in `WeightedBarMapFW`, and outer naturality plus outer-only laws are
in `WeightedBarOuter`; categorical packaging is in `WeightedBarFunctor`. None of those are proved
here. Enriched copowers, enriched
coends, the profunctor/bicategorical bridge, promotion of
`wbarSectionComp` to a simplicial map, pointwise joint functoriality without a global sized
coproduct hypothesis, realization/homotopy-colimit
conclusions, and all derived/infinity-categorical claims are deferred beyond this
module. No local `Copowered`, enriched coend, profunctor-composition, or
model-category API is introduced.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOrdinaryWeightedBar

universe vJ uJ vC uC uW

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- Weighted indexing type in degree `n`: pairs of a chain `s` with a weight element
over its right endpoint. The weight is contravariant, so elements lie over
`Opposite.op s.right`; the diagram value will sit over `s.left`. -/
abbrev WIdx (J : Type uJ) [Category.{vJ} J] (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) :=
  Σ s : SrepBridge.SrepIdx J n, W.obj (Opposite.op s.right)

/-- Dropping the first entry preserves the right endpoint definitionally. -/
theorem wDropFirst_right {n : ℕ} (s : SrepBridge.SrepIdx J (n + 1)) :
    (SrepBridge.srepDropFirst s).right = s.right := rfl

/-- Dropping the last entry exposes the second-to-last vertex definitionally. -/
theorem wDropLast_right {n : ℕ} (s : SrepBridge.SrepIdx J (n + 1)) :
    (SrepBridge.srepDropLast s).right = s.obj' n := rfl

/-- Repeating the first entry preserves the right endpoint definitionally. -/
theorem wDupFirst_right {n : ℕ} (s : SrepBridge.SrepIdx J n) :
    (SrepBridge.srepDupFirst s).right = s.right := rfl

/-- Index map of the outermost face `d₀`: drop the first entry of the chain; the weight
element is carried along the definitional right-endpoint identification. -/
def wFaceZeroIdx (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) (p : WIdx J W (n + 1)) :
    WIdx J W n :=
  ⟨SrepBridge.srepDropFirst p.1, p.2⟩

/-- Index map of the outermost face `d_last`: drop the last entry of the chain, acting
on the weight element by the last arrow of the chain. -/
def wFaceLastIdx (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) (p : WIdx J W (n + 1)) :
    WIdx J W n :=
  ⟨SrepBridge.srepDropLast p.1, W.map (p.1.map' n (n + 1)).op p.2⟩

/-- Index map of the outermost degeneracy `s₀`: repeat the first entry of the chain;
both endpoints are definitionally fixed. -/
def wDegZeroIdx (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) (p : WIdx J W n) :
    WIdx J W (n + 1) :=
  ⟨SrepBridge.srepDupFirst p.1, p.2⟩

/-- Index map of functoriality in the weight: apply `ψ` to the weight element,
leaving the chain unchanged. Stated as an abbreviation so the definitional
fixing of the chain component is visible to tactics at reducible transparency. -/
abbrev wMapWIdx {W W' : Jᵒᵖ ⥤ Type uW} (n : ℕ) (ψ : W ⟶ W') (p : WIdx J W n) :
    WIdx J W' n :=
  ⟨p.1, ψ.app (Opposite.op p.1.right) p.2⟩

/-- Degree `n` of the strict ordinary weighted bar: the coproduct of diagram values at
left endpoints, indexed over weighted chains. -/
noncomputable def wbarObj (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] : C :=
  ∐ fun p : WIdx J W n => F.obj p.1.left

/-- Inclusion of the summand indexed by the weighted chain `p`. -/
noncomputable def wbarIncl (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    (p : WIdx J W n) : F.obj p.1.left ⟶ wbarObj W F n :=
  Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left) p

/-- Universal map out of a weighted-bar degree from component maps. -/
noncomputable def wbarDesc (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] {P : C}
    (e : ∀ p : WIdx J W n, F.obj p.1.left ⟶ P) : wbarObj W F n ⟶ P :=
  Limits.Sigma.desc e

/-- Computation rule for `wbarDesc`. -/
theorem wbarDesc_ι (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] {P : C}
    (e : ∀ p : WIdx J W n, F.obj p.1.left ⟶ P) (p : WIdx J W n) :
    wbarIncl W F n p ≫ wbarDesc W F n e = e p :=
  Limits.Sigma.ι_comp_desc e p

/-- Functoriality of weighted-bar degrees in the diagram: the weighted index type is
unchanged, so this is a plain `Sigma.map`. -/
noncomputable def wbarMapF {W : Jᵒᵖ ⥤ Type uW} {F G : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)] (φ : F ⟶ G) :
    wbarObj W F n ⟶ wbarObj W G n :=
  Limits.Sigma.map (fun p : WIdx J W n => φ.app p.1.left)

/-- Computation rule for `wbarMapF`. -/
theorem wbarMapF_ι {W : Jᵒᵖ ⥤ Type uW} {F G : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) (p : WIdx J W n) :
    wbarIncl W F n p ≫ wbarMapF n φ = φ.app p.1.left ≫ wbarIncl W G n p :=
  Limits.Sigma.ι_map (fun p : WIdx J W n => φ.app p.1.left) p

/-- `wbarMapF` preserves identities. -/
theorem wbarMapF_id {W : Jᵒᵖ ⥤ Type uW} (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarMapF n (𝟙 F) = 𝟙 (wbarObj W F n) := by
  change Limits.Sigma.map (fun p : WIdx J W n => 𝟙 (F.obj p.1.left)) =
    𝟙 (wbarObj W F n)
  exact Limits.Sigma.map_id

/-- `wbarMapF` preserves composition. -/
theorem wbarMapF_comp {W : Jᵒᵖ ⥤ Type uW} {F G H : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => H.obj p.1.left)]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    wbarMapF (W := W) n φ ≫ wbarMapF (W := W) n ψ =
      wbarMapF (W := W) n (φ ≫ ψ) := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  change wbarIncl W F n p ≫ (wbarMapF n φ ≫ wbarMapF n ψ) =
    wbarIncl W F n p ≫ wbarMapF n (φ ≫ ψ)
  rw [←Category.assoc, wbarMapF_ι, Category.assoc, wbarMapF_ι, wbarMapF_ι,
    NatTrans.comp_app]
  simp only [Category.assoc]

/-- Functoriality of weighted-bar degrees in the weight, via the index map `wMapWIdx`
with identity coefficient maps. -/
noncomputable def wbarMapW {W W' : Jᵒᵖ ⥤ Type uW} (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)] (ψ : W ⟶ W') :
    wbarObj W F n ⟶ wbarObj W' F n :=
  Limits.Sigma.map' (wMapWIdx n ψ) (fun p : WIdx J W n => 𝟙 (F.obj p.1.left))

/-- Computation rule for `wbarMapW`. -/
theorem wbarMapW_ι {W W' : Jᵒᵖ ⥤ Type uW} (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)]
    (ψ : W ⟶ W') (p : WIdx J W n) :
    wbarIncl W F n p ≫ wbarMapW F n ψ =
      𝟙 (F.obj p.1.left) ≫ wbarIncl W' F n (wMapWIdx n ψ p) := by
  change Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left) p ≫
      Limits.Sigma.map' (wMapWIdx n ψ) (fun p : WIdx J W n => 𝟙 (F.obj p.1.left)) =
    (𝟙 (F.obj p.1.left) : F.obj p.1.left ⟶ F.obj p.1.left) ≫
      Limits.Sigma.ι (fun p : WIdx J W' n => F.obj p.1.left) (wMapWIdx n ψ p)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- `wbarMapW` preserves identities. -/
theorem wbarMapW_id {W : Jᵒᵖ ⥤ Type uW} (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarMapW F n (𝟙 W) = 𝟙 (wbarObj W F n) := by
  have hcone : ∀ p : WIdx J W n,
      wbarIncl W F n (wMapWIdx n (𝟙 W) p) = wbarIncl W F n p := by
    intro p
    obtain ⟨s, w⟩ := p
    rfl
  apply Limits.Sigma.hom_ext (f := fun p : WIdx J W n => F.obj p.1.left)
  intro p
  obtain ⟨s, w⟩ := p
  change wbarIncl W F n ⟨s, w⟩ ≫ wbarMapW F n (𝟙 W) =
    wbarIncl W F n ⟨s, w⟩ ≫ 𝟙 (wbarObj W F n)
  rw [wbarMapW_ι, hcone ⟨s, w⟩, Category.id_comp, Category.comp_id]

/-- `wbarMapW` preserves composition. -/
theorem wbarMapW_comp {W W' W'' : Jᵒᵖ ⥤ Type uW} (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W'' n => F.obj p.1.left)]
    (ψ : W ⟶ W') (ψ' : W' ⟶ W'') :
    wbarMapW F n ψ ≫ wbarMapW F n ψ' = wbarMapW F n (ψ ≫ ψ') := by
  have hcone : ∀ p : WIdx J W n,
      wbarIncl W'' F n (wMapWIdx n ψ' (wMapWIdx n ψ p)) =
        wbarIncl W'' F n (wMapWIdx n (ψ ≫ ψ') p) := by
    intro p
    obtain ⟨s, w⟩ := p
    rfl
  apply Limits.Sigma.hom_ext (f := fun p : WIdx J W n => F.obj p.1.left)
  intro p
  obtain ⟨s, w⟩ := p
  change wbarIncl W F n ⟨s, w⟩ ≫ (wbarMapW F n ψ ≫ wbarMapW F n ψ') =
    wbarIncl W F n ⟨s, w⟩ ≫ wbarMapW F n (ψ ≫ ψ')
  rw [←Category.assoc, wbarMapW_ι, Category.assoc, wbarMapW_ι, wbarMapW_ι]
  simp only [Category.id_comp]
  exact hcone ⟨s, w⟩

/-- Outermost face `d₀` of the strict ordinary weighted bar: drop the first entry of
each chain, acting on the diagram coefficient by its first arrow (the
`srepFaceZeroComponent`); the weight element is carried along the definitional
right-endpoint identification. -/
noncomputable def wbarFaceZero (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarObj W F (n + 1) ⟶ wbarObj W F n :=
  Limits.Sigma.map' (wFaceZeroIdx W n)
    (fun p => SrepBridge.srepFaceZeroComponent F p.1)

/-- Computation rule for `wbarFaceZero`. -/
theorem wbarFaceZero_ι (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    (p : WIdx J W (n + 1)) :
    wbarIncl W F (n + 1) p ≫ wbarFaceZero W F n =
      SrepBridge.srepFaceZeroComponent F p.1 ≫
        wbarIncl W F n (wFaceZeroIdx W n p) := by
  change Limits.Sigma.ι (fun p : WIdx J W (n + 1) => F.obj p.1.left) p ≫
      Limits.Sigma.map' (wFaceZeroIdx W n)
        (fun p => SrepBridge.srepFaceZeroComponent F p.1) =
    SrepBridge.srepFaceZeroComponent F p.1 ≫
      Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left)
        (wFaceZeroIdx W n p)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- Outermost face `d_last` of the strict ordinary weighted bar: drop the last entry of
each chain, acting on the weight element by the last arrow; the diagram coefficient is
transported by `srepFaceLastComponent`. -/
noncomputable def wbarFaceLast (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarObj W F (n + 1) ⟶ wbarObj W F n :=
  Limits.Sigma.map' (wFaceLastIdx W n)
    (fun p => SrepBridge.srepFaceLastComponent F p.1)

/-- Computation rule for `wbarFaceLast`. -/
theorem wbarFaceLast_ι (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    (p : WIdx J W (n + 1)) :
    wbarIncl W F (n + 1) p ≫ wbarFaceLast W F n =
      SrepBridge.srepFaceLastComponent F p.1 ≫
        wbarIncl W F n (wFaceLastIdx W n p) := by
  change Limits.Sigma.ι (fun p : WIdx J W (n + 1) => F.obj p.1.left) p ≫
      Limits.Sigma.map' (wFaceLastIdx W n)
        (fun p => SrepBridge.srepFaceLastComponent F p.1) =
    SrepBridge.srepFaceLastComponent F p.1 ≫
      Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left)
        (wFaceLastIdx W n p)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- Outermost degeneracy `s₀` of the strict ordinary weighted bar: repeat the first
entry of each chain; both coefficients are the identity
`srepDegZeroComponent`. -/
noncomputable def wbarDegZero (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)] :
    wbarObj W F n ⟶ wbarObj W F (n + 1) :=
  Limits.Sigma.map' (wDegZeroIdx W n)
    (fun p => SrepBridge.srepDegZeroComponent F p.1)

/-- Computation rule for `wbarDegZero`. -/
theorem wbarDegZero_ι (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    (p : WIdx J W n) :
    wbarIncl W F n p ≫ wbarDegZero W F n =
      SrepBridge.srepDegZeroComponent F p.1 ≫
        wbarIncl W F (n + 1) (wDegZeroIdx W n p) := by
  change Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left) p ≫
      Limits.Sigma.map' (wDegZeroIdx W n)
        (fun p => SrepBridge.srepDegZeroComponent F p.1) =
    SrepBridge.srepDegZeroComponent F p.1 ≫
      Limits.Sigma.ι (fun p : WIdx J W (n + 1) => F.obj p.1.left)
        (wDegZeroIdx W n p)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- Degreewise comparison isomorphism in the diagram variable, from a natural
isomorphism. This is the weighted analogue of the `barIdObjIso` pattern: an explicit
isomorphism, never a definitional identification. -/
noncomputable def wbarMapFIso {W : Jᵒᵖ ⥤ Type uW} {F G : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ≅ G) : wbarObj W F n ≅ wbarObj W G n where
  hom := wbarMapF n φ.hom
  inv := wbarMapF n φ.inv
  hom_inv_id := by
    rw [wbarMapF_comp, φ.hom_inv_id, wbarMapF_id]
  inv_hom_id := by
    rw [wbarMapF_comp, φ.inv_hom_id, wbarMapF_id]

/-- Computation rule for the forward direction of `wbarMapFIso`. -/
theorem wbarMapFIso_hom_ι {W : Jᵒᵖ ⥤ Type uW} {F G : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ≅ G) (p : WIdx J W n) :
    wbarIncl W F n p ≫ (wbarMapFIso n φ).hom =
      (φ.app p.1.left).hom ≫ wbarIncl W G n p := by
  exact wbarMapF_ι n φ.hom p

/-- Computation rule for the inverse direction of `wbarMapFIso`. -/
theorem wbarMapFIso_inv_ι {W : Jᵒᵖ ⥤ Type uW} {F G : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ≅ G) (p : WIdx J W n) :
    wbarIncl W G n p ≫ (wbarMapFIso n φ).inv =
      (φ.app p.1.left).inv ≫ wbarIncl W F n p := by
  exact wbarMapF_ι n φ.inv p

/-- Named degreewise comparison from ordinary simplicial replacement into the weighted
bar along a chosen family of weight elements at right endpoints. This is a pointwise
family in the spirit of `bridgeConstComp`, not a simplicial map: for an arbitrary
chosen family `σ` it cannot be promoted without the necessary naturality and
compatibility data. The inner simplicial identities are present; no compatibility with
`srepFaceZero` / `srepFaceLast` / `srepDegZero` is claimed. -/
noncomputable def wbarSectionComp (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
    (σ : ∀ a : J, W.obj (Opposite.op a)) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepBridge.SrepIdx J n => F.obj s.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    SrepBridge.srepObj F n ⟶ wbarObj W F n :=
  Limits.Sigma.map' (fun s => (⟨s, σ s.right⟩ : WIdx J W n))
    (fun s : SrepBridge.SrepIdx J n => 𝟙 (F.obj s.left))

/-- Computation rule for `wbarSectionComp`. -/
theorem wbarSectionComp_ι (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
    (σ : ∀ a : J, W.obj (Opposite.op a)) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepBridge.SrepIdx J n => F.obj s.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    (s : SrepBridge.SrepIdx J n) :
    SrepBridge.srepIncl F n s ≫ wbarSectionComp W F σ n =
      𝟙 (F.obj s.left) ≫ wbarIncl W F n ⟨s, σ s.right⟩ := by
  change Limits.Sigma.ι (fun s : SrepBridge.SrepIdx J n => F.obj s.left) s ≫
      Limits.Sigma.map' (fun s => (⟨s, σ s.right⟩ : WIdx J W n))
        (fun s : SrepBridge.SrepIdx J n => 𝟙 (F.obj s.left)) =
    (𝟙 (F.obj s.left) : F.obj s.left ⟶ F.obj (⟨s, σ s.right⟩ : WIdx J W n).1.left) ≫
      Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left) ⟨s, σ s.right⟩
  exact Limits.Sigma.ι_comp_map' _ _ _

end StrictOrdinaryWeightedBar
end CategoryTheory
