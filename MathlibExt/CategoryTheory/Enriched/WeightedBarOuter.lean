/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.WeightedBar
public import MathlibExt.CategoryTheory.ComposableArrows.StrictOmitDup

/-!
# Strict outer-operator completion for the ordinary weighted bar

This module is the strict outer-operator completion packet for the ordinary weighted
bar from `WeightedBar`. It proves naturality of the three outer operators
`wbarFaceZero` / `wbarFaceLast` / `wbarDegZero` in the diagram variable `F` and in
the weight variable `W`, together with the three outer-only coherence laws: the
`d₀`/`d_last` interchange, the `s₀`/`d₀` section law, and the `s₀`/`d_last`
interchange. Every proof is degreewise through the `Limits.Sigma`
inclusion API (`Sigma.hom_ext`, `Sigma.map'_comp_map'`, `Sigma.map'_eq`,
`Sigma.ι_comp_map'`): index maps commute definitionally or by weight naturality,
while coefficient maps commute by naturality of the diagram morphism or collapse
as identity-on-coefficients `eqToHom` composites.

Orientation: `d₀` drops the first chain entry and acts on diagram coefficients;
`d_last` drops the last entry and acts on weight elements; `s₀` repeats the first
entry and is the identity on both sides. Naturality squares preserve this
orientation: operators commute with reindexing in either variable.

Hypotheses: each statement assumes exactly the coproduct instances of the degrees
it mentions, with the same explicit families as `WeightedBar`.

Nonclaims (this file only): no inner faces or degeneracies, no full simplicial
identities, no `SimplicialObject.Data` packaging, no `Data`/`GenRel` genuine
bridge, no enriched copowers or coends, no profunctor composition, and no
realization or homotopy-colimit conclusion. Inner operators are in
`WeightedBarInner`, `Data` packaging and the six relations are in
`WeightedBarData`, genuine promotion is in `WeightedBarSimplicial`, and separate
naturality with the mixed square is in `WeightedBarMapF` / `WeightedBarMapW` /
`WeightedBarMapFW`. This strict ordinary prefix is not
identified with the future genuinely enriched bar.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOrdinaryWeightedBar

universe vJ uJ vC uC uW

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- Internal: slide a naturality square past endpoint identifications. -/
private theorem wSlide {F G : J ⥤ C} (φ : F ⟶ G) {X Y : J} {h : X = Y} :
    eqToHom (congrArg F.obj h) ≫ φ.app Y =
      φ.app X ≫ eqToHom (congrArg G.obj h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Internal: the `d_last` index map commutes with weight reindexing, by naturality
of the weight morphism. The chain component is unchanged on both sides. -/
private theorem wFaceLastIdx_mapW {W W' : Jᵒᵖ ⥤ Type uW} (n : ℕ) (ψ : W ⟶ W')
    (p : WIdx J W (n + 1)) :
    wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p) =
      wMapWIdx n ψ (wFaceLastIdx W n p) := by
  obtain ⟨s, w⟩ := p
  have hnat := ψ.naturality (s.map' n (n + 1)).op
  have helem := congrArg (fun e : W.obj _ ⟶ W'.obj _ => e w) hnat
  refine congrArg (fun w' => (⟨SrepBridge.srepDropLast s, w'⟩ : WIdx J W' n)) ?_
  exact helem.symm

/-- Internal: dropping the first entry then the last agrees with dropping the last
entry then the first, as functions on weighted indices. -/
private theorem wFaceZero_faceLast_idx (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) :
    (wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) =
      (wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) := by
  funext p
  obtain ⟨s, w⟩ := p
  rfl

/-- Internal: duplicating the first entry then dropping the last agrees with dropping
the last entry then duplicating the first, as functions on weighted indices. -/
private theorem wDegZero_faceLast_idx (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) :
    (wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) =
      (wDegZeroIdx W n ∘ wFaceLastIdx W n) := by
  funext p
  obtain ⟨s, w⟩ := p
  have hchain : SrepBridge.srepDropLast (SrepBridge.srepDupFirst s) =
      SrepBridge.srepDupFirst (SrepBridge.srepDropLast s) := by
    change ComposableArrows.δlastFunctor.obj (s.precomp (𝟙 s.left)) =
      (ComposableArrows.δlastFunctor.obj s).precomp (𝟙 _)
    exact StrictOmitDup.dropLast_dupFirst_eq s
  have harr : (SrepBridge.srepDupFirst s).map' (n + 1) (n + 1 + 1) =
      s.map' n (n + 1) := by
    change (s.precomp (𝟙 s.left)).map' (n + 1) (n + 1 + 1) = s.map' n (n + 1)
    exact StrictOmitDup.dupFirst_lastArrow_eq s
  have hpair : (⟨SrepBridge.srepDropLast (SrepBridge.srepDupFirst s),
      W.map ((SrepBridge.srepDupFirst s).map' (n + 1) (n + 1 + 1)).op w⟩ :
      WIdx J W (n + 1)) =
      ⟨SrepBridge.srepDupFirst (SrepBridge.srepDropLast s),
        W.map (s.map' n (n + 1)).op w⟩ :=
    Sigma.ext hchain (by cases harr; rfl)
  change (wFaceLastIdx W (n + 1) (wDegZeroIdx W (n + 1) ⟨s, w⟩)) =
    (wDegZeroIdx W n (wFaceLastIdx W n ⟨s, w⟩))
  exact hpair

/-- Internal: `d₀` coefficient commutes with `φ`, across endpoint transports. -/
private theorem wHCoeffFaceZeroF (F G : J ⥤ C) (φ : F ⟶ G) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceZeroComponent F s ≫
        φ.app (SrepBridge.srepDropFirst s).left =
      φ.app s.left ≫ SrepBridge.srepFaceZeroComponent G s := by
  change (𝟙 _ ≫ F.map (s.map' 0 1) ≫ 𝟙 _) ≫
      φ.app (SrepBridge.srepDropFirst s).left =
    φ.app s.left ≫ (𝟙 _ ≫ G.map (s.map' 0 1) ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  exact φ.naturality _

/-- Internal: `d_last` coefficient commutes with `φ`, across endpoint transports. -/
private theorem wHCoeffFaceLastF (F G : J ⥤ C) (φ : F ⟶ G) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceLastComponent F s ≫
        φ.app (SrepBridge.srepDropLast s).left =
      φ.app s.left ≫ SrepBridge.srepFaceLastComponent G s :=
  wSlide φ (h := (SrepBridge.srepDropLast_left s).symm)

/-- Internal: `s₀` coefficient commutes with `φ`, across endpoint transports. -/
private theorem wHCoeffDegZeroF (F G : J ⥤ C) (φ : F ⟶ G) {n : ℕ}
    (s : SrepBridge.SrepIdx J n) :
    SrepBridge.srepDegZeroComponent F s ≫
        φ.app (SrepBridge.srepDupFirst s).left =
      φ.app s.left ≫ SrepBridge.srepDegZeroComponent G s :=
  wSlide φ (h := (SrepBridge.srepDupFirst_left s).symm)

/-- Internal: outer `d₀`/`d_last` coefficients commute. -/
private theorem wHCoeffInterFL (F : J ⥤ C) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 2)) :
    (SrepBridge.srepFaceZeroComponent F s ≫ SrepBridge.srepFaceLastComponent F
      (SrepBridge.srepDropFirst s)) =
    (SrepBridge.srepFaceLastComponent F s ≫ SrepBridge.srepFaceZeroComponent F
      (SrepBridge.srepDropLast s)) := by
  have hm : s.map' 0 1 = (SrepBridge.srepDropLast s).map' 0 1 := rfl
  change (𝟙 _ ≫ F.map (s.map' 0 1) ≫ 𝟙 _) ≫ 𝟙 _ =
    𝟙 _ ≫ (𝟙 _ ≫ F.map ((SrepBridge.srepDropLast s).map' 0 1) ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  exact congrArg (F.map) hm

/-- Internal: outer `s₀`/`d_last` coefficients commute. -/
private theorem wHCoeffInterDL (F : J ⥤ C) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    (SrepBridge.srepDegZeroComponent F s ≫ SrepBridge.srepFaceLastComponent F
      (SrepBridge.srepDupFirst s)) =
    (SrepBridge.srepFaceLastComponent F s ≫ SrepBridge.srepDegZeroComponent F
      (SrepBridge.srepDropLast s)) := by
  have h1 : SrepBridge.srepDegZeroComponent F s = 𝟙 _ := rfl
  have h2 : SrepBridge.srepFaceLastComponent F (SrepBridge.srepDupFirst s) =
      𝟙 _ := rfl
  have h3 : SrepBridge.srepFaceLastComponent F s = 𝟙 _ := rfl
  have h4 : SrepBridge.srepDegZeroComponent F (SrepBridge.srepDropLast s) =
      𝟙 _ := rfl
  rw [h1, h2, h3, h4]
  exact (Category.comp_id _).trans (Category.comp_id _).symm

/-- Internal: outer `s₀`/`d₀` coefficients compose to the identity. -/
private theorem wHCoeffSection (F : J ⥤ C) {n : ℕ}
    (s : SrepBridge.SrepIdx J n) :
    SrepBridge.srepDegZeroComponent F s ≫ SrepBridge.srepFaceZeroComponent F
      (SrepBridge.srepDupFirst s) = 𝟙 _ := by
  have hm : (SrepBridge.srepDupFirst s).map' 0 1 = 𝟙 _ := rfl
  have h1 : SrepBridge.srepDegZeroComponent F s = 𝟙 _ := rfl
  rw [h1]
  change 𝟙 _ ≫ (𝟙 _ ≫ F.map ((SrepBridge.srepDupFirst s).map' 0 1) ≫ 𝟙 _) =
    𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  exact (congrArg F.map hm).trans (Functor.map_id _ _)

/-- `d₀` is natural in the diagram variable: acting by `φ` commutes with dropping
the first chain entry. Both sides map degree `n + 1` to degree `n`. -/
theorem wbarFaceZero_mapF (W : Jᵒᵖ ⥤ Type uW) (F G : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) :
    wbarFaceZero W F n ≫ wbarMapF (W := W) n φ =
      wbarMapF (W := W) (n + 1) φ ≫ wbarFaceZero W G n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W F (n + 1) p ≫
      (wbarFaceZero W F n ≫ wbarMapF (W := W) n φ) =
    wbarIncl W F (n + 1) p ≫
      (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceZero W G n)
  have hL : wbarIncl W F (n + 1) p ≫
      (wbarFaceZero W F n ≫ wbarMapF (W := W) n φ) =
      (SrepBridge.srepFaceZeroComponent F p.1 ≫
        φ.app (wFaceZeroIdx W n p).1.left) ≫
        wbarIncl W G n (wFaceZeroIdx W n p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarFaceZero W F n ≫ wbarMapF (W := W) n φ)
        = (wbarIncl W F (n + 1) p ≫ wbarFaceZero W F n) ≫
            wbarMapF (W := W) n φ := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceZeroComponent F p.1 ≫
            wbarIncl W F n (wFaceZeroIdx W n p)) ≫
            wbarMapF (W := W) n φ := by
          exact congrArg (· ≫ wbarMapF (W := W) n φ)
            (wbarFaceZero_ι W F n p)
      _ = SrepBridge.srepFaceZeroComponent F p.1 ≫
            (wbarIncl W F n (wFaceZeroIdx W n p) ≫
              wbarMapF (W := W) n φ) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent F p.1 ≫
            (φ.app (wFaceZeroIdx W n p).1.left ≫
              wbarIncl W G n (wFaceZeroIdx W n p)) := by
          exact congrArg (SrepBridge.srepFaceZeroComponent F p.1 ≫ ·)
            (wbarMapF_ι n φ (wFaceZeroIdx W n p))
      _ = (SrepBridge.srepFaceZeroComponent F p.1 ≫
            φ.app (wFaceZeroIdx W n p).1.left) ≫
            wbarIncl W G n (wFaceZeroIdx W n p) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) p ≫
      (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceZero W G n) =
      (φ.app p.1.left ≫ SrepBridge.srepFaceZeroComponent G p.1) ≫
        wbarIncl W G n (wFaceZeroIdx W n p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceZero W G n)
        = (wbarIncl W F (n + 1) p ≫ wbarMapF (W := W) (n + 1) φ) ≫
            wbarFaceZero W G n := by
          exact (Category.assoc _ _ _).symm
      _ = (φ.app p.1.left ≫ wbarIncl W G (n + 1) p) ≫
            wbarFaceZero W G n := by
          exact congrArg (· ≫ wbarFaceZero W G n)
            (wbarMapF_ι (n + 1) φ p)
      _ = φ.app p.1.left ≫
            (wbarIncl W G (n + 1) p ≫ wbarFaceZero W G n) := by
          exact Category.assoc _ _ _
      _ = φ.app p.1.left ≫ (SrepBridge.srepFaceZeroComponent G p.1 ≫
            wbarIncl W G n (wFaceZeroIdx W n p)) := by
          exact congrArg (φ.app p.1.left ≫ ·)
            (wbarFaceZero_ι W G n p)
      _ = (φ.app p.1.left ≫ SrepBridge.srepFaceZeroComponent G p.1) ≫
            wbarIncl W G n (wFaceZeroIdx W n p) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (SrepBridge.srepFaceZeroComponent F p.1 ≫
      φ.app (wFaceZeroIdx W n p).1.left) =
      (φ.app p.1.left ≫ SrepBridge.srepFaceZeroComponent G p.1) :=
    wHCoeffFaceZeroF F G φ p.1
  calc wbarIncl W F (n + 1) p ≫
          (wbarFaceZero W F n ≫ wbarMapF (W := W) n φ)
      = (SrepBridge.srepFaceZeroComponent F p.1 ≫
          φ.app (wFaceZeroIdx W n p).1.left) ≫
          wbarIncl W G n (wFaceZeroIdx W n p) := hL
    _ = (φ.app p.1.left ≫ SrepBridge.srepFaceZeroComponent G p.1) ≫
          wbarIncl W G n (wFaceZeroIdx W n p) := by
        exact congrArg (· ≫ wbarIncl W G n (wFaceZeroIdx W n p)) hcoeff
    _ = wbarIncl W F (n + 1) p ≫
          (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceZero W G n) := hR.symm

/-- `d_last` is natural in the diagram variable: acting by `φ` commutes with dropping
the last chain entry. Both sides map degree `n + 1` to degree `n`. -/
theorem wbarFaceLast_mapF (W : Jᵒᵖ ⥤ Type uW) (F G : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) :
    wbarFaceLast W F n ≫ wbarMapF (W := W) n φ =
      wbarMapF (W := W) (n + 1) φ ≫ wbarFaceLast W G n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W F (n + 1) p ≫
      (wbarFaceLast W F n ≫ wbarMapF (W := W) n φ) =
    wbarIncl W F (n + 1) p ≫
      (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceLast W G n)
  have hL : wbarIncl W F (n + 1) p ≫
      (wbarFaceLast W F n ≫ wbarMapF (W := W) n φ) =
      (SrepBridge.srepFaceLastComponent F p.1 ≫
        φ.app (wFaceLastIdx W n p).1.left) ≫
        wbarIncl W G n (wFaceLastIdx W n p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarFaceLast W F n ≫ wbarMapF (W := W) n φ)
        = (wbarIncl W F (n + 1) p ≫ wbarFaceLast W F n) ≫
            wbarMapF (W := W) n φ := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
            wbarIncl W F n (wFaceLastIdx W n p)) ≫
            wbarMapF (W := W) n φ := by
          exact congrArg (· ≫ wbarMapF (W := W) n φ)
            (wbarFaceLast_ι W F n p)
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (wbarIncl W F n (wFaceLastIdx W n p) ≫
              wbarMapF (W := W) n φ) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (φ.app (wFaceLastIdx W n p).1.left ≫
              wbarIncl W G n (wFaceLastIdx W n p)) := by
          exact congrArg (SrepBridge.srepFaceLastComponent F p.1 ≫ ·)
            (wbarMapF_ι n φ (wFaceLastIdx W n p))
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
            φ.app (wFaceLastIdx W n p).1.left) ≫
            wbarIncl W G n (wFaceLastIdx W n p) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) p ≫
      (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceLast W G n) =
      (φ.app p.1.left ≫ SrepBridge.srepFaceLastComponent G p.1) ≫
        wbarIncl W G n (wFaceLastIdx W n p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceLast W G n)
        = (wbarIncl W F (n + 1) p ≫ wbarMapF (W := W) (n + 1) φ) ≫
            wbarFaceLast W G n := by
          exact (Category.assoc _ _ _).symm
      _ = (φ.app p.1.left ≫ wbarIncl W G (n + 1) p) ≫
            wbarFaceLast W G n := by
          exact congrArg (· ≫ wbarFaceLast W G n)
            (wbarMapF_ι (n + 1) φ p)
      _ = φ.app p.1.left ≫
            (wbarIncl W G (n + 1) p ≫ wbarFaceLast W G n) := by
          exact Category.assoc _ _ _
      _ = φ.app p.1.left ≫ (SrepBridge.srepFaceLastComponent G p.1 ≫
            wbarIncl W G n (wFaceLastIdx W n p)) := by
          exact congrArg (φ.app p.1.left ≫ ·)
            (wbarFaceLast_ι W G n p)
      _ = (φ.app p.1.left ≫ SrepBridge.srepFaceLastComponent G p.1) ≫
            wbarIncl W G n (wFaceLastIdx W n p) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (SrepBridge.srepFaceLastComponent F p.1 ≫
      φ.app (wFaceLastIdx W n p).1.left) =
      (φ.app p.1.left ≫ SrepBridge.srepFaceLastComponent G p.1) :=
    wHCoeffFaceLastF F G φ p.1
  calc wbarIncl W F (n + 1) p ≫
          (wbarFaceLast W F n ≫ wbarMapF (W := W) n φ)
      = (SrepBridge.srepFaceLastComponent F p.1 ≫
          φ.app (wFaceLastIdx W n p).1.left) ≫
          wbarIncl W G n (wFaceLastIdx W n p) := hL
    _ = (φ.app p.1.left ≫ SrepBridge.srepFaceLastComponent G p.1) ≫
          wbarIncl W G n (wFaceLastIdx W n p) := by
        exact congrArg (· ≫ wbarIncl W G n (wFaceLastIdx W n p)) hcoeff
    _ = wbarIncl W F (n + 1) p ≫
          (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceLast W G n) := hR.symm

/-- `s₀` is natural in the diagram variable: acting by `φ` commutes with repeating
the first chain entry. Both sides map degree `n` to degree `n + 1`. -/
theorem wbarDegZero_mapF (W : Jᵒᵖ ⥤ Type uW) (F G : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj p.1.left)]
    (φ : F ⟶ G) :
    wbarDegZero W F n ≫ wbarMapF (W := W) (n + 1) φ =
      wbarMapF (W := W) n φ ≫ wbarDegZero W G n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  change wbarIncl W F n p ≫
      (wbarDegZero W F n ≫ wbarMapF (W := W) (n + 1) φ) =
    wbarIncl W F n p ≫
      (wbarMapF (W := W) n φ ≫ wbarDegZero W G n)
  have hL : wbarIncl W F n p ≫
      (wbarDegZero W F n ≫ wbarMapF (W := W) (n + 1) φ) =
      (SrepBridge.srepDegZeroComponent F p.1 ≫
        φ.app (wDegZeroIdx W n p).1.left) ≫
        wbarIncl W G (n + 1) (wDegZeroIdx W n p) := by
    calc wbarIncl W F n p ≫
            (wbarDegZero W F n ≫ wbarMapF (W := W) (n + 1) φ)
        = (wbarIncl W F n p ≫ wbarDegZero W F n) ≫
            wbarMapF (W := W) (n + 1) φ := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
            wbarIncl W F (n + 1) (wDegZeroIdx W n p)) ≫
            wbarMapF (W := W) (n + 1) φ := by
          exact congrArg (· ≫ wbarMapF (W := W) (n + 1) φ)
            (wbarDegZero_ι W F n p)
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (wbarIncl W F (n + 1) (wDegZeroIdx W n p) ≫
              wbarMapF (W := W) (n + 1) φ) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (φ.app (wDegZeroIdx W n p).1.left ≫
              wbarIncl W G (n + 1) (wDegZeroIdx W n p)) := by
          exact congrArg (SrepBridge.srepDegZeroComponent F p.1 ≫ ·)
            (wbarMapF_ι (n + 1) φ (wDegZeroIdx W n p))
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
            φ.app (wDegZeroIdx W n p).1.left) ≫
            wbarIncl W G (n + 1) (wDegZeroIdx W n p) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F n p ≫
      (wbarMapF (W := W) n φ ≫ wbarDegZero W G n) =
      (φ.app p.1.left ≫ SrepBridge.srepDegZeroComponent G p.1) ≫
        wbarIncl W G (n + 1) (wDegZeroIdx W n p) := by
    calc wbarIncl W F n p ≫
            (wbarMapF (W := W) n φ ≫ wbarDegZero W G n)
        = (wbarIncl W F n p ≫ wbarMapF (W := W) n φ) ≫
            wbarDegZero W G n := by
          exact (Category.assoc _ _ _).symm
      _ = (φ.app p.1.left ≫ wbarIncl W G n p) ≫
            wbarDegZero W G n := by
          exact congrArg (· ≫ wbarDegZero W G n)
            (wbarMapF_ι n φ p)
      _ = φ.app p.1.left ≫
            (wbarIncl W G n p ≫ wbarDegZero W G n) := by
          exact Category.assoc _ _ _
      _ = φ.app p.1.left ≫ (SrepBridge.srepDegZeroComponent G p.1 ≫
            wbarIncl W G (n + 1) (wDegZeroIdx W n p)) := by
          exact congrArg (φ.app p.1.left ≫ ·)
            (wbarDegZero_ι W G n p)
      _ = (φ.app p.1.left ≫ SrepBridge.srepDegZeroComponent G p.1) ≫
            wbarIncl W G (n + 1) (wDegZeroIdx W n p) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (SrepBridge.srepDegZeroComponent F p.1 ≫
      φ.app (wDegZeroIdx W n p).1.left) =
      (φ.app p.1.left ≫ SrepBridge.srepDegZeroComponent G p.1) :=
    wHCoeffDegZeroF F G φ p.1
  calc wbarIncl W F n p ≫
          (wbarDegZero W F n ≫ wbarMapF (W := W) (n + 1) φ)
      = (SrepBridge.srepDegZeroComponent F p.1 ≫
          φ.app (wDegZeroIdx W n p).1.left) ≫
          wbarIncl W G (n + 1) (wDegZeroIdx W n p) := hL
    _ = (φ.app p.1.left ≫ SrepBridge.srepDegZeroComponent G p.1) ≫
          wbarIncl W G (n + 1) (wDegZeroIdx W n p) := by
        exact congrArg (· ≫ wbarIncl W G (n + 1) (wDegZeroIdx W n p))
          hcoeff
    _ = wbarIncl W F n p ≫
          (wbarMapF (W := W) n φ ≫ wbarDegZero W G n) := hR.symm

/-- `d₀` is natural in the weight variable: reindexing by `ψ` commutes with dropping
the first chain entry, along the definitional right-endpoint identification. -/
theorem wbarFaceZero_mapW (W W' : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)]
    (ψ : W ⟶ W') :
    wbarFaceZero W F n ≫ wbarMapW F n ψ =
      wbarMapW F (n + 1) ψ ≫ wbarFaceZero W' F n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W F (n + 1) p ≫
      (wbarFaceZero W F n ≫ wbarMapW F n ψ) =
    wbarIncl W F (n + 1) p ≫
      (wbarMapW F (n + 1) ψ ≫ wbarFaceZero W' F n)
  have hL : wbarIncl W F (n + 1) p ≫
      (wbarFaceZero W F n ≫ wbarMapW F n ψ) =
      (SrepBridge.srepFaceZeroComponent F p.1 ≫ 𝟙 _) ≫
        wbarIncl W' F n (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p)) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarFaceZero W F n ≫ wbarMapW F n ψ)
        = (wbarIncl W F (n + 1) p ≫ wbarFaceZero W F n) ≫
            wbarMapW F n ψ := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceZeroComponent F p.1 ≫
            wbarIncl W F n (wFaceZeroIdx W n p)) ≫
            wbarMapW F n ψ := by
          exact congrArg (· ≫ wbarMapW F n ψ)
            (wbarFaceZero_ι W F n p)
      _ = SrepBridge.srepFaceZeroComponent F p.1 ≫
            (wbarIncl W F n (wFaceZeroIdx W n p) ≫
              wbarMapW F n ψ) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent F p.1 ≫
            (𝟙 _ ≫
              wbarIncl W' F n
                (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p))) := by
          exact congrArg (SrepBridge.srepFaceZeroComponent F p.1 ≫ ·)
            (wbarMapW_ι F n ψ (wFaceZeroIdx W n p))
      _ = (SrepBridge.srepFaceZeroComponent F p.1 ≫ 𝟙 _) ≫
            wbarIncl W' F n
              (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p)) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) p ≫
      (wbarMapW F (n + 1) ψ ≫ wbarFaceZero W' F n) =
      (𝟙 _ ≫
          SrepBridge.srepFaceZeroComponent F
            (wMapWIdx (n + 1) ψ p).1) ≫
        wbarIncl W' F n (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p)) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarMapW F (n + 1) ψ ≫ wbarFaceZero W' F n)
        = (wbarIncl W F (n + 1) p ≫ wbarMapW F (n + 1) ψ) ≫
            wbarFaceZero W' F n := by
          exact (Category.assoc _ _ _).symm
      _ = (𝟙 _ ≫ wbarIncl W' F (n + 1) (wMapWIdx (n + 1) ψ p)) ≫
            wbarFaceZero W' F n := by
          exact congrArg (· ≫ wbarFaceZero W' F n)
            (wbarMapW_ι F (n + 1) ψ p)
      _ = 𝟙 _ ≫
            (wbarIncl W' F (n + 1) (wMapWIdx (n + 1) ψ p) ≫
              wbarFaceZero W' F n) := by
          exact Category.assoc _ _ _
      _ = 𝟙 _ ≫ (SrepBridge.srepFaceZeroComponent F
              (wMapWIdx (n + 1) ψ p).1 ≫
            wbarIncl W' F n
              (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p))) := by
          exact congrArg (𝟙 _ ≫ ·)
            (wbarFaceZero_ι W' F n (wMapWIdx (n + 1) ψ p))
      _ = (𝟙 _ ≫
              SrepBridge.srepFaceZeroComponent F
                (wMapWIdx (n + 1) ψ p).1) ≫
            wbarIncl W' F n
              (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p)) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (SrepBridge.srepFaceZeroComponent F p.1 ≫ 𝟙 _) =
      (𝟙 _ ≫
        SrepBridge.srepFaceZeroComponent F
          (wMapWIdx (n + 1) ψ p).1) := by
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  calc wbarIncl W F (n + 1) p ≫
          (wbarFaceZero W F n ≫ wbarMapW F n ψ)
      = (SrepBridge.srepFaceZeroComponent F p.1 ≫ 𝟙 _) ≫
          wbarIncl W' F n
            (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p)) := hL
    _ = (𝟙 _ ≫
            SrepBridge.srepFaceZeroComponent F
              (wMapWIdx (n + 1) ψ p).1) ≫
          wbarIncl W' F n
            (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p)) := by
        exact congrArg (· ≫ wbarIncl W' F n
          (wFaceZeroIdx W' n (wMapWIdx (n + 1) ψ p))) hcoeff
    _ = wbarIncl W F (n + 1) p ≫
          (wbarMapW F (n + 1) ψ ≫ wbarFaceZero W' F n) := hR.symm

/-- `s₀` is natural in the weight variable: reindexing by `ψ` commutes with repeating
the first chain entry, along the definitional endpoint identifications. -/
theorem wbarDegZero_mapW (W W' : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' (n + 1) => F.obj p.1.left)]
    (ψ : W ⟶ W') :
    wbarDegZero W F n ≫ wbarMapW F (n + 1) ψ =
      wbarMapW F n ψ ≫ wbarDegZero W' F n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  change wbarIncl W F n p ≫
      (wbarDegZero W F n ≫ wbarMapW F (n + 1) ψ) =
    wbarIncl W F n p ≫
      (wbarMapW F n ψ ≫ wbarDegZero W' F n)
  have hL : wbarIncl W F n p ≫
      (wbarDegZero W F n ≫ wbarMapW F (n + 1) ψ) =
      (SrepBridge.srepDegZeroComponent F p.1 ≫ 𝟙 _) ≫
        wbarIncl W' F (n + 1)
          (wDegZeroIdx W' n (wMapWIdx n ψ p)) := by
    calc wbarIncl W F n p ≫
            (wbarDegZero W F n ≫ wbarMapW F (n + 1) ψ)
        = (wbarIncl W F n p ≫ wbarDegZero W F n) ≫
            wbarMapW F (n + 1) ψ := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
            wbarIncl W F (n + 1) (wDegZeroIdx W n p)) ≫
            wbarMapW F (n + 1) ψ := by
          exact congrArg (· ≫ wbarMapW F (n + 1) ψ)
            (wbarDegZero_ι W F n p)
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (wbarIncl W F (n + 1) (wDegZeroIdx W n p) ≫
              wbarMapW F (n + 1) ψ) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (𝟙 _ ≫
              wbarIncl W' F (n + 1)
                (wDegZeroIdx W' n (wMapWIdx n ψ p))) := by
          exact congrArg (SrepBridge.srepDegZeroComponent F p.1 ≫ ·)
            (wbarMapW_ι F (n + 1) ψ (wDegZeroIdx W n p))
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫ 𝟙 _) ≫
            wbarIncl W' F (n + 1)
              (wDegZeroIdx W' n (wMapWIdx n ψ p)) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F n p ≫
      (wbarMapW F n ψ ≫ wbarDegZero W' F n) =
      (𝟙 _ ≫
          SrepBridge.srepDegZeroComponent F (wMapWIdx n ψ p).1) ≫
        wbarIncl W' F (n + 1)
          (wDegZeroIdx W' n (wMapWIdx n ψ p)) := by
    calc wbarIncl W F n p ≫
            (wbarMapW F n ψ ≫ wbarDegZero W' F n)
        = (wbarIncl W F n p ≫ wbarMapW F n ψ) ≫
            wbarDegZero W' F n := by
          exact (Category.assoc _ _ _).symm
      _ = (𝟙 _ ≫ wbarIncl W' F n (wMapWIdx n ψ p)) ≫
            wbarDegZero W' F n := by
          exact congrArg (· ≫ wbarDegZero W' F n)
            (wbarMapW_ι F n ψ p)
      _ = 𝟙 _ ≫
            (wbarIncl W' F n (wMapWIdx n ψ p) ≫
              wbarDegZero W' F n) := by
          exact Category.assoc _ _ _
      _ = 𝟙 _ ≫ (SrepBridge.srepDegZeroComponent F
              (wMapWIdx n ψ p).1 ≫
            wbarIncl W' F (n + 1)
              (wDegZeroIdx W' n (wMapWIdx n ψ p))) := by
          exact congrArg (𝟙 _ ≫ ·)
            (wbarDegZero_ι W' F n (wMapWIdx n ψ p))
      _ = (𝟙 _ ≫
              SrepBridge.srepDegZeroComponent F
                (wMapWIdx n ψ p).1) ≫
            wbarIncl W' F (n + 1)
              (wDegZeroIdx W' n (wMapWIdx n ψ p)) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (SrepBridge.srepDegZeroComponent F p.1 ≫ 𝟙 _) =
      (𝟙 _ ≫
        SrepBridge.srepDegZeroComponent F (wMapWIdx n ψ p).1) := by
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  calc wbarIncl W F n p ≫
          (wbarDegZero W F n ≫ wbarMapW F (n + 1) ψ)
      = (SrepBridge.srepDegZeroComponent F p.1 ≫ 𝟙 _) ≫
          wbarIncl W' F (n + 1)
            (wDegZeroIdx W' n (wMapWIdx n ψ p)) := hL
    _ = (𝟙 _ ≫
            SrepBridge.srepDegZeroComponent F (wMapWIdx n ψ p).1) ≫
          wbarIncl W' F (n + 1)
            (wDegZeroIdx W' n (wMapWIdx n ψ p)) := by
        exact congrArg (· ≫ wbarIncl W' F (n + 1)
          (wDegZeroIdx W' n (wMapWIdx n ψ p))) hcoeff
    _ = wbarIncl W F n p ≫
          (wbarMapW F n ψ ≫ wbarDegZero W' F n) := hR.symm

/-- `d_last` is natural in the weight variable: reindexing by `ψ` commutes with
dropping the last chain entry, by naturality of `ψ` at the last arrow. -/
theorem wbarFaceLast_mapW (W W' : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)]
    (ψ : W ⟶ W') :
    wbarFaceLast W F n ≫ wbarMapW F n ψ =
      wbarMapW F (n + 1) ψ ≫ wbarFaceLast W' F n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W F (n + 1) p ≫
      (wbarFaceLast W F n ≫ wbarMapW F n ψ) =
    wbarIncl W F (n + 1) p ≫
      (wbarMapW F (n + 1) ψ ≫ wbarFaceLast W' F n)
  have hL : wbarIncl W F (n + 1) p ≫
      (wbarFaceLast W F n ≫ wbarMapW F n ψ) =
      (SrepBridge.srepFaceLastComponent F p.1 ≫ 𝟙 _) ≫
        wbarIncl W' F n (wMapWIdx n ψ (wFaceLastIdx W n p)) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarFaceLast W F n ≫ wbarMapW F n ψ)
        = (wbarIncl W F (n + 1) p ≫ wbarFaceLast W F n) ≫
            wbarMapW F n ψ := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
            wbarIncl W F n (wFaceLastIdx W n p)) ≫
            wbarMapW F n ψ := by
          exact congrArg (· ≫ wbarMapW F n ψ)
            (wbarFaceLast_ι W F n p)
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (wbarIncl W F n (wFaceLastIdx W n p) ≫
              wbarMapW F n ψ) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (𝟙 _ ≫
              wbarIncl W' F n
                (wMapWIdx n ψ (wFaceLastIdx W n p))) := by
          exact congrArg (SrepBridge.srepFaceLastComponent F p.1 ≫ ·)
            (wbarMapW_ι F n ψ (wFaceLastIdx W n p))
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫ 𝟙 _) ≫
            wbarIncl W' F n
              (wMapWIdx n ψ (wFaceLastIdx W n p)) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) p ≫
      (wbarMapW F (n + 1) ψ ≫ wbarFaceLast W' F n) =
      (𝟙 _ ≫
          SrepBridge.srepFaceLastComponent F
            (wMapWIdx (n + 1) ψ p).1) ≫
        wbarIncl W' F n
          (wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p)) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarMapW F (n + 1) ψ ≫ wbarFaceLast W' F n)
        = (wbarIncl W F (n + 1) p ≫ wbarMapW F (n + 1) ψ) ≫
            wbarFaceLast W' F n := by
          exact (Category.assoc _ _ _).symm
      _ = (𝟙 _ ≫ wbarIncl W' F (n + 1) (wMapWIdx (n + 1) ψ p)) ≫
            wbarFaceLast W' F n := by
          exact congrArg (· ≫ wbarFaceLast W' F n)
            (wbarMapW_ι F (n + 1) ψ p)
      _ = 𝟙 _ ≫
            (wbarIncl W' F (n + 1) (wMapWIdx (n + 1) ψ p) ≫
              wbarFaceLast W' F n) := by
          exact Category.assoc _ _ _
      _ = 𝟙 _ ≫ (SrepBridge.srepFaceLastComponent F
              (wMapWIdx (n + 1) ψ p).1 ≫
            wbarIncl W' F n
              (wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p))) := by
          exact congrArg (𝟙 _ ≫ ·)
            (wbarFaceLast_ι W' F n (wMapWIdx (n + 1) ψ p))
      _ = (𝟙 _ ≫
              SrepBridge.srepFaceLastComponent F
                (wMapWIdx (n + 1) ψ p).1) ≫
            wbarIncl W' F n
              (wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p)) := by
          exact (Category.assoc _ _ _).symm
  have hidx : wMapWIdx n ψ (wFaceLastIdx W n p) =
      wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p) :=
    (wFaceLastIdx_mapW n ψ p).symm
  have hcoeff : (SrepBridge.srepFaceLastComponent F p.1 ≫ 𝟙 _) =
      (𝟙 _ ≫
        SrepBridge.srepFaceLastComponent F
          (wMapWIdx (n + 1) ψ p).1) := by
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  calc wbarIncl W F (n + 1) p ≫
          (wbarFaceLast W F n ≫ wbarMapW F n ψ)
      = (SrepBridge.srepFaceLastComponent F p.1 ≫ 𝟙 _) ≫
          wbarIncl W' F n (wMapWIdx n ψ (wFaceLastIdx W n p)) := hL
    _ = (𝟙 _ ≫
            SrepBridge.srepFaceLastComponent F
              (wMapWIdx (n + 1) ψ p).1) ≫
          wbarIncl W' F n
            (wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p)) := by
        have htrans := Limits.Sigma.eqToHom_comp_ι
          (fun q : WIdx J W' n => F.obj q.1.left) hidx.symm
        have hE : ∀ (_e : F.obj
              (wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p)).1.left =
              F.obj (wMapWIdx n ψ (wFaceLastIdx W n p)).1.left),
            eqToHom _e = 𝟙 _ := fun _ => rfl
        have hbridge : (𝟙 _ ≫
              SrepBridge.srepFaceLastComponent F
                (wMapWIdx (n + 1) ψ p).1) ≫
            wbarIncl W' F n (wMapWIdx n ψ (wFaceLastIdx W n p)) =
            (𝟙 _ ≫
              SrepBridge.srepFaceLastComponent F
                (wMapWIdx (n + 1) ψ p).1) ≫
            wbarIncl W' F n
              (wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p)) := by
          calc (𝟙 _ ≫
                SrepBridge.srepFaceLastComponent F
                  (wMapWIdx (n + 1) ψ p).1) ≫
                wbarIncl W' F n (wMapWIdx n ψ (wFaceLastIdx W n p))
              = (𝟙 _ ≫
                  SrepBridge.srepFaceLastComponent F
                    (wMapWIdx (n + 1) ψ p).1) ≫
                  (eqToHom _ ≫ wbarIncl W' F n
                    (wFaceLastIdx W' n
                      (wMapWIdx (n + 1) ψ p))) := by
                exact congrArg ((𝟙 _ ≫
                  SrepBridge.srepFaceLastComponent F
                    (wMapWIdx (n + 1) ψ p).1) ≫ ·) htrans.symm
            _ = ((𝟙 _ ≫
                  SrepBridge.srepFaceLastComponent F
                    (wMapWIdx (n + 1) ψ p).1) ≫ eqToHom _) ≫
                  wbarIncl W' F n
                    (wFaceLastIdx W' n
                      (wMapWIdx (n + 1) ψ p)) := by
                exact (Category.assoc _ _ _).symm
            _ = (𝟙 _ ≫
                  SrepBridge.srepFaceLastComponent F
                    (wMapWIdx (n + 1) ψ p).1) ≫
                  wbarIncl W' F n
                    (wFaceLastIdx W' n
                      (wMapWIdx (n + 1) ψ p)) := by
                exact congrArg (· ≫ wbarIncl W' F n
                  (wFaceLastIdx W' n (wMapWIdx (n + 1) ψ p)))
                  ((congrArg ((𝟙 _ ≫
                    SrepBridge.srepFaceLastComponent F
                      (wMapWIdx (n + 1) ψ p).1) ≫ ·) (hE _)).trans
                    (Category.comp_id _))
        exact (congrArg (· ≫ wbarIncl W' F n
          (wMapWIdx n ψ (wFaceLastIdx W n p))) hcoeff).trans hbridge
    _ = wbarIncl W F (n + 1) p ≫
          (wbarMapW F (n + 1) ψ ≫ wbarFaceLast W' F n) := hR.symm

/-- Outer `d₀`/`d_last` interchange: dropping the first entry then the last agrees
with dropping the last entry then the first. Both sides map degree `n + 2` to
degree `n`. No inner simplicial identity is claimed. -/
theorem wbarFaceZero_faceLast_interchange (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
    (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 2) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarFaceZero W F (n + 1) ≫ wbarFaceLast W F n =
      wbarFaceLast W F (n + 1) ≫ wbarFaceZero W F n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 2) => ?_)
  change wbarIncl W F (n + 2) p ≫
      (wbarFaceZero W F (n + 1) ≫ wbarFaceLast W F n) =
    wbarIncl W F (n + 2) p ≫
      (wbarFaceLast W F (n + 1) ≫ wbarFaceZero W F n)
  have hL : wbarIncl W F (n + 2) p ≫
      (wbarFaceZero W F (n + 1) ≫ wbarFaceLast W F n) =
      (SrepBridge.srepFaceZeroComponent F p.1 ≫
        SrepBridge.srepFaceLastComponent F
          (SrepBridge.srepDropFirst p.1)) ≫
        wbarIncl W F n
          ((wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p) := by
    calc wbarIncl W F (n + 2) p ≫
            (wbarFaceZero W F (n + 1) ≫ wbarFaceLast W F n)
        = (wbarIncl W F (n + 2) p ≫ wbarFaceZero W F (n + 1)) ≫
            wbarFaceLast W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceZeroComponent F p.1 ≫
            wbarIncl W F (n + 1) (wFaceZeroIdx W (n + 1) p)) ≫
            wbarFaceLast W F n := by
          exact congrArg (· ≫ wbarFaceLast W F n)
            (wbarFaceZero_ι W F (n + 1) p)
      _ = SrepBridge.srepFaceZeroComponent F p.1 ≫
            (wbarIncl W F (n + 1) (wFaceZeroIdx W (n + 1) p) ≫
              wbarFaceLast W F n) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent F p.1 ≫
            (SrepBridge.srepFaceLastComponent F
              (wFaceZeroIdx W (n + 1) p).1 ≫
              wbarIncl W F n
                (wFaceLastIdx W n (wFaceZeroIdx W (n + 1) p))) := by
          exact congrArg (SrepBridge.srepFaceZeroComponent F p.1 ≫ ·)
            (wbarFaceLast_ι W F n (wFaceZeroIdx W (n + 1) p))
      _ = (SrepBridge.srepFaceZeroComponent F p.1 ≫
            SrepBridge.srepFaceLastComponent F
              (SrepBridge.srepDropFirst p.1)) ≫
            wbarIncl W F n
              ((wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 2) p ≫
      (wbarFaceLast W F (n + 1) ≫ wbarFaceZero W F n) =
      (SrepBridge.srepFaceLastComponent F p.1 ≫
        SrepBridge.srepFaceZeroComponent F
          (SrepBridge.srepDropLast p.1)) ≫
        wbarIncl W F n
          ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p) := by
    calc wbarIncl W F (n + 2) p ≫
            (wbarFaceLast W F (n + 1) ≫ wbarFaceZero W F n)
        = (wbarIncl W F (n + 2) p ≫ wbarFaceLast W F (n + 1)) ≫
            wbarFaceZero W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
            wbarIncl W F (n + 1) (wFaceLastIdx W (n + 1) p)) ≫
            wbarFaceZero W F n := by
          exact congrArg (· ≫ wbarFaceZero W F n)
            (wbarFaceLast_ι W F (n + 1) p)
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (wbarIncl W F (n + 1) (wFaceLastIdx W (n + 1) p) ≫
              wbarFaceZero W F n) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (SrepBridge.srepFaceZeroComponent F
              (wFaceLastIdx W (n + 1) p).1 ≫
              wbarIncl W F n
                (wFaceZeroIdx W n (wFaceLastIdx W (n + 1) p))) := by
          exact congrArg (SrepBridge.srepFaceLastComponent F p.1 ≫ ·)
            (wbarFaceZero_ι W F n (wFaceLastIdx W (n + 1) p))
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
            SrepBridge.srepFaceZeroComponent F
              (SrepBridge.srepDropLast p.1)) ≫
            wbarIncl W F n
              ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p) := by
          exact (Category.assoc _ _ _).symm
  have hidx : (wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p =
      (wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p :=
    congrFun (wFaceZero_faceLast_idx W n) p
  have hcoeff : (SrepBridge.srepFaceZeroComponent F p.1 ≫
      SrepBridge.srepFaceLastComponent F (SrepBridge.srepDropFirst p.1)) =
      (SrepBridge.srepFaceLastComponent F p.1 ≫
        SrepBridge.srepFaceZeroComponent F
          (SrepBridge.srepDropLast p.1)) :=
    wHCoeffInterFL F p.1
  calc wbarIncl W F (n + 2) p ≫
          (wbarFaceZero W F (n + 1) ≫ wbarFaceLast W F n)
      = (SrepBridge.srepFaceZeroComponent F p.1 ≫
          SrepBridge.srepFaceLastComponent F
            (SrepBridge.srepDropFirst p.1)) ≫
          wbarIncl W F n
            ((wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p) := hL
    _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
          SrepBridge.srepFaceZeroComponent F
            (SrepBridge.srepDropLast p.1)) ≫
          wbarIncl W F n
            ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p) := by
        have htrans := Limits.Sigma.eqToHom_comp_ι
          (fun q : WIdx J W n => F.obj q.1.left) hidx.symm
        have hE : ∀ (_e : F.obj
              ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p).1.left =
              F.obj ((wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p).1.left),
            eqToHom _e = 𝟙 _ := fun _ => rfl
        have hbridge : (SrepBridge.srepFaceLastComponent F p.1 ≫
              SrepBridge.srepFaceZeroComponent F
                (SrepBridge.srepDropLast p.1)) ≫
            wbarIncl W F n
              ((wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p) =
            (SrepBridge.srepFaceLastComponent F p.1 ≫
              SrepBridge.srepFaceZeroComponent F
                (SrepBridge.srepDropLast p.1)) ≫
            wbarIncl W F n
              ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p) := by
          calc (SrepBridge.srepFaceLastComponent F p.1 ≫
                SrepBridge.srepFaceZeroComponent F
                  (SrepBridge.srepDropLast p.1)) ≫
                wbarIncl W F n
                  ((wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p)
              = (SrepBridge.srepFaceLastComponent F p.1 ≫
                  SrepBridge.srepFaceZeroComponent F
                    (SrepBridge.srepDropLast p.1)) ≫
                  (eqToHom _ ≫ wbarIncl W F n
                    ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p)) := by
                exact congrArg ((SrepBridge.srepFaceLastComponent F p.1 ≫
                  SrepBridge.srepFaceZeroComponent F
                    (SrepBridge.srepDropLast p.1)) ≫ ·) htrans.symm
            _ = ((SrepBridge.srepFaceLastComponent F p.1 ≫
                  SrepBridge.srepFaceZeroComponent F
                    (SrepBridge.srepDropLast p.1)) ≫ eqToHom _) ≫
                  wbarIncl W F n
                    ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p) := by
                exact (Category.assoc _ _ _).symm
            _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
                  SrepBridge.srepFaceZeroComponent F
                    (SrepBridge.srepDropLast p.1)) ≫
                  wbarIncl W F n
                    ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p) := by
                exact congrArg (· ≫ wbarIncl W F n
                  ((wFaceZeroIdx W n ∘ wFaceLastIdx W (n + 1)) p))
                  ((congrArg ((SrepBridge.srepFaceLastComponent F p.1 ≫
                    SrepBridge.srepFaceZeroComponent F
                      (SrepBridge.srepDropLast p.1)) ≫ ·) (hE _)).trans
                    (Category.comp_id _))
        exact (congrArg (· ≫ wbarIncl W F n
          ((wFaceLastIdx W n ∘ wFaceZeroIdx W (n + 1)) p)) hcoeff).trans
          hbridge
    _ = wbarIncl W F (n + 2) p ≫
          (wbarFaceLast W F (n + 1) ≫ wbarFaceZero W F n) := hR.symm

/-- Outer `s₀`/`d₀` section law: repeating the first entry then dropping it is the
identity. This is the degreewise outer degeneracy section, not a full simplicial
identity. -/
theorem wbarDegZero_faceZero_section (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)] :
    wbarDegZero W F n ≫ wbarFaceZero W F n = 𝟙 (wbarObj W F n) := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  change wbarIncl W F n p ≫ (wbarDegZero W F n ≫ wbarFaceZero W F n) =
    wbarIncl W F n p ≫ 𝟙 (wbarObj W F n)
  have hL : wbarIncl W F n p ≫
      (wbarDegZero W F n ≫ wbarFaceZero W F n) =
      (SrepBridge.srepDegZeroComponent F p.1 ≫
        SrepBridge.srepFaceZeroComponent F
          (SrepBridge.srepDupFirst p.1)) ≫
        wbarIncl W F n (wFaceZeroIdx W n (wDegZeroIdx W n p)) := by
    calc wbarIncl W F n p ≫
            (wbarDegZero W F n ≫ wbarFaceZero W F n)
        = (wbarIncl W F n p ≫ wbarDegZero W F n) ≫
            wbarFaceZero W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
            wbarIncl W F (n + 1) (wDegZeroIdx W n p)) ≫
            wbarFaceZero W F n := by
          exact congrArg (· ≫ wbarFaceZero W F n)
            (wbarDegZero_ι W F n p)
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (wbarIncl W F (n + 1) (wDegZeroIdx W n p) ≫
              wbarFaceZero W F n) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (SrepBridge.srepFaceZeroComponent F
              (wDegZeroIdx W n p).1 ≫
              wbarIncl W F n
                (wFaceZeroIdx W n (wDegZeroIdx W n p))) := by
          exact congrArg (SrepBridge.srepDegZeroComponent F p.1 ≫ ·)
            (wbarFaceZero_ι W F n (wDegZeroIdx W n p))
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
            SrepBridge.srepFaceZeroComponent F
              (SrepBridge.srepDupFirst p.1)) ≫
            wbarIncl W F n (wFaceZeroIdx W n (wDegZeroIdx W n p)) := by
          exact (Category.assoc _ _ _).symm
  have hidx : wFaceZeroIdx W n (wDegZeroIdx W n p) = p := by
    obtain ⟨s, w⟩ := p
    rfl
  calc wbarIncl W F n p ≫ (wbarDegZero W F n ≫ wbarFaceZero W F n)
      = (SrepBridge.srepDegZeroComponent F p.1 ≫
          SrepBridge.srepFaceZeroComponent F
            (SrepBridge.srepDupFirst p.1)) ≫
          wbarIncl W F n (wFaceZeroIdx W n (wDegZeroIdx W n p)) := hL
    _ = 𝟙 (F.obj p.1.left) ≫ wbarIncl W F n p := by
        have htrans := Limits.Sigma.eqToHom_comp_ι
          (fun q : WIdx J W n => F.obj q.1.left) hidx.symm
        have hE : ∀ (_e : F.obj p.1.left =
              F.obj (wFaceZeroIdx W n (wDegZeroIdx W n p)).1.left),
            eqToHom _e = 𝟙 _ := fun _ => rfl
        calc (SrepBridge.srepDegZeroComponent F p.1 ≫
              SrepBridge.srepFaceZeroComponent F
                (SrepBridge.srepDupFirst p.1)) ≫
              wbarIncl W F n (wFaceZeroIdx W n (wDegZeroIdx W n p))
            = 𝟙 (F.obj p.1.left) ≫
                wbarIncl W F n
                  (wFaceZeroIdx W n (wDegZeroIdx W n p)) := by
              exact congrArg (· ≫ wbarIncl W F n
                (wFaceZeroIdx W n (wDegZeroIdx W n p)))
                (wHCoeffSection F p.1)
          _ = 𝟙 (F.obj p.1.left) ≫
                (eqToHom _ ≫ wbarIncl W F n p) := by
              exact congrArg (𝟙 (F.obj p.1.left) ≫ ·) htrans.symm
          _ = (𝟙 (F.obj p.1.left) ≫ eqToHom _) ≫
                wbarIncl W F n p := by
              exact (Category.assoc _ _ _).symm
          _ = 𝟙 (F.obj p.1.left) ≫ wbarIncl W F n p := by
              exact congrArg (· ≫ wbarIncl W F n p)
                ((congrArg (𝟙 (F.obj p.1.left) ≫ ·) (hE _)).trans
                  (Category.comp_id _))
    _ = wbarIncl W F n p ≫ 𝟙 (wbarObj W F n) := by
        exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Outer `s₀`/`d_last` interchange: repeating the first entry then dropping the last
agrees with dropping the last entry then repeating the first. Both sides are
endomorphisms of degree `n + 1`. No inner simplicial identity is claimed. -/
theorem wbarDegZero_faceLast_interchange (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
    (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 2) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarDegZero W F (n + 1) ≫ wbarFaceLast W F (n + 1) =
      wbarFaceLast W F n ≫ wbarDegZero W F n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W F (n + 1) p ≫
      (wbarDegZero W F (n + 1) ≫ wbarFaceLast W F (n + 1)) =
    wbarIncl W F (n + 1) p ≫
      (wbarFaceLast W F n ≫ wbarDegZero W F n)
  have hL : wbarIncl W F (n + 1) p ≫
      (wbarDegZero W F (n + 1) ≫ wbarFaceLast W F (n + 1)) =
      (SrepBridge.srepDegZeroComponent F p.1 ≫
        SrepBridge.srepFaceLastComponent F
          (SrepBridge.srepDupFirst p.1)) ≫
        wbarIncl W F (n + 1)
          ((wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarDegZero W F (n + 1) ≫ wbarFaceLast W F (n + 1))
        = (wbarIncl W F (n + 1) p ≫ wbarDegZero W F (n + 1)) ≫
            wbarFaceLast W F (n + 1) := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
            wbarIncl W F (n + 2) (wDegZeroIdx W (n + 1) p)) ≫
            wbarFaceLast W F (n + 1) := by
          exact congrArg (· ≫ wbarFaceLast W F (n + 1))
            (wbarDegZero_ι W F (n + 1) p)
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (wbarIncl W F (n + 2) (wDegZeroIdx W (n + 1) p) ≫
              wbarFaceLast W F (n + 1)) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepDegZeroComponent F p.1 ≫
            (SrepBridge.srepFaceLastComponent F
              (wDegZeroIdx W (n + 1) p).1 ≫
              wbarIncl W F (n + 1)
                (wFaceLastIdx W (n + 1)
                  (wDegZeroIdx W (n + 1) p))) := by
          exact congrArg (SrepBridge.srepDegZeroComponent F p.1 ≫ ·)
            (wbarFaceLast_ι W F (n + 1) (wDegZeroIdx W (n + 1) p))
      _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
            SrepBridge.srepFaceLastComponent F
              (SrepBridge.srepDupFirst p.1)) ≫
            wbarIncl W F (n + 1)
              ((wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1))
                p) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) p ≫
      (wbarFaceLast W F n ≫ wbarDegZero W F n) =
      (SrepBridge.srepFaceLastComponent F p.1 ≫
        SrepBridge.srepDegZeroComponent F
          (SrepBridge.srepDropLast p.1)) ≫
        wbarIncl W F (n + 1)
          ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarFaceLast W F n ≫ wbarDegZero W F n)
        = (wbarIncl W F (n + 1) p ≫ wbarFaceLast W F n) ≫
            wbarDegZero W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
            wbarIncl W F n (wFaceLastIdx W n p)) ≫
            wbarDegZero W F n := by
          exact congrArg (· ≫ wbarDegZero W F n)
            (wbarFaceLast_ι W F n p)
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (wbarIncl W F n (wFaceLastIdx W n p) ≫
              wbarDegZero W F n) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent F p.1 ≫
            (SrepBridge.srepDegZeroComponent F
              (wFaceLastIdx W n p).1 ≫
              wbarIncl W F (n + 1)
                (wDegZeroIdx W n (wFaceLastIdx W n p))) := by
          exact congrArg (SrepBridge.srepFaceLastComponent F p.1 ≫ ·)
            (wbarDegZero_ι W F n (wFaceLastIdx W n p))
      _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
            SrepBridge.srepDegZeroComponent F
              (SrepBridge.srepDropLast p.1)) ≫
            wbarIncl W F (n + 1)
              ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p) := by
          exact (Category.assoc _ _ _).symm
  have hidx : (wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) p =
      (wDegZeroIdx W n ∘ wFaceLastIdx W n) p :=
    congrFun (wDegZero_faceLast_idx W n) p
  have hcoeff : (SrepBridge.srepDegZeroComponent F p.1 ≫
      SrepBridge.srepFaceLastComponent F (SrepBridge.srepDupFirst p.1)) =
      (SrepBridge.srepFaceLastComponent F p.1 ≫
        SrepBridge.srepDegZeroComponent F
          (SrepBridge.srepDropLast p.1)) :=
    wHCoeffInterDL F p.1
  calc wbarIncl W F (n + 1) p ≫
          (wbarDegZero W F (n + 1) ≫ wbarFaceLast W F (n + 1))
      = (SrepBridge.srepDegZeroComponent F p.1 ≫
          SrepBridge.srepFaceLastComponent F
            (SrepBridge.srepDupFirst p.1)) ≫
          wbarIncl W F (n + 1)
            ((wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) p) := hL
    _ = (SrepBridge.srepFaceLastComponent F p.1 ≫
          SrepBridge.srepDegZeroComponent F
            (SrepBridge.srepDropLast p.1)) ≫
          wbarIncl W F (n + 1)
            ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p) := by
        have htrans := Limits.Sigma.eqToHom_comp_ι
          (fun q : WIdx J W (n + 1) => F.obj q.1.left) hidx.symm
        have hE : ∀ (_e : F.obj
              ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p).1.left =
              F.obj ((wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) p).1.left),
            eqToHom _e = 𝟙 _ := fun _ => rfl
        have hbridge : (SrepBridge.srepDegZeroComponent F p.1 ≫
              SrepBridge.srepFaceLastComponent F
                (SrepBridge.srepDupFirst p.1)) ≫
            wbarIncl W F (n + 1)
              ((wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) p) =
            (SrepBridge.srepDegZeroComponent F p.1 ≫
              SrepBridge.srepFaceLastComponent F
                (SrepBridge.srepDupFirst p.1)) ≫
            wbarIncl W F (n + 1)
              ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p) := by
          calc (SrepBridge.srepDegZeroComponent F p.1 ≫
                SrepBridge.srepFaceLastComponent F
                  (SrepBridge.srepDupFirst p.1)) ≫
                wbarIncl W F (n + 1)
                  ((wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) p)
              = (SrepBridge.srepDegZeroComponent F p.1 ≫
                  SrepBridge.srepFaceLastComponent F
                    (SrepBridge.srepDupFirst p.1)) ≫
                  (eqToHom _ ≫ wbarIncl W F (n + 1)
                    ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p)) := by
                exact congrArg ((SrepBridge.srepDegZeroComponent F p.1 ≫
                  SrepBridge.srepFaceLastComponent F
                    (SrepBridge.srepDupFirst p.1)) ≫ ·) htrans.symm
            _ = ((SrepBridge.srepDegZeroComponent F p.1 ≫
                  SrepBridge.srepFaceLastComponent F
                    (SrepBridge.srepDupFirst p.1)) ≫ eqToHom _) ≫
                  wbarIncl W F (n + 1)
                    ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p) := by
                exact (Category.assoc _ _ _).symm
            _ = (SrepBridge.srepDegZeroComponent F p.1 ≫
                  SrepBridge.srepFaceLastComponent F
                    (SrepBridge.srepDupFirst p.1)) ≫
                  wbarIncl W F (n + 1)
                    ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p) := by
                exact congrArg (· ≫ wbarIncl W F (n + 1)
                  ((wDegZeroIdx W n ∘ wFaceLastIdx W n) p))
                  ((congrArg ((SrepBridge.srepDegZeroComponent F p.1 ≫
                    SrepBridge.srepFaceLastComponent F
                      (SrepBridge.srepDupFirst p.1)) ≫ ·) (hE _)).trans
                    (Category.comp_id _))
        exact (congrArg (· ≫ wbarIncl W F (n + 1)
          ((wFaceLastIdx W (n + 1) ∘ wDegZeroIdx W (n + 1)) p))
          hcoeff).trans hbridge
    _ = wbarIncl W F (n + 1) p ≫
          (wbarFaceLast W F n ≫ wbarDegZero W F n) := hR.symm

end StrictOrdinaryWeightedBar
end CategoryTheory
