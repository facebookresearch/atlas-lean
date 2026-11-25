/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.WeightedBarOuter

/-!
# Strict inner-operator packet for the ordinary weighted bar

This module is the strict inner-operator packet for the ordinary weighted bar
from `WeightedBar` / `WeightedBarOuter`. It provides reusable interior
omit/duplicate index operators and the interior face/degeneracy maps, with
naturality of each interior operator in the diagram variable `F` and in the
weight variable `W`. Every proof is degreewise through the
`Limits.Sigma` inclusion API (`Sigma.hom_ext`, `Sigma.ι_comp_map'`,
`Sigma.eqToHom_comp_ι`), exactly mirroring the outer packet.

Orientation: an interior face `dᵢ` drops an interior chain entry through the
`StrictOmitDup.omitAt` functor and transports the diagram coefficient
along the propositionally preserved left endpoint; the weight element is
transported along the propositionally preserved right endpoint. An interior
degeneracy `sᵢ` duplicates an entry through
`StrictOmitDup.dupAt` with the same transport pattern. Interior faces
act by pure transport on coefficients (the left endpoint vertex itself is
unchanged, unlike `d₀` which moves it along the first arrow), so no arrow
action is introduced.

Endpoint facts used: omission at `i` fixes the zeroth vertex when `i ≠ 0`
(`Fin.succAbove_ne_zero_zero`) and fixes the last vertex when
`i ≠ Fin.last _` (`Fin.succAbove_ne_last_last`); duplication fixes both
endpoints unconditionally (`Fin.predAbove_right_zero` and
`Fin.predAbove_right_last`). All cross-length moves are explicit `eqToHom`
transports through these named endpoint lemmas; no propositional cross-length
equality is replaced by bare `rfl`. Comparisons stay maps and isomorphisms,
never definitional identifications, following the generic comparison and
endpoint-transport discipline.

Hypotheses: each statement assumes exactly the coproduct instances of the
degrees it mentions, with the same explicit families as `WeightedBar`, plus
`[NeZero (n + 1)]` wherever the left-endpoint `Fin` fact requires it (matching
`StrictOmitDup`, which threads the same instance).

Nonclaims and exact blocker: no simplicial identity is proved here, hence no
`SimplicialObject.Data` packaging (which would require `δ_comp_δ`,
`δ_comp_σ_of_le`, `δ_comp_σ_self`, `δ_comp_σ_succ`, `δ_comp_σ_of_gt`, and
`σ_comp_σ` for every applicable interior/outer position pair), no
`GenRel`/genuine simplicial transport, and no promotion of the pointwise
`wbarSectionComp` family to a simplicial map (which additionally needs full
naturality plus all identities). No enriched copowers or coends, no
profunctor composition, and no realization or homotopy-colimit conclusion. The
iterated omit/duplicate chain identities are in `StrictOmitDupChain`
(`δδ`, `σσ`, and the below/self/successor/above `δσ` families with `map'`
arrow transports); `StrictOmitDup` supplies the associator
comparison isomorphisms (`omitOmitObjIso`, `dupDupObjIso`, `omitDupObjIso`,
`mapWhiskerObjIso`) and the
endpoint coherence equalities `dropLast_dupFirst_eq` and
`dupFirst_lastArrow_eq`. Assembly of the total weighted face/degeneracy
operators into `SimplicialObject.Data` is in `WeightedBarData`, genuine
promotion is in `WeightedBarSimplicial`, and separate diagram/weight naturality
with the mixed square is in `WeightedBarMapF` / `WeightedBarMapW` /
`WeightedBarMapFW`; none of those are proved here.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOrdinaryWeightedBar

universe vJ uJ vC uC uW

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- Interior omission fixes the zeroth vertex: omitting at `i ≠ 0` preserves
the left endpoint object. This is the left-endpoint transport used by interior
face coefficients. -/
@[simp]
theorem wOmitInner_obj_zero {n : ℕ} [NeZero (n + 1)] {i : Fin (n + 2)}
    (hi0 : i ≠ 0) (s : SrepBridge.SrepIdx J (n + 1)) :
    ((StrictOmitDup.omitAt i).obj s).obj 0 = s.obj 0 :=
  congrArg s.obj (Fin.succAbove_ne_zero_zero hi0)

/-- Interior omission fixes the last vertex: omitting at `i ≠ Fin.last _`
preserves the right endpoint object. This is the right-endpoint transport used
by interior face weight elements. -/
@[simp]
theorem wOmitInner_obj_last {n : ℕ} {i : Fin (n + 2)}
    (hiLast : i ≠ Fin.last (n + 1)) (s : SrepBridge.SrepIdx J (n + 1)) :
    ((StrictOmitDup.omitAt i).obj s).obj (Fin.last n) =
      s.obj (Fin.last (n + 1)) :=
  congrArg s.obj (Fin.succAbove_ne_last_last hiLast)

/-- Duplication fixes the zeroth vertex unconditionally: duplicating at any
position preserves the left endpoint object. This is the left-endpoint
transport used by interior degeneracy coefficients. -/
@[simp]
theorem wDupInner_obj_zero {n : ℕ} [NeZero (n + 1)] {i : Fin (n + 1)}
    (s : SrepBridge.SrepIdx J n) :
    ((StrictOmitDup.dupAt i).obj s).obj 0 = s.obj 0 :=
  congrArg s.obj (Fin.predAbove_right_zero (i := i))

/-- Duplication fixes the last vertex unconditionally: duplicating at any
position preserves the right endpoint object. This is the right-endpoint
transport used by interior degeneracy weight elements. -/
@[simp]
theorem wDupInner_obj_last {n : ℕ} {i : Fin (n + 1)}
    (s : SrepBridge.SrepIdx J n) :
    ((StrictOmitDup.dupAt i).obj s).obj (Fin.last (n + 1)) =
      s.obj (Fin.last n) :=
  congrArg s.obj (Fin.predAbove_right_last)

/-- Index map of an interior face `dᵢ`: omit the chain entry at `i`, acting on
the weight element by transport along the preserved right endpoint. Only
`i ≠ Fin.last _` is required here; the left-endpoint condition `i ≠ 0` is
enforced at the operator coefficient level. -/
def wFaceInnerIdx (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) (i : Fin (n + 2))
    (hiLast : i ≠ Fin.last (n + 1)) (p : WIdx J W (n + 1)) : WIdx J W n :=
  ⟨(StrictOmitDup.omitAt i).obj p.1,
    W.map (eqToHom (wOmitInner_obj_last hiLast p.1 :
      ((StrictOmitDup.omitAt i).obj p.1).right = p.1.right)).op p.2⟩

/-- Index map of an interior degeneracy `sᵢ`: duplicate the chain entry at
`i`; both endpoint preservations for duplication are unconditional, so no
position hypothesis is needed. -/
def wDegInnerIdx (W : Jᵒᵖ ⥤ Type uW) (n : ℕ) (i : Fin (n + 1))
    (p : WIdx J W n) : WIdx J W (n + 1) :=
  ⟨(StrictOmitDup.dupAt i).obj p.1,
    W.map (eqToHom (wDupInner_obj_last p.1 :
      ((StrictOmitDup.dupAt i).obj p.1).right = p.1.right)).op p.2⟩

/-- Coefficient map of an interior face at the chain `s`: pure transport along
the preserved left endpoint. Unlike `d₀`, no arrow action occurs because the
left endpoint vertex itself is unchanged. -/
def wFaceInnerComponent (F : J ⥤ C) {n : ℕ} (i : Fin (n + 2)) (hi0 : i ≠ 0)
    [NeZero (n + 1)] (s : SrepBridge.SrepIdx J (n + 1)) :
    F.obj s.left ⟶ F.obj (((StrictOmitDup.omitAt i).obj s).left) :=
  eqToHom (congrArg F.obj ((wOmitInner_obj_zero hi0 s :
    ((StrictOmitDup.omitAt i).obj s).left = s.left).symm))

/-- Coefficient map of an interior degeneracy at the chain `s`: pure transport
along the preserved left endpoint. -/
def wDegInnerComponent (F : J ⥤ C) {n : ℕ} (i : Fin (n + 1))
    [NeZero (n + 1)] (s : SrepBridge.SrepIdx J n) :
    F.obj s.left ⟶ F.obj (((StrictOmitDup.dupAt i).obj s).left) :=
  eqToHom (congrArg F.obj ((wDupInner_obj_zero s :
    ((StrictOmitDup.dupAt i).obj s).left = s.left).symm))

/-- Interior face `dᵢ` of the strict ordinary weighted bar (for `i ≠ 0` and
`i ≠ Fin.last _`): omit the `i`-th chain entry, transporting the diagram
coefficient and the weight element along the preserved endpoints. -/
noncomputable def wbarFaceInner (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarObj W F (n + 1) ⟶ wbarObj W F n :=
  Limits.Sigma.map' (wFaceInnerIdx W n i hiLast)
    (fun p => wFaceInnerComponent F i hi0 p.1)

/-- Computation rule for `wbarFaceInner`. -/
theorem wbarFaceInner_ι (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    (p : WIdx J W (n + 1)) :
    wbarIncl W F (n + 1) p ≫ wbarFaceInner W F n i hi0 hiLast =
      wFaceInnerComponent F i hi0 p.1 ≫
        wbarIncl W F n (wFaceInnerIdx W n i hiLast p) := by
  change Limits.Sigma.ι (fun p : WIdx J W (n + 1) => F.obj p.1.left) p ≫
      Limits.Sigma.map' (wFaceInnerIdx W n i hiLast)
        (fun p => wFaceInnerComponent F i hi0 p.1) =
    wFaceInnerComponent F i hi0 p.1 ≫
      Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left)
        (wFaceInnerIdx W n i hiLast p)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- Interior degeneracy `sᵢ` of the strict ordinary weighted bar: duplicate
the `i`-th chain entry, transporting the diagram coefficient and the weight
element along the preserved endpoints. -/
noncomputable def wbarDegInner (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    (i : Fin (n + 1)) [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)] :
    wbarObj W F n ⟶ wbarObj W F (n + 1) :=
  Limits.Sigma.map' (wDegInnerIdx W n i)
    (fun p => wDegInnerComponent F i p.1)

/-- Computation rule for `wbarDegInner`. -/
theorem wbarDegInner_ι (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    (i : Fin (n + 1)) [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    (p : WIdx J W n) :
    wbarIncl W F n p ≫ wbarDegInner W F n i =
      wDegInnerComponent F i p.1 ≫
        wbarIncl W F (n + 1) (wDegInnerIdx W n i p) := by
  change Limits.Sigma.ι (fun p : WIdx J W n => F.obj p.1.left) p ≫
      Limits.Sigma.map' (wDegInnerIdx W n i)
        (fun p => wDegInnerComponent F i p.1) =
    wDegInnerComponent F i p.1 ≫
      Limits.Sigma.ι (fun p : WIdx J W (n + 1) => F.obj p.1.left)
        (wDegInnerIdx W n i p)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- Internal: slide a naturality square past endpoint identifications.
Mirrors the outer packet's internal slide for transport coefficients. -/
private theorem wSlideInner {F G : J ⥤ C} (φ : F ⟶ G) {X Y : J}
    {h : X = Y} :
    eqToHom (congrArg F.obj h) ≫ φ.app Y =
      φ.app X ≫ eqToHom (congrArg G.obj h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Internal: the interior-face index map commutes with weight reindexing, by
naturality of the weight morphism at the endpoint transport. The chain
component is unchanged on both sides. -/
private theorem wFaceInnerIdx_mapW {W W' : Jᵒᵖ ⥤ Type uW} (n : ℕ)
    (i : Fin (n + 2)) (hiLast : i ≠ Fin.last (n + 1)) (ψ : W ⟶ W')
    (p : WIdx J W (n + 1)) :
    wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p) =
      wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p) := by
  obtain ⟨s, w⟩ := p
  have hR : ((StrictOmitDup.omitAt i).obj s).right = s.right :=
    wOmitInner_obj_last hiLast s
  have hnat := ψ.naturality (eqToHom hR).op
  have helem := congrArg (fun e : W.obj _ ⟶ W'.obj _ => e w) hnat
  refine congrArg (fun w' => (⟨(StrictOmitDup.omitAt i).obj s, w'⟩ :
    WIdx J W' n)) ?_
  exact helem.symm

/-- Internal: the interior-degeneracy index map commutes with weight
reindexing, by naturality of the weight morphism at the endpoint transport.
The chain component is unchanged on both sides. -/
private theorem wDegInnerIdx_mapW {W W' : Jᵒᵖ ⥤ Type uW} (n : ℕ)
    (i : Fin (n + 1)) (ψ : W ⟶ W') (p : WIdx J W n) :
    wDegInnerIdx W' n i (wMapWIdx n ψ p) =
      wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p) := by
  obtain ⟨s, w⟩ := p
  have hR : ((StrictOmitDup.dupAt i).obj s).right = s.right :=
    wDupInner_obj_last s
  have hnat := ψ.naturality (eqToHom hR).op
  have helem := congrArg (fun e : W.obj _ ⟶ W'.obj _ => e w) hnat
  refine congrArg (fun w' => (⟨(StrictOmitDup.dupAt i).obj s, w'⟩ :
    WIdx J W' (n + 1))) ?_
  exact helem.symm

/-- Interior `dᵢ` is natural in the diagram variable: acting by `φ` commutes
with omitting the `i`-th chain entry. Both sides map degree `n + 1` to
degree `n`. -/
theorem wbarFaceInner_mapF (W : Jᵒᵖ ⥤ Type uW) (F G : J ⥤ C) (n : ℕ)
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) :
    wbarFaceInner W F n i hi0 hiLast ≫ wbarMapF (W := W) n φ =
      wbarMapF (W := W) (n + 1) φ ≫ wbarFaceInner W G n i hi0 hiLast := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W F (n + 1) p ≫
      (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapF (W := W) n φ) =
    wbarIncl W F (n + 1) p ≫
      (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceInner W G n i hi0 hiLast)
  have hL : wbarIncl W F (n + 1) p ≫
      (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapF (W := W) n φ) =
      (wFaceInnerComponent F i hi0 p.1 ≫
        φ.app (wFaceInnerIdx W n i hiLast p).1.left) ≫
        wbarIncl W G n (wFaceInnerIdx W n i hiLast p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapF (W := W) n φ)
        = (wbarIncl W F (n + 1) p ≫ wbarFaceInner W F n i hi0 hiLast) ≫
            wbarMapF (W := W) n φ := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F i hi0 p.1 ≫
            wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) ≫
            wbarMapF (W := W) n φ := by
          exact congrArg (· ≫ wbarMapF (W := W) n φ)
            (wbarFaceInner_ι W F n i hi0 hiLast p)
      _ = wFaceInnerComponent F i hi0 p.1 ≫
            (wbarIncl W F n (wFaceInnerIdx W n i hiLast p) ≫
              wbarMapF (W := W) n φ) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F i hi0 p.1 ≫
            (φ.app (wFaceInnerIdx W n i hiLast p).1.left ≫
              wbarIncl W G n (wFaceInnerIdx W n i hiLast p)) := by
          exact congrArg (wFaceInnerComponent F i hi0 p.1 ≫ ·)
            (wbarMapF_ι n φ (wFaceInnerIdx W n i hiLast p))
      _ = (wFaceInnerComponent F i hi0 p.1 ≫
            φ.app (wFaceInnerIdx W n i hiLast p).1.left) ≫
            wbarIncl W G n (wFaceInnerIdx W n i hiLast p) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) p ≫
      (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceInner W G n i hi0 hiLast) =
      (φ.app p.1.left ≫ wFaceInnerComponent G i hi0 p.1) ≫
        wbarIncl W G n (wFaceInnerIdx W n i hiLast p) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarMapF (W := W) (n + 1) φ ≫ wbarFaceInner W G n i hi0 hiLast)
        = (wbarIncl W F (n + 1) p ≫ wbarMapF (W := W) (n + 1) φ) ≫
            wbarFaceInner W G n i hi0 hiLast := by
          exact (Category.assoc _ _ _).symm
      _ = (φ.app p.1.left ≫ wbarIncl W G (n + 1) p) ≫
            wbarFaceInner W G n i hi0 hiLast := by
          exact congrArg (· ≫ wbarFaceInner W G n i hi0 hiLast)
            (wbarMapF_ι (n + 1) φ p)
      _ = φ.app p.1.left ≫
            (wbarIncl W G (n + 1) p ≫ wbarFaceInner W G n i hi0 hiLast) := by
          exact Category.assoc _ _ _
      _ = φ.app p.1.left ≫ (wFaceInnerComponent G i hi0 p.1 ≫
            wbarIncl W G n (wFaceInnerIdx W n i hiLast p)) := by
          exact congrArg (φ.app p.1.left ≫ ·)
            (wbarFaceInner_ι W G n i hi0 hiLast p)
      _ = (φ.app p.1.left ≫ wFaceInnerComponent G i hi0 p.1) ≫
            wbarIncl W G n (wFaceInnerIdx W n i hiLast p) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (wFaceInnerComponent F i hi0 p.1 ≫
      φ.app (wFaceInnerIdx W n i hiLast p).1.left) =
      (φ.app p.1.left ≫ wFaceInnerComponent G i hi0 p.1) :=
    wSlideInner φ (h := (wOmitInner_obj_zero hi0 p.1).symm)
  calc wbarIncl W F (n + 1) p ≫
          (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapF (W := W) n φ)
      = (wFaceInnerComponent F i hi0 p.1 ≫
          φ.app (wFaceInnerIdx W n i hiLast p).1.left) ≫
          wbarIncl W G n (wFaceInnerIdx W n i hiLast p) := hL
    _ = (φ.app p.1.left ≫ wFaceInnerComponent G i hi0 p.1) ≫
          wbarIncl W G n (wFaceInnerIdx W n i hiLast p) := by
        exact congrArg (· ≫ wbarIncl W G n (wFaceInnerIdx W n i hiLast p))
          hcoeff
    _ = wbarIncl W F (n + 1) p ≫
          (wbarMapF (W := W) (n + 1) φ ≫
            wbarFaceInner W G n i hi0 hiLast) := hR.symm

/-- Interior `sᵢ` is natural in the diagram variable: acting by `φ` commutes
with duplicating the `i`-th chain entry. Both sides map degree `n` to
degree `n + 1`. -/
theorem wbarDegInner_mapF (W : Jᵒᵖ ⥤ Type uW) (F G : J ⥤ C) (n : ℕ)
    (i : Fin (n + 1)) [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj p.1.left)]
    (φ : F ⟶ G) :
    wbarDegInner W F n i ≫ wbarMapF (W := W) (n + 1) φ =
      wbarMapF (W := W) n φ ≫ wbarDegInner W G n i := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  change wbarIncl W F n p ≫
      (wbarDegInner W F n i ≫ wbarMapF (W := W) (n + 1) φ) =
    wbarIncl W F n p ≫
      (wbarMapF (W := W) n φ ≫ wbarDegInner W G n i)
  have hL : wbarIncl W F n p ≫
      (wbarDegInner W F n i ≫ wbarMapF (W := W) (n + 1) φ) =
      (wDegInnerComponent F i p.1 ≫
        φ.app (wDegInnerIdx W n i p).1.left) ≫
        wbarIncl W G (n + 1) (wDegInnerIdx W n i p) := by
    calc wbarIncl W F n p ≫
            (wbarDegInner W F n i ≫ wbarMapF (W := W) (n + 1) φ)
        = (wbarIncl W F n p ≫ wbarDegInner W F n i) ≫
            wbarMapF (W := W) (n + 1) φ := by
          exact (Category.assoc _ _ _).symm
      _ = (wDegInnerComponent F i p.1 ≫
            wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) ≫
            wbarMapF (W := W) (n + 1) φ := by
          exact congrArg (· ≫ wbarMapF (W := W) (n + 1) φ)
            (wbarDegInner_ι W F n i p)
      _ = wDegInnerComponent F i p.1 ≫
            (wbarIncl W F (n + 1) (wDegInnerIdx W n i p) ≫
              wbarMapF (W := W) (n + 1) φ) := by
          exact Category.assoc _ _ _
      _ = wDegInnerComponent F i p.1 ≫
            (φ.app (wDegInnerIdx W n i p).1.left ≫
              wbarIncl W G (n + 1) (wDegInnerIdx W n i p)) := by
          exact congrArg (wDegInnerComponent F i p.1 ≫ ·)
            (wbarMapF_ι (n + 1) φ (wDegInnerIdx W n i p))
      _ = (wDegInnerComponent F i p.1 ≫
            φ.app (wDegInnerIdx W n i p).1.left) ≫
            wbarIncl W G (n + 1) (wDegInnerIdx W n i p) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F n p ≫
      (wbarMapF (W := W) n φ ≫ wbarDegInner W G n i) =
      (φ.app p.1.left ≫ wDegInnerComponent G i p.1) ≫
        wbarIncl W G (n + 1) (wDegInnerIdx W n i p) := by
    calc wbarIncl W F n p ≫
            (wbarMapF (W := W) n φ ≫ wbarDegInner W G n i)
        = (wbarIncl W F n p ≫ wbarMapF (W := W) n φ) ≫
            wbarDegInner W G n i := by
          exact (Category.assoc _ _ _).symm
      _ = (φ.app p.1.left ≫ wbarIncl W G n p) ≫
            wbarDegInner W G n i := by
          exact congrArg (· ≫ wbarDegInner W G n i)
            (wbarMapF_ι n φ p)
      _ = φ.app p.1.left ≫
            (wbarIncl W G n p ≫ wbarDegInner W G n i) := by
          exact Category.assoc _ _ _
      _ = φ.app p.1.left ≫ (wDegInnerComponent G i p.1 ≫
            wbarIncl W G (n + 1) (wDegInnerIdx W n i p)) := by
          exact congrArg (φ.app p.1.left ≫ ·)
            (wbarDegInner_ι W G n i p)
      _ = (φ.app p.1.left ≫ wDegInnerComponent G i p.1) ≫
            wbarIncl W G (n + 1) (wDegInnerIdx W n i p) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (wDegInnerComponent F i p.1 ≫
      φ.app (wDegInnerIdx W n i p).1.left) =
      (φ.app p.1.left ≫ wDegInnerComponent G i p.1) :=
    wSlideInner φ (h := (wDupInner_obj_zero p.1).symm)
  calc wbarIncl W F n p ≫
          (wbarDegInner W F n i ≫ wbarMapF (W := W) (n + 1) φ)
      = (wDegInnerComponent F i p.1 ≫
          φ.app (wDegInnerIdx W n i p).1.left) ≫
          wbarIncl W G (n + 1) (wDegInnerIdx W n i p) := hL
    _ = (φ.app p.1.left ≫ wDegInnerComponent G i p.1) ≫
          wbarIncl W G (n + 1) (wDegInnerIdx W n i p) := by
        exact congrArg (· ≫ wbarIncl W G (n + 1) (wDegInnerIdx W n i p))
          hcoeff
    _ = wbarIncl W F n p ≫
          (wbarMapF (W := W) n φ ≫ wbarDegInner W G n i) := hR.symm

/-- Interior `dᵢ` is natural in the weight variable: reindexing by `ψ`
commutes with omitting the `i`-th chain entry, by naturality of `ψ` at the
endpoint transport. -/
theorem wbarFaceInner_mapW (W W' : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)]
    (ψ : W ⟶ W') :
    wbarFaceInner W F n i hi0 hiLast ≫ wbarMapW F n ψ =
      wbarMapW F (n + 1) ψ ≫ wbarFaceInner W' F n i hi0 hiLast := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W F (n + 1) p ≫
      (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapW F n ψ) =
    wbarIncl W F (n + 1) p ≫
      (wbarMapW F (n + 1) ψ ≫ wbarFaceInner W' F n i hi0 hiLast)
  have hL : wbarIncl W F (n + 1) p ≫
      (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapW F n ψ) =
      (wFaceInnerComponent F i hi0 p.1 ≫ 𝟙 _) ≫
        wbarIncl W' F n (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p)) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapW F n ψ)
        = (wbarIncl W F (n + 1) p ≫ wbarFaceInner W F n i hi0 hiLast) ≫
            wbarMapW F n ψ := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F i hi0 p.1 ≫
            wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) ≫
            wbarMapW F n ψ := by
          exact congrArg (· ≫ wbarMapW F n ψ)
            (wbarFaceInner_ι W F n i hi0 hiLast p)
      _ = wFaceInnerComponent F i hi0 p.1 ≫
            (wbarIncl W F n (wFaceInnerIdx W n i hiLast p) ≫
              wbarMapW F n ψ) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F i hi0 p.1 ≫
            (𝟙 _ ≫
              wbarIncl W' F n
                (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p))) := by
          exact congrArg (wFaceInnerComponent F i hi0 p.1 ≫ ·)
            (wbarMapW_ι F n ψ (wFaceInnerIdx W n i hiLast p))
      _ = (wFaceInnerComponent F i hi0 p.1 ≫ 𝟙 _) ≫
            wbarIncl W' F n
              (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p)) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) p ≫
      (wbarMapW F (n + 1) ψ ≫ wbarFaceInner W' F n i hi0 hiLast) =
      (𝟙 _ ≫
          wFaceInnerComponent F i hi0
            (wMapWIdx (n + 1) ψ p).1) ≫
        wbarIncl W' F n
          (wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p)) := by
    calc wbarIncl W F (n + 1) p ≫
            (wbarMapW F (n + 1) ψ ≫ wbarFaceInner W' F n i hi0 hiLast)
        = (wbarIncl W F (n + 1) p ≫ wbarMapW F (n + 1) ψ) ≫
            wbarFaceInner W' F n i hi0 hiLast := by
          exact (Category.assoc _ _ _).symm
      _ = (𝟙 _ ≫ wbarIncl W' F (n + 1) (wMapWIdx (n + 1) ψ p)) ≫
            wbarFaceInner W' F n i hi0 hiLast := by
          exact congrArg (· ≫ wbarFaceInner W' F n i hi0 hiLast)
            (wbarMapW_ι F (n + 1) ψ p)
      _ = 𝟙 _ ≫
            (wbarIncl W' F (n + 1) (wMapWIdx (n + 1) ψ p) ≫
              wbarFaceInner W' F n i hi0 hiLast) := by
          exact Category.assoc _ _ _
      _ = 𝟙 _ ≫ (wFaceInnerComponent F i hi0
              (wMapWIdx (n + 1) ψ p).1 ≫
            wbarIncl W' F n
              (wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p))) := by
          exact congrArg (𝟙 _ ≫ ·)
            (wbarFaceInner_ι W' F n i hi0 hiLast (wMapWIdx (n + 1) ψ p))
      _ = (𝟙 _ ≫
              wFaceInnerComponent F i hi0
                (wMapWIdx (n + 1) ψ p).1) ≫
            wbarIncl W' F n
              (wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p)) := by
          exact (Category.assoc _ _ _).symm
  have hidx : wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p) =
      wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p) :=
    (wFaceInnerIdx_mapW n i hiLast ψ p).symm
  have hcoeff : (wFaceInnerComponent F i hi0 p.1 ≫ 𝟙 _) =
      (𝟙 _ ≫
        wFaceInnerComponent F i hi0
          (wMapWIdx (n + 1) ψ p).1) := by
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  calc wbarIncl W F (n + 1) p ≫
          (wbarFaceInner W F n i hi0 hiLast ≫ wbarMapW F n ψ)
      = (wFaceInnerComponent F i hi0 p.1 ≫ 𝟙 _) ≫
          wbarIncl W' F n (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p)) := hL
    _ = (𝟙 _ ≫
            wFaceInnerComponent F i hi0
              (wMapWIdx (n + 1) ψ p).1) ≫
          wbarIncl W' F n
            (wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p)) := by
        have htrans := Limits.Sigma.eqToHom_comp_ι
          (fun q : WIdx J W' n => F.obj q.1.left) hidx.symm
        have hE : ∀ (_e : F.obj
              (wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p)).1.left =
              F.obj (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p)).1.left),
            eqToHom _e = 𝟙 _ := fun _ => rfl
        have hbridge : (𝟙 _ ≫
                wFaceInnerComponent F i hi0
                  (wMapWIdx (n + 1) ψ p).1) ≫
            wbarIncl W' F n (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p)) =
            (𝟙 _ ≫
                wFaceInnerComponent F i hi0
                  (wMapWIdx (n + 1) ψ p).1) ≫
            wbarIncl W' F n
              (wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p)) := by
          calc (𝟙 _ ≫
                  wFaceInnerComponent F i hi0
                    (wMapWIdx (n + 1) ψ p).1) ≫
                wbarIncl W' F n (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p))
              = (𝟙 _ ≫
                    wFaceInnerComponent F i hi0
                      (wMapWIdx (n + 1) ψ p).1) ≫
                  (eqToHom _ ≫ wbarIncl W' F n
                    (wFaceInnerIdx W' n i hiLast
                      (wMapWIdx (n + 1) ψ p))) := by
                exact congrArg ((𝟙 _ ≫
                    wFaceInnerComponent F i hi0
                      (wMapWIdx (n + 1) ψ p).1) ≫ ·)
                  htrans.symm
            _ = ((𝟙 _ ≫
                    wFaceInnerComponent F i hi0
                      (wMapWIdx (n + 1) ψ p).1) ≫ eqToHom _) ≫
                  wbarIncl W' F n
                    (wFaceInnerIdx W' n i hiLast
                      (wMapWIdx (n + 1) ψ p)) := by
                exact (Category.assoc _ _ _).symm
            _ = (𝟙 _ ≫
                    wFaceInnerComponent F i hi0
                      (wMapWIdx (n + 1) ψ p).1) ≫
                  wbarIncl W' F n
                    (wFaceInnerIdx W' n i hiLast
                      (wMapWIdx (n + 1) ψ p)) := by
                exact congrArg (· ≫ wbarIncl W' F n
                  (wFaceInnerIdx W' n i hiLast (wMapWIdx (n + 1) ψ p)))
                  ((congrArg ((𝟙 _ ≫
                      wFaceInnerComponent F i hi0
                        (wMapWIdx (n + 1) ψ p).1) ≫ ·)
                    (hE _)).trans
                    (Category.comp_id _))
        exact (congrArg (· ≫ wbarIncl W' F n
          (wMapWIdx n ψ (wFaceInnerIdx W n i hiLast p))) hcoeff).trans hbridge
    _ = wbarIncl W F (n + 1) p ≫
          (wbarMapW F (n + 1) ψ ≫ wbarFaceInner W' F n i hi0 hiLast) := hR.symm

/-- Interior `sᵢ` is natural in the weight variable: reindexing by `ψ`
commutes with duplicating the `i`-th chain entry, by naturality of `ψ` at the
endpoint transport. -/
theorem wbarDegInner_mapW (W W' : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C) (n : ℕ)
    (i : Fin (n + 1)) [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W' (n + 1) => F.obj p.1.left)]
    (ψ : W ⟶ W') :
    wbarDegInner W F n i ≫ wbarMapW F (n + 1) ψ =
      wbarMapW F n ψ ≫ wbarDegInner W' F n i := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  change wbarIncl W F n p ≫
      (wbarDegInner W F n i ≫ wbarMapW F (n + 1) ψ) =
    wbarIncl W F n p ≫
      (wbarMapW F n ψ ≫ wbarDegInner W' F n i)
  have hL : wbarIncl W F n p ≫
      (wbarDegInner W F n i ≫ wbarMapW F (n + 1) ψ) =
      (wDegInnerComponent F i p.1 ≫ 𝟙 _) ≫
        wbarIncl W' F (n + 1)
          (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p)) := by
    calc wbarIncl W F n p ≫
            (wbarDegInner W F n i ≫ wbarMapW F (n + 1) ψ)
        = (wbarIncl W F n p ≫ wbarDegInner W F n i) ≫
            wbarMapW F (n + 1) ψ := by
          exact (Category.assoc _ _ _).symm
      _ = (wDegInnerComponent F i p.1 ≫
            wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) ≫
            wbarMapW F (n + 1) ψ := by
          exact congrArg (· ≫ wbarMapW F (n + 1) ψ)
            (wbarDegInner_ι W F n i p)
      _ = wDegInnerComponent F i p.1 ≫
            (wbarIncl W F (n + 1) (wDegInnerIdx W n i p) ≫
              wbarMapW F (n + 1) ψ) := by
          exact Category.assoc _ _ _
      _ = wDegInnerComponent F i p.1 ≫
            (𝟙 _ ≫
              wbarIncl W' F (n + 1)
                (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p))) := by
          exact congrArg (wDegInnerComponent F i p.1 ≫ ·)
            (wbarMapW_ι F (n + 1) ψ (wDegInnerIdx W n i p))
      _ = (wDegInnerComponent F i p.1 ≫ 𝟙 _) ≫
            wbarIncl W' F (n + 1)
              (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p)) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F n p ≫
      (wbarMapW F n ψ ≫ wbarDegInner W' F n i) =
      (𝟙 _ ≫
          wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
        wbarIncl W' F (n + 1)
          (wDegInnerIdx W' n i (wMapWIdx n ψ p)) := by
    calc wbarIncl W F n p ≫
            (wbarMapW F n ψ ≫ wbarDegInner W' F n i)
        = (wbarIncl W F n p ≫ wbarMapW F n ψ) ≫
            wbarDegInner W' F n i := by
          exact (Category.assoc _ _ _).symm
      _ = (𝟙 _ ≫ wbarIncl W' F n (wMapWIdx n ψ p)) ≫
            wbarDegInner W' F n i := by
          exact congrArg (· ≫ wbarDegInner W' F n i)
            (wbarMapW_ι F n ψ p)
      _ = 𝟙 _ ≫
            (wbarIncl W' F n (wMapWIdx n ψ p) ≫
              wbarDegInner W' F n i) := by
          exact Category.assoc _ _ _
      _ = 𝟙 _ ≫ (wDegInnerComponent F i (wMapWIdx n ψ p).1 ≫
            wbarIncl W' F (n + 1)
              (wDegInnerIdx W' n i (wMapWIdx n ψ p))) := by
          exact congrArg (𝟙 _ ≫ ·)
            (wbarDegInner_ι W' F n i (wMapWIdx n ψ p))
      _ = (𝟙 _ ≫
              wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
            wbarIncl W' F (n + 1)
              (wDegInnerIdx W' n i (wMapWIdx n ψ p)) := by
          exact (Category.assoc _ _ _).symm
  have hidx : wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p) =
      wDegInnerIdx W' n i (wMapWIdx n ψ p) :=
    (wDegInnerIdx_mapW n i ψ p).symm
  have hcoeff : (wDegInnerComponent F i p.1 ≫ 𝟙 _) =
      (𝟙 _ ≫
        wDegInnerComponent F i (wMapWIdx n ψ p).1) := by
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  calc wbarIncl W F n p ≫
          (wbarDegInner W F n i ≫ wbarMapW F (n + 1) ψ)
      = (wDegInnerComponent F i p.1 ≫ 𝟙 _) ≫
          wbarIncl W' F (n + 1)
            (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p)) := hL
    _ = (𝟙 _ ≫
            wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
          wbarIncl W' F (n + 1)
            (wDegInnerIdx W' n i (wMapWIdx n ψ p)) := by
        have htrans := Limits.Sigma.eqToHom_comp_ι
          (fun q : WIdx J W' (n + 1) => F.obj q.1.left) hidx.symm
        have hE : ∀ (_e : F.obj
              (wDegInnerIdx W' n i (wMapWIdx n ψ p)).1.left =
              F.obj (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p)).1.left),
            eqToHom _e = 𝟙 _ := fun _ => rfl
        have hbridge : (𝟙 _ ≫
                wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
            wbarIncl W' F (n + 1)
              (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p)) =
            (𝟙 _ ≫
                wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
            wbarIncl W' F (n + 1)
              (wDegInnerIdx W' n i (wMapWIdx n ψ p)) := by
          calc (𝟙 _ ≫
                  wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
                wbarIncl W' F (n + 1)
                  (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p))
              = (𝟙 _ ≫
                    wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
                  (eqToHom _ ≫ wbarIncl W' F (n + 1)
                    (wDegInnerIdx W' n i (wMapWIdx n ψ p))) := by
                exact congrArg ((𝟙 _ ≫
                    wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫ ·)
                  htrans.symm
            _ = ((𝟙 _ ≫
                    wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫ eqToHom _) ≫
                  wbarIncl W' F (n + 1)
                    (wDegInnerIdx W' n i (wMapWIdx n ψ p)) := by
                exact (Category.assoc _ _ _).symm
            _ = (𝟙 _ ≫
                    wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫
                  wbarIncl W' F (n + 1)
                    (wDegInnerIdx W' n i (wMapWIdx n ψ p)) := by
                exact congrArg (· ≫ wbarIncl W' F (n + 1)
                  (wDegInnerIdx W' n i (wMapWIdx n ψ p)))
                  ((congrArg ((𝟙 _ ≫
                      wDegInnerComponent F i (wMapWIdx n ψ p).1) ≫ ·)
                    (hE _)).trans
                    (Category.comp_id _))
        exact (congrArg (· ≫ wbarIncl W' F (n + 1)
          (wMapWIdx (n + 1) ψ (wDegInnerIdx W n i p))) hcoeff).trans hbridge
    _ = wbarIncl W F n p ≫
          (wbarMapW F n ψ ≫ wbarDegInner W' F n i) := hR.symm

end StrictOrdinaryWeightedBar
end CategoryTheory
