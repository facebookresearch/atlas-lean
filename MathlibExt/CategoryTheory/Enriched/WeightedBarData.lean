/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.WeightedBarInner
public import MathlibExt.CategoryTheory.ComposableArrows.StrictOmitDupChain

/-!
# Strict ordinary weighted bar as simplicial data

This module assembles the strict ordinary weighted bar from `WeightedBar`,
`WeightedBarOuter`, and `WeightedBarInner` into `SimplicialObject.Data`.

For a small indexing category `J`, a contravariant ordinary weight
`W : Jᵒᵖ ⥤ Type`, and a covariant diagram `F : J ⥤ C`, degree `n` is
`wbarObj`. The total face `wbarδ` dispatches on the simplex index:
index `0` is the outer `wbarFaceZero`, the last index is the
outer `wbarFaceLast`, and every interior index is
`wbarFaceInner`. The total degeneracy `wbarσ` is uniformly the
interior degeneracy; the comparison `wbarσ_zero` identifies its zeroth instance
with the outer `wbarDegZero` so the outer packet laws stay reusable.

The six simplicial relations are proved from the chain identities in
`StrictOmitDupChain` (`omitOmit_chain_obj` for faces, `dupDup_chain_obj` for
degeneracies, and the four `omitDup` chain facts for the mixed relations),
together with the three outer laws from `WeightedBarOuter`. Chain
normalization, weight fusion, `weight transport`, and the endpoint/interior
case analyses are all private; only the total operators, their
dispatch/comparison lemmas, the six relations, the bundled `wbarData`, and its
object/face/degeneracy computations are public.

Orientation: faces drop a chain entry (outer faces at the ends, interior
omission otherwise) while degeneracies duplicate one. Coefficients are pure
endpoint transports except at `d₀`, which alone acts by a diagram arrow.

Hypotheses: every degree is assumed to have the needed coproduct, once, as a
global instance; the canonical `NeZero (n + 1)` instances are hidden
internally so the public operators are total.

Nonclaims: no `GenRel`/genuine promotion (in `WeightedBarSimplicial`),
no simplicial replacement comparison, no enriched/profunctor bridge, and no realization,
homotopy-colimit, or model-category conclusion. Separate naturality and its mixed square are in
`WeightedBarMapF` / `WeightedBarMapW` / `WeightedBarMapFW`; their categorical packaging is in
`WeightedBarFunctor`.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOrdinaryWeightedBar

universe vJ uJ vC uC uW

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
variable [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]

/-- Internal: hidden canonical positivity instance so total operators need no
explicit `NeZero` argument. Public declarations stay total. -/
private instance wHiddenNeZero (n : ℕ) : NeZero (n + 1) := ⟨by omega⟩

/-- Internal: the last index of `Fin (n + 2)` differs from `0`. Used only to
discharge the outer dispatch negation. -/
private theorem wLastNeZero (n : ℕ) : Fin.last (n + 1) ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval

/-- Total face operator of the strict ordinary weighted bar. At index `0` it
is the outer `d₀`, at the last index it is the outer `d_last`, and otherwise
it is the interior face. The motive is constant, so no index transport is
needed across the dispatch. -/
noncomputable def wbarδ (n : ℕ) (i : Fin (n + 2)) :
    wbarObj W F (n + 1) ⟶ wbarObj W F n :=
  if h0 : i = 0 then wbarFaceZero W F n
  else if hlast : i = Fin.last (n + 1) then wbarFaceLast W F n
  else wbarFaceInner W F n i h0 hlast

/-- Dispatch at index `0`: the total face is the accepted outer `d₀`. -/
theorem wbarδ_zero (n : ℕ) : wbarδ W F n 0 = wbarFaceZero W F n := by
  unfold wbarδ
  exact dite_eq_left rfl

/-- Dispatch at the last index: the total face is the accepted outer
`d_last`. -/
theorem wbarδ_last (n : ℕ) :
    wbarδ W F n (Fin.last (n + 1)) = wbarFaceLast W F n := by
  unfold wbarδ
  rw [dite_eq_right (wLastNeZero n), dite_eq_left rfl]

/-- Dispatch at an interior index: the total face is the accepted interior
face. -/
theorem wbarδ_inner (n : ℕ) (i : Fin (n + 2))
    (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1)) :
    wbarδ W F n i = wbarFaceInner W F n i hi0 hiLast := by
  unfold wbarδ
  rw [dite_eq_right hi0, dite_eq_right hiLast]

/-- Total degeneracy operator of the strict ordinary weighted bar, uniformly
the accepted interior degeneracy. Uniformity keeps the `σσ` relation a single
interior-interior chain computation; the zeroth comparison below reconnects
it with the outer `s₀` for the mixed relations. -/
noncomputable def wbarσ (n : ℕ) (i : Fin (n + 1)) :
    wbarObj W F n ⟶ wbarObj W F (n + 1) :=
  wbarDegInner W F n i

/-- Coproduct-inclusion formula for the total degeneracy, from the accepted
interior rule. -/
theorem wbarσ_ι (n : ℕ) (i : Fin (n + 1)) (p : WIdx J W n) :
    wbarIncl W F n p ≫ wbarσ W F n i =
      wDegInnerComponent F i p.1 ≫
        wbarIncl W F (n + 1) (wDegInnerIdx W n i p) :=
  wbarDegInner_ι W F n i p

/-- Internal: fuse two nested weight transports into one, by functoriality and
`eqToHom_trans`. Both equalities run from the iterated chain toward the base
chain; the outer one is applied second. -/
private theorem wWeightFuse (W : Jᵒᵖ ⥤ Type uW) {a b c : J}
    (e1 : a = b) (e2 : b = c) (w : W.obj (Opposite.op c)) :
    W.map (eqToHom e1).op (W.map (eqToHom e2).op w) =
      W.map (eqToHom (e1.trans e2)).op w := by
  have hcomp : W.map (eqToHom e2).op ≫ W.map (eqToHom e1).op =
      W.map ((eqToHom e2).op ≫ (eqToHom e1).op) := by
    rw [Functor.map_comp]
  have hop : (eqToHom e2).op ≫ (eqToHom e1).op =
      (eqToHom e1 ≫ eqToHom e2).op := by
    rw [op_comp]
  have htrans : eqToHom e1 ≫ eqToHom e2 = eqToHom (e1.trans e2) := by
    rw [eqToHom_trans]
  calc W.map (eqToHom e1).op (W.map (eqToHom e2).op w)
      = (W.map (eqToHom e2).op ≫ W.map (eqToHom e1).op) w := rfl
    _ = W.map ((eqToHom e2).op ≫ (eqToHom e1).op) w := by
        exact (Functor.map_comp W _ _).symm ▸ rfl
    _ = W.map (eqToHom (e1.trans e2)).op w := by
        rw [hop, htrans]

/-- Internal: a `WIdx` equality from a chain equality plus weight transports
over a common base weight. The chains are variables, so casing on the chain
equality leaves definitionally irrelevant endpoint proofs. -/
private theorem wIdxOfChainEq (W : Jᵒᵖ ⥤ Type uW) {m : ℕ}
    {s1 s2 : SrepBridge.SrepIdx J m} (h : s1 = s2) {a : J}
    (e1 : s1.right = a) (e2 : s2.right = a)
    (w : W.obj (Opposite.op a)) :
    (⟨s1, W.map (eqToHom e1).op w⟩ : WIdx J W m) =
      ⟨s2, W.map (eqToHom e2).op w⟩ := by
  refine Sigma.ext h ?_
  cases h
  rfl

/-- Internal: collapse two nested weight actions into one, by functoriality. -/
private theorem wWeightComp (W : Jᵒᵖ ⥤ Type uW) {a b c : J} (f : a ⟶ b)
    (g : b ⟶ c) (w : W.obj (Opposite.op c)) :
    W.map f.op (W.map g.op w) = W.map (f ≫ g).op w := by
  calc
    _ = (W.map g.op ≫ W.map f.op) w := rfl
    _ = W.map (g.op ≫ f.op) w := by
      exact (Functor.map_comp W _ _).symm ▸ rfl
    _ = _ := by rw [op_comp]

/-- Internal: a `WIdx` equality from a chain equality plus arrow-level weight
actions over a common base weight. The arrow equality is transported along the
chain equality. -/
private theorem wIdxOfChainEqMap (W : Jᵒᵖ ⥤ Type uW) {m : ℕ}
    {s₁ s₂ : SrepBridge.SrepIdx J m} (h : s₁ = s₂) {a : J}
    (f₁ : s₁.right ⟶ a) (f₂ : s₂.right ⟶ a)
    (hf : f₁ =
      eqToHom (congrArg (fun s : SrepBridge.SrepIdx J m => s.right) h) ≫ f₂)
    (w : W.obj (Opposite.op a)) :
    (⟨s₁, W.map f₁.op w⟩ : WIdx J W m) =
      ⟨s₂, W.map f₂.op w⟩ := by
  cases h
  simp only [eqToHom_refl, Category.id_comp] at hf
  cases hf
  rfl

/-- Internal: iterated duplications commute at the chain level, from the
accepted `dupDup_chain_obj`. The second composite is read in the same
single-whiskering normal form by definitional reassociation. -/
private theorem wChainDupDup {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j)
    (s : SrepBridge.SrepIdx J n) :
    (StrictOmitDup.dupAt i.castSucc).obj ((StrictOmitDup.dupAt j).obj s) =
      (StrictOmitDup.dupAt j.succ).obj ((StrictOmitDup.dupAt i).obj s) := by
  have e1 := StrictOmitDup.dupDup_chain_obj (C := J) h s
  have e2 : (StrictOmitDup.dupAt (C := J) i ⋙
      StrictOmitDup.dupAt (C := J) j.succ).obj s =
      (ComposableArrows.whiskerLeftFunctor
        (StrictOmitDup.dupFinFunctor (n + 1) j.succ ⋙
          StrictOmitDup.dupFinFunctor n i)).obj s := rfl
  exact e1.trans e2.symm

/-- Internal: iterated omissions commute at the chain level, from the accepted
`omitOmit_chain_obj`, in the same normal form. -/
private theorem wChainOmitOmit {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j)
    (s : SrepBridge.SrepIdx J (n + 2)) :
    (StrictOmitDup.omitAt (C := J) i).obj
        ((StrictOmitDup.omitAt (C := J) j.succ).obj s) =
      (StrictOmitDup.omitAt (C := J) j).obj
        ((StrictOmitDup.omitAt (C := J) i.castSucc).obj s) := by
  have e1 := StrictOmitDup.omitOmit_chain_obj (C := J) h s
  have e2 : (StrictOmitDup.omitAt (C := J) (n := n + 1) i.castSucc ⋙
      StrictOmitDup.omitAt (C := J) (n := n) j).obj s =
      (ComposableArrows.whiskerLeftFunctor
        (StrictOmitDup.omitFinFunctor n j ⋙
          StrictOmitDup.omitFinFunctor (n + 1) i.castSucc)).obj s := rfl
  exact e1.trans e2.symm

/-- Internal: below-case duplication/omission commutation at the chain level,
from `omitDupBelow_chain_obj`. -/
private theorem wChainBelow {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) (s : SrepBridge.SrepIdx J (n + 1)) :
    (StrictOmitDup.omitAt (C := J) i.castSucc).obj
        ((StrictOmitDup.dupAt (C := J) j.succ).obj s) =
      (StrictOmitDup.dupAt (C := J) j).obj
        ((StrictOmitDup.omitAt (C := J) i).obj s) := by
  have e1 := StrictOmitDup.omitDupBelow_chain_obj (C := J) h s
  have e3 : (StrictOmitDup.omitAt (C := J) (n := n) i ⋙
      StrictOmitDup.dupAt (C := J) (n := n) j).obj s =
      (ComposableArrows.whiskerLeftFunctor
        (StrictOmitDup.dupFinFunctor n j ⋙
          StrictOmitDup.omitFinFunctor n i)).obj s := rfl
  exact e1.trans e3.symm

/-- Internal: self-case duplication/omission is the identity at the chain
level, from `omitDupSelf_chain_obj`. -/
private theorem wChainSelf {n : ℕ} {i : Fin (n + 1)}
    (s : SrepBridge.SrepIdx J n) :
    (StrictOmitDup.omitAt (C := J) i.castSucc).obj
        ((StrictOmitDup.dupAt (C := J) i).obj s) = s := by
  have e1 := StrictOmitDup.omitDupSelf_chain_obj (C := J) (n := n) (i := i) s
  have e2 : (ComposableArrows.whiskerLeftFunctor
      (Functor.id (Fin (n + 1)))).obj s = s := rfl
  exact e1.trans e2

/-- Internal: successor-case duplication/omission is the identity at the chain
level, from `omitDupSucc_chain_obj`. -/
private theorem wChainSucc {n : ℕ} {i : Fin (n + 1)}
    (s : SrepBridge.SrepIdx J n) :
    (StrictOmitDup.omitAt (C := J) i.succ).obj
        ((StrictOmitDup.dupAt (C := J) i).obj s) = s := by
  have e1 := StrictOmitDup.omitDupSucc_chain_obj (C := J) (n := n) (i := i) s
  have e2 : (ComposableArrows.whiskerLeftFunctor
      (Functor.id (Fin (n + 1)))).obj s = s := rfl
  exact e1.trans e2

/-- Internal: above-case duplication/omission commutation at the chain level,
from `omitDupAbove_chain_obj`. -/
private theorem wChainAbove {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) (s : SrepBridge.SrepIdx J (n + 1)) :
    (StrictOmitDup.omitAt (C := J) i.succ).obj
        ((StrictOmitDup.dupAt (C := J) j.castSucc).obj s) =
      (StrictOmitDup.dupAt (C := J) j).obj
        ((StrictOmitDup.omitAt (C := J) i).obj s) := by
  have e1 := StrictOmitDup.omitDupAbove_chain_obj (C := J) h s
  have e3 : (StrictOmitDup.omitAt (C := J) (n := n) i ⋙
      StrictOmitDup.dupAt (C := J) (n := n) j).obj s =
      (ComposableArrows.whiskerLeftFunctor
        (StrictOmitDup.dupFinFunctor n j ⋙
          StrictOmitDup.omitFinFunctor n i)).obj s := rfl
  exact e1.trans e3.symm

/-- Internal: dropping the first entry is omission at `0`, via the accepted
`omitFin_zero_succ` index equality transported through pre-whiskering. -/
private theorem wOmitZeroChain {n : ℕ} (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepDropFirst s = (StrictOmitDup.omitAt (0 : Fin (n + 2))).obj s := by
  have hFin : Fin.succFunctor (n + 1) = StrictOmitDup.omitFinFunctor n 0 := by
    refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
    change k.succ = (StrictOmitDup.omitFinFunctor n 0).obj k
    exact (StrictOmitDup.omitFin_zero_succ n k).symm
  have h := StrictOmitDup.whiskerLeft_obj_eq_of_idx_obj_eq (C := J) hFin s
  change (ComposableArrows.whiskerLeftFunctor (Fin.succFunctor (n + 1))).obj s =
    (ComposableArrows.whiskerLeftFunctor (StrictOmitDup.omitFinFunctor n 0)).obj s
  exact h

/-- Internal: dropping the last entry is omission at `last`, via the accepted
`omitFin_last_castSucc` index equality transported through pre-whiskering. -/
private theorem wOmitLastChain {n : ℕ} (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepDropLast s =
      (StrictOmitDup.omitAt (Fin.last (n + 1))).obj s := by
  have hFin : Fin.castSuccFunctor (n + 1) =
      StrictOmitDup.omitFinFunctor n (Fin.last (n + 1)) := by
    refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
    change k.castSucc = (StrictOmitDup.omitFinFunctor n (Fin.last (n + 1))).obj k
    exact (StrictOmitDup.omitFin_last_castSucc n k).symm
  have h := StrictOmitDup.whiskerLeft_obj_eq_of_idx_obj_eq (C := J) hFin s
  change (ComposableArrows.whiskerLeftFunctor (Fin.castSuccFunctor (n + 1))).obj s =
    (ComposableArrows.whiskerLeftFunctor
      (StrictOmitDup.omitFinFunctor n (Fin.last (n + 1)))).obj s
  exact h

/-- Internal: duplicating at `0` repeats the first entry, following the green
`dropLast_dupFirst_eq` shape with `dupFin_zero_obj`, `dupFin_zero_succ`,
`Precomp.map_zero_one`/`map_succ_succ`, `whiskerLeft_map'`, and `map'_self`. -/
private theorem wDupZeroChain {n : ℕ} (s : SrepBridge.SrepIdx J n) :
    (StrictOmitDup.dupAt (0 : Fin (n + 1))).obj s =
      SrepBridge.srepDupFirst s := by
  refine ComposableArrows.ext (fun (k : Fin (n + 2)) => ?_) (fun (i : Nat) (hi : i < n + 1) => ?_)
  · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · rw [StrictOmitDup.dupAt_obj_obj, StrictOmitDup.dupFin_zero_obj]
      rfl
    · rw [StrictOmitDup.dupAt_obj_obj, StrictOmitDup.dupFin_zero_succ]
      rfl
  · by_cases hi0 : i = 0
    · subst hi0
      have e0 : (StrictOmitDup.dupFinFunctor n (0 : Fin (n + 1))).obj
          (⟨0, by omega⟩ : Fin (n + 2)) = (⟨0, by omega⟩ : Fin (n + 1)) := by
        simp
      have e1 : (StrictOmitDup.dupFinFunctor n (0 : Fin (n + 1))).obj
          (⟨0 + 1, by omega⟩ : Fin (n + 2)) = (⟨0, by omega⟩ : Fin (n + 1)) := by
        have : (⟨0 + 1, by omega⟩ : Fin (n + 2)) =
            (⟨0, by omega⟩ : Fin (n + 1)).succ := by
          apply Fin.ext
          simp
        rw [this]
        exact StrictOmitDup.dupFin_zero_succ n _
      have hW : ((StrictOmitDup.dupAt (0 : Fin (n + 1))).obj s).map' 0
          (0 + 1) (by omega) (by omega) =
          eqToHom _ ≫ s.map' 0 0 (by omega) (by omega) ≫ eqToHom _ :=
        StrictOmitDup.whiskerLeft_map' (C := J) s e0 e1 (hab := by omega) (hab' := by omega)
      have hSelf : s.map' 0 0 (by omega) (by omega) = 𝟙 _ :=
        ComposableArrows.map'_self s 0
      rw [hW, hSelf]
      have hR : (SrepBridge.srepDupFirst s).map' 0 (0 + 1) (by omega) hi =
        𝟙 ((SrepBridge.srepDupFirst s).obj ⟨0, by omega⟩) := rfl
      rw [hR]
      rfl
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have e0 : (StrictOmitDup.dupFinFunctor n (0 : Fin (n + 1))).obj
          (⟨k + 1, by omega⟩ : Fin (n + 2)) =
          (⟨k, by omega⟩ : Fin (n + 1)) := by
        have h : (⟨k + 1, by omega⟩ : Fin (n + 2)) =
            (⟨k, by omega⟩ : Fin (n + 1)).succ := by
          apply Fin.ext
          simp
        rw [h]
        exact StrictOmitDup.dupFin_zero_succ n _
      have e1 : (StrictOmitDup.dupFinFunctor n (0 : Fin (n + 1))).obj
          (⟨k + 1 + 1, by omega⟩ : Fin (n + 2)) =
          (⟨k + 1, by omega⟩ : Fin (n + 1)) := by
        have h : (⟨k + 1 + 1, by omega⟩ : Fin (n + 2)) =
            (⟨k + 1, by omega⟩ : Fin (n + 1)).succ := by
          apply Fin.ext
          simp
        rw [h]
        exact StrictOmitDup.dupFin_zero_succ n _
      have hW : ((StrictOmitDup.dupAt (0 : Fin (n + 1))).obj s).map' (k + 1)
          (k + 1 + 1) (by omega) (by omega) =
          eqToHom _ ≫ s.map' k (k + 1) (by omega) (by omega) ≫ eqToHom _ :=
        StrictOmitDup.whiskerLeft_map' (C := J) s e0 e1 (hab := by omega) (hab' := by omega)
      have hSucc : s.map' k (k + 1) (by omega) (by omega) =
          (SrepBridge.srepDupFirst s).map' (k + 1) (k + 1 + 1) (by omega)
            (by omega) := by
        simp [SrepBridge.srepDupFirst, ComposableArrows.Precomp.map_succ_succ]
      rw [hW, hSucc]
      rfl

/-- Comparison of the uniform degeneracy at index `0` with the accepted outer
`s₀`. Rewriting through this identification lets the mixed `δσ` arguments
reuse the three accepted outer laws. The chain part identifies endpoint
duplication with first-entry repetition; weight and coefficient transports
fuse by the private helpers. -/
theorem wbarσ_zero (n : ℕ) :
    wbarσ W F n 0 = wbarDegZero W F n := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  obtain ⟨s, w⟩ := p
  have hchain : (StrictOmitDup.dupAt (0 : Fin (n + 1))).obj s =
      SrepBridge.srepDupFirst s :=
    wDupZeroChain s
  have eInner : ((StrictOmitDup.dupAt (0 : Fin (n + 1))).obj s).right =
      s.right := wDupInner_obj_last s
  have hIdx : wDegInnerIdx W n 0 ⟨s, w⟩ = wDegZeroIdx W n ⟨s, w⟩ := by
    change (⟨(StrictOmitDup.dupAt (0 : Fin (n + 1))).obj s,
        W.map (eqToHom eInner).op w⟩ : WIdx J W (n + 1)) =
      ⟨SrepBridge.srepDupFirst s, w⟩
    have hRHS : W.map
        (eqToHom (rfl : (SrepBridge.srepDupFirst s).right = s.right)).op w =
        w := by
      have hEq : (eqToHom
          (rfl : (SrepBridge.srepDupFirst s).right = s.right)).op = 𝟙 _ := rfl
      rw [hEq, W.map_id]
      rfl
    have hBase := wIdxOfChainEq W hchain eInner
      (rfl : (SrepBridge.srepDupFirst s).right = s.right) w
    have hEqPair : (⟨SrepBridge.srepDupFirst s,
        W.map (eqToHom (rfl : (SrepBridge.srepDupFirst s).right = s.right)).op w⟩ :
        WIdx J W (n + 1)) = ⟨SrepBridge.srepDupFirst s, w⟩ :=
      congrArg (fun ww => (⟨SrepBridge.srepDupFirst s, ww⟩ : WIdx J W (n + 1))) hRHS
    exact hBase.trans hEqPair
  change wbarIncl W F n ⟨s, w⟩ ≫ wbarσ W F n 0 =
    wbarIncl W F n ⟨s, w⟩ ≫ wbarDegZero W F n
  rw [wbarσ_ι, wbarDegZero_ι]
  have hcoeff : wDegInnerComponent F (0 : Fin (n + 1)) s =
      SrepBridge.srepDegZeroComponent F s := by
    unfold wDegInnerComponent SrepBridge.srepDegZeroComponent
    rfl
  calc (wDegInnerComponent F (0 : Fin (n + 1)) s ≫
        wbarIncl W F (n + 1) (wDegInnerIdx W n 0 ⟨s, w⟩))
      = (SrepBridge.srepDegZeroComponent F s ≫
        wbarIncl W F (n + 1) (wDegInnerIdx W n 0 ⟨s, w⟩)) := by
          exact congrArg (· ≫ _) hcoeff
    _ = (SrepBridge.srepDegZeroComponent F s ≫
        wbarIncl W F (n + 1) (wDegZeroIdx W n ⟨s, w⟩)) := by
          have hPack := congrArg
            (fun p : WIdx J W (n + 1) =>
              (⟨F.obj p.1.left, wbarIncl W F (n + 1) p⟩ :
                Sigma (fun X : C => (X ⟶ wbarObj W F (n + 1))))) hIdx
          have hHEq : wbarIncl W F (n + 1) (wDegInnerIdx W n 0 ⟨s, w⟩) ≍
              wbarIncl W F (n + 1) (wDegZeroIdx W n ⟨s, w⟩) :=
            (Sigma.mk.inj_iff.mp hPack).2
          have hIncl : wbarIncl W F (n + 1) (wDegInnerIdx W n 0 ⟨s, w⟩) =
              wbarIncl W F (n + 1) (wDegZeroIdx W n ⟨s, w⟩) :=
            eq_of_heq hHEq
          exact congrArg (SrepBridge.srepDegZeroComponent F s ≫ ·) hIncl
    _ = (SrepBridge.srepDegZeroComponent F s ≫
        wbarIncl W F (n + 1) (wDegZeroIdx W n ⟨s, w⟩)) := rfl

/-- Internal: `WIdx` equality for iterated interior duplications. The chain
part is `wChainDupDup`; the weight part fuses the two transports on each
side and lifts the chain equality. -/
private theorem wIdxDupDup (n : ℕ) {i j : Fin (n + 1)} (h : i ≤ j)
    (s : SrepBridge.SrepIdx J n) (w : W.obj (Opposite.op s.right)) :
    wDegInnerIdx W (n + 1) i.castSucc (wDegInnerIdx W n j ⟨s, w⟩) =
      wDegInnerIdx W (n + 1) j.succ (wDegInnerIdx W n i ⟨s, w⟩) := by
  have hchain := wChainDupDup (n := n) h s
  have eJ : ((StrictOmitDup.dupAt j).obj s).right = s.right :=
    wDupInner_obj_last s
  have eI : ((StrictOmitDup.dupAt i).obj s).right = s.right :=
    wDupInner_obj_last s
  have eJI : ((StrictOmitDup.dupAt i.castSucc).obj
      ((StrictOmitDup.dupAt j).obj s)).right =
      ((StrictOmitDup.dupAt j).obj s).right :=
    wDupInner_obj_last _
  have eIJ : ((StrictOmitDup.dupAt j.succ).obj
      ((StrictOmitDup.dupAt i).obj s)).right =
      ((StrictOmitDup.dupAt i).obj s).right :=
    wDupInner_obj_last _
  have fuseL := wWeightFuse W eJI eJ w
  have fuseR := wWeightFuse W eIJ eI w
  have hL : wDegInnerIdx W (n + 1) i.castSucc
      (wDegInnerIdx W n j ⟨s, w⟩) =
      (⟨(StrictOmitDup.dupAt i.castSucc).obj ((StrictOmitDup.dupAt j).obj s),
        W.map (eqToHom (eJI.trans eJ)).op w⟩ : WIdx J W (n + 2)) := by
    change wDegInnerIdx W (n + 1) i.castSucc
        ⟨(StrictOmitDup.dupAt j).obj s, W.map (eqToHom eJ).op w⟩ = _
    have hpair : wDegInnerIdx W (n + 1) i.castSucc
        ⟨(StrictOmitDup.dupAt j).obj s, W.map (eqToHom eJ).op w⟩ =
        ⟨(StrictOmitDup.dupAt i.castSucc).obj ((StrictOmitDup.dupAt j).obj s),
          W.map (eqToHom eJI).op (W.map (eqToHom eJ).op w)⟩ := rfl
    rw [hpair, fuseL]
  have hR : wDegInnerIdx W (n + 1) j.succ
      (wDegInnerIdx W n i ⟨s, w⟩) =
      (⟨(StrictOmitDup.dupAt j.succ).obj ((StrictOmitDup.dupAt i).obj s),
        W.map (eqToHom (eIJ.trans eI)).op w⟩ : WIdx J W (n + 2)) := by
    change wDegInnerIdx W (n + 1) j.succ
        ⟨(StrictOmitDup.dupAt i).obj s, W.map (eqToHom eI).op w⟩ = _
    have hpair : wDegInnerIdx W (n + 1) j.succ
        ⟨(StrictOmitDup.dupAt i).obj s, W.map (eqToHom eI).op w⟩ =
        ⟨(StrictOmitDup.dupAt j.succ).obj ((StrictOmitDup.dupAt i).obj s),
          W.map (eqToHom eIJ).op (W.map (eqToHom eI).op w)⟩ := rfl
    rw [hpair, fuseR]
  rw [hL, hR]
  exact wIdxOfChainEq W hchain (eJI.trans eJ) (eIJ.trans eI) w

/-- Internal: transport a coproduct inclusion along a `WIdx` equality.
Packing domain and morphism as a `Sigma` pair keeps the motive
well-typed; the second projection is the needed heterogeneous equality. -/
private theorem wbarInclHEqOfIdxEq {m : ℕ} {p₁ p₂ : WIdx J W m}
    (h : p₁ = p₂) :
    wbarIncl W F m p₁ ≍ wbarIncl W F m p₂ := by
  have hPack := congrArg
    (fun p : WIdx J W m =>
      (⟨F.obj p.1.left, wbarIncl W F m p⟩ :
        Sigma (fun X : C => (X ⟶ wbarObj W F m)))) h
  exact (Sigma.mk.inj_iff.mp hPack).2

/-- Internal: combine a `WIdx` equality with a heterogeneous coefficient
equality into a fixed-source composite equality. Eliminating the index
equality makes the heterogeneous equality homogeneous, so no standalone `Eq`
between morphisms with propositionally equal codomains is needed. -/
private theorem wbarCompEqOfIdxEqHEq {m : ℕ} {p q : WIdx J W m} (h : p = q)
    {X : C} {f : X ⟶ F.obj p.1.left} {g : X ⟶ F.obj q.1.left} (hf : f ≍ g) :
    f ≫ wbarIncl W F m p = g ≫ wbarIncl W F m q := by
  subst h
  have hfg : f = g := eq_of_heq hf
  rw [hfg]

/-- `σσ` for the total degeneracy: iterated duplications commute. Uniformity
reduces this to the interior-interior chain identity; coefficients are pure
transports, so the `Sigma` bridge fuses with them by proof irrelevance. -/
theorem wbar_σ_comp_σ (n : ℕ) {i j : Fin (n + 1)} (h : i ≤ j) :
    wbarσ W F n j ≫ wbarσ W F (n + 1) i.castSucc =
      wbarσ W F n i ≫ wbarσ W F (n + 1) j.succ := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  obtain ⟨s, w⟩ := p
  have hIdx := wIdxDupDup W n h s w
  change wbarIncl W F n ⟨s, w⟩ ≫
      (wbarσ W F n j ≫ wbarσ W F (n + 1) i.castSucc) =
    wbarIncl W F n ⟨s, w⟩ ≫
      (wbarσ W F n i ≫ wbarσ W F (n + 1) j.succ)
  have hL : wbarIncl W F n ⟨s, w⟩ ≫
      (wbarσ W F n j ≫ wbarσ W F (n + 1) i.castSucc) =
      (wDegInnerComponent F j s ≫
        wDegInnerComponent F i.castSucc ((StrictOmitDup.dupAt j).obj s)) ≫
        wbarIncl W F (n + 2)
          (wDegInnerIdx W (n + 1) i.castSucc
            (wDegInnerIdx W n j ⟨s, w⟩)) := by
    calc wbarIncl W F n ⟨s, w⟩ ≫
            (wbarσ W F n j ≫ wbarσ W F (n + 1) i.castSucc)
        = (wbarIncl W F n ⟨s, w⟩ ≫ wbarσ W F n j) ≫
            wbarσ W F (n + 1) i.castSucc := by
          exact (Category.assoc _ _ _).symm
      _ = (wDegInnerComponent F j s ≫
            wbarIncl W F (n + 1) (wDegInnerIdx W n j ⟨s, w⟩)) ≫
            wbarσ W F (n + 1) i.castSucc := by
          exact congrArg (· ≫ wbarσ W F (n + 1) i.castSucc)
            (wbarσ_ι W F n j ⟨s, w⟩)
      _ = wDegInnerComponent F j s ≫
            (wbarIncl W F (n + 1) (wDegInnerIdx W n j ⟨s, w⟩) ≫
              wbarσ W F (n + 1) i.castSucc) := by
          exact Category.assoc _ _ _
      _ = wDegInnerComponent F j s ≫
            (wDegInnerComponent F i.castSucc
              (wDegInnerIdx W n j ⟨s, w⟩).1 ≫
              wbarIncl W F (n + 2)
                (wDegInnerIdx W (n + 1) i.castSucc
                  (wDegInnerIdx W n j ⟨s, w⟩))) := by
          exact congrArg (wDegInnerComponent F j s ≫ ·)
            (wbarσ_ι W F (n + 1) i.castSucc (wDegInnerIdx W n j ⟨s, w⟩))
      _ = (wDegInnerComponent F j s ≫
            wDegInnerComponent F i.castSucc
              ((StrictOmitDup.dupAt j).obj s)) ≫
            wbarIncl W F (n + 2)
              (wDegInnerIdx W (n + 1) i.castSucc
                (wDegInnerIdx W n j ⟨s, w⟩)) := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F n ⟨s, w⟩ ≫
      (wbarσ W F n i ≫ wbarσ W F (n + 1) j.succ) =
      (wDegInnerComponent F i s ≫
        wDegInnerComponent F j.succ ((StrictOmitDup.dupAt i).obj s)) ≫
        wbarIncl W F (n + 2)
          (wDegInnerIdx W (n + 1) j.succ
            (wDegInnerIdx W n i ⟨s, w⟩)) := by
    calc wbarIncl W F n ⟨s, w⟩ ≫
            (wbarσ W F n i ≫ wbarσ W F (n + 1) j.succ)
        = (wbarIncl W F n ⟨s, w⟩ ≫ wbarσ W F n i) ≫
            wbarσ W F (n + 1) j.succ := by
          exact (Category.assoc _ _ _).symm
      _ = (wDegInnerComponent F i s ≫
            wbarIncl W F (n + 1) (wDegInnerIdx W n i ⟨s, w⟩)) ≫
            wbarσ W F (n + 1) j.succ := by
          exact congrArg (· ≫ wbarσ W F (n + 1) j.succ)
            (wbarσ_ι W F n i ⟨s, w⟩)
      _ = wDegInnerComponent F i s ≫
            (wbarIncl W F (n + 1) (wDegInnerIdx W n i ⟨s, w⟩) ≫
              wbarσ W F (n + 1) j.succ) := by
          exact Category.assoc _ _ _
      _ = wDegInnerComponent F i s ≫
            (wDegInnerComponent F j.succ
              (wDegInnerIdx W n i ⟨s, w⟩).1 ≫
              wbarIncl W F (n + 2)
                (wDegInnerIdx W (n + 1) j.succ
                  (wDegInnerIdx W n i ⟨s, w⟩))) := by
          exact congrArg (wDegInnerComponent F i s ≫ ·)
            (wbarσ_ι W F (n + 1) j.succ (wDegInnerIdx W n i ⟨s, w⟩))
      _ = (wDegInnerComponent F i s ≫
            wDegInnerComponent F j.succ
              ((StrictOmitDup.dupAt i).obj s)) ≫
            wbarIncl W F (n + 2)
              (wDegInnerIdx W (n + 1) j.succ
                (wDegInnerIdx W n i ⟨s, w⟩)) := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (wDegInnerComponent F j s ≫
      wDegInnerComponent F i.castSucc ((StrictOmitDup.dupAt j).obj s)) =
      (wDegInnerComponent F i s ≫
        wDegInnerComponent F j.succ ((StrictOmitDup.dupAt i).obj s)) := by
    unfold wDegInnerComponent
    simp only [eqToHom_trans]
    rfl
  calc wbarIncl W F n ⟨s, w⟩ ≫
          (wbarσ W F n j ≫ wbarσ W F (n + 1) i.castSucc)
      = (wDegInnerComponent F j s ≫
          wDegInnerComponent F i.castSucc
            ((StrictOmitDup.dupAt j).obj s)) ≫
          wbarIncl W F (n + 2)
            (wDegInnerIdx W (n + 1) i.castSucc
              (wDegInnerIdx W n j ⟨s, w⟩)) := hL
    _ = (wDegInnerComponent F i s ≫
          wDegInnerComponent F j.succ
            ((StrictOmitDup.dupAt i).obj s)) ≫
          wbarIncl W F (n + 2)
            (wDegInnerIdx W (n + 1) i.castSucc
              (wDegInnerIdx W n j ⟨s, w⟩)) := by
        exact congrArg (· ≫ _) hcoeff
    _ = (wDegInnerComponent F i s ≫
          wDegInnerComponent F j.succ
            ((StrictOmitDup.dupAt i).obj s)) ≫
          wbarIncl W F (n + 2)
            (wDegInnerIdx W (n + 1) j.succ
              (wDegInnerIdx W n i ⟨s, w⟩)) := by
        have hHEq := wbarInclHEqOfIdxEq W F hIdx
        have hIncl :
            wbarIncl W F (n + 2)
                (wDegInnerIdx W (n + 1) i.castSucc
                  (wDegInnerIdx W n j ⟨s, w⟩)) =
              wbarIncl W F (n + 2)
                (wDegInnerIdx W (n + 1) j.succ
                  (wDegInnerIdx W n i ⟨s, w⟩)) :=
          eq_of_heq hHEq
        exact congrArg
          ((wDegInnerComponent F i s ≫
            wDegInnerComponent F j.succ
              ((StrictOmitDup.dupAt i).obj s)) ≫ ·) hIncl
    _ = wbarIncl W F n ⟨s, w⟩ ≫
          (wbarσ W F n i ≫ wbarσ W F (n + 1) j.succ) := hR.symm

/-- Internal: `WIdx` equality for the below case with interior faces.
Chain part is `wChainBelow`; weight transports fuse on each side. The last-
index side conditions follow from `i ≤ j.castSucc` by value bounds. -/
private theorem wIdxBelowInterior (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) (_hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    (s : SrepBridge.SrepIdx J (n + 1)) (w : W.obj (Opposite.op s.right)) :
    wFaceInnerIdx W (n + 1) i.castSucc
        (by
          intro hlast
          have hval := congrArg Fin.val hlast
          simp [Fin.val_last] at hval
          have _hj := j.is_lt
          have hi := Fin.le_iff_val_le_val.mp h
          simp [Fin.val_castSucc] at hi
          omega : i.castSucc ≠ Fin.last (n + 2))
        (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩) =
      wDegInnerIdx W n j (wFaceInnerIdx W n i hiLast ⟨s, w⟩) := by
  have hchain := wChainBelow (n := n) h s
  have eDup : ((StrictOmitDup.dupAt j.succ).obj s).right = s.right :=
    wDupInner_obj_last s
  have eOmit : ((StrictOmitDup.omitAt i).obj s).right = s.right := by
    have := wOmitInner_obj_last hiLast s
    exact this
  have hne : i.castSucc ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last] at hval
    have _hj := j.is_lt
    have hi := Fin.le_iff_val_le_val.mp h
    simp [Fin.val_castSucc] at hi
    omega
  have eLeft : ((StrictOmitDup.omitAt i.castSucc).obj
      ((StrictOmitDup.dupAt j.succ).obj s)).right =
      ((StrictOmitDup.dupAt j.succ).obj s).right :=
    wOmitInner_obj_last hne _
  have eRight : ((StrictOmitDup.dupAt j).obj
      ((StrictOmitDup.omitAt i).obj s)).right =
      ((StrictOmitDup.omitAt i).obj s).right :=
    wDupInner_obj_last _
  have fuseL := wWeightFuse W eLeft eDup w
  have fuseR := wWeightFuse W eRight eOmit w
  have hL : wFaceInnerIdx W (n + 1) i.castSucc hne
      (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩) =
      (⟨(StrictOmitDup.omitAt i.castSucc).obj
        ((StrictOmitDup.dupAt j.succ).obj s),
        W.map (eqToHom (eLeft.trans eDup)).op w⟩ : WIdx J W (n + 1)) := by
    change wFaceInnerIdx W (n + 1) i.castSucc hne
        ⟨(StrictOmitDup.dupAt j.succ).obj s,
          W.map (eqToHom eDup).op w⟩ = _
    have hpair : wFaceInnerIdx W (n + 1) i.castSucc hne
        ⟨(StrictOmitDup.dupAt j.succ).obj s,
          W.map (eqToHom eDup).op w⟩ =
        ⟨(StrictOmitDup.omitAt i.castSucc).obj
          ((StrictOmitDup.dupAt j.succ).obj s),
          W.map (eqToHom eLeft).op (W.map (eqToHom eDup).op w)⟩ := rfl
    rw [hpair, fuseL]
  have hR : wDegInnerIdx W n j (wFaceInnerIdx W n i hiLast ⟨s, w⟩) =
      (⟨(StrictOmitDup.dupAt j).obj ((StrictOmitDup.omitAt i).obj s),
        W.map (eqToHom (eRight.trans eOmit)).op w⟩ : WIdx J W (n + 1)) := by
    have hpair : wDegInnerIdx W n j
        ⟨(StrictOmitDup.omitAt i).obj s, W.map (eqToHom eOmit).op w⟩ =
        ⟨(StrictOmitDup.dupAt j).obj ((StrictOmitDup.omitAt i).obj s),
          W.map (eqToHom eRight).op (W.map (eqToHom eOmit).op w)⟩ := rfl
    change wDegInnerIdx W n j (wFaceInnerIdx W n i hiLast ⟨s, w⟩) = _
    have hface : wFaceInnerIdx W n i hiLast (⟨s, w⟩ : WIdx J W (n + 1)) =
        ⟨(StrictOmitDup.omitAt i).obj s, W.map (eqToHom eOmit).op w⟩ := rfl
    rw [hface, hpair, fuseR]
  rw [hL, hR]
  exact wIdxOfChainEq W hchain (eLeft.trans eDup) (eRight.trans eOmit) w

/-- Internal: `WIdx` equality for the above case with interior faces. Chain
part is `wChainAbove`; weight transports fuse on each side. -/
private theorem wIdxAboveInterior (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) (hiLast : i ≠ Fin.last (n + 1))
    (s : SrepBridge.SrepIdx J (n + 1)) (w : W.obj (Opposite.op s.right)) :
    wFaceInnerIdx W (n + 1) i.succ
        (by
          intro hlast
          have hval := congrArg Fin.val hlast
          simp [Fin.val_last] at hval
          have hjl := Fin.lt_def.mp h
          simp [Fin.val_castSucc] at hjl
          have _hi := i.is_lt
          have hiNe : i.val ≠ n + 1 := by
            intro heq
            apply hiLast
            apply Fin.ext
            simp [Fin.val_last, heq]
          omega : i.succ ≠ Fin.last (n + 2))
        (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩) =
      wDegInnerIdx W n j (wFaceInnerIdx W n i hiLast ⟨s, w⟩) := by
  have hchain := wChainAbove (n := n) h s
  have eDup : ((StrictOmitDup.dupAt j.castSucc).obj s).right = s.right :=
    wDupInner_obj_last s
  have eOmit : ((StrictOmitDup.omitAt i).obj s).right = s.right :=
    wOmitInner_obj_last hiLast s
  have hne : i.succ ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last] at hval
    have hjl := Fin.lt_def.mp h
    simp [Fin.val_castSucc] at hjl
    have hi := i.is_lt
    have hiNe : i.val ≠ n + 1 := by
      intro heq
      apply hiLast
      apply Fin.ext
      simp [Fin.val_last, heq]
    omega
  have eLeft : ((StrictOmitDup.omitAt i.succ).obj
      ((StrictOmitDup.dupAt j.castSucc).obj s)).right =
      ((StrictOmitDup.dupAt j.castSucc).obj s).right :=
    wOmitInner_obj_last hne _
  have eRight : ((StrictOmitDup.dupAt j).obj
      ((StrictOmitDup.omitAt i).obj s)).right =
      ((StrictOmitDup.omitAt i).obj s).right :=
    wDupInner_obj_last _
  have fuseL := wWeightFuse W eLeft eDup w
  have fuseR := wWeightFuse W eRight eOmit w
  have hL : wFaceInnerIdx W (n + 1) i.succ hne
      (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩) =
      (⟨(StrictOmitDup.omitAt i.succ).obj
        ((StrictOmitDup.dupAt j.castSucc).obj s),
        W.map (eqToHom (eLeft.trans eDup)).op w⟩ : WIdx J W (n + 1)) := by
    have hpair : wFaceInnerIdx W (n + 1) i.succ hne
        ⟨(StrictOmitDup.dupAt j.castSucc).obj s,
          W.map (eqToHom eDup).op w⟩ =
        ⟨(StrictOmitDup.omitAt i.succ).obj
          ((StrictOmitDup.dupAt j.castSucc).obj s),
          W.map (eqToHom eLeft).op (W.map (eqToHom eDup).op w)⟩ := rfl
    change wFaceInnerIdx W (n + 1) i.succ hne
        ⟨(StrictOmitDup.dupAt j.castSucc).obj s,
          W.map (eqToHom eDup).op w⟩ = _
    rw [hpair, fuseL]
  have hR : wDegInnerIdx W n j (wFaceInnerIdx W n i hiLast ⟨s, w⟩) =
      (⟨(StrictOmitDup.dupAt j).obj ((StrictOmitDup.omitAt i).obj s),
        W.map (eqToHom (eRight.trans eOmit)).op w⟩ : WIdx J W (n + 1)) := by
    have hface : wFaceInnerIdx W n i hiLast (⟨s, w⟩ : WIdx J W (n + 1)) =
        ⟨(StrictOmitDup.omitAt i).obj s, W.map (eqToHom eOmit).op w⟩ := rfl
    have hpair : wDegInnerIdx W n j
        ⟨(StrictOmitDup.omitAt i).obj s, W.map (eqToHom eOmit).op w⟩ =
        ⟨(StrictOmitDup.dupAt j).obj ((StrictOmitDup.omitAt i).obj s),
          W.map (eqToHom eRight).op (W.map (eqToHom eOmit).op w)⟩ := rfl
    change wDegInnerIdx W n j (wFaceInnerIdx W n i hiLast ⟨s, w⟩) = _
    rw [hface, hpair, fuseR]
  rw [hL, hR]
  exact wIdxOfChainEq W hchain (eLeft.trans eDup) (eRight.trans eOmit) w

/-- Below relation for the total operators, in the interior-face case. Both
sides expand through the accepted inclusion rules; the index parts agree by
`wIdxBelowInterior` and the pure-transport coefficients agree by
`eqToHom_trans`. -/
private theorem wbar_δ_comp_σ_of_le_interior (n : ℕ) {i : Fin (n + 2)}
    {j : Fin (n + 1)} (h : i ≤ j.castSucc) (hi0 : i ≠ 0)
    (hiLast : i ≠ Fin.last (n + 1)) :
    wbarσ W F (n + 1) j.succ ≫ wbarδ W F (n + 1) i.castSucc =
      wbarδ W F n i ≫ wbarσ W F n j := by
  have hiCastNe : i.castSucc ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last] at hval
    have hj := j.is_lt
    have hi := Fin.le_iff_val_le_val.mp h
    simp [Fin.val_castSucc] at hi
    omega
  have hiCast0 : i.castSucc ≠ 0 := by
    intro h0
    have hval := congrArg Fin.val h0
    simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Fin.val_eq_zero_iff] at hval
    exact hi0 (Fin.ext (by simpa using hval))
  rw [wbarδ_inner _ _ _ i.castSucc hiCast0 hiCastNe, wbarδ_inner _ _ _ i hi0 hiLast]
  change wbarσ W F (n + 1) j.succ ≫
      wbarFaceInner W F (n + 1) i.castSucc hiCast0 hiCastNe =
    wbarFaceInner W F n i hi0 hiLast ≫ wbarσ W F n j
  unfold wbarσ
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  obtain ⟨s, w⟩ := p
  have hIdx := wIdxBelowInterior W n h hi0 hiLast s w
  let qL : WIdx J W (n + 1) :=
    wFaceInnerIdx W (n + 1) i.castSucc hiCastNe
      (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩)
  let qR : WIdx J W (n + 1) :=
    wDegInnerIdx W n j (wFaceInnerIdx W n i hiLast ⟨s, w⟩)
  have hL : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
      (wbarDegInner W F (n + 1) j.succ ≫
        wbarFaceInner W F (n + 1) i.castSucc hiCast0 hiCastNe) =
      (wDegInnerComponent F j.succ s ≫
        wFaceInnerComponent F i.castSucc hiCast0
          ((StrictOmitDup.dupAt j.succ).obj s)) ≫
        wbarIncl W F (n + 1) qL := by
    calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarDegInner W F (n + 1) j.succ ≫
              wbarFaceInner W F (n + 1) i.castSucc hiCast0 hiCastNe)
        = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            wbarDegInner W F (n + 1) j.succ) ≫
            wbarFaceInner W F (n + 1) i.castSucc hiCast0 hiCastNe := by
          exact (Category.assoc _ _ _).symm
      _ = (wDegInnerComponent F j.succ s ≫
            wbarIncl W F (n + 2) (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩)) ≫
            wbarFaceInner W F (n + 1) i.castSucc hiCast0 hiCastNe := by
          exact congrArg (· ≫ _)
            (wbarDegInner_ι W F (n + 1) j.succ ⟨s, w⟩)
      _ = wDegInnerComponent F j.succ s ≫
            (wbarIncl W F (n + 2) (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩) ≫
              wbarFaceInner W F (n + 1) i.castSucc hiCast0 hiCastNe) := by
          exact Category.assoc _ _ _
      _ = wDegInnerComponent F j.succ s ≫
            (wFaceInnerComponent F i.castSucc hiCast0
              ((StrictOmitDup.dupAt j.succ).obj s) ≫
              wbarIncl W F (n + 1) qL) := by
          exact congrArg (wDegInnerComponent F j.succ s ≫ ·)
            (wbarFaceInner_ι W F (n + 1) i.castSucc hiCast0 hiCastNe
              (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩))
      _ = (wDegInnerComponent F j.succ s ≫
            wFaceInnerComponent F i.castSucc hiCast0
              ((StrictOmitDup.dupAt j.succ).obj s)) ≫
            wbarIncl W F (n + 1) qL := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
      (wbarFaceInner W F n i hi0 hiLast ≫ wbarDegInner W F n j) =
      (wFaceInnerComponent F i hi0 s ≫
        wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) ≫
        wbarIncl W F (n + 1) qR := by
    calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarFaceInner W F n i hi0 hiLast ≫ wbarDegInner W F n j)
        = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            wbarFaceInner W F n i hi0 hiLast) ≫
            wbarDegInner W F n j := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F i hi0 s ≫
            wbarIncl W F n (wFaceInnerIdx W n i hiLast ⟨s, w⟩)) ≫
            wbarDegInner W F n j := by
          exact congrArg (· ≫ _) (wbarFaceInner_ι W F n i hi0 hiLast ⟨s, w⟩)
      _ = wFaceInnerComponent F i hi0 s ≫
            (wbarIncl W F n (wFaceInnerIdx W n i hiLast ⟨s, w⟩) ≫
              wbarDegInner W F n j) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F i hi0 s ≫
            (wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s) ≫
              wbarIncl W F (n + 1) qR) := by
          exact congrArg (wFaceInnerComponent F i hi0 s ≫ ·)
            (wbarDegInner_ι W F n j
              (wFaceInnerIdx W n i hiLast ⟨s, w⟩))
      _ = (wFaceInnerComponent F i hi0 s ≫
            wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) ≫
            wbarIncl W F (n + 1) qR := by
          exact (Category.assoc _ _ _).symm
  have hcoeffHEq : (wDegInnerComponent F j.succ s ≫
      wFaceInnerComponent F i.castSucc hiCast0
        ((StrictOmitDup.dupAt j.succ).obj s)) ≍
      (wFaceInnerComponent F i hi0 s ≫
        wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) := by
    unfold wDegInnerComponent wFaceInnerComponent
    simp only [eqToHom_trans]
    exact (CategoryTheory.eqToHom_heq_id_dom _ _ _).trans
      (CategoryTheory.eqToHom_heq_id_dom _ _ _).symm
  calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
          (wbarDegInner W F (n + 1) j.succ ≫
            wbarFaceInner W F (n + 1) i.castSucc hiCast0 hiCastNe)
      = (wDegInnerComponent F j.succ s ≫
          wFaceInnerComponent F i.castSucc hiCast0
            ((StrictOmitDup.dupAt j.succ).obj s)) ≫
          wbarIncl W F (n + 1) qL := hL
    _ = (wFaceInnerComponent F i hi0 s ≫
          wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) ≫
          wbarIncl W F (n + 1) qR :=
        wbarCompEqOfIdxEqHEq W F hIdx hcoeffHEq
    _ = wbarIncl W F (n + 1) ⟨s, w⟩ ≫
          (wbarFaceInner W F n i hi0 hiLast ≫ wbarDegInner W F n j) := hR.symm

/-- Below relation for the total operators. When the face index is `0` both
sides reduce to outer faces after rewriting the zeroth degeneracy through
`wbarσ_zero`; the accepted outer naturality then applies at the index level
while coefficients are identities. Otherwise the interior argument above
applies. The last-face case for `i` is impossible under `i ≤ j.castSucc`
unless `j` is also last, in which case both faces are outer and the accepted
outer interchange applies. -/
theorem wbar_δ_comp_σ_of_le (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) :
    wbarσ W F (n + 1) j.succ ≫ wbarδ W F (n + 1) i.castSucc =
      wbarδ W F n i ≫ wbarσ W F n j := by
  by_cases hi0 : i = 0
  · subst hi0
    have h0eq : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    rw [h0eq, wbarδ_zero, wbarδ_zero]
    change wbarσ W F (n + 1) j.succ ≫ wbarFaceZero W F (n + 1) =
      wbarFaceZero W F n ≫ wbarσ W F n j
    unfold wbarσ
    refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
    obtain ⟨s, w⟩ := p
    have hchain : SrepBridge.srepDropFirst
        ((StrictOmitDup.dupAt j.succ).obj s) =
        (StrictOmitDup.dupAt j).obj (SrepBridge.srepDropFirst s) := by
      have hL0 := wOmitZeroChain ((StrictOmitDup.dupAt j.succ).obj s)
      have hR0 := wOmitZeroChain s
      have hMid := wChainBelow (n := n) (i := (0 : Fin (n + 2)))
        (j := j) (Fin.zero_le _) s
      have h0eq : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
        apply Fin.ext
        simp
      rw [h0eq] at hMid
      exact hL0.trans (hMid.trans (congrArg _ hR0.symm))
    have eDup : ((StrictOmitDup.dupAt j.succ).obj s).right = s.right :=
      wDupInner_obj_last s
    have eRight : ((StrictOmitDup.dupAt j).obj
        (SrepBridge.srepDropFirst s)).right =
        (SrepBridge.srepDropFirst s).right :=
      wDupInner_obj_last _
    have hIdx : wFaceZeroIdx W (n + 1)
        (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩) =
        wDegInnerIdx W n j (wFaceZeroIdx W n ⟨s, w⟩) := by
      change (⟨SrepBridge.srepDropFirst
          ((StrictOmitDup.dupAt j.succ).obj s),
          W.map (eqToHom eDup).op w⟩ : WIdx J W (n + 1)) =
        ⟨(StrictOmitDup.dupAt j).obj (SrepBridge.srepDropFirst s),
          W.map (eqToHom eRight).op w⟩
      exact wIdxOfChainEq W hchain eDup eRight w
    let pL : WIdx J W (n + 1) :=
      wFaceZeroIdx W (n + 1) (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩)
    let pR : WIdx J W (n + 1) :=
      wDegInnerIdx W n j (wFaceZeroIdx W n ⟨s, w⟩)
    have hL : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
        (wbarDegInner W F (n + 1) j.succ ≫ wbarFaceZero W F (n + 1)) =
        (wDegInnerComponent F j.succ s ≫
          SrepBridge.srepFaceZeroComponent F
            ((StrictOmitDup.dupAt j.succ).obj s)) ≫
          wbarIncl W F (n + 1) pL := by
      calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              (wbarDegInner W F (n + 1) j.succ ≫ wbarFaceZero W F (n + 1))
          = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              wbarDegInner W F (n + 1) j.succ) ≫
              wbarFaceZero W F (n + 1) := by
            exact (Category.assoc _ _ _).symm
        _ = (wDegInnerComponent F j.succ s ≫
              wbarIncl W F (n + 2)
                (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩)) ≫
              wbarFaceZero W F (n + 1) := by
            exact congrArg (· ≫ _) (wbarDegInner_ι W F _ _ _)
        _ = wDegInnerComponent F j.succ s ≫
              (wbarIncl W F (n + 2)
                (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩) ≫
                wbarFaceZero W F (n + 1)) := by
            exact Category.assoc _ _ _
        _ = wDegInnerComponent F j.succ s ≫
              (SrepBridge.srepFaceZeroComponent F
                ((StrictOmitDup.dupAt j.succ).obj s) ≫
                wbarIncl W F (n + 1) pL) := by
            exact congrArg (wDegInnerComponent F j.succ s ≫ ·)
              (wbarFaceZero_ι W F (n + 1)
                (wDegInnerIdx W (n + 1) j.succ ⟨s, w⟩))
        _ = (wDegInnerComponent F j.succ s ≫
              SrepBridge.srepFaceZeroComponent F
                ((StrictOmitDup.dupAt j.succ).obj s)) ≫
              wbarIncl W F (n + 1) pL := by
            exact (Category.assoc _ _ _).symm
    have hR : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
        (wbarFaceZero W F n ≫ wbarDegInner W F n j) =
        (SrepBridge.srepFaceZeroComponent F s ≫
          wDegInnerComponent F j (SrepBridge.srepDropFirst s)) ≫
          wbarIncl W F (n + 1) pR := by
      calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              (wbarFaceZero W F n ≫ wbarDegInner W F n j)
          = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫ wbarFaceZero W F n) ≫
              wbarDegInner W F n j := by
            exact (Category.assoc _ _ _).symm
        _ = (SrepBridge.srepFaceZeroComponent F s ≫
              wbarIncl W F n (wFaceZeroIdx W n ⟨s, w⟩)) ≫
              wbarDegInner W F n j := by
            exact congrArg (· ≫ _) (wbarFaceZero_ι W F n ⟨s, w⟩)
        _ = SrepBridge.srepFaceZeroComponent F s ≫
              (wbarIncl W F n (wFaceZeroIdx W n ⟨s, w⟩) ≫
                wbarDegInner W F n j) := by
            exact Category.assoc _ _ _
        _ = SrepBridge.srepFaceZeroComponent F s ≫
              (wDegInnerComponent F j (SrepBridge.srepDropFirst s) ≫
                wbarIncl W F (n + 1) pR) := by
            exact congrArg (SrepBridge.srepFaceZeroComponent F s ≫ ·)
              (wbarDegInner_ι W F n j (wFaceZeroIdx W n ⟨s, w⟩))
        _ = (SrepBridge.srepFaceZeroComponent F s ≫
              wDegInnerComponent F j (SrepBridge.srepDropFirst s)) ≫
              wbarIncl W F (n + 1) pR := by
            exact (Category.assoc _ _ _).symm
    have hcoeffHEq : (wDegInnerComponent F j.succ s ≫
        SrepBridge.srepFaceZeroComponent F
          ((StrictOmitDup.dupAt j.succ).obj s)) ≍
        (SrepBridge.srepFaceZeroComponent F s ≫
          wDegInnerComponent F j (SrepBridge.srepDropFirst s)) := by
      have e0 : (StrictOmitDup.dupFinFunctor (n + 1) j.succ).obj
          (⟨0, by omega⟩ : Fin (n + 3)) = (⟨0, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [StrictOmitDup.dupFinFunctor_obj]
        show (j.succ.predAbove (⟨0, by omega⟩ : Fin (n + 3))).val = 0
        rw [Fin.predAbove_of_le_castSucc _ _ (by
          rw [Fin.le_iff_val_le_val]
          change (0 : ℕ) ≤ (Fin.castSucc j.succ).val
          omega)]
        rfl
      have e1 : (StrictOmitDup.dupFinFunctor (n + 1) j.succ).obj
          (⟨1, by omega⟩ : Fin (n + 3)) = (⟨1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [StrictOmitDup.dupFinFunctor_obj]
        show (j.succ.predAbove (⟨1, by omega⟩ : Fin (n + 3))).val = 1
        have hval : (Fin.castSucc j.succ).val = j.val + 1 := by
          simp only [Fin.val_castSucc, Fin.val_succ]
        rw [Fin.predAbove_of_le_castSucc _ _ (by
          rw [Fin.le_iff_val_le_val, hval]
          change (1 : ℕ) ≤ j.val + 1
          omega)]
        rfl
      have harr : (((StrictOmitDup.dupAt j.succ).obj s).map' 0 1 (by omega)
          (by omega)) =
          eqToHom (congrArg s.obj e0) ≫ s.map' 0 1 (by omega) (by omega) ≫
            eqToHom (congrArg s.obj e1.symm) := by
        exact StrictOmitDup.whiskerLeft_map' s e0 e1
      have hmap : F.map (((StrictOmitDup.dupAt j.succ).obj s).map' 0 1 (by omega)
          (by omega)) =
          F.map (eqToHom (congrArg s.obj e0)) ≫
            F.map (s.map' 0 1 (by omega) (by omega)) ≫
              F.map (eqToHom (congrArg s.obj e1.symm)) := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg F.map harr
      unfold wDegInnerComponent SrepBridge.srepFaceZeroComponent
      rw [hmap, eqToHom_map, eqToHom_map]
      let core : F.obj (s.obj ⟨0, by omega⟩) ⟶
          F.obj (s.obj ⟨1, by omega⟩) :=
        F.map (s.map' 0 1 (by omega) (by omega))
      have hLead : F.obj s.left = F.obj (s.obj ⟨0, by omega⟩) :=
        congrArg F.obj (SrepBridge.srepLeftZero s)
      have hMid : F.obj (s.obj ⟨1, by omega⟩) =
          F.obj ((SrepBridge.srepDropFirst s).left) :=
        congrArg F.obj (SrepBridge.srepDropFirst_left s).symm
      have hLast : F.obj ((SrepBridge.srepDropFirst s).left) =
          F.obj (((StrictOmitDup.dupAt j).obj
            (SrepBridge.srepDropFirst s)).left) :=
        congrArg F.obj (wDupInner_obj_zero
          (SrepBridge.srepDropFirst s)).symm
      have hDegOuter : F.obj s.left =
          F.obj (((StrictOmitDup.dupAt j.succ).obj s).left) :=
        congrArg F.obj (wDupInner_obj_zero s).symm
      have hLeadDup : F.obj (((StrictOmitDup.dupAt j.succ).obj s).left) =
          F.obj (((StrictOmitDup.dupAt j.succ).obj s).obj ⟨0, by omega⟩) :=
        congrArg F.obj
          (SrepBridge.srepLeftZero ((StrictOmitDup.dupAt j.succ).obj s))
      have hMapLead : F.obj
          (((StrictOmitDup.dupAt j.succ).obj s).obj ⟨0, by omega⟩) =
          F.obj (s.obj ⟨0, by omega⟩) :=
        congrArg F.obj (congrArg s.obj e0)
      have hMapTrail : F.obj (s.obj ⟨1, by omega⟩) =
          F.obj (((StrictOmitDup.dupAt j.succ).obj s).obj ⟨1, by omega⟩) :=
        congrArg F.obj (congrArg s.obj e1.symm)
      have hMidDup : F.obj
          (((StrictOmitDup.dupAt j.succ).obj s).obj ⟨1, by omega⟩) =
          F.obj ((SrepBridge.srepDropFirst
            ((StrictOmitDup.dupAt j.succ).obj s)).left) :=
        congrArg F.obj (SrepBridge.srepDropFirst_left
          ((StrictOmitDup.dupAt j.succ).obj s)).symm
      have hRightCore :
          (((eqToHom hLead ≫ core) ≫ eqToHom hMid) ≫
            eqToHom hLast) ≍ core :=
        ((CategoryTheory.comp_eqToHom_heq (C := C)
          (f := (eqToHom hLead ≫ core) ≫ eqToHom hMid)
          (h := hLast)).trans (CategoryTheory.comp_eqToHom_heq
          (C := C) (f := eqToHom hLead ≫ core) (h := hMid))).trans
          (CategoryTheory.eqToHom_comp_heq (C := C)
          (f := core) (h := hLead))
      have hLeftCore :
          (((eqToHom hDegOuter ≫ eqToHom hLeadDup) ≫
            ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)) ≫
            eqToHom hMidDup) ≍ core := by
        have hDropMid : ((((eqToHom hDegOuter ≫ eqToHom hLeadDup) ≫
            ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)) ≫
            eqToHom hMidDup)) ≍ ((eqToHom hDegOuter ≫ eqToHom hLeadDup) ≫
                ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)) :=
          CategoryTheory.comp_eqToHom_heq (C := C)
            (f := (eqToHom hDegOuter ≫ eqToHom hLeadDup) ≫
              ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail))
            (h := hMidDup)
        have hAssoc : (((eqToHom hDegOuter ≫ eqToHom hLeadDup) ≫
                ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail))) ≍
            (eqToHom hDegOuter ≫ (eqToHom hLeadDup ≫
              ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail))) :=
          heq_of_eq (Category.assoc (f := eqToHom hDegOuter)
            (g := eqToHom hLeadDup)
            (h := ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)))
        have hDropDeg : (eqToHom hDegOuter ≫ (eqToHom hLeadDup ≫
                ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail))) ≍
            (eqToHom hLeadDup ≫
              ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)) :=
          CategoryTheory.eqToHom_comp_heq (C := C)
            (f := eqToHom hLeadDup ≫
              ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail))
            (h := hDegOuter)
        have hDropLead : (eqToHom hLeadDup ≫
                ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)) ≍
            ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail) :=
          CategoryTheory.eqToHom_comp_heq (C := C)
            (f := (eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)
            (h := hLeadDup)
        have hDropTrail : (((eqToHom hMapLead ≫ core) ≫
            eqToHom hMapTrail)) ≍ (eqToHom hMapLead ≫ core) :=
          CategoryTheory.comp_eqToHom_heq (C := C)
            (f := eqToHom hMapLead ≫ core)
            (h := hMapTrail)
        have hDropMap : (eqToHom hMapLead ≫ core) ≍ core :=
          CategoryTheory.eqToHom_comp_heq (C := C)
            (f := core)
            (h := hMapLead)
        exact hDropMid.trans (hAssoc.trans (hDropDeg.trans
          (hDropLead.trans (hDropTrail.trans hDropMap))))
      have hBoundaryL :
          (eqToHom hDegOuter ≫ eqToHom hLeadDup ≫
            (eqToHom hMapLead ≫ core ≫ eqToHom hMapTrail) ≫ eqToHom hMidDup) ≍
          (((eqToHom hDegOuter ≫ eqToHom hLeadDup) ≫
            ((eqToHom hMapLead ≫ core) ≫ eqToHom hMapTrail)) ≫
            eqToHom hMidDup) :=
        heq_of_eq (by simp only [← Category.assoc])
      have hBoundaryR :
          (((eqToHom hLead ≫ core) ≫ eqToHom hMid) ≫ eqToHom hLast) ≍
          ((eqToHom hLead ≫ core ≫ eqToHom hMid) ≫ eqToHom hLast) :=
        heq_of_eq (by simp only [← Category.assoc])
      exact hBoundaryL.trans (hLeftCore.trans (hRightCore.symm.trans hBoundaryR))
    calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarσ W F (n + 1) j.succ ≫ wbarFaceZero W F (n + 1))
        = (wDegInnerComponent F j.succ s ≫
            SrepBridge.srepFaceZeroComponent F
              ((StrictOmitDup.dupAt j.succ).obj s)) ≫
            wbarIncl W F (n + 1) pL := hL
      _ = (SrepBridge.srepFaceZeroComponent F s ≫
            wDegInnerComponent F j (SrepBridge.srepDropFirst s)) ≫
            wbarIncl W F (n + 1) pR :=
          wbarCompEqOfIdxEqHEq W F hIdx hcoeffHEq
      _ = wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarFaceZero W F n ≫ wbarDegInner W F n j) := hR.symm
  · by_cases hiLast : i = Fin.last (n + 1)
    · subst hiLast
      have hcontra := Fin.le_iff_val_le_val.mp h
      simp [Fin.val_last, Fin.val_castSucc] at hcontra
      have hj := j.is_lt
      omega
    · exact wbar_δ_comp_σ_of_le_interior W F n h hi0 hiLast

/-- Self relation for the total operators: `σ i ≫ δ i.castSucc = 𝟙`. At
`i = 0` the degeneracy rewrites to outer `s₀` through `wbarσ_zero` and the
accepted outer section law applies. Otherwise both operators are interior
and the chain identity `wChainSelf` plus weight/coefficient fusion give the
identity. -/
theorem wbar_δ_comp_σ_self (n : ℕ) {i : Fin (n + 1)} :
    wbarσ W F n i ≫ wbarδ W F n i.castSucc = 𝟙 (wbarObj W F n) := by
  by_cases hi0 : i = 0
  · subst hi0
    have h0eq : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      simp
    rw [h0eq, wbarδ_zero, wbarσ_zero]
    exact wbarDegZero_faceZero_section W F n
  · have hiCast0 : i.castSucc ≠ (0 : Fin (n + 2)) := by
      intro h0
      have hval := congrArg Fin.val h0
      simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        Fin.val_eq_zero_iff] at hval
      exact hi0 (Fin.ext (by simpa using hval))
    have hiCastLast : i.castSucc ≠ Fin.last (n + 1) := by
      intro hlast
      have hval := congrArg Fin.val hlast
      simp [Fin.val_last, Fin.val_castSucc] at hval
      have hi := i.is_lt
      omega
    rw [wbarδ_inner _ _ _ i.castSucc hiCast0 hiCastLast]
    change wbarσ W F n i ≫ wbarFaceInner W F n i.castSucc hiCast0 hiCastLast =
      𝟙 _
    unfold wbarσ
    refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
    obtain ⟨s, w⟩ := p
    have hchain := wChainSelf (n := n) (i := i) s
    have eDup : ((StrictOmitDup.dupAt i).obj s).right = s.right :=
      wDupInner_obj_last s
    have eOmit : ((StrictOmitDup.omitAt i.castSucc).obj
        ((StrictOmitDup.dupAt i).obj s)).right =
        ((StrictOmitDup.dupAt i).obj s).right :=
      wOmitInner_obj_last hiCastLast _
    have hIdx : wFaceInnerIdx W n i.castSucc hiCastLast
        (wDegInnerIdx W n i ⟨s, w⟩) = (⟨s, w⟩ : WIdx J W n) := by
      have fuse := wWeightFuse W eOmit eDup w
      have hpair : wFaceInnerIdx W n i.castSucc hiCastLast
          ⟨(StrictOmitDup.dupAt i).obj s, W.map (eqToHom eDup).op w⟩ =
          ⟨(StrictOmitDup.omitAt i.castSucc).obj
            ((StrictOmitDup.dupAt i).obj s),
            W.map (eqToHom eOmit).op (W.map (eqToHom eDup).op w)⟩ := rfl
      change wFaceInnerIdx W n i.castSucc hiCastLast
          ⟨(StrictOmitDup.dupAt i).obj s, W.map (eqToHom eDup).op w⟩ = _
      rw [hpair, fuse]
      simpa only [eqToHom_refl, Functor.map_id, op_id, Functor.map_id_apply, id_apply] using
        wIdxOfChainEq W hchain (eOmit.trans eDup) rfl w
    calc wbarIncl W F n ⟨s, w⟩ ≫
            (wbarDegInner W F n i ≫
              wbarFaceInner W F n i.castSucc hiCast0 hiCastLast)
        = (wDegInnerComponent F i s ≫
            wFaceInnerComponent F i.castSucc hiCast0
              ((StrictOmitDup.dupAt i).obj s)) ≫
            wbarIncl W F n (wFaceInnerIdx W n i.castSucc hiCastLast
              (wDegInnerIdx W n i ⟨s, w⟩)) := by
          calc wbarIncl W F n ⟨s, w⟩ ≫
                  (wbarDegInner W F n i ≫
                    wbarFaceInner W F n i.castSucc hiCast0 hiCastLast)
              = (wbarIncl W F n ⟨s, w⟩ ≫ wbarDegInner W F n i) ≫ _ := by
                exact (Category.assoc _ _ _).symm
            _ = (wDegInnerComponent F i s ≫
                  wbarIncl W F (n + 1) (wDegInnerIdx W n i ⟨s, w⟩)) ≫
                wbarFaceInner W F n i.castSucc hiCast0 hiCastLast := by
              exact congrArg (· ≫ wbarFaceInner W F n i.castSucc hiCast0 hiCastLast)
                (wbarDegInner_ι W F n i ⟨s, w⟩)
            _ = wDegInnerComponent F i s ≫
                (wbarIncl W F (n + 1) (wDegInnerIdx W n i ⟨s, w⟩) ≫
                  wbarFaceInner W F n i.castSucc hiCast0 hiCastLast) := by
              exact Category.assoc _ _ _
            _ = wDegInnerComponent F i s ≫
                (wFaceInnerComponent F i.castSucc hiCast0
                  (wDegInnerIdx W n i ⟨s, w⟩).1 ≫
                  wbarIncl W F n
                    (wFaceInnerIdx W n i.castSucc hiCastLast
                      (wDegInnerIdx W n i ⟨s, w⟩))) := by
              exact congrArg (wDegInnerComponent F i s ≫ ·)
                (wbarFaceInner_ι W F n i.castSucc hiCast0 hiCastLast
                  (wDegInnerIdx W n i ⟨s, w⟩))
            _ = _ := by
              exact (Category.assoc (f := wDegInnerComponent F i s)
                (g := wFaceInnerComponent F i.castSucc hiCast0
                  (wDegInnerIdx W n i ⟨s, w⟩).1)
                (h := wbarIncl W F n (wFaceInnerIdx W n i.castSucc hiCastLast
                  (wDegInnerIdx W n i ⟨s, w⟩)))).symm
      _ = 𝟙 _ ≫ wbarIncl W F n ⟨s, w⟩ := by
          have hcoeffHEq : (wDegInnerComponent F i s ≫
              wFaceInnerComponent F i.castSucc hiCast0
                ((StrictOmitDup.dupAt i).obj s)) ≍ 𝟙 (F.obj s.left) := by
            unfold wDegInnerComponent wFaceInnerComponent
            simp only [eqToHom_trans]
            exact CategoryTheory.eqToHom_heq_id_dom _ _ _
          exact wbarCompEqOfIdxEqHEq W F hIdx hcoeffHEq
      _ = wbarIncl W F n ⟨s, w⟩ ≫ 𝟙 _ := by
          exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Successor relation for the total operators: `σ i ≫ δ i.succ = 𝟙`.
The degeneracy index is never `0` after succession, so no `wbarσ_zero`
rewrite is needed. At `i = last` the face is outer-last (pure transport)
and the index equality is direct by `ext`; otherwise both operators are
interior and `wChainSucc` applies. Coefficients are pure transports in all
cases. -/
theorem wbar_δ_comp_σ_succ (n : ℕ) {i : Fin (n + 1)} :
    wbarσ W F n i ≫ wbarδ W F n i.succ = 𝟙 (wbarObj W F n) := by
  have hSucc0 : i.succ ≠ (0 : Fin (n + 2)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp [Fin.val_succ] at hval
  by_cases hiLast : i = Fin.last n
  · subst hiLast
    have hSuccLast : (Fin.last n).succ = Fin.last (n + 1) := by
      apply Fin.ext
      simp [Fin.val_last]
    rw [hSuccLast, wbarδ_last]
    change wbarσ W F n _ ≫ wbarFaceLast W F n = 𝟙 _
    unfold wbarσ
    refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
    obtain ⟨s, w⟩ := p
    have hchain : SrepBridge.srepDropLast
        ((StrictOmitDup.dupAt (Fin.last n)).obj s) = s := by
      have e1 := wChainSucc (n := n)
        (i := Fin.last n) s
      have hLast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        simp [Fin.val_last]
      rw [hLast] at e1
      have hOmit := wOmitLastChain
        ((StrictOmitDup.dupAt (Fin.last n)).obj s)
      exact hOmit.trans e1
    have eDup : ((StrictOmitDup.dupAt (Fin.last n)).obj s).right = s.right :=
      wDupInner_obj_last s
    have hDupTop :=
      StrictOmitDup.dupTop_lastArrow_id (C := J) s
    have hIdx : wFaceLastIdx W n
        (wDegInnerIdx W n (Fin.last n) ⟨s, w⟩) =
        (⟨s, w⟩ : WIdx J W n) := by
      have hCollapse : W.map
            (((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1) (by omega)
              (by omega)).op
            (W.map (eqToHom eDup).op w) =
            W.map
              ((((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1)
                (by omega) (by omega)) ≫ eqToHom eDup).op w :=
        wWeightComp W
          (((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1) (by omega)
            (by omega))
          (eqToHom eDup) w
      have hf : (((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1)
            (by omega) (by omega)) ≫ eqToHom eDup =
          eqToHom
              (congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain) ≫
            (𝟙 _ : s.right ⟶ s.right) := by
        rw [hDupTop]
        simp only [eqToHom_trans, Category.comp_id,
          Category.id_comp]
        have hTop : ((StrictOmitDup.dupAt (Fin.last n)).obj s).obj ⟨n, by omega⟩ =
            ((StrictOmitDup.dupAt (Fin.last n)).obj s).obj ⟨n + 1, by omega⟩ :=
          (congrArg s.obj StrictOmitDup.dupTop_prev).trans
            (congrArg s.obj (StrictOmitDup.dupIdx_top (p := Fin.last n)).symm)
        have hTerm : (eqToHom hTop ≫ eqToHom eDup) ≍ eqToHom hTop :=
          CategoryTheory.comp_eqToHom_heq (C := J) (f := eqToHom hTop) (h := eDup)
        exact eq_of_heq (hTerm.trans
          ((CategoryTheory.eqToHom_heq_id_dom
              (((StrictOmitDup.dupAt (Fin.last n)).obj s).obj ⟨n, by omega⟩)
              (((StrictOmitDup.dupAt (Fin.last n)).obj s).right) hTop).trans
            (CategoryTheory.eqToHom_heq_id_dom
              (((StrictOmitDup.dupAt (Fin.last n)).obj s).obj ⟨n, by omega⟩)
              (s.right)
              (congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain)).symm))
      have hpair : wFaceLastIdx W n
            (wDegInnerIdx W n (Fin.last n) ⟨s, w⟩) =
          (⟨SrepBridge.srepDropLast
              ((StrictOmitDup.dupAt (Fin.last n)).obj s),
            W.map
              ((((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1)
                (by omega) (by omega)) ≫ eqToHom eDup).op w⟩ :
            WIdx J W n) := by
        change wFaceLastIdx W n
            ⟨(StrictOmitDup.dupAt (Fin.last n)).obj s,
              W.map (eqToHom eDup).op w⟩ = _
        have hbase : wFaceLastIdx W n
              ⟨(StrictOmitDup.dupAt (Fin.last n)).obj s,
                W.map (eqToHom eDup).op w⟩ =
            ⟨SrepBridge.srepDropLast
                ((StrictOmitDup.dupAt (Fin.last n)).obj s),
              W.map
                (((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1)
                  (by omega) (by omega)).op
                (W.map (eqToHom eDup).op w)⟩ := rfl
        rw [hbase, hCollapse]
      rw [hpair]
      have hBase : (⟨SrepBridge.srepDropLast
          ((StrictOmitDup.dupAt (Fin.last n)).obj s),
        W.map
          ((((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1)
            (by omega) (by omega)) ≫ eqToHom eDup).op w⟩ :
        WIdx J W n) = (⟨s, W.map (𝟙 _).op w⟩ : WIdx J W n) :=
        wIdxOfChainEqMap W hchain
          ((((StrictOmitDup.dupAt (Fin.last n)).obj s).map' n (n + 1) (by omega)
              (by omega)) ≫ eqToHom eDup)
          (𝟙 _) hf w
      have hId : (⟨s, W.map (𝟙 _).op w⟩ : WIdx J W n) = ⟨s, w⟩ := by
        have hWeight : W.map (𝟙 s.right).op w = w := by
          simp only [op_id, Functor.map_id_apply]
        exact Sigma.ext rfl (heq_of_eq hWeight)
      exact hBase.trans hId
    let pDeg : WIdx J W (n + 1) := wDegInnerIdx W n (Fin.last n) ⟨s, w⟩
    let pFace : WIdx J W n := wFaceLastIdx W n pDeg
    calc wbarIncl W F n ⟨s, w⟩ ≫
            (wbarDegInner W F n (Fin.last n) ≫ wbarFaceLast W F n)
        = (wDegInnerComponent F (Fin.last n) s ≫
            SrepBridge.srepFaceLastComponent F pDeg.1) ≫
            wbarIncl W F n pFace := by
          calc wbarIncl W F n ⟨s, w⟩ ≫
                  (wbarDegInner W F n (Fin.last n) ≫ wbarFaceLast W F n)
              = (wbarIncl W F n ⟨s, w⟩ ≫ wbarDegInner W F n (Fin.last n)) ≫
                  wbarFaceLast W F n := by
                exact (Category.assoc _ _ _).symm
            _ = (wDegInnerComponent F (Fin.last n) s ≫
                  wbarIncl W F (n + 1) pDeg) ≫
                  wbarFaceLast W F n := by
                exact congrArg (· ≫ wbarFaceLast W F n)
                  (wbarDegInner_ι W F n (Fin.last n) ⟨s, w⟩)
            _ = wDegInnerComponent F (Fin.last n) s ≫
                (wbarIncl W F (n + 1) pDeg ≫ wbarFaceLast W F n) := by
                exact Category.assoc _ _ _
            _ = wDegInnerComponent F (Fin.last n) s ≫
                (SrepBridge.srepFaceLastComponent F pDeg.1 ≫
                  wbarIncl W F n pFace) := by
                exact congrArg (wDegInnerComponent F (Fin.last n) s ≫ ·)
                  (wbarFaceLast_ι W F n pDeg)
            _ = _ := by
                exact (Category.assoc (f := wDegInnerComponent F (Fin.last n) s)
                  (g := SrepBridge.srepFaceLastComponent F pDeg.1)
                  (h := wbarIncl W F n pFace)).symm
      _ = 𝟙 (F.obj s.left) ≫ wbarIncl W F n ⟨s, w⟩ := by
          have hcoeff : (wDegInnerComponent F (Fin.last n) s ≫
              SrepBridge.srepFaceLastComponent F pDeg.1) = 𝟙 (F.obj s.left) := by
            dsimp only [pDeg, wDegInnerIdx]
            unfold wDegInnerComponent SrepBridge.srepFaceLastComponent
            rw [CategoryTheory.eqToHom_trans]
            have hDupLeft : ((StrictOmitDup.dupAt (Fin.last n)).obj s).left = s.left :=
              wDupInner_obj_zero s
            have hDropLeft : ((StrictOmitDup.dupAt (Fin.last n)).obj s).left =
                (SrepBridge.srepDropLast ((StrictOmitDup.dupAt (Fin.last n)).obj s)).left :=
              (SrepBridge.srepDropLast_left ((StrictOmitDup.dupAt (Fin.last n)).obj s)).symm
            have hComb : F.obj s.left =
                F.obj (SrepBridge.srepDropLast ((StrictOmitDup.dupAt (Fin.last n)).obj s)).left :=
              (congrArg F.obj hDupLeft.symm).trans (congrArg F.obj hDropLeft)
            exact eq_of_heq
              (CategoryTheory.eqToHom_heq_id_dom (C := C) (X := F.obj s.left)
                (Y := F.obj (SrepBridge.srepDropLast
                  ((StrictOmitDup.dupAt (Fin.last n)).obj s)).left)
                (h := hComb))
          have hPFace : pFace = (⟨s, w⟩ : WIdx J W n) := by
            dsimp only [pFace, pDeg]
            exact hIdx
          have hcoeffHEq : (wDegInnerComponent F (Fin.last n) s ≫
              SrepBridge.srepFaceLastComponent F pDeg.1) ≍ 𝟙 (F.obj s.left) :=
            heq_of_eq hcoeff
          exact wbarCompEqOfIdxEqHEq W F hPFace hcoeffHEq
      _ = wbarIncl W F n ⟨s, w⟩ ≫ 𝟙 _ := by
          exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have hSuccLast : i.succ ≠ Fin.last (n + 1) := by
      intro hlast
      have hval := congrArg Fin.val hlast
      simp [Fin.val_last, Fin.val_succ] at hval
      have hne : i.val ≠ n := by
        intro heq
        apply hiLast
        apply Fin.ext
        simp [Fin.val_last, heq]
      omega
    rw [wbarδ_inner _ _ _ i.succ hSucc0 hSuccLast]
    change wbarσ W F n i ≫ wbarFaceInner W F n i.succ hSucc0 hSuccLast = 𝟙 _
    unfold wbarσ
    refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
    obtain ⟨s, w⟩ := p
    have hchain := wChainSucc (n := n) (i := i) s
    have eDup : ((StrictOmitDup.dupAt i).obj s).right = s.right :=
      wDupInner_obj_last s
    have eOmit : ((StrictOmitDup.omitAt i.succ).obj
        ((StrictOmitDup.dupAt i).obj s)).right =
        ((StrictOmitDup.dupAt i).obj s).right :=
      wOmitInner_obj_last (by
        intro hlast
        have hval := congrArg Fin.val hlast
        simp [Fin.val_last, Fin.val_succ] at hval
        have hi := i.is_lt
        omega) _
    have hIdx : wFaceInnerIdx W n i.succ hSuccLast
        (wDegInnerIdx W n i ⟨s, w⟩) = (⟨s, w⟩ : WIdx J W n) := by
      have fuse := wWeightFuse W eOmit eDup w
      have hpair : wFaceInnerIdx W n i.succ hSuccLast
          ⟨(StrictOmitDup.dupAt i).obj s, W.map (eqToHom eDup).op w⟩ =
          ⟨(StrictOmitDup.omitAt i.succ).obj
            ((StrictOmitDup.dupAt i).obj s),
            W.map (eqToHom eOmit).op (W.map (eqToHom eDup).op w)⟩ := rfl
      change wFaceInnerIdx W n i.succ hSuccLast
          ⟨(StrictOmitDup.dupAt i).obj s, W.map (eqToHom eDup).op w⟩ = _
      rw [hpair, fuse]
      have hBase : (⟨(StrictOmitDup.omitAt i.succ).obj
          ((StrictOmitDup.dupAt i).obj s),
          W.map (eqToHom (eOmit.trans eDup)).op w⟩ : WIdx J W n) =
          (⟨s, W.map (𝟙 s.right).op w⟩ : WIdx J W n) :=
        wIdxOfChainEq W hchain (eOmit.trans eDup) rfl w
      have hWeight : W.map (𝟙 s.right).op w = w := by
        simp only [op_id, Functor.map_id_apply]
      have hId : (⟨s, W.map (𝟙 s.right).op w⟩ : WIdx J W n) = ⟨s, w⟩ :=
        Sigma.ext rfl (heq_of_eq hWeight)
      exact hBase.trans hId
    let pDeg : WIdx J W (n + 1) := wDegInnerIdx W n i ⟨s, w⟩
    let pFace : WIdx J W n := wFaceInnerIdx W n i.succ hSuccLast pDeg
    calc wbarIncl W F n ⟨s, w⟩ ≫
            (wbarDegInner W F n i ≫
              wbarFaceInner W F n i.succ hSucc0 hSuccLast)
        = (wDegInnerComponent F i s ≫
            wFaceInnerComponent F i.succ hSucc0 pDeg.1) ≫
            wbarIncl W F n pFace := by
          calc wbarIncl W F n ⟨s, w⟩ ≫
                  (wbarDegInner W F n i ≫
                    wbarFaceInner W F n i.succ hSucc0 hSuccLast)
              = (wbarIncl W F n ⟨s, w⟩ ≫ wbarDegInner W F n i) ≫
                  wbarFaceInner W F n i.succ hSucc0 hSuccLast := by
                exact (Category.assoc _ _ _).symm
            _ = (wDegInnerComponent F i s ≫
                  wbarIncl W F (n + 1) pDeg) ≫
                  wbarFaceInner W F n i.succ hSucc0 hSuccLast := by
                exact congrArg (· ≫ wbarFaceInner W F n i.succ hSucc0 hSuccLast)
                  (wbarDegInner_ι W F n i ⟨s, w⟩)
            _ = wDegInnerComponent F i s ≫
                (wbarIncl W F (n + 1) pDeg ≫
                  wbarFaceInner W F n i.succ hSucc0 hSuccLast) := by
                exact Category.assoc _ _ _
            _ = wDegInnerComponent F i s ≫
                (wFaceInnerComponent F i.succ hSucc0 pDeg.1 ≫
                  wbarIncl W F n pFace) := by
                exact congrArg (wDegInnerComponent F i s ≫ ·)
                  (wbarFaceInner_ι W F n i.succ hSucc0 hSuccLast pDeg)
            _ = _ := by
                exact (Category.assoc (f := wDegInnerComponent F i s)
                  (g := wFaceInnerComponent F i.succ hSucc0 pDeg.1)
                  (h := wbarIncl W F n pFace)).symm
      _ = 𝟙 (F.obj s.left) ≫ wbarIncl W F n ⟨s, w⟩ := by
          have hcoeff : (wDegInnerComponent F i s ≫
              wFaceInnerComponent F i.succ hSucc0 pDeg.1) =
              𝟙 (F.obj s.left) := by
            dsimp only [pDeg, wDegInnerIdx]
            unfold wDegInnerComponent wFaceInnerComponent
            simp only [eqToHom_trans]
            rfl
          have hPFace : pFace = (⟨s, w⟩ : WIdx J W n) := by
            dsimp only [pFace, pDeg]
            exact hIdx
          have hcoeffHEq : (wDegInnerComponent F i s ≫
              wFaceInnerComponent F i.succ hSucc0 pDeg.1) ≍ 𝟙 (F.obj s.left) :=
            heq_of_eq hcoeff
          exact wbarCompEqOfIdxEqHEq W F hPFace hcoeffHEq
      _ = wbarIncl W F n ⟨s, w⟩ ≫ 𝟙 _ := by
          exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Above relation for the total operators. The interior case expands through
the accepted inclusion rules with index agreement by `wIdxAboveInterior` and
pure-transport coefficient agreement. At `i = last` both faces are outer-last
(pure transports) and the index equality is direct by `ext`; the face at
`i = 0` is impossible under `j.castSucc < i`. -/
theorem wbar_δ_comp_σ_of_gt (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) :
    wbarσ W F (n + 1) j.castSucc ≫ wbarδ W F (n + 1) i.succ =
      wbarδ W F n i ≫ wbarσ W F n j := by
  have hi0 : i ≠ 0 := by
    intro h0
    subst h0
    have hlt := Fin.lt_def.mp h
    simp at hlt
  have hSucc0 : i.succ ≠ (0 : Fin (n + 3)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp [Fin.val_succ] at hval
  by_cases hiLast : i = Fin.last (n + 1)
  · subst hiLast
    have hSuccLast : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
      apply Fin.ext
      simp [Fin.val_last]
    rw [hSuccLast, wbarδ_last, wbarδ_last]
    change wbarσ W F (n + 1) _ ≫ wbarFaceLast W F (n + 1) =
      wbarFaceLast W F n ≫ wbarσ W F n _
    unfold wbarσ
    refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
    obtain ⟨s, w⟩ := p
    have hchain : SrepBridge.srepDropLast
        ((StrictOmitDup.dupAt j.castSucc).obj s) =
        (StrictOmitDup.dupAt j).obj (SrepBridge.srepDropLast s) := by
      have hL0 := wOmitLastChain ((StrictOmitDup.dupAt j.castSucc).obj s)
      have hR0 := wOmitLastChain s
      have hMid := wChainAbove (n := n) (i := Fin.last (n + 1)) (j := j) h s
      have hLastSucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
        apply Fin.ext
        simp [Fin.val_last]
      rw [hLastSucc] at hMid
      exact hL0.trans (hMid.trans (congrArg _ hR0.symm))
    have eDup : ((StrictOmitDup.dupAt j.castSucc).obj s).right = s.right :=
      wDupInner_obj_last s
    have eRight : ((StrictOmitDup.dupAt j).obj
        (SrepBridge.srepDropLast s)).right =
        (SrepBridge.srepDropLast s).right :=
      wDupInner_obj_last _
    have hp : (j.castSucc).val < n + 1 := j.is_lt
    have hDup := StrictOmitDup.dup_lastArrow (C := J) hp s
    have hIdx : wFaceLastIdx W (n + 1)
        (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩) =
        wDegInnerIdx W n j (wFaceLastIdx W n ⟨s, w⟩) := by
      have hCollapseL : W.map
            (((StrictOmitDup.dupAt j.castSucc).obj s).map' (n + 1) (n + 2)
              (by omega) (by omega)).op
            (W.map (eqToHom eDup).op w) =
            W.map
              ((((StrictOmitDup.dupAt j.castSucc).obj s).map' (n + 1) (n + 2)
                (by omega) (by omega)) ≫ eqToHom eDup).op w :=
        wWeightComp W
          (((StrictOmitDup.dupAt j.castSucc).obj s).map' (n + 1) (n + 2)
            (by omega) (by omega))
          (eqToHom eDup) w
      have hCollapseR : W.map (eqToHom eRight).op
            (W.map (s.map' n (n + 1) (by omega) (by omega)).op w) =
            W.map ((eqToHom eRight ≫ s.map' n (n + 1) (by omega) (by omega))).op
              w :=
        wWeightComp W (eqToHom eRight) (s.map' n (n + 1) (by omega) (by omega)) w
      have hf : (((StrictOmitDup.dupAt j.castSucc).obj s).map' (n + 1) (n + 2)
            (by omega) (by omega)) ≫ eqToHom eDup =
          eqToHom
              (congrArg (fun t : SrepBridge.SrepIdx J (n + 1) => t.right)
                hchain) ≫
            (eqToHom eRight ≫ s.map' n (n + 1) (by omega) (by omega)) := by
        rw [hDup]
        let hCore : s.obj ⟨n, by omega⟩ ⟶ s.obj ⟨n + 1, by omega⟩ :=
          s.map' n (n + 1) (by omega) (by omega)
        have hDropDup : ((eqToHom
              (congrArg s.obj (StrictOmitDup.dupIdx_prev hp)) ≫
              (s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≫
                eqToHom (congrArg s.obj ((StrictOmitDup.dupIdx_top
                  (n := n + 1) (p := j.castSucc)).symm)))) ≫
            eqToHom eDup) ≍
            (eqToHom (congrArg s.obj (StrictOmitDup.dupIdx_prev hp)) ≫
              (s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≫
                eqToHom (congrArg s.obj ((StrictOmitDup.dupIdx_top
                  (n := n + 1) (p := j.castSucc)).symm)))) :=
          CategoryTheory.comp_eqToHom_heq (C := J)
            (f := (eqToHom
              (congrArg s.obj (StrictOmitDup.dupIdx_prev hp)) ≫
              (s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≫
                eqToHom (congrArg s.obj ((StrictOmitDup.dupIdx_top
                  (n := n + 1) (p := j.castSucc)).symm)))))
            (h := eDup)
        have hDropDupLead : (eqToHom
              (congrArg s.obj (StrictOmitDup.dupIdx_prev hp)) ≫
              (s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≫
                eqToHom (congrArg s.obj ((StrictOmitDup.dupIdx_top
                  (n := n + 1) (p := j.castSucc)).symm)))) ≍
            (s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj ((StrictOmitDup.dupIdx_top
                (n := n + 1) (p := j.castSucc)).symm))) :=
          CategoryTheory.eqToHom_comp_heq (C := J)
            (f := (s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj ((StrictOmitDup.dupIdx_top
                (n := n + 1) (p := j.castSucc)).symm))))
            (h := congrArg s.obj (StrictOmitDup.dupIdx_prev hp))
        have hDropDupTrail : (s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj ((StrictOmitDup.dupIdx_top
                (n := n + 1) (p := j.castSucc)).symm))) ≍
            s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) :=
          CategoryTheory.comp_eqToHom_heq (C := J)
            (f := s.map' (n + 1 - 1) (n + 1) (by omega) (by omega))
            (h := congrArg s.obj ((StrictOmitDup.dupIdx_top
              (n := n + 1) (p := j.castSucc)).symm))
        have hBridgeL : s.map' (n + 1 - 1) (n + 1) (by omega) (by omega) ≍
            hCore :=
          by
            dsimp only [hCore]
            simpa only [Nat.add_sub_cancel] using
              (HEq.rfl : s.map' n (n + 1) (by omega) (by omega) ≍
                s.map' n (n + 1) (by omega) (by omega))
        have hSideL := hDropDup.trans
          (hDropDupLead.trans (hDropDupTrail.trans hBridgeL))
        have hDropChain : (eqToHom
              (congrArg (fun t : SrepBridge.SrepIdx J (n + 1) => t.right)
                hchain) ≫
              (eqToHom eRight ≫
                s.map' n (n + 1) (by omega) (by omega))) ≍
            (eqToHom eRight ≫ s.map' n (n + 1) (by omega) (by omega)) :=
          CategoryTheory.eqToHom_comp_heq (C := J)
            (f := (eqToHom eRight ≫ s.map' n (n + 1) (by omega) (by omega)))
            (h := congrArg (fun t : SrepBridge.SrepIdx J (n + 1) => t.right)
              hchain)
        have hDropRight : (eqToHom eRight ≫
            s.map' n (n + 1) (by omega) (by omega)) ≍ hCore :=
          CategoryTheory.eqToHom_comp_heq (C := J)
            (f := s.map' n (n + 1) (by omega) (by omega))
            (h := eRight)
        have hSideR := hDropChain.trans hDropRight
        exact eq_of_heq (hSideL.trans hSideR.symm)
      have hpairL : wFaceLastIdx W (n + 1)
            (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩) =
          (⟨SrepBridge.srepDropLast
              ((StrictOmitDup.dupAt j.castSucc).obj s),
            W.map
              ((((StrictOmitDup.dupAt j.castSucc).obj s).map' (n + 1) (n + 2)
                (by omega) (by omega)) ≫ eqToHom eDup).op w⟩ :
            WIdx J W (n + 1)) := by
        change wFaceLastIdx W (n + 1)
            ⟨(StrictOmitDup.dupAt j.castSucc).obj s,
              W.map (eqToHom eDup).op w⟩ = _
        have hbase : wFaceLastIdx W (n + 1)
              ⟨(StrictOmitDup.dupAt j.castSucc).obj s,
                W.map (eqToHom eDup).op w⟩ =
            ⟨SrepBridge.srepDropLast
                ((StrictOmitDup.dupAt j.castSucc).obj s),
              W.map
                (((StrictOmitDup.dupAt j.castSucc).obj s).map' (n + 1) (n + 2)
                  (by omega) (by omega)).op
                (W.map (eqToHom eDup).op w)⟩ := rfl
        rw [hbase, hCollapseL]
      have hpairR : wDegInnerIdx W n j (wFaceLastIdx W n ⟨s, w⟩) =
          (⟨(StrictOmitDup.dupAt j).obj (SrepBridge.srepDropLast s),
            W.map
              ((eqToHom eRight ≫ s.map' n (n + 1) (by omega) (by omega))).op
              w⟩ : WIdx J W (n + 1)) := by
        have hface : wFaceLastIdx W n (⟨s, w⟩ : WIdx J W (n + 1)) =
            ⟨SrepBridge.srepDropLast s,
              W.map (s.map' n (n + 1) (by omega) (by omega)).op w⟩ := rfl
        have hdeg : wDegInnerIdx W n j
              ⟨SrepBridge.srepDropLast s,
                W.map (s.map' n (n + 1) (by omega) (by omega)).op w⟩ =
            ⟨(StrictOmitDup.dupAt j).obj (SrepBridge.srepDropLast s),
              W.map (eqToHom eRight).op
                (W.map (s.map' n (n + 1) (by omega) (by omega)).op w)⟩ := rfl
        change wDegInnerIdx W n j (wFaceLastIdx W n ⟨s, w⟩) = _
        rw [hface, hdeg, hCollapseR]
      rw [hpairL, hpairR]
      exact wIdxOfChainEqMap W hchain
        ((((StrictOmitDup.dupAt j.castSucc).obj s).map' (n + 1) (n + 2)
          (by omega) (by omega)) ≫ eqToHom eDup)
        (eqToHom eRight ≫ s.map' n (n + 1) (by omega) (by omega)) hf w
    let pDegL : WIdx J W (n + 2) := wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩
    let pFaceL : WIdx J W (n + 1) := wFaceLastIdx W (n + 1) pDegL
    let pFaceR : WIdx J W n := wFaceLastIdx W n ⟨s, w⟩
    let pDegR : WIdx J W (n + 1) := wDegInnerIdx W n j pFaceR
    have hCore : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarDegInner W F (n + 1) j.castSucc ≫ wbarFaceLast W F (n + 1)) =
          wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarFaceLast W F n ≫ wbarDegInner W F n j) := by
          have hL : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              (wbarDegInner W F (n + 1) j.castSucc ≫ wbarFaceLast W F (n + 1)) =
              (wDegInnerComponent F j.castSucc s ≫
                SrepBridge.srepFaceLastComponent F pDegL.1) ≫
                wbarIncl W F (n + 1) pFaceL := by
            calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
                    (wbarDegInner W F (n + 1) j.castSucc ≫ wbarFaceLast W F (n + 1))
                = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫
                    wbarDegInner W F (n + 1) j.castSucc) ≫
                    wbarFaceLast W F (n + 1) := by
                  exact (Category.assoc _ _ _).symm
              _ = (wDegInnerComponent F j.castSucc s ≫
                    wbarIncl W F (n + 2) pDegL) ≫
                    wbarFaceLast W F (n + 1) := by
                exact congrArg (· ≫ wbarFaceLast W F (n + 1))
                  (wbarDegInner_ι W F (n + 1) j.castSucc ⟨s, w⟩)
              _ = wDegInnerComponent F j.castSucc s ≫
                  (wbarIncl W F (n + 2) pDegL ≫ wbarFaceLast W F (n + 1)) := by
                exact Category.assoc _ _ _
              _ = wDegInnerComponent F j.castSucc s ≫
                  (SrepBridge.srepFaceLastComponent F pDegL.1 ≫
                    wbarIncl W F (n + 1) pFaceL) := by
                exact congrArg (wDegInnerComponent F j.castSucc s ≫ ·)
                  (wbarFaceLast_ι W F (n + 1) pDegL)
              _ = _ := by
                exact (Category.assoc (f := wDegInnerComponent F j.castSucc s)
                  (g := SrepBridge.srepFaceLastComponent F pDegL.1)
                  (h := wbarIncl W F (n + 1) pFaceL)).symm
          have hR : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              (wbarFaceLast W F n ≫ wbarDegInner W F n j) =
              (SrepBridge.srepFaceLastComponent F s ≫
                wDegInnerComponent F j pFaceR.1) ≫
                wbarIncl W F (n + 1) pDegR := by
            calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
                    (wbarFaceLast W F n ≫ wbarDegInner W F n j)
                = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫ wbarFaceLast W F n) ≫
                    wbarDegInner W F n j := by
                  exact (Category.assoc _ _ _).symm
              _ = (SrepBridge.srepFaceLastComponent F s ≫
                    wbarIncl W F n pFaceR) ≫
                    wbarDegInner W F n j := by
                exact congrArg (· ≫ wbarDegInner W F n j)
                  (wbarFaceLast_ι W F n ⟨s, w⟩)
              _ = SrepBridge.srepFaceLastComponent F s ≫
                  (wbarIncl W F n pFaceR ≫ wbarDegInner W F n j) := by
                exact Category.assoc _ _ _
              _ = SrepBridge.srepFaceLastComponent F s ≫
                  (wDegInnerComponent F j pFaceR.1 ≫
                    wbarIncl W F (n + 1) pDegR) := by
                exact congrArg (SrepBridge.srepFaceLastComponent F s ≫ ·)
                  (wbarDegInner_ι W F n j pFaceR)
              _ = _ := by
                exact (Category.assoc (f := SrepBridge.srepFaceLastComponent F s)
                  (g := wDegInnerComponent F j pFaceR.1)
                  (h := wbarIncl W F (n + 1) pDegR)).symm
          have hcoeff : (wDegInnerComponent F j.castSucc s ≫
              SrepBridge.srepFaceLastComponent F pDegL.1) =
              (SrepBridge.srepFaceLastComponent F s ≫
                wDegInnerComponent F j pFaceR.1) := by
            have hProjL : pDegL.1 =
                (StrictOmitDup.dupAt j.castSucc).obj s := rfl
            have hProjR : pFaceR.1 =
                SrepBridge.srepDropLast s := rfl
            dsimp only [pDegL, pFaceL, pFaceR, pDegR, wDegInnerIdx, wFaceLastIdx]
            have hDupL : ((StrictOmitDup.dupAt j.castSucc).obj s).left =
                s.left :=
              wDupInner_obj_zero s
            have hDropL : (SrepBridge.srepDropLast
                ((StrictOmitDup.dupAt j.castSucc).obj s)).left =
                ((StrictOmitDup.dupAt j.castSucc).obj s).left :=
              SrepBridge.srepDropLast_left _
            have hDropR : (SrepBridge.srepDropLast s).left = s.left :=
              SrepBridge.srepDropLast_left s
            have hDupR : ((StrictOmitDup.dupAt j).obj
                (SrepBridge.srepDropLast s)).left =
                (SrepBridge.srepDropLast s).left :=
              wDupInner_obj_zero _
            unfold wDegInnerComponent SrepBridge.srepFaceLastComponent
            simp only [eqToHom_trans]
            rfl
          have hcoeffHEq : (wDegInnerComponent F j.castSucc s ≫
              SrepBridge.srepFaceLastComponent F pDegL.1) ≍
              (SrepBridge.srepFaceLastComponent F s ≫
                wDegInnerComponent F j pFaceR.1) :=
            heq_of_eq hcoeff
          calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
                  (wbarDegInner W F (n + 1) j.castSucc ≫ wbarFaceLast W F (n + 1))
              = (wDegInnerComponent F j.castSucc s ≫
                  SrepBridge.srepFaceLastComponent F pDegL.1) ≫
                  wbarIncl W F (n + 1) pFaceL := hL
            _ = (SrepBridge.srepFaceLastComponent F s ≫
                  wDegInnerComponent F j pFaceR.1) ≫
                  wbarIncl W F (n + 1) pDegR :=
                wbarCompEqOfIdxEqHEq W F hIdx hcoeffHEq
            _ = wbarIncl W F (n + 1) ⟨s, w⟩ ≫
                  (wbarFaceLast W F n ≫ wbarDegInner W F n j) := hR.symm
    exact hCore
  · have hSuccLast : i.succ ≠ Fin.last (n + 2) := by
      intro hlast
      have hval := congrArg Fin.val hlast
      simp [Fin.val_last, Fin.val_succ] at hval
      have hi := i.is_lt
      have hjl := Fin.lt_def.mp h
      simp [Fin.val_castSucc] at hjl
      have hne : i.val ≠ n + 1 := by
        intro heq
        apply hiLast
        apply Fin.ext
        simp [Fin.val_last, heq]
      omega
    have hiLastN : i ≠ Fin.last (n + 1) := hiLast
    rw [wbarδ_inner _ _ _ i.succ hSucc0 hSuccLast, wbarδ_inner _ _ _ i hi0 hiLastN]
    change wbarσ W F (n + 1) j.castSucc ≫
        wbarFaceInner W F (n + 1) i.succ hSucc0 hSuccLast =
      wbarFaceInner W F n i hi0 hiLastN ≫ wbarσ W F n j
    unfold wbarσ
    refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
    obtain ⟨s, w⟩ := p
    have hIdx := wIdxAboveInterior W n h hiLastN s w
    let qL : WIdx J W (n + 1) :=
      wFaceInnerIdx W (n + 1) i.succ hSuccLast
        (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩)
    let qR : WIdx J W (n + 1) :=
      wDegInnerIdx W n j (wFaceInnerIdx W n i hiLastN ⟨s, w⟩)
    have hL : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
        (wbarDegInner W F (n + 1) j.castSucc ≫
          wbarFaceInner W F (n + 1) i.succ hSucc0 hSuccLast) =
        (wDegInnerComponent F j.castSucc s ≫
          wFaceInnerComponent F i.succ hSucc0
            ((StrictOmitDup.dupAt j.castSucc).obj s)) ≫
          wbarIncl W F (n + 1) qL := by
      calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              (wbarDegInner W F (n + 1) j.castSucc ≫
                wbarFaceInner W F (n + 1) i.succ hSucc0 hSuccLast)
          = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              wbarDegInner W F (n + 1) j.castSucc) ≫
              wbarFaceInner W F (n + 1) i.succ hSucc0 hSuccLast := by
            exact (Category.assoc _ _ _).symm
        _ = (wDegInnerComponent F j.castSucc s ≫
              wbarIncl W F (n + 2) (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩)) ≫
              wbarFaceInner W F (n + 1) i.succ hSucc0 hSuccLast := by
            exact congrArg (· ≫ _)
              (wbarDegInner_ι W F (n + 1) j.castSucc ⟨s, w⟩)
        _ = wDegInnerComponent F j.castSucc s ≫
              (wbarIncl W F (n + 2) (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩) ≫
                wbarFaceInner W F (n + 1) i.succ hSucc0 hSuccLast) := by
            exact Category.assoc _ _ _
        _ = wDegInnerComponent F j.castSucc s ≫
              (wFaceInnerComponent F i.succ hSucc0
                ((StrictOmitDup.dupAt j.castSucc).obj s) ≫
                wbarIncl W F (n + 1) qL) := by
            exact congrArg (wDegInnerComponent F j.castSucc s ≫ ·)
              (wbarFaceInner_ι W F (n + 1) i.succ hSucc0 hSuccLast
                (wDegInnerIdx W (n + 1) j.castSucc ⟨s, w⟩))
        _ = (wDegInnerComponent F j.castSucc s ≫
              wFaceInnerComponent F i.succ hSucc0
                ((StrictOmitDup.dupAt j.castSucc).obj s)) ≫
              wbarIncl W F (n + 1) qL := by
            exact (Category.assoc _ _ _).symm
    have hR : wbarIncl W F (n + 1) ⟨s, w⟩ ≫
        (wbarFaceInner W F n i hi0 hiLastN ≫ wbarDegInner W F n j) =
        (wFaceInnerComponent F i hi0 s ≫
          wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) ≫
          wbarIncl W F (n + 1) qR := by
      calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              (wbarFaceInner W F n i hi0 hiLastN ≫ wbarDegInner W F n j)
          = (wbarIncl W F (n + 1) ⟨s, w⟩ ≫
              wbarFaceInner W F n i hi0 hiLastN) ≫
              wbarDegInner W F n j := by
            exact (Category.assoc _ _ _).symm
        _ = (wFaceInnerComponent F i hi0 s ≫
              wbarIncl W F n (wFaceInnerIdx W n i hiLastN ⟨s, w⟩)) ≫
              wbarDegInner W F n j := by
            exact congrArg (· ≫ _) (wbarFaceInner_ι W F n i hi0 hiLastN ⟨s, w⟩)
        _ = wFaceInnerComponent F i hi0 s ≫
              (wbarIncl W F n (wFaceInnerIdx W n i hiLastN ⟨s, w⟩) ≫
                wbarDegInner W F n j) := by
            exact Category.assoc _ _ _
        _ = wFaceInnerComponent F i hi0 s ≫
              (wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s) ≫
                wbarIncl W F (n + 1) qR) := by
            exact congrArg (wFaceInnerComponent F i hi0 s ≫ ·)
              (wbarDegInner_ι W F n j
                (wFaceInnerIdx W n i hiLastN ⟨s, w⟩))
        _ = (wFaceInnerComponent F i hi0 s ≫
              wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) ≫
              wbarIncl W F (n + 1) qR := by
            exact (Category.assoc _ _ _).symm
    have hcoeffHEq : (wDegInnerComponent F j.castSucc s ≫
        wFaceInnerComponent F i.succ hSucc0
          ((StrictOmitDup.dupAt j.castSucc).obj s)) ≍
        (wFaceInnerComponent F i hi0 s ≫
          wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) := by
      unfold wDegInnerComponent wFaceInnerComponent
      simp only [eqToHom_trans]
      exact (CategoryTheory.eqToHom_heq_id_dom _ _ _).trans
        (CategoryTheory.eqToHom_heq_id_dom _ _ _).symm
    calc wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarDegInner W F (n + 1) j.castSucc ≫
              wbarFaceInner W F (n + 1) i.succ hSucc0 hSuccLast)
        = (wDegInnerComponent F j.castSucc s ≫
            wFaceInnerComponent F i.succ hSucc0
              ((StrictOmitDup.dupAt j.castSucc).obj s)) ≫
            wbarIncl W F (n + 1) qL := hL
      _ = (wFaceInnerComponent F i hi0 s ≫
            wDegInnerComponent F j ((StrictOmitDup.omitAt i).obj s)) ≫
            wbarIncl W F (n + 1) qR :=
          wbarCompEqOfIdxEqHEq W F hIdx hcoeffHEq
      _ = wbarIncl W F (n + 1) ⟨s, w⟩ ≫
            (wbarFaceInner W F n i hi0 hiLastN ≫ wbarDegInner W F n j) := hR.symm

/-- Internal: `WIdx` equality for iterated interior faces. Chain part is
`wChainOmitOmit`; weight transports fuse on each side. Only the last-index
side conditions are needed here; the zero conditions enter through the
`wbarδ_inner` rewrites at the caller. -/
private theorem wIdxOmitOmitInterior (n : ℕ) {i j : Fin (n + 2)} (h : i ≤ j)
    (hiLast : i ≠ Fin.last (n + 1)) (hjLast : j ≠ Fin.last (n + 1))
    (hJSuccLast : j.succ ≠ Fin.last (n + 2))
    (hICastLast : i.castSucc ≠ Fin.last (n + 2))
    (s : SrepBridge.SrepIdx J (n + 2)) (w : W.obj (Opposite.op s.right)) :
    wFaceInnerIdx W n i hiLast
        (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩) =
      wFaceInnerIdx W n j hjLast
        (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩) := by
  have hchain := wChainOmitOmit (n := n) h s
  have eFirstL : ((StrictOmitDup.omitAt j.succ).obj s).right = s.right :=
    wOmitInner_obj_last hJSuccLast s
  have eFirstR : ((StrictOmitDup.omitAt i.castSucc).obj s).right = s.right :=
    wOmitInner_obj_last hICastLast s
  have eLeft : ((StrictOmitDup.omitAt i).obj
      ((StrictOmitDup.omitAt j.succ).obj s)).right =
      ((StrictOmitDup.omitAt j.succ).obj s).right :=
    wOmitInner_obj_last hiLast _
  have eRight : ((StrictOmitDup.omitAt j).obj
      ((StrictOmitDup.omitAt i.castSucc).obj s)).right =
      ((StrictOmitDup.omitAt i.castSucc).obj s).right :=
    wOmitInner_obj_last hjLast _
  have fuseL := wWeightFuse W eLeft eFirstL w
  have fuseR := wWeightFuse W eRight eFirstR w
  have hL : wFaceInnerIdx W n i hiLast
      (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩) =
      (⟨(StrictOmitDup.omitAt i).obj
        ((StrictOmitDup.omitAt j.succ).obj s),
        W.map (eqToHom (eLeft.trans eFirstL)).op w⟩ : WIdx J W n) := by
    have hpair : wFaceInnerIdx W n i hiLast
        ⟨(StrictOmitDup.omitAt j.succ).obj s,
          W.map (eqToHom eFirstL).op w⟩ =
        ⟨(StrictOmitDup.omitAt i).obj
          ((StrictOmitDup.omitAt j.succ).obj s),
          W.map (eqToHom eLeft).op (W.map (eqToHom eFirstL).op w)⟩ := rfl
    change wFaceInnerIdx W n i hiLast
        (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩) = _
    have hface : wFaceInnerIdx W (n + 1) j.succ hJSuccLast (⟨s, w⟩ :
        WIdx J W (n + 2)) =
        ⟨(StrictOmitDup.omitAt j.succ).obj s,
          W.map (eqToHom eFirstL).op w⟩ := rfl
    rw [hface, hpair, fuseL]
  have hR : wFaceInnerIdx W n j hjLast
      (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩) =
      (⟨(StrictOmitDup.omitAt j).obj
        ((StrictOmitDup.omitAt i.castSucc).obj s),
        W.map (eqToHom (eRight.trans eFirstR)).op w⟩ : WIdx J W n) := by
    have hpair : wFaceInnerIdx W n j hjLast
        ⟨(StrictOmitDup.omitAt i.castSucc).obj s,
          W.map (eqToHom eFirstR).op w⟩ =
        ⟨(StrictOmitDup.omitAt j).obj
          ((StrictOmitDup.omitAt i.castSucc).obj s),
          W.map (eqToHom eRight).op (W.map (eqToHom eFirstR).op w)⟩ := rfl
    change wFaceInnerIdx W n j hjLast
        (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩) = _
    have hface : wFaceInnerIdx W (n + 1) i.castSucc hICastLast (⟨s, w⟩ :
        WIdx J W (n + 2)) =
        ⟨(StrictOmitDup.omitAt i.castSucc).obj s,
          W.map (eqToHom eFirstR).op w⟩ := rfl
    rw [hface, hpair, fuseR]
  rw [hL, hR]
  exact wIdxOfChainEq W hchain (eLeft.trans eFirstL) (eRight.trans eFirstR) w

/-- Interior-interior `δδ`: when all four faces are interior, iterated
omissions commute. Coefficients are pure transports, so the bridge fuses by
proof irrelevance after the `eqToHom_trans` normalization. -/
private theorem wbar_δ_comp_δ_interior (n : ℕ) {i j : Fin (n + 2)} (h : i ≤ j)
    (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    (hj0 : j ≠ 0) (hjLast : j ≠ Fin.last (n + 1)) :
    wbarδ W F (n + 1) j.succ ≫ wbarδ W F n i =
      wbarδ W F (n + 1) i.castSucc ≫ wbarδ W F n j := by
  have hJSucc0 : j.succ ≠ (0 : Fin (n + 3)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp [Fin.val_succ] at hval
  have hJSuccLast : j.succ ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last, Fin.val_succ] at hval
    have hjNe : j.val ≠ n + 1 := by
      intro heq
      apply hjLast
      apply Fin.ext
      simp [Fin.val_last, heq]
    omega
  have hICast0 : i.castSucc ≠ (0 : Fin (n + 3)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Fin.val_eq_zero_iff] at hval
    exact hi0 (Fin.ext (by simpa using hval))
  have hICastLast : i.castSucc ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last, Fin.val_castSucc] at hval
    have hi := i.is_lt
    omega
  rw [wbarδ_inner _ _ _ j.succ hJSucc0 hJSuccLast, wbarδ_inner _ _ _ i hi0 hiLast,
    wbarδ_inner _ _ _ i.castSucc hICast0 hICastLast, wbarδ_inner _ _ _ j hj0 hjLast]
  change wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
      wbarFaceInner W F n i hi0 hiLast =
    wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast ≫
      wbarFaceInner W F n j hj0 hjLast
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 2) => ?_)
  obtain ⟨s, w⟩ := p
  have hIdx := wIdxOmitOmitInterior (W := W) (n := n) h hiLast hjLast
    hJSuccLast hICastLast s w
  let qL : WIdx J W n :=
    wFaceInnerIdx W n i hiLast
      (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩)
  let qR : WIdx J W n :=
    wFaceInnerIdx W n j hjLast
      (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩)
  have hL : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
        wbarFaceInner W F n i hi0 hiLast) =
      (wFaceInnerComponent F j.succ hJSucc0 s ≫
        wFaceInnerComponent F i hi0
          ((StrictOmitDup.omitAt j.succ).obj s)) ≫
        wbarIncl W F n qL := by
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
              wbarFaceInner W F n i hi0 hiLast)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast) ≫
            wbarFaceInner W F n i hi0 hiLast := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F j.succ hJSucc0 s ≫
            wbarIncl W F (n + 1)
              (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩)) ≫
            wbarFaceInner W F n i hi0 hiLast := by
          exact congrArg (· ≫ _)
            (wbarFaceInner_ι W F (n + 1) j.succ hJSucc0 hJSuccLast ⟨s, w⟩)
      _ = wFaceInnerComponent F j.succ hJSucc0 s ≫
            (wbarIncl W F (n + 1)
              (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩) ≫
              wbarFaceInner W F n i hi0 hiLast) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F j.succ hJSucc0 s ≫
            (wFaceInnerComponent F i hi0
              ((StrictOmitDup.omitAt j.succ).obj s) ≫ wbarIncl W F n qL) := by
          exact congrArg (wFaceInnerComponent F j.succ hJSucc0 s ≫ ·)
            (wbarFaceInner_ι W F n i hi0 hiLast
              (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩))
      _ = (wFaceInnerComponent F j.succ hJSucc0 s ≫
            wFaceInnerComponent F i hi0
              ((StrictOmitDup.omitAt j.succ).obj s)) ≫
            wbarIncl W F n qL := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast ≫
        wbarFaceInner W F n j hj0 hjLast) =
      (wFaceInnerComponent F i.castSucc hICast0 s ≫
        wFaceInnerComponent F j hj0
          ((StrictOmitDup.omitAt i.castSucc).obj s)) ≫
        wbarIncl W F n qR := by
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast ≫
              wbarFaceInner W F n j hj0 hjLast)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast) ≫
            wbarFaceInner W F n j hj0 hjLast := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F i.castSucc hICast0 s ≫
            wbarIncl W F (n + 1)
              (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩)) ≫
            wbarFaceInner W F n j hj0 hjLast := by
          exact congrArg (· ≫ _)
            (wbarFaceInner_ι W F (n + 1) i.castSucc hICast0 hICastLast ⟨s, w⟩)
      _ = wFaceInnerComponent F i.castSucc hICast0 s ≫
            (wbarIncl W F (n + 1)
              (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩) ≫
              wbarFaceInner W F n j hj0 hjLast) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F i.castSucc hICast0 s ≫
            (wFaceInnerComponent F j hj0
              ((StrictOmitDup.omitAt i.castSucc).obj s) ≫ wbarIncl W F n qR) := by
          exact congrArg (wFaceInnerComponent F i.castSucc hICast0 s ≫ ·)
            (wbarFaceInner_ι W F n j hj0 hjLast
              (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩))
      _ = (wFaceInnerComponent F i.castSucc hICast0 s ≫
            wFaceInnerComponent F j hj0
              ((StrictOmitDup.omitAt i.castSucc).obj s)) ≫
            wbarIncl W F n qR := by
          exact (Category.assoc _ _ _).symm
  have hcoeffHEq : (wFaceInnerComponent F j.succ hJSucc0 s ≫
      wFaceInnerComponent F i hi0
        ((StrictOmitDup.omitAt j.succ).obj s)) ≍
      (wFaceInnerComponent F i.castSucc hICast0 s ≫
        wFaceInnerComponent F j hj0
          ((StrictOmitDup.omitAt i.castSucc).obj s)) := by
    unfold wFaceInnerComponent
    simp only [eqToHom_trans]
    exact (CategoryTheory.eqToHom_heq_id_dom _ _ _).trans
      (CategoryTheory.eqToHom_heq_id_dom _ _ _).symm
  calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
            wbarFaceInner W F n i hi0 hiLast)
      = (wFaceInnerComponent F j.succ hJSucc0 s ≫
          wFaceInnerComponent F i hi0
            ((StrictOmitDup.omitAt j.succ).obj s)) ≫
          wbarIncl W F n qL := hL
    _ = (wFaceInnerComponent F i.castSucc hICast0 s ≫
          wFaceInnerComponent F j hj0
            ((StrictOmitDup.omitAt i.castSucc).obj s)) ≫
          wbarIncl W F n qR :=
        wbarCompEqOfIdxEqHEq W F hIdx hcoeffHEq
    _ = wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast ≫
            wbarFaceInner W F n j hj0 hjLast) := hR.symm

/-- Endpoint `δδ` with `i = 0` and `j = last`: dropping the last entry then
the first agrees with dropping the first then the last. Both rewrites land on
outer faces, so the accepted outer interchange applies directly. -/
private theorem wbar_δ_comp_δ_zero_last (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 2)}
    (hi : i = 0) (hj : j = Fin.last (n + 1)) :
    wbarδ W F (n + 1) j.succ ≫ wbarδ W F n i =
      wbarδ W F (n + 1) i.castSucc ≫ wbarδ W F n j := by
  subst hi
  subst hj
  have hJSuccLast : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
    apply Fin.ext
    simp [Fin.val_last]
  have hICast0 : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
    apply Fin.ext
    simp
  rw [hJSuccLast, wbarδ_last, wbarδ_zero, hICast0, wbarδ_zero, wbarδ_last]
  exact (wbarFaceZero_faceLast_interchange W F n).symm

/-- Interior-last `δδ`: the face at `i` is interior and `j = last`, so the
first face on the left is outer-last while the remaining three are interior
except the final outer-last. Coefficients are pure transports on both sides.
The chain commutation is direct by `ComposableArrows.ext`: at the index level
it is `castSucc` against `succAbove` strictly below the omitted position.
The weight-arrow agreement is the accepted `omit_lastArrow` preservation,
lifted through `Sigma.ext` as in `wDegZero_faceLast_idx`. -/
private theorem wbar_δ_comp_δ_interior_last (n : ℕ) {i : Fin (n + 2)}
    (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1)) :
    wbarδ W F (n + 1) (Fin.last (n + 1)).succ ≫ wbarδ W F n i =
      wbarδ W F (n + 1) i.castSucc ≫ wbarδ W F n (Fin.last (n + 1)) := by
  have hLastSucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
    apply Fin.ext
    simp [Fin.val_last]
  have hICast0 : i.castSucc ≠ (0 : Fin (n + 3)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Fin.val_eq_zero_iff] at hval
    exact hi0 (Fin.ext (by simpa using hval))
  have hICastLast : i.castSucc ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last, Fin.val_castSucc] at hval
    have hi := i.is_lt
    omega
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 2) => ?_)
  obtain ⟨s, w⟩ := p
  have hiVal : i.val ≤ n := by
    have hi := i.is_lt
    have hne : i.val ≠ n + 1 := by
      intro heq
      apply hiLast
      apply Fin.ext
      simp [Fin.val_last, heq]
    omega
  have hchain : (StrictOmitDup.omitAt (C := J) i).obj
      (SrepBridge.srepDropLast s) =
      SrepBridge.srepDropLast
        ((StrictOmitDup.omitAt (C := J) i.castSucc).obj s) := by
    have hL0 := wOmitLastChain s
    have hR0 := wOmitLastChain ((StrictOmitDup.omitAt (C := J) i.castSucc).obj s)
    have hle : i ≤ Fin.last (n + 1) := by
      rw [Fin.le_iff_val_le_val]
      simp [Fin.val_last]
      omega
    have hMid := wChainOmitOmit (n := n) (i := i)
      (j := Fin.last (n + 1)) hle s
    have hLastSucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
      apply Fin.ext
      simp [Fin.val_last]
    rw [hLastSucc] at hMid
    have hLeftEq : (StrictOmitDup.omitAt (C := J) i).obj
        (SrepBridge.srepDropLast s) =
        (StrictOmitDup.omitAt (C := J) i).obj
          ((StrictOmitDup.omitAt (C := J) (Fin.last (n + 2))).obj s) := by
      exact congrArg _ hL0
    exact hLeftEq.trans (hMid.trans hR0.symm)
  have hp : (i.castSucc).val + 1 ≤ n + 1 := by
    simp [Fin.val_castSucc]
    omega
  have e0 := StrictOmitDup.omitIdx_shift_lo (n := n + 1) (p := i.castSucc) hp
  have e1 := StrictOmitDup.omitIdx_shift_top (n := n + 1) (p := i.castSucc) hp
  have harr : ((StrictOmitDup.omitAt (C := J) i.castSucc).obj s).map' n (n + 1)
        (by omega) (by omega) =
        eqToHom (congrArg s.obj e0) ≫ s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
          eqToHom (congrArg s.obj e1.symm) := by
    have harr0 := StrictOmitDup.omit_lastArrow (n := n + 1) hp s
    simp only [StrictOmitDup.omitAt_obj] at harr0
    exact harr0
  have hIdx : wFaceInnerIdx W n i hiLast (wFaceLastIdx W (n + 1) ⟨s, w⟩) =
      wFaceLastIdx W n
        (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩) := by
    have eFirst : ((StrictOmitDup.omitAt i.castSucc).obj s).right = s.right :=
      wOmitInner_obj_last hICastLast s
    have eLeft : ((StrictOmitDup.omitAt i).obj
        (SrepBridge.srepDropLast s)).right =
        (SrepBridge.srepDropLast s).right :=
      wOmitInner_obj_last hiLast _
    let fL : ((StrictOmitDup.omitAt (C := J) i).obj
        (SrepBridge.srepDropLast s)).right ⟶ s.right :=
      eqToHom eLeft ≫ s.map' (n + 1) (n + 2) (by omega) (by omega)
    let fR : (SrepBridge.srepDropLast
        ((StrictOmitDup.omitAt (C := J) i.castSucc).obj s)).right ⟶ s.right :=
      ((StrictOmitDup.omitAt (C := J) i.castSucc).obj s).map' n (n + 1)
        (by omega) (by omega) ≫ eqToHom eFirst
    have hf : fL =
        eqToHom
            (congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain) ≫
          fR := by
      have hFR_fold : fR =
            (((StrictOmitDup.omitAt (C := J) i.castSucc).obj s).map' n (n + 1)
              (by omega) (by omega) ≫ eqToHom eFirst) := rfl
      have hFL_fold : fL =
            (eqToHom eLeft ≫ s.map' (n + 1) (n + 2) (by omega) (by omega)) := rfl
      have hStep : (((StrictOmitDup.omitAt (C := J) i.castSucc).obj s).map' n (n + 1)
              (by omega) (by omega) ≫ eqToHom eFirst) =
            ((eqToHom (congrArg s.obj e0) ≫ s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm)) ≫ eqToHom eFirst) :=
        congrArg (· ≫ eqToHom eFirst) harr
      have hFR_harr : fR =
            ((eqToHom (congrArg s.obj e0) ≫ s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm)) ≫ eqToHom eFirst) :=
        hFR_fold.trans hStep
      have hSideL : fL ≍ s.map' (n + 1) (n + 2) (by omega) (by omega) :=
        (heq_of_eq hFL_fold).trans
          (CategoryTheory.eqToHom_comp_heq (C := J)
            (f := s.map' (n + 1) (n + 2) (by omega) (by omega)) (h := eLeft))
      have hDropChain : (eqToHom
            (congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain) ≫ fR) ≍ fR :=
        CategoryTheory.eqToHom_comp_heq (C := J) (f := fR)
          (h := congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain)
      have hDropFirst : fR ≍ ((eqToHom (congrArg s.obj e0) ≫
            s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm)) ≫ eqToHom eFirst) :=
        heq_of_eq hFR_harr
      have hDropTrail : (((eqToHom (congrArg s.obj e0) ≫
            s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm)) ≫ eqToHom eFirst)) ≍
            ((eqToHom (congrArg s.obj e0) ≫
              s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
                eqToHom (congrArg s.obj e1.symm))) :=
        CategoryTheory.comp_eqToHom_heq (C := J)
          (f := (eqToHom (congrArg s.obj e0) ≫
            s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm))) (h := eFirst)
      have hDropLead : ((eqToHom (congrArg s.obj e0) ≫
            s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm))) ≍
            ((s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm))) :=
        CategoryTheory.eqToHom_comp_heq (C := J)
          (f := (s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
            eqToHom (congrArg s.obj e1.symm)))
          (h := congrArg s.obj e0)
      have hDropLast : ((s.map' (n + 1) (n + 2) (by omega) (by omega) ≫
            eqToHom (congrArg s.obj e1.symm))) ≍
          s.map' (n + 1) (n + 2) (by omega) (by omega) :=
        CategoryTheory.comp_eqToHom_heq (C := J)
          (f := s.map' (n + 1) (n + 2) (by omega) (by omega))
          (h := congrArg s.obj e1.symm)
      have hSideR : (eqToHom
            (congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain) ≫ fR) ≍
          s.map' (n + 1) (n + 2) (by omega) (by omega) :=
        hDropChain.trans
          (hDropFirst.trans (hDropTrail.trans (hDropLead.trans hDropLast)))
      exact eq_of_heq (hSideL.trans hSideR.symm)
    have hCollapseL : W.map (eqToHom eLeft).op
          (W.map (s.map' (n + 1) (n + 2) (by omega) (by omega)).op w) =
          W.map fL.op w :=
      wWeightComp W (eqToHom eLeft) (s.map' (n + 1) (n + 2) (by omega) (by omega))
        w
    have hCollapseR : W.map
            (((StrictOmitDup.omitAt (C := J) i.castSucc).obj s).map' n (n + 1)
              (by omega) (by omega)).op
            (W.map (eqToHom eFirst).op w) =
          W.map fR.op w :=
      wWeightComp W
        (((StrictOmitDup.omitAt (C := J) i.castSucc).obj s).map' n (n + 1)
          (by omega) (by omega))
        (eqToHom eFirst) w
    have hpairL : wFaceInnerIdx W n i hiLast (wFaceLastIdx W (n + 1) ⟨s, w⟩) =
          (⟨(StrictOmitDup.omitAt i).obj (SrepBridge.srepDropLast s),
            W.map fL.op w⟩ : WIdx J W n) := by
      change (⟨(StrictOmitDup.omitAt i).obj (SrepBridge.srepDropLast s),
          W.map (eqToHom eLeft).op
            (W.map (s.map' (n + 1) (n + 2)).op w)⟩ : WIdx J W n) = _
      rw [hCollapseL]
    have hpairR : wFaceLastIdx W n
          (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩) =
          (⟨SrepBridge.srepDropLast
            ((StrictOmitDup.omitAt i.castSucc).obj s),
            W.map fR.op w⟩ : WIdx J W n) := by
      change (⟨SrepBridge.srepDropLast
          ((StrictOmitDup.omitAt i.castSucc).obj s),
          W.map (((StrictOmitDup.omitAt i.castSucc).obj s).map' n (n + 1)).op
            (W.map (eqToHom eFirst).op w)⟩ : WIdx J W n) = _
      rw [hCollapseR]
    rw [hpairL, hpairR]
    exact wIdxOfChainEqMap W hchain fL fR hf w
  let qL : WIdx J W n :=
    wFaceInnerIdx W n i hiLast (wFaceLastIdx W (n + 1) ⟨s, w⟩)
  let qR : WIdx J W n :=
    wFaceLastIdx W n (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩)
  have hL : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceLast W F (n + 1) ≫ wbarFaceInner W F n i hi0 hiLast) =
      (SrepBridge.srepFaceLastComponent F s ≫
        wFaceInnerComponent F i hi0 (SrepBridge.srepDropLast s)) ≫
        wbarIncl W F n qL := by
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceLast W F (n + 1) ≫ wbarFaceInner W F n i hi0 hiLast)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫ wbarFaceLast W F (n + 1)) ≫
            wbarFaceInner W F n i hi0 hiLast := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceLastComponent F s ≫
            wbarIncl W F (n + 1) (wFaceLastIdx W (n + 1) ⟨s, w⟩)) ≫
            wbarFaceInner W F n i hi0 hiLast := by
          exact congrArg (· ≫ _) (wbarFaceLast_ι W F (n + 1) ⟨s, w⟩)
      _ = SrepBridge.srepFaceLastComponent F s ≫
            (wbarIncl W F (n + 1) (wFaceLastIdx W (n + 1) ⟨s, w⟩) ≫
              wbarFaceInner W F n i hi0 hiLast) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent F s ≫
            (wFaceInnerComponent F i hi0 _ ≫ wbarIncl W F n qL) := by
          exact congrArg (SrepBridge.srepFaceLastComponent F s ≫ ·)
            (wbarFaceInner_ι W F n i hi0 hiLast (wFaceLastIdx W (n + 1) ⟨s, w⟩))
      _ = (SrepBridge.srepFaceLastComponent F s ≫
            wFaceInnerComponent F i hi0 (SrepBridge.srepDropLast s)) ≫
            wbarIncl W F n qL := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast ≫
        wbarFaceLast W F n) =
      (wFaceInnerComponent F i.castSucc hICast0 s ≫
        SrepBridge.srepFaceLastComponent F
          ((StrictOmitDup.omitAt i.castSucc).obj s)) ≫
        wbarIncl W F n qR := by
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast ≫
              wbarFaceLast W F n)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast) ≫
            wbarFaceLast W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F i.castSucc hICast0 s ≫
            wbarIncl W F (n + 1)
              (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩)) ≫
            wbarFaceLast W F n := by
          exact congrArg (· ≫ _)
            (wbarFaceInner_ι W F (n + 1) i.castSucc hICast0 hICastLast ⟨s, w⟩)
      _ = wFaceInnerComponent F i.castSucc hICast0 s ≫
            (wbarIncl W F (n + 1)
              (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩) ≫
              wbarFaceLast W F n) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F i.castSucc hICast0 s ≫
            (SrepBridge.srepFaceLastComponent F _ ≫ wbarIncl W F n qR) := by
          exact congrArg (wFaceInnerComponent F i.castSucc hICast0 s ≫ ·)
            (wbarFaceLast_ι W F n
              (wFaceInnerIdx W (n + 1) i.castSucc hICastLast ⟨s, w⟩))
      _ = (wFaceInnerComponent F i.castSucc hICast0 s ≫
            SrepBridge.srepFaceLastComponent F
              ((StrictOmitDup.omitAt i.castSucc).obj s)) ≫
            wbarIncl W F n qR := by
          exact (Category.assoc _ _ _).symm
  have hcoeffHEq : (SrepBridge.srepFaceLastComponent F s ≫
      wFaceInnerComponent F i hi0 (SrepBridge.srepDropLast s)) ≍
      (wFaceInnerComponent F i.castSucc hICast0 s ≫
        SrepBridge.srepFaceLastComponent F
          ((StrictOmitDup.omitAt i.castSucc).obj s)) := by
    unfold SrepBridge.srepFaceLastComponent wFaceInnerComponent
    simp only [eqToHom_trans]
    exact (CategoryTheory.eqToHom_heq_id_dom _ _ _).trans
      (CategoryTheory.eqToHom_heq_id_dom _ _ _).symm
  calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarδ W F (n + 1) (Fin.last (n + 1)).succ ≫ wbarδ W F n i)
      = wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceLast W F (n + 1) ≫
            wbarFaceInner W F n i hi0 hiLast) := by
        rw [hLastSucc, wbarδ_last, wbarδ_inner _ _ _ i hi0 hiLast]
    _ = (SrepBridge.srepFaceLastComponent F s ≫
          wFaceInnerComponent F i hi0 (SrepBridge.srepDropLast s)) ≫
          wbarIncl W F n qL := hL
    _ = (wFaceInnerComponent F i.castSucc hICast0 s ≫
          SrepBridge.srepFaceLastComponent F
            ((StrictOmitDup.omitAt i.castSucc).obj s)) ≫
          wbarIncl W F n qR :=
        wbarCompEqOfIdxEqHEq W F hIdx hcoeffHEq
    _ = wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceInner W F (n + 1) i.castSucc hICast0 hICastLast ≫
            wbarFaceLast W F n) := hR.symm
    _ = wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarδ W F (n + 1) i.castSucc ≫ wbarδ W F n (Fin.last (n + 1))) := by
        rw [wbarδ_inner _ _ _ i.castSucc hICast0 hICastLast, wbarδ_last]

/-- Zero-interior `δδ`: with `i = 0` and `j` interior, the left pair is
interior-then-`d₀` and the right pair is `d₀`-then-interior. The chain
commutation is direct by `ComposableArrows.ext` (dropping the first entry
after an interior omission agrees with omitting after dropping the first).
Coefficients fuse the single `F.map` action across the pure transports via
the accepted `omit_firstArrow` preservation, exactly as in the `δσ`
below-case at `i = 0`. -/
private theorem wbar_δ_comp_δ_zero_interior (n : ℕ) {j : Fin (n + 2)}
    (hj0 : j ≠ 0) (hjLast : j ≠ Fin.last (n + 1)) :
    wbarδ W F (n + 1) j.succ ≫ wbarδ W F n 0 =
      wbarδ W F (n + 1) (0 : Fin (n + 2)).castSucc ≫ wbarδ W F n j := by
  have hJSucc0 : j.succ ≠ (0 : Fin (n + 3)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp [Fin.val_succ] at hval
  have hJSuccLast : j.succ ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last, Fin.val_succ] at hval
    have hjNe : j.val ≠ n + 1 := by
      intro heq
      apply hjLast
      apply Fin.ext
      simp [Fin.val_last, heq]
    omega
  have h0Cast : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
    apply Fin.ext
    simp
  rw [wbarδ_inner _ _ _ j.succ hJSucc0 hJSuccLast, wbarδ_zero,
    h0Cast, wbarδ_zero, wbarδ_inner _ _ _ j hj0 hjLast]
  change wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
      wbarFaceZero W F n =
    wbarFaceZero W F (n + 1) ≫ wbarFaceInner W F n j hj0 hjLast
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 2) => ?_)
  obtain ⟨s, w⟩ := p
  have hchain : SrepBridge.srepDropFirst
      ((StrictOmitDup.omitAt (C := J) j.succ).obj s) =
      (StrictOmitDup.omitAt (C := J) j).obj
        (SrepBridge.srepDropFirst s) := by
    have hL0 := wOmitZeroChain ((StrictOmitDup.omitAt (C := J) j.succ).obj s)
    have hR0 := wOmitZeroChain s
    have hMid := wChainOmitOmit (n := n) (i := (0 : Fin (n + 2))) (j := j)
      (Fin.zero_le _) s
    have h0eq : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    rw [h0eq] at hMid
    have hLeftEq : SrepBridge.srepDropFirst
        ((StrictOmitDup.omitAt (C := J) j.succ).obj s) =
        (StrictOmitDup.omitAt (C := J) (0 : Fin (n + 2))).obj
          ((StrictOmitDup.omitAt (C := J) j.succ).obj s) := hL0
    have hRightEq : (StrictOmitDup.omitAt (C := J) j).obj
        (SrepBridge.srepDropFirst s) =
        (StrictOmitDup.omitAt (C := J) j).obj
          ((StrictOmitDup.omitAt (C := J) (0 : Fin (n + 3))).obj s) := by
      exact congrArg _ hR0
    rw [hLeftEq, hRightEq]
    exact hMid
  have eOmit : ((StrictOmitDup.omitAt j.succ).obj s).right = s.right :=
    wOmitInner_obj_last hJSuccLast s
  have eRight : ((StrictOmitDup.omitAt j).obj
      (SrepBridge.srepDropFirst s)).right =
      (SrepBridge.srepDropFirst s).right :=
    wOmitInner_obj_last hjLast _
  have hIdx : wFaceZeroIdx W n
      (wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩) =
      wFaceInnerIdx W n j hjLast (wFaceZeroIdx W (n + 1) ⟨s, w⟩) := by
    change (⟨SrepBridge.srepDropFirst
        ((StrictOmitDup.omitAt j.succ).obj s),
        W.map (eqToHom eOmit).op w⟩ : WIdx J W n) =
      ⟨(StrictOmitDup.omitAt j).obj (SrepBridge.srepDropFirst s),
        W.map (eqToHom eRight).op w⟩
    exact wIdxOfChainEq W hchain eOmit eRight w
  let qMidL : WIdx J W (n + 1) :=
    wFaceInnerIdx W (n + 1) j.succ hJSuccLast ⟨s, w⟩
  let qL : WIdx J W n := wFaceZeroIdx W n qMidL
  have hL : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
        wbarFaceZero W F n) =
      (wFaceInnerComponent F j.succ hJSucc0 s ≫
        SrepBridge.srepFaceZeroComponent F
          ((StrictOmitDup.omitAt j.succ).obj s)) ≫
        wbarIncl W F n qL := by
    have hZeroMid := wbarFaceZero_ι W F n qMidL
    change wbarIncl W F (n + 1) qMidL ≫ wbarFaceZero W F n =
        SrepBridge.srepFaceZeroComponent F
          ((StrictOmitDup.omitAt j.succ).obj s) ≫
          wbarIncl W F n qL at hZeroMid
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
              wbarFaceZero W F n)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast) ≫
            wbarFaceZero W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F j.succ hJSucc0 s ≫
            wbarIncl W F (n + 1) qMidL) ≫
            wbarFaceZero W F n := by
          exact congrArg (· ≫ _)
            (wbarFaceInner_ι W F (n + 1) j.succ hJSucc0 hJSuccLast ⟨s, w⟩)
      _ = wFaceInnerComponent F j.succ hJSucc0 s ≫
            (wbarIncl W F (n + 1) qMidL ≫
              wbarFaceZero W F n) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F j.succ hJSucc0 s ≫
            (SrepBridge.srepFaceZeroComponent F
              ((StrictOmitDup.omitAt j.succ).obj s) ≫ wbarIncl W F n qL) := by
          exact congrArg (wFaceInnerComponent F j.succ hJSucc0 s ≫ ·) hZeroMid
      _ = (wFaceInnerComponent F j.succ hJSucc0 s ≫
            SrepBridge.srepFaceZeroComponent F
              ((StrictOmitDup.omitAt j.succ).obj s)) ≫
            wbarIncl W F n qL := by
          exact (Category.assoc _ _ _).symm
  let qMidR : WIdx J W (n + 1) := wFaceZeroIdx W (n + 1) ⟨s, w⟩
  let qR : WIdx J W n := wFaceInnerIdx W n j hjLast qMidR
  have hR : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceZero W F (n + 1) ≫ wbarFaceInner W F n j hj0 hjLast) =
      (SrepBridge.srepFaceZeroComponent F s ≫
        wFaceInnerComponent F j hj0 (SrepBridge.srepDropFirst s)) ≫
        wbarIncl W F n qR := by
    have hInnerMid := wbarFaceInner_ι W F n j hj0 hjLast qMidR
    change wbarIncl W F (n + 1) qMidR ≫ wbarFaceInner W F n j hj0 hjLast =
        wFaceInnerComponent F j hj0 (SrepBridge.srepDropFirst s) ≫
          wbarIncl W F n qR at hInnerMid
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceZero W F (n + 1) ≫
              wbarFaceInner W F n j hj0 hjLast)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫ wbarFaceZero W F (n + 1)) ≫
            wbarFaceInner W F n j hj0 hjLast := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceZeroComponent F s ≫
            wbarIncl W F (n + 1) qMidR) ≫
            wbarFaceInner W F n j hj0 hjLast := by
          exact congrArg (· ≫ _)
            (wbarFaceZero_ι W F (n + 1) ⟨s, w⟩)
      _ = SrepBridge.srepFaceZeroComponent F s ≫
            (wbarIncl W F (n + 1) qMidR ≫
              wbarFaceInner W F n j hj0 hjLast) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent F s ≫
            (wFaceInnerComponent F j hj0 (SrepBridge.srepDropFirst s) ≫
              wbarIncl W F n qR) := by
          exact congrArg (SrepBridge.srepFaceZeroComponent F s ≫ ·) hInnerMid
      _ = (SrepBridge.srepFaceZeroComponent F s ≫
            wFaceInnerComponent F j hj0 (SrepBridge.srepDropFirst s)) ≫
            wbarIncl W F n qR := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (wFaceInnerComponent F j.succ hJSucc0 s ≫
      SrepBridge.srepFaceZeroComponent F
        ((StrictOmitDup.omitAt j.succ).obj s)) ≍
      (SrepBridge.srepFaceZeroComponent F s ≫
        wFaceInnerComponent F j hj0 (SrepBridge.srepDropFirst s)) := by
    change (eqToHom _ ≫
        (eqToHom _ ≫ F.map (((StrictOmitDup.omitAt j.succ).obj s).map' 0 1) ≫
          eqToHom _)) ≍
      ((eqToHom _ ≫ F.map (s.map' 0 1) ≫ eqToHom _) ≫ eqToHom _)
    have hjPos : 1 < (j.succ).val := by
      have hjNe : j.val ≠ 0 := by
        intro heq
        exact hj0 (Fin.ext (by simp [heq]))
      simp only [Fin.val_succ]
      exact Nat.succ_lt_succ (Nat.pos_of_ne_zero hjNe)
    have harr := StrictOmitDup.omit_firstArrow (C := J) (n := n + 1)
      (p := j.succ) hjPos (by omega) s
    rw [harr]
    erw [Functor.map_comp, Functor.map_comp]
    erw [eqToHom_map, eqToHom_map]
    simp only [eqToHom_trans, Category.assoc]
    simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
      comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
    rfl
  calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceInner W F (n + 1) j.succ hJSucc0 hJSuccLast ≫
            wbarFaceZero W F n)
      = (wFaceInnerComponent F j.succ hJSucc0 s ≫
          SrepBridge.srepFaceZeroComponent F
            ((StrictOmitDup.omitAt j.succ).obj s)) ≫
          wbarIncl W F n qL := hL
    _ = (SrepBridge.srepFaceZeroComponent F s ≫
          wFaceInnerComponent F j hj0 (SrepBridge.srepDropFirst s)) ≫
          wbarIncl W F n qR :=
        wbarCompEqOfIdxEqHEq W F hIdx hcoeff
    _ = wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceZero W F (n + 1) ≫
            wbarFaceInner W F n j hj0 hjLast) := hR.symm

/-- Zero-zero `δδ`: dropping the first entry twice. The left pair is
interior-at-`1` then `d₀`; the right pair is `d₀` then `d₀`. The chain
commutation is direct by `ComposableArrows.ext` (omitting position `1` then
dropping the first agrees with dropping the first twice). Coefficients fuse
the `F.map` actions by functoriality: the omitted chain's first arrow is the
composite of the original first two arrows, via `whiskerLeft_map'`, and the
right side composes the two successive `d₀` actions by `Functor.map_comp`. -/
private theorem wbar_δ_comp_δ_zero_zero (n : ℕ) :
    wbarδ W F (n + 1) (0 : Fin (n + 2)).succ ≫ wbarδ W F n 0 =
      wbarδ W F (n + 1) (0 : Fin (n + 2)).castSucc ≫ wbarδ W F n 0 := by
  have hSucc0 : (0 : Fin (n + 2)).succ ≠ (0 : Fin (n + 3)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp at hval
  have hSuccLast : (0 : Fin (n + 2)).succ ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last] at hval
  have h0Cast : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
    apply Fin.ext
    simp
  rw [wbarδ_inner _ _ _ (0 : Fin (n + 2)).succ hSucc0 hSuccLast, wbarδ_zero, h0Cast, wbarδ_zero]
  change wbarFaceInner W F (n + 1) (0 : Fin (n + 2)).succ hSucc0 hSuccLast ≫
      wbarFaceZero W F n =
    wbarFaceZero W F (n + 1) ≫ wbarFaceZero W F n
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 2) => ?_)
  obtain ⟨s, w⟩ := p
  have hchain : SrepBridge.srepDropFirst
      ((StrictOmitDup.omitAt (C := J) (0 : Fin (n + 2)).succ).obj s) =
      SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s) := by
    have hL0 := wOmitZeroChain
      ((StrictOmitDup.omitAt (C := J) (0 : Fin (n + 2)).succ).obj s)
    have hInner := wOmitZeroChain s
    have hOuter := wOmitZeroChain (SrepBridge.srepDropFirst s)
    have hMid := wChainOmitOmit (n := n) (i := (0 : Fin (n + 2)))
      (j := (0 : Fin (n + 2))) le_rfl s
    have h0eq : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    rw [h0eq] at hMid
    have hRight : SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s) =
        (StrictOmitDup.omitAt (C := J) (0 : Fin (n + 2))).obj
          ((StrictOmitDup.omitAt (C := J) (0 : Fin (n + 3))).obj s) := by
      exact hOuter.trans (congrArg _ hInner)
    exact hL0.trans (hMid.trans hRight.symm)
  have eOmit : ((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s).right =
      s.right := by
    have hne : (0 : Fin (n + 2)).succ ≠ Fin.last (n + 2) := hSuccLast
    exact wOmitInner_obj_last hne s
  let qMidL : WIdx J W (n + 1) :=
    wFaceInnerIdx W (n + 1) (0 : Fin (n + 2)).succ hSuccLast ⟨s, w⟩
  let qL : WIdx J W n := wFaceZeroIdx W n qMidL
  let qMidR : WIdx J W (n + 1) := wFaceZeroIdx W (n + 1) ⟨s, w⟩
  let qR : WIdx J W n := wFaceZeroIdx W n qMidR
  have hIdx : qL = qR := by
    have hRHS : W.map
        (eqToHom (rfl : (SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s)).right =
          s.right)).op w = w := by
      have hEq : (eqToHom
          (rfl : (SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s)).right =
            s.right)).op = 𝟙 _ := rfl
      rw [hEq, W.map_id]
      rfl
    have hBase := wIdxOfChainEq W hchain eOmit
      (rfl : (SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s)).right =
        s.right) w
    have hEqPair : (⟨SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s),
        W.map (eqToHom (rfl : (SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s)).right =
          s.right)).op w⟩ : WIdx J W n) =
        ⟨SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s), w⟩ :=
      congrArg (fun ww => (⟨SrepBridge.srepDropFirst (SrepBridge.srepDropFirst s), ww⟩ :
        WIdx J W n)) hRHS
    exact hBase.trans hEqPair
  have hL : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceInner W F (n + 1) (0 : Fin (n + 2)).succ hSucc0 hSuccLast ≫
        wbarFaceZero W F n) =
      (wFaceInnerComponent F (0 : Fin (n + 2)).succ hSucc0 s ≫
        SrepBridge.srepFaceZeroComponent F
          ((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s)) ≫
        wbarIncl W F n qL := by
    have hZeroMid := wbarFaceZero_ι W F n qMidL
    change wbarIncl W F (n + 1) qMidL ≫ wbarFaceZero W F n =
        SrepBridge.srepFaceZeroComponent F
          ((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s) ≫
          wbarIncl W F n qL at hZeroMid
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceInner W F (n + 1) (0 : Fin (n + 2)).succ hSucc0 hSuccLast ≫
              wbarFaceZero W F n)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            wbarFaceInner W F (n + 1) (0 : Fin (n + 2)).succ hSucc0 hSuccLast) ≫
            wbarFaceZero W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F (0 : Fin (n + 2)).succ hSucc0 s ≫
            wbarIncl W F (n + 1) qMidL) ≫
            wbarFaceZero W F n := by
          exact congrArg (· ≫ _)
            (wbarFaceInner_ι W F (n + 1) (0 : Fin (n + 2)).succ hSucc0 hSuccLast ⟨s, w⟩)
      _ = wFaceInnerComponent F (0 : Fin (n + 2)).succ hSucc0 s ≫
            (wbarIncl W F (n + 1) qMidL ≫ wbarFaceZero W F n) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F (0 : Fin (n + 2)).succ hSucc0 s ≫
            (SrepBridge.srepFaceZeroComponent F
              ((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s) ≫ wbarIncl W F n qL) := by
          exact congrArg (wFaceInnerComponent F (0 : Fin (n + 2)).succ hSucc0 s ≫ ·) hZeroMid
      _ = (wFaceInnerComponent F (0 : Fin (n + 2)).succ hSucc0 s ≫
            SrepBridge.srepFaceZeroComponent F
              ((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s)) ≫
            wbarIncl W F n qL := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceZero W F (n + 1) ≫ wbarFaceZero W F n) =
      (SrepBridge.srepFaceZeroComponent F s ≫
        SrepBridge.srepFaceZeroComponent F
          (SrepBridge.srepDropFirst s)) ≫
        wbarIncl W F n qR := by
    have hZeroMidR := wbarFaceZero_ι W F n qMidR
    change wbarIncl W F (n + 1) qMidR ≫ wbarFaceZero W F n =
        SrepBridge.srepFaceZeroComponent F
          (SrepBridge.srepDropFirst s) ≫
          wbarIncl W F n qR at hZeroMidR
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceZero W F (n + 1) ≫ wbarFaceZero W F n)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫ wbarFaceZero W F (n + 1)) ≫
            wbarFaceZero W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceZeroComponent F s ≫
            wbarIncl W F (n + 1) qMidR) ≫
            wbarFaceZero W F n := by
          exact congrArg (· ≫ _) (wbarFaceZero_ι W F (n + 1) ⟨s, w⟩)
      _ = SrepBridge.srepFaceZeroComponent F s ≫
            (wbarIncl W F (n + 1) qMidR ≫ wbarFaceZero W F n) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent F s ≫
            (SrepBridge.srepFaceZeroComponent F
              (SrepBridge.srepDropFirst s) ≫ wbarIncl W F n qR) := by
          exact congrArg (SrepBridge.srepFaceZeroComponent F s ≫ ·) hZeroMidR
      _ = (SrepBridge.srepFaceZeroComponent F s ≫
            SrepBridge.srepFaceZeroComponent F
              (SrepBridge.srepDropFirst s)) ≫
            wbarIncl W F n qR := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (wFaceInnerComponent F _ hSucc0 s ≫
      SrepBridge.srepFaceZeroComponent F
        ((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s)) ≍
      (SrepBridge.srepFaceZeroComponent F s ≫
        SrepBridge.srepFaceZeroComponent F
          (SrepBridge.srepDropFirst s)) := by
    change (eqToHom _ ≫
        (eqToHom _ ≫ F.map (((StrictOmitDup.omitAt _).obj s).map' 0 1) ≫
          eqToHom _)) ≍
      ((eqToHom _ ≫ F.map (s.map' 0 1) ≫ eqToHom _) ≫
        (eqToHom _ ≫ F.map ((SrepBridge.srepDropFirst s).map' 0 1) ≫
          eqToHom _))
    have e0 : (StrictOmitDup.omitFinFunctor (n + 1) (0 : Fin (n + 2)).succ).obj
        (⟨0, by omega⟩ : Fin (n + 2)) = (⟨0, by omega⟩ : Fin (n + 3)) :=
      StrictOmitDup.omitIdx_zero (by simp only [Fin.val_succ, Fin.val_zero]; omega)
    have e1 : (StrictOmitDup.omitFinFunctor (n + 1) (0 : Fin (n + 2)).succ).obj
        (⟨1, by omega⟩ : Fin (n + 2)) = (⟨2, by omega⟩ : Fin (n + 3)) := by
      simp only [StrictOmitDup.omitFinFunctor_obj]
      rw [Fin.succAbove_of_le_castSucc _ _ (by
        rw [Fin.le_iff_val_le_val]
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
        omega)]
      rfl
    have harr : (((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s).map' 0 1
        (by omega) (by omega)) =
        eqToHom (congrArg s.obj e0) ≫ s.map' 0 2 (by omega) (by omega) ≫
          eqToHom (congrArg s.obj e1.symm) := by
      exact StrictOmitDup.whiskerLeft_map' s e0 e1
    have hcomp : s.map' 0 2 (by omega) (by omega) =
        s.map' 0 1 (by omega) (by omega) ≫ s.map' 1 2 (by omega) (by omega) :=
      s.map'_comp 0 1 2 (by omega) (by omega) (by omega)
    have e0d : (Fin.succFunctor (n + 2)).obj
        (⟨0, by omega⟩ : Fin (n + 2)) = (⟨1, by omega⟩ : Fin (n + 3)) := by
      simp only [Fin.succFunctor_obj]
      apply Fin.ext
      simp only [Fin.val_succ]
    have e1d : (Fin.succFunctor (n + 2)).obj
        (⟨1, by omega⟩ : Fin (n + 2)) = (⟨2, by omega⟩ : Fin (n + 3)) := by
      simp only [Fin.succFunctor_obj]
      apply Fin.ext
      simp only [Fin.val_succ]
    have hdrop : ((SrepBridge.srepDropFirst s).map' 0 1 (by omega) (by omega)) =
        eqToHom (congrArg s.obj e0d) ≫ s.map' 1 2 (by omega) (by omega) ≫
          eqToHom (congrArg s.obj e1d.symm) :=
      StrictOmitDup.whiskerLeft_map' s e0d e1d
    rw [harr, hcomp, hdrop]
    erw [Functor.map_comp, Functor.map_comp]
    erw [eqToHom_map, eqToHom_map]
    erw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    erw [eqToHom_map, eqToHom_map]
    simp only [eqToHom_trans, Category.assoc]
    rw [eqToHom_comp_heq_iff]
    rw [eqToHom_comp_heq_iff]
    rw [eqToHom_comp_heq_iff]
    conv_lhs => rw [← Category.assoc]
    rw [comp_eqToHom_heq_iff]
    rw [heq_eqToHom_comp_iff]
    refine CategoryTheory.heq_comp rfl rfl rfl (HEq.refl _) (?_.symm)
    rw [heq_eqToHom_comp_iff]
    rw [heq_eqToHom_comp_iff]
    rw [heq_eqToHom_comp_iff]
    rw [heq_comp_eqToHom_iff]
  calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceInner W F (n + 1) (0 : Fin (n + 2)).succ hSucc0 hSuccLast ≫
            wbarFaceZero W F n)
      = (wFaceInnerComponent F (0 : Fin (n + 2)).succ hSucc0 s ≫
          SrepBridge.srepFaceZeroComponent F
            ((StrictOmitDup.omitAt (0 : Fin (n + 2)).succ).obj s)) ≫
          wbarIncl W F n qL := hL
    _ = (SrepBridge.srepFaceZeroComponent F s ≫
          SrepBridge.srepFaceZeroComponent F
            (SrepBridge.srepDropFirst s)) ≫
          wbarIncl W F n qR :=
        wbarCompEqOfIdxEqHEq W F hIdx hcoeff
    _ = wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceZero W F (n + 1) ≫ wbarFaceZero W F n) := hR.symm

/-- Last-last `δδ`: both faces on the left are outer-last; on the right the
first face is the interior omission just below the top and the second is
outer-last. Coefficients are pure transports on both sides. The chain
commutation is direct by `ComposableArrows.ext` (the omitted position sits
above every index of the remaining chain, so a single
`succAbove_of_le_castSucc` rewrite closes each vertex). The weight-arrow
agreement expresses the omitted chain's last arrow through `whiskerLeft_map'`
and splits the two-step span by functoriality, matching the two successive
outer-last weight actions. -/
private theorem wbar_δ_comp_δ_last_last (n : ℕ) :
    wbarδ W F (n + 1) (Fin.last (n + 1)).succ ≫ wbarδ W F n (Fin.last (n + 1)) =
      wbarδ W F (n + 1) (Fin.last (n + 1)).castSucc ≫
        wbarδ W F n (Fin.last (n + 1)) := by
  have hLastSucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
    apply Fin.ext
    simp [Fin.val_last]
  have hICast0 : (Fin.last (n + 1)).castSucc ≠ (0 : Fin (n + 3)) := by
    intro h0
    have hval := congrArg Fin.val h0
    simp [Fin.val_last, Fin.val_castSucc] at hval
  have hICastLast : (Fin.last (n + 1)).castSucc ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    simp [Fin.val_last, Fin.val_castSucc] at hval
  rw [hLastSucc, wbarδ_last, wbarδ_last,
    wbarδ_inner _ _ _ (Fin.last (n + 1)).castSucc hICast0 hICastLast]
  change wbarFaceLast W F (n + 1) ≫ wbarFaceLast W F n =
    wbarFaceInner W F (n + 1) (Fin.last (n + 1)).castSucc hICast0 hICastLast ≫
      wbarFaceLast W F n
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 2) => ?_)
  obtain ⟨s, w⟩ := p
  let qMidL : WIdx J W (n + 1) := wFaceLastIdx W (n + 1) ⟨s, w⟩
  let qL : WIdx J W n := wFaceLastIdx W n qMidL
  let qMidR : WIdx J W (n + 1) :=
    wFaceInnerIdx W (n + 1) (Fin.last (n + 1)).castSucc hICastLast ⟨s, w⟩
  let qR : WIdx J W n := wFaceLastIdx W n qMidR
  have hchain : SrepBridge.srepDropLast (SrepBridge.srepDropLast s) =
      SrepBridge.srepDropLast
        ((StrictOmitDup.omitAt (C := J)
          (Fin.last (n + 1)).castSucc).obj s) := by
    have hInner := wOmitLastChain s
    have hOuter := wOmitLastChain (SrepBridge.srepDropLast s)
    have hR0 := wOmitLastChain
      ((StrictOmitDup.omitAt (C := J) (Fin.last (n + 1)).castSucc).obj s)
    have hle : Fin.last (n + 1) ≤ Fin.last (n + 1) := le_rfl
    have hMid := wChainOmitOmit (n := n) (i := Fin.last (n + 1))
      (j := Fin.last (n + 1)) hle s
    have hLastSucc : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
      apply Fin.ext
      simp [Fin.val_last]
    rw [hLastSucc] at hMid
    have hLeft : SrepBridge.srepDropLast (SrepBridge.srepDropLast s) =
        (StrictOmitDup.omitAt (C := J) (Fin.last (n + 1))).obj
          ((StrictOmitDup.omitAt (C := J) (Fin.last (n + 2))).obj s) := by
      exact hOuter.trans (congrArg _ hInner)
    have hRightEq : SrepBridge.srepDropLast
        ((StrictOmitDup.omitAt (C := J) (Fin.last (n + 1)).castSucc).obj s) =
        (StrictOmitDup.omitAt (C := J) (Fin.last (n + 1))).obj
          ((StrictOmitDup.omitAt (C := J) (Fin.last (n + 1)).castSucc).obj s) :=
      hR0
    rw [hLeft, hRightEq]
    exact hMid
  have e0 : (StrictOmitDup.omitFinFunctor (n + 1)
      (Fin.last (n + 1)).castSucc).obj (⟨n, by omega⟩ : Fin (n + 2)) =
      (⟨n, by omega⟩ : Fin (n + 3)) := by
    simp only [StrictOmitDup.omitFinFunctor_obj]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.lt_succ_self n)]
    rfl
  have e1 : (StrictOmitDup.omitFinFunctor (n + 1)
      (Fin.last (n + 1)).castSucc).obj (⟨n + 1, by omega⟩ : Fin (n + 2)) =
      (⟨n + 2, by omega⟩ : Fin (n + 3)) := by
    simp only [StrictOmitDup.omitFinFunctor_obj]
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_refl (n + 1))]
    rfl
  have harr : (((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s).map' n
      (n + 1) (by omega) (by omega)) =
      eqToHom (congrArg s.obj e0) ≫ s.map' n (n + 2) (by omega) (by omega) ≫
        eqToHom (congrArg s.obj e1.symm) :=
    StrictOmitDup.whiskerLeft_map' s e0 e1
  have hspan : s.map' n (n + 2) (by omega) (by omega) =
      s.map' n (n + 1) (by omega) (by omega) ≫
        s.map' (n + 1) (n + 2) (by omega) (by omega) :=
    s.map'_comp n (n + 1) (n + 2) (by omega) (by omega) (by omega)
  have eOmit : (((StrictOmitDup.omitAt
      (Fin.last (n + 1)).castSucc).obj s)).right = s.right := by
    have hne : (Fin.last (n + 1)).castSucc ≠ Fin.last (n + 2) := hICastLast
    exact wOmitInner_obj_last hne s
  have hIdx : qL = qR := by
    change wFaceLastIdx W n (wFaceLastIdx W (n + 1) ⟨s, w⟩) =
      wFaceLastIdx W n
        (wFaceInnerIdx W (n + 1) (Fin.last (n + 1)).castSucc hICastLast
          ⟨s, w⟩)
    let fL : (SrepBridge.srepDropLast (SrepBridge.srepDropLast s)).right ⟶
        s.right :=
      (SrepBridge.srepDropLast s).map' n (n + 1) (by omega) (by omega) ≫
        s.map' (n + 1) (n + 2) (by omega) (by omega)
    let fR : (SrepBridge.srepDropLast
        ((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s)).right ⟶
        s.right :=
      (((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s).map' n
        (n + 1) (by omega) (by omega)) ≫ eqToHom eOmit
    have hf : fL =
        eqToHom
            (congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain) ≫
          fR := by
      have hFL : fL = s.map' n (n + 2) (by omega) (by omega) := by
        unfold fL
        exact hspan.symm
      have hFR : fR =
          (eqToHom (congrArg s.obj e0) ≫
            s.map' n (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm)) ≫ eqToHom eOmit :=
        congrArg (· ≫ eqToHom eOmit) harr
      have hSideL : fL ≍ s.map' n (n + 2) (by omega) (by omega) :=
        heq_of_eq hFL
      have hPeelOmit : ((eqToHom (congrArg s.obj e0) ≫
          s.map' n (n + 2) (by omega) (by omega) ≫
            eqToHom (congrArg s.obj e1.symm)) ≫ eqToHom eOmit) ≍
          (eqToHom (congrArg s.obj e0) ≫
            s.map' n (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm)) :=
        CategoryTheory.comp_eqToHom_heq (C := J)
          (f := eqToHom (congrArg s.obj e0) ≫
            s.map' n (n + 2) (by omega) (by omega) ≫
              eqToHom (congrArg s.obj e1.symm))
          (h := eOmit)
      have hReassoc : (eqToHom (congrArg s.obj e0) ≫
          (s.map' n (n + 2) (by omega) (by omega) ≫
            eqToHom (congrArg s.obj e1.symm))) =
          ((eqToHom (congrArg s.obj e0) ≫
            s.map' n (n + 2) (by omega) (by omega)) ≫
              eqToHom (congrArg s.obj e1.symm)) :=
        (Category.assoc _ _ _).symm
      have hPeelV1 : ((eqToHom (congrArg s.obj e0) ≫
          s.map' n (n + 2) (by omega) (by omega)) ≫
            eqToHom (congrArg s.obj e1.symm)) ≍
          (eqToHom (congrArg s.obj e0) ≫
            s.map' n (n + 2) (by omega) (by omega)) :=
        CategoryTheory.comp_eqToHom_heq (C := J)
          (f := eqToHom (congrArg s.obj e0) ≫
            s.map' n (n + 2) (by omega) (by omega))
          (h := congrArg s.obj e1.symm)
      have hPeelV0 : (eqToHom (congrArg s.obj e0) ≫
          s.map' n (n + 2) (by omega) (by omega)) ≍
          s.map' n (n + 2) (by omega) (by omega) :=
        CategoryTheory.eqToHom_comp_heq (C := J)
          (f := s.map' n (n + 2) (by omega) (by omega))
          (h := congrArg s.obj e0)
      have hSideR : eqToHom
          (congrArg (fun t : SrepBridge.SrepIdx J n => t.right) hchain) ≫
          fR ≍ s.map' n (n + 2) (by omega) (by omega) :=
        (CategoryTheory.eqToHom_comp_heq (C := J) (f := fR)
          (h := congrArg (fun t : SrepBridge.SrepIdx J n => t.right)
            hchain)).trans
          ((heq_of_eq hFR).trans
            (hPeelOmit.trans
              ((heq_of_eq hReassoc).trans (hPeelV1.trans hPeelV0))))
      exact eq_of_heq (hSideL.trans hSideR.symm)
    have hCollapseL : W.map
            ((SrepBridge.srepDropLast s).map' n (n + 1) (by omega)
              (by omega)).op
            (W.map (s.map' (n + 1) (n + 2) (by omega) (by omega)).op w) =
          W.map fL.op w :=
      wWeightComp W
        ((SrepBridge.srepDropLast s).map' n (n + 1) (by omega) (by omega))
        (s.map' (n + 1) (n + 2) (by omega) (by omega)) w
    have hCollapseR : W.map
            (((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s).map' n
              (n + 1) (by omega) (by omega)).op
            (W.map (eqToHom eOmit).op w) =
          W.map fR.op w :=
      wWeightComp W
        (((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s).map' n
          (n + 1) (by omega) (by omega))
        (eqToHom eOmit) w
    have hpairL : wFaceLastIdx W n (wFaceLastIdx W (n + 1) ⟨s, w⟩) =
          (⟨SrepBridge.srepDropLast (SrepBridge.srepDropLast s),
            W.map fL.op w⟩ : WIdx J W n) := by
      change (⟨SrepBridge.srepDropLast (SrepBridge.srepDropLast s),
          W.map ((SrepBridge.srepDropLast s).map' n (n + 1)).op
            (W.map (s.map' (n + 1) (n + 2)).op w)⟩ : WIdx J W n) = _
      rw [hCollapseL]
    have hpairR : wFaceLastIdx W n
          (wFaceInnerIdx W (n + 1) (Fin.last (n + 1)).castSucc hICastLast
            ⟨s, w⟩) =
          (⟨SrepBridge.srepDropLast
            ((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s),
            W.map fR.op w⟩ : WIdx J W n) := by
      change (⟨SrepBridge.srepDropLast
          ((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s),
          W.map (((StrictOmitDup.omitAt
            (Fin.last (n + 1)).castSucc).obj s).map' n (n + 1)).op
            (W.map (eqToHom eOmit).op w)⟩ : WIdx J W n) = _
      rw [hCollapseR]
    rw [hpairL, hpairR]
    exact wIdxOfChainEqMap W hchain fL fR hf w
  have hL : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceLast W F (n + 1) ≫ wbarFaceLast W F n) =
      (SrepBridge.srepFaceLastComponent F s ≫
        SrepBridge.srepFaceLastComponent F
          (SrepBridge.srepDropLast s)) ≫
        wbarIncl W F n qL := by
    have hLastMid := wbarFaceLast_ι W F n qMidL
    change wbarIncl W F (n + 1) qMidL ≫ wbarFaceLast W F n =
        SrepBridge.srepFaceLastComponent F (SrepBridge.srepDropLast s) ≫
          wbarIncl W F n qL at hLastMid
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceLast W F (n + 1) ≫ wbarFaceLast W F n)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫ wbarFaceLast W F (n + 1)) ≫
            wbarFaceLast W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceLastComponent F s ≫
            wbarIncl W F (n + 1) qMidL) ≫ wbarFaceLast W F n := by
          exact congrArg (· ≫ _) (wbarFaceLast_ι W F (n + 1) ⟨s, w⟩)
      _ = SrepBridge.srepFaceLastComponent F s ≫
            (wbarIncl W F (n + 1) qMidL ≫ wbarFaceLast W F n) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent F s ≫
            (SrepBridge.srepFaceLastComponent F _ ≫ wbarIncl W F n qL) := by
          exact congrArg (SrepBridge.srepFaceLastComponent F s ≫ ·) hLastMid
      _ = (SrepBridge.srepFaceLastComponent F s ≫
            SrepBridge.srepFaceLastComponent F _) ≫
            wbarIncl W F n qL := by
          exact (Category.assoc _ _ _).symm
  have hR : wbarIncl W F (n + 2) ⟨s, w⟩ ≫
      (wbarFaceInner W F (n + 1) (Fin.last (n + 1)).castSucc hICast0
          hICastLast ≫ wbarFaceLast W F n) =
      (wFaceInnerComponent F _ hICast0 s ≫
        SrepBridge.srepFaceLastComponent F _) ≫
        wbarIncl W F n qR := by
    have hLastMidR := wbarFaceLast_ι W F n qMidR
    change wbarIncl W F (n + 1) qMidR ≫ wbarFaceLast W F n =
        SrepBridge.srepFaceLastComponent F
          ((StrictOmitDup.omitAt (Fin.last (n + 1)).castSucc).obj s) ≫
          wbarIncl W F n qR at hLastMidR
    calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            (wbarFaceInner W F (n + 1) _ hICast0 hICastLast ≫
              wbarFaceLast W F n)
        = (wbarIncl W F (n + 2) ⟨s, w⟩ ≫
            wbarFaceInner W F (n + 1) _ hICast0 hICastLast) ≫
            wbarFaceLast W F n := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent F _ hICast0 s ≫ wbarIncl W F (n + 1) qMidR) ≫
            wbarFaceLast W F n := by
          exact congrArg (· ≫ _)
            (wbarFaceInner_ι W F (n + 1) (Fin.last (n + 1)).castSucc hICast0
              hICastLast ⟨s, w⟩)
      _ = wFaceInnerComponent F _ hICast0 s ≫
            (wbarIncl W F (n + 1) qMidR ≫ wbarFaceLast W F n) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent F _ hICast0 s ≫
            (SrepBridge.srepFaceLastComponent F _ ≫ wbarIncl W F n qR) := by
          exact congrArg (wFaceInnerComponent F _ hICast0 s ≫ ·) hLastMidR
      _ = (wFaceInnerComponent F _ hICast0 s ≫
            SrepBridge.srepFaceLastComponent F _) ≫
            wbarIncl W F n qR := by
          exact (Category.assoc _ _ _).symm
  have hcoeff : (SrepBridge.srepFaceLastComponent F s ≫
      SrepBridge.srepFaceLastComponent F (SrepBridge.srepDropLast s)) =
      (wFaceInnerComponent F _ hICast0 s ≫
        SrepBridge.srepFaceLastComponent F _) := by
    unfold SrepBridge.srepFaceLastComponent wFaceInnerComponent
    simp only [eqToHom_trans]
    rfl
  calc wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceLast W F (n + 1) ≫ wbarFaceLast W F n)
      = (SrepBridge.srepFaceLastComponent F s ≫
          SrepBridge.srepFaceLastComponent F _) ≫
          wbarIncl W F n qL := hL
    _ = (wFaceInnerComponent F _ hICast0 s ≫
          SrepBridge.srepFaceLastComponent F _) ≫
          wbarIncl W F n qR :=
        wbarCompEqOfIdxEqHEq W F hIdx (heq_of_eq hcoeff)
    _ = wbarIncl W F (n + 2) ⟨s, w⟩ ≫
          (wbarFaceInner W F (n + 1) _ hICast0 hICastLast ≫
            wbarFaceLast W F n) := hR.symm

/-- `δδ` for the total face operator: omitting `j.succ` then `i` agrees with
omitting `i.castSucc` then `j`, for `i ≤ j`. Dispatch on endpoints: both zero
is `wbar_δ_comp_δ_zero_zero`, zero against last is the accepted outer
interchange, zero against interior is `wbar_δ_comp_δ_zero_interior`, last
against last is `wbar_δ_comp_δ_last_last`, interior against last is
`wbar_δ_comp_δ_interior_last`, and interior against interior is
`wbar_δ_comp_δ_interior`. The `j = 0` subcase under interior `i` is
impossible by value bounds. -/
theorem wbar_δ_comp_δ (n : ℕ) {i j : Fin (n + 2)} (h : i ≤ j) :
    wbarδ W F (n + 1) j.succ ≫ wbarδ W F n i =
      wbarδ W F (n + 1) i.castSucc ≫ wbarδ W F n j := by
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      exact wbar_δ_comp_δ_zero_zero W F n
    · by_cases hjLast : j = Fin.last (n + 1)
      · exact wbar_δ_comp_δ_zero_last W F n rfl hjLast
      · exact wbar_δ_comp_δ_zero_interior W F n hj0 hjLast
  · by_cases hiLast : i = Fin.last (n + 1)
    · subst hiLast
      have hj : j = Fin.last (n + 1) := by
        have hle := Fin.le_iff_val_le_val.mp h
        simp [Fin.val_last] at hle
        have hjlt := j.is_lt
        apply Fin.ext
        simp [Fin.val_last]
        omega
      subst hj
      exact wbar_δ_comp_δ_last_last W F n
    · by_cases hj0 : j = 0
      · subst hj0
        have hle := Fin.le_iff_val_le_val.mp h
        simp at hle
        have hi_eq : i = 0 := by
          apply Fin.ext
          simp
          omega
        exact absurd hi_eq hi0
      · by_cases hjLast : j = Fin.last (n + 1)
        · subst hjLast
          exact wbar_δ_comp_δ_interior_last W F n hi0 hiLast
        · exact wbar_δ_comp_δ_interior W F n h hi0 hiLast hj0 hjLast

/-- The strict ordinary weighted bar as simplicial data: objects are the
accepted `wbarObj`, faces and degeneracies are the total operators, and the
six relations are the total-operator identities proved above from the
accepted chain facts and outer laws. -/
noncomputable def wbarData : SimplicialObject.Data C where
  obj := fun n => wbarObj W F n
  δ := fun {n} i => wbarδ W F n i
  σ := fun {n} i => wbarσ W F n i
  δ_comp_δ := fun {n} {_i _j} h => wbar_δ_comp_δ W F n h
  δ_comp_σ_of_le := fun {n} {_i _j} h => wbar_δ_comp_σ_of_le W F n h
  δ_comp_σ_self := fun {n} {_i} => wbar_δ_comp_σ_self W F n
  δ_comp_σ_succ := fun {n} {_i} => wbar_δ_comp_σ_succ W F n
  δ_comp_σ_of_gt := fun {n} {_i _j} h => wbar_δ_comp_σ_of_gt W F n h
  σ_comp_σ := fun {n} {_i _j} h => wbar_σ_comp_σ W F n h

/-- Object computation for the bundled data. -/
@[simp]
theorem wbarData_obj (n : ℕ) : (wbarData W F).obj n = wbarObj W F n :=
  rfl

/-- Face computation for the bundled data. -/
@[simp]
theorem wbarData_δ {n : ℕ} (i : Fin (n + 2)) :
    (wbarData W F).δ i = wbarδ W F n i :=
  rfl

/-- Degeneracy computation for the bundled data. -/
@[simp]
theorem wbarData_σ {n : ℕ} (i : Fin (n + 1)) :
    (wbarData W F).σ i = wbarσ W F n i :=
  rfl

end StrictOrdinaryWeightedBar
end CategoryTheory
