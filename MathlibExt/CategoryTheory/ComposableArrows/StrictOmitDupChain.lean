/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.ComposableArrows.StrictOmitDup

/-!
# Strict omit/duplicate chain equalities for composable-arrow chains

This module supplies reusable strict finite omit/duplicate equalities over
composable-arrow chains, unblocking weighted-bar simplicial identities.
All orientations and domains are derived from the actual
`omitFinFunctor` / `dupFinFunctor`, `omitAt` / `dupAt`,
and `Fin.succAbove` / `Fin.predAbove`.

Contents, per relation (diagrammatic composition throughout, first-applied
chain map giving the outer index function):

* `δδ` (`omitOmit_*`): for `i ≤ j`,
  `omitAt (j.succ) ⋙ omitAt i` against the whiskering by
  `omitFin j ⋙ omitFin i.castSucc`;
* `σσ` (`dupDup_*`): for `i ≤ j`,
  `dupAt j ⋙ dupAt (i.castSucc)` against the whiskering by
  `dupFin (j.succ) ⋙ dupFin i`;
* `δσ` below (`omitDupBelow_*`): for `i ≤ j.castSucc`,
  `dupAt (j.succ) ⋙ omitAt (i.castSucc)` against the whiskering by
  `dupFin j ⋙ omitFin i`;
* `δσ` self (`omitDupSelf_*`): `dupAt i ⋙ omitAt (i.castSucc)` against the
  whiskering by the identity, via `Fin.predAbove_succAbove`;
* `δσ` successor (`omitDupSucc_*`): `dupAt i ⋙ omitAt (i.succ)` against the
  whiskering by the identity;
* `δσ` above (`omitDupAbove_*`): for `j.castSucc < i`,
  `dupAt (j.castSucc) ⋙ omitAt (i.succ)` against the whiskering by
  `dupFin j ⋙ omitFin i`.

Each relation is proved at four levels: pointwise index objects (`_*_idx_obj`),
Fin functors (`_*_fin` by `Functor.ext` with object-level Fin arithmetic and
thin-hom `Subsingleton.elim`), chain functors (`_*_chain_fun` by
reassociation-defeq `show` plus `congrArg` of the Fin equality), and chain
objects (`_*_chain_obj` by rewriting with the chain-functor equality).
Cross-length functors and chain objects are never identified definitionally;
iterated `omitAt` / `dupAt` composites are compared with single-whiskering
functors, never force-folded.

Endpoint index facts (`omitIdx_*`, `dupIdx_*`, `dupTop_prev`) feed the four
arrow transport lemmas (`omit_firstArrow`, `omit_lastArrow`, `dup_lastArrow`,
`dupTop_lastArrow` plus the `𝟙` corollary `dupTop_lastArrow_id`), all in
`ComposableArrows.map'` form via the generic `whiskerLeft_map'` transport.

Reuse: the `StrictOmitDup` functors, obj/map computation rules,
`dupFin_last_obj`, and associator comparison isos (available for downstream
comparison transport); `whiskerLeftFunctor`, `whiskerLeft`,
`Functor.comp_obj`, `Functor.comp_map`, `eqToHom_map`, `Fin.succAbove` /
`Fin.predAbove` characterization lemmas, and `Fin` val `rfl` facts.
No weighted bars, coproducts, Sigma transport, `Data`, enriched, or derived
content appears here.

Exact boundary: strict Fin/functor equalities and `map'` arrow transports
only. Endpoint comparison isomorphisms, inner faces, the five simplicial
identities, and any `SimplicialObject.Data` packaging remain downstream.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOmitDup

universe v u

variable {C : Type u} [Category.{v} C]

/-- Transport an index-functor equality through pre-whiskering on objects.
Reserved downstream transport from a Fin equality alone; the six `_*_chain_obj`
lemmas here rewrite with the chain-functor equality instead, so this file
does not call it. -/
theorem whiskerLeft_obj_eq_of_idx_obj_eq {m n : ℕ}
    {Φ Ψ : Fin (m + 1) ⥤ Fin (n + 1)} (h : Φ = Ψ)
    (F : ComposableArrows C n) :
    (ComposableArrows.whiskerLeftFunctor Φ).obj F =
      (ComposableArrows.whiskerLeftFunctor Ψ).obj F :=
  congrArg (fun Φ => (ComposableArrows.whiskerLeftFunctor Φ).obj F) h

/-- Pointwise `δδ` index equality: omitting `j.succ` then `i` agrees with
omitting `j` then `i.castSucc`, for `i ≤ j`. The first rewrite swaps the
omission order via `Fin.succAbove_succAbove_succAbove_predAbove`; the two
bridges collapse the swapped indices via `Fin.succAbove_succ_of_le` and
`Fin.predAbove_succ_of_le`. -/
theorem omitOmit_idx_obj {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j)
    (k : Fin (n + 1)) :
    (j.succ).succAbove (i.succAbove k) =
      (i.castSucc).succAbove (j.succAbove k) := by
  rw [← Fin.succAbove_succAbove_succAbove_predAbove (j.succ) i k,
    Fin.succAbove_succ_of_le _ _ h, Fin.predAbove_succ_of_le _ _ h]

/-- Fin-functor `δδ` equality, from `Fin (n + 1)` to `Fin (n + 3)`. -/
theorem omitOmit_fin {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    (omitFinFunctor n i ⋙ omitFinFunctor (n + 1) j.succ) =
      (omitFinFunctor n j ⋙ omitFinFunctor (n + 1) i.castSucc) := by
  refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
  simp only [Functor.comp_obj, omitFinFunctor_obj]
  exact omitOmit_idx_obj h _

/-- Chain-functor `δδ` equality, from `ComposableArrows C (n + 2)` to
`ComposableArrows C n`. -/
theorem omitOmit_chain_fun {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    (omitAt (C := C) (n := n + 1) j.succ ⋙ omitAt (n := n) i) =
      ComposableArrows.whiskerLeftFunctor
        (omitFinFunctor n j ⋙ omitFinFunctor (n + 1) i.castSucc) := by
  change ComposableArrows.whiskerLeftFunctor
      (omitFinFunctor n i ⋙ omitFinFunctor (n + 1) j.succ) = _
  exact congrArg _ (omitOmit_fin h)

/-- Chain-object `δδ` equality. -/
theorem omitOmit_chain_obj {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j)
    (F : ComposableArrows C (n + 2)) :
    (omitAt (n := n + 1) j.succ ⋙ omitAt (n := n) i).obj F =
      (ComposableArrows.whiskerLeftFunctor
        (omitFinFunctor n j ⋙ omitFinFunctor (n + 1) i.castSucc)).obj F := by
  rw [omitOmit_chain_fun h]

/-- Pointwise `σσ` index equality: duplicating `j` then `i.castSucc` agrees
with duplicating `i` then `j.succ`, for `i ≤ j`. Three value regions
(`k ≤ i`, `i < k ≤ j + 1`, `j + 1 < k`), each closed by the four matching
`Fin.predAbove_of_*` characterizations and a `Fin.ext` value computation. -/
theorem dupDup_idx_obj {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j)
    (k : Fin (n + 3)) :
    j.predAbove ((i.castSucc).predAbove k) =
      i.predAbove ((j.succ).predAbove k) := by
  have hij : i.val ≤ j.val := Fin.le_iff_val_le_val.mp h
  have hklt : k.val < n + 3 := k.is_lt
  have hilt : i.val < n + 1 := i.is_lt
  have hjlt : j.val < n + 1 := j.is_lt
  rcases (Nat.lt_or_ge i.val k.val).symm with hki | hki
  · have hW2 : k ≤ Fin.castSucc (i.castSucc) := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ i.val; omega
    have hkne : k ≠ Fin.last (n + 2) :=
      ne_of_lt (by rw [Fin.lt_def]; change k.val < n + 2; omega)
    have hY2 : (k.castPred hkne) ≤ Fin.castSucc j := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val; omega
    have hU2 : k ≤ Fin.castSucc (j.succ) := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val + 1; omega
    have hV2 : (k.castPred hkne) ≤ Fin.castSucc i := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ i.val; omega
    rw [Fin.predAbove_of_le_castSucc _ _ hW2, Fin.predAbove_of_le_castSucc _ _ hY2,
      Fin.predAbove_of_le_castSucc _ _ hU2, Fin.predAbove_of_le_castSucc _ _ hV2]
  · rcases (Nat.lt_or_ge (j.val + 1) k.val).symm with hkj | hkj
    · have hW1 : Fin.castSucc (i.castSucc) < k := by
        rw [Fin.lt_def]; change i.val < k.val; omega
      have hkne : k ≠ Fin.last (n + 2) :=
        ne_of_lt (by rw [Fin.lt_def]; change k.val < n + 2; omega)
      have hk0 : k ≠ 0 :=
        ne_of_gt (by rw [Fin.lt_def]; change (0 : ℕ) < k.val; omega)
      have hY2 : (k.pred hk0) ≤ Fin.castSucc j := by
        rw [Fin.le_iff_val_le_val]; change k.val - 1 ≤ j.val; omega
      have hU2 : k ≤ Fin.castSucc (j.succ) := by
        rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val + 1; omega
      have hV1 : Fin.castSucc i < (k.castPred hkne) := by
        rw [Fin.lt_def]; change i.val < k.val; omega
      rw [Fin.predAbove_of_castSucc_lt _ _ hW1, Fin.predAbove_of_le_castSucc _ _ hY2,
        Fin.predAbove_of_le_castSucc _ _ hU2, Fin.predAbove_of_castSucc_lt _ _ hV1]
      apply Fin.ext
      change k.val - 1 = k.val - 1
      omega
    · have hW1 : Fin.castSucc (i.castSucc) < k := by
        rw [Fin.lt_def]; change i.val < k.val; omega
      have hk0 : k ≠ 0 :=
        ne_of_gt (by rw [Fin.lt_def]; change (0 : ℕ) < k.val; omega)
      have hY1 : Fin.castSucc j < (k.pred hk0) := by
        rw [Fin.lt_def]; change j.val < k.val - 1; omega
      have hU1 : Fin.castSucc (j.succ) < k := by
        rw [Fin.lt_def]; change j.val + 1 < k.val; omega
      have hV1 : Fin.castSucc i < (k.pred hk0) := by
        rw [Fin.lt_def]; change i.val < k.val - 1; omega
      rw [Fin.predAbove_of_castSucc_lt _ _ hW1, Fin.predAbove_of_castSucc_lt _ _ hY1,
        Fin.predAbove_of_castSucc_lt _ _ hU1, Fin.predAbove_of_castSucc_lt _ _ hV1]

/-- Fin-functor `σσ` equality, from `Fin (n + 3)` to `Fin (n + 1)`. -/
theorem dupDup_fin {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    (dupFinFunctor (n + 1) (i.castSucc) ⋙ dupFinFunctor n j) =
      (dupFinFunctor (n + 1) (j.succ) ⋙ dupFinFunctor n i) := by
  refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
  simp only [Functor.comp_obj, dupFinFunctor_obj]
  exact dupDup_idx_obj h _

/-- Chain-functor `σσ` equality, from `ComposableArrows C n` to
`ComposableArrows C (n + 2)`. -/
theorem dupDup_chain_fun {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    (dupAt (C := C) (n := n) j ⋙ dupAt (n := n + 1) (i.castSucc)) =
      ComposableArrows.whiskerLeftFunctor
        (dupFinFunctor (n + 1) (j.succ) ⋙ dupFinFunctor n i) := by
  change ComposableArrows.whiskerLeftFunctor
      (dupFinFunctor (n + 1) (i.castSucc) ⋙ dupFinFunctor n j) = _
  exact congrArg _ (dupDup_fin h)

/-- Chain-object `σσ` equality. -/
theorem dupDup_chain_obj {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j)
    (F : ComposableArrows C n) :
    (dupAt (n := n) j ⋙ dupAt (n := n + 1) (i.castSucc)).obj F =
      (ComposableArrows.whiskerLeftFunctor
        (dupFinFunctor (n + 1) (j.succ) ⋙ dupFinFunctor n i)).obj F := by
  rw [dupDup_chain_fun h]

/-- Pointwise `δσ`-below index equality: duplicating `j.succ` then omitting
`i.castSucc` agrees with omitting `i` then duplicating `j`, for
`i ≤ j.castSucc`. Three value regions (`k < i`, `i ≤ k ≤ j`, `j < k`). -/
theorem omitDupBelow_idx_obj {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) (k : Fin (n + 2)) :
    (j.succ).predAbove ((i.castSucc).succAbove k) =
      i.succAbove (j.predAbove k) := by
  have hij : i.val ≤ j.val := by
    have h' := Fin.le_iff_val_le_val.mp h
    simp only [Fin.val_castSucc] at h'
    exact h'
  have hklt : k.val < n + 2 := k.is_lt
  have hilt : i.val < n + 2 := i.is_lt
  have hjlt : j.val < n + 1 := j.is_lt
  rcases Nat.lt_or_ge k.val i.val with hki | hki
  · have hX1 : Fin.castSucc k < i.castSucc := by
      rw [Fin.lt_def]; change k.val < i.val; omega
    have hkne : k ≠ Fin.last (n + 1) :=
      ne_of_lt (by rw [Fin.lt_def]; change k.val < n + 1; omega)
    have hY2 : (k.castSucc) ≤ Fin.castSucc (j.succ) := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val + 1; omega
    have hU2 : k ≤ Fin.castSucc j := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val; omega
    have hV1 : Fin.castSucc (k.castPred hkne) < i := by
      rw [Fin.lt_def]; change k.val < i.val; omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hX1, Fin.predAbove_of_le_castSucc _ _ hY2,
      Fin.predAbove_of_le_castSucc _ _ hU2, Fin.succAbove_of_castSucc_lt _ _ hV1]
    apply Fin.ext
    change k.val = k.val
    omega
  · rcases (Nat.lt_or_ge j.val k.val).symm with hkj | hkj
    · have hX2 : i.castSucc ≤ Fin.castSucc k := by
        rw [Fin.le_iff_val_le_val]; change i.val ≤ k.val; omega
      have hkne : k ≠ Fin.last (n + 1) :=
        ne_of_lt (by rw [Fin.lt_def]; change k.val < n + 1; omega)
      have hY2 : (k.succ) ≤ Fin.castSucc (j.succ) := by
        rw [Fin.le_iff_val_le_val]; change k.val + 1 ≤ j.val + 1; omega
      have hU2 : k ≤ Fin.castSucc j := by
        rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val; omega
      have hV2 : i ≤ Fin.castSucc (k.castPred hkne) := by
        rw [Fin.le_iff_val_le_val]; change i.val ≤ k.val; omega
      rw [Fin.succAbove_of_le_castSucc _ _ hX2, Fin.predAbove_of_le_castSucc _ _ hY2,
        Fin.predAbove_of_le_castSucc _ _ hU2, Fin.succAbove_of_le_castSucc _ _ hV2]
      apply Fin.ext
      change k.val + 1 = k.val + 1
      omega
    · have hX2 : i.castSucc ≤ Fin.castSucc k := by
        rw [Fin.le_iff_val_le_val]; change i.val ≤ k.val; omega
      have hk0 : k ≠ 0 :=
        ne_of_gt (by rw [Fin.lt_def]; change (0 : ℕ) < k.val; omega)
      have hY1 : Fin.castSucc (j.succ) < (k.succ) := by
        rw [Fin.lt_def]; change j.val + 1 < k.val + 1; omega
      have hU1 : Fin.castSucc j < k := by
        rw [Fin.lt_def]; change j.val < k.val; omega
      have hV2 : i ≤ Fin.castSucc (k.pred hk0) := by
        rw [Fin.le_iff_val_le_val]; change i.val ≤ k.val - 1; omega
      rw [Fin.succAbove_of_le_castSucc _ _ hX2, Fin.predAbove_of_castSucc_lt _ _ hY1,
        Fin.predAbove_of_castSucc_lt _ _ hU1, Fin.succAbove_of_le_castSucc _ _ hV2]
      apply Fin.ext
      change (k.val + 1) - 1 = (k.val - 1) + 1
      omega

/-- Fin-functor `δσ`-below equality, on `Fin (n + 2)`. -/
theorem omitDupBelow_fin {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) :
    (omitFinFunctor (n + 1) (i.castSucc) ⋙ dupFinFunctor (n + 1) (j.succ)) =
      (dupFinFunctor n j ⋙ omitFinFunctor n i) := by
  refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
  simp only [Functor.comp_obj, omitFinFunctor_obj, dupFinFunctor_obj]
  exact omitDupBelow_idx_obj h _

/-- Chain-functor `δσ`-below equality, on `ComposableArrows C (n + 1)`. -/
theorem omitDupBelow_chain_fun {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) :
    (dupAt (C := C) (n := n + 1) (j.succ) ⋙ omitAt (n := n + 1) (i.castSucc)) =
      ComposableArrows.whiskerLeftFunctor
        (dupFinFunctor n j ⋙ omitFinFunctor n i) := by
  change ComposableArrows.whiskerLeftFunctor
      (omitFinFunctor (n + 1) (i.castSucc) ⋙ dupFinFunctor (n + 1) (j.succ)) = _
  exact congrArg _ (omitDupBelow_fin h)

/-- Chain-object `δσ`-below equality. -/
theorem omitDupBelow_chain_obj {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) (F : ComposableArrows C (n + 1)) :
    (dupAt (n := n + 1) (j.succ) ⋙ omitAt (n := n + 1) (i.castSucc)).obj F =
      (ComposableArrows.whiskerLeftFunctor
        (dupFinFunctor n j ⋙ omitFinFunctor n i)).obj F := by
  rw [omitDupBelow_chain_fun h]

/-- Pointwise `δσ`-self index equality: duplicating `i` then omitting
`i.castSucc` is the identity, via `Fin.predAbove_succAbove`. -/
theorem omitDupSelf_idx_obj {n : ℕ} {i : Fin (n + 1)} (k : Fin (n + 1)) :
    i.predAbove ((i.castSucc).succAbove k) = k :=
  Fin.predAbove_succAbove _ _

/-- Fin-functor `δσ`-self equality: the composite is `Functor.id`. -/
theorem omitDupSelf_fin {n : ℕ} {i : Fin (n + 1)} :
    (omitFinFunctor n (i.castSucc) ⋙ dupFinFunctor n i) =
      Functor.id (Fin (n + 1)) := by
  refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
  simp only [Functor.comp_obj, omitFinFunctor_obj, dupFinFunctor_obj]
  exact omitDupSelf_idx_obj _

/-- Chain-functor `δσ`-self equality, on `ComposableArrows C n`. -/
theorem omitDupSelf_chain_fun {n : ℕ} {i : Fin (n + 1)} :
    (dupAt (C := C) (n := n) i ⋙ omitAt (n := n) (i.castSucc)) =
      ComposableArrows.whiskerLeftFunctor (Functor.id (Fin (n + 1))) := by
  change ComposableArrows.whiskerLeftFunctor
      (omitFinFunctor n (i.castSucc) ⋙ dupFinFunctor n i) = _
  exact congrArg _ omitDupSelf_fin

/-- Chain-object `δσ`-self equality. -/
theorem omitDupSelf_chain_obj {n : ℕ} {i : Fin (n + 1)}
    (F : ComposableArrows C n) :
    (dupAt (n := n) i ⋙ omitAt (n := n) (i.castSucc)).obj F =
      (ComposableArrows.whiskerLeftFunctor (Functor.id (Fin (n + 1)))).obj F := by
  rw [omitDupSelf_chain_fun]

/-- Pointwise `δσ`-successor index equality: duplicating `i` then omitting
`i.succ` is the identity, by a two-case split (`k ≤ i` versus `i < k`). -/
theorem omitDupSucc_idx_obj {n : ℕ} {i : Fin (n + 1)} (k : Fin (n + 1)) :
    i.predAbove ((i.succ).succAbove k) = k := by
  rcases Fin.le_or_lt k i with hki | hki
  · rw [Fin.succAbove_succ_of_le _ _ hki, Fin.predAbove_castSucc_of_le _ _ hki]
  · rw [Fin.succAbove_succ_of_lt _ _ hki,
      Fin.predAbove_succ_of_le _ _ (Fin.le_of_lt hki)]

/-- Fin-functor `δσ`-successor equality: the composite is `Functor.id`. -/
theorem omitDupSucc_fin {n : ℕ} {i : Fin (n + 1)} :
    (omitFinFunctor n (i.succ) ⋙ dupFinFunctor n i) =
      Functor.id (Fin (n + 1)) := by
  refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
  simp only [Functor.comp_obj, omitFinFunctor_obj, dupFinFunctor_obj]
  exact omitDupSucc_idx_obj _

/-- Chain-functor `δσ`-successor equality, on `ComposableArrows C n`. -/
theorem omitDupSucc_chain_fun {n : ℕ} {i : Fin (n + 1)} :
    (dupAt (C := C) (n := n) i ⋙ omitAt (n := n) (i.succ)) =
      ComposableArrows.whiskerLeftFunctor (Functor.id (Fin (n + 1))) := by
  change ComposableArrows.whiskerLeftFunctor
      (omitFinFunctor n (i.succ) ⋙ dupFinFunctor n i) = _
  exact congrArg _ omitDupSucc_fin

/-- Chain-object `δσ`-successor equality. -/
theorem omitDupSucc_chain_obj {n : ℕ} {i : Fin (n + 1)}
    (F : ComposableArrows C n) :
    (dupAt (n := n) i ⋙ omitAt (n := n) (i.succ)).obj F =
      (ComposableArrows.whiskerLeftFunctor (Functor.id (Fin (n + 1)))).obj F := by
  rw [omitDupSucc_chain_fun]

/-- Pointwise `δσ`-above index equality: duplicating `j.castSucc` then
omitting `i.succ` agrees with omitting `i` then duplicating `j`, for
`j.castSucc < i`. Three value regions (`k ≤ j`, `j < k ≤ i`, `i < k`). -/
theorem omitDupAbove_idx_obj {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) (k : Fin (n + 2)) :
    (j.castSucc).predAbove ((i.succ).succAbove k) =
      i.succAbove (j.predAbove k) := by
  have hji : j.val < i.val := by
    have h' := Fin.lt_def.mp h
    simp only [Fin.val_castSucc] at h'
    exact h'
  have hklt : k.val < n + 2 := k.is_lt
  have hjlt : j.val < n + 1 := j.is_lt
  rcases (Nat.lt_or_ge j.val k.val).symm with hkj | hkj
  · have hX1 : Fin.castSucc k < i.succ := by
      rw [Fin.lt_def]; change k.val < i.val + 1; omega
    have hkne : k ≠ Fin.last (n + 1) :=
      ne_of_lt (by rw [Fin.lt_def]; change k.val < n + 1; omega)
    have hY2 : (k.castSucc) ≤ Fin.castSucc (j.castSucc) := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val; omega
    have hU2 : k ≤ Fin.castSucc j := by
      rw [Fin.le_iff_val_le_val]; change k.val ≤ j.val; omega
    have hV1 : Fin.castSucc (k.castPred hkne) < i := by
      rw [Fin.lt_def]; change k.val < i.val; omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hX1, Fin.predAbove_of_le_castSucc _ _ hY2,
      Fin.predAbove_of_le_castSucc _ _ hU2, Fin.succAbove_of_castSucc_lt _ _ hV1]
    apply Fin.ext
    change k.val = k.val
    omega
  · rcases (Nat.lt_or_ge i.val k.val).symm with hki | hki
    · have hX1 : Fin.castSucc k < i.succ := by
        rw [Fin.lt_def]; change k.val < i.val + 1; omega
      have hk0 : k ≠ 0 :=
        ne_of_gt (by rw [Fin.lt_def]; change (0 : ℕ) < k.val; omega)
      have hY1 : Fin.castSucc (j.castSucc) < (k.castSucc) := by
        rw [Fin.lt_def]; change j.val < k.val; omega
      have hU1 : Fin.castSucc j < k := by
        rw [Fin.lt_def]; change j.val < k.val; omega
      have hV1 : Fin.castSucc (k.pred hk0) < i := by
        rw [Fin.lt_def]; change k.val - 1 < i.val; omega
      rw [Fin.succAbove_of_castSucc_lt _ _ hX1, Fin.predAbove_of_castSucc_lt _ _ hY1,
        Fin.predAbove_of_castSucc_lt _ _ hU1, Fin.succAbove_of_castSucc_lt _ _ hV1]
      apply Fin.ext
      change k.val - 1 = k.val - 1
      omega
    · have hX2 : i.succ ≤ Fin.castSucc k := by
        rw [Fin.le_iff_val_le_val]; change i.val + 1 ≤ k.val; omega
      have hk0 : k ≠ 0 :=
        ne_of_gt (by rw [Fin.lt_def]; change (0 : ℕ) < k.val; omega)
      have hY1 : Fin.castSucc (j.castSucc) < (k.succ) := by
        rw [Fin.lt_def]; change j.val < k.val + 1; omega
      have hU1 : Fin.castSucc j < k := by
        rw [Fin.lt_def]; change j.val < k.val; omega
      have hV2 : i ≤ Fin.castSucc (k.pred hk0) := by
        rw [Fin.le_iff_val_le_val]; change i.val ≤ k.val - 1; omega
      rw [Fin.succAbove_of_le_castSucc _ _ hX2, Fin.predAbove_of_castSucc_lt _ _ hY1,
        Fin.predAbove_of_castSucc_lt _ _ hU1, Fin.succAbove_of_le_castSucc _ _ hV2]
      apply Fin.ext
      change (k.val + 1) - 1 = (k.val - 1) + 1
      omega

/-- Fin-functor `δσ`-above equality, on `Fin (n + 2)`. -/
theorem omitDupAbove_fin {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) :
    (omitFinFunctor (n + 1) (i.succ) ⋙ dupFinFunctor (n + 1) (j.castSucc)) =
      (dupFinFunctor n j ⋙ omitFinFunctor n i) := by
  refine Functor.ext (fun k => ?_) (fun X Y f => Subsingleton.elim _ _)
  simp only [Functor.comp_obj, omitFinFunctor_obj, dupFinFunctor_obj]
  exact omitDupAbove_idx_obj h _

/-- Chain-functor `δσ`-above equality, on `ComposableArrows C (n + 1)`. -/
theorem omitDupAbove_chain_fun {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) :
    (dupAt (C := C) (n := n + 1) (j.castSucc) ⋙ omitAt (n := n + 1) (i.succ)) =
      ComposableArrows.whiskerLeftFunctor
        (dupFinFunctor n j ⋙ omitFinFunctor n i) := by
  change ComposableArrows.whiskerLeftFunctor
      (omitFinFunctor (n + 1) (i.succ) ⋙ dupFinFunctor (n + 1) (j.castSucc)) = _
  exact congrArg _ (omitDupAbove_fin h)

/-- Chain-object `δσ`-above equality. -/
theorem omitDupAbove_chain_obj {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) (F : ComposableArrows C (n + 1)) :
    (dupAt (n := n + 1) (j.castSucc) ⋙ omitAt (n := n + 1) (i.succ)).obj F =
      (ComposableArrows.whiskerLeftFunctor
        (dupFinFunctor n j ⋙ omitFinFunctor n i)).obj F := by
  rw [omitDupAbove_chain_fun h]

/-- Omission away from `0` fixes the zeroth index. -/
theorem omitIdx_zero {n : ℕ} {p : Fin (n + 2)} (hp : 0 < p.val) :
    (omitFinFunctor n p).obj (⟨0, by omega⟩ : Fin (n + 1)) =
      (⟨0, by omega⟩ : Fin (n + 2)) := by
  apply Fin.ext
  change (p.succAbove (⟨0, by omega⟩ : Fin (n + 1))).val = 0
  rw [Fin.succAbove_of_castSucc_lt _ _ (by
    rw [Fin.lt_def]
    change (0 : ℕ) < p.val
    omega)]
  rfl

/-- Omission above `1` fixes the first index. -/
theorem omitIdx_one {n : ℕ} {p : Fin (n + 2)} (hp : 1 < p.val) :
    (omitFinFunctor n p).obj (⟨1, by omega⟩ : Fin (n + 1)) =
      (⟨1, by omega⟩ : Fin (n + 2)) := by
  apply Fin.ext
  change (p.succAbove (⟨1, by omega⟩ : Fin (n + 1))).val = 1
  rw [Fin.succAbove_of_castSucc_lt _ _ (by
    rw [Fin.lt_def]
    change (1 : ℕ) < p.val
    omega)]
  rfl

/-- Omission at `p.val + 1 ≤ n` sends `n - 1` to `n` (shift past the hole). -/
theorem omitIdx_shift_lo {n : ℕ} {p : Fin (n + 2)} (hp : p.val + 1 ≤ n) :
    (omitFinFunctor n p).obj (⟨n - 1, by omega⟩ : Fin (n + 1)) =
      (⟨n, by omega⟩ : Fin (n + 2)) := by
  have hside : p ≤ Fin.castSucc (⟨n - 1, by omega⟩ : Fin (n + 1)) := by
    rw [Fin.le_iff_val_le_val]
    change p.val ≤ n - 1
    omega
  apply Fin.ext
  change (p.succAbove (⟨n - 1, by omega⟩ : Fin (n + 1))).val =
    ((⟨n, by omega⟩ : Fin (n + 2))).val
  rw [Fin.succAbove_of_le_castSucc _ _ hside]
  change n - 1 + 1 = n
  omega

/-- Omission at `p.val + 1 ≤ n` sends `n` to `n + 1` (shift past the hole). -/
theorem omitIdx_shift_top {n : ℕ} {p : Fin (n + 2)} (hp : p.val + 1 ≤ n) :
    (omitFinFunctor n p).obj (⟨n, by omega⟩ : Fin (n + 1)) =
      (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
  have hside : p ≤ Fin.castSucc (⟨n, by omega⟩ : Fin (n + 1)) := by
    rw [Fin.le_iff_val_le_val]
    change p.val ≤ n
    omega
  apply Fin.ext
  change (p.succAbove (⟨n, by omega⟩ : Fin (n + 1))).val =
    ((⟨n + 1, by omega⟩ : Fin (n + 2))).val
  rw [Fin.succAbove_of_le_castSucc _ _ hside]
  change n + 1 = n + 1
  omega

/-- Every duplicate index functor preserves the last index (accepted
`dupFin_last_obj` in `⟨_, by omega⟩` form). -/
theorem dupIdx_top {n : ℕ} {p : Fin (n + 1)} :
    (dupFinFunctor n p).obj (⟨n + 1, by omega⟩ : Fin (n + 2)) =
      (⟨n, by omega⟩ : Fin (n + 1)) :=
  dupFin_last_obj n p

/-- Duplication below the top sends `n` to `n - 1`. -/
theorem dupIdx_prev {n : ℕ} {p : Fin (n + 1)} (hp : p.val < n) :
    (dupFinFunctor n p).obj (⟨n, by omega⟩ : Fin (n + 2)) =
      (⟨n - 1, by omega⟩ : Fin (n + 1)) := by
  apply Fin.ext
  change (p.predAbove (⟨n, by omega⟩ : Fin (n + 2))).val =
    ((⟨n - 1, by omega⟩ : Fin (n + 1))).val
  rw [Fin.predAbove_of_castSucc_lt _ _ (by
    rw [Fin.lt_def]
    change p.val < n
    omega)]
  change n - 1 = n - 1
  omega

/-- Duplication at the top fixes `n` at the last index. -/
theorem dupTop_prev {n : ℕ} :
    (dupFinFunctor n (Fin.last n)).obj (⟨n, by omega⟩ : Fin (n + 2)) =
      Fin.last n := by
  apply Fin.ext
  change ((Fin.last n).predAbove (⟨n, by omega⟩ : Fin (n + 2))).val =
    (Fin.last n).val
  rw [Fin.predAbove_of_le_castSucc _ _ (by
    rw [Fin.le_iff_val_le_val]
    change n ≤ n
    omega)]
  change n = n
  omega

/-- Generic `map'` transport across pre-whiskering: the `a → b` arrow of a
pre-whiskered chain equals the transported `a' → b'` arrow of the original
chain along the index equalities. The Fin-level naturality square holds by
thin-hom `Subsingleton.elim`; `eqToHom_map` and functoriality finish. -/
theorem whiskerLeft_map' {m n : ℕ} {Φ : Fin (n + 1) ⥤ Fin (m + 1)}
    (F : ComposableArrows C m) {a b : ℕ} {ha : a < n + 1} {hb : b < n + 1}
    {hab : a ≤ b} {a' b' : ℕ} {ha' : a' < m + 1} {hb' : b' < m + 1} {hab' : a' ≤ b'}
    (e0 : Φ.obj ⟨a, ha⟩ = (⟨a', ha'⟩ : Fin (m + 1)))
    (e1 : Φ.obj ⟨b, hb⟩ = (⟨b', hb'⟩ : Fin (m + 1))) :
    (F.whiskerLeft Φ).map' a b hab (by omega) =
      eqToHom (congrArg F.obj e0) ≫ F.map' a' b' hab' (by omega) ≫
        eqToHom (congrArg F.obj e1.symm) := by
  simp only [ComposableArrows.map']
  have key : ∀ {x y : Fin (n + 1)} {x' y' : Fin (m + 1)}
      (w : Φ.obj x ⟶ Φ.obj y) (u : x' ⟶ y')
      (f0 : Φ.obj x = x') (f1 : Φ.obj y = y'),
      F.map w = eqToHom (congrArg F.obj f0) ≫ F.map u ≫
        eqToHom (congrArg F.obj f1.symm) := by
    intro _ _ _ _ w u f0 f1
    have hw : w = eqToHom f0 ≫ u ≫ eqToHom f1.symm := Subsingleton.elim _ _
    rw [hw, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact key _ _ e0 e1

/-- First-arrow preservation under omission away from the ends:
for `1 < p.val`, the `0 → 1` arrow of the omitted chain is the transported
`0 → 1` arrow of the original chain. -/
theorem omit_firstArrow {n : ℕ} {p : Fin (n + 2)} (hp : 1 < p.val) (hn : 1 ≤ n)
    (F : ComposableArrows C (n + 1)) :
    ((omitAt p).obj F).map' 0 1 (by omega) hn =
      eqToHom (congrArg F.obj (omitIdx_zero (by omega))) ≫
        F.map' 0 1 (by omega) (by omega) ≫
        eqToHom (congrArg F.obj (omitIdx_one hp).symm) := by
  simp only [omitAt_obj]
  exact whiskerLeft_map' F (omitIdx_zero (by omega)) (omitIdx_one hp)

/-- Last-arrow preservation under omission below the top: for
`p.val + 1 ≤ n`, the `(n - 1) → n` arrow of the omitted chain is the
transported `n → (n + 1)` (last) arrow of the original chain. -/
theorem omit_lastArrow {n : ℕ} {p : Fin (n + 2)} (hp : p.val + 1 ≤ n)
    (F : ComposableArrows C (n + 1)) :
    ((omitAt p).obj F).map' (n - 1) n (by omega) (by omega) =
      eqToHom (congrArg F.obj (omitIdx_shift_lo hp)) ≫
        F.map' n (n + 1) (by omega) (by omega) ≫
        eqToHom (congrArg F.obj (omitIdx_shift_top hp).symm) := by
  simp only [omitAt_obj]
  exact whiskerLeft_map' F (omitIdx_shift_lo hp) (omitIdx_shift_top hp)

/-- Last-arrow behavior under duplication away from the top: for
`p.val < n`, the `n → (n + 1)` (last) arrow of the duplicated chain is the
transported `(n - 1) → n` arrow of the original chain. -/
theorem dup_lastArrow {n : ℕ} {p : Fin (n + 1)} (hp : p.val < n)
    (F : ComposableArrows C n) :
    ((dupAt p).obj F).map' n (n + 1) (by omega) (by omega) =
      eqToHom (congrArg F.obj (dupIdx_prev hp)) ≫
        F.map' (n - 1) n (by omega) (by omega) ≫
        eqToHom (congrArg F.obj dupIdx_top.symm) := by
  simp only [dupAt_obj]
  exact whiskerLeft_map' F (dupIdx_prev hp) dupIdx_top

/-- Last-arrow behavior under duplication at the top: the `n → (n + 1)`
(last) arrow of the top-duplicated chain is the transported `n → n` arrow. -/
theorem dupTop_lastArrow {n : ℕ} (F : ComposableArrows C n) :
    ((dupAt (Fin.last n)).obj F).map' n (n + 1) (by omega) (by omega) =
      eqToHom (congrArg F.obj dupTop_prev) ≫
        F.map' n n (by omega) (by omega) ≫
        eqToHom (congrArg F.obj (dupIdx_top (p := Fin.last n)).symm) := by
  simp only [dupAt_obj]
  exact whiskerLeft_map' F dupTop_prev (dupIdx_top (p := Fin.last n))

/-- Last-arrow identity at the top: the `n → (n + 1)` (last) arrow of the
top-duplicated chain is the identity (up to endpoint transport). -/
theorem dupTop_lastArrow_id {n : ℕ} (F : ComposableArrows C n) :
    ((dupAt (Fin.last n)).obj F).map' n (n + 1) (by omega) (by omega) =
      eqToHom (congrArg F.obj dupTop_prev) ≫ 𝟙 _ ≫
        eqToHom (congrArg F.obj (dupIdx_top (p := Fin.last n)).symm) := by
  rw [dupTop_lastArrow, ComposableArrows.map'_self F n]
  rfl

end StrictOmitDup
end CategoryTheory
