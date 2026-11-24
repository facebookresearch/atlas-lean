/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.StdSimplexMinimalFace
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Minimal-face regression clients for `StdSimplexMinimalFace`

Concrete checks for `Convexity.StdSimplex.exists_strictly_positive_preimage`,
`Convexity.StdSimplex.unique_preimage_of_injective`, and
`Convexity.StdSimplex.range_eq_support_of_strictly_positive`: a midpoint of edge 0-1
in `Convexity.StdSimplex ℝ (Fin 3)` with support exactly `{0, 1}`, and the vertex at
`0` with support exactly `{0}`. The face map is the explicit inclusion
`Fin.castSucc : Fin 2 → Fin 3` with the strictly positive interior point
`(1 / 2, 1 / 2)`, checked by coordinate equalities through `weights_map_apply` and the
fiber-sum API. No new reusable construction is introduced.

Reuse map (preflight on base `cf64c54ab`):
- `Convexity.StdSimplex.exists_strictly_positive_preimage`,
  `Convexity.StdSimplex.unique_preimage_of_injective`,
  `Convexity.StdSimplex.range_eq_support_of_strictly_positive`,
  `Convexity.StdSimplex.weights_map_apply`, and
  `Convexity.StdSimplex.map_injective`
  (`MathlibExt/Analysis/Convex/StdSimplex.lean`): `reuse`.
- `Convexity.StdSimplex.map`, `Convexity.StdSimplex.single`,
  `Convexity.StdSimplex.weights_single`, and
  `Convexity.StdSimplex.mem_range_map_iff` (pinned Mathlib): `reuse`.
- No `generalize` or `local` entry: this file adds only concrete regression examples.

Nonclaims: no SSet realization quotient, carrier theorem, product, or
model-category result.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibExtTest.Topology.Convenient.StdSimplexMinimalFaceTests

/-- Midpoint of edge 0-1 in `Convexity.StdSimplex ℝ (Fin 3)`. -/
noncomputable def pHalf : Convexity.StdSimplex ℝ (Fin 3) where
  weights :=
    Finsupp.equivFunOnFinite.symm
      (fun i => if i = 0 then (1 / 2 : ℝ) else if i = 1 then (1 / 2 : ℝ) else 0)
  nonneg m := by
    have h : 0 ≤ (if m = 0 then (1 / 2 : ℝ) else if m = 1 then (1 / 2 : ℝ) else 0) := by
      fin_cases m <;> simp
    simpa using h
  total := by
    have h : (∑ i : Fin 3,
        (if i = 0 then (1 / 2 : ℝ) else if i = 1 then (1 / 2 : ℝ) else 0)) = 1 := by
      rw [Fin.sum_univ_three]
      simp
      norm_num
    simpa [Finsupp.sum_fintype] using h

/-- Unfolding equation for the midpoint coordinates. -/
@[simp] theorem pHalf_val (i : Fin 3) : pHalf.weights i =
    (if i = 0 then (1 / 2 : ℝ) else if i = 1 then (1 / 2 : ℝ) else 0) :=
  rfl

/-- The support of `pHalf` is exactly the two endpoints. -/
theorem pHalf_support : { i | pHalf.weights i ≠ 0 } = ({ 0, 1 } : Set (Fin 3)) := by
  ext i
  fin_cases i <;> simp [pHalf_val]

/-- Explicit face inclusion `Fin 2 → Fin 3` covering the support. -/
def f02 : Fin 2 → Fin 3 := Fin.castSucc

theorem hf02 : Function.Injective f02 :=
  Fin.castSucc_injective _

/-- Strictly positive interior point `(1 / 2, 1 / 2)` of the edge. -/
noncomputable def qHalf : Convexity.StdSimplex ℝ (Fin 2) where
  weights := Finsupp.equivFunOnFinite.symm (fun _ => (1 / 2 : ℝ))
  nonneg m := by
    have h : (0 : ℝ) ≤ 1 / 2 := by norm_num
    exact h
  total := by
    have h : (∑ _ : Fin 2, (1 / 2 : ℝ)) = 1 := by
      rw [Fin.sum_univ_two]
      norm_num
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)]

/-- Unfolding equation for the interior-point coordinates. -/
@[simp] theorem qHalf_val (i : Fin 2) : qHalf.weights i = (1 / 2 : ℝ) :=
  rfl

theorem hqHalf_pos : ∀ i, 0 < qHalf.weights i := by
  intro i
  fin_cases i <;> simp [qHalf_val]

/-- The interior point maps to the midpoint under the face inclusion. -/
theorem hMap : qHalf.map f02 = pHalf := by
  have h0 : (qHalf.map f02).weights 0 = pHalf.weights 0 := by
    have hfilter : Finset.univ.filter (fun x : Fin 2 => f02 x = 0) = { 0 } := by
      decide
    have hLHS : (qHalf.map f02).weights 0 = qHalf.weights 0 := by
      rw [Convexity.StdSimplex.weights_map_apply, hfilter,
        Finset.sum_singleton]
    have hRHS : pHalf.weights 0 = qHalf.weights 0 := by
      simp [pHalf_val, qHalf_val]
    rw [hLHS, hRHS]
  have h1 : (qHalf.map f02).weights 1 = pHalf.weights 1 := by
    have hfilter : Finset.univ.filter (fun x : Fin 2 => f02 x = 1) = { 1 } := by
      decide
    have hLHS : (qHalf.map f02).weights 1 = qHalf.weights 1 := by
      rw [Convexity.StdSimplex.weights_map_apply, hfilter,
        Finset.sum_singleton]
    have hRHS : pHalf.weights 1 = qHalf.weights 1 := by
      simp [pHalf_val, qHalf_val]
    rw [hLHS, hRHS]
  have h2 : (qHalf.map f02).weights 2 = pHalf.weights 2 := by
    have hfilter : Finset.univ.filter (fun x : Fin 2 => f02 x = 2) = ∅ := by
      decide
    have hLHS : (qHalf.map f02).weights 2 = 0 := by
      rw [Convexity.StdSimplex.weights_map_apply, hfilter,
        Finset.sum_empty]
    have hRHS : pHalf.weights 2 = 0 := by
      simp [pHalf_val]
    rw [hLHS, hRHS]
  apply Convexity.StdSimplex.ext
  ext y
  fin_cases y
  · exact h0
  · exact h1
  · exact h2

/-- The midpoint factors through a strictly positive interior point. -/
theorem pHalf_has_positive_preimage :
    ∃ (k : ℕ) (f : Fin k → Fin 3),
      Function.Injective f ∧
        ∃ q : Convexity.StdSimplex ℝ (Fin k),
          (∀ i, 0 < q.weights i) ∧ q.map f = pHalf :=
  Convexity.StdSimplex.exists_strictly_positive_preimage pHalf

/-- The interior preimage above the explicit face is unique. -/
theorem qHalf_unique (q' : Convexity.StdSimplex ℝ (Fin 2))
    (h' : q'.map f02 = pHalf) : q' = qHalf :=
  Convexity.StdSimplex.unique_preimage_of_injective hf02 pHalf h' hMap

/-- The explicit face range is the support. -/
theorem f02_range_eq_pHalf_support : Set.range f02 = { i | pHalf.weights i ≠ 0 } :=
  Convexity.StdSimplex.range_eq_support_of_strictly_positive hf02 hqHalf_pos hMap

/-- Vertex at `0` in `Convexity.StdSimplex ℝ (Fin 3)`. -/
noncomputable def v0 : Convexity.StdSimplex ℝ (Fin 3) :=
  Convexity.StdSimplex.single (0 : Fin 3)

/-- The vertex support is the singleton `{0}`. -/
theorem v0_support : { i | v0.weights i ≠ 0 } = ({ 0 } : Set (Fin 3)) := by
  ext i
  fin_cases i <;> simp [v0, Convexity.StdSimplex.weights_single]

/-- The vertex factors through a strictly positive interior point. -/
theorem v0_has_positive_preimage :
    ∃ (k : ℕ) (f : Fin k → Fin 3),
      Function.Injective f ∧
        ∃ q : Convexity.StdSimplex ℝ (Fin k),
          (∀ i, 0 < q.weights i) ∧ q.map f = v0 :=
  Convexity.StdSimplex.exists_strictly_positive_preimage v0

-- Reuse preflight on exact base `e03d93ceeeaf5a96a1f82c23d9d3f7ce89914e42`:
-- `Convexity.StdSimplex.map_surjective_pos` (`StdSimplex.lean`): `reuse` (applied below,
-- never restated). Coordinate equalities reuse `Convexity.StdSimplex.weights_map_apply`
-- in the style of `hMap`. No `generalize`/`local` entry.

/-- Collapsing surjection `Fin 3 → Fin 2` identifying `0` and `1`. -/
def gSurj : Fin 3 → Fin 2 := fun i => if i = 2 then 1 else 0

theorem hgSurj : Function.Surjective gSurj := by
  intro j
  fin_cases j
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩

theorem hgSurj_not_injective : ¬ Function.Injective gSurj := by
  intro h
  have h01 : gSurj 0 = gSurj 1 := by decide
  have hcontra : (0 : Fin 3) = 1 := h h01
  exact (by decide : (0 : Fin 3) ≠ 1) hcontra

/-- Constant strictly positive point of the 2-simplex. -/
noncomputable def qThird : Convexity.StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm (fun _ => (1 / 3 : ℝ))
  nonneg m := by
    have h : (0 : ℝ) ≤ 1 / 3 := by norm_num
    exact h
  total := by
    have h : (∑ _ : Fin 3, (1 / 3 : ℝ)) = 1 := by
      rw [Fin.sum_univ_three]
      norm_num
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)]

/-- Unfolding equation for the constant-point coordinates. -/
@[simp] theorem qThird_val (i : Fin 3) : qThird.weights i = (1 / 3 : ℝ) :=
  rfl

theorem hqThird_pos : ∀ i, 0 < qThird.weights i := by
  intro i
  simp only [qThird_val]
  norm_num

/-- Collapsing-face regression for `map_surjective_pos`: the two fibers have
distinct sums (`2 / 3` vs `1 / 3`), so a transposed fiber sum fails. -/
theorem gSurj_collapse_vals :
    (qThird.map gSurj).weights 0 = 2 / 3 ∧
    (qThird.map gSurj).weights 1 = 1 / 3 ∧
    ∀ j, 0 < (qThird.map gSurj).weights j := by
  have h0 : (qThird.map gSurj).weights 0 = 2 / 3 := by
    have hfilter : Finset.univ.filter (fun x : Fin 3 => gSurj x = 0) = {0, 1} := by
      decide
    rw [Convexity.StdSimplex.weights_map_apply, hfilter,
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
    simp only [qThird_val]
    norm_num
  have h1 : (qThird.map gSurj).weights 1 = 1 / 3 := by
    have hfilter : Finset.univ.filter (fun x : Fin 3 => gSurj x = 1) = {2} := by
      decide
    rw [Convexity.StdSimplex.weights_map_apply, hfilter,
      Finset.sum_singleton, qThird_val]
  exact ⟨h0, h1, Convexity.StdSimplex.map_surjective_pos hgSurj hqThird_pos⟩

-- Reuse preflight on exact base `245c7e03dea92ebab16452812bd63adf2bb7a76f`:
-- `Convexity.StdSimplex.exists_support_face_mono` (`StdSimplexMinimalFace.lean`): `reuse`
-- (applied as black box below, never restated).
-- `Convexity.StdSimplex.range_eq_support_of_strictly_positive` (same file): `reuse`
-- (support-range sanity only).
-- `SimplexCategory.mono_iff_injective` (pinned Mathlib): `reuse`.
-- `Set.ncard_range_of_injective`, `Set.ncard_insert_of_notMem`,
-- `Set.ncard_singleton`, `Nat.card_eq_fintype_card`, `Fintype.card_fin`
-- (pinned Mathlib): `reuse`. No `generalize`/`local` entry.

/-- Point with proper non-prefix support `{0,2}` in `Convexity.StdSimplex ℝ (Fin 3)`. -/
noncomputable def p02 : Convexity.StdSimplex ℝ (Fin 3) where
  weights :=
    Finsupp.equivFunOnFinite.symm
      (fun i => if i = 0 then (1 / 2 : ℝ) else if i = 2 then (1 / 2 : ℝ) else 0)
  nonneg m := by
    have h : 0 ≤ (if m = 0 then (1 / 2 : ℝ) else if m = 2 then (1 / 2 : ℝ) else 0) := by
      fin_cases m <;> simp
    simpa using h
  total := by
    have h : (∑ i : Fin 3,
        (if i = 0 then (1 / 2 : ℝ) else if i = 2 then (1 / 2 : ℝ) else 0)) = 1 := by
      rw [Fin.sum_univ_three]
      simp
      norm_num
    simpa [Finsupp.sum_fintype] using h

/-- Unfolding equation for `p02` coordinates. -/
@[simp] theorem p02_val (i : Fin 3) : p02.weights i =
    (if i = 0 then (1 / 2 : ℝ) else if i = 2 then (1 / 2 : ℝ) else 0) :=
  rfl

/-- The support of `p02` is exactly `{0,2}`: proper and non-prefix. -/
theorem p02_support : { i | p02.weights i ≠ 0 } = ({ 0, 2 } : Set (Fin 3)) := by
  ext i
  fin_cases i <;> simp [p02_val]

/-- Black-box regression for `exists_support_face_mono` on the non-prefix point. -/
theorem p02_has_support_face_mono :
    ∃ (k : ℕ) (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk 2),
      CategoryTheory.Mono φ ∧
        ∃ q : Convexity.StdSimplex ℝ (Fin (k + 1)), (∀ i, 0 < q.weights i) ∧
          q.map (fun i => φ.toOrderHom i) = p02 :=
  Convexity.StdSimplex.exists_support_face_mono p02

/-- The returned face is injective: simplex-category mono packaging check. -/
theorem p02_face_injective :
    ∃ (k : ℕ) (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk 2),
      Function.Injective (fun i => φ.toOrderHom i) ∧
        ∃ q : Convexity.StdSimplex ℝ (Fin (k + 1)), (∀ i, 0 < q.weights i) ∧
          q.map (fun i => φ.toOrderHom i) = p02 := by
  obtain ⟨k, φ, hMono, q, hPos, hMap⟩ :=
    Convexity.StdSimplex.exists_support_face_mono p02
  exact ⟨k, φ, SimplexCategory.mono_iff_injective.mp hMono, q, hPos, hMap⟩

/-- The returned face range is the non-prefix support: positivity and map check. -/
theorem p02_face_support :
    ∃ (k : ℕ) (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk 2),
      Function.Injective (fun i => φ.toOrderHom i) ∧
        Set.range (fun i => φ.toOrderHom i) = ({ 0, 2 } : Set (Fin 3)) := by
  obtain ⟨k, φ, hMono, q, hPos, hMap⟩ :=
    Convexity.StdSimplex.exists_support_face_mono p02
  have hInj : Function.Injective (fun i => φ.toOrderHom i) :=
    SimplexCategory.mono_iff_injective.mp hMono
  have hRange :=
    Convexity.StdSimplex.range_eq_support_of_strictly_positive hInj hPos hMap
  rw [p02_support] at hRange
  exact ⟨k, φ, hInj, hRange⟩

/-- Support-cardinality signal: the non-prefix `{0,2}` point forces `k = 1`. -/
theorem p02_face_card :
    ∀ (k : ℕ) (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk 2)
      (q : Convexity.StdSimplex ℝ (Fin (k + 1))),
      CategoryTheory.Mono φ → (∀ i, 0 < q.weights i) →
      q.map (fun i => φ.toOrderHom i) = p02 → k = 1 := by
  intro k φ q hMono hPos hMap
  have hInj : Function.Injective (fun i => φ.toOrderHom i) :=
    SimplexCategory.mono_iff_injective.mp hMono
  have hRange :=
    Convexity.StdSimplex.range_eq_support_of_strictly_positive hInj hPos hMap
  rw [p02_support] at hRange
  have hNcard : (Set.range (fun i => φ.toOrderHom i)).ncard = 2 := by
    rw [hRange, Set.ncard_insert_of_notMem (by decide), Set.ncard_singleton]
  have hNcard2 : (Set.range (fun i => φ.toOrderHom i)).ncard = k + 1 := by
    rw [Set.ncard_range_of_injective hInj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hEq : k + 1 = 2 := hNcard2.symm.trans hNcard
  omega

#print axioms p02_face_support
#print axioms p02_face_card

#check @Convexity.StdSimplex.exists_strictly_positive_preimage
#check @Convexity.StdSimplex.unique_preimage_of_injective
#check @Convexity.StdSimplex.range_eq_support_of_strictly_positive
#print axioms hMap
#print axioms pHalf_support
#print axioms v0_support
#print axioms f02_range_eq_pHalf_support

end MathlibExtTest.Topology.Convenient.StdSimplexMinimalFaceTests
