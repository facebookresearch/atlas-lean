/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.PlanarNetworkTotalPositivity
import Mathlib.Basic.Real.Basic

/-!
# Tests for the weighted Lindström–Gessel–Viennot lemma and planar networks

A non-degenerate instance of the hypotheses: the one-edge network `0 → 1` on `Fin 2`, with
source `0`, sink `1` and edge weight `w`. Its unique path `[0, 1]` has weight `w`.
-/

namespace MathlibExtTest.LinearAlgebra.Matrix.PlanarNetworkTotalPositivity

open MetaMathlibExt

/-- The paths of the one-edge network are exactly `[0, 1]`. -/
lemma oneEdge_path (p : List (Fin 2)) : p ∈ ({[0, 1]} : Finset (List (Fin 2))) ↔
    (p.head? = some 0 ∧ p.getLast? = some 1 ∧ p.IsChain (fun u v => u < v)) := by
  constructor
  · intro h
    rw [Finset.mem_singleton] at h
    subst h
    refine ⟨rfl, rfl, ?_⟩
    simp
  · rintro ⟨hh, hl, hc⟩
    rw [Finset.mem_singleton]
    match p, hh, hl, hc with
    | [a], hh, hl, _ => simp at hh hl; rw [hh] at hl; exact absurd hl (by decide)
    | [a, b], hh, hl, _ => simp at hh hl; rw [hh, hl]
    | a :: b :: c :: l, _, _, hc =>
      simp only [List.isChain_cons_cons] at hc
      have h1 := Fin.lt_def.mp hc.1
      have h2 := Fin.lt_def.mp hc.2.1
      have h3 := c.isLt
      omega

/-- The weighted lemma on the one-edge network: `det [w] = w`. -/
example (w : ℝ) :
    ∑ F ∈ ({fun _ => [0, 1]} : Finset (Fin 1 → List (Fin 2))),
        ∏ i, lgvPathWeight (fun _ _ => w) (F i) =
      Matrix.det (fun (_ _ : Fin 1) => w) := by
  refine lindstrom_gessel_viennot_weighted 1 (fun u v => u < v) (fun _ => 0) (fun _ => 1)
    Fin.val (fun _ _ h => h) (fun _ _ => {[0, 1]}) (fun _ _ p => oneEdge_path p) _ _
    (fun _ _ => by simp [lgvPathWeight]) (fun _ _ _ _ h => absurd h (by omega)) _ ?_
  intro F
  simp only [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨fun _ => rfl, fun i j h => absurd (Subsingleton.elim i j) h⟩
  · rintro ⟨h, -⟩
    funext i
    exact h i

/-- A nonnegative edge weight gives a totally nonnegative weight matrix. -/
example (w : ℝ) (hw : 0 ≤ w) :
    (Matrix.of fun (_i _j : Fin 1) => ∑ p ∈ ({[0, 1]} : Finset (List (Fin 2))),
      lgvPathWeight (fun _ _ => w) p).IsTotallyNonneg :=
  planarNetwork_isTotallyNonneg 1 (fun u v => u < v) (fun _ => 0) (fun _ => 1) Fin.val
    (fun _ _ h => h) (fun _ _ => {[0, 1]}) (fun _ _ p => oneEdge_path p) _ (fun _ _ => hw)
    (fun _ _ _ _ h => absurd h (by omega))

/-- A positive edge weight on the (totally connected) one-edge network gives a matrix with
positive minors. -/
example (w : ℝ) (hw : 0 < w) :
    Matrix.HasPositiveMinors (Matrix.of fun (_i _j : Fin 1) =>
      ∑ p ∈ ({[0, 1]} : Finset (List (Fin 2))), lgvPathWeight (fun _ _ => w) p) := by
  refine planarNetwork_hasPositiveMinors 1 (fun u v => u < v) (fun _ => 0) (fun _ => 1) Fin.val
    (fun _ _ h => h) (fun _ _ => {[0, 1]}) (fun _ _ p => oneEdge_path p) _ (fun _ _ => hw)
    (fun _ _ _ _ h => absurd h (by omega)) ?_
  intro k r c _ _
  refine ⟨fun _ => [0, 1], fun _ => Finset.mem_singleton_self _, fun a b hab => ?_⟩
  have hk : k ≤ 1 := by simpa using Fintype.card_le_of_injective r ‹StrictMono r›.injective
  exact absurd (Fin.ext (by omega)) hab

end MathlibExtTest.LinearAlgebra.Matrix.PlanarNetworkTotalPositivity
