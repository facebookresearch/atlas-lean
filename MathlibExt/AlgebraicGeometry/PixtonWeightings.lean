/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import MathlibExt.AlgebraicGeometry.UniversalCurveStability

@[expose] public noncomputable section

/-!
# Pixton modular graph coefficients

Weightings are functions on the actual finite half-edge set satisfying
edge oppositeness and vertex balance with the fixed leg weights.
The graph automorphism cardinal is the cardinal of the actual graph
isomorphism type. The normalized sum divides by r to the graph Betti
number and by that cardinal. Only positive moduli are summed.

Source: Janda--Pandharipande--Pixton--Zvonkine, Double ramification
cycles on the moduli spaces of curves, Appendix A.
-/

namespace MathlibExt.AlgebraicGeometry.PixtonWeightings

open Finset
open scoped BigOperators
open _root_.MathlibExt.AlgebraicGeometry.UniversalCurveStability

/-- Actual finite data of a graph isomorphism. -/
def isoCode {g n : ℕ} {G H : StableGraph g n} (f : GraphIso G H) :=
  (f.vertex, f.edge, f.branch)

/-- All graph-isomorphism data are determined by their permutations. -/
theorem isoCode_injective {g n : ℕ} (G H : StableGraph g n) :
    Function.Injective (isoCode (G := G) (H := H)) := by
  intro f h eq
  cases f
  cases h
  simp only [isoCode, Prod.mk.injEq] at eq
  rcases eq with ⟨hv, he, hb⟩
  cases hv
  cases he
  cases hb
  rfl

instance graphIsoFintype {g n : ℕ} (G H : StableGraph g n) : Fintype (GraphIso G H) := by
  classical
  exact Fintype.ofInjective isoCode (isoCode_injective G H)

/-- The actual identity automorphism. -/
def identityIso {g n : ℕ} (G : StableGraph g n) : GraphIso G G where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  branch _ := Equiv.refl _
  endpoint _ _ := rfl
  genus _ := rfl
  marking _ := rfl

/-- Automorphism factor, on the actual labeled genus/marking graph. -/
def automorphismOrder {g n : ℕ} (G : StableGraph g n) : ℕ :=
  Fintype.card (GraphIso G G)

/-- The automorphism denominator is positive. -/
theorem automorphismOrder_pos {g n : ℕ} (G : StableGraph g n) :
    0 < automorphismOrder G := by
  let : Nonempty (GraphIso G G) := ⟨identityIso G⟩
  exact Fintype.card_pos_iff.mpr inferInstance

/-- The connected graph's first Betti number. -/
def firstBetti {g n : ℕ} (G : StableGraph g n) : ℕ :=
  G.edges + 1 - G.vertices

/-- Modular weighting conditions on exactly the finite half-edge set. -/
def Weighting {g n : ℕ} (G : StableGraph g n) (a : Fin n → ℤ)
    (r : ℕ) [NeZero r] :=
  {w : Fin G.edges × Fin 2 → ZMod r //
    (∀ e, w (e, 0) + w (e, 1) = 0) ∧
    ∀ v : Fin G.vertices,
      (∑ h : Fin G.edges × Fin 2, if G.endpoint h.1 h.2 = v then w h else 0) +
        (∑ i : Fin n, if G.marking i = v then (a i : ZMod r) else 0) = 0}

instance weightingFintype {g n : ℕ} (G : StableGraph g n) (a : Fin n → ℤ)
    (r : ℕ) [NeZero r] : Fintype (Weighting G a r) := by
  classical
  unfold Weighting
  infer_instance

/-- One graph coefficient of the modular weighting sum, including both normalizations. -/
def normalizedSum {g n : ℕ} (G : StableGraph g n) (a : Fin n → ℤ)
    (k : Fin G.edges → ℕ) (r : ℕ) (hr : 0 < r) : ℚ := by
  classical
  letI : NeZero r := ⟨ne_of_gt hr⟩
  exact
    (∑ w : Weighting G a r,
      ∏ e : Fin G.edges, ((w.val (e, 0)).val * (w.val (e, 1)).val : ℚ) ^ k e) /
        ((r : ℚ) ^ firstBetti G * automorphismOrder G)

/-- Constant term of an explicit regularization polynomial. -/
def regularizedConstant (p : Polynomial ℚ) : ℚ := p.coeff 0

/-- Eventual polynomial agreement determines the polynomial uniquely. -/
theorem eventualPolynomial_unique (p q : Polynomial ℚ) (N : ℕ)
    (h : ∀ r : ℕ, N ≤ r → p.eval (r : ℚ) = q.eval (r : ℚ)) : p = q := by
  have hi : Function.Injective (fun r : ℕ ↦ (N : ℚ) + r) := by
    intro a b eq
    simpa using (add_left_cancel eq)
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective hi).mono ?_
  rintro x ⟨r, rfl⟩
  simpa only [Set.mem_ofPred_eq, Nat.cast_add] using h (N + r) (Nat.le_add_right N r)

end MathlibExt.AlgebraicGeometry.PixtonWeightings
