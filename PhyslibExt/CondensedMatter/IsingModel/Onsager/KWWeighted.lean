/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWPhaseLoops
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusDecoration

/-!

# Kac-Ward matrices with edge-dependent weights

The torus Kac-Ward matrix with an independent weight on every edge, with and without boundary
phases.

## i. Overview

Replacing the uniform activity `x` by an arbitrary weight on each torus edge gives the weighted
Kac-Ward matrix: the entry for a step along dart `d₁` followed by `d₂` is the weight of the edge of
`d₁` times the turn weight. With constant weight `x` it is the usual Kac-Ward matrix. Loop weights
become products of edge weights times turning phases (times boundary phases in the twisted version).
Edge-dependent weights allow the Kac-Ward identity to be proved coefficient by coefficient as an
identity of multivariate series.

## ii. Key results

- `ons_KWmatWeighted` : the edge-weighted Kac-Ward matrix
- `ons_KWmatWeightedPhase` : its twisted version
- `ons_loopWeight_KWmatWeighted_eq` : its loop weights

## iii. Table of contents

- A. The weighted matrix
- B. Boundary phases

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. The weighted matrix -/

/-- The edge-weighted Kac-Ward matrix: the entry from `d₁` to `d₂` is the weight of the torus edge
of `d₁` times the turn weight, when `d₂` starts at the head of `d₁`. -/
noncomputable def ons_KWmatWeighted (L : ℕ)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 =>
    if d2.1 = ons_dirStep L d1.2 d1.1 then
      weight (ons_portEdge L d1) * ons_turnW omega d1.2 d2.2
    else 0

lemma ons_KWmatWeighted_const (L : ℕ) (x omega : ℂ) :
    ons_KWmatWeighted L (fun _ => x) omega = ons_KWmat L x omega := by
  ext d2 d1
  simp only [ons_KWmatWeighted, ons_KWmat]

lemma ons_loopWeight_KWmatWeighted_eq
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega : ℂ)
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_loopWeight (ons_KWmatWeighted L weight omega) d =
      (∏ k, weight (ons_portEdge L (d k))) *
        ∏ k, ons_turnW omega (d (k + 1)).2 (d k).2 := by
  unfold ons_loopWeight ons_KWmatWeighted
  have hfac : ∀ k : Fin n,
      (if (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 then
          weight (ons_portEdge L (d (k + 1))) *
            ons_turnW omega (d (k + 1)).2 (d k).2
        else 0) =
      weight (ons_portEdge L (d (k + 1))) *
        ons_turnW omega (d (k + 1)).2 (d k).2 := by
    intro k
    rw [ite_eq_left (hvalid k)]
  rw [Finset.prod_congr rfl (fun k _ => hfac k),
    Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => weight (ons_portEdge L (d k)))

/-! ## B. Boundary phases -/

/-- The edge-weighted Kac-Ward matrix with each step multiplied by its direction phase. -/
noncomputable def ons_KWmatWeightedPhase (L : ℕ)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 =>
    ons_dirPhase u v d1.2 * ons_KWmatWeighted L weight omega d2 d1

lemma ons_KWmatWeightedPhase_const (L : ℕ) (x omega u v : ℂ) :
    ons_KWmatWeightedPhase L (fun _ => x) omega u v =
      ons_KWmatPhase L x omega u v := by
  ext d2 d1
  simp only [ons_KWmatWeightedPhase, ons_KWmatWeighted_const,
    ons_KWmatPhase]

lemma ons_loopWeight_KWmatWeightedPhase
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega u v) d =
      (∏ k, ons_dirPhase u v (d k).2) *
        ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
  unfold ons_loopWeight ons_KWmatWeightedPhase
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n))
    (fun k => ons_dirPhase u v (d k).2)

end StatMech.Onsager
