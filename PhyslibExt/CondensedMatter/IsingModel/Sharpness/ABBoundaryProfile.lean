/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABMeanfieldGhost
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.BoxMagnetizationRatioLattice

/-!
# Box magnetization with boundary target

The Aizenman–Barsky magnetization of the box `Λ_n ⊂ ℤ^d` with target the ghost or the vertex
boundary of the box, and the two differential inequalities it satisfies.

## i. Overview

`abbMag d n β h` is the probability that the origin of `Λ_n` is joined to the ghost or to `∂Λ_n`,
for unit couplings and field `h`. It is jointly differentiable. The mean-field inequality
`1 - M ≤ β ∂_β M` holds when `φ(S) ≥ 1` for every possible surface (`abbMag_meanfield`, hypothesis
`hphi`), and the Aizenman–Barsky envelope `∂_β M ≤ J₀ U ∂_h M` holds when every site reaches the
target with probability at most `U` (`abbMag_aizenmanBarsky_le_envelope`, hypothesis `htarget`).

## ii. Key results

- `abbTarget` : the ghost together with `∂Λ_n`
- `abbMag` : the box magnetization with boundary target
- `abbMag_meanfield` : the mean-field inequality, conditional on `hphi`
- `abbMag_aizenmanBarsky_le_envelope` : the envelope inequality, conditional on `htarget`

## iii. Table of contents

- A. The target and the magnetization
- B. Differential inequalities

## iv. References

- M. Aizenman, D. J. Barsky, "Sharpness of the phase transition in percolation models",
  Comm. Math. Phys. 108 (1987) 489–526
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace RandomCurrent StatMech.Lattice

/-! ## A. The target and the magnetization -/

/-- The target set in the box `Λ_n` with a ghost: the ghost `none` and the vertex boundary `∂Λ_n`.
-/
def abbTarget (d n : Nat) : Set (Option (sctBox d n)) :=
  {z | z = none ∨ ∃ x : sctBox d n,
    z = some x ∧ (x : Site d) ∈ vertexBoundary d n}

@[simp] lemma none_mem_abbTarget (d n : Nat) :
    none ∈ abbTarget d n := Or.inl rfl

lemma some_mem_abbTarget_iff (d n : Nat) (x : sctBox d n) :
    some x ∈ abbTarget d n ↔ (x : Site d) ∈ vertexBoundary d n := by
  constructor
  · rintro (h | ⟨y, hxy, hy⟩)
    · simp at h
    · exact Option.some.inj hxy ▸ hy
  · intro hx
    exact Or.inr ⟨x, rfl, hx⟩

/-- Unit couplings on the edges of the box. -/
def abbCoupling (d n : Nat) : Sym2 (sctBox d n) -> Real := fun _ => 1

/-- The probability that the origin of `Λ_n` reaches the ghost or `∂Λ_n`. -/
noncomputable def abbMag (d n : Nat) (beta h : Real) : Real :=
  abmgTargetMag (sctBoxGraph d n) (abbCoupling d n)
    (sctBoxOrigin d n) (abbTarget d n) beta h

/-- `φ(S)` for the box problem (edges of the box only). -/
noncomputable def abbPhi (d n : Nat) (beta h : Real)
    (S : Finset (Option (sctBox d n))) : Real :=
  abmgTargetPhi (sctBoxGraph d n) (abbCoupling d n)
    (sctBoxOrigin d n) (abbTarget d n) beta h S

lemma abbMag_differentiableAt_joint (d n : Nat) (beta h : Real) :
    DifferentiableAt Real (Function.uncurry (abbMag d n)) (beta, h) := by
  exact abfa_differentiableAt_prob_joint (sctBoxGraph d n)
    (abbCoupling d n)
    (connEvent (withGhost (sctBoxGraph d n)) Set.univ
      (some (sctBoxOrigin d n)) (abbTarget d n)) beta h

/-! ## B. Differential inequalities -/

/-- The mean-field inequality `1 - M ≤ β ∂_β M` for the box magnetization, if `φ(S) ≥ 1` for every
possible surface `S`. -/
theorem abbMag_meanfield (d n : Nat) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h)
    (hphi : ∀ S : Finset (Option (sctBox d n)),
      some (sctBoxOrigin d n) ∈ S ->
      (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty ->
        1 <= abbPhi d n beta h S) :
    1 - abbMag d n beta h <=
      beta * deriv (fun b => abbMag d n b h) beta := by
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 <= abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  have h := abmg_meanfield_target_finite (sctBoxGraph d n)
    (abbCoupling d n) (sctBoxOrigin d n) (abbTarget d n)
    beta h 1 hJ hbeta hh (by
      intro S hoS hocc
      exact hphi S hoS hocc)
  simpa [abbMag, abbPhi] using h

/-- The Aizenman–Barsky envelope inequality `∂_β M ≤ J₀ U ∂_h M` for the box magnetization, if every
site reaches the target with probability at most `U` and row sums are at most `J₀`. -/
theorem abbMag_aizenmanBarsky_le_envelope
    (d n : Nat) (beta h J0 U : Real)
    (hrow : ∀ x, abcrIncidentCoupling (sctBoxGraph d n)
      (abbCoupling d n) x <= J0)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hU : 0 <= U)
    (htarget : ∀ x : sctBox d n,
      probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) Set.univ
          (some x) (abbTarget d n)) <= U) :
    deriv (fun b => abbMag d n b h) beta <=
      J0 * U * deriv (fun t => abbMag d n beta t) h := by
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 <= abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  exact
    (abfa_aizenmanBarsky_target_le_envelope (sctBoxGraph d n)
      (abbCoupling d n) (sctBoxOrigin d n) (abbTarget d n)
      beta h J0 U (none_mem_abbTarget d n) hJ hrow hbeta hh hU htarget)

end Sharpness
end StatMech
