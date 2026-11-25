/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import MathlibExt.LinearAlgebra.Matrix.RoucheCapelli
public import PhyslibExt.Mechanics.HarmonicMechanics
public import PhyslibExt.Mechanics.TrussEquilibrium
import MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Three-dimensional wrench origin transport and truss solvability

The moment of a finite three-dimensional load system about a reference point, the wrench it
defines, and the change of reference point; and when the force-only equilibrium of a pin-jointed
planar truss has a solution, and when that solution is unique.

## i. Overview

A finite load system in one inertial frame: forces `F i` applied at the points `r i` and free
couples `C i`, for `i` in a finite index type. Its resultant is `R = ∑ i, F i`, the existing
`PhyslibExt.Mechanics.HarmonicMechanics.resultantForce`, and its moment about a reference point
`O` is `M_O = ∑ i, ((r i - O) ⨯₃ F i + C i)`, the lever arm running from `O` to the point of
application. The pair `(R, M_O)` is the wrench of the system about `O`.

Model inputs (hypotheses of the module):

* all points, forces and couples are components in one inertial frame;
* a free couple contributes its moment about every reference point;
* lengths and forces keep their own units: positions carry a length factor, forces a force
  factor, and couples and moments their product;
* no elasticity: the loads are given, and no deformation or constitutive law enters.

Moving the reference point from `O` to `O'` keeps the resultant and adds `(O - O') ⨯₃ R` to the
moment. The moment is therefore the same about every point when the resultant vanishes, and some
reference point changes it when the resultant does not.

The planar projection concerns the forces alone, with the free couples discarded: the planar
moment `PhyslibExt.Mechanics.HarmonicMechanics.moment2D` carries no couples. For the forces,
projection onto the plane of the first two axes keeps only the third component of the moment about
the origin, which is the planar moment of the projected forces; its shift law is
`PhyslibExt.Mechanics.HarmonicMechanics.moment2D_shift`. A force normal to that plane can carry a
nonzero moment that the projection loses.

Truss equilibrium (section E) uses the planar truss of `PhyslibExt.Mechanics.TrussEquilibrium`,
given in its current configuration: joints at the positions `r`, straight two-force members from
`a e` to `b e` with axial forces `N e` (tension positive, ideal pins), support reactions `ρ s`
acting at the joint `sj s` along the given direction `sd s`, and loads `f` at the joint coordinates
only. Joint balance `JointBalance r a b sj sd f N ρ` is the matrix equation
`equilibriumMatrix r a b sj sd *ᵥ Sum.elim N ρ = f` (`jointBalance_iff_mulVec`): for `j` joints, `m`
members and `r` reaction components, `2 j` equations in `m + r` unknowns. With the current geometry
the balance is exact; substituting the reference geometry needs small displacements. When
`m + r = 2 j` and the equilibrium matrix has injective `mulVec`, every load has exactly one balance
(`Matrix.exists_unique_mulVec_eq` after renumbering the equations). In general a load has a balance
exactly when the equilibrium matrix and the augmented matrix `(A | f)` have equal rank
(`MetaMathlibExt.rouche_capelli`). Injectivity alone (full column rank) gives at most one balance,
not one for every load, and it rules out members with coincident endpoints: their unit column is
zero, so a unit force in such a member would balance zero loads, a spurious state of self-stress.
The count `m + r = 2 j` alone is not enough. A collinear chain pinned at both ends has a state of
self-stress (member forces and reactions that balance zero loads), so the balance of an axial load
at the middle joint is not unique but a one-parameter family. Its square equilibrium matrix is then
not surjective either: a transverse load at the middle joint has no balance, because neither member
has a transverse component there; that joint can move transversally without stretching either member
to first order, an infinitesimal mechanism.

Non-goals: equilibrium of a general constrained rigid body, distributed loads, the central axis of
a wrench, and any empirical adequacy or system safety claim.

## ii. Key results

- `momentAbout_eq_add_cross`, `wrenchAbout_eq_transport` : the origin transport
  `M_O' = M_O + (O - O') ⨯₃ R`, for the moment and for the wrench record.
- `momentAbout_eq_of_resultantForce_eq_zero`, `exists_momentAbout_ne_of_resultantForce_ne_zero` :
  the moment is origin independent exactly when the resultant vanishes.
- `wrenchAbout_smul` : with positions and the reference point scaled by a length factor, forces
  by a force factor and couples by the product of the two, the resultant scales with the force
  factor and the moment with the product.
- `moment2D_planarPart` : for the forces alone, free couples discarded, the planar moment of the
  projected forces is the third component of their moment about the origin.
- `jointBalance_existsUnique_of_injective` : with `m + r = 2 j` and an injective equilibrium
  matrix, every joint load has exactly one balance.
- `exists_jointBalance_iff_rank` : a joint load has a balance exactly when the equilibrium matrix
  and the augmented matrix have equal rank.
- `jointBalance_unique_of_injective`, `endpoints_ne_of_injective` : an injective equilibrium
  matrix gives at most one balance and noncoincident member endpoints.

## iii. Table of contents

- A. Resultant, moment and wrench of a finite load system
- B. Origin transport and origin invariance
- C. Units
- D. Planar projection of the forces
- E. Truss equilibrium: solvability and uniqueness

## iv. References

- F. P. Beer, E. R. Johnston Jr. and D. F. Mazurek, *Vector Mechanics for Engineers: Statics*,
  chapter 3 (equivalent systems of forces; moving a force-couple system to another point).
- J. L. Meriam and L. G. Kraige, *Engineering Mechanics: Statics*, chapter 2 (moments and
  couples in three dimensions; resultants and the wrench).
- F. P. Beer, E. R. Johnston Jr. and D. F. Mazurek, *Vector Mechanics for Engineers: Statics*,
  chapter 6 (method of joints; determinate, indeterminate and improperly constrained trusses).
- S. Pellegrino and C. R. Calladine, *Matrix analysis of statically and kinematically
  indeterminate frameworks*, International Journal of Solids and Structures 22 (1986):
  equilibrium matrix, states of self-stress and mechanisms.
- `PhyslibExt.Mechanics.TrussEquilibrium` (truss equilibrium matrix and joint balance),
  `MetaMathlibExt.rouche_capelli` and `Matrix.exists_unique_mulVec_eq`.
-/

@[expose] public section

open scoped Matrix

namespace Mechanics.EngineeringStatics

open PhyslibExt.Mechanics.HarmonicMechanics

variable {ι : Type*} [Fintype ι]

/-! ## A. Resultant, moment and wrench of a finite load system -/

/-- Moment about the reference point `O` of the forces `F i` applied at the points `r i` and the
free couples `C i`: `M_O = ∑ i, ((r i - O) ⨯₃ F i + C i)`. All vectors are components in one
inertial frame. -/
noncomputable def momentAbout (r F C : ι → Fin 3 → ℝ) (O : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∑ i, ((r i - O) ⨯₃ F i + C i)

/-- A three-dimensional wrench: a resultant force and a moment about a reference point. The
reference point is not part of the pair. -/
structure Wrench where
  /-- The resultant force. -/
  force : Fin 3 → ℝ
  /-- The moment about the reference point. -/
  moment : Fin 3 → ℝ

/-- The wrench of the load system about `O`: the resultant `R = ∑ i, F i` and the moment
`M_O`. -/
noncomputable def wrenchAbout (r F C : ι → Fin 3 → ℝ) (O : Fin 3 → ℝ) : Wrench :=
  ⟨resultantForce F, momentAbout r F C O⟩

/-- Transport of a wrench from the reference point `O` to the reference point `O'`: the force is
kept and the moment gains `(O - O') ⨯₃ force`. -/
noncomputable def Wrench.transport (W : Wrench) (O O' : Fin 3 → ℝ) : Wrench :=
  ⟨W.force, W.moment + (O - O') ⨯₃ W.force⟩

/-! ## B. Origin transport and origin invariance -/

/-- Origin transport of the moment: `M_O' = M_O + (O - O') ⨯₃ R`. -/
lemma momentAbout_eq_add_cross (r F C : ι → Fin 3 → ℝ) (O O' : Fin 3 → ℝ) :
    momentAbout r F C O' = momentAbout r F C O + (O - O') ⨯₃ resultantForce F := by
  unfold momentAbout resultantForce
  have hadd : ∀ a b c : Fin 3 → ℝ, (a + b) ⨯₃ c = a ⨯₃ c + b ⨯₃ c := fun a b c => by
    rw [map_add, LinearMap.add_apply]
  have hdecomp : ∀ i, r i - O' = (r i - O) + (O - O') := fun i => by abel
  have hrearr : ∀ i : ι, (r i - O) ⨯₃ F i + (O - O') ⨯₃ F i + C i
      = ((r i - O) ⨯₃ F i + C i) + (O - O') ⨯₃ F i := fun i => by abel
  simp_rw [hdecomp, hadd, hrearr, Finset.sum_add_distrib]
  congr 1
  exact (map_sum _ _ _).symm

/-- The wrench about `O'` is the wrench about `O` transported to `O'`. -/
lemma wrenchAbout_eq_transport (r F C : ι → Fin 3 → ℝ) (O O' : Fin 3 → ℝ) :
    wrenchAbout r F C O' = (wrenchAbout r F C O).transport O O' := by
  have h1 : wrenchAbout r F C O' = ⟨resultantForce F, momentAbout r F C O'⟩ := rfl
  have h2 : wrenchAbout r F C O = ⟨resultantForce F, momentAbout r F C O⟩ := rfl
  have h3 : (⟨resultantForce F, momentAbout r F C O⟩ : Wrench).transport O O'
      = ⟨resultantForce F, momentAbout r F C O + (O - O') ⨯₃ resultantForce F⟩ := rfl
  rw [h1, h2, h3, momentAbout_eq_add_cross]

/-- Origin invariance: when the resultant vanishes, the moment is the same about every
reference point. -/
lemma momentAbout_eq_of_resultantForce_eq_zero {r F C : ι → Fin 3 → ℝ}
    (hR : resultantForce F = 0) (O O' : Fin 3 → ℝ) :
    momentAbout r F C O' = momentAbout r F C O := by
  rw [momentAbout_eq_add_cross, hR, map_zero, add_zero]

/-- A nonzero resultant changes the moment: some reference point gives a different moment. -/
lemma exists_momentAbout_ne_of_resultantForce_ne_zero {r F C : ι → Fin 3 → ℝ}
    (hR : resultantForce F ≠ 0) (O : Fin 3 → ℝ) :
    ∃ O' : Fin 3 → ℝ, momentAbout r F C O' ≠ momentAbout r F C O := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hR
  rw [Pi.zero_apply] at hj
  fin_cases j
  · refine ⟨O - ![0, 1, 0], ?_⟩
    rw [momentAbout_eq_add_cross, sub_sub_cancel]
    intro hcon
    rw [add_eq_left] at hcon
    rw [show (![0, 1, 0] : Fin 3 → ℝ) ⨯₃ resultantForce F
        = ![resultantForce F 2, 0, -resultantForce F 0] from by simp [cross_apply]] at hcon
    have h2 := congrFun hcon 2
    apply hj
    simpa using h2
  · refine ⟨O - ![0, 0, 1], ?_⟩
    rw [momentAbout_eq_add_cross, sub_sub_cancel]
    intro hcon
    rw [add_eq_left] at hcon
    rw [show (![0, 0, 1] : Fin 3 → ℝ) ⨯₃ resultantForce F
        = ![-resultantForce F 1, resultantForce F 0, 0] from by simp [cross_apply]] at hcon
    have h0 := congrFun hcon 0
    apply hj
    simpa using h0
  · refine ⟨O - ![1, 0, 0], ?_⟩
    rw [momentAbout_eq_add_cross, sub_sub_cancel]
    intro hcon
    rw [add_eq_left] at hcon
    rw [show (![1, 0, 0] : Fin 3 → ℝ) ⨯₃ resultantForce F
        = ![0, -resultantForce F 2, resultantForce F 1] from by simp [cross_apply]] at hcon
    have h1 := congrFun hcon 1
    apply hj
    simpa using h1

/-! ## C. Units -/

/-- Physical dimensions are retained: with lengths scaled by `ℓ`, forces by `f`, and couples by
`ℓ * f`, the resultant scales by `f` and the moment about the scaled reference point by
`ℓ * f`. The identity holds for all real `ℓ` and `f`; read as a change of units, `ℓ > 0` and
`f > 0` are the length and force factors. -/
lemma wrenchAbout_smul (ℓ f : ℝ) (r F C : ι → Fin 3 → ℝ) (O : Fin 3 → ℝ) :
    wrenchAbout (fun i => ℓ • r i) (fun i => f • F i) (fun i => (ℓ * f) • C i) (ℓ • O) =
      ⟨f • resultantForce F, (ℓ * f) • momentAbout r F C O⟩ := by
  have hs : ∀ u v : Fin 3 → ℝ, (ℓ • u) ⨯₃ (f • v) = (ℓ * f) • (u ⨯₃ v) := by
    intro u v
    rw [map_smul crossProduct ℓ u, LinearMap.smul_apply, map_smul (crossProduct u) f v,
      smul_smul]
  have hW : wrenchAbout (fun i => ℓ • r i) (fun i => f • F i) (fun i => (ℓ * f) • C i) (ℓ • O)
      = ⟨resultantForce (fun i => f • F i),
        momentAbout (fun i => ℓ • r i) (fun i => f • F i) (fun i => (ℓ * f) • C i)
          (ℓ • O)⟩ := rfl
  rw [hW]
  congr 1
  · exact Finset.smul_sum.symm
  · unfold momentAbout
    simp_rw [← smul_sub, hs, ← smul_add]
    exact Finset.smul_sum.symm

/-! ## D. Planar projection of the forces -/

/-- Components on the plane of the first two axes. -/
def planarPart (v : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![v 0, v 1]

/-- Force-only planar projection: the planar moment of the projected forces about the origin is the
third component of the moment about the origin of the forces alone, with the free couples discarded
(`C = 0`), since the planar moment carries no couples. -/
lemma moment2D_planarPart (r F : ι → Fin 3 → ℝ) :
    moment2D (fun i => planarPart (r i)) (fun i => planarPart (F i)) =
      momentAbout r F (fun _ => 0) 0 2 := by
  unfold moment2D momentAbout planarPart
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [cross_apply]

/-! ## E. Truss equilibrium: solvability and uniqueness -/

section TrussSolvability

open Matrix Mechanics.TrussCompatibility Mechanics.TrussEquilibrium

/-- **Square and injective.** If `Fintype.card M + Fintype.card R = 2 * Fintype.card J` (member
forces plus reaction components equal twice the joints) and the equilibrium matrix has injective
`mulVec`, every joint load `f` has exactly one balancing pair of member forces and reactions. -/
lemma jointBalance_existsUnique_of_injective {J M R : Type*} [Fintype J] [DecidableEq J]
    [Fintype M] [Fintype R] (r : J → (Fin 2 → ℝ)) (a b : M → J) (sj : R → J)
    (sd : R → (Fin 2 → ℝ)) (hsq : Fintype.card M + Fintype.card R = 2 * Fintype.card J)
    (hinj : Function.Injective (equilibriumMatrix r a b sj sd).mulVec) (f : J × Fin 2 → ℝ) :
    ∃! p : (M → ℝ) × (R → ℝ), JointBalance r a b sj sd f p.1 p.2 := by
  set A := equilibriumMatrix r a b sj sd with hAdef
  have hcard : Fintype.card (J × Fin 2) = Fintype.card (M ⊕ R) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, hsq]
    ring
  set σ : (J × Fin 2) ≃ (M ⊕ R) := Fintype.equivOfCardEq hcard
  have hA' : ∀ y, A.submatrix id σ *ᵥ y = A *ᵥ (y ∘ σ.symm) := fun y => by
    rw [Matrix.submatrix_mulVec_equiv]
    rfl
  have hinj' : Function.Injective (A.submatrix id σ).mulVec := by
    intro y₁ y₂ h
    change A.submatrix id σ *ᵥ y₁ = A.submatrix id σ *ᵥ y₂ at h
    rw [hA', hA'] at h
    have h2 := hinj h
    funext c
    have := congrFun h2 (σ c)
    simpa using this
  obtain ⟨y, hy, huniq⟩ := Matrix.exists_unique_mulVec_eq hinj' f
  have hx₀ : A *ᵥ (y ∘ σ.symm) = f := by
    rw [← hA']
    exact hy
  have huniqA : ∀ x, A *ᵥ x = f → x = y ∘ σ.symm := fun x hx => by
    have hcomp : (x ∘ σ) ∘ σ.symm = x := by
      funext j
      simp
    have hxσ : x ∘ σ = y := huniq (x ∘ σ) (show A.submatrix id σ *ᵥ (x ∘ σ) = f by
      rw [hA', hcomp]
      exact hx)
    funext j
    have := congrFun hxσ (σ.symm j)
    simpa using this
  refine ⟨((y ∘ σ.symm) ∘ Sum.inl, (y ∘ σ.symm) ∘ Sum.inr), ?_, ?_⟩
  · change JointBalance r a b sj sd f ((y ∘ σ.symm) ∘ Sum.inl) ((y ∘ σ.symm) ∘ Sum.inr)
    rw [jointBalance_iff_mulVec, Sum.elim_comp_inl_inr]
    exact hx₀
  · rintro ⟨N, ρ⟩ h
    have hx := huniqA _ ((jointBalance_iff_mulVec r a b sj sd f N ρ).1 h)
    refine Prod.ext (funext fun m => ?_) (funext fun s => ?_)
    · simpa using congrFun hx (Sum.inl m)
    · simpa using congrFun hx (Sum.inr s)

set_option linter.unusedFintypeInType false in
/-- **Rank test.** A joint load `f` has a balancing pair exactly when the equilibrium matrix and
the augmented matrix `(A | f)` have equal rank. -/
lemma exists_jointBalance_iff_rank {J M R : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [Fintype R] (r : J → (Fin 2 → ℝ)) (a b : M → J) (sj : R → J) (sd : R → (Fin 2 → ℝ))
    (f : J × Fin 2 → ℝ) :
    (∃ (N : M → ℝ) (ρ : R → ℝ), JointBalance r a b sj sd f N ρ) ↔
      (equilibriumMatrix r a b sj sd).rank =
        (Matrix.of (fun i => Sum.elim (equilibriumMatrix r a b sj sd i) (fun _ : Fin 1 => f i)) :
          Matrix (J × Fin 2) ((M ⊕ R) ⊕ Fin 1) ℝ).rank := by
  rw [← MetaMathlibExt.rouche_capelli]
  constructor
  · rintro ⟨N, ρ, h⟩
    exact ⟨Sum.elim N ρ, (jointBalance_iff_mulVec r a b sj sd f N ρ).1 h⟩
  · rintro ⟨x, hx⟩
    refine ⟨x ∘ Sum.inl, x ∘ Sum.inr, ?_⟩
    rw [jointBalance_iff_mulVec, Sum.elim_comp_inl_inr]
    exact hx

set_option linter.unusedFintypeInType false in
/-- **At most one balance.** If the equilibrium matrix has injective `mulVec` (full column rank),
two balancing pairs for the same loads coincide; existence for every load needs more. -/
lemma jointBalance_unique_of_injective {J M R : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [Fintype R] {r : J → (Fin 2 → ℝ)} {a b : M → J} {sj : R → J} {sd : R → (Fin 2 → ℝ)}
    (hinj : Function.Injective (equilibriumMatrix r a b sj sd).mulVec) {f : J × Fin 2 → ℝ}
    {N N' : M → ℝ} {ρ ρ' : R → ℝ} (h : JointBalance r a b sj sd f N ρ)
    (h' : JointBalance r a b sj sd f N' ρ') : N = N' ∧ ρ = ρ' := by
  have hx := hinj (((jointBalance_iff_mulVec r a b sj sd f N ρ).1 h).trans
    ((jointBalance_iff_mulVec r a b sj sd f N' ρ').1 h').symm)
  exact ⟨funext fun m => by simpa using congrFun hx (Sum.inl m),
    funext fun s => by simpa using congrFun hx (Sum.inr s)⟩

/-- **Nonzero member lengths.** An injective equilibrium matrix has noncoincident endpoints for
every member, the two-force-member domain of `memberLength_pos_of_ne`: coincident endpoints give
a zero unit column (Lean's `x / 0 = 0`), so a unit force in that member balances zero loads, a
spurious state of self-stress. -/
lemma endpoints_ne_of_injective {J M R : Type*} [DecidableEq J] [Fintype M] [Fintype R]
    {r : J → (Fin 2 → ℝ)} {a b : M → J} {sj : R → J} {sd : R → (Fin 2 → ℝ)}
    (hinj : Function.Injective (equilibriumMatrix r a b sj sd).mulVec) (e : M) :
    r (a e) ≠ r (b e) := by
  classical
  intro heq
  have hcol : equilibriumMatrix r a b sj sd *ᵥ Pi.single (Sum.inl e) 1 = 0 := by
    funext q
    simp [Matrix.mulVec_single, equilibriumMatrix, axialCompatibilityUnit, axialCompatibility,
      heq]
  have := congrFun (hinj (hcol.trans (Matrix.mulVec_zero _).symm)) (Sum.inl e)
  simp at this

end TrussSolvability

end Mechanics.EngineeringStatics

end
