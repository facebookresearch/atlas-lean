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

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.Algebra.Ring.Defs

/-!
# Odd cohomology of a cyclic group with invertible order

For any finite group, averaging a one-cocycle by the inverse group order
expresses it as a coboundary when the group order is a unit in the coefficient
ring. Thus H1 vanishes without a cyclicity assumption.

For a finite cyclic group, the periodic resolution identifies every positive
odd cohomological degree with H1. Consequently all positive odd-degree group
cohomology vanishes when the group order is invertible.

The degree-two and degree-three specializations are intentionally absent: the
general finite-group averaging theorems provide strictly stronger results in
those degrees.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

/-- Degree-one cohomology of a finite group vanishes when the group order is
invertible in the coefficient ring. -/
theorem H1_subsingleton_of_card_isUnit
    {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) :
    Subsingleton (H1 A) := by
  refine ⟨fun x y => ?_⟩
  have hzero (z : H1 A) : z = 0 := by
    induction z using H1_induction_on with
    | _ f =>
      apply (H1π_eq_zero_iff f).2
      let c : Rˣ := hcard.unit
      let S : A := ∑ g : G, f g
      let a : A := -((↑(c⁻¹) : R) • S)
      refine ⟨a, ?_⟩
      funext h
      have hsum : S = A.ρ h S + (Fintype.card G : R) • f h := by
        calc
          S = ∑ g : G, f (h * g) :=
            (Function.Bijective.sum_comp
              (Group.mulLeft_bijective h) fun g : G => f g).symm
          _ = ∑ g : G, (A.ρ h (f g) + f h) := by
            apply Finset.sum_congr rfl
            intro g _
            exact (mem_cocycles₁_iff f).1 f.2 h g
          _ = A.ρ h S + (Fintype.card G : R) • f h := by
            rw [Finset.sum_add_distrib, map_sum]
            rw [Finset.sum_const, Finset.card_univ,
              ← Nat.cast_smul_eq_nsmul R]
      have hdiff : S - A.ρ h S = (Fintype.card G : R) • f h := by
        calc
          S - A.ρ h S =
              (A.ρ h S + (Fintype.card G : R) • f h) - A.ρ h S :=
            congrArg (fun t => t - A.ρ h S) hsum
          _ = (Fintype.card G : R) • f h := add_sub_cancel_left _ _
      change A.ρ h a - a = f h
      calc
        A.ρ h a - a = (↑(c⁻¹) : R) • (S - A.ρ h S) := by
          dsimp only [a]
          rw [map_neg, map_smul]
          module
        _ = (↑(c⁻¹) : R) • ((Fintype.card G : R) • f h) := by
          rw [hdiff]
        _ = f h := by
          rw [← mul_smul]
          change (((↑(c⁻¹) : R) * (c : R)) • f h) = f h
          rw [Units.inv_mul, one_smul]
  exact sub_eq_zero.mp (hzero (x - y))

/-- Every odd-degree cohomology module of a finite cyclic group vanishes when
the group order is invertible. -/
theorem odd_subsingleton_of_isCyclic_of_card_isUnit
    {R G : Type u} [CommRing R] [Group G] [Fintype G] [IsCyclic G]
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R))
    (i : ℕ) (hi : Odd i) :
    Subsingleton (groupCohomology A i) := by
  let _ : CommGroup G := IsCyclic.commGroup
  let g : G := (IsCyclic.exists_generator (α := G)).choose
  have hg : ∀ x, x ∈ Subgroup.zpowers g :=
    (IsCyclic.exists_generator (α := G)).choose_spec
  let e : groupCohomology A i ≅ H1 A :=
    Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg i hi ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm
  let hH1 : Subsingleton (H1 A) := H1_subsingleton_of_card_isUnit A hcard
  exact ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    (hH1.elim (e.hom x) (e.hom y))⟩

end groupCohomology
