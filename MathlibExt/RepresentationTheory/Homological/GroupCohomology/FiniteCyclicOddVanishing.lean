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
# Odd cyclic cohomology with invertible group order

Let R be a commutative ring, G a finite group, and A an R-linear representation in universe u.
If m=|G| is a unit in R, every one-cocycle x is the coboundary of a=-m⁻¹Σ_{h∈G}x(h): x(g)=g•a-a.
Hence H¹(G,A) is zero.

If G is cyclic, its periodic resolution identifies every odd cohomological degree i with H¹. The
same unit hypothesis therefore makes H^i(G,A) zero for every odd natural number i.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

/-- Let R be a commutative ring, G a finite group, and A an R-linear G-representation, in the given
universe u. Assume m=|G| is a unit in R and write m⁻¹ for the coefficient of its inverse unit.
The module H¹(G,A) is subsingleton, so all of its classes are zero. For a one-cocycle x, the
coefficient a=-m⁻¹Σ_{h∈G}x(h) satisfies x(g)=ρ(g)a-a for every g, providing its coboundary
representative. -/
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

/-- Let R be a commutative ring, G a finite group, and A an R-linear G-representation, in the given
universe u. Assume m=|G| is a unit in R and write m⁻¹ for the coefficient of its inverse unit.
Assume also that G is cyclic. For every natural number i with i odd, H^i(G,A) is subsingleton.
The periodic cyclic resolution identifies H^i with H¹, whose cocycles are coboundaries by
averaging. -/
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
