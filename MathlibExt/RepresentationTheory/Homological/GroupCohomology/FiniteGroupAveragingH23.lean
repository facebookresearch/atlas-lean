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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThree

/-!
# Averaging contractions in degrees two and three

Let `G` be finite and suppose its order is a unit in a commutative
coefficient ring.  Averaging the final variable of an inhomogeneous
two-cocycle gives a one-cochain whose boundary is that cocycle.  Averaging
the final variable of a three-cocycle with the opposite sign similarly
gives a two-cochain boundary.

These explicit contractions prove that H2 and H3 vanish for every finite
group under the invertible-order hypothesis.  No cyclicity, field, or
semisimplicity hypothesis is used, and no assertion is made when the group
order is not invertible.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace groupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Averaging the final variable of a degree-two cochain. -/
noncomputable def averageLastCochainTwo
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R))
    (z : G × G → A) : G → A := fun g =>
  (↑(hcard.unit⁻¹) : R) • ∑ t : G, z (g, t)

/-- The averaged last-variable one-cochain has boundary equal to the
original degree-two cocycle. -/
theorem d₁₂_averageLastCochainTwo
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R))
    (z : cocycles₂ A) :
    (d₁₂ A).hom (averageLastCochainTwo A hcard z) = z := by
  funext p
  rcases p with ⟨g, h⟩
  let S : G → A := fun q => ∑ t : G, z (q, t)
  have hreindex : (∑ t : G, z (g, h * t)) = S g := by
    exact Function.Bijective.sum_comp (Group.mulLeft_bijective h)
      (fun t : G => z (g, t))
  have hsum : S (g * h) + (Fintype.card G : R) • z (g, h) =
      A.ρ g (S h) + S g := by
    calc
      S (g * h) + (Fintype.card G : R) • z (g, h) =
          (∑ t : G, z (g * h, t)) + ∑ _t : G, z (g, h) := by
        rw [Finset.sum_const, Finset.card_univ,
          ← Nat.cast_smul_eq_nsmul R]
      _ = ∑ t : G, (z (g * h, t) + z (g, h)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ t : G, (A.ρ g (z (h, t)) + z (g, h * t)) := by
        apply Finset.sum_congr rfl
        intro t _
        exact (mem_cocycles₂_iff z).1 z.2 g h t
      _ = A.ρ g (S h) + S g := by
        rw [Finset.sum_add_distrib, map_sum, hreindex]
  have hboundary : A.ρ g (S h) - S (g * h) + S g =
      (Fintype.card G : R) • z (g, h) := by
    calc
      A.ρ g (S h) - S (g * h) + S g =
          (A.ρ g (S h) + S g) - S (g * h) := by abel
      _ = (S (g * h) + (Fintype.card G : R) • z (g, h)) -
          S (g * h) := congrArg (fun q => q - S (g * h)) hsum.symm
      _ = (Fintype.card G : R) • z (g, h) := add_sub_cancel_left _ _
  change A.ρ g (averageLastCochainTwo A hcard z h) -
      averageLastCochainTwo A hcard z (g * h) +
        averageLastCochainTwo A hcard z g = z (g, h)
  calc
    A.ρ g (averageLastCochainTwo A hcard z h) -
          averageLastCochainTwo A hcard z (g * h) +
          averageLastCochainTwo A hcard z g =
        (↑(hcard.unit⁻¹) : R) •
          (A.ρ g (S h) - S (g * h) + S g) := by
      unfold averageLastCochainTwo
      change A.ρ g ((↑(hcard.unit⁻¹) : R) • S h) -
          (↑(hcard.unit⁻¹) : R) • S (g * h) +
          (↑(hcard.unit⁻¹) : R) • S g = _
      rw [map_smul]
      module
    _ = (↑(hcard.unit⁻¹) : R) •
        ((Fintype.card G : R) • z (g, h)) := by rw [hboundary]
    _ = z (g, h) := by
      rw [← mul_smul]
      change (((↑(hcard.unit⁻¹) : R) * (hcard.unit : R)) •
        z (g, h)) = z (g, h)
      rw [Units.inv_mul, one_smul]

/-- Averaging the final variable of a degree-three cochain, with the sign
required by the inhomogeneous differential. -/
noncomputable def averageLastCochainThree
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R))
    (z : G × G × G → A) : G × G → A := fun p =>
  -((↑(hcard.unit⁻¹) : R) • ∑ t : G, z (p.1, p.2, t))

/-- The signed averaged last-variable two-cochain has boundary equal to the
original degree-three cocycle. -/
theorem d₂₃_averageLastCochainThree
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R))
    (z : cocycles₃ A) :
    (d₂₃ A).hom (averageLastCochainThree A hcard z) = z := by
  funext p
  rcases p with ⟨g, h, i⟩
  let S : G × G → A := fun q => ∑ t : G, z (q.1, q.2, t)
  have hreindex : (∑ t : G, z (g, h, i * t)) = S (g, h) := by
    exact Function.Bijective.sum_comp (Group.mulLeft_bijective i)
      (fun t : G => z (g, h, t))
  have hsum : A.ρ g (S (h, i)) - S (g * h, i) + S (g, h * i) -
      S (g, h) + (Fintype.card G : R) • z (g, h, i) = 0 := by
    calc
      A.ρ g (S (h, i)) - S (g * h, i) + S (g, h * i) -
          S (g, h) + (Fintype.card G : R) • z (g, h, i) =
        (∑ t : G, A.ρ g (z (h, i, t))) -
          (∑ t : G, z (g * h, i, t)) +
          (∑ t : G, z (g, h * i, t)) -
          (∑ t : G, z (g, h, i * t)) +
          (∑ _t : G, z (g, h, i)) := by
        rw [map_sum, hreindex, Finset.sum_const, Finset.card_univ,
          ← Nat.cast_smul_eq_nsmul R]
      _ = ∑ t : G, (A.ρ g (z (h, i, t)) - z (g * h, i, t) +
          z (g, h * i, t) - z (g, h, i * t) + z (g, h, i)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        exact (mem_cocycles₃_def z).1 z.2 g h i t
  have hboundary : A.ρ g (S (h, i)) - S (g * h, i) + S (g, h * i) -
      S (g, h) = -((Fintype.card G : R) • z (g, h, i)) := by
    rw [add_eq_zero_iff_eq_neg] at hsum
    exact hsum
  change A.ρ g (averageLastCochainThree A hcard z (h, i)) -
      averageLastCochainThree A hcard z (g * h, i) +
      averageLastCochainThree A hcard z (g, h * i) -
      averageLastCochainThree A hcard z (g, h) = z (g, h, i)
  calc
    A.ρ g (averageLastCochainThree A hcard z (h, i)) -
          averageLastCochainThree A hcard z (g * h, i) +
          averageLastCochainThree A hcard z (g, h * i) -
          averageLastCochainThree A hcard z (g, h) =
        -((↑(hcard.unit⁻¹) : R) •
          (A.ρ g (S (h, i)) - S (g * h, i) + S (g, h * i) -
            S (g, h))) := by
      unfold averageLastCochainThree
      change A.ρ g (-((↑(hcard.unit⁻¹) : R) • S (h, i))) -
          (-((↑(hcard.unit⁻¹) : R) • S (g * h, i))) +
          (-((↑(hcard.unit⁻¹) : R) • S (g, h * i))) -
          (-((↑(hcard.unit⁻¹) : R) • S (g, h))) = _
      rw [map_neg, map_smul]
      module
    _ = (↑(hcard.unit⁻¹) : R) •
        ((Fintype.card G : R) • z (g, h, i)) := by
      rw [hboundary, smul_neg, neg_neg]
    _ = z (g, h, i) := by
      rw [← mul_smul]
      change (((↑(hcard.unit⁻¹) : R) * (hcard.unit : R)) •
        z (g, h, i)) = z (g, h, i)
      rw [Units.inv_mul, one_smul]

/-- Degree-two cohomology of a finite group vanishes when its order is a
unit in the coefficient ring. -/
theorem H2_subsingleton_of_card_isUnit
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) :
    Subsingleton (H2 A) := by
  refine ⟨fun x y => ?_⟩
  have hzero (q : H2 A) : q = 0 := by
    induction q using H2_induction_on with
    | _ z =>
        apply (H2π_eq_zero_iff z).2
        exact ⟨averageLastCochainTwo A hcard z,
          d₁₂_averageLastCochainTwo A hcard z⟩
  exact sub_eq_zero.mp (hzero (x - y))

/-- Degree-three cohomology of a finite group vanishes when its order is a
unit in the coefficient ring. -/
theorem H3_subsingleton_of_card_isUnit
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) :
    Subsingleton (H3 A) := by
  refine ⟨fun x y => ?_⟩
  have hzero (q : H3 A) : q = 0 := by
    induction q using H3_induction_on with
    | _ z =>
        apply (H3π_eq_zero_iff z).2
        exact ⟨averageLastCochainThree A hcard z,
          d₂₃_averageLastCochainThree A hcard z⟩
  exact sub_eq_zero.mp (hzero (x - y))

end groupCohomology
