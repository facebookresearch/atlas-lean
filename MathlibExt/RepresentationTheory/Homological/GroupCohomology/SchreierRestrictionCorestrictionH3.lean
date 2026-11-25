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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestriction
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThree

/-!
# Restriction followed by chosen-transversal corestriction in degree three

For every finite right transversal, degree-three Schreier corestriction after
restriction is multiplication by the subgroup index on `H³`.  The proof uses
an explicit degree-two prism homotopy on inhomogeneous three-cocycles.
Consequently degree-three restriction is injective whenever the subgroup
index is a unit in the coefficient ring.

This file does not prove independence of the chosen transversal and therefore
does not define canonical degree-three corestriction.  It also makes no
Kummer, norm-residue, or Bloch--Kato claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance restrictionCorestrictionH3TransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- One prism summand of the degree-two homotopy comparing degree-three
restriction-corestriction with index multiplication. -/
noncomputable def restrictionCorestrictionHomotopyTwoTerm
    (A : Rep k G) (T : H.RightTransversal) (z : cocycles₃ A)
    (t : (T : Set G)) (g h : G) : A :=
  A.ρ (t : G)⁻¹
    (z ((t : G), g, h) -
      z ((T.schreierFactor t g : G),
        (T.schreierRep t g : G), h) +
      z ((T.schreierFactor t g : G),
        (T.schreierFactor (T.schreierRep t g) h : G),
        (T.schreierRep (T.schreierRep t g) h : G)))

/-- The signed degree-two prism homotopy comparing degree-three
restriction-corestriction with index multiplication. -/
noncomputable def restrictionCorestrictionHomotopyTwo
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ A) : G × G → A := fun p =>
  -∑ t : (T : Set G),
    restrictionCorestrictionHomotopyTwoTerm A T z t p.1 p.2

/-- The single-transversal-term prism identity behind the degree-three
restriction/corestriction index formula. -/
theorem restrictionCorestrictionThree_term
    (A : Rep k G) (T : H.RightTransversal) (z : cocycles₃ A)
    (t : (T : Set G)) (g h i : G) :
    A.ρ (t : G)⁻¹
        (z ((T.schreierFactor t g : G),
          (T.schreierFactor (T.schreierRep t g) h : G),
          (T.schreierFactor
            (T.schreierRep (T.schreierRep t g) h) i : G))) =
      z (g, h, i) +
          restrictionCorestrictionHomotopyTwoTerm A T z t (g * h) i -
        restrictionCorestrictionHomotopyTwoTerm A T z t g (h * i) +
        restrictionCorestrictionHomotopyTwoTerm A T z t g h -
          A.ρ g
            (restrictionCorestrictionHomotopyTwoTerm A T z
              (T.schreierRep t g) h i) := by
  let a : H := T.schreierFactor t g
  let r : (T : Set G) := T.schreierRep t g
  let b : H := T.schreierFactor r h
  let s : (T : Set G) := T.schreierRep r h
  let c : H := T.schreierFactor s i
  let u : (T : Set G) := T.schreierRep s i
  have htr : (a : G) * (r : G) = (t : G) * g :=
    T.schreierFactor_mul_schreierRep t g
  have hrs : (b : G) * (s : G) = (r : G) * h :=
    T.schreierFactor_mul_schreierRep r h
  have hsu : (c : G) * (u : G) = (s : G) * i :=
    T.schreierFactor_mul_schreierRep s i
  have hcocycle := (mem_cocycles₃_def z).1 z.2
  have h₁ := hcocycle (t : G) g h i
  have h₂ := hcocycle (a : G) (r : G) h i
  have h₃ := hcocycle (a : G) (b : G) (s : G) i
  have h₄ := hcocycle (a : G) (b : G) (c : G) (u : G)
  have hstep₁ :
      A.ρ (t : G) (z (g, h, i)) + z ((t : G), g * h, i) -
          z ((t : G), g, h * i) + z ((t : G), g, h) =
        z ((t : G) * g, h, i) := by
    rw [← sub_eq_zero]
    calc
      A.ρ (t : G) (z (g, h, i)) + z ((t : G), g * h, i) -
            z ((t : G), g, h * i) + z ((t : G), g, h) -
            z ((t : G) * g, h, i) =
          A.ρ (t : G) (z (g, h, i)) - z ((t : G) * g, h, i) +
            z ((t : G), g * h, i) - z ((t : G), g, h * i) +
              z ((t : G), g, h) := by abel
      _ = 0 := h₁
  have hstep₂ :
      z ((a : G) * (r : G), h, i) + z ((a : G), (r : G), h * i) -
          z ((a : G), (r : G), h) -
          A.ρ (a : G) (z ((r : G), h, i)) =
        z ((a : G), (r : G) * h, i) := by
    rw [← sub_eq_zero]
    calc
      z ((a : G) * (r : G), h, i) + z ((a : G), (r : G), h * i) -
            z ((a : G), (r : G), h) -
            A.ρ (a : G) (z ((r : G), h, i)) -
            z ((a : G), (r : G) * h, i) =
          -(A.ρ (a : G) (z ((r : G), h, i)) -
            z ((a : G) * (r : G), h, i) +
            z ((a : G), (r : G) * h, i) -
            z ((a : G), (r : G), h * i) +
            z ((a : G), (r : G), h)) := by abel
      _ = 0 := by rw [h₂, neg_zero]
  have hstep₃ :
      z ((a : G), (b : G) * (s : G), i) -
          z ((a : G) * (b : G), (s : G), i) +
          z ((a : G), (b : G), (s : G)) +
          A.ρ (a : G) (z ((b : G), (s : G), i)) =
        z ((a : G), (b : G), (s : G) * i) := by
    rw [← sub_eq_zero]
    calc
      z ((a : G), (b : G) * (s : G), i) -
            z ((a : G) * (b : G), (s : G), i) +
            z ((a : G), (b : G), (s : G)) +
            A.ρ (a : G) (z ((b : G), (s : G), i)) -
            z ((a : G), (b : G), (s : G) * i) =
          A.ρ (a : G) (z ((b : G), (s : G), i)) -
            z ((a : G) * (b : G), (s : G), i) +
            z ((a : G), (b : G) * (s : G), i) -
            z ((a : G), (b : G), (s : G) * i) +
            z ((a : G), (b : G), (s : G)) := by abel
      _ = 0 := h₃
  have hstep₄ :
      z ((a : G), (b : G), (c : G) * (u : G)) +
          z ((a : G) * (b : G), (c : G), (u : G)) -
          z ((a : G), (b : G) * (c : G), (u : G)) -
          A.ρ (a : G) (z ((b : G), (c : G), (u : G))) =
        z ((a : G), (b : G), (c : G)) := by
    rw [← sub_eq_zero]
    calc
      z ((a : G), (b : G), (c : G) * (u : G)) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) -
            z ((a : G), (b : G), (c : G)) =
          -(A.ρ (a : G) (z ((b : G), (c : G), (u : G))) -
            z ((a : G) * (b : G), (c : G), (u : G)) +
            z ((a : G), (b : G) * (c : G), (u : G)) -
            z ((a : G), (b : G), (c : G) * (u : G)) +
            z ((a : G), (b : G), (c : G))) := by abel
      _ = 0 := by rw [h₄, neg_zero]
  have hinside :
      A.ρ (t : G) (z (g, h, i)) +
          (z ((t : G), g * h, i) -
            z (((a * b : H) : G), (s : G), i) +
            z (((a * b : H) : G), (c : G), (u : G))) -
          (z ((t : G), g, h * i) -
            z ((a : G), (r : G), h * i) +
            z ((a : G), ((b * c : H) : G), (u : G))) +
          (z ((t : G), g, h) - z ((a : G), (r : G), h) +
            z ((a : G), (b : G), (s : G))) -
          A.ρ (a : G)
            (z ((r : G), h, i) - z ((b : G), (s : G), i) +
              z ((b : G), (c : G), (u : G))) =
        z ((a : G), (b : G), (c : G)) := by
    calc
      A.ρ (t : G) (z (g, h, i)) +
            (z ((t : G), g * h, i) -
              z (((a * b : H) : G), (s : G), i) +
              z (((a * b : H) : G), (c : G), (u : G))) -
            (z ((t : G), g, h * i) -
              z ((a : G), (r : G), h * i) +
              z ((a : G), ((b * c : H) : G), (u : G))) +
            (z ((t : G), g, h) - z ((a : G), (r : G), h) +
              z ((a : G), (b : G), (s : G))) -
            A.ρ (a : G)
              (z ((r : G), h, i) - z ((b : G), (s : G), i) +
                z ((b : G), (c : G), (u : G))) =
          (A.ρ (t : G) (z (g, h, i)) + z ((t : G), g * h, i) -
              z ((t : G), g, h * i) + z ((t : G), g, h)) +
            z ((a : G), (r : G), h * i) - z ((a : G), (r : G), h) -
            A.ρ (a : G) (z ((r : G), h, i)) -
            z ((a : G) * (b : G), (s : G), i) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) +
            z ((a : G), (b : G), (s : G)) +
            A.ρ (a : G) (z ((b : G), (s : G), i)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by
        simp only [map_add, map_sub]
        simp only [Subgroup.coe_mul]
        abel
      _ = z ((t : G) * g, h, i) +
            z ((a : G), (r : G), h * i) - z ((a : G), (r : G), h) -
            A.ρ (a : G) (z ((r : G), h, i)) -
            z ((a : G) * (b : G), (s : G), i) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) +
            z ((a : G), (b : G), (s : G)) +
            A.ρ (a : G) (z ((b : G), (s : G), i)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by
        rw [hstep₁]
      _ = z ((a : G) * (r : G), h, i) +
            z ((a : G), (r : G), h * i) - z ((a : G), (r : G), h) -
            A.ρ (a : G) (z ((r : G), h, i)) -
            z ((a : G) * (b : G), (s : G), i) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) +
            z ((a : G), (b : G), (s : G)) +
            A.ρ (a : G) (z ((b : G), (s : G), i)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by rw [htr]
      _ = z ((a : G), (r : G) * h, i) -
            z ((a : G) * (b : G), (s : G), i) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) +
            z ((a : G), (b : G), (s : G)) +
            A.ρ (a : G) (z ((b : G), (s : G), i)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by
        rw [hstep₂]
      _ = z ((a : G), (b : G) * (s : G), i) -
            z ((a : G) * (b : G), (s : G), i) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) +
            z ((a : G), (b : G), (s : G)) +
            A.ρ (a : G) (z ((b : G), (s : G), i)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by rw [hrs]
      _ = z ((a : G), (b : G), (s : G) * i) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by
        calc
          z ((a : G), (b : G) * (s : G), i) -
                z ((a : G) * (b : G), (s : G), i) +
                z ((a : G) * (b : G), (c : G), (u : G)) -
                z ((a : G), (b : G) * (c : G), (u : G)) +
                z ((a : G), (b : G), (s : G)) +
                A.ρ (a : G) (z ((b : G), (s : G), i)) -
                A.ρ (a : G) (z ((b : G), (c : G), (u : G))) =
              (z ((a : G), (b : G) * (s : G), i) -
                z ((a : G) * (b : G), (s : G), i) +
                z ((a : G), (b : G), (s : G)) +
                A.ρ (a : G) (z ((b : G), (s : G), i))) +
                z ((a : G) * (b : G), (c : G), (u : G)) -
                z ((a : G), (b : G) * (c : G), (u : G)) -
                A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by abel
          _ = z ((a : G), (b : G), (s : G) * i) +
                z ((a : G) * (b : G), (c : G), (u : G)) -
                z ((a : G), (b : G) * (c : G), (u : G)) -
                A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by
            rw [hstep₃]
      _ = z ((a : G), (b : G), (c : G) * (u : G)) +
            z ((a : G) * (b : G), (c : G), (u : G)) -
            z ((a : G), (b : G) * (c : G), (u : G)) -
            A.ρ (a : G) (z ((b : G), (c : G), (u : G))) := by rw [hsu]
      _ = z ((a : G), (b : G), (c : G)) := hstep₄
  have htransport (x : A) :
      A.ρ (t : G)⁻¹ (A.ρ (a : G) x) =
        A.ρ g (A.ρ (r : G)⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul]
    change A.ρ ((t : G)⁻¹ * (T.schreierFactor t g : G)) x = _
    rw [T.inv_mul_schreierFactor t g, map_mul, Module.End.mul_apply]
  have happ := congrArg (A.ρ (t : G)⁻¹) hinside
  unfold restrictionCorestrictionHomotopyTwoTerm
  rw [T.schreierFactor_mul t g h,
    T.schreierFactor_mul r h i,
    T.schreierRep_mul t g h,
    T.schreierRep_mul r h i]
  change A.ρ (t : G)⁻¹ (z ((a : G), (b : G), (c : G))) = _
  rw [← happ]
  simp only [map_add, map_sub]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]
  rw [htransport, htransport, htransport]

/-- Chosen-transversal degree-three corestriction after restriction differs
from index multiplication by the displayed degree-two prism boundary. -/
theorem corestrictionCochainThree_restriction
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ A) :
    corestrictionCochainThree A T
        (mapCocycles₃ (Subgroup.subtype H) (𝟙 _) z) =
      (H.index : k) • (z : G × G × G → A) +
        (d₂₃ A).hom (restrictionCorestrictionHomotopyTwo A T z) := by
  funext p
  rcases p with ⟨g, h, i⟩
  rw [corestrictionCochainThree_apply]
  change
    (∑ t : (T : Set G),
      A.ρ (t : G)⁻¹
        (z ((T.schreierFactor t g : G),
          (T.schreierFactor (T.schreierRep t g) h : G),
          (T.schreierFactor
            (T.schreierRep (T.schreierRep t g) h) i : G)))) =
      (H.index : k) • z (g, h, i) +
        (A.ρ g (restrictionCorestrictionHomotopyTwo A T z (h, i)) -
          restrictionCorestrictionHomotopyTwo A T z (g * h, i) +
          restrictionCorestrictionHomotopyTwo A T z (g, h * i) -
          restrictionCorestrictionHomotopyTwo A T z (g, h))
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (z ((T.schreierFactor t g : G),
            (T.schreierFactor (T.schreierRep t g) h : G),
            (T.schreierFactor
              (T.schreierRep (T.schreierRep t g) h) i : G)))) =
        ∑ t : (T : Set G),
          (z (g, h, i) +
              restrictionCorestrictionHomotopyTwoTerm A T z t (g * h) i -
            restrictionCorestrictionHomotopyTwoTerm A T z t g (h * i) +
            restrictionCorestrictionHomotopyTwoTerm A T z t g h -
              A.ρ g
                (restrictionCorestrictionHomotopyTwoTerm A T z
                  (T.schreierRep t g) h i)) := by
    apply Finset.sum_congr rfl
    intro t _
    exact restrictionCorestrictionThree_term A T z t g h i
  rw [hterms]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ]
  have hreindex :
      (∑ t : (T : Set G),
          restrictionCorestrictionHomotopyTwoTerm A T z
            (T.schreierRep t g) h i) =
        ∑ t : (T : Set G),
          restrictionCorestrictionHomotopyTwoTerm A T z t h i :=
    (T.schreierRepEquiv g).sum_comp
      (fun t : (T : Set G) =>
        restrictionCorestrictionHomotopyTwoTerm A T z t h i)
  rw [← map_sum, hreindex]
  unfold restrictionCorestrictionHomotopyTwo
  rw [map_neg, map_sum]
  have hcard : Fintype.card (T : Set G) = H.index := by
    rw [Fintype.card_eq_nat_card, T.2.card_right]
  rw [hcard, ← Nat.cast_smul_eq_nsmul k]
  module

/-- Representative form of `cor ∘ res = [G : H]` on `H³` for every chosen
right transversal. -/
theorem corestrictionH3OfRightTransversal_restriction_H3π
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ A) :
    corestrictionH3OfRightTransversal A T
        (map (Subgroup.subtype H) (𝟙 _) 3 (H3π A z)) =
      (H.index : k) • H3π A z := by
  rw [H3π_comp_map_apply,
    corestrictionH3OfRightTransversal_H3π]
  calc
    H3π A
        (corestrictionCocyclesThree A T
          (mapCocycles₃ (Subgroup.subtype H) (𝟙 _) z)) =
      H3π A ((H.index : k) • z) := by
        apply (H3π_eq_iff _ _).2
        refine ⟨restrictionCorestrictionHomotopyTwo A T z, ?_⟩
        rw [coe_corestrictionCocyclesThree]
        change
          (d₂₃ A).hom (restrictionCorestrictionHomotopyTwo A T z) =
            corestrictionCochainThree A T
                (mapCocycles₃ (Subgroup.subtype H) (𝟙 _) z) -
              (H.index : k) • (z : G × G × G → A)
        rw [corestrictionCochainThree_restriction]
        module
    _ = (H.index : k) • H3π A z := (H3π A).hom.map_smul _ _

/-- Chosen-transversal degree-three corestriction after restriction is
multiplication by the subgroup index. -/
theorem corestrictionH3OfRightTransversal_restriction
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : H3 A) :
    corestrictionH3OfRightTransversal A T
        (map (Subgroup.subtype H) (𝟙 _) 3 x) =
      (H.index : k) • x := by
  induction x using H3_induction_on with
  | _ z =>
      exact corestrictionH3OfRightTransversal_restriction_H3π
        (H := H) A T z

/-- Degree-three restriction to a finite-index subgroup is injective when
the subgroup index is a unit in the coefficient ring.  A right transversal
is supplied only to witness the left inverse up to the unit scalar. -/
theorem restrictionH3_injective_of_isUnit_index
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (hindex : IsUnit (H.index : k)) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
        (Subgroup.subtype H) (𝟙 _) 3) := by
  intro x y hxy
  apply hindex.smul_left_cancel.mp
  rw [← corestrictionH3OfRightTransversal_restriction A T x,
    ← corestrictionH3OfRightTransversal_restriction A T y, hxy]

end groupCohomology
