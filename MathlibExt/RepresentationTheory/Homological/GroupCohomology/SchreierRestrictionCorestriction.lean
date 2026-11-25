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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeMapRepresentative
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH2

/-!
# Restriction followed by Schreier corestriction

For a finite-index subgroup `H ≤ G`, this file proves in degrees one and two
that corestriction after restriction is multiplication by `[G : H]`.  The
proof is explicit on inhomogeneous cocycles.  In degree one the comparison is
a degree-zero coboundary.  In degree two it is the boundary of the standard
Schreier change-of-section one-cochain.

Consequently restriction is injective in both degrees whenever the image of
the subgroup index is a unit in the coefficient ring.  No degree-three
corestriction, Mackey formula, or claim for a noninvertible index is made.
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

noncomputable local instance restrictionCorestrictionTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-zero homotopy comparing restriction-corestriction with index
multiplication on degree-one cocycles. -/
noncomputable def restrictionCorestrictionHomotopyZero
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₁ A) : A :=
  -∑ t : (T : Set G), A.ρ (t : G)⁻¹ (z (t : G))

/-- The single-transversal-term identity behind the degree-one
restriction-corestriction homotopy. -/
theorem restrictionCorestrictionOne_term
    (A : Rep k G) (T : H.RightTransversal)
    (z : cocycles₁ A) (t : (T : Set G)) (g : G) :
    A.ρ (t : G)⁻¹
        (z (T.schreierFactor t g : G)) =
      z g + A.ρ (t : G)⁻¹ (z (t : G)) -
        A.ρ g
          (A.ρ (T.schreierRep t g : G)⁻¹
            (z (T.schreierRep t g : G))) := by
  have htg := (mem_cocycles₁_iff z).1 z.2 (t : G) g
  have hfactor := (mem_cocycles₁_iff z).1 z.2
    (T.schreierFactor t g : G) (T.schreierRep t g : G)
  have hdecomp := T.schreierFactor_mul_schreierRep t g
  have hzfactor :
      z (T.schreierFactor t g : G) =
        A.ρ (t : G) (z g) + z (t : G) -
          A.ρ (T.schreierFactor t g : G)
            (z (T.schreierRep t g : G)) := by
    calc
      z (T.schreierFactor t g : G) =
          z ((T.schreierFactor t g : G) *
              (T.schreierRep t g : G)) -
            A.ρ (T.schreierFactor t g : G)
              (z (T.schreierRep t g : G)) := by rw [hfactor]; abel
      _ = z ((t : G) * g) -
            A.ρ (T.schreierFactor t g : G)
              (z (T.schreierRep t g : G)) := by rw [hdecomp]
      _ = A.ρ (t : G) (z g) + z (t : G) -
            A.ρ (T.schreierFactor t g : G)
              (z (T.schreierRep t g : G)) := by rw [htg]
  rw [hzfactor, map_sub, map_add]
  have hcancel :
      A.ρ (t : G)⁻¹ (A.ρ (t : G) (z g)) = z g := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  have hlast :
      A.ρ (t : G)⁻¹
          (A.ρ (T.schreierFactor t g : G)
            (z (T.schreierRep t g : G))) =
        A.ρ g
          (A.ρ (T.schreierRep t g : G)⁻¹
            (z (T.schreierRep t g : G))) := by
    rw [← Module.End.mul_apply, ← map_mul,
      T.inv_mul_schreierFactor t g, map_mul,
      Module.End.mul_apply]
  rw [hcancel, hlast]

/-- Chosen-transversal corestriction after restriction on a degree-one
cocycle differs from index multiplication by the displayed zero-cochain
boundary. -/
theorem corestrictionCochainOne_restriction
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₁ A) :
    corestrictionCochainOne A T
        (mapCocycles₁ (Subgroup.subtype H) (𝟙 _) z) =
      (H.index : k) • (z : G → A) +
        (d₀₁ A).hom (restrictionCorestrictionHomotopyZero A T z) := by
  funext g
  rw [corestrictionCochainOne_apply]
  change
    (∑ t : (T : Set G),
      A.ρ (t : G)⁻¹ (z (T.schreierFactor t g : G))) =
        (H.index : k) • z g +
          (A.ρ g (restrictionCorestrictionHomotopyZero A T z) -
            restrictionCorestrictionHomotopyZero A T z)
  have hterms :
      (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹ (z (T.schreierFactor t g : G))) =
        ∑ t : (T : Set G),
          (z g + A.ρ (t : G)⁻¹ (z (t : G)) -
            A.ρ g
              (A.ρ (T.schreierRep t g : G)⁻¹
                (z (T.schreierRep t g : G)))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact restrictionCorestrictionOne_term A T z t g
  rw [hterms]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ]
  have hreindex :
      (∑ t : (T : Set G),
          A.ρ (T.schreierRep t g : G)⁻¹
            (z (T.schreierRep t g : G))) =
        ∑ t : (T : Set G), A.ρ (t : G)⁻¹ (z (t : G)) :=
    (T.schreierRepEquiv g).sum_comp
      (fun t : (T : Set G) => A.ρ (t : G)⁻¹ (z (t : G)))
  rw [← map_sum, hreindex]
  unfold restrictionCorestrictionHomotopyZero
  rw [map_neg, map_sum]
  have hcard : Fintype.card (T : Set G) = H.index := by
    rw [Fintype.card_eq_nat_card, T.2.card_right]
  rw [hcard, ← Nat.cast_smul_eq_nsmul k]
  module

/-- One summand of the degree-one homotopy comparing degree-two
restriction-corestriction with index multiplication. -/
noncomputable def restrictionCorestrictionHomotopyOneTerm
    (A : Rep k G) (T : H.RightTransversal) (z : cocycles₂ A)
    (t : (T : Set G)) (g : G) : A :=
  A.ρ (t : G)⁻¹
    (z ((t : G), g) -
      z ((T.schreierFactor t g : G), (T.schreierRep t g : G)))

/-- The degree-one homotopy comparing restriction-corestriction with index
multiplication on degree-two cocycles. -/
noncomputable def restrictionCorestrictionHomotopyOne
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₂ A) : G → A := fun g =>
  -∑ t : (T : Set G), restrictionCorestrictionHomotopyOneTerm A T z t g

/-- The single-transversal-term identity behind the degree-two
restriction-corestriction homotopy. -/
theorem restrictionCorestrictionTwo_term
    (A : Rep k G) (T : H.RightTransversal) (z : cocycles₂ A)
    (t : (T : Set G)) (g h : G) :
    A.ρ (t : G)⁻¹
        (z ((T.schreierFactor t g : G),
          (T.schreierFactor (T.schreierRep t g) h : G))) =
      z (g, h) + restrictionCorestrictionHomotopyOneTerm A T z t (g * h) -
        restrictionCorestrictionHomotopyOneTerm A T z t g -
          A.ρ g
            (restrictionCorestrictionHomotopyOneTerm A T z
              (T.schreierRep t g) h) := by
  let a : H := T.schreierFactor t g
  let r : (T : Set G) := T.schreierRep t g
  let b : H := T.schreierFactor r h
  let s : (T : Set G) := T.schreierRep r h
  have htr : (a : G) * (r : G) = (t : G) * g := by
    exact T.schreierFactor_mul_schreierRep t g
  have hrs : (b : G) * (s : G) = (r : G) * h := by
    exact T.schreierFactor_mul_schreierRep r h
  have hab : T.schreierFactor t (g * h) = a * b := by
    exact T.schreierFactor_mul t g h
  have hs : T.schreierRep t (g * h) = s := by
    exact T.schreierRep_mul t g h
  have habcoe : (((a * b : H) : G)) = (a : G) * (b : G) := rfl
  have hcocycle := (mem_cocycles₂_iff z).1 z.2
  have h₁ := hcocycle (t : G) g h
  have h₂ := hcocycle (a : G) (r : G) h
  have h₃ := hcocycle (a : G) (b : G) (s : G)
  have hstep₁ :
      A.ρ (t : G) (z (g, h)) + z ((t : G), g * h) -
          z ((t : G), g) = z ((t : G) * g, h) := by
    rw [← h₁]
    abel
  have hstep₂ :
      z ((a : G) * (r : G), h) - A.ρ (a : G) (z ((r : G), h)) +
          z ((a : G), (r : G)) = z ((a : G), (r : G) * h) := by
    calc
      z ((a : G) * (r : G), h) - A.ρ (a : G) (z ((r : G), h)) +
          z ((a : G), (r : G)) =
        (z ((a : G) * (r : G), h) + z ((a : G), (r : G))) -
          A.ρ (a : G) (z ((r : G), h)) := by abel
      _ = (A.ρ (a : G) (z ((r : G), h)) +
            z ((a : G), (r : G) * h)) -
          A.ρ (a : G) (z ((r : G), h)) := by rw [h₂]
      _ = z ((a : G), (r : G) * h) := by abel
  have hstep₃ :
      z ((a : G), (b : G) * (s : G)) +
          A.ρ (a : G) (z ((b : G), (s : G))) -
          z ((a : G) * (b : G), (s : G)) = z ((a : G), (b : G)) := by
    calc
      z ((a : G), (b : G) * (s : G)) +
          A.ρ (a : G) (z ((b : G), (s : G))) -
          z ((a : G) * (b : G), (s : G)) =
        (A.ρ (a : G) (z ((b : G), (s : G))) +
            z ((a : G), (b : G) * (s : G))) -
          z ((a : G) * (b : G), (s : G)) := by abel
      _ = (z ((a : G) * (b : G), (s : G)) +
            z ((a : G), (b : G))) -
          z ((a : G) * (b : G), (s : G)) := by rw [h₃]
      _ = z ((a : G), (b : G)) := by abel
  have hinside :
      A.ρ (t : G) (z (g, h)) +
          (z ((t : G), g * h) -
            z (((a * b : H) : G), (s : G))) -
          (z ((t : G), g) - z ((a : G), (r : G))) -
          A.ρ (a : G)
            (z ((r : G), h) - z ((b : G), (s : G))) =
        z ((a : G), (b : G)) := by
    calc
      A.ρ (t : G) (z (g, h)) +
            (z ((t : G), g * h) - z (((a * b : H) : G), (s : G))) -
            (z ((t : G), g) - z ((a : G), (r : G))) -
            A.ρ (a : G) (z ((r : G), h) - z ((b : G), (s : G))) =
          (A.ρ (t : G) (z (g, h)) + z ((t : G), g * h) -
              z ((t : G), g)) + z ((a : G), (r : G)) -
            A.ρ (a : G) (z ((r : G), h)) +
              A.ρ (a : G) (z ((b : G), (s : G))) -
                z ((a : G) * (b : G), (s : G)) := by
        rw [habcoe]
        simp only [map_sub]
        abel
      _ = z ((t : G) * g, h) + z ((a : G), (r : G)) -
            A.ρ (a : G) (z ((r : G), h)) +
              A.ρ (a : G) (z ((b : G), (s : G))) -
                z ((a : G) * (b : G), (s : G)) := by rw [hstep₁]
      _ = z ((a : G) * (r : G), h) + z ((a : G), (r : G)) -
            A.ρ (a : G) (z ((r : G), h)) +
              A.ρ (a : G) (z ((b : G), (s : G))) -
                z ((a : G) * (b : G), (s : G)) := by rw [htr]
      _ = (z ((a : G) * (r : G), h) -
              A.ρ (a : G) (z ((r : G), h)) +
                z ((a : G), (r : G))) +
              A.ρ (a : G) (z ((b : G), (s : G))) -
                z ((a : G) * (b : G), (s : G)) := by abel
      _ = z ((a : G), (r : G) * h) +
              A.ρ (a : G) (z ((b : G), (s : G))) -
                z ((a : G) * (b : G), (s : G)) := by rw [hstep₂]
      _ = z ((a : G), (b : G) * (s : G)) +
              A.ρ (a : G) (z ((b : G), (s : G))) -
                z ((a : G) * (b : G), (s : G)) := by rw [hrs]
      _ = z ((a : G), (b : G)) := hstep₃
  have htransport (x : A) :
      A.ρ (t : G)⁻¹ (A.ρ (a : G) x) =
        A.ρ g (A.ρ (r : G)⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul]
    change A.ρ ((t : G)⁻¹ * (T.schreierFactor t g : G)) x = _
    rw [T.inv_mul_schreierFactor t g, map_mul,
      Module.End.mul_apply]
  have happ := congrArg (A.ρ (t : G)⁻¹) hinside
  unfold restrictionCorestrictionHomotopyOneTerm
  rw [hab, hs]
  change
    A.ρ (t : G)⁻¹ (z ((a : G), (b : G))) =
      z (g, h) +
          A.ρ (t : G)⁻¹
            (z ((t : G), g * h) - z (((a * b : H) : G), (s : G))) -
        A.ρ (t : G)⁻¹
            (z ((t : G), g) - z ((a : G), (r : G))) -
          A.ρ g
            (A.ρ (r : G)⁻¹
              (z ((r : G), h) - z ((b : G), (s : G))))
  rw [← happ]
  simp only [map_add, map_sub]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]
  rw [htransport, htransport]

/-- Chosen-transversal corestriction after restriction on a degree-two
cocycle differs from index multiplication by the displayed one-cochain
boundary. -/
theorem corestrictionCochainTwo_restriction
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₂ A) :
    corestrictionCochainTwo A T
        (mapCocycles₂ (Subgroup.subtype H) (𝟙 _) z) =
      (H.index : k) • (z : G × G → A) +
        (d₁₂ A).hom (restrictionCorestrictionHomotopyOne A T z) := by
  funext p
  rcases p with ⟨g, h⟩
  rw [corestrictionCochainTwo_apply]
  change
    (∑ t : (T : Set G),
      A.ρ (t : G)⁻¹
        (z ((T.schreierFactor t g : G),
          (T.schreierFactor (T.schreierRep t g) h : G)))) =
      (H.index : k) • z (g, h) +
        (A.ρ g (restrictionCorestrictionHomotopyOne A T z h) -
          restrictionCorestrictionHomotopyOne A T z (g * h) +
            restrictionCorestrictionHomotopyOne A T z g)
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (z ((T.schreierFactor t g : G),
            (T.schreierFactor (T.schreierRep t g) h : G)))) =
        ∑ t : (T : Set G),
          (z (g, h) +
              restrictionCorestrictionHomotopyOneTerm A T z t (g * h) -
            restrictionCorestrictionHomotopyOneTerm A T z t g -
              A.ρ g
                (restrictionCorestrictionHomotopyOneTerm A T z
                  (T.schreierRep t g) h)) := by
    apply Finset.sum_congr rfl
    intro t _
    exact restrictionCorestrictionTwo_term A T z t g h
  rw [hterms]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ]
  have hreindex :
      (∑ t : (T : Set G),
          restrictionCorestrictionHomotopyOneTerm A T z
            (T.schreierRep t g) h) =
        ∑ t : (T : Set G),
          restrictionCorestrictionHomotopyOneTerm A T z t h :=
    (T.schreierRepEquiv g).sum_comp
      (fun t : (T : Set G) =>
        restrictionCorestrictionHomotopyOneTerm A T z t h)
  rw [← map_sum, hreindex]
  unfold restrictionCorestrictionHomotopyOne
  rw [map_neg, map_sum]
  have hcard : Fintype.card (T : Set G) = H.index := by
    rw [Fintype.card_eq_nat_card, T.2.card_right]
  rw [hcard, ← Nat.cast_smul_eq_nsmul k]
  module

/-- Representative form of `cor ∘ res = [G : H]` on `H¹`. -/
theorem corestrictionH1_restriction_H1π
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₁ A) :
    corestrictionH1 A
        (map (Subgroup.subtype H) (𝟙 _) 1 (H1π A z)) =
      (H.index : k) • H1π A z := by
  rw [map_H1π, corestrictionH1_H1π A T]
  calc
    H1π A
        (corestrictionCocyclesOne A T
          (mapCocycles₁ (Subgroup.subtype H) (𝟙 _) z)) =
      H1π A ((H.index : k) • z) := by
        apply (H1π_eq_iff _ _).2
        refine ⟨restrictionCorestrictionHomotopyZero A T z, ?_⟩
        rw [coe_corestrictionCocyclesOne]
        change
          (d₀₁ A).hom (restrictionCorestrictionHomotopyZero A T z) =
            corestrictionCochainOne A T
                (mapCocycles₁ (Subgroup.subtype H) (𝟙 _) z) -
              (H.index : k) • (z : G → A)
        rw [corestrictionCochainOne_restriction]
        module
    _ = (H.index : k) • H1π A z := (H1π A).hom.map_smul _ _

/-- Representative form of `cor ∘ res = [G : H]` on `H²`. -/
theorem corestrictionH2_restriction_H2π
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₂ A) :
    corestrictionH2 A
        (map (Subgroup.subtype H) (𝟙 _) 2 (H2π A z)) =
      (H.index : k) • H2π A z := by
  rw [map_H2π, corestrictionH2_H2π A T]
  calc
    H2π A
        (corestrictionCocyclesTwo A T
          (mapCocycles₂ (Subgroup.subtype H) (𝟙 _) z)) =
      H2π A ((H.index : k) • z) := by
        apply (H2π_eq_iff _ _).2
        refine ⟨restrictionCorestrictionHomotopyOne A T z, ?_⟩
        rw [coe_corestrictionCocyclesTwo]
        change
          (d₁₂ A).hom (restrictionCorestrictionHomotopyOne A T z) =
            corestrictionCochainTwo A T
                (mapCocycles₂ (Subgroup.subtype H) (𝟙 _) z) -
              (H.index : k) • (z : G × G → A)
        rw [corestrictionCochainTwo_restriction]
        module
    _ = (H.index : k) • H2π A z := (H2π A).hom.map_smul _ _

/-- Canonical degree-one corestriction after restriction is multiplication by
the subgroup index. -/
theorem corestrictionH1_restriction
    (A : Rep k G) [H.FiniteIndex] (x : H1 A) :
    corestrictionH1 A (map (Subgroup.subtype H) (𝟙 _) 1 x) =
      (H.index : k) • x := by
  induction x using H1_induction_on with
  | _ z =>
      exact corestrictionH1_restriction_H1π (H := H) A
        (default : H.RightTransversal) z

/-- Canonical degree-two corestriction after restriction is multiplication by
the subgroup index. -/
theorem corestrictionH2_restriction
    (A : Rep k G) [H.FiniteIndex] (x : H2 A) :
    corestrictionH2 A (map (Subgroup.subtype H) (𝟙 _) 2 x) =
      (H.index : k) • x := by
  induction x using H2_induction_on with
  | _ z =>
      exact corestrictionH2_restriction_H2π (H := H) A
        (default : H.RightTransversal) z

/-- Linear-map form of the degree-one restriction/corestriction composite
formula. -/
theorem corestrictionH1_comp_restriction
    (A : Rep k G) [H.FiniteIndex] :
    (corestrictionH1 A).comp
        (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
          (Subgroup.subtype H) (𝟙 _) 1).hom =
      (H.index : k) • LinearMap.id := by
  ext x
  exact corestrictionH1_restriction A x

/-- Linear-map form of the degree-two restriction/corestriction composite
formula. -/
theorem corestrictionH2_comp_restriction
    (A : Rep k G) [H.FiniteIndex] :
    (corestrictionH2 A).comp
        (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
          (Subgroup.subtype H) (𝟙 _) 2).hom =
      (H.index : k) • LinearMap.id := by
  ext x
  exact corestrictionH2_restriction A x

/-- Degree-one restriction to a finite-index subgroup is injective when the
subgroup index is a unit in the coefficient ring. -/
theorem restrictionH1_injective_of_isUnit_index
    (A : Rep k G) [H.FiniteIndex]
    (hindex : IsUnit (H.index : k)) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
        (Subgroup.subtype H) (𝟙 _) 1) := by
  intro x y hxy
  apply hindex.smul_left_cancel.mp
  rw [← corestrictionH1_restriction A x,
    ← corestrictionH1_restriction A y, hxy]

/-- Degree-two restriction to a finite-index subgroup is injective when the
subgroup index is a unit in the coefficient ring. -/
theorem restrictionH2_injective_of_isUnit_index
    (A : Rep k G) [H.FiniteIndex]
    (hindex : IsUnit (H.index : k)) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
        (Subgroup.subtype H) (𝟙 _) 2) := by
  intro x y hxy
  apply hindex.smul_left_cancel.mp
  rw [← corestrictionH2_restriction A x,
    ← corestrictionH2_restriction A y, hxy]

end groupCohomology
