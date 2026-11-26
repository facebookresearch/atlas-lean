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
# Degree-three restriction and right-transversal corestriction

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `A` a representation.
For each right transversal `T`, transfer of a restricted three-cocycle differs from `[G:H]`
times that cocycle by the coboundary of an explicit two-cochain.

Writing `t g=h₁r₁` and `r₁h=h₂r₂` in the Schreier decomposition, the two-cochain is
`K₂z(g,h)=-∑ t∈T, ρ(t⁻¹)(z(t,g,h)-z(h₁,r₁,h)+z(h₁,h₂,r₂))`. Thus `cor_T ∘ res = [G:H]` on
`H³(G,A)`. If the index is a unit in `k`, restriction is injective.
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, `T` a right transversal,
`z ∈ Z³(G,A)`, and `t∈T`. For `g,h∈G`, put `h₁=h_T(t,g)`, `r₁=r_T(t,g)`, `h₂=h_T(r₁,h)`, and
`r₂=r_T(r₁,h)`, using `a b=h_T(a,b)r_T(a,b)`. The summand
`restrictionCorestrictionHomotopyTwoTerm A T z t g h` equals
`ρ(t⁻¹)(z(t,g,h)-z(h₁,r₁,h)+z(h₁,h₂,r₂))`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `z ∈ Z³(G,A)`. The two-cochain `restrictionCorestrictionHomotopyTwo A T z`
has value `K₂z(g,h)=-∑ t∈T, ρ(t⁻¹)(z(t,g,h)-z(h₁,r₁,h)+z(h₁,h₂,r₂))`, where `t g=h₁r₁` and
`r₁h=h₂r₂` are the successive Schreier decompositions. -/
noncomputable def restrictionCorestrictionHomotopyTwo
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ A) : G × G → A := fun p =>
  -∑ t : (T : Set G),
    restrictionCorestrictionHomotopyTwoTerm A T z t p.1 p.2

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, `T` a right transversal,
`z ∈ Z³(G,A)`, `t∈T`, and `g,h,i∈G`. Write `Q_t(a,b)=restrictionCorestrictionHomotopyTwoTerm A
T z t a b`. If `h₁=h_T(t,g)`, `r₁=r_T(t,g)`, `h₂=h_T(r₁,h)`, `r₂=r_T(r₁,h)`, and
`h₃=h_T(r₂,i)`, then
`ρ(t⁻¹)z(h₁,h₂,h₃)=z(g,h,i)+Q_t(gh,i)-Q_t(g,hi)+Q_t(g,h)-ρ(g)Q_{r₁}(h,i)`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `z ∈ Z³(G,A)`. Then `corestrictionCochainThree A T (res z) = (H.index : k) •
z + d²(K₂z)`, where `K₂z=-∑ t∈T, restrictionCorestrictionHomotopyTwoTerm A T z t`. The
differential is `d²c(g,h,i)=ρ(g)c(h,i)-c(gh,i)+c(g,hi)-c(g,h)`, and restriction uses the
subgroup inclusion with unchanged coefficients. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `z ∈ Z³(G,A)`. Then `corestrictionH3OfRightTransversal A T (map H.subtype (𝟙
_) 3 (H3π A z)) = (H.index : k) • H3π A z` in `H³(G,A)`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` a
right transversal. For every `x ∈ H³(G,A)`, `corestrictionH3OfRightTransversal A T (map
H.subtype (𝟙 _) 3 x) = (H.index : k) • x`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` any
right transversal. If `IsUnit (H.index : k)`, then restriction `map H.subtype (𝟙 _) 3 :
H³(G,A) → H³(H,Rep.res H.subtype A)` is injective. -/
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
