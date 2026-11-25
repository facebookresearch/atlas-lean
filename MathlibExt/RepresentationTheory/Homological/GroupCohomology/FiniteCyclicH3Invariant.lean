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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CyclicEvenResolutionComparison
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwo
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeHomologyIso

/-!
# An explicit cyclic invariant for degree-three group cohomology

For a finite group and a chosen element `g`, a degree-three inhomogeneous
cochain has the cyclic sum

`sum_h z(g,h,g)`.

On a three-cocycle this sum lies in the kernel of the representation norm.
On a three-coboundary `d t` it is

`(rho(g) - 1) (sum_h t(h,g))`.

Thus it is exactly the explicit odd cyclic-resolution invariant expected in
`Ker(N) / Im(rho(g)-1)`.  We also compute it on the landed `(1,2)` cup and
on the right-associated nested `(1,1,1)` cup representatives.

The remaining comparison step is to identify this explicit invariant map
with Mathlib's abstract `Rep.FiniteCyclicGroup.groupCohomologyIsoOdd`, whose
comparison chain map is chosen through the projective resolution.  No H3
generation, Kummer-symbol generation, or Bloch--Kato claim is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory ShortComplex Limits
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

@[simp]
theorem cyclicSumThree_apply (A : Rep k G) (g : G)
    (z : G × G × G → A) :
    cyclicSumThree A g z = ∑ h : G, z (g, h, g) :=
  rfl

private theorem sum_mulLeft {M : Type*} [AddCommMonoid M]
    (g : G) (f : G → M) :
    (∑ h : G, f (g * h)) = ∑ h : G, f h := by
  simpa using (Equiv.mulLeft g).sum_comp Finset.univ f

private theorem sum_mulRight {M : Type*} [AddCommMonoid M]
    (g : G) (f : G → M) :
    (∑ h : G, f (h * g)) = ∑ h : G, f h := by
  simpa using (Equiv.mulRight g).sum_comp Finset.univ f

/-- The cyclic sum of a degree-three coboundary is in the image of
`rho(g)-1`. -/
theorem cyclicSumThree_d₂₃ (A : Rep k G) (g : G)
    (t : G × G → A) :
    cyclicSumThree A g ((d₂₃ A).hom t) =
      A.ρ g (∑ h : G, t (h, g)) - ∑ h : G, t (h, g) := by
  rw [cyclicSumThree_apply]
  simp only [d₂₃_hom_apply, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, map_sum]
  rw [sum_mulLeft g (fun h => t (h, g))]
  rw [sum_mulRight g (fun h => t (g, h))]
  abel

/-- Sum a four-cochain over the first and third arguments, with the second
and fourth arguments fixed at `g`. -/
noncomputable def cyclicSumFour (A : Rep k G) (g : G) :
    ModuleCat.of k (G × G × G × G → A) ⟶ ModuleCat.of k A :=
  ModuleCat.ofHom
    { toFun := fun w => ∑ a : G, ∑ h : G, w (a, g, h, g)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, RingHom.id_apply,
          Finset.smul_sum] }

@[simp]
theorem cyclicSumFour_apply (A : Rep k G) (g : G)
    (w : G × G × G × G → A) :
    cyclicSumFour A g w = ∑ a : G, ∑ h : G, w (a, g, h, g) :=
  rfl

/-- The degree-three cyclic sum intertwines the next inhomogeneous
differential with the representation norm. -/
theorem cyclicSumThree_comp_norm (A : Rep k G) (g : G) :
    cyclicSumThree A g ≫ A.norm.asHom.toModuleCatHom =
      d₃₄ A ≫ cyclicSumFour A g := by
  ext z
  change A.ρ.norm (∑ h : G, z (g, h, g)) =
    ∑ a : G, ∑ h : G,
      (A.ρ a (z (g, h, g)) - z (a * g, h, g) +
        z (a, g * h, g) - z (a, g, h * g) + z (a, g, h))
  unfold Representation.norm
  simp only [LinearMap.sum_apply]
  have h₁ : (∑ a : G, ∑ h : G, z (a * g, h, g)) =
      ∑ a : G, ∑ h : G, z (a, h, g) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    exact sum_mulRight g (fun a => z (a, h, g))
  have h₂ : (∑ a : G, ∑ h : G, z (a, g * h, g)) =
      ∑ a : G, ∑ h : G, z (a, h, g) := by
    apply Finset.sum_congr rfl
    intro a _
    exact sum_mulLeft g (fun h => z (a, h, g))
  have h₃ : (∑ a : G, ∑ h : G, z (a, g, h * g)) =
      ∑ a : G, ∑ h : G, z (a, g, h) := by
    apply Finset.sum_congr rfl
    intro a _
    exact sum_mulRight g (fun h => z (a, g, h))
  simp_rw [map_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h₁, h₂, h₃]
  abel

/-- Explicit morphism from the inhomogeneous H3 short complex to the odd
cyclic short complex. -/
noncomputable def cyclicOddComparisonHom (A : Rep k G) (g : G) :
    shortComplexH3 A ⟶ Rep.FiniteCyclicGroup.subCompNormHom A g where
  τ₁ := cyclicSumTwo A g
  τ₂ := cyclicSumThree A g
  τ₃ := cyclicSumFour A g
  comm₁₂ := cyclicSumTwo_comp_sub A g
  comm₂₃ := cyclicSumThree_comp_norm A g

/-- A degree-three cocycle's cyclic sum is killed by the norm. -/
theorem cyclicSumThree_norm_eq_zero (A : Rep k G) (g : G)
    (z : cocycles₃ A) :
    ∑ a : G, A.ρ a (cyclicSumThree A g z) = 0 := by
  have hcomm := ConcreteCategory.congr_hom
    (cyclicSumThree_comp_norm A g) z
  change A.norm.asHom.hom (cyclicSumThree A g z) =
    cyclicSumFour A g (d₃₄ A z) at hcomm
  rw [Rep.norm_apply, Representation.norm, LinearMap.sum_apply] at hcomm
  calc
    (∑ a : G, A.ρ a (cyclicSumThree A g z)) =
        cyclicSumFour A g (d₃₄ A z) := hcomm
    _ = cyclicSumFour A g 0 := congrArg _ z.property
    _ = 0 := map_zero _

/-- A degree-three cocycle mapped into the kernel of the finite-group norm. -/
noncomputable def cyclicThreeCocycleInvariant (A : Rep k G) (g : G) :
    cocycles₃ A →ₗ[k] LinearMap.ker A.norm.asHom.hom.toLinearMap :=
  LinearMap.codRestrict (LinearMap.ker A.norm.asHom.hom.toLinearMap)
    ((cyclicSumThree A g).hom.comp (cocycles₃ A).subtype) (fun z => by
    rw [LinearMap.mem_ker]
    change A.norm.asHom.hom (cyclicSumThree A g z) = 0
    rw [Rep.norm_apply]
    rw [Representation.norm]
    rw [LinearMap.sum_apply]
    exact cyclicSumThree_norm_eq_zero A g z)

@[simp]
theorem cyclicThreeCocycleInvariant_coe
    (A : Rep k G) (g : G) (z : cocycles₃ A) :
    (cyclicThreeCocycleInvariant A g z : A) = cyclicSumThree A g z :=
  rfl

/-- The explicit odd periodic quotient `Ker(N) / Im(rho(g)-1)`. -/
noncomputable abbrev cyclicOddQuotient (A : Rep k G) (g : G) : ModuleCat k :=
  (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.H

/-- Quotient map from norm-kernel representatives to the explicit odd
periodic quotient, before comparison with inhomogeneous cohomology. -/
noncomputable abbrev cyclicOddHomologyπ (A : Rep k G) (g : G) :
    ↧(LinearMap.ker A.norm.asHom.hom.toLinearMap) ⟶
      cyclicOddQuotient A g :=
  (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.π

/-- The explicit odd quotient map vanishes exactly on
`Im(rho(g)-1)`. -/
theorem cyclicOddHomologyπ_eq_zero_iff
    (A : Rep k G) (g : G)
    (x : LinearMap.ker A.norm.asHom.hom.toLinearMap) :
    cyclicOddHomologyπ A g x = 0 ↔
      x.1 ∈ LinearMap.range
        (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
  change Submodule.Quotient.mk x = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change x ∈ LinearMap.range
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatToCycles ↔ _
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    exact congrArg Subtype.val hy
  · rintro ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact hy

/-- A degree-three coboundary has zero image in the explicit odd cyclic
homology quotient. -/
theorem cyclicOddHomologyπ_cyclicThreeCocycleInvariant_eq_zero
    (A : Rep k G) (g : G)
    (z : cocycles₃ A) (hz : H3π A z = 0) :
    cyclicOddHomologyπ A g (cyclicThreeCocycleInvariant A g z) = 0 := by
  rw [cyclicOddHomologyπ_eq_zero_iff A g]
  obtain ⟨t, ht⟩ := (H3π_eq_zero_iff z).mp hz
  refine ⟨∑ h : G, t (h, g), ?_⟩
  change A.ρ g (∑ h : G, t (h, g)) - ∑ h : G, t (h, g) =
    cyclicSumThree A g z
  rw [← cyclicSumThree_d₂₃ A g t, ht]

/-- The composite cocycle invariant kills the kernel of the inhomogeneous
H3 quotient map. -/
theorem cyclicThreeCocycleInvariant_ker_le
    (A : Rep k G) (g : G) :
    LinearMap.ker (H3π A).hom ≤
      LinearMap.ker ((cyclicOddHomologyπ A g).hom.comp
        (cyclicThreeCocycleInvariant A g)) := by
  intro z hz
  rw [LinearMap.mem_ker]
  exact cyclicOddHomologyπ_cyclicThreeCocycleInvariant_eq_zero
    A g z hz

/-- Map from ordinary H3 to the concrete odd cyclic quotient induced by
the explicit low-degree short-complex comparison. -/
noncomputable def cyclicOddComparisonQuotientMap
    (A : Rep k G) (g : G) :
    H3 A ⟶ cyclicOddQuotient A g :=
  (H3Iso A).hom ≫
    ShortComplex.leftHomologyMap'
      (cyclicOddComparisonHom A g)
      (shortComplexH3 A).moduleCatLeftHomologyData
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData

/-- On explicit cycles, the low-degree comparison's cycle map is the
cyclic invariant `sum_h z(g,h,g)`. -/
theorem cyclesMap_cyclicOddComparisonHom_apply
    (A : Rep k G) (g : G) (z : cocycles₃ A) :
    ShortComplex.cyclesMap'
        (cyclicOddComparisonHom A g)
        (shortComplexH3 A).moduleCatLeftHomologyData
        (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData z =
      cyclicThreeCocycleInvariant A g z := by
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The low-degree comparison sends the class of `z` to the quotient
class of its explicit cyclic invariant. -/
theorem cyclicOddComparisonQuotientMap_H3π
    (A : Rep k G) (g : G) (z : cocycles₃ A) :
    cyclicOddComparisonQuotientMap A g (H3π A z) =
      cyclicOddHomologyπ A g (cyclicThreeCocycleInvariant A g z) := by
  have hH3m : H3π A ≫ (H3Iso A).hom =
      (shortComplexH3 A).moduleCatLeftHomologyData.π := by
    simp only [H3π, Category.assoc, π_comp_H3Iso_hom,
      Iso.inv_hom_id_assoc]
  have hm : H3π A ≫ cyclicOddComparisonQuotientMap A g =
      ShortComplex.cyclesMap'
          (cyclicOddComparisonHom A g)
          (shortComplexH3 A).moduleCatLeftHomologyData
          (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData ≫
        (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.π := by
    unfold cyclicOddComparisonQuotientMap
    rw [← Category.assoc, hH3m]
    exact ShortComplex.leftHomologyπ_naturality'
      (cyclicOddComparisonHom A g)
      (shortComplexH3 A).moduleCatLeftHomologyData
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData
  have hz := ConcreteCategory.congr_hom hm z
  change cyclicOddComparisonQuotientMap A g (H3π A z) = _
  rw [← cyclesMap_cyclicOddComparisonHom_apply A g z]
  exact hz

/-- Explicit comparison from inhomogeneous H3 to the odd periodic cyclic
homology model, obtained by descending the cyclic sum invariant. -/
noncomputable def cyclicH3ToOddHomology
    (A : Rep k G) (g : G) :
    H3 A →ₗ[k] cyclicOddQuotient A g :=
  (cyclicOddComparisonQuotientMap A g).hom

/-- Representative computation for the explicit cyclic H3 comparison. -/
@[simp]
theorem cyclicH3ToOddHomology_H3π
    (A : Rep k G) (g : G)
    (z : cocycles₃ A) :
    cyclicH3ToOddHomology A g (H3π A z) =
      cyclicOddHomologyπ A g (cyclicThreeCocycleInvariant A g z) := by
  exact cyclicOddComparisonQuotientMap_H3π A g z

/-- The direct quotient descent is exactly the map induced by the explicit
low-degree short-complex comparison. -/
theorem cyclicH3ToOddHomology_eq_cyclicOddComparisonQuotientMap
    (A : Rep k G) (g : G) :
    cyclicH3ToOddHomology A g =
      (cyclicOddComparisonQuotientMap A g).hom :=
  rfl

/-- Mathlib's cyclic-resolution computation of `H3` as the explicit odd
periodic quotient `Ker(N) / Im(rho(g)-1)`.  This equivalence is canonical
relative to Mathlib's chosen projective-resolution comparison. -/
noncomputable def cyclicH3OddLinearEquiv
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    H3 A ≃ₗ[k] cyclicOddQuotient A g :=
  ((Rep.FiniteCyclicGroup.groupCohomologyIsoOdd
    A g hg 3 (by exact ⟨1, rfl⟩)) ≪≫
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatHomologyIso).toLinearEquiv

/-- The precise remaining compatibility with Mathlib's abstract cyclic
resolution comparison. -/
def CyclicH3ComparisonCompatible
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
  cyclicH3ToOddHomology A g =
    (cyclicH3OddLinearEquiv A g hg).toLinearMap

/-- Compatibility with Mathlib's abstract comparison is equivalent to
the expected cyclic-sum formula on every inhomogeneous representative. -/
theorem cyclicH3ComparisonCompatible_iff
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    CyclicH3ComparisonCompatible A g hg ↔
      ∀ z : cocycles₃ A,
        cyclicH3OddLinearEquiv A g hg (H3π A z) =
          cyclicOddHomologyπ A g
            (cyclicThreeCocycleInvariant A g z) := by
  constructor
  · intro h z
    change (cyclicH3OddLinearEquiv A g hg).toLinearMap (H3π A z) = _
    rw [← h]
    exact cyclicH3ToOddHomology_H3π A g z
  · intro h
    apply LinearMap.ext
    intro c
    refine H3_induction_on c ?_
    intro z
    rw [cyclicH3ToOddHomology_H3π]
    exact (h z).symm

/-- Cohomologous degree-three cocycles have cyclic invariants differing by
an element of `Im(rho(g)-1)`. -/
theorem cyclicThreeCocycleInvariant_sub_mem_range
    (A : Rep k G) (g : G) (x y : cocycles₃ A)
    (hxy : H3π A x = H3π A y) :
    (cyclicThreeCocycleInvariant A g x : A) -
        cyclicThreeCocycleInvariant A g y ∈
      LinearMap.range
        (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
  obtain ⟨t, ht⟩ := (H3π_eq_iff x y).mp hxy
  refine ⟨∑ h : G, t (h, g), ?_⟩
  change A.ρ g (∑ h : G, t (h, g)) - ∑ h : G, t (h, g) = _
  rw [← cyclicSumThree_d₂₃ A g t, ht]
  rw [map_sub]
  rw [cyclicThreeCocycleInvariant_coe, cyclicThreeCocycleInvariant_coe]

/-- Cyclic invariant of a degree-`(1,2)` cup representative. -/
theorem cyclicSumThree_cupCocycleOneTwo
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cyclicSumThree (A ⊗ B) g
        (cupCocycleOneTwo A B x y) =
      ∑ h : G, x g ⊗ₜ[k] B.ρ g (y (h, g)) :=
  rfl

/-- Norm-kernel representative of a degree-`(1,2)` cup in the explicit
odd periodic model. -/
noncomputable def cyclicCupOneTwoInvariant
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    LinearMap.ker (A ⊗ B).norm.asHom.hom.toLinearMap :=
  cyclicThreeCocycleInvariant (A ⊗ B) g
    (cupCocycleOneTwo A B x y)

@[simp]
theorem cyclicCupOneTwoInvariant_coe
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    (cyclicCupOneTwoInvariant A B g x y).1 =
      ∑ h : G, x g ⊗ₜ[k] B.ρ g (y (h, g)) := by
  rw [cyclicCupOneTwoInvariant, cyclicThreeCocycleInvariant_coe,
    cyclicSumThree_cupCocycleOneTwo]

/-- The explicit odd-quotient image of a degree-`(1,2)` cup class. -/
theorem cyclicH3ToOddHomology_cupOneTwo
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cyclicH3ToOddHomology (A ⊗ B) g
        (H3π (A ⊗ B) (cupCocycleOneTwo A B x y)) =
      cyclicOddHomologyπ (A ⊗ B) g
        (cyclicCupOneTwoInvariant A B g x y) :=
  cyclicH3ToOddHomology_H3π (A ⊗ B) g _

/-- Cyclic invariant of the landed right-associated triple cup
representative. -/
theorem cyclicSumThree_nestedCupOneOne
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    cyclicSumThree (A ⊗ (B ⊗ C)) g
        (cupCocycleOneTwo A (B ⊗ C) x
          (cupCocycleOneOne B C y z)) =
      ∑ h : G, x g ⊗ₜ[k]
        (B ⊗ C).ρ g (y h ⊗ₜ[k] C.ρ h (z g)) :=
  rfl

/-- Norm-kernel representative of a right-associated triple cup in the
explicit odd periodic model. -/
noncomputable def cyclicNestedCupOneOneInvariant
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    LinearMap.ker (A ⊗ (B ⊗ C)).norm.asHom.hom.toLinearMap :=
  cyclicThreeCocycleInvariant (A ⊗ (B ⊗ C)) g
    (cupCocycleOneTwo A (B ⊗ C) x
      (cupCocycleOneOne B C y z))

@[simp]
theorem cyclicNestedCupOneOneInvariant_coe
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    (cyclicNestedCupOneOneInvariant A B C g x y z).1 =
      ∑ h : G, x g ⊗ₜ[k]
        (B ⊗ C).ρ g (y h ⊗ₜ[k] C.ρ h (z g)) := by
  rw [cyclicNestedCupOneOneInvariant,
    cyclicThreeCocycleInvariant_coe,
    cyclicSumThree_nestedCupOneOne]

/-- The explicit odd-quotient image of a right-associated triple cup
class. -/
theorem cyclicH3ToOddHomology_nestedCupOneOne
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    cyclicH3ToOddHomology (A ⊗ (B ⊗ C)) g
        (H3π (A ⊗ (B ⊗ C))
          (cupCocycleOneTwo A (B ⊗ C) x
            (cupCocycleOneOne B C y z))) =
      cyclicOddHomologyπ (A ⊗ (B ⊗ C)) g
        (cyclicNestedCupOneOneInvariant A B C g x y z) :=
  cyclicH3ToOddHomology_H3π (A ⊗ (B ⊗ C)) g _

/-- Under the exact comparison compatibility isolated above, Mathlib's
cyclic-resolution equivalence sends a right-associated triple cup to its
explicit cyclic-sum representative. -/
theorem cyclicH3OddLinearEquiv_nestedCupOneOne_of_compatible
    (A B C : Rep k G) (g : G)
    (hg : ∀ a, a ∈ Subgroup.zpowers g)
    (hcompat : CyclicH3ComparisonCompatible (A ⊗ (B ⊗ C)) g hg)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    cyclicH3OddLinearEquiv (A ⊗ (B ⊗ C)) g hg
        (H3π (A ⊗ (B ⊗ C))
          (cupCocycleOneTwo A (B ⊗ C) x
            (cupCocycleOneOne B C y z))) =
      cyclicOddHomologyπ (A ⊗ (B ⊗ C)) g
        (cyclicNestedCupOneOneInvariant A B C g x y z) :=
  (cyclicH3ComparisonCompatible_iff
    (A ⊗ (B ⊗ C)) g hg).mp hcompat _

end groupCohomology
