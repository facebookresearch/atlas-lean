/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitrary

/-!
# Differential compatibility of arbitrary Schreier transfer

The chosen-transversal `Fin n` transfer commutes with the arbitrary
inhomogeneous group-cohomology differential.  Thus the degreewise transfer
maps assemble into a cochain map in every degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators
open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionArbitraryDifferentialFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Reindexing the leading differential term by the Schreier permutation,
with an arbitrary remaining factor tuple. -/
theorem sum_rho_mul_schreierRep_inv_factorTuple
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    {n : ℕ} (f : (Fin n → H) → A) (g : Fin (n + 1) → G) :
    (∑ t : (T : Set G),
      A.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
        (f (T.schreierFactorTuple (T.schreierRep t (g 0))
          (Fin.tail g)))) =
      A.ρ (g 0)
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (f (T.schreierFactorTuple t (Fin.tail g)))) := by
  calc
    (∑ t : (T : Set G),
        A.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
          (f (T.schreierFactorTuple (T.schreierRep t (g 0))
            (Fin.tail g)))) =
        ∑ t : (T : Set G),
          A.ρ (g 0 * (t : G)⁻¹)
            (f (T.schreierFactorTuple t (Fin.tail g))) :=
      (T.schreierRepEquiv (g 0)).sum_comp
        (fun t : (T : Set G) ↦
          A.ρ (g 0 * (t : G)⁻¹)
            (f (T.schreierFactorTuple t (Fin.tail g))))
    _ = ∑ t : (T : Set G),
        A.ρ (g 0)
          (A.ρ (t : G)⁻¹
            (f (T.schreierFactorTuple t (Fin.tail g)))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ (g 0)
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (f (T.schreierFactorTuple t (Fin.tail g)))) := by
      rw [map_sum]

/-- Arbitrary-degree Schreier transfer commutes pointwise with the
inhomogeneous differential. -/
theorem corestrictionCochain_d
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ) (f : (Fin n → H) → A) :
    corestrictionCochain A T (n + 1)
        ((inhomogeneousCochains.d
          (Rep.res (Subgroup.subtype H) A) n).hom f) =
      (inhomogeneousCochains.d A n).hom
        (corestrictionCochain A T n f) := by
  funext g
  simp only [corestrictionCochain_apply,
    inhomogeneousCochains.d_hom_apply, map_add, map_sum, map_smul]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  · have hlead : (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          ((Rep.res (Subgroup.subtype H) A).ρ
            (T.schreierFactorTuple t g 0)
            (f (fun i ↦ T.schreierFactorTuple t g i.succ)))) =
        A.ρ (g 0)
          (∑ t : (T : Set G),
            A.ρ (t : G)⁻¹
              (f (T.schreierFactorTuple t (Fin.tail g)))) := by
      have hterms : (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            ((Rep.res (Subgroup.subtype H) A).ρ
              (T.schreierFactorTuple t g 0)
              (f (fun i ↦ T.schreierFactorTuple t g i.succ)))) =
          ∑ t : (T : Set G),
            A.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
              (f (T.schreierFactorTuple (T.schreierRep t (g 0))
                (Fin.tail g))) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Subgroup.RightTransversal.schreierFactorTuple_zero]
        change A.ρ (t : G)⁻¹
            (A.ρ (T.schreierFactor t (g 0) : G)
              (f (fun i ↦ T.schreierFactorTuple t g i.succ))) = _
        rw [← Module.End.mul_apply, ← map_mul,
          T.inv_mul_schreierFactor t (g 0)]
        congr 2
        exact (Subgroup.RightTransversal.schreierFactorTuple_tail T t g).symm
      rw [hterms]
      exact sum_rho_mul_schreierRep_inv_factorTuple A T f g
    simpa only [map_sum, Fin.tail_def] using hlead
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t _
    congr 2
    exact congrArg f
      (Subgroup.RightTransversal.schreierFactorTuple_contractNth T t g j).symm

/-- The arbitrary-degree chosen-transversal transfers assemble into a
cochain map. -/
noncomputable def corestrictionCochains
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.inhomogeneousCochains
        (Rep.res (Subgroup.subtype H) A) ⟶
      groupCohomology.inhomogeneousCochains A where
  f n := ModuleCat.ofHom (corestrictionCochain A T n)
  comm' i j hij := by
    subst j
    rw [groupCohomology.inhomogeneousCochains.d_def,
      groupCohomology.inhomogeneousCochains.d_def]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (corestrictionCochain_d A T i f).symm

@[simp]
theorem corestrictionCochains_f
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (corestrictionCochains A T).f n =
      ModuleCat.ofHom (corestrictionCochain A T n) :=
  rfl

/-- Arbitrary-degree group-cohomological transfer attached to one right
transversal. -/
noncomputable def corestrictionOfRightTransversal
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    groupCohomology (Rep.res (Subgroup.subtype H) A) n ⟶
      groupCohomology A n :=
  HomologicalComplex.homologyMap (corestrictionCochains A T) n

/-- Arbitrary-degree representative formula for chosen-transversal
corestriction. -/
theorem corestrictionOfRightTransversal_π
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (z : groupCohomology.cocycles
      (Rep.res (Subgroup.subtype H) A) n) :
    corestrictionOfRightTransversal A T n
        (groupCohomology.π (Rep.res (Subgroup.subtype H) A) n z) =
      groupCohomology.π A n
        (HomologicalComplex.cyclesMap
          (corestrictionCochains A T) n z) := by
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (corestrictionCochains A T) n) z

/-- The transferred generic cycle has the arbitrary Schreier cochain as its
underlying inhomogeneous cochain. -/
theorem iCocycles_corestriction_cyclesMap
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (z : groupCohomology.cocycles
      (Rep.res (Subgroup.subtype H) A) n) :
    groupCohomology.iCocycles A n
        (HomologicalComplex.cyclesMap
          (corestrictionCochains A T) n z) =
      corestrictionCochain A T n
        (groupCohomology.iCocycles
          (Rep.res (Subgroup.subtype H) A) n z) := by
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (corestrictionCochains A T) n) z

@[simp]
theorem corestrictionOfRightTransversal_zero
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    corestrictionOfRightTransversal A T n 0 = 0 :=
  map_zero _

end groupCohomology
