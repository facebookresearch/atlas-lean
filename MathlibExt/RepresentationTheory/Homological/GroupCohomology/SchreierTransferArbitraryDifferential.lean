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
# Differential compatibility and cohomology of Schreier transfer

For a finite-index H ≤ G, right transversal T and G-representation A, the tuple transfer
cor_Tⁿ(f)(g) = ∑ₜ ρ(t⁻¹)f(T.schreierFactorTuple t g) commutes with the inhomogeneous group-
cohomology differential, with its usual alternating signs: cor_Tⁿ⁺¹(dⁿf) = dⁿ(cor_Tⁿf).

The degreewise maps therefore assemble into a cochain map C*(H,A|H) → C*(G,A). Applying
homology gives a map Hⁿ(H,A|H) → Hⁿ(G,A) in every degree, whose value on a represented class
is the class of the transferred cycle.
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

/-- Finite representatives for differential-compatible transfer.

The finite-index hypothesis supplies the finite right-transversal type used in the cochain
differential and transfer sums. -/
noncomputable local instance corestrictionArbitraryDifferentialFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The leading differential sum after a Schreier update.

For g = (g₀,…,gₙ), the sum weighted by ρ(g₀r(t,g₀)⁻¹) over the factor tuples of the tail
starting at r(t,g₀) equals ρ(g₀) times the ordinary transfer sum of that tail. -/
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

/-- Arbitrary-degree transfer commutes with the differential.

For every n and H-cochain f, transferring dⁿf in degree n+1 equals applying the G-differential
dⁿ to the degree-n transfer of f. -/
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

/-- The Schreier transfer as a cochain-complex morphism.

The chosen-transversal maps in all degrees define a morphism from the inhomogeneous cochain
complex of A|H to that of A. -/
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

/-- The degree component of the transfer cochain map.

The component in degree n of corestrictionCochains A T is the ModuleCat morphism of the linear
map corestrictionCochain A T n. -/
@[simp]
theorem corestrictionCochains_f
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (corestrictionCochains A T).f n =
      ModuleCat.ofHom (corestrictionCochain A T n) :=
  rfl

/-- The cohomological transfer in an arbitrary degree.

For n ≥ 0, apply homology to the chosen-transversal cochain map to obtain Hⁿ(H,A|H) → Hⁿ(G,A). -/
noncomputable def corestrictionOfRightTransversal
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    groupCohomology (Rep.res (Subgroup.subtype H) A) n ⟶
      groupCohomology A n :=
  HomologicalComplex.homologyMap (corestrictionCochains A T) n

/-- The arbitrary-degree transfer on a cycle class.

Applying the transfer to the class of z ∈ Zⁿ(H,A|H) gives the class of the cycle obtained by
applying the transfer cochain map to z. -/
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

/-- The cochain underlying a transferred arbitrary-degree cycle.

Including the transferred cycle into G-cochains gives the degree-n Schreier transfer of the
included H-cycle cochain. -/
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

/-- The transfer preserves the zero class in every degree.

For each n, the chosen-transversal cohomology map sends 0 in Hⁿ(H,A|H) to 0 in Hⁿ(G,A). -/
@[simp]
theorem corestrictionOfRightTransversal_zero
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    corestrictionOfRightTransversal A T n 0 = 0 :=
  map_zero _

end groupCohomology
