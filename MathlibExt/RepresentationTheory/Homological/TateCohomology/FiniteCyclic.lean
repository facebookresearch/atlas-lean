/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic

@[expose] public noncomputable section

open CategoryTheory Limits ModuleCat Rep

namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
variable (A : Rep R G)

/-- Normalized degree-zero short complex. -/
private noncomputable abbrev zeroSC : ShortComplex (ModuleCat R) :=
  ShortComplex.mk A.norm.asHom.toModuleCatHom
    (groupCohomology.d₀₁ A) (Rep.norm_comp_d_eq_zero A)

/-- Normalized degree-minus-one short complex. -/
private noncomputable abbrev negOneSC : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (groupHomology.d₁₀ A)
    A.norm.asHom.toModuleCatHom (Rep.comp_eq_zero A)

/-- Normalization iso for the `(-1, 0, 1)` boundary short complex. -/
private noncomputable def zeroNormIso :
    (tateComplex A).sc' (-1) 0 1 ≅ zeroSC A :=
  ShortComplex.isoMk (groupHomology.chainsIso₀ A)
    (groupCohomology.cochainsIso₀ A) (groupCohomology.cochainsIso₁ A)
    (by
      change (groupHomology.chainsIso₀ A).hom ≫ A.norm.asHom.toModuleCatHom =
        A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom
      rw [Rep.tateNorm, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (groupCohomology.comp_d₀₁_eq A)

/-- Normalization iso for the `(-2, -1, 0)` boundary short complex. -/
private noncomputable def negOneNormIso :
    (tateComplex A).sc' (-2) (-1) 0 ≅ negOneSC A :=
  ShortComplex.isoMk (groupHomology.chainsIso₁ A)
    (groupHomology.chainsIso₀ A) (groupCohomology.cochainsIso₀ A)
    (groupHomology.comp_d₁₀_eq A)
    (by
      change (groupHomology.chainsIso₀ A).hom ≫ A.norm.asHom.toModuleCatHom =
        A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom
      rw [Rep.tateNorm, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Degree-zero bridge, ending at the normalized short complex homology. -/
private noncomputable def zeroBridge :
    tateCohomology A 0 ≅ (zeroSC A).homology :=
  ((tateComplex A).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).trans
    (ShortComplex.homologyMapIso (zeroNormIso A))

private lemma zeroSC_ker_eq (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (zeroSC A).g.hom =
      LinearMap.ker (Rep.FiniteCyclicGroup.normHomCompSub A g).g.hom := by
  change LinearMap.ker (groupCohomology.d₀₁ A).hom =
    LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap
  rw [groupCohomology.d₀₁_ker_eq_invariants]
  ext x
  simpa [Rep.sub_hom, sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x

private noncomputable def zeroKernelEquiv (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (zeroSC A).g.hom ≃ₗ[R]
      LinearMap.ker (Rep.FiniteCyclicGroup.normHomCompSub A g).g.hom :=
  LinearEquiv.ofEq _ _ (zeroSC_ker_eq A g hg)

private lemma zeroSC_range_map_eq (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (LinearMap.range (zeroSC A).moduleCatToCycles).map
        (zeroKernelEquiv A g hg).toLinearMap =
      LinearMap.range
        (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatToCycles := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    simp [zeroKernelEquiv, zeroSC,
      Rep.FiniteCyclicGroup.normHomCompSub,
      ShortComplex.moduleCatToCycles]
  · rintro ⟨z, rfl⟩
    refine ⟨_, ⟨z, rfl⟩, ?_⟩
    apply Subtype.ext
    simp [zeroKernelEquiv, zeroSC,
      Rep.FiniteCyclicGroup.normHomCompSub,
      ShortComplex.moduleCatToCycles]

private noncomputable def zeroIso (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A 0 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A g).homology :=
  zeroBridge A ≪≫
    (zeroSC A).moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv _ _ (zeroKernelEquiv A g hg)
      (zeroSC_range_map_eq A g hg)).toModuleIso ≪≫
    (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatHomologyIso.symm

/-- Degree-minus-one bridge, ending at the normalized short complex homology. -/
private noncomputable def negOneBridge :
    tateCohomology A (-1) ≅ (negOneSC A).homology :=
  ((tateComplex A).homologyIsoSc' (-2) (-1) 0 (by simp) (by simp)).trans
    (ShortComplex.homologyMapIso (negOneNormIso A))

private lemma negOneSC_range_eq (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.range (negOneSC A).moduleCatToCycles =
      LinearMap.range
        (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatToCycles := by
  change LinearMap.range ((groupHomology.d₁₀ A).hom.codRestrict
      (LinearMap.ker A.norm.asHom.hom.toLinearMap) _) =
    LinearMap.range ((Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap.codRestrict
      (LinearMap.ker A.norm.asHom.hom.toLinearMap) _)
  have hRange : LinearMap.range (groupHomology.d₁₀ A).hom =
      LinearMap.range (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
    rw [groupHomology.range_d₁₀_eq_coinvariantsKer,
      Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg]
    ext x; simp [Rep.sub_hom]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hmem := LinearMap.mem_range_self (groupHomology.d₁₀ A).hom y
    rw [hRange] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, Subtype.ext hz⟩
  · rintro ⟨y, rfl⟩
    have hmem :=
      LinearMap.mem_range_self (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap y
    rw [← hRange] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, Subtype.ext hz⟩

private noncomputable def negOneIso (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-1) ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A g).homology :=
  negOneBridge A ≪≫
    (negOneSC A).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (negOneSC_range_eq A g hg)).toModuleIso ≪≫
    (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatHomologyIso.symm

private noncomputable def positivePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) [NeZero i] :
    tateCohomology A (i : ℤ) ≅ tateCohomology A ((i + 2 : ℕ) : ℤ) := by
  letI : NeZero (i + 2) := ⟨by omega⟩
  by_cases hi : Even i
  · have h2 : Even (i + 2) := hi.add even_two
    simpa using ((isoGroupCohomology (R := R) (G := G) i).app A ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg i hi ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg (i + 2) h2).symm ≪≫
      ((isoGroupCohomology (R := R) (G := G) (i + 2)).app A).symm)
  · have ho : Odd i := Nat.not_even_iff_odd.mp hi
    have ho2 : Odd (i + 2) := ho.add_even even_two
    simpa using ((isoGroupCohomology (R := R) (G := G) i).app A ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg i ho ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg (i + 2) ho2).symm ≪≫
      ((isoGroupCohomology (R := R) (G := G) (i + 2)).app A).symm)

private noncomputable def negativePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) :
    tateCohomology A (-(i + 4 : ℤ)) ≅ tateCohomology A (-(i + 2 : ℤ)) := by
  letI : DecidableEq G := Classical.decEq G
  letI : NeZero (i + 3) := ⟨by omega⟩
  letI : NeZero (i + 1) := ⟨by omega⟩
  by_cases h : Even (i + 1)
  · have h3 : Even (i + 3) := by simpa [Nat.add_assoc] using h.add even_two
    exact ((TateCohomology.isoGroupHomology (-(i + 4 : ℤ)) (i + 3) (by omega)).app A ≪≫
      Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg (i + 3) h3 ≪≫
      (Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg (i + 1) h).symm ≪≫
      ((TateCohomology.isoGroupHomology (-(i + 2 : ℤ)) (i + 1) (by omega)).app A).symm)
  · have ho : Odd (i + 1) := Nat.not_even_iff_odd.mp h
    have ho3 : Odd (i + 3) := by simpa [Nat.add_assoc] using ho.add_even even_two
    exact ((TateCohomology.isoGroupHomology (-(i + 4 : ℤ)) (i + 3) (by omega)).app A ≪≫
      Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg (i + 3) ho3 ≪≫
      (Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg (i + 1) ho).symm ≪≫
      ((TateCohomology.isoGroupHomology (-(i + 2 : ℤ)) (i + 1) (by omega)).app A).symm)

private noncomputable def zeroPeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A 0 ≅ tateCohomology A 2 := by
  letI : NeZero 2 := ⟨by omega⟩
  simpa using (zeroIso A g hg ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm ≪≫
    ((isoGroupCohomology (R := R) (G := G) 2).app A).symm)

private noncomputable def negOnePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-1) ≅ tateCohomology A 1 := by
  letI : NeZero 1 := ⟨by omega⟩
  simpa using (negOneIso A g hg ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm ≪≫
    ((isoGroupCohomology (R := R) (G := G) 1).app A).symm)

private noncomputable def negTwoPeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-2) ≅ tateCohomology A 0 := by
  letI : DecidableEq G := Classical.decEq G
  letI : NeZero 1 := ⟨by omega⟩
  simpa using (((isoGroupHomology (R := R) (G := G) (-2) 1 (by omega)).app A) ≪≫
    Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg 1 odd_one ≪≫
    (zeroIso A g hg).symm)

private noncomputable def negThreePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-3) ≅ tateCohomology A (-1) := by
  letI : DecidableEq G := Classical.decEq G
  letI : NeZero 2 := ⟨by omega⟩
  simpa using (((isoGroupHomology (R := R) (G := G) (-3) 2 (by omega)).app A) ≪≫
    Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg 2 even_two ≪≫
    (negOneIso A g hg).symm)

/-- Tate cohomology of a finite cyclic group is two-periodic. -/
theorem nonempty_periodicityIso {R G : Type u} [CommRing R] [Group G]
    [Fintype G] [IsCyclic G] (A : Rep R G) (n : ℤ) :
    Nonempty (tateCohomology A n ≅ tateCohomology A (n + 2)) := by
  let _ : CommGroup G := IsCyclic.commGroup
  let _ : DecidableEq G := Classical.decEq G
  let g : G := (IsCyclic.exists_generator (α := G)).choose
  have hg : ∀ x, x ∈ Subgroup.zpowers g :=
    (IsCyclic.exists_generator (α := G)).choose_spec
  refine ⟨?_⟩
  cases n with
  | ofNat i =>
    cases i with
    | zero => simpa using zeroPeriodicityIso A g hg
    | succ i =>
      letI : NeZero (i + 1) := ⟨by omega⟩
      simpa using positivePeriodicityIso A g hg (i + 1)
  | negSucc i =>
    cases i with
    | zero => simpa using negOnePeriodicityIso A g hg
    | succ i =>
      cases i with
      | zero => simpa using negTwoPeriodicityIso A g hg
      | succ i =>
        cases i with
        | zero => simpa using negThreePeriodicityIso A g hg
        | succ i =>
          convert negativePeriodicityIso A g hg i using 1 <;>
            simp [Int.negSucc_eq] <;> ring_nf

end TateCohomology
