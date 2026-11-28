/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalCoreInterval
public import MathlibExt.Algebra.Homology.PartialTotalNegativeVanishing
public import MathlibExt.Algebra.Homology.PartialTotalStepVanishing

/-!
# Spectral-sequence existence for the partial-total filtration

Let `B` be a first-quadrant bicomplex in an abelian category. The partial-total spectral
object satisfies the two vanishing conditions for the increasing homological spectral-sequence
core.

If a bidegree has no outgoing page-`r` arrow, the associated outer-left interval has zero
homology by vanishing of negative filtration stages. If it has no incoming page-`r` arrow, the
outer-right interval has zero homology below the support of its row. These statements
construct the spectral-sequence instance for all natural bidegrees.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- Outer-left interval vanishing when a page arrow has no target.

Let `r` and `r'` be integers with `1 ≤ r` and `r + 1 = r'`. Suppose the page-`r` differential
shape has no arrow out of `pq`. For `n = core.deg pq + 1`, the homology object associated to
the interval `core.i₀ r' pq ⟶ core.i₀ r pq` is zero. First-quadrant support places this
interval at negative partial-total stages. -/
theorem partialTotalSpectralObject_isZero_i₀_le
    (r r' : ℤ) (pq : ℕ × ℕ)
    (hpq : ∀ pq' : ℕ × ℕ,
      ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq pq')
    (n : ℤ) (hn : n = (core).deg pq + 1)
    (hrr' : r + 1 = r') (hr : 1 ≤ r) :
    IsZero ((B.partialTotalSpectralObject.H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₀_le r r' pq hrr' hr)))) := by
  rcases pq with ⟨p, q⟩
  subst r'
  subst n
  have hpr : (p : ℤ) < r := by
    by_contra h
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ (p : ℤ) - r by omega)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ (q : ℤ) + r - 1 by omega)
    exact hpq ⟨p', q'⟩ (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> omega)
  have hneg := B.isZero_partialTotalSpectralObjectHObj_of_neg
    ((core).deg (p, q) + 1) ((p : ℤ) - (r + 1)) ((p : ℤ) - r)
    (by omega) (by omega) (by omega)
  convert hneg using 1; subsingleton

/-- Outer-right interval vanishing when a page arrow has no source.

Let `r` and `r'` be integers with `1 ≤ r` and `r + 1 = r'`. Suppose the page-`r` differential
shape has no arrow into `pq`. For `n = core.deg pq - 1`, the homology object associated to the
interval `core.i₃ r pq ⟶ core.i₃ r' pq` is zero. First-quadrant support puts this degree below
the contributing row. -/
theorem partialTotalSpectralObject_isZero_i₃_le
    (r r' : ℤ) (pq : ℕ × ℕ)
    (hpq : ∀ pq' : ℕ × ℕ,
      ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq' pq)
    (n : ℤ) (hn : n = (core).deg pq - 1)
    (hrr' : r + 1 = r') (hr : 1 ≤ r) :
    IsZero ((B.partialTotalSpectralObject.H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₃_le r r' pq hrr' hr)))) := by
  rcases pq with ⟨p, q⟩
  subst r'
  subst n
  have hqr : (q : ℤ) < r - 1 := by
    by_contra h
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ (p : ℤ) + r by omega)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ (q : ℤ) - r + 1 by omega)
    exact hpq ⟨p', q'⟩ (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> omega)
  obtain ⟨P, hP⟩ := Int.eq_ofNat_of_zero_le
    (show 0 ≤ (p : ℤ) + r by omega)
  let k := p + q + 1
  have hk : k < P := by
    dsimp [k]
    omega
  have hLower : (core).i₃ r (p, q) = (core).i₁ (P, 0) := by
    change (((p : ℤ) + r - 1 : ℤ) : EInt) =
      (((P : ℤ) - 1 : ℤ) : EInt)
    apply congrArg (fun z : ℤ ↦ (z : EInt))
    omega
  have hUpper : (core).i₃ (r + 1) (p, q) = (core).i₂ (P, 0) := by
    change (((p : ℤ) + (r + 1) - 1 : ℤ) : EInt) = ((P : ℤ) : EInt)
    apply congrArg (fun z : ℤ ↦ (z : EInt))
    omega
  let F := B.partialTotalCochainFiltration
  let outerMap := F.map
    (homOfLE ((core).i₃_le r (r + 1) (p, q) (hrr' := by omega) (hr := hr)))
  let coreMap := F.map (homOfLE ((core).le₁₂ (P, 0)))
  let indexIso : CategoryTheory.ComposableArrows.mk₁ outerMap ≅
      CategoryTheory.ComposableArrows.mk₁ coreMap :=
    CategoryTheory.ComposableArrows.isoMk₁
      (eqToIso (congrArg F.obj hLower))
      (eqToIso (congrArg F.obj hUpper)) (by
        change outerMap ≫ eqToHom (congrArg F.obj hUpper) =
          eqToHom (congrArg F.obj hLower) ≫ coreMap
        rw [← eqToHom_map F hLower, ← eqToHom_map F hUpper,
          ← F.map_comp, ← F.map_comp]
        congr 1)
  let stepIso := indexIso ≪≫ B.partialTotalE₁CochainStepIso P 0
  let coneIso := (HomotopyCategory.composableArrowsFunctor C).mapIso stepIso
  have hStep := B.isZero_partialTotalStepConeHomology_of_lt P k hk
  have hCone : IsZero ((CochainComplex.mappingCone outerMap).homology
      (-(k : ℤ))) :=
    IsZero.of_iso hStep (HomologicalComplex.homologyMapIso coneIso (-(k : ℤ)))
  have hOuter : IsZero ((B.partialTotalSpectralObject.H (-(k : ℤ))).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₃_le r (r + 1) (p, q)
          (hrr' := by omega) (hr := hr))))) :=
    IsZero.of_iso hCone
      (B.partialTotalSpectralObjectHObjIso (-(k : ℤ))
        ((core).i₃_le r (r + 1) (p, q) (hrr' := by omega) (hr := hr)))
  have hdeg : -(k : ℤ) = (core).deg (p, q) - 1 := by
    dsimp [k]
    change -((p + q + 1 : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ) - 1
    push_cast
    omega
  have hdeg' : (core).deg (p, q) - 1 = -(k : ℤ) := hdeg.symm
  convert hOuter using 1
  exact congrArg (fun z : ℤ ↦
    (B.partialTotalSpectralObject.H z).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₃_le r (r + 1) (p, q)
          (hrr' := by omega) (hr := hr))))) hdeg'

/-- Spectral sequence of the first-quadrant partial-total object.

The partial-total spectral object of a first-quadrant bicomplex in an abelian category has a
spectral sequence for the increasing homological core. The required vanishing conditions are
the outer-left and outer-right interval vanishing statements. -/
instance partialTotalSpectralObject_hasSpectralSequence :
    B.partialTotalSpectralObject.HasSpectralSequence core where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr :=
    B.partialTotalSpectralObject_isZero_i₀_le
      r r' pq hpq n hn hrr' hr
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr :=
    B.partialTotalSpectralObject_isZero_i₃_le
      r r' pq hpq n hn hrr' hr

end HomologicalComplex₂

end
