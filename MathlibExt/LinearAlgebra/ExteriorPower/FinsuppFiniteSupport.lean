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

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Finite support of exterior powers of a free coefficient module

The finite coordinate inclusion is the existing finite linear-combination
map. Its coordinate restriction is a retraction, so the native exterior-power
map is injective. Every exterior element comes from some finite coordinate
module: write it as a finite sum of decomposable wedges and unite the finite
supports of their vectors. No ordered or finite basis of the ambient module
is assumed.
-/

@[expose] public section

noncomputable section

universe u v

namespace Finsupp

variable (R : Type u) [CommRing R] {I : Type v}

/-- The original finite coordinate inclusion as a native linear combination. -/
def finsetInclude (s : Finset I) : (s → R) →ₗ[R] (I →₀ R) := by
  classical
  exact Fintype.linearCombination R (fun i : s => Finsupp.single i.val 1)

/-- Restrict the original finitely supported vector to the finite coordinates. -/
def finsetRestrict (s : Finset I) : (I →₀ R) →ₗ[R] (s → R) :=
  LinearMap.pi (fun i : s => Finsupp.lapply i.val)

theorem finsetInclude_apply (s : Finset I) (m : s → R) :
    finsetInclude R s m = ∑ i : s, Finsupp.single i.val (m i) := by
  classical
  simp only [finsetInclude, Fintype.linearCombination_apply,
    Finsupp.smul_single, smul_eq_mul, mul_one]

@[simp]
theorem finsetRestrict_apply (s : Finset I) (m : I →₀ R) (i : s) :
    finsetRestrict R s m i = m i.val := rfl

/-- The actual coordinate restriction retracts the actual inclusion. -/
theorem finsetRestrict_comp_include (s : Finset I) :
    (finsetRestrict R s).comp (finsetInclude R s) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro m
  funext i
  change finsetRestrict R s (finsetInclude R s m) i = m i
  rw [finsetRestrict_apply, finsetInclude_apply]
  change (Finsupp.lapply i.val : (I →₀ R) →ₗ[R] R)
    (∑ j : s, Finsupp.single j.val (m j)) = m i
  rw [map_sum, Finset.sum_eq_single i]
  · simp only [Finsupp.lapply_apply, Finsupp.single_eq_same]
  · intro j hj hji
    have hval : j.val ≠ i.val := fun h => hji (Subtype.ext h)
    simp only [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hval.symm]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- Restriction followed by inclusion recovers a vector whose support is
contained in the original finite coordinate set. -/
theorem finsetInclude_restrict_of_support_subset (s : Finset I) (m : I →₀ R)
    (hm : m.support ⊆ s) : finsetInclude R s (finsetRestrict R s m) = m := by
  classical
  apply Finsupp.ext
  intro a
  rw [finsetInclude_apply]
  change (Finsupp.lapply a : (I →₀ R) →ₗ[R] R)
    (∑ j : s, Finsupp.single j.val (finsetRestrict R s m j)) = m a
  rw [map_sum]
  by_cases ha : a ∈ s
  · let i : s := ⟨a, ha⟩
    rw [Finset.sum_eq_single i]
    · simp only [Finsupp.lapply_apply, i, Finsupp.single_eq_same, finsetRestrict_apply]
    · intro j hj hji
      have hval : j.val ≠ a := fun h => hji (Subtype.ext h)
      simp only [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hval.symm]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · have hzero : m a = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => ha (hm h))
    rw [hzero]
    apply Finset.sum_eq_zero
    intro j hj
    have hval : j.val ≠ a := fun h => ha (h ▸ j.property)
    simp only [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hval.symm]

end Finsupp

namespace exteriorPower

variable (R : Type u) [CommRing R] {I : Type v}

/-- The native exterior map of the original finite coordinate inclusion is
injective because the original coordinate restriction is a retraction. -/
theorem map_finsetInclude_injective (s : Finset I) (n : ℕ) :
    Function.Injective (map n (Finsupp.finsetInclude R s)) :=
  map_injective (Finsupp.finsetRestrict R s) (Finsupp.finsetRestrict_comp_include R s)

/-- Every exterior element of the arbitrary free coordinate module has an
actual preimage in the exterior power of a finite coordinate module. -/
theorem exists_preimage_finset (n : ℕ) (z : ⋀[R]^n (I →₀ R)) :
    ∃ s : Finset I, ∃ zS : ⋀[R]^n (s → R),
      map n (Finsupp.finsetInclude R s) zS = z := by
  classical
  have hz : z ∈ Submodule.span R
      (Set.range (ιMulti R n (M := I →₀ R))) := by
    rw [ιMulti_span]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  let s : Finset I := c.support.biUnion
    (fun a => Finset.univ.biUnion (fun j : Fin n => (a j).support))
  let zS : ⋀[R]^n (s → R) := c.sum
    (fun a r => r • ιMulti R n (fun j => Finsupp.finsetRestrict R s (a j)))
  refine ⟨s, zS, ?_⟩
  change map n (Finsupp.finsetInclude R s)
    (c.sum (fun a r => r • ιMulti R n (fun j => Finsupp.finsetRestrict R s (a j)))) = z
  calc
    _ = c.sum (fun a r => r •
        map n (Finsupp.finsetInclude R s)
          (ιMulti R n (fun j => Finsupp.finsetRestrict R s (a j)))) := by
      simp only [Finsupp.sum, map_sum, map_smul]
    _ = c.sum (fun a r => r • ιMulti R n a) := by
      simp only [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply congrArg (fun q : ⋀[R]^n (I →₀ R) => c a • q)
      rw [map_apply_ιMulti]
      apply congrArg (ιMulti R n)
      funext j
      change Finsupp.finsetInclude R s (Finsupp.finsetRestrict R s (a j)) = a j
      apply Finsupp.finsetInclude_restrict_of_support_subset
      intro i hi
      exact Finset.mem_biUnion.mpr
        ⟨a, ha, Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hi⟩⟩
    _ = z := hc

end exteriorPower
