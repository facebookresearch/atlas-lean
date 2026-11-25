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

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Directed closed unions of nonunital C-star ideals

A nonempty directed family of closed two-sided star ideals has a closed union
ideal obtained by closing its algebraic directed union. All carriers, scalar
operations and topology are inherited from the ambient algebra. No complete
lattice or alternative quotient structure is installed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ClosedStarIdeal

universe uA uI

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {ι : Type uI} [Nonempty ι]

/-- **Directed supremum of closed star ideals.** Let `A` be a nonunital complex C*-algebra and `(Iᵢ)ᵢ∈ι`
a nonempty directed family of closed two-sided star ideals of `A`, ordered by inclusion. The norm
closure of `⋃ i, Iᵢ` is the least closed two-sided star ideal containing the whole family. -/
def directedSup (I : ι → ClosedStarIdeal A) (hI : Directed (· ≤ ·) I) :
    ClosedStarIdeal A := by
  let S : NonUnitalStarSubalgebra ℂ A := ⨆ i, (I i).carrier
  have hS : (S : Set A) = ⋃ i, ((I i).carrier : Set A) := by
    apply NonUnitalStarSubalgebra.coe_iSup_of_directed
    intro i j
    obtain ⟨k, hik, hjk⟩ := hI i j
    exact ⟨k, hik, hjk⟩
  have hleft (a : A) : Set.MapsTo (fun x : A => a * x) (S : Set A) S := by
    intro x hx
    rw [hS] at hx ⊢
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, (I i).isTwoSided.mul_mem_left a hxi⟩
  have hright (a : A) : Set.MapsTo (fun x : A => x * a) (S : Set A) S := by
    intro x hx
    rw [hS] at hx ⊢
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, (I i).isTwoSided.mul_mem_right hxi a⟩
  have hstar : Set.MapsTo (star : A → A) (S : Set A) S := by
    intro x hx
    exact StarMemClass.star_mem (s := S) hx
  let D : Submodule ℂ A :=
    (NonUnitalStarSubalgebra.quotientSubmodule S).topologicalClosure
  have hD : (D : Set A) = closure (S : Set A) := by
    rw [Submodule.topologicalClosure_coe]
    rfl
  let T : NonUnitalStarSubalgebra ℂ A :=
    { toNonUnitalSubalgebra :=
        { carrier := D
          zero_mem' := D.zero_mem
          add_mem' := D.add_mem
          smul_mem' := by
            intro c x hx
            exact D.smul_mem c hx
          mul_mem' := by
            intro x y _hx hy
            change y ∈ (D : Set A) at hy
            rw [hD] at hy ⊢
            exact ((hleft x).closure (continuous_id'.const_mul x)) hy }
      star_mem' := by
        intro x hx
        change x ∈ (D : Set A) at hx
        rw [hD] at hx ⊢
        exact (hstar.closure continuous_star) hx }
  refine
    { carrier := T
      isTwoSided := ?_
      isClosed := ?_ }
  · constructor
    · intro a x hx
      change a * x ∈ (D : Set A)
      change x ∈ (D : Set A) at hx
      rw [hD] at hx ⊢
      exact ((hleft a).closure (continuous_id'.const_mul a)) hx
    · intro x hx a
      change x * a ∈ (D : Set A)
      change x ∈ (D : Set A) at hx
      rw [hD] at hx ⊢
      exact ((hright a).closure (continuous_id'.mul_const a)) hx
  · change IsClosed (D : Set A)
    rw [hD]
    exact isClosed_closure

/-- **Carrier of a directed closed-ideal supremum.** Let `A` be a nonunital complex C*-algebra and
`(Iᵢ)ᵢ∈ι` a nonempty directed family of closed two-sided star ideals of `A`, ordered by inclusion.
The carrier of the directed supremum is exactly the norm closure of `⋃ i, Iᵢ`. -/
theorem directedSup_carrier (I : ι → ClosedStarIdeal A)
    (hI : Directed (· ≤ ·) I) :
    ((directedSup I hI).carrier : Set A) =
      closure (⋃ i, ((I i).carrier : Set A)) := by
  change
    (((NonUnitalStarSubalgebra.quotientSubmodule
      (⨆ i, (I i).carrier)).topologicalClosure : Submodule ℂ A) : Set A) =
        closure (⋃ i, ((I i).carrier : Set A))
  rw [Submodule.topologicalClosure_coe]
  change closure ((⨆ i, (I i).carrier : NonUnitalStarSubalgebra ℂ A) : Set A) = _
  rw [NonUnitalStarSubalgebra.coe_iSup_of_directed (by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hI i j
    exact ⟨k, hik, hjk⟩)]

/-- **Each ideal lies in the directed supremum.** Let `A` be a nonunital complex C*-algebra and
`(Iᵢ)ᵢ∈ι` a nonempty directed family of closed two-sided star ideals of `A`, ordered by inclusion.
Every `Iᵢ` is contained in the closed ideal defined by the norm closure of the union. -/
theorem le_directedSup (I : ι → ClosedStarIdeal A)
    (hI : Directed (· ≤ ·) I) (i : ι) : I i ≤ directedSup I hI := by
  intro x hx
  change x ∈ ((directedSup I hI).carrier : Set A)
  rw [directedSup_carrier]
  exact subset_closure (Set.mem_iUnion.mpr ⟨i, hx⟩)

/-- **Least-upper-bound property of a directed supremum.** Let `A` be a nonunital complex C*-algebra and
`(Iᵢ)ᵢ∈ι` a nonempty directed family of closed two-sided star ideals of `A`, ordered by inclusion.
If a closed two-sided star ideal `K` contains every `Iᵢ`, it contains their directed supremum. -/
theorem directedSup_le (I : ι → ClosedStarIdeal A)
    (hI : Directed (· ≤ ·) I) (K : ClosedStarIdeal A)
    (hK : ∀ i, I i ≤ K) : directedSup I hI ≤ K := by
  intro x hx
  change x ∈ (K.carrier : Set A)
  change x ∈ ((directedSup I hI).carrier : Set A) at hx
  rw [directedSup_carrier] at hx
  exact closure_minimal (Set.iUnion_subset fun i => hK i) K.isClosed hx

end ClosedStarIdeal
