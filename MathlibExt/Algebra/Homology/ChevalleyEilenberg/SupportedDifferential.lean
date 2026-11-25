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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Canonical
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.BracketBoundaryList
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Chevalley–Eilenberg differentials supported in one degree

Projection to exterior degree n + 1 followed by the Chevalley–Eilenberg differential defines
an endomorphism of the full exterior algebra. It agrees with the boundary on that homogeneous
component and vanishes on the other components.

Consecutive supported differentials compose to zero. Ordered-wedge formulas express the
boundary as a signed sum over pairs of Lie inputs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Extend the differential from exterior degree `n + 1` by zero on every other homogeneous
degree, using the grading projection. -/
def supportedDifferential (n : ℕ) : Module.End R (ExteriorAlgebra R L) :=
  (boundary R L).comp (_root_.GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i L) (n + 1))

/-- On its input degree, the supported differential is the canonical exterior boundary. -/
theorem supportedDifferential_of_mem (n : ℕ) (a : ExteriorAlgebra R L)
    (ha : a ∈ ⋀[R]^(n + 1) L) :
    supportedDifferential R L n a = boundary R L a := by
  simp only [supportedDifferential, LinearMap.comp_apply, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[R]^i L) ha]

/-- The supported differential vanishes on every other input degree. -/
theorem supportedDifferential_of_mem_ne (n m : ℕ) (a : ExteriorAlgebra R L)
    (ha : a ∈ ⋀[R]^m L) (hm : m ≠ n + 1) :
    supportedDifferential R L n a = 0 := by
  simp only [supportedDifferential, LinearMap.comp_apply, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[R]^i L) ha hm, map_zero]

/-- The supported operator agrees with the degree-restricted differential on the canonical
exterior-power subtype. -/
@[simp]
theorem supportedDifferential_apply_exteriorPower (n : ℕ) (a : ⋀[R]^(n + 1) L) :
    supportedDifferential R L n a = (differential R L n a : ExteriorAlgebra R L) := by
  rw [supportedDifferential_of_mem R L n a a.property, differential_coe]

/-- Consecutive supported CE differentials compose to zero on the whole exterior algebra,
including inputs outside their selected degrees. -/
theorem supportedDifferential_comp_supportedDifferential (n : ℕ) :
    (supportedDifferential R L n).comp (supportedDifferential R L (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  have hproj :
      GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i L) (n + 1 + 1) a ∈
        ⋀[R]^(n + 1 + 1) L :=
    (DirectSum.decompose (fun i : ℕ => ⋀[R]^i L) a (n + 1 + 1)).property
  have hdegree : supportedDifferential R L (n + 1) a ∈ ⋀[R]^(n + 1) L := by
    simpa only [supportedDifferential, LinearMap.comp_apply, Nat.add_sub_cancel] using
      boundary_mem_exteriorPower R L (n + 1 + 1) _ hproj
  change supportedDifferential R L n (supportedDifferential R L (n + 1) a) = 0
  rw [supportedDifferential_of_mem R L n _ hdegree]
  exact boundary_squared R L _

/-- The supported operator from exterior degree one to degree zero vanishes on the whole exterior
algebra. -/
@[simp]
theorem supportedDifferential_zero : supportedDifferential R L 0 = 0 := by
  apply LinearMap.ext
  intro a
  let b : ⋀[R]^1 L := DirectSum.decompose (fun i : ℕ => ⋀[R]^i L) a 1
  have hd : differential R L 0 = 0 := (canonicalPresentedData R L).d_zero
  change boundary R L (b : ExteriorAlgebra R L) = 0
  simpa only [differential_coe, LinearMap.zero_apply, ZeroMemClass.coe_zero] using
    congrArg (fun z : ⋀[R]^0 L => (z : ExteriorAlgebra R L))
      (LinearMap.congr_fun hd b)

/-- The global boundary on any pure word is the full strict-pair sum in ordered list notation,
including scalar and one-vector input. -/
theorem boundary_ιMulti_eq_sum_pairs (n : ℕ) (v : Fin n → L) :
    boundary R L (ExteriorAlgebra.ιMulti R n v) =
      ∑ i : Fin n, ∑ j : Fin n,
        if i.val < j.val then
          ((-1 : R) ^ (i.val + j.val)) •
            (ExteriorAlgebra.ι R ⁅v i, v j⁆ *
              ((((List.ofFn v).eraseIdx j.val).eraseIdx i.val).map
                (ExteriorAlgebra.ι R)).prod)
        else 0 := by
  cases n with
  | zero => simp only [ExteriorAlgebra.ιMulti_zero_apply, boundary_one, Fin.sum_univ_zero]
  | succ n => rw [boundary_ιMulti, bracketBoundary_coe_eq_sum_pairs]

/-- The canonical CE boundary on a list of generators has the ordered bracket-and-deletion
formula, with no chosen differential involved. -/
theorem boundary_prod_map_ι (xs : List L) :
    boundary R L (xs.map (ExteriorAlgebra.ι R)).prod =
      ∑ i : Fin xs.length, ∑ j : Fin xs.length,
        if i.val < j.val then
          ((-1 : R) ^ (i.val + j.val)) •
            (ExteriorAlgebra.ι R ⁅xs.get i, xs.get j⁆ *
              (((xs.eraseIdx j.val).eraseIdx i.val).map (ExteriorAlgebra.ι R)).prod)
        else 0 := by
  have hmap : (List.ofFn xs.get).map (ExteriorAlgebra.ι R) =
      List.ofFn (fun i => ExteriorAlgebra.ι R (xs.get i)) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rfl
  have hword : ExteriorAlgebra.ιMulti R xs.length xs.get =
      (xs.map (ExteriorAlgebra.ι R)).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, ← hmap, List.ofFn_get]
  have h := boundary_ιMulti_eq_sum_pairs R L xs.length xs.get
  rw [hword] at h
  simpa only [List.ofFn_get] using h

end ChevalleyEilenberg
