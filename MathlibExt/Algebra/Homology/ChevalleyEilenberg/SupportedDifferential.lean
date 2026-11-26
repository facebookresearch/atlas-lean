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
# Exterior CE differentials supported in one input degree

Let ∂ be the exterior CE boundary. For n : ℕ, compose projection onto exterior degree n + 1
with ∂ to obtain an endomorphism D_n of the full exterior algebra. It equals ∂ on that degree
and is zero on all other homogeneous degrees. Consecutive supported operators compose to zero,
and D₀ is zero.

On an ordered list of generators, ∂ is the strict-pair sum with coefficient (−1)^(i+j). The
bracket [x_i,x_j] is placed first, and the remaining product deletes position j before i so
the other entries keep their order. The same formula applies to pure exterior words, including
lengths zero and one.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For n : ℕ, supportedDifferential R L n = ∂ ∘
GradedAlgebra.proj_(n+1) : E →ₗ[R] E, using the canonical homogeneous decomposition. -/
def supportedDifferential (n : ℕ) : Module.End R (ExteriorAlgebra R L) :=
  (boundary R L).comp (_root_.GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i L) (n + 1))

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For a ∈ ⋀[R]^(n+1) L inside E, supportedDifferential n a =
∂(a). -/
theorem supportedDifferential_of_mem (n : ℕ) (a : ExteriorAlgebra R L)
    (ha : a ∈ ⋀[R]^(n + 1) L) :
    supportedDifferential R L n a = boundary R L a := by
  simp only [supportedDifferential, LinearMap.comp_apply, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[R]^i L) ha]

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For a ∈ ⋀[R]^m L and m ≠ n + 1, supportedDifferential n a = 0. -/
theorem supportedDifferential_of_mem_ne (n m : ℕ) (a : ExteriorAlgebra R L)
    (ha : a ∈ ⋀[R]^m L) (hm : m ≠ n + 1) :
    supportedDifferential R L n a = 0 := by
  simp only [supportedDifferential, LinearMap.comp_apply, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[R]^i L) ha hm, map_zero]

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For a : ⋀[R]^(n+1) L, supportedDifferential n a is the
inclusion in E of differential R L n a. -/
@[simp]
theorem supportedDifferential_apply_exteriorPower (n : ℕ) (a : ⋀[R]^(n + 1) L) :
    supportedDifferential R L n a = (differential R L n a : ExteriorAlgebra R L) := by
  rw [supportedDifferential_of_mem R L n a a.property, differential_coe]

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For every n : ℕ, supportedDifferential n ∘
supportedDifferential (n + 1) = 0 as R-linear endomorphisms of E. -/
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

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. supportedDifferential R L 0 = 0 on the whole exterior algebra,
since the CE boundary vanishes on degree one. -/
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

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For v : Fin n → L, ∂(ιMulti v) is ∑ i,j : Fin n with i<j, (−1 :
R)^(i+j) • (ι([v_i,v_j]) * product of the remaining ordered generators). The remaining list is
(List.ofFn v).eraseIdx j then eraseIdx i, so the larger index is removed first. -/
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

/-- Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For xs : List L, ∂(product(xs.map ι)) is the sum over i<j in
Fin xs.length of (−1 : R)^(i+j) times ι([xs_i,xs_j]) followed by the product of xs with index
j then i erased. Empty and one-entry lists have an empty pair sum. -/
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
