/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.IdealCountFaces
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Naive ideal-count subcomplexes and their associated complexes

For the relative naive quotient kernel, the stages F_p,n require at least n + 1 − p ideal
entries and are preserved by the full Hochschild b boundary. The predecessor L_p is zero at p
= 0 and F_(p−1) otherwise, so it is also a subcomplex.

Restricting b defines the filtered and predecessor complexes, with their component inclusion
maps. Quotienting F_p,n by L_p,n viewed inside it defines the associated complex. Its
differential is induced by the restricted boundary, and the quotient projections form a chain
map which kills the predecessor inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

private theorem originalNaiveBoundary_square (n : ℕ)
    (x : (relativeNaiveComplex k A I).X (n + 2)) :
    ((relativeNaiveComplex k A I).d (n + 1) n).hom
      (((relativeNaiveComplex k A I).d (n + 2) (n + 1)).hom x) = 0 := by
  have h := congrArg
    (fun f : (relativeNaiveComplex k A I).X (n + 2) ⟶
      (relativeNaiveComplex k A I).X n => f.hom x)
    ((relativeNaiveComplex k A I).d_comp_d (n + 2) (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] using h

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. For p,n : ℕ, L_p,n ≤ F_p,n. -/
theorem naiveLowerWordFiltration_le (p n : ℕ) :
    naiveLowerFiltration k A I p n ≤ naiveWordFiltration k A I p n := by
  by_cases hp : p = 0
  · simp only [naiveLowerFiltration, hp, ite_eq_left, bot_le]
  · simpa only [naiveLowerFiltration, ite_eq_right hp] using
      (naiveWordFiltration_mono k A I (Nat.sub_le p 1) n)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. For p,n : ℕ, the image of L_p,n+1 under K_b.d (n + 1) n lies in L_p,n, including
the zero predecessor at p = 0. -/
theorem naiveLowerWordFiltration_d (p n : ℕ) :
    (naiveLowerFiltration k A I p (n + 1)).map
        ((relativeNaiveComplex k A I).d (n + 1) n).hom ≤
      naiveLowerFiltration k A I p n := by
  by_cases hp : p = 0
  · subst p
    simp [naiveLowerFiltration]
  · simpa only [naiveLowerFiltration, ite_eq_right hp] using
      (naiveWordFiltration_d k A I (p - 1) n)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveStageD p n : F_p,n+1 →ₗ[k] F_p,n is the relative kernel boundary with its
domain and codomain restricted to these stages. -/
def naiveStageD (p n : ℕ) :
    naiveWordFiltration k A I p (n + 1) →ₗ[k] naiveWordFiltration k A I p n :=
  LinearMap.codRestrict (naiveWordFiltration k A I p n)
    (((relativeNaiveComplex k A I).d (n + 1) n).hom.domRestrict
      (naiveWordFiltration k A I p (n + 1)))
    (fun x => (Submodule.map_le_iff_le_comap.mp (naiveWordFiltration_d k A I p n)) x.property)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveLowerStageD p n : L_p,n+1 →ₗ[k] L_p,n is the restriction of the relative
boundary to the lower stages. -/
def naiveLowerStageD (p n : ℕ) :
    naiveLowerFiltration k A I p (n + 1) →ₗ[k] naiveLowerFiltration k A I p n :=
  LinearMap.codRestrict (naiveLowerFiltration k A I p n)
    (((relativeNaiveComplex k A I).d (n + 1) n).hom.domRestrict
      (naiveLowerFiltration k A I p (n + 1)))
    (fun x => (Submodule.map_le_iff_le_comap.mp
      (naiveLowerWordFiltration_d k A I p n)) x.property)

private theorem naiveStageD_square (p n : ℕ) :
    ModuleCat.ofHom (naiveStageD k A I p (n + 1)) ≫
      ModuleCat.ofHom (naiveStageD k A I p n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((relativeNaiveComplex k A I).d (n + 1) n).hom
      (((relativeNaiveComplex k A I).d (n + 2) (n + 1)).hom x.val) = 0
  exact originalNaiveBoundary_square k A I n x.val

private theorem naiveLowerStageD_square (p n : ℕ) :
    ModuleCat.ofHom (naiveLowerStageD k A I p (n + 1)) ≫
      ModuleCat.ofHom (naiveLowerStageD k A I p n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((relativeNaiveComplex k A I).d (n + 1) n).hom
      (((relativeNaiveComplex k A I).d (n + 2) (n + 1)).hom x.val) = 0
  exact originalNaiveBoundary_square k A I n x.val

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveFilteredWordComplex p has degree-n module F_p,n and successor differential
naiveStageD p n. Its square-zero law is inherited from K_b. -/
def naiveFilteredWordComplex (p : ℕ) : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (naiveWordFiltration k A I p n))
    (fun n => ModuleCat.ofHom (naiveStageD k A I p n)) (by exact naiveStageD_square k A I p)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveLowerWordComplex p has degree-n module L_p,n and differential naiveLowerStageD
p n; at p = 0 all these modules are zero. -/
def naiveLowerWordComplex (p : ℕ) : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (naiveLowerFiltration k A I p n))
    (fun n => ModuleCat.ofHom (naiveLowerStageD k A I p n))
    (by exact naiveLowerStageD_square k A I p)

@[simp]
theorem naiveFilteredWordComplex_X (p n : ℕ) :
    (naiveFilteredWordComplex k A I p).X n =
      ModuleCat.of k (naiveWordFiltration k A I p n) := rfl

@[simp]
theorem naiveLowerWordComplex_X (p n : ℕ) :
    (naiveLowerWordComplex k A I p).X n =
      ModuleCat.of k (naiveLowerFiltration k A I p n) := rfl

private theorem naiveFilteredWordComplex_d (p n : ℕ) :
    (naiveFilteredWordComplex k A I p).d (n + 1) n =
      ModuleCat.ofHom (naiveStageD k A I p n) :=
  ChainComplex.of_d (fun m => ModuleCat.of k (naiveWordFiltration k A I p m))
    (fun m => ModuleCat.ofHom (naiveStageD k A I p m)) n

private theorem naiveLowerWordComplex_d (p n : ℕ) :
    (naiveLowerWordComplex k A I p).d (n + 1) n =
      ModuleCat.ofHom (naiveLowerStageD k A I p n) :=
  ChainComplex.of_d (fun m => ModuleCat.of k (naiveLowerFiltration k A I p m))
    (fun m => ModuleCat.ofHom (naiveLowerStageD k A I p m)) n

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. For x : F_p,n+1, inclusion of the filtered differential's value into K_b.X n equals
K_b.d (n + 1) n applied to x.val. -/
theorem naiveFilteredWordComplex_d_val (p n : ℕ)
    (x : naiveWordFiltration k A I p (n + 1)) :
    (naiveWordFiltration k A I p n).subtype
      (((naiveFilteredWordComplex k A I p).d (n + 1) n).hom x) =
      ((relativeNaiveComplex k A I).d (n + 1) n).hom x.val := by
  rw [naiveFilteredWordComplex_d]
  rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveFilteredWordInclusion p : naiveFilteredWordComplex p ⟶ K_b has degree-n
component F_p,n.subtype. -/
def naiveFilteredWordInclusion (p : ℕ) :
    naiveFilteredWordComplex k A I p ⟶ relativeNaiveComplex k A I :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (naiveWordFiltration k A I p n).subtype)
    (fun n => by
      rw [naiveFilteredWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

@[simp]
theorem naiveFilteredWordInclusion_f (p n : ℕ) :
    (naiveFilteredWordInclusion k A I p).f n =
      ModuleCat.ofHom (naiveWordFiltration k A I p n).subtype := rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveLowerWordInclusion p maps naiveLowerWordComplex p to naiveFilteredWordComplex
p by the component inclusions L_p,n ≤ F_p,n. -/
def naiveLowerWordInclusion (p : ℕ) :
    naiveLowerWordComplex k A I p ⟶ naiveFilteredWordComplex k A I p :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (Submodule.inclusion (naiveLowerWordFiltration_le k A I p n)))
    (fun n => by
      rw [naiveFilteredWordComplex_d, naiveLowerWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. For p ≤ q, naiveFilteredWordMap maps naiveFilteredWordComplex p to
naiveFilteredWordComplex q using the inclusions F_p,n ≤ F_q,n in every degree. -/
def naiveFilteredWordMap {p q : ℕ} (h : p ≤ q) :
    naiveFilteredWordComplex k A I p ⟶ naiveFilteredWordComplex k A I q :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (Submodule.inclusion (naiveWordFiltration_mono k A I h n)))
    (fun n => by
      rw [naiveFilteredWordComplex_d, naiveFilteredWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveLayerD p n maps F_p,n+1/L_p,n+1 to F_p,n/L_p,n by the quotient map induced
from naiveStageD p n and lower-stage preservation. -/
def naiveLayerD (p n : ℕ) :
    naiveWordLayer k A I p (n + 1) →ₗ[k] naiveWordLayer k A I p n :=
  ((naiveLowerFiltration k A I p (n + 1)).comap
    (naiveWordFiltration k A I p (n + 1)).subtype).mapQ
    ((naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype)
    (naiveStageD k A I p n) (by
      intro x hx
      change ((relativeNaiveComplex k A I).d (n + 1) n).hom x.val ∈
        naiveLowerFiltration k A I p n
      exact (Submodule.map_le_iff_le_comap.mp
        (naiveLowerWordFiltration_d k A I p n)) hx)

private theorem naiveLayerD_projection (p n : ℕ)
    (x : naiveWordFiltration k A I p (n + 1)) :
    naiveLayerD k A I p n (naiveWordLayerProjection k A I p (n + 1) x) =
      naiveWordLayerProjection k A I p n (naiveStageD k A I p n x) := rfl

private theorem naiveLayerD_square (p n : ℕ) :
    ModuleCat.ofHom (naiveLayerD k A I p (n + 1)) ≫
      ModuleCat.ofHom (naiveLayerD k A I p n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on _ y ?_
  intro x
  change naiveLayerD k A I p n
    (naiveLayerD k A I p (n + 1) (naiveWordLayerProjection k A I p (n + 2) x)) = 0
  rw [naiveLayerD_projection, naiveLayerD_projection]
  have hs : naiveStageD k A I p n (naiveStageD k A I p (n + 1) x) = 0 := by
    apply Subtype.ext
    exact originalNaiveBoundary_square k A I n x.val
  rw [hs, map_zero]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveAssociatedWordComplex p has degree-n object F_p,n modulo the inverse image of
L_p,n inside F_p,n, and differential naiveLayerD p n. -/
def naiveAssociatedWordComplex (p : ℕ) : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (naiveWordLayer k A I p n))
    (fun n => ModuleCat.ofHom (naiveLayerD k A I p n)) (by exact naiveLayerD_square k A I p)

@[simp]
theorem naiveAssociatedWordComplex_X (p n : ℕ) :
    (naiveAssociatedWordComplex k A I p).X n =
      ModuleCat.of k (naiveWordLayer k A I p n) := rfl

private theorem naiveAssociatedWordComplex_d (p n : ℕ) :
    (naiveAssociatedWordComplex k A I p).d (n + 1) n =
      ModuleCat.ofHom (naiveLayerD k A I p n) :=
  ChainComplex.of_d (fun m => ModuleCat.of k (naiveWordLayer k A I p m))
    (fun m => ModuleCat.ofHom (naiveLayerD k A I p m)) n

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveAssociatedWordProjection p maps naiveFilteredWordComplex p to
naiveAssociatedWordComplex p by naiveWordLayerProjection p n in degree n. -/
def naiveAssociatedWordProjection (p : ℕ) :
    naiveFilteredWordComplex k A I p ⟶ naiveAssociatedWordComplex k A I p :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (naiveWordLayerProjection k A I p n))
    (fun n => by
      rw [naiveFilteredWordComplex_d, naiveAssociatedWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact naiveLayerD_projection k A I p n x)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. For x : F_p,n+1, the associated differential of [x] is [naiveStageD p n x] in
F_p,n/L_p,n. -/
theorem naiveAssociatedWordComplex_d_projection (p n : ℕ)
    (x : naiveWordFiltration k A I p (n + 1)) :
    ((naiveAssociatedWordComplex k A I p).d (n + 1) n).hom
        (naiveWordLayerProjection k A I p (n + 1) x) =
      naiveWordLayerProjection k A I p n
        (((naiveFilteredWordComplex k A I p).d (n + 1) n).hom x) := by
  rw [naiveAssociatedWordComplex_d, naiveFilteredWordComplex_d]
  exact naiveLayerD_projection k A I p n x

@[simp]
theorem naiveAssociatedWordProjection_f (p n : ℕ) :
    (naiveAssociatedWordProjection k A I p).f n =
      ModuleCat.ofHom (naiveWordLayerProjection k A I p n) := rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. naiveLowerWordInclusion p ≫ naiveAssociatedWordProjection p = 0 as a chain map from
the predecessor complex to the associated complex. -/
theorem naiveLowerWordInclusion_projection (p : ℕ) :
    naiveLowerWordInclusion k A I p ≫ naiveAssociatedWordProjection k A I p = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change naiveWordLayerProjection k A I p n
    (Submodule.inclusion (naiveLowerWordFiltration_le k A I p n) x) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact x.property

theorem naiveLowerWordComplex_zero_X (n : ℕ) :
    (naiveLowerWordComplex k A I 0).X n =
      ModuleCat.of k (⊥ : Submodule k ((relativeNaiveComplex k A I).X n)) := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
