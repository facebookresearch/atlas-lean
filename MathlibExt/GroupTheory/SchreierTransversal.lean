/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- AI-assisted original formalization: Avocado; responsible human author: @toskua.
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Group

/-!
# Schreier representatives and subgroup factors

Let H be a subgroup of G and T a right transversal, so every g ∈ G has a unique decomposition
g = h·t with h ∈ H and t ∈ T. For t ∈ T, write tg = a(t,g)·r(t,g). The new representatives
satisfy r(t,g₁g₂) = r(r(t,g₁),g₂), and the factors satisfy a(t,g₁g₂) = a(t,g₁)a(r(t,g₁),g₂).

For a finite tuple (g₀,…,gₙ₋₁), the representative scan starts at t and updates by right
multiplication. Its subgroup factors multiply to the subgroup component of t times each
partial product. Contracting adjacent tuple entries or removing the first entry gives the
corresponding contractions and tails of the factor and representative scans.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Subgroup.RightTransversal

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- The new representative after right multiplication.

For t ∈ T and g ∈ G, r(t,g) is the unique representative in T for which tg = h·r(t,g) with h ∈
H. -/
noncomputable def schreierRep (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) : (T : Set G) :=
  (T.2.equiv ((t : G) * g)).2

/-- The subgroup factor after right multiplication.

For t ∈ T and g ∈ G, a(t,g) is the unique element of H satisfying tg = a(t,g)·r(t,g). -/
noncomputable def schreierFactor (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) : H :=
  (T.2.equiv ((t : G) * g)).1

/-- The Schreier decomposition of a product.

The subgroup factor and representative satisfy a(t,g)·r(t,g) = tg in G. -/
theorem schreierFactor_mul_schreierRep (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) :
    (schreierFactor T t g : G) * (schreierRep T t g : G) =
      (t : G) * g :=
  T.2.equiv_fst_mul_equiv_snd ((t : G) * g)

/-- The inverse representative formula for a subgroup factor.

The decomposition tg = a(t,g)r(t,g) implies t⁻¹a(t,g) = g r(t,g)⁻¹. The multiplication order
is retained in the ambient group G. -/
theorem inv_mul_schreierFactor (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) :
    (t : G)⁻¹ * (schreierFactor T t g : G) =
      g * (schreierRep T t g : G)⁻¹ := by
  rw [schreierFactor, schreierRep,
    T.2.equiv_fst_eq_mul_inv ((t : G) * g)]
  group

/-- Successive right multiplication of representatives.

For g₁,g₂ ∈ G, the representative obtained from tg₁g₂ is r(t,g₁g₂) = r(r(t,g₁),g₂). -/
theorem schreierRep_mul (T : H.RightTransversal)
    (t : (T : Set G)) (g₁ g₂ : G) :
    schreierRep T t (g₁ * g₂) =
      schreierRep T (schreierRep T t g₁) g₂ := by
  change (T.2.equiv ((t : G) * (g₁ * g₂))).2 =
    (T.2.equiv (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).2
  calc
    (T.2.equiv ((t : G) * (g₁ * g₂))).2 =
        (T.2.equiv
          ((schreierFactor T t g₁ : G) *
            ((schreierRep T t g₁ : G) * g₂))).2 := by
      congr 2
      calc
        (t : G) * (g₁ * g₂) = ((t : G) * g₁) * g₂ :=
          (mul_assoc _ _ _).symm
        _ = ((schreierFactor T t g₁ : G) *
              (schreierRep T t g₁ : G)) * g₂ := by
          rw [schreierFactor_mul_schreierRep]
        _ = (schreierFactor T t g₁ : G) *
              ((schreierRep T t g₁ : G) * g₂) :=
          mul_assoc _ _ _
    _ = (T.2.equiv
          (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).2 := by
      simpa only [schreierFactor, schreierRep] using congrArg Prod.snd
          (T.2.equiv_mul_left
            (schreierFactor T t g₁)
            ((schreierRep T t g₁ : G) * g₂))

/-- The multiplicative Schreier factor identity.

For g₁,g₂ ∈ G, the factors in H satisfy a(t,g₁g₂) = a(t,g₁)a(r(t,g₁),g₂). -/
theorem schreierFactor_mul (T : H.RightTransversal)
    (t : (T : Set G)) (g₁ g₂ : G) :
    schreierFactor T t (g₁ * g₂) =
      schreierFactor T t g₁ *
        schreierFactor T (schreierRep T t g₁) g₂ := by
  change (T.2.equiv ((t : G) * (g₁ * g₂))).1 =
    (T.2.equiv ((t : G) * g₁)).1 *
      (T.2.equiv (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).1
  calc
    (T.2.equiv ((t : G) * (g₁ * g₂))).1 =
        (T.2.equiv
          ((schreierFactor T t g₁ : G) *
            ((schreierRep T t g₁ : G) * g₂))).1 := by
      congr 2
      calc
        (t : G) * (g₁ * g₂) = ((t : G) * g₁) * g₂ :=
          (mul_assoc _ _ _).symm
        _ = ((schreierFactor T t g₁ : G) *
              (schreierRep T t g₁ : G)) * g₂ := by
          rw [schreierFactor_mul_schreierRep]
        _ = (schreierFactor T t g₁ : G) *
              ((schreierRep T t g₁ : G) * g₂) :=
          mul_assoc _ _ _
    _ = (T.2.equiv ((t : G) * g₁)).1 *
          (T.2.equiv
            (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).1 := by
      simpa only [schreierFactor, schreierRep] using congrArg Prod.fst
          (T.2.equiv_mul_left
            (schreierFactor T t g₁)
            ((schreierRep T t g₁ : G) * g₂))

/-- The representative after multiplication by one.

For each t ∈ T, the representative r(t,1) equals t. -/
@[simp]
theorem schreierRep_one (T : H.RightTransversal)
    (t : (T : Set G)) : schreierRep T t 1 = t := by
  simpa only [schreierRep, mul_one] using
    T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.property

/-- The subgroup factor after multiplication by one.

For each t ∈ T, the subgroup factor a(t,1) equals the identity of H. -/
@[simp]
theorem schreierFactor_one (T : H.RightTransversal)
    (t : (T : Set G)) : schreierFactor T t 1 = 1 := by
  apply Subtype.ext
  change ((T.2.equiv ((t : G) * 1)).1 : G) = (1 : G)
  simpa only [mul_one] using congrArg Subtype.val
    (T.2.equiv_fst_eq_one_of_mem_of_one_mem H.one_mem t.property)

/-- The permutation of representatives defined by a group element.

For fixed g ∈ G, the map t ↦ r(t,g) is an equivalence of T with itself. Its inverse is t ↦
r(t,g⁻¹). -/
noncomputable def schreierRepEquiv (T : H.RightTransversal) (g : G) :
    (T : Set G) ≃ (T : Set G) where
  toFun t := schreierRep T t g
  invFun t := schreierRep T t g⁻¹
  left_inv t := by
    change schreierRep T (schreierRep T t g) g⁻¹ = t
    rw [← schreierRep_mul, mul_inv_cancel, schreierRep_one]
  right_inv t := by
    change schreierRep T (schreierRep T t g⁻¹) g = t
    rw [← schreierRep_mul, inv_mul_cancel, schreierRep_one]

/-- Values of the representative permutation.

The permutation of T associated to g sends t to the Schreier representative r(t,g). -/
@[simp]
theorem schreierRepEquiv_apply (T : H.RightTransversal)
    (g : G) (t : (T : Set G)) :
    schreierRepEquiv T g t = schreierRep T t g :=
  rfl

end Subgroup.RightTransversal

namespace Subgroup.RightTransversal

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- The representative scan of a finite tuple.

For g : Fin n → G, the scan at i ∈ Fin (n+1) is r(t,Pᵢ), where Pᵢ = g₀⋯gᵢ₋₁ is the ordered
partial product and P₀ = 1. -/
noncomputable def schreierRepScan {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) : Fin (n + 1) → (T : Set G) :=
  fun i ↦ T.schreierRep t (Fin.partialProd g i)

/-- The initial representative in a tuple scan.

The representative scan of g : Fin n → G begins at the supplied t ∈ T. -/
@[simp]
theorem schreierRepScan_get_zero {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) :
    schreierRepScan T t g 0 = t := by
  unfold schreierRepScan
  rw [Fin.partialProd_zero, schreierRep_one]

/-- One step of the representative scan.

If rᵢ is the representative before coordinate i, the representative after that coordinate is
rᵢ₊₁ = r(rᵢ,gᵢ). -/
@[simp]
theorem schreierRepScan_get_succ {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) (i : Fin n) :
    schreierRepScan T t g i.succ =
      T.schreierRep (schreierRepScan T t g i.castSucc) (g i) := by
  unfold schreierRepScan
  rw [Fin.partialProd_succ, schreierRep_mul]

/-- Representative scans under adjacent contraction.

Apply Fin.contractNth j using multiplication to g : Fin (n+1) → G. The scan of the contracted
tuple at i equals the original scan at j.succ.succAbove i, retaining the exact endpoint and
index conventions of the contraction. -/
theorem schreierRepScan_contractNth {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) (j : Fin (n + 1))
    (i : Fin (n + 1)) :
    schreierRepScan T t (Fin.contractNth j (fun x y ↦ x * y) g) i =
      schreierRepScan T t g (j.succ.succAbove i) := by
  unfold schreierRepScan
  have h := Fin.partialProd_contractNth g j
  exact congrArg (fun q ↦ T.schreierRep t (q i)) h

/-- The representative scan after the first coordinate.

Scanning the tail of g : Fin (n+1) → G from r(t,g₀) gives, at i, the original scan at i+1. -/
theorem schreierRepScan_tail {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) (i : Fin (n + 1)) :
    schreierRepScan T (T.schreierRep t (g 0)) (Fin.tail g) i =
      schreierRepScan T t g i.succ := by
  unfold schreierRepScan
  rw [← T.schreierRep_mul, ← Fin.partialProd_succ']

/-- The subgroup factors of a finite tuple scan.

For the representative scan rᵢ of g : Fin n → G, the factor tuple has coordinate a(rᵢ,gᵢ) ∈ H. -/
noncomputable def schreierFactorTuple {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) : Fin n → H :=
  fun i ↦ T.schreierFactor
    (schreierRepScan T t g i.castSucc) (g i)

/-- The coordinate formula for tuple factors in the ambient group.

If rᵢ and rᵢ₊₁ are consecutive representatives, the i-th subgroup factor has ambient value rᵢ
gᵢ rᵢ₊₁⁻¹. -/
theorem schreierFactorTuple_coe {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) (i : Fin n) :
    (schreierFactorTuple T t g i : G) =
      (schreierRepScan T t g i.castSucc : G) * g i *
        (schreierRepScan T t g i.succ : G)⁻¹ := by
  unfold schreierFactorTuple
  rw [schreierFactor, T.2.equiv_fst_eq_mul_inv]
  congr 2
  exact congrArg Subtype.val (schreierRepScan_get_succ T t g i).symm

/-- Factor tuples under adjacent contraction.

Contracting g by Fin.contractNth j using multiplication gives the same subgroup factor tuple
as contracting the factor tuple by multiplication in H. The same finite index j is used on
both sides. -/
theorem schreierFactorTuple_contractNth {n : ℕ}
    (T : H.RightTransversal) (t : (T : Set G))
    (g : Fin (n + 1) → G) (j : Fin (n + 1)) :
    schreierFactorTuple T t
        (Fin.contractNth j (fun x y ↦ x * y) g) =
      Fin.contractNth j (fun x y ↦ x * y)
        (schreierFactorTuple T t g) := by
  funext i
  apply Subtype.ext
  rw [schreierFactorTuple_coe,
    schreierRepScan_contractNth, schreierRepScan_contractNth]
  simp only [Fin.succ_succAbove_succ]
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h,
      Fin.contractNth_apply_of_lt _ _ _ _ h]
    rw [Fin.succAbove_of_castSucc_lt j.succ i.castSucc (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega),
      Fin.succAbove_of_castSucc_lt j i (by
        simpa only [Fin.lt_def, Fin.val_castSucc] using h)]
    rw [schreierFactorTuple_coe]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h,
      Fin.contractNth_apply_of_eq _ _ _ _ h]
    rw [Fin.succAbove_of_castSucc_lt j.succ i.castSucc (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega),
      Fin.succAbove_of_le_castSucc j i (by
        simpa only [Fin.le_def, Fin.val_castSucc] using le_of_eq h.symm)]
    change _ =
      (schreierFactorTuple T t g i.castSucc : G) *
        (schreierFactorTuple T t g i.succ : G)
    rw [schreierFactorTuple_coe, schreierFactorTuple_coe]
    simp only [Fin.castSucc_succ]
    group
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h,
      Fin.contractNth_apply_of_gt _ _ _ _ h]
    rw [Fin.succAbove_of_le_castSucc j.succ i.castSucc (by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega),
      Fin.succAbove_of_le_castSucc j i (by
        simpa only [Fin.le_def, Fin.val_castSucc] using le_of_lt h)]
    rw [schreierFactorTuple_coe]
    simp only [Fin.castSucc_succ]

/-- The subgroup factor tuple after the first coordinate.

The factor tuple of the tail of g, started at r(t,g₀), is the tail of the factor tuple of g
started at t. -/
theorem schreierFactorTuple_tail {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) :
    schreierFactorTuple T (T.schreierRep t (g 0)) (Fin.tail g) =
      Fin.tail (schreierFactorTuple T t g) := by
  funext i
  apply Subtype.ext
  change (schreierFactorTuple T (T.schreierRep t (g 0))
      (Fin.tail g) i : G) = (schreierFactorTuple T t g i.succ : G)
  rw [schreierFactorTuple_coe, schreierFactorTuple_coe,
    schreierRepScan_tail, schreierRepScan_tail]
  rfl

/-- The first subgroup factor of a tuple.

For a nonempty tuple g, its zeroth factor is a(t,g₀). -/
@[simp]
theorem schreierFactorTuple_zero {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) :
    schreierFactorTuple T t g 0 = T.schreierFactor t (g 0) := by
  unfold schreierFactorTuple
  rw [show (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) from rfl,
    schreierRepScan_get_zero]

/-- The second subgroup factor of a tuple.

For a tuple with at least two entries, its factor at coordinate 1 is a(r(t,g₀),g₁). -/
@[simp]
theorem schreierFactorTuple_one {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 2) → G) :
    schreierFactorTuple T t g 1 =
      T.schreierFactor (T.schreierRep t (g 0)) (g 1) := by
  unfold schreierFactorTuple
  rw [show (1 : Fin (n + 2)).castSucc = (0 : Fin (n + 2)).succ from rfl,
    schreierRepScan_get_succ,
    show (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) from rfl,
    schreierRepScan_get_zero]

/-- The third subgroup factor of a tuple.

For a tuple with at least three entries, its factor at coordinate 2 is a(r(r(t,g₀),g₁),g₂). -/
@[simp]
theorem schreierFactorTuple_two {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 3) → G) :
    schreierFactorTuple T t g 2 =
      T.schreierFactor
        (T.schreierRep (T.schreierRep t (g 0)) (g 1)) (g 2) := by
  unfold schreierFactorTuple
  rw [show (2 : Fin (n + 3)).castSucc = (1 : Fin (n + 3)).succ from rfl,
    schreierRepScan_get_succ,
    show (1 : Fin (n + 3)).castSucc = (0 : Fin (n + 3)).succ from rfl,
    schreierRepScan_get_succ,
    show (0 : Fin (n + 3)).castSucc = (0 : Fin (n + 4)) from rfl,
    schreierRepScan_get_zero]

/-- Partial products of subgroup factors.

For any i ∈ Fin (n+1), the ordered partial product of the first i subgroup factors equals the
H-component in the right-transversal decomposition of t·(g₀⋯gᵢ₋₁). -/
theorem factorTuple_partialProd (T : H.RightTransversal) {n : ℕ} (t : (T : Set G)) (x : Fin n → G)
    (i : Fin (n + 1)) :
    Fin.partialProd (T.schreierFactorTuple t x) i =
      (T.2.equiv ((t : G) * Fin.partialProd x i)).1 := by
  induction i using Fin.induction with
  | zero =>
      rw [Fin.partialProd_zero, Fin.partialProd_zero, mul_one]
      exact (T.2.equiv_fst_eq_one_of_mem_of_one_mem H.one_mem t.property).symm
  | succ i ih =>
      rw [Fin.partialProd_succ, Fin.partialProd_succ, ih]
      unfold schreierFactorTuple schreierRepScan schreierFactor
      let y := (t : G) * Fin.partialProd x i.castSucc
      have hy := T.2.equiv_fst_mul_equiv_snd y
      have hm := congrArg Prod.fst
        (T.2.equiv_mul_left (T.2.equiv y).1 (((T.2.equiv y).2 : G) * x i))
      have he : (t : G) * (Fin.partialProd x i.castSucc * x i) =
          ((T.2.equiv y).1 : G) * (((T.2.equiv y).2 : G) * x i) := by
        exact (mul_assoc _ _ _).symm.trans
          ((congrArg (fun z : G => z * x i) hy).symm.trans (mul_assoc _ _ _))
      exact hm.symm.trans (congrArg (fun z : G => (T.2.equiv z).1) he.symm)


end Subgroup.RightTransversal
