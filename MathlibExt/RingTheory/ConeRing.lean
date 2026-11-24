/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.BlockDiagonal
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Algebra.Module.Opposite

/-!
# Weibel's literal cone ring

`ConeRing R` is the ring of all row-and-column finite matrices indexed by
the natural numbers. No uniform support bound or finite coefficient range
is imposed. The countable pairing fixes the actual first-block and tail
injections. Their original partial-permutation matrices give explicit
direct-sum equivalences of the regular right and left modules.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS

/-- Weibel's cone ring of all original row-and-column finite countable matrices. -/
abbrev ConeRing (R : Type uR) [Zero R] := Matrix.LocallyFinite ℕ ℕ R

namespace ConeRing

open Matrix.LocallyFinite

variable {R : Type uR} {S : Type uS}

/-- The literal first-block injection under the standard countable pairing. -/
def firstEmbedding : ℕ ↪ ℕ :=
  (blockEmbedding (0 : ℕ)).trans Nat.pairEquiv.toEmbedding

/-- The literal successor-block injection, retaining both original unpaired coordinates. -/
def tailEmbedding : ℕ ↪ ℕ where
  toFun i := Nat.pair (i.unpair.1 + 1) i.unpair.2
  inj' a b h := by
    have hp : (a.unpair.1 + 1, a.unpair.2) = (b.unpair.1 + 1, b.unpair.2) :=
      Nat.pairEquiv.injective h
    have hfst : a.unpair.1 + 1 = b.unpair.1 + 1 := congrArg Prod.fst hp
    have hsnd := congrArg (fun z : ℕ × ℕ => z.2) hp
    apply Nat.pairEquiv.symm.injective
    change a.unpair = b.unpair
    exact Prod.ext (Nat.add_right_cancel hfst) hsnd

/-- The first original block has copy coordinate zero. -/
@[simp]
theorem firstEmbedding_apply (i : ℕ) : firstEmbedding i = Nat.pair 0 i := rfl

/-- The tail injection shifts the original copy coordinate and retains the original row. -/
@[simp]
theorem tailEmbedding_apply_pair (k i : ℕ) :
    tailEmbedding (Nat.pair k i) = Nat.pair (k + 1) i := by
  change Nat.pair ((Nat.unpair (Nat.pair k i)).1 + 1)
    (Nat.unpair (Nat.pair k i)).2 = Nat.pair (k + 1) i
  rw [Nat.unpair_pair]

/-- The original first-block image is precisely the zero-copy locus. -/
theorem mem_range_firstEmbedding (i : ℕ) :
    i ∈ Set.range firstEmbedding ↔ i.unpair.1 = 0 := by
  constructor
  · rintro ⟨j, rfl⟩
    simp
  · intro h
    refine ⟨i.unpair.2, ?_⟩
    change Nat.pair 0 i.unpair.2 = i
    rw [← h, Nat.pair_unpair]

/-- The original tail image is precisely the positive-copy locus. -/
theorem mem_range_tailEmbedding (i : ℕ) :
    i ∈ Set.range tailEmbedding ↔ 0 < i.unpair.1 := by
  constructor
  · rintro ⟨j, rfl⟩
    change 0 < (Nat.unpair (Nat.pair (j.unpair.1 + 1) j.unpair.2)).1
    rw [Nat.unpair_pair]
    exact Nat.succ_pos _
  · intro h
    refine ⟨Nat.pair (i.unpair.1 - 1) i.unpair.2, ?_⟩
    rw [tailEmbedding_apply_pair, Nat.sub_add_cancel (Nat.succ_le_of_lt h)]
    exact Nat.pair_unpair i

/-- The actual first and tail image sets are disjoint. -/
theorem ranges_disjoint : Disjoint (Set.range firstEmbedding) (Set.range tailEmbedding) := by
  apply Set.disjoint_left.mpr
  intro i hfirst htail
  exact (Nat.ne_of_gt (mem_range_tailEmbedding i |>.mp htail))
    (mem_range_firstEmbedding i |>.mp hfirst)

/-- The actual first and successor blocks cover every original countable index. -/
theorem ranges_cover : Set.range firstEmbedding ∪ Set.range tailEmbedding = Set.univ := by
  ext i
  simp only [Set.mem_union, Set.mem_univ, mem_range_firstEmbedding,
    mem_range_tailEmbedding, iff_true]
  exact Nat.eq_zero_or_pos i.unpair.1

/-- The actual first-block partial-permutation inclusion matrix. -/
abbrev firstInclusion (R : Type uR) [Semiring R] : ConeRing R :=
  inclusion (R := R) firstEmbedding

/-- The actual successor-block partial-permutation inclusion matrix. -/
abbrev tailInclusion (R : Type uR) [Semiring R] : ConeRing R :=
  inclusion (R := R) tailEmbedding

/-- The actual first-block projection matrix. -/
abbrev firstProjection (R : Type uR) [Semiring R] : ConeRing R :=
  projection (R := R) firstEmbedding

/-- The actual successor-block projection matrix. -/
abbrev tailProjection (R : Type uR) [Semiring R] : ConeRing R :=
  projection (R := R) tailEmbedding

/-- The original first projection and inclusion multiply to the original identity. -/
theorem firstProjection_mul_firstInclusion [Semiring R] :
    firstProjection R * firstInclusion R = 1 := projection_comp_inclusion firstEmbedding

/-- The original tail projection and inclusion multiply to the original identity. -/
theorem tailProjection_mul_tailInclusion [Semiring R] :
    tailProjection R * tailInclusion R = 1 := projection_comp_inclusion tailEmbedding

/-- The original first projection annihilates the original tail inclusion. -/
theorem firstProjection_mul_tailInclusion [Semiring R] :
    firstProjection R * tailInclusion R = 0 :=
  projection_comp_inclusion_of_disjoint tailEmbedding firstEmbedding ranges_disjoint.symm

/-- The original tail projection annihilates the original first inclusion. -/
theorem tailProjection_mul_firstInclusion [Semiring R] :
    tailProjection R * firstInclusion R = 0 :=
  projection_comp_inclusion_of_disjoint firstEmbedding tailEmbedding ranges_disjoint

/-- The original two corner projections sum to the original countable identity. -/
theorem inclusion_projection_sum [Semiring R] :
    firstInclusion R * firstProjection R + tailInclusion R * tailProjection R = 1 := by
  change (inclusion firstEmbedding).comp (projection firstEmbedding) +
    (inclusion tailEmbedding).comp (projection tailEmbedding) = (1 : ConeRing R)
  rw [inclusion_comp_projection, inclusion_comp_projection]
  exact cornerProjection_partition firstEmbedding tailEmbedding ranges_disjoint ranges_cover

/-- The literal block-sum homomorphism of the original cone ring. -/
abbrev blockSumHom (R : Type uR) [Semiring R] : ConeRing R × ConeRing R →+* ConeRing R :=
  blockSumRingHom firstEmbedding tailEmbedding ranges_disjoint ranges_cover

/-- The original regular right cone module is explicitly equivalent to two copies of itself. -/
def directSumRightLinearEquiv (R : Type uR) [Semiring R] :
    ConeRing R ≃ₗ[(ConeRing R)ᵐᵒᵖ] ConeRing R × ConeRing R where
  toFun x := (firstProjection R * x, tailProjection R * x)
  invFun x := firstInclusion R * x.1 + tailInclusion R * x.2
  left_inv x := by
    change firstInclusion R * (firstProjection R * x) +
      tailInclusion R * (tailProjection R * x) = x
    rw [← mul_assoc, ← mul_assoc, ← add_mul, inclusion_projection_sum, one_mul]
  right_inv x := by
    apply Prod.ext
    · change firstProjection R * (firstInclusion R * x.1 + tailInclusion R * x.2) = x.1
      rw [mul_add, ← mul_assoc, ← mul_assoc, firstProjection_mul_firstInclusion,
        firstProjection_mul_tailInclusion, one_mul, zero_mul, add_zero]
    · change tailProjection R * (firstInclusion R * x.1 + tailInclusion R * x.2) = x.2
      rw [mul_add, ← mul_assoc, ← mul_assoc, tailProjection_mul_firstInclusion,
        tailProjection_mul_tailInclusion, zero_mul, one_mul, zero_add]
  map_add' x y := Prod.ext (mul_add _ _ _) (mul_add _ _ _)
  map_smul' r x := by
    change (firstProjection R * (x * MulOpposite.unop r),
        tailProjection R * (x * MulOpposite.unop r)) =
      ((firstProjection R * x) * MulOpposite.unop r,
        (tailProjection R * x) * MulOpposite.unop r)
    exact Prod.ext (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm

/-- The actual regular-right-module forward map retains both original projection matrices. -/
@[simp]
theorem directSumRightLinearEquiv_apply [Semiring R] (x : ConeRing R) :
    directSumRightLinearEquiv R x = (firstProjection R * x, tailProjection R * x) := rfl

/-- The actual regular-right-module inverse retains both original inclusion matrices. -/
@[simp]
theorem directSumRightLinearEquiv_symm_apply [Semiring R] (x : ConeRing R × ConeRing R) :
    (directSumRightLinearEquiv R).symm x = firstInclusion R * x.1 + tailInclusion R * x.2 := rfl

/-- The original regular left cone module has the actual transposed direct-sum equivalence. -/
def directSumLeftLinearEquiv (R : Type uR) [Semiring R] :
    ConeRing R ≃ₗ[ConeRing R] ConeRing R × ConeRing R where
  toFun x := (x * firstInclusion R, x * tailInclusion R)
  invFun x := x.1 * firstProjection R + x.2 * tailProjection R
  left_inv x := by
    change (x * firstInclusion R) * firstProjection R +
      (x * tailInclusion R) * tailProjection R = x
    rw [mul_assoc, mul_assoc, ← mul_add, inclusion_projection_sum, mul_one]
  right_inv x := by
    apply Prod.ext
    · change (x.1 * firstProjection R + x.2 * tailProjection R) * firstInclusion R = x.1
      rw [add_mul, mul_assoc, mul_assoc, firstProjection_mul_firstInclusion,
        tailProjection_mul_firstInclusion, mul_one, mul_zero, add_zero]
    · change (x.1 * firstProjection R + x.2 * tailProjection R) * tailInclusion R = x.2
      rw [add_mul, mul_assoc, mul_assoc, firstProjection_mul_tailInclusion,
        tailProjection_mul_tailInclusion, mul_zero, mul_one, zero_add]
  map_add' x y := Prod.ext (add_mul _ _ _) (add_mul _ _ _)
  map_smul' r x := by
    change ((r * x) * firstInclusion R, (r * x) * tailInclusion R) =
      (r * (x * firstInclusion R), r * (x * tailInclusion R))
    exact Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)

/-- The actual regular-left-module forward map retains both original inclusion matrices. -/
@[simp]
theorem directSumLeftLinearEquiv_apply [Semiring R] (x : ConeRing R) :
    directSumLeftLinearEquiv R x = (x * firstInclusion R, x * tailInclusion R) := rfl

/-- The actual regular-left-module inverse retains both original projection matrices. -/
@[simp]
theorem directSumLeftLinearEquiv_symm_apply [Semiring R] (x : ConeRing R × ConeRing R) :
    (directSumLeftLinearEquiv R).symm x = x.1 * firstProjection R + x.2 * tailProjection R := rfl

/-- The original entrywise cone-ring homomorphism of a coefficient homomorphism. -/
abbrev map [Semiring R] [Semiring S] (f : R →+* S) : ConeRing R →+* ConeRing S :=
  mapRingHom f

/-- The original scalar inclusion is the actual constant diagonal matrix homomorphism. -/
def scalarHom (R : Type uR) [Semiring R] : R →+* ConeRing R where
  toFun r := diagonal fun _ => r
  map_zero' := by
    classical
    ext i j
    simp [diagonal_apply]
  map_one' := rfl
  map_add' a b := by
    classical
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, Matrix.LocallyFinite.add_apply, h]
  map_mul' a b := (diagonal_comp_diagonal (fun _ => a) (fun _ => b)).symm

/-- The original scalar homomorphism is injective by its actual zero diagonal coefficient. -/
theorem scalarHom_injective (R : Type uR) [Semiring R] : Function.Injective (scalarHom R) := by
  intro a b h
  have h0 := congrArg (fun A : ConeRing R => A 0 0) h
  simpa [scalarHom, diagonal_apply] using h0

/-- The original scalar inclusion is natural for the actual entrywise cone-ring homomorphism. -/
theorem map_scalarHom [Semiring R] [Semiring S] (f : R →+* S) (r : R) :
    map f (scalarHom R r) = scalarHom S (f r) := by
  classical
  ext i j
  change f (diagonal (fun _ : ℕ => r) i j) = diagonal (fun _ : ℕ => f r) i j
  by_cases h : i = j <;> simp [diagonal_apply, h]

/-- A constant original diagonal matrix has finite total support exactly when its scalar is zero. -/
theorem scalarHom_hasFiniteSupport_iff [Semiring R] (r : R) :
    HasFiniteSupport (scalarHom R r) ↔ r = 0 := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := exists_bound_of_hasFiniteSupport h
    have hn := hN N N (Or.inl le_rfl)
    simpa [scalarHom, diagonal_apply] using hn
  · rintro rfl
    exact (scalarHom R).map_zero.symm ▸ hasFiniteSupport_zero

end ConeRing

end
