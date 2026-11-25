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

public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# The associated graded algebra of a natural-number filtration

For a monotone multiplicative filtration by submodules, the degree `n`
carrier is the original `F n` modulo the preceding stage, with a zero
denominator in degree zero. Multiplication descends the original product
through both quotient maps. The native `DirectSum.GRing` and `GAlgebra`
instances assemble these products on the original external direct sum.

No basis, coordinate isomorphism, or projectivity is used in the construction.
The last criterion derives commutativity from the actual degree-lowering
commutator of filtered representatives.
-/

@[expose] public section

noncomputable section

open scoped DirectSum

universe u v

namespace FilteredAlgebra

variable {R : Type u} [CommRing R] {A : Type v} [Ring A] [Algebra R A]
  (F : ℕ → Submodule R A)

/-- The preceding ambient filtration stage, including zero in degree zero. -/
def lower : ℕ → Submodule R A
  | 0 => ⊥
  | n + 1 => F n

/-- A monotone natural-number filtration has its usual preceding stages. -/
theorem isFiltration_lower (hF : Monotone F) : IsFiltration F (lower F) where
  mono := hF
  is_le {i j} hij := by
    cases j with
    | zero => exact (Nat.not_lt_zero i hij).elim
    | succ j => exact hF (Nat.le_of_lt_succ hij)
  is_sup B j hB := by
    cases j with
    | zero => exact bot_le
    | succ j => exact hB j (Nat.lt_succ_self j)

/-- The actual lower stage as a submodule of the degree-stage carrier. -/
def lowerInStage : (n : ℕ) → Submodule R (F n)
  | 0 => ⊥
  | n + 1 => (F n).comap (F (n + 1)).subtype

/-- The original quotient layer in degree `n`. -/
abbrev Grade (n : ℕ) := F n ⧸ lowerInStage F n

/-- The original finite-support direct sum of quotient layers. -/
abbrev AssociatedGraded := ⨁ n : ℕ, Grade F n

theorem mem_lowerInStage_iff (n : ℕ) (x : F n) :
    x ∈ lowerInStage F n ↔ x.val ∈ lower F n := by
  cases n with
  | zero => simp [lowerInStage, lower]
  | succ n => rfl

variable [IsRingFiltration F (lower F)]

/-- Multiplication of actual representatives, with its earned filtration bound. -/
def stageProduct (n m : ℕ) : F n →ₗ[R] F m →ₗ[R] F (n + m) where
  toFun x :=
    { toFun := fun y => ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩
      map_add' y z := by
        apply Subtype.ext
        exact mul_add x.val y.val z.val
      map_smul' r y := by
        apply Subtype.ext
        exact mul_smul_comm r x.val y.val }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact add_mul x.val y.val z.val
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact smul_mul_assoc r x.val y.val

@[simp]
theorem stageProduct_coe (n m : ℕ) (x : F n) (y : F m) :
    (stageProduct F n m x y).val = x.val * y.val := rfl

theorem stageProduct_mem_lower_left (n m : ℕ) (x : F n) (y : F m)
    (hx : x ∈ lowerInStage F n) :
    stageProduct F n m x y ∈ lowerInStage F (n + m) := by
  rw [mem_lowerInStage_iff] at hx ⊢
  cases n with
  | zero =>
      have hx0 : x.val = 0 := (Submodule.mem_bot R).mp hx
      change x.val * y.val ∈ lower F (0 + m)
      rw [hx0, zero_mul]
      exact (lower F (0 + m)).zero_mem
  | succ n =>
      change x.val ∈ F n at hx
      change x.val * y.val ∈ lower F (Nat.succ n + m)
      rw [Nat.succ_add]
      exact SetLike.mul_mem_graded hx y.property

theorem stageProduct_mem_lower_right (n m : ℕ) (x : F n) (y : F m)
    (hy : y ∈ lowerInStage F m) :
    stageProduct F n m x y ∈ lowerInStage F (n + m) := by
  rw [mem_lowerInStage_iff] at hy ⊢
  cases m with
  | zero =>
      have hy0 : y.val = 0 := (Submodule.mem_bot R).mp hy
      change x.val * y.val ∈ lower F (n + 0)
      rw [hy0, mul_zero]
      exact (lower F (n + 0)).zero_mem
  | succ m =>
      change y.val ∈ F m at hy
      change x.val * y.val ∈ F (n + m)
      exact SetLike.mul_mem_graded x.property hy

/-- The original representative product descended through its right quotient. -/
def productAfterRightQuotient (n m : ℕ) :
    F n →ₗ[R] Grade F m →ₗ[R] Grade F (n + m) where
  toFun x := (lowerInStage F m).liftQ
    ((lowerInStage F (n + m)).mkQ.comp (stageProduct F n m x)) (by
      intro y hy
      change (lowerInStage F (n + m)).mkQ (stageProduct F n m x y) = 0
      exact (Submodule.Quotient.mk_eq_zero (lowerInStage F (n + m))).mpr
        (stageProduct_mem_lower_right F n m x y hy))
  map_add' x y := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      map_add, LinearMap.add_apply]
  map_smul' r x := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The original product descended through both actual quotient maps. -/
def gradeProduct (n m : ℕ) : Grade F n →ₗ[R] Grade F m →ₗ[R] Grade F (n + m) :=
  (lowerInStage F n).liftQ (productAfterRightQuotient F n m) (by
    intro x hx
    change productAfterRightQuotient F n m x = 0
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro y
    change (lowerInStage F (n + m)).mkQ (stageProduct F n m x y) = 0
    exact (Submodule.Quotient.mk_eq_zero (lowerInStage F (n + m))).mpr
      (stageProduct_mem_lower_left F n m x y hx))

theorem gradeProduct_mk (n m : ℕ) (x : F n) (y : F m) :
    gradeProduct F n m ((lowerInStage F n).mkQ x) ((lowerInStage F m).mkQ y) =
      (lowerInStage F (n + m)).mkQ
        ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩ := by
  simp only [gradeProduct, productAfterRightQuotient, Submodule.liftQ_apply, LinearMap.comp_apply]
  rfl

/-- The original scalar map restricted to the actual degree-zero stage. -/
def scalarStage : R →ₗ[R] F 0 :=
  (Algebra.linearMap R A).codRestrict (F 0) (fun r => by
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact (F 0).smul_mem r (SetLike.one_mem_graded F))

@[simp]
theorem scalarStage_coe (r : R) : (scalarStage F r).val = algebraMap R A r := rfl

/-- The quotient class of the original algebra unit in degree zero. -/
def gradeOne : Grade F 0 :=
  (lowerInStage F 0).mkQ ⟨(1 : A), SetLike.one_mem_graded F⟩

/-- The original scalar map in the degree-zero quotient. -/
def gradeScalar : R →ₗ[R] Grade F 0 :=
  (lowerInStage F 0).mkQ.comp (scalarStage F)

theorem gradeScalar_one : gradeScalar F 1 = gradeOne F := by
  apply congrArg (lowerInStage F 0).mkQ
  apply Subtype.ext
  exact map_one (algebraMap R A)

instance gradeGMul : GradedMonoid.GMul (Grade F) where
  mul a b := gradeProduct F _ _ a b

instance gradeGOne : GradedMonoid.GOne (Grade F) where
  one := gradeOne F

theorem graded_one : (1 : GradedMonoid (Grade F)) =
    GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ
      ⟨(1 : A), SetLike.one_mem_graded F⟩) := rfl

theorem graded_mul_mk (n m : ℕ) (x : F n) (y : F m) :
    (GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ x) : GradedMonoid (Grade F)) *
        GradedMonoid.mk (A := Grade F) m ((lowerInStage F m).mkQ y) =
      GradedMonoid.mk (A := Grade F) (n + m) ((lowerInStage F (n + m)).mkQ
        ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩) := by
  change GradedMonoid.mk (A := Grade F) (n + m)
      (gradeProduct F n m ((lowerInStage F n).mkQ x) ((lowerInStage F m).mkQ y)) = _
  rw [gradeProduct_mk]

instance gradeGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (Grade F) where
  __ := gradeGMul F
  mul_zero a := map_zero (gradeProduct F _ _ a)
  zero_mul {i j} a := by
    change gradeProduct F i j 0 a = 0
    exact (congrArg (fun f => f a) (gradeProduct F i j).map_zero).trans rfl
  mul_add a b c := map_add (gradeProduct F _ _ a) b c
  add_mul {i j} a b c := by
    change gradeProduct F i j (a + b) c = _
    exact LinearMap.congr_fun ((gradeProduct F i j).map_add a b) c

omit [IsRingFiltration F (lower F)] in
/-- Equal degrees and equal original representatives give equal native
graded quotient constructors, with the actual degree cast eliminated. -/
theorem gradedMk_congr {n m : ℕ} (h : n = m) (u : F n) (v : F m)
    (huv : u.val = v.val) :
    GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u) =
      GradedMonoid.mk (A := Grade F) m ((lowerInStage F m).mkQ v) := by
  subst m
  exact congrArg (fun q : F n => GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ q))
    (Subtype.ext huv)

instance gradeGMonoid : GradedMonoid.GMonoid (Grade F) where
  __ := gradeGMul F
  __ := gradeGOne F
  one_mul x := by
    rcases x with ⟨n, x⟩
    obtain ⟨u, rfl⟩ := (lowerInStage F n).mkQ_surjective x
    let one : F 0 := ⟨1, SetLike.one_mem_graded F⟩
    have hMul := graded_mul_mk F 0 n one u
    change GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ one) *
      GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u) =
        GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u)
    exact hMul.trans (gradedMk_congr F (Nat.zero_add n) _ u (one_mul u.val))
  mul_one x := by
    rcases x with ⟨n, x⟩
    obtain ⟨u, rfl⟩ := (lowerInStage F n).mkQ_surjective x
    let one : F 0 := ⟨1, SetLike.one_mem_graded F⟩
    have hMul := graded_mul_mk F n 0 u one
    change GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u) *
      GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ one) =
        GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u)
    exact hMul.trans (gradedMk_congr F (Nat.add_zero n) _ u (mul_one u.val))
  mul_assoc x y z := by
    rcases x with ⟨n, x⟩
    rcases y with ⟨m, y⟩
    rcases z with ⟨k, z⟩
    obtain ⟨u, rfl⟩ := (lowerInStage F n).mkQ_surjective x
    obtain ⟨v, rfl⟩ := (lowerInStage F m).mkQ_surjective y
    obtain ⟨w, rfl⟩ := (lowerInStage F k).mkQ_surjective z
    let uv : F (n + m) := stageProduct F n m u v
    let vw : F (m + k) := stageProduct F m k v w
    let gu : GradedMonoid (Grade F) := GradedMonoid.mk n ((lowerInStage F n).mkQ u)
    let gv : GradedMonoid (Grade F) := GradedMonoid.mk m ((lowerInStage F m).mkQ v)
    let gw : GradedMonoid (Grade F) := GradedMonoid.mk k ((lowerInStage F k).mkQ w)
    have hLeft : (gu * gv) * gw =
        GradedMonoid.mk (A := Grade F) ((n + m) + k)
          ((lowerInStage F ((n + m) + k)).mkQ (stageProduct F (n + m) k uv w)) :=
      (congrArg (fun t : GradedMonoid (Grade F) => t * gw) (graded_mul_mk F n m u v)).trans
        (graded_mul_mk F (n + m) k uv w)
    have hRight : gu * (gv * gw) =
        GradedMonoid.mk (A := Grade F) (n + (m + k))
          ((lowerInStage F (n + (m + k))).mkQ (stageProduct F n (m + k) u vw)) :=
      (congrArg (fun t : GradedMonoid (Grade F) => gu * t) (graded_mul_mk F m k v w)).trans
        (graded_mul_mk F n (m + k) u vw)
    have hAssoc :
        GradedMonoid.mk (A := Grade F) ((n + m) + k)
          ((lowerInStage F ((n + m) + k)).mkQ (stageProduct F (n + m) k uv w)) =
        GradedMonoid.mk (A := Grade F) (n + (m + k))
          ((lowerInStage F (n + (m + k))).mkQ (stageProduct F n (m + k) u vw)) :=
      gradedMk_congr F (Nat.add_assoc n m k) _ _ (mul_assoc u.val v.val w.val)
    exact hLeft.trans (hAssoc.trans hRight.symm)

instance gradeGSemiring : DirectSum.GSemiring (Grade F) where
  __ := gradeGNonUnitalNonAssocSemiring F
  __ := gradeGMonoid F
  natCast n := gradeScalar F (n : R)
  natCast_zero := (congrArg (gradeScalar F) (Nat.cast_zero (R := R))).trans
    (gradeScalar F).map_zero
  natCast_succ n := by
    rw [Nat.cast_add, Nat.cast_one, map_add, gradeScalar_one]
    rfl

instance gradeGRing : DirectSum.GRing (Grade F) where
  __ := gradeGSemiring F
  intCast n := gradeScalar F (n : R)
  intCast_ofNat n := by
    exact congrArg (gradeScalar F) (Int.cast_natCast n)
  intCast_negSucc_ofNat n := by
    rw [Int.cast_negSucc]
    exact (gradeScalar F).map_neg _

instance gradeGAlgebra : DirectSum.GAlgebra R (Grade F) where
  toFun := (gradeScalar F).toAddMonoidHom
  map_one := gradeScalar_one F
  map_mul r s := by
    change GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ (scalarStage F (r * s))) =
      GradedMonoid.mk (A := Grade F) (0 + 0)
        (gradeProduct F 0 0 ((lowerInStage F 0).mkQ (scalarStage F r))
          ((lowerInStage F 0).mkQ (scalarStage F s)))
    rw [gradeProduct_mk]
    exact gradedMk_congr F rfl _ _ ((algebraMap R A).map_mul r s)
  commutes r x := by
    rcases x with ⟨n, x⟩
    obtain ⟨u, rfl⟩ := (lowerInStage F n).mkQ_surjective x
    change (GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ (scalarStage F r)) :
      GradedMonoid (Grade F)) * GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u) =
        GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u) *
          GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ (scalarStage F r))
    rw [graded_mul_mk, graded_mul_mk]
    exact gradedMk_congr F (by omega) _ _ (Algebra.commutes r u.val)
  smul_def r x := by
    rcases x with ⟨n, x⟩
    obtain ⟨u, rfl⟩ := (lowerInStage F n).mkQ_surjective x
    change GradedMonoid.mk (A := Grade F) n (r • (lowerInStage F n).mkQ u) =
      (GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ (scalarStage F r)) :
        GradedMonoid (Grade F)) * GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u)
    rw [graded_mul_mk, ← map_smul]
    exact gradedMk_congr F (Nat.zero_add n).symm _ _ (Algebra.smul_def r u.val)

/-- The symbol of an actual filtered representative, in the original direct sum. -/
def symbol (n : ℕ) : F n →ₗ[R] AssociatedGraded F :=
  (DirectSum.lof R ℕ (Grade F) n).comp (lowerInStage F n).mkQ

omit [IsRingFiltration F (lower F)] in
@[simp]
theorem symbol_mk (n : ℕ) (u : F n) :
    symbol F n u = DirectSum.lof R ℕ (Grade F) n ((lowerInStage F n).mkQ u) := rfl

/-- Multiplication of symbols is the quotient class of the original product. -/
theorem symbol_mul (n m : ℕ) (x : F n) (y : F m) :
    symbol F n x * symbol F m y =
      symbol F (n + m) ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩ := by
  change DirectSum.of (Grade F) n ((lowerInStage F n).mkQ x) *
      DirectSum.of (Grade F) m ((lowerInStage F m).mkQ y) = _
  rw [DirectSum.of_mul_of]
  change DirectSum.of (Grade F) (n + m)
    (gradeProduct F n m ((lowerInStage F n).mkQ x) ((lowerInStage F m).mkQ y)) = _
  exact congrArg (DirectSum.of (Grade F) (n + m)) (gradeProduct_mk F n m x y)

theorem symbol_one :
    symbol F 0 ⟨(1 : A), SetLike.one_mem_graded F⟩ = 1 := rfl

theorem symbol_algebraMap (r : R) :
    symbol F 0 (scalarStage F r) = algebraMap R (AssociatedGraded F) r := rfl

/-- Symbols of original representatives generate the entire original direct sum. -/
@[elab_as_elim]
theorem symbol_induction {motive : AssociatedGraded F → Prop}
    (zero : motive 0) (symbol : ∀ n (u : F n), motive (FilteredAlgebra.symbol F n u))
    (add : ∀ x y, motive x → motive y → motive (x + y)) (z : AssociatedGraded F) :
    motive z := by
  induction z using DirectSum.induction_on with
  | zero => exact zero
  | of n x =>
      obtain ⟨u, rfl⟩ := (lowerInStage F n).mkQ_surjective x
      exact symbol n u
  | add x y hx hy => exact add x y hx hy

/-- Maps out of the associated graded module are determined by actual symbols. -/
theorem linearMap_ext_symbol {M : Type*} [AddCommGroup M] [Module R M]
    {f g : AssociatedGraded F →ₗ[R] M}
    (h : ∀ n (u : F n), f (symbol F n u) = g (symbol F n u)) : f = g := by
  apply LinearMap.ext
  intro z
  exact symbol_induction F (by rw [map_zero, map_zero]) h
    (fun x y hx hy => by rw [map_add, map_add, hx, hy]) z

omit [IsRingFiltration F (lower F)] in
theorem symbol_congr {n m : ℕ} (h : n = m) (u : F n) (v : F m)
    (huv : u.val = v.val) : symbol F n u = symbol F m v := by
  subst m
  apply congrArg (symbol F n)
  exact Subtype.ext huv

/-- Actual lowering of commutators implies that every pair of symbols commutes. -/
theorem symbol_comm_of_commutator_mem
    (hcomm : ∀ n m (u : F n) (v : F m), u.val * v.val - v.val * u.val ∈ lower F (n + m))
    (n m : ℕ) (u : F n) (v : F m) : symbol F n u * symbol F m v =
      symbol F m v * symbol F n u := by
  let uv : F (n + m) := ⟨u.val * v.val, SetLike.mul_mem_graded u.property v.property⟩
  let vu : F (n + m) := ⟨v.val * u.val, by
    simpa only [Nat.add_comm m n] using SetLike.mul_mem_graded v.property u.property⟩
  have hq : (lowerInStage F (n + m)).mkQ uv = (lowerInStage F (n + m)).mkQ vu := by
    apply (Submodule.Quotient.eq (lowerInStage F (n + m))).mpr
    exact (mem_lowerInStage_iff F (n + m) (uv - vu)).mpr (hcomm n m u v)
  calc
    symbol F n u * symbol F m v = symbol F (n + m) uv := symbol_mul F n m u v
    _ = symbol F (n + m) vu := congrArg (DirectSum.lof R ℕ (Grade F) (n + m)) hq
    _ = symbol F (m + n)
        ⟨v.val * u.val, SetLike.mul_mem_graded v.property u.property⟩ :=
      symbol_congr F (Nat.add_comm n m) vu _ rfl
    _ = symbol F m v * symbol F n u := (symbol_mul F m n v u).symm

/-- The native associated graded product is commutative when actual filtered
commutators lie in the preceding ambient stage. -/
theorem mul_comm_of_commutator_mem
    (hcomm : ∀ n m (u : F n) (v : F m), u.val * v.val - v.val * u.val ∈ lower F (n + m))
    (x y : AssociatedGraded F) : x * y = y * x := by
  have h : ∀ x : AssociatedGraded F, ∀ y : AssociatedGraded F, x * y = y * x := by
    intro x
    refine symbol_induction F ?_ ?_ ?_ x
    · intro y
      rw [zero_mul, mul_zero]
    · intro n u y
      refine symbol_induction F ?_ ?_ ?_ y
      · rw [mul_zero, zero_mul]
      · intro m v
        exact symbol_comm_of_commutator_mem F hcomm n m u v
      · intro y z hy hz
        rw [mul_add, add_mul, hy, hz]
    · intro x y hx hy z
      rw [add_mul, mul_add, hx z, hy z]
  exact h x y

end FilteredAlgebra
