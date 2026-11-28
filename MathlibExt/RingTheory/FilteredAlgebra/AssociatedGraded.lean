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
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Associated graded algebras of natural-number filtrations

Let `R` be a commutative ring, `A` an `R`-algebra, and `F : ℕ → Submodule R A`. Put `lower F 0
= ⊥` and `lower F (n + 1) = F n`. The degree-`n` layer is `F n` modulo the pullback of its
preceding stage, with zero denominator in degree zero. Their external direct sum is the
associated graded module.

Assume `F` is an increasing ring filtration for these preceding stages. The product of
representatives `x ∈ F n` and `y ∈ F m` descends to degree `n + m`, with `[x] * [y] = [x *
y]`. The unit and algebra scalars lie in degree zero. These products give the associated
graded an `R`-algebra structure.

The symbol maps generate the direct sum additively. If every filtered commutator `x*y - y*x`
lies in `lower F (n + m)`, the associated graded multiplication is commutative. The scalar and
algebra-carrier universes are independent.

For the preceding-stage convention `F₋₁ = 0` and adjacent quotients, see J. F. Jardine,
*K-theory*, Lecture 009, §21. This is background for the construction; the Lean API does not
assume exhaustivity of the filtration.
-/

@[expose] public section

noncomputable section

open scoped DirectSum

universe u v

namespace FilteredAlgebra

variable {R : Type u} [CommRing R] {A : Type v} [Ring A] [Algebra R A]
  (F : ℕ → Submodule R A)

/-- Preceding filtration stages with zero at degree zero.

For a submodule family `F`, define `lower F 0 = ⊥` and `lower F (n + 1) = F n`. The degree-
zero denominator is zero rather than a truncated predecessor stage. -/
def lower : ℕ → Submodule R A
  | 0 => ⊥
  | n + 1 => F n

/-- Monotone submodule families have the preceding-stage filtration relation.

If `F : ℕ → Submodule R A` is monotone, then `F` and `lower F` satisfy `IsFiltration`. In
particular, every earlier stage lies in the preceding stage of a strictly later degree. -/
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

/-- Preceding stage viewed inside the current submodule.

The degree-zero submodule of `F 0` is zero. In degree `n + 1`, `lowerInStage F (n + 1)` is the
pullback of `F n` along the subtype map `F (n + 1) →ₗ[R] A`. For an increasing filtration this
is the preceding stage inside the current stage. -/
def lowerInStage : (n : ℕ) → Submodule R (F n)
  | 0 => ⊥
  | n + 1 => (F n).comap (F (n + 1)).subtype

/-- Quotient layer of a submodule family.

For natural `n`, `Grade F n` is the `R`-module `F n ⧸ lowerInStage F n`. Degree zero has
denominator zero; for an increasing filtration, degree `n + 1` is `F (n + 1) / F n`. -/
abbrev Grade (n : ℕ) := F n ⧸ lowerInStage F n

/-- External direct sum of the quotient layers.

The associated graded module of `F` is `⨁ n : ℕ, Grade F n`, the direct sum of its adjacent
quotient layers. Elements have finite degree support. -/
abbrev AssociatedGraded := ⨁ n : ℕ, Grade F n

/-- Membership in the preceding-stage submodule.

For `x : F n`, membership in `lowerInStage F n` is equivalent to membership of its underlying
element `x.val` in `lower F n`. -/
theorem mem_lowerInStage_iff (n : ℕ) (x : F n) :
    x ∈ lowerInStage F n ↔ x.val ∈ lower F n := by
  cases n with
  | zero => simp [lowerInStage, lower]
  | succ n => rfl

/-- Filtered representative as a homogeneous associated-graded element.

For natural `n`, the linear symbol map takes `u : F n` to its quotient class in `Grade F n`
and then includes that class in degree `n` of the external direct sum. -/
def symbol (n : ℕ) : F n →ₗ[R] AssociatedGraded F :=
  (DirectSum.lof R ℕ (Grade F) n).comp (lowerInStage F n).mkQ

/-- Symbol map as quotient projection and direct-sum inclusion.

The symbol of `u : F n` is `DirectSum.lof R ℕ (Grade F) n ((lowerInStage F n).mkQ u)`. -/
@[simp]
theorem symbol_mk (n : ℕ) (u : F n) :
    symbol F n u = DirectSum.lof R ℕ (Grade F) n ((lowerInStage F n).mkQ u) := rfl

/-- Additive induction on homogeneous symbols.

A property of associated-graded elements holds everywhere if it holds at zero and at every
symbol of a filtered representative, and is preserved by addition. -/
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

/-- Linear maps from the associated graded are determined by symbols.

Two `R`-linear maps from `AssociatedGraded F` to an `R`-module are equal if their values agree
on `symbol F n u` for all natural `n` and all `u : F n`. -/
theorem linearMap_ext_symbol {M : Type*} [AddCommGroup M] [Module R M]
    {f g : AssociatedGraded F →ₗ[R] M}
    (h : ∀ n (u : F n), f (symbol F n u) = g (symbol F n u)) : f = g := by
  apply LinearMap.ext
  intro z
  exact symbol_induction F (by rw [map_zero, map_zero]) h
    (fun x y hx hy => by rw [map_add, map_add, hx, hy]) z

/-- Equal degree and underlying representative give equal symbols.

If `n = m` and `u : F n` and `v : F m` have equal underlying elements in `A`, then `symbol F n
u = symbol F m v`. -/
theorem symbol_congr {n m : ℕ} (h : n = m) (u : F n) (v : F m)
    (huv : u.val = v.val) : symbol F n u = symbol F m v := by
  subst m
  apply congrArg (symbol F n)
  exact Subtype.ext huv

variable [IsRingFiltration F (lower F)]

/-- Bilinear multiplication between filtered stages.

For a ring filtration, multiplication in `A` gives an `R`-bilinear map `F n →ₗ[R] F m →ₗ[R] F
(n + m)` with value the product of the underlying representatives. -/
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

/-- Underlying element of filtered stage multiplication.

For `x : F n` and `y : F m`, the underlying element of `stageProduct F n m x y` is `x.val *
y.val`, in that order. -/
@[simp]
theorem stageProduct_coe (n m : ℕ) (x : F n) (y : F m) :
    (stageProduct F n m x y).val = x.val * y.val := rfl

/-- A lower-stage left factor gives a lower-stage product.

If `x : F n` belongs to `lowerInStage F n`, then its product with any `y : F m` belongs to
`lowerInStage F (n + m)`. -/
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

/-- A lower-stage right factor gives a lower-stage product.

If `y : F m` belongs to `lowerInStage F m`, then its product with any `x : F n` belongs to
`lowerInStage F (n + m)`. -/
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

/-- Multiplication on associated graded quotient layers.

Postcompose filtered stage multiplication with the output quotient projection, then use
`LinearMap.liftQ₂` to descend both inputs by their preceding stages. The lower-left and
lower-right filtration laws give the two kernel conditions, including when a degree is zero. -/
def gradeProduct (n m : ℕ) : Grade F n →ₗ[R] Grade F m →ₗ[R] Grade F (n + m) :=
  LinearMap.liftQ₂ (lowerInStage F n) (lowerInStage F m)
    ((stageProduct F n m).compr₂ (lowerInStage F (n + m)).mkQ)
    (by
      intro x hx
      apply LinearMap.ext
      intro y
      change (lowerInStage F (n + m)).mkQ (stageProduct F n m x y) = 0
      exact (Submodule.Quotient.mk_eq_zero (lowerInStage F (n + m))).mpr
        (stageProduct_mem_lower_left F n m x y hx))
    (by
      intro y hy
      apply LinearMap.ext
      intro x
      change (lowerInStage F (n + m)).mkQ (stageProduct F n m x y) = 0
      exact (Submodule.Quotient.mk_eq_zero (lowerInStage F (n + m))).mpr
        (stageProduct_mem_lower_right F n m x y hy))

/-- Representative formula for quotient-layer multiplication.

For `x : F n` and `y : F m`, multiplying their quotient classes gives the class in degree `n +
m` of `x.val * y.val`. -/
theorem gradeProduct_mk (n m : ℕ) (x : F n) (y : F m) :
    gradeProduct F n m ((lowerInStage F n).mkQ x) ((lowerInStage F m).mkQ y) =
      (lowerInStage F (n + m)).mkQ
        ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩ := by
  simp only [gradeProduct, Submodule.mkQ_apply, LinearMap.liftQ₂_mk,
    LinearMap.compr₂_apply]
  rfl

/-- Algebra scalars restricted to filtration degree zero.

The algebra map `R → A` has image in `F 0`, since `1 ∈ F 0` and `F 0` is an `R`-submodule. Its
codomain restriction is an `R`-linear map `R →ₗ[R] F 0`. -/
def scalarStage : R →ₗ[R] F 0 :=
  (Algebra.linearMap R A).codRestrict (F 0) (fun r => by
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact (F 0).smul_mem r (SetLike.one_mem_graded F))

/-- Underlying element of the degree-zero scalar restriction.

For `r : R`, the underlying element of `scalarStage F r` is `algebraMap R A r`. -/
@[simp]
theorem scalarStage_coe (r : R) : (scalarStage F r).val = algebraMap R A r := rfl

/-- Unit class in the degree-zero quotient layer.

The element `gradeOne F : Grade F 0` is the quotient class of `1 : A`, regarded as an element
of `F 0`. -/
def gradeOne : Grade F 0 :=
  (lowerInStage F 0).mkQ ⟨(1 : A), SetLike.one_mem_graded F⟩

/-- Algebra scalars in the degree-zero quotient layer.

The linear map `gradeScalar F : R →ₗ[R] Grade F 0` is the degree-zero stage scalar map
followed by the quotient projection. -/
def gradeScalar : R →ₗ[R] Grade F 0 :=
  (lowerInStage F 0).mkQ.comp (scalarStage F)

/-- The scalar one gives the degree-zero unit class.

The degree-zero scalar class satisfies `gradeScalar F 1 = gradeOne F`. -/
theorem gradeScalar_one : gradeScalar F 1 = gradeOne F := by
  apply congrArg (lowerInStage F 0).mkQ
  apply Subtype.ext
  exact map_one (algebraMap R A)

/-- Graded multiplication on the quotient family.

The quotient-layer products define graded multiplication on the family `Grade F`, with a
product of degrees `n` and `m` lying in degree `n + m`. -/
instance gradeGMul : GradedMonoid.GMul (Grade F) where
  mul a b := gradeProduct F _ _ a b

/-- Graded unit in the quotient family.

The graded unit is `gradeOne F` in degree zero. -/
instance gradeGOne : GradedMonoid.GOne (Grade F) where
  one := gradeOne F

/-- Unit of the graded family as a representative class.

The unit of `GradedMonoid (Grade F)` is the element in degree zero represented by `1 : A` in
the quotient `Grade F 0`. -/
theorem graded_one : (1 : GradedMonoid (Grade F)) =
    GradedMonoid.mk (A := Grade F) 0 ((lowerInStage F 0).mkQ
      ⟨(1 : A), SetLike.one_mem_graded F⟩) := rfl

/-- Representative product in the graded family.

The product of degree-`n` and degree-`m` quotient representatives is the degree-`n + m` class
of their product in `A`. -/
theorem graded_mul_mk (n m : ℕ) (x : F n) (y : F m) :
    (GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ x) : GradedMonoid (Grade F)) *
        GradedMonoid.mk (A := Grade F) m ((lowerInStage F m).mkQ y) =
      GradedMonoid.mk (A := Grade F) (n + m) ((lowerInStage F (n + m)).mkQ
        ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩) := by
  change GradedMonoid.mk (A := Grade F) (n + m)
      (gradeProduct F n m ((lowerInStage F n).mkQ x) ((lowerInStage F m).mkQ y)) = _
  rw [gradeProduct_mk]

/-- Distributive graded multiplication on quotient layers.

The bilinear quotient products satisfy multiplication by zero and both distributive laws.
These give the graded nonunital nonassociative semiring structure on the family `Grade F`. -/
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
/-- Equal degree and representative give equal graded elements.

If `n = m` and representatives `u : F n` and `v : F m` have equal underlying elements in `A`,
their quotient classes define the same element of `GradedMonoid (Grade F)`. -/
theorem gradedMk_congr {n m : ℕ} (h : n = m) (u : F n) (v : F m)
    (huv : u.val = v.val) :
    GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ u) =
      GradedMonoid.mk (A := Grade F) m ((lowerInStage F m).mkQ v) := by
  subst m
  exact congrArg (fun q : F n => GradedMonoid.mk (A := Grade F) n ((lowerInStage F n).mkQ q))
    (Subtype.ext huv)

/-- Associative unital multiplication on the graded family.

The quotient-layer multiplication is associative, and the class of `1 : A` in degree zero is a
two-sided unit. These give the graded monoid structure on `Grade F`. -/
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

/-- Graded semiring structure of associated quotient layers.

The distributive graded multiplication and graded monoid structure combine to give a graded
semiring. Natural-number casts are represented by their algebra scalars in degree zero. -/
instance gradeGSemiring : DirectSum.GSemiring (Grade F) where
  __ := gradeGNonUnitalNonAssocSemiring F
  __ := gradeGMonoid F
  natCast n := gradeScalar F (n : R)
  natCast_zero := (congrArg (gradeScalar F) (Nat.cast_zero (R := R))).trans
    (gradeScalar F).map_zero
  natCast_succ n := by
    rw [Nat.cast_add, Nat.cast_one, map_add, gradeScalar_one]
    rfl

/-- Graded ring structure of associated quotient layers.

The graded semiring structure extends to a graded ring using the additive groups in the
quotient layers. Integer casts are their degree-zero scalar classes. -/
instance gradeGRing : DirectSum.GRing (Grade F) where
  __ := gradeGSemiring F
  intCast n := gradeScalar F (n : R)
  intCast_ofNat n := by
    exact congrArg (gradeScalar F) (Int.cast_natCast n)
  intCast_negSucc_ofNat n := by
    rw [Int.cast_negSucc]
    exact (gradeScalar F).map_neg _

/-- Graded algebra structure over the ground ring.

The degree-zero map `gradeScalar F` gives a graded `R`-algebra structure on `Grade F`. It
preserves the unit and multiplication, has central image, and induces the given `R`-action on
the quotient layers. -/
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

/-- Symbols multiply as filtered representatives.

For `x : F n` and `y : F m`, the product of their symbols is the degree-`n + m` symbol of
`x.val * y.val`. -/
theorem symbol_mul (n m : ℕ) (x : F n) (y : F m) :
    symbol F n x * symbol F m y =
      symbol F (n + m) ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩ := by
  change DirectSum.of (Grade F) n ((lowerInStage F n).mkQ x) *
      DirectSum.of (Grade F) m ((lowerInStage F m).mkQ y) = _
  rw [DirectSum.of_mul_of]
  change DirectSum.of (Grade F) (n + m)
    (gradeProduct F n m ((lowerInStage F n).mkQ x) ((lowerInStage F m).mkQ y)) = _
  exact congrArg (DirectSum.of (Grade F) (n + m)) (gradeProduct_mk F n m x y)

/-- Degree-zero symbol of the unit is the associated-graded unit.

The symbol of `1 : A`, regarded in `F 0`, equals `1` in the associated graded algebra. -/
theorem symbol_one :
    symbol F 0 ⟨(1 : A), SetLike.one_mem_graded F⟩ = 1 := rfl

/-- Degree-zero scalar symbols give the associated-graded algebra map.

For `r : R`, the symbol of `scalarStage F r` equals `algebraMap R (AssociatedGraded F) r`. -/
theorem symbol_algebraMap (r : R) :
    symbol F 0 (scalarStage F r) = algebraMap R (AssociatedGraded F) r := rfl

/-- Lowering filtered commutators makes homogeneous symbols commute.

Suppose `u.val * v.val - v.val * u.val ∈ lower F (n + m)` for all natural degrees and filtered
representatives. Then every pair of homogeneous symbols commutes in `AssociatedGraded F`. -/
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

/-- Degree-lowering commutators make the associated graded commutative.

If every commutator of elements in `F n` and `F m` lies in `lower F (n + m)`, then `x * y = y
* x` for all associated-graded elements `x` and `y`. The conclusion follows from commutativity
of symbols and additive generation. -/
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
