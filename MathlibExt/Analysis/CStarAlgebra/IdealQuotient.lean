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

public import MathlibExt.Analysis.Normed.Algebra.NonUnitalSubalgebra.Quotient
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Star.StarAlgHom

import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Quotients by closed two-sided nonunital star subalgebras

This file supplies the algebraic and topological carrier needed to quotient a
complex nonunital star algebra by a two-sided star-stable subspace. Mathlib's
canonical `Submodule.Quotient` remains the carrier, so its additive,
complex-linear, quotient-norm, and completeness API is reused definitionally.

The induced multiplication and star structures are scoped: importing this
file installs no global quotient-ring or quotient-star instance. Multiplication,
the ring and scalar laws, and the normed-ring structure delegate definitionally
to the neutral `NonUnitalSubalgebra.Quotient` construction. For a closed
two-sided star ideal, the quotient C-star structure is provided explicitly as
`NonUnitalStarSubalgebra.Quotient.nonUnitalCStarAlgebra`, also not as an instance.
If a nonunital star algebra homomorphism sends one two-sided star ideal into
another, `NonUnitalStarSubalgebra.Quotient.map` is the induced map on the two
quotients and `map_comp_mk` records its factorization through the projections.

Novelty boundary: `Ideal.Quotient` and `Ideal.quotientMap` support
noncommutative ideals carrying `Ideal.IsTwoSided`, and `TwoSidedIdeal` supplies
a ring-congruence quotient.  None provides this canonical complex
normed-module quotient together with the scoped star and C-star structure.
-/

@[expose] public section

namespace NonUnitalStarSubalgebra

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

/-- **Two-sided star ideal condition.** Let `A` be a nonunital normed ring with a ring involution and a
complex normed vector-space structure compatible with multiplication and star, and let `S ⊆ A` be a
nonunital complex star subalgebra. The subalgebra is two-sided when `a s` and `s a` belong to `S`
for every `a ∈ A` and `s ∈ S`. -/
class IsTwoSided (S : NonUnitalStarSubalgebra ℂ A) : Prop where
  mul_mem_left (a : A) {x : A} : x ∈ S → a * x ∈ S
  mul_mem_right {x : A} : x ∈ S → (a : A) → x * a ∈ S

/-- A two-sided star subalgebra has a two-sided underlying nonunital
subalgebra. -/
instance instIsTwoSidedToNonUnitalSubalgebra
    (S : NonUnitalStarSubalgebra ℂ A) [S.IsTwoSided] :
    NonUnitalSubalgebra.IsTwoSided S.toNonUnitalSubalgebra where
  mul_mem_left a {_x} hx := IsTwoSided.mul_mem_left a hx
  mul_mem_right {_x} hx a := IsTwoSided.mul_mem_right hx a

/-- **Complex submodule underlying a star subalgebra.** Let `A` be a nonunital normed ring with a ring
involution and a complex normed vector-space structure compatible with multiplication and star, and
let `S ⊆ A` be a nonunital complex star subalgebra. Its underlying complex vector subspace is the
submodule with the same elements as `S`. -/
abbrev quotientSubmodule (S : NonUnitalStarSubalgebra ℂ A) : Submodule ℂ A :=
  NonUnitalSubalgebra.quotientSubmodule S.toNonUnitalSubalgebra

/-- **Quotient by a star subalgebra.** Let `A` be a nonunital normed ring with a ring involution and a
complex normed vector-space structure compatible with multiplication and star, and let `S ⊆ A` be a
nonunital complex star subalgebra. The carrier `A/S` is the quotient of the complex vector space `A`
by the underlying submodule of `S`. -/
abbrev Quotient (S : NonUnitalStarSubalgebra ℂ A) :=
  NonUnitalSubalgebra.Quotient S.toNonUnitalSubalgebra

namespace Quotient

variable (S : NonUnitalStarSubalgebra ℂ A)

/-- **Complex-linear quotient projection.** Let `A` be a nonunital normed ring with a ring involution
and a complex normed vector-space structure compatible with multiplication and star, and let `S ⊆ A`
be a nonunital complex star subalgebra. The projection `a ↦ [a]` is a complex-linear map from `A` to
the vector quotient `A/S`. -/
def mkL : A →ₗ[ℂ] S.Quotient :=
  (quotientSubmodule S).mkQ

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
@[simp]
theorem mkL_apply (a : A) : mkL S a = Submodule.Quotient.mk a := rfl

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
theorem mkL_surjective : Function.Surjective (mkL S) :=
  (quotientSubmodule S).mkQ_surjective

/-- **Multiplication on a two-sided quotient.** Let `A` be a nonunital normed ring with a ring
involution and a complex normed vector-space structure compatible with multiplication and star, and
let `S ⊆ A` be a nonunital complex star subalgebra. If `S` is two-sided, multiplication on `A/S` is
given by `[a][b] = [a b]`. -/
@[instance_reducible]
def quotientMul [S.IsTwoSided] : Mul S.Quotient :=
  NonUnitalSubalgebra.Quotient.quotientMul S.toNonUnitalSubalgebra

/-- **Involution on a star quotient.** Let `A` be a nonunital normed ring with a ring involution and a
complex normed vector-space structure compatible with multiplication and star, and let `S ⊆ A` be a
nonunital complex star subalgebra. The involution on `A/S` is given by `[a]* = [a*]`. -/
@[instance_reducible]
def quotientStar : Star S.Quotient where
  star := _root_.Quotient.map' (fun x : A ↦ star x) fun x y hxy ↦ by
    apply (Submodule.quotientRel_def (quotientSubmodule S)).2
    have hxy' : x - y ∈ S :=
      (Submodule.quotientRel_def (quotientSubmodule S)).1 hxy
    change star x - star y ∈ S
    simpa only [star_sub] using (star_mem (s := S) hxy')

/-- Scoped quotient multiplication. -/
scoped instance instMul [S.IsTwoSided] : Mul S.Quotient := quotientMul S

/-- Scoped quotient involution. -/
scoped instance instStar : Star S.Quotient := quotientStar S

open scoped NonUnitalStarSubalgebra.Quotient

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
theorem mk_mul [S.IsTwoSided] (x y : A) :
    (Submodule.Quotient.mk (x * y) : S.Quotient) =
      Submodule.Quotient.mk x * Submodule.Quotient.mk y :=
  NonUnitalSubalgebra.Quotient.mk_mul S.toNonUnitalSubalgebra x y

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
@[simp]
theorem mk_star (x : A) :
    (Submodule.Quotient.mk (star x) : S.Quotient) =
      star (Submodule.Quotient.mk x : S.Quotient) := by
  rfl

/-- Scoped nonunital ring structure induced from the ambient ring. -/
scoped instance instNonUnitalRing [S.IsTwoSided] :
    NonUnitalRing S.Quotient :=
  NonUnitalSubalgebra.Quotient.instNonUnitalRing S.toNonUnitalSubalgebra

/-- Scoped star-ring structure induced from the ambient involution. -/
scoped instance instStarRing [S.IsTwoSided] :
    StarRing S.Quotient where
  star_involutive := by
    rintro ⟨x⟩
    change Submodule.Quotient.mk (star (star x)) = Submodule.Quotient.mk x
    rw [star_star]
  star_add := by
    rintro ⟨x⟩ ⟨y⟩
    change Submodule.Quotient.mk (star (x + y)) =
      Submodule.Quotient.mk (star x + star y)
    rw [star_add]
  star_mul := by
    rintro ⟨x⟩ ⟨y⟩
    change Submodule.Quotient.mk (star (x * y)) =
      Submodule.Quotient.mk (star y * star x)
    rw [star_mul]

/-- Scoped complex star-module structure. -/
scoped instance instStarModule :
    StarModule ℂ S.Quotient where
  star_smul := by
    intro c x
    rcases x with ⟨x⟩
    change Submodule.Quotient.mk (star (c • x)) =
      Submodule.Quotient.mk (star c • star x)
    rw [star_smul]

/-- Scoped scalar-tower law, the first half of the nonunital complex algebra structure. -/
scoped instance instIsScalarTower [S.IsTwoSided] :
    IsScalarTower ℂ S.Quotient S.Quotient :=
  NonUnitalSubalgebra.Quotient.instIsScalarTower S.toNonUnitalSubalgebra

/-- Scoped scalar-commutation law, the second half of the nonunital complex algebra structure. -/
scoped instance instSMulCommClass [S.IsTwoSided] :
    SMulCommClass ℂ S.Quotient S.Quotient :=
  NonUnitalSubalgebra.Quotient.instSMulCommClass S.toNonUnitalSubalgebra

/-- **Star-algebra quotient projection.** Let `A` be a nonunital normed ring with a ring involution and
a complex normed vector-space structure compatible with multiplication and star, and let `S ⊆ A` be
a nonunital complex star subalgebra. If `S` is two-sided, the projection `a ↦ [a]` is a nonunital
complex star-algebra homomorphism from `A` to `A/S`. -/
def mk [S.IsTwoSided] : A →⋆ₙₐ[ℂ] S.Quotient where
  toFun := Submodule.Quotient.mk
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
@[simp]
theorem mk_apply [S.IsTwoSided] (x : A) : mk S x = Submodule.Quotient.mk x := rfl

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
theorem mk_eq_zero [S.IsTwoSided] (x : A) : mk S x = 0 ↔ x ∈ S :=
  Submodule.Quotient.mk_eq_zero (quotientSubmodule S)

section Normed

/-- **Continuous linear quotient projection.** Let `A` be a nonunital normed ring with a ring involution
and a complex normed vector-space structure compatible with multiplication and star, and let `S ⊆ A`
be a nonunital complex star subalgebra. With the quotient seminorm on `A/S`, the projection `a ↦
[a]` is a continuous complex-linear map. -/
def mkCL : A →L[ℂ] S.Quotient :=
  (quotientSubmodule S).mkQL

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
@[simp]
theorem mkCL_apply (x : A) : mkCL S x = Submodule.Quotient.mk x := rfl

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] in
/-- **Contractivity of the quotient projection.** Let `A` be a nonunital normed ring with a ring
involution and a complex normed vector-space structure compatible with multiplication and star, and
let `S ⊆ A` be a nonunital complex star subalgebra. For every `a ∈ A`, the quotient seminorm
satisfies `‖[a]‖ ≤ ‖a‖`. -/
theorem norm_mk_le (x : A) :
    ‖(Submodule.Quotient.mk x : S.Quotient)‖ ≤ ‖x‖ :=
  NonUnitalSubalgebra.Quotient.norm_mk_le S.toNonUnitalSubalgebra x

end Normed

variable {B : Type*} [NonUnitalRing B] [StarRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]

/-- **Descended star homomorphism on a quotient.** Let `A` be a nonunital normed ring with a ring
involution and a complex normed vector-space structure compatible with multiplication and star, and
let `S ⊆ A` be a nonunital complex star subalgebra. Assume that `S` is two-sided. For a nonunital
complex star algebra `B` and a nonunital complex star homomorphism `f : A → B` that vanishes on `S`,
there is a descended star homomorphism `A/S → B` sending `[a]` to `f(a)`. -/
def lift [S.IsTwoSided] (f : A →⋆ₙₐ[ℂ] B) (hS : ∀ x ∈ S, f x = 0) :
    S.Quotient →⋆ₙₐ[ℂ] B := by
  let fL : S.Quotient →ₗ[ℂ] B :=
    (quotientSubmodule S).liftQ (LinearMap.ofClass f) fun x hx ↦ hS x hx
  exact
    { toFun := fL
      map_zero' := fL.map_zero
      map_add' := fL.map_add
      map_smul' := fL.map_smul
      map_mul' := by
        rintro ⟨x⟩ ⟨y⟩
        change f (x * y) = f x * f y
        exact map_mul f x y
      map_star' := by
        rintro ⟨x⟩
        change f (star x) = star (f x)
        exact map_star f x }

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] in
theorem lift_mk [S.IsTwoSided] (f : A →⋆ₙₐ[ℂ] B)
    (hS : ∀ x ∈ S, f x = 0) (x : A) :
    lift S f hS (mk S x) = f x := by
  rfl

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] in
/-- **Evaluation of a descended star homomorphism.** Let `A` be a nonunital normed ring with a ring
involution and a complex normed vector-space structure compatible with multiplication and star, and
let `S ⊆ A` be a nonunital complex star subalgebra. Assume that `S` is two-sided. For a nonunital
complex star algebra `B`, a nonunital complex star homomorphism `f : A → B` vanishing on `S`, and `a
∈ A`, its quotient lift evaluates at `[a]` to `f(a)`. -/
@[simp]
theorem lift_mkQ [S.IsTwoSided] (f : A →⋆ₙₐ[ℂ] B)
    (hS : ∀ x ∈ S, f x = 0) (x : A) :
    lift S f hS (Submodule.Quotient.mk x) = f x :=
  lift_mk S f hS x

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] in
/-- **Extensionality of quotient star homomorphisms.** Let `A` be a nonunital normed ring with a ring
involution and a complex normed vector-space structure compatible with multiplication and star, and
let `S ⊆ A` be a nonunital complex star subalgebra. Assume that `S` is two-sided. For a nonunital
complex star algebra `B`, two nonunital star homomorphisms `A/S → B` are equal if their composites
with the projection `A → A/S` agree. -/
theorem hom_ext [S.IsTwoSided]
    (f g : S.Quotient →⋆ₙₐ[ℂ] B)
    (h : f.comp (mk S) = g.comp (mk S)) : f = g := by
  ext x
  obtain ⟨x, rfl⟩ := mkL_surjective S x
  exact DFunLike.congr_fun h x

section Map

variable {C : Type*} [NonUnitalNormedRing C] [StarRing C] [NormedSpace ℂ C]
  [IsScalarTower ℂ C C] [SMulCommClass ℂ C C] [StarModule ℂ C]
variable (T : NonUnitalStarSubalgebra ℂ C)

/-- **Star homomorphism induced on quotients.** Let `A,C` be nonunital normed complex star algebras, let
`S ⊆ A` and `T ⊆ C` be two-sided nonunital star subalgebras, and let `f : A → C` be a nonunital
complex star homomorphism satisfying `f(S) ⊆ T`. It induces the nonunital complex star homomorphism
`A/S → C/T` given by `[a] ↦ [f(a)]`. -/
def map [S.IsTwoSided] [T.IsTwoSided]
    (f : A →⋆ₙₐ[ℂ] C) (hf : Set.MapsTo f S T) :
    S.Quotient →⋆ₙₐ[ℂ] T.Quotient :=
  lift S ((mk T).comp f) fun x hx ↦ (mk_eq_zero T (f x)).2 (hf hx)

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [IsScalarTower ℂ C C] [SMulCommClass ℂ C C] [StarModule ℂ C] in
theorem map_mk [S.IsTwoSided] [T.IsTwoSided]
    (f : A →⋆ₙₐ[ℂ] C) (hf : Set.MapsTo f S T) (x : A) :
    NonUnitalStarSubalgebra.Quotient.map S T f hf (mk S x) = mk T (f x) :=
  lift_mk S ((mk T).comp f) _ x

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [IsScalarTower ℂ C C] [SMulCommClass ℂ C C] [StarModule ℂ C] in
/-- **Evaluation of an induced quotient map.** Let `A,C` be nonunital normed complex star algebras, let
`S ⊆ A` and `T ⊆ C` be two-sided nonunital star subalgebras, and let `f : A → C` be a nonunital
complex star homomorphism satisfying `f(S) ⊆ T`. For each `a ∈ A`, the induced quotient homomorphism
sends its class modulo `S` to the class of `f(a)` modulo `T`. -/
@[simp]
theorem map_mkQ [S.IsTwoSided] [T.IsTwoSided]
    (f : A →⋆ₙₐ[ℂ] C) (hf : Set.MapsTo f S T) (x : A) :
    NonUnitalStarSubalgebra.Quotient.map S T f hf
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  map_mk S T f hf x

omit [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [IsScalarTower ℂ C C] [SMulCommClass ℂ C C] [StarModule ℂ C] in
/-- **Quotient projections intertwine an induced map.** Let `A,C` be nonunital normed complex star
algebras, let `S ⊆ A` and `T ⊆ C` be two-sided nonunital star subalgebras, and let `f : A → C` be a
nonunital complex star homomorphism satisfying `f(S) ⊆ T`. The projection `A → A/S` followed by the
induced map equals `f` followed by the projection `C → C/T`. -/
theorem map_comp_mk [S.IsTwoSided] [T.IsTwoSided]
    (f : A →⋆ₙₐ[ℂ] C) (hf : Set.MapsTo f S T) :
    (NonUnitalStarSubalgebra.Quotient.map S T f hf).comp (mk S) = (mk T).comp f := by
  ext x
  exact map_mk S T f hf x

end Map

section Analytic

open Filter Metric
open scoped CStarAlgebra Topology

variable {B : Type*} [NonUnitalCStarAlgebra B]
variable (T : NonUnitalStarSubalgebra ℂ B)

/-- **Submultiplicative quotient seminorm.** Let `B` be a nonunital complex C*-algebra and `T ⊆ B` a
two-sided nonunital star subalgebra. The quotient seminorm on `B/T` satisfies `‖x y‖ ≤ ‖x‖ ‖y‖` for
every pair of quotient elements. -/
theorem norm_mul_le [T.IsTwoSided] (x y : T.Quotient) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  NonUnitalSubalgebra.Quotient.norm_mul_le T.toNonUnitalSubalgebra x y

/-- The quotient normed-ring structure is the neutral quotient structure. -/
noncomputable scoped instance instNonUnitalNormedRing
    [T.IsTwoSided] [IsClosed (T : Set B)] :
    NonUnitalNormedRing T.Quotient :=
  NonUnitalSubalgebra.Quotient.instNonUnitalNormedRing T.toNonUnitalSubalgebra

/-- **Involution preserves the quotient seminorm.** Let `B` be a nonunital complex C*-algebra and `T ⊆
B` a two-sided nonunital star subalgebra. For every `x ∈ B/T`, `‖x*‖ = ‖x‖`. -/
theorem norm_star_eq [T.IsTwoSided] (x : T.Quotient) : ‖star x‖ = ‖x‖ := by
  have hle (y : T.Quotient) : ‖star y‖ ≤ ‖y‖ := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨a, ha, haε⟩ :=
      Submodule.Quotient.norm_mk_lt (S := quotientSubmodule T) y hε
    calc
      ‖star y‖ = ‖(Submodule.Quotient.mk (star a) : T.Quotient)‖ := by
        rw [← ha, mk_star]
      _ ≤ ‖star a‖ := norm_mk_le T _
      _ = ‖a‖ := _root_.norm_star a
      _ ≤ ‖y‖ + ε := haε.le
  refine le_antisymm (hle x) ?_
  have hss : star (star x) = x := (instStarRing T).star_involutive x
  simpa only [hss] using hle (star x)

private theorem norm_compression_le (e b : B)
    (he : ‖1 - (e : B⁺¹)‖ ≤ 1) :
    ‖b - e * b - b * e + e * b * e‖ ≤ ‖b‖ := by
  rw [← Unitization.norm_inr (𝕜 := ℂ)]
  simp only [Unitization.inr_add, Unitization.inr_sub, Unitization.inr_mul]
  rw [show (b : B⁺¹) - e * b - b * e + e * b * e =
      (1 - e) * b * (1 - e) by noncomm_ring]
  calc
    ‖(1 - (e : B⁺¹)) * (b : B⁺¹) * (1 - e)‖ ≤
        ‖(1 - (e : B⁺¹)) * (b : B⁺¹)‖ * ‖1 - (e : B⁺¹)‖ :=
      _root_.norm_mul_le _ _
    _ ≤ (‖1 - (e : B⁺¹)‖ * ‖(b : B⁺¹)‖) * ‖1 - (e : B⁺¹)‖ :=
      mul_le_mul_of_nonneg_right (_root_.norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖(b : B⁺¹)‖) * 1 := by gcongr
    _ = ‖b‖ := by simp [Unitization.norm_inr]

private theorem exists_complementary_contraction_norm_sub_mul_lt
    [IsClosed (T : Set B)] (i : T) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : T, star (e : B) = e ∧ ‖e‖ ≤ 1 ∧
      ‖1 - ((e : B) : B⁺¹)‖ ≤ 1 ∧ ‖i - e * i‖ < ε := by
  let _ : PartialOrder B := CStarAlgebra.spectralOrder B
  let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let l := CStarAlgebra.approximateUnit T
  have hl : Filter.IsIncreasingApproximateUnit l := CStarAlgebra.increasingApproximateUnit T
  have ht : Tendsto (fun e : T ↦ i - e * i) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := i) (f := l)).sub (hl.tendsto_mul_right i)
  have hevent : ∀ᶠ e in l, ‖i - e * i‖ < ε := by
    simpa [dist_eq_norm] using Metric.tendsto_nhds.mp ht ε hε
  obtain ⟨e, he0, he1, heclose⟩ :=
    (hl.eventually_nonneg.and <| hl.eventually_norm.and hevent).exists
  have he0B : 0 ≤ (e : B) := by
    have he0' : ((0 : T) : B) ≤ (e : B) := Subtype.coe_le_coe.mpr he0
    simpa only [NonUnitalStarSubalgebra.coe_zero T] using he0'
  have heIcc : ((e : B) : B⁺¹) ∈ Set.Icc 0 1 := by
    refine ⟨Unitization.inr_nonneg_iff.mpr he0B, ?_⟩
    rw [← CStarAlgebra.norm_le_one_iff_of_nonneg _
        (Unitization.inr_nonneg_iff.mpr he0B),
      Unitization.norm_inr]
    exact he1
  have hOneSub : ‖1 - ((e : B) : B⁺¹)‖ ≤ 1 := by
    have hnonneg : 0 ≤ 1 - ((e : B) : B⁺¹) := sub_nonneg.mpr heIcc.2
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnonneg).2
      (sub_le_self 1 heIcc.1)
  exact ⟨e, he0B.isSelfAdjoint.star_eq, he1, hOneSub, heclose⟩

/-- **C*-lower bound in a closed quotient.** Let `B` be a nonunital complex C*-algebra and `T ⊆ B` a
closed two-sided nonunital star subalgebra. For every `x ∈ B/T`, `‖x‖² ≤ ‖x* x‖` in the quotient
norm. -/
theorem norm_sq_le_norm_star_mul_self [T.IsTwoSided] [IsClosed (T : Set B)]
    (x : T.Quotient) : ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  obtain ⟨a, rfl⟩ := mkL_surjective T x
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨b, hb, hbε⟩ := Submodule.Quotient.norm_mk_lt
    (S := quotientSubmodule T)
    (star (Submodule.Quotient.mk a : T.Quotient) * Submodule.Quotient.mk a) (half_pos hε)
  let i : B := star a * a - b
  have hi : i ∈ T := by
    apply (mk_eq_zero T i).1
    dsimp only [i]
    have hb' : mk T b = star (mk T a) * mk T a := by simpa using hb
    rw [map_sub, map_mul, map_star, hb']
    simp
  obtain ⟨e, hestar, heNorm, heContract, heclose⟩ :=
    exists_complementary_contraction_norm_sub_mul_lt T (⟨i, hi⟩ : T) (by positivity : 0 < ε / 4)
  let eB : B := e
  change ‖i - eB * i‖ < ε / 4 at heclose
  have hresidual : ‖(i - eB * i) - (i - eB * i) * eB‖ < ε / 2 := by
    calc
      ‖(i - eB * i) - (i - eB * i) * eB‖ ≤
          ‖i - eB * i‖ + ‖(i - eB * i) * eB‖ := norm_sub_le _ _
      _ ≤ ‖i - eB * i‖ + ‖i - eB * i‖ * ‖eB‖ :=
        add_le_add le_rfl (_root_.norm_mul_le _ _)
      _ ≤ ‖i - eB * i‖ + ‖i - eB * i‖ :=
        add_le_add le_rfl <| by
          calc
            ‖i - eB * i‖ * ‖eB‖ ≤ ‖i - eB * i‖ * 1 :=
              mul_le_mul_of_nonneg_left (by simpa [eB] using heNorm) (norm_nonneg _)
            _ = ‖i - eB * i‖ := mul_one _
      _ < ε / 2 := by linarith
  have hae : a * eB ∈ T := IsTwoSided.mul_mem_left a e.property
  have hae0 : (Submodule.Quotient.mk (a * eB) : T.Quotient) = 0 :=
    (mk_eq_zero T _).2 hae
  have hquot : ‖(Submodule.Quotient.mk a : T.Quotient)‖ ≤ ‖a - a * eB‖ := by
    rw [← show (Submodule.Quotient.mk (a - a * eB) : T.Quotient) =
      Submodule.Quotient.mk a by
        rw [Submodule.Quotient.mk_sub, hae0, sub_zero]]
    exact norm_mk_le T _
  have hsquare :
      star (a - a * eB) * (a - a * eB) =
        (b - eB * b - b * eB + eB * b * eB) +
          ((i - eB * i) - (i - eB * i) * eB) := by
    dsimp only [i]
    rw [star_sub, star_mul, hestar]
    noncomm_ring
  calc
    ‖(Submodule.Quotient.mk a : T.Quotient)‖ *
        ‖(Submodule.Quotient.mk a : T.Quotient)‖ ≤
        ‖a - a * eB‖ * ‖a - a * eB‖ :=
      mul_self_le_mul_self (norm_nonneg _) hquot
    _ = ‖star (a - a * eB) * (a - a * eB)‖ :=
      CStarRing.norm_star_mul_self.symm
    _ = ‖(b - eB * b - b * eB + eB * b * eB) +
          ((i - eB * i) - (i - eB * i) * eB)‖ := by rw [hsquare]
    _ ≤ ‖b - eB * b - b * eB + eB * b * eB‖ +
          ‖(i - eB * i) - (i - eB * i) * eB‖ := norm_add_le _ _
    _ ≤ ‖b‖ + ε / 2 := (add_lt_add_of_le_of_lt
      (norm_compression_le eB b heContract) hresidual).le
    _ ≤ (‖star (Submodule.Quotient.mk a : T.Quotient) *
          Submodule.Quotient.mk a‖ + ε / 2) + ε / 2 :=
      by linarith
    _ = ‖star (Submodule.Quotient.mk a : T.Quotient) *
          Submodule.Quotient.mk a‖ + ε := by ring

/-- **C*-algebra structure on a closed star quotient.** Let `B` be a nonunital complex C*-algebra and `T
⊆ B` a closed two-sided nonunital star subalgebra. The quotient `B/T`, with its quotient norm and
induced complex algebra operations and involution, is a nonunital complex C*-algebra. -/
@[instance_reducible]
noncomputable def nonUnitalCStarAlgebra [T.IsTwoSided] [IsClosed (T : Set B)] :
    NonUnitalCStarAlgebra T.Quotient where
  toNonUnitalNormedRing := instNonUnitalNormedRing T
  __ : StarRing T.Quotient := instStarRing T
  __ : CompleteSpace T.Quotient := inferInstance
  __ : NormedSpace ℂ T.Quotient := inferInstance
  __ : IsScalarTower ℂ T.Quotient T.Quotient := instIsScalarTower T
  __ : SMulCommClass ℂ T.Quotient T.Quotient := instSMulCommClass T
  __ : StarModule ℂ T.Quotient := instStarModule T
  norm_mul_self_le := norm_sq_le_norm_star_mul_self T

end Analytic

end Quotient

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgHom

open scoped CStarAlgebra NonUnitalStarSubalgebra.Quotient

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

private def closedRangeKernel (rho : A →⋆ₙₐ[ℂ] B) :
    NonUnitalStarSubalgebra ℂ A :=
  NonUnitalStarSubalgebra.comap rho ⊥

@[simp]
private theorem mem_closedRangeKernel_iff (rho : A →⋆ₙₐ[ℂ] B) (a : A) :
    a ∈ closedRangeKernel rho ↔ rho a = 0 := by
  change rho a ∈ (⊥ : NonUnitalStarSubalgebra ℂ B) ↔ rho a = 0
  exact NonUnitalStarAlgebra.mem_bot

private theorem closedRangeKernelIsTwoSided (rho : A →⋆ₙₐ[ℂ] B) :
    (closedRangeKernel rho).IsTwoSided where
  mul_mem_left a {x} hx := by
    rw [mem_closedRangeKernel_iff] at hx ⊢
    simp [hx]
  mul_mem_right {x} hx a := by
    rw [mem_closedRangeKernel_iff] at hx ⊢
    simp [hx]

private theorem isClosed_closedRangeKernel (rho : A →⋆ₙₐ[ℂ] B) :
    IsClosed (closedRangeKernel rho : Set A) := by
  simpa [closedRangeKernel] using
    (isClosed_singleton.preimage (map_continuous rho) : IsClosed (rho ⁻¹' ({0} : Set B)))

private def closedRangeKernelLift (rho : A →⋆ₙₐ[ℂ] B)
    [(closedRangeKernel rho).IsTwoSided] :
    (closedRangeKernel rho).Quotient →⋆ₙₐ[ℂ] B :=
  NonUnitalStarSubalgebra.Quotient.lift (closedRangeKernel rho) rho
    fun x hx ↦ (mem_closedRangeKernel_iff rho x).1 hx

private theorem closedRangeKernelLift_mk (rho : A →⋆ₙₐ[ℂ] B)
    [(closedRangeKernel rho).IsTwoSided] (a : A) :
    closedRangeKernelLift rho (NonUnitalStarSubalgebra.Quotient.mk
      (closedRangeKernel rho) a) = rho a :=
  NonUnitalStarSubalgebra.Quotient.lift_mk (closedRangeKernel rho) rho _ a

@[simp]
private theorem closedRangeKernelLift_mkQ (rho : A →⋆ₙₐ[ℂ] B)
    [(closedRangeKernel rho).IsTwoSided] (a : A) :
    closedRangeKernelLift rho (Submodule.Quotient.mk a) = rho a :=
  closedRangeKernelLift_mk rho a

private theorem closedRangeKernelLift_injective (rho : A →⋆ₙₐ[ℂ] B)
    [(closedRangeKernel rho).IsTwoSided] :
    Function.Injective (closedRangeKernelLift rho) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ :=
    NonUnitalStarSubalgebra.Quotient.mkL_surjective (closedRangeKernel rho) x
  obtain ⟨b, rfl⟩ :=
    NonUnitalStarSubalgebra.Quotient.mkL_surjective (closedRangeKernel rho) y
  apply (Submodule.Quotient.eq
    (NonUnitalStarSubalgebra.quotientSubmodule (closedRangeKernel rho))).2
  have hxy' : rho a = rho b := by
    rw [← closedRangeKernelLift_mk rho a, ← closedRangeKernelLift_mk rho b]
    exact hxy
  change a - b ∈ closedRangeKernel rho
  rw [mem_closedRangeKernel_iff, map_sub, sub_eq_zero]
  exact hxy'

private theorem range_closedRangeKernelLift (rho : A →⋆ₙₐ[ℂ] B)
    [(closedRangeKernel rho).IsTwoSided] :
    Set.range (closedRangeKernelLift rho) = Set.range rho := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨a, rfl⟩ :=
      NonUnitalStarSubalgebra.Quotient.mkL_surjective (closedRangeKernel rho) q
    exact ⟨a, (closedRangeKernelLift_mk rho a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨NonUnitalStarSubalgebra.Quotient.mk (closedRangeKernel rho) a,
      closedRangeKernelLift_mk rho a⟩

/-- **Closed range of a C*-homomorphism.** For nonunital complex C*-algebras `A,B`, the range of every
nonunital complex star-algebra homomorphism `ρ : A → B` is closed in the norm topology of `B`. -/
theorem isClosed_range (rho : A →⋆ₙₐ[ℂ] B) : IsClosed (Set.range rho) := by
  let _ : (closedRangeKernel rho).IsTwoSided := closedRangeKernelIsTwoSided rho
  let _ : IsClosed (closedRangeKernel rho : Set A) := isClosed_closedRangeKernel rho
  let _ : NonUnitalCStarAlgebra (closedRangeKernel rho).Quotient :=
    NonUnitalStarSubalgebra.Quotient.nonUnitalCStarAlgebra (closedRangeKernel rho)
  rw [← range_closedRangeKernelLift rho]
  exact (NonUnitalStarAlgHom.isometry (closedRangeKernelLift rho)
    (closedRangeKernelLift_injective rho)).isClosedEmbedding.isClosed_range

end NonUnitalStarAlgHom

/-! ## Bundled closed two-sided star ideals -/

/-- **Closed two-sided star ideal.** For a nonunital complex C*-algebra `A`, this is a nonunital complex
star subalgebra `I ⊆ A` that is norm-closed and absorbs multiplication by every element of `A` on
both sides. -/
structure ClosedStarIdeal (A : Type*) [NonUnitalCStarAlgebra A] where
  /-- The actual scalar-stable star subalgebra underlying the two-sided ideal. -/
  carrier : NonUnitalStarSubalgebra ℂ A
  isTwoSided : carrier.IsTwoSided
  isClosed : IsClosed (carrier : Set A)

namespace ClosedStarIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

open scoped CStarAlgebra

instance instSetLike : SetLike (ClosedStarIdeal A) A where
  coe I := I.carrier
  coe_injective I J h := by
    cases I
    cases J
    congr
    exact SetLike.coe_injective h

instance instCoeCarrier :
    Coe (ClosedStarIdeal A) (NonUnitalStarSubalgebra ℂ A) :=
  ⟨carrier⟩

@[simp]
theorem mem_carrier (I : ClosedStarIdeal A) (x : A) :
    x ∈ I.carrier ↔ x ∈ I :=
  Iff.rfl

@[ext]
theorem ext {I J : ClosedStarIdeal A}
    (h : ∀ x : A, x ∈ I ↔ x ∈ J) : I = J := by
  apply SetLike.coe_injective
  ext x
  exact h x

/-- Closed star ideals are ordered by inclusion of their carriers. -/
instance instPartialOrder : PartialOrder (ClosedStarIdeal A) :=
  PartialOrder.lift ((↑) : ClosedStarIdeal A → Set A) SetLike.coe_injective

/-- **Zero closed star ideal.** The zero subalgebra is a closed two-sided star ideal of every nonunital
complex C*-algebra `A`. -/
def bot (A : Type*) [NonUnitalCStarAlgebra A] : ClosedStarIdeal A where
  carrier := ⊥
  isTwoSided := by
    constructor
    · intro a x hx
      have hx0 : x = 0 := NonUnitalStarAlgebra.mem_bot.mp hx
      subst x
      simp
    · intro x hx a
      have hx0 : x = 0 := NonUnitalStarAlgebra.mem_bot.mp hx
      subst x
      simp
  isClosed := by
    simpa only [NonUnitalStarAlgebra.coe_bot] using
      (isClosed_singleton : IsClosed ({0} : Set A))

@[simp]
theorem mem_bot (x : A) : x ∈ bot A ↔ x = 0 :=
  NonUnitalStarAlgebra.mem_bot

instance instOrderBot : OrderBot (ClosedStarIdeal A) where
  bot := bot A
  bot_le I := by
    intro x hx
    have hx0 : x = 0 := (mem_bot x).1 hx
    subst x
    exact I.carrier.zero_mem

/-- **Whole closed star ideal.** The whole algebra is a closed two-sided star ideal of every nonunital
complex C*-algebra `A`. -/
def top (A : Type*) [NonUnitalCStarAlgebra A] : ClosedStarIdeal A where
  carrier := ⊤
  isTwoSided := by
    constructor <;> simp
  isClosed := by
    simpa only [NonUnitalStarAlgebra.coe_top] using
      (isClosed_univ : IsClosed (Set.univ : Set A))

@[simp]
theorem mem_top (x : A) : x ∈ top A :=
  Set.mem_univ x

instance instOrderTop : OrderTop (ClosedStarIdeal A) where
  top := top A
  le_top _I := by
    intro x _hx
    exact mem_top x

/-! ### Essential closed star ideals -/

/-- **Essential closed star ideal.** Let `A` be a nonunital complex C*-algebra and let `I ⊆ A` be a
closed two-sided star ideal. The ideal is essential when `a x = 0` for every `x ∈ I` implies `a = 0`
for every `a ∈ A`, so its left annihilator is zero. -/
def IsEssential (I : ClosedStarIdeal A) : Prop :=
  ∀ a : A, (∀ x : I, a * (x : A) = 0) → a = 0

/-- **Left and right annihilator characterizations of essentiality.** Let `A` be a nonunital complex
C*-algebra and let `I ⊆ A` be a closed two-sided star ideal. The ideal is essential exactly when `x
a = 0` for every `x ∈ I` implies `a = 0`, so its right annihilator is also zero. -/
theorem isEssential_iff_right_annihilator_zero (I : ClosedStarIdeal A) :
    I.IsEssential ↔
      ∀ a : A, (∀ x : I, (x : A) * a = 0) → a = 0 := by
  constructor
  · intro hI a ha
    have hstar : star a = 0 := hI (star a) fun x ↦ by
      have hxstar : star (x : A) ∈ I :=
        StarMemClass.star_mem (s := I.carrier) x.property
      have hzero := ha (⟨star (x : A), hxstar⟩ : I)
      have := congrArg star hzero
      simpa only [star_mul, star_zero, star_star] using this
    simpa only [star_eq_zero] using hstar
  · intro hI a ha
    have hstar : star a = 0 := hI (star a) fun x ↦ by
      have hxstar : star (x : A) ∈ I :=
        StarMemClass.star_mem (s := I.carrier) x.property
      have hzero := ha (⟨star (x : A), hxstar⟩ : I)
      have := congrArg star hzero
      simpa only [star_mul, star_zero, star_star] using this
    simpa only [star_eq_zero] using hstar

/-- **Preimage of a closed star ideal.** For nonunital complex C*-algebras `A,B`, a nonunital complex
star homomorphism `f : A → B`, and a closed two-sided star ideal `J ⊆ B`, the preimage `f⁻¹(J)` is a
closed two-sided star ideal of `A`. -/
def comap
    {B : Type*} [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (J : ClosedStarIdeal B) : ClosedStarIdeal A where
  carrier := NonUnitalStarSubalgebra.comap f J.carrier
  isTwoSided := by
    constructor
    · intro a x hx
      change f (a * x) ∈ J
      rw [map_mul]
      exact J.isTwoSided.mul_mem_left (f a) hx
    · intro x hx a
      change f (x * a) ∈ J
      rw [map_mul]
      exact J.isTwoSided.mul_mem_right hx (f a)
  isClosed := by
    change IsClosed (f ⁻¹' (J : Set B))
    exact J.isClosed.preimage (map_continuous f)

@[simp]
theorem mem_comap
    {B : Type*} [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (J : ClosedStarIdeal B) (x : A) :
    x ∈ comap f J ↔ f x ∈ J :=
  Iff.rfl

/-- **Kernel as a closed star ideal.** For nonunital complex C*-algebras `A,B` and a nonunital complex
star homomorphism `f : A → B`, the kernel `{a : f(a) = 0}` is a closed two-sided star ideal of `A`. -/
def ker
    {B : Type*} [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) : ClosedStarIdeal A :=
  comap f (bot B)

@[simp]
theorem mem_ker
    {B : Type*} [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (x : A) :
    x ∈ ker f ↔ f x = 0 := by
  rw [ker, mem_comap, mem_bot]

/-! ### Canonical carrier and quotient structures -/

/-- **C*-algebra structure of a closed star ideal.** Let `A` be a nonunital complex C*-algebra and let
`I ⊆ A` be a closed two-sided star ideal. The ideal `I`, with its inherited norm, involution, and
complex algebra operations, is a nonunital complex C*-algebra. -/
@[instance_reducible]
noncomputable def carrierCStarAlgebra (I : ClosedStarIdeal A) :
    NonUnitalCStarAlgebra I.carrier := by
  let _ : IsClosed (I.carrier : Set A) := I.isClosed
  exact NonUnitalStarSubalgebra.nonUnitalCStarAlgebra I.carrier

/-- **Quotient carrier of a closed star ideal.** Let `A` be a nonunital complex C*-algebra and let `I ⊆
A` be a closed two-sided star ideal. Its quotient carrier is the complex vector quotient `A/I`. -/
abbrev Quotient (I : ClosedStarIdeal A) := I.carrier.Quotient

open scoped NonUnitalStarSubalgebra.Quotient

/-- **C*-algebra quotient by a closed ideal.** Let `A` be a nonunital complex C*-algebra and let `I ⊆ A`
be a closed two-sided star ideal. The quotient `A/I` is a nonunital complex C*-algebra with the
quotient norm and induced involution and complex algebra operations. -/
@[instance_reducible]
noncomputable def quotientCStarAlgebra (I : ClosedStarIdeal A) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    NonUnitalCStarAlgebra I.Quotient := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : IsClosed (I.carrier : Set A) := I.isClosed
  exact NonUnitalStarSubalgebra.Quotient.nonUnitalCStarAlgebra I.carrier

/-- **Projection onto a closed C*-quotient.** Let `A` be a nonunital complex C*-algebra and let `I ⊆ A`
be a closed two-sided star ideal. The projection `a ↦ [a]` is a nonunital complex star-algebra
homomorphism from `A` onto `A/I`. -/
noncomputable def quotientMap (I : ClosedStarIdeal A) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    A →⋆ₙₐ[ℂ] I.Quotient := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.mk I.carrier

@[simp]
theorem quotientMap_apply (I : ClosedStarIdeal A) (x : A) :
    I.quotientMap x = (Submodule.Quotient.mk x : I.Quotient) :=
  rfl

theorem quotientMap_eq_zero_iff (I : ClosedStarIdeal A) (x : A) :
    I.quotientMap x = 0 ↔ x ∈ I := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.mk_eq_zero I.carrier x

theorem quotientMap_surjective (I : ClosedStarIdeal A) :
    Function.Surjective I.quotientMap := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.mkL_surjective I.carrier

/-! ### Explicit unital quotient structure -/

section UnitalQuotient

variable {U : Type*} [CStarAlgebra U]

/-- **Unital C*-structure on a closed ideal quotient.** Let `U` be a unital complex C*-algebra and `I ⊆
U` a closed two-sided star ideal. The quotient `U/I` is a unital complex C*-algebra with the
quotient norm and unit `[1]`. This also allows `I = U`, giving the zero quotient. -/
@[instance_reducible]
noncomputable def unitalQuotientCStarAlgebra
    (I : ClosedStarIdeal U) : CStarAlgebra I.Quotient := by
  let _ : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  let _ : One I.Quotient := ⟨I.quotientMap 1⟩
  let _ : Pow I.Quotient ℕ := ⟨fun q n ↦ npowRec n q⟩
  let _ : NatCast I.Quotient := ⟨fun n ↦ I.quotientMap (n : U)⟩
  let _ : IntCast I.Quotient := ⟨fun n ↦ I.quotientMap (n : U)⟩
  let ring : Ring I.Quotient := fast_instance%
    Function.Surjective.ring I.quotientMap I.quotientMap_surjective
      (map_zero I.quotientMap) rfl
      (map_add I.quotientMap) (map_mul I.quotientMap)
      (map_neg I.quotientMap) (map_sub I.quotientMap)
      (fun n x ↦ map_nsmul I.quotientMap n x)
      (fun n x ↦ map_zsmul I.quotientMap n x)
      (fun x n ↦ by
        induction n with
        | zero =>
            rw [pow_zero]
            rfl
        | succ n ih =>
            rw [pow_succ]
            change I.quotientMap (x ^ n * x) =
              npowRec n (I.quotientMap x) * I.quotientMap x
            rw [map_mul, ih]
            rfl)
      (fun _ ↦ rfl) fun _ ↦ rfl
  let _ : Ring I.Quotient := ring
  let algebra : Algebra ℂ I.Quotient :=
    Algebra.ofModule smul_mul_assoc mul_smul_comm
  let _ : Algebra ℂ I.Quotient := algebra
  let normedRing : NormedRing I.Quotient :=
    { toRing := ring
      toNorm := inferInstance
      toMetricSpace := inferInstance
      dist_eq := (I.quotientCStarAlgebra).toNonUnitalNormedRing.dist_eq
      norm_mul_le := (I.quotientCStarAlgebra).toNonUnitalNormedRing.norm_mul_le }
  let _ : NormedRing I.Quotient := normedRing
  let normedAlgebra : NormedAlgebra ℂ I.Quotient :=
    { toAlgebra := algebra
      norm_smul_le := norm_smul_le }
  let _ : NormedAlgebra ℂ I.Quotient := normedAlgebra
  exact
    { toNormedRing := normedRing
      toStarRing := (I.quotientCStarAlgebra).toStarRing
      toCompleteSpace := (I.quotientCStarAlgebra).toCompleteSpace
      toCStarRing := (I.quotientCStarAlgebra).toCStarRing
      toNormedAlgebra := normedAlgebra
      toStarModule := (I.quotientCStarAlgebra).toStarModule }

/-- **Unital star quotient projection.** Let `U` be a unital complex C*-algebra and `I ⊆ U` a closed
two-sided star ideal. The projection `u ↦ [u]` is a unital complex star-algebra homomorphism `U →
U/I`. -/
noncomputable def unitalQuotientMap
    (I : ClosedStarIdeal U) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    U →⋆ₐ[ℂ] I.Quotient := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  exact
    { toFun := I.quotientMap
      map_one' := rfl
      map_mul' := map_mul I.quotientMap
      map_zero' := map_zero I.quotientMap
      map_add' := map_add I.quotientMap
      commutes' := fun c ↦ by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          map_smul]
        rfl
      map_star' := map_star I.quotientMap }

@[simp]
theorem unitalQuotientMap_apply
    (I : ClosedStarIdeal U) (a : U) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    I.unitalQuotientMap a = I.quotientMap a := by
  rfl

/-- **Underlying nonunital quotient homomorphism.** Let `U` be a unital complex C*-algebra and `I ⊆ U` a
closed two-sided star ideal. Forgetting unit preservation from the unital quotient homomorphism
gives the nonunital quotient homomorphism with the same values. -/
theorem unitalQuotientMap_toNonUnitalStarAlgHom
    (I : ClosedStarIdeal U) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    I.unitalQuotientMap.toNonUnitalStarAlgHom = I.quotientMap := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  apply NonUnitalStarAlgHom.ext
  intro a
  rfl

theorem unitalQuotientMap_surjective
    (I : ClosedStarIdeal U) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    Function.Surjective I.unitalQuotientMap := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  exact I.quotientMap_surjective

theorem unitalQuotientMap_eq_zero_iff
    (I : ClosedStarIdeal U) (a : U) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    I.unitalQuotientMap a = 0 ↔ a ∈ I := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  exact I.quotientMap_eq_zero_iff a

theorem unitalQuotientMap_one
    (I : ClosedStarIdeal U) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    I.unitalQuotientMap 1 = 1 := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  exact map_one I.unitalQuotientMap

/-- **Unit class in a C*-quotient.** Let `U` be a unital complex C*-algebra and `I ⊆ U` a closed
two-sided star ideal. The class of the unit of `U` is the unit of `U/I`. -/
@[simp]
theorem quotient_mk_one (I : ClosedStarIdeal U) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    (Submodule.Quotient.mk (1 : U) : I.Quotient) = 1 := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  simpa only [unitalQuotientMap_apply, quotientMap_apply] using
    unitalQuotientMap_one I

end UnitalQuotient

/-- **Quotient map from an ideal inclusion.** Let `A` be a nonunital complex C*-algebra and `I ⊆ J`
closed two-sided star ideals of `A`. The inclusion defines a nonunital complex star homomorphism
`A/I → A/J` sending `[a]ᵢ` to `[a]ⱼ`. -/
noncomputable def quotientMapOfLE (I J : ClosedStarIdeal A) (h : I ≤ J) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    let _ : J.carrier.IsTwoSided := J.isTwoSided
    I.Quotient →⋆ₙₐ[ℂ] J.Quotient := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.map I.carrier J.carrier
    (NonUnitalStarAlgHom.id ℂ A) fun x hx ↦ h hx

/-- **Evaluation of an inclusion-induced quotient map.** Let `A` be a nonunital complex C*-algebra and
`I ⊆ J` closed two-sided star ideals of `A`. For every `a ∈ A`, the induced map sends the class of
`a` modulo `I` to its class modulo `J`. -/
theorem quotientMapOfLE_quotientMap
    (I J : ClosedStarIdeal A) (h : I ≤ J) (x : A) :
    quotientMapOfLE I J h (I.quotientMap x) = J.quotientMap x := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  rfl

/-- **Classes under an inclusion-induced quotient map.** Let `A` be a nonunital complex C*-algebra and
`I ⊆ J` closed two-sided star ideals of `A`. For every `a ∈ A`, the induced quotient map evaluates
at `[a]ᵢ` to `[a]ⱼ`, using the underlying complex-vector quotient projections. -/
@[simp]
theorem quotientMapOfLE_mkQ
    (I J : ClosedStarIdeal A) (h : I ≤ J) (x : A) :
    quotientMapOfLE I J h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : J.Quotient) := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  simpa only [quotientMap_apply] using quotientMapOfLE_quotientMap I J h x

/-- **Quotient map of a reflexive ideal inclusion.** For a nonunital complex C*-algebra `A` and a closed
two-sided star ideal `I ⊆ A`, the quotient homomorphism induced by `I ⊆ I` is the identity of `A/I`. -/
@[simp]
theorem quotientMapOfLE_refl (I : ClosedStarIdeal A) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    quotientMapOfLE I I le_rfl = NonUnitalStarAlgHom.id ℂ I.Quotient := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  apply NonUnitalStarAlgHom.ext
  intro q
  obtain ⟨x, rfl⟩ := I.quotientMap_surjective q
  rw [quotientMapOfLE_quotientMap]
  rfl

/-- **Composition of inclusion-induced quotient maps.** For a nonunital complex C*-algebra `A` and
closed two-sided star ideals `I ⊆ J ⊆ K`, the composite `A/I → A/J → A/K` equals the quotient
homomorphism induced by `I ⊆ K`. -/
theorem quotientMapOfLE_trans
    (I J K : ClosedStarIdeal A) (hIJ : I ≤ J) (hJK : J ≤ K) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    let _ : J.carrier.IsTwoSided := J.isTwoSided
    let _ : K.carrier.IsTwoSided := K.isTwoSided
    quotientMapOfLE I K (hIJ.trans hJK) =
      (quotientMapOfLE J K hJK).comp (quotientMapOfLE I J hIJ) := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  let _ : K.carrier.IsTwoSided := K.isTwoSided
  apply NonUnitalStarAlgHom.ext
  intro q
  obtain ⟨x, rfl⟩ := I.quotientMap_surjective q
  simp only [NonUnitalStarAlgHom.comp_apply, quotientMapOfLE_quotientMap]

end ClosedStarIdeal

namespace NonUnitalStarAlgHom

open scoped CStarAlgebra NonUnitalStarSubalgebra.Quotient

universe u v

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Homomorphism from the kernel quotient to the range.** Let `A,B` be nonunital complex C*-algebras
and `ρ : A → B` a nonunital complex star-algebra homomorphism. It induces the nonunital star
homomorphism `A/ker(ρ) → range(ρ)` given by `[a] ↦ ρ(a)`. -/
noncomputable def quotientKerRangeHom (rho : A →⋆ₙₐ[ℂ] B) :
    let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
      (ClosedStarIdeal.ker rho).isTwoSided
    (ClosedStarIdeal.ker rho).Quotient →⋆ₙₐ[ℂ]
      NonUnitalStarAlgHom.range rho := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.lift
    (ClosedStarIdeal.ker rho).carrier (NonUnitalStarAlgHom.rangeRestrict rho) fun x hx ↦ by
      apply Subtype.ext
      exact (ClosedStarIdeal.mem_ker rho x).1 hx

/-- **Evaluation of the kernel-quotient range map.** Let `A,B` be nonunital complex C*-algebras and `ρ :
A → B` a nonunital complex star-algebra homomorphism. For every `a ∈ A`, the induced map from
`A/ker(ρ)` to the range sends `[a]` to `ρ(a)`, regarded as an element of the range. -/
theorem quotientKerRangeHom_quotientMap (rho : A →⋆ₙₐ[ℂ] B) (a : A) :
    quotientKerRangeHom rho ((ClosedStarIdeal.ker rho).quotientMap a) =
      NonUnitalStarAlgHom.rangeRestrict rho a := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  rfl

/-- **Kernel quotient classes under the range map.** Let `A,B` be nonunital complex C*-algebras and `ρ :
A → B` a nonunital complex star-algebra homomorphism. For every `a ∈ A`, the vector-space quotient
class `[a]` maps to `ρ(a)` in the range. -/
@[simp]
theorem quotientKerRangeHom_mkQ (rho : A →⋆ₙₐ[ℂ] B) (a : A) :
    quotientKerRangeHom rho (Submodule.Quotient.mk a) =
      NonUnitalStarAlgHom.rangeRestrict rho a := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  simpa only [ClosedStarIdeal.quotientMap_apply] using
    quotientKerRangeHom_quotientMap rho a

/-- **First isomorphism theorem for nonunital C*-algebras.** Let `A,B` be nonunital complex C*-algebras
and `ρ : A → B` a nonunital complex star-algebra homomorphism. There is a complex star-algebra
equivalence `A/ker(ρ) ≃ range(ρ)`, with the quotient norm on the left and inherited norm on the
right. -/
noncomputable def quotientKerEquivRange (rho : A →⋆ₙₐ[ℂ] B) :
    let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
      (ClosedStarIdeal.ker rho).isTwoSided
    (ClosedStarIdeal.ker rho).Quotient ≃⋆ₐ[ℂ]
      NonUnitalStarAlgHom.range rho := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  refine StarAlgEquiv.ofBijective (quotientKerRangeHom rho) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := (ClosedStarIdeal.ker rho).quotientMap_surjective x
    obtain ⟨b, rfl⟩ := (ClosedStarIdeal.ker rho).quotientMap_surjective y
    apply (Submodule.Quotient.eq
      (NonUnitalStarSubalgebra.quotientSubmodule
        (ClosedStarIdeal.ker rho).carrier)).2
    change a - b ∈ ClosedStarIdeal.ker rho
    rw [ClosedStarIdeal.mem_ker, map_sub, sub_eq_zero]
    simpa only [quotientKerRangeHom_quotientMap,
      NonUnitalStarAlgHom.coe_codRestrict] using congrArg Subtype.val hxy
  · intro y
    obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range rho).1 y.property
    refine ⟨(ClosedStarIdeal.ker rho).quotientMap a, ?_⟩
    apply Subtype.ext
    simpa only [quotientKerRangeHom_quotientMap,
      NonUnitalStarAlgHom.coe_codRestrict] using ha

/-- **Evaluation of the first-isomorphism equivalence.** Let `A,B` be nonunital complex C*-algebras and
`ρ : A → B` a nonunital complex star-algebra homomorphism. The canonical equivalence `A/ker(ρ) ≃
range(ρ)` sends `[a]` to `ρ(a)` for every `a ∈ A`. -/
theorem quotientKerEquivRange_quotientMap (rho : A →⋆ₙₐ[ℂ] B) (a : A) :
    quotientKerEquivRange rho
        ((ClosedStarIdeal.ker rho).quotientMap a) =
      NonUnitalStarAlgHom.rangeRestrict rho a := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  change quotientKerRangeHom rho
      ((ClosedStarIdeal.ker rho).quotientMap a) =
    NonUnitalStarAlgHom.rangeRestrict rho a
  exact quotientKerRangeHom_quotientMap rho a

/-- **Classes in the first-isomorphism equivalence.** Let `A,B` be nonunital complex C*-algebras and `ρ
: A → B` a nonunital complex star-algebra homomorphism. The canonical equivalence from the
vector-space quotient `A/ker(ρ)` to the range evaluates at `[a]` to `ρ(a)`. -/
@[simp]
theorem quotientKerEquivRange_mkQ (rho : A →⋆ₙₐ[ℂ] B) (a : A) :
    quotientKerEquivRange rho (Submodule.Quotient.mk a) =
      NonUnitalStarAlgHom.rangeRestrict rho a := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  simpa only [ClosedStarIdeal.quotientMap_apply] using
    quotientKerEquivRange_quotientMap rho a

/-- **First isomorphism theorem for a surjective C*-homomorphism.** Let `A,B` be nonunital complex
C*-algebras and `ρ : A → B` a nonunital complex star-algebra homomorphism. If `ρ` is surjective, the
kernel quotient is complex star-algebra equivalent to `B`. -/
noncomputable def quotientKerEquivOfSurjective
    (rho : A →⋆ₙₐ[ℂ] B) (hrho : Function.Surjective rho) :
    let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
      (ClosedStarIdeal.ker rho).isTwoSided
    (ClosedStarIdeal.ker rho).Quotient ≃⋆ₐ[ℂ] B := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  exact (quotientKerEquivRange rho).trans <|
    StarAlgEquiv.ofBijective
      (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range rho)) ⟨
        fun _ _ h ↦ Subtype.ext h,
        fun b ↦ by
          obtain ⟨a, rfl⟩ := hrho b
          exact ⟨⟨rho a, NonUnitalStarAlgHom.mem_range_self rho a⟩, rfl⟩⟩

/-- **Evaluation of the surjective first isomorphism.** Let `A,B` be nonunital complex C*-algebras and
`ρ : A → B` a nonunital complex star-algebra homomorphism. If `ρ` is surjective, its canonical
equivalence `A/ker(ρ) ≃ B` sends `[a]` to `ρ(a)` for every `a ∈ A`. -/
theorem quotientKerEquivOfSurjective_quotientMap
    (rho : A →⋆ₙₐ[ℂ] B) (hrho : Function.Surjective rho) (a : A) :
    quotientKerEquivOfSurjective rho hrho
        ((ClosedStarIdeal.ker rho).quotientMap a) = rho a := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  simp only [quotientKerEquivOfSurjective, StarAlgEquiv.trans_apply]
  change (((quotientKerEquivRange rho)
      ((ClosedStarIdeal.ker rho).quotientMap a) :
        NonUnitalStarAlgHom.range rho) : B) = rho a
  simpa only [NonUnitalStarAlgHom.coe_codRestrict] using
    congrArg Subtype.val (quotientKerEquivRange_quotientMap rho a)

/-- **Quotient classes under the surjective first isomorphism.** Let `A,B` be nonunital complex
C*-algebras and `ρ : A → B` a nonunital complex star-algebra homomorphism. If `ρ` is surjective, the
canonical equivalence from the vector-space quotient `A/ker(ρ)` to `B` evaluates at `[a]` to `ρ(a)`. -/
@[simp]
theorem quotientKerEquivOfSurjective_mkQ
    (rho : A →⋆ₙₐ[ℂ] B) (hrho : Function.Surjective rho) (a : A) :
    quotientKerEquivOfSurjective rho hrho (Submodule.Quotient.mk a) = rho a := by
  let _ : (ClosedStarIdeal.ker rho).carrier.IsTwoSided :=
    (ClosedStarIdeal.ker rho).isTwoSided
  simpa only [ClosedStarIdeal.quotientMap_apply] using
    quotientKerEquivOfSurjective_quotientMap rho hrho a

end NonUnitalStarAlgHom
