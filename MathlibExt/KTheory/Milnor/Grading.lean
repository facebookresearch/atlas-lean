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

public import MathlibExt.KTheory.Milnor.Basic
public import MathlibExt.LinearAlgebra.TensorAlgebra.Grading
public import MathlibExt.RingTheory.GradedAlgebra.Homogeneous.TwoSidedIdeal

/-!
# Grading for Milnor K-theory

The tensor ring `TensorRing F = TensorAlgebra ℤ (Additive Fˣ)` is naturally
`ℕ`-graded. Its degree family is the reusable
`TensorAlgebra.degree ℤ (Additive Fˣ)` from
`MathlibExt.LinearAlgebra.TensorAlgebra.Grading`, i.e. `(range ι) ^ n`,
supplied by the canonical `TensorAlgebra.gradedAlgebra` instance. The
homogeneous projection `TensorRing.proj` is a transparent abbreviation for the
general `GradedAlgebra.proj`, so lemmas such as `GradedAlgebra.proj_mem`,
`proj_eq_self`, `proj_eq_zero_of_ne`, and `proj_mul_eq_sum_antidiagonal`
apply definitionally.

Degree membership for generators and their products is now derived from that
general API: `ι` lies in degree one via `TensorAlgebra.degree_one`, and
products of degree-one elements lie in degree two via graded multiplication or
`TensorAlgebra.tprod_mem_degree`. This eliminates any local restatement of the
tensor-algebra grading construction.

Steinberg generators `ι a * ι (1 - a)` lie in degree two and are homogeneous.
The two-sided ideal they generate, `steinbergIdeal F`, is therefore
homogeneous: its underlying `Ideal` is closed under homogeneous projections.
This is proved directly with `TwoSidedIdeal.span_induction` and the generic
projection lemmas, without importing `TensorRingProjFormula`,
`SteinbergIdealProj`, `steinbergDegreeSpan`, `ClassicalDegree`, or later
modules.

The Milnor K-ring `MilnorKRing F` is the quotient by this ideal. Its linear
quotient map `mkLinear` is implemented as `(steinbergIdeal F).ringCon.mkₐ ℤ`,
so `MilnorKRing.degree F n = (TensorRing.degree F n).map mkLinear` is
definitionally `TwoSidedIdeal.quotientGrade (steinbergIdeal F)
(TensorRing.degree F)`. The homogeneous quotient therefore inherits a genuine
`GradedAlgebra` instance via `TwoSidedIdeal.gradedAlgebraQuotientGrade`.

## Main definitions

* `MilnorK.TensorRing.degree` – degree-`n` submodule of the tensor ring,
  definitionally `TensorAlgebra.degree ℤ (Additive Fˣ) n` from the general
  tensor-algebra grading API.
* `MilnorK.TensorRing.proj` – homogeneous projection onto degree `n`, defined
  as `GradedAlgebra.proj (TensorRing.degree F) n`.
* `MilnorK.MilnorKRing.mkLinear` – linear projection `TensorRing F →ₗ[ℤ]
  MilnorKRing F` from the generic `mkₐ`.
* `MilnorK.MilnorKRing.degree` – degree-`n` subgroup of the Milnor K-ring,
  definitionally the generic quotient grading.
* `MilnorK.MilnorKRing.degreeCastEquiv` – transport of degree subtypes along
  equalities of indices, via `LinearEquiv.cast`.
* `MilnorK.MilnorKRing.degreeLinear` – degreewise quotient component
  `TensorRing.degree F n →ₗ[ℤ] MilnorKRing.degree F n`, specialization of
  `TwoSidedIdeal.quotientGradeComponent`.

## Main results

* `steinbergSet_subset_degree_two` – Steinberg generators sit in degree two.
* `steinbergSet_homogeneous` – each Steinberg generator is a homogeneous
  element for the tensor grading.
* `steinbergIdeal_asIdeal_isHomogeneous` – the Steinberg ideal is homogeneous,
  so the quotient inherits the grading.
* `symbol_mem_degree_one` and `symbol_mul_mem_degree_two` – Milnor symbols and
  their products lie in the expected degree pieces of `MilnorKRing F`, via the
  general degree-one membership.
* `MilnorKRing.degreeLinear_apply_coe`, `degreeLinear_surjective`,
  `degreeLinear_ker` – Milnor specialization of the generic homogeneous
  two-sided quotient component API: computation, surjectivity, and kernel as
  comap of the restricted Steinberg ideal.
-/

@[expose] public section

open TensorAlgebra DirectSum
open scoped TensorAlgebra

namespace MilnorK

variable (F : Type*) [Field F]

/-- Degree `n` component of the tensor ring, definitionally the general
`TensorAlgebra.degree ℤ (Additive Fˣ) n` from
`MathlibExt.LinearAlgebra.TensorAlgebra.Grading`. -/
abbrev TensorRing.degree (n : ℕ) : Submodule ℤ (TensorRing F) :=
  TensorAlgebra.degree ℤ (Additive Fˣ) n

/-- Homogeneous projection of the tensor ring onto degree `n`. Transparent
abbreviation for the general graded projection. -/
abbrev TensorRing.proj (n : ℕ) : TensorRing F →ₗ[ℤ] TensorRing F :=
  GradedAlgebra.proj (TensorRing.degree F) n

/-- Every element of `ι` lands in degree one, via the general
`TensorAlgebra.degree_one`. -/
lemma ι_mem_degree_one (u : Fˣ) :
    TensorAlgebra.ι ℤ (Additive.ofMul u) ∈ TensorRing.degree F 1 := by
  rw [TensorRing.degree, TensorAlgebra.degree_one]
  exact LinearMap.mem_range_self _ _

/-- Product of two degree-one `ι` elements lies in degree two, via graded
multiplication of degree-one members. -/
lemma ι_mul_ι_mem_degree_two (a b : Fˣ) :
    TensorAlgebra.ι ℤ (Additive.ofMul a) * TensorAlgebra.ι ℤ (Additive.ofMul b)
      ∈ TensorRing.degree F 2 := by
  have h1 : TensorAlgebra.ι ℤ (Additive.ofMul a) ∈ TensorRing.degree F 1 :=
    ι_mem_degree_one F a
  have h2 : TensorAlgebra.ι ℤ (Additive.ofMul b) ∈ TensorRing.degree F 1 :=
    ι_mem_degree_one F b
  exact SetLike.GradedMul.mul_mem h1 h2

/-- Steinberg generators are homogeneous of degree two in the tensor ring. -/
theorem steinbergSet_subset_degree_two :
    steinbergSet F ⊆ TensorRing.degree F 2 := by
  intro x hx
  rcases hx with ⟨a, ha0, ha1, rfl⟩
  exact ι_mul_ι_mem_degree_two F (Units.mk0 a ha0) (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm))

/-- Every Steinberg generator is a homogeneous element for the tensor grading. -/
theorem steinbergSet_homogeneous (x : TensorRing F) (hx : x ∈ steinbergSet F) :
    SetLike.IsHomogeneousElem (TensorRing.degree F) x := by
  use 2
  exact steinbergSet_subset_degree_two F hx

/-- The Steinberg ideal is homogeneous for `TensorRing.degree`. Proved directly
with `TwoSidedIdeal.span_induction` and generic projection lemmas. -/
theorem steinbergIdeal_asIdeal_isHomogeneous :
    (steinbergIdeal F).asIdeal.IsHomogeneous (TensorRing.degree F) := by
  have key : ∀ x ∈ steinbergIdeal F, ∀ n : ℕ,
      GradedAlgebra.proj (TensorRing.degree F) n x ∈ steinbergIdeal F := by
    intro x hx
    refine TwoSidedIdeal.span_induction ?_ ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy n
      have hy2 : y ∈ TensorRing.degree F 2 := steinbergSet_subset_degree_two F hy
      by_cases hn : n = 2
      · subst hn
        rw [GradedAlgebra.proj_eq_self hy2]
        exact TwoSidedIdeal.subset_span hy
      · have hne : (2 : ℕ) ≠ n := fun h => hn h.symm
        rw [GradedAlgebra.proj_eq_zero_of_ne hy2 hne]
        exact (steinbergIdeal F).zero_mem
    · intro n
      simp only [map_zero]
      exact (steinbergIdeal F).zero_mem
    · intro x y _ _ hx hy n
      rw [map_add]
      exact (steinbergIdeal F).add_mem (hx n) (hy n)
    · intro x _ hx n
      rw [map_neg]
      exact (steinbergIdeal F).neg_mem (hx n)
    · intro a x _ hx n
      rw [GradedAlgebra.proj_mul_eq_sum_antidiagonal (𝒜 := TensorRing.degree F) a x n]
      have hmem : ∀ ij ∈ Finset.antidiagonal n,
          GradedAlgebra.proj (TensorRing.degree F) ij.1 a *
          GradedAlgebra.proj (TensorRing.degree F) ij.2 x ∈ steinbergIdeal F := by
        intro ij _
        exact (steinbergIdeal F).mul_mem_left _ _ (hx ij.2)
      have hsum : (∑ ij ∈ Finset.antidiagonal n,
          GradedAlgebra.proj (TensorRing.degree F) ij.1 a *
          GradedAlgebra.proj (TensorRing.degree F) ij.2 x) ∈
          (steinbergIdeal F).asIdeal := by
        apply Submodule.sum_mem
        intro ij hij
        exact TwoSidedIdeal.mem_asIdeal.mpr (hmem ij hij)
      exact TwoSidedIdeal.mem_asIdeal.mp hsum
    · intro b x _ hx n
      rw [GradedAlgebra.proj_mul_eq_sum_antidiagonal (𝒜 := TensorRing.degree F) x b n]
      have hmem : ∀ ij ∈ Finset.antidiagonal n,
          GradedAlgebra.proj (TensorRing.degree F) ij.1 x *
          GradedAlgebra.proj (TensorRing.degree F) ij.2 b ∈ steinbergIdeal F := by
        intro ij _
        exact (steinbergIdeal F).mul_mem_right _ _ (hx ij.1)
      have hsum : (∑ ij ∈ Finset.antidiagonal n,
          GradedAlgebra.proj (TensorRing.degree F) ij.1 x *
          GradedAlgebra.proj (TensorRing.degree F) ij.2 b) ∈
          (steinbergIdeal F).asIdeal := by
        apply Submodule.sum_mem
        intro ij hij
        exact TwoSidedIdeal.mem_asIdeal.mpr (hmem ij hij)
      exact TwoSidedIdeal.mem_asIdeal.mp hsum
  rw [Ideal.isHomogeneous_iff_forall_subset]
  intro n x hx
  have hx_as : x ∈ (steinbergIdeal F).asIdeal := hx
  have hx' : x ∈ steinbergIdeal F := TwoSidedIdeal.mem_asIdeal.mp hx_as
  have h := key x hx' n
  have heq : GradedRing.proj (TensorRing.degree F) n x =
      GradedAlgebra.proj (TensorRing.degree F) n x := by
    simp [GradedRing.proj_apply, GradedAlgebra.proj_apply]
  have hring : GradedRing.proj (TensorRing.degree F) n x ∈ steinbergIdeal F := by
    rw [heq]
    exact h
  have hring_as : GradedRing.proj (TensorRing.degree F) n x ∈
      (steinbergIdeal F).asIdeal :=
    TwoSidedIdeal.mem_asIdeal.mpr hring
  exact Set.mem_preimage.mpr hring_as

namespace MilnorKRing

/-- Linear map version of the quotient projection, implemented from `mkₐ`. -/
def mkLinear : TensorRing F →ₗ[ℤ] MilnorKRing F :=
  (steinbergIdeal F).ringCon.mkₐ ℤ |>.toLinearMap

/-- `mkLinear` agrees with the ring quotient map `mk`. -/
@[simp]
lemma mkLinear_apply (x : TensorRing F) : mkLinear F x = MilnorKRing.mk F x := rfl

/-- Degree `n` subgroup of the Milnor K-ring, definitionally the generic quotient grade. -/
def degree (n : ℕ) : Submodule ℤ (MilnorKRing F) :=
  Submodule.map (mkLinear F) (TensorRing.degree F n)

/-- The Milnor K-ring grading is the generic two-sided quotient grading. -/
noncomputable instance instGradedAlgebra :
    GradedAlgebra (degree F) :=
  TwoSidedIdeal.gradedAlgebraQuotientGrade (steinbergIdeal F)
    (steinbergIdeal_asIdeal_isHomogeneous F)

/-- Linear equivalence transporting degree subtypes along an index equality. -/
def degreeCastEquiv {m n : ℕ} (h : m = n) :
    ↥(degree F m) ≃ₗ[ℤ] ↥(degree F n) :=
  LinearEquiv.cast (R := ℤ) (M := fun k => ↥(degree F k)) h

/-- The degree cast over `rfl` is the identity equivalence. -/
@[simp] theorem degreeCastEquiv_rfl {m : ℕ} :
    degreeCastEquiv F (m := m) (n := m) rfl = LinearEquiv.refl ℤ _ := by
  ext x; cases rfl; rfl

/-- The symmetric of a degree cast is the cast over the symmetric equality. -/
@[simp] theorem degreeCastEquiv_symm {m n : ℕ} (h : m = n) :
    (degreeCastEquiv F h).symm = degreeCastEquiv F h.symm := by
  cases h; ext x; rfl

/-- Composition of degree casts is the cast over the transitive equality. -/
@[simp] theorem degreeCastEquiv_trans {l m n : ℕ} (h₁ : l = m) (h₂ : m = n) :
    (degreeCastEquiv F h₁).trans (degreeCastEquiv F h₂) =
      degreeCastEquiv F (h₁.trans h₂) := by
  cases h₁; cases h₂; ext x; rfl

/-- The degree cast equivalence acts as a type-level cast on subtypes. -/
theorem degreeCastEquiv_apply {m n : ℕ} (h : m = n) (x : ↥(degree F m)) :
    degreeCastEquiv F h x = cast (congrArg (fun k => ↥(degree F k)) h) x := by
  cases h; rfl

/-- Casting a degree element preserves its underlying ring value. -/
theorem degree_cast_val {m n : ℕ} (h : m = n) (x : degree F m) :
    (cast (congrArg (fun k => ↥(degree F k)) h) x).1 = x.1 := by
  cases h; rfl

/-- Degree cast preserves the underlying ring value. -/
theorem degreeCastEquiv_val {m n : ℕ} (h : m = n) (x : degree F m) :
    (degreeCastEquiv F h x).1 = x.1 := by
  rw [degreeCastEquiv_apply]; exact degree_cast_val F h x

/-- Linear projection from the tensor degree `n` onto the Milnor degree `n`,
Milnor specialization of `TwoSidedIdeal.quotientGradeComponent`. -/
def degreeLinear (n : ℕ) : TensorRing.degree F n →ₗ[ℤ] degree F n :=
  (steinbergIdeal F).quotientGradeComponent (Agrade := TensorRing.degree F) n

/-- Computation for `degreeLinear`: underlying quotient element is `mkLinear`. -/
@[simp]
theorem degreeLinear_apply_coe (n : ℕ) (x : TensorRing.degree F n) :
    (degreeLinear F n x : MilnorKRing F) = mkLinear F (x : TensorRing F) :=
  rfl

/-- `degreeLinear` is surjective onto `MilnorKRing.degree F n`. -/
theorem degreeLinear_surjective (n : ℕ) :
    Function.Surjective (degreeLinear F n) :=
  TwoSidedIdeal.quotientGradeComponent_surjective (steinbergIdeal F)
    (Agrade := TensorRing.degree F) n

/-- Kernel of `degreeLinear` is the comap of the restricted Steinberg ideal. -/
theorem degreeLinear_ker (n : ℕ) :
    LinearMap.ker (degreeLinear F n) =
      Submodule.comap (TensorRing.degree F n).subtype
        ((steinbergIdeal F).asIdeal.restrictScalars ℤ) :=
  TwoSidedIdeal.quotientGradeComponent_ker (steinbergIdeal F)
    (Agrade := TensorRing.degree F) n

/-- The symbol of a unit lies in degree one of the Milnor K-ring. -/
lemma symbol_mem_degree_one (u : Fˣ) : symbol F u ∈ degree F 1 := by
  unfold symbol degree
  rw [← mkLinear_apply]
  exact Submodule.mem_map_of_mem (ι_mem_degree_one F u)

/-- The product of two symbols lies in degree two. -/
lemma symbol_mul_mem_degree_two (a b : Fˣ) :
    symbol F a * symbol F b ∈ degree F 2 := by
  unfold symbol degree
  rw [← RingHom.map_mul, ← mkLinear_apply]
  exact Submodule.mem_map_of_mem (ι_mul_ι_mem_degree_two F a b)

end MilnorKRing

end MilnorK
