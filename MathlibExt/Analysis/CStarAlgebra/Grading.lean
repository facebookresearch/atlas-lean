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

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.Additive
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.FixedPoint
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Gradings of C-star algebras

A grading is kept as an explicit point-norm action of `ZMod 2`; no ambient
action or grading instance is installed.  The degree-zero component reuses the
fixed-point subalgebra of the action, while the degree-one component is the
negative eigenspace of the generating automorphism.
-/

@[expose] public section

noncomputable section

open Set
open scoped CStarAlgebra

universe uA uB uC

/-- **Grading of a nonunital C*-algebra.** For a nonunital complex C*-algebra `A`, a grading is a
point-norm continuous action of `ℤ/2ℤ` by complex star-algebra automorphisms. Its degree-one
automorphism is involutive, with even and odd parts given by its positive and negative eigenspaces. -/
abbrev CStarGrading
    (A : Type uA) [NonUnitalCStarAlgebra A] :=
  PointNormCStarAddAction (ZMod 2) A

namespace CStarGrading

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- **Homomorphism of graded C*-algebras.** For nonunital complex C*-algebras `A,B` with point-norm
continuous `ℤ/2ℤ` gradings `γ_A,γ_B`, a graded homomorphism is a nonunital complex star homomorphism
`f : A → B` satisfying `f(γ_A(s)a) = γ_B(s)(f(a))` for every degree `s` and `a ∈ A`. -/
abbrev Hom (γA : CStarGrading A) (γB : CStarGrading B) :=
  PointNormCStarAddAction.Hom γA γB

namespace Hom

variable {γA : CStarGrading A} {γB : CStarGrading B}
  {γC : CStarGrading C}

@[simp]
theorem equivariant (φ : Hom γA γB) (n : ZMod 2) (a : A) :
    φ (PointNormCStarAddAction.aut γA n a) =
      PointNormCStarAddAction.aut γB n (φ a) :=
  PointNormCStarAddAction.Hom.equivariant φ n a

/-- **Identity graded homomorphism.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The identity nonunital complex star homomorphism of `A` is
equivariant for `γ`. -/
def id (γ : CStarGrading A) : Hom γ γ :=
  PointNormCStarAddAction.Hom.id γ

@[simp]
theorem id_apply (γ : CStarGrading A) (a : A) : id γ a = a :=
  rfl

/-- **Composition of graded homomorphisms.** For three graded nonunital complex C*-algebras `A,B,C`,
equivariant nonunital star homomorphisms `φ : A → B` and `ψ : B → C` have the equivariant composite
`ψ ∘ φ : A → C`. -/
def comp (ψ : Hom γB γC) (φ : Hom γA γB) : Hom γA γC :=
  PointNormCStarAddAction.Hom.comp ψ φ

@[simp]
theorem comp_apply (ψ : Hom γB γC) (φ : Hom γA γB) (a : A) :
    comp ψ φ a = ψ (φ a) :=
  rfl

@[simp]
theorem id_comp (φ : Hom γA γB) : comp (id γB) φ = φ :=
  PointNormCStarAddAction.Hom.id_comp φ

@[simp]
theorem comp_id (φ : Hom γA γB) : comp φ (id γA) = φ :=
  PointNormCStarAddAction.Hom.comp_id φ

theorem comp_assoc {D : Type*} [NonUnitalCStarAlgebra D]
    {γD : CStarGrading D}
    (χ : Hom γC γD) (ψ : Hom γB γC) (φ : Hom γA γB) :
    comp (comp χ ψ) φ = comp χ (comp ψ φ) :=
  PointNormCStarAddAction.Hom.comp_assoc χ ψ φ

end Hom

private theorem zmod_two_eq_zero_or_one (n : ZMod 2) : n = 0 ∨ n = 1 := by
  fin_cases n
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

/-- **Degree-one grading automorphism.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The generator is the complex star-algebra automorphism `σ = γ(1)`. -/
def generatorAut (γ : CStarGrading A) : A ≃⋆ₐ[ℂ] A :=
  PointNormCStarAddAction.aut γ 1

@[simp]
theorem generatorAut_apply (γ : CStarGrading A) (a : A) :
    γ.generatorAut a =
      γ (Multiplicative.ofAdd (1 : ZMod 2)) a :=
  rfl

/-- **Bounded linear grading generator.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The grading generator `σ` is a continuous complex-linear map `A →
A`. -/
def generatorCLM (γ : CStarGrading A) : A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := γ.generatorAut
      map_add' := map_add γ.generatorAut
      map_smul' := map_smul γ.generatorAut }
    1 fun a ↦ by
      change ‖γ.generatorAut a‖ ≤ 1 * ‖a‖
      rw [StarAlgEquiv.norm_map]
      exact (one_mul ‖a‖).ge

@[simp]
theorem generatorCLM_apply (γ : CStarGrading A) (a : A) :
    γ.generatorCLM a = γ.generatorAut a :=
  rfl

/-- **The grading generator has order two.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. For every `a ∈ A`, `σ(σ(a)) = a`. -/
theorem generator_involutive (γ : CStarGrading A) :
    Function.Involutive γ.generatorAut := by
  intro a
  calc
    γ.generatorAut (γ.generatorAut a) =
        γ (Multiplicative.ofAdd ((1 : ZMod 2) + 1)) a :=
      (PointNormCStarAddAction.apply_add γ 1 1 a).symm
    _ = a := by
      rw [zmod_two_one_add_one]
      exact PointNormCStarAddAction.apply_zero γ a

@[simp]
theorem generator_apply_generator (γ : CStarGrading A) (a : A) :
    γ.generatorAut (γ.generatorAut a) = a :=
  γ.generator_involutive a

/-- **Even star subalgebra.** Let `A` be a nonunital complex C*-algebra and let `γ` be a point-norm
continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for the
automorphism of degree one. The even subalgebra is the fixed-point nonunital star subalgebra `{a ∈ A
: σ(a) = a}`. -/
abbrev evenSubalgebra (γ : CStarGrading A) :
    NonUnitalStarSubalgebra ℂ A :=
  PointNormCStarAction.fixedPointSubalgebra γ

/-- **Even complex-linear part.** Let `A` be a nonunital complex C*-algebra and let `γ` be a point-norm
continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for the
automorphism of degree one. The even part is the complex-linear subspace `{a ∈ A : σ(a) = a}`. -/
abbrev evenPart (γ : CStarGrading A) : Submodule ℂ A :=
  γ.evenSubalgebra.toNonUnitalSubalgebra.toSubmodule

/-- **Odd complex-linear part.** Let `A` be a nonunital complex C*-algebra and let `γ` be a point-norm
continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for the
automorphism of degree one. The odd part is the negative eigenspace `{a ∈ A : σ(a) = -a}`. -/
def oddPart (γ : CStarGrading A) : Submodule ℂ A :=
  LinearMap.ker (γ.generatorCLM.toLinearMap + LinearMap.id)

/-- **Degree-indexed homogeneous parts.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The homogeneous part of degree zero is the even part, and that of
degree one is the odd part. -/
def part (γ : CStarGrading A) : ZMod 2 → Submodule ℂ A :=
  fun n => if n = 0 then γ.evenPart else γ.oddPart

@[simp]
theorem part_zero (γ : CStarGrading A) : γ.part 0 = γ.evenPart := by
  simp [part]

@[simp]
theorem part_one (γ : CStarGrading A) : γ.part 1 = γ.oddPart := by
  simp [part]

/-- **Membership in the even part.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. For every `a ∈ A`, membership in the even part is equivalent to
`σ(a) = a`. -/
theorem mem_evenPart_iff_generator (γ : CStarGrading A) (a : A) :
    a ∈ γ.evenPart ↔ γ.generatorAut a = a := by
  change (∀ g : Multiplicative (ZMod 2), γ g a = a) ↔ _
  constructor
  · intro h
    exact h (Multiplicative.ofAdd 1)
  · intro h n
    rcases zmod_two_eq_zero_or_one n.toAdd with h0 | h1
    · have hn : n = (1 : Multiplicative (ZMod 2)) := by
        exact Multiplicative.toAdd.injective (by simpa using h0)
      subst n
      exact PointNormCStarAction.apply_one γ a
    · have hn : n = Multiplicative.ofAdd (1 : ZMod 2) := by
        exact Multiplicative.toAdd.injective (by simpa using h1)
      subst n
      exact h

/-- **Membership in the odd part.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. For every `a ∈ A`, membership in the odd part is equivalent to `σ(a)
= -a`. -/
theorem mem_oddPart_iff_generator (γ : CStarGrading A) (a : A) :
    a ∈ γ.oddPart ↔ γ.generatorAut a = -a := by
  change γ.generatorCLM a + a = 0 ↔ γ.generatorAut a = -a
  rw [generatorCLM_apply]
  exact add_eq_zero_iff_eq_neg

/-- **Sign of a parity degree.** For `n ∈ ℤ/2ℤ`, the complex sign is `1` when `n=0` and `-1` when `n=1`. -/
def degreeSign (n : ZMod 2) : ℂ :=
  ((((-1 : ℤˣ) ^ n : ℤˣ) : ℤ) : ℂ)

@[simp]
theorem degreeSign_zero : degreeSign 0 = 1 := by
  simp [degreeSign]

@[simp]
theorem degreeSign_one : degreeSign 1 = -1 := by
  norm_num [degreeSign]

theorem degreeSign_add (m n : ZMod 2) :
    degreeSign (m + n) = degreeSign m * degreeSign n := by
  rcases zmod_two_eq_zero_or_one m with hm | hm <;>
    rcases zmod_two_eq_zero_or_one n with hn | hn <;>
    rw [hm, hn]
  all_goals simp only [zero_add, add_zero, zmod_two_one_add_one,
    degreeSign_zero, degreeSign_one]
  all_goals norm_num

theorem degreeSign_mul (m n : ZMod 2) :
    degreeSign (m * n) =
      if m = 1 ∧ n = 1 then -1 else 1 := by
  rcases zmod_two_eq_zero_or_one m with hm | hm <;>
    rcases zmod_two_eq_zero_or_one n with hn | hn <;>
    rw [hm, hn]
  all_goals simp only [zero_mul, mul_zero, one_mul, degreeSign_zero,
    degreeSign_one]
  all_goals norm_num

@[simp]
theorem degreeSign_sq (n : ZMod 2) : degreeSign n * degreeSign n = 1 := by
  rcases zmod_two_eq_zero_or_one n with hn | hn <;> rw [hn]
  · rw [degreeSign_zero]
    norm_num
  · rw [degreeSign_one]
    norm_num

@[simp]
theorem star_degreeSign (n : ZMod 2) : star (degreeSign n) = degreeSign n := by
  rcases zmod_two_eq_zero_or_one n with hn | hn <;> rw [hn]
  · rw [degreeSign_zero, star_one]
  · rw [degreeSign_one, star_neg, star_one]

/-- **Homogeneous element of a specified degree.** Let `A` be a nonunital complex C*-algebra and let `γ`
be a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ`
for the automorphism of degree one. An element `a ∈ A` is homogeneous of degree `n ∈ ℤ/2ℤ` when it
belongs to the corresponding even or odd subspace. -/
def IsHomogeneousOf (γ : CStarGrading A) (n : ZMod 2) (a : A) : Prop :=
  a ∈ γ.part n

/-- **Degree-tagged homogeneous elements.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. An element of this type is a degree `n ∈ ℤ/2ℤ` together with an
element of the homogeneous part of degree `n`. -/
def Homogeneous (γ : CStarGrading A) :=
  Σ n : ZMod 2, γ.part n

/-- **Coefficient of a tagged homogeneous element.** Let `A` be a nonunital complex C*-algebra and let
`γ` be a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write
`σ` for the automorphism of degree one. For a tagged homogeneous element, this is its underlying
element of `A`, with the degree tag forgotten. -/
def Homogeneous.coe {γ : CStarGrading A} (x : γ.Homogeneous) : A :=
  x.2.1

instance (γ : CStarGrading A) (x : γ.Homogeneous) :
    CoeDep γ.Homogeneous x A :=
  ⟨x.coe⟩

@[simp]
theorem homogeneous_coe_mk (γ : CStarGrading A) (n : ZMod 2)
    (a : γ.part n) :
    Homogeneous.coe (⟨n, a⟩ : γ.Homogeneous) = a :=
  rfl

theorem mem_part_iff_generator (γ : CStarGrading A) (n : ZMod 2) (a : A) :
    a ∈ γ.part n ↔ γ.generatorAut a = degreeSign n • a := by
  rcases zmod_two_eq_zero_or_one n with rfl | rfl
  · simpa [IsHomogeneousOf] using γ.mem_evenPart_iff_generator a
  · rw [part_one, mem_oddPart_iff_generator, degreeSign_one, neg_one_smul]

theorem isHomogeneousOf_iff_generator (γ : CStarGrading A)
    (n : ZMod 2) (a : A) :
    γ.IsHomogeneousOf n a ↔ γ.generatorAut a = degreeSign n • a :=
  γ.mem_part_iff_generator n a

theorem isClosed_evenPart (γ : CStarGrading A) :
    IsClosed (γ.evenPart : Set A) :=
  PointNormCStarAction.isClosed_fixedPointSubalgebra γ

theorem isClosed_oddPart (γ : CStarGrading A) :
    IsClosed (γ.oddPart : Set A) := by
  exact ContinuousLinearMap.isClosed_ker
    (γ.generatorCLM + ContinuousLinearMap.id ℂ A)

theorem isClosed_part (γ : CStarGrading A) (n : ZMod 2) :
    IsClosed (γ.part n : Set A) := by
  rcases zmod_two_eq_zero_or_one n with rfl | rfl
  · exact γ.isClosed_evenPart
  · exact γ.isClosed_oddPart

theorem star_mem_part (γ : CStarGrading A) {n : ZMod 2} {a : A}
    (ha : a ∈ γ.part n) :
    star a ∈ γ.part n := by
  rw [γ.mem_part_iff_generator] at ha ⊢
  rw [map_star, ha, star_smul, star_degreeSign]

theorem mul_mem_part (γ : CStarGrading A) {m n : ZMod 2} {a b : A}
    (ha : a ∈ γ.part m) (hb : b ∈ γ.part n) :
    a * b ∈ γ.part (m + n) := by
  rw [γ.mem_part_iff_generator] at ha hb ⊢
  rw [map_mul, ha, hb, smul_mul_assoc, mul_smul_comm,
    ← mul_smul, ← degreeSign_add]

/-- **Multiplication respects degree.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The product of elements of degrees `m,n` belongs to the homogeneous
part of degree `m+n` in `ℤ/2ℤ`. -/
theorem gradedMul (γ : CStarGrading A) : SetLike.GradedMul γ.part where
  mul_mem := by
    intro i j a b ha hb
    exact γ.mul_mem_part ha hb

/-- **Multiplication action respects degree.** Let `A` be a nonunital complex C*-algebra and let `γ` be
a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. Regarding multiplication as an action of `A` on itself, an element
of degree `m` sends the part of degree `n` into the part of degree `m+n`. -/
theorem gradedSMul (γ : CStarGrading A) : SetLike.GradedSMul γ.part γ.part := by
  constructor
  intro i j a b ha hb
  exact γ.mul_mem_part ha hb

theorem smul_mem_part (γ : CStarGrading A) (n : ZMod 2)
    (z : ℂ) {a : A} (ha : a ∈ γ.part n) :
    z • a ∈ γ.part n :=
  (γ.part n).smul_mem z ha

theorem zero_mem_part (γ : CStarGrading A) (n : ZMod 2) :
    (0 : A) ∈ γ.part n :=
  (γ.part n).zero_mem

theorem degree_eq_of_mem_mem (γ : CStarGrading A)
    {m n : ZMod 2} {a : A}
    (ham : a ∈ γ.part m) (han : a ∈ γ.part n) (ha : a ≠ 0) :
    m = n := by
  rcases zmod_two_eq_zero_or_one m with rfl | rfl
  · rcases zmod_two_eq_zero_or_one n with rfl | rfl
    · rfl
    · rw [part_zero, mem_evenPart_iff_generator] at ham
      rw [part_one, mem_oddPart_iff_generator] at han
      exfalso
      apply ha
      have ha_neg : a = -a := ham.symm.trans han
      have htwo : (2 : ℂ) • a = 0 := by
        simpa only [two_smul] using (add_eq_zero_iff_eq_neg.mpr ha_neg)
      have hinv := congrArg (fun x : A => (2 : ℂ)⁻¹ • x) htwo
      simpa [smul_smul] using hinv
  · rcases zmod_two_eq_zero_or_one n with rfl | rfl
    · rw [part_one, mem_oddPart_iff_generator] at ham
      rw [part_zero, mem_evenPart_iff_generator] at han
      exfalso
      apply ha
      have ha_neg : a = -a := han.symm.trans ham
      have htwo : (2 : ℂ) • a = 0 := by
        simpa only [two_smul] using (add_eq_zero_iff_eq_neg.mpr ha_neg)
      have hinv := congrArg (fun x : A => (2 : ℂ)⁻¹ • x) htwo
      simpa [smul_smul] using hinv
    · rfl

/-! ## Canonical projections and decomposition -/

/-- **Projection onto the even part.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The continuous complex-linear projection onto the even part is `a ↦
(a + σ(a))/2`. -/
def evenProjection (γ : CStarGrading A) : A →L[ℂ] A :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ A + γ.generatorCLM)

/-- **Projection onto the odd part.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The continuous complex-linear projection onto the odd part is `a ↦
(a - σ(a))/2`. -/
def oddProjection (γ : CStarGrading A) : A →L[ℂ] A :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ A - γ.generatorCLM)

@[simp]
theorem evenProjection_apply (γ : CStarGrading A) (a : A) :
    γ.evenProjection a = (2 : ℂ)⁻¹ • (a + γ.generatorAut a) := by
  simp only [evenProjection, smul_apply, add_apply, ContinuousLinearMap.id_apply,
    generatorCLM_apply]

@[simp]
theorem oddProjection_apply (γ : CStarGrading A) (a : A) :
    γ.oddProjection a = (2 : ℂ)⁻¹ • (a - γ.generatorAut a) := by
  simp only [oddProjection, smul_apply, sub_apply, ContinuousLinearMap.id_apply,
    generatorCLM_apply]

theorem generator_evenProjection (γ : CStarGrading A) (a : A) :
    γ.generatorAut (γ.evenProjection a) = γ.evenProjection a := by
  rw [evenProjection_apply, map_smul, map_add,
    generator_apply_generator]
  congr 1
  abel

theorem generator_oddProjection (γ : CStarGrading A) (a : A) :
    γ.generatorAut (γ.oddProjection a) = -γ.oddProjection a := by
  rw [oddProjection_apply, map_smul, map_sub, generator_apply_generator]
  module

theorem evenProjection_mem (γ : CStarGrading A) (a : A) :
    γ.evenProjection a ∈ γ.evenPart :=
  (γ.mem_evenPart_iff_generator _).2 (γ.generator_evenProjection a)

theorem oddProjection_mem (γ : CStarGrading A) (a : A) :
    γ.oddProjection a ∈ γ.oddPart :=
  (γ.mem_oddPart_iff_generator _).2 (γ.generator_oddProjection a)

theorem evenProjection_add_oddProjection (γ : CStarGrading A) (a : A) :
    γ.evenProjection a + γ.oddProjection a = a := by
  rw [evenProjection_apply, oddProjection_apply]
  module

theorem evenProjection_eq_self_of_mem (γ : CStarGrading A) {a : A}
    (ha : a ∈ γ.evenPart) :
    γ.evenProjection a = a := by
  rw [evenProjection_apply, (γ.mem_evenPart_iff_generator a).1 ha]
  module

theorem oddProjection_eq_self_of_mem (γ : CStarGrading A) {a : A}
    (ha : a ∈ γ.oddPart) :
    γ.oddProjection a = a := by
  rw [oddProjection_apply, (γ.mem_oddPart_iff_generator a).1 ha]
  module

theorem evenProjection_eq_zero_of_mem_odd (γ : CStarGrading A) {a : A}
    (ha : a ∈ γ.oddPart) :
    γ.evenProjection a = 0 := by
  rw [evenProjection_apply, (γ.mem_oddPart_iff_generator a).1 ha]
  module

theorem oddProjection_eq_zero_of_mem_even (γ : CStarGrading A) {a : A}
    (ha : a ∈ γ.evenPart) :
    γ.oddProjection a = 0 := by
  rw [oddProjection_apply, (γ.mem_evenPart_iff_generator a).1 ha]
  module

@[simp]
theorem evenProjection_idem (γ : CStarGrading A) :
    γ.evenProjection.comp γ.evenProjection = γ.evenProjection := by
  ext a
  exact γ.evenProjection_eq_self_of_mem (γ.evenProjection_mem a)

@[simp]
theorem oddProjection_idem (γ : CStarGrading A) :
    γ.oddProjection.comp γ.oddProjection = γ.oddProjection := by
  ext a
  exact γ.oddProjection_eq_self_of_mem (γ.oddProjection_mem a)

@[simp]
theorem evenProjection_comp_oddProjection (γ : CStarGrading A) :
    γ.evenProjection.comp γ.oddProjection = 0 := by
  ext a
  exact γ.evenProjection_eq_zero_of_mem_odd (γ.oddProjection_mem a)

@[simp]
theorem oddProjection_comp_evenProjection (γ : CStarGrading A) :
    γ.oddProjection.comp γ.evenProjection = 0 := by
  ext a
  exact γ.oddProjection_eq_zero_of_mem_even (γ.evenProjection_mem a)

theorem evenProjection_add_oddProjection_eq_id (γ : CStarGrading A) :
    γ.evenProjection + γ.oddProjection = ContinuousLinearMap.id ℂ A := by
  ext a
  exact γ.evenProjection_add_oddProjection a

theorem range_evenProjection (γ : CStarGrading A) :
    γ.evenProjection.range = γ.evenPart := by
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    exact γ.evenProjection_mem b
  · intro a ha
    exact ⟨a, γ.evenProjection_eq_self_of_mem ha⟩

theorem range_oddProjection (γ : CStarGrading A) :
    γ.oddProjection.range = γ.oddPart := by
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    exact γ.oddProjection_mem b
  · intro a ha
    exact ⟨a, γ.oddProjection_eq_self_of_mem ha⟩

theorem ker_evenProjection (γ : CStarGrading A) :
    γ.evenProjection.ker = γ.oddPart := by
  ext a
  constructor
  · intro ha
    have hzero : γ.evenProjection a = 0 := ha
    have hodd : γ.oddProjection a = a := by
      have hsum := γ.evenProjection_add_oddProjection a
      rw [hzero, zero_add] at hsum
      exact hsum
    rw [← hodd]
    exact γ.oddProjection_mem a
  · intro ha
    exact γ.evenProjection_eq_zero_of_mem_odd ha

theorem ker_oddProjection (γ : CStarGrading A) :
    γ.oddProjection.ker = γ.evenPart := by
  ext a
  constructor
  · intro ha
    have hzero : γ.oddProjection a = 0 := ha
    have heven : γ.evenProjection a = a := by
      have hsum := γ.evenProjection_add_oddProjection a
      rw [hzero, add_zero] at hsum
      exact hsum
    rw [← heven]
    exact γ.evenProjection_mem a
  · intro ha
    exact γ.oddProjection_eq_zero_of_mem_even ha

/-- **Topological even-odd decomposition.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The map `a ↦ ((a+σ(a))/2,(a-σ(a))/2)` is a continuous complex-linear
equivalence from `A` to the product of its even and odd parts, with inverse addition. -/
def decomposition (γ : CStarGrading A) :
    A ≃L[ℂ] γ.evenPart × γ.oddPart := by
  let forward : A →L[ℂ] γ.evenPart × γ.oddPart :=
    (γ.evenProjection.codRestrict γ.evenPart γ.evenProjection_mem).prod
      (γ.oddProjection.codRestrict γ.oddPart γ.oddProjection_mem)
  let inverse : γ.evenPart × γ.oddPart →L[ℂ] A :=
    γ.evenPart.subtypeL.coprod γ.oddPart.subtypeL
  exact ContinuousLinearEquiv.equivOfInverse forward inverse
    (fun a => by
      exact γ.evenProjection_add_oddProjection a)
    (fun p => by
      apply Prod.ext
      · apply Subtype.ext
        change γ.evenProjection ((p.1 : A) + (p.2 : A)) = p.1
        rw [map_add, γ.evenProjection_eq_self_of_mem p.1.property,
          γ.evenProjection_eq_zero_of_mem_odd p.2.property, add_zero]
      · apply Subtype.ext
        change γ.oddProjection ((p.1 : A) + (p.2 : A)) = p.2
        rw [map_add, γ.oddProjection_eq_zero_of_mem_even p.1.property,
          γ.oddProjection_eq_self_of_mem p.2.property, zero_add])

@[simp]
theorem decomposition_apply (γ : CStarGrading A) (a : A) :
    γ.decomposition a =
      (⟨γ.evenProjection a, γ.evenProjection_mem a⟩,
        ⟨γ.oddProjection a, γ.oddProjection_mem a⟩) :=
  rfl

@[simp]
theorem decomposition_symm_apply (γ : CStarGrading A)
    (p : γ.evenPart × γ.oddPart) :
    γ.decomposition.symm p = (p.1 : A) + p.2 :=
  rfl

theorem even_odd_isCompl (γ : CStarGrading A) :
    IsCompl γ.evenPart γ.oddPart := by
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff_inf_le]
    intro a ha
    rw [Submodule.mem_bot]
    have heven := γ.evenProjection_eq_self_of_mem ha.1
    have hzero := γ.evenProjection_eq_zero_of_mem_odd ha.2
    exact heven.symm.trans hzero
  · rw [codisjoint_iff_le_sup]
    intro a _
    have hmem : γ.evenProjection a + γ.oddProjection a ∈
        γ.evenPart ⊔ γ.oddPart :=
      Submodule.add_mem_sup (γ.evenProjection_mem a) (γ.oddProjection_mem a)
    rwa [γ.evenProjection_add_oddProjection a] at hmem

/-- **Internal direct sum of homogeneous parts.** Let `A` be a nonunital complex C*-algebra and let `γ`
be a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ`
for the automorphism of degree one. The even and odd parts form an internal complex-linear direct
sum in `A`. -/
theorem isInternal_part (γ : CStarGrading A) :
    DirectSum.IsInternal γ.part := by
  have huniv : (Set.univ : Set (ZMod 2)) = {0, 1} := by
    ext n
    rcases zmod_two_eq_zero_or_one n with rfl | rfl <;> simp
  exact (DirectSum.isInternal_submodule_iff_isCompl γ.part
    (show (0 : ZMod 2) ≠ 1 by decide) huniv).2 γ.even_odd_isCompl

/-- **Direct-sum decomposition of a graded algebra.** Let `A` be a nonunital complex C*-algebra and let
`γ` be a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write
`σ` for the automorphism of degree one. The two homogeneous parts give a complex-linear direct-sum
decomposition of `A` indexed by `ℤ/2ℤ`. -/
@[instance_reducible]
noncomputable def directSumDecomposition (γ : CStarGrading A) :
    DirectSum.Decomposition γ.part :=
  γ.isInternal_part.chooseDecomposition

/-! ## Tagged homogeneous operations -/

namespace Homogeneous

variable {γ : CStarGrading A}

/-- **Product of tagged homogeneous elements.** Let `A` be a nonunital complex C*-algebra and let `γ` be
a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. For tagged elements of degrees `m,n`, their product is the product
in `A` tagged with degree `m+n`. -/
def mul (x y : γ.Homogeneous) : γ.Homogeneous :=
  ⟨x.1 + y.1,
    ⟨(x : A) * (y : A), γ.mul_mem_part x.2.property y.2.property⟩⟩

@[simp]
theorem mul_degree (x y : γ.Homogeneous) : (mul x y).1 = x.1 + y.1 :=
  rfl

@[simp]
theorem coe_mul (x y : γ.Homogeneous) :
    ((mul x y : γ.Homogeneous) : A) = (x : A) * (y : A) :=
  rfl

/-- **Involution of a tagged homogeneous element.** Let `A` be a nonunital complex C*-algebra and let
`γ` be a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write
`σ` for the automorphism of degree one. Taking the involution of a homogeneous element keeps its
degree in `ℤ/2ℤ`. -/
def star (x : γ.Homogeneous) : γ.Homogeneous :=
  ⟨x.1, ⟨Star.star (x : A), γ.star_mem_part x.2.property⟩⟩

@[simp]
theorem star_degree (x : γ.Homogeneous) : (star x).1 = x.1 :=
  rfl

@[simp]
theorem coe_star (x : γ.Homogeneous) :
    ((star x : γ.Homogeneous) : A) = Star.star (x : A) :=
  rfl

end Homogeneous

/-! ## Gradings from involutions -/

/-- **Grading generated by an involution.** For a nonunital complex C*-algebra `A` and a complex
star-algebra automorphism `σ : A → A` satisfying `σ² = id`, the identity and `σ` define a point-norm
continuous `ℤ/2ℤ` grading of `A`. -/
def ofInvolution (σ : A ≃⋆ₐ[ℂ] A) (hσ : Function.Involutive σ) :
    CStarGrading A := by
  let involutionAut : ZMod 2 → A ≃⋆ₐ[ℂ] A :=
    fun n ↦ if n = 0 then 1 else σ
  have involutionAut_zero : involutionAut 0 = 1 := by
    simp [involutionAut]
  have degree_cases (n : ZMod 2) : n = 0 ∨ n = 1 := by
    fin_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
  have involutionAut_add (m n : ZMod 2) :
      involutionAut (m + n) = involutionAut m * involutionAut n := by
    have hs : σ * σ = 1 := by
      ext a
      exact hσ a
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases degree_cases m with hm | hm <;>
      rcases degree_cases n with hn | hn <;>
      rw [hm, hn]
    all_goals simp only [zero_add, add_zero, h11]
    all_goals simp [involutionAut, hs]
  exact
    { toMonoidHom :=
        { toFun := fun n ↦ involutionAut n.toAdd
          map_one' := by
            change involutionAut 0 = 1
            exact involutionAut_zero
          map_mul' := by
            intro m n
            change involutionAut (m.toAdd + n.toAdd) =
              involutionAut m.toAdd * involutionAut n.toAdd
            exact involutionAut_add m.toAdd n.toAdd }
      continuous_orbit := fun _ ↦ continuous_of_discreteTopology }

@[simp]
theorem ofInvolution_apply_zero (σ : A ≃⋆ₐ[ℂ] A)
    (hσ : Function.Involutive σ) (a : A) :
    PointNormCStarAddAction.aut (ofInvolution σ hσ) 0 a = a := by
  change (if (0 : ZMod 2) = 0 then (1 : A ≃⋆ₐ[ℂ] A) else σ) a = a
  simp

@[simp]
theorem ofInvolution_apply_one (σ : A ≃⋆ₐ[ℂ] A)
    (hσ : Function.Involutive σ) (a : A) :
    PointNormCStarAddAction.aut (ofInvolution σ hσ) 1 a = σ a := by
  change (if (1 : ZMod 2) = 0 then (1 : A ≃⋆ₐ[ℂ] A) else σ) a = σ a
  simp

@[simp]
theorem ofInvolution_generatorAut (σ : A ≃⋆ₐ[ℂ] A)
    (hσ : Function.Involutive σ) :
    (ofInvolution σ hσ).generatorAut = σ := by
  ext a
  exact ofInvolution_apply_one σ hσ a

theorem ofInvolution_generator_roundTrip (γ : CStarGrading A) :
    ofInvolution γ.generatorAut γ.generator_involutive = γ := by
  apply PointNormCStarAction.ext_apply
  intro n a
  rcases zmod_two_eq_zero_or_one n.toAdd with h0 | h1
  · have hn : n = (1 : Multiplicative (ZMod 2)) := by
      exact Multiplicative.toAdd.injective (by simpa using h0)
    subst n
    exact (PointNormCStarAction.apply_one _ _).trans
      (PointNormCStarAction.apply_one γ a).symm
  · have hn : n = Multiplicative.ofAdd (1 : ZMod 2) := by
      exact Multiplicative.toAdd.injective (by simpa using h1)
    subst n
    exact ofInvolution_apply_one γ.generatorAut γ.generator_involutive a

/-! ## Equivariant equivalences -/

/-- **Equivalence of graded C*-algebras.** For nonunital complex C*-algebras `A,B` with gradings
`γ_A,γ_B`, a graded equivalence is a complex star-algebra equivalence `e : A ≃ B` satisfying
`e(γ_A(s)a) = γ_B(s)(e(a))` for every `s,a`. -/
structure Equiv (γA : CStarGrading A) (γB : CStarGrading B)
    extends A ≃⋆ₐ[ℂ] B where
  equivariant' : ∀ (n : ZMod 2) a,
    toFun (PointNormCStarAddAction.aut γA n a) =
      PointNormCStarAddAction.aut γB n (toFun a)

namespace Equiv

variable {γA : CStarGrading A} {γB : CStarGrading B}
  {γC : CStarGrading C}

instance : EquivLike (Equiv γA γB) A B where
  coe e := e.toStarAlgEquiv
  inv e := e.toStarAlgEquiv.symm
  left_inv e := e.toStarAlgEquiv.left_inv
  right_inv e := e.toStarAlgEquiv.right_inv
  coe_injective' e f h _ := by
    cases e with
    | mk e he =>
      cases f with
      | mk f hf =>
        have hef : e = f := StarAlgEquiv.ext fun a ↦ congrFun h a
        subst f
        rfl

instance : NonUnitalAlgEquivClass (Equiv γA γB) ℂ A B where
  map_mul e := map_mul e.toStarAlgEquiv
  map_add e := map_add e.toStarAlgEquiv
  map_smulₛₗ e := map_smul e.toStarAlgEquiv

instance : StarRingEquivClass (Equiv γA γB) A B where
  map_star e := map_star e.toStarAlgEquiv

@[simp]
theorem equivariant (e : Equiv γA γB) (n : ZMod 2) (a : A) :
    e (PointNormCStarAddAction.aut γA n a) =
      PointNormCStarAddAction.aut γB n (e a) :=
  e.equivariant' n a

@[ext]
theorem ext {e f : Equiv γA γB} (h : ∀ a, e a = f a) : e = f := by
  cases e with
  | mk e he =>
    cases f with
    | mk f hf =>
      have h' : e = f := StarAlgEquiv.ext h
      subst f
      rfl

/-- **Identity grading equivalence.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The identity star-algebra equivalence of `A` intertwines `γ` with
itself. -/
def refl (γ : CStarGrading A) : Equiv γ γ where
  toStarAlgEquiv := StarAlgEquiv.refl ℂ A
  equivariant' := fun _ _ => rfl

@[simp]
theorem refl_apply (γ : CStarGrading A) (a : A) : refl γ a = a :=
  rfl

/-- **Inverse grading equivalence.** Let `A,B` be nonunital complex C*-algebras with gradings `γ_A,γ_B`,
and let `e : A ≃ B` be a complex star-algebra equivalence intertwining their `ℤ/2ℤ` actions. The
inverse star-algebra equivalence `e⁻¹ : B ≃ A` intertwines the gradings in the opposite direction. -/
def symm (e : Equiv γA γB) : Equiv γB γA where
  toStarAlgEquiv := e.toStarAlgEquiv.symm
  equivariant' := by
    intro n b
    apply e.toStarAlgEquiv.injective
    change e.toStarAlgEquiv
        (e.toStarAlgEquiv.symm (PointNormCStarAddAction.aut γB n b)) =
      e.toStarAlgEquiv (PointNormCStarAddAction.aut γA n
        (e.toStarAlgEquiv.symm b))
    have h := e.equivariant n (e.toStarAlgEquiv.symm b)
    have heb : e.toStarAlgEquiv (e.toStarAlgEquiv.symm b) = b :=
      e.toStarAlgEquiv.apply_symm_apply b
    have h' : e.toStarAlgEquiv (PointNormCStarAddAction.aut γA n
        (e.toStarAlgEquiv.symm b)) =
        PointNormCStarAddAction.aut γB n b := by
      exact h.trans (congrArg (PointNormCStarAddAction.aut γB n) heb)
    exact (e.toStarAlgEquiv.apply_symm_apply _).trans h'.symm

@[simp]
theorem symm_apply_apply (e : Equiv γA γB) (a : A) :
    CStarGrading.Equiv.symm e (e a) = a :=
  e.toStarAlgEquiv.left_inv a

@[simp]
theorem apply_symm_apply (e : Equiv γA γB) (b : B) :
    e (CStarGrading.Equiv.symm e b) = b :=
  e.toStarAlgEquiv.right_inv b

/-- **Composition of grading equivalences.** For graded nonunital complex C*-algebras `A,B,C`,
grading-intertwining star-algebra equivalences `e : A ≃ B` and `f : B ≃ C` compose to a grading
equivalence `f ∘ e : A ≃ C`. -/
def trans (e : Equiv γA γB) (f : Equiv γB γC) : Equiv γA γC where
  toStarAlgEquiv := e.toStarAlgEquiv.trans f.toStarAlgEquiv
  equivariant' := by
    intro n a
    change f (e (PointNormCStarAddAction.aut γA n a)) =
      PointNormCStarAddAction.aut γC n (f (e a))
    rw [e.equivariant, f.equivariant]

@[simp]
theorem trans_apply (e : Equiv γA γB) (f : Equiv γB γC) (a : A) :
    e.trans f a = f (e a) :=
  rfl

@[simp]
theorem refl_trans (e : Equiv γA γB) : (refl γA).trans e = e := by
  ext a
  rfl

@[simp]
theorem trans_refl (e : Equiv γA γB) : e.trans (refl γB) = e := by
  ext a
  rfl

theorem trans_assoc {D : Type*} [NonUnitalCStarAlgebra D]
    {γD : CStarGrading D}
    (e : Equiv γA γB) (f : Equiv γB γC) (g : Equiv γC γD) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  ext a
  rfl

/-- **Homomorphism underlying a grading equivalence.** Let `A,B` be nonunital complex C*-algebras with
gradings `γ_A,γ_B`, and let `e : A ≃ B` be a complex star-algebra equivalence intertwining their
`ℤ/2ℤ` actions. The nonunital complex star homomorphism underlying `e` is equivariant for the two
gradings. -/
def toHom (e : Equiv γA γB) : PointNormCStarAddAction.Hom γA γB where
  toNonUnitalStarAlgHom := e.toStarAlgEquiv.toNonUnitalStarAlgHom
  equivariant' := by
    intro n a
    change e (PointNormCStarAddAction.aut γA n.toAdd a) =
      PointNormCStarAddAction.aut γB n.toAdd (e a)
    exact e.equivariant n.toAdd a

@[simp]
theorem toHom_apply (e : Equiv γA γB) (a : A) : e.toHom a = e a :=
  rfl

theorem mapsTo_part (e : Equiv γA γB) (n : ZMod 2) :
    Set.MapsTo e (γA.part n : Set A) (γB.part n : Set B) := by
  intro a ha
  change a ∈ γA.part n at ha
  change e a ∈ γB.part n
  rw [γA.mem_part_iff_generator] at ha
  rw [γB.mem_part_iff_generator]
  have he := e.equivariant 1 a
  change e (γA.generatorAut a) = γB.generatorAut (e a) at he
  rw [← he, ha, map_smul]

theorem mem_part_iff (e : Equiv γA γB) (n : ZMod 2) (a : A) :
    e a ∈ γB.part n ↔ a ∈ γA.part n := by
  constructor
  · intro ha
    have := (CStarGrading.Equiv.symm e).mapsTo_part n ha
    simpa using this
  · intro ha
    exact e.mapsTo_part n ha

/-- **Continuous linear equivalence of graded algebras.** Let `A,B` be nonunital complex C*-algebras
with gradings `γ_A,γ_B`, and let `e : A ≃ B` be a complex star-algebra equivalence intertwining
their `ℤ/2ℤ` actions. The underlying complex-linear equivalence `A ≃ B` is continuous in both
directions for their C*-norms. -/
def toContinuousLinearEquiv (e : Equiv γA γB) : A ≃L[ℂ] B where
  toFun := e
  invFun := CStarGrading.Equiv.symm e
  left_inv := CStarGrading.Equiv.symm_apply_apply e
  right_inv := CStarGrading.Equiv.apply_symm_apply e
  map_add' := map_add e
  map_smul' := map_smul e
  continuous_toFun := (StarAlgEquiv.isometry e.toStarAlgEquiv).continuous
  continuous_invFun := (StarAlgEquiv.isometry e.toStarAlgEquiv.symm).continuous

@[simp]
theorem toContinuousLinearEquiv_apply (e : Equiv γA γB) (a : A) :
    e.toContinuousLinearEquiv a = e a :=
  rfl

/-- **Equivalence of homogeneous parts.** Let `A,B` be nonunital complex C*-algebras with gradings
`γ_A,γ_B`, and let `e : A ≃ B` be a complex star-algebra equivalence intertwining their `ℤ/2ℤ`
actions. For any degree `n ∈ ℤ/2ℤ`, restriction of `e` gives a continuous complex-linear equivalence
between the degree-`n` parts. -/
def partEquiv (e : Equiv γA γB) (n : ZMod 2) :
    γA.part n ≃L[ℂ] γB.part n := by
  let forward : γA.part n →L[ℂ] γB.part n :=
    (e.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (γA.part n).subtypeL).codRestrict (γB.part n) fun a ↦ by
        change e.toContinuousLinearEquiv (a : A) ∈ γB.part n
        rw [toContinuousLinearEquiv_apply]
        exact e.mapsTo_part n a.property
  let backward : γB.part n →L[ℂ] γA.part n :=
    ((CStarGrading.Equiv.toContinuousLinearEquiv
      (CStarGrading.Equiv.symm e)).toContinuousLinearMap.comp
      (γB.part n).subtypeL).codRestrict (γA.part n) fun b ↦ by
        change (CStarGrading.Equiv.toContinuousLinearEquiv
          (CStarGrading.Equiv.symm e)) (b : B) ∈ γA.part n
        rw [toContinuousLinearEquiv_apply]
        exact (CStarGrading.Equiv.symm e).mapsTo_part n b.property
  exact ContinuousLinearEquiv.equivOfInverse forward backward
    (fun a ↦ by
      apply Subtype.ext
      exact CStarGrading.Equiv.symm_apply_apply e _)
    (fun b ↦ by
      apply Subtype.ext
      exact CStarGrading.Equiv.apply_symm_apply e _)

@[simp]
theorem partEquiv_apply (e : Equiv γA γB) (n : ZMod 2)
    (a : γA.part n) :
    ((e.partEquiv n a : γB.part n) : B) = e a := by
  simp only [partEquiv, ContinuousLinearEquiv.equivOfInverse_apply]
  exact toContinuousLinearEquiv_apply e a

/-- **Equivalence of the odd parts.** Let `A,B` be nonunital complex C*-algebras with gradings
`γ_A,γ_B`, and let `e : A ≃ B` be a complex star-algebra equivalence intertwining their `ℤ/2ℤ`
actions. Restriction of `e` gives a continuous complex-linear equivalence between the odd subspaces
of the two algebras. -/
abbrev oddEquiv (e : Equiv γA γB) : γA.oddPart ≃L[ℂ] γB.oddPart :=
  e.partEquiv 1

@[simp]
theorem oddEquiv_apply (e : Equiv γA γB) (a : γA.oddPart) :
    ((e.oddEquiv a : γB.oddPart) : B) = e a :=
  partEquiv_apply e 1 a

/-- **Transport of tagged homogeneous elements.** Let `A,B` be nonunital complex C*-algebras with
gradings `γ_A,γ_B`, and let `e : A ≃ B` be a complex star-algebra equivalence intertwining their
`ℤ/2ℤ` actions. Applying `e` to the underlying element transports a tagged homogeneous element of
`A` to one of `B` with the same degree. -/
def mapHomogeneous (e : Equiv γA γB) (x : γA.Homogeneous) :
    γB.Homogeneous :=
  ⟨x.1, ⟨e x, e.mapsTo_part x.1 x.2.property⟩⟩

@[simp]
theorem mapHomogeneous_degree (e : Equiv γA γB) (x : γA.Homogeneous) :
    (e.mapHomogeneous x).1 = x.1 :=
  rfl

@[simp]
theorem coe_mapHomogeneous (e : Equiv γA γB) (x : γA.Homogeneous) :
    ((e.mapHomogeneous x : γB.Homogeneous) : B) = e x :=
  rfl

theorem mapHomogeneous_mul (e : Equiv γA γB)
    (x y : γA.Homogeneous) :
    e.mapHomogeneous (Homogeneous.mul x y) =
      Homogeneous.mul (e.mapHomogeneous x) (e.mapHomogeneous y) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  change e ((x : A) * (y : A)) = e x * e y
  exact map_mul e.toStarAlgEquiv (x : A) (y : A)

theorem mapHomogeneous_star (e : Equiv γA γB) (x : γA.Homogeneous) :
    e.mapHomogeneous (Homogeneous.star x) =
      Homogeneous.star (e.mapHomogeneous x) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  change e (Star.star (x : A)) = Star.star (e x)
  exact map_star e.toStarAlgEquiv (x : A)

/-- **Star equivalence of the even subalgebras.** Let `A,B` be nonunital complex C*-algebras with
gradings `γ_A,γ_B`, and let `e : A ≃ B` be a complex star-algebra equivalence intertwining their
`ℤ/2ℤ` actions. Restriction of `e` gives a complex star-algebra equivalence between the fixed-point
even subalgebras. -/
def evenEquiv (e : Equiv γA γB) :
    γA.evenSubalgebra ≃⋆ₐ[ℂ] γB.evenSubalgebra :=
  StarAlgEquiv.ofBijective e.toHom.fixedPointMap
    ⟨by
      intro a b h
      apply Subtype.ext
      exact e.toStarAlgEquiv.injective (congrArg Subtype.val h),
     by
      intro b
      refine ⟨⟨CStarGrading.Equiv.symm e b, ?_⟩, ?_⟩
      · have hb0 : (b : B) ∈ γB.part 0 := by
          change (b : B) ∈ γB.evenPart
          exact b.property
        have hout := (CStarGrading.Equiv.symm e).mapsTo_part 0 hb0
        change CStarGrading.Equiv.symm e (b : B) ∈ γA.evenPart at hout
        exact hout
      · apply Subtype.ext
        simp⟩

@[simp]
theorem evenEquiv_apply (e : Equiv γA γB) (a : γA.evenSubalgebra) :
    ((e.evenEquiv a : γB.evenSubalgebra) : B) = e a :=
  rfl

end Equiv

/-! ## Transport by conjugation -/

/-- **Transport of a C*-grading.** Let `A,B` be nonunital complex C*-algebras, `e : A ≃ B` a complex
star-algebra equivalence, and `γ_A` a grading of `A`. Conjugating each grading automorphism by `e`
defines a grading on `B`: `γ_B(s) = e ∘ γ_A(s) ∘ e⁻¹`. -/
def transport (e : A ≃⋆ₐ[ℂ] B) (γ : CStarGrading A) :
    CStarGrading B := by
  let conjugateGenerator : B ≃⋆ₐ[ℂ] B :=
    (e.symm.trans γ.generatorAut).trans e
  have conjugateGenerator_involutive :
      Function.Involutive conjugateGenerator := by
    intro b
    change e (γ.generatorAut (e.symm
      (e (γ.generatorAut (e.symm b))))) = b
    rw [e.symm_apply_apply, γ.generator_involutive, e.apply_symm_apply]
  exact ofInvolution conjugateGenerator conjugateGenerator_involutive

@[simp]
theorem transport_apply (e : A ≃⋆ₐ[ℂ] B) (γ : CStarGrading A)
    (n : ZMod 2) (b : B) :
    PointNormCStarAddAction.aut (transport e γ) n b =
      e (PointNormCStarAddAction.aut γ n (e.symm b)) := by
  rcases zmod_two_eq_zero_or_one n with hn | hn
  · rw [hn]
    calc
      PointNormCStarAddAction.aut (transport e γ) 0 b = b :=
        PointNormCStarAddAction.apply_zero (transport e γ) b
      _ = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = e (PointNormCStarAddAction.aut γ 0 (e.symm b)) :=
        congrArg e (PointNormCStarAddAction.apply_zero γ (e.symm b)).symm
  · rw [hn]
    have hgen : (transport e γ).generatorAut =
        (e.symm.trans γ.generatorAut).trans e := by
      simp only [transport]
      apply ofInvolution_generatorAut
    change (transport e γ).generatorAut b =
      e (γ.generatorAut (e.symm b))
    rw [hgen]
    rfl

@[simp]
theorem transport_refl (γ : CStarGrading A) :
    transport (StarAlgEquiv.refl ℂ A) γ = γ := by
  apply PointNormCStarAction.ext_apply
  intro n a
  have hn : Multiplicative.ofAdd n.toAdd = n :=
    Multiplicative.ofAdd.apply_symm_apply n
  rw [← hn]
  change PointNormCStarAddAction.aut
      (transport (StarAlgEquiv.refl ℂ A) γ) n.toAdd a =
    PointNormCStarAddAction.aut γ n.toAdd a
  rw [transport_apply]
  rfl

theorem transport_trans (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C)
    (γ : CStarGrading A) :
    transport (e.trans f) γ = transport f (transport e γ) := by
  apply PointNormCStarAction.ext_apply
  intro n c
  have hn : Multiplicative.ofAdd n.toAdd = n :=
    Multiplicative.ofAdd.apply_symm_apply n
  rw [← hn]
  change PointNormCStarAddAction.aut (transport (e.trans f) γ) n.toAdd c =
    PointNormCStarAddAction.aut (transport f (transport e γ)) n.toAdd c
  rw [transport_apply, transport_apply, transport_apply]
  rfl

theorem transport_symm (e : A ≃⋆ₐ[ℂ] B) (γ : CStarGrading A) :
    transport e.symm (transport e γ) = γ := by
  have h := transport_trans e e.symm γ
  have he : e.trans e.symm = StarAlgEquiv.refl ℂ A := by
    ext a
    exact e.symm_apply_apply a
  rw [he, transport_refl] at h
  exact h.symm

/-- **Equivalence to a transported grading.** Let `A,B` be nonunital complex C*-algebras, `e : A ≃ B` a
complex star-algebra equivalence, and `γ_A` a grading of `A`. The equivalence `e` intertwines the
grading of `A` with its conjugate grading on `B`. -/
def transportEquiv (e : A ≃⋆ₐ[ℂ] B) (γ : CStarGrading A) :
    Equiv γ (transport e γ) where
  toStarAlgEquiv := e
  equivariant' := by
    intro n a
    have h := transport_apply e γ n (e a)
    rw [e.symm_apply_apply] at h
    exact h.symm

@[simp]
theorem transportEquiv_apply (e : A ≃⋆ₐ[ℂ] B)
    (γ : CStarGrading A) (a : A) :
    transportEquiv e γ a = e a :=
  rfl

theorem Equiv.map_evenProjection {γA : CStarGrading A}
    {γB : CStarGrading B} (e : Equiv γA γB) (a : A) :
    e (γA.evenProjection a) = γB.evenProjection (e a) := by
  have he := e.equivariant 1 a
  change e (γA.generatorAut a) = γB.generatorAut (e a) at he
  rw [evenProjection_apply, evenProjection_apply, map_smul, map_add, he]

theorem Equiv.map_oddProjection {γA : CStarGrading A}
    {γB : CStarGrading B} (e : Equiv γA γB) (a : A) :
    e (γA.oddProjection a) = γB.oddProjection (e a) := by
  have he := e.equivariant 1 a
  change e (γA.generatorAut a) = γB.generatorAut (e a) at he
  rw [oddProjection_apply, oddProjection_apply, map_smul, map_sub, he]

theorem Equiv.map_decomposition {γA : CStarGrading A}
    {γB : CStarGrading B} (e : Equiv γA γB) (a : A) :
    (e.partEquiv 0 (γA.decomposition a).1,
      e.partEquiv 1 (γA.decomposition a).2) =
        γB.decomposition (e a) := by
  apply Prod.ext <;> apply Subtype.ext
  · calc
      ((e.partEquiv 0 (γA.decomposition a).1 : γB.part 0) : B) =
          e ((γA.decomposition a).1 : A) :=
        Equiv.partEquiv_apply e 0 _
      _ = e (γA.evenProjection a) := by rw [decomposition_apply]
      _ = γB.evenProjection (e a) := e.map_evenProjection a
      _ = ((γB.decomposition (e a)).1 : B) := by rw [decomposition_apply]
  · calc
      ((e.partEquiv 1 (γA.decomposition a).2 : γB.part 1) : B) =
          e ((γA.decomposition a).2 : A) :=
        Equiv.partEquiv_apply e 1 _
      _ = e (γA.oddProjection a) := by rw [decomposition_apply]
      _ = γB.oddProjection (e a) := e.map_oddProjection a
      _ = ((γB.decomposition (e a)).2 : B) := by rw [decomposition_apply]

/-! ## Graded commutators -/

/-- **Bilinear commutator for specified parities.** For a nonunital complex C*-algebra `A` and degrees
`m,n ∈ ℤ/2ℤ`, the formula `(x,y) ↦ x y - (-1)^(m n) y x` is a continuous complex-bilinear map from
`A × A` to `A`. -/
def commutatorOfDegreesL (m n : ZMod 2) :
    A →L[ℂ] A →L[ℂ] A :=
  ContinuousLinearMap.mul ℂ A -
    degreeSign (m * n) • (ContinuousLinearMap.mul ℂ A).flip

@[simp]
theorem commutatorOfDegreesL_apply (m n : ZMod 2) (a b : A) :
    commutatorOfDegreesL (A := A) m n a b =
      a * b - degreeSign (m * n) • (b * a) :=
  rfl

theorem commutatorOfDegrees_mem_part (γ : CStarGrading A)
    {m n : ZMod 2} {a b : A}
    (ha : a ∈ γ.part m) (hb : b ∈ γ.part n) :
    commutatorOfDegreesL (A := A) m n a b ∈ γ.part (m + n) := by
  apply (γ.part (m + n)).sub_mem
  · exact γ.mul_mem_part ha hb
  · exact (γ.part (m + n)).smul_mem _
      (by simpa [add_comm] using γ.mul_mem_part hb ha)

namespace Homogeneous

variable {γ : CStarGrading A}

/-- **Graded commutator of homogeneous elements.** Let `A` be a nonunital complex C*-algebra and let `γ`
be a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ`
for the automorphism of degree one. For homogeneous `x,y` of degrees `m,n`, their graded commutator
is `x y - (-1)^(m n) y x`, tagged with degree `m+n`. -/
def commutator (x y : γ.Homogeneous) : γ.Homogeneous :=
  ⟨x.1 + y.1,
    ⟨commutatorOfDegreesL (A := A) x.1 y.1 (x : A) (y : A),
      γ.commutatorOfDegrees_mem_part x.2.property y.2.property⟩⟩

@[simp]
theorem commutator_degree (x y : γ.Homogeneous) :
    (commutator x y).1 = x.1 + y.1 :=
  rfl

@[simp]
theorem coe_commutator (x y : γ.Homogeneous) :
    ((commutator x y : γ.Homogeneous) : A) =
      (x : A) * (y : A) -
        degreeSign (x.1 * y.1) • ((y : A) * (x : A)) :=
  rfl

end Homogeneous

/-- **Projection to a homogeneous part.** Let `A` be a nonunital complex C*-algebra and let `γ` be a
point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. For `n ∈ ℤ/2ℤ`, this is the continuous complex-linear even
projection when `n=0` and odd projection when `n=1`. -/
def partProjection (γ : CStarGrading A) (n : ZMod 2) : A →L[ℂ] A :=
  if n = 0 then γ.evenProjection else γ.oddProjection

@[simp]
theorem partProjection_zero (γ : CStarGrading A) :
    γ.partProjection 0 = γ.evenProjection := by
  simp [partProjection]

@[simp]
theorem partProjection_one (γ : CStarGrading A) :
    γ.partProjection 1 = γ.oddProjection := by
  simp [partProjection]

theorem partProjection_mem (γ : CStarGrading A) (n : ZMod 2) (a : A) :
    γ.partProjection n a ∈ γ.part n := by
  rcases zmod_two_eq_zero_or_one n with rfl | rfl
  · exact γ.evenProjection_mem a
  · exact γ.oddProjection_mem a

theorem partProjection_eq_self_of_mem (γ : CStarGrading A)
    {n : ZMod 2} {a : A} (ha : a ∈ γ.part n) :
    γ.partProjection n a = a := by
  rcases zmod_two_eq_zero_or_one n with rfl | rfl
  · exact γ.evenProjection_eq_self_of_mem ha
  · exact γ.oddProjection_eq_self_of_mem ha

theorem partProjection_eq_zero_of_mem_ne (γ : CStarGrading A)
    {m n : ZMod 2} {a : A} (ha : a ∈ γ.part m) (hmn : m ≠ n) :
    γ.partProjection n a = 0 := by
  rcases zmod_two_eq_zero_or_one m with rfl | rfl
  · rcases zmod_two_eq_zero_or_one n with rfl | rfl
    · exact (hmn rfl).elim
    · exact γ.oddProjection_eq_zero_of_mem_even ha
  · rcases zmod_two_eq_zero_or_one n with rfl | rfl
    · exact γ.evenProjection_eq_zero_of_mem_odd ha
    · exact (hmn rfl).elim

/-- **Continuous bilinear graded commutator.** Let `A` be a nonunital complex C*-algebra and let `γ` be
a point-norm continuous action of `ℤ/2ℤ` on `A` by complex star-algebra automorphisms. Write `σ` for
the automorphism of degree one. The formula `[x_m,y_n] = x_m y_n - (-1)^(m n) y_n x_m` for
homogeneous elements extends continuously and complex-bilinearly to all of `A × A` through the even
and odd projections. -/
def commutatorL (γ : CStarGrading A) : A →L[ℂ] A →L[ℂ] A := by
  let projected (m n : ZMod 2) : A →L[ℂ] A →L[ℂ] A :=
    let L : A →L[ℂ] A →L[ℂ] A := commutatorOfDegreesL m n
    (((ContinuousLinearMap.precompR A L).flip (γ.partProjection n)).comp
      (γ.partProjection m))
  exact projected 0 0 + projected 0 1 + projected 1 0 + projected 1 1

@[simp]
theorem commutatorL_apply (γ : CStarGrading A) (a b : A) :
    γ.commutatorL a b =
      commutatorOfDegreesL (A := A) 0 0
          (γ.evenProjection a) (γ.evenProjection b) +
        commutatorOfDegreesL (A := A) 0 1
          (γ.evenProjection a) (γ.oddProjection b) +
        commutatorOfDegreesL (A := A) 1 0
          (γ.oddProjection a) (γ.evenProjection b) +
        commutatorOfDegreesL (A := A) 1 1
          (γ.oddProjection a) (γ.oddProjection b) :=
  rfl

theorem commutatorL_of_mem (γ : CStarGrading A)
    {m n : ZMod 2} {a b : A}
    (ha : a ∈ γ.part m) (hb : b ∈ γ.part n) :
    γ.commutatorL a b = commutatorOfDegreesL (A := A) m n a b := by
  rcases zmod_two_eq_zero_or_one m with rfl | rfl
  · rcases zmod_two_eq_zero_or_one n with rfl | rfl
    · simp [commutatorL_apply, γ.evenProjection_eq_self_of_mem ha,
        γ.oddProjection_eq_zero_of_mem_even ha,
        γ.evenProjection_eq_self_of_mem hb,
        γ.oddProjection_eq_zero_of_mem_even hb]
    · simp [commutatorL_apply, γ.evenProjection_eq_self_of_mem ha,
        γ.oddProjection_eq_zero_of_mem_even ha,
        γ.oddProjection_eq_self_of_mem hb,
        γ.evenProjection_eq_zero_of_mem_odd hb]
  · rcases zmod_two_eq_zero_or_one n with rfl | rfl
    · simp [commutatorL_apply, γ.oddProjection_eq_self_of_mem ha,
        γ.evenProjection_eq_zero_of_mem_odd ha,
        γ.evenProjection_eq_self_of_mem hb,
        γ.oddProjection_eq_zero_of_mem_even hb]
    · simp [commutatorL_apply, γ.oddProjection_eq_self_of_mem ha,
        γ.evenProjection_eq_zero_of_mem_odd ha,
        γ.oddProjection_eq_self_of_mem hb,
        γ.evenProjection_eq_zero_of_mem_odd hb]

theorem commutator_skew (m n : ZMod 2) (a b : A) :
    commutatorOfDegreesL (A := A) m n a b +
        degreeSign (m * n) • commutatorOfDegreesL (A := A) n m b a = 0 := by
  rcases zmod_two_eq_zero_or_one m with hm | hm <;>
    rcases zmod_two_eq_zero_or_one n with hn | hn <;>
    rw [hm, hn]
  all_goals simp only [commutatorOfDegreesL_apply, zero_mul, mul_zero,
    one_mul, degreeSign_zero, degreeSign_one, one_smul, neg_one_smul]
  all_goals module

theorem commutator_leibniz (m n p : ZMod 2) (a b c : A) :
    commutatorOfDegreesL (A := A) m (n + p) a (b * c) =
      commutatorOfDegreesL (A := A) m n a b * c +
        degreeSign (m * n) •
          (b * commutatorOfDegreesL (A := A) m p a c) := by
  rcases zmod_two_eq_zero_or_one m with hm | hm <;>
    rcases zmod_two_eq_zero_or_one n with hn | hn <;>
    rcases zmod_two_eq_zero_or_one p with hp | hp <;>
    rw [hm, hn, hp]
  all_goals simp only [commutatorOfDegreesL_apply, zero_mul, mul_zero,
    one_mul, zero_add, add_zero, zmod_two_one_add_one, degreeSign_zero,
    degreeSign_one, one_smul, neg_one_smul]
  all_goals noncomm_ring

theorem commutator_jacobi (m n p : ZMod 2) (a b c : A) :
    degreeSign (m * p) •
        commutatorOfDegreesL (A := A) (m + n) p
          (commutatorOfDegreesL (A := A) m n a b) c +
      degreeSign (m * n) •
        commutatorOfDegreesL (A := A) (n + p) m
          (commutatorOfDegreesL (A := A) n p b c) a +
      degreeSign (n * p) •
        commutatorOfDegreesL (A := A) (p + m) n
          (commutatorOfDegreesL (A := A) p m c a) b = 0 := by
  rcases zmod_two_eq_zero_or_one m with hm | hm <;>
    rcases zmod_two_eq_zero_or_one n with hn | hn <;>
    rcases zmod_two_eq_zero_or_one p with hp | hp <;>
    rw [hm, hn, hp]
  all_goals simp only [commutatorOfDegreesL_apply, zero_mul, mul_zero,
    one_mul, zero_add, add_zero, zmod_two_one_add_one, degreeSign_zero,
    degreeSign_one, one_smul, neg_one_smul]
  all_goals noncomm_ring

theorem commutator_mem_part (γ : CStarGrading A)
    {m n : ZMod 2} {a b : A}
    (ha : a ∈ γ.part m) (hb : b ∈ γ.part n) :
    γ.commutatorL a b ∈ γ.part (m + n) := by
  rw [γ.commutatorL_of_mem ha hb]
  exact γ.commutatorOfDegrees_mem_part ha hb

theorem Equiv.map_commutatorOfDegrees {γA : CStarGrading A}
    {γB : CStarGrading B} (e : Equiv γA γB)
    (m n : ZMod 2) (a b : A) :
    e (commutatorOfDegreesL (A := A) m n a b) =
      commutatorOfDegreesL (A := B) m n (e a) (e b) := by
  simp [commutatorOfDegreesL_apply, map_sub, map_mul, map_smul]

theorem Equiv.map_commutator {γA : CStarGrading A}
    {γB : CStarGrading B} (e : Equiv γA γB) (a b : A) :
    e (γA.commutatorL a b) = γB.commutatorL (e a) (e b) := by
  simp only [commutatorL_apply, map_add, e.map_evenProjection,
    e.map_oddProjection, e.map_commutatorOfDegrees]

theorem Equiv.mapHomogeneous_commutator {γA : CStarGrading A}
    {γB : CStarGrading B} (e : Equiv γA γB)
    (x y : γA.Homogeneous) :
    e.mapHomogeneous (Homogeneous.commutator x y) =
      Homogeneous.commutator (e.mapHomogeneous x) (e.mapHomogeneous y) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Subtype.ext
  exact e.map_commutatorOfDegrees x.1 y.1 x y

/-! ## C-star consequences -/

theorem odd_selfAdjoint_commutator_self
    (γ : CStarGrading A) {a : A}
    (ha : a ∈ γ.oddPart) (hsa : IsSelfAdjoint a) :
    γ.commutatorL a a = (2 : ℂ) • (star a * a) := by
  have ha1 : a ∈ γ.part 1 := by simpa only [part_one] using ha
  rw [γ.commutatorL_of_mem ha1 ha1]
  simp only [commutatorOfDegreesL_apply, one_mul, degreeSign_one,
    neg_smul, one_smul, sub_neg_eq_add, hsa.star_eq]
  rw [two_smul ℂ]

theorem odd_selfAdjoint_commutator_self_nonneg
    (γ : CStarGrading A) {a : A}
    (ha : a ∈ γ.oddPart) (hsa : IsSelfAdjoint a) :
    @LE.le A (CStarAlgebra.spectralOrder A).toLE 0 (γ.commutatorL a a) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  change 0 ≤ γ.commutatorL a a
  rw [γ.odd_selfAdjoint_commutator_self ha hsa]
  rw [two_smul ℂ]
  exact add_nonneg (star_mul_self_nonneg a) (star_mul_self_nonneg a)

theorem odd_commutator
    (γ : CStarGrading A) {a b : A}
    (ha : a ∈ γ.oddPart) (hb : b ∈ γ.oddPart) :
    γ.commutatorL a b = a * b + b * a := by
  have ha1 : a ∈ γ.part 1 := by simpa only [part_one] using ha
  have hb1 : b ∈ γ.part 1 := by simpa only [part_one] using hb
  rw [γ.commutatorL_of_mem ha1 hb1]
  simp [commutatorOfDegreesL_apply]

theorem odd_selfAdjoint_commutator_isSelfAdjoint
    (γ : CStarGrading A) {a b : A}
    (ha : a ∈ γ.oddPart) (hb : b ∈ γ.oddPart)
    (hsa : IsSelfAdjoint a) (hsb : IsSelfAdjoint b) :
    IsSelfAdjoint (γ.commutatorL a b) := by
  rw [γ.odd_commutator ha hb]
  change star (a * b + b * a) = a * b + b * a
  simp [hsa.star_eq, hsb.star_eq, add_comm]

end CStarGrading
