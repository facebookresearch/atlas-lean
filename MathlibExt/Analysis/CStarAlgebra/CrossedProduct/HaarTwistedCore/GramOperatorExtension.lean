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

public import MathlibExt.Analysis.CStarAlgebra.SeminormGramDomain
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.FiniteHilbertGramCoefficient
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormGramGroupActions
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Bounded operators from the dense Gram coefficient span

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram domain D is
span_ℂ{T(f)ξ:f∈Carrier μ α,ξ∈E}, with its inherited Hilbert norm; D is dense in E. For a
finitely supported function c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The
coefficient transform C_a(c)=∑(f,ξ) c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ)
c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the same finite formal sums. The bounds ‖C_a(c)‖≤‖a‖‖ev(c)‖
and ‖G_g(c)‖=‖ev(c)‖ make these transforms well defined on D. They extend to a bounded
coefficient operator P_a and an isometric group operator U_g on E.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators InnerProductSpace

namespace HaarTwistedCore

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α)) (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **Evaluation of finite formal Gram sums.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The complex linear map gramEvaluation μ α
p H ρ sends c to ev(c)∈E.
-/
def gramEvaluation : ((Carrier μ α × ρ.essentialSpace) →₀ ℂ) →ₗ[ℂ] ρ.essentialSpace :=
  Finsupp.linearCombination ℂ fun z =>
    ρ.essentialRepresentation (p.toNonUnitalCompletion z.1) z.2

omit [μ.Regular] in
/-- **Range of finite Gram evaluation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram domain D is
span_ℂ{T(f)ξ:f∈Carrier μ α,ξ∈E}, with its inherited Hilbert norm; D is dense in E. For a
finitely supported function c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The range of
gramEvaluation μ α p H ρ equals D=p.rawHilbertGramDomain H ρ.
-/
theorem gramEvaluation_range :
    (gramEvaluation μ α p H ρ).range = p.rawHilbertGramDomain H ρ := by
  exact Finsupp.range_linearCombination ℂ

omit [μ.Regular] in
/-- **Density of finite Gram evaluation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The map gramEvaluation μ α p H ρ has
dense range in E.
-/
theorem denseRange_gramEvaluation : DenseRange (gramEvaluation μ α p H ρ) := by
  have hrange : Set.range (gramEvaluation μ α p H ρ) =
      (p.rawHilbertGramDomain H ρ : Set ρ.essentialSpace) := by
    change ((gramEvaluation μ α p H ρ).range : Set ρ.essentialSpace) = _
    rw [gramEvaluation_range]
  change Dense (Set.range (gramEvaluation μ α p H ρ))
  rw [hrange]
  exact p.dense_rawHilbertGramDomain H ρ

/-- **Coefficient transform of a finite formal Gram sum.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. The complex linear map gramCoefficientTransform μ α p H ρ a sends c
to C_a(c)∈E.
-/
def gramCoefficientTransform (a : A) :
    ((Carrier μ α × ρ.essentialSpace) →₀ ℂ) →ₗ[ℂ] ρ.essentialSpace :=
  Finsupp.linearCombination ℂ fun z =>
    ρ.essentialRepresentation (p.toNonUnitalCompletion (coefficientLeft μ α a z.1)) z.2

/-- **Group transform of a finite formal Gram sum.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. The complex linear map gramGroupTransform μ α p H ρ g sends c to
G_g(c)∈E.
-/
def gramGroupTransform (g : G) :
    ((Carrier μ α × ρ.essentialSpace) →₀ ℂ) →ₗ[ℂ] ρ.essentialSpace :=
  Finsupp.linearCombination ℂ fun z =>
    ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g z.1)) z.2

omit [μ.Regular] in
/-- **Coefficient bound for a finite formal Gram sum.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. For a∈A and a finite formal sum c, ‖C_a(c)‖≤‖a‖‖ev(c)‖.
-/
theorem norm_gramCoefficientTransform_le (a : A)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    ‖gramCoefficientTransform μ α p H ρ a x‖ ≤ ‖a‖ * ‖gramEvaluation μ α p H ρ x‖ := by
  simpa only [finiteHilbertGramCoefficient_inr, finiteHilbertGram,
    gramCoefficientTransform, gramEvaluation, Finsupp.linearCombination_apply, Finsupp.sum] using
    norm_finiteHilbertGramCoefficient_inr_le μ α p ρ.essentialRepresentation a x.support x
      (fun z => z.1) (fun z => z.2)

/-- **Group norm invariance of a finite formal Gram sum.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. For g∈G and a finite formal sum c, ‖G_g(c)‖=‖ev(c)‖.
-/
theorem norm_gramGroupTransform (g : G)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    ‖gramGroupTransform μ α p H ρ g x‖ = ‖gramEvaluation μ α p H ρ x‖ := by
  simpa only [gramGroupTransform, gramEvaluation, Finsupp.linearCombination_apply, Finsupp.sum] using
    norm_sum_completedRepresentation_groupLeft μ α p ρ.essentialSpace
      ρ.essentialRepresentation g x.support x (fun z => z.1) (fun z => z.2)

omit [μ.Regular] in
/-- **Coefficient transforms vanish on the Gram evaluation kernel.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. For a∈A, ker(ev)⊆ker(C_a): ev(c)=0 implies C_a(c)=0.
-/
theorem gramCoefficientTransform_kernel (a : A) :
    (gramEvaluation μ α p H ρ).ker ≤ (gramCoefficientTransform μ α p H ρ a).ker := by
  intro x hx
  change gramEvaluation μ α p H ρ x = 0 at hx
  change gramCoefficientTransform μ α p H ρ a x = 0
  have hbase : finiteHilbertGram μ α p ρ.essentialRepresentation x.support x
      (fun z => z.1) (fun z => z.2) = 0 := by
    simpa only [finiteHilbertGram, gramEvaluation,
      Finsupp.linearCombination_apply, Finsupp.sum] using hx
  have hzero := finiteHilbertGramCoefficient_inr_eq_zero_of_eq_zero μ α p
    ρ.essentialRepresentation a x.support x (fun z => z.1) (fun z => z.2) hbase
  simpa only [finiteHilbertGramCoefficient_inr, gramCoefficientTransform,
    Finsupp.linearCombination_apply, Finsupp.sum] using hzero

/-- **Group transforms have the Gram evaluation kernel.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. For g∈G, ker(G_g)=ker(ev), so G_g(c)=0 exactly when ev(c)=0.
-/
theorem gramGroupTransform_kernel (g : G) :
    (gramGroupTransform μ α p H ρ g).ker = (gramEvaluation μ α p H ρ).ker := by
  ext x
  change gramGroupTransform μ α p H ρ g x = 0 ↔ gramEvaluation μ α p H ρ x = 0
  constructor
  · intro h
    apply norm_eq_zero.mp
    have hn := norm_gramGroupTransform μ α p H ρ g x
    rw [h, norm_zero] at hn
    exact hn.symm
  · intro h
    apply norm_eq_zero.mp
    exact (norm_gramGroupTransform μ α p H ρ g x).trans (by rw [h, norm_zero])

/-- **Coefficient action on the Gram domain.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram domain D is
span_ℂ{T(f)ξ:f∈Carrier μ α,ξ∈E}, with its inherited Hilbert norm; D is dense in E. For a
finitely supported function c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The
coefficient transform C_a(c)=∑(f,ξ) c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ)
c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the same finite formal sums. The bounded complex linear map
gramCoefficientOnDomain μ α p H ρ a:D→E is ev(c)↦C_a(c), with ‖C_a(c)‖≤‖a‖‖ev(c)‖.
-/
def gramCoefficientOnDomain (a : A) :
    (gramEvaluation μ α p H ρ).range →L[ℂ] ρ.essentialSpace :=
  (gramCoefficientTransform μ α p H ρ a).compLeftInverse (gramEvaluation μ α p H ρ)

omit [μ.Regular] in
/-- **Value of the descended Gram coefficient action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. For every finite formal sum c, gramCoefficientOnDomain μ α p H ρ a
(ev(c))=C_a(c), with ev(c) viewed in the evaluation range.
-/
theorem gramCoefficientOnDomain_apply (a : A)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    gramCoefficientOnDomain μ α p H ρ a
      ⟨gramEvaluation μ α p H ρ x, LinearMap.mem_range_self _ x⟩ =
        gramCoefficientTransform μ α p H ρ a x := by
  exact LinearMap.compLeftInverse_apply_of_bdd _ _
    ⟨‖a‖, norm_gramCoefficientTransform_le μ α p H ρ a⟩ x _ rfl

/-- **Extension of the Gram coefficient action to the essential space.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram domain D is
span_ℂ{T(f)ξ:f∈Carrier μ α,ξ∈E}, with its inherited Hilbert norm; D is dense in E. The Gram
coefficient and group operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The bounded complex linear operator gramCoefficientOperator μ
α p H ρ a:E→E is the continuous extension of the coefficient action on D.
-/
def gramCoefficientOperator (a : A) : ρ.essentialSpace →L[ℂ] ρ.essentialSpace :=
  (gramCoefficientTransform μ α p H ρ a).extendOfNorm (gramEvaluation μ α p H ρ)

omit [μ.Regular] in
/-- **Gram coefficient operator on a source generator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a∈A, f∈Carrier μ α and ξ∈E,
gramCoefficientOperator μ α p H ρ a (T(f)ξ)=T(s↦a*f(s))ξ.
-/
theorem gramCoefficientOperator_apply_generator (a : A) (f : Carrier μ α) (ξ : ρ.essentialSpace) :
    gramCoefficientOperator μ α p H ρ a
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
        ρ.essentialRepresentation (p.toNonUnitalCompletion (coefficientLeft μ α a f)) ξ := by
  have h := LinearMap.extendOfNorm_eq (f := gramCoefficientTransform μ α p H ρ a)
    (e := gramEvaluation μ α p H ρ) (denseRange_gramEvaluation μ α p H ρ)
    ⟨‖a‖, norm_gramCoefficientTransform_le μ α p H ρ a⟩ (Finsupp.single (f, ξ) 1)
  simpa only [gramCoefficientOperator, gramCoefficientTransform, gramEvaluation,
    Finsupp.linearCombination_single, one_smul] using h

omit [μ.Regular] in
/-- **Pointwise norm bound for the extended Gram coefficient operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For a∈A and ξ∈E, ‖P_a ξ‖≤‖a‖‖ξ‖.
-/
theorem norm_gramCoefficientOperator_apply_le (a : A) (ξ : ρ.essentialSpace) :
    ‖gramCoefficientOperator μ α p H ρ a ξ‖ ≤ ‖a‖ * ‖ξ‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_gramEvaluation μ α p H ρ) ‖a‖
    (norm_gramCoefficientTransform_le μ α p H ρ a) ξ

omit [μ.Regular] in
/-- **Operator norm bound for the Gram coefficient action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For a∈A, ‖gramCoefficientOperator μ α p H ρ a‖=‖P_a‖≤‖a‖.
-/
theorem opNorm_gramCoefficientOperator_le (a : A) :
    ‖gramCoefficientOperator μ α p H ρ a‖ ≤ ‖a‖ :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_gramEvaluation μ α p H ρ) (norm_nonneg a)
    (norm_gramCoefficientTransform_le μ α p H ρ a)

/-- **Group action on the Gram domain.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram domain D is
span_ℂ{T(f)ξ:f∈Carrier μ α,ξ∈E}, with its inherited Hilbert norm; D is dense in E. For a
finitely supported function c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The
coefficient transform C_a(c)=∑(f,ξ) c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ)
c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the same finite formal sums. The bounded complex linear map
gramGroupOnDomain μ α p H ρ g:D→E sends ev(c) to G_g(c).
-/
def gramGroupOnDomain (g : G) :
    (gramEvaluation μ α p H ρ).range →L[ℂ] ρ.essentialSpace :=
  (gramGroupTransform μ α p H ρ g).compLeftInverse (gramEvaluation μ α p H ρ)

/-- **Value of the descended Gram group action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For a finitely supported function
c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The coefficient transform C_a(c)=∑(f,ξ)
c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ) c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the
same finite formal sums. For every finite formal sum c, gramGroupOnDomain μ α p H ρ g
(ev(c))=G_g(c), with ev(c) viewed in the evaluation range.
-/
theorem gramGroupOnDomain_apply (g : G)
    (x : (Carrier μ α × ρ.essentialSpace) →₀ ℂ) :
    gramGroupOnDomain μ α p H ρ g
      ⟨gramEvaluation μ α p H ρ x, LinearMap.mem_range_self _ x⟩ =
        gramGroupTransform μ α p H ρ g x := by
  exact LinearMap.compLeftInverse_apply_of_bdd _ _
    ⟨1, fun z => by simpa only [one_mul] using (norm_gramGroupTransform μ α p H ρ g z).le⟩ x _ rfl

/-- **Isometry on the Gram domain.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram domain D is
span_ℂ{T(f)ξ:f∈Carrier μ α,ξ∈E}, with its inherited Hilbert norm; D is dense in E. For a
finitely supported function c:(Carrier μ α×E)→₀ℂ, put ev(c)=∑(f,ξ) c(f,ξ)•T(f)ξ. The
coefficient transform C_a(c)=∑(f,ξ) c(f,ξ)•T(s↦a*f(s))ξ and group transform G_g(c)=∑(f,ξ)
c(f,ξ)•T(s↦α_g(f(g⁻¹*s)))ξ act on the same finite formal sums. For x∈D, ‖gramGroupOnDomain μ α
p H ρ g x‖=‖x‖.
-/
theorem norm_gramGroupOnDomain_apply (g : G) (x : (gramEvaluation μ α p H ρ).range) :
    ‖gramGroupOnDomain μ α p H ρ g x‖ = ‖x‖ := by
  rcases x with ⟨y, ⟨z, hz⟩⟩
  subst y
  rw [gramGroupOnDomain_apply]
  exact norm_gramGroupTransform μ α p H ρ g z

/-- **Extended Gram group isometry.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram domain D is
span_ℂ{T(f)ξ:f∈Carrier μ α,ξ∈E}, with its inherited Hilbert norm; D is dense in E. The Gram
coefficient and group operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The complex linear isometry gramGroupIsometry μ α p H ρ g:E→E
extends the group action on D and sends T(f)ξ to T(s↦α_g(f(g⁻¹*s)))ξ.
-/
def gramGroupIsometry (g : G) : ρ.essentialSpace →ₗᵢ[ℂ] ρ.essentialSpace :=
  (gramGroupTransform μ α p H ρ g).extendOfIsometry
    (e := gramEvaluation μ α p H ρ) (denseRange_gramEvaluation μ α p H ρ)
    (norm_gramGroupTransform μ α p H ρ g)

/-- **Bounded operator underlying the Gram group isometry.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The bounded complex linear operator gramGroupOperator μ α p H
ρ g is the isometry gramGroupIsometry μ α p H ρ g viewed as U_g:E→E.
-/
def gramGroupOperator (g : G) : ρ.essentialSpace →L[ℂ] ρ.essentialSpace :=
  (gramGroupIsometry μ α p H ρ g).toContinuousLinearMap

/-- **Gram group operator on a source generator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. For g∈G, f∈Carrier μ α and ξ∈E,
gramGroupOperator μ α p H ρ g (T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ.
-/
theorem gramGroupOperator_apply_generator (g : G) (f : Carrier μ α) (ξ : ρ.essentialSpace) :
    gramGroupOperator μ α p H ρ g
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
        ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g f)) ξ := by
  change (gramGroupIsometry μ α p H ρ g).toContinuousLinearMap
    (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) = _
  rw [gramGroupIsometry, LinearMap.toContinuousLinearMap_extendOfIsometry]
  have h := LinearMap.extendOfNorm_eq (f := gramGroupTransform μ α p H ρ g)
    (e := gramEvaluation μ α p H ρ) (denseRange_gramEvaluation μ α p H ρ)
    ⟨1, fun x => by simpa only [one_mul] using (norm_gramGroupTransform μ α p H ρ g x).le⟩
    (Finsupp.single (f, ξ) 1)
  simpa only [gramGroupTransform, gramEvaluation, Finsupp.linearCombination_single, one_smul] using h

/-- **Norm preservation of the extended Gram group action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G and ξ∈E, ‖gramGroupOperator μ α p H ρ g ξ‖=‖ξ‖.
-/
theorem norm_gramGroupOperator_apply (g : G) (ξ : ρ.essentialSpace) :
    ‖gramGroupOperator μ α p H ρ g ξ‖ = ‖ξ‖ :=
  (gramGroupIsometry μ α p H ρ g).norm_map ξ

end

end HaarTwistedCore
