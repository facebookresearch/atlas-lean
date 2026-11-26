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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.GramOperatorExtension
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Coefficient and unitary laws for Gram operators

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The map a↦P_a is a nonunital complex star homomorphism. The
map g↦U_g is a unitary group homomorphism, with star(U_g)=U_(g⁻¹). Their covariance is
U_g*P_a*star(U_g)=P_(α_g(a)).
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

omit [μ.Regular] in
/-- **Gram generators determine a bounded operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. If bounded complex linear operators
Q,S:E→E satisfy Q(T(f)ξ)=S(T(f)ξ) for every core coefficient f and ξ∈E, then Q=S.
-/
theorem gramOperator_ext (T S : ρ.essentialSpace →L[ℂ] ρ.essentialSpace)
    (h : ∀ (f : Carrier μ α) (ξ : ρ.essentialSpace),
      T (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
        S (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)) : T = S := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (p.dense_rawHilbertGramDomain H ρ).induction ?_
    (isClosed_eq T.continuous S.continuous) ξ
  intro η hη
  exact LinearMap.eqOn_span (f := T.toLinearMap) (g := S.toLinearMap)
    (by rintro _ ⟨⟨f, ζ⟩, rfl⟩; exact h f ζ) hη

omit [μ.Regular] in
/-- **Gram generator inner products determine an adjoint.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. Let Q,S:E→E be bounded complex linear
operators. If ⟪Q(T(f)ξ),T(k)η⟫_ℂ=⟪T(f)ξ,S(T(k)η)⟫_ℂ for all core coefficients f,k and ξ,η∈E,
then Q=star(S), the operator adjoint of S.
-/
theorem gramOperator_eq_star_of_inner_generators
    (T S : ρ.essentialSpace →L[ℂ] ρ.essentialSpace)
    (h : ∀ (f k : Carrier μ α) (ξ η : ρ.essentialSpace),
      ⟪T (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ),
        ρ.essentialRepresentation (p.toNonUnitalCompletion k) η⟫_ℂ =
      ⟪ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ,
        S (ρ.essentialRepresentation (p.toNonUnitalCompletion k) η)⟫_ℂ) :
    T = star S := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff T S).mpr
  intro ξ η
  refine (denseRange_gramEvaluation μ α p H ρ).induction_on₂
    (isClosed_eq ((T.continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner (S.continuous.comp continuous_snd))) ?_ ξ η
  intro x y
  simp only [gramEvaluation, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z : ℂ => y i * z)
  apply Finset.sum_congr rfl
  intro j _
  rw [h j.1 i.1 j.2 i.2]

omit [μ.Regular] in
/-- **Zero in the Gram coefficient representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The zero coefficient acts by P_0=0.
-/
theorem gramCoefficientOperator_zero :
    gramCoefficientOperator μ α p H ρ (0 : A) = 0 := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  rw [gramCoefficientOperator_apply_generator]
  have hzero : coefficientLeft μ α (0 : A) f = 0 :=
    congrArg (fun L : Module.End ℂ (Carrier μ α) => L f) (map_zero (coefficientLeftHom μ α))
  rw [hzero, map_zero, map_zero]
  rfl

omit [μ.Regular] in
/-- **Additivity of Gram coefficient operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For a,b∈A, P_(a+b)=P_a+P_b.
-/
theorem gramCoefficientOperator_add (a b : A) :
    gramCoefficientOperator μ α p H ρ (a + b) =
      gramCoefficientOperator μ α p H ρ a + gramCoefficientOperator μ α p H ρ b := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramCoefficientOperator μ α p H ρ (a + b)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    gramCoefficientOperator μ α p H ρ a
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) +
      gramCoefficientOperator μ α p H ρ b
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator,
    gramCoefficientOperator_apply_generator, coefficientLeft_add, LinearMap.add_apply,
    map_add, map_add]
  rfl

omit [μ.Regular] in
/-- **Complex scaling of Gram coefficient operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For c∈ℂ and a∈A, P_(c•a)=c•P_a.
-/
theorem gramCoefficientOperator_smul (c : ℂ) (a : A) :
    gramCoefficientOperator μ α p H ρ (c • a) = c • gramCoefficientOperator μ α p H ρ a := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramCoefficientOperator μ α p H ρ (c • a)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    c • gramCoefficientOperator μ α p H ρ a
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator,
    coefficientLeft_smul, LinearMap.smul_apply, map_smul, map_smul]
  rfl

omit [μ.Regular] in
/-- **Multiplication of Gram coefficient operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For a,b∈A, P_(a*b)=P_a*P_b, with operator composition on E.
-/
theorem gramCoefficientOperator_mul (a b : A) :
    gramCoefficientOperator μ α p H ρ (a * b) =
      gramCoefficientOperator μ α p H ρ a * gramCoefficientOperator μ α p H ρ b := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramCoefficientOperator μ α p H ρ (a * b)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    gramCoefficientOperator μ α p H ρ a
      (gramCoefficientOperator μ α p H ρ b
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ))
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator,
    gramCoefficientOperator_apply_generator, coefficientLeft_mul, LinearMap.comp_apply]

omit [μ.Regular] in
/-- **Adjoint of a Gram coefficient operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For a∈A, P_star(a)=star(P_a).
-/
theorem gramCoefficientOperator_star (a : A) :
    gramCoefficientOperator μ α p H ρ (star a) = star (gramCoefficientOperator μ α p H ρ a) := by
  apply gramOperator_eq_star_of_inner_generators μ α p H ρ
  intro f h ξ η
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator]
  have hGram (u v : Carrier μ α) :
      ⟪ρ.essentialRepresentation (p.toNonUnitalCompletion u) ξ,
        ρ.essentialRepresentation (p.toNonUnitalCompletion v) η⟫_ℂ =
      ⟪ξ, ρ.essentialRepresentation (p.toNonUnitalCompletion (star u * v)) η⟫_ℂ := by
    exact p.rawHilbertGramGenerator_inner H ρ u v ξ η
  rw [hGram, hGram]
  have hStar : star (coefficientLeft μ α (star a) f) =
      coefficientRight μ α a (star f) := by
    change crossedStar μ α (coefficientLeft μ α (star a) f) =
      coefficientRight μ α a (crossedStar μ α f)
    simpa only [star_star] using crossedStar_coefficientLeft μ α (star a) f
  have hRaw : star (coefficientLeft μ α (star a) f) * h =
      star f * coefficientLeft μ α a h := by
    rw [hStar]
    exact (convolution_coefficientLeft μ α a (star f) h).symm
  rw [hRaw]

/-- **Gram coefficient star representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The nonunital complex star homomorphism
gramCoefficientRepresentation μ α p H ρ:A→B(E) is the map a↦P_a.
-/
def gramCoefficientRepresentation : A →⋆ₙₐ[ℂ] (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) where
  toFun := gramCoefficientOperator μ α p H ρ
  map_zero' := gramCoefficientOperator_zero μ α p H ρ
  map_add' := gramCoefficientOperator_add μ α p H ρ
  map_smul' := gramCoefficientOperator_smul μ α p H ρ
  map_mul' := gramCoefficientOperator_mul μ α p H ρ
  map_star' := gramCoefficientOperator_star μ α p H ρ

omit [μ.Regular] in
/-- **Value of the Gram coefficient representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For a∈A, gramCoefficientRepresentation μ α p H ρ
a=gramCoefficientOperator μ α p H ρ a=P_a.
-/
@[simp]
theorem gramCoefficientRepresentation_apply (a : A) :
    gramCoefficientRepresentation μ α p H ρ a = gramCoefficientOperator μ α p H ρ a := rfl

/-- **Identity in the Gram group action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The group identity acts as U_1=1, the identity operator on E.
-/
theorem gramGroupOperator_one : gramGroupOperator μ α p H ρ (1 : G) = 1 := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  rw [gramGroupOperator_apply_generator, groupLeft_one, LinearMap.id_apply]
  rfl

/-- **Multiplication in the Gram group action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g,h∈G, U_(g*h)=U_g*U_h.
-/
theorem gramGroupOperator_mul (g h : G) :
    gramGroupOperator μ α p H ρ (g * h) =
      gramGroupOperator μ α p H ρ g * gramGroupOperator μ α p H ρ h := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramGroupOperator μ α p H ρ (g * h)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    gramGroupOperator μ α p H ρ g
      (gramGroupOperator μ α p H ρ h
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ))
  rw [gramGroupOperator_apply_generator, gramGroupOperator_apply_generator,
    gramGroupOperator_apply_generator, groupLeft_mul, LinearMap.comp_apply]

/-- **Right inverse of a Gram group operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G, U_g*U_(g⁻¹)=1 on E.
-/
theorem gramGroupOperator_mul_inv (g : G) :
    gramGroupOperator μ α p H ρ g * gramGroupOperator μ α p H ρ g⁻¹ = 1 := by
  rw [← gramGroupOperator_mul, mul_inv_cancel, gramGroupOperator_one]

/-- **Left inverse of a Gram group operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G, U_(g⁻¹)*U_g=1 on E.
-/
theorem gramGroupOperator_inv_mul (g : G) :
    gramGroupOperator μ α p H ρ g⁻¹ * gramGroupOperator μ α p H ρ g = 1 := by
  rw [← gramGroupOperator_mul, inv_mul_cancel, gramGroupOperator_one]

/-- **Adjoint is a left inverse of a Gram group operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G, star(U_g)*U_g=1 on E.
-/
theorem gramGroupOperator_star_mul_self (g : G) :
    star (gramGroupOperator μ α p H ρ g) * gramGroupOperator μ α p H ρ g = 1 := by
  change (gramGroupOperator μ α p H ρ g).adjoint.comp (gramGroupOperator μ α p H ρ g) = 1
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
    (norm_gramGroupOperator_apply μ α p H ρ g)

/-- **Adjoint of a Gram group operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G, star(U_g)=U_(g⁻¹).
-/
theorem gramGroupOperator_star (g : G) :
    star (gramGroupOperator μ α p H ρ g) = gramGroupOperator μ α p H ρ g⁻¹ := by
  calc
    _ = star (gramGroupOperator μ α p H ρ g) * 1 := (mul_one _).symm
    _ = star (gramGroupOperator μ α p H ρ g) *
        (gramGroupOperator μ α p H ρ g * gramGroupOperator μ α p H ρ g⁻¹) := by
      rw [gramGroupOperator_mul_inv]
    _ = (star (gramGroupOperator μ α p H ρ g) * gramGroupOperator μ α p H ρ g) *
        gramGroupOperator μ α p H ρ g⁻¹ := (mul_assoc _ _ _).symm
    _ = gramGroupOperator μ α p H ρ g⁻¹ := by rw [gramGroupOperator_star_mul_self, one_mul]

/-- **Unitarity of a Gram group operator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G, U_g is a unitary operator on E:
star(U_g)*U_g=U_g*star(U_g)=1.
-/
theorem gramGroupOperator_mem_unitary (g : G) :
    gramGroupOperator μ α p H ρ g ∈ unitary (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) := by
  exact ⟨gramGroupOperator_star_mul_self μ α p H ρ g,
    by rw [gramGroupOperator_star, gramGroupOperator_mul_inv]⟩

/-- **Unitary group representation from Gram operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The group homomorphism gramGroupUnitaryRepresentation μ α p H
ρ:G→unitary(B(E)) sends g to U_g.
-/
def gramGroupUnitaryRepresentation : G →* unitary (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) where
  toFun g := ⟨gramGroupOperator μ α p H ρ g, gramGroupOperator_mem_unitary μ α p H ρ g⟩
  map_one' := Subtype.ext (gramGroupOperator_one μ α p H ρ)
  map_mul' g h := Subtype.ext (gramGroupOperator_mul μ α p H ρ g h)

/-- **Operator underlying the Gram unitary representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G, the bounded operator underlying
gramGroupUnitaryRepresentation μ α p H ρ g equals gramGroupOperator μ α p H ρ g=U_g.
-/
@[simp]
theorem gramGroupUnitaryRepresentation_apply_coe (g : G) :
    (gramGroupUnitaryRepresentation μ α p H ρ g : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) =
      gramGroupOperator μ α p H ρ g := rfl

/-- **Covariance of Gram group and coefficient operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G and a∈A, U_g*P_a=P_(α_g(a))*U_g.
-/
theorem gramGroupOperator_mul_coefficient (g : G) (a : A) :
    gramGroupOperator μ α p H ρ g * gramCoefficientOperator μ α p H ρ a =
      gramCoefficientOperator μ α p H ρ (α g a) * gramGroupOperator μ α p H ρ g := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramGroupOperator μ α p H ρ g
      (gramCoefficientOperator μ α p H ρ a
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)) =
    gramCoefficientOperator μ α p H ρ (α g a)
      (gramGroupOperator μ α p H ρ g
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ))
  rw [gramCoefficientOperator_apply_generator, gramGroupOperator_apply_generator,
    gramGroupOperator_apply_generator, gramCoefficientOperator_apply_generator]
  have hRaw := congrArg (fun L : Module.End ℂ (Carrier μ α) => L f)
    (groupLeft_coefficientLeft μ α g a)
  change groupLeft μ α g (coefficientLeft μ α a f) =
    coefficientLeft μ α (α g a) (groupLeft μ α g f) at hRaw
  rw [hRaw]

/-- **Conjugation covariance of the Gram representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action. Let p be any C-star seminorm on
the twisted core, Xp its separated completion, ιp its dense map, H a complex Hilbert space and
ρ:Xp→B(H) a nonunital complex star homomorphism. Write E for the essential Hilbert subspace of
ρ and T(f)=ρE(ιp(f)) for its restricted operator on E. The Gram coefficient and group
operators P_a,U_g on E are determined by P_a(T(f)ξ)=T(s↦a*f(s))ξ and
U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For g∈G and a∈A, U_g*P_a*star(U_g)=P_(α_g(a)), with
coefficient map gramCoefficientRepresentation and group map gramGroupUnitaryRepresentation.
-/
theorem gramRepresentation_covariance (g : G) (a : A) :
    (gramGroupUnitaryRepresentation μ α p H ρ g : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) *
        gramCoefficientRepresentation μ α p H ρ a *
        star (gramGroupUnitaryRepresentation μ α p H ρ g : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) =
      gramCoefficientRepresentation μ α p H ρ (α g a) := by
  change gramGroupOperator μ α p H ρ g * gramCoefficientOperator μ α p H ρ a *
    star (gramGroupOperator μ α p H ρ g) = gramCoefficientOperator μ α p H ρ (α g a)
  rw [gramGroupOperator_mul_coefficient, mul_assoc, gramGroupOperator_star,
    gramGroupOperator_mul_inv, mul_one]

end

end HaarTwistedCore
