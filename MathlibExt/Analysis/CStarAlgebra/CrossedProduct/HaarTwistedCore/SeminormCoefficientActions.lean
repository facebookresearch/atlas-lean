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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MultiplierActions
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import MathlibExt.Analysis.CStarAlgebra.SquareComplement
public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Coefficient bounds in C-star seminorms

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on the twisted core and a∈A, the coefficient actions L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a)
satisfy p(L_a f)≤‖a‖p(f) and p(R_a f)≤‖a‖p(f). The coefficient unitization gives a positive
square complement and a cross-Gram identity for these bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

section UnitizedActions

variable {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) (α : PointNormCStarAction G A)

/-- **Algebra representation by left coefficient multiplication.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The nonunital complex algebra
homomorphism coefficientLeftHom μ α:A→End_ℂ(Carrier μ α) sends a to the linear map L_a
f(s)=a*f(s).
-/
def coefficientLeftHom : A →ₙₐ[ℂ] Module.End ℂ (Carrier μ α) where
  toFun := coefficientLeft μ α
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply ext μ α
    intro s
    simp only [coefficientLeft_apply, zero_mul, LinearMap.zero_apply]
    rfl
  map_add' := coefficientLeft_add μ α
  map_mul' := coefficientLeft_mul μ α
  map_smul' := coefficientLeft_smul μ α

/-- **Unitized left coefficient representation.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The unital complex algebra
homomorphism coefficientLeftUnitization μ α:Unitization ℂ A→End_ℂ(Carrier μ α) sends a
unitized coefficient z=(c,a) to the linear action f↦c•f+L_a f, where L_a f(s)=a*f(s).
-/
def coefficientLeftUnitization : Unitization ℂ A →ₐ[ℂ] Module.End ℂ (Carrier μ α) :=
  (coefficientLeftHom μ α).toAlgHom

/-- **Action of a unitized coefficient.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For z=(c,a)∈Unitization ℂ A and
f∈Carrier μ α, coefficientLeftUnitization μ α z f=c•f+coefficientLeft μ α a f, where
coefficientLeft a f(s)=a*f(s).
-/
@[simp]
theorem coefficientLeftUnitization_apply (a : Unitization ℂ A) (f : Carrier μ α) :
    coefficientLeftUnitization μ α a f = a.fst • f + coefficientLeft μ α a.snd f :=
  rfl

/-- **Pointwise value of the unitized coefficient action.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For z=(c,a)∈Unitization ℂ A,
f∈Carrier μ α and s∈G, coefficientLeftUnitization μ α z f s=c•f(s)+a*f(s).
-/
@[simp]
theorem coefficientLeftUnitization_apply_pointwise
    (a : Unitization ℂ A) (f : Carrier μ α) (s : G) :
    coefficientLeftUnitization μ α a f s = a.fst • f s + a.snd * f s :=
  rfl

/-- **Coefficient inclusion in the unitized action.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a∈A included as
(0,a)∈Unitization ℂ A, coefficientLeftUnitization μ α a=coefficientLeft μ α a, the map
f(s)↦a*f(s).
-/
@[simp]
theorem coefficientLeftUnitization_inr (a : A) :
    coefficientLeftUnitization μ α (a : Unitization ℂ A) = coefficientLeft μ α a := by
  apply LinearMap.ext
  intro f
  simp only [coefficientLeftUnitization_apply, Unitization.fst_inr,
    Unitization.snd_inr, zero_smul, zero_add]

/-- **Real scalars in the unitized coefficient action.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For r∈ℝ and f∈Carrier μ α,
coefficientLeftUnitization μ α (algebraMap ℝ (Unitization ℂ A) r) f=(r:ℂ)•f.
-/
theorem coefficientLeftUnitization_algebraMap (r : ℝ) (f : Carrier μ α) :
    coefficientLeftUnitization μ α (algebraMap ℝ (Unitization ℂ A) r) f = (r : ℂ) • f := by
  change coefficientLeftUnitization μ α (Unitization.inl (r : ℂ)) f = (r : ℂ) • f
  have hzero : coefficientLeft μ α (0 : A) = (0 : Module.End ℂ (Carrier μ α)) :=
    (coefficientLeftHom μ α).map_zero
  simp only [coefficientLeftUnitization_apply, Unitization.fst_inl,
    Unitization.snd_inl, hzero, LinearMap.zero_apply, add_zero]

end UnitizedActions

section SquareComplement

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Positive square complement of a coefficient.**

Let A be a nonunital complex C-star algebra and view a∈A in its complex unitization Ã. The
element b=coefficientSquareComplement a is the positive square root of ‖a‖²1-star(a)*a in Ã.
-/
def coefficientSquareComplement (a : A) : Unitization ℂ A := by
  let : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
  exact CStarAlgebra.normSquareComplement (a : Unitization ℂ A)

/-- **Square complement identity in the coefficient unitization.**

Let A be a nonunital complex C-star algebra, a∈A included in Ã=Unitization ℂ A and
b=coefficientSquareComplement a. Then star(a)*a+star(b)*b=‖a‖²1 in Ã.
-/
theorem coefficientSquareComplement_identity (a : A) :
    star (a : Unitization ℂ A) * (a : Unitization ℂ A) +
      star (coefficientSquareComplement a) * coefficientSquareComplement a =
        algebraMap ℝ (Unitization ℂ A) (‖a‖ ^ 2) := by
  let : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
  simpa only [coefficientSquareComplement, Unitization.norm_inr] using
    CStarAlgebra.star_mul_self_add_normSquareComplement (a : Unitization ℂ A)

end SquareComplement

section OriginalGramIdentities

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (α : PointNormCStarAction G A)

omit [μ.Regular] in
/-- **Star exchange for the unitized coefficient action.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For z∈Unitization ℂ A let L_z
f=z.fst•f+coefficientLeft μ α z.snd f. For core coefficients f,h, star(L_z
f)*h=star(f)*L_star(z) h, where * is twisted convolution.
-/
theorem coefficientLeftUnitization_star_mul (a : Unitization ℂ A) (f h : Carrier μ α) :
    star (coefficientLeftUnitization μ α a f) * h =
      star f * coefficientLeftUnitization μ α (star a) h := by
  have hStar : star (coefficientLeft μ α a.snd f) =
      coefficientRight μ α (star a.snd) (star f) :=
    crossedStar_coefficientLeft μ α a.snd f
  have hCentral : star f * coefficientLeft μ α (star a.snd) h =
      coefficientRight μ α (star a.snd) (star f) * h :=
    convolution_coefficientLeft μ α (star a.snd) (star f) h
  calc
    _ = (star a.fst • star f + coefficientRight μ α (star a.snd) (star f)) * h := by
      rw [coefficientLeftUnitization_apply, star_add, star_smul, hStar]
    _ = star a.fst • (star f * h) + coefficientRight μ α (star a.snd) (star f) * h := by
      rw [add_mul, smul_mul_assoc]
    _ = star a.fst • (star f * h) + star f * coefficientLeft μ α (star a.snd) h := by
      rw [← hCentral]
    _ = star f * (star a.fst • h + coefficientLeft μ α (star a.snd) h) := by
      rw [mul_add, mul_smul_comm]
    _ = _ := by
      rw [coefficientLeftUnitization_apply, Unitization.fst_star, Unitization.snd_star]

omit [μ.Regular] in
/-- **Cross-Gram identity for a coefficient and its square complement.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a∈A put
b=coefficientSquareComplement a, L_a f(s)=a*f(s), and L_b f=b.fst•f+coefficientLeft μ α b.snd
f. For core coefficients f,h, star(L_a f)*L_a h+star(L_b f)*L_b h=‖a‖²•(star(f)*h), with
twisted convolution and the real scalar embedded in ℂ.
-/
theorem coefficientLeft_cross_gram_square (a : A) (f h : Carrier μ α) :
    star (coefficientLeft μ α a f) * coefficientLeft μ α a h +
      star (coefficientLeftUnitization μ α (coefficientSquareComplement a) f) *
        coefficientLeftUnitization μ α (coefficientSquareComplement a) h =
      ((‖a‖ ^ 2 : ℝ) : ℂ) • (star f * h) := by
  let L := coefficientLeftUnitization μ α
  let c := coefficientSquareComplement a
  have hMul (x y : Unitization ℂ A) : L (x * y) h = L x (L y h) :=
    congrArg (fun T : Module.End ℂ (Carrier μ α) => T h) (map_mul L x y)
  have hAdd (x y : Unitization ℂ A) : L (x + y) h = L x h + L y h :=
    congrArg (fun T : Module.End ℂ (Carrier μ α) => T h) (map_add L x y)
  rw [← coefficientLeftUnitization_inr μ α a]
  change star (L (a : Unitization ℂ A) f) * L (a : Unitization ℂ A) h +
    star (L c f) * L c h = _
  calc
    _ = star f * L (star (a : Unitization ℂ A)) (L (a : Unitization ℂ A) h) +
        star f * L (star c) (L c h) := by
      rw [coefficientLeftUnitization_star_mul, coefficientLeftUnitization_star_mul]
    _ = star f * L (star (a : Unitization ℂ A) * (a : Unitization ℂ A)) h +
        star f * L (star c * c) h := by
      rw [← hMul, ← hMul]
    _ = star f * (L (star (a : Unitization ℂ A) * (a : Unitization ℂ A)) h +
        L (star c * c) h) := (mul_add _ _ _).symm
    _ = star f * L (star (a : Unitization ℂ A) * (a : Unitization ℂ A) + star c * c) h := by
      rw [← hAdd]
    _ = star f * L (algebraMap ℝ (Unitization ℂ A) (‖a‖ ^ 2)) h := by
      rw [coefficientSquareComplement_identity]
    _ = _ := by
      rw [coefficientLeftUnitization_algebraMap]
      exact mul_smul_comm _ _ _

omit [μ.Regular] in
/-- **Left coefficient bound in any C-star seminorm.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, a∈A and core coefficient f, p(coefficientLeft μ α a f)≤‖a‖p(f), where coefficientLeft a
f(s)=a*f(s).
-/
theorem seminorm_coefficientLeft_le (p : CStarSeminorm (Carrier μ α)) (a : A) (f : Carrier μ α) :
    p (coefficientLeft μ α a f) ≤ ‖a‖ * p f := by
  let : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let : PartialOrder p.NonUnitalCompletion := CStarAlgebra.spectralOrder _
  let : StarOrderedRing p.NonUnitalCompletion := CStarAlgebra.spectralOrderedRing _
  let q : Carrier μ α →⋆ₙₐ[ℂ] p.NonUnitalCompletion := p.toNonUnitalCompletion
  let F : p.NonUnitalCompletion := q f
  let X : p.NonUnitalCompletion := q (coefficientLeft μ α a f)
  let Y : p.NonUnitalCompletion :=
    q (coefficientLeftUnitization μ α (coefficientSquareComplement a) f)
  have hRaw := coefficientLeft_cross_gram_square μ α a f f
  have hSquare : star X * X + star Y * Y = ((‖a‖ ^ 2 : ℝ) : ℂ) • (star F * F) := by
    have h := congrArg q hRaw
    simpa only [map_add, map_mul, map_smul, map_star, F, X, Y] using h
  have hLe : star X * X ≤ ((‖a‖ ^ 2 : ℝ) : ℂ) • (star F * F) :=
    (le_add_of_nonneg_right (star_mul_self_nonneg Y)).trans_eq hSquare
  have hNorm := CStarAlgebra.norm_le_norm_of_le_of_nonneg hLe (star_mul_self_nonneg X)
  have hr : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  have hSq : ‖X‖ ^ 2 ≤ (‖a‖ * ‖F‖) ^ 2 := by
    calc
      ‖X‖ ^ 2 = ‖star X * X‖ := by rw [CStarRing.norm_star_mul_self, pow_two]
      _ ≤ ‖((‖a‖ ^ 2 : ℝ) : ℂ) • (star F * F)‖ := hNorm
      _ = (‖a‖ * ‖F‖) ^ 2 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
          CStarRing.norm_star_mul_self]
        ring
  have hBound : ‖X‖ ≤ ‖a‖ * ‖F‖ :=
    (sq_le_sq₀ (norm_nonneg X) (mul_nonneg (norm_nonneg a) (norm_nonneg F))).mp hSq
  simpa only [X, F, q, CStarSeminorm.norm_toNonUnitalCompletion] using hBound

omit [μ.Regular] in
/-- **Right coefficient bound in any C-star seminorm.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, a∈A and core coefficient f, p(coefficientRight μ α a f)≤‖a‖p(f), where coefficientRight a
f(s)=f(s)*α_s(a).
-/
theorem seminorm_coefficientRight_le (p : CStarSeminorm (Carrier μ α)) (a : A) (f : Carrier μ α) :
    p (coefficientRight μ α a f) ≤ ‖a‖ * p f := by
  have hStar : star (coefficientRight μ α a f) = coefficientLeft μ α (star a) (star f) :=
    crossedStar_coefficientRight μ α a f
  calc
    p (coefficientRight μ α a f) = p (star (coefficientRight μ α a f)) := (p.map_star _).symm
    _ = p (coefficientLeft μ α (star a) (star f)) := congrArg p hStar
    _ ≤ ‖star a‖ * p (star f) := seminorm_coefficientLeft_le μ α p (star a) (star f)
    _ = ‖a‖ * p f := by rw [norm_star, p.map_star]

end OriginalGramIdentities

end

end HaarTwistedCore
