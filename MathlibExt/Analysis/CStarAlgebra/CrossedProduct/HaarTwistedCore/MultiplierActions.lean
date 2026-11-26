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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.StarRing
public import MathlibExt.MeasureTheory.Group.HaarWeightedInversion
public import Mathlib.Topology.ContinuousMap.CocompactMap
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Coefficient and group actions on the twisted convolution core

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients f,
define L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For core coefficients f, define L_g
f(s)=α_g(f(g⁻¹*s)) and R_g f(s)=δ(g)•f(s*g⁻¹), where δ(g)=Measure.modularCharacter g is
embedded in ℂ. These are complex-linear actions on compactly supported continuous
coefficients. They satisfy the covariance and star-exchange identities and the convolution
centralizer equations (R_a f)*h=f*(L_a h) and (R_g f)*h=f*(L_g h).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open scoped CompactlySupported Pointwise NNReal CStarAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

section CoefficientCc

variable {G : Type uG} [TopologicalSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Left coefficient action on compactly supported functions.**

Let G be a topological space and A a nonunital complex C-star algebra. For a∈A,
coefficientLeftCc a is the complex linear map C_c(G,A)→C_c(G,A) given by f(s)↦a*f(s).
-/
def coefficientLeftCc (a : A) : C_c(G, A) →ₗ[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := a * f s
      continuous_toFun := continuous_const.mul (map_continuous f)
      hasCompactSupport' := f.hasCompactSupport.mul_left }
  map_add' f h := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change a * (f s + h s) = a * f s + a * h s
    exact mul_add _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change a * (c • f s) = c • (a * f s)
    exact mul_smul_comm _ _ _

/-- **Pointwise value of left coefficient multiplication.**

Let G be a topological space, A a nonunital complex C-star algebra, a∈A, f∈C_c(G,A) and s∈G.
Then coefficientLeftCc a f s=a*f(s).
-/
@[simp]
theorem coefficientLeftCc_apply (a : A) (f : C_c(G, A)) (s : G) :
    coefficientLeftCc a f s = a * f s := rfl

section Monoid

variable [Monoid G] (α : PointNormCStarAction G A)

/-- **Action-valued right coefficient multiplication.**

Let G be a monoid with a topology, A a nonunital complex C-star algebra and α a point-norm
action. For a∈A, coefficientRightCc α a:C_c(G,A)→ₗ[ℂ]C_c(G,A) sends f to s↦f(s)*α_s(a).
-/
def coefficientRightCc (a : A) : C_c(G, A) →ₗ[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := f s * α s a
      continuous_toFun := (map_continuous f).mul
        (α.continuous_apply continuous_id continuous_const)
      hasCompactSupport' := f.hasCompactSupport.mul_right }
  map_add' f h := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change (f s + h s) * α s a = f s * α s a + h s * α s a
    exact add_mul _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change (c • f s) * α s a = c • (f s * α s a)
    exact smul_mul_assoc _ _ _

/-- **Pointwise value of right coefficient multiplication.**

Let G be a monoid with a topology, A a nonunital complex C-star algebra and α a point-norm
action. For a∈A, f∈C_c(G,A) and s∈G, coefficientRightCc α a f s=f(s)*α_s(a).
-/
@[simp]
theorem coefficientRightCc_apply (a : A) (f : C_c(G, A)) (s : G) :
    coefficientRightCc α a f s = f s * α s a := rfl

end Monoid
end CoefficientCc

section GroupCc

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Left group translation of compact coefficients.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. For g∈G, groupLeftCc α g:C_c(G,A)→ₗ[ℂ]C_c(G,A) sends f to
s↦α_g(f(g⁻¹*s)).
-/
def groupLeftCc (α : PointNormCStarAction G A) (g : G) : C_c(G, A) →ₗ[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := α g (f (g⁻¹ * s))
      continuous_toFun := α.continuous_apply continuous_const
        ((map_continuous f).comp (continuous_const.mul continuous_id))
      hasCompactSupport' :=
        (f.comp (Homeomorph.mulLeft g⁻¹).toCocompactMap).hasCompactSupport.comp_left
          (α.apply_zero g) }
  map_add' f h := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change α g (f (g⁻¹ * s) + h (g⁻¹ * s)) =
      α g (f (g⁻¹ * s)) + α g (h (g⁻¹ * s))
    exact α.apply_add _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change α g (c • f (g⁻¹ * s)) = c • α g (f (g⁻¹ * s))
    exact α.apply_smul _ _ _

omit [LocallyCompactSpace G] in
/-- **Pointwise value of the left compact group translate.**

Let G be a topological group, A a nonunital complex C-star algebra and α a point-norm action.
For g,s∈G and f∈C_c(G,A), groupLeftCc α g f s=α_g(f(g⁻¹*s)).
-/
@[simp]
theorem groupLeftCc_apply (α : PointNormCStarAction G A) (g : G) (f : C_c(G, A)) (s : G) :
    groupLeftCc α g f s = α g (f (g⁻¹ * s)) := rfl

/-- **Modular right translation of compact coefficients.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. For g∈G, groupRightCc g:C_c(G,A)→ₗ[ℂ]C_c(G,A) sends f to
s↦δ(g)•f(s*g⁻¹), where δ(g)=Measure.modularCharacter g is embedded in ℂ.
-/
def groupRightCc (g : G) : C_c(G, A) →ₗ[ℂ] C_c(G, A) :=
  ((Measure.modularCharacter g : ℝ) : ℂ) •
    CompactlySupportedContinuousMap.compLinearMap (R := ℂ) (Homeomorph.mulRight g⁻¹).toCocompactMap

/-- **Pointwise value of the modular compact right translate.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. For g,s∈G and f∈C_c(G,A), groupRightCc g f
s=((Measure.modularCharacter g:ℝ):ℂ)•f(s*g⁻¹).
-/
@[simp]
theorem groupRightCc_apply (g : G) (f : C_c(G, A)) (s : G) :
    groupRightCc g f s = ((Measure.modularCharacter g : ℝ) : ℂ) • f (s * g⁻¹) := rfl

end GroupCc

section CoreCoefficient

variable {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- **Left coefficient action on the indexed core.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The complex linear map
coefficientLeft μ α a:Carrier μ α→Carrier μ α sends f to s↦a*f(s).
-/
def coefficientLeft (a : A) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (coefficientLeftCc a (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change coefficientLeftCc a (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (coefficientLeftCc a (toCc μ α f)) +
        fromCc μ α (coefficientLeftCc a (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change coefficientLeftCc a (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (coefficientLeftCc a (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

/-- **Left coefficient value on the indexed core.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a∈A, f∈Carrier μ α and s∈G,
coefficientLeft μ α a f s=a*f(s).
-/
@[simp]
theorem coefficientLeft_apply (a : A) (f : Carrier μ α) (s : G) :
    coefficientLeft μ α a f s = a * f s := rfl

/-- **Right coefficient action on the indexed core.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The complex linear map
coefficientRight μ α a:Carrier μ α→Carrier μ α sends f to s↦f(s)*α_s(a).
-/
def coefficientRight (a : A) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (coefficientRightCc α a (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change coefficientRightCc α a (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (coefficientRightCc α a (toCc μ α f)) +
        fromCc μ α (coefficientRightCc α a (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change coefficientRightCc α a (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (coefficientRightCc α a (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

/-- **Right coefficient value on the indexed core.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a∈A, f∈Carrier μ α and s∈G,
coefficientRight μ α a f s=f(s)*α_s(a).
-/
@[simp]
theorem coefficientRight_apply (a : A) (f : Carrier μ α) (s : G) :
    coefficientRight μ α a f s = f s * α s a := rfl

/-- **Composition of left coefficient actions.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For core coefficients f, define
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For a,b∈A, L_(a*b)=L_a∘L_b.
-/
theorem coefficientLeft_mul (a b : A) :
    coefficientLeft μ α (a * b) = (coefficientLeft μ α a).comp (coefficientLeft μ α b) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, coefficientLeft_apply, mul_assoc]

/-- **Reversed composition of right coefficient actions.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For core coefficients f, define
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For a,b∈A, R_(a*b)=R_b∘R_a.
-/
theorem coefficientRight_mul (a b : A) :
    coefficientRight μ α (a * b) = (coefficientRight μ α b).comp (coefficientRight μ α a) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, coefficientRight_apply, α.apply_mul_elem, mul_assoc]

/-- **Additivity in the left coefficient parameter.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For core coefficients f, define
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For a,b∈A, L_(a+b)=L_a+L_b.
-/
theorem coefficientLeft_add (a b : A) :
    coefficientLeft μ α (a + b) = coefficientLeft μ α a + coefficientLeft μ α b := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.add_apply, coefficientLeft_apply, toCc_add,
    CompactlySupportedContinuousMap.add_apply, add_mul]

/-- **Additivity in the right coefficient parameter.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For core coefficients f, define
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For a,b∈A, R_(a+b)=R_a+R_b.
-/
theorem coefficientRight_add (a b : A) :
    coefficientRight μ α (a + b) = coefficientRight μ α a + coefficientRight μ α b := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.add_apply, coefficientRight_apply, toCc_add,
    CompactlySupportedContinuousMap.add_apply, α.apply_add, mul_add]

/-- **Complex scaling in the left coefficient parameter.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For core coefficients f, define
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For c∈ℂ and a∈A, L_(c•a)=c•L_a.
-/
theorem coefficientLeft_smul (c : ℂ) (a : A) :
    coefficientLeft μ α (c • a) = c • coefficientLeft μ α a := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.smul_apply, coefficientLeft_apply, toCc_smul,
    CompactlySupportedContinuousMap.smul_apply, smul_mul_assoc]

/-- **Complex scaling in the right coefficient parameter.**

Let G be a group with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For core coefficients f, define
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For c∈ℂ and a∈A, R_(c•a)=c•R_a.
-/
theorem coefficientRight_smul (c : ℂ) (a : A) :
    coefficientRight μ α (c • a) = c • coefficientRight μ α a := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.smul_apply, coefficientRight_apply, toCc_smul,
    CompactlySupportedContinuousMap.smul_apply, α.apply_smul, mul_smul_comm]

end CoreCoefficient

section CoreGroup

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- **Left group action on the indexed core.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. The complex linear map
groupLeft μ α g on Carrier μ α sends f to s↦α_g(f(g⁻¹*s)).
-/
def groupLeft (g : G) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (groupLeftCc α g (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change groupLeftCc α g (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (groupLeftCc α g (toCc μ α f)) +
        fromCc μ α (groupLeftCc α g (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change groupLeftCc α g (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (groupLeftCc α g (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

omit [LocallyCompactSpace G] in
/-- **Left group value on the indexed core.**

Let G be a topological group with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For g,s∈G and f∈Carrier μ α,
groupLeft μ α g f s=α_g(f(g⁻¹*s)).
-/
@[simp]
theorem groupLeft_apply (g : G) (f : Carrier μ α) (s : G) :
    groupLeft μ α g f s = α g (f (g⁻¹ * s)) := rfl

/-- **Modular right group action on the indexed core.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. The complex linear map
groupRight μ α g on Carrier μ α sends f to s↦δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g.
-/
def groupRight (g : G) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (groupRightCc g (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change groupRightCc g (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (groupRightCc g (toCc μ α f)) +
        fromCc μ α (groupRightCc g (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change groupRightCc g (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (groupRightCc g (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

/-- **Modular right group value on the indexed core.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For g,s∈G and
f∈Carrier μ α, groupRight μ α g f s=((Measure.modularCharacter g:ℝ):ℂ)•f(s*g⁻¹).
-/
@[simp]
theorem groupRight_apply (g : G) (f : Carrier μ α) (s : G) :
    groupRight μ α g f s = ((Measure.modularCharacter g : ℝ) : ℂ) • f (s * g⁻¹) := rfl

omit [LocallyCompactSpace G] in
/-- **Identity in the left core group action.**

Let G be a topological group with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For L_g f(s)=α_g(f(g⁻¹*s)), the
identity group element acts by L_1=id on Carrier μ α.
-/
theorem groupLeft_one : groupLeft μ α 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [groupLeft_apply, inv_one, one_mul, α.apply_one, LinearMap.id_apply]

/-- **Identity in the right core group action.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For R_g
f(s)=δ(g)•f(s*g⁻¹), with δ(g)=Measure.modularCharacter g, R_1=id on Carrier μ α.
-/
theorem groupRight_one : groupRight μ α 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [groupRight_apply, map_one, NNReal.coe_one, Complex.ofReal_one,
    inv_one, mul_one, one_smul, LinearMap.id_apply]

omit [LocallyCompactSpace G] in
/-- **Composition of left core group translations.**

Let G be a topological group with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For L_g f(s)=α_g(f(g⁻¹*s)),
L_(g*h)=L_g∘L_h on Carrier μ α.
-/
theorem groupLeft_mul (g h : G) :
    groupLeft μ α (g * h) = (groupLeft μ α g).comp (groupLeft μ α h) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, groupLeft_apply, α.apply_mul, mul_inv_rev, mul_assoc]

/-- **Reversed composition of right core group translations.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For R_g
f(s)=δ(g)•f(s*g⁻¹), with δ(g)=Measure.modularCharacter g, R_(g*h)=R_h∘R_g on Carrier μ α.
-/
theorem groupRight_mul (g h : G) :
    groupRight μ α (g * h) = (groupRight μ α h).comp (groupRight μ α g) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, groupRight_apply, map_mul, NNReal.coe_mul,
    Complex.ofReal_mul, mul_inv_rev, mul_assoc, smul_smul]
  rw [mul_comm (((Measure.modularCharacter g : ℝ) : ℂ))
    (((Measure.modularCharacter h : ℝ) : ℂ))]

omit [LocallyCompactSpace G] in
/-- **Covariance of left core group and coefficient actions.**

Let G be a topological group with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For L_g f(s)=α_g(f(g⁻¹*s)) and L_a
f(s)=a*f(s), L_g∘L_a=L_(α_g(a))∘L_g.
-/
theorem groupLeft_coefficientLeft (g : G) (a : A) :
    (groupLeft μ α g).comp (coefficientLeft μ α a) =
      (coefficientLeft μ α (α g a)).comp (groupLeft μ α g) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, groupLeft_apply, coefficientLeft_apply, α.apply_mul_elem]

/-- **Covariance of right core group and coefficient actions.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For R_a
f(s)=f(s)*α_s(a) and R_g f(s)=δ(g)•f(s*g⁻¹), with δ(g)=Measure.modularCharacter g,
R_a∘R_g=R_g∘R_(α_g(a)).
-/
theorem coefficientRight_groupRight (g : G) (a : A) :
    (coefficientRight μ α a).comp (groupRight μ α g) =
      (groupRight μ α g).comp (coefficientRight μ α (α g a)) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, coefficientRight_apply, groupRight_apply]
  have ha : α (s * g⁻¹) (α g a) = α s a := by
    rw [← α.apply_mul, mul_assoc, inv_mul_cancel, mul_one]
  change (α.aut (s * g⁻¹)) ((α.aut g) a) = (α.aut s) a at ha
  rw [ha, smul_mul_assoc]

end CoreGroup

section CoreStar

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- **Modular star exchanges left and adjoint right coefficients.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f, define L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For the modular star
f⁎(s)=δ(s)•α_s(star(f(s⁻¹))), where δ(s)=Measure.modularCharacter s, (L_a f)⁎=R_star(a)(f⁎).
-/
theorem crossedStar_coefficientLeft (a : A) (f : Carrier μ α) :
    crossedStar μ α (coefficientLeft μ α a f) =
      coefficientRight μ α (star a) (crossedStar μ α f) := by
  apply ext μ α
  intro s
  simp only [crossedStar_apply, coefficientLeft_apply, coefficientRight_apply,
    star_mul, α.apply_mul_elem, smul_mul_assoc]

/-- **Modular star exchanges right and adjoint left coefficients.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f, define L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For the modular star
f⁎(s)=δ(s)•α_s(star(f(s⁻¹))), where δ(s)=Measure.modularCharacter s, (R_a f)⁎=L_star(a)(f⁎).
-/
theorem crossedStar_coefficientRight (a : A) (f : Carrier μ α) :
    crossedStar μ α (coefficientRight μ α a f) =
      coefficientLeft μ α (star a) (crossedStar μ α f) := by
  apply ext μ α
  intro s
  rw [crossedStar_apply, coefficientRight_apply, coefficientLeft_apply, crossedStar_apply]
  rw [star_mul, ← α.apply_star, α.apply_mul_elem, α.apply_apply_inv, mul_smul_comm]

/-- **Modular star exchanges left and inverse right translations.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f, define L_g f(s)=α_g(f(g⁻¹*s)) and R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is embedded in ℂ. For the modular star
f⁎(s)=δ(s)•α_s(star(f(s⁻¹))), (L_g f)⁎=R_(g⁻¹)(f⁎).
-/
theorem crossedStar_groupLeft (g : G) (f : Carrier μ α) :
    crossedStar μ α (groupLeft μ α g f) =
      groupRight μ α g⁻¹ (crossedStar μ α f) := by
  apply ext μ α
  intro s
  have hδ : Measure.modularCharacter g⁻¹ * Measure.modularCharacter (s * g) =
      Measure.modularCharacter s := by
    rw [map_mul, mul_left_comm, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hd : ((Measure.modularCharacter g⁻¹ : ℝ) : ℂ) *
      ((Measure.modularCharacter (s * g) : ℝ) : ℂ) =
        ((Measure.modularCharacter s : ℝ) : ℂ) := by exact_mod_cast hδ
  rw [crossedStar_apply, groupLeft_apply, groupRight_apply, crossedStar_apply, inv_inv]
  rw [← α.apply_star, ← α.apply_mul, mul_inv_rev, smul_smul, hd]

/-- **Modular star exchanges right and inverse left translations.**

Let G be a locally compact topological group with a measurable structure, μ a measure on G, A
a nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f, define L_g f(s)=α_g(f(g⁻¹*s)) and R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is embedded in ℂ. For the modular star
f⁎(s)=δ(s)•α_s(star(f(s⁻¹))), (R_g f)⁎=L_(g⁻¹)(f⁎).
-/
theorem crossedStar_groupRight (g : G) (f : Carrier μ α) :
    crossedStar μ α (groupRight μ α g f) =
      groupLeft μ α g⁻¹ (crossedStar μ α f) := by
  apply ext μ α
  intro s
  have hstar : star ((Measure.modularCharacter g : ℝ) : ℂ) =
      ((Measure.modularCharacter g : ℝ) : ℂ) := by simp
  have hδ : Measure.modularCharacter s * Measure.modularCharacter g =
      Measure.modularCharacter (g * s) := by rw [map_mul, mul_comm]
  have hd : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter g : ℝ) : ℂ) =
        ((Measure.modularCharacter (g * s) : ℝ) : ℂ) := by exact_mod_cast hδ
  rw [crossedStar_apply, groupRight_apply, groupLeft_apply, crossedStar_apply, inv_inv]
  rw [star_smul, hstar, α.apply_smul, α.apply_smul, ← α.apply_mul,
    inv_mul_cancel_left, mul_inv_rev, smul_smul, hd]

end CoreStar

section CoreCompatibility

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Left coefficient action is a convolution left centralizer.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f, define L_a f(s)=a*f(s)
and R_a f(s)=f(s)*α_s(a). For core coefficients f,h, L_a(f*h)=(L_a f)*h, where (f*h)(s)=∫ t,
f(t)*α_t(h(t⁻¹*s)) ∂μ.
-/
theorem coefficientLeft_convolution (a : A) (f h : Carrier μ α) :
    coefficientLeft μ α a (convolution μ α f h) =
      convolution μ α (coefficientLeft μ α a f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [coefficientLeft_apply, convolution_apply, convolution_apply]
  simp_rw [coefficientLeft_apply]
  let L : A →L[ℂ] A := ContinuousLinearMap.mul ℂ A a
  have hL (z : A) : L z = a * z := rfl
  calc
    a * (∫ t : G, f t * α t (h (t⁻¹ * s)) ∂μ) =
        L (∫ t : G, kernel α (toCc μ α f) (toCc μ α h) s t ∂μ) := rfl
    _ = ∫ t : G, L (kernel α (toCc μ α f) (toCc μ α h) s t) ∂μ :=
      (L.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α h) s)).symm
    _ = ∫ t : G, (a * f t) * α t (h (t⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hL, kernel]
      exact (mul_assoc _ _ _).symm

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Right coefficient action is a convolution right centralizer.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f, define L_a f(s)=a*f(s)
and R_a f(s)=f(s)*α_s(a). For core coefficients f,h, R_a(f*h)=f*(R_a h), where * is the μ-Haar
twisted convolution.
-/
theorem coefficientRight_convolution (a : A) (f h : Carrier μ α) :
    coefficientRight μ α a (convolution μ α f h) =
      convolution μ α f (coefficientRight μ α a h) := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [coefficientRight_apply, convolution_apply, convolution_apply]
  simp_rw [coefficientRight_apply]
  let R : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A).flip (α s a)
  have hR (z : A) : R z = z * α s a := rfl
  calc
    (∫ t : G, f t * α t (h (t⁻¹ * s)) ∂μ) * α s a =
        R (∫ t : G, kernel α (toCc μ α f) (toCc μ α h) s t ∂μ) := rfl
    _ = ∫ t : G, R (kernel α (toCc μ α f) (toCc μ α h) s t) ∂μ :=
      (R.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α h) s)).symm
    _ = ∫ t : G, f t * α t (h (t⁻¹ * s) * α (t⁻¹ * s) a) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have ha : α t (α (t⁻¹ * s) a) = α s a := by
        rw [← α.apply_mul, mul_inv_cancel_left]
      rw [hR, kernel]
      change (α.aut t) ((α.aut (t⁻¹ * s)) a) = (α.aut s) a at ha
      rw [map_mul (α.aut t), ha]
      exact mul_assoc _ _ _

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Coefficient actions form a compatible centralizer pair.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f, define L_a f(s)=a*f(s)
and R_a f(s)=f(s)*α_s(a). For core coefficients f,h, f*(L_a h)=(R_a f)*h, where * is twisted
convolution.
-/
theorem convolution_coefficientLeft (a : A) (f h : Carrier μ α) :
    convolution μ α f (coefficientLeft μ α a h) =
      convolution μ α (coefficientRight μ α a f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [convolution_apply, convolution_apply]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [coefficientLeft_apply, coefficientRight_apply, map_mul (α.aut t), mul_assoc]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Left group action is a convolution left centralizer.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For L_g f(s)=α_g(f(g⁻¹*s)) and twisted
convolution *, L_g(f*h)=(L_g f)*h for core coefficients f,h.
-/
theorem groupLeft_convolution (g : G) (f h : Carrier μ α) :
    groupLeft μ α g (convolution μ α f h) =
      convolution μ α (groupLeft μ α g f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [groupLeft_apply, convolution_apply, convolution_apply]
  let T : A →L[ℂ] A :=
    ⟨LinearMap.ofClass (α.aut g), (StarAlgEquiv.isometry (α.aut g)).continuous⟩
  have hT (z : A) : T z = α g z := rfl
  let K : G → A := fun u => α g (f (g⁻¹ * u)) * α u (h (u⁻¹ * s))
  have hPoint (t : G) :
      T (kernel α (toCc μ α f) (toCc μ α h) (g⁻¹ * s) t) = K (g * t) := by
    rw [hT, kernel]
    simp only [K, α.apply_mul_elem, α.apply_mul, inv_mul_cancel_left,
      mul_inv_rev, mul_assoc]
  calc
    α g (∫ t : G, f t * α t (h (t⁻¹ * (g⁻¹ * s))) ∂μ) =
        T (∫ t : G, kernel α (toCc μ α f) (toCc μ α h) (g⁻¹ * s) t ∂μ) := rfl
    _ = ∫ t : G, T (kernel α (toCc μ α f) (toCc μ α h) (g⁻¹ * s) t) ∂μ :=
      (T.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α h) (g⁻¹ * s))).symm
    _ = ∫ t : G, K (g * t) ∂μ := integral_congr_ae (Eventually.of_forall hPoint)
    _ = ∫ u : G, K u ∂μ := integral_mul_left_eq_self (μ := μ) K g
    _ = ∫ u : G, groupLeft μ α g f u * α u (h (u⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [groupLeft_apply]

omit [μ.Regular] in
/-- **Modular right group action is a convolution right centralizer.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action. For R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g, R_g(f*h)=f*(R_g h) for core coefficients f,h and twisted
convolution *.
-/
theorem groupRight_convolution (g : G) (f h : Carrier μ α) :
    groupRight μ α g (convolution μ α f h) =
      convolution μ α f (groupRight μ α g h) := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [groupRight_apply, convolution_apply, convolution_apply]
  calc
    ((Measure.modularCharacter g : ℝ) : ℂ) •
        (∫ t : G, f t * α t (h (t⁻¹ * (s * g⁻¹))) ∂μ) =
      ∫ t : G, ((Measure.modularCharacter g : ℝ) : ℂ) •
        (f t * α t (h (t⁻¹ * (s * g⁻¹)))) ∂μ := (integral_smul _ _).symm
    _ = ∫ t : G, f t * α t (groupRight μ α g h (t⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [groupRight_apply, map_smul (α.aut t), mul_smul_comm, mul_assoc]

/-- **Group translations form a compatible centralizer pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients f,
define L_g f(s)=α_g(f(g⁻¹*s)) and R_g f(s)=δ(g)•f(s*g⁻¹), where δ(g)=Measure.modularCharacter
g is embedded in ℂ. For core coefficients f,h and twisted convolution *, f*(L_g h)=(R_g f)*h.
-/
theorem convolution_groupLeft (g : G) (f h : Carrier μ α) :
    convolution μ α f (groupLeft μ α g h) =
      convolution μ α (groupRight μ α g f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [convolution_apply, convolution_apply]
  let K : G → A := fun u => f (u * g⁻¹) * α u (h (u⁻¹ * s))
  have hPoint (t : G) : f t * α t (groupLeft μ α g h (t⁻¹ * s)) = K (t * g) := by
    rw [groupLeft_apply]
    simp only [K, α.apply_mul, mul_inv_rev, mul_assoc]
    rw [mul_inv_cancel, mul_one]
  calc
    (∫ t : G, f t * α t (groupLeft μ α g h (t⁻¹ * s)) ∂μ) =
        ∫ t : G, K (t * g) ∂μ := integral_congr_ae (Eventually.of_forall hPoint)
    _ = (Measure.modularCharacter g : ℝ) • ∫ u : G, K u ∂μ :=
      MeasureTheory.integral_mul_right_modular μ K g
    _ = ((Measure.modularCharacter g : ℝ) : ℂ) • ∫ u : G, K u ∂μ := rfl
    _ = ∫ u : G, ((Measure.modularCharacter g : ℝ) : ℂ) • K u ∂μ :=
      (integral_smul _ _).symm
    _ = ∫ u : G, groupRight μ α g f u * α u (h (u⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [groupRight_apply, smul_mul_assoc]

end CoreCompatibility

end

end HaarTwistedCore
