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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Uniform
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Completely positive asymptotic morphisms

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. The subclass CompletelyPositiveContraction consists of families
with ‖φ_t(a)‖≤‖a‖ at every time, the CP-contractive specialization used by Blackadar. For
completely positive contraction asymptotic families φ0,φ1:A→B, a homotopy F has slices
A→C([0,1],B) that are completely positive contractions and endpoints F_t(a)(0)=φ0_t(a),
F_t(a)(1)=φ1_t(a). Its asymptotic limits use the supremum norm over the interval.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped CStarAlgebra

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Completely positive time slices.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. The property IsCompletelyPositive φ
means that for every t∈T there is a completely positive complex-linear map s_t:A→B with
s_t(a)=φ_t(a) for all a. Positivity uses the canonical C-star positive cones at every matrix
level.
-/
def IsCompletelyPositive (phi : AsymptoticMorphism A B) : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  ∀ t : AsymptoticTime, ∃ s : A →CP B, ∀ a : A, s a = phi t a

/-- **Asymptotic family with completely positive slices.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. The structure CompletelyPositiveFamily A B consists of such an
asymptotic family and its complete-positivity property.
-/
structure CompletelyPositiveFamily (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    extends AsymptoticMorphism A B where
  /-- **Complete positivity of each slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. The field completelyPositive asserts that every time slice equals
a completely positive complex-linear map A→B for the canonical C-star positive cones.
-/
  completelyPositive : IsCompletelyPositive toAsymptoticMorphism

/-- **Completely positive contractive asymptotic family.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. CompletelyPositiveContraction A B is this class of
asymptotic star morphisms.
-/
structure CompletelyPositiveContraction (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    extends AsymptoticMorphism A B where
  /-- **Contractive complete positivity of each slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. The field completelyPositiveContraction asserts that every
slice is a completely positive complex-linear contraction A→B.
-/
  completelyPositiveContraction :
    IsCompletelyPositiveContraction toAsymptoticMorphism

namespace CompletelyPositiveFamily

@[ext]
theorem ext {phi psi : CompletelyPositiveFamily A B}
    (h : phi.toAsymptoticMorphism = psi.toAsymptoticMorphism) : phi = psi := by
  cases phi
  cases psi
  cases h
  rfl

/-- **Reparametrization of a completely positive family.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For continuous r:T→T with r(t)→∞, the reparametrized family has
slices φ_(r(t)), which remain completely positive.
-/
def reparam (phi : CompletelyPositiveFamily A B)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Tendsto r atTop atTop) : CompletelyPositiveFamily A B where
  toAsymptoticMorphism := phi.toAsymptoticMorphism.reparam r hr hrTop
  completelyPositive := by
    have h := phi.completelyPositive
    dsimp only [IsCompletelyPositive] at h ⊢
    intro t
    exact h (r t)

@[simp]
theorem reparam_apply (phi : CompletelyPositiveFamily A B)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Tendsto r atTop atTop) (t : AsymptoticTime) (a : A) :
    (reparam phi r hr hrTop).toAsymptoticMorphism t a =
      phi.toAsymptoticMorphism (r t) a := by
  rfl

end CompletelyPositiveFamily

namespace CompletelyPositiveContraction

@[ext]
theorem ext {phi psi : CompletelyPositiveContraction A B}
    (h : phi.toAsymptoticMorphism = psi.toAsymptoticMorphism) : phi = psi := by
  cases phi
  cases psi
  cases h
  rfl

/-- **A CP-contractive family as a completely positive family.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. The map toCompletelyPositiveFamily retains the same
asymptotic coefficient values and regards each slice as a completely positive map.
-/
def toCompletelyPositiveFamily (phi : CompletelyPositiveContraction A B) :
    CompletelyPositiveFamily A B where
  toAsymptoticMorphism := phi.toAsymptoticMorphism
  completelyPositive := by
    have h := phi.completelyPositiveContraction
    dsimp only [IsCompletelyPositiveContraction] at h
    dsimp only [IsCompletelyPositive]
    intro t
    obtain ⟨s, _, hs⟩ := h t
    exact ⟨s, hs⟩

@[simp]
theorem toCompletelyPositiveFamily_toAsymptoticMorphism
    (phi : CompletelyPositiveContraction A B) :
    (toCompletelyPositiveFamily phi).toAsymptoticMorphism =
      phi.toAsymptoticMorphism := by
  rfl

/-- **Constant CP-contractive family of a star homomorphism.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A nonunital complex star
homomorphism f:A→B gives CompletelyPositiveContraction.ofHom f with values φ_t(a)=f(a), each
slice being completely positive and contractive.
-/
def ofHom (f : A →⋆ₙₐ[ℂ] B) : CompletelyPositiveContraction A B where
  toAsymptoticMorphism := AsymptoticMorphism.ofHom f
  completelyPositiveContraction := by
    let : PartialOrder A := CStarAlgebra.spectralOrder A
    let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    let : PartialOrder B := CStarAlgebra.spectralOrder B
    let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    let s : A →CP B :=
      CompletelyPositiveMapClass.toCompletelyPositiveLinearMap f
    change ∀ t : AsymptoticTime, ∃ s : A →CP B,
      (∀ a : A, ‖s a‖ ≤ ‖a‖) ∧ ∀ a : A, s a = AsymptoticMorphism.ofHom f t a
    intro t
    exact ⟨s, NonUnitalStarAlgHom.norm_apply_le f, fun _ => rfl⟩

@[simp]
theorem ofHom_apply (f : A →⋆ₙₐ[ℂ] B)
    (t : AsymptoticTime) (a : A) :
    (ofHom f).toAsymptoticMorphism t a = f a := by
  rfl

/-- **Point-norm homomorphism family as CP-contractive asymptotic morphism.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). Suppose f_t:A→B are nonunital
complex star homomorphisms and t↦f_t(a) is continuous for every a.
CompletelyPositiveContraction.ofHomFamily f hf has values φ_t(a)=f_t(a), with completely
positive contraction slices.
-/
def ofHomFamily (f : AsymptoticTime → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a : A, Continuous fun t => f t a) :
    CompletelyPositiveContraction A B where
  toAsymptoticMorphism := AsymptoticMorphism.ofHomFamily f hf
  completelyPositiveContraction := by
    let _ : PartialOrder A := CStarAlgebra.spectralOrder A
    let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    let _ : PartialOrder B := CStarAlgebra.spectralOrder B
    let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    change ∀ t : AsymptoticTime, ∃ s : A →CP B,
      (∀ a : A, ‖s a‖ ≤ ‖a‖) ∧
        ∀ a : A, s a = AsymptoticMorphism.ofHomFamily f hf t a
    intro t
    let s : A →CP B :=
      CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (f t)
    exact ⟨s, NonUnitalStarAlgHom.norm_apply_le (f t), fun _ => rfl⟩

/-- **Underlying asymptotic morphism of a homomorphism family.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). For nonunital complex star
homomorphisms f_t:A→B with continuous orbits t↦f_t(a), the underlying family of
CompletelyPositiveContraction.ofHomFamily f hf equals AsymptoticMorphism.ofHomFamily f hf.
-/
@[simp]
theorem ofHomFamily_toAsymptoticMorphism
    (f : AsymptoticTime → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a : A, Continuous fun t => f t a) :
    (ofHomFamily f hf).toAsymptoticMorphism =
      AsymptoticMorphism.ofHomFamily f hf :=
  rfl

/-- **Value of the CP-contractive homomorphism-family construction.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). For nonunital complex star
homomorphisms f_t:A→B with continuous coefficient orbits,
CompletelyPositiveContraction.ofHomFamily f hf has φ_t(a)=f_t(a) for t≥1.
-/
theorem ofHomFamily_apply (f : AsymptoticTime → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a : A, Continuous fun t => f t a)
    (t : AsymptoticTime) (a : A) :
    (ofHomFamily f hf).toAsymptoticMorphism t a = f t a :=
  rfl

/-- **Reparametrization preserves completely positive contractions.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For continuous r:T→T with r(t)→∞, reparam φ r has slices
φ_(r(t)) and retains ‖φ_(r(t))(a)‖≤‖a‖.
-/
def reparam (phi : CompletelyPositiveContraction A B)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Tendsto r atTop atTop) : CompletelyPositiveContraction A B where
  toAsymptoticMorphism := phi.toAsymptoticMorphism.reparam r hr hrTop
  completelyPositiveContraction := by
    have h := phi.completelyPositiveContraction
    dsimp only [IsCompletelyPositiveContraction] at h ⊢
    intro t
    exact h (r t)

@[simp]
theorem reparam_apply (phi : CompletelyPositiveContraction A B)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Tendsto r atTop atTop) (t : AsymptoticTime) (a : A) :
    (reparam phi r hr hrTop).toAsymptoticMorphism t a =
      phi.toAsymptoticMorphism (r t) a := by
  rfl

/-- **Homotopy through completely positive contractions.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For completely positive contraction asymptotic families
φ0,φ1:A→B, a homotopy F has slices A→C([0,1],B) that are completely positive contractions and
endpoints F_t(a)(0)=φ0_t(a), F_t(a)(1)=φ1_t(a). Its asymptotic limits use the supremum norm
over the interval. Such interval-valued families constitute
CompletelyPositiveContraction.Homotopy φ0 φ1.
-/
structure Homotopy (phi₀ phi₁ : CompletelyPositiveContraction A B) where
  /-- **Interval-valued CP-contractive homotopy family.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For completely positive contraction asymptotic families
φ0,φ1:A→B, a homotopy F has slices A→C([0,1],B) that are completely positive contractions and
endpoints F_t(a)(0)=φ0_t(a), F_t(a)(1)=φ1_t(a). Its asymptotic limits use the supremum norm
over the interval. The field family is this asymptotic morphism A→C([0,1],B) with completely
positive contraction slices.
-/
  family : CompletelyPositiveContraction A C(unitInterval, B)
  /-- **Initial endpoint of a CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For completely positive contraction asymptotic families
φ0,φ1:A→B, a homotopy F has slices A→C([0,1],B) that are completely positive contractions and
endpoints F_t(a)(0)=φ0_t(a), F_t(a)(1)=φ1_t(a). Its asymptotic limits use the supremum norm
over the interval. The field start states F_t(a)(0)=φ0_t(a) for every a∈A and t≥1.
-/
  start : ∀ (t : AsymptoticTime) (a : A),
    family.toAsymptoticMorphism t a 0 = phi₀.toAsymptoticMorphism t a
  /-- **Terminal endpoint of a CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For completely positive contraction asymptotic families
φ0,φ1:A→B, a homotopy F has slices A→C([0,1],B) that are completely positive contractions and
endpoints F_t(a)(0)=φ0_t(a), F_t(a)(1)=φ1_t(a). Its asymptotic limits use the supremum norm
over the interval. The field finish states F_t(a)(1)=φ1_t(a) for every a∈A and t≥1.
-/
  finish : ∀ (t : AsymptoticTime) (a : A),
    family.toAsymptoticMorphism t a 1 = phi₁.toAsymptoticMorphism t a

namespace Homotopy

/-- **Underlying asymptotic homotopy of a CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For completely positive contraction asymptotic families
φ0,φ1:A→B, a homotopy F has slices A→C([0,1],B) that are completely positive contractions and
endpoints F_t(a)(0)=φ0_t(a), F_t(a)(1)=φ1_t(a). Its asymptotic limits use the supremum norm
over the interval. The map toAsymptoticHomotopy regards F as an ordinary interval-valued
asymptotic homotopy with the same family and endpoint values.
-/
def toAsymptoticHomotopy
    {phi₀ phi₁ : CompletelyPositiveContraction A B}
    (H : Homotopy phi₀ phi₁) :
    AsymptoticMorphism.Homotopy phi₀.toAsymptoticMorphism
      phi₁.toAsymptoticMorphism where
  family := H.family.toAsymptoticMorphism
  start := H.start
  finish := H.finish

end Homotopy

/-- **Homotopy relation for CP-contractive asymptotic morphisms.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For completely positive contraction asymptotic families
φ0,φ1:A→B, a homotopy F has slices A→C([0,1],B) that are completely positive contractions and
endpoints F_t(a)(0)=φ0_t(a), F_t(a)(1)=φ1_t(a). Its asymptotic limits use the supremum norm
over the interval. CompletelyPositiveContraction.Homotopic φ0 φ1 means that a homotopy F with
these endpoints exists.
-/
def Homotopic
    (phi psi : CompletelyPositiveContraction A B) : Prop :=
  Nonempty (Homotopy phi psi)

end CompletelyPositiveContraction

/-- **Constant completely positive family of a star homomorphism.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A nonunital complex star
homomorphism f:A→B gives CompletelyPositiveFamily.ofHom f with values φ_t(a)=f(a), a
completely positive map at every time.
-/
def CompletelyPositiveFamily.ofHom (f : A →⋆ₙₐ[ℂ] B) :
    CompletelyPositiveFamily A B :=
  (CompletelyPositiveContraction.ofHom f).toCompletelyPositiveFamily

@[simp]
theorem CompletelyPositiveFamily.ofHom_apply (f : A →⋆ₙₐ[ℂ] B)
    (t : AsymptoticTime) (a : A) :
    (CompletelyPositiveFamily.ofHom f).toAsymptoticMorphism t a = f a := by
  rfl

end AsymptoticMorphism
