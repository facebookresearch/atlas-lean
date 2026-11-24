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
# Completely positive asymptotic families

This file separates a broad neutral CP-slice carrier from Blackadar's literal
CP-contraction specialization. Both reuse the existing nonlinear asymptotic
family and canonical spectral orders. No finite-time norm bound is added to
the broad carrier.

The literal homotopy DATA uses CP contractions into `C([0,1],B)`. No homotopy
setoid or quotient is installed before CP-contractive gluing is proved.
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

/-- Every finite-time slice has a genuine completely positive complex-linear
witness. No finite-time norm contraction is required. -/
def IsCompletelyPositive (phi : AsymptoticMorphism A B) : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  ∀ t : AsymptoticTime, ∃ s : A →CP B, ∀ a : A, s a = phi t a

/-- Broad neutral carrier of CP-slice asymptotic families. Blackadar's
source carrier is the contraction specialization below. -/
structure CompletelyPositiveFamily (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    extends AsymptoticMorphism A B where
  /-- Every finite-time slice has a CP complex-linear witness. -/
  completelyPositive : IsCompletelyPositive toAsymptoticMorphism

/-- Blackadar's literal finite-time completely-positive-contraction carrier. -/
structure CompletelyPositiveContraction (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    extends AsymptoticMorphism A B where
  /-- Every finite-time slice has a CP contraction witness. -/
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

/-- Proper reparametrization preserves the same CP slice witnesses. -/
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

/-- Forgetting the norm inequalities gives the broad neutral CP carrier. -/
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

/-- An actual star homomorphism as a constant CP-contractive asymptotic
family. -/
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

/-- A point-norm continuous time family of star homomorphisms is a literal
CP-contractive asymptotic family. No uniform-in-time hom-space continuity is
required beyond the continuous orbit of each input. -/
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

/-- Forgetting the CPC witness retains the existing raw time family. -/
@[simp]
theorem ofHomFamily_toAsymptoticMorphism
    (f : AsymptoticTime → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a : A, Continuous fun t => f t a) :
    (ofHomFamily f hf).toAsymptoticMorphism =
      AsymptoticMorphism.ofHomFamily f hf :=
  rfl

/-- The time-family constructor keeps the literal homomorphism value. -/
theorem ofHomFamily_apply (f : AsymptoticTime → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a : A, Continuous fun t => f t a)
    (t : AsymptoticTime) (a : A) :
    (ofHomFamily f hf).toAsymptoticMorphism t a = f t a :=
  rfl

/-- Proper reparametrization preserves CP and every finite-time contraction
inequality. -/
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

/-- A literal CP-contractive homotopy: the whole interval-valued family,
not only its endpoint evaluations, has CP-contraction slices. -/
structure Homotopy (phi₀ phi₁ : CompletelyPositiveContraction A B) where
  /-- The whole interval-valued CP-contractive asymptotic family. -/
  family : CompletelyPositiveContraction A C(unitInterval, B)
  /-- Exact value at the initial endpoint. -/
  start : ∀ (t : AsymptoticTime) (a : A),
    family.toAsymptoticMorphism t a 0 = phi₀.toAsymptoticMorphism t a
  /-- Exact value at the terminal endpoint. -/
  finish : ∀ (t : AsymptoticTime) (a : A),
    family.toAsymptoticMorphism t a 1 = phi₁.toAsymptoticMorphism t a

namespace Homotopy

/-- Forget the CP-contraction evidence while retaining the actual homotopy
family and endpoints. -/
def toAsymptoticHomotopy
    {phi₀ phi₁ : CompletelyPositiveContraction A B}
    (H : Homotopy phi₀ phi₁) :
    AsymptoticMorphism.Homotopy phi₀.toAsymptoticMorphism
      phi₁.toAsymptoticMorphism where
  family := H.family.toAsymptoticMorphism
  start := H.start
  finish := H.finish

end Homotopy

/-- Literal homotopy through one whole interval-valued CPC family. -/
def Homotopic
    (phi psi : CompletelyPositiveContraction A B) : Prop :=
  Nonempty (Homotopy phi psi)

end CompletelyPositiveContraction

/-- An actual star homomorphism also supplies the broad CP-only family. -/
def CompletelyPositiveFamily.ofHom (f : A →⋆ₙₐ[ℂ] B) :
    CompletelyPositiveFamily A B :=
  (CompletelyPositiveContraction.ofHom f).toCompletelyPositiveFamily

@[simp]
theorem CompletelyPositiveFamily.ofHom_apply (f : A →⋆ₙₐ[ℂ] B)
    (t : AsymptoticTime) (a : A) :
    (CompletelyPositiveFamily.ofHom f).toAsymptoticMorphism t a = f a := by
  rfl

end AsymptoticMorphism
