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

public import MathlibExt.RingTheory.DifferentialGraded.TwistingCochain

/-!
# Maurer–Cartan cochains for graded convolution

Let R be a commutative ring, C a dg coalgebra, and A a dg algebra in integer cochain complexes
of R-modules. A degree-n cochain f has differential δf=d_A f+(-1)^{n+1}f d_C. The convolution
f⋆g=μ_A(f⊗g)Δ_C has degree |f|+|g|, with Koszul factor (-1)^{|g|p} on a left input of degree p.

The Maurer–Cartan equation for τ of degree one is δτ+τ⋆τ=0 in degree two. Its bundled form
records τ and this equation, is determined by τ, and has the zero solution. A twisting cochain
supplies such a solution through its Maurer–Cartan field.

For graded twisting morphisms and Maurer–Cartan equations, see J.-L. Loday and B. Vallette,
Algebraic Operads, Grundlehren346, Springer2012, https://doi.org/10.1007/978-3-642-30362-3.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [MonObj A] [ComonObj C]

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. For a degree-n cochain f:C→A, δf=d_A f+(-1)^{n+1}f d_C.
Convolution f⋆g=μ_A(f⊗g)Δ_C uses (-1)^{|g|p} on the left input degree p. A degree-one τ is
Maurer–Cartan when δτ+τ⋆τ=0 in degree two. This predicate is the equality
δ_{1,2}(τ)+conv(τ,τ)=0, with both terms degree two. -/
def IsMaurerCartan (τ : HomComplex.Cochain C A 1) : Prop :=
  HomComplex.δ 1 (1 + 1) τ + conv τ τ = 0

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. A degree-one τ is Maurer–Cartan when δτ+τ⋆τ=0 in degree two. The
cochain τ=0 is a solution because δ0=0 and 0⋆0=0. -/
theorem IsMaurerCartan.zero : IsMaurerCartan (R := R) (C := C) (A := A) 0 := by
  unfold IsMaurerCartan
  rw [HomComplex.δ_zero, conv_zero_left, add_zero]

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. A degree-one τ is Maurer–Cartan when δτ+τ⋆τ=0 in degree two. For
a twisting cochain t, its underlying degree-one cochain τ=t.tau satisfies this predicate by the
twisting-cochain equation. -/
theorem TwistingCochain.isMaurerCartan
    (τ : TwistingCochain (R := R) (C := C) (A := A)) :
    IsMaurerCartan τ.tau :=
  τ.maurer_cartan

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. A degree-one τ is Maurer–Cartan when δτ+τ⋆τ=0 in degree two. The
data consist of τ∈Hom¹(C,A) and the proposition δτ+τ⋆τ=0. The underlying cochain determines the
bundle. -/
structure MaurerCartan where
  /-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
  category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
  total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
  fourfold tensor extensionality. The projection τ∈Hom¹(C,A) is the underlying homogeneous
  R-linear cochain of degree one. Its Maurer–Cartan equation is the separate proposition field. -/
  tau : HomComplex.Cochain C A 1
  /-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
  category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
  total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
  fourfold tensor extensionality. A degree-one τ is Maurer–Cartan when δτ+τ⋆τ=0 in degree two. The
  field isMC states that its projected cochain τ satisfies δ_{1,2}(τ)+τ⋆τ=0. -/
  isMC : IsMaurerCartan tau

-- The underlying cochain is exposed by the Maurer–Cartan projection.
instance : CoeOut (MaurerCartan (R := R) (C := C) (A := A))
    (HomComplex.Cochain C A 1) :=
  ⟨MaurerCartan.tau⟩

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. For x,y Maurer–Cartan bundles, x.tau=y.tau implies x=y. Their
equation fields are proofs of the same proposition on the common cochain. -/
@[ext]
theorem MaurerCartan.ext {x y : MaurerCartan (R := R) (C := C) (A := A)}
    (h : x.tau = y.tau) : x = y := by
  obtain ⟨a, ha⟩ := x
  obtain ⟨b, hb⟩ := y
  simp only at h
  subst h
  rfl

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. A degree-one τ is Maurer–Cartan when δτ+τ⋆τ=0 in degree two. The
zero bundle has τ=0 and the equation δ0+0⋆0=0. -/
def MaurerCartan.zero : MaurerCartan (R := R) (C := C) (A := A) :=
  ⟨0, IsMaurerCartan.zero⟩

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. Projection of the zero Maurer–Cartan bundle to Hom¹(C,A) equals
the zero degree-one cochain. -/
@[simp]
theorem MaurerCartan.zero_tau :
    (MaurerCartan.zero (R := R) (C := C) (A := A)).tau = 0 :=
  rfl

end CochainComplex
