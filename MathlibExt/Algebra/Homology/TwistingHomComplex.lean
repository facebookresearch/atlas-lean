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

public import MathlibExt.Algebra.Homology.TwistingDifferential

/-!
# The additive twisting Hom complex

Let C be a dg coalgebra and A a dg algebra over a commutative ring R. For a Maurer–Cartan
cochain τ of degree one, D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ is additive in degree n and squares to zero.

The twisting Hom complex has degree-n abelian group Hom^n(C,A), differential D_τ from n to n+1,
and zero differential to every other degree. The underlying cochains and their integer grading
are retained.
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

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. For f,g∈Hom^n(C,A),
D_τ(f+g)=D_τ(f)+D_τ(g). The identity holds for any degree-one τ. -/
theorem twistedDifferential_add {n : ℤ}
    (τ : HomComplex.Cochain C A 1)
    (f g : HomComplex.Cochain C A n) :
    twistedDifferential τ (f + g) =
      twistedDifferential τ f + twistedDifferential τ g := by
  unfold twistedDifferential
  rw [HomComplex.δ_add, conv_add_right, conv_add_left]
  have hcast_add : ∀ {a b : ℤ} (hab : a = b)
      (x y : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (x + y) =
        cast (congrArg (HomComplex.Cochain C A) hab) x +
          cast (congrArg (HomComplex.Cochain C A) hab) y := by
    intro a b hab x y
    cases hab
    rfl
  rw [hcast_add (add_comm 1 n), smul_add]
  abel

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. For n,m∈ℤ, the additive map
Hom^n(C,A)→Hom^m(C,A) is D_τ transported through n+1=m when that equality holds, and is zero
otherwise. -/
noncomputable def twistedDifferentialHom
    (τ : HomComplex.Cochain C A 1) (n m : ℤ) :
    HomComplex.Cochain C A n →+ HomComplex.Cochain C A m where
  toFun f :=
    if h : n + 1 = m then
      cast (congrArg (HomComplex.Cochain C A) h) (twistedDifferential τ f)
    else 0
  map_zero' := by
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_zero]
      cases h
      rfl
    · simp only [dite_eq_right h]
  map_add' := by
    intro f g
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_add]
      cases h
      rfl
    · simp only [dite_eq_right h, add_zero]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. If δτ+τ⋆τ=0, the ℤ-cochain complex
has abelian-group term Hom^n(C,A), differential D_τ:n→n+1, and zero outside that relation. The
MC equation gives the complex square-zero law. -/
noncomputable def twistedHomComplex
    (τ : HomComplex.Cochain C A 1) (hMC : IsMaurerCartan τ) :
    CochainComplex AddCommGrpCat ℤ where
  X n := AddCommGrpCat.of (HomComplex.Cochain C A n)
  d n m := AddCommGrpCat.ofHom (twistedDifferentialHom τ n m)
  shape n m hnm := by
    have h : ¬ n + 1 = m := by simpa [ComplexShape.up_Rel] using hnm
    ext f
    simp [twistedDifferentialHom, dite_eq_right h]
  d_comp_d' n m k hij hjk := by
    have h1 : n + 1 = m := by simpa [ComplexShape.up_Rel] using hij
    have h2 : m + 1 = k := by simpa [ComplexShape.up_Rel] using hjk
    ext f p q hpq x
    simp only [twistedDifferentialHom, dite_eq_left h1, dite_eq_left h2]
    cases h1
    cases h2
    rw [← AddCommGrpCat.ofHom_comp, AddCommGrpCat.ofHom_apply,
      AddMonoidHom.comp_apply]
    have hSq := twistedDifferential_sq_zero τ f hMC
    have hW := congrArg
      (fun g : HomComplex.Cochain C A ((n + 1) + 1) =>
        ModuleCat.Hom.hom (g.v p q hpq) x) hSq
    exact hW

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For Maurer–Cartan τ and n∈ℤ, the
degree-n object of the additive twisting Hom complex is the abelian group Hom^n(C,A). -/
@[simp]
theorem twistedHomComplex_X (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n : ℤ) :
    (twistedHomComplex τ hMC).X n =
      AddCommGrpCat.of (HomComplex.Cochain C A n) :=
  rfl

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. For Maurer–Cartan τ, n,m∈ℤ, and
f∈Hom^n(C,A), d_{n,m}(f) is D_τ(f) transported to m if n+1=m, and zero if n+1≠m. -/
@[simp]
theorem twistedHomComplex_d_apply (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n m : ℤ)
    (f : HomComplex.Cochain C A n) :
    ((twistedHomComplex τ hMC).d n m) f =
      (if h : n + 1 = m then
        cast (congrArg (HomComplex.Cochain C A) h)
          (twistedDifferential τ f)
      else 0) :=
  rfl

end CochainComplex
