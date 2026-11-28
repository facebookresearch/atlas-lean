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

public import MathlibExt.Algebra.Homology.TwistingMaurerCartan
public import MathlibExt.Algebra.Homology.TwistingConvolutionMonoid

/-!
# Left twisting of the convolution differential

Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps.

Write f⋆g=μ_A(f⊗g)Δ_C for convolution. For degrees |f|=m, |g|=n, the graded tensor contributes
(-1)^{np} on left input degree p. The Hom differential of f of degree n has component
(δf)_p=f_p≫d_A+(-1)^{n+1}d_C≫f_{p+1}.

For τ of degree one, the left-twisted operator on f of degree n is Dₗ_τf=δf+τ⋆f, of degree 1+n.
The Maurer–Cartan equation δτ+τ⋆τ=0 implies Dₗ_ττ=0 and (Dₗ_τ)²f=0 in degree 1+(1+n).
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

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For a degree-one τ:C→A and a degree-n cochain f:C→A, define Dₗ_τf=δf+τ⋆f in
degree 1+n, where ⋆=μ_A(-⊗-)Δ_C and (δf)_p=f_p≫d_A+(-1)^{n+1}d_C≫f_{p+1}. -/
noncomputable def twistedCobarDifferential {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain C A (1 + n) :=
  HomComplex.δ n (1 + n) f + conv τ f

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |τ|=1, |f|=n and integers p,q with p+1+n=q, the C_p→A_q component of Dₗ_τf
is (δf)_{p,q}+(τ⋆f)_{p,q}. Here (δf)_{p,q}=f_p≫d_A+(-1)^{n+1}d_C≫f_{p+1} and the tensor in τ⋆f
contributes (-1)^{np₁} on a coproduct summand C_{p₁}⊗C_{p₂}. -/
@[simp]
theorem twistedCobarDifferential_v {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (p q : ℤ) (hpq : p + (1 + n) = q) :
    (twistedCobarDifferential τ f).v p q hpq =
      (HomComplex.δ n (1 + n) f).v p q hpq + (conv τ f).v p q hpq := rfl

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For any degree-one τ:C→A and integer n, Dₗ_τ(0)=0 as a degree-(1+n) cochain,
where Dₗ_τf=δf+μ_A(τ⊗f)Δ_C. -/
theorem twistedCobarDifferential_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) :
    twistedCobarDifferential τ (0 : HomComplex.Cochain C A n) = 0 := by
  unfold twistedCobarDifferential
  rw [HomComplex.δ_zero, conv_zero_right, add_zero]

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. If τ:C→A has degree one and satisfies δτ+τ⋆τ=0, then Dₗ_ττ=0 in degree two. Its
left twist is Dₗ_ττ=δτ+τ⋆τ, where ⋆=μ_A(-⊗-)Δ_C. -/
theorem twistedCobarDifferential_self_eq_zero
    {τ : HomComplex.Cochain C A 1} (h : IsMaurerCartan τ) :
    twistedCobarDifferential τ τ = 0 := h

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. If a degree-one τ satisfies δτ+τ⋆τ=0, then Dₗ_τ(Dₗ_τf)=0 for every
integer-degree cochain f:C→A. Here Dₗ_τf=δf+τ⋆f for |f|=n, and the second application has degree
1+(1+n). -/
theorem twistedCobar_sq_zero {n : ℤ}
    {τ : HomComplex.Cochain C A 1} (hMC : IsMaurerCartan τ)
    (f : HomComplex.Cochain C A n) :
    twistedCobarDifferential τ (twistedCobarDifferential τ f) = 0 := by
  unfold twistedCobarDifferential
  rw [HomComplex.δ_add, conv_add_right]
  have hδδ : HomComplex.δ (1 + n) (1 + (1 + n))
      (HomComplex.δ n (1 + n) f) = 0 :=
    HomComplex.δ_δ n (1 + n) (1 + (1 + n)) f
  rw [hδδ, zero_add]
  apply HomComplex.Cochain.ext
  intro r s hrs
  simp only [HomComplex.Cochain.add_v, HomComplex.Cochain.zero_v]
  have hsign : (1 : ℤ).negOnePow = -1 := by decide
  have hmn : n + 1 = 1 + n := by omega
  have hLeib := conv_leibniz τ f
  have hLeib_v := HomComplex.Cochain.congr_v hLeib r s (by omega)
  simp only [HomComplex.Cochain.add_v, HomComplex.Cochain.units_smul_v]
    at hLeib_v
  have hDeltaBridge :
      (HomComplex.δ (1 + n) (1 + (1 + n)) (conv τ f)).v r s hrs =
      (HomComplex.δ (1 + n) (1 + n + 1) (conv τ f)).v r s (by omega) := by
    have hDeg : (1 + (1 + n) : ℤ) = 1 + n + 1 := by omega
    have hgen : ∀ {b1 b2 : ℤ} (h : b1 = b2) (hpq1 : r + b1 = s)
        (hpq2 : r + b2 = s),
        (HomComplex.δ (1 + n) b1 (conv τ f)).v r s hpq1 =
        (HomComplex.δ (1 + n) b2 (conv τ f)).v r s hpq2 := by
      intro b1 b2 h hpq1 hpq2
      subst h
      rfl
    exact hgen hDeg hrs (by omega)
  have hXBridge :
      ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ 1 (1 + 1) τ) f)
        (by omega : (0 : ℤ) + (1 + 1 + n) = 1 + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (1 + n + 1) + 0 = 1 + n + 1))).v r s (by omega) =
      (conv (HomComplex.δ 1 (1 + 1) τ) f).v r s (by omega) := by
    unfold conv
    rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
  have hYgen : ∀ {d1 d2 : ℤ} (hd : d1 = d2)
      (h1 : (0 : ℤ) + (1 + d1) = 1 + n + 1)
      (h2 : (1 + n + 1) + 0 = 1 + n + 1) (hpq1 : r + (1 + n + 1) = s)
      (hpq2 : r + (1 + d2) = s),
      ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
          (tensorCochain τ (HomComplex.δ n d1 f)) h1).comp
          (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) h2)).v r s hpq1 =
        (conv τ (HomComplex.δ n d2 f)).v r s hpq2 := by
    intro d1 d2 hd h1 h2 hpq1 hpq2
    subst hd
    unfold conv
    rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
      HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
  have hYBridge :
      ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain τ (HomComplex.δ n (n + 1) f))
        (by omega : (0 : ℤ) + (1 + (n + 1)) = 1 + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (1 + n + 1) + 0 = 1 + n + 1))).v r s (by omega) =
      (conv τ (HomComplex.δ n (1 + n) f)).v r s hrs :=
    hYgen (d1 := n + 1) (d2 := 1 + n) (by omega) (by omega) (by omega)
      (by omega) hrs
  have hAssoc_v := HomComplex.Cochain.congr_v (conv_assoc τ τ f) r s hrs
  have hCast : ∀ {a b : ℤ} (hab : a = b)
      (z : HomComplex.Cochain C A a) (p q : ℤ) (hpq : p + b = q),
      (cast (congrArg (HomComplex.Cochain C A) hab) z).v p q hpq =
      z.v p q (by omega) := by
    intro a b hab z p q hpq
    subst hab
    rfl
  have hAdd : conv (HomComplex.δ 1 (1 + 1) τ + conv τ τ) f =
      conv (HomComplex.δ 1 (1 + 1) τ) f + conv (conv τ τ) f :=
    conv_add_left _ _ _
  have hAdd_v := HomComplex.Cochain.congr_v hAdd r s (by omega)
  simp only [HomComplex.Cochain.add_v] at hAdd_v
  have hZero := conv_zero_left (C := C) (A := A) (m := 1 + 1) (n := n) f
  have hZero_v := HomComplex.Cochain.congr_v hZero r s (by omega)
  simp only [HomComplex.Cochain.zero_v] at hZero_v
  rw [hDeltaBridge, hLeib_v, hsign, Units.neg_smul, one_smul, hXBridge,
    hYBridge, ← hAssoc_v] at ⊢
  rw [hCast (add_assoc 1 1 n) (conv (conv τ τ) f) r s hrs] at ⊢
  have hCancel :
      (conv (HomComplex.δ 1 (1 + 1) τ) f).v r s (by omega) +
          (-(conv τ (HomComplex.δ n (1 + n) f)).v r s hrs) +
        ((conv τ (HomComplex.δ n (1 + n) f)).v r s hrs +
          (conv (conv τ τ) f).v r s (by omega)) =
        (conv (HomComplex.δ 1 (1 + 1) τ) f).v r s (by omega) +
          (conv (conv τ τ) f).v r s (by omega) := by abel
  rw [hCancel, ← hAdd_v, hMC, hZero_v] at ⊢

end CochainComplex
