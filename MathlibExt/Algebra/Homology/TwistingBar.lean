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
# Right twisting of the convolution differential

Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps.

Write f⋆g=μ_A(f⊗g)Δ_C for convolution. For degrees |f|=m, |g|=n, the graded tensor contributes
(-1)^{np} on left input degree p. The Hom differential of f of degree n has component
(δf)_p=f_p≫d_A+(-1)^{n+1}d_C≫f_{p+1}.

For τ of degree one, the right-twisted operator on f of degree n is Dᵣ_τf=δf-(-1)^n f⋆τ, of
degree n+1. The Maurer–Cartan equation is δτ+τ⋆τ=0. It implies Dᵣ_ττ=0 and (Dᵣ_τ)²f=0 in degree
(n+1)+1.

For background on twisting morphisms, see J.-L. Loday and B. Vallette, Algebraic Operads,
Springer, 2012, <https://doi.org/10.1007/978-3-642-30362-3>.
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
determine maps. For a degree-one τ:C→A and a degree-n cochain f:C→A, define Dᵣ_τf=δf-(-1)^n f⋆τ
in degree n+1, where ⋆=μ_A(-⊗-)Δ_C and (δf)_p=f_p≫d_A+(-1)^{n+1}d_C≫f_{p+1}. -/
noncomputable def twistedBarDifferential {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain C A (n + 1) :=
  HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |τ|=1, |f|=n and integers p,q with p+n+1=q, the C_p→A_q component of Dᵣ_τf
is (δf)_{p,q}-(-1)^n(f⋆τ)_{p,q}. Here (δf)_{p,q}=f_p≫d_A+(-1)^{n+1}d_C≫f_{p+1} and ⋆ uses the
graded tensor sign (-1)^p for its degree-one right factor. -/
@[simp]
theorem twistedBarDifferential_v {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (p q : ℤ) (hpq : p + (n + 1) = q) :
    (twistedBarDifferential τ f).v p q hpq =
      (HomComplex.δ n (n + 1) f).v p q hpq - n.negOnePow • (conv f τ).v p q hpq := rfl

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For any degree-one τ:C→A and integer n, Dᵣ_τ(0)=0 as a degree-(n+1) cochain,
where Dᵣ_τf=δf-(-1)^n μ_A(f⊗τ)Δ_C. -/
theorem twistedBarDifferential_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) :
    twistedBarDifferential τ (0 : HomComplex.Cochain C A n) = 0 := by
  unfold twistedBarDifferential
  rw [HomComplex.δ_zero, conv_zero_left, smul_zero, sub_zero]

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. If τ:C→A has degree one and satisfies δτ+τ⋆τ=0, then Dᵣ_ττ=0 in degree two. The
identity uses Dᵣ_ττ=δτ-(-1)^1τ⋆τ=δτ+τ⋆τ, with ⋆=μ_A(-⊗-)Δ_C. -/
theorem twistedBarDifferential_self_eq_zero
    {τ : HomComplex.Cochain C A 1} (h : IsMaurerCartan τ) :
    twistedBarDifferential τ τ = 0 := by
  unfold twistedBarDifferential
  have hsign : (1 : ℤ).negOnePow = -1 := by decide
  rw [hsign, Units.neg_smul, one_smul, sub_neg_eq_add]
  exact h

/-- Let R be a commutative ring, C an integer-graded dg R-coalgebra and A an integer-graded dg
R-algebra. Assume graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. If a degree-one τ satisfies δτ+τ⋆τ=0, then Dᵣ_τ(Dᵣ_τf)=0 for every
integer-degree cochain f:C→A. Here Dᵣ_τf=δf-(-1)^n f⋆τ for |f|=n, and the second application has
degree (n+1)+1. -/
theorem twistedBar_sq_zero {n : ℤ}
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n)
    (h : IsMaurerCartan τ) :
    twistedBarDifferential τ (twistedBarDifferential τ f) = 0 := by
  unfold twistedBarDifferential
  have hδδ : HomComplex.δ (n + 1) ((n + 1) + 1)
      (HomComplex.δ n (n + 1) f) = 0 :=
    HomComplex.δ_δ n (n + 1) ((n + 1) + 1) f
  have hsucc : (n + 1).negOnePow = -n.negOnePow := Int.negOnePow_succ n
  have hsq : n.negOnePow * n.negOnePow = 1 := by
    rw [← Int.negOnePow_add]
    have h2 : n + n = 2 * n := by omega
    rw [h2, Int.negOnePow_two_mul]
  have hsq_smul : ∀ (x : HomComplex.Cochain C A ((n + 1) + 1)),
      n.negOnePow • (n.negOnePow • x) = x := by
    intro x
    rw [smul_smul, hsq, one_smul]
  have hLeib := conv_leibniz f τ
  have hAssoc := conv_assoc f τ τ
  have hdeg : (n + 1) + 1 = n + (1 + 1) := add_assoc n 1 1
  -- Component cast computation for integer degree transport, proved by
  -- `subst` on generic equality (cf. `TwistingCobar` `hCast`).
  have hcastV : ∀ {a b : ℤ} (hab : a = b) (z : HomComplex.Cochain C A a)
      (p q : ℤ) (hpq : p + b = q),
      (cast (congrArg (HomComplex.Cochain C A) hab) z).v p q hpq =
        z.v p q (by omega) := by
    intro a b hab z p q hpq
    subst hab
    rfl
  -- General cast bridges for integer degree transport, proved by `subst`
  -- on generic equality (cf. `TwistingCobar` `hCast`); applied below with
  -- the specific `hdeg` to avoid `cases` on compound integer equality.
  have hcast_add_general : ∀ {a b : ℤ} (hab : a = b)
      (x y : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (x + y) =
        cast (congrArg (HomComplex.Cochain C A) hab) x +
        cast (congrArg (HomComplex.Cochain C A) hab) y := by
    intro a b hab x y
    subst hab
    rfl
  have hcast0_general : ∀ {a b : ℤ} (hab : a = b),
      cast (congrArg (HomComplex.Cochain C A) hab)
        (0 : HomComplex.Cochain C A a) =
        (0 : HomComplex.Cochain C A b) := by
    intro a b hab
    subst hab
    rfl
  -- Convolution is additive in the first argument (second fixed to `τ`);
  -- negation follows from `conv_add_left` + `conv_zero_left`.
  have hconv_neg_left : ∀ (x : HomComplex.Cochain C A (n + 1)),
      conv (-x) τ = -conv x τ := by
    intro x
    have h0 : conv (-x) τ + conv x τ = 0 := by
      rw [← conv_add_left, neg_add_cancel, conv_zero_left]
    exact eq_neg_of_add_eq_zero_left h0
  have hconv_sub_left : ∀ (a b : HomComplex.Cochain C A (n + 1)),
      conv (a - b) τ = conv a τ - conv b τ := by
    intro a b
    rw [sub_eq_add_neg, conv_add_left, hconv_neg_left, sub_eq_add_neg]
  -- The first Leibniz summand is definitionally `conv (δ f) τ`
  -- (same degree, same composites up to proof irrelevance).
  have hT1 : (((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ n (n + 1) f) τ) (zero_add ((n + 1) + 1))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero ((n + 1) + 1))) =
      conv (HomComplex.δ n (n + 1) f) τ := rfl
  -- The second Leibniz summand is the `add_assoc` cast of `conv f (δ τ)`.
  have hT2 : ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain f (HomComplex.δ 1 (1 + 1) τ))
        (by omega : (0 : ℤ) + (n + (1 + 1)) = (n + 1) + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : ((n + 1) + 1) + 0 = (n + 1) + 1)) :
        HomComplex.Cochain C A ((n + 1) + 1)) =
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
        (conv f (HomComplex.δ 1 (1 + 1) τ)) := by
    apply HomComplex.Cochain.ext
    intro p q hpq
    unfold conv
    rw [hcastV hdeg.symm,
      HomComplex.Cochain.comp_v, HomComplex.Cochain.comp_v,
      HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v, tensorCochain_v,
      HomComplex.Cochain.comp_v, HomComplex.Cochain.comp_v,
      HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v, tensorCochain_v]
    all_goals omega
  -- Leibniz in curvature-ready form: `δ(f ⋆ τ)` with the second leg cast.
  have hLeib_expand : HomComplex.δ (n + 1) ((n + 1) + 1) (conv f τ) =
      conv (HomComplex.δ n (n + 1) f) τ +
        n.negOnePow • cast
          (congrArg (HomComplex.Cochain C A) (hdeg.symm))
          (conv f (HomComplex.δ 1 (1 + 1) τ)) := by
    rw [hLeib, hT1, hT2]
  -- Associativity in the goal orientation: `(f ⋆ τ) ⋆ τ` is the cast of
  -- `f ⋆ (τ ⋆ τ)` backwards; derive the reverse direction by cast.
  have hAssoc_rev : conv (conv f τ) τ =
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
        (conv f (conv τ τ)) := by
    rw [← hAssoc]
    simp
  -- Expand the outer differential and the outer convolution.
  have hδ_outer : HomComplex.δ (n + 1) ((n + 1) + 1)
        (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) =
        HomComplex.δ (n + 1) ((n + 1) + 1) (HomComplex.δ n (n + 1) f) -
          n.negOnePow • HomComplex.δ (n + 1) ((n + 1) + 1) (conv f τ) := by
    rw [HomComplex.δ_sub, HomComplex.δ_units_smul]
  have hconv_outer : conv
        (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) τ =
        conv (HomComplex.δ n (n + 1) f) τ -
          n.negOnePow • conv (conv f τ) τ := by
    rw [hconv_sub_left, conv_smul_left]
  -- Cast distributes over `Add` by general cast; keep everything in
  -- the goal degree `((n + 1) + 1)` and factor the right curvature.
  have hcast_add : ∀ (a b : HomComplex.Cochain C A (n + (1 + 1))),
      cast (congrArg (HomComplex.Cochain C A) (hdeg.symm)) (a + b) =
        cast (congrArg (HomComplex.Cochain C A) (hdeg.symm)) a +
          cast (congrArg (HomComplex.Cochain C A) (hdeg.symm)) b := by
    intro a b
    exact hcast_add_general hdeg.symm a b
  have hcurv : conv f (HomComplex.δ 1 (1 + 1) τ) + conv f (conv τ τ) =
      conv f (HomComplex.δ 1 (1 + 1) τ + conv τ τ) := by
    rw [conv_add_right]
  have hMC0 : conv f (HomComplex.δ 1 (1 + 1) τ + conv τ τ) = 0 := by
    have h0 : HomComplex.δ 1 (1 + 1) τ + conv τ τ = 0 := h
    rw [h0, conv_zero_right]
  -- Assemble: δδ vanishes, `(δf ⋆ τ)` cancels by `hsucc`, `s_n^2 = 1`
  -- leaves the right curvature `-f ⋆ (δτ + τ ⋆ τ)`, which is zero by `h`.
  calc HomComplex.δ (n + 1) ((n + 1) + 1)
          (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) -
          (n + 1).negOnePow • conv
            (HomComplex.δ n (n + 1) f - n.negOnePow • conv f τ) τ
        = (0 - n.negOnePow •
            (conv (HomComplex.δ n (n + 1) f) τ +
              n.negOnePow • cast
                (congrArg (HomComplex.Cochain C A) (hdeg.symm))
                (conv f (HomComplex.δ 1 (1 + 1) τ)))) -
          (n + 1).negOnePow •
            (conv (HomComplex.δ n (n + 1) f) τ -
              n.negOnePow • conv (conv f τ) τ) := by
          rw [hδ_outer, hδδ, hLeib_expand, hconv_outer]
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ))) -
            (cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (conv τ τ))) := by
          rw [hsucc, Units.neg_smul, hAssoc_rev]
          simp only [zero_sub, smul_add, smul_sub, sub_neg_eq_add,
            hsq_smul]
          abel
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ)) +
            cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (conv τ τ))) := by
          abel
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ) +
                conv f (conv τ τ))) := by
          rw [hcast_add]
      _ = -(cast (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (conv f (HomComplex.δ 1 (1 + 1) τ + conv τ τ))) := by
          rw [hcurv]
      _ = 0 := by
          rw [hMC0]
          have hcast0 : cast
              (congrArg (HomComplex.Cochain C A) (hdeg.symm))
              (0 : HomComplex.Cochain C A (n + (1 + 1))) =
              (0 : HomComplex.Cochain C A ((n + 1) + 1)) := by
            exact hcast0_general hdeg.symm
          rw [hcast0, neg_zero]

end CochainComplex
