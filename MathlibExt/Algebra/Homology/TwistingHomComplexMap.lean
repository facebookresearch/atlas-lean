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

public import MathlibExt.Algebra.Homology.TwistingHomComplex
public import MathlibExt.RingTheory.DifferentialGraded.TwistingCochain
public import MathlibExt.Algebra.Homology.TwistingMaurerCartanFunctoriality

/-!
# Maps of additive twisting Hom complexes

Let C,C' be dg coalgebras and A,B dg algebras over a commutative ring. Maps ψ:C'→C and φ:A→B
send a Maurer–Cartan cochain τ to τ'=φτψ and each homogeneous f to Φ(f)=φfψ in the same degree.

The degree maps are additive and satisfy Φ(D_τ f)=D_{τ'}Φ(f). They therefore define a map
between the additive twisting Hom complexes. Identity maps retain every cochain, and two maps
compose by ψ₁≫ψ₂ on the coalgebra side and φ₂≫φ₁ on the algebra side; the bundled laws are given
degreewise.
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

variable {B : CochainComplex (ModuleCat R) ℤ} [MonObj B]
variable {C' : CochainComplex (ModuleCat R) ℤ} [ComonObj C']

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. Let ψ:C'→C be a dg coalgebra map and
φ:A→B a dg algebra map. For a Maurer–Cartan bundle x with τ, put τ'=φτψ and Φ_n(f)=φfψ. For any
n∈ℤ and f∈Hom^n(C,A), Φ_n(f)=φ∘f∘ψ∈Hom^n(C',B). The supplied MC bundle fixes the twists used by
the later complex map. -/
noncomputable def twistedHomComplexMapCochain {n : ℤ}
    (_x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ]
    (f : HomComplex.Cochain C A n) : HomComplex.Cochain C' B n :=
  (HomComplex.Cochain.ofHom ψ).comp
    (f.comp (HomComplex.Cochain.ofHom φ) (add_zero n)) (zero_add n)

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. Let ψ:C'→C be a dg coalgebra map and
φ:A→B a dg algebra map. For a Maurer–Cartan bundle x with τ, put τ'=φτψ and Φ_n(f)=φfψ. For
f∈Hom^n(C,A), Φ_{n+1}(D_τ f)=D_{τ'}(Φ_n f). The twist τ' is the cochain of the mapped
Maurer–Cartan bundle. -/
theorem twistedHomComplexMapCochain_twistedDifferential {n : ℤ}
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ]
    (f : HomComplex.Cochain C A n) :
    twistedHomComplexMapCochain x ψ φ (twistedDifferential x.tau f) =
      twistedDifferential (x.map ψ φ).tau
        (twistedHomComplexMapCochain x ψ φ f) := by
  have hδ : ∀ (g : HomComplex.Cochain C A n),
      twistedHomComplexMapCochain x ψ φ (HomComplex.δ n (n + 1) g) =
        HomComplex.δ n (n + 1) (twistedHomComplexMapCochain x ψ φ g) := by
    intro g
    unfold twistedHomComplexMapCochain
    rw [← HomComplex.δ_comp_ofHom, ← HomComplex.δ_ofHom_comp]
  have hconv : ∀ {m k : ℤ} (a : HomComplex.Cochain C A m)
      (b : HomComplex.Cochain C A k),
      twistedHomComplexMapCochain x ψ φ (conv a b) =
        conv (twistedHomComplexMapCochain x ψ φ a)
          (twistedHomComplexMapCochain x ψ φ b) := by
    intro m k a b
    unfold twistedHomComplexMapCochain
    rw [conv_postcomp, conv_precomp]
  have hcast : ∀ {a b : ℤ} (hab : a = b) (y : HomComplex.Cochain C A a),
      twistedHomComplexMapCochain x ψ φ
          (cast (congrArg (HomComplex.Cochain C A) hab) y) =
        cast (congrArg (HomComplex.Cochain C' B) hab)
          (twistedHomComplexMapCochain x ψ φ y) := by
    intro a b hab y
    cases hab
    rfl
  have hadd : ∀ (a b : HomComplex.Cochain C A (n + 1)),
      twistedHomComplexMapCochain x ψ φ (a + b) =
        twistedHomComplexMapCochain x ψ φ a +
          twistedHomComplexMapCochain x ψ φ b := by
    intro a b
    unfold twistedHomComplexMapCochain
    rw [HomComplex.Cochain.add_comp, HomComplex.Cochain.comp_add]
  have hsub : ∀ (a b : HomComplex.Cochain C A (n + 1)),
      twistedHomComplexMapCochain x ψ φ (a - b) =
        twistedHomComplexMapCochain x ψ φ a -
          twistedHomComplexMapCochain x ψ φ b := by
    intro a b
    rw [sub_eq_add_neg, hadd, sub_eq_add_neg]
    congr 1
    unfold twistedHomComplexMapCochain
    rw [HomComplex.Cochain.neg_comp, HomComplex.Cochain.comp_neg]
  have hsmul : ∀ (k : ℤˣ) (y : HomComplex.Cochain C A (n + 1)),
      twistedHomComplexMapCochain x ψ φ (k • y) =
        k • twistedHomComplexMapCochain x ψ φ y := by
    intro k y
    unfold twistedHomComplexMapCochain
    rcases Int.units_eq_one_or k with rfl | rfl
    · simp only [one_smul]
    · simp only [Units.neg_smul, one_smul,
        HomComplex.Cochain.neg_comp, HomComplex.Cochain.comp_neg]
  have htau : twistedHomComplexMapCochain x ψ φ x.tau = (x.map ψ φ).tau :=
    rfl
  unfold twistedDifferential
  simp only [MaurerCartan.map_tau]
  rw [hsub, hadd, hδ, hcast (add_comm 1 n), hsmul, hconv, hconv, htau,
    MaurerCartan.map_tau]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. Let ψ:C'→C be a dg coalgebra map and
φ:A→B a dg algebra map. For a Maurer–Cartan bundle x with τ, put τ'=φτψ and Φ_n(f)=φfψ. For each
n∈ℤ, Φ_n:Hom^n(C,A)→Hom^n(C',B) is an additive group homomorphism, given by φfψ. -/
noncomputable def twistedHomComplexMapHom {n : ℤ}
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    HomComplex.Cochain C A n →+ HomComplex.Cochain C' B n where
  toFun := twistedHomComplexMapCochain x ψ φ
  map_zero' := by
    unfold twistedHomComplexMapCochain
    simp only [HomComplex.Cochain.zero_comp, HomComplex.Cochain.comp_zero]
  map_add' := by
    intro f g
    unfold twistedHomComplexMapCochain
    simp only [HomComplex.Cochain.add_comp, HomComplex.Cochain.comp_add]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. Let ψ:C'→C be a dg coalgebra map and
φ:A→B a dg algebra map. For a Maurer–Cartan bundle x with τ, put τ'=φτψ and Φ_n(f)=φfψ. The maps
Φ_n assemble to a cochain map from the additive complex twisted by τ to the one twisted by τ'.
Its degree-n component is the additive homomorphism f↦φfψ. -/
noncomputable def twistedHomComplexMap
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    twistedHomComplex x.tau x.isMC ⟶
      twistedHomComplex (x.map ψ φ).tau (x.map ψ φ).isMC where
  f n := AddCommGrpCat.ofHom (twistedHomComplexMapHom x ψ φ (n := n))
  comm' := by
    intro i j hij
    have h1 : i + 1 = j := by simpa [ComplexShape.up_Rel] using hij
    subst h1
    change (AddCommGrpCat.ofHom (twistedHomComplexMapHom (n := i) x ψ φ) ≫
        AddCommGrpCat.ofHom
          (twistedDifferentialHom (x.map ψ φ).tau i (i + 1))) =
      (AddCommGrpCat.ofHom (twistedDifferentialHom x.tau i (i + 1)) ≫
        AddCommGrpCat.ofHom (twistedHomComplexMapHom (n := i + 1) x ψ φ))
    ext g p q hpq z
    rw [← AddCommGrpCat.ofHom_comp, AddCommGrpCat.ofHom_apply,
      AddMonoidHom.comp_apply, ← AddCommGrpCat.ofHom_comp,
      AddCommGrpCat.ofHom_apply, AddMonoidHom.comp_apply]
    have e1 : (twistedDifferentialHom (x.map ψ φ).tau i (i + 1))
          ((twistedHomComplexMapHom (n := i) x ψ φ) g) =
        twistedDifferential (x.map ψ φ).tau
          (twistedHomComplexMapCochain x ψ φ g) := by
      simp [twistedDifferentialHom, twistedHomComplexMapHom]
    have e2 : (twistedHomComplexMapHom (n := i + 1) x ψ φ)
          ((twistedDifferentialHom x.tau i (i + 1)) g) =
        twistedHomComplexMapCochain x ψ φ (twistedDifferential x.tau g) := by
      simp [twistedDifferentialHom, twistedHomComplexMapHom]
    rw [e1, e2]
    have hC := twistedHomComplexMapCochain_twistedDifferential x ψ φ g
    have hW := congrArg
      (fun h : HomComplex.Cochain C' B (i + 1) =>
        ModuleCat.Hom.hom (h.v p q hpq) z) hC
    exact hW.symm

variable {B' : CochainComplex (ModuleCat R) ℤ} [MonObj B']
variable {C'' : CochainComplex (ModuleCat R) ℤ} [ComonObj C'']

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For a Maurer–Cartan bundle x and
f∈Hom^n(C,A), the degreewise transport using id_C and id_A sends f to f. -/
theorem twistedHomComplexMapCochain_id
    (x : MaurerCartan (R := R) (C := C) (A := A))
    {n : ℤ} (f : HomComplex.Cochain C A n) :
    twistedHomComplexMapCochain x (𝟙 C) (𝟙 A) f = f := by
  unfold twistedHomComplexMapCochain
  simp only [HomComplex.Cochain.comp_id, HomComplex.Cochain.id_comp]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. Let ψ₂:C'→C,ψ₁:C''→C' be coalgebra
maps and φ₂:A→B,φ₁:B→B' algebra maps. For x and f∈Hom^n(C,A),
Φ_{ψ₁,φ₁}(Φ_{ψ₂,φ₂}(f))=Φ_{ψ₁≫ψ₂,φ₂≫φ₁}(f), with the second transport based on the mapped MC
bundle. -/
theorem twistedHomComplexMapCochain_comp
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ₂ : C' ⟶ C) [IsComonHom ψ₂] (φ₂ : A ⟶ B) [IsMonHom φ₂]
    (ψ₁ : C'' ⟶ C') [IsComonHom ψ₁] (φ₁ : B ⟶ B') [IsMonHom φ₁]
    {n : ℤ} (f : HomComplex.Cochain C A n) :
    twistedHomComplexMapCochain (x.map ψ₂ φ₂) ψ₁ φ₁
        (twistedHomComplexMapCochain x ψ₂ φ₂ f) =
      twistedHomComplexMapCochain x (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁) f := by
  unfold twistedHomComplexMapCochain
  simp only [HomComplex.Cochain.ofHom_comp,
    HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
    HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For a Maurer–Cartan x, n∈ℤ, and
f∈Hom^n(C,A), the n-th component of the additive complex map for id_C,id_A sends f to f. -/
theorem twistedHomComplexMap_id_f
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (n : ℤ) (f : HomComplex.Cochain C A n) :
    ((twistedHomComplexMap x (𝟙 C) (𝟙 A)).f n) f = f := by
  change twistedHomComplexMapCochain x (𝟙 C) (𝟙 A) f = f
  exact twistedHomComplexMapCochain_id x f

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For coalgebra maps ψ₂:C'→C,ψ₁:C''→C'
and algebra maps φ₂:A→B,φ₁:B→B', the composite of the two additive complex maps has the same
degree-n value on every f as the map for ψ₁≫ψ₂ and φ₂≫φ₁. -/
theorem twistedHomComplexMap_comp_f
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ₂ : C' ⟶ C) [IsComonHom ψ₂] (φ₂ : A ⟶ B) [IsMonHom φ₂]
    (ψ₁ : C'' ⟶ C') [IsComonHom ψ₁] (φ₁ : B ⟶ B') [IsMonHom φ₁]
    (n : ℤ) (f : HomComplex.Cochain C A n) :
    (((twistedHomComplexMap x ψ₂ φ₂) ≫
        (twistedHomComplexMap (x.map ψ₂ φ₂) ψ₁ φ₁)).f n) f =
      ((twistedHomComplexMap x (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁)).f n) f := by
  rw [HomologicalComplex.comp_f]
  change twistedHomComplexMapCochain (x.map ψ₂ φ₂) ψ₁ φ₁
        (twistedHomComplexMapCochain x ψ₂ φ₂ f) =
      twistedHomComplexMapCochain x (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁) f
  exact twistedHomComplexMapCochain_comp x ψ₂ φ₂ ψ₁ φ₁ f

end CochainComplex
