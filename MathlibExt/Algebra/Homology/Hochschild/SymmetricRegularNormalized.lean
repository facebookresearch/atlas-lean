/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficients
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.NormalizedMixedBicomplex

/-!
# Symmetric regular normalized chains and Connes' operator

For a commutative k-algebra A, the symmetric opposite action on the regular coefficient A equals
regular right multiplication, and the algebra structure recovered from the scalar action equals
the given k-algebra structure. Thus the symmetric normalized Hochschild complex and the regular
normalized b-complex used for Connes' operator have the same degree objects and differentials.
Their comparison isomorphism has identity components.

The normalized Connes maps Bₙ : C̄ₙ(A,A) → C̄ₙ₊₁(A,A) are transported through this comparison.
They retain B²=0 and bB+Bb=0 in every natural-number degree. The maps are ground-linear over an
arbitrary commutative k.

For the normalized Connes mixed complex, see J.-L. Loday, Cyclic Homology, second edition, §2.1.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

/-- For a commutative ring A, the symmetric Aᵐᵒᵖ-action on A, aᵐᵒᵖ·m = a·m, equals the regular right
multiplication action aᵐᵒᵖ·m = m·a, by commutativity. -/
theorem regular_opModule_eq : opModule A A = (Semiring.toOppositeModule : Module Aᵐᵒᵖ A) := by
  apply Module.ext'
  intro a m
  rw [opModule_smul]
  change MulOpposite.unop a * m = m * MulOpposite.unop a
  exact mul_comm _ _

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. The k-algebra structure on A obtained from
the regular scalar action r ↦ r·1, denoted NonUnital.regularAlgebra k A, equals the given
k-algebra structure on A. -/
theorem regularAlgebra_eq : NonUnital.regularAlgebra k A = (inferInstance : Algebra k A) := by
  apply Algebra.algebra_ext
  intro r
  change r • (1 : A) = algebraMap k A r
  rw [Algebra.smul_def, mul_one]

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. The symmetric normalized coefficient complex
normalizedChainComplex k A A equals NonUnital.normalizedBComplex k A, the regular normalized
b-complex used for Connes' operator. The symmetric right action and reconstructed ground algebra
structure agree with the regular ones. -/
theorem regularNormalizedComplex_eq : normalizedChainComplex k A A = NonUnital.normalizedBComplex k A := by
  unfold normalizedChainComplex NonUnital.normalizedBComplex
  congr 1 <;> first
    | exact regular_opModule_eq A
    | exact (regularAlgebra_eq k A).symm
    | exact proof_irrel_heq _ _

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. For every n : ℕ, the degree-n objects of
normalizedChainComplex k A A and NonUnital.normalizedBComplex k A are equal. Both are the
ground-module tensor A ⊗_k(A/(k·1))^{⊗n}. -/
theorem regularNormalized_X_eq (n : ℕ) :
    (normalizedChainComplex k A A).X n = (NonUnital.normalizedBComplex k A).X n := by
  change ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n =
    ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n
  rfl

/-- Let C be a category with zero morphisms, c a complex shape on an arbitrary index type, and K,L
homological complexes of shape c. If h : K=L, the component identifications eᵢ : Kᵢ → Lᵢ induced
by h satisfy eᵢ ≫ d_L(i,j) = d_K(i,j) ≫ eⱼ for every pair of indices i,j. -/
private theorem differential_eq_transport {C : Type*} [Category* C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (h : K = L) (i j : ι) :
    eqToHom (congrArg (fun T : HomologicalComplex C c => T.X i) h) ≫ L.d i j =
      K.d i j ≫ eqToHom (congrArg (fun T : HomologicalComplex C c => T.X j) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. The equality of normalized degree objects
gives an isomorphism normalizedChainComplex k A A ≅ NonUnital.normalizedBComplex k A. Its
components are the identity on every normalized coefficient tensor. -/
def regularNormalizedComplexIso : normalizedChainComplex k A A ≅ NonUnital.normalizedBComplex k A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => eqToIso (regularNormalized_X_eq k A n))
    (by
      intro i j _
      simpa only [eqToIso.hom] using differential_eq_transport (regularNormalizedComplex_eq k A) i j)

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. For every n : ℕ, the nth component of
regularNormalizedComplexIso.hom is the identity of the normalized regular degree-n object. -/
theorem regularNormalizedComplexIso_hom_f (n : ℕ) :
    (regularNormalizedComplexIso k A).hom.f n = 𝟙 ((normalizedChainComplex k A A).X n) := by
  change (eqToIso (regularNormalized_X_eq k A n)).hom = 𝟙 ((normalizedChainComplex k A A).X n)
  rw [eqToIso.hom]
  exact eqToHom_refl ((normalizedChainComplex k A A).X n) (regularNormalized_X_eq k A n)

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. For every n : ℕ, the nth component of
regularNormalizedComplexIso.inv is also the identity of the normalized regular degree-n object. -/
theorem regularNormalizedComplexIso_inv_f (n : ℕ) :
    (regularNormalizedComplexIso k A).inv.f n = 𝟙 ((normalizedChainComplex k A A).X n) := by
  change (eqToIso (regularNormalized_X_eq k A n)).inv = 𝟙 ((normalizedChainComplex k A A).X n)
  rw [eqToIso.inv]
  exact eqToHom_refl ((normalizedChainComplex k A A).X n) (regularNormalized_X_eq k A n).symm

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. For all i,j : ℕ, the differentials of
normalizedChainComplex k A A and NonUnital.normalizedBComplex k A from degree i to degree j are
equal. -/
theorem regularNormalized_d_eq (i j : ℕ) :
    (normalizedChainComplex k A A).d i j = (NonUnital.normalizedBComplex k A).d i j := by
  have h := (regularNormalizedComplexIso k A).hom.comm i j
  simp only [regularNormalizedComplexIso_hom_f] at h
  exact h.symm

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. In every n : ℕ, the regular normalized
Connes operator defines a k-module map Bₙ = regularNormalizedConnes k A n : C̄ₙ(A,A) →
C̄ₙ₊₁(A,A), through the identity-component comparison with the normalized b-complex. -/
def regularNormalizedConnes (n : ℕ) :
    (normalizedChainComplex k A A).X n ⟶ (normalizedChainComplex k A A).X (n + 1) :=
  ModuleCat.ofHom (NonUnital.normalizedBoundary k A n).hom

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. In degree n : ℕ, the underlying linear map
of regularNormalizedConnes k A n equals the underlying linear map NonUnital.normalizedBoundary k
A n, the descended normalized Connes operator. -/
theorem regularNormalizedConnes_hom (n : ℕ) :
    (regularNormalizedConnes k A n).hom = (NonUnital.normalizedBoundary k A n).hom := rfl

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. For every n : ℕ, Bₙ followed by Bₙ₊₁ is zero
on normalized regular chains: regularNormalizedConnes k A n ≫ regularNormalizedConnes k A (n+1)
= 0. -/
theorem regularNormalizedConnes_square (n : ℕ) :
    regularNormalizedConnes k A n ≫ regularNormalizedConnes k A (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := ConcreteCategory.congr_hom (NonUnital.normalizedBoundary_square k A n) x
  change (NonUnital.normalizedBoundary k A (n + 1)).hom
    ((NonUnital.normalizedBoundary k A n).hom x) = 0 at h
  change (NonUnital.normalizedBoundary k A (n + 1)).hom
    ((NonUnital.normalizedBoundary k A n).hom x) = 0
  exact h

/-- Let R be a ring and M,N,P be R-modules. For module morphisms f : M→N, g : N→M, h : M→P and i :
P→M, the endomorphism f ≫ g + h ≫ i has underlying linear map g ∘ f + i ∘ h. -/
private theorem comp_add_hom {R : Type*} [Ring R] {M N P : ModuleCat R}
    (f : M ⟶ N) (g : N ⟶ M) (h : M ⟶ P) (i : P ⟶ M) :
    (f ≫ g + h ≫ i).hom = g.hom.comp f.hom + i.hom.comp h.hom := rfl

/-- Let k be a commutative ring and A a commutative k-algebra. Let C̄(A,A) be the normalized
Hochschild chain complex with regular coefficients. For every n : ℕ, the endomorphism of
C̄ₙ₊₁(A,A) given by bₙ₊₂ ∘ Bₙ₊₁ + Bₙ ∘ bₙ₊₁ is zero. Here b lowers degree and B raises degree,
so this is the full normalized mixed-complex identity bB+Bb=0. -/
theorem regularNormalizedConnes_mixed (n : ℕ) :
    regularNormalizedConnes k A (n + 1) ≫ (normalizedChainComplex k A A).d (n + 2) (n + 1) +
      (normalizedChainComplex k A A).d (n + 1) n ≫ regularNormalizedConnes k A n = 0 := by
  rw [regularNormalized_d_eq k A (n + 2) (n + 1), regularNormalized_d_eq k A (n + 1) n]
  apply ModuleCat.hom_ext
  have hNative := congrArg ModuleCat.Hom.hom (NonUnital.normalizedBoundary_mixed k A n)
  have hB₁ := regularNormalizedConnes_hom k A (n + 1)
  have hB₀ := regularNormalizedConnes_hom k A n
  have hcomponents := congrArg₂
    (fun f g => ((NonUnital.normalizedBComplex k A).d (n + 2) (n + 1)).hom.comp f +
      g.comp ((NonUnital.normalizedBComplex k A).d (n + 1) n).hom) hB₁ hB₀
  exact (comp_add_hom (regularNormalizedConnes k A (n + 1))
    ((NonUnital.normalizedBComplex k A).d (n + 2) (n + 1))
    ((NonUnital.normalizedBComplex k A).d (n + 1) n) (regularNormalizedConnes k A n)).trans
      (hcomponents.trans
        ((comp_add_hom (NonUnital.normalizedBoundary k A (n + 1))
          ((NonUnital.normalizedBComplex k A).d (n + 2) (n + 1))
          ((NonUnital.normalizedBComplex k A).d (n + 1) n)
          (NonUnital.normalizedBoundary k A n)).symm.trans hNative))

end ModuleCat.Algebra.Hochschild.Symmetric
