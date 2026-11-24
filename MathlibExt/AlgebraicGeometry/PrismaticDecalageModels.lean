/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Literal ideal décalage of connective prismatic cochain models

For a connective complex K the ith term is the actual submodule
{x in I^i K^i | dx in I^(i+1) K^(i+1)}. The differential and inclusion are
restrictions of the original differential and the actual submodule maps.
No endofunctor is chosen and merely called décalage. Applying this formula
to a termwise I-torsion-free model realizes Lη_I; that source-normalized
model and the geometric Frobenius comparison are separate requests.

References: BMS18 arXiv:1602.03148v3, Section 6; BMS19
arXiv:1802.03261v2, Proposition 5.8; Bhatt–Scholze,
arXiv:1905.08229v4, Theorem 15.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticDecalageModels

open CategoryTheory
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

variable {A : Type} [CommRing A] (I : Ideal A)
  (K : CochainComplex (ModuleCat.{1} A) ℕ)

def term (i : ℕ) : Submodule A (K.X i) :=
  (I ^ i • (⊤ : Submodule A (K.X i))) ⊓
    (I ^ (i + 1) • (⊤ : Submodule A (K.X (i + 1)))).comap (K.d i (i + 1)).hom

def differential (i : ℕ) : ModuleCat.of A (term I K i) ⟶
    ModuleCat.of A (term I K (i + 1)) :=
  ModuleCat.ofHom
    { toFun := fun x ↦
        ⟨(K.d i (i + 1)).hom x.val, x.property.2, by
          change (K.d (i + 1) (i + 1 + 1)).hom ((K.d i (i + 1)).hom x.val) ∈
            I ^ (i + 1 + 1) • (⊤ : Submodule A (K.X (i + 1 + 1)))
          have hz := congrArg (fun f : K.X i ⟶ K.X (i + 1 + 1) ↦ f.hom x.val)
            (K.d_comp_d i (i + 1) (i + 1 + 1))
          change (K.d (i + 1) (i + 1 + 1)).hom ((K.d i (i + 1)).hom x.val) = 0 at hz
          rw [hz]
          exact Submodule.zero_mem _⟩
      map_add' x y := Subtype.ext (map_add _ x.val y.val)
      map_smul' a x := Subtype.ext ((K.d i (i + 1)).hom.map_smul a x.val) }

theorem differential_square (i : ℕ) :
    differential I K i ≫ differential I K (i + 1) = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change (K.d (i + 1) (i + 1 + 1)).hom ((K.d i (i + 1)).hom x.val) = 0
  exact congrArg (fun f : K.X i ⟶ K.X (i + 1 + 1) ↦ f.hom x.val)
    (K.d_comp_d i (i + 1) (i + 1 + 1))

def natComplex : CochainComplex (ModuleCat.{1} A) ℕ :=
  CochainComplex.of (fun i ↦ ModuleCat.of A (term I K i))
    (differential I K) (differential_square I K)

def natInclusion : natComplex I K ⟶ K where
  f i := ModuleCat.ofHom (term I K i).subtype
  comm' i j h := by
    have hj : i + 1 = j := h
    subst j
    simp only [natComplex, CochainComplex.of_d]
    ext x
    rfl

def complex : Cochains A :=
  (natComplex I K).extend ComplexShape.embeddingUpNat

def inclusion : complex I K ⟶ K.extend ComplexShape.embeddingUpNat :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{1} A)).map (natInclusion I K)

def derived : D A := DerivedCategory.Q.obj (complex I K)

/-- The native canonical filtration terms on η_I K, with both ideal powers fixed. -/
def filteredTerm (j i : ℕ) : Submodule A (K.X i) :=
  (I ^ max j i • (⊤ : Submodule A (K.X i))) ⊓
    (I ^ max j (i + 1) • (⊤ : Submodule A (K.X (i + 1)))).comap (K.d i (i + 1)).hom

def idealAction (i : ℕ) : I ⊗[A] (K.X i) →ₗ[A] K.X i :=
  TensorProduct.lift ((LinearMap.lsmul A (K.X i)).comp I.subtype)

/-- The actual ideal-action map is injective in every term. For an
invertible ideal this is the local generator torsion-free condition. -/
def IsIdealRegularModel : Prop :=
  ∀ i : ℕ, Function.Injective (idealAction I K i)

end MathlibExt.AlgebraicGeometry.PrismaticDecalageModels
