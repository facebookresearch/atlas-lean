/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Source proposal; Native elaboration is unexecuted. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficients
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.NormalizedMixedBicomplex

/-!
# The symmetric regular normalized complex and Connes B

For a commutative algebra, the symmetric opposite action
agrees with regular right multiplication. The normalized
identity comparison transports the regular Connes B, its
square-zero law and its anticommutation with the differential.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

/-- The symmetric regular opposite action equals the native regular right action. -/
theorem regular_opModule_eq : opModule A A = (Semiring.toOppositeModule : Module Aᵐᵒᵖ A) := by
  apply Module.ext'
  intro a m
  rw [opModule_smul]
  change MulOpposite.unop a * m = m * MulOpposite.unop a
  exact mul_comm _ _

/-- The regular Connes construction retains the given ground algebra. -/
theorem regularAlgebra_eq : NonUnital.regularAlgebra k A = (inferInstance : Algebra k A) := by
  apply Algebra.algebra_ext
  intro r
  change r • (1 : A) = algebraMap k A r
  rw [Algebra.smul_def, mul_one]

/-- The symmetric and original regular normalized complexes coincide through the original structures. -/
theorem regularNormalizedComplex_eq : normalizedChainComplex k A A = NonUnital.normalizedBComplex k A := by
  unfold normalizedChainComplex NonUnital.normalizedBComplex
  congr 1 <;> first
    | exact regular_opModule_eq A
    | exact (regularAlgebra_eq k A).symm
    | exact proof_irrel_heq _ _

/-- The two original normalized degree objects agree through their ground tensor carrier. -/
theorem regularNormalized_X_eq (n : ℕ) :
    (normalizedChainComplex k A A).X n = (NonUnital.normalizedBComplex k A).X n := by
  change ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n =
    ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n
  rfl

/-- Equality of native complexes gives the original component transport square. -/
private theorem differential_eq_transport {C : Type*} [Category* C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (h : K = L) (i j : ι) :
    eqToHom (congrArg (fun T : HomologicalComplex C c => T.X i) h) ≫ L.d i j =
      K.d i j ≫ eqToHom (congrArg (fun T : HomologicalComplex C c => T.X j) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The original regular/symmetric normalized comparison uses native identity transport in each degree. -/
def regularNormalizedComplexIso : normalizedChainComplex k A A ≅ NonUnital.normalizedBComplex k A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => eqToIso (regularNormalized_X_eq k A n))
    (by
      intro i j _
      simpa only [eqToIso.hom] using differential_eq_transport (regularNormalizedComplex_eq k A) i j)

/-- The comparison preserves every original normalized coefficient tensor. -/
theorem regularNormalizedComplexIso_hom_f (n : ℕ) :
    (regularNormalizedComplexIso k A).hom.f n = 𝟙 ((normalizedChainComplex k A A).X n) := by
  change (eqToIso (regularNormalized_X_eq k A n)).hom = 𝟙 ((normalizedChainComplex k A A).X n)
  rw [eqToIso.hom]
  exact eqToHom_refl ((normalizedChainComplex k A A).X n) (regularNormalized_X_eq k A n)

/-- The inverse comparison also retains every original normalized coefficient tensor. -/
theorem regularNormalizedComplexIso_inv_f (n : ℕ) :
    (regularNormalizedComplexIso k A).inv.f n = 𝟙 ((normalizedChainComplex k A A).X n) := by
  change (eqToIso (regularNormalized_X_eq k A n)).inv = 𝟙 ((normalizedChainComplex k A A).X n)
  rw [eqToIso.inv]
  exact eqToHom_refl ((normalizedChainComplex k A A).X n) (regularNormalized_X_eq k A n).symm

/-- The identity comparison identifies the two differentials in every pair of degrees. -/
theorem regularNormalized_d_eq (i j : ℕ) :
    (normalizedChainComplex k A A).d i j = (NonUnital.normalizedBComplex k A).d i j := by
  have h := (regularNormalizedComplexIso k A).hom.comm i j
  simp only [regularNormalizedComplexIso_hom_f] at h
  exact h.symm

/-- The original regular Connes B, viewed on the symmetric normalized endpoints. -/
def regularNormalizedConnes (n : ℕ) :
    (normalizedChainComplex k A A).X n ⟶ (normalizedChainComplex k A A).X (n + 1) :=
  ModuleCat.ofHom (NonUnital.normalizedBoundary k A n).hom

/-- Its original degree map is exactly the literal normalized B. -/
theorem regularNormalizedConnes_hom (n : ℕ) :
    (regularNormalizedConnes k A n).hom = (NonUnital.normalizedBoundary k A n).hom := rfl

/-- The regular B has square zero on these original normalized endpoints. -/
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

/-- The native module-hom getter takes the same two compositions and their sum to linear maps. -/
private theorem comp_add_hom {R : Type*} [Ring R] {M N P : ModuleCat R}
    (f : M ⟶ N) (g : N ⟶ M) (h : M ⟶ P) (i : P ⟶ M) :
    (f ≫ g + h ≫ i).hom = g.hom.comp f.hom + i.hom.comp h.hom := rfl

/-- The original complete bB+Bb law holds on the original symmetric regular normalized complex. -/
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
