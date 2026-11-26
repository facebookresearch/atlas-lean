/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport

/-!
# One cycle input in the cochain pairing differential

The Leibniz identity for a graded cochain pairing has two differential terms. When the left
input is a cycle of degree `p`, only the right differential remains, with sign `(-1)^p`. When
the right input is a cycle, only the left differential remains, with coefficient one.

The formulas use natural cochain degrees and the explicit object equality maps to total degree
`p + q + 1`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace HomologicalComplex.CochainGradedPairing

universe u

variable (R : Type u) [CommRing R]

private lemma moduleHom_comp_apply {A B C : ModuleCat.{u} R}
    (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) :=
  rfl

@[simp]
private lemma moduleHom_add_apply {A B : ModuleCat.{u} R}
    (f g : A ⟶ B) (x : A) :
    (f + g).hom x = f.hom x + g.hom x :=
  rfl

@[simp]
private lemma moduleHom_zsmul_apply {A B : ModuleCat.{u} R}
    (n : ℤ) (f : A ⟶ B) (x : A) :
    (n • f).hom x = n • f.hom x :=
  rfl

@[simp]
private lemma moduleTensorHom_tmul {A B C D : ModuleCat.{u} R}
    (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
    (f ⊗ₘ g).hom (x ⊗ₜ[R] y) = f.hom x ⊗ₜ[R] g.hom y :=
  rfl

/-- Cycle in the left input leaves the signed right differential.

For a left cycle `x` in degree `p` and a right element `y` in degree `q`, the differential of
their pairing is `(-1)^p` times the pairing of `x` with `d y`, transported to degree `p + q +
1`. -/
theorem pair_d_right_of_cycle
    {K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    (x : K₁.cycles p) (y : K₂.X q) :
    (K₃.d (p + q) (p + q + 1)).hom
        ((P.pair p q).hom ((K₁.iCycles p).hom x ⊗ₜ[R] y)) =
      ((-1 : ℤ) ^ p) •
        (K₃.XIsoOfEq (show p + (q + 1) = p + q + 1 by omega)).hom.hom
          ((P.pair p (q + 1)).hom
            ((K₁.iCycles p).hom x ⊗ₜ[R] (K₂.d q (q + 1)).hom y)) := by
  have h := ConcreteCategory.congr_hom (P.leibniz p q)
    ((K₁.iCycles p).hom x ⊗ₜ[R] y)
  have hx : (K₁.d p (p + 1)).hom ((K₁.iCycles p).hom x) = 0 := by
    exact ConcreteCategory.congr_hom (K₁.iCycles_d p (p + 1)) x
  simp only [moduleHom_comp_apply, moduleHom_add_apply,
    moduleHom_zsmul_apply, moduleTensorHom_tmul] at h
  rw [hx] at h
  simpa using h

/-- Cycle in the right input leaves the left differential.

For a left element `x` and a right cycle `y`, the differential of their pairing is the pairing
of `d x` with `y`, transported to degree `p + q + 1`. -/
theorem pair_d_left_of_cycle
    {K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    (x : K₁.X p) (y : K₂.cycles q) :
    (K₃.d (p + q) (p + q + 1)).hom
        ((P.pair p q).hom (x ⊗ₜ[R] (K₂.iCycles q).hom y)) =
      (K₃.XIsoOfEq (show (p + 1) + q = p + q + 1 by omega)).hom.hom
        ((P.pair (p + 1) q).hom
          ((K₁.d p (p + 1)).hom x ⊗ₜ[R] (K₂.iCycles q).hom y)) := by
  have h := ConcreteCategory.congr_hom (P.leibniz p q)
    (x ⊗ₜ[R] (K₂.iCycles q).hom y)
  have hy : (K₂.d q (q + 1)).hom ((K₂.iCycles q).hom y) = 0 := by
    exact ConcreteCategory.congr_hom (K₂.iCycles_d q (q + 1)) y
  simp only [moduleHom_comp_apply, moduleHom_add_apply,
    moduleHom_zsmul_apply, moduleTensorHom_tmul] at h
  rw [hy] at h
  simpa using h

end HomologicalComplex.CochainGradedPairing
