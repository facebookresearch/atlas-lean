/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.LinearYonedaCochainPairing
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.ChainMap

/-!
# Alexander--Whitney maps and linear-Yoneda pairings

The Alexander--Whitney component is a sum over every split of a simplicial
degree.  A linear-Yoneda pairing descriptor selects one bidegree, so its
composite with the Alexander--Whitney component is exactly the corresponding
front-face/back-face summand.

The split is indexed by `s : Fin (n + 1)`, with complementary degree
`n - s`.  This formulation avoids transports while covering every pair of
nonnegative degrees summing to `n`.

## Main declaration

* `AlgebraicTopology.AlexanderWhitney.alternatingComponent_comp_linearYonedaPairingDescOfEq`
* `AlgebraicTopology.AlexanderWhitney.alternatingComponent_comp_linearYonedaPairingDesc`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory Simplicial

namespace AlgebraicTopology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ Z : C, ((curriedTensor C).obj Z).Additive]
variable (X Y : SimplicialObject C)
variable [HomologicalComplex.HasTensor
  ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
  ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
variable {M N P : C}

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive] in
/-- The front face for the canonical complementary degree `(p + q) - p`
agrees with the front face for the specified degree `q`. -/
theorem frontFace_add_sub (p q : ℕ) :
    frontFace (C := C) X
        (show p + (p + q - p) = p + q by omega) =
      frontFace (C := C) X (show p + q = p + q by rfl) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.multiGoal false in
omit [MonoidalCategory C] [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive] in
/-- Transporting the canonical complementary-degree back face from
`(p + q) - p` to `q` gives the specified back face. -/
theorem backFace_add_sub_comp_XIsoOfEq (p q : ℕ) :
    backFace (C := C) Y
        (show p + (p + q - p) = p + q by omega) ≫
      (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).XIsoOfEq
        (show p + q - p = q by omega)).hom =
    backFace (C := C) Y (show p + q = p + q by rfl) := by
  change Y.map (backInclusion p (p + q - p) (p + q) (by omega)).op ≫
      eqToHom (congrArg
        (fun n => Y.obj (Opposite.op (SimplexCategory.mk n)))
        (show p + q - p = q by omega)) =
    Y.map (backInclusion p q (p + q) rfl).op
  rw [← eqToHom_map]
  rw [← Y.map_comp]
  apply congrArg Y.map
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  ext i
  · simp [backInclusion, SimplexCategory.subinterval]
  all_goals
    apply congrArg Opposite.op
    apply SimplexCategory.ext
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The Alexander--Whitney component at total degree `p + q` selects the
requested `(p,q)` linear-Yoneda pairing descriptor. -/
theorem alternatingComponent_comp_linearYonedaPairingDesc
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi : X.obj (Opposite.op (SimplexCategory.mk p)) ⟶ M)
    (psi : Y.obj (Opposite.op (SimplexCategory.mk q)) ⟶ N) :
    alternatingComponent X Y (p + q) ≫
        HomologicalComplex.linearYonedaPairingDesc C mu p q phi psi =
      (frontFace (C := C) X rfl ⊗ₘ backFace (C := C) Y rfl) ≫
        (phi ⊗ₘ psi) ≫ mu := by
  unfold HomologicalComplex.linearYonedaPairingDesc
  rw [alternatingComponent_eq_sum, Preadditive.sum_comp]
  rw [Fintype.sum_eq_single (⟨p, by omega⟩ : Fin (p + q + 1))]
  · dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq_of_eq
      (C := C)
      (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
      mu p q (p + q) p (p + q - p) rfl (by omega)
      rfl (by omega) phi psi]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    rw [frontFace_add_sub, backFace_add_sub_comp_XIsoOfEq]
    have hfront :
        frontFace (C := C) (p := p) (q := q) (n := p + q) X rfl ≫
            𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) =
          frontFace (C := C) (p := p) (q := q) (n := p + q) X rfl :=
      Category.comp_id _
    rw [hfront]
  · intro i hi
    have hne : (i : ℕ) ≠ p := by
      intro h
      apply hi
      apply Fin.ext
      exact h
    dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq]
    simp [hne]

/-- Composing an Alexander--Whitney component with a linear-Yoneda pairing
descriptor selects exactly the front-face/back-face term in the requested
bidegree. -/
theorem alternatingComponent_comp_linearYonedaPairingDescOfEq
    (mu : M ⊗ N ⟶ P) (n : ℕ) (s : Fin (n + 1))
    (phi : X.obj (Opposite.op (SimplexCategory.mk s)) ⟶ M)
    (psi : Y.obj (Opposite.op (SimplexCategory.mk (n - s))) ⟶ N) :
    alternatingComponent X Y n ≫
        HomologicalComplex.linearYonedaPairingDescOfEq C mu s (n - s) n
          (by omega) phi psi =
      (frontFace (C := C) X (show s + (n - s) = n by omega) ⊗ₘ
          backFace (C := C) Y (show s + (n - s) = n by omega)) ≫
        (phi ⊗ₘ psi) ≫ mu := by
  rw [alternatingComponent_eq_sum, Preadditive.sum_comp]
  rw [Fintype.sum_eq_single s]
  · dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq
      (C := C)]
    simp
  · intro i hi
    have hne : (i : ℕ) ≠ s := by
      intro h
      apply hi
      apply Fin.ext
      exact h
    dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq
      (C := C)]
    simp [hne]

end AlgebraicTopology.AlexanderWhitney
